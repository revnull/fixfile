{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable,
    TypeFamilies, DeriveDataTypeable, TupleSections #-}

{- |
    Module      :  Data.FixFile.Trie
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    This is a Trie data type that can be used with 'FixFile'. It can be used
    as a key-value store where the key is a 'ByteString' of arbitrary size.
-}
module Data.FixFile.Trie.Light (Trie
                               ,value
                               ,freeze
                               ,createTrieFile
                               ,openTrieFile
                               ,lookupTrie
                               ,lookupTrieT
                               ,descendTrie
                               ,descendTrieT
                               ,insertTrie
                               ,insertTrieT
                               ,deleteTrie
                               ,deleteTrieT
                               ,iterateTrie
                               ,iterateTrieT
                               ) where

import Prelude hiding (tail)

import Control.Applicative hiding (empty)
import Control.Monad
import Data.Array
import qualified Data.ByteString.Lazy as BS
import Data.Dynamic
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Serialize
import Data.Word
import GHC.Generics

import Data.FixFile
import Data.FixFile.Trie.Shared

-- | 'Fixed' @('Trie' v)@ is a trie mapping lazy 'ByteString's to values of
--   type v.
data Trie v a =
    Tail (Maybe v)
  | String (Maybe v) BS.ByteString a
  | Small (Maybe v) [(Word8, a)]
  | Big (Maybe v) (Array Word8 (Maybe a))
  | Mutable (Maybe v) (M.Map Word8 a)
  deriving (Read, Show, Generic, Functor, Foldable, Traversable, Typeable)

instance Null1 (Trie v) where
    empty1 = Tail Nothing
    null1 (Tail Nothing) = True
    null1 _ = False

instance (Serialize v, Serialize a) => Serialize (Trie v a) where
    put (Tail a) = putWord8 1 >> put a
    put (String m b a) = putWord8 2 >> put m >> put b >> put a
    put (Small m l) = putWord8 3 >> put m >> put l
    put (Big m a) = putWord8 4 >> put m >> put a
    put m = put $ freeze' m
    get = getWord8 >>= getTrie where
        getTrie 1 = Tail <$> get
        getTrie 2 = String <$> get <*> get <*> get
        getTrie 3 = Small <$> get <*> get
        getTrie 4 = Big <$> get <*> get
        getTrie _ = error "Invalid Serialized Trie"

tail :: Fixed g => Maybe v -> g (Trie v)
tail = inf . Tail where

string :: Fixed g => Maybe v -> BS.ByteString ->
    g (Trie v) -> g (Trie v)
string v k t = inf $ String v k t

fill :: Fixed g => BS.ByteString -> Maybe v -> g (Trie v) -> g (Trie v)
fill k x t = if BS.null k
    then t
    else string x k t

small :: Fixed g => Maybe v -> [(Word8, g (Trie v))] -> g (Trie v)
small v l = inf $ Small v l

big :: Fixed g => Maybe v -> Array Word8 (Maybe (g (Trie v))) -> g (Trie v)
big v l = inf $ Big v l

mut :: Fixed g => Maybe v -> M.Map Word8 (g (Trie v)) -> g (Trie v)
mut v l = inf $ Mutable v l

value :: Fixed g => g (Trie v) -> Maybe v
value = phi . outf where
    phi (Tail v) = v
    phi (String v _ _) = v
    phi (Small v _) = v
    phi (Big v _) = v
    phi (Mutable v _) = v

-- | 'freeze' takes a 'Trie' that has been mutated and creates a copy of it
-- that allows for faster lookups. This happens automatically for 'Trie's that
-- are serialized to a 'FixFile'. A 'Trie' will be automatically thawed on
-- any node that is modified.
freeze :: Fixed g => g (Trie v) -> g (Trie v)
freeze = cata (inf . freeze') where

freeze' :: Trie v a -> Trie v a
freeze' (Mutable a b) = if M.size b > bigThreshold
    then 
        let Just ((minb,_),_) = M.minViewWithKey b
            Just ((maxb,_),_) = M.maxViewWithKey b
        in Big a $ array (minb, maxb) $ do
            i <- [minb..maxb]
            case M.lookup i b of
                Nothing -> return (i, Nothing)
                Just t -> return (i, Just t)
    else Small a $ M.toList b
freeze' m = m

thaw :: Trie v a -> Trie v a
thaw (Big a b) = Mutable a . M.fromList $ do
    (i, Just v) <- assocs b
    return (i, v)
thaw (Small a b) = Mutable a $ M.fromList b
thaw m = m

-- | Create a 'FixFile' of @('Trie' v)@ data.
createTrieFile :: (Serialize v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (Trie v)))
createTrieFile fp = createFixFile (Ref empty) fp

-- | Open a 'FixFile' of @('Trie' v)@ data.
openTrieFile :: (Serialize v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (Trie v)))
openTrieFile = openFixFile

-- | Lookup a possible value stored in a trie for a given 'ByteString' key.
lookupTrie :: Fixed g => BS.ByteString -> g (Trie v) -> Maybe v
lookupTrie a b = descendTrie a b >>= value

-- | 'Transaction' version of 'lookupTrie'.
lookupTrieT :: Serialize v =>
    BS.ByteString -> Transaction (Ref (Trie v)) s (Maybe v)
lookupTrieT k = lookupT (lookupTrie k)

-- | Lookup a possible value stored in a trie for a given 'ByteString' key.
descendTrie :: Fixed g => BS.ByteString -> g (Trie v) -> Maybe (g (Trie v))
descendTrie a b = para phi b b a where
    term t k = guard (BS.null k) >> return t
    phi t t' k = term t' k <|> phi' t k
    phi' (Tail _) _ = Nothing
    phi' (String _ s (t', t)) k = do
        let (_, lt, rt) = splitKey s k
        case (BS.null lt, BS.null rt) of
            (True, _) -> t t' rt
            (False, False) -> Nothing
            _ -> return . inf $ (String Nothing lt t')
    phi' (Small _ l) k = do
        (c, r) <- BS.uncons k
        (t', t) <- lookupAscending c l
        t t' r
    phi' (Big _ l) k = do
        (c, r) <- BS.uncons k
        guard (inRange (bounds l) c)
        (t', t) <- l ! c
        t t' r
    phi' (Mutable _ l) k = do
        (c, r) <- BS.uncons k
        (t', t) <- M.lookup c l
        t t' r

descendTrieT :: Serialize v => BS.ByteString ->
    Transaction (Ref (Trie v)) s (Maybe (Stored s (Trie v)))
descendTrieT a = lookupT (descendTrie a)

-- | Insert a value into a trie for the given 'ByteString' key.
insertTrie :: Fixed g => BS.ByteString -> v -> g (Trie v) -> g (Trie v)
insertTrie a b c = para phi c a where
    val = Just b
    valTail = tail val
    phi (Tail vm) k = fill k vm valTail
    phi (String vm s (tn, ta)) k
        | BS.null k = string val s tn
        | otherwise =
            let (sh, lt, rt) = splitKey k s
                Just (lh, ls) = BS.uncons lt
                Just (rh, rs) = BS.uncons rt
            in case (BS.null sh, BS.null lt, BS.null rt) of
                (True, False, False) -> mut vm $ M.fromList
                    [(lh, fill ls Nothing valTail), (rh, fill rs Nothing tn)]
                (True, _, _) -> error "Invalid Key Split"
                (_, False, False) -> string vm sh $ mut Nothing $ M.fromList
                    [(lh, fill ls Nothing valTail), (rh, fill rs Nothing tn)]
                (_, True, False) -> string vm sh $ string val rt tn
                (_, False, True) -> string vm sh $ ta lt
                (_, True, True) -> string vm s $ ta lt
    phi x@(Big _ t) k
        | BS.null k = big val (fmap (fmap fst) t)
        | otherwise = phi (thaw x) k
    phi x@(Small _ t) k
        | BS.null k = small val (fmap (fmap fst) t)
        | otherwise = phi (thaw x) k
    phi (Mutable vm m) k = case BS.uncons k of
        Nothing -> mut val (fmap fst m)
        Just (kh, kt) -> mut vm $ case M.lookup kh m of
            Nothing -> M.insert kh (fill kt Nothing valTail) $ fmap fst m
            Just (_, ta) -> M.insert kh (ta kt) $ fmap fst m

-- | 'Transaction' version of 'insertTrie'.
insertTrieT :: Serialize v =>
    BS.ByteString -> v -> Transaction (Ref (Trie v)) s ()
insertTrieT k v = alterT (insertTrie k v)
 
data Deleted g v = 
    NoDelete
  | Deleted Bool (g (Trie v)) (Maybe (BS.ByteString, g (Trie v)))

-- | Delete a value from a trie for a given 'ByteString' key.
deleteTrie :: Fixed g => BS.ByteString -> g (Trie v) -> g (Trie v)
deleteTrie a b = newHead $ para phi b a where
    newHead NoDelete = b
    newHead (Deleted True _ _) = empty
    newHead (Deleted _ h _) = h
    phi (Tail _) k = if BS.null k
        then Deleted True empty Nothing
        else NoDelete
    phi (String vm s (tn, ta)) k
        | BS.null k = if isJust vm
            then Deleted False (string Nothing s tn) (Just (s, tn))
            else NoDelete
        | otherwise = del where
            (_, lt, rt) = splitKey k s
            ta' = ta lt
            del = if BS.null rt
                then case ta' of
                    NoDelete -> NoDelete
                    Deleted True _ _ -> if isNothing vm
                        then Deleted True empty Nothing
                        else Deleted False (tail vm) Nothing
                    Deleted False tn' (Just (b', tn'')) ->
                        Deleted False (string vm s tn') $
                            Just (BS.append s b', tn'')
                    Deleted False tn' Nothing ->
                        Deleted False (string vm s tn') Nothing
                else NoDelete
    phi x@(Small vm ts) k
        | BS.null k = case vm of
            Nothing -> NoDelete
            _ -> Deleted False (small Nothing (fmap (fmap fst) ts)) Nothing
        | otherwise = phi (thaw x) k
    phi x@(Big vm ts) k
        | BS.null k = case vm of
            Nothing -> NoDelete
            _ -> Deleted False (big Nothing (fmap (fmap fst) ts)) Nothing
        | otherwise = phi (thaw x) k
    phi (Mutable vm ts) k
        | BS.null k = case vm of
            Nothing -> NoDelete
            _ -> Deleted False (mut Nothing (fmap fst ts)) Nothing
        | otherwise = fromJust . (<|> Just NoDelete) $ do
            (kh, kt) <- BS.uncons k
            (_, ta) <- M.lookup kh ts
            return $ case ta kt of
                Deleted True _ _ ->
                    let ts' = fmap fst $ M.delete kh $ ts
                        mut' = mut vm ts'
                    in case M.size ts' of
                        0 -> if isNothing vm
                            then Deleted True empty Nothing
                            else Deleted False (tail vm) Nothing
                        _ -> Deleted False mut' Nothing
                Deleted False dt _ ->
                    let ts' = M.insert kh dt $ fmap fst ts
                        mut' = mut vm ts'
                    in Deleted False mut' Nothing
                _ -> NoDelete

-- | 'Transaction' version of 'deleteTrie'.
deleteTrieT :: Serialize v =>
    BS.ByteString -> Transaction (Ref (Trie v)) s ()
deleteTrieT k = alterT (deleteTrie k)

-- | Iterate over a Trie for all of the 'ByteString' and value tuples for a
-- given 'ByteString' prefix.
iterateTrie :: Fixed g => BS.ByteString -> g (Trie v) -> [(BS.ByteString, v)]
iterateTrie a b = cata phi b a BS.empty [] where
    kvlist _ _ Nothing = id
    kvlist k k' (Just v) = if BS.null k
        then ((k', v):) else id
    phi (Tail vm) k k' = kvlist k k' vm
    phi (String vm s ta) k k' = kvlist k k' vm <> ta' where
        (_, lt, rt) = splitKey k s
        ta' = if BS.null lt || BS.null rt
            then ta lt (BS.append k' s)
            else mempty
    phi (Small vm ts) k k' = kvlist k k' vm <> ts' where
        mapKeys (xk, xv) = xv k (BS.snoc k' xk)
        ts' = case BS.uncons k of
            Nothing -> foldMap mapKeys ts
            Just (i, k'') -> case lookupAscending i ts of
                Nothing -> mempty
                Just xv -> xv k'' (BS.snoc k' i)
    phi (Big vm ts) k k' = kvlist k k' vm <> ts' where
        mapKeys (_, Nothing) = mempty
        mapKeys (xk, Just xv) = xv k (BS.snoc k' xk)
        ts' = case BS.uncons k of
            Nothing -> foldMap mapKeys (assocs ts)
            Just (i, k'') -> case guard (inRange (bounds ts) i) >> ts ! i of
                Nothing -> mempty
                Just r -> r k'' (BS.snoc k' i) 
    phi (Mutable vm ts) k k' = kvlist k k' vm <> ts' where
        mapKeys (xk, xv) = xv k (BS.snoc k' xk)
        ts' = case BS.uncons k of
            Nothing -> foldMap mapKeys (M.assocs ts)
            Just (i, k'') -> case M.lookup i ts of
                Nothing -> mempty
                Just r -> r k'' (BS.snoc k' i)

-- | 'Transaction' version of 'iterateTrie'.
iterateTrieT :: Serialize v => BS.ByteString ->
    Transaction (Ref (Trie v)) s [(BS.ByteString, v)]
iterateTrieT k = lookupT (iterateTrie k)

instance FixedAlg (Trie v) where
    type Alg (Trie v) = v

instance FixedSub (Trie v) where
    type Sub (Trie v) v v' = Trie v'

instance FixedFunctor (Trie v) where
    fmapF f = cata phi where
        phi (Tail v) = tail (fmap f v)
        phi (String v b t) = string (fmap f v) b t
        phi (Small v ts) = small (fmap f v) ts
        phi (Big v ts) = big (fmap f v) ts
        phi (Mutable v ts) = mut (fmap f v) ts

instance FixedFoldable (Trie v) where
    foldMapF f = cata phi where
        mapply Nothing = mempty
        mapply (Just v) = f v
        phi (Tail v) = mapply v
        phi (String v _ t) = mapply v <> t
        phi (Small v l) = mapply v <> mconcat (snd <$> l)
        phi (Big v a) = mapply v <> foldMap (maybe mempty id) a
        phi (Mutable v m) = mapply v <> foldMap id m

instance FixedTraversable (Trie v) where
    traverseF f = cata phi where
        mapply Nothing = pure Nothing
        mapply (Just v) = Just <$> f v
        phi (Tail v) = tail <$> mapply v
        phi (String v b a) = string <$> mapply v <*> pure b <*> a
        phi (Small v l) = small <$> mapply v <*>
            traverse (\(w, a) -> (w,) <$> a) l
        phi (Big v a) = big <$> mapply v <*> traverse tapply a where
            tapply Nothing = pure Nothing
            tapply (Just t) = Just <$> t
        phi (Mutable v m) = mut <$> mapply v <*> traverse id m


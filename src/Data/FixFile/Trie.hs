{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable,
    TypeFamilies, DeriveDataTypeable, TupleSections, DefaultSignatures #-}

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
module Data.FixFile.Trie (Trie
                         ,freeze
                         ,createTrieFile
                         ,openTrieFile
                         ,lookupTrie
                         ,lookupTrieT
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

-- | 'Fixed' @('Trie' v)@ is a trie mapping lazy 'ByteString's to values of
--   type v.
data Trie v a =
    Value v
  | Tail (Maybe a)
  | String (Maybe a) BS.ByteString a
  | Small (Maybe a) [(Word8, a)]
  | Big (Maybe a) (Array Word8 (Maybe a))
  | Mutable (Maybe a) (M.Map Word8 a)
  deriving (Read, Show, Generic, Functor, Foldable, Traversable, Typeable)

instance Null1 (Trie v) where
    empty1 = Tail Nothing
    null1 (Tail Nothing) = True
    null1 _ = False

instance (Serialize v, Serialize a) => Serialize (Trie v a) where
    put (Value v) = putWord8 0 >> put v
    put (Tail a) = putWord8 1 >> put a
    put (String m b a) = putWord8 2 >> put m >> put b >> put a
    put (Small m l) = putWord8 3 >> put m >> put l
    put (Big m a) = putWord8 4 >> put m >> put a
    put m = put $ freeze' m
    get = getWord8 >>= getTrie where
        getTrie 0 = Value <$> get
        getTrie 1 = Tail <$> get
        getTrie 2 = String <$> get <*> get <*> get
        getTrie 3 = Small <$> get <*> get
        getTrie 4 = Big <$> get <*> get
        getTrie _ = error "Invalid Serialized Trie"

value :: Fixed g => v -> g (Trie v)
value = inf . Value

tail :: Fixed g => Maybe (g (Trie v)) -> g (Trie v)
tail = inf . Tail where

string :: Fixed g => Maybe (g (Trie v)) -> BS.ByteString ->
    g (Trie v) -> g (Trie v)
string v k t = inf $ String v k t

fill :: Fixed g => BS.ByteString -> Maybe (g (Trie v)) -> g (Trie v) ->
    g (Trie v)
fill k x t = if BS.null k
    then t
    else string x k t

small :: Fixed g => Maybe (g (Trie v)) -> [(Word8, g (Trie v))]
    -> g (Trie v)
small v l = inf $ Small v l

big :: Fixed g => Maybe (g (Trie v)) ->
    Array Word8 (Maybe (g (Trie v)))
    -> g (Trie v)
big v l = inf $ Big v l

mut :: Fixed g => Maybe (g (Trie v)) -> M.Map Word8 (g (Trie v)) -> 
    g (Trie v)
mut v l = inf $ Mutable v l

bigThreshold :: Int
bigThreshold = 20

-- | 'freeze' takes a 'Trie' that has been mutated and creates a copy of it
-- that allows for faster lookups. This happens automatically for 'Trie's that
-- are serialized to a 'FixFile'. A 'Trie' will be automatically thawed on
-- any node that is modified.
freeze :: Fixed g => g (Trie v) -> g (Trie v)
freeze = cata (inf . freeze') where

freeze' :: Trie v a -> Trie v a
freeze' (Mutable a b) = if M.size b > bigThreshold
    then Big a $ array (minBound, maxBound) $ do
        i <- [minBound..maxBound]
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
lookupTrie a b = cata phi b a where
    term v k = guard (BS.null k) >> v >>= ($ k)
    phi (Value v) _ = return v
    phi (Tail v) k = term v k
    phi (String v s t) k = term v k <|> do
        let (_, lt, rt) = splitKey s k
        guard (BS.null lt)
        t rt
    phi (Small v l) k = term v k <|> do
        (c, r) <- BS.uncons k
        t <- lookup c l
        t r
    phi (Big v l) k = term v k <|> do
        (c, r) <- BS.uncons k
        t <- l ! c
        t r
    phi (Mutable v l) k = term v k <|> do
        (c, r) <- BS.uncons k
        t <- M.lookup c l
        t r

-- | 'Transaction' version of 'lookupTrie'.
lookupTrieT :: Serialize v =>
    BS.ByteString -> Transaction (Ref (Trie v)) s (Maybe v)
lookupTrieT k = lookupT (lookupTrie k)

splitKey :: BS.ByteString -> BS.ByteString ->
    (BS.ByteString, BS.ByteString, BS.ByteString)
splitKey x y = case (BS.uncons x, BS.uncons y) of
    (Nothing, Nothing) -> (BS.empty, BS.empty, BS.empty)
    (Nothing, Just _) -> (BS.empty, x, y)
    (Just _, Nothing) -> (BS.empty, x, y)
    (Just (xc, xs), Just (yc, ys)) -> if xc == yc
        then let (shared, xt, yt) = splitKey xs ys
            in (BS.cons xc shared, xt, yt)
        else (BS.empty, x, y)

-- | Insert a value into a trie for the given 'ByteString' key.
insertTrie :: Fixed g => BS.ByteString -> v -> g (Trie v) -> g (Trie v)
insertTrie a b c = para phi c a where
    val = Just $ value b
    valTail = tail val
    phi (Value _) _ = error "Badly formed Trie"
    phi (Tail vm) k = fill k (fmap fst vm) valTail
    phi (String vm s (tn, ta)) k
        | BS.null k = string val s tn
        | otherwise =
            let (sh, lt, rt) = splitKey k s
                Just (lh, ls) = BS.uncons lt
                Just (rh, rs) = BS.uncons rt
                vm' = fmap fst vm
            in case (BS.null sh, BS.null lt, BS.null rt) of
                (True, False, False) -> mut vm' $ M.fromList
                    [(lh, fill ls Nothing valTail), (rh, fill rs Nothing tn)]
                (True, _, _) -> error "Invalid Key Split"
                (_, False, False) -> string vm' sh $ mut Nothing $ M.fromList
                    [(lh, fill ls Nothing valTail), (rh, fill rs Nothing tn)]
                (_, True, False) -> string vm' sh $ string val rt tn
                (_, False, True) -> string vm' sh $ ta lt
                (_, True, True) -> string vm' s $ ta lt
    phi x@(Big _ t) k
        | BS.null k = big val (fmap (fmap fst) t)
        | otherwise = phi (thaw x) k
    phi x@(Small _ t) k
        | BS.null k = small val (fmap (fmap fst) t)
        | otherwise = phi (thaw x) k
    phi (Mutable vm m) k = case BS.uncons k of
        Nothing -> mut val (fmap fst m)
        Just (kh, kt) -> mut (fmap fst vm) $ case M.lookup kh m of
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
    phi (Value _) _ = error "Invalid Trie"
    phi (Tail _) k = if BS.null k
        then Deleted True empty Nothing
        else NoDelete
    phi (String vm s (tn, ta)) k
        | BS.null k = if isJust vm
            then Deleted False (string Nothing s tn) (Just (s, tn))
            else NoDelete
    
        | otherwise =
            let (_, lt, rt) = splitKey k s
                ta' = ta lt
                vm' = fmap fst vm
            in if BS.null rt
                then case ta' of
                    NoDelete -> NoDelete
                    Deleted True _ _ -> if isNothing vm'
                        then Deleted True empty Nothing
                        else Deleted False (tail vm') Nothing
                    Deleted False tn' (Just (b', tn'')) ->
                        Deleted False (string vm' s tn') $
                            Just (BS.append s b', tn'')
                    Deleted False tn' Nothing ->
                        Deleted False (string vm' s tn') Nothing
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
                        mut' = mut vm' ts'
                        vm' = fmap fst vm
                    in case M.size ts' of
                        0 -> if isNothing vm'
                            then Deleted True empty Nothing
                            else Deleted False (tail vm') Nothing
                        _ -> Deleted False mut' Nothing
                Deleted False dt _ ->
                    let ts' = M.insert kh dt $ fmap fst ts
                        mut' = mut vm' ts'
                        vm' = fmap fst vm
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
    phi (Value v) _ k' l = (k',v):l
    phi (Tail vm) k k' l = maybe l (\va -> va k k' l) (guard (BS.null k) >> vm)
    phi (String vm s ta) k k' l =
        let (_, lt, rt) = splitKey k s
            f l' = maybe l' (\va -> va k k' l') (guard (BS.null k) >> vm)
        in if BS.null lt || BS.null rt
            then f $ ta lt (BS.append k' s) l 
            else f l
    phi (Small vm ts) k k' l  = 
        let f l' = maybe l' (\va -> va k k' l') (guard (BS.null k) >> vm)
        in case BS.uncons k of
            Nothing -> ($ l) . (f .) . Prelude.foldr (.) id $ do
                (i, r) <- ts
                return $ r BS.empty (BS.snoc k' i)
            Just (i, k'') -> case lookup i ts of
                Nothing -> l
                Just r -> r k'' (BS.snoc k' i) l
    phi (Big vm ts) k k' l  = 
        let f l' = maybe l' (\va -> va k k' l') (guard (BS.null k) >> vm)
        in case BS.uncons k of
            Nothing -> ($ l) . (f .) . Prelude.foldr (.) id $ do
                (i, Just r) <- assocs ts
                return $ r BS.empty (BS.snoc k' i)
            Just (i, k'') -> case ts ! i of
                Nothing -> l
                Just r -> r k'' (BS.snoc k' i) l
    phi (Mutable vm ts) k k' l  = 
        let f l' = maybe l' (\va -> va k k' l') (guard (BS.null k) >> vm)
        in case BS.uncons k of
            Nothing -> ($ l) . (f .) . Prelude.foldr (.) id $ do
                (i, r) <- M.toList ts
                return $ r BS.empty (BS.snoc k' i)
            Just (i, k'') -> case M.lookup i ts of
                Nothing -> l
                Just r -> r k'' (BS.snoc k' i) l

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
        phi (Value v) = value (f v)
        phi (Tail v) = tail v
        phi (String v b t) = string v b t
        phi (Small v ts) = small v ts
        phi (Big v ts) = big v ts
        phi (Mutable v ts) = mut v ts

instance FixedFoldable (Trie v) where
    foldMapF f = maybe mempty id . cata phi where
        phi (Value v) = Just (f v)
        phi (Tail v) = join v
        phi (String v _ t) = join v <> t
        phi (Small v l) = join v <> mconcat (snd <$> l)
        phi (Big v a) = join v <> mconcat (join <$> elems a)
        phi (Mutable v m) = join v <> foldMap id m

instance FixedTraversable (Trie v) where
    traverseF f = cata phi where
        mapply Nothing = pure Nothing
        mapply (Just v) = Just <$> v
        phi (Value v) = value <$> f v
        phi (Tail v) = tail <$> mapply v
        phi (String v b a) = string <$> mapply v <*> pure b <*> a
        phi (Small v l) = small <$> mapply v <*>
            traverse (\(w, a) -> (w,) <$> a) l
        phi (Big v a) = big <$> mapply v <*> traverse mapply a
        phi (Mutable v m) = mut <$> mapply v <*> traverse id m


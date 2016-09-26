{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable,
    DeriveDataTypeable, DataKinds, KindSignatures, TypeFamilies,
    TupleSections, DefaultSignatures #-}

{- |
    Module      :  Data.FixFile.BTree.Light
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    This is a BTree data type that can be used with 'FixFile'. It can be used
    as a key-value store where the same key can correspond to multiple values.
    It supports logarithmic insert, lookup, and delete operations. This BTree
    embeds values in the leaf nodes instead of providing them with distinct
    leaf nodes. It is not recommended for use with large values.
-}
module Data.FixFile.BTree.Light (BTree
                                ,createBTreeFile
                                ,openBTreeFile
                                ,depth
                                ,insertBTree
                                ,insertBTreeT
                                ,lookupBTree
                                ,lookupBTreeT
                                ,filterBTree
                                ,filterBTreeT
                                ,deleteBTree
                                ,deleteBTreeT
                                ,partitionBTree
                                ,toListBTree
                                ,fromListBTree
                                ) where

import Control.Monad.Writer
import Data.Serialize
import Data.Dynamic
import Data.Word
import qualified Data.Vector as V
import GHC.Generics
import GHC.TypeLits

import Data.FixFile

{- |
    A 'Fixed' @('BTree' n k v)@ stores a BTree of key/value pairs.
    'n' should be a 'Nat' and will be the maximum number of elements in each
    branch of the 'BTree'.
-}
data BTree (n :: Nat) k v a =
    Empty
  | Node Word32 (Either (V.Vector (k, v)) (V.Vector (k, a)))
    deriving (Read, Show, Generic, Functor, Foldable, Traversable, Typeable)

instance Null1 (BTree n k v) where
    empty1 = Empty
    null1 Empty = True
    null1 _ = False

instance (Serialize k, Serialize v, Serialize a) => Serialize (BTree n k v a) where
    put Empty = putWord8 0x45
    put (Node _ (Left vec)) = do
        putWord8 0x4c
        put (V.length vec)
        mapM_ put vec
    put (Node d (Right vec)) = do
        putWord8 0x52
        put d
        put (V.length vec)
        mapM_ put vec
    get = getWord8 >>= getBTree where
        getBTree 0x45 = return Empty
        getBTree 0x4c = (Node 1 . Left) <$>
            (get >>= \n -> V.replicateM n get)
        getBTree 0x52 = Node <$> get <*>
            (get >>= \n -> Right <$> V.replicateM n get)
        getBTree _ = error "Can't decode into BTree"

-- | Compute the depth of a 'BTree' 
depth :: Fixed g => g (BTree n k v) -> Int
depth = dep . outf where
    dep Empty = 0
    dep (Node d _) = fromIntegral d

node :: Fixed g => Word32 -> V.Vector (k, g (BTree n k v)) -> g (BTree n k v)
node d = inf . Node d . Right

leaf :: Fixed g => V.Vector (k, v) -> g (BTree n k v)
leaf = inf . Node 1 . Left

-- | Create a 'FixFile' storing a @('BTree' k v)@.
--   The initial value is 'empty'.
createBTreeFile :: (Typeable n, Serialize k, Typeable k, Serialize v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (BTree n k v)))
createBTreeFile fp = createFixFile (Ref empty) fp

-- | Open a 'FixFile' storing a @('BTree' k v)@.
openBTreeFile :: (Serialize k, Typeable k, Serialize v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (BTree n k v)))
openBTreeFile = openFixFile

treeNodeSize :: KnownNat n => g (BTree n k v) -> Integer
treeNodeSize = validate . natVal . p where
    p :: g (BTree n k v) -> Proxy n
    p _ = Proxy
    validate n = if n < 2
        then error "BTree branch size must be > 1."
        else n

splitRange :: Ord k => k -> V.Vector (k, v) -> (Int, Int)
splitRange k vec = V.foldl' rangeSum (0,0) vec where
    rangeSum t@(i1, i2) (k', _)
        | k' < k = (i1 `seq` i1 + 1, i2 `seq` i2 + 1)
        | k == k' = (i1, i2 `seq` i2 + 1)
        | otherwise = t

split3 :: (Int, Int) -> V.Vector a -> (V.Vector a, V.Vector a, V.Vector a)
split3 (s1, s2) vec = (vl, vm, vr) where
    (vm',vr) = V.splitAt s2 vec
    (vl, vm) = V.splitAt s1 vm'

data Insert n k v g =
    Inserted k (g (BTree n k v))
  | Split Word32 (k, (g (BTree n k v))) (k, (g (BTree n k v)))

-- | Insert the value 'v' with the key 'k' into a 'Fixed' @('BTree' k v)@.
insertBTree :: (KnownNat n, Ord k, Fixed g) => k -> v -> g (BTree n k v) ->
    g (BTree n k v)
insertBTree k v t = merge . para phi $ t where
    merge (Inserted _ x) = x
    merge (Split d lt rt) = node (d + 1) $ V.fromList [lt, rt]
    nodeSize = fromIntegral $ treeNodeSize t

    newNode d c cs
        | c > nodeSize =
            let (l, r) = V.splitAt (nodeSize `div` 2) cs
                l' = V.force l
                r' = V.force r
                mini = fst . V.head
            in Split d (mini l, node d l') (mini r, node d r')
        | otherwise = 
            Inserted (fst $ V.head cs) (node d cs)

    newLeaf c cs
        | c > nodeSize =
            let (l, r) = V.splitAt (nodeSize `div` 2) cs
                l' = V.force l
                r' = V.force r
                mini = fst . V.head
            in Split 1 (mini l, leaf l') (mini r, leaf r')
        | otherwise =
            Inserted (fst $ V.head cs) (leaf cs)
            
    nodes = fmap (\(a,(b,_)) -> (a, b))

    phi Empty = Inserted k $ leaf $ V.singleton (k, v)

    phi (Node 1 (Left vec)) =
        let (lt, eq, gt) = split3 (splitRange k vec) vec
            newSize = 1 + V.length vec
        in newLeaf newSize (V.concat [lt, eq, V.singleton (k, v), gt])
    phi (Node _ (Left _)) = error "Malformed Leaf"

    phi (Node d (Right vec)) = 
        let (lt, eq, gt) = split3 (splitRange k vec) vec
            lt' = nodes lt
            eq' = nodes eq
            gt' = nodes gt
            currSize = V.length vec
            (c, csf) = case (V.null eq, V.null lt) of
                (False, _) ->
                    (V.last eq, \n -> V.concat [lt', V.init eq', n, gt'])
                (_, False) ->
                    (V.last lt, \n -> V.concat [V.init lt', n, gt'])
                _ -> (V.head gt, \n -> V.concat [n, V.tail gt'])
        in case snd (snd c) of
            Inserted k' n' ->
                newNode d currSize (csf $ V.singleton (k', n'))
            Split _ ls rs ->
                newNode d (currSize + 1) (csf $ V.fromList [ls, rs])

-- | 'Transaction' version of 'insertBTree'.
insertBTreeT :: (KnownNat n, Ord k, Serialize k, Serialize v) => k -> v ->
    Transaction (Ref (BTree n k v)) s ()
insertBTreeT k v = alterT (insertBTree k v)

-- | Lookup the values stored for the key 'k' in a 'Fixed' @('BTree' k v)@.
lookupBTree :: (Ord k, Fixed g) => k -> g (BTree n k v) -> [v]
lookupBTree k = ($ []) . cata phi where
    phi Empty l = l

    phi (Node 1 (Left vec)) l =
        let (_, eq, _) = split3 (splitRange k vec) vec
        in V.foldr ((:) . snd) l eq
    phi (Node _ (Left _)) _ = error "Malformed Leaf"

    phi (Node _ (Right vec)) l =
        let (_, eq, _) = split3 (s1 - 1, s2) vec
            (s1, s2) = splitRange k vec
        in V.foldr (($) . snd) l eq

-- | 'Transaction' version of 'lookupBTree'.
lookupBTreeT :: (Ord k, Serialize k, Serialize v) => k ->
    Transaction (Ref (BTree n k v)) s [v]
lookupBTreeT k = lookupT (lookupBTree k)

data Deleted n k v g =
    Deleted k (g (BTree n k v))
  | AllDeleted
  | UnChanged

-- | Filter items from a 'Fixed' @('BTree' k v)@ for a key 'k' that match
--   the predicate.
filterBTree :: (Ord k, Fixed g) => k -> (v -> Bool) ->
    g (BTree n k v) -> g (BTree n k v)
filterBTree k f t = deleted' . para phi $ t where
    deleted' UnChanged = t
    deleted' AllDeleted = empty
    deleted' (Deleted _ x) = x

    nodes = fmap (\(a, (b, _)) -> (a, b))

    phi Empty = UnChanged

    phi (Node 1 (Left vec)) =
        let (lt, eq, gt) = split3 (splitRange k vec) vec
            eq' = V.filter (f . snd) eq
            vec' = V.concat [lt, eq', gt]
            mink = fst (V.head vec')
        in case (V.null vec', V.length eq /= V.length eq') of
            (True, _) -> AllDeleted
            (_, False) -> UnChanged
            _ -> Deleted mink $ leaf vec'
    phi (Node _ (Left _)) = error "Malformed Leaf"

    phi (Node d (Right vec)) =
        let (lt, eq, gt) = split3 (s1 - 1, s2) vec
            (s1, s2) = splitRange k vec
            lt' = nodes lt
            gt' = nodes gt
            (eq',del) = runWriter $ do
                res <- flip V.filterM eq $ \(_, (_, a)) ->
                    case a of
                        UnChanged -> return True
                        Deleted _ _ -> tell (Any True) >> return True
                        AllDeleted -> tell (Any True) >> return False
                forM res $ \(nk, (n, a)) -> do
                    case a of
                        UnChanged -> return (nk, n)
                        Deleted nk' a' -> return (nk', a')
                        AllDeleted -> error "AllDeleted?" -- should be unreachable
            vec' = V.concat [lt', eq', gt']
            mink = fst (V.head vec')
        in case (V.null vec', getAny del) of
            (True, _) -> AllDeleted
            (_, False) -> UnChanged
            _ -> Deleted mink $ node d vec'

-- | 'Transaction' version of 'filterBTree'.
filterBTreeT :: (Ord k, Serialize k, Serialize v) => k -> (v -> Bool) ->
    Transaction (Ref (BTree n k v)) s ()
filterBTreeT k f = alterT (filterBTree k f)

-- | Delete all items for key 'k' from the 'Fixed' @('BTree' k v)@.
deleteBTree :: (Ord k, Fixed g) => k -> g (BTree n k v) -> g (BTree n k v)
deleteBTree k = filterBTree k (const False)

-- | 'Transaction' version of 'deleteBTree'.
deleteBTreeT :: (Ord k, Serialize k, Serialize v) => k ->
    Transaction (Ref (BTree n k v)) s ()
deleteBTreeT k = alterT (deleteBTree k)

data SkewDir = L | R

data Parted n k v g =
    NoPart SkewDir
  | Parted (k, (g (BTree n k v))) (k, (g (BTree n k v)))

-- | Split a 'BTree' into two two 'BTree's with keys < 'k' and keys > 'k'.
partitionBTree :: (Ord k, Fixed g) => k -> g (BTree n k v) ->
    (g (BTree n k v), g (BTree n k v))
partitionBTree k t = parted . para phi $ t where
    parted (NoPart L) = (t, empty)
    parted (NoPart R) = (empty, t)
    parted (Parted (_, l) (_, r)) = (l, r)

    nodes = fmap (\(a, (b, _)) -> (a, b))

    phi Empty = NoPart L

    phi (Node 1 (Left vec)) =
        let (lt, gte) = V.splitAt s1 vec
            (s1, _) = splitRange k vec
            minkl = fst (V.head lt)
            minkr = fst (V.head gte)
        in case (V.null lt, V.null gte) of
            (True, _) -> NoPart R
            (_, True) -> NoPart L
            _ -> Parted (minkl, leaf lt) (minkr, leaf gte)
    phi (Node _ (Left _)) = error "Malformed Leaf"

    phi (Node d (Right vec)) = 
        let (lt, eq, gt) = split3 (s1 - 1, s1) vec
            (s1, _) = splitRange k vec
            lt' = nodes lt
            eq' = nodes eq
            gt' = nodes gt
            minkl = if V.null lt then fst (V.head eq) else fst (V.head lt)
            (_,(_,eqa)) = V.head eq
        in case (V.null eq, V.null gt, eqa) of
            (True, _, _) -> NoPart R
            (_, True, NoPart L) -> NoPart L
            (_, _, NoPart R) -> error "Malformed BTree"
            (_, _, NoPart L) ->
                let minkr = fst (V.head gt')
                    ln = node d (V.concat [lt', eq'])
                    rn = node d (V.force gt')
                in Parted (minkl, ln) (minkr, rn)
            (_, _, Parted tl tr@(prk, _)) ->
                let ln = node d (V.concat [lt', V.singleton tl])
                    rn = node d (V.concat [V.singleton tr, gt'])
                in Parted (minkl, ln) (prk, rn)

-- | Turn a 'Fixed' @('BTree' k v)@ into a list of key value tuples.
toListBTree :: (Ord k, Fixed g) => g (BTree n k v) -> [(k,v)]
toListBTree t = cata phi t [] where
    phi Empty = id

    phi (Node 1 (Left vec)) = foldMap (:) vec
    phi (Node _ (Left _)) = error "Malformed Leaf"

    phi (Node _ (Right vec)) = foldMap snd vec

-- | Turn a list of key value tuples into a 'Fixed' @('BTree' k v)@.
fromListBTree :: (KnownNat n, Ord k, Fixed g) => [(k,v)] -> g (BTree n k v)
fromListBTree = foldr (uncurry insertBTree) empty

instance FixedAlg (BTree n k v) where
    type Alg (BTree n k v) = v

instance FixedSub (BTree n k v) where
    type Sub (BTree n k v) v v' = BTree n k v'

instance FixedFunctor (BTree n k v) where
    fmapF f = cata phi where
        phi Empty = empty
        phi (Node 1 (Left vec)) = leaf $ fmap (fmap f) vec
        phi (Node _ (Left _)) = error "Malformed Leaf"
        phi (Node c (Right vec)) = node c vec

instance FixedFoldable (BTree n k v) where
    foldMapF f = cata phi where
        phi Empty = mempty
        phi (Node 1 (Left vec)) = foldMap (f . snd) vec
        phi (Node _ (Left _)) = error "Malformed Leaf"
        phi (Node _ (Right vec)) = foldMap snd vec

instance FixedTraversable (BTree n k v) where
    traverseF f = cata phi where
        phi Empty = pure empty
        phi (Node 1 (Left vec)) = leaf <$> traverse (\(w, a) -> (w,) <$> f a) vec 
        phi (Node _ (Left _)) = error "Malformed Leaf"
        phi (Node c (Right vec)) = node c <$> traverse (\(w, a) -> (w,) <$> a) vec 


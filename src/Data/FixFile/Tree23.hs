{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable,
    KindSignatures, TypeFamilies, FlexibleInstances, FlexibleContexts,
    DeriveDataTypeable #-}

{- |
    Module      :  Data.FixFile.Tree23
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    This is an implementation of a Two-Three Tree data structure that can be
    used with 'FixFile'. It has two interfaces that are
-}
module Data.FixFile.Tree23 (Tree23
                           ,TreeD
                           ,empty
                           ,null
                           ,size
                           ,depth
                           -- | * Set
                           ,Set
                           ,createSetFile
                           ,openSetFile
                           ,insertSet
                           ,lookupSet
                           ,deleteSet
                           ,partitionSet
                           ,toListSet
                           ,fromListSet
                           ,insertSetT
                           ,lookupSetT
                           ,deleteSetT
                           ,partitionSetT
                           -- | * Map
                           ,Map
                           ,createMapFile
                           ,openMapFile
                           ,insertMap
                           ,lookupMap
                           ,deleteMap
                           ,partitionMap
                           ,alterMap
                           ,mapMap
                           ,toListMap
                           ,fromListMap
                           ,insertMapT
                           ,lookupMapT
                           ,deleteMapT
                           ,partitionMapT
                           ,alterMapT
                           ,keysMap
                           ,valuesMap
                           ,partitionTree23
                           ) where

import Prelude hiding (null)

import Data.Dynamic
import Data.Binary
import Data.Maybe
import GHC.Generics
 
import Data.FixFile

data Tree23F k v a = 
    Empty
  | Leaf k v
  | Two a k a
  | Three a k a k a
  deriving (Read, Show, Eq, Ord, Generic, Functor, Foldable, Traversable,
            Typeable)

{- |
    'Fixed' @('TreeD' d)@ represents a Two-Three tree. The data type 'd' should
    have data families for it's key and value. These data families are not
    exported from the module. As a result, the only valid types for 'd' are
    @('Set' k)@ as defined here or @('Map' k v)@, also defined here.
-}
type TreeD d = Tree23F (TreeKey d) (TreeValue d)

-- | Type synonym for the 'Fixed' representation of a Two-Three Tree.
type Tree23 g d = g (TreeD d)

data family TreeKey d

data family TreeValue d

instance (Binary a, Binary (TreeKey d), Binary (TreeValue d)) =>
    Binary (Tree23F (TreeKey d) (TreeValue d) a)

-- | An empty 'Fixed' 'Tree23'.
empty :: Fixed g => Tree23 g d
empty = inf Empty

leaf :: Fixed g => TreeKey d -> TreeValue d -> Tree23 g d
leaf k v = inf $ Leaf k v

two :: Fixed g => Tree23 g d -> TreeKey d ->
    Tree23 g d -> Tree23 g d
two l v r = inf $ Two l v r

three :: Fixed g => Tree23 g d -> TreeKey d -> Tree23 g d ->
    TreeKey d -> Tree23 g d -> Tree23 g d
three l t1 m t2 r =
    inf $ Three l t1 m t2 r

-- | Predicate that returns true if there are no items in the 'Tree23'.
null :: Fixed g => Tree23 g d -> Bool
null = null' . outf where
    null' Empty = True
    null' _ = False

-- | Number of entries in @('Tree23' g d)@.
size :: Fixed g => Tree23 g d -> Int
size = cata phi where
    phi Empty = 0
    phi (Leaf _ _) = 1
    phi (Two l _ r) = l + r
    phi (Three l _ m _ r) = l + m + r

-- | The depth of @('Tree23' g d)@. @0@ represents en empty Tree.
depth :: Fixed g => Tree23 g d -> Int
depth = cata phi where
    phi Empty = 0
    phi (Leaf _ _) = 1
    phi (Two l _ _) = l + 1
    phi (Three l _ _ _ _) = l + 1

-- | A 'Set' of 'k' represented as a Two-Three Tree.
data Set k

newtype instance TreeKey (Set k) = SK k
    deriving (Read, Show, Eq, Ord, Generic, Typeable)

data instance TreeValue (Set k) = SV
    deriving (Read, Show, Eq, Ord, Generic, Typeable)

instance Binary k => Binary (TreeKey (Set k))

instance Binary (TreeValue (Set k))

-- | Insert an item into a set.
insertSet :: (Fixed g, Ord k) => k -> Tree23 g (Set k) -> Tree23 g (Set k)
insertSet k = alterTree23 (SK k) (maybe (Just $ Just SV) (const Nothing))

-- | Lookup an item in a set.
lookupSet :: (Fixed g, Ord k) => k -> Tree23 g (Set k) -> Bool
lookupSet k = isJust . lookupTree23 (SK k)

-- | Delete an item from a set.
deleteSet :: (Fixed g, Ord k) => k -> Tree23 g (Set k) -> Tree23 g (Set k)
deleteSet k = alterTree23 (SK k) (const $ Just Nothing)

-- | Split a set into sets of items < k and >= k
partitionSet :: (Fixed g, Ord k) => k -> Tree23 g (Set k) ->
    (Tree23 g (Set k), Tree23 g (Set k))
partitionSet k = partitionTree23 (SK k)

-- | Convert a set into a list of items.
toListSet :: (Fixed g, Ord k) => Tree23 g (Set k) -> [k]
toListSet = ($ []) . cata phi where
    phi Empty xs = xs
    phi (Leaf (SK k) _) xs = k:xs
    phi (Two la _ ra) xs = la . ra $ xs
    phi (Three la _ ma _ ra) xs = la . ma . ra $ xs

-- | Convert a list of items into a set.
fromListSet :: (Fixed g, Ord k) => [k] -> Tree23 g (Set k)
fromListSet = Prelude.foldr insertSet empty

-- | Create a 'FixFile' for storing a set of items.
createSetFile :: (Binary k, Typeable k) =>
    FilePath -> IO (FixFile (Ref (TreeD (Set k))))
createSetFile fp = createFixFile (Ref empty) fp

-- | Open a 'FixFile' for storing a set of items.
openSetFile :: (Binary k, Typeable k) =>
    FilePath ->IO (FixFile (Ref (TreeD (Set k))))
openSetFile fp = openFixFile fp

-- | 'Transaction' version of 'insertSet'.
insertSetT :: (Binary k, Ord k) =>
    k -> Transaction (Ref (TreeD (Set k))) s ()
insertSetT k = alterT (insertSet k) 

-- | 'FTransaction' version of 'lookupSet'.
lookupSetT :: (Binary k, Ord k) =>
    k -> Transaction (Ref (TreeD (Set k))) s Bool
lookupSetT k = lookupT (lookupSet k)

-- | 'FTransaction' version of 'deleteSet'.
deleteSetT :: (Binary k, Ord k) =>
    k -> Transaction (Ref (TreeD (Set k))) s ()
deleteSetT k = alterT (deleteSet k)

-- | 'Transaction' version of 'partitionSet'.
partitionSetT :: (Binary k, Ord k, f ~ TreeD (Set k)) => k ->
    Transaction (Ref f) s (Stored s f, Stored s f)
partitionSetT k = lookupT (partitionSet k)

-- | A 'Map' of keys 'k' to values 'v' represented as a Two-Three Tree.
data Map k v

newtype instance TreeKey (Map k v) = MK k
    deriving (Read, Show, Eq, Ord, Generic, Typeable)

newtype instance TreeValue (Map k v) = MV { fromMV :: v }
    deriving (Read, Show, Eq, Ord, Generic, Typeable)

instance Binary k => Binary (TreeKey (Map k v))

instance Binary v => Binary (TreeValue (Map k v))

-- | Insert value 'v' into a map for key 'k'. Any existing value is replaced.
insertMap :: (Fixed g, Ord k) => k -> v -> Tree23 g (Map k v) ->
    Tree23 g (Map k v)
insertMap k v = alterTree23 (MK k) (const . Just . Just $ MV v)

-- | Lookup an item in a map corresponding to key 'k'.
lookupMap :: (Fixed g, Ord k) => k -> Tree23 g (Map k v) -> Maybe v
lookupMap k = fmap toV . lookupTree23 (MK k) where
    toV (MV v) = v

-- | Delete an item from a map at key 'k'.
deleteMap :: (Fixed g, Ord k) => k -> Tree23 g (Map k v) -> Tree23 g (Map k v)
deleteMap k = alterTree23 (MK k) (const . Just $ Nothing)

-- | Apply a function to alter a Map at key 'k'. The function takes
--   @('Maybe' v)@ as an argument for any possible exiting value and returns
--   @Nothing@ to delete a value or @Just v@ to set a new value.
alterMap :: (Fixed g, Ord k) => k -> (Maybe v -> Maybe v) ->
    Tree23 g (Map k v) -> Tree23 g (Map k v)
alterMap k f = alterTree23 (MK k) (Just . fmap MV . f . fmap fromMV)

-- | Split a set into maps for keys < k and >= k
partitionMap :: (Fixed g, Ord k) => k -> Tree23 g (Map k v) ->
    (Tree23 g (Map k v), Tree23 g (Map k v))
partitionMap k = partitionTree23 (MK k)

-- | Convert a map into a list of key-value tuples.
toListMap :: (Fixed g, Ord k) => Tree23 g (Map k v) -> [(k,v)]
toListMap = ($ []) . cata phi where
    phi Empty xs = xs
    phi (Leaf (MK k) (MV v)) xs = (k,v):xs
    phi (Two la _ ra) xs = la . ra $ xs
    phi (Three la _ ma _ ra) xs = la . ma . ra $ xs

-- | Convert a lst of key-value tuples into a map.
fromListMap :: (Fixed g, Ord k) => [(k,v)] -> Tree23 g (Map k v)
fromListMap = Prelude.foldr (uncurry insertMap) empty

-- | Return the list of keys in a map.
keysMap :: (Fixed g, Ord k) => Tree23 g (Map k v) -> [k]
keysMap = fmap fst . toListMap

-- | Return a list of values in a map.
valuesMap :: (Fixed g, Ord k) => Tree23 g (Map k v) -> [v]
valuesMap = fmap snd . toListMap

-- | Map a function over a map. Because of the way Tree23 is implemented, it is
--   not possible to create a Functor instance to achieve this.
mapMap :: (Fixed g, Fixed h, Ord k) => (a -> b) -> Tree23 g (Map k a) ->
    Tree23 h (Map k b)
mapMap f = cata phi where
    phi Empty = empty
    phi (Leaf (MK k) (MV a)) = leaf (MK k) (MV (f a))
    phi (Two l (MK k) r) = two l (MK k) r
    phi (Three l (MK k1) m (MK k2) r) = three l (MK k1) m (MK k2) r

-- | Create a 'FixFile' of a Map.
createMapFile :: (Binary k, Typeable k, Binary v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (TreeD (Map k v))))
createMapFile fp = createFixFile (Ref empty) fp

-- | Open a 'FixFile' of a Map.
openMapFile :: (Binary k, Typeable k, Binary v, Typeable v) =>
    FilePath -> IO (FixFile (Ref (TreeD (Map k v))))
openMapFile fp = openFixFile fp

-- | 'Transaction' version of 'insertMap'.
insertMapT :: (Binary k, Binary v, Ord k) =>
    k -> v -> Transaction (Ref (TreeD (Map k v))) s ()
insertMapT k v = alterT (insertMap k v) 

-- | 'Transaction' version of 'lookupMap'.
lookupMapT :: (Binary k, Binary v, Ord k) =>
    k -> Transaction (Ref (TreeD (Map k v))) s (Maybe v)
lookupMapT k = lookupT (lookupMap k)

-- | 'Transaction' version of 'deleteMap'.
deleteMapT :: (Binary k, Binary v, Ord k) => k ->
    Transaction (Ref (TreeD (Map k v))) s ()
deleteMapT k = alterT (deleteMap k)

-- | 'Transaction' version of 'partitionMap'.
partitionMapT :: (Binary k, Ord k, Binary v, f ~ TreeD (Map k v)) => k ->
    Transaction (Ref f) s (Stored s f, Stored s f)
partitionMapT k = lookupT (partitionMap k)

-- | 'FTransaction' version of 'alterMap'.
alterMapT :: (Binary k, Binary v, Ord k) => k ->
    (Maybe v -> Maybe v) -> 
    Transaction (Ref (TreeD (Map k v))) s ()
alterMapT k f = alterT (alterMap k f)

-- lookup the value (if it exists) from a Fixed Tree23 for a given key.
lookupTree23 :: (Fixed g, Ord (TreeKey d)) => TreeKey d ->
    Tree23 g d -> Maybe (TreeValue d)
lookupTree23 k = cata phi where
    phi Empty = Nothing
    phi (Leaf k' v)
        | k == k' = Just v
        | otherwise = Nothing
    phi (Two la k' ra) =
        case compare k k' of
            LT -> la
            _ -> ra
    phi (Three la k1 ma k2 ra) =
        case (compare k k1, compare k k2) of
            (LT, _) -> la
            (_, LT) -> ma
            (_, _) -> ra

data Change g d =
    NoChange
  | Changed (Maybe (TreeKey d)) (Tree23 g d)
  | Unbalanced (Maybe (TreeKey d)) (Tree23 g d)
  | Hole
  | Split (Tree23 g d) (TreeKey d) (Tree23 g d)

-- So, this function is a bit overwhelming, but it does everything that to
-- handle all of the operations that modify a 2-3 tree.
--
-- The (TreeKey d) is the key where the modification should take place.
-- The function takes one argument which is Maybe the value stored in the
-- tree for the given key.
-- The function returns Nothing if no change is made to the tree, Just Nothing
-- if the value should be deleted from the tree, and Just v for the new value]
-- to be written to the tree.
alterTree23 :: (Fixed g, Ord (TreeKey d)) => TreeKey d ->
    (Maybe (TreeValue d) -> Maybe (Maybe (TreeValue d))) ->
    Tree23 g d -> Tree23 g d
alterTree23 k f t = processHead $ para phi t t where
    processHead NoChange = t
    processHead (Changed _ t') = t'
    processHead Hole = empty
    processHead (Unbalanced _ t') = t'
    processHead (Split lt d rt) = two lt d rt

    phi Empty _ = case f Nothing of
        Just (Just v) -> Changed Nothing $ leaf k v
        _ -> NoChange

    phi (Leaf k' v') n
        | k == k' = case f (Just v') of
            Nothing -> NoChange
            Just Nothing -> Hole
            Just (Just v) -> Changed Nothing $ leaf k' v
        | otherwise = case f Nothing of
            Nothing -> NoChange
            Just Nothing -> NoChange
            Just (Just v) -> if k < k'
                then Split (leaf k v) k' n
                else Split n k (leaf k v)

    phi (Two (ln, la) k' (rn, ra)) _
        | k < k' = case la ln of
            NoChange -> NoChange
            Changed nk la' ->
                Changed nk $ two la' k' rn
            Split la' k'' ma'->
                Changed Nothing $ three la' k'' ma' k' rn
            Hole -> Unbalanced (Just k') rn
            Unbalanced uk un -> case outf rn of
                Three ln' k1 mn' k2 rn' -> Changed uk $
                    two (two un k' ln') k1 (two mn' k2 rn')
                Two ln' k1 rn' -> Unbalanced uk $
                    three un k' ln' k1 rn'
                _ -> error "Invalid Tree23"
        | otherwise = case ra rn of
            NoChange -> NoChange
            Hole -> Unbalanced Nothing ln
            Changed dk dn -> Changed Nothing $
                two ln (maybe k' id dk) dn
            Split ma' k'' ra' -> Changed Nothing $
                three ln k' ma' k'' ra'
            Unbalanced uk un -> case outf ln of
                Three ln' k1 mn' k2 rn' -> Changed Nothing $
                    two (two ln' k1 mn') k2 (two rn' (maybe k' id uk) un)
                Two ln' k1 rn' -> Unbalanced Nothing $
                    three ln' k1 rn' (maybe k' id uk) un
                _ -> error "Invalid Tree23"

    phi (Three (ln, la) k1 (mn, ma) k2 (rn, ra)) _ 
        | k < k1 = case la ln of
            NoChange -> NoChange
            Hole -> Changed (Just k1) $ two mn k2 rn
            Changed dk dn -> Changed dk $
                three dn k1 mn k2 rn
            Split ln' k' rn' -> Split
                (two ln' k' rn') k1 (two mn k2 rn)
            Unbalanced uk un -> case outf mn of
                Three ln' k1' mn' k2' rn' -> Changed uk $
                    three (two un k1 ln') k1' (two mn' k2' rn') k2 rn
                Two ln' k1' rn' -> Changed uk $
                    two (three un k1 ln' k1' rn') k2 rn
                _ -> error "Invalid Tree23"

        | k < k2 = case ma mn of
            NoChange -> NoChange
            Hole -> Changed Nothing $ two ln k2 rn
            Changed dk dn -> Changed Nothing $
                three ln (maybe k1 id dk) dn k2 rn
            Split mn' k' rn' -> Split
                (two ln k1 mn') k' (two rn' k2 rn)
            Unbalanced uk un -> case outf rn of
                Three ln' k1' mn' k2' rn' -> Changed Nothing $
                    three ln (maybe k1 id uk) (two un k2 ln')
                        k1' (two mn' k2' rn')
                Two ln' k1' rn' -> Changed Nothing $
                    two ln (maybe k1 id uk) (three un k2 ln' k1' rn')
                _ -> error "Invalid Tree23"

        | otherwise = case ra rn of
            NoChange -> NoChange
            Hole -> Changed Nothing $ two ln k1 mn
            Changed dk dn -> Changed Nothing $
                three ln k1 mn (maybe k2 id dk) dn
            Split mn' k' rn' -> Split
                (two ln k1 mn) k2 (two mn' k' rn')
            Unbalanced uk un -> case outf mn of
                Three ln' k1' mn' k2' rn' -> Changed Nothing $
                    three ln k1 (two ln' k1' mn') k2'
                        (two rn' (maybe k2 id uk) un)
                Two ln' k1' rn' -> Changed Nothing $ two ln k1
                    (three ln' k1' rn' (maybe k2 id uk) un)
                _ -> error "Invalid Tree23"


data SkewDir = L | R

data Partition g d =
    NoPartition
  | Skew SkewDir
  | Split2 (Int, Tree23 g d) (Int, Tree23 g d)

merge :: (Fixed g, Ord (TreeKey d)) => Int -> Tree23 g d -> TreeKey d ->
    Int -> Tree23 g d -> (Int, Tree23 g d)
merge ld ln k rd rn
    | ld == rd = (ld + 1, two ln k rn)
    | ld < rd = case (rd - ld, outf rn) of
        (1, Two rln rk rrn) -> (rd, three ln k rln rk rrn)
        (1, Three rln rk1 rmn rk2 rrn) ->
            (rd + 1, two (two ln k rln) rk1 (two rmn rk2 rrn))
        (_, Two rln rk rrn) ->
            let (ld', rln') = merge ld ln k (rd - 1) rln
            in merge ld' rln' rk (rd - 1) rrn
        (_, Three rln rk1 rmn rk2 rrn) ->
            let (ld', rln') = merge ld ln k (rd - 1) rln
            in merge ld' rln' rk1 (rd - 1) (two rmn rk2 rrn)
        _ -> error "Malformed Tree23"
    | otherwise = case (ld - rd, outf ln) of
        (1, Two lln lk lrn) -> (ld, three lln lk lrn k rn)
        (1, Three lln lk1 lmn lk2 lrn) ->
            (ld + 1, two (two lln lk1 lmn) lk2 (two lrn k rn))
        (_, Two lln lk lrn) ->
            let (rd', lrn') = merge (ld - 1) lrn k rd rn
            in merge (ld - 1) lln lk rd' lrn'
        (_, Three lln lk1 lmn lk2 lrn) ->
            let (rd', lrn') = merge (ld - 1) lrn k rd rn
            in merge (ld - 1) (two lln lk1 lmn) lk2 rd' lrn'
        _ -> error "Malformed Tree23"

partitionTree23 :: (Fixed g, Ord (TreeKey d)) => TreeKey d ->
    Tree23 g d -> (Tree23 g d, Tree23 g d)
partitionTree23 k t = resp $ para phi t where
    resp NoPartition = (t, t)
    resp (Skew L) = (t, empty)
    resp (Skew R) = (empty, t)
    resp (Split2 (_, l) (_, r)) = (l, r)
    phi Empty = NoPartition
    phi (Leaf k' _) 
        | k' < k = Skew L
        | otherwise = Skew R
    phi (Two (ln, la) k' (rn, ra))
        | k' == k = Split2 (-1, ln) (-1, rn)
        | k' < k = case ra of
            Skew L -> Skew L
            Skew R -> Split2 (-1, ln) (-1, rn)
            Split2 (lbal, lv) (rbal, rv) ->
                Split2 (merge (-1) ln k' lbal lv) (rbal - 1, rv)
            _ -> error "Malformed Tree23"
        | otherwise = case la of
            Skew L -> Split2 (-1, ln) (-1, rn)
            Skew R -> Skew R
            Split2 (lbal, lv) (rbal, rv) ->
                Split2 (lbal - 1, lv) (merge rbal rv k' (-1) rn)
            _ -> error "Malformed Tree23"
    phi (Three (ln, la) k1 (mn, ma) k2 (rn, ra))
        | k1 == k = Split2 (-1, ln) (0, two mn k2 rn)
        | k2 == k = Split2 (0, two ln k1 mn) (-1, rn)
        | k2 < k = case ra of
            Skew L -> Skew L
            Skew R -> Split2 (0, two ln k1 mn) (-1, rn)
            Split2 (lbal, lv) (rbal, rv) ->
                Split2 (merge 0 (two ln k1 mn) k2 lbal lv) (rbal - 1, rv)
            _ -> error "Malformed Tree23"
        | k1 < k = case ma of
            Skew L -> Split2 (0, two ln k1 mn) (-1, rn)
            Skew R -> Split2 (-1, ln) (0, two mn k2 rn)
            Split2 (lbal, lv) (rbal, rv) ->
                Split2 (merge (-1) ln k1 lbal lv) (merge rbal rv k2 (-1) rn)
            _ -> error "Malformed Tree23"
        | otherwise = case la of
            Skew R -> Skew R
            Skew L -> Split2 (-1, ln) (0, two mn k2 rn)
            Split2 (lbal, lv) (rbal, rv) ->
                Split2 (lbal -1, lv) (merge rbal rv k2 0 (two mn k2 rn))
            _ -> error "Malformed Tree23"


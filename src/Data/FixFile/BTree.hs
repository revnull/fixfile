{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{- |
    Module      :  Data.FixFile.BTree
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    This is a BTree data type that can be used with 'FixFile'. It can be used
    as a key-value store where the same key can correspond to multiple values.
    It supports logarithmic insert, lookup, and delete operations.
-}
module Data.FixFile.BTree (BTree
                          ,createBTreeFile
                          ,openBTreeFile
                          ,empty
                          ,insertBTree
                          ,insertBTreeT
                          ,lookupBTree
                          ,lookupBTreeT
                          ,filterBTree
                          ,filterBTreeT
                          ,deleteBTree
                          ,deleteBTreeT
                          ,toListBTree
                          ,fromListBTree
                          ) where

import Data.FixFile.Fixed
import Data.FixFile
import Data.Binary
import Data.Foldable hiding (concat, foldr)
import Data.Traversable
import GHC.Generics
import Data.Array

{- |
    A 'Fixed' @('BTree' k v)@ stores a BTree of key/value pairs.
-}
data BTree k v a =
    Empty
  | Value v
  | Node Word32 (Array Int (k, a))
    deriving (Read, Show, Generic, Functor, Foldable, Traversable)

instance (Binary k, Binary v, Binary a) => Binary (BTree k v a)

-- | An empty 'BTree' 
empty :: Fixed g => g (BTree k v)
empty = inf Empty

value :: Fixed g => v -> g (BTree k v)
value = inf . Value

node :: Fixed g => Word32 -> Array Int (k, g (BTree k v)) -> g (BTree k v)
node d = inf . Node d

-- | Create a 'FixFile' storing a @('BTree' k v)@.
--   The initial value is 'empty'.
createBTreeFile :: (Binary k, Binary v) => FilePath -> IO (FixFile (BTree k v))
createBTreeFile fp = createFixFile empty fp

-- | Open a 'FixFile' storing a @('BTree' k v)@.
openBTreeFile :: (Binary k, Binary v) => FilePath -> IO (FixFile (BTree k v))
openBTreeFile = openFixFile

nodeSize :: Integral i => i
nodeSize = 32

lookupPos :: (Ord k) => Bool -> k -> Array Int (k, v) ->
    (Int, [(k, v)], (k, v), [(k, v)])
lookupPos ff k arr = result . findFirst . uncurry binary $ bounds arr where
    result i =
        let (a, b:c) = splitAt i $ elems arr
        in (i, a, b, c)
    lookupi = fst . (arr !)
    findFirst = if ff then findFirst' else id
    findFirst' 0 = 0
    findFirst' i = if lookupi (i - 1) == k
        then findFirst' (i - 1)
        else i
    binary mini maxi = 
        let avg = (maxi + mini) `div` 2
            avgi = lookupi avg
        in case (maxi - mini <= 1, compare k avgi) of 
            (True, _) -> if lookupi maxi <= k then maxi else mini
            (_, EQ) -> avg
            (_, LT) -> binary mini (avg - 1)
            (_, _) -> binary avg maxi

splitRange :: (Ord k) => k -> Array Int (k, v) ->
    ([(k,v)], [(k,v)], [(k,v)])
splitRange k = uncurry splitMax . splitMin id Nothing . elems where
    splitMin f Nothing [] = (f [], [])
    splitMin f (Just t) [] = (f [], [t])
    splitMin f Nothing xl@(xt@(xk,_):xs) = case compare xk k of
        LT -> splitMin f (Just xt) xs
        _ -> (f [], xl)
    splitMin f (Just t) xl@(xt@(xk,_):xs) = case compare xk k of
        LT -> splitMin (f . (t:)) (Just xt) xs
        _ -> (f [], t:xl)
    splitMax p xs = 
        let (c, n) = splitMax' id xs
        in (p, c, n)
    splitMax' f [] = (f [], [])
    splitMax' f xl@(xt@(xk,_):xs) = case compare xk k of
        GT -> (f [], xl)
        _ -> splitMax' (f . (xt:)) xs

data Insert k v g =
    Inserted k (g (BTree k v))
  | Split Word32 (k, (g (BTree k v))) (k, (g (BTree k v)))

-- | Insert the value 'v' with the key 'k' into a 'Fixed' @('BTree' k v)@.
insertBTree :: (Ord k, Fixed g) => k -> v -> g (BTree k v) -> g (BTree k v)
insertBTree k v = merge . para phi where
    merge (Inserted _ x) = x
    merge (Split d lt rt) = node (d + 1) $ array (0, 1)
        [(0, lt), (1, rt)]
    
    newNode d c ls = if c > nodeSize
        then
            let (l, r) = splitAt half ls
                half = nodeSize `div` 2
                half' = c - half
                mini = fst . head
            in Split d (mini l, node d $ array (0, half - 1) $ zip [0..] l)
                (mini r, node d $ array (0, half' - 1) $ zip [0..] r)
        else Inserted (fst $ head ls) (node d $ array (0, c-1) $ zip [0..] ls)

    children xs = [(i, x) | (i, (x, _)) <- xs]

    phi Empty = Inserted k $ node 0 $ array (0,0) [(0, (k, value v))]
    phi (Value _) = error "insertBTree phi Value error"
    phi (Node 0 a) =
        let (_, p, (kc, (km, _)), n) = lookupPos False k a
            newSize = (2+) . snd . bounds $ a
        in if kc <= k
            then newNode 0 newSize $
                children p ++ [(kc, km), (k, value v)] ++ children n
            else newNode 0 newSize $
                children p ++ [(k, value v), (kc, km)] ++ children n
    phi (Node d a) =
        let (_, p, (_, (_, ka)), n) = lookupPos False k a
            newSize = 1 + currSize
            currSize = (1+) . snd . bounds $ a
        in case ka of
            Inserted k' n' -> newNode d currSize $
                children p ++ (k', n'):children n
            Split _ lt rt -> newNode d newSize $
                children p ++ [lt, rt] ++ children n

-- | 'Transaction' version of 'insertBTree'.
insertBTreeT :: (Ord k, Binary k, Binary v) => k -> v ->
    Transaction (BTree k v) (WT s) ()
insertBTreeT k v = alterT (insertBTree k v)

-- | Lookup the values stored for the key 'k' in a 'Fixed' @('BTree' k v)@.
lookupBTree :: (Ord k, Fixed g) => k -> g (BTree k v) -> [v]
lookupBTree k = ($ []) . cata phi where
    phi Empty l = l
    phi (Value v) l = v:l
    phi (Node 0 a) l = foldr ($) l . fmap snd . filter ((k ==) . fst) . elems
        $ a
    phi (Node _ a) l =
        let (_, c, _) = splitRange k a
        in foldr ($) l $ fmap snd c

-- | 'Transaction' version of 'lookupBTree'.
lookupBTreeT :: (Ord k, Binary k, Binary v) => k ->
    Transaction (BTree k v) s [v]
lookupBTreeT k = lookupT (lookupBTree k)

data Deleted k v g =
    Deleted k (g (BTree k v))
  | AllDeleted
  | UnChanged

-- | Filter items from a 'Fixed' @('BTree' k v)@ for a key 'k' that match
--   the predicate.
filterBTree :: (Ord k, Fixed g) => k -> (v -> Bool) ->
    g (BTree k v) -> g (BTree k v)
filterBTree k f t = deleted' . para phi $ t where
    deleted' UnChanged = t
    deleted' AllDeleted = empty
    deleted' (Deleted _ x) = x
    phi Empty = UnChanged
    phi (Value v) = if f v
        then UnChanged
        else AllDeleted
    phi (Node 0 a) =
        let al = do
                (nk, (nn, nv)) <- elems a
                case (nk == k, nv) of
                    (False, _) -> return (False, ((nk, nn):))
                    (_, UnChanged) -> return (False, ((nk, nn):))
                    _ -> return (True, id)
            alb = foldr ((||) . fst) False al
            al' = foldr (($) . snd) [] al
            mink = fst . head $ al'
        in case (alb, null al') of
            (True, True) -> AllDeleted
            (True, False) -> Deleted mink $ node 0 $
                array (0, length al' - 1) $ zip [0..] al'
            (False, _) -> UnChanged
    phi (Node d a) = 
        let (p, c, n) = splitRange k a
            p' = [(nk, nv) | (nk, (nv, _)) <- p]
            c'' = do
                (nk, (nn, nv)) <- c
                case nv of
                    UnChanged -> return (False, ((nk, nn):))
                    AllDeleted -> return (True, id)
                    Deleted k' v' -> return (True, ((k', v'):))
            c' = foldr (($) . snd) [] c''
            cb = foldr ((||) . fst) False c''
            n' = [(nk, nv) | (nk, (nv, _)) <- n]
            al = p' ++ c' ++ n'
            mink = fst . head $ al
        in case (cb, null al) of
            (False, _) -> UnChanged
            (True, True) -> AllDeleted
            (True, False) -> Deleted mink $ node d $
                array (0, length al - 1) $ zip [0..] al

-- | 'Transaction' version of 'filterBTree'.
filterBTreeT :: (Ord k, Binary k, Binary v) => k -> (v -> Bool) ->
    Transaction (BTree k v) (WT s) ()
filterBTreeT k f = alterT (filterBTree k f)

-- | Delete all items for key 'k' from the 'Fixed' @('BTree' k v)@.
deleteBTree :: (Ord k, Fixed g) => k -> g (BTree k v) -> g (BTree k v)
deleteBTree k = filterBTree k (const False)

-- | 'Transaction' version of 'deleteBTree'.
deleteBTreeT :: (Ord k, Binary k, Binary v) => k ->
    Transaction (BTree k v) (WT s) ()
deleteBTreeT k = alterT (deleteBTree k)

-- | Turn a 'Fixed' @('BTree' k v)@ into a list of key value tuples.
toListBTree :: (Ord k, Fixed g) => g (BTree k v) -> [(k,v)]
toListBTree t = cata phi t Nothing [] where
    phi Empty _ l = l
    phi (Value v) (Just k) l = (k, v):l
    phi (Value _) _ _ = error "Value with no Key"
    phi (Node _ a) _ l = foldr (\(k,v) -> ((v (Just k)) .)) id (elems a) l

-- | Turn a list of key value tuples into a 'Fixed' @('BTree' k v)@.
fromListBTree :: (Ord k, Fixed g) => [(k,v)] -> g (BTree k v)
fromListBTree = foldr (uncurry insertBTree) empty


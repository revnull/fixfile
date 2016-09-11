{-# LANGUAGE DataKinds #-}

module TestLightBTree(testLightBTree) where

import Data.Function
import Data.List hiding (null)
import Data.Monoid
import Prelude hiding (null)

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.BTree.Light
import qualified Data.FixFile.Tree23 as T23

prop_BTreeInsert :: [(Int, String)] -> Bool
prop_BTreeInsert xs = allIns where
    empt = empty :: Fix (BTree 3 Int String)
    fullSet = foldr (uncurry insertBTree) empt xs
    allIns = all (not . null . flip lookupBTree fullSet) $ fmap fst xs

prop_BTreeDelete :: [(Int, String)] -> [Int] -> Bool
prop_BTreeDelete xs ys = allIns where
    empt = empty :: Fix (BTree 3 Int String)
    fullSet = foldr (uncurry insertBTree) empt xs
    delSet = foldr deleteBTree fullSet ys
    allIns = all (null . flip lookupBTree delSet) ys

prop_BTreeDeleteAll :: [(Int, String)] -> Bool
prop_BTreeDeleteAll xs = allIns where
    empt = empty :: Fix (BTree 3 Int String)
    keys = map fst xs
    fullSet = foldr (uncurry insertBTree) empt xs
    delSet = foldr deleteBTree fullSet keys
    allIns = all (null . flip lookupBTree delSet) keys

prop_BTreeFilter :: [(Int, String)] -> Int -> String -> Bool
prop_BTreeFilter xs k v = testFilt where
    empt = empty :: Fix (BTree 3 Int String)
    baseSet = foldr (uncurry insertBTree) empt xs
    delSet = deleteBTree k baseSet
    fullSet = insertBTree k v $ insertBTree k ('a':v) delSet
    filtSet = filterBTree k (== v) fullSet
    testFilt = [v] == lookupBTree k filtSet

prop_BTreePartition :: [(Int, String)] -> Int -> Bool
prop_BTreePartition xs k = testPart where
    empt = empty :: Fix (BTree 3 Int String)
    fullTree = foldr (uncurry insertBTree) empt xs
    (treeL, treeR) = partitionBTree k fullTree
    emptT23 = empty :: Fix (T23.Tree23 (T23.Map Int Int))
    counts = T23.toListMap $ foldr countItems emptT23 xs
    countItems (k', _) m = T23.alterMap k' (Just . maybe 1 (1+)) m
    correctTree (k', l) =
        let (tree1,tree2) = if k' < k
                then (treeL, treeR)
                else (treeR, treeL)
        in l == (length (lookupBTree k' tree1)) &&
            null (lookupBTree k' tree2)
    testPart = all correctTree counts

prop_BTreeNodeSize :: [(Int, String)] -> Bool
prop_BTreeNodeSize xs = depth fullSet1 >= depth fullSet2 where
    empt1 = empty :: Fix (BTree 2 Int String)
    empt2 = empty :: Fix (BTree 5 Int String)
    fullSet1 = foldr (uncurry insertBTree) empt1 xs
    fullSet2 = foldr (uncurry insertBTree) empt2 xs

prop_BTreeFunctor :: [String] -> Bool
prop_BTreeFunctor xs = testList == toListBTree bt' where
    xs' = zip xs xs
    testList = fmap (fmap length) $ sortBy (compare `on` fst) xs'
    bt' = fmapF' length (fromListBTree xs') :: Fix (BTree 3 String Int)

prop_BTreeFoldable :: [(Int, Int)] -> Bool
prop_BTreeFoldable xs = listSum == btreeSum where
    listSum = getSum $ foldMap (Sum . snd) xs
    bt = fromListBTree xs :: Fix (BTree 3 Int Int)
    btreeSum = getSum $ foldMapF Sum bt

prop_BTreeTraversable :: [(Int, Int)] -> Bool
prop_BTreeTraversable xs = testEvens evens' && testOdds odds' where
    odds = fromListBTree $ filter (odd . snd) xs :: Fix (BTree 3 Int Int)
    evens = fromListBTree $ filter (even . snd) xs :: Fix (BTree 3 Int Int)
    f x = if even x then Nothing else Just x
    odds' = toListBTree <$> traverseF' f odds
    evens' = toListBTree <$> traverseF' f evens
    testEvens Nothing = True
    testEvens (Just l) = null l
    testOdds Nothing = False
    testOdds _ = True

testLightBTree = testGroup "Light BTree"
    [
        testProperty "Light BTree Insert" prop_BTreeInsert
       ,testProperty "Light BTree Delete" prop_BTreeDelete
       ,testProperty "Light BTree Delete All" prop_BTreeDeleteAll
       ,testProperty "Light BTree Filter" prop_BTreeFilter
       ,testProperty "Light BTree Partition" prop_BTreePartition
       ,testProperty "Light BTree Node Size" prop_BTreeNodeSize
       ,testProperty "Light BTree Functor" prop_BTreeFunctor
       ,testProperty "Light BTree Foldable" prop_BTreeFoldable
       ,testProperty "Light BTree Traversable" prop_BTreeTraversable
    ]

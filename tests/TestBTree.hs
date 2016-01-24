
module TestBTree(testBTree) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.BTree

prop_BTreeInsert :: [[(Int, String)]] -> Bool
prop_BTreeInsert xs = allIns where
    empt = empty :: Fix (BTree Int String)
    xs' = concat xs
    fullSet = foldr (uncurry insertBTree) empt xs'
    allIns = all (not . null . flip lookupBTree fullSet) $ fmap fst xs'

prop_BTreeDelete :: [[(Int, String)]] -> [Int] -> Bool
prop_BTreeDelete xs ys = allIns where
    empt = empty :: Fix (BTree Int String)
    xs' = concat xs
    fullSet = foldr (uncurry insertBTree) empt xs'
    delSet = foldr deleteBTree fullSet ys
    allIns = all (null . flip lookupBTree delSet) ys

prop_BTreeDeleteAll :: [[(Int, String)]] -> Bool
prop_BTreeDeleteAll xs = allIns where
    empt = empty :: Fix (BTree Int String)
    xs' = concat xs
    keys = map fst xs'
    fullSet = foldr (uncurry insertBTree) empt xs'
    delSet = foldr deleteBTree fullSet keys
    allIns = all (null . flip lookupBTree delSet) keys

prop_BTreeFilter :: [[(Int, String)]] -> Int -> String -> Bool
prop_BTreeFilter xs k v = testFilt where
    empt = empty :: Fix (BTree Int String)
    xs' = concat xs
    baseSet = foldr (uncurry insertBTree) empt xs'
    delSet = deleteBTree k baseSet
    fullSet = insertBTree k v $ insertBTree k ('a':v) delSet
    filtSet = filterBTree k (== v) fullSet
    testFilt = [v] == lookupBTree k filtSet

testBTree = testGroup "BTree"
    [
        testProperty "BTree Insert" prop_BTreeInsert
       ,testProperty "BTree Delete" prop_BTreeDelete
       ,testProperty "BTree Delete All" prop_BTreeDeleteAll
       ,testProperty "BTree Filter" prop_BTreeFilter
    ]

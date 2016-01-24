
module TestSet(testSet) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.Set

prop_SetInsert :: [Int] -> Bool
prop_SetInsert xs = allIns where
    fullSet = foldr insertSet (empty :: Fix (Set Int)) xs
    allIns = all (flip lookupSet fullSet) xs

prop_SetDelete :: [Int] -> [Int] -> Bool
prop_SetDelete xs ys = allDels where
    fullSet = foldr insertSet (empty :: Fix (Set Int)) xs
    delSet = foldr deleteSet fullSet ys
    allDels = all (not . flip lookupSet delSet) ys

prop_SetDeleteAll :: [Int] -> Bool
prop_SetDeleteAll xs = allDeleted where
    fullSet = foldr insertSet (empty :: Fix (Set Int)) xs
    delSet = foldr deleteSet fullSet xs
    allDeleted = [] == toListSet delSet

testSet = testGroup "Set"
    [
        testProperty "Set Insert" prop_SetInsert
       ,testProperty "Set Delete" prop_SetDelete
       ,testProperty "Set Delete All" prop_SetDeleteAll
    ]

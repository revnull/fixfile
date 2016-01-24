
module TestTree23(test23) where
    
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.Tree23

import Data.Maybe


prop_SetInsert :: [Int] -> Bool
prop_SetInsert xs = allIns where
    fullSet = foldr insertSet (empty :: Tree23 Fix (Set Int)) xs
    allIns = all (flip lookupSet fullSet) xs

prop_SetDelete :: [Int] -> [Int] -> Bool
prop_SetDelete xs ys = allDels where
    fullSet = foldr insertSet (empty :: Tree23 Fix (Set Int)) xs
    delSet = foldr deleteSet fullSet ys
    allDels = all (not . flip lookupSet delSet) ys

prop_SetDeleteAll :: [Int] -> Bool
prop_SetDeleteAll xs = allDeleted where
    fullSet = foldr insertSet (empty :: Tree23 Fix (Set Int)) xs
    delSet = foldr deleteSet fullSet xs
    allDeleted = [] == toListSet delSet

prop_MapInsert :: [(Int,String)] -> Bool
prop_MapInsert xs = allIns where
    empt = empty :: Tree23 Fix (Map Int String)
    fullSet = foldr (uncurry insertMap) empt xs
    allIns = all (isJust . flip lookupMap fullSet) $ fmap fst xs

prop_MapDelete :: [(Int,String)] -> [Int] -> Bool
prop_MapDelete ins dels = allDels where
    empt = empty :: Tree23 Fix (Map Int String)
    fullSet = foldr (uncurry insertMap) empt ins
    delSet = foldr deleteMap fullSet dels
    allDels = all (isNothing . flip lookupMap delSet) dels

prop_MapReplace :: [(Int,String)] ->  Int -> String -> String -> Bool
prop_MapReplace ins rk rv rv' = replTest where
    empt = empty :: Tree23 Fix (Map Int String)
    fullSet = foldr (uncurry insertMap) empt ins
    replSet = insertMap rk rv' $ insertMap rk rv fullSet
    replTest = Just rv' == lookupMap rk replSet

prop_MapDeleteAll :: [(Int,String)] -> Bool
prop_MapDeleteAll xs = allDeleted where
    fullSet = foldr (uncurry insertMap)
        (empty :: Tree23 Fix (Map Int String)) xs
    delSet = foldr deleteMap fullSet $ fmap fst xs
    allDeleted = [] == toListMap delSet

prop_MapMap :: [(Int,String)] -> String -> Bool
prop_MapMap xs pre = allMap where
    empt = empty :: Tree23 Fix (Map Int String)
    fullMap = foldr (uncurry insertMap) empt xs
    pl = length pre
    mapped = mapMap (pre ++) fullMap :: Tree23 Fix (Map Int String)
    keys = fmap fst xs
    allMap = all ((Just pre ==) . fmap (take pl) . flip lookupMap mapped) keys 

test23 = testGroup "Tree23"
    [
        testGroup "Set"
        [
            testProperty "Set Insert" prop_SetInsert
           ,testProperty "Set Delete" prop_SetDelete
           ,testProperty "Set Delete All" prop_SetDeleteAll
        ]
       ,testGroup "Map"
       [
            testProperty "Map Insert" prop_MapInsert
           ,testProperty "Map Delete" prop_MapDelete
           ,testProperty "Map Replace" prop_MapReplace
           ,testProperty "Map Delete All" prop_MapDeleteAll
           ,testProperty "Map Map" prop_MapMap
       ]
    ]

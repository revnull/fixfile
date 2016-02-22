
module TestTree23(test23) where
    
import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.Tree23

import Data.Maybe

empty23 :: Fix (Tree23 d)
empty23 = empty

prop_SetInsert :: [Int] -> Bool
prop_SetInsert xs = allIns where
    fullSet = foldr insertSet empty23 xs
    allIns = all (flip lookupSet fullSet) xs

prop_SetDelete :: [Int] -> [Int] -> Bool
prop_SetDelete xs ys = allDels where
    fullSet = foldr insertSet empty23 xs
    delSet = foldr deleteSet fullSet ys
    allDels = all (not . flip lookupSet delSet) ys

prop_SetDeleteAll :: [Int] -> Bool
prop_SetDeleteAll xs = allDeleted where
    fullSet = foldr insertSet empty23 xs
    delSet = foldr deleteSet fullSet xs
    allDeleted = [] == toListSet delSet

prop_SetPartition :: [Int] -> Int -> Bool
prop_SetPartition xs i = parted where
    fullSet = fromListSet xs :: Fix (Tree23 (Set Int))
    (ltSet', gteSet') = partitionSet i fullSet
    ltSet = toListSet ltSet'
    gteSet = toListSet gteSet'
    parted = all (< i) ltSet && all (>= i) gteSet

prop_SetMinMax :: [Int] -> Int -> Bool
prop_SetMinMax xs' i = minMax where
    xs = i:xs'
    minxs = minimum xs
    maxxs = maximum xs
    fullSet = fromListSet xs :: Fix (Tree23 (Set Int))
    Just minxs' = minSet fullSet
    Just maxxs' = maxSet fullSet
    minMax = minxs == minxs' && maxxs == maxxs'

prop_MapInsert :: [(Int,String)] -> Bool
prop_MapInsert xs = allIns where
    empt = empty :: Fix (Tree23 (Map Int String))
    fullSet = foldr (uncurry insertMap) empt xs
    allIns = all (isJust . flip lookupMap fullSet) $ fmap fst xs

prop_MapDelete :: [(Int,String)] -> [Int] -> Bool
prop_MapDelete ins dels = allDels where
    fullMap :: Fix (Tree23 (Map Int String))
    fullMap = fromListMap ins
    delSet = foldr deleteMap fullMap dels
    allDels = all (isNothing . flip lookupMap delSet) dels

prop_MapReplace :: [(Int,String)] ->  Int -> String -> String -> Bool
prop_MapReplace ins rk rv rv' = replTest where
    fullMap :: Fix (Tree23 (Map Int String))
    fullMap = foldr (uncurry insertMap) empty23 ins
    replMap = insertMap rk rv' $ insertMap rk rv fullMap
    replTest = Just rv' == lookupMap rk replMap

prop_MapDeleteAll :: [(Int,String)] -> Bool
prop_MapDeleteAll xs = allDeleted where
    fullMap :: Fix (Tree23 (Map Int String))
    fullMap = fromListMap xs
    delSet = foldr deleteMap fullMap $ fmap fst xs
    allDeleted = [] == toListMap delSet

prop_MapPartition :: [(Int, String)] -> Int -> Bool
prop_MapPartition xs i = parted where
    fullMap = fromListMap xs :: Fix (Tree23 (Map Int String))
    (ltMap', gteMap') = partitionMap i fullMap
    ltMap = fmap fst $ toListMap ltMap'
    gteMap = fmap fst $ toListMap gteMap'
    parted = all (< i) ltMap && all (>= i) gteMap

prop_MapMap :: [(Int,String)] -> String -> Bool
prop_MapMap xs pre = allMap where
    fullMap :: Fix (Tree23 (Map Int String))
    fullMap = foldr (uncurry insertMap) empty23 xs
    pl = length pre
    mapped :: Fix (Tree23 (Map Int String))
    mapped = mapMap (pre ++) fullMap
    keys = fmap fst xs
    allMap = all ((Just pre ==) . fmap (take pl) . flip lookupMap mapped) keys 

prop_MapMinMax :: [(Int, String)] -> (Int, String) -> Bool
prop_MapMinMax xs'' i = minMax where
    xs' = i:xs''
    fullMap = fromListMap xs' :: Fix (Tree23 (Map Int String))
    xs = toListMap fullMap
    minxs = minimum xs
    maxxs = maximum xs
    Just minxs' = minMap fullMap
    Just maxxs' = maxMap fullMap
    minMax = minxs == minxs' && maxxs == maxxs'
       

test23 = testGroup "Tree23"
    [
        testGroup "Set"
        [
            testProperty "Set Insert" prop_SetInsert
           ,testProperty "Set Delete" prop_SetDelete
           ,testProperty "Set Delete All" prop_SetDeleteAll
           ,testProperty "Set Partition" prop_SetPartition
           ,testProperty "Set Min/Max" prop_SetMinMax
        ]
       ,testGroup "Map"
       [
            testProperty "Map Insert" prop_MapInsert
           ,testProperty "Map Delete" prop_MapDelete
           ,testProperty "Map Replace" prop_MapReplace
           ,testProperty "Map Delete All" prop_MapDeleteAll
           ,testProperty "Map Partition" prop_MapPartition
           ,testProperty "Map Map" prop_MapMap
       ]
    ]

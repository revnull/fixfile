{-# LANGUAGE OverloadedStrings #-}

module TestTrie(testTrie) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.Trie

import qualified Data.ByteString.Lazy as BS
import Data.Maybe
import Control.Applicative hiding (empty)

instance Arbitrary BS.ByteString where
    arbitrary = BS.pack <$> arbitrary

instance CoArbitrary BS.ByteString where
    coarbitrary c = coarbitrary $ BS.unpack c

prop_TrieInsert :: [(BS.ByteString, Int)] -> Bool
prop_TrieInsert xs = allIns where
    empt = empty :: Fix (Trie Int)
    fullSet = foldr (uncurry insertTrie) empt xs
    allIns = all (isJust . flip lookupTrie fullSet) $ fmap fst xs

prop_TrieFreeze :: [(BS.ByteString, Int)] -> Bool
prop_TrieFreeze xs = allIns where
    empt = empty :: Fix (Trie Int)
    fullSet = freeze $ foldr (uncurry insertTrie) empt xs
    allIns = all (isJust . flip lookupTrie fullSet) $ fmap fst xs

prop_TrieThaw :: [(BS.ByteString, Int)] -> [(BS.ByteString, Int)] -> Bool
prop_TrieThaw xs ys = allIns where
    empt = empty :: Fix (Trie Int)
    halfSet = freeze $ foldr (uncurry insertTrie) empt xs
    fullSet = foldr (uncurry insertTrie) halfSet ys
    keys = fmap fst $ xs ++ ys
    allIns = all (isJust . flip lookupTrie fullSet) keys

prop_TrieDelete :: [(BS.ByteString, Int)] -> [BS.ByteString] -> 
    [BS.ByteString] -> Bool
prop_TrieDelete ins pre del = allDels where
    empt = empty :: Fix (Trie Int)
    insJoin = do
        p <- pre
        (ik, iv) <- ins
        return (BS.append p ik, iv)
    delJoin = do
        p <- pre
        dk <- del
        return (BS.append p dk)
    fullSet = foldr (uncurry insertTrie) empt insJoin
    delSet = foldr deleteTrie fullSet delJoin
    allDels = all (isNothing . flip lookupTrie delSet) delJoin

prop_TrieDeleteAll :: [(BS.ByteString, Int)] -> Bool
prop_TrieDeleteAll xs = allDels where
    empt = empty :: Fix (Trie Int)
    fullSet = foldr (uncurry insertTrie) empt xs
    delSet = foldr deleteTrie fullSet $ fmap fst xs
    allDels = [] == iterateTrie "" delSet

prop_TrieReplace :: [(BS.ByteString, Int)] -> BS.ByteString -> Int -> Int ->
    Bool
prop_TrieReplace xs rk rv rv' = replTest where
    empt = empty :: Fix (Trie Int)
    fullSet = foldr (uncurry insertTrie) empt xs
    replSet = insertTrie rk rv' $ insertTrie rk rv fullSet
    replTest = Just rv' == lookupTrie rk replSet

prop_TrieIterate :: [(BS.ByteString, Int)] -> BS.ByteString -> Bool
prop_TrieIterate xs pre = allIter where
    empt = empty :: Fix (Trie Int)
    ins = [(BS.append pre suf, x) | (suf, x) <- xs]
    fullSet = foldr (uncurry insertTrie) empt ins
    iter = iterateTrie pre fullSet
    allIter = all (isJust . flip lookup ins) $ fmap fst iter

testTrie = testGroup "Trie"
    [
        testProperty "Trie Insert" prop_TrieInsert
       ,testProperty "Trie Freeze" prop_TrieFreeze
       ,testProperty "Trie Thaw" prop_TrieThaw
       ,testProperty "Trie Delete" prop_TrieDelete
       ,testProperty "Trie Delete All" prop_TrieDeleteAll
       ,testProperty "Trie Replace" prop_TrieReplace
       ,testProperty "Trie Iterate" prop_TrieIterate
    ]

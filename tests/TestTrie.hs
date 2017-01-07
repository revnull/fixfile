{-# LANGUAGE OverloadedStrings #-}

module TestTrie(testTrie) where

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck

import Data.FixFile
import Data.FixFile.Trie

import qualified Data.ByteString.Lazy as BS
import Data.Function
import Data.List hiding (null)
import Data.Maybe
import Data.Monoid
import Control.Applicative hiding (empty)
import Prelude hiding (null)

instance Arbitrary BS.ByteString where
    arbitrary = BS.pack <$> arbitrary

instance CoArbitrary BS.ByteString where
    coarbitrary c = coarbitrary $ BS.unpack c

prop_TrieInsert :: [(BS.ByteString, Int)] -> Bool
prop_TrieInsert xs = allIns where
    empt = empty :: Fix (Trie Int)
    fullSet = foldr (uncurry insertTrie) empt xs
    allIns = all (isJust . flip lookupTrie fullSet) $ fmap fst xs

prop_TrieLookupNegative :: [BS.ByteString] -> [BS.ByteString] -> Bool
prop_TrieLookupNegative xs negs = allIns where
    empt = empty :: Fix (Trie Int)
    fullSet = foldr (flip insertTrie 0) empt xs
    negs' = filter (\x -> not (any (== x) xs)) negs
    allIns = all (isNothing . flip lookupTrie fullSet) negs'

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

prop_TrieDelete :: [(BS.ByteString, Int)] -> BS.ByteString -> 
    BS.ByteString -> Bool
prop_TrieDelete ins pre del = allDels where
    empt = empty :: Fix (Trie Int)
    pres = [(BS.append pre ik, iv) | (ik,iv) <- ins]
    dels = [(BS.append del ik, iv) | (ik,iv) <- ins]
    delks = fmap fst dels
    fullTrie = foldr (uncurry insertTrie) empt (pres ++ dels)
    delSet = foldr deleteTrie fullTrie delks
    allDels = all (isNothing . flip lookupTrie delSet) delks

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

prop_TrieFunctor :: [(BS.ByteString, String)] -> Bool
prop_TrieFunctor xs = testAll where
    testAll = xs'' == iterateTrie BS.empty trie' &&
        xs'' == iterateTrie BS.empty frozenTrie'
    xs' = nubBy ((==) `on` fst) $ sortBy (compare `on` fst) xs
    xs'' = fmap (fmap length) xs'
    trie = foldr (uncurry insertTrie) empty xs' :: Fix (Trie String)
    trie' = fmapF' length trie
    frozenTrie' = fmapF' length (freeze trie)

prop_TrieFoldable :: [(BS.ByteString, Int)] -> Bool
prop_TrieFoldable xs = testAll where
    testAll = listSum == trieSum && listSum == frozenTrieSum
    xs' = nubBy ((==) `on` fst) $ sortBy (compare `on` fst) xs
    listSum = getSum $ foldMap (Sum . snd) xs'
    trie = foldr (uncurry insertTrie) empty xs' :: Fix (Trie Int)
    trieSum = getSum $ foldMapF Sum trie
    frozenTrieSum = getSum $ foldMapF Sum (freeze trie)

prop_TrieTraversable :: [(BS.ByteString, Int)] -> Bool
prop_TrieTraversable xs = testAll where
    testAll = testEvens evens'' && testOdds odds'' &&
        testEvens frozenEvens'' && testOdds frozenOdds''
    evens = filter (even . snd) xs
    odds = filter (odd . snd) xs
    evens' = foldr (uncurry insertTrie) empty evens :: Fix (Trie Int)
    odds' = foldr (uncurry insertTrie) empty odds :: Fix (Trie Int)
    frozenEvens' = freeze evens'
    frozenOdds' = freeze odds'
    f x = if even x then Nothing else Just x
    evens'' = traverseF' f evens'
    odds'' = traverseF' f odds'
    frozenEvens'' = traverseF' f frozenEvens'
    frozenOdds'' = traverseF' f frozenOdds'
    testEvens Nothing = True
    testEvens _ = null evens
    testOdds Nothing = False
    testOdds _ = True

testTrie = testGroup "Trie"
    [
        testProperty "Trie Insert" prop_TrieInsert
       ,testProperty "Trie Lookup Negative" prop_TrieLookupNegative
       ,testProperty "Trie Freeze" prop_TrieFreeze
       ,testProperty "Trie Thaw" prop_TrieThaw
       ,testProperty "Trie Delete" prop_TrieDelete
       ,testProperty "Trie Delete All" prop_TrieDeleteAll
       ,testProperty "Trie Replace" prop_TrieReplace
       ,testProperty "Trie Iterate" prop_TrieIterate
       ,testProperty "Trie Functor" prop_TrieFunctor
       ,testProperty "Trie Foldable" prop_TrieFoldable
       ,testProperty "Trie Traversable" prop_TrieTraversable
    ]

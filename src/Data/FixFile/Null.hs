{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Data.FixFile.Null (
                          Null1(..)
                         ,Null(..)
                         ) where

import Data.FixFile.Fixed

{-|
    'Null' is a typeclass for representing data that can be 'empty' as well as
    the 'null' predicate that can determine if a piece of data is 'empty'.
 -}
class Null f where
    empty :: f
    null :: f -> Bool

{-|
    'Null1' is for expressing null types of kind @(* -> *)@.
 -}
class Null1 f where
    empty1 :: f a
    null1 :: f a -> Bool

instance Null1 f => Null (f a) where
    empty = empty1
    null = null1

instance Null1 Maybe where
    empty1 = Nothing
    null1 Nothing = True
    null1 _ = False

instance Null1 [] where
    empty1 = []
    null1 [] = True
    null1 _ = False

instance (Fixed g, Null1 f) => Null (g f) where
    empty = inf empty1
    null = null1 . outf


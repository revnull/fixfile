
{- |
    Module      :  Data.FixFile.Fixed
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    This is a data type that can be used with a 'FixFile' to store a set of
    'Ordered' items as an unbalanced binary tree. This file is not recommended
    for use, but exists for educational purposes. It has a simple
    implementation that is easier to read than some of the more advanced
    balanced data types.
-}
module Data.FixFile.Fixed (
                            Fix(..)
                           ,Fixed(..)
                           ,CataAlg
                           ,cata
                           ,AnaAlg
                           ,ana
                           ,ParaAlg
                           ,para
                           ,iso
                           ) where

{-|
    'Fixed' is a typeclass for representing the fixed point of a 'Functor'.
    A well-behaved instance of 'Fixed' should not change the shape of the
    underlying 'Functor'.

    In other words, the following should always be true:
@
'outf' ('inf' x) == x
@
 -}
class Fixed g where
    inf :: f (g f) -> g f
    outf :: g f -> f (g f)

{-|
    'Fix' is a type for creating an in-memory representation of the fixed
    point of a 'Functor'.

-}
newtype Fix f = InF { outF :: f (Fix f) }

instance Fixed Fix where
    inf = InF
    outf = outF

{-|
    'AnaAlg' is an anamorpism F-Algebra.
-}
type AnaAlg f a = a -> f a

{-|
    'ana' applies an AnaAlg over an argument to produce a fixed-point
    of a Functor.
-}
ana :: (Functor f, Fixed g) => AnaAlg f a -> a -> g f
ana f = inf . fmap (ana f) . f

{-|
    'CataAlg' is a catamorphism F-Algebra.
-}
type CataAlg f a = f a -> a

{-|
    'cata' applies a 'CataAlg' over a fixed point of a 'Functor'.
-}
cata :: (Functor f, Fixed g) => CataAlg f a -> g f -> a
cata f = f . fmap (cata f) . outf

{-|
    'ParaAlg' is a paramorphism F-Algebra.
-}
type ParaAlg g f a = f (g f, a) -> a

{-|
    'para' applies a 'ParaAlg' over a fixed point of a 'Functor'.
-}
para :: (Functor f, Fixed g) => ParaAlg g f a -> g f -> a
para f = f . fmap para' . outf where
    para' x = (x, para f x)

{-|
    'iso' maps from a fixed point of a 'Functor' to a different fixed
    point of the same 'Functor'. For any two well-behaved instances of
    'Fixed', the shape of the 'Functor' should remain unchanged.
-}
iso :: (Functor f, Fixed g, Fixed h) => g f -> h f
iso = cata inf


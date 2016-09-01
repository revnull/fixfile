{-# LANGUAGE TypeFamilies #-}

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
                           ,CataMAlg
                           ,cata
                           ,cataM
                           ,AnaAlg
                           ,AnaMAlg
                           ,ana
                           ,anaM
                           ,ParaAlg
                           ,ParaMAlg
                           ,para
                           ,paraM
                           ,iso
                           ,hylo
                           ,hyloM
                           ,FixedAlg(..)
                           ,FixedSub(..)
                           ,FixedFunctor(..)
                           ,fmapF'
                           ,FixedFoldable(..)
                           ,FixedTraversable(..)
                           ,traverseF'
                           ) where

import Control.Monad

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
    {-# INLINE inf #-}
    outf = outF
    {-# INLINE outf #-}

{-|
    'AnaAlg' is an anamorpism F-Algebra.
-}
type AnaAlg f a = a -> f a

{-|
    'AnaMAlg' is a monadic anamorpism F-Algebra.
-}
type AnaMAlg m f a = a -> m (f a)

{-|
    'ana' applies an AnaAlg over an argument to produce a fixed-point
    of a Functor.
-}
ana :: (Functor f, Fixed g) => AnaAlg f a -> a -> g f
ana f = inf . fmap (ana f) . f

{-|
    'anaM' is a monadic anamorphism.
-}
anaM :: (Traversable f, Fixed g, Monad m) =>
    AnaMAlg m f a -> a -> m (g f)
anaM f = fmap inf . (traverse (anaM f) =<<) . f

{-|
    'CataAlg' is a catamorphism F-Algebra.
-}
type CataAlg f a = f a -> a

{-|
    'CataMAlg' is a monadic catamorphism F-Algebra.
-}
type CataMAlg m f a = f a -> m a

{-|
    'cata' applies a 'CataAlg' over a fixed point of a 'Functor'.
-}
cata :: (Functor f, Fixed g) => CataAlg f a -> g f -> a
cata f = f . fmap (cata f) . outf

{-|
    'cataM' is a monadic catamorphism.
-}
cataM :: (Traversable f, Fixed g, Monad m) =>
    CataMAlg m f a -> g f -> m a
cataM f = (>>= f) . (traverse (cataM f)) . outf

{-|
    'ParaAlg' is a paramorphism F-Algebra.
-}
type ParaAlg g f a = f (g f, a) -> a

{-|
    'ParaAlg' is a monadic paramorphism F-Algebra.
-}
type ParaMAlg m g f a = f (g f, a) -> m a

{-|
    'para' applies a 'ParaAlg' over a fixed point of a 'Functor'.
-}
para :: (Functor f, Fixed g) => ParaAlg g f a -> g f -> a
para f = f . fmap para' . outf where
    para' x = (x, para f x)

{-|
    'paraM' is a monadic paramorphism.
-}
paraM :: (Traversable f, Fixed g, Monad m) =>
    ParaMAlg m g f a -> g f -> m a
paraM f = (>>= f) . mapM para' . outf where
    para' x = do
        x' <- paraM f x
        return (x, x')

{-|
    'iso' maps from a fixed point of a 'Functor' to a different fixed
    point of the same 'Functor'. For any two well-behaved instances of
    'Fixed', the shape of the 'Functor' should remain unchanged.
-}
iso :: (Functor f, Fixed g, Fixed h) => g f -> h f
iso = cata inf

{-|
    'hylo' combines ana and cata into a single operation.
-}
hylo :: Functor f => AnaAlg f a -> CataAlg f b -> a -> b
hylo f g = hylo' where hylo' = g . fmap hylo' . f

{-|
    'hyloM' is a monadic hylomorphism.
-}

hyloM :: (Traversable f, Monad m) =>
    AnaMAlg m f a -> CataMAlg m f b -> a -> m b
hyloM f g = hylo' where hylo' = g <=< mapM hylo' <=< f

{-|
    'FixedAlg' is a typeclass for describing the relationship between a
    'Functor' that is used with a 'Fixed' combinator and an algebraic datatype
    in that 'Functor' other than the one used for fixed-point recursion.
-}
class FixedAlg (f :: * -> *) where
    type Alg f :: *

{-|
    'FixedSub' is a typeclass for describing the relationship between a
    'FixedAlg' 'Functor' @f@ and that same 'Functor' with @Alg f@ switched
    from @v@ to @v'@.
-}
class FixedAlg f => FixedSub f where
    type Sub f v v' :: * -> *

{-|
    'FixedFunctor' is a typeclass for describing mapping behavior for datatypes
    used with 'Fixed' combinators.
-}
class FixedSub f => FixedFunctor f where
    -- | Map over a 'Fixed' recursive 'FixedSub' @f@.
    fmapF :: (Fixed g, Fixed g', a ~ Alg f) =>
        (a -> b) -> g f -> g' (Sub f a b)

-- | 'fmapF', but using a single instance of 'Fixed'.
fmapF' :: (FixedFunctor f, Fixed g, a ~ Alg f) =>
    (a -> b) -> g f -> g (Sub f a b)
fmapF' = fmapF

{-|
    'FixedFoldable' is a typeclass for describing folds over datatypes with
    'Fixed' combinators.
-}
class FixedAlg f => FixedFoldable f where
    -- | Fold over a 'Fixed' recursive 'FixedAlg' @f@.
    foldMapF :: (Fixed g, Monoid m, a ~ Alg f) => (a -> m) -> g f -> m

{-|
    'FixedTraversable' is a typeclass for describing traversals over datatypes
    with 'Fixed' combinators.
-}
class FixedSub f => FixedTraversable f where
    -- | Traverse over a 'Fixed' recursive 'FixedSub' @f@ in the 'Applicative'
    -- @h@.
    traverseF :: (Fixed g, Fixed g', Applicative h, a ~ Alg f) =>
        (a -> h b) -> g f -> h (g' (Sub f a b))

-- | 'traverseF', but using a single instance of 'Fixed'.
traverseF' :: (FixedTraversable f, Fixed g, Applicative h, a ~ Alg f) =>
    (a -> h b) -> g f -> h (g (Sub f a b))
traverseF' = traverseF


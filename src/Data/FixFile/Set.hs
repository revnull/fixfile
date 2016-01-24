{-# LANGUAGE DeriveGeneric, DeriveFunctor, DeriveFoldable, DeriveTraversable #-}

{- |
    Module      :  Data.FixFile.Set
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
module Data.FixFile.Set (Set
                         ,createSetFile
                         ,openSetFile
                         ,empty
                         ,insertSet
                         ,insertSetT
                         ,deleteSet
                         ,deleteSetT
                         ,lookupSet
                         ,lookupSetT
                         ,toListSet
                         ,toListSetT
                         ) where

import Data.FixFile
import Data.FixFile.Fixed
import Data.Binary
import Data.Foldable hiding (concat, toList)
import Data.Traversable
import GHC.Generics
import Prelude hiding (lookup)
import Control.Applicative hiding (empty)

{- |
    A 'Fixed' @('Set' i)@ is a set of items represented as a binary tree.
-}
data Set i a = Empty | Node a i a
    deriving (Read, Show, Generic, Functor, Foldable, Traversable)

instance (Binary i, Binary a) => Binary (Set i a)

-- | An empty 'Set'.
empty :: Fixed g => g (Set i)
empty = inf Empty

node :: Fixed g => g (Set i) -> i -> g (Set i) -> g (Set i)
node l i r = inf $ Node l i r

-- | Insert an item 'i' into a 'Fixed' recursive @'Set' i@.
insertSet :: (Ord i, Fixed g) => i -> g (Set i) -> g (Set i)
insertSet i s = newHead $ para phi s where
    newHead = maybe s id
    phi Empty = Just $ node empty i empty
    phi (Node (ln, la) j (rn, ra)) = case compare i j of
        EQ -> Nothing
        LT -> la >>= \l -> return $ node l j rn
        GT -> ra >>= \r -> return $ node ln j r

-- | 'Transaction' version of 'insertSet'.
insertSetT :: (Ord i, Binary i) => i -> Transaction (Set i) (WT s) ()
insertSetT i = alterT (insertSet i)

-- | Delete an item 'i' into a 'Fixed' recursive @'Set' i@.
deleteSet :: (Ord i, Fixed g) => i -> g (Set i) -> g (Set i)
deleteSet i s = newHead $ para phi s Nothing where
    newHead = maybe s id
    phi Empty x = x
    phi (Node (ln, la) j (rn, ra)) Nothing = case compare i j of
        EQ -> la (Just rn)
        LT -> la Nothing >>= \l -> return $ node l j rn
        GT -> ra Nothing >>= \r -> return $ node ln j r
    phi (Node (ln, _) j (_, ra)) x = node ln j <$> ra x

-- | 'Transaction' version of 'deleteSet'.
deleteSetT :: (Ord i, Binary i) => i -> Transaction (Set i) (WT s) ()
deleteSetT i = alterT (deleteSet i)

-- | Predicate to lookup an item from a @'Set' i@.
lookupSet :: (Ord i, Fixed g) => i -> g (Set i) -> Bool
lookupSet i = cata phi where
    phi Empty = False
    phi (Node la j ra) = case compare i j of
        EQ -> True
        LT -> la
        GT -> ra

-- | 'Transaction' version of 'lookupSet'.
lookupSetT :: (Ord i, Binary i) => i -> Transaction (Set i) s Bool
lookupSetT i = lookupT (lookupSet i)

-- | Create a @'FixFile' ('Set' i)@.
createSetFile :: Binary i => FilePath -> IO (FixFile (Set i))
createSetFile fp = createFixFile empty fp

-- | Open a @'FixFile' ('Set' i)@.
openSetFile :: Binary i => FilePath -> IO (FixFile (Set i))
openSetFile = openFixFile

-- | Turn a 'Fixed' recurive structure of @'Set' i@ into a list.
toListSet :: Fixed g => g (Set i) -> [i]
toListSet s = cata phi s [] where
    phi Empty l = l
    phi (Node la i ra) l = (la . (i:) . ra) l

-- | 'Transaction' version of 'toListSet'.
toListSetT :: Binary i => Transaction (Set i) s [i]
toListSetT = lookupT toListSet


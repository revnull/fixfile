{-# LANGUAGE ScopedTypeVariables, RankNTypes, KindSignatures,
    MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
    FunctionalDependencies, TypeFamilies, UndecidableInstances,
    DeriveDataTypeable, DeriveGeneric #-}

{-|
    
    Module      :  Data.FixFile
    Copyright   :  (C) 2016 Rev. Johnny Healey
    License     :  LGPL-3
    Maintainer  :  Rev. Johnny Healey <rev.null@gmail.com>
    Stability   :  experimental
    Portability :  unknown

    A 'FixFile' is file for storing recursive data. The file supports MVCC
    through an append-only file.

    In order to eliminate distinctions between data structures that are
    file-backed versus in-memory, this library makes heavy use of lazy IO.
    Transactions are used to ensure safety of the unsafe IO.

    The data structures used by a 'FixFile' should not be recursive directly,
    but should have instances of 'Foldable', 'Traversable', and 'Binary' and
    should be structured such that the fixed point of the data type is
    recursive.
 -}

module Data.FixFile (
                      -- * Fixed point combinators
                      Fixed(..)
                     ,Fix(..)
                     ,Stored
                     ,Pos
                     -- * F-Algebras
                     ,CataAlg
                     ,cata
                     ,AnaAlg
                     ,ana
                     ,ParaAlg
                     ,para
                     ,iso
                     -- * Root Data
                     ,Root(..)
                     ,Ptr
                     ,Ref(..)
                     ,ref
                     ,Tup(..)
                     ,tup
                     -- * FixFiles
                     ,FixFile
                     ,createFixFile
                     ,createFixFileHandle
                     ,openFixFile
                     ,openFixFileHandle
                     ,vacuum
                     -- * Transactions
                     ,Transaction
                     ,RootTransaction
                     ,RT
                     ,WT
                     ,alterT
                     ,lookupT
                     ,readTransaction
                     ,writeTransaction
                     ,subTransaction
                     ,subRoot
                     ,getRoot
                     ,putRoot
                     ,getFull
                     ) where

import Prelude hiding (sequence, mapM, lookup)

import Control.Concurrent.MVar
import Control.Exception
import Control.Lens hiding (iso, para)
import qualified Control.Monad.RWS as RWS
import Control.Monad.Identity hiding (mapM)
import Control.Monad.Trans
import Data.Binary
import Data.ByteString.Lazy as BSL
import Data.Dynamic
import Data.HashTable.IO
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import Data.Traversable (mapM)
import GHC.Generics
import System.FilePath
import System.Directory
import System.IO
import System.IO.Unsafe

import Data.FixFile.Fixed

type HashTable k v = CuckooHashTable k v

data Cache a = Cache Int (HashTable Pos a) (HashTable Pos a)
    deriving (Typeable)

type Caches = M.Map TypeRep Dynamic

createCache :: IO (Cache f)
createCache = Cache 0 <$> new <*> new

cacheInsert :: Pos -> a -> Cache a -> IO (Cache a)
cacheInsert p f (Cache i oc nc) =
    if i >= 50
        then new >>= cacheInsert p f . Cache 0 nc
        else do
            insert nc p f
            return (Cache (i + 1) oc nc)

cacheLookup :: Pos -> Cache a -> IO (Cache a, Maybe a)
cacheLookup p c@(Cache _ oc nc) = do
    nval <- lookup nc p
    val <- maybe (lookup oc p) (return . Just) nval
    case (nval, val) of
        (Nothing, Just v) -> do
            c' <- cacheInsert p v c
            return (c', val)
        _ -> return (c, val)

getCachedOrStored :: Typeable a => Pos -> IO a -> MVar Caches -> IO a
getCachedOrStored p m cs = do
    mval <- withCache cs (cacheLookup p)
    case mval of
        Just v -> return v
        Nothing -> do
            v <- m
            withCache_ cs (cacheInsert p v)
            return v

withCache :: Typeable c => MVar Caches -> (Cache c -> IO (Cache c, a)) -> IO a
withCache cs f = modifyMVar cs $ \cmap -> do
    let mc = M.lookup mt cmap >>= fromDynamic
        mt = typeOf $ fromJust mc
    c <- maybe createCache return mc
    (c', a) <- f c
    return (M.insert mt (toDyn c') cmap, a)

withCache_ :: Typeable c => MVar Caches -> (Cache c -> IO (Cache c)) -> IO ()
withCache_ cs f = withCache cs $ \c -> f c >>= \c' -> return (c', ())

-- | A Position in a file.
type Pos = Word64

-- FFH is a FixFile Handle. This is an internal data structure.
data FFH = FFH (MVar Handle) (MVar Caches)

getRawBlock :: Binary a => Handle -> Pos -> IO a
getRawBlock h p = do
    hSeek h AbsoluteSeek (fromIntegral p)
    (sb :: Word32) <- decode <$> (BSL.hGet h 4)
    decode <$> BSL.hGet h (fromIntegral sb)

getBlock :: (Typeable f, Binary (f Pos)) => Pos -> FFH -> IO (f Pos)
getBlock p (FFH mh mc) = getCachedOrStored p readFromFile mc where
    readFromFile = withMVar mh $ flip getRawBlock p

putBlock :: (Typeable a, Binary a) => a -> FFH -> IO Pos
putBlock a (FFH mh mc) = putRawBlock >>= cacheBlock where
    putRawBlock = withMVar mh $ \h -> do
        hSeek h SeekFromEnd 0
        p <- fromIntegral <$> hTell h
        let enc  = encode a
            len  = fromIntegral $ BSL.length enc
            len' = encode (len :: Word32)
            enc' = mappend len' enc
        BSL.hPut h enc'
        return p
    cacheBlock p = do
        withCache_ mc (cacheInsert p a)
        return p

-- | A 'Stored\'' is a fixpoint combinator for data that is potentially
-- | file-backed.
data Stored' a =
    -- | A memory-only instance of 'a'.
    Memory a
    -- | An instance of 'a' that is file-backed.
  | Cached !Pos a
  deriving (Read, Show, Eq, Ord)

instance Functor Stored' where
    fmap f (Memory a) = Memory (f a)
    fmap f (Cached p a) = Cached p (f a)

instance Foldable Stored' where
    foldMap f (Memory a) = f a
    foldMap f (Cached _ a) = f a

instance Traversable Stored' where
    traverse f (Memory a) = Memory <$> f a
    traverse f (Cached p a) = Cached p <$> f a

{- | 
    'Stored' is a fixed-point combinator of 'f' in Transaction 's'.
-}
newtype Stored s f = InS { outS :: Stored' (f (Stored s f)) }

instance Fixed (Stored s) where
    inf = InS . Memory
    outf (InS (Memory a)) = a
    outf (InS (Cached _ a)) = a

-- | Write the stored data to disk so that the on-disk representation 
--   matches what is in memory.
sync :: (Traversable f, Binary (f Pos), Typeable f) =>
    FFH -> Stored s f -> IO Pos
sync h = commit . outS where
    commit (Memory r) = do
        r' <- mapM (sync h) r
        putBlock r' h
    commit (Cached p _) = return p

-- | 'RT' is a read transaction of 's'
data RT s
-- | 'WT' is a write transaction of 's'
data WT s

{- |
    A 'Transaction' is an isolated execution of a read or update operation
    on the root object stored in a 'FixFile'. 'f' is the 'Functor' that is
    stored by the 'FixFile'. 's' is a phantom type used to isolate 'Stored'
    values to the transaction where they are run. 'a' is the result of the
    transaction.
-}
newtype Transaction (f :: * -> *) s a = Transaction {
    runT :: RWS.RWST FFH () (Stored s f) IO a
  }

instance Functor (Transaction f s) where
    fmap f (Transaction t) = Transaction $ fmap f t

instance Applicative (Transaction f s) where
    pure = Transaction . pure
    Transaction a <*> Transaction b = Transaction $ a <*> b

instance Monad (Transaction f s) where
    return = pure
    Transaction t >>= f = Transaction $ RWS.RWST $ \ffh root -> do
        (a, root', w) <- RWS.runRWST t ffh root
        (a', root'', w') <- RWS.runRWST (runT $ f a) ffh root'
        return (a', root'', w `mappend` w')

newtype Ptr (f :: * -> *) = Ptr Pos
    deriving Generic

instance Binary (Ptr f)

class Root (r :: (((* -> *) -> *) -> *)) where
    readRoot :: r Ptr -> RootTransaction r' s (r (Stored s))
    writeRoot :: r (Stored (WT s)) -> RootTransaction r' (WT s) (r Ptr)
    fromMemRep :: r Fix -> r (Stored s)
    toMemRep :: r (Stored s) -> r Fix

data Ref (f :: * -> *) (g :: (* -> *) -> *) = Ref { deRef :: g f }
    deriving (Generic)

instance (Typeable f, Binary (f Pos), Traversable f) => Root (Ref f) where
    readRoot (Ref (Ptr p)) = Ref <$> (withHandle $ flip readStoredLazy p)
    writeRoot (Ref a) = (Ref . Ptr) <$> (withHandle $ flip sync a)
    fromMemRep (Ref a) = Ref . iso $ a
    toMemRep (Ref a) = Ref . iso $ a

instance Binary (Ref f Ptr)

ref :: Lens' (Ref f g) (g f)
ref = lens (\(Ref a) -> a) (\_ b -> Ref b)

newtype Tup r1 r2 (g :: (* -> *) -> *) = Tup { unTup :: (r1 g, r2 g) }

instance (Root r1, Root r2) => Root (Tup r1 r2) where
    readRoot (Tup (p1, p2)) = do
        r1 <- readRoot p1
        r2 <- readRoot p2
        return $ Tup (r1, r2)
    writeRoot (Tup (r1, r2)) = do
        p1 <- writeRoot r1
        p2 <- writeRoot r2
        return $ Tup (p1, p2)
    fromMemRep (Tup (m1, m2)) = Tup (fromMemRep m1, fromMemRep m2)
    toMemRep (Tup (r1, r2)) = Tup (toMemRep r1, toMemRep r2)

tup :: Lens' (Tup r1 r2 g) (r1 g, r2 g)
tup = lens (\(Tup t) -> t) (\_ t -> Tup t)

newtype RootTransaction r s a = RTransaction {
    runRT :: RWS.RWST FFH (Last (r Ptr)) (r (Stored s)) IO a
  }

instance Functor (RootTransaction f s) where
    fmap f (RTransaction t) = RTransaction $ fmap f t

instance Applicative (RootTransaction f s) where
    pure = RTransaction . pure
    RTransaction a <*> RTransaction b = RTransaction $ a <*> b

instance Monad (RootTransaction f s) where
    return = pure
    RTransaction t >>= f = RTransaction $ RWS.RWST $ \ffh root -> do
        (a, root', w) <- RWS.runRWST t ffh root
        (a', root'', w') <- RWS.runRWST (runRT $ f a) ffh root'
        return (a', root'', w `mappend` w')

subRoot :: Lens' (r (Stored s)) (r' (Stored s)) -> RootTransaction r' s a ->
    RootTransaction r s a
subRoot l st = RTransaction $ RWS.RWST $ \ffh root -> do
    (a, r, _) <- RWS.runRWST (runRT st) ffh (root^.l)
    return (a, set l r root, mempty)

subTransaction :: Lens' (r (Stored s)) (Stored s f) -> Transaction f s a ->
    RootTransaction r s a
subTransaction l st = RTransaction $ RWS.RWST $ \ffh root -> do
    (a, r, _) <- RWS.runRWST (runT st) ffh (root^.l)
    return (a, set l r root, mempty)

withHandle :: (FFH -> IO a) -> RootTransaction r s a
withHandle f = RTransaction $ RWS.ask >>= liftIO . f

-- | Get the root object stored in the file.
getRoot :: RootTransaction r s (r (Stored s))
getRoot = RTransaction $ RWS.get

getFixed :: Transaction f s (Stored s f)
getFixed = Transaction $ RWS.get

-- | Update the root object of the file. This only takes effect at the
--   end of the tranaction.
putRoot :: Root r => r (Stored (WT s)) -> RootTransaction r (WT s) ()
putRoot =  putRoot'

putRoot' :: Root r => r (Stored s) -> RootTransaction r s ()
putRoot' = RTransaction . RWS.put

putFixed :: Stored (WT s) f -> Transaction f (WT s) ()
putFixed = Transaction . RWS.put

readStoredLazy :: (Traversable f, Binary (f Pos), Typeable f) =>
    FFH -> Pos -> IO (Stored s f)
readStoredLazy h p = do
    f <- getBlock p h
    let fcons = InS . Cached p
    fcons <$> mapM (unsafeInterleaveIO . readStoredLazy h) f

{- |
    The preferred way to modify the root object of a 'FixFile' is by using
    'alterT'. It applies a function that takes the root object as a
    @'Stored' ('WT' s) 'f'@ and returns the new desired head of the
    same type.
-}
alterT :: (tr ~ Transaction f (WT s), Traversable f, Binary (f Pos)) =>
    (Stored (WT s) f -> Stored (WT s) f) -> tr ()
alterT f = getFixed >>= putFixed . f

{- |
    The preferred way to read from a 'FixFile' is to use 'lookupT'. It
    applies a function that takes a @'Stored' s f@ and returns a value.
-}
lookupT :: (tr ~ Transaction f s, Traversable f, Binary (f Pos)) =>
    (Stored s f -> a) -> tr a
lookupT f = f <$> getFixed


{- |
    A 'FixFile' is a handle for accessing a file-backed recursive data
    structure. 'f' is the 'Functor' that the file is storing.
-}
data FixFile r = FixFile FilePath (MVar (FFH, r Ptr)) (MVar ())

acquireWriteLock :: FixFile f -> IO ()
acquireWriteLock (FixFile _ _ wl) = do
    void $ takeMVar wl

releaseWriteLock :: FixFile f -> IO ()
releaseWriteLock (FixFile _ _ wl) = do
    putMVar wl ()

withWriteLock :: FixFile f -> IO a -> IO a
withWriteLock ff f = do
    acquireWriteLock ff
    f `finally` releaseWriteLock ff

readHeader :: FFH -> IO (Pos)
readHeader (FFH mh _) = withMVar mh $ \h -> do
    hSeek h AbsoluteSeek 0
    decode <$> BSL.hGet h 8

updateHeader :: Pos -> RootTransaction r (WT s) ()
updateHeader p = do
    withHandle $ \(FFH mh _) -> 
        withMVar mh $ \h -> do
            hSeek h AbsoluteSeek 0
            BSL.hPut h (encode p)
            hFlush h

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath'.
-}
createFixFile :: (Root r, Binary (r Ptr), Typeable r) =>
    r Fix -> FilePath -> IO (FixFile r)
createFixFile initial path =
    openFile path ReadWriteMode >>= createFixFileHandle initial path

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath' and using the 'Handle' to the
    file to be created.
-}
createFixFileHandle :: (Root r, Binary (r Ptr), Typeable r) =>
    r Fix -> FilePath -> Handle -> IO (FixFile r)
createFixFileHandle initial path h = do
    ffh <- FFH <$> newMVar h <*> newMVar M.empty
    BSL.hPut h (encode (0 :: Pos))
    let t = runRT $ do
            dr <- writeRoot $ fromMemRep initial
            (withHandle $ putBlock dr) >>= updateHeader
            RTransaction . RWS.tell . Last . Just $ dr
    (_,_,root') <- RWS.runRWST t ffh undefined
    let Just root = getLast root'
    ffhmv <- newMVar (ffh, root)
    FixFile path ffhmv <$> newMVar ()

{- |
    Open a 'FixFile' from the file described by 'FilePath'.
-}
openFixFile :: Binary (r Ptr) => FilePath -> IO (FixFile r)
openFixFile path =
    openFile path ReadWriteMode >>= openFixFileHandle path

{- |
    Open a 'FixFile' from the file described by 'FilePath' and using the
    'Handle' to the file.
-}
openFixFileHandle :: Binary (r Ptr) => FilePath -> Handle ->
    IO (FixFile r)
openFixFileHandle path h = do
    ffh <- FFH <$> newMVar h <*> newMVar M.empty
    root <- readHeader ffh >>= getRawBlock h 
    ffhmv <- newMVar (ffh, root)
    FixFile path ffhmv <$> newMVar ()

{- |
    Perform a read transaction on a 'FixFile'. This transaction cannot
    modify the root object stored in the file. The returned value is lazily
    evaluated, but will always correspond to the root object at the start
    of the transaction.
-}
readTransaction :: Root r => FixFile r ->
    (forall s. RootTransaction r (RT s) a) -> IO a
readTransaction (FixFile _ ffhmv _) t = do
    (ffh, root) <- readMVar ffhmv
    let t' = readRoot root >>= putRoot' >> t
    (a, _) <- RWS.evalRWST (runRT t') ffh undefined
    return a

{- |
    Perform a write transaction on a 'FixFile'. This operation differs from
    the readTransaction in that the root object stored in the file can
    potentially be updated by this 'Transaction'.
-}
writeTransaction :: (Root r, Binary (r Ptr), Typeable r) => 
    FixFile r -> (forall s. RootTransaction r (WT s) a)
    -> IO a
writeTransaction ff@(FixFile _ ffhmv _) t = res where
    res = withWriteLock ff runTransaction
    runTransaction = do
        (ffh, root) <- readMVar ffhmv
        let t' = readRoot root >>= putRoot >> t >>= save
            save a = do
                dr <- getRoot >>= writeRoot
                (withHandle $ putBlock dr) >>= updateHeader
                RTransaction . RWS.tell . Last . Just $ dr
                return a
        (a, root') <- RWS.evalRWST (runRT t') ffh undefined
        case getLast root' of
            Nothing -> return ()
            Just root'' -> do
                void $ swapMVar ffhmv (ffh, root'')
        return a

{- |
    Get the full datastructure from the transaction as a @'Fix' f@.
-}
getFull :: (Traversable f, Binary (f Pos)) => Transaction f s (Fix f)
getFull = iso <$> getFixed

{- |
    Because a 'FixFile' is backed by an append-only file, there is a periodic
    need to 'vacuum' the file to garbage collect data that is no longer
    referenced from the root. This task operates on a temporary file that then
    replaces the file that backs FixFile.

    The memory usage of this operation scales with the recursive depth of the
    full structure stored in the file.
-}
vacuum :: (Root r, Binary (r Ptr), Typeable r) =>
    FixFile r -> IO ()
vacuum ff@(FixFile path mv _) = withWriteLock ff runVacuum where
    runVacuum = do
        mval <- takeMVar mv

        readFFHMV <- newMVar mval
        readDB <- FixFile path readFFHMV <$> newMVar ()

        (tp, th) <- openTempFile (takeDirectory path) ".ffile.tmp"
        hClose th

        rootMem <- readTransaction readDB (toMemRep <$> getRoot)
        (FixFile _ newMV _) <- createFixFile rootMem tp

        renameFile tp path

        takeMVar newMV >>= putMVar mv
    

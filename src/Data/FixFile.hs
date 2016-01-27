{-# LANGUAGE ScopedTypeVariables, RankNTypes, KindSignatures,
    MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
    FunctionalDependencies, TypeFamilies, UndecidableInstances #-}

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
                     -- * FixFiles
                     ,FixFile
                     ,createFixFile
                     ,createFixFileHandle
                     ,openFixFile
                     ,openFixFileHandle
                     ,vacuum
                     -- * Transactions
                     ,Transaction
                     ,RT
                     ,WT
                     ,alterT
                     ,lookupT
                     ,readTransaction
                     ,writeTransaction
                     ,getRoot
                     ,putRoot
                     ,getFull
                     ) where

import Prelude hiding (sequence, mapM, lookup)
import Data.Word
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.Monoid
import Data.Foldable
import Data.Traversable

import Control.Monad.Trans
import System.IO
import System.IO.Unsafe
import Data.ByteString.Lazy as BSL
import Control.Applicative
import qualified Control.Monad.RWS as RWS
import Control.Concurrent.MVar
import Control.Exception
import Control.Monad.Identity hiding (mapM)
import Data.IORef
import Data.HashTable.IO
import System.IO.Temp
import System.FilePath
import System.Directory

import Data.FixFile.Fixed

type HashTable k v = CuckooHashTable k v

data Cache f = Cache Int (HashTable Pos (f Pos)) (HashTable Pos (f Pos))

createCache :: IO (Cache f)
createCache = Cache 0 <$> new <*> new

cacheInsert :: Pos -> f Pos -> Cache f -> IO (Cache f)
cacheInsert p f (Cache i oc nc) =
    if i >= 50
        then new >>= cacheInsert p f . Cache 0 nc
        else do
            insert nc p f
            return (Cache (i + 1) oc nc)

getCachedOrStored :: Pos -> Cache f -> IO (f Pos) -> IO (Cache f, f Pos)
getCachedOrStored p c@(Cache i oc nc) m = do
    nval <- lookup nc p
    val <- maybe (lookup oc p) (return . Just) nval
    case (nval, val) of
        (Nothing, Nothing) -> do
            f <- m
            c' <- cacheInsert p f c
            return (c', f)
        (Nothing, Just f) -> do
            c' <- cacheInsert p f c
            return (c', f)
        (Just f, _) -> return (c, f)

-- | A Position in a file.
type Pos = Word64

-- FFH is a FixFile Handle. This is an internal data structure.
newtype FFH f = FFH (MVar (Handle, Cache f))

withFFH :: FFH f -> (Handle -> Cache f -> IO a) -> IO a
withFFH (FFH mv) f = withMVar mv $ \(h, c) -> f h c

modifyFFH :: MonadIO m => 
    FFH f -> (Handle -> Cache f -> IO (Cache f, a)) -> m a
modifyFFH (FFH mv) fn = liftIO $ modifyMVar mv $ \(h, c) -> do
    (c', a) <- fn h c
    return ((h, c'), a)

getBlock :: (MonadIO m, Binary (f Pos)) => Pos -> FFH f -> m (f Pos)
getBlock p ffh = modifyFFH ffh readFromFile where
    readFromFile h c = getCachedOrStored p c $ do
        hSeek h AbsoluteSeek (fromIntegral p)
        (sb :: Word32) <- decode <$> (BSL.hGet h 4)
        decode <$> BSL.hGet h (fromIntegral sb)

putBlock :: (MonadIO m, Binary (f Pos)) => f Pos -> FFH f -> m Pos
putBlock a ffh = liftIO $ modifyFFH ffh $ \h c -> do
    hSeek h SeekFromEnd 0
    p <- fromIntegral <$> hTell h
    let enc  = encode a
        len  = fromIntegral $ BSL.length enc
        len' = encode (len :: Word32)
        enc' = mappend len' enc
    BSL.hPut h enc'
    c' <- cacheInsert p a c
    return (c', p)

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
    foldMap f (Cached p a) = f a

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

storedPos' :: Stored s f -> Pos
storedPos' (InS (Cached p _)) = p
storedPos' _ = error "Improper sync of data structure."

-- | Write the stored data to disk so that the on-disk representation 
--   matches what is in memory.
sync :: (Traversable f, Binary (f Pos)) =>
    Stored s f -> Transaction f s Pos
sync = commit . outS where
    commit (Memory r) = do
        r' <- mapM sync r
        withHandle $ putBlock r'
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
    runT :: RWS.RWST (FFH f) (Last Pos) (Stored s f) IO a
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

withHandle :: (FFH f -> IO a) -> Transaction f s a
withHandle f = Transaction $ RWS.ask >>= liftIO . f

-- | Get the root object stored in the file.
getRoot :: Transaction f s (Stored s f)
getRoot = Transaction $ RWS.get

-- | Update the root object of the file. This only takes effect at the
--   end of the tranaction.
putRoot :: Stored (WT s) f -> Transaction f (WT s) ()
putRoot = Transaction . RWS.put

liftIO' :: IO a -> Transaction f s a
liftIO' = Transaction . liftIO

readStoredLazy :: (Traversable f, Binary (f Pos)) =>
    FFH f -> Pos -> IO (Stored s f)
readStoredLazy h p = do
    f <- getBlock p h
    let cons = InS . Cached p
    cons <$> mapM (unsafeInterleaveIO . readStoredLazy h) f

{- |
    The preferred way to modify the root object of a 'FixFile' is by using
    'alterT'. It applies a function that takes the root object as a
    @'Stored' ('WT' s) 'f'@ and returns the new desired head of the
    same type.
-}
alterT :: (tr ~ Transaction f (WT s), Traversable f, Binary (f Pos)) =>
    (Stored (WT s) f -> Stored (WT s) f) -> tr ()
alterT f = getRoot >>= putRoot . f

{- |
    The preferred way to read from a 'FixFile' is to use 'lookupT'. It
    applies a function that takes a @'Stored' s f@ and returns a value.
-}
lookupT :: (tr ~ Transaction f s, Traversable f, Binary (f Pos)) =>
    (Stored s f -> a) -> tr a
lookupT f = f <$> getRoot


{- |
    A 'FixFile' is a handle for accessing a file-backed recursive data
    structure. 'f' is the 'Functor' that the file is storing.
-}
data FixFile (f :: * -> *) = FixFile FilePath (MVar (FFH f, Pos)) (MVar ())

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

readHeader :: FFH f -> IO (Pos)
readHeader ffh = withFFH ffh $ \h _ -> do
    hSeek h AbsoluteSeek 0
    decode <$> BSL.hGet h 8

updateHeader :: (Functor f, Binary (f Pos)) => Pos -> 
    Transaction f (WT s) ()
updateHeader p = do
    withHandle $ \ffh -> 
        withFFH ffh $ \h _ -> do
            hSeek h AbsoluteSeek 0
            BSL.hPut h (encode p)
            hFlush h
    Transaction . RWS.tell . pure $ p

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath'.
-}
createFixFile :: (Traversable f, Binary (f Pos)) => Fix f -> FilePath ->
    IO (FixFile f)
createFixFile init path =
    openFile path ReadWriteMode >>= createFixFileHandle init path

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath' and using the 'Handle' to the
    file to be created.
-}
createFixFileHandle :: (Traversable f, Binary (f Pos)) => Fix f -> FilePath ->
    Handle -> IO (FixFile f)
createFixFileHandle init path h = do
    c <- createCache
    ffh <- FFH <$> newMVar (h, c)
    BSL.hPut h (encode (0 :: Pos))
    let t = runT $ do
            let root = iso init
            sync root >>= updateHeader
    (_,_,hdr') <- RWS.runRWST t ffh undefined
    let Just hdr = getLast hdr'
    ffhmv <- newMVar (ffh, hdr)
    FixFile path ffhmv <$> newMVar ()

{- |
    Open a 'FixFile' from the file described by 'FilePath'.
-}
openFixFile :: FilePath -> IO (FixFile f)
openFixFile path =
    openFile path ReadWriteMode >>= openFixFileHandle path

{- |
    Open a 'FixFile' from the file described by 'FilePath' and using the
    'Handle' to the file.
-}
openFixFileHandle :: FilePath -> Handle -> IO (FixFile f)
openFixFileHandle path h = do
    h <- openFile path ReadWriteMode
    c <- createCache
    ffh <- FFH <$> newMVar (h, c)
    hdr <- readHeader ffh
    ffhmv <- newMVar (ffh, hdr)
    FixFile path ffhmv <$> newMVar ()

{- |
    Perform a read transaction on a 'FixFile'. This transaction cannot
    modify the root object stored in the file. The returned value is lazily
    evaluated, but will always correspond to the root object at the start
    of the transaction.
-}
readTransaction :: (Traversable f, Binary (f Pos)) => FixFile f ->
    (forall s. Transaction f (RT s) a) -> IO a
readTransaction (FixFile _ ffhmv _) t = do
    (ffh, hdr) <- readMVar ffhmv
    root <- readStoredLazy ffh hdr
    (a, _) <- RWS.evalRWST (runT t) ffh root
    return a

{- |
    Perform a write transaction on a 'FixFile'. This operation differs from
    the readTransaction in that the root object stored in the file can
    potentially be updated by this 'Transaction'.
-}
writeTransaction :: (Binary (f Pos), Traversable f)
    => FixFile f -> (forall s. Transaction f (WT s) a)
    -> IO a
writeTransaction ff@(FixFile _ ffhmv _) t = withWriteLock ff runTransaction where
    runTransaction = do
        (ffh, hdr) <- readMVar ffhmv
        let t' = t >>= save
            save res = do
                root' <- getRoot
                sync root' >>= updateHeader
                return res
        root <- readStoredLazy ffh hdr
        (a, hdr') <- RWS.evalRWST (runT t') ffh root
        System.IO.putStrLn $ show hdr'
        case getLast hdr' of
            Nothing -> return ()
            Just hdr'' -> void $ swapMVar ffhmv (ffh, hdr'')
        return a

{- |
    Get the full datastructure from the transaction as a @'Fix' f@.
-}
getFull :: (Traversable f, Binary (f Pos)) => Transaction f s (Fix f)
getFull = iso <$> getRoot

{- |
    Because a 'FixFile' is backed by an append-only file, there is a periodic
    need to 'vacuum' the file to garbage collect data that is no longer
    referenced from the root. This task operates on a temporary file that then
    replaces the file that backs FixFile.

    The memory usage of this operation scales with the recursive depth of the
    full structure stored in the file.
-}
vacuum :: (Traversable f, Binary (f Pos)) => FixFile f -> IO ()
vacuum ff@(FixFile path mv _) = withWriteLock ff runVacuum where
    runVacuum = do
        mval <- takeMVar mv

        readFFHMV <- newMVar mval
        readDB <- FixFile path readFFHMV <$> newMVar ()

        (tp, th) <- openTempFile (takeDirectory path) ".ffile.tmp"
        hClose th

        (FixFile _ newMV _) <- readTransaction readDB getFull >>=
            flip createFixFile tp

        renameFile tp path

        takeMVar newMV >>= putMVar mv
    

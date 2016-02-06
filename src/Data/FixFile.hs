{-# LANGUAGE ScopedTypeVariables, RankNTypes, KindSignatures,
    MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
    FunctionalDependencies, TypeFamilies, UndecidableInstances,
    DeriveDataTypeable, DeriveGeneric #-}

{- |
    
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

    There is also the concept of the 'Root' data of a 'FixFile'.  This can be
    used as a kind of header for a FixFile that can allow several recursive
    data structures to be modified in a single transaction.

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
                     -- * FixFiles
                     ,FixFile
                     ,createFixFile
                     ,createFixFileHandle
                     ,openFixFile
                     ,openFixFileHandle
                     ,closeFixFile
                     ,vacuum
                     -- * Transactions
                     ,Transaction
                     ,alterT
                     ,lookupT
                     ,readTransaction
                     ,writeTransaction
                     ,subTransaction
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

{- | 
    'Stored' is a fixed-point combinator of 'f' in Transaction 's'.
-}
data Stored s f =
    -- | A memory-only instance of 'a'.
    Memory (f (Stored s f))
    -- | An instance of 'a' that is file-backed.
  | Cached !Pos (f (Stored s f))

instance Fixed (Stored s) where
    inf = Memory
    outf (Memory a) = a
    outf (Cached _ a) = a

-- | Write the stored data to disk so that the on-disk representation 
--   matches what is in memory.
sync :: (Traversable f, Binary (f Pos), Typeable f) =>
    FFH -> Stored s f -> IO Pos
sync h = commit where
    commit (Memory r) = do
        r' <- mapM commit r
        putBlock r' h
    commit (Cached p _) = return p

{- |
    A 'Ptr' is a 'Pos' with a phantom type for a functor 'f'. A 'Root' expects
    an argument that resembles a 'Fixed', but we can pass it a 'Ptr' instead.
    This is not a well-formed 'Fixed' because it doesn't actually store 'f'.
    But, it can be serialized, which allows a 'Root' object that takes this
    as an argument to be serialized.
-}
newtype Ptr (f :: * -> *) = Ptr Pos
    deriving Generic

instance Binary (Ptr f)

{- |
    A 'Root' datastructure acts as a kind of header that can contain one or
    more 'Ref's to different recursive structures. It takes one argument,
    which has the kind of @((* -> *) -> *)@. This argument should be either an
    instance of 'Fixed' or a 'Ptr'. If it is an instance of 'Fixed', then
    the 'Root' can contain recursive data structures. If it is passed 'Ptr'
    as an argument, then the 'Root' will contain a non-recursive structure,
    but can be serialized.

-}
class Root (r :: (((* -> *) -> *) -> *)) where
    -- | Deserialize @'r' 'Ptr'@ inside a 'Transaction'.
    readRoot :: r Ptr -> Transaction r' s (r (Stored s))
    -- | Serialize @'r' 'Ptr'@ inside a 'Transaction'. This will result in
    -- | changes to any recursive structures to be written as well.
    writeRoot :: r (Stored s) -> Transaction r' s (r Ptr)

    -- | 'iso', but applied to an instance of 'Root'.
    rootIso :: (Fixed g, Fixed h) => r g -> r h

{- |
    A 'Ref' is a reference to a 'Functor' 'f' in the 'Fixed' instance of 'g'.

    This is an instance of 'Root' and acts to bridge between the 'Root' and
    the recursively defined data structure that is @('g' 'f')@.
-}
data Ref (f :: * -> *) (g :: (* -> *) -> *) = Ref { deRef :: g f }
    deriving (Generic)

instance (Typeable f, Binary (f Pos), Traversable f) => Root (Ref f) where
    readRoot (Ref (Ptr p)) = Ref <$> (withHandle $ flip readStoredLazy p)
    writeRoot (Ref a) = (Ref . Ptr) <$> (withHandle $ flip sync a)
    rootIso = Ref . iso . deRef

instance Binary (Ref f Ptr)

-- | Lens for accessing the value stored in a Ref
ref :: Lens' (Ref f g) (g f)
ref = lens (\(Ref a) -> a) (\_ b -> Ref b)

{- |
    A 'Transaction' is an isolated execution of a read or update operation
    on the root object stored in a 'FixFile'. 'r' is the 'Root' data that is
    stored by the 'FixFile'. 's' is a phantom type used to isolate 'Stored'
    values to the transaction where they are run.
-}
newtype Transaction r s a = Transaction {
    runRT :: RWS.RWST FFH (Last (r Ptr)) (r (Stored s)) IO a
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
        (a', root'', w') <- RWS.runRWST (runRT $ f a) ffh root'
        return (a', root'', w `mappend` w')

instance RWS.MonadState (r (Stored s)) (Transaction r s) where
    get = Transaction $ RWS.get
    put = Transaction . RWS.put
    state = Transaction . RWS.state

{- |
    Perform a 'Transaction' on a part of the root object.
-}
subTransaction :: Lens' (r (Stored s)) (r' (Stored s)) -> Transaction r' s a ->
    Transaction r s a
subTransaction l st = Transaction $ RWS.RWST $ \ffh root -> do
    (a, r, _) <- RWS.runRWST (runRT st) ffh (root^.l)
    return (a, set l r root, mempty)

withHandle :: (FFH -> IO a) -> Transaction r s a
withHandle f = Transaction $ RWS.ask >>= liftIO . f

readStoredLazy :: (Traversable f, Binary (f Pos), Typeable f) =>
    FFH -> Pos -> IO (Stored s f)
readStoredLazy h p = do
    f <- getBlock p h
    let fcons = Cached p
    fcons <$> mapM (unsafeInterleaveIO . readStoredLazy h) f

{- |
    The preferred way to modify the root object of a 'FixFile' is by using
    'alterT'. It applies a function that takes the root object as a
    @'Stored' 's' 'f'@ and returns the new desired head of the
    same type.
-}
alterT :: (tr ~ Transaction (Ref f) s, Traversable f, Binary (f Pos)) =>
    (Stored s f -> Stored s f) -> tr ()
alterT f = ref %= f

{- |
    The preferred way to read from a 'FixFile' is to use 'lookupT'. It
    applies a function that takes a @'Stored' s f@ and returns a value.
-}
lookupT :: (tr ~ Transaction (Ref f) s, Traversable f, Binary (f Pos)) =>
    (Stored s f -> a) -> tr a
lookupT f = f <$> use ref

{- |
    A 'FixFile' is a handle for accessing a file-backed recursive data
    structure. 'r' is the 'Root' object stored in the 'FixFile'.
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

updateHeader :: Pos -> Transaction r s ()
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
            dr <- writeRoot $ rootIso initial
            (withHandle $ putBlock dr) >>= updateHeader
            Transaction . RWS.tell . Last . Just $ dr
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
    Close a 'FixFile'. This can potentially cause errors on data that is lazily
    being read from a 'Transaction'.
-}
closeFixFile :: FixFile r -> IO ()
closeFixFile (FixFile path tmv _) = do
    (FFH mh _, _) <- takeMVar tmv
    h <- takeMVar mh
    hClose h
    putMVar mh $ error (path ++ " is closed.")
    putMVar tmv $ error (path ++ " is closed.")

{- |
    Perform a read transaction on a 'FixFile'. This transaction cannot
    modify the root object stored in the file. The returned value is lazily
    evaluated, but will always correspond to the root object at the start
    of the transaction.
-}
readTransaction :: Root r => FixFile r ->
    (forall s. Transaction r s a) -> IO a
readTransaction (FixFile _ ffhmv _) t = do
    (ffh, root) <- readMVar ffhmv
    let t' = readRoot root >>= RWS.put >> t
    (a, _) <- RWS.evalRWST (runRT t') ffh undefined
    return a

{- |
    Perform a write transaction on a 'FixFile'. This operation differs from
    the readTransaction in that the root object stored in the file can
    potentially be updated by this 'Transaction'.
-}
writeTransaction :: (Root r, Binary (r Ptr), Typeable r) => 
    FixFile r -> (forall s. Transaction r s a)
    -> IO a
writeTransaction ff@(FixFile _ ffhmv _) t = res where
    res = withWriteLock ff runTransaction
    runTransaction = do
        (ffh, root) <- readMVar ffhmv
        let t' = readRoot root >>= RWS.put >> t >>= save
            save a = do
                dr <- RWS.get >>= writeRoot
                (withHandle $ putBlock dr) >>= updateHeader
                Transaction . RWS.tell . Last . Just $ dr
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
getFull :: Functor f => Transaction (Ref f) s (Fix f)
getFull = uses ref iso

{- |
    Because a 'FixFile' is backed by an append-only file, there is a periodic
    need to 'vacuum' the file to garbage collect data that is no longer
    referenced from the root. This task operates on a temporary file that then
    replaces the file that backs FixFile.

    The memory usage of this operation scales with the recursive depth of the
    structure stored in the file.
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

        rootMem <- readTransaction readDB (rootIso <$> RWS.get)
        (FixFile _ newMV _) <- createFixFile rootMem tp

        renameFile tp path

        takeMVar newMV >>= putMVar mv
    

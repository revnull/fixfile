{-# LANGUAGE ScopedTypeVariables, RankNTypes, KindSignatures,
    MultiParamTypeClasses, FlexibleInstances, FlexibleContexts,
    FunctionalDependencies, TypeFamilies, UndecidableInstances,
    DeriveDataTypeable, DeriveGeneric, ConstraintKinds #-}

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
    but should have instances of 'Typeable', 'Traversable', and 'Binary' and
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
                     -- * F-Algebras
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
                     ,hylo
                     ,hyloM
                     ,iso
                     -- * Fixed Typeclasses
                     ,FixedAlg(..)
                     ,FixedSub(..)
                     ,FixedFunctor(..)
                     ,fmapF'
                     ,FixedFoldable(..)
                     ,FixedTraversable(..)
                     ,traverseF'
                     -- * Root Data
                     ,Fixable
                     ,FixTraverse(..)
                     ,Root
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
                     ,fixFilePath
                     ,clone
                     ,cloneH
                     ,vacuum
                     -- * Transactions
                     ,Transaction
                     ,alterT
                     ,lookupT
                     ,readTransaction
                     ,writeTransaction
                     ,writeExceptTransaction
                     ,subTransaction
                     ,getRoot
                     ,getFull
                     ) where

import Prelude hiding (sequence, mapM, lookup)

import Control.Concurrent.MVar
import Control.Exception
import Control.Lens hiding (iso, para)
import Control.Monad.Except hiding (mapM_)
import qualified Control.Monad.RWS as RWS hiding (mapM_)
import Data.Binary
import Data.ByteString as BS
import Data.ByteString.Lazy as BSL
import Data.Dynamic
import Data.Hashable
import Data.HashTable.IO hiding (mapM_)
import Data.IORef
import qualified Data.Map as M
import Data.Maybe
import Data.Monoid
import GHC.Generics
import System.FilePath
import System.Directory
import System.IO
import System.IO.Unsafe

import Data.FixFile.Fixed

type HashTable k v = CuckooHashTable k v

data Cache f = Cache Int (HashTable (Ptr f) (f (Ptr f)))
    (HashTable (Ptr f) (f (Ptr f)))
    deriving (Typeable)

type Caches = M.Map TypeRep Dynamic

createCache :: IO (Cache f)
createCache = Cache 0 <$> new <*> new

cacheInsert :: Ptr f -> f (Ptr f) -> Cache f -> IO (Cache f)
cacheInsert p f (Cache i oc nc) =
    if i >= 50
        then new >>= cacheInsert p f . Cache 0 nc
        else do
            insert nc p f
            return (Cache (i + 1) oc nc)

cacheLookup :: Ptr f -> Cache f -> IO (Cache f, Maybe (f (Ptr f)))
cacheLookup p c@(Cache _ oc nc) = do
    nval <- lookup nc p
    val <- maybe (lookup oc p) (return . Just) nval
    case (nval, val) of
        (Nothing, Just v) -> do
            c' <- cacheInsert p v c
            return (c', val)
        _ -> return (c, val)

getCachedOrStored :: Typeable f => Ptr f -> IO (f (Ptr f)) -> MVar Caches ->
    IO (f (Ptr f))
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

type Pos = Word64

data WriteBuffer = WB ([BS.ByteString] -> [BS.ByteString]) Pos Pos

bufferFlushSize :: Word64
bufferFlushSize = 10485760 -- 10 MB

initWB :: Handle -> IO WriteBuffer
initWB h = do
    hSeek h SeekFromEnd 0
    p <- fromIntegral <$> hTell h
    return $ WB id p p

writeWB :: Binary a => a -> WriteBuffer -> (WriteBuffer, Pos, Bool)
writeWB a (WB bsf st end) = sbs `seq` wb where
    wb = (WB bsf' st end', end, end' - st > bufferFlushSize)
    enc = encode a
    len = fromIntegral $ BSL.length enc
    len' = encode (len :: Word32)
    sbs = BSL.toStrict (len' <> enc)
    end' = end + 4 + fromIntegral len
    bsf' = bsf . (sbs:)

flushBuffer :: WriteBuffer -> Handle -> IO WriteBuffer
flushBuffer (WB bsf st en) h = do
    hSeek h SeekFromEnd 0
    p <- fromIntegral <$> hTell h
    when (p /= st) $ fail "WriteBuffer position failure."
    mapM_ (BS.hPut h) (bsf [])
    return (WB id en en)

-- FFH is a FixFile Handle. This is an internal data structure.
data FFH = FFH (MVar Handle) (IORef WriteBuffer) (MVar Caches)

getRawBlock :: Binary a => Handle -> Pos -> IO a
getRawBlock h p = do
    hSeek h AbsoluteSeek (fromIntegral p)
    (sb :: Word32) <- decode <$> (BSL.hGet h 4)
    decode <$> BSL.hGet h (fromIntegral sb)

getBlock :: (Typeable f, Binary (f (Ptr f))) => Ptr f -> FFH -> IO (f (Ptr f))
getBlock p@(Ptr pos) (FFH mh _ mc) = getCachedOrStored p readFromFile mc where
    readFromFile = withMVar mh $ flip getRawBlock pos

putRawBlock :: Binary a => Bool -> a -> FFH -> IO Pos
putRawBlock fl a (FFH mh wb _) = do
    wb' <- readIORef wb
    let (wb'', p, fl') = writeWB a wb'
    if (fl' || fl)
        then do
            wb''' <- withMVar mh (flushBuffer wb'')
            writeIORef wb wb'''
        else writeIORef wb wb''
    return p

putBlock :: (Typeable f, Binary (f (Ptr f))) => (f (Ptr f)) -> FFH ->
    IO (Ptr f)
putBlock a h@(FFH _ _ mc) = putRawBlock False a h >>= cacheBlock . Ptr where
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
  | Cached {-# UNPACK #-} !(Ptr f) (f (Stored s f))

instance Fixed (Stored s) where
    inf = Memory
    {-# INLINE inf #-}
    outf (Memory a) = a
    outf (Cached _ a) = a
    {-# INLINE outf #-}

-- | Write the stored data to disk so that the on-disk representation 
--   matches what is in memory.
sync :: (Traversable f, Binary (f (Ptr f)), Typeable f) =>
    FFH -> Stored s f -> IO (Ptr f)
sync h = commit where
    commit (Memory r) = do
        r' <- mapM commit r
        putBlock r' h
    commit (Cached p _) = return p

{- |
    A 'Ptr' points to a location in a 'FixFile' and has a phantom type for a 
    'Functor' 'f'. A 'Root' expects an argument that resembles a 'Fixed',
    but we can pass it a 'Ptr' instead. This is not a well-formed 'Fixed'
    because it can't be unpacked into @'f' ('Ptr' 'f')@.
    
    But, it can be serialized, which allows a 'Root' object that takes this
    as an argument to be serialized.
-}
newtype Ptr (f :: * -> *) = Ptr Pos
    deriving (Generic, Eq, Ord, Read, Show)

instance Binary (Ptr f)

instance Hashable (Ptr f) where
    hashWithSalt x (Ptr y) = hashWithSalt x y

-- | A Constraint for data that can be used with a 'Ref'
type Fixable f = (Traversable f, Binary (f (Ptr f)), Typeable f)

{- |
    'FixTraverse' is a class based on 'Traverse' but taking an argument of kind
    @((* -> *) -> *)@ instead of @*@.
-}
class FixTraverse (t :: ((* -> *) -> *) -> *) where
    -- | Given a function that maps from @a@ to @b@ over @'Fixable' g@ in the
    --   'Applicative' @f@, traverse over @t@ changing the fixed-point
    --   combinator from @a@ to @b@.
    traverseFix :: Applicative f =>
        (forall g. Fixable g => a g -> f (b g)) -> t a -> f (t b)

{- | 
    A 'Root' is a datastructure that is an instance of 'FixTraverse' and
    'Binary'. This acts as a sort of "header" for the file where the 'Root'
    may have several 'Ref's under it to different 'Functors'.
-}

type Root r = (FixTraverse r, Binary (r Ptr))

readRoot :: Root r => r Ptr -> Transaction r' s (r (Stored s))
readRoot = traverseFix readPtr where
    readPtr p = withHandle $ flip readStoredLazy p

writeRoot :: Root r => r (Stored s) -> Transaction r' s (r Ptr)
writeRoot = traverseFix writeStored where
    writeStored s = withHandle $ flip sync s

rootIso :: (Root r, Fixed g, Fixed h) => r g -> r h
rootIso = runIdentity . traverseFix (Identity . iso)

{- |
    A 'Ref' is a reference to a 'Functor' 'f' in the 'Fixed' instance of 'g'.

    This is an instance of 'Root' and acts to bridge between the 'Root' and
    the recursively defined data structure that is @('g' 'f')@.
-}
newtype Ref (f :: * -> *) (g :: (* -> *) -> *) = Ref { deRef :: g f }
    deriving (Generic)

instance Binary (Ref f Ptr)

instance Fixable f => FixTraverse (Ref f) where
    traverseFix isoT (Ref a) = Ref <$> isoT a

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

readStoredLazy :: (Traversable f, Binary (f (Ptr f)), Typeable f) =>
    FFH -> Ptr f -> IO (Stored s f)
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
alterT :: (tr ~ Transaction (Ref f) s, Traversable f, Binary (f (Ptr f))) =>
    (Stored s f -> Stored s f) -> tr ()
alterT f = ref %= f

{- |
    The preferred way to read from a 'FixFile' is to use 'lookupT'. It
    applies a function that takes a @'Stored' s f@ and returns a value.
-}
lookupT :: (tr ~ Transaction (Ref f) s, Traversable f, Binary (f (Ptr f))) =>
    (Stored s f -> a) -> tr a
lookupT f = f <$> use ref

{- |
    A 'FixFile' is a handle for accessing a file-backed recursive data
    structure. 'r' is the 'Root' object stored in the 'FixFile'.
-}
data FixFile r = FixFile FilePath (MVar (FFH, r Ptr)) (MVar ())

-- | Get the 'FilePath' of a 'FixFile'.
fixFilePath :: FixFile r -> FilePath
fixFilePath (FixFile p _ _) = p

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
readHeader (FFH mh _ _) = withMVar mh $ \h -> do
    hSeek h AbsoluteSeek 0
    decode <$> BSL.hGet h 8

updateHeader :: Pos -> Transaction r s ()
updateHeader p = do
    withHandle $ \(FFH mh _ _) -> 
        withMVar mh $ \h -> do
            hSeek h AbsoluteSeek 0
            BSL.hPut h (encode p)
            hFlush h

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath'.
-}
createFixFile :: Root r => r Fix -> FilePath -> IO (FixFile r)
createFixFile initial path =
    openBinaryFile path ReadWriteMode >>= createFixFileHandle initial path

{- |
    Create a 'FixFile', using @'Fix' f@ as the initial structure to store
    at the location described by 'FilePath' and using the 'Handle' to the
    file to be created.
-}
createFixFileHandle :: Root r =>
    r Fix -> FilePath -> Handle -> IO (FixFile r)
createFixFileHandle initial path h = do
    BSL.hPut h (encode (0 :: Pos))
    wb <- initWB h
    ffh <- FFH <$> newMVar h <*> newIORef wb <*> newMVar M.empty
    let t = runRT $ do
            dr <- writeRoot $ rootIso initial
            (withHandle $ putRawBlock True dr) >>= updateHeader
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
    openBinaryFile path ReadWriteMode >>= openFixFileHandle path

{- |
    Open a 'FixFile' from the file described by 'FilePath' and using the
    'Handle' to the file.
-}
openFixFileHandle :: Binary (r Ptr) => FilePath -> Handle ->
    IO (FixFile r)
openFixFileHandle path h = do
    wb <- initWB h
    ffh <- FFH <$> newMVar h <*> newIORef wb <*> newMVar M.empty
    root <- readHeader ffh >>= getRawBlock h 
    ffhmv <- newMVar (ffh, root)
    FixFile path ffhmv <$> newMVar ()

{- |
    Close a 'FixFile'. This can potentially cause errors on data that is lazily
    being read from a 'Transaction'.
-}
closeFixFile :: FixFile r -> IO ()
closeFixFile (FixFile path tmv _) = do
    (FFH mh _ _, _) <- takeMVar tmv
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
writeTransaction :: Root r => 
    FixFile r -> (forall s. Transaction r s a)
    -> IO a
writeTransaction ff@(FixFile _ ffhmv _) t = res where
    res = withWriteLock ff runTransaction
    runTransaction = do
        (ffh, root) <- readMVar ffhmv
        let t' = readRoot root >>= RWS.put >> t >>= save
            save a = do
                dr <- RWS.get >>= writeRoot
                (withHandle $ putRawBlock True dr) >>= updateHeader
                Transaction . RWS.tell . Last . Just $ dr
                return a
        (a, root') <- RWS.evalRWST (runRT t') ffh undefined
        case getLast root' of
            Nothing -> return ()
            Just root'' -> do
                void $ swapMVar ffhmv (ffh, root'')
        return a

{- |
    The 'writeExceptTransaction' function behaves like 'writeTransaction', but
    applies to a 'Transaction' wrapped in 'ExceptT'. In the event that an
    exception propagates through the 'Transaction', the updates are not
    committed to disk.

    This is meant to provide a mechanism for aborting 'Transaction's.
-}
writeExceptTransaction :: Root r => 
    FixFile r -> (forall s. ExceptT e (Transaction r s) a)
    -> IO (Either e a)
writeExceptTransaction ff@(FixFile _ ffhmv _) t = res where
    res = withWriteLock ff runTransaction
    runTransaction = do
        (ffh, root) <- readMVar ffhmv
        let t' = readRoot root >>= RWS.put >> runExceptT t >>= save
            save l@(Left _) = return l
            save r@(Right _) = do
                dr <- RWS.get >>= writeRoot
                (withHandle $ putRawBlock True dr) >>= updateHeader
                Transaction . RWS.tell . Last . Just $ dr
                return r
        (a, root') <- RWS.evalRWST (runRT t') ffh undefined
        case (a, getLast root') of
            (Right _, Just root'') -> do
                void $ swapMVar ffhmv (ffh, root'')
            _ -> return ()
        return a


{- |
    Get the root datastructure from the transaction as @r 'Fix'@.
-}
getRoot :: Root r => Transaction r s (r Fix)
getRoot = rootIso <$> RWS.get

{- |
    Get the full datastructure from the transaction as a @'Fix' f@.
-}
getFull :: Functor f => Transaction (Ref f) s (Fix f)
getFull = uses ref iso

{- |
    'cloneH' is 'clone' but taking a 'Handle' as an argument instead of a
    'FilePath'.
-}
cloneH :: Root r => FixFile r -> Handle -> IO ()
cloneH (FixFile _ mv _) dh = runClone where
    runClone = do
        mv'@(ffh, root) <- takeMVar mv

        BSL.hPut dh (encode (Ptr 0))

        wb <- initWB dh
        wb' <- newIORef wb
        dffh <- FFH <$> newMVar dh <*> return wb' <*> newMVar M.empty

        root' <- traverseFix (copyPtr ffh dffh) root

        r' <- putRawBlock True root' dffh 

        hSeek dh AbsoluteSeek 0
        BSL.hPut dh (encode r')

        putMVar mv mv'

    copyPtr ffh h = hyloM
        (flip getBlock ffh)
        ((Ptr <$>) . flip (putRawBlock False) h)

{- |
    It's potentially useful to copy the contents of a 'FixFile' to a new
    location as a backup. The 'clone' function essentially runs 'vacuum'
    on a 'FixFile', but writes the output to the specified path.
-}
clone :: Root r => FilePath -> FixFile r -> IO ()
clone fp ff = openBinaryFile fp ReadWriteMode >>= cloneH ff

{- |
    Because a 'FixFile' is backed by an append-only file, there is a periodic
    need to 'vacuum' the file to garbage collect data that is no longer
    referenced from the root. This task operates on a temporary file that then
    replaces the file that backs FixFile.

    The memory usage of this operation scales with the recursive depth of the
    structure stored in the file.
-}
vacuum :: Root r => FixFile r -> IO ()
vacuum ff@(FixFile path mv _) = withWriteLock ff runVacuum where
    runVacuum = do
        (tp, th) <- openTempFile (takeDirectory path) ".ffile.tmp"
    
        cloneH ff th

        (FixFile _ newMV _) <- openFixFileHandle tp th

        renameFile tp path

        void $ takeMVar mv
        readMVar newMV >>= putMVar mv


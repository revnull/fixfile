{-# LANGUAGE DeriveGeneric, FlexibleInstances #-}

module TestFixFile(testFixFile) where

import Data.Binary
import Data.FixFile
import Data.FixFile.Tree23

import Test.Tasty
import Test.Tasty.QuickCheck
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Test.QuickCheck.Gen
import Test.QuickCheck.Gen.Unsafe
import System.IO.Temp
import System.IO
import System.Directory
import GHC.Generics

import Control.Monad
import Control.Monad.Trans
import Control.Exception hiding (assert)
import Control.Applicative hiding (empty)
import Data.Maybe

import Control.Lens
import Control.Concurrent
import Control.Concurrent.MVar
import System.Timeout

data TestRoot g =
    TR (Ref (TreeD (Map Int String)) g) (Ref (TreeD (Set String)) g)
    deriving (Generic)

instance Binary (TestRoot Ptr)

instance Root (TestRoot) where
    readRoot (TR a b) = TR <$> readRoot a <*> readRoot b
    writeRoot (TR a b) = TR <$> writeRoot a <*> writeRoot b
    rootIso (TR a b) = TR (rootIso a) (rootIso b)

emptyTR :: TestRoot Fix
emptyTR = TR (Ref empty) (Ref empty)

tr1 :: Lens' (TestRoot g) (Ref (TreeD (Map Int String)) g)
tr1 = lens (\(TR a _) -> a) (\(TR _ b) a -> TR a b)

tr2 :: Lens' (TestRoot g) (Ref (TreeD (Set String)) g)
tr2 = lens (\(TR _ b) -> b) (\(TR a _) b -> TR a b)

withTestFile :: (FilePath -> Handle -> IO a) -> PropertyM IO a
withTestFile = liftIO . withSystemTempFile "testfile"

prop_FileInsert :: [(Int, String)] -> Property
prop_FileInsert xs = monadicIO testIns where
    testIns = do
        (res1, res2) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle emptyTR f h
            forM_ xs $ \(k, v) -> writeTransaction ff $ do
                subTransaction tr1 $
                    insertMapT k v
                subTransaction tr2 $
                    insertSetT v
            res1 <- readTransaction ff $ do
                subTransaction tr1 $
                    mapM lookupMapT (fmap fst xs)
            res2 <- readTransaction ff $ do
                subTransaction tr2 $
                    mapM lookupSetT (fmap snd xs)
            res1' <- evaluate $ all isJust res1
            res2' <- evaluate $ all id res2
            return (res1', res2')
        assert res1
        assert res2

prop_Vacuum :: [(Int, String)] -> Property
prop_Vacuum xs = monadicIO testVac where
    testVac = do
        (res1, res2) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle emptyTR f h
            forM_ xs $ \(k, v) -> writeTransaction ff $ do
                subTransaction tr1 $ insertMapT k v
                subTransaction tr2 $ insertSetT v
            vacuum ff
            res1 <- readTransaction ff $ do
                subTransaction tr1 $
                    mapM lookupMapT (fmap fst xs)
            res2 <- readTransaction ff $ do
                subTransaction tr2 $
                    mapM lookupSetT (fmap snd xs)
            res1' <- evaluate $ all isJust res1
            res2' <- evaluate $ all id res2
            return (res1', res2')
        assert res1
        assert res2

prop_FileDelete :: [(Int, String)] -> [Int] -> [String] -> Property
prop_FileDelete xs deli dels = monadicIO testDels where
    testDels = do
        (res1, res2) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle emptyTR f h
            forM_ xs $ \(k, v) -> writeTransaction ff $ do
                subTransaction tr1 $ insertMapT k v
                subTransaction tr2 $ insertSetT v
            writeTransaction ff $ 
                subTransaction tr1 $
                    mapM_ deleteMapT deli
            writeTransaction ff $
                subTransaction tr2 $
                    mapM_ deleteSetT dels
            res1 <- readTransaction ff $ do
                subTransaction tr1 $
                    mapM lookupMapT deli
            res2 <- readTransaction ff $ do
                subTransaction tr2 $
                    mapM lookupSetT dels
            res1' <- evaluate $ all isNothing res1
            res2' <- evaluate $ all not res2
            return (res1', res2')
        assert res1
        assert res2

prop_OpenClose :: [(Int, String)] -> Property
prop_OpenClose xs = monadicIO testOpenClose where
    testOpenClose = do
        (res1, res2) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle emptyTR f h
            forM_ xs $ \(k, v) -> writeTransaction ff $ do
                subTransaction tr1 $
                    insertMapT k v
                subTransaction tr2 $
                    insertSetT v
            closeFixFile ff
            ff <- openFixFile f
            res1 <- readTransaction ff $ do
                subTransaction tr1 $
                    mapM lookupMapT (fmap fst xs)
            res2 <- readTransaction ff $ do
                subTransaction tr2 $
                    mapM lookupSetT (fmap snd xs)
            res1' <- evaluate $ all isJust res1
            res2' <- evaluate $ all id res2
            return (res1', res2')
        assert res1
        assert res2
            

prop_Concurrent :: [(Int, String)] -> [(Int, String)] -> Property
prop_Concurrent xs repls = monadicIO testCon where
    cleanRepl = toListMap $ (fromListMap repls :: Tree23 Fix (Map Int String))
    keys = fmap fst cleanRepl
    desired = fmap (Just . snd) cleanRepl
    readFn ff wmv resmv = do
        w <- any id <$> mapM isEmptyMVar wmv
        vals1 <- readTransaction ff $ subTransaction tr1 $
            mapM lookupMapT keys
        res1 <- evaluate $ vals1 == desired
        vals2 <- readTransaction ff $ subTransaction tr2 $
            mapM lookupSetT (fmap snd repls)
        res2 <- evaluate $ all not vals2
        if w
            then yield >> readFn ff wmv resmv
            else putMVar resmv (res1, res2)
    writeFn1 ff wmv = do
        yield
        forM_ xs $ \(k,v) -> writeTransaction ff $ subTransaction tr1 $
            insertMapT k v
        yield
        vacuum ff
        forM_ cleanRepl $ \(k, v) -> writeTransaction ff $
            subTransaction tr1 $ insertMapT k v
        putMVar wmv True
    writeFn2 ff wmv = do
        yield
        forM_ xs $ \(_, v) -> writeTransaction ff $ subTransaction tr2 $
            insertSetT v
        yield
        vacuum ff
        forM_ xs $ \(_, v) -> writeTransaction ff $ subTransaction tr2 $
            deleteSetT v
        putMVar wmv True
    wrapThread io = do
        res <- timeout 5000000 io
        case res of
            Nothing -> error "Thread Timed out"
            _ -> return ()
    testCon = do
        (res1, res2) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle emptyTR f h
            writeDone1 <- newEmptyMVar
            writeDone2 <- newEmptyMVar
            readDone <- newEmptyMVar
            let writeMs = [writeDone1, writeDone2]
            forkIO $ (wrapThread $ readFn ff writeMs readDone)
                `onException` putMVar readDone (False, False)
            forkIO $ (wrapThread $ timeout 10000000 $ writeFn1 ff writeDone1)
                `onException` putMVar writeDone1 False
            forkIO $ (wrapThread $ timeout 10000000 $ writeFn2 ff writeDone2)
                `onException` putMVar writeDone2 False
            mapM readMVar writeMs
            readMVar readDone
        assert res1
        assert res2

testFixFile = testGroup "FixFile"
    [
        testProperty "Insert" prop_FileInsert
       ,testProperty "Vacuum" prop_Vacuum
       ,testProperty "Delete" prop_FileDelete
       ,testProperty "Open/Close" prop_OpenClose
       ,testProperty "Concurrent" prop_Concurrent
    ]

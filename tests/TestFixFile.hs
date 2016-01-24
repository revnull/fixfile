
module TestFixFile(testFixFile) where

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

import Control.Monad
import Control.Monad.Trans
import Control.Exception hiding (assert)
import Control.Applicative hiding (empty)
import Data.Maybe

import Control.Concurrent
import Control.Concurrent.MVar
import System.Timeout

withTestFile :: (FilePath -> Handle -> IO a) -> PropertyM IO a
withTestFile = liftIO . withSystemTempFile "testfile"

prop_FileInsert :: [[(Int, String)]] -> Property
prop_FileInsert xss = monadicIO testIns where
    empt = empty :: Tree23 Fix (Map Int String)
    testIns = do
        res <- withTestFile $ \f h -> do
            ff <- createFixFileHandle empt f h
            forM_ xss $ \xs -> writeTransaction ff $
                mapM_ (uncurry insertMapT) xs
            res <- forM xss $ \xs -> readTransaction ff $
                mapM lookupMapT (fmap fst xs)
            evaluate $ all isJust $ concat res
        assert res

prop_Vacuum :: [[(Int, String)]] -> Property
prop_Vacuum xss = monadicIO testVac where
    empt = empty :: Tree23 Fix (Map Int String)
    testVac = do
        res <- withTestFile $ \f h -> do
            ff <- createFixFileHandle empt f h
            forM_ xss $ \xs -> writeTransaction ff $
                mapM_ (uncurry insertMapT) xs
            vacuum ff
            res <- forM xss $ \xs -> readTransaction ff $
                mapM lookupMapT (fmap fst xs)
            evaluate $ all isJust $ concat res
        assert res

prop_FileDelete :: [[(Int, String)]] -> [Int] -> Property
prop_FileDelete xss dels = monadicIO testDels where
    empt = empty :: Tree23 Fix (Map Int String)
    testDels = do
        res <- withTestFile $ \f h -> do
            ff <- createFixFileHandle empt f h
            forM_ xss $ \xs -> writeTransaction ff $
                mapM_ (uncurry insertMapT) xs
            writeTransaction ff $ mapM_ deleteMapT dels
            res <- forM xss $ \xs -> readTransaction ff $
                mapM lookupMapT dels
            evaluate $ all isNothing $ concat res
        assert res

prop_Concurrent :: [[(Int, String)]] -> [(Int, String)] -> Property
prop_Concurrent xss repls = monadicIO testCon where
    empt = empty :: Tree23 Fix (Map Int String)
    cleanRepl = toListMap $ (fromListMap repls :: Tree23 Fix (Map Int String))
    keys = fmap fst cleanRepl
    desired = fmap (Just . snd) cleanRepl
    readFn ff wmv resmv = do
        w <- isEmptyMVar wmv
        vals <- readTransaction ff $
            mapM lookupMapT keys
        res <- evaluate $ vals == desired
        if w then readFn ff wmv resmv else putMVar resmv res
    writeFn ff wmv = do
        forM_ xss $ \xs -> writeTransaction ff $
            mapM_ (uncurry insertMapT) xs
        vacuum ff
        forM_ cleanRepl $ \(k, v) -> writeTransaction ff $ insertMapT k v
        putMVar wmv True
    testCon = do
        (ws, rs) <- withTestFile $ \f h -> do
            ff <- createFixFileHandle empt f h
            writeDone <- newEmptyMVar
            readDone <- newEmptyMVar
            forkIO $ (void $ timeout 5000000 $ readFn ff writeDone readDone)
                `onException` putMVar readDone False
            forkIO $ (void $ timeout 5000000 $ writeFn ff writeDone)
                `onException` putMVar writeDone False
            writeSuccess <- readMVar writeDone
            readSuccess <- readMVar readDone
            return (writeSuccess, readSuccess)
        assert ws
        assert rs

testFixFile = testGroup "FixFile"
    [
        testProperty "Insert" prop_FileInsert
       ,testProperty "Vacuum" prop_Vacuum
       ,testProperty "Delete" prop_FileDelete
       ,testProperty "Concurrent" prop_Concurrent
    ]

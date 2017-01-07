
module Data.FixFile.Trie.Shared (
                                 bigThreshold
                                ,lookupAscending
                                ,splitKey
                                ) where

import Data.ByteString.Lazy as BS

bigThreshold :: Int
bigThreshold = 20

splitKey :: BS.ByteString -> BS.ByteString ->
    (BS.ByteString, BS.ByteString, BS.ByteString)
splitKey x y = case (BS.uncons x, BS.uncons y) of
    (Nothing, Nothing) -> (BS.empty, BS.empty, BS.empty)
    (Nothing, Just _) -> (BS.empty, x, y)
    (Just _, Nothing) -> (BS.empty, x, y)
    (Just (xc, xs), Just (yc, ys)) -> if xc == yc
        then let (shared, xt, yt) = splitKey xs ys
            in (BS.cons xc shared, xt, yt)
        else (BS.empty, x, y)

lookupAscending :: Ord a => a -> [(a, b)] -> Maybe b
lookupAscending _ [] = Nothing
lookupAscending k ((x,y):xs) = case compare x k of
    LT -> lookupAscending k xs
    EQ -> Just y
    _ -> Nothing


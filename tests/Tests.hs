
import Test.Tasty

import TestSet
import TestTree23
import TestTrie
import TestBTree
import TestLightBTree
import TestFixFile

main :: IO ()
main = defaultMain $
    testGroup "FixFile"
    [
        test23
       ,testSet
       ,testTrie
       ,testBTree
       ,testLightBTree
       ,testFixFile
    ]


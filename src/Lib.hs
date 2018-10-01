module Lib
    ( someFunc
    ) where

import Prelude hiding (length, map, filter, head, tail, foldl1)
import Language.Haskell.Liquid.Prelude (liquidError)

{-@ length :: xs:[a] -> {v: Int | v = (len xs)} @-}
length :: [a] -> Int
length []     = 0
length (x:xs) = 1 + length xs

{-@ xs :: {v:[String] | (len v) = 1 } @-}
xs = "dog" : []

{-@ ys :: {v:[String] | (len v) = 2 } @-}
ys = ["cat", "dog"]

{-@ zs :: {v:[String] | (len v) = 3 } @-}
zs = "hippo" : ys


someFunc :: IO ()
someFunc = putStrLn "someFunc"

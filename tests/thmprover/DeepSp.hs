{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
-- {-@ LIQUID "--no-termination" @-}
module DeepSp where

import GHC.Base
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ reflect fib @-}
{-@ fib :: i:Nat -> Nat / [i] @-}
fib :: Int -> Int
fib i | i == 0 = 0
      | i == 1 = 1
      | otherwise = fib (i-1) + fib (i-2)

{-@ type OnePlusOne = { 1 + 1 == 2 } @-}

{-@ propOnePlueOne :: _ -> OnePlusOne @-}
propOnePlueOne _ = trivial *** QED

{-@ reflexivity :: i:{v:Int | v == 0} -> y:{v:Int | v == 0} -> {i == y} @-}
reflexivity :: Int -> Int -> Proof -- This is necessary for typechecking for liquid
reflexivity _ _ = trivial *** QED

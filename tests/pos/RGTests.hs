{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--no-termination" @-}

module RGTests where

import RG
import Data.IORef
import GHC.Base
import Language.Haskell.Liquid.Prelude
import Language.Haskell.Liquid.ProofCombinators

{-@ generic_accept_stable :: forall <p :: a -> Bool, r :: a -> a -> Bool >.
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    ()
                    @-}
generic_accept_stable :: (a -> a -> a) -> ()
generic_accept_stable pf = ()

{-@ generic_accept_reflexivity :: forall <p :: a -> Bool, r :: a -> a -> Bool>.
                    x: a<p> -> y: a<r x> -> { x == y }
  @-}
  -- could do { x > 0 && y > 0 }
generic_accept_reflexivity :: a -> a -> Proof
generic_accept_reflexivity x y
  =   x
  ==. y
  ==. undefined -- proves_reflexivity x y (hmm...how?)
  *** QED

{-@ proves_reflexivity :: x:{v:Int | v > 0} -> y:{v:Int | v > 0} -> {v:Int | v > 0} @-}
proves_reflexivity :: Int -> Int -> Int
proves_reflexivity x y = x

test :: ()
test = generic_accept_stable proves_reflexivity


{-@ coerce :: forall <p :: a -> Bool, r :: a -> a -> Bool >.
              f:(x:a<p> -> a<r x>) ->
              pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
              a<p> ->
              a<p> @-}
coerce :: (a -> a) -> (a -> a -> a) -> a -> a
coerce f pf v = pf v (f v)

{-@ test_injectStable :: ref:RGRef<{\x -> x > 0}
                                  ,{\x y -> x <= y}
				  ,{\x y -> x <= y}> Int ->
                         {v : Int | ((pastValue ref v) && (v > 20) && (v >= 0))} ->
                         {x : RGRef<{\x -> x >= 0}
				   ,{\x y -> x <= y}
				   ,{\x y -> x <= y}> Int | x = ref} @-}
test_injectStable :: RGRef Int -> Int -> RGRef Int
test_injectStable ref v = injectStable ref v

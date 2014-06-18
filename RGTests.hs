module RGTests where

import RG
import Data.IORef
import GHC.Base
import Language.Haskell.Liquid.Prelude

{-@ generic_accept_stable :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
                    f:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
                    ()
                    @-}
generic_accept_stable :: (a -> a -> a) -> ()
generic_accept_stable pf = ()

{-@ proves_reflexivity :: x:{v:Int | v > 0} -> y:{v:Int | v > 0} -> {v:Int | v > 0} @-}
proves_reflexivity :: Int -> Int -> Int
proves_reflexivity x y = x

test :: ()
test = generic_accept_stable proves_reflexivity


{-@ test_axiom :: forall <p :: a -> Prop, r :: a -> a -> Prop>.
    ir:IORef a -> 
    rr:{r:RGRef<p,r> a | ((rgref_ref r) = ir)} ->
    v:a ->
    w:{rw:RealWorld | (pointsTo ir rw v)} ->
    {w2:RealWorld | (rgpointsTo (Wrap ir) w2 v)}
@-}
test_axiom :: IORef a -> RGRef a -> a -> RealWorld -> RealWorld
test_axiom ir (Wrap rr) v w = liquidAssume (axiom_rgpointsTo rr w v) w

{-@ coerce :: forall <p :: a -> Prop, r :: a -> a -> Prop >.
              f:(x:a<p> -> a<r x>) ->
              pf:(x:a<p> -> y:a<r x> -> {v:a<p> | (v = y)}) ->
	      a<p> ->
	      a<p> @-}
coerce :: (a -> a) -> (a -> a -> a) -> a -> a
coerce f pf v = pf v (f v)
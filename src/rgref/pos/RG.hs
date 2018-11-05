module RG where

import Language.Haskell.Liquid.Prelude
import Data.IORef as R
import GHC.Base
import Unsafe.Coerce

{-@ data RGRef a < p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>
         = Wrap (rgref_ref :: R.IORef a <p>)
  @-}

data RGRef a = Wrap (R.IORef a)
  deriving Eq

{-@  assume forgetIOTriple :: forall < p :: RealWorld -> Bool, r :: RealWorld -> a -> Bool, q :: a -> Bool>.
                              IO (a<q>) -> IO (a<q>)
@-}
forgetIOTriple :: IO a -> IO a
forgetIOTriple a = a

{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}

{-@ measure getsnd :: (a, b) -> b
    getsnd (x, y) = y
  @-}

{-@ newRGRef :: forall < p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool >.
                       { x :: a<p> |- a<r x> <: a<p> }
                       { x :: a<p> |- a<g x> <: a<r x> }
                       { x :: a<p> |- {v : a | v = x} <: a <g x> }
                       e : a <p> ->
                       IO (RGRef <p, r, g> a) @-}
newRGRef :: a -> IO (RGRef a)
newRGRef e = do r <- newIORef e
                return (Wrap r)

{-@ measure pastValue :: RGRef a -> a -> Bool @-}
{-@ measure pastValueb :: RGRef a -> b -> Bool @-}
{-@ measure terminalValue :: RGRef a -> a @-}
{-@ measure shareValue :: RGRef a -> a @-}

{-@ assume axiom_pastIsTerminal :: forall < p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
                             ref : RGRef<p,r,g> a ->
                             v : { v : a | (pastValue ref v)} ->
                             (x : { x : a | x = v } -> y : a <r x> -> { z : a | ((z = y) && (z = x))}) ->
                             (x : { x : a | x = v } -> y : a <g x> -> { z : a | ((z = y) && (z = x))}) ->
                             { b : Bool | (((terminalValue ref) = v) <=> (pastValue ref v))}
                             @-}
axiom_pastIsTerminal :: RGRef a -> a -> (a -> a -> a) -> (a -> a -> a) -> Bool
axiom_pastIsTerminal = undefined

{-@ assume injectStable :: forall < p :: a -> Bool,
                                    q :: a -> Bool,
                                    r :: a -> a -> Bool,
                                    g :: a -> a -> Bool>.
                                    {x :: a <q> |- a <r x> <: a<q>}
                                    ref : RGRef <p, r, g> a ->
                                    {v : a <q> | (pastValue ref v)} ->
                                    {r : (RGRef <q, r, g> a) | (ref = r)}
@-}
injectStable :: RGRef a -> a -> RGRef a
injectStable ref v = liquidAssume undefined ref

{-@ assume injectStable2 :: forall <p :: a -> Bool, 
                                         q :: a -> Bool,
                                         r :: a -> a -> Bool,
                                         g :: a -> a -> Bool>.
                    pf:(j:a<q> -> k:a<r j> -> {z:a<q> | z = k}) ->
                    ref:RGRef<p,r,g> a ->
                    {v:a<q> | (pastValue ref v)} ->
                    {r : (RGRef<q,r,g> a) | (ref = r)} @-}
injectStable2 :: (a -> a -> a) -> RGRef a -> a -> RGRef a
injectStable2 pf ref v = liquidAssume undefined ref

{-@ measure translate :: RGRef a -> RGRef b @-}

-- {-@ assume downcast :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>. 
--                 { x::b |- b <: a }
--                 { x::b |- b<r x> <: b<p> }
--                 ref:RGRef<p,r,g> a ->
  --                 { v:b | pastValue ref v } ->
--                 { r : RGRef<p,r,g> b | ref == r } @-}
{-@ assume downcast :: forall <p :: b -> Bool, r :: b -> b -> Bool, g :: b -> b -> Bool>. 
                   { x :: b |- b <: a }
                   { x :: b |- b<r x> <: b<p> }
                   ref : RGRef a -> 
                   { v : b | pastValueb ref v } -> 
                   { r : RGRef<p,r,g> b | (translate ref) == r } 
  @-}
downcast :: RGRef a -> b -> RGRef b
downcast r v = (unsafeCoerce r)

{-@ assume typecheck_pastval :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
                                x:RGRef<p,r,g> a ->
                                v:{v:a | (pastValue x v)} ->
                                {q:a | (q = v)} @-}
typecheck_pastval :: RGRef a -> a -> a
typecheck_pastval x v = v

{-@ assume readRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool, pre :: RealWorld -> Bool>.
                    x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
readRGRef (Wrap x) = readIORef x

{-@ assume readRGRef2 :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool, pre :: RealWorld -> Bool>.
                    x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
readRGRef2 (Wrap x) = readIORef x

-- Again, would be nice to tie to pointsTo
{-@ assume writeRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>. 
                          x:(RGRef<p,r,g> a) -> 
                          old:a -> 
                          new:a<r old> -> 
                          (IO ()) @-}
writeRGRef :: RGRef a -> a -> a -> IO ()
writeRGRef  (Wrap x) old new = writeIORef x new

{- assume Data.IORef.modifyIORef :: forall <p :: a -> Bool>. IORef a<p> -> (a<p> -> a<p>) -> IO () @-}

{-@ modifyRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
modifyRGRef :: RGRef a -> (a -> a) -> IO ()
modifyRGRef (Wrap x) f = modifyIORef x f --(\ v -> pf v (f v))

{-@ modifyRGRef' :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
-- TODO: strictify, so we don't de-optimize modifyIORef' calls
modifyRGRef' :: RGRef a -> (a -> a) -> IO ()
modifyRGRef' (Wrap x) f = modifyIORef' x f --(\ v -> pf v (f v))

{-@ atomicModifyRGRef :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool >.
                    {x::a<p> |- a<g x> <: a<p>}
                    rf:(RGRef<p, r, g> a) ->
                    f:(x:a<p> -> a<g x>) ->
                    IO () @-}
atomicModifyRGRef :: RGRef a -> (a -> a) -> IO ()
atomicModifyRGRef (Wrap x) f = atomicModifyIORef' x (\ v -> ((f v),()))

{- The following is an adaptation of atomCAS from GHC's testsuite/tests/concurrent/prog003/CASList.hs -}
{-@ rgCAS :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool >.
             {x::a<p> |- a<g x> <: a<p>}
             Eq a =>
             RGRef<p,r,g> a -> old:a<p> -> new:a<g old> ->
             IO Bool
@-}
rgCAS :: Eq a => RGRef a -> a -> a -> IO Bool
rgCAS (Wrap ptr) old new =
   atomicModifyIORef' ptr (\ cur -> if cur == old
                                   then (new, True)
                                   else (cur, False))

{-@ rgCASpublish :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool, pb :: b -> Bool, rb :: b -> b -> Bool, gb :: b -> b -> Bool>.
             {x::a<p> |- a<g x> <: a<p>}
             {x::b<pb> |- b<rb x> <: b<pb>}
             {x::b<pb> |- b<gb x> <: b<rb x>}
             {x::b<pb> |- {v:b | v = x} <: b<gb x>}
             Eq a =>
             e:b<pb> ->
             RGRef<p,r,g> a -> old:a<p> -> new:(({r:(RGRef<pb,rb,gb> b) | shareValue r = e}) -> a<g old>) ->
             IO Bool
@-}
rgCASpublish :: Eq a => b -> RGRef a -> a -> (RGRef b -> a) -> IO Bool
rgCASpublish e (Wrap ptr) old new =
   do pub <- newRGRef e
      atomicModifyIORef' ptr (\ cur -> if cur == old
                                      then (new (liquidAssume (coerceb pub e) pub), True)
                                      else (cur, False))

{-@ assume coerceb :: forall <pb :: b -> Bool, rb :: b -> b -> Bool, gb :: b -> b -> Bool>.
              r:RGRef<pb,rb,gb> b -> e:b -> {x:Bool | shareValue r = e} @-}
coerceb :: RGRef b -> b -> Bool
coerceb r e = undefined

-- {-@ assume safe_covar :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
--                  { x::a |- a <: b }
--                  { x::a<p> |- a<g x> <: b }
--                  ref:RGRef<p,r,g> a ->
--                  {r : RGRef<p,r,g> b | ref == r } @-}
-- ref:RGRef<p,r,g> a ->
{-@ assume safe_covar :: forall <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool>.
                 { x::a |- a <: b }
                 { x::a<p> |- a<g x> <: b }
                 ref:RGRef<p,r,g> a ->
                 {r : RGRef b | (translate ref) == r } @-}
safe_covar :: RGRef a -> RGRef b
safe_covar r = unsafeCoerce r

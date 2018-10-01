{-# LANGUAGE NoMonomorphismRestriction, GADTs #-}

{-@ LIQUID "--notermination"           @-}
{-@ LIQUID "--short-names"             @-}
{-@ LIQUID "--ple"                     @-}

module RG where

import Language.Haskell.Liquid.Prelude
import Data.IORef as R
import GHC.Base
import Unsafe.Coerce
import Prelude hiding (break, exists, repeat, succ)
--import Data.List hiding (break)

--chain :: (b -> c -> Bool) -> (a -> b -> Bool)
--      -> (a -> c -> Bool) ->  a -> b -> c -> Bool
--chain p q r = \ x y z -> q x y ==> p y z ==> r x z

repeat :: Int -> (a -> a) -> a -> a
goal   :: Int -> Int
     
{-@ bound step @-}
step :: (a -> a -> Bool) -> (Int -> a -> Bool) -> Int -> a -> a -> Bool
step pf pr = \ i x x' -> pr (i - 1) x ==> pf x x' ==> pr i x'

-- This syntax is not yet supported in liquidhaskell-8
{- repeat :: forall a <f :: a -> a -> Bool, r :: Int -> a -> Bool>.
                (Step a f r) => 
                 n:Nat -> (y:a -> a<f y>) -> a<r 0> -> a<r n>
  @-}


{-@ repeat :: forall a <f :: a -> a -> Bool, r :: Int -> a -> Bool>.
                {i::Int, x::a<r (i-1)>|- a<f x> <:a <r i>}
                 n:Nat -> (y:a -> a<f y>) -> a<r 0> -> a<r n>
  @-}
repeat 0 _ x = x
repeat n f x = repeat (n - 1) f (f x)

{-@ goal :: n:Nat -> {r:Nat | n <= r} @-}
goal n = repeat n (+ 1) 0

{-@ data BST a = Leaf
               | Node { root  :: a
                      , left  :: BSTL a root
                      , right :: BSTR a root } @-}
{-@ type BSTL a X = BST {v:a | v < X}             @-}
{-@ type BSTR a X = BST {v:a | X < v}             @-}
data BST a = Leaf
           | Node { root  :: a
                  , left  :: BST a
                  , right :: BST a }



{-@ data Assoc v <p :: Int -> Bool> = KV { keyVals :: [(Int<p>, v)] } @-}
data Assoc v = KV [(Int, v)]

{-@ data IRef a <p :: a -> Bool> = Wrap (iref_ref :: IORef a<p>) @-}
data IRef a = Wrap (IORef a)


--{-@ max2 :: forall <p :: Int -> Prop>. 
--            Int<p> -> Int<p> -> Int<p> @-}
--max2     :: Int -> Int -> Int
--max2 x y = if x <= y then y else x 

--type Table t v = [Dict t v]

--data Dict key val = D {ddom :: [key], dfun :: key -> val}
--{-@ ddom :: forall <range :: key -> val -> Bool>.
--           x:Dict <range> key val  -> {v:[key] | v = ddom x}
--  @-}


--data ST s a = ST {runState :: s -> (a,s)}
--
--{-@ data ST s a <p :: s -> Prop, q :: s -> s -> Prop, r :: s -> a -> Prop> 
--  = ST (runState :: x:s<p> -> (a<r x>, s<q x>)) @-}
--
--{-@ runState :: forall <p :: s -> Bool, q :: s -> s -> Bool, r :: s -> a -> Bool>. ST <p, q, r> s a -> x:s<p> -> (a<r x>, s<q x>) @-}



{-@ predicate Btwn Lo V Hi = (Lo <= V && V <= Hi) @-}

-- Monomorphic Association Lists
-- -----------------------------


-- Dependent Tuples via Abstract Refinements
-- 
-- data (a, b)<p :: a -> b -> Prop> = (x:a, b<p x>)

-- Instantiate the `p` in *different* ways.

--{-@ plusOnes :: [(Int, Int)<{\x1 x2 -> x2 = x1 + 1}>] @-}
--plusOnes = [(0,1), (5,6), (999,1000)]

{-@ break :: (a -> Bool) -> x:[a]
          -> ([a], [a])<\y -> {z:[a] |  (Break x y z)}> @-}

{-@ predicate Break X Y Z   = (len X) = (len Y) + (len Z) @-}
break                   :: (a -> Bool) -> [a] -> ([a], [a])
break _ xs@[]           =  (xs, xs)
break p xs@(x:xs')
           | p x        =  ([], xs)
           | otherwise  =  let (ys, zs) = break p xs'
                           in (x:ys,zs)

type Size    = Int



-- {-@ data Tree a <l :: a -> a -> Prop, r :: a -> a -> Prop>
--   = Leaf
--   | Node { c   :: Col
--          , key :: a
--          , lt  :: Tree<l,r> a<l key>
--          , rt  :: Tree<l,r> a<r key> } @-}

-- {-@ data RGRef a = Wrap (rgref_ref :: R.IORef a) @-}


--{-@ data RGRef a <p :: a -> Bool, r :: a -> a -> Bool, g :: a -> a -> Bool> 
--    = Wrap (rgref_ref :: R.IORef a<p>) @-}
--data RGRef a = Wrap (R.IORef a)
--    deriving Eq

-- {-@ assume forgetIOTriple :: forall <p :: RealWorld -> Prop, r :: RealWorld -> a -> Prop, q :: a -> Prop>.
--                              IO (a<q>) -> IO (a<q>) @-}
-- forgetIOTriple :: IO a -> IO a
-- forgetIOTriple a = a
-- 
-- {- A stability proof can be embedded into LH as a function of type:
--     x:a<p> -> y:a<r x> -> {v:a<p> | v = y}
--     This encodes the requirement that knowing P x and R x y is sufficient to deduce P y.
-- -}
-- {- A relational implication can be embedded as a function of type:
--     x:a -> y:a<g x> -> {v:() | r x y }
-- -}
-- 
{-@ measure getfst :: (a, b) -> a
    getfst (x, y) = x
  @-}
{-@ measure getsnd :: (a, b) -> b
    getsnd (x, y) = y
  @-}

{- TODO: e2 is a hack to sidestep the inference of false for r,
   it forces r to be inhabited. -}
-- -- ((r (getfst v) (getsnd v)) /\ (v = (x,y)))
-- {-@ newRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
--                     {x::a<p> |- a<r x> <: a<p>}
--                     {x::a<p> |- a<g x> <: a<r x>}
--                     {x::a<p> |- {v:a | v = x} <: a<g x>}
--                     e:a<p> -> 
--                     IO (RGRef <p, r, g> a) @-}
-- newRGRef :: a -> IO (RGRef a)
-- newRGRef e = do r <- newIORef e
--                 return (Wrap r)

-- -- We'll be needing some witness of past values
-- {-@ measure pastValue :: RGRef a -> a -> Prop @-}
-- {-@ measure terminalValue :: RGRef a -> a @-}
-- -- This is for carrying strong (identity) refinement into sharing/publication
-- {-@ measure shareValue :: RGRef a -> a @-}
-- 
-- {-@ assume axiom_pastIsTerminal :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
--                              ref:RGRef<p,r,g> a ->
--                              v:{v:a | (pastValue ref v)} ->
--                              (x:{x:a | x = v} -> y:a<r x> -> {z:a | ((z = y) && (z = x))}) ->
--                              (x:{x:a | x = v} -> y:a<g x> -> {z:a | ((z = y) && (z = x))}) ->
--                              { b : Bool | (((terminalValue ref) = v) <=> (pastValue ref v))}
--                              @-}
-- axiom_pastIsTerminal :: RGRef a -> a -> (a -> a -> a) -> (a -> a -> a) -> Bool
-- axiom_pastIsTerminal = undefined
-- 
-- {- A more general, but less pleasant to use way to exploit observations of stable properties.
--  - If we observe that some past value of ref has property q, and q is stable w.r.t. r, we can
--  - conclude that current and future values of ref also satisfy q. -}
-- {-@ assume injectStable :: forall <p :: a -> Prop, 
--                                          q :: a -> Prop,
--                                          r :: a -> a -> Prop,
--                                          g :: a -> a -> Prop>.
--                     {x::a<q> |- a<r x> <: a<q>}
--                     ref:RGRef<p,r,g> a ->
--                     {v:a<q> | (pastValue ref v)} ->
--                     {r : (RGRef<q,r,g> a) | (ref = r)} @-}
-- injectStable :: RGRef a -> a -> RGRef a
-- injectStable ref v = liquidAssume undefined ref
-- -- TODO: Can we do the above without undefined? it gives a warning...
-- {-@ assume injectStable2 :: forall <p :: a -> Prop, 
--                                          q :: a -> Prop,
--                                          r :: a -> a -> Prop,
--                                          g :: a -> a -> Prop>.
--                     pf:(j:a<q> -> k:a<r j> -> {z:a<q> | z = k}) ->
--                     ref:RGRef<p,r,g> a ->
--                     {v:a<q> | (pastValue ref v)} ->
--                     {r : (RGRef<q,r,g> a) | (ref = r)} @-}
-- injectStable2 :: (a -> a -> a) -> RGRef a -> a -> RGRef a
-- injectStable2 pf ref v = liquidAssume undefined ref
-- -- TODO: Can we do the above without undefined? it gives a warning...
-- 
-- {-@ assume downcast :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
--                 { x::b |- b <: a }
--                 { x::b |- b<r x> <: b<p> }
--                 ref:RGRef<p,r,g> a ->
--                 {v:b | pastValue ref v } ->
--                 {r : RGRef<p,r,g> b | ref = r } @-}
-- downcast :: RGRef a -> b -> RGRef b
-- downcast r v =  (unsafeCoerce r)
-- 
-- 
-- {-@ assume typecheck_pastval :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
--                                 x:RGRef<p,r,g> a ->
--                                 v:{v:a | (pastValue x v)} ->
--                                 {q:a | (q = v)} @-}
-- typecheck_pastval :: RGRef a -> a -> a
-- typecheck_pastval x v = v
-- 
-- {-@ assume readRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
--                     x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
-- readRGRef (Wrap x) = readIORef x
-- 
-- {-@ assume readRGRef2 :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pre :: RealWorld -> Prop>.
--                     x:RGRef<p, r, g> a -> IO ({res:a<p> | (pastValue x res)}) @-}
-- readRGRef2 (Wrap x) = readIORef x
-- 
-- -- Again, would be nice to tie to pointsTo
-- {-@ assume writeRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>. 
--                           x:(RGRef<p,r,g> a) -> 
--                           old:a -> 
--                           new:a<r old> -> 
--                           (IO ()) @-}
-- writeRGRef :: RGRef a -> a -> a -> IO ()
-- writeRGRef  (Wrap x) old new = writeIORef x new
-- 
-- {- assume Data.IORef.modifyIORef :: forall <p :: a -> Prop>. IORef a<p> -> (a<p> -> a<p>) -> IO () @-}
-- 
-- {-@ modifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
--                     {x::a<p> |- a<g x> <: a<p>}
--                     rf:(RGRef<p, r, g> a) ->
--                     f:(x:a<p> -> a<g x>) ->
--                     IO () @-}
-- modifyRGRef :: RGRef a -> (a -> a) -> IO ()
-- modifyRGRef (Wrap x) f = modifyIORef x f --(\ v -> pf v (f v))
-- 
-- {-@ modifyRGRef' :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
--                     {x::a<p> |- a<g x> <: a<p>}
--                     rf:(RGRef<p, r, g> a) ->
--                     f:(x:a<p> -> a<g x>) ->
--                     IO () @-}
-- -- TODO: strictify, so we don't de-optimize modifyIORef' calls
-- modifyRGRef' :: RGRef a -> (a -> a) -> IO ()
-- modifyRGRef' (Wrap x) f = modifyIORef' x f --(\ v -> pf v (f v))
-- 
-- {-@ atomicModifyRGRef :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
--                     {x::a<p> |- a<g x> <: a<p>}
--                     rf:(RGRef<p, r, g> a) ->
--                     f:(x:a<p> -> a<g x>) ->
--                     IO () @-}
-- atomicModifyRGRef :: RGRef a -> (a -> a) -> IO ()
-- atomicModifyRGRef (Wrap x) f = atomicModifyIORef' x (\ v -> ((f v),()))
-- 
-- {- The following is an adaptation of atomCAS from GHC's testsuite/tests/concurrent/prog003/CASList.hs -}
-- {-@ rgCAS :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop >.
--              {x::a<p> |- a<g x> <: a<p>}
--              Eq a =>
--              RGRef<p,r,g> a -> old:a<p> -> new:a<g old> ->
--              IO Bool
-- @-}
-- rgCAS :: Eq a => RGRef a -> a -> a -> IO Bool
-- rgCAS (Wrap ptr) old new =
--    atomicModifyIORef' ptr (\ cur -> if cur == old
--                                    then (new, True)
--                                    else (cur, False))
-- 
-- {-@ rgCASpublish :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop, pb :: b -> Prop, rb :: b -> b -> Prop, gb :: b -> b -> Prop>.
--              {x::a<p> |- a<g x> <: a<p>}
--              {x::b<pb> |- b<rb x> <: b<pb>}
--              {x::b<pb> |- b<gb x> <: b<rb x>}
--              {x::b<pb> |- {v:b | v = x} <: b<gb x>}
--              Eq a =>
--              e:b<pb> ->
--              RGRef<p,r,g> a -> old:a<p> -> new:(({r:(RGRef<pb,rb,gb> b) | shareValue r = e}) -> a<g old>) ->
--              IO Bool
-- @-}
-- rgCASpublish :: Eq a => b -> RGRef a -> a -> (RGRef b -> a) -> IO Bool
-- rgCASpublish e (Wrap ptr) old new =
--    do pub <- newRGRef e
--       atomicModifyIORef' ptr (\ cur -> if cur == old
--                                       then (new (liquidAssume (coerce pub e) pub), True)
--                                       else (cur, False))
--            where
--            {-@ assume coerce :: forall <pb :: b -> Prop, rb :: b -> b -> Prop, gb :: b -> b -> Prop>.
--                          r:RGRef<pb,rb,gb> b -> e:b -> {x:Bool | shareValue r = e} @-}
--            coerce :: RGRef b -> b -> Bool
--            coerce r e = undefined
-- 
-- {-@ assume safe_covar :: forall <p :: a -> Prop, r :: a -> a -> Prop, g :: a -> a -> Prop>.
--                 { x::a |- a <: b }
--                 { x::a<p> |- a<g x> <: b }
--                 ref:RGRef<p,r,g> a ->
--                 {r : RGRef<p,r,g> b | ref = r } @-}
-- safe_covar :: RGRef a -> RGRef b
-- safe_covar r = unsafeCoerce r
-- 

{-@ LIQUID "--no-totality" @-}
{-@ LIQUID "--reflection"  @-}

module Problems where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RGRef.RG
import Language.Haskell.Liquid.Prelude



{-@ predicate SetRG X Y =
    (((isNull X) && (isNode Y)) ||
     ((isNode X) && (isDel Y) && ((val X) = (val Y)) && ((nxt X) = (nxt Y))) ||
     ((isNode X) && (isNode Y) && (isDel (terminalValue (nxt X))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((isHead X) && (isHead Y) && (isDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
     ((isNode X) && (isNode Y) && ((val X) = (val Y)) && (nxt X = nxt (shareValue (nxt Y)))) ||
     ((isHead X) && (isHead Y) && (nxt X = nxt (shareValue (nxt Y)))) ||
     (X = Y)
     )
@-}

-- setRG x y =
--   where
--     nullAndNode = isNull x && isNode y
--     nodeAndDel  = isNode x && isDel y && (val x == val y) && (nxt x == nxt y)
--   ((isNode x) && (isNode y) && (isDel (terminalValue (nxt x))) && ((val X) = (val Y)) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
--   ((isHead X) && (isHead Y) && (isDel (terminalValue (nxt X))) && ((nxt (terminalValue (nxt X))) = (nxt Y))) ||
--   ((isNode X) && (isNode Y) && ((val X) = (val Y)) && (nxt X = nxt (shareValue (nxt Y)))) ||
--   ((isHead X) && (isHead Y) && (nxt X = nxt (shareValue (nxt Y)))) ||
--   (X = Y)


-- {-@
-- data Set a <p :: a -> Bool > = 
--     Node (node_val :: a<p>) (slack :: { v : a | node_val <= v}) (node_next :: ((RGRef<{\x -> (1 > 0)}
--                                                                                      ,{\x y -> (SetRG x y)}
--                                                                                      ,{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a))))
--   | DelNode (del_val :: a<p>) (slack :: { v : a | del_val <= v}) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a)))
--   | Null
--   | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
-- @-}
data Set a 
    = Node a a ((RGRef (Set a)))
    | DelNode a a ((RGRef (Set a)))
    | Null
    | Head ((RGRef (Set a))) deriving Eq

-- ISSUE 1: crash when checking myNext

-- {-@ reflect myNext @-}
-- {-@ myNext :: l:{x:Set a | not (isNull x) } -> 
--               {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)}
-- 	      ,{\x y -> (SetRG x y)}> (Set <{\x -> ((isHead l) || (slack l < x))}> a) 
-- 	      ((nxt l) = r) 
-- 
-- @-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v lb n) = n
myNext (DelNode v lb n) = n
myNext (Head n) = n

{-@ reflect nodeclass @-}
nodeclass :: Set a -> Int
nodeclass (Head n) = 0
nodeclass (Node v lb n) = 1
nodeclass (DelNode v lb n) = 2
nodeclass (Null) = 3


{-@ reflect isHead @-}
isHead :: Set a -> Bool
isHead x = (nodeclass x == 0)
{-@ reflect isNode @-}
isNode :: Set a -> Bool
isNode x = (nodeclass x == 1)
{-@ reflect isDel @-}
isDel :: Set a -> Bool
isDel x  = (nodeclass x == 2)
{-@ reflect isNull @-}
isNull :: Set a -> Bool
isNull x = (nodeclass x == 3)

{-@ reflect nxt @-}
nxt :: Set a -> (RGRef (Set a))
nxt (Node v lb n) = n
nxt (DelNode v lb n) = n
nxt (Head n) = n

{-@ reflect val @-}
val :: Set a -> a
val (Node v lb n) = v
val (DelNode v lb n) = v

-- {-@ measure nxt :: Set a -> (RGRef (Set a))
--     nxt (Node v lb n) = n
--     nxt (DelNode v lb n) = n
--     nxt (Head n) = n
-- @-}
-- {-@ measure val :: Set a -> a
--     val (Node v lb n) = v
--     val (DelNode v lb n) = v
-- @-}

--    -- ISSUE 2: Can't instantiate an axiom properly
--    -- When this is Int, it works.  When we use Set Int, it fails, giving a message that includes the
--    -- body of SetRG even though it's not explicitly here... something's up with the recursive pointer
--    -- {-@ injectStable3 :: forall <p :: (Set Int) -> Bool, 
--    --                                          q :: (Set Int) -> Bool,
--    --                                          r :: (Set Int) -> (Set Int) -> Bool,
--    --                                          g :: (Set Int) -> (Set Int) -> Bool,
--    --                                          z :: Int -> Bool>.
--    --                     {x::(Set <z> Int)<q> |- (Set <z> Int)<r x> <: (Set <z> Int)<q>}
--    --                     ref:RGRef<p,r,g> (Set <z> Int) ->
--    --                     {v:(Set <z> Int)<q> | (pastValue ref v)} ->
--    --                     {r : (RGRef<q,r,g> (Set <z> Int)) | (ref = r)} @-}
--    injectStable3 :: RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
--    injectStable3 ref v = undefined -- injectStable ref v
--    
--    -- trying without <z>
--    -- {-@ injectStable4 :: forall <p :: (Set Int) -> Bool, 
--    --                                          q :: (Set Int) -> Bool,
--    --                                          r :: (Set Int) -> (Set Int) -> Bool,
--    --                                          g :: (Set Int) -> (Set Int) -> Bool>.
--    --                     {x::(Set Int)<q> |- (Set Int)<r x> <: (Set Int)<q>}
--    --                     ref:RGRef<p,r,g> (Set Int) ->
--    --                     {v:(Set Int)<q> | (pastValue ref v)} ->
--    --                     {r : (RGRef<q,r,g> (Set Int)) | (ref = r)} @-}
--    injectStable4 :: RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
--    injectStable4 ref v = undefined -- injectStable ref v
--    
--    
--    -- {-@ injectExplicit :: forall <p :: (Set Int) -> Bool, 
--    --                                          q :: (Set Int) -> Bool,
--    --                                          r :: (Set Int) -> (Set Int) -> Bool,
--    --                                          g :: (Set Int) -> (Set Int) -> Bool>.
--    --                     pf:(j:(Set Int)<q> -> k:(Set Int)<r j> -> {z:(Set Int)<q> | z = k}) ->
--    --                     ref:RGRef<p,r,g> (Set Int) ->
--    --                     {v:(Set Int)<q> | (pastValue ref v)} ->
--    --                     {r : (RGRef<q,r,g> (Set Int)) | (ref = r)} @-}
--    injectExplicit :: ((Set Int) -> (Set Int) -> (Set Int)) -> RGRef (Set Int) -> (Set Int) -> RGRef (Set Int)
--    injectExplicit pf ref v = undefined -- injectStable2 pf ref v
--    
--    {-@ assume isDelOnly :: x:Set a -> 
--                            {v:Bool | ((isDel x) <=> ((not (isHead x)) && (not (isNull x)) && (not (isNode x))))} @-}
--    isDelOnly :: Set a -> Bool
--    isDelOnly x = True

-- {-@ assume isNodeOnly :: x:Set a -> 
--                         {v:Bool | ((isNode x) <=> ((not (isHead x)) && (not (isNull x)) && (not (isDel x))))} @-}
-- isNodeOnly :: Set a -> Bool
-- isNodeOnly x = True

-- {-@ injectBound :: forall <z :: a -> Bool, s :: Set a -> Bool>.
--              { x::a |- (Set<z> a)<s> <: {v:Set<z> a | (isNode v || isDel v) && val v < x } }
--    --              {x::(Set<z> a)<s> |- (Set<z> a)<SetRG x> <: (Set<z> a)<s>}
--    --              ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) ->
--    --              x:a ->
--    --              {n:(Set<z> a)<s> | pastValue ref n} ->
--    --              {r:RGRef<s,{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <z> a) | r = ref } @-}
--    injectBound :: RGRef (Set a) -> a -> Set a -> RGRef (Set a)
--    injectBound ref x n = undefined -- injectStable ref (liquidAssume (isDelOnly n) (liquidAssume (isNodeOnly n) n))

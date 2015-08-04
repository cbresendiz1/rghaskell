{-# LANGUAGE BangPatterns,CPP #-}
-- Disable termination checking; this is lock-free, not wait-free
{-@ LIQUID "--no-termination" @-}
module HellerSet where

import Control.Monad
import Data.IORef
import Control.Concurrent
import Control.Concurrent.Chan
import System.Environment
import Data.Time

import RG
import Language.Haskell.Liquid.Prelude

-- #define USE_UNPACK
-- #define USE_STRICT

#if defined(USE_UNPACK)
#define UNPACK(p) {-# UNPACK #-} !(p)
#elif defined(USE_STRICT)
#define UNPACK(p) !(p)
#else
#define UNPACK(p) p
#endif


-- Rely/Guarantee for next-pointers:
-- Permitted operations are:
-- 1. [Append] Replacing Null with a Node
-- 2. [Logical Deletion] Replacing a Node with a DelNode, preserving the next ptr
-- 3. [Physical Deletion at Node] Replacing a (Node v x) with (Node v y) if x points to (DelNode _ y) (see below)
-- 4. [Physical Deletion at Head] Bumping a Head node's next to the second node (this is a deletion, but I think there's an opt
-- 5. [Insertion at Node]
-- 6. [Insertion at Head]
-- in the delete code that skips the Node -> DelNode transition)
-- Deletion occurs not by replacing a DelNode with something else, but by replacing a Node pointing
-- to a DelNode with a given next pointer with a Node having the same value, and updated (bumped
-- forward) next pointer.  So once a reference points to a DelNode, that's permanent, making the
-- node type and next pointer /stable/.  So with a way to observe the additional stable refinement
-- that a cell has become deleted, I could actually enforce the correct management of next pointers
-- on deletion.
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
-- Also, note the progression of values a given NextPtr points to:
--     a) Null ->
--     b) Node x n ->
--     c) Node x n' -> (where n pointed to (DelNode n') or an insertion occurred); repeat b->c indefinitely
--     c) DelNode x n' ->
--     d) [disconnected]

{-@ any_stable_listrg :: x:Set a -> y:{v:Set a | (SetRG x v)} -> {v:Set a | (v = y)} @-}
any_stable_listrg :: Set a -> Set a -> Set a
any_stable_listrg x y = y

{-@ listrg_refl :: x:Set a -> y:{v:Set a | (SetRG x v)} -> {v:Set a | ((SetRG x y) && (y = v))} @-}
listrg_refl :: Set a -> Set a -> Set a
listrg_refl x y = y
-- TODO: How do I balance < vs <= in p when crossing logically-deleted nodes?
-- TODO: Do i need an Ord a here, for the version that parses?  Or is it treating node_val as a
-- measure rather than a name?
{-@
data Set a <p :: a -> Prop > = 
    Node (node_val :: a<p>) (slack :: { v : a | node_val <= v}) (node_next :: ((RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a))))
  | DelNode (del_val :: a<p>) (slack :: { v : a | del_val <= v}) (del_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (slack < x)}> a)))
  | Null
  | Head (head_next :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> (1 > 0)}> a)))
@-}
data Set a = Node a a (UNPACK(RGRef (Set a)))
            | DelNode a a (UNPACK(RGRef (Set a)))
            | Null
            | Head (UNPACK(RGRef (Set a))) deriving Eq

{-@ data SetHandle a = SetHandle (lh_head :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)))
                                 (lh_tail :: IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a))) @-}
data SetHandle a = SetHandle (UNPACK(IORef (RGRef (Set a))))
                             (UNPACK(IORef (RGRef (Set a))))

{-# INLINE myNext #-}
{-@ myNext :: l:Set a -> 
              {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\x -> ((isHead l) || (slack l < x))}> a) |
                   ((nxt l) = r) }
@-}
myNext :: Set a -> RGRef (Set a)
myNext (Node v lb n) = n
myNext (DelNode v lb n) = n
myNext (Head n) = n
myNext _ = error "myNext"

{-@ type InteriorPtr a = RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) @-}

-- LH seems fine with incomplete pattern matches here,
-- which is great.  It means fewer refinements are added
-- to each constructor, making a lot less work for inference and SMT.
{-@ measure nxt :: Set a -> (RGRef (Set a))
    nxt (Node v lb n) = n
    nxt (DelNode v lb n) = n
    nxt (Head n) = n
@-}
{-@ measure isHead :: Set a -> Prop
    isHead (Head n) = true
    isHead (Node v lb n) = false
    isHead (DelNode v lb n) = false
    isHead (Null) = false
@-}
{-@ measure isNode :: Set a -> Prop
    isNode (Node v lb n) = true
    isNode (DelNode v lb n) = false
    isNode (Null) = false
    isNode (Head n) = false
@-}
{-@ measure val :: Set a -> a
    val (Node v lb n) = v
    val (DelNode v lb n) = v
@-}
{-@ myval :: x:Set a -> {v:a | v = val x} @-}
myval (Node v lb n) = v
myval (DelNode v lb n) = v
{-@ measure isDel :: Set a -> Prop
    isDel (DelNode v lb n) = true
    isDel (Null) = false
    isDel (Head n) = false
    isDel (Node v lb n) = false
@-}
{-@ measure isNull :: Set a -> Prop
    isNull (Null) = true
    isNull (Head n) = false
    isNull (Node v lb n) = false
    isNull (DelNode v lb n) = false
@-}
-- A cleaner to show the SMT these predicates are disjoint may be to redefine them as predicates on
-- another measure mapping nodes to some SetTypeEnum...
{-@ assume isDelOnly :: x:Set a -> 
                        {v:Bool | ((isDel x) <=> ((not (isHead x)) && (not (isNull x)) && (not (isNode x))))} @-}
isDelOnly :: Set a -> Bool
isDelOnly x = undefined

-- we assume a static head pointer, pointing to the first node which must be Head
-- the deleted field of Head is always False, it's only there to make some of the code
-- more uniform
-- tail points to the last node which must be Null


{-@ type Iterator a = IORef (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)) @-}
type Iterator a = IORef (RGRef (Set a))


-------------------------------------------
-- auxilliary functions



while b cmd = if b then do {cmd; while b cmd}
              else return ()

repeatUntil cmd = do { b <- cmd; if b then return ()
                                  else repeatUntil cmd }

atomCAS :: Eq a => IORef a -> a -> a -> IO Bool
atomCAS ptr old new =
   atomicModifyIORef ptr (\ cur -> if cur == old
                                   then (new, True)
                                   else (cur, False))

atomicWrite :: IORef a -> a -> IO ()
atomicWrite ptr x =
   atomicModifyIORef ptr (\ _ -> (x,()))


----------------------------------------------
-- functions operating on lists

{-@ dummyRef :: (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a)) @-}
dummyRef :: (RGRef (Set a))
dummyRef = undefined

{-@ allocNull :: forall <p :: a -> Prop>.
                 IO (RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a)) @-}
allocNull :: IO (RGRef (Set a))
allocNull = 
   let memo_null = Null in
   newRGRef memo_null

-- we create a new list
newSet :: IO (SetHandle a)
newSet = 
   --do null <- newRGRef memo_null memo_null any_stable_listrg
   do null <- allocNull
      let memo_hd = Head null 
      hd <- newRGRef memo_hd
      hdPtr <- newIORef hd
      tailPtr <- newIORef null
      return (SetHandle hdPtr tailPtr)


-- Wrap rgCAS with the refinements made concrete, to help inference
{-@ rgSetCAS :: Eq a =>
                 RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) ->
                 old:(Set a) ->
                 new:{v:(Set a) | (SetRG old v)} ->
                 IO Bool
@-}
rgSetCAS :: Eq a => RGRef (Set a) -> Set a -> Set a -> IO Bool
rgSetCAS r old new = rgCAS r old new --any_stable_listrg

-- I exported pastValue via qualif, but simply defining this fixes qualifier inference....
{-@ readPastValue :: x:InteriorPtr a -> IO ({v:(Set a) | (pastValue x v)}) @-}
readPastValue :: RGRef (Set a) -> IO (Set a)
readPastValue x = readRGRef2 x


{-@ terminal_listrg :: rf:InteriorPtr a -> v:{v:Set a | (isDel v)}->
                       x:{x:Set a | (x = v)} ->y:{y:Set a | (SetRG x y)} -> {z:Set a | ((x = z) && (z = y))} @-}
terminal_listrg :: RGRef (Set a) -> Set a -> Set a -> Set a -> Set a
terminal_listrg rf v x y = liquidAssume (isDelOnly x) y

{-@ downcast_set :: y:a -> 
                    ref:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> y < v}> a) ->
                    x:{x:a | x < y} ->
                    {v:(Set <{\v -> x < v}> a) | pastValue ref v } ->
                    {r:RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <{\v -> x < v}> a) | r = ref } @-}
downcast_set :: a -> RGRef (Set a) -> a -> Set a -> RGRef (Set a)
downcast_set y r x v = downcast r v

insert :: Ord a => SetHandle a -> a -> IO Bool
insert (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
  where
     {-@ go :: forall <p :: a -> Prop >.
               RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) -> IO Bool @-}
     go !prevPtr =
        do prevNode <- readRGRef2 prevPtr
           -- note this next line skips over the head 
           let curPtr = myNext prevNode
           curNode <- forgetIOTriple (readRGRef curPtr)
           case curNode of
             Node y lb nextNode ->
                if x == y
                then return False --- already present, not added
                else if y < x
                     then go nextNode 
                     else --- insertion!  add between previous and current
                        case prevNode of
                          Node prevVal vlb q -> do let a = liquidAssert (x <= y) True
                                                   let b = liquidAssert (vlb <= y) a
                                                   let c = liquidAssert (prevVal <= y) b
                                                   let d = liquidAssert (prevVal <= x) c
                                                   let e = liquidAssert (x < y) d
                                                   let f = liquidAssert (x < myval curNode) e
                                                   let g = liquidAssert (q == curPtr) f
                                                   let h = liquidAssert (False) g
                                                   -- #1
                                                   -- So we know curNode :: Set<{\v-> x < v},...,...>
                                                   -- but the type system only infers x<y, and
                                                   -- doesn't push this back to curNode's refinement,
                                                   -- doesn't push this back into the Set index
                                                   -- as a result,
                                                   -- curPtr2 doesn't get the refinement we want
                                                   -- We're trying to push this into the ref
                                                   -- refinement, since it should get desugared to
                                                   -- the same thing 
                                                   -- we have curNode::Set<{\v -> vlb < v}>, and
                                                   -- myval curNode == y
                                                   -- Seems overly restrictive to require x < vlb
                                                   -- here.  It's sort of implicit from the
                                                   -- pastValue requirement on downcast(_set).
                                                   -- Maybe lift that.  Still stuck on getting
                                                   -- curNode's type related to x, but I think this
                                                   -- is the right track.
                                                   let curPtrC = downcast_set vlb curPtr x curNode
                                                   let newNode = liquidAssert h (Node x x curPtrC)
                                                   -- #2 and apparently also because it can't prove
                                                   -- prevVal <= x.  Need to refine type of go for
                                                   -- lb?  
                                                   b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Node prevVal prevVal ptr)
                                                   if b then return True else go prevPtr
                          Head _ -> do let newNode = (Node x x curPtr)
                                       b <- rgCASpublish newNode prevPtr prevNode (\ptr -> Head ptr)
                                       if b then return True else go prevPtr
                          DelNode _ _ _ -> undefined -- TODO: go startPtr -- predecessor deleted, try again
             Null -> -- TODO insert at end... subset of previous case
                     undefined
             DelNode v lb nextNode -> 
                     case prevNode of
                       Node prevVal vlb q -> do let refinedtail = (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) (nextNode))
                                                b <- rgSetCAS prevPtr prevNode (Node prevVal (liquidAssert (prevVal < v) lb) (refinedtail))
                                                if b then go prevPtr else go curPtr
                       Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                    if b then go prevPtr else go curPtr
                       DelNode _ _ _ -> go curPtr    -- if parent deleted simply move ahead

find :: Ord a => SetHandle a -> a -> IO Bool
find (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: forall <p :: a -> Prop >.
                RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set <p> a) -> IO Bool @-}
      go !prevPtr =
           do prevNode <-  readRGRef2 prevPtr
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y lb nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      return True
                   else go curPtr -- continue
                Null -> return False -- reached end of list; TODO short-circuit based on bounds
                DelNode v lb nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node prevVal vlb q -> do let refinedtail = (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) (nextNode))
                                                   let _ = liquidAssert (q == curPtr) True
                                                   b <- rgSetCAS prevPtr prevNode (Node prevVal (liquidAssert (prevVal < v) lb) (refinedtail))
                                                   if b then go prevPtr else go curPtr
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ _ -> go curPtr    -- if parent deleted simply move ahead




delete :: Eq a => SetHandle a -> a -> IO Bool
delete (SetHandle head _) x =
  do startPtr <- readIORef head
     go startPtr
   where
      {-@ go :: RGRef<{\x -> (1 > 0)},{\x y -> (SetRG x y)},{\x y -> (SetRG x y)}> (Set a) -> IO Bool @-}
      go prevPtr =
        do do prevNode <- forgetIOTriple (readRGRef prevPtr)
              let curPtr = myNext prevNode -- head/node/delnode have all next
              curNode <- forgetIOTriple (readRGRef curPtr)
              case curNode of
                Node y lb nextNode ->
                   if (x == y)
                   then -- node found and alive 
                      do b <- rgSetCAS curPtr curNode (DelNode y lb nextNode)
                         if b then return True
                          else go prevPtr -- spin
                   else go curPtr -- continue
                Null -> return False -- reached end of list; TODO shortcircuit
                DelNode v lb nextNode -> 
                         -- atomically delete curNode by setting the next of prevNode to next of curNode
                         -- if this fails we simply move ahead
                        case prevNode of
                          Node v2 v2lb _ -> do b <- rgSetCAS prevPtr prevNode (Node v2 lb (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                               if b then go prevPtr else go curPtr
                          --Head {} -> do b <- rgSetCAS prevPtr prevNode (Head nextNode)
                          Head _ -> do b <- rgSetCAS prevPtr prevNode (Head (liquidAssume (axiom_pastIsTerminal curPtr curNode (terminal_listrg curPtr curNode) (terminal_listrg curPtr curNode)) nextNode))
                                       if b then go prevPtr else go curPtr
                          DelNode _ _ _ -> go curPtr    -- if parent deleted simply move ahead



























-- pad html render
--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

module spec GHC.Base where

-- must begin by reproducing the LH include/GHC/Base.spec, since this one will override the original, not supplement it
import GHC.Prim
import GHC.Classes
import GHC.Types

embed GHC.Types.Int      as int
embed Prop               as bool

measure Prop   :: GHC.Types.Bool -> Prop

measure len :: forall a. [a] -> GHC.Types.Int
len ([])     = 0
len (y:ys)   = 1 + (len ys)

measure null :: forall a. [a] -> Prop
null ([])   = true
null (x:xs) = false

measure fst :: (a,b) -> a
fst (a,b) = a

measure snd :: (a,b) -> b
snd (a,b) = b

invariant {v: [a] | len(v) >= 0 }
map       :: (a -> b) -> xs:[a] -> {v: [b] | len(v) = len(xs)}
(++)      :: xs:[a] -> ys:[a] -> {v:[a] | (len v) = (len xs) + (len ys)}

$         :: (a -> b) -> a -> b
id        :: x:a -> {v:a | v = x}

 

--assume bindIO :: forall <p :: RealWorld -> Prop, q :: RealWorld -> a -> Prop, r :: a -> RealWorld -> a -> Prop>.
--                          (IO<p,q> a -> (x:a -> IO<q x,r x>) -> IO<p,{\ w v -> (exists[x:a].(r x w v))}> b)

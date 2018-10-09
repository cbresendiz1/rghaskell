{-@ LIQUID "--short-names" @-}
{-@ LIQUID "--higherorder" @-}

module Logic where

main :: IO()
main = return ()

{-@ measure size @-}
size :: [a] -> Int
size [] = 0
size (x:xs) = 1 + size xs

{-@ (<=>) :: p:Bool -> q:Bool -> {v:Bool | v <=> (p <=> q)} @-}
False <=> False = True
False <=> True  = False
True  <=> True  = True
True  <=> False = False

{-@ size :: xs : [a] -> {v:Int | v = size xs} @-}

{-@ (==>) :: p: Bool -> q: Bool -> {v:Bool | v <=> (p ==> q)} @-}
False ==> False = True
False ==> True  = True
True  ==> True  = True
True  ==> False = False

{-@ type TRUE  = {v:Bool | v    } @-}
{-@ type FALSE = {v:Bool | not v} @-}

{-@ fx0 :: [a] -> [a] -> TRUE @-}
fx0 xs ys = (xs == ys) ==> (size xs == size ys)

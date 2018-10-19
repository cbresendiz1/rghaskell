module BadMeasureParse where

{-@ measure multiParam :: Int -> Int -> Bool @-}

{-@ assume v :: {x : Int | (multiParam x (x+1))} @-}
v :: Int
v = undefined

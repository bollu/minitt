A simple type-theoretic language: Mini-TT

I finally managed to piece together a curricula for learning how to implement dependently typed languages by recursive paper-chasing:
1. [MiniTT paper](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf)
2. CoC from ATAPL
3. CIC from A compact kernel for the calculus of inductive constructions
4. CubicalTT from cubicalTT
5. Pfenning, constructive logic: http://www.cs.cmu.edu/~fp/courses/15317-f17/schedule.html

#### Running

```
$ ghci Main.hs
ghci> :main examples/bool.rkt 
file contents:
(let Bool U
   (Sum [true 1] [false 1]))
```

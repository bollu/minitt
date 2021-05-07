A simple type-theoretic language: Mini-TT

I finally managed to piece together a curricula for learning how to implement dependently typed languages by recursive paper-chasing:

1. [MiniTT paper](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf)
2. CoC from ATAPL
3. CIC from A compact kernel for the calculus of inductive constructions
4. CubicalTT from cubicalTT
5. Pfenning, constructive logic: http://www.cs.cmu.edu/~fp/courses/15317-f17/schedule.html

Reading on normalization by evaluation:

1. NBE for typed STLC: [Wiki article](https://en.wikipedia.org/wiki/Normalisation_by_evaluation), 
   [Favonia's introduction to NBE](https://www.youtube.com/watch?v=atKqqiXslyo)
2. NBE for untyped LC: [A Denotational Account of Untyped Normalization by Evaluation](https://link.springer.com/content/pdf/10.1007%2F978-3-540-24727-2_13.pdf
)

Reading on bidirectional type checking:

1. [Bidirectional typing, compose conf video](https://www.youtube.com/watch?v=utyBNDj7s2w)
2. [Bidirectional Typing by JOSHUA DUNFIELD & NEEL KRISHNASWAMI](https://arxiv.org/abs/1908.05839)



#### Running

```
$ ghci Main.hs
ghci> :main examples/bool.rkt 
file contents:
(let Bool U
   (Sum [true 1] [false 1]))
```

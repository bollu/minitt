A simple type-theoretic language: Mini-TT

I finally managed to piece together a curricula for learning how to implement dependently typed languages by recursive paper-chasing:

1. [MiniTT paper](http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf)
1. [Andrej Bauer: how to implement dependent type theory 1](http://math.andrej.com/2012/11/08/how-to-implement-dependent-type-theory-i/)
1. [Tiark Rompf: minimal dependent types in javascript](https://tiarkrompf.github.io/notes/?/dependent-types/aside4)
1. [Checking dependent types with NBE, based on the little typer](http://davidchristiansen.dk/tutorials/nbe/)
1. CoC from ATAPL
1. CIC from A compact kernel for the calculus of inductive constructions
1. CubicalTT from cubicalTT
1. [Pfenning, lecture notes handout on bidirectional typing (great)!](https://www.cs.cmu.edu/~fp/courses/15312-f04/handouts/15-bidirectional.pdf)

Reading on normalization by evaluation:

1. NBE for typed STLC: [Wiki article](https://en.wikipedia.org/wiki/Normalisation_by_evaluation), 
   [Favonia's introduction to NBE](https://www.youtube.com/watch?v=atKqqiXslyo)
2. NBE for untyped LC: [A Denotational Account of Untyped Normalization by Evaluation](https://link.springer.com/content/pdf/10.1007%2F978-3-540-24727-2_13.pdf
)

Reading on bidirectional type checking:

1. [Bidirectional typing, compose conf video](https://www.youtube.com/watch?v=utyBNDj7s2w)
2. [Bidirectional Typing by JOSHUA DUNFIELD & NEEL KRISHNASWAMI](https://arxiv.org/abs/1908.05839)



Reading on surface syntax issues:

1. [Eliminating dependent pattern matching](https://static.googleusercontent.com/media/research.google.com/en//pubs/archive/99.pdf)
2. [The view from the left](http://strictlypositive.org/vfl.pdf)
3. [Elimination with a motive](https://citeseerx.ist.psu.edu/viewdoc/download?doi=10.1.1.1085.8468&rep=rep1&type=pdf#:~:text=An%20elimination%20rule%20with%20an,allow%20the%20corresponding%20recursive%20calls.)


Reading on implementing tactics:
- [TheoryCS answer](https://cstheory.stackexchange.com/a/5697/49498)
- [A tactic language for system Coq](http://www.lirmm.fr/~delahaye/papers/ltac%20(LPAR%2700).pdf)
- Implementing Tactics and Tacticals in a Higher-order Programming Language


# Bidirectional type checking by Pfenning

To check if the rules of a typing judgement yield a type checking algorithm,
we use Pfenning's recipe. First, some syntax. Given a typing rule `val : ty` I'll call the
  `val` part the LHS/LEFT, the `ty` part the RHS/RIGHT. Given a judgement of
  the form:

```
v1:t1, v2:t2, ... vn:tn
------------------------
v':t'
```

I will call the `v1:t1`, `vi:ti` as the TOP and the `v':t'` the BOT. This gives us a visual
coordinate system to talk about a typing judgement. The flow of information goes in the direction of
`bottom-left` -> `top-left` -> `top-right` -> `bottom-right`. (imagine a `∩` shape over the judgement),
like so:

```
           MID
  v1→t1 → v2→t2 ... → vn→tn
--↑----------------------↓--
  v'                    :t'
START                    END
```

> For typing rules with multiple premises we analyze the premises from left
> to right. For each premise we first show that all inputs are **known** and
> outputs are **free**. Then, we assume all outputs are **known** before checking
> the next premise.  After the last premise has been checked we still have to
> show that the outputs of the conclusion are all known by now. As an example,
> consider the rule for function application.

```
e1: t2 -> t; e2: t2
--------------------
 apply(e1, e2) : t
```

Applying the technique we have, type checking fails:
1. We start with bottom-left `apply(e1, e2)`. From this, we assume that `e1, e2` are GIVEN
1. We start checking top-left `e1 : t2`.
1. The LHS `e1` is GIVEN, and the RHS `t2 -> t` is FREE. Thus, this rule is correct.
1. We now finish on the rule `e1 : t2 -> t` and assume that `t2`, `t` are also GIVEN (`e1` was always given).
1. We proceed to start checking `e2 : t2`.
1. the LHS `e2` is GIVEN, but the RHS `t2` is NOT FREE, since it is GIVEN from `t2 -> t`.
1. Thus, we FAIL.

To fix the failure, we rewrite the judgement, by swapping the order of `e2:t2`
and `e1: t2 -> t`:


```
e1: t2 -> t; e2: t2';  t2'=t2:Void
--------------------
 apply(e1, e2) : t
```

1. We start with bottom-left `apply(e1, e2)`. From this, we assume that `e1, e2` are GIVEN.
1. We start checking top-left `e1:t2->t`.
1. The LHS `e1` is GIVEN. The rhs `t2->t` is FREE. Thus, this rule is correct.
1. We finish on the rule `e1:t2->t`, and assume that `t2`, `t` are also GIVEN.
1. We proceed to start checking `e2:t2'`.
1. The LHS `e2` is GIVEN, the RHS `t2'` is FREE.
1. We finish on the rule `e2:t2`, and assume that from now on `t2` is GIVEN.
1. We start checking the top-right `t2' = t2: Void`.
1. The LHS `t2', t2` is GIVEN. the RHS `Void` is nonsensical, and is thus always FREE.
1. Finally, we start checking the bottom-right `t`.
1. We need to check that `t` is GIVEN, which is true. Hence, we are done.

Meditate on the fact that this is in fact algorithmic type checking. We can
literally derive an algorithm from this bottom-left to top-left to top-right to
bottom-right construction we have going on here to type-check `apply(e1, e2)`.


Also see that here, we assumed that we HAD the face that `e1: t2 -> t` and `e2: t2'`,
and that we could check `t2' = t2. That is, we had the types, we simply wanted
to check the type of `apply(e1, e2)`. However, in reality, if we can _infer_
that `e1` has type `ti -> to`, we can then CHECK that `e2` has type `ti` and INFER that 
`apply(e1, e2)` has type `to`. We will write this as:

```
e1 => ti -> to; e2 <= ti;
--------------------
 apply(e1, e2) => to
```

- `expr => T` means "`expr` implies it has type `T` / we can infer that `expr` has type `T`.
- `expr <= T` means that "`expr` can be checked to have type `T`".

- Elimination forms (projectors) can be in synthesis mode since they are
  "projections". Thus by "conservation of information".  since they are losing
  information at the value level, they maybe able to synthesize information at
  the type level.  `info(large val) = info(small val) + info(small ty)` is the
  rough heuristic in my mind. For example, an identifier `x` can be seen as a projection/elimination
  of the _environment_, and thus its type must be synthesized. Similarly, a function application `(f $ x)`
  is an elimination of the arrow `→`. Its type can be synthesized by synthesizing a type for `f` to find the
  output type. 
- Introduction forms (constructors) are generally in type checking mode, since one cannot synthesize types "out of nothing"
  in general. For example, if we see `[]`, we can't synthesize a type because we don't know if it's a list of int/float/whatever.
  if we see `Left 'a'`  we can't synthesize a type because we only know it's `Either Char ?` where the `?` is unknowable.
  If we see a `\x -> ()` we can't synthesize a type because we only know the type is `? -> ()`. We don't know what type of `x`
  is.
- In summary: we will generally check
  constructors/products/lambdas/introduction, and infer
  destructors/projection/applications/elimination.

Let's now consider the rule for lambdas `λ(x:t). e`. Since a `λ` is used to introduce an arrow `->`
at the type level, the judgement's conclusion will be in CHECKING mode. We have the rule:

```
   Γ,x:ti ⊢ e <= to
----------------------
    Γ ⊢ λ(x:ti).e <= ti -> to
```

Let's check the mode:
1. Given `Γ ⊢λ(x:ti).e <= ti -> to` [we are given the `ti <= to` since it's an
   input to the type checker].
1. Let's start processing `Γ,x:ti ⊢ e <= to`
1. We are GIVEN `Γ,x,ti,e` and `to` from the input. There is nothing to produce
   as output, thus we are done.
1. We are GIVEN `ti, to`. Thus we are done.
1. This is not super clear. It makes way more sense to think of it algorithmically, where we need
   some things as inputs and others as outputs. The idea is that any point in time, we should have all
   our inputs and our outputs must be undetermined. **That's IT**.


Let's next look at the rule for function applications.

```
 Γ⊢e1 => ti -> to;  Γ⊢e2 <= ti
---------------------------
 Γ⊢  apply(e1, e2) => to
```

1. Given `Γ⊢  apply(e1, e2)`. We are not given a `to` since we don't know what it should be.
1. In  `Γ⊢e1 => ti -> to`, `Γ, e1` are GIVEN, thus we have the inputs. `ti, to` are FREE thus we are free
   to synthesize any `ti -> to` we want.
1. In `Γ⊢e2 <= ti`, we are given `Γ, e2, ti`. Thus we can check this expression and we are done.
1. Finally, we need to produce a `to`, which we can indeed do. Thus we are done.


In general, we have a rule that mediates between inference and checking, which says that
if `e` is to be checked as type `t`, and we can infer `e` as type `s`, then `s`
must be consistent with `t`.

```
Γ⊢e => s; s≤ t
----------------[MEDIATE-CHECK-INFER]
Γ⊢e <= t
```

1. We start with `e` and `t` given.
1. Given `e`, we synthesize an `s` which is free.
1. We then check that `s ≤ t`, where both `s` and `t` are known. Done.


For sums, we type-check, because intuitively, given only the left type, it is
impossible to know what the right hand side type is given only the left hand side
(and vice versa).

```
x <= s
----------[SUM-INTRO-L]
Γ⊢left(x) <= s + t
```

Here, notice that it is unclear if we should have gone with `x <= s` or `x =>
s`. However, Pfenning's discipline makes it clear. Since we already have `x, s,
t` as inputs from the bottom, we musn't "waste information", and we must check
that `x <= s`, as inferring a new type would mean that the type we infer would
not be free. We could have written a rule like:

```
x => s'; s' ≤ s
----------[SUM-INTRO-L-SYNTH]
Γ⊢left(x) <= s + t
```

which would obey Pfenning's discipline. However, this new rule `SUM-INTRO-L-SYNTH`
that synthesizes an `s'` and checks that `s' ≤ s` is already subsumed in the rule `MEDIATE-CHECK-INFER`.


```
x <= t
----------
Γ⊢right(x) <= s + t
```
```
For `case` analysis, we choose to do type checking so that we don't
need to compute least upper bounds. If we are willing to compute LUBs,
we would have inferred the type of a `case`. In this version of the `case` type
definition, we infer the type of scrutinee.

```
e => tl + tr;  xl:tl⊢el:s; xr:tr⊢er:s
-------------
case(e, xl.el, xr.er) <= s
```

For recursive types, `roll/ana` should be type-checked as it is a constructor,
and `unroll/cata` should be type inferred. Recall that the fixed point of a type
`\t -> <type-expr>` is given by μt.<type-expr>`. For example, the type of `List x`
is given by `μt.1+xt`, since the fixed point of this becomes `1 + x(1 + x(1 + x(...` which 
is equal to `1 + x + x^2 + ...`.  The inference rule for `roll` and `unroll` is:

```
 e <= {μt.σ}[t:=σ]
---------------
 roll(e) <= μt.σ
```

`roll` takes a `μt.σ` with one layer exposed and then "rolls it back in".
For example, recall that `nat = μt.1+t`, since we get the type as morally `1 + (1 + (1 + ...)`, that is,
we have an infinite number of trivial construtors, for `0, 1, 2, ...`.
we can write `zero = roll (Left (◊))` where `◊:1` is the single inhabitant
of the unit type. We consider `Left(◊):1+(μt.1+t)`, and thus `roll(Left(◊))` produces a `μt.1+t` by rolling it up.
Similarly, we can define the successor function as `succ x = roll(Right(x))` which
has type `(μt.1+t) -> (μt.1+t)`. See that `x: μt.1+t` and `Right(x):1+ μt.1+t`, and thus
`roll(Right(x)):μt.1+t`.

```
 e => μt.σ
---------------
 unroll(e) => μt.σ[t:=σ]
```


So far, we haven't needed any type annotations at all. This is magical, how is
this possible?  This is possible because our type inference algorithm is not
COMPLETE!  There are many situations where we want to synthesize a type for an
expression, but we only know how to check that expression, and thus we get
STUCK.  For example, when a construction and elimination form meet. In general,
say we have something like `elim(cons)`. The `elim` wishes to infer the type of
the `cons` (eg. think of the sum type).  However, the `cons` only knows how to
check its type, not infer. Thus, we get stuck. Another situation like this 
is of the form `(λx.x) $ 3`.  Here, the `$` will attmpt to infer the type of `(λx.x)`,
but we only know how to check the type of `(λx.x)`. Hence, we will need a type
annotation `(λx.x : int -> int) $ 3`. This is generally okay, because programmers
supposedly, according to Pfenning, tend to take such redexes and convert the LHS into a
definition, which can be annotated with a type and commented and whatnot.

We add a rule to our type system on how to support annotations. This rule tells
us that if `x` is annotated with `t`, then we can synthesize that `x` has type `t`
provided that type checking `x` to have type `t` succeeds.
The type checking rule `x <= t` can then trigger the type synthesis rule (`MEDIATE-CHECK-INFER`)
to find `x => t` if necessary.


```
 x <= t
---------------------[ANNOTATE]
 annotate(x, t) => t
```



# NBE

We see that the neutral terms in NBE correspond only to _eliminators_. The intuition is that
constructors are always "freely buildable", since they are the free fragment of the semantics.
The only place where reduction/computation/crunching happens is at the eliminators. Thus,
it is only at the eliminators that we can get stuck. Hence, NBE will have neutral values
for thing like (1) variables, which eliminate the context, (2) applications, which eliminate the
arrow, (3) recursion schemes of naturals, because this eliminates the naturals, etc. Also, for all
of these, the "syntactic fragment" of the neutral object (which recall holds on to both syntax and normal forms)
will hold syntactic fragments of the thing we are eliminating, and semantic values  of the other arguments.
For example, (1) neutral-applications (`Nap Neutral ValAndTy`) hold on to a
syntactic description of the function, and a semantic `Val` of the argument (2)
recursion scheme for naturals (`Nrec Type Neutral ValAndTy ValAndTy`) holds on
to a syntactic description of the `nat` and a semantic `Val` of the other
arguments `type`, `base`, `step`.


#### Running

```
$ ghci Main.hs
ghci> :main examples/bool.rkt 
file contents:
(let Bool U
   (Sum [true 1] [false 1]))
```

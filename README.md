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


Reading on future things of interest:

- [Pi Sigma: Dependent types without the sugar](https://www.andres-loeh.de/PiSigma/PiSigma.pdf)


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

we need to define value representations of each _introduction form_ / _constructor_,
because these are the values that can be built up. Therefore, we will *never get stuck*
at a constructor, because we can *always* build a value from a constructor.


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


> Because every Absurd is neutral, do-ind-Absurd has only cases for
> neutral targets.

I think every absurd is neutral because Absurd has no constructors.


# Bidirectional dependeng Type checking with elaboration

> When examining types, looking for specific type constructors, the type
> checker matches against their values. This ensures that the type checker
> never forgets to normalize before checking, which could lead to types
> that contain unrealized computation not being properly matche

> For instance, the typing rules for `ind-Nat` might give rise to the type 
> `((λ (k) Atom) zero)` for the base. Attempting to use that expression as the
> type for `'sandwich` would be incorrect without first reducing it.
> Using values, which cannot even represent redexes, removes the need to worry
> about normalization prior to inspection.


- why is `U`'s type synthesized? shouldn't it be checked, being a constructor? `;)`
- Similarly, why is `Esigma`'s type synthesized?
- Elaboration simply replaces expressions with annotated expressions (ie, `Eannotated { ty :: Expr, val :: Expr}`).
  It DOES NOT RETURM `(Type=Val, Expr)` where `Type` is a normal form.

##### `car`

To implement the type-checking of `car`, I implemented this as:

```hs
nbe :: [(Name, Type)] -> Type -> Exp -> Either String Exp
nbe ctx t e = do 
    v <- val ctx e
    readbackVal ctx t v 

synth ctx (Ecar p) = do
    tpe <- synth ctx p
    tpe' <- nbe ctx UNIV tpe 
    tleft <- case tpe' of
            Esigma x tleft tright -> return tleft
            _ -> Left $ "expected Ecar to be given value of Σ type." <>
                        "Value |" <> show p <> "| " <>
                        "has non-Σ type |" <> show tpe' <> "|"
    return (Eannotate tleft (Ecar p))
```

while the tutorial implements this as:

```lisp
[`(car ,pr)
  (go-on ([`(the ,pr-ty ,pr-out) (synth Γ pr)])
    (match (val (ctx->env Γ) pr-ty)
      [(SIGMA A D)
        (go `(the ,(read-back-norm Γ (THE (UNI) A)) (car ,pr-out)))]
      [non-SIGMA
        (stop e (format "Expected Σ, got ~v"
        (read-back-norm Γ (THE (UNI) non-SIGMA))))]))]
```
I find the final-step:

```lisp
(read-back-norm Γ (THE (UNI) non-SIGMA))
```

Confusing. Why do we know that `non-SIGMA` lives in `UNIV`? *EDIT*: I 
understand now. The value we match on is `(match (val (ctx->env Γ) pr-ty))`. Notice
that `pr-ty` comes from `[(the ,pr-ty ,pr-out) (synth Γ pr)]`. Correctness of
`synth` guarantees that `pr-ty` lives in `UNIV`, and thus the normal form 
computed by `val` (`non-SIGMA`) will live in `UNIV`. This ensures that
`read-back-norm` does the right thing. Also notice that I depend on exactly the
same thing! The line `tpe' <- nbe ctx UNIV tpe` relies on the fact that `nbe`
will return me an elaborated expression taht lives in `UNIV`!

Also note that my implementation does not return the elaborated version of `p`
at `return (Eannotate tleft (Ecar p))`. This tells us that I should probably
pattern-match on the output of `synth ctx p` and then discriminate error
messages on that basis:

```hs
synth ctx (Ecar p) = do
    (Eannotate pty pelab) <- synth ctx p
               ^^^eval this
    ptyv <- val ctx pty
    tleft <- case ptyv of
            SIGMA left _ -> readbackVal ctx UNIV left
            nonSigma -> do 
                ptyve <- readbackVal ctx UNIV nonSigma
                Left $ "expected Ecar to be given value of Σ type." <>
                        "Value |" <> show pelab <> "| " <>
                        "has non-Σ type |" <> show ptyve <> "|"
    -- | return the elaborated version of p.
    return (Eannotate tleft (Ecar pelab))
```

My previous implementation of:

```hs
tpe <- synth ctx p
```

was straight up wrong, because `synth` returns an `Eannotate`, NOT a type!
TODO: I should really think of changing the return type of `synth`.


##### `cdr`

Inventing evidence is wrong; And yet, that is what I did on my first
try to implement `cdr`. I create a fake variable `let x = NEU lv (Nvar xname)`
and then use this to type check `cdr`. Rather, what I ought to do is to
extract out the `car` of the value by evaluation, and then use it to
build the type of the `cdr`.

```hs
-- | Original broken impl that invents evidence.
synth ctx (Ecdr p) = do
    (Eannotate pty pelab) <- synth ctx p
    ptyv <- val ctx pty
    case ptyv of
      SIGMA lv rclosure -> do 
          let xname = fresh (map fst ctx) "x"
          let x = NEU lv (Nvar xname)
          rv <- valOfClosure rclosure x
          re <- readbackVal ctx UNIV rv
          return (Eannotate re (Ecar pelab))
      nonSigma -> do 
        ptyve <- readbackVal ctx UNIV nonSigma
        Left $ "expected Ecar to be given value of Σ type." <>
                "Value |" <> show pelab <> "| " <>
                        "has non-Σ type |" <> show ptyve <> "|"
```

Corrected imlementation that produces an `x` by evaluation:

```hs
-- | Correct haskell imeplementation
synth ctx (Ecdr p) = do
    (Eannotate pty pelab) <- synth ctx p
    ptyv <- val ctx pty
    case ptyv of
      SIGMA lt rtclosure -> do 
          lv <- val ctx (Ecar p)
          rt <- valOfClosure rtclosure lv
          rte <- readbackVal ctx UNIV rt
          return (Eannotate rte (Ecar pelab))
      nonSigma -> do 
        ptyve <- readbackVal ctx UNIV nonSigma
        Left $ "expected Ecar to be given value of Σ type." <>
                "Value |" <> show pelab <> "| " <>
                        "has non-Σ type |" <> show ptyve <> "|"
```

I also have quite a large problem in naming these variables. The fact
that `type, val, kind` are all synonyms makes naming strange. I am considering
moving to name things by "level", so `val -> 0`, `type -> 1`, `kind -> 2`, and
so on.  So, the variable `lv` (the `car` of the pair) becomes `l0`. The value
`rt` (the type of the RHS of the Σ-type) becomes `r1`, and so on.
##### indnat

I forgot to elaborate all my arguments:

```hs
synth ctx (Eindnat etarget emotive ebase estep) = do
    target' <- check ctx etarget NAT
    targetv <- val ctx target'

    motive' <- check ctx emotive (PI NAT (ClosureShallow "_" $ \_ -> return UNIV))
    motivev <- val ctx motive' -- motive or motive'?

    doAp motivev ZERO >>= check ctx ebase  -- WHOOPS, forgot to use return
    check ctx estep (indNatStepType motivev) -- WHOOPS

    motivetargetve <- doAp motivev targetv >>= readbackVal ctx UNIV
    return (Eannotate motivetargetve (Eindnat target' motive' ebase estep))
```


I also switched to the naming convention where the values that are derived
after checking are called `out`. This seems to be a nice way to be explicit
about what is happening. Also, chaining data to eliminate intermediates using
`>>=` greatly improves readability.

```hs
synth ctx (Eindnat etarget emotive ebase estep) = do
    targetout <- check ctx etarget NAT
    motiveout <- check ctx emotive (PI NAT (ClosureShallow "_" $ \_ -> return UNIV))
    motivev <- val ctx motiveout
    targetv <- val ctx targetout

    baseout <- doAp motivev ZERO >>= check ctx ebase 
    stepout <- check ctx estep (indNatStepType motivev)

    motivetargetve <- doAp motivev targetv >>= readbackVal ctx UNIV
    return (Eannotate motivetargetve 
                      (Eindnat targetout motiveout baseout stepout))
```

##### equality type `(eq A from to)`:

I got it right!

```hs
synth ctx (Eeq te frome toe) = do
    tout <- check ctx te UNIV
    toutv <- val ctx tout
    fromout <- check ctx frome toutv
    toout <- check ctx toe toutv
    return $ (Eannotate Euniv (Eeq tout fromout toout))
```


##### replace:

My implementation:

```hs
synth ctx (Ereplace etarget emotive ebase) = do
    (Eannotate ttarget etargetout) <- synth ctx etarget
    check ctx ttarget UNIV -- check that lives in UNIV
    -- | pattern match the equality object to learn types of motive and base
    etargetoutv <- val ctx etargetout
    (x, from, to) <- case etargetoutv of
        EQ x from to -> return (x, from, to)
        _ -> Left $ "expected (replace  to destructure an EQ value; " <>
                  "Found | " <> show etarget <> "|"
    -- motive :: X -> UNIV
    motiveout <- check ctx emotive (PI x $ ClosureShallow "_" $ \_ -> return UNIV)
    motivev <- val ctx motiveout
    baseout <- doAp motivev from >>= check ctx ebase

    return (Ereplace etargetout motiveout baseout)
```

The racket implementation forgoes the check that `ttarget` lives in `UNIV`:

```hs
synth ctx (Ereplace etarget emotive ebase) = do
    (Eannotate ttarget etargetout) <- synth ctx etarget
    -- vvv NOT CHECKED BY RACKET IMPLEMENTATION
    -- check ctx ttarget UNIV -- check that lives in UNIV
    -- | pattern match the equality object to learn types of motive and base
    etargetoutv <- val ctx etargetout
```

I guess the idea is that checking this does not buy us anything, since we
immediately pattern match on it to see that it's an equality object, which must
live in `UNIV`.

##### `pi`

My original implementation:

```hs
-- | my initial (incorrect) implementation
-- PI = -> (DOM: UNIV) -> (x: DOM) -> (CODOM: DOM -> UNIV) -> PI (x: DOM) CODOM
synth ctx (Epi x edom ecodom) = do
    domout@(Eannotate domt _) <- check ctx edom UNIV
    domtv <- val ctx domt 
    codomout <- check ctx ecodom 
                (PI domtv $ ClosureShallow "_" $ \_ -> return UNIV)
    return (Eannotate Euniv (Epi x domout codomout))
```

This is completely wrong, since the type of the codomain cannot be a `Π` type!
It's the combination of the domain and the codomain that gives us a `Π` type!
Moreover, I should have realized that this implementation would more likely
than not have caused the implementation to loop! `check Π` would call out
to `synth Π` which would generate a `check Π` which ... . The correct solution
is to treat it like a lambda: extend the context, and then evaluate the codomain.

```hs
-- | correct implementation
synth ctx (Epi x edom ecodom) = do
    domout@(Eannotate domt _) <- check ctx edom UNIV
    domtv <- val ctx domt 
    codomout <- check ((x,domtv):ctx) ecodom UNIV
    return (Eannotate Euniv (Epi x domout codomout))
```

The implementation above is the current implementation, which sets up
the new environment by binding the type of `x` to `domtv` and then evaluating
the type of the codomain.


##### `indabsurd`

```hs
synth ctx (Eindabsurd etarget emotive) = do
    targetout <- check ctx etarget ABSURD
    motiveout <- check ctx emotive UNIV
    return $ Eannotate motiveout (Eindabsurd targetout motiveout)
```

We implement absurd by type checking, and then annotating the fact that the 
result of induction has the same type as the motive.

##### `ap`


```hs
-- | my initial (correct) implementation
synth ctx Eatom = return (Eannotate Euniv Eatom)
synth ctx (Eap ef ex) = do
    fout@(Eannotate tf _) <- synth ctx ef
    vf <- val ctx fout
    (tin, toutclosure) <- case vf of
        PI tin tout -> return (tin, tout)
        notPi -> Left $ "expected function type to be PI type at" <>
                  "|" <> show fout <> "|, found type" <> 
                  "|" <> show notPi <> "|"
    xout <- check ctx ex tin
    tout <- valOfClosure toutclosure xv >>= readbackVal ctx UNIV
    return $ Eannotate tout (Eap fout xout)
```

We see very clearly how evaluation is interleaved with type-checking. The rule
for `ap` seems to be the BEST rule to show this interleaving. See that
we first check the type of `f` to know that it has a type
`(PI (_: tin), toutclosure[_])` type. We check that `xe` has type `tin`.
Then we *evaluate* `xe` into `xv`, to lean the output type `tout`.


What I find entirely baffling is why this is not undecidable! It seems
to me like we are able to "check" anything during type checking...

##### `cons`

```hs
-- | check pattern matches on the value
check :: [(Name, Type)] -> Exp -> Type -> Either String Exp
check ctx  (Econs ea ed) t = do
    (ta, tdclosure) <- case t of
      SIGMA ta tdclosure -> return (ta, tdclosure)
      notSigma -> Left $ "expected cons to have Σ type. " <>
                   "Found |" <> show (Econs ea ed) <> "|" <>
                   "to have type |" <> show notSigma <> "|"
    aout <- check ctx ea ta
    eav <- val ctx ea
    td <- valOfClosure  tdclosure eav
    dout <- check ctx ed td
    return $ Eannotate undefined (Econs aout dout)
```

This was the first checking rule I wrote. In the code above,
I wasn't sure if I had to annotate a `cons` so I left the `Eannotate`
with an `undefined.

# Running

```
$ ghci Main.hs
ghci> :main examples/bool.rkt 
file contents:
(let Bool U
   (Sum [true 1] [false 1]))
```

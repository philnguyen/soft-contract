Motivation
=========================================

Some of the motivations seem unrelated because the new approach
happen to solve them.
I'll need to figure out how to distill these into well-defined purpose.

The previous approach of using a heap to track invariants didn't scale:

* We repeatedly unroll opaque values when verifying recursive functions,
  causing non-termination.
* To mitigate non-termination, we detect recursion and summarize the stack,
  widening values in an ad-hoc way expected to work for common programs.
* If we time out, we prove nothing about the program, leaving *all* contracts
  for runtime checks.
* If we add side effects, we'll have to include a different store. [TODO elaborate]
* Side effects prevent us from remembering contract checking result.
* We couldn't effectively prove strong inductive contacts
  (e.g. `length xs = length (map f xs))`)

The new modification to our tool aims to

* Handle effects precisely, recognizing effectful predicates on-the-fly
  and only remember effect-free ones.
* Make it easier to prove strong inductive contracts.
* Allow guaranteeing termination with more "localized" imprecision.
* Make it convenient to optimize programs after verification.


Overview
=========================================

Given a standard semantics

    e, ρ, σ  ⇓  V, σ

We augment it with:

* Path invariant `Γ` accumulating expressions known to have evaluated
  to truth (non-`#f`) without side effects.
  This set remembers the invariants for free variables in the current context,
  e.g. `{(cons? x), (not (int? (car x)))}`

        Γ ::= {e ...}

* Pure expression `e′` that is equivalent to `e`, if `Γ` is true.
  Such expression may not exist, so `e′` is a "`Maybe e`".
  This steals the concept of `object` in TR.

        e′ ::= e | ∅

The modified execution is now

    e, Γ, ρ, σ  ⇓  ⟨V, e′⟩, Γ, σ

For example:

    (if (int? n) (+ 1 n) (set! n 42))
    {}
    {n ↦ α}
    {α ↦ •}
        ⇓
    ⟨•, (+ 1 n)⟩
    {(int? n)}
    {α ↦ •}

Also:

    (if (int? n) (+ 1 n) (set! n 42))
    {}
    {n ↦ α}
    {α ↦ •}
        ⇓
    ⟨void, ∅⟩
    {(not (int? n))}
    {α ↦ 42}

The implementation uses small-step semantics with widened store (`σ`) and stack-store (`σₖ`).
The configuration includes the expression, path invariant (`Γ`), and stack address (`τ`).

    widened state ξ ::= ⟨{C …}, σ, σₖ⟩
    configuration C ::= ⟨E, Γ, τ⟩
                  E ::= ⟨e, ρ⟩ | ⟨V, e′⟩
    value store   σ ::= {α ↦ {V…}, …}
    stack store   σ ::= {τ ↦ {κ…}, …}
    stack         κ ::= ⟨φ, τ⟩
    stack frame   φ ::= …
    stack address τ ::= ⟨e, ρ, Γ⟩


## Path invariants

Each conditional's scrutiny `e` evaluates to some value `V` and a simplified expression `e′`.
For each branch taken, the path invariant is refined with either `e′` or `not e′`.

    σ, Γ, ρ ⊢ e ⇓ ⟨V, e′⟩, Γ₁, σ₁
    Γ₂ = Γ₁ ∪ {e′},  Γ₂ is sat
    σ₁, Γ₂, ρ ⊢ e₁ ⇓ ⟨Vₐ, e′ₐ⟩, Γ₃, σ₂
    -----------------------------------------[If-True]
    σ, Γ, ρ ⊢ if e e₁ e₂ ⇓ ⟨Vₐ, e′ₐ⟩, Γ₃, σ₂

Compared to previous, we delayed the splitting until conditional instead of at `δ`,
compressing the state space a little.

The path invariant also helps eliminating spurious bindings
and function returns.
For example, `x = null` is unsat if the path invariant is `{(cons? x)}`.

    V ∈ σ(ρ(x))
    Γ ∧ (x = V) is sat
    -----------------------------------------[Var]
    σ, Γ, ρ ⊢ x ⇓ ⟨V, x⟩, Γ, σ

## Side effects

Expressions with side effects such as `set!` do not give a useful simplified expression.

    σ, Γ, ρ ⊢ e ⇓ ⟨V, e′⟩, Γ′, σ′
    ----------------------------------------------------[Set!]
    σ, Γ, ρ ⊢ set! x e ⇓ ⟨void, ∅⟩, Γ′, σ′ ⊔ [ρ(x) ↦ V]

Reading from a mutable box or assignable value does not count as a pure expression, either.

    x is assignable; V ∈ σ(ρ(x))
    -----------------------------------------[Mut-Var]
    σ, Γ, ρ ⊢ x ⇓ ⟨V, ∅⟩, Γ, σ

When a function application `(f x)` appears in an `if`'s scrutiny,
if the execution of `f`'s body has side effects, `(f x)` is automatically dropped.

    (define (f x) ...#|side effect|#...)

    σ, Γ, ρ ⊢ (f x) ⇓ ⟨V, ∅⟩, Γ₁, σ₁
    Γ₂ = Γ₁ ∪ {∅} = Γ₁
    ...
    -----------------------------------------
    σ, Γ, ρ ⊢ if (f x) e₁ e₂ ⇓ ...

Opaque functions are assumed pure by default, unless annotated as effectful.

#####TODO:

It seems that if the purpose is just remembering the *result* of function
application, then it's the *reading from mutable states* that's impure,
not the writing.
For example:

     (define (weird-int? x)
        (if (int? x)
            (set! x 42); returns `void`, so `true`
            #f))

     (if (weird-int? x) (weird-int? x) 'ignore)

Although `weird-int?` has side effects, it's always equivalent to `int?`
up to truth values and does not depend on any state.
It's valid to remember `(weird-int? x)`'s result,
and in the second application of `(weird-int? x)`, throw away the returned `#f`.
(In this small example, we happen to be able to handle `int?`,
so remembering `weird-int?` is not neccessary.
But if we replace `int?` with something complicated
or opaque, it can help).


## Termination

We keep `Γ` finite.
It contains only a subset of the sub-expressions of the `λ`-body under execution
(and their negations).
This means we do not carry over invariants across function calls
because that potentially accumulates bigger path invariants.
For example,

    (define (list? x)
      (cond [(null? x) #t]
            [(cons? x) (list? (cdr x))]
            [else #f]))

    (list? •)

Carrying path invariants across recursive function calls would
result in different states where `x` is a list of length `0`, `1`, `2`, etc.
Instead, we just remember the result and their simplified expression.
The body of `list? x` steps to 4 results like below:
(2 base cases `(1,4)` and 2 recursive cases `(2,3)`).

    (cond [(null? x) #t]
          [(cons? x) (list? (cdr x))]
          [else #f])

    ↦* (1)  ⟨#t, #t⟩, {(null? x)}
        (2)  ⟨#t, (list? (cdr x))⟩, {(cons? x)}
        (3)  ⟨#f, (list? (cdr x))⟩, {(cons? x)}
        (4)  ⟨#f, #f⟩, {(not (null? x)), (not (cons? x))}

Then we rely on the proof relation to see what it means for `(list (cdr x))`
to evaluate to `#t` and `#f`.
To do this, we add a global table `M` remembering the simplification of each expression
under specific path invariants:

    M ::= {e ↦ {⟨e′, Γ⟩…},…}

Now we would remember that:

    |body of (list? x)|
    ↦* (i)   #t, {(null? x)}
        (ii)  (list? (cdr x)), {(cons? x)}
        (iii) #f, {(not (null? x)), (not (cons? x))}

An entry `e ↦ {⟨e′, Γ⟩…}` in table `M` means: *"If we've obtained a result of `e`,
that result must have been obtained by one of `{⟨e′,Γ⟩…}`.
Some of them might be spurious, but there's nothing else."*

Now suppose there's another function using `(list? x)`:

    (define (reverse x a)
      (cond [(null? x) a]
            [else (reverse (cdr x) (cons (car x) a))]))

    (if (list? x) (reverse x '()) 'ignore)
    
In the `else` clause of `reverse`, it is up to (our layer of the proof relation)
to see that `{(list? x), (not (null? x))} ⊢ (cons? x) : ✓`
and eliminate the spurious error.

This is also the mechanism I use to allow proving strong inductive properties.

By doing things this way, we shift the (potentially) infinite unrolling
to the prover instead of the execution.
If we set a time bound on each query, we can guarantee termination
with more localized imprecision than simply timing out the execution as before.

## Optimization

I still haven't been sure if table `M` is enough to read off at the end
as the unreachable-code-eliminated program,
or we actually need another pass to construct something reasonable.

Detailed rules
=========================================

Motivation
=========================================

The previous approach of using a heap to track invariants didn't scale:

* We repeated unroll opaque values when verifying recursive functions,
  causing non-termination.
* To mitigate non-termination, we detect recursion and summarized the stack,
  widening values in an ad-hoc way that hopefully works for most cases.
* If we time out, we prove nothing about the program, leaving *all* contracts
  for runtime checks.
* If we add side effects, we'll have to include a different store. [TODO elaborate]
* Side effects prevent us from remembering contract checking result.
* We couldn't effectively prove strong inductive contacts
  (e.g. `length xs = length (map f xs))`)

The new modification to our tool aims to

* Handle effectful functions/contracts precisely.
* Make it easier to prove strong inductive contracts.
* Allow guaranteeing termination with localized imprecision.
* Make it convenient to optimize programs after verification.


Rules
=========================================

# Overview

Given a standard semantics

    e, ρ, σ  ⇓  V, σ

We augment it with:

* Path invariant `Γ` accumulating expressions known to have evaluated
  to truth (non-`#f`) without side effects.
  This set remembers the invariants for free variables in the current context.

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

The implementation uses small-step semantics with widened store and stack-store (`σₖ`).
The configuration includes the expression, invariant (`Γ`), and stack address (`τ`).

    widened state ξ ::= ⟨{C …}, σ, σₖ⟩
    configuration C ::= ⟨E, Γ, τ⟩
                  E ::= ⟨e, ρ⟩ | ⟨V, e′⟩
    value store   σ ::= {α ↦ {V…}, …}
    stack store   σ ::= {τ ↦ {κ…}, …}
    stack         κ ::= ⟨φ, τ⟩
    stack frame   φ ::= …
    stack address τ ::= ⟨e, ρ, Γ⟩

We keep `Γ` finite.
It contains only a subset of the sub-expressions of the `λ`-body under execution
(and their negations).
This means we do not carry over invariants across function calls.
For example,

    [TODO example]

To fix this, we include another global table `M`
remembering what expression evaluating to what value and simplifying to what expression
under what path invariant:

    M ::= {e ↦ {⟨V, e′, Γ⟩…}, …}

# Details

import data.set definitions metafunctions

constant alloc (x: x) (σ: σ): a

-- The setup of this formalism is that the "concrete semantics" is just a sub-relation
-- of the full semantics with symbolic values, and there's one `alloc` function.
-- The assumption of `alloc_fresh` is only needed for the concrete side
-- to ensure consistency of abstraction mapping.
-- We could have used 2 distinct semantics, where the symbolic side had an arbitrary
-- `alloc'` function with no further assumption.
axiom alloc_fresh (x: x) (σ: σ): map_excl σ (alloc x σ)

-- Assume variables are partitioned by predicate `uk_x`, which tells that they come
-- from purely instantiated code.
constant uk_x: x → Prop
noncomputable def kn_x x := ¬ uk_x x
attribute [reducible] kn_x

-- In retrospect, we probably don't need `uk_a`
constant uk_a: a → Prop
noncomputable def kn_a a := ¬ uk_a a
attribute [reducible] kn_a
axiom alloc_preserves_uk {x: x} (σ: σ): uk_x x → uk_a (alloc x σ)
axiom alloc_preserves_kn {x: x} (σ: σ): kn_x x → kn_a (alloc x σ)

-- Fully concrete expressions that can appear in instantiated code
-- All variables (bound and free) must be `uk`, and blame label `ℓᵤₖ`
-- distinct from those in transparent code.
inductive uk_e: e → Prop
| n  : ∀ {n}, uk_e (e.n n)
| lam: ∀ {x e}, uk_x x → uk_e e → uk_e (e.lam x e)
| x  : ∀ {x}, uk_x x → uk_e (e.x x)
| app: ∀ {e₁ e₂}, uk_e e₁ → uk_e e₂ → uk_e (e.app ℓ.uk e₁ e₂)
| set: ∀ {x e}, uk_x x → uk_e e → uk_e (e.set x e)

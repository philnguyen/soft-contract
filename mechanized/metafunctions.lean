import data.set definitions

def set_del {τ: Type} (x: τ) (xs: set τ) := set.diff xs (set.insert x ∅)
attribute [reducible] set_del

-- Collect free variables in expression
noncomputable def fv: e → set x
| (e.n _)        := ∅
| e.s            := ∅
| (e.lam x e)    := set_del x (fv e)
| (e.x x)        := set.insert x ∅
| (e.app _ e₁ e₂):= fv e₁ ∪ fv e₂
| (e.set x e)    := set.insert x (fv e)
attribute [simp] fv

noncomputable def ρ_ext := @ext_map x a
noncomputable def σ_ext := @ext_map a V
noncomputable def F_ext := @ext_map a a
attribute [reducible] ρ_ext
attribute [reducible] σ_ext
attribute [reducible] F_ext

noncomputable def ρ_to := @map_to₁ x a -- deterministic
noncomputable def σ_to := @map_to  a V -- non-deterministic in general
noncomputable def F_to := @map_to₁ a a -- deterministic
attribute [reducible] ρ_to
attribute [reducible] σ_to
attribute [reducible] F_to

-- A version of environment restriction that
-- (1) uses the empty environment for an empty domain,
-- (2) otherwise just leaves it as-is.
--
-- (1) is important in making explicit that instantiated code doesn't have implicit access
-- to transparent parts of the program
-- (2) is just to avoid unimportant defailts
constant shrink_ρ: set x → ρ → ρ
axiom shrink_empty (ρ: ρ): shrink_ρ ∅ ρ = []
axiom shrink_nonempty (ρ: ρ) (dom: set x) (non_empty: dom ≠ ∅): shrink_ρ dom ρ = ρ
attribute [simp] shrink_nonempty
attribute [simp] shrink_empty

import data.set definitions metafunctions reduction assumptions

-- Instantiation of expression
inductive inst_e: e → e → Prop
-- Structural cases
| n  : ∀ {n}, inst_e (e.n n) (e.n n)
| lam: ∀ {x e e'},
         kn_x x →
         inst_e e e' →
         inst_e (e.lam x e) (e.lam x e')
| x  : ∀ {x}, kn_x x → inst_e (e.x x) (e.x x)
| app: ∀ {e₁ e₂ e₁' e₂'},
         inst_e e₁ e₁' →
         inst_e e₂ e₂' →
         inst_e (e.app ℓ.kn e₁ e₂) (e.app ℓ.kn e₁' e₂')
| set: ∀ {x e e'},
         kn_x x →
         inst_e e e' →
         inst_e (e.set x e) (e.set x e')
-- Each symbol stands for the base value or a syntactically closed lambdas
| n_s: ∀ {n}, inst_e (e.n n) e.s
| l_s: ∀ {x e},
         uk_x x →
         uk_e e →
         fv (e.lam x e) = ∅ →
         inst_e (e.lam x e) e.s
infix `⊑ₑ`: 40 := inst_e

-- Instantiation of environment
inductive inst_ρ: F → ρ → ρ → Prop
| mt : ∀ {F}, inst_ρ F [] []
| ext: ∀ {F x a a' ρ ρ'},
         kn_x x →
         kn_a a →
         kn_a a' →
         F_to F a a' →
         inst_ρ F ρ ρ' →
         inst_ρ F (ρ_ext ρ x a) (ρ_ext ρ' x a')

inductive opq_ρ: F → ρ → Prop
| mt : ∀ {F}, opq_ρ F []
| ext: ∀ {F a x ρ},
         uk_x x →
         uk_a a →
         F_to F a aₗ →
         opq_ρ F ρ →
         opq_ρ F (ρ_ext ρ x a)

-- Instantiation between run-time values
inductive inst_V: F → V → V → Prop
| n  : ∀ {F n}, inst_V F (V.n n) (V.n n)
| clo: ∀ {F x e e' ρ ρ'},
         kn_x x →
         inst_e e e' →
         inst_ρ F ρ ρ' →
         inst_V F (V.c x e ρ) (V.c x e' ρ')
-- non-structural cases
| n_s: ∀ {F n}, inst_V F (V.n n) V.s
| l_s: ∀ {F x e ρ},
         uk_x x →
         uk_e e →
         opq_ρ F ρ →
         inst_V F (V.c x e ρ) V.s

inductive rstr_V: F → σ → V → Prop
| of : ∀ {F σ' V V'}, σ_to σ' aₗ V' → inst_V F V V' → rstr_V F σ' V

inductive inst_A: F → A → A → Prop
| V  : ∀ {F V V'},
         inst_V F V V' →
         inst_A F (A.V V) (A.V V')
| blm: ∀ {F}, inst_A F (A.blm ℓ.kn) (A.blm ℓ.kn)

inductive inst_E: F → E → E → Prop
-- structural cases
| ev : ∀ {F e e' ρ ρ'},
         inst_e e e' →
         inst_ρ F ρ ρ' →
         inst_E F (E.ev e ρ) (E.ev e' ρ')
| rt : ∀ {F A A'},
         inst_A F A A' →
         inst_E F (E.rt A) (E.rt A')
-- non-structural cases
-- `hv Cs` form approximates entire classes of "unknown code" with access to leak set `Cs`
| hv : ∀ {F e ρ},
         uk_e e →
         opq_ρ F ρ →
         inst_E F (E.ev e ρ) E.hv

-- Instantiation between stack frames
inductive inst_φ: F → φ → φ → Prop
| fn: ∀ {F V V'},
        inst_V F V V' →
        inst_φ F (φ.fn ℓ.kn V) (φ.fn ℓ.kn V')
| ar: ∀ {F e e' ρ ρ'},
        inst_e e e' →
        inst_ρ F ρ ρ' →
        inst_φ F (φ.ar ℓ.kn e ρ) (φ.ar ℓ.kn e' ρ')
| st: ∀ {F a a'},
        kn_a a →
        kn_a a' →
        F_to F a a' →
        inst_φ F (φ.st a) (φ.st a')

-- Purely opaque stack frame
inductive rstr_φ: F → σ → φ → Prop
| fn: ∀ {F σ' V}, rstr_V F σ' V → rstr_φ F σ' (φ.fn ℓ.uk V)
| ar: ∀ {F σ' e ρ}, uk_e e → opq_ρ F ρ → rstr_φ F σ' (φ.ar ℓ.uk e ρ)
| st: ∀ {F σ' a}, uk_a a → F_to F a aₗ → rstr_φ F σ' (φ.st a)

-- Instantiation of stack
-- In case it's more intuitive in evaluation-hole notation:
--
-- -----------------------------------------[mt]  
--   [] ⊑ [] 
--
--   V ⊑ V'            ℰ ⊑ ℰ'
-- -----------------------------------------[ext_fn]
--   ℰ[V []] ⊑ ℰ'[V' []]
--
--   ℰ ⊑ ℰ'
-- -----------------------------------------[ns0]
--   ℰ ⊑ ℰ'[●/Cs []]
--
--   rstr⟦⟨e,ρ⟩, Cs⟧        ℰ ⊑ ℰ'[●/Cs []]
-- -----------------------------------------[nsn_ar]
--   ℰ[[] ⟨e,ρ⟩]  ⊑  ℰ[●_Cs []]
--
--   rstr⟦V, Cs⟧           ℰ ⊑ ℰ'[●/Cs []]
-- -----------------------------------------[nsn_fn]
--   ℰ[V []] ⊑ ℰ[●/Cs []]
inductive inst_κ: F → σ → κ → κ → Prop
-- structural cases
| mt : ∀ {F σ'}, inst_κ F σ' [] []
| ext: ∀ {F σ' φ φ' κ κ'},
         inst_φ F φ φ' →
         inst_κ F σ' κ κ' →
         inst_κ F σ' (φ :: κ) (φ' :: κ')
-- non-structural cases: opaque application approximates 0+ unknown frames
-- as long as the frames are restricted up to `Cs` behavior from the known
| ns0: ∀ {F σ' κ κ'},
         inst_κ F σ' κ κ' →
         inst_κ F σ' κ (φ.fn ℓ.uk V.s :: κ')
| nsn: ∀ {F σ' φ κ κ'},
         rstr_φ F σ' φ →
         inst_κ F σ'       κ  (φ.fn ℓ.uk V.s :: κ') →
         inst_κ F σ' (φ :: κ) (φ.fn ℓ.uk V.s :: κ')

inductive inst_σ: F → σ → σ → Prop -- TODO am I sure about this defn?
/-| of : ∀ {F σ σ'},
         (∀ {a a' V}, F_to F a a' → σ_to σ a V → (∃ V', σ_to σ' a' V' ∧ inst_V F V V')) →
         inst_σ F σ σ'-/
| mt : ∀ {σ'}, inst_σ [] [] σ'
| ext: ∀ {F σ σ' a a' V V'},
         map_excl F a →
         map_excl σ a →
         inst_V F V V' →
         inst_σ F σ σ' →
         inst_σ (F_ext F a a') (σ_ext σ a V) (σ_ext σ' a' V')
| wid: ∀ {F σ σ' a' V'},
         inst_σ F σ σ' →
         inst_σ F σ (σ_ext σ' a' V')
| mut: ∀ {F σ σ' a a' V V'},
         F_to F a a' →
         inst_V F V V' →
         inst_σ F σ σ' →
         inst_σ F (σ_ext σ a V) (σ_ext σ' a' V')

-- Instantiation of state
inductive inst_s: F → s → s → Prop
| of: ∀ {F E E' κ κ' σ σ'},
        inst_E F E E' →
        inst_κ F σ' κ κ' →
        inst_σ F σ σ' →
        inst_s F ⟨E, κ, σ⟩ ⟨E', κ', σ'⟩

noncomputable def inst (s s': s): Prop := ∃ F, inst_s F s s'
attribute [reducible] inst
infix `⊑`: 40 := inst

import definitions metafunctions assumptions

-- Reduction
inductive r: s → s → Prop
-- simple
| n  : ∀ {ρ κ σ n},
         r ⟨E.ev (e.n n) ρ    , κ, σ⟩
           ⟨E.rt (A.V (V.n n)), κ, σ⟩
| s  : ∀ {ρ κ σ},
         r ⟨E.ev e.s ρ                  , κ, σ⟩
           ⟨E.rt (A.V V.s), κ, σ⟩ -- not allocated in store yet
| lam: ∀ {x e ρ κ σ},
         r ⟨E.ev (e.lam x e)                              ρ   , κ, σ⟩
           ⟨E.rt (A.V (V.c x e (shrink_ρ (fv (e.lam x e)) ρ))), κ, σ⟩
| x  : ∀ {x a V κ ρ σ},
         ρ_to ρ x a →
         σ_to σ a V →
         r ⟨E.ev (e.x x) ρ, κ, σ⟩
           ⟨E.rt (A.V V)  , κ, σ⟩
-- apply
| app: ∀ {ℓ e₁ e₂ ρ κ σ},
         r ⟨E.ev (e.app ℓ e₁ e₂) ρ, κ               , σ⟩
           ⟨E.ev          e₁     ρ, φ.ar ℓ e₂ ρ :: κ, σ⟩
| app_swp:
       ∀ {V ℓ e ρ κ σ},
         r ⟨E.rt (A.V V), φ.ar ℓ e ρ :: κ, σ⟩
           ⟨E.ev e ρ    , φ.fn ℓ V   :: κ, σ⟩
| app_bse:
       ∀ {V κ σ n},
         r ⟨E.rt (A.V V)     , φ.fn ℓ.kn (V.n n) :: κ, σ⟩
           ⟨E.rt (A.blm ℓ.kn),                     [], σ⟩
| app_clo:
       ∀ {V ℓ x e ρ κ σ},
         -- FIXME inlining `alloc` for now just b/c i don't know how to hint rw in the proof
         r ⟨E.rt (A.V V)                  , φ.fn ℓ (V.c x e ρ) :: κ, σ                    ⟩
           ⟨E.ev e (ρ_ext ρ x (alloc x σ)),                       κ, σ_ext σ (alloc x σ) V⟩
| app_sym_blm:
       ∀ {V κ σ},
         r ⟨E.rt (A.V V)    , φ.fn ℓ.kn V.s :: κ, σ⟩
           ⟨E.rt (A.blm ℓ.kn),                [], σ⟩
| app_sym_hv:
       ∀ {ℓ V κ σ},
         r ⟨E.rt (A.V V), φ.fn ℓ    V.s :: κ,              σ             ⟩
           ⟨E.hv        , φ.fn ℓ.uk V.s :: κ, σ_ext (σ_ext σ aₗ V.s) aₗ V⟩
| app_sym_ok:
       ∀ {ℓ V κ σ},
         r ⟨E.rt (A.V V), φ.fn ℓ V.s :: κ, σ⟩
           -- this is surprising without looking at other rules
           ⟨E.rt (A.V V),               κ, σ⟩
-- havoc
| hv_rt:
       ∀ {a V κ σ},
         σ_to σ a V →
         r ⟨E.hv        , κ, σ⟩
           ⟨E.rt (A.V V), κ, σ⟩
| hv_co:
       ∀ {Vₓ V κ σ},
         σ_to σ aₗ Vₓ → -- Inefficient split here, just to make proof "in-sync"
         σ_to σ aₗ V →
         r ⟨E.hv,                         κ, σ⟩
           ⟨E.rt (A.V Vₓ), φ.fn ℓ.uk V :: κ, σ⟩ -- TODO- set!
| st0: ∀ {x a e ρ κ σ},
       ρ_to ρ x a →
       r ⟨E.ev (e.set x e) ρ,           κ, σ⟩
         ⟨E.ev          e  ρ, φ.st a :: κ, σ⟩
| st1: ∀ {V a κ σ},
       r ⟨E.rt (A.V V      ), φ.st a :: κ, σ          ⟩
         ⟨E.rt (A.V (V.n 1)),           κ, σ_ext σ a V⟩
infix `~>`: 40 := r

-- Reflexive transitive closure of 1-step reduction
inductive rr: s → s → Prop
| rfl: ∀ {s}, rr s s
| trn: ∀ {s₁ s₂ s₃}, r s₁ s₂ → rr s₂ s₃ → rr s₁ s₃

infix `~>*`: 40 := rr -- FIXME: what's the appropriate precedence?

-- 1-step trivially implies *-steps
def rr₁ {s₁ s₂} (r₁: s₁ ~> s₂): s₁ ~>* s₂ := rr.trn r₁ rr.rfl
infixr `⊗`: 40 := rr.trn

lemma rr_tran {s₁ s₂ s₃} (rr₁: s₁ ~>* s₂) (rr₂: s₂ ~>* s₃): s₁ ~>* s₃ :=
begin induction rr₁ with s₀ s₄ s₅ s₆,
  {assumption},
  {exact rr.trn (by assumption) (ih_1 rr₂)}
end

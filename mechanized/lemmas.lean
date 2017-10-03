import helper_lemmas assumptions

lemma ev_reduction_preserves_approximation
  {e e': e}
  {ρ ρ': ρ}
  {κ κ': κ}
  {σ σ': σ}
  {s: s}
  {F: F}
  (sim_e: e ⊑ₑ e')
  (sim_ρ: inst_ρ F ρ ρ')
  (sim_κ: inst_κ F σ' κ κ')
  (sim_σ: inst_σ F σ σ')
  (concrete_reduction: ⟨E.ev e ρ, κ, σ⟩ ~> s):
  ∃ s', ⟨E.ev e' ρ', κ', σ'⟩ ~>* s' ∧ s ⊑ s' :=
begin cases sim_e,

  -- n ⊑ n
  {cases concrete_reduction,
   exact in_1_step r.n _ (inst_E.rt (inst_A.V inst_V.n)) sim_κ sim_σ},

  -- λx.e ⊑ λx.e', where fv⟦λx.e⟧ = fv⟦λx.e'⟧ = ∅
  {cases concrete_reduction,
   have sim_ρ':_, from closing_preserves_inst sim_e sim_ρ,
   have sim_V :_, from inst_V.clo ‹kn_x x› ‹e ⊑ₑ e'› sim_ρ',
   in_1_step r.lam F (inst_E.rt (inst_A.V sim_V)) sim_κ sim_σ},

  -- x ⊑ x
  {cases concrete_reduction,
   exact exists.elim (lookup_ρ (by assumption) (by assumption) sim_ρ sim_σ)
     (take a',
      assume exists_V',
      exists.elim exists_V'
        (take V',
           (assume ⟨ρ'_x, σ'_a', sim_V⟩,
              in_1_step (r.x ρ'_x σ'_a') _ (inst_E.rt (inst_A.V sim_V)) sim_κ sim_σ)))},

  -- e₁ e₂ ⊑ e₁' e₂'
  {cases concrete_reduction,
   have sim_E':_, from inst_E.ev ‹e₁ ⊑ₑ e₁'› sim_ρ,
   have sim_φ :_, from inst_φ.ar ‹e₂ ⊑ₑ e₂'› sim_ρ,
   in_1_step r.app _ sim_E' (inst_κ.ext sim_φ sim_κ) sim_σ},

  -- set! x e ⊑ set! x e'
  {cases concrete_reduction,
   have exists_a':_, from inst_a_from_lookup_ρ (by assumption) sim_ρ,
   have sim_E':_, from inst_E.ev ‹e ⊑ₑ e'› sim_ρ,
   exists.elim exists_a'
     (take a',
      assume ⟨ρ'_x, F_a⟩,
        have kna : _, from inst_ρ_implies_kn_l (by assumption) (by assumption),
        have kna': kn_a a', from inst_ρ_implies_kn_r (by assumption) (by assumption),
        have sim_κ':_, from inst_κ.ext (inst_φ.st kna kna' F_a) sim_κ,
        in_1_step (r.st0 ρ'_x) _ sim_E' sim_κ' sim_σ)},

  -- n ⊑ ●
  {cases concrete_reduction,
   exact in_1_step r.s _ (inst_E.rt (inst_A.V inst_V.n_s)) sim_κ sim_σ},

  -- λx.e ⊑ ●
  {cases concrete_reduction,
   have closed_ρ_empty: shrink_ρ (fv (e.lam x e)) ρ = [], by simp [‹fv (e.lam x e) = ∅›],
   begin rw [closed_ρ_empty],
     have sim_V: inst_V F _ V.s, from inst_V.l_s ‹uk_x x› ‹uk_e e› opq_ρ.mt,
     in_1_step r.s _ (inst_E.rt (inst_A.V sim_V)) sim_κ sim_σ
   end}
end
  
lemma rt_reduction_preserves_approximation
  {κ κ': κ}
  (σ': σ)
  {σ : σ}
  {s: s}
  {F: F}
  (sim_κ: inst_κ F σ' κ κ'):
  ∀ (A': A)
    {A : A}
    (sim_A: inst_A F A A')
    (sim_σ: inst_σ F σ σ')
    (concrete_reduction: ⟨E.rt A, κ, σ⟩ ~> s),
    ∃ s', ⟨E.rt A', κ', σ'⟩ ~>* s' ∧ s ⊑ s' :=
begin induction sim_κ,

  -- [Contradictory] empty stack
  {intros, cases concrete_reduction},

  -- top frame comes from transparent code
  {intros, cases concrete_reduction,
  
     -- ar⟨e,ρ⟩
     {cases sim_A, cases ‹inst_φ F (φ.ar ℓ e ρ) φ'›,
      have sim_E':_, from inst_E.ev ‹e ⊑ₑ e'› (by assumption),
      have sim_κ':_, from inst_κ.ext (inst_φ.fn (by assumption)) (by assumption),
      in_1_step r.app_swp _ sim_E' sim_κ' sim_σ},

     -- fn⟨n⟩
     {cases sim_A, cases ‹inst_φ F (φ.fn ℓ.kn (V.n n)) φ'›, cases ‹inst_V F (V.n n) V'›, 
        -- fn⟨n⟩ ⊑ fn⟨n⟩
        {exact in_1_step r.app_bse _ (inst_E.rt inst_A.blm) inst_κ.mt sim_σ},
        -- fn⟨n⟩ ⊑ fn⟨●⟩
        {exact in_1_step r.app_sym_blm _ (inst_E.rt inst_A.blm) inst_κ.mt sim_σ}},

     -- fn⟨Clo⟨x,e,ρ⟩⟩
     {cases sim_A, cases ‹inst_φ F (φ.fn ℓ (V.c x e ρ)) φ'›, cases ‹inst_V F (V.c x e ρ) V'›,
        -- fn⟨Clo⟨x,e,ρ⟩⟩ ⊑ fn⟨Clo⟨x,e',ρ'⟩⟩
        {pose a  := alloc x σ,
         pose a' := alloc x σ',
         pose F' := F_ext F a a',
         have σ_na: _, from alloc_fresh x σ,
         have F_na: map_excl F a, from σ_excl_implies_F_excl sim_σ σ_na,
         have kna : _, from alloc_preserves_kn σ ‹kn_x x›,
         have kna': _, from alloc_preserves_kn σ' ‹kn_x x›,
         have sim_ρ': inst_ρ F' _ _,
           from inst_ρ.ext ‹kn_x x› kna kna' map_to₁.fnd
                (ext_F_preserves_inst_ρ F_na (by assumption)),
         in_1_step r.app_clo _
           (inst_E.ev ‹e ⊑ₑ e'› sim_ρ')
           (ext_preserves_inst_κ F_na (by assumption))
           (inst_σ.ext F_na σ_na (by assumption) sim_σ)},

        -- fn⟨Clo⟨x,e,ρ⟩⟩ ⊑ fn⟨●⟩
        {pose a := alloc x σ,
         pose F' := F_ext F a aₗ,
         have σ_na: map_excl σ a, from alloc_fresh _ _,
         have F_na: map_excl F a, from σ_excl_implies_F_excl sim_σ σ_na,
         have uka: _, from alloc_preserves_uk σ ‹uk_x x›,
         in_1_step r.app_sym_hv F'
           (inst_E.hv ‹uk_e e› (opq_ρ.ext ‹uk_x x› uka map_to₁.fnd
                                     (ext_F_preserves_opq_ρ F_na (by assumption))))
           (ext_preserves_inst_κ F_na (inst_κ.ns0 (ext_σ_preserves_inst_κ (by assumption))))
           (inst_σ.ext F_na σ_na (by assumption) (inst_σ.wid sim_σ))}},


     -- [Contradictory] fn⟨●⟩
     {exact absurd (by assumption) inst_φ_no_sym},
     {exact absurd (by assumption) inst_φ_no_sym},
     {exact absurd (by assumption) inst_φ_no_sym},

     -- set!⟨a⟩
     {cases sim_A, cases ‹inst_φ _ _ _›,
      exact in_1_step r.st1 F
        (inst_E.rt (inst_A.V inst_V.n))
        (ext_σ_preserves_inst_κ (by assumption))
        (inst_σ.mut (by assumption) (by assumption) sim_σ)}
    },

  -- (● []) approximates 0 frame
  -- This case doesn't do case analysis on top frame, just relies on induction hypothesis
  {intros,
   cases sim_A,

     {pose σ₁' := σ_ext σ' aₗ V',
      have sim_σ': inst_σ F σ σ₁', from inst_σ.wid sim_σ,
      exists.elim (ih_1 (A.V V') sim_A sim_σ concrete_reduction)
        (take s₁', assume ⟨steps, sim_s⟩,
           ⟨s₁', ⟨rr.trn r.app_sym_ok steps, sim_s⟩⟩)},

     {cases concrete_reduction}},

  -- (● []) approximates 1+ opaque frames
  {intros,
   cases sim_A,
   cases concrete_reduction,

     -- ar⟨e,ρ⟩
     {cases ‹rstr_φ F σ' (φ.ar ℓ e ρ)›,
      exact in_1_step r.app_sym_hv F
        (inst_E.hv ‹uk_e e› (by assumption))
        (inst_κ.nsn (rstr_φ.fn (rstr_V.of map_to.fnd (by assumption)))
                    (ext_σ_preserves_inst_κ (ext_σ_preserves_inst_κ (by assumption))))
        (inst_σ.wid (inst_σ.wid sim_σ))},

     -- [Contradictory] fn⟨n⟩
     {cases ‹rstr_φ F _ (φ.fn ℓ.kn (V.n n))›},

     -- fn⟨Clo⟨x,e,ρ⟩⟩
     {cases ‹rstr_φ F _ (φ.fn ℓ (V.c x e ρ))›,
      cases ‹rstr_V F σ' (V.c x e ρ)›,
      cases ‹inst_V F (V.c x e ρ) V'›,
        -- transparent code
        {pose a := alloc x σ,
         pose a' := alloc x (σ_ext (σ_ext σ' aₗ V.s) aₗ V'),
         have σ_na: map_excl σ a, from alloc_fresh _ _,
         have F_na: map_excl F a, from σ_excl_implies_F_excl sim_σ σ_na,
         have kna : kn_a a , from alloc_preserves_kn _ ‹kn_x x›,
         have kna': kn_a a', from alloc_preserves_kn _ ‹kn_x x›,
         in_steps (r.app_sym_hv
                  ⊗ r.hv_co map_to.fnd (map_to.rst (map_to.rst (by assumption)))
                  ⊗ r.app_clo
                  ⊗ rr.rfl)
           (F_ext F a a')
           (inst_E.ev ‹e ⊑ₑ e'› (inst_ρ.ext ‹kn_x x› kna kna' map_to₁.fnd (ext_F_preserves_inst_ρ F_na (by assumption))))
           (ext_preserves_inst_κ F_na
             (ext_σ_preserves_inst_κ
                (ext_σ_preserves_inst_κ (by assumption))))
           (inst_σ.ext F_na σ_na (by assumption) (inst_σ.wid (inst_σ.wid sim_σ)))},

        -- opaque code
        {pose a := alloc x σ,
         have σ_na: map_excl σ a, from alloc_fresh _ _,
         have F_na: map_excl F a, from σ_excl_implies_F_excl sim_σ σ_na,
         have uka: _, from alloc_preserves_uk σ ‹uk_x x›,
         in_1_step r.app_sym_hv (F_ext F a aₗ)
           (inst_E.hv ‹uk_e e› (opq_ρ.ext ‹uk_x x› uka map_to₁.fnd
                                 (ext_F_preserves_opq_ρ F_na (by assumption))))
           (ext_preserves_inst_κ F_na (ext_σ_preserves_inst_κ (by assumption)))
           (inst_σ.ext F_na σ_na (by assumption) (inst_σ.wid sim_σ))}},

     -- [Contradictory] fn⟨●⟩
     {cases ‹rstr_φ _ _ _›},
     {cases ‹rstr_φ _ _ _›, cases ‹rstr_V F σ' V.s›, cases ‹inst_V F V.s V'›},
     {cases ‹rstr_φ _ _ _›, cases ‹rstr_V F σ' V.s›, cases ‹inst_V F V.s V'›},

     -- set!⟨a⟩
     {cases ‹rstr_φ F σ' (φ.st _)›,
      exact in_steps (r.app_sym_hv ⊗ r.hv_rt (map_to.rst map_to.fnd) ⊗ rr.rfl) F
        (inst_E.rt (inst_A.V inst_V.n_s))
        (ext_σ_preserves_inst_κ (ext_σ_preserves_inst_κ (by assumption)))
        (inst_σ.mut (by assumption) (by assumption) (inst_σ.wid sim_σ))},

     -- [Contradictory] blame
     {cases concrete_reduction}}

end

lemma hv_reduction_preserves_approximation
  {e: e}
  {ρ: ρ}
  {κ κ': κ}
  {σ σ': σ}
  {F: F}
  {s: s}
  (sim_E: inst_E F (E.ev e ρ) E.hv)
  (sim_κ: inst_κ F σ' κ κ')
  (sim_σ: inst_σ F σ σ')
  (symbolic_state_wellformed: s_wellformed ⟨E.hv, κ', σ'⟩)
  (concrete_reduction: ⟨E.ev e ρ, κ, σ⟩ ~> s):
  ∃ s', ⟨E.hv, κ', σ'⟩ ~>* s' ∧ s ⊑ s' :=
begin cases sim_κ,

  -- Structural cases are contradictory
  {cases symbolic_state_wellformed},
  {cases symbolic_state_wellformed, cases ‹inst_φ F φ (φ.fn ℓ.uk V.s)›},

  -- (● []) approximates 0 frame
  {cases symbolic_state_wellformed,
   cases concrete_reduction,
    
     -- n
     {exact in_1_step (r.hv_rt (by assumption)) _ (inst_E.rt (inst_A.V inst_V.n_s)) (by assumption) sim_σ},

     -- [Contradictory] ●
     {cases sim_E, cases ‹uk_e e.s›},
  
     -- λx.e
     {cases sim_E, cases ‹uk_e (e.lam x e)›,
      have opq_ρ': opq_ρ _ (shrink_ρ (fv _) _),
        from closing_preserves_opq (by assumption),
      have sim_E':_, from inst_E.rt (inst_A.V (inst_V.l_s ‹uk_x x› ‹uk_e e› opq_ρ')),
      in_1_step (r.hv_rt (by assumption)) _ sim_E' (by assumption) sim_σ},

     -- x
     {cases sim_E,
      have F_a:_, from lookup_opq_ρ (by assumption) (by assumption),
      exists.elim (inst_V_from_lookup_σ F_a (by assumption) sim_σ)
        (take V', assume ⟨σ'_a', sim_V⟩,
           have sim_E':_, from inst_E.rt (inst_A.V sim_V),
           in_1_step (r.hv_rt σ'_a') _ sim_E' (by assumption) sim_σ)},

     -- (e₁ e₂)
     {cases sim_E, cases ‹uk_e (e.app ℓ e₁ e₂)›,
      have sim_E':_, from inst_E.hv ‹uk_e e₁› (by assumption),
      have sim_κ':_,
        from inst_κ.nsn (rstr_φ.ar ‹uk_e e₂› (by assumption)) (inst_κ.ns0 (by assumption)),
      in_0_step _ sim_E' sim_κ' sim_σ},

     -- set! x e
     {cases sim_E, cases ‹uk_e (e.set x e)›,
      have F_a:_, from lookup_opq_ρ (by assumption) (by assumption),
      have sim_E':_, from inst_E.hv ‹uk_e e› (by assumption),
      have uka: _, from opq_ρ_implies_uk (by assumption) (by assumption),
      have sim_κ':_, from inst_κ.nsn (rstr_φ.st uka F_a) (inst_κ.ns0 (by assumption)),
      in_0_step _ sim_E' sim_κ' sim_σ}},

  -- (● []) approximates 1+ frames
  {cases symbolic_state_wellformed,
   cases concrete_reduction,
   
     -- n
     {have sim_κ': _, from inst_κ.nsn (by assumption) (by assumption),
      in_1_step (r.hv_rt (by assumption)) _ (inst_E.rt (inst_A.V inst_V.n_s)) sim_κ' sim_σ},

     -- [Contradictory] ●
     {cases sim_E, cases ‹uk_e e.s›},

     -- λx.e
     {cases sim_E, cases ‹uk_e (e.lam x e)›,
      have opq_ρ': opq_ρ _ (shrink_ρ (fv _) _),
        from closing_preserves_opq (by assumption),
      have sim_E':_, from inst_E.rt (inst_A.V (inst_V.l_s ‹uk_x x› ‹uk_e e› opq_ρ')),
      in_1_step (r.hv_rt (by assumption)) _ sim_E' (by assumption) sim_σ},
 
     -- x
     {cases sim_E,
      have F_a:_, from lookup_opq_ρ (by assumption) (by assumption),
      exists.elim (inst_V_from_lookup_σ F_a (by assumption) sim_σ)
        (take V', assume ⟨σ'_a', sim_V⟩,
           have sim_E':_, from inst_E.rt (inst_A.V sim_V),
           in_1_step (r.hv_rt σ'_a') _ sim_E' (by assumption) sim_σ)},

     -- (e₁ e₂)
     {cases sim_E, cases ‹uk_e (e.app ℓ e₁ e₂)›,
      have sim_E':_, from inst_E.hv ‹uk_e e₁› (by assumption),
      have sim_κ':_,
        from inst_κ.nsn (rstr_φ.ar ‹uk_e e₂› (by assumption))
             (inst_κ.nsn (by assumption) (by assumption)),
      in_0_step _ sim_E' sim_κ' sim_σ},

     -- set! x e
     {cases sim_E, cases ‹uk_e (e.set x e)›,
      have F_a:_, from lookup_opq_ρ (by assumption) (by assumption),
      have sim_E':_, from inst_E.hv ‹uk_e e› (by assumption),
      have uka: _, from opq_ρ_implies_uk (by assumption) (by assumption),
      have sim_κ':_,
        from inst_κ.nsn (rstr_φ.st uka F_a) (inst_κ.nsn (by assumption) (by assumption)),
      in_0_step _ sim_E' sim_κ' sim_σ}}
end

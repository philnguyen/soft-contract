import finite_map definitions reduction metafunctions instantiation assumptions

-- This module declares and proves lemmas that are not important but help proving soundness

/-----------------------------------------
-- Shorthand for use in proofs
-----------------------------------------/

lemma in_steps {E E₁' E₂': E} {κ κ₁' κ₂': κ} {σ σ₁' σ₂': σ}
  (r: ⟨E₁',κ₁',σ₁'⟩ ~>* ⟨E₂',κ₂',σ₂'⟩)
  (F: F)
  (sim_E: inst_E F E E₂')
  (sim_κ: inst_κ F σ₂' κ κ₂')
  (sim_σ: inst_σ F σ σ₂'):
  ∃ s', ⟨E₁',κ₁',σ₁'⟩ ~>* s' ∧ ⟨E,κ,σ⟩ ⊑ s' :=
⟨_, ⟨r, ⟨F, ⟨sim_E, sim_κ, sim_σ⟩⟩⟩⟩

lemma in_0_step {E E': E} {κ κ': κ} {σ σ': σ}
  (F: F)
  (sim_E: inst_E F E E')
  (sim_κ: inst_κ F σ' κ κ')
  (sim_σ: inst_σ F σ σ'):
  ∃ s', ⟨E',κ',σ'⟩ ~>* s' ∧ ⟨E,κ,σ⟩ ⊑ s' :=
in_steps rr.rfl F sim_E sim_κ sim_σ

lemma in_1_step {E₂ E₁' E₂': E} {κ₂ κ₁' κ₂': κ} {σ₂ σ₁' σ₂': σ}
  (r: ⟨E₁',κ₁',σ₁'⟩ ~> ⟨E₂',κ₂',σ₂'⟩)
  (F: F)
  (sim_E: inst_E F E₂ E₂')
  (sim_κ: inst_κ F σ₂' κ₂ κ₂')
  (sim_σ: inst_σ F σ₂ σ₂'):
  ∃ s₂', ⟨E₁',κ₁',σ₁'⟩ ~>* s₂' ∧ ⟨E₂,κ₂,σ₂⟩ ⊑ s₂' :=
in_steps (rr₁ r) F sim_E sim_κ sim_σ


/-----------------------------------------
-- Helper lemmas
-----------------------------------------/

lemma inst_ρ_implies_kn_l {F: F} {ρ ρ': ρ} {x: x} {a: a}
  (ρ_x: ρ_to ρ x a)
  (sim: inst_ρ F ρ ρ'):
  kn_a a :=
begin induction sim,
  {cases ρ_x},
  {cases ρ_x,
    {assumption},
    {exact ih_1 (by assumption)}}
end

lemma inst_ρ_implies_kn_r {F: F} {ρ ρ': ρ} {x: x} {a': a}
  (ρ'_x: ρ_to ρ' x a')
  (sim: inst_ρ F ρ ρ'):
  kn_a a' :=
begin induction sim,
  {cases ρ'_x},
  {cases ρ'_x,
    {assumption},
    {exact ih_1 (by assumption)}}
end

lemma opq_ρ_implies_uk {F: F} {ρ: ρ} {x: x} {a: a}
  (ρ_x: ρ_to ρ x a)
  (opq: opq_ρ F ρ):
  uk_a a :=
begin induction opq,
  {cases ρ_x},
  {cases ρ_x,
     {assumption},
     {exact ih_1 (by assumption)}}
end

lemma ext_F_preserves_opq_ρ {F} {a₁ a₁': a} {ρ: ρ} 
  (F_excl: map_excl F a₁)
  (opq: opq_ρ F ρ):
  opq_ρ (F_ext F a₁ a₁') ρ :=
begin induction opq with F F aₓ x ρ₀ ukx ukaₓ F_aₓ opq₀ IH,
  {constructor},
  {have a₁ ≠ aₓ, from excl_implies_ineq₁ F_aₓ F_excl,
   opq_ρ.ext (by assumption)
             (by assumption)
              (map_to₁.rst ‹a₁ ≠ aₓ› F_aₓ)
              (IH F_excl)}
end

lemma ext_F_preserves_inst_ρ {F} {a a': a} {ρ ρ': ρ} 
  (F_excl: map_excl F a)
  (sim_ρ: inst_ρ F ρ ρ'):
  inst_ρ (F_ext F a a') ρ ρ' :=
begin induction sim_ρ,
  {constructor},
  {exact inst_ρ.ext (by assumption) (by assumption) (by assumption)
                     (map_to₁.rst (excl_implies_ineq₁ (by assumption) F_excl) (by assumption))
                     (ih_1 F_excl)}
end

lemma ext_F_preserves_inst_V {F} {a a': a} {V V': V} 
  (F_excl: map_excl F a)
  (sim_V: inst_V F V V'):
  inst_V (F_ext F a a') V V' :=
begin cases sim_V,
  {constructor},
  {exact inst_V.clo (by assumption) (by assumption)
                    (ext_F_preserves_inst_ρ F_excl (by assumption))},
  {constructor},
  {exact inst_V.l_s (by assumption) (by assumption)
                    (ext_F_preserves_opq_ρ F_excl (by assumption))}
end

lemma ext_σ_preserves_rstr_V {F} {σ': σ} {a': a} {V' V₀': V}
  (opq: rstr_V F σ' V₀'):
  rstr_V F (σ_ext σ' a' V') V₀' :=
begin cases opq,
  exact rstr_V.of (map_to.rst (by assumption)) (by assumption)
end

lemma ext_σ_preserves_rstr_φ {F} {σ': σ} {φ: φ} {a': a} {V': V}
  (opq: rstr_φ F σ' φ):
  rstr_φ F (σ_ext σ' a' V') φ :=
begin induction opq,
  {exact rstr_φ.fn (ext_σ_preserves_rstr_V (by assumption))},
  {exact rstr_φ.ar (by assumption) (by assumption)},
  {exact rstr_φ.st (by assumption) (by assumption)}
end

lemma ext_σ_preserves_inst_κ {F} {σ': σ} {a': a} {κ κ': κ} {V': V}
  (sim_κ: inst_κ F σ' κ κ'):
  inst_κ F (σ_ext σ' a' V') κ κ' :=
begin induction sim_κ,
  {constructor},
  {exact inst_κ.ext (by assumption) ih_1},
  {exact inst_κ.ns0 ih_1},
  {exact inst_κ.nsn (ext_σ_preserves_rstr_φ (by assumption)) ih_1}
end

lemma ext_F_preserves_inst_φ {F} {φ φ': φ} {a a': a}
  (F_excl: map_excl F a)
  (sim: inst_φ F φ φ'):
  inst_φ (F_ext F a a') φ φ' :=
begin cases sim,
  {exact inst_φ.fn (ext_F_preserves_inst_V F_excl (by assumption))},
  {exact inst_φ.ar (by assumption) (ext_F_preserves_inst_ρ F_excl (by assumption))},
  {exact inst_φ.st (by assumption) (by assumption)
                   (map_to₁.rst (excl_implies_ineq₁ (by assumption) (by assumption))
                                (by assumption))}
end

lemma ext_preserves_rstr_V {F} {σ': σ} {a a': a} {V' V₀': V}
  (F_excl: map_excl F a)
  (opq: rstr_V F σ' V₀'):
  rstr_V (F_ext F a a') (σ_ext σ' a' V') V₀' :=
begin cases opq,
  {exact rstr_V.of (map_to.rst (by assumption))
                   (ext_F_preserves_inst_V F_excl (by assumption))}
end

lemma ext_preserves_rstr_φ {F} {σ': σ} {a a': a} {φ: φ} {V': V}
  (F_excl: map_excl F a)
  (opq: rstr_φ F σ' φ):
  rstr_φ (F_ext F a a') (σ_ext σ' a' V') φ :=
begin cases opq,
  {exact rstr_φ.fn (ext_preserves_rstr_V F_excl (by assumption))},
  {exact rstr_φ.ar (by assumption) (ext_F_preserves_opq_ρ F_excl (by assumption))},
  {exact rstr_φ.st (by assumption)
                   (map_to₁.rst (excl_implies_ineq₁ (by assumption) (by assumption))
                                (by assumption))}
end

lemma ext_preserves_inst_κ {F} {σ': σ} {a a': a} {κ κ': κ} {V': V}
  (F_excl: map_excl F a)
  (sim_κ: inst_κ F σ' κ κ'):
  inst_κ (F_ext F a a') (σ_ext σ' a' V') κ κ' :=
begin induction sim_κ,
  {constructor},
  {exact inst_κ.ext (ext_F_preserves_inst_φ F_excl (by assumption)) (ih_1 F_excl)},
  {exact inst_κ.ns0 (ih_1 F_excl)},
  {exact inst_κ.nsn (ext_preserves_rstr_φ F_excl (by assumption)) (ih_1 F_excl)}
end

lemma closing_preserves_opq {F dom ρ}
  (opq: opq_ρ F ρ):
  opq_ρ F (shrink_ρ dom ρ) :=
begin cases classical.em (dom = ∅),
  {simp [a], constructor},
  {simp [a], assumption}
end

lemma inst_a_from_lookup_ρ {F: F} {ρ ρ': ρ} {x: x} {a: a}
  (ρ_at_x: ρ_to ρ x a)
  (sim_ρ: inst_ρ F ρ ρ'):
  ∃ a', ρ_to ρ' x a' ∧ F_to F a a' :=
begin induction sim_ρ,
  {cases ρ_at_x},
  {cases ρ_at_x,
     {exact ⟨a', ⟨map_to₁.fnd, (by assumption)⟩⟩},
     {cases (ih_1 (by assumption)) with a₁' h₁',
      cases h₁' with ρ'_at_a₁' F_at_a,
      exact ⟨a₁', ⟨map_to₁.rst (by assumption) ρ'_at_a₁', F_at_a⟩⟩}}
end

lemma inst_V_from_lookup_σ {F: F} {σ σ': σ} {a a': a} {V: V}
  (F_at_a: F_to F a a')
  (σ_at_a: σ_to σ a V)
  (sim_σ: inst_σ F σ σ'):
  ∃ V', σ_to σ' a' V' ∧ inst_V F V V' :=
begin induction sim_σ,
  {cases σ_at_a},
  {cases σ_at_a,
     {cases F_at_a,
        {exact ⟨V', ⟨map_to.fnd, ext_F_preserves_inst_V (by assumption) (by assumption)⟩⟩},
        {contradiction}},
     {cases F_at_a,
        {exfalso, exact excl_not_map_to (by assumption) (by assumption)},
        {cases ih_1 (by assumption) (by assumption) with V₂' h',
         cases h' with h₁ h₂,
         exact ⟨V₂', ⟨map_to.rst h₁, ext_F_preserves_inst_V (by assumption) h₂⟩⟩}}},
  {cases ih_1 (by assumption) (by assumption) with V₂' h',
   cases h' with h₁ h₂,
   exact ⟨V₂', ⟨map_to.rst h₁, h₂⟩⟩},
  {cases σ_at_a,
     {note same := map_to₁_unique F_at_a (by assumption),
      rw same,
      exact ⟨V', ⟨map_to.fnd, by assumption⟩⟩},
     {cases ih_1 F_at_a (by assumption) with V₂' h',
      cases h' with h₁ h₂,
      exact ⟨V₂', ⟨map_to.rst h₁, h₂⟩⟩}}
end

lemma lookup_opq_ρ {F: F} {ρ: ρ} {x: x} {a: a}
  (opq: opq_ρ F ρ)
  (ρ_x: ρ_to ρ x a):
  F_to F a aₗ :=
begin induction opq,
  {cases ρ_x},
  {cases ρ_x,
     {assumption},
     {exact (ih_1 (by assumption))}}
end

lemma lookup_ρ {F: F} {σ σ': σ} {ρ ρ': ρ} {x: x} {a: a} {V: V}
  (ρ_at_x: ρ_to ρ x a)
  (σ_at_a: σ_to σ a V)
  (sim_ρ: inst_ρ F ρ ρ')
  (sim_σ: inst_σ F σ σ'):
  ∃ a' V', ρ_to ρ' x a' ∧ σ_to σ' a' V' ∧ inst_V F V V' :=
begin
cases (inst_a_from_lookup_ρ ρ_at_x sim_ρ) with a' ha',
cases ha' with ρ'_at_a' F_at_a,
cases (inst_V_from_lookup_σ F_at_a σ_at_a sim_σ) with V' hV',
cases hV' with σ'_at_a' sim_V,
exact ⟨_, _, ⟨ρ'_at_a', σ'_at_a', sim_V⟩⟩
end

-- Instantiated stack cannot contain symbol
lemma inst_φ_no_sym {F ℓ φ}: ¬ inst_φ F (φ.fn ℓ V.s) φ :=
assume contra, begin cases contra, cases a end

lemma inst_κ_no_sym {F σ' ℓ κ κ'}: ¬ inst_κ F σ' (φ.fn ℓ V.s :: κ) κ' :=
assume contra,
begin induction κ', -- better to induct on `contra` but can't...
  {cases contra},
  {cases contra,
     {exact inst_φ_no_sym (by assumption)},
     {exact (ih_1 (by assumption))},
     {cases ‹rstr_φ _ _ _›, cases ‹rstr_V _ _ _›, cases ‹inst_V _ _ _›}}
end

-- By construction, opaque body `hv V` is always on top of `fn ●` stack frame
-- I define and prove this invariant simply because I use the CESK machine,
-- and want to have indepdent definitions of `E⊑E` and `κ⊑κ`,
-- instead of saying that "opaque application ⟨V, fn ● ∷ κ, σ⟩" approximates unknown code.
inductive s_wellformed: s → Prop
| ev: ∀ {e' ρ' κ' σ'}, σ_to σ' aₗ V.s → s_wellformed ⟨E.ev e' ρ', κ', σ'⟩ -- don't care
| rt: ∀ {A' κ' σ'}, σ_to σ' aₗ V.s → s_wellformed ⟨E.rt A', κ', σ'⟩ -- don't care
| hv: ∀ {κ' σ'}, σ_to σ' aₗ V.s → s_wellformed ⟨E.hv, φ.fn ℓ.uk V.s :: κ', σ'⟩

lemma reduction_preserves_wellformedness
  {s₁ s₂: s}
  (s₁_wellformed: s_wellformed s₁)
  (trace: s₁ ~>* s₂):
  s_wellformed s₂ :=
begin induction trace,
  {assumption},
  {apply ih_1, cases ‹_ ~> _›,
     repeat {cases s₁_wellformed,
             repeat {constructor},
             try {repeat {apply map_to.rst}},
             assumption}}
end

-- Restricting simulating environments by the same domain preserves simulation
lemma shrink_preserves_inst {F dom ρ ρ'}
  (sim: inst_ρ F ρ ρ'):
  inst_ρ F (shrink_ρ dom ρ) (shrink_ρ dom ρ') :=
begin cases classical.em (dom = ∅), -- cheating
  {simp [a], exact inst_ρ.mt},
  {have h : shrink_ρ dom ρ  = ρ , from shrink_nonempty ρ  dom (by assumption),
   have h': shrink_ρ dom ρ' = ρ', from shrink_nonempty ρ' dom (by assumption),
   begin simp [h, h'], exact sim
   end}
end

-- Instantiating holes in incomplete expression preserves set of free variables
lemma inst_preserves_fv {e e'} (sim: inst_e e e'): fv e = fv e' :=
begin induction sim,
  {simp},
  {simp, rw ih_1},
  {simp},
  {simp, rw ih_1, rw ih_2},
  {simp, rw ih_1},
  {simp},
  {simp, rw -a, simp}
end

lemma closing_preserves_inst {F e e' ρ ρ'}
  (sim_e: inst_e e e')
  (sim_ρ: inst_ρ F ρ ρ'):
  inst_ρ F (shrink_ρ (fv e) ρ) (shrink_ρ (fv e') ρ') :=
have same_dom: fv e = fv e', from inst_preserves_fv sim_e,
begin rw same_dom, exact shrink_preserves_inst sim_ρ end

lemma σ_excl_implies_F_excl {F: F} {σ σ': σ} {a: a}
  (sim: inst_σ F σ σ')
  (σ_na: map_excl σ a):
  map_excl F a :=
begin induction sim,
  {constructor},
  {cases σ_na,
     exact map_excl.ext (by assumption) (ih_1 (by assumption))},
  {exact ih_1 σ_na},
  {cases σ_na, exact ih_1 (by assumption)}
end

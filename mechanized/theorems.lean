import definitions lemmas

lemma reduction_preserves_approximation
-- Symbolic state `s₁'`, in 0+ steps,
-- continues to approximate the next step of any state `s₁` it currently approximates
  {s₁ s₂ s₁' : s}
  (s₁'_wellformed: s_wellformed s₁')
  (concrete_reduction: s₁ ~> s₂ )
  (approximation     : s₁ ⊑  s₁'):
  ∃ s₂', s₁' ~>* s₂' ∧ s₂ ⊑ s₂' :=
begin
cases approximation with F sim_s,
cases sim_s,
cases ‹inst_E F E E'›,
  
  -- structural case `ev`
  {apply ev_reduction_preserves_approximation, repeat {assumption}},

  -- structural case `rt`
  {apply rt_reduction_preserves_approximation, repeat {assumption}},

  -- non-structural case `hv`
  {apply hv_reduction_preserves_approximation, repeat {assumption}}
end

-- Another indirect lemma proving `~>*` preserves `⊑`, just b/c Lean is weird...
lemma refl_tran_reduction_preserves_approximation
  {s₁ s₂: s}
  (concrete_trace: s₁ ~>* s₂):
  ∀ (s₁': s)
    (s₁'_wellformed: s_wellformed s₁')
    (approximation : s₁ ⊑   s₁'),
     ∃ s₂', s₁' ~>* s₂' ∧ s₂ ⊑ s₂' :=
begin induction concrete_trace,
  -- Base case of length-0 trace
  {intros, exact ⟨s₁', ⟨rr.rfl, approximation⟩⟩},
  -- Step case
  {intros,
   have first_step_simulated: ∃ s₂', s₁' ~>* s₂' ∧ s₂ ⊑ s₂',
     from reduction_preserves_approximation s₁'_wellformed ‹s₁ ~> s₂› approximation,
   exists.elim first_step_simulated
     (take s₂', assume ⟨steps₁, simulation₁⟩,
        have s₂'_wellformed: _,
          from reduction_preserves_wellformedness s₁'_wellformed steps₁,
        have result: _, from ih_1 s₂' s₂'_wellformed simulation₁,
        exists.elim result
          (take sₐ', assume ⟨steps₂, simulation₂⟩,
             ⟨sₐ', ⟨rr_tran steps₁ steps₂, simulation₂⟩⟩))}
end

theorem symbolic_discovers_blame
-- Running symbolic program `e'` (by first loading it to initial state with `inj`)
-- results in a blame `(blm ℓₖₙ)` on the transparent component
-- if running any instantiation `e` of `e'` can do so.
  (e e': e)
  (approx: e ⊑ₑ e'):
  (∃ σ  κ , inj  e  ~>* ⟨E.rt (A.blm ℓ.kn), κ , σ ⟩) →
  (∃ σ' κ', inj' e' ~>* ⟨E.rt (A.blm ℓ.kn), κ', σ'⟩) :=
assume exists_error_trace,
exists.elim exists_error_trace
  (take σ, assume h,
     exists.elim h
       (take κ,
        assume concrete_error_trace,
        begin
          note symbolic_error_trace :=
          refl_tran_reduction_preserves_approximation
                concrete_error_trace
                (inj' e')
                (s_wellformed.ev map_to.fnd)
                ⟨[], inst_s.of (inst_E.ev approx inst_ρ.mt) inst_κ.mt inst_σ.mt⟩,
          cases symbolic_error_trace with sₐ' h,
          cases h with stepsₐ approxₐ,
          cases approxₐ with F approx_sₐ,
          cases approx_sₐ with F Eₐ Eₐ' κₐ κₐ' σₐ σₐ' approx_Eₐ approx_κₐ approx_σₐ,
          cases approx_Eₐ, cases ‹inst_A F (A.blm ℓ.kn) A'›,
          exact ⟨_, _, stepsₐ⟩
        end))

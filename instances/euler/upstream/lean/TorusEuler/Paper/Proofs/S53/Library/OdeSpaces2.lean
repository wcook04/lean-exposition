import TorusEuler.Paper.Proofs.S53.Library.OdeSpaces

/-!
# S53 library: the submodules `Esub`, `Fsub`, `Asub` and the derivative maps
-/

open Set


namespace TorusEuler.Paper.Lib.S53

noncomputable section

variable {Idx : Type} {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Membership in the space of solution jets. -/
def EP (s : Slab) (u : List Idx → ℝ → V) : Prop :=
  IsSymm u ∧ ∀ w, DifferentiableOn ℝ (u w) (Icc s.l s.r) ∧
    ContinuousOn (derivWithin (u w) (Icc s.l s.r)) (Icc s.l s.r)

/-- Auxiliary fact `derivWithin_add_on` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem derivWithin_add_on (s : Slab) {f g : ℝ → V} (hf : DifferentiableOn ℝ f (Icc s.l s.r))
    (hg : DifferentiableOn ℝ g (Icc s.l s.r)) {t : ℝ} (ht : t ∈ Icc s.l s.r) :
    derivWithin (f + g) (Icc s.l s.r) t =
      derivWithin f (Icc s.l s.r) t + derivWithin g (Icc s.l s.r) t :=
  derivWithin_add (hf t ht) (hg t ht)

/-- Auxiliary fact `derivWithin_smul_on` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem derivWithin_smul_on (s : Slab) {f : ℝ → V} (c : ℝ) (hf : DifferentiableOn ℝ f (Icc s.l s.r))
    {t : ℝ} (ht : t ∈ Icc s.l s.r) :
    derivWithin (c • f) (Icc s.l s.r) t = c • derivWithin f (Icc s.l s.r) t :=
  derivWithin_const_smul c (hf t ht)

/-- The space of solution jets. -/
def Esub (Idx V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (s : Slab) :
    Submodule ℝ (List Idx → ℝ → V) where
  carrier := {u | EP s u}
  add_mem' := by
    rintro u v ⟨hu, hu'⟩ ⟨hv, hv'⟩
    refine ⟨fun {w w'} h => ?_, fun w => ⟨(hu' w).1.add (hv' w).1, ?_⟩⟩
    · simp only [Pi.add_apply]; rw [hu h, hv h]
    · refine ((hu' w).2.add (hv' w).2).congr fun t ht => ?_
      simp only [Pi.add_apply]
      exact derivWithin_add_on s (hu' w).1 (hv' w).1 ht
  zero_mem' := by
    refine ⟨fun _ => rfl, fun w => ⟨differentiableOn_const _, ?_⟩⟩
    exact (continuousOn_const (c := (0 : V))).congr fun t _ => by simp
  smul_mem' := by
    rintro c u ⟨hu, hu'⟩
    refine ⟨fun {w w'} h => ?_, fun w => ⟨(hu' w).1.const_smul c, ?_⟩⟩
    · simp only [Pi.smul_apply]; rw [hu h]
    · refine ((hu' w).2.const_smul c).congr fun t ht => ?_
      simp only [Pi.smul_apply]
      exact derivWithin_smul_on s c (hu' w).1 ht

/-- Weighted boundedness of a function on the slab. -/
def WBdd (s : Slab) (f : ℝ → V) : Prop := ∃ M : ℝ, ∀ t ∈ Icc s.l s.r, ‖f t‖ ≤ M * s.g t

omit [NormedSpace ℝ V] in
/-- Auxiliary fact `wbdd_of_continuousOn` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem wbdd_of_continuousOn (s : Slab) {f : ℝ → V} (hf : ContinuousOn f (Icc s.l s.r)) :
    WBdd s f := by
  have hc : ContinuousOn (fun t => ‖f t‖ / s.g t) (Icc s.l s.r) :=
    hf.norm.div s.hgc fun t ht => (s.hg0 t ht).ne'
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨M, fun t ht => ?_⟩
  have h := hM t ht
  rw [Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (s.hg0 t ht).le)] at h
  exact (div_le_iff₀ (s.hg0 t ht)).mp h

omit [NormedSpace ℝ V] in
/-- Auxiliary fact `add` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem WBdd.add {s : Slab} {f g : ℝ → V} (hf : WBdd s f) (hg : WBdd s g) : WBdd s (f + g) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨N, hN⟩ := hg
  refine ⟨M + N, fun t ht => ?_⟩
  calc ‖(f + g) t‖ ≤ ‖f t‖ + ‖g t‖ := norm_add_le _ _
    _ ≤ M * s.g t + N * s.g t := add_le_add (hM t ht) (hN t ht)
    _ = _ := by ring

/-- Auxiliary fact `smul` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem WBdd.smul {s : Slab} {f : ℝ → V} (c : ℝ) (hf : WBdd s f) : WBdd s (c • f) := by
  obtain ⟨M, hM⟩ := hf
  refine ⟨|c| * M, fun t ht => ?_⟩
  calc ‖(c • f) t‖ = |c| * ‖f t‖ := by simp [norm_smul]
    _ ≤ |c| * (M * s.g t) := mul_le_mul_of_nonneg_left (hM t ht) (abs_nonneg _)
    _ = _ := by ring

end

end TorusEuler.Paper.Lib.S53

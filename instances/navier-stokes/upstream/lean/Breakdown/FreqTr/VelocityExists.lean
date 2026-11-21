import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.VelocityExists

theorem differentiableAt_of_isTestField {φ : Space → Space} (hφ : IsTestField φ) (y : Space) :
    DifferentiableAt ℝ φ y :=
  (hφ.1.differentiable (by simp)).differentiableAt

theorem isTestField_add {φ ψ : Space → Space} (hφ : IsTestField φ) (hψ : IsTestField ψ) :
    IsTestField (φ + ψ) := by
  refine ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, fun y => ?_⟩
  have e : fderiv ℝ (φ + ψ) y = fderiv ℝ φ y + fderiv ℝ ψ y :=
    fderiv_add (differentiableAt_of_isTestField hφ y) (differentiableAt_of_isTestField hψ y)
  have a := hφ.2.2 y
  have b := hψ.2.2 y
  simp only [divergenceAt, e, add_apply, PiLp.add_apply,
    Finset.sum_add_distrib] at a b ⊢
  rw [a, b, add_zero]

theorem isTestField_sub {φ ψ : Space → Space} (hφ : IsTestField φ) (hψ : IsTestField ψ) :
    IsTestField (φ - ψ) := by
  refine ⟨hφ.1.sub hψ.1, hφ.2.1.sub hψ.2.1, fun y => ?_⟩
  have e : fderiv ℝ (φ - ψ) y = fderiv ℝ φ y - fderiv ℝ ψ y :=
    fderiv_sub (differentiableAt_of_isTestField hφ y) (differentiableAt_of_isTestField hψ y)
  have a := hφ.2.2 y
  have b := hψ.2.2 y
  simp only [divergenceAt, e, sub_apply, PiLp.sub_apply,
    Finset.sum_sub_distrib] at a b ⊢
  rw [a, b, sub_zero]

theorem isTestField_smul (c : ℝ) {φ : Space → Space} (hφ : IsTestField φ) :
    IsTestField (c • φ) := by
  refine ⟨hφ.1.const_smul c, hφ.2.1.smul_left (f := fun _ : Space => c), fun y => ?_⟩
  have e : fderiv ℝ (c • φ) y = c • fderiv ℝ φ y :=
    fderiv_const_smul (differentiableAt_of_isTestField hφ y) c
  have a := hφ.2.2 y
  simp only [divergenceAt, e, smul_apply, PiLp.smul_apply, smul_eq_mul,
    ← Finset.mul_sum] at a ⊢
  rw [a, mul_zero]

theorem isDecayField_of_isTestField {φ : Space → Space} (hφ : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hs, hc, hd⟩ := hφ
  refine ⟨hs, hd, ?_⟩
  obtain ⟨M₁, hM₁⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨M₂, hM₂⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv ℝ)
  obtain ⟨M, hM, hMa, hMb⟩ : ∃ M : ℝ, 0 ≤ M ∧ (∀ y, ‖φ y‖ ≤ M) ∧ ∀ y, ‖fderiv ℝ φ y‖ ≤ M :=
    ⟨max (max M₁ M₂) 0, le_max_right _ _,
      fun y => (hM₁ y).trans ((le_max_left _ _).trans (le_max_left _ _)),
      fun y => (hM₂ y).trans ((le_max_right _ _).trans (le_max_left _ _))⟩
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall 0
  obtain ⟨R, hR0, hR⟩ : ∃ R : ℝ, 0 ≤ R ∧ ∀ y ∈ tsupport φ, ‖y‖ ≤ R := by
    refine ⟨max R₀ 0, le_max_right _ _, fun y hy => ?_⟩
    have h := hR₀ hy
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h.trans (le_max_left _ _)
  refine ⟨M * (1 + R) ^ 2, fun y => ?_⟩
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  have hpos : 0 < 1 + ‖y‖ := by linarith
  by_cases hys : y ∈ tsupport φ
  · have h1 : 1 + ‖y‖ ≤ 1 + R := by linarith [hR y hys]
    constructor
    · rw [le_div_iff₀ hpos]
      calc ‖φ y‖ * (1 + ‖y‖) ≤ M * (1 + R) := mul_le_mul (hMa y) h1 hpos.le hM
        _ ≤ M * (1 + R) ^ 2 := by
            apply mul_le_mul_of_nonneg_left _ hM
            nlinarith
    · rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul (hMb y) (pow_le_pow_left₀ hpos.le h1 2) (by positivity) hM
  · have h0 : φ y = 0 := image_eq_zero_of_notMem_tsupport hys
    have h0' : fderiv ℝ φ y = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hys (tsupport_fderiv_subset ℝ h))
    rw [h0, h0', norm_zero, norm_zero]
    exact ⟨div_nonneg (mul_nonneg hM (sq_nonneg _)) hpos.le,
      div_nonneg (mul_nonneg hM (sq_nonneg _)) (by positivity)⟩

theorem toLpOrZero_eq {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (hf : MemLp f p volume) : toLpOrZero p f = hf.toLp f := by
  unfold toLpOrZero
  rw [dif_pos hf]

theorem toLpOrZero_add {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : Space → F} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    toLpOrZero p (f + g) = toLpOrZero p f + toLpOrZero p g := by
  rw [toLpOrZero_eq hf, toLpOrZero_eq hg, toLpOrZero_eq (hf.add hg), MemLp.toLp_add]

theorem toLpOrZero_sub {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f g : Space → F} (hf : MemLp f p volume) (hg : MemLp g p volume) :
    toLpOrZero p (f - g) = toLpOrZero p f - toLpOrZero p g := by
  rw [toLpOrZero_eq hf, toLpOrZero_eq hg, toLpOrZero_eq (hf.sub hg), MemLp.toLp_sub]

theorem toLpOrZero_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}
    [Fact (1 ≤ p)] (c : ℝ) {f : Space → F} (hf : MemLp f p volume) :
    toLpOrZero p (c • f) = c • toLpOrZero p f := by
  rw [toLpOrZero_eq hf, toLpOrZero_eq (hf.const_smul c), MemLp.toLp_const_smul]

theorem extend_subtypeL_apply {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (s : Submodule ℝ E)
    (hs : Dense (s : Set E)) (T : s →L[ℝ] F) (x : E) (hx : x ∈ s) :
    T.extend s.subtypeL x = T ⟨x, hx⟩ :=
  ContinuousLinearMap.extend_eq T hs.denseRange_val (isUniformInducing_val (s : Set E)) ⟨x, hx⟩

end Internal.VelocityExists

open Internal.VelocityExists in
theorem velocityExists (h1 : TestDense) (h2 : TestSpanSpec) (h3 : EmbedLinear) (h4 : EmbedNorm)
    (h5 : GradSixDecay) : VelocityExists := by
  obtain ⟨S, hS⟩ := h5
  have hmem : ∀ φ, IsTestField φ → MemLp φ 6 volume :=
    fun φ hφ => (hS φ (isDecayField_of_isTestField hφ)).1
  have hbd : ∀ f, IsDecayField f → ‖toLpOrZero 6 f‖ ≤ S * ‖embedX f‖ := fun f hf => by
    obtain ⟨hm, hb⟩ := hS f hf
    rw [toLpOrZero_eq hm, Lp.norm_toLp]
    rw [← h4 f hf, Real.sqrt_sq (norm_nonneg _)] at hb
    exact hb
  have heq : ∀ φ ψ, IsTestField φ → IsTestField ψ → embedX φ = embedX ψ →
      toLpOrZero 6 φ = toLpOrZero 6 ψ := by
    intro φ ψ hφ hψ h
    have hb := hbd _ (isDecayField_of_isTestField (isTestField_sub hφ hψ))
    rw [toLpOrZero_sub (hmem φ hφ) (hmem ψ hψ),
      h3.2.1 φ ψ (isDecayField_of_isTestField hφ) (isDecayField_of_isTestField hψ), h, sub_self,
      norm_zero, mul_zero] at hb
    exact sub_eq_zero.mp (norm_le_zero_iff.mp hb)
  choose g hg hge using h2
  have hadd : ∀ x y : testSpan, toLpOrZero 6 (g ((x + y : testSpan) : X) (x + y).2) =
      toLpOrZero 6 (g x x.2) + toLpOrZero 6 (g y y.2) := by
    intro x y
    have hx := hg x x.2
    have hy := hg y y.2
    rw [← toLpOrZero_add (hmem _ hx) (hmem _ hy)]
    apply heq _ _ (hg _ _) (isTestField_add hx hy)
    have e1 : embedX (g x x.2 + g y y.2) = embedX (g x x.2) + embedX (g y y.2) :=
      h3.1 _ _ (isDecayField_of_isTestField hx) (isDecayField_of_isTestField hy)
    exact (hge _ _).trans ((Submodule.coe_add x y).trans
      (e1.trans (congrArg₂ (· + ·) (hge x x.2) (hge y y.2))).symm)
  have hsmul : ∀ (c : ℝ) (x : testSpan), toLpOrZero 6 (g ((c • x : testSpan) : X) (c • x).2) =
      c • toLpOrZero 6 (g x x.2) := by
    intro c x
    have hx := hg x x.2
    rw [← toLpOrZero_smul c (hmem _ hx)]
    apply heq _ _ (hg _ _) (isTestField_smul c hx)
    have e1 : embedX (c • g x x.2) = c • embedX (g x x.2) :=
      h3.2.2 c _ (isDecayField_of_isTestField hx)
    exact (hge _ _).trans ((Submodule.coe_smul c x).trans
      (e1.trans (congrArg (c • ·) (hge x x.2))).symm)
  have hnorm : ∀ x : testSpan, ‖toLpOrZero 6 (g x x.2)‖ ≤ S * ‖x‖ := by
    intro x
    have hb := hbd _ (isDecayField_of_isTestField (hg x x.2))
    exact hb.trans_eq (congrArg (S * ·) (congrArg norm (hge x x.2)))
  let T₀ : testSpan →ₗ[ℝ] L6R :=
    { toFun := fun x => toLpOrZero 6 (g x x.2)
      map_add' := hadd
      map_smul' := hsmul }
  let T : testSpan →L[ℝ] L6R := T₀.mkContinuous S hnorm
  have hT : ∀ x, T x = toLpOrZero 6 (g x x.2) := fun x => rfl
  refine ⟨T.extend testSpan.subtypeL, fun φ hφ => ?_⟩
  have hm : embedX φ ∈ testSpan := Submodule.subset_span ⟨φ, hφ, rfl⟩
  rw [extend_subtypeL_apply testSpan h1 T _ hm, hT]
  exact heq _ _ (hg _ hm) hφ (hge _ hm)

end Breakdown.Freq

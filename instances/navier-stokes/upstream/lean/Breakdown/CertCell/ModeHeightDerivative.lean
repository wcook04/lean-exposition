import Breakdown.CertCell.ModeHeightOrbitAverage

open scoped ContDiff Topology ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.HeightModes

open CellCert.CellAnalysis (cylPoint axialUnit)
open HeightOrbit

def rotCoeff0 : Fin 3 → (Space →L[ℝ] ℝ) := ![EuclideanSpace.proj 0, EuclideanSpace.proj 1, 0]

def rotCoeff1 : Fin 3 → (Space →L[ℝ] ℝ) := ![EuclideanSpace.proj 1, -EuclideanSpace.proj 0, 0]

def rotCoeff2 : Fin 3 → (Space →L[ℝ] ℝ) := ![0, 0, EuclideanSpace.proj 2]

def frameCoord (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ := q.1 • rotCoeff0 a + q.2 • rotCoeff1 a + rotCoeff2 a

theorem frameCoord_smooth (a : Fin 3) : ContDiff ℝ ∞ (frameCoord a) :=
  ((contDiff_fst.smul contDiff_const).add (contDiff_snd.smul contDiff_const)).add contDiff_const

theorem frameCoord_apply (a : Fin 3) (θ : ℝ) (u : Space) :
    frameCoord a (Real.cos θ, Real.sin θ) u = axialRot (-θ) u a := by
  fin_cases a <;> simp [frameCoord, rotCoeff0, rotCoeff1, rotCoeff2, axialRot, unitVector, Real.cos_neg,
    Real.sin_neg]
  ring

theorem axialRot_planePoint (p : ℝ × ℝ) (φ : ℝ) : axialRot φ (planePoint p) = cylPoint p.1 φ p.2 := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, cylPoint, unitVector] <;> ring

theorem axialRot_first (φ : ℝ) : axialRot φ (unitVector 0) = unitAt (Real.cos φ, Real.sin φ) := by
  ext i
  fin_cases i <;> simp [axialRot, unitAt, unitVector]

theorem axialRot_third (φ : ℝ) : axialRot φ (unitVector 2) = axialUnit := by
  ext i
  fin_cases i <;> simp [axialRot, axialUnit, unitVector]

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mode_eq {β : Type*} (ξ : ℤ × ℤ) (f' : ℝ → ℝ → β → ℝ) (b : β) (h : ℝ → Space → E)
    (Λ : ℝ × ℝ → (E →L[ℝ] ℝ)) (p : ℝ × ℝ)
    (hpt : ∀ τ θ, f' τ θ b = Λ (Real.cos θ, Real.sin θ) (h τ (cylPoint p.1 θ p.2))) :
    modeAverage ξ f' b = (1 / (2 * Real.pi) : ℂ) * waveAvg h Λ ξ.1 ξ.2 p := by
  unfold modeAverage waveAvg wave timeFactor
  congr 1
  refine intervalIntegral.integral_congr fun τ _ => ?_
  simp only
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [hpt τ θ]
  rw [← mul_assoc, ← Complex.exp_add]
  congr 2
  unfold CellCert.CellAnalysis.azimuth
  push_cast
  ring

theorem vel_rep (ξ : ℤ × ℤ) (v : ℝ → Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVel ξ v 0 (planePoint p) a = (1 / (2 * Real.pi) : ℂ) * waveAvg v (frameCoord a) ξ.1 ξ.2 p :=
  mode_eq ξ _ a v (frameCoord a) p fun τ θ => by
    rw [zero_add, axialRot_planePoint, frameCoord_apply]

theorem gradz_rep (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeGrad ξ G 0 (planePoint p) (a, 2) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg G (axialL (frameCoord a)) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 2) G (axialL (frameCoord a)) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, axialRot_third, axialL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem gradr_rep (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeGrad ξ G 0 (planePoint p) (a, 0) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg G (radialL (frameCoord a)) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 0) G (radialL (frameCoord a)) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, axialRot_first, radialL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem secondDerivzz_rep (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeSecondDeriv ξ H 0 (planePoint p) (a, 2, 2) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg H (axialL (axialL (frameCoord a))) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 2, 2) H (axialL (axialL (frameCoord a))) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, axialRot_third, axialL, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.apply_apply, frameCoord_apply]

theorem secondDerivrz_rep (ξ : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) =
      (1 / (2 * Real.pi) : ℂ) * waveAvg H (radialL (axialL (frameCoord a))) ξ.1 ξ.2 p :=
  mode_eq ξ _ (a, 0, 2) H (radialL (axialL (frameCoord a))) p fun τ θ => by
    simp only [zero_add, axialRot_planePoint, axialRot_first, axialRot_third, axialL, radialL,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, frameCoord_apply]


theorem vec_sum (u : Space) : u = ∑ i : Fin 3, u i • unitVector i := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem opNorm_le_cols {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (A : Space →L[ℝ] X) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  calc ‖A u‖ = ‖∑ i : Fin 3, u i • A (unitVector i)‖ := by
        conv_lhs => rw [vec_sum u]
        simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖u i • A (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖u‖ * ‖A (unitVector i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le u i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (unitVector i)‖) * ‖u‖ := by rw [← Finset.mul_sum, mul_comm]

theorem loc_norm {X : Type} [NormedAddCommGroup X] {f : Space → X} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => ‖f y‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Eventually.of_forall fun y => by simp)

theorem col_loc {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {A : Space → (Space →L[ℝ] X)}
    (hA : LocallyIntegrable A volume) (j : Fin 3) : LocallyIntegrable (fun y => A y (unitVector j)) volume :=
  hA.mono (hA.aestronglyMeasurable.apply_continuousLinearMap _) (Eventually.of_forall fun y => by
    refine ((A y).le_opNorm _).trans (le_of_eq ?_)
    rw [unitVector, PiLp.norm_single, norm_one, mul_one])

theorem flip_loc {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {B : Space → (Space →L[ℝ] Space →L[ℝ] X)}
    (hm : AEStronglyMeasurable B volume) (hc : ∀ i : Fin 3, LocallyIntegrable (fun y => (B y).flip (unitVector i)) volume) :
    LocallyIntegrable B volume := by
  have hs : LocallyIntegrable (fun y => ‖(B y).flip (unitVector 0)‖ + ‖(B y).flip (unitVector 1)‖
      + ‖(B y).flip (unitVector 2)‖) volume := ((loc_norm (hc 0)).add (loc_norm (hc 1))).add (loc_norm (hc 2))
  refine hs.mono hm (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (by positivity), ← ContinuousLinearMap.opNorm_flip]
  simpa [Fin.sum_univ_three] using opNorm_le_cols (B y).flip

theorem grad_weak_op {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : LocallyIntegrable G volume) (hH : LocallyIntegrable H volume)
    (hw : ∀ i : Fin 3, IsWeakGradient (fun y => G y (unitVector i)) (fun y => (H y).flip (unitVector i)))
    (φ : Space → ℝ) (hφ : SteadyCert.IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) :=
    hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => φ y • H y (unitVector j)) :=
    (col_loc hH j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
      (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
    intro i
    rw [show (-∫ y, φ y • H y (unitVector j)) (unitVector i) = -((∫ y, φ y • H y (unitVector j)) (unitVector i))
      from rfl, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
    have := (hw i).2.2 φ hφ j
    simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.flip_apply] at this ⊢
    rw [this, neg_neg]
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_sum u]
  simp only [map_sum, map_smul, key]

theorem scale_id {A B : ℝ × ℝ → ℂ} {χ ψ : ℝ × ℝ → ℝ} (k : ℂ)
    (h : ∫ p, ((χ p : ℝ) : ℂ) * A p = -∫ p, ((ψ p : ℝ) : ℂ) * B p) :
    ∫ p, ((χ p : ℝ) : ℂ) * (k * A p) = -∫ p, ((ψ p : ℝ) : ℂ) * (k * B p) := by
  have e1 : (fun p => ((χ p : ℝ) : ℂ) * (k * A p)) = fun p => k * (((χ p : ℝ) : ℂ) * A p) :=
    funext fun p => by ring
  have e2 : (fun p => ((ψ p : ℝ) : ℂ) * (k * B p)) = fun p => k * (((ψ p : ℝ) : ℂ) * B p) :=
    funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem mixed_partial {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ ψ q u) p w = fderiv ℝ (fun q => fderiv ℝ ψ q w) p u := by
  have hdiff : DifferentiableAt ℝ (fderiv ℝ ψ) p :=
    ((contDiff_infty_iff_fderiv.1 hψ).2.differentiable (by simp)) p
  have ap : ∀ u' w', fderiv ℝ (fun q => fderiv ℝ ψ q u') p w' = fderiv ℝ (fderiv ℝ ψ) p w' u' := by
    intro u' w'
    rw [fderiv_clm_apply hdiff (differentiableAt_const u')]
    simp
  rw [ap, ap]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) w u

theorem deriv_test {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ)
    (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) (u : ℝ × ℝ) :
    ContDiff ℝ ∞ (fun p => fderiv ℝ ψ p u) ∧ HasCompactSupport (fun p => fderiv ℝ ψ p u) ∧
      ∀ p ∈ tsupport (fun p => fderiv ℝ ψ p u), 0 < p.1 :=
  ⟨(contDiff_infty_iff_fderiv.1 hψ).2.clm_apply contDiff_const, hc.fderiv_apply (𝕜 := ℝ) u,
    fun p hp => hpos p (tsupport_fderiv_apply_subset ℝ u hp)⟩

end Internal.HeightModes

open Internal.HeightLine Internal.HeightOrbit Internal.HeightModes in
theorem modeHeightDeriv (hE : HessianEnergyIdentityHolds) : ModeHeightDerivHolds := by
  intro Γ P v G H g hp ξ a
  obtain ⟨lv, lG, lH⟩ := Coercive.perturbationLocalIntegrabilityHolds_proof Γ P v G H g hp
  have hslice : ∀ᵐ τ, AEStronglyMeasurable (H τ) volume := hp.measurable_secondDeriv.prodMk_left
  have w1 : ∀ᵐ τ, LocallyIntegrable (v τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => G τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • v τ y = -∫ y, φ y • G τ y (unitVector j) := by
    filter_upwards [hp.weak_gradient] with τ hτ
    refine ⟨hτ.1, fun j => col_loc hτ.2.1 j, fun φ hφ j => ?_⟩
    rw [hτ.2.2 φ hφ j, neg_neg]
  have w2 : ∀ᵐ τ, LocallyIntegrable (G τ) volume ∧
      (∀ j : Fin 3, LocallyIntegrable (fun y => H τ y (unitVector j)) volume) ∧
      ∀ φ : Space → ℝ, SteadyCert.IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) • G τ y = -∫ y, φ y • H τ y (unitVector j) := by
    filter_upwards [hp.weak_gradient, hp.weak_secondDeriv, hslice] with τ h1 h2 h3
    have hHl : LocallyIntegrable (H τ) volume := flip_loc h3 fun i => (h2 i).2.1
    exact ⟨h1.2.1, fun j => col_loc hHl j, fun φ hφ j => grad_weak_op h1.2.1 hHl h2 φ hφ j⟩
  have L1s := frameCoord_smooth a
  have L2s : ContDiff ℝ ∞ (axialL (frameCoord a)) := L1s.clm_comp contDiff_const
  have L1c := L1s.continuous
  have L2c := L2s.continuous
  set c : ℂ := (1 / (2 * Real.pi) : ℂ)
  have iU : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeVel ξ v 0 (planePoint p) a) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) := fun _ _ _ _ h0 => by
    simp only [vel_rep]
    exact (waveAvg_integrableOn v lv _ L1c _ _ h0).const_mul c
  have iUz : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, 2)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) := fun _ _ _ _ h0 => by
    simp only [gradz_rep]
    exact (waveAvg_integrableOn G lG _ (axialL_cont L1c) _ _ h0).const_mul c
  have iUr : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeGrad ξ G 0 (planePoint p) (a, 0)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) := fun _ _ _ _ h0 => by
    simp only [gradr_rep]
    exact (waveAvg_integrableOn G lG _ (radialL_cont L1c) _ _ h0).const_mul c
  have iWzz : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, 2, 2)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) :=
    fun _ _ _ _ h0 => by
      simp only [secondDerivzz_rep]
      exact (waveAvg_integrableOn H lH _ (axialL_cont L2c) _ _ h0).const_mul c
  have iWrz : ∀ a₁ b₁ c₁ d₁ : ℝ, 0 < a₁ →
      IntegrableOn (fun p => modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2)) (Icc a₁ b₁ ×ˢ Icc c₁ d₁) :=
    fun _ _ _ _ h0 => by
      simp only [secondDerivrz_rep]
      exact (waveAvg_integrableOn H lH _ (radialL_cont L2c) _ _ h0).const_mul c
  have P1 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2)) := by
    intro ψ hψ hc hpos
    have h := plane_weak v G lv lG w1 (frameCoord a) L1s ξ.1 ξ.2 ψ hψ hc hpos
    simp only [vel_rep, gradr_rep, gradz_rep]
    exact ⟨scale_id c h.1, scale_id c h.2⟩
  have P2 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2)) ∧
      (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 2) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 2, 2)) := by
    intro ψ hψ hc hpos
    have h := plane_weak G H lG lH w2 (axialL (frameCoord a)) L2s ξ.1 ξ.2 ψ hψ hc hpos
    simp only [gradz_rep, secondDerivrz_rep, secondDerivzz_rep]
    exact ⟨scale_id c h.1, scale_id c h.2⟩
  have P3 : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) (a, 0) =
        -∫ p, ((ψ p : ℝ) : ℂ) * modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) := by
    intro ψ hψ hc hpos
    obtain ⟨z1, z2, z3⟩ := deriv_test hψ hc hpos (0, 1)
    obtain ⟨r1, r2, r3⟩ := deriv_test hψ hc hpos (1, 0)
    have A := (P1 _ z1 z2 z3).1
    have B := (P1 _ r1 r2 r3).2
    have C := (P2 ψ hψ hc hpos).1
    have e : (fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (0, 1)) p (1, 0) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a) =
        fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (1, 0)) p (0, 1) : ℝ) : ℂ) * modeVel ξ v 0 (planePoint p) a :=
      funext fun p => by rw [mixed_partial hψ]
    rw [e, B] at A
    rw [← C, ← neg_eq_iff_eq_neg.2 A.symm, neg_neg]
  have S1 := slice_weak _ _ iU iUz fun ψ hψ hc hpos => (P1 ψ hψ hc hpos).2
  have S2 := slice_weak _ _ iUz iWzz fun ψ hψ hc hpos => (P2 ψ hψ hc hpos).2
  have S3 := slice_weak _ _ iUr iWrz P3
  filter_upwards [S1, S2, S3] with r h1 h2 h3 h h0
  exact ⟨h1 h h0, h2 h h0, h3 h h0⟩

end Breakdown.CertCell.Bridge

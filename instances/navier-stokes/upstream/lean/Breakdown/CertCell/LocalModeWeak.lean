import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.ModeWeakIdentity
import Breakdown.FracCell.ModeRadialWeakProof
import Breakdown.FracCell.HeightModeIbp

open scoped ContDiff
open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

private def planeFrameAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

private theorem planeFrameAt_circle (θ : ℝ) : planeFrameAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

private def planeFrameCoord (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, planeFrameAt q a k • EuclideanSpace.proj k

private def circleFrameCoord (a : Fin 3) (θ : ℝ) : Space →L[ℝ] ℝ := planeFrameCoord a (Real.cos θ, Real.sin θ)

private theorem circleFrameCoord_apply (a : Fin 3) (θ : ℝ) (u : Space) :
    circleFrameCoord a θ u = inner ℝ u (frameUnit θ a) := by
  simp [circleFrameCoord, planeFrameCoord, planeFrameAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

private theorem planeFrameAt_coord_smooth (a k : Fin 3) :
    ContDiff ℝ ∞ (fun q : ℝ × ℝ => planeFrameAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [planeFrameAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

private theorem planeFrameAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => planeFrameAt q a) :=
  (contDiff_piLp 2).2 fun k => planeFrameAt_coord_smooth a k

private theorem planeFrameCoord_smooth (a : Fin 3) : ContDiff ℝ ∞ (planeFrameCoord a) := by
  unfold planeFrameCoord
  exact ContDiff.sum fun k _ => (planeFrameAt_coord_smooth a k).smul contDiff_const

private def planeRadialColumnCoord (a : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (planeFrameCoord a q).comp (ContinuousLinearMap.apply ℝ Space (planeFrameAt q 0))

private def circleRadialColumnCoord (a : Fin 3) (θ : ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  planeRadialColumnCoord a (Real.cos θ, Real.sin θ)

private theorem planeRadialColumnCoord_smooth (a : Fin 3) : ContDiff ℝ ∞ (planeRadialColumnCoord a) :=
  (planeFrameCoord_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (planeFrameAt_smooth 0))

private theorem circleRadialColumnCoord_apply (a : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    circleRadialColumnCoord a θ M = inner ℝ (M (frameUnit θ 0)) (frameUnit θ a) := by
  simp only [circleRadialColumnCoord, planeRadialColumnCoord, planeFrameAt_circle, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]
  exact circleFrameCoord_apply a θ _

private theorem space_eq_sum_coords (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem opNorm_le_sum_columns {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [space_eq_sum_coords u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

private theorem locallyIntegrable_norm_of {E : Type} [NormedAddCommGroup E] {f : Space → E}
    (hf : LocallyIntegrable f volume) : LocallyIntegrable (fun y => ‖f y‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun y => by simp)

private theorem locallyIntegrable_of_columns {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Space → (Space →L[ℝ] E)} (hm : AEStronglyMeasurable A volume)
    (hc : ∀ i, LocallyIntegrable (fun y => A y (unitVector i)) volume) : LocallyIntegrable A volume := by
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖A y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((locallyIntegrable_norm_of (hc 0)).add (locallyIntegrable_norm_of (hc 1))).add
      (locallyIntegrable_norm_of (hc 2))
  refine hs.mono hm (Filter.Eventually.of_forall fun y => ?_)
  refine (opNorm_le_sum_columns (A y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

private theorem gradient_column_memLp {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2
    (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

private theorem second_entry_memLp {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j i : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (hm.apply_continuousLinearMap (unitVector j)).apply_continuousLinearMap (unitVector i)
  refine (memLp_two_iff_integrable_sq_norm hmj).2
    (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  calc ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i' : Fin 3, ‖H y (unitVector j) (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖H y (unitVector j) (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
    _ ≤ ∑ j' : Fin 3, ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

private def IsHalfPlaneTest (ψ : ℝ × ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧ ∀ p ∈ tsupport ψ, 0 < p.1

private theorem isHalfPlaneTest_fderiv {ψ : ℝ × ℝ → ℝ} (hψ : IsHalfPlaneTest ψ) (u : ℝ × ℝ) :
    IsHalfPlaneTest (fun p => fderiv ℝ ψ p u) :=
  ⟨(hψ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const,
    hψ.2.1.fderiv_apply (𝕜 := ℝ) u, fun p hp => hψ.2.2 p (tsupport_fderiv_apply_subset ℝ u hp)⟩

private theorem fderiv_fderiv_comm {ψ : ℝ × ℝ → ℝ} (hψ : ContDiff ℝ ∞ ψ) (p u w : ℝ × ℝ) :
    fderiv ℝ (fun q => fderiv ℝ ψ q u) p w = fderiv ℝ (fun q => fderiv ℝ ψ q w) p u := by
  have hd : Differentiable ℝ (fderiv ℝ ψ) :=
    (hψ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp)
  have e : ∀ u', fderiv ℝ (fun q => fderiv ℝ ψ q u') p = (fderiv ℝ (fderiv ℝ ψ) p).flip u' := by
    intro u'
    rw [fderiv_clm_apply (hd p) (differentiableAt_const u')]
    simp
  rw [e, e]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hψ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) w u

private theorem weak_mixed_of_three {V g0 g2 h : ℝ × ℝ → ℂ}
    (I1 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * V p = -∫ p, (ψ p : ℂ) * g0 p)
    (I2 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * V p = -∫ p, (ψ p : ℂ) * g2 p)
    (I4 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * g0 p = -∫ p, (ψ p : ℂ) * h p)
    (ψ : ℝ × ℝ → ℝ) (hψ : IsHalfPlaneTest ψ) :
    ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * g2 p = -∫ p, (ψ p : ℂ) * h p := by
  have a := I2 _ (isHalfPlaneTest_fderiv hψ (1, 0))
  have b := I1 _ (isHalfPlaneTest_fderiv hψ (0, 1))
  have e : (fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (1, 0)) p (0, 1) : ℝ) : ℂ) * V p) =
      fun p => ((fderiv ℝ (fun q => fderiv ℝ ψ q (0, 1)) p (1, 0) : ℝ) : ℂ) * V p :=
    funext fun p => by rw [fderiv_fderiv_comm hψ.1]
  rw [e, b, I4 ψ hψ] at a
  rw [neg_neg] at a
  rw [a, neg_neg]

private theorem weak_identity_const_mul {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

private theorem frameVec_eq_inner (θ : ℝ) (u : Space) (a : Fin 3) :
    frameVec θ u a = inner ℝ u (frameUnit θ a) := by
  fin_cases a <;> rfl

theorem localModeWeakIdentity : LocalModeWeakIdentityStatement := by
  intro m v G H hs n a
  have hv : LocallyIntegrable v volume := hs.velocity_six.locallyIntegrable (by norm_num)
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (gradient_column_memLp hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)
  have hG : LocallyIntegrable G volume := locallyIntegrable_of_columns hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    locallyIntegrable_of_columns (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
      (second_entry_memLp hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1,
        ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [space_eq_sum_coords u]
    simp only [map_sum, map_smul, key]
  have hmv : ∀ p : ℝ × ℝ, modeVec m n v p.1 p.2 a = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (circleFrameCoord a θ (v (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [modeVec, circleFrameCoord_apply, frameVec_eq_inner]
  have hgm : ∀ (b : Fin 3) (p : ℝ × ℝ), gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (circleFrameCoord a θ (G (cylPoint p.1 θ p.2) (frameUnit θ b)) : ℂ) := by
    intro b p
    simp only [gradMode, modeMat, circleFrameCoord_apply]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a 0 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (circleRadialColumnCoord a θ (H (cylPoint p.1 θ p.2) axialUnit) : ℂ) := by
    intro p
    simp only [modeThird, circleRadialColumnCoord_apply]
    rfl
  have I1 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p := by
    intro ψ hψ
    simp only [hmv, hgm]
    exact weak_identity_const_mul _ (cylModeWeak Space v G hv hGc hs.weak_gradient (planeFrameCoord a)
      (planeFrameCoord_smooth a) m n ψ hψ.1 hψ.2.1 hψ.2.2).1
  have I2 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
      -∫ p, (ψ p : ℂ) * gradMode m n G a 2 p := by
    intro ψ hψ
    simp only [hmv, hgm]
    exact weak_identity_const_mul _ (cylModeWeak Space v G hv hGc hs.weak_gradient (planeFrameCoord a)
      (planeFrameCoord_smooth a) m n ψ hψ.1 hψ.2.1 hψ.2.2).2
  have I4 : ∀ ψ, IsHalfPlaneTest ψ → ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a 0 p =
      -∫ p, (ψ p : ℂ) * modeThird m n H a 0 2 p := by
    intro ψ hψ
    simp only [hth, hgm]
    exact weak_identity_const_mul _ (cylModeWeak (Space →L[ℝ] Space) G H hG hHc hweakG
      (planeRadialColumnCoord a) (planeRadialColumnCoord_smooth a) m n ψ hψ.1 hψ.2.1 hψ.2.2).2
  intro ψ hψ hc hpos
  have ht : IsHalfPlaneTest ψ := ⟨hψ, hc, hpos⟩
  exact ⟨I1 ψ ht, I2 ψ ht, weak_mixed_of_three I1 I2 I4 ψ ht, I4 ψ ht⟩

theorem localModeRadialWeak : LocalModeRadialWeakStatement := by
  intro K hK m v G H hs n a
  have hG2 : MemLp G 2 volume :=
    ModeRadialWeakInternal.grad_memLp hs.measurable_gradient hs.gradient_two
  have hGl : LocallyIntegrable G volume := hG2.locallyIntegrable (by norm_num)
  have hF := ModeRadialWeakInternal.vel_on (m := m) hs.velocity_six n a
  have hg := ModeRadialWeakInternal.grad_on (m := m) hGl n a
  have hW : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
        -∫ p, (ψ p : ℂ) * gradMode m n G a 0 p :=
    fun ψ h1 h2 h3 => (localModeWeakIdentity m v G H hs n a ψ h1 h2 h3).1
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  have h12 : K.r₁ < K.r₂ := hK.r_order.2
  have hz0 : 0 ≤ K.z₁ := hK.z_order.1
  have hsub : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp =>
    ⟨⟨h0.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hp.2.1, hp.2.2], hp.2.2⟩⟩
  have hFr : IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect :=
    IntegrableOn.mono_set (hF K.r₂ K.z₂) hsub
  have hgr := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a 0
  refine ⟨hFr, hgr, ?_⟩
  intro ψ hψ hψ1 hψ2 t ht
  have hgm : AEStronglyMeasurable (fun p : ℝ × ℝ => gradMode m n G a 0 p) (volume.restrict K.rect) :=
    (ModeRadialWeakInternal.grad_meas hs.measurable_gradient n a K.r₂ K.z₂).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  have hwpos : ∀ r, 0 < r → 0 < K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith
  have hwn : ∀ r ∈ Icc K.r₁ K.r₂, 0 ≤ K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs <;> linarith [hr.1]
  have hwl : ∀ r ∈ Icc K.r₁ K.r₂, r - K.r₁ ≤ (1 + (K.r₂ - K.r₁)) * K.lineWeight r := by
    intro r hr
    simp only [CellBox.lineWeight]
    split_ifs with h
    · rw [h, sub_zero]
      have : 0 ≤ r := h0.trans hr.1
      nlinarith
    · linarith [hr.2]
  exact ModeRadialWeakInternal.rect_psi hF hg hW h0 h12 (LowEntry.Internal.lineWeight_cont K) hwpos hwn hwl
    hFr hgr hgm hψ hψ1 hψ2 ht

theorem localHeightModeIbp : LocalHeightModeIbpStatement := by
  intro m n v G H hs K hK a
  have hA := LowEntry.Internal.modeVec_int K hK m n hs.velocity_six a
  have hB := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two a 2
  refine ⟨hB, fun f h hf hh h1 h2 => ?_⟩
  obtain ⟨φ, hφs, hφsupp, ⟨Cφ, hCφ⟩, hφlim⟩ :=
    FracInternal.HeightModeIbp.approx_cont K.r₁ K.r₂ hK.r_order.2 f hf.continuousOn
  obtain ⟨β, hβs, hβ0, hβd0, hβdc, ⟨Cβ, hCβ⟩, hβlim⟩ :=
    FracInternal.HeightModeIbp.approx_c1 K.z₁ K.z₂ hK.z_order.2 h hh h1 h2
  have hCφ0 : 0 ≤ Cφ := le_trans (abs_nonneg _) (hCφ 0 0)
  have hCβ0 : 0 ≤ Cβ := le_trans (abs_nonneg _) (hCβ 0 0).1
  have hw : ContDiff ℝ ∞ K.lineWeight := by
    by_cases h0 : K.r₁ = 0
    · have e : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, h0]
      rw [e]; exact contDiff_id
    · have e : K.lineWeight = fun _ => 1 := funext fun r => by simp [CellBox.lineWeight, h0]
      rw [e]; exact contDiff_const
  have key : ∀ k, ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ) =
      -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((φ k p.1 * β k p.2 : ℝ) : ℂ) := by
    intro k
    set ψ : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * φ k p.1 * β k p.2 with hψ
    have hψs : ContDiff ℝ ∞ ψ :=
      ((hw.comp contDiff_fst).mul ((hφs k).comp contDiff_fst)).mul ((hβs k).comp contDiff_snd)
    obtain ⟨e, he, hφe⟩ := hφsupp k
    have hφoff : ∀ r, r ∉ Icc K.r₁ K.r₂ → φ k r = 0 :=
      fun r hr => hφe r (fun h' => hr ⟨by linarith [h'.1], by linarith [h'.2]⟩)
    have hψoff : ∀ p, p ∉ K.rect → ψ p = 0 := by
      intro p hp
      simp only [CellBox.rect, mem_prod, not_and_or] at hp
      rcases hp with hp | hp
      · simp [hψ, hφoff p.1 hp]
      · simp [hψ, hβ0 k p.2 hp]
    have hψc : HasCompactSupport ψ := HasCompactSupport.intro (isCompact_Icc.prod isCompact_Icc) hψoff
    have hψpos : ∀ p ∈ tsupport ψ, 0 < p.1 := by
      intro p hp
      have hsub : tsupport ψ ⊆ {q : ℝ × ℝ | K.r₁ + e ≤ q.1} := by
        refine closure_minimal (fun q hq => ?_) (isClosed_le continuous_const continuous_fst)
        by_contra hc
        apply hq
        simp only [mem_ofPred_eq, not_le] at hc
        simp [hψ, hφe q.1 (fun h' => by linarith [h'.1])]
      have := hsub hp
      simp only [mem_ofPred_eq] at this
      linarith [hK.r_order.1]
    have hder : ∀ p, fderiv ℝ ψ p (0, 1) = K.lineWeight p.1 * φ k p.1 * deriv (β k) p.2 := by
      intro p
      have hl : HasDerivAt (fun z : ℝ => (p.1, z)) ((0 : ℝ), (1 : ℝ)) p.2 :=
        (hasDerivAt_const _ _).prodMk (hasDerivAt_id _)
      have h1 := ((hψs.differentiable (by simp)) (p.1, p.2)).hasFDerivAt.comp_hasDerivAt p.2 hl
      have h2 : HasDerivAt (fun z => ψ (p.1, z)) (K.lineWeight p.1 * φ k p.1 * deriv (β k) p.2) p.2 := by
        have h4 := (((hβs k).differentiable (by simp)) p.2).hasDerivAt.const_mul (K.lineWeight p.1 * φ k p.1)
        simpa only [hψ] using h4
      have h3 := h1.unique h2
      rw [Prod.mk.eta] at h3
      exact h3
    have hid := (localModeWeakIdentity m v G H hs n a ψ hψs hψc hψpos).2.1
    have eL : ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a =
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
          ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1; funext p; rw [hder]; push_cast; ring
      · intro p hp
        simp only [CellBox.rect, mem_prod, not_and_or] at hp
        rcases hp with hp | hp
        · simp [hφoff p.1 hp]
        · simp [hβd0 k p.2 (fun h' => hp (Ioo_subset_Icc_self h'))]
    have eR : ∫ p, (ψ p : ℂ) * gradMode m n G a 2 p =
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((φ k p.1 * β k p.2 : ℝ) : ℂ) := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
      · congr 1; funext p; simp only [hψ]; push_cast; ring
      · intro p hp
        simp only [CellBox.rect, mem_prod, not_and_or] at hp
        rcases hp with hp | hp
        · simp [hφoff p.1 hp]
        · simp [hβ0 k p.2 hp]
    rw [eL, eR] at hid
    exact hid
  have hint : ∀ᵐ p ∂(volume.restrict K.rect), p.1 ∈ Ioo K.r₁ K.r₂ ∧ p.2 ∈ Ioo K.z₁ K.z₂ := by
    filter_upwards [ae_restrict_mem (LowEntry.Internal.rect_meas K),
      ae_restrict_of_ae (FracInternal.HeightModeIbp.line_fst K.r₁),
      ae_restrict_of_ae (FracInternal.HeightModeIbp.line_fst K.r₂),
      ae_restrict_of_ae (FracInternal.HeightModeIbp.line_snd K.z₁),
      ae_restrict_of_ae (FracInternal.HeightModeIbp.line_snd K.z₂)]
      with p hp hr1 hr2 hz1 hz2
    exact ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm hr1), lt_of_le_of_ne hp.1.2 hr2⟩,
      ⟨lt_of_le_of_ne hp.2.1 (Ne.symm hz1), lt_of_le_of_ne hp.2.2 hz2⟩⟩
  have hlimL : Tendsto (fun k => ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((φ k p.1 * deriv (β k) p.2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
        ((f p.1 * deriv h p.2 : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖(K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a‖ * (Cφ * Cβ)) (fun k => ?_)
      (hA.norm.mul_const _) (fun k => ?_) ?_
    · exact hA.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((hφs k).continuous.comp continuous_fst).mul ((hβdc k).comp continuous_snd))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hCφ k p.1) (hCβ k p.2).2 (abs_nonneg _) hCφ0) (norm_nonneg _)
    · filter_upwards [hint] with p hp
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
        ((hφlim p.1 hp.1).mul (hβlim p.2 hp.2).2))
  have hlimR : Tendsto (fun k => ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p *
      ((φ k p.1 * β k p.2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((f p.1 * h p.2 : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun p => ‖(K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p‖ * (Cφ * Cβ)) (fun k => ?_)
      (hB.norm.mul_const _) (fun k => ?_) ?_
    · exact hB.aestronglyMeasurable.mul (Complex.continuous_ofReal.comp
        (((hφs k).continuous.comp continuous_fst).mul ((hβs k).continuous.comp continuous_snd))).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hCφ k p.1) (hCβ k p.2).1 (abs_nonneg _) hCφ0) (norm_nonneg _)
    · filter_upwards [hint] with p hp
      exact tendsto_const_nhds.mul ((Complex.continuous_ofReal.tendsto _).comp
        ((hφlim p.1 hp.1).mul (hβlim p.2 hp.2).1))
  exact tendsto_nhds_unique hlimL (hlimR.neg.congr (fun k => (key k).symm))

end LocalField

end CertCell

end Breakdown

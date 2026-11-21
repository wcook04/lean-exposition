import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineDeriv
import Breakdown.FracCell.GivenProfilePowerFieldJumpsPieces

open scoped ContDiff Topology
open Set Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline heightRatio radialVec polarVecQ azimVecQ weightPoly radialScale heightDeriv)

private def OffSlope {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Space → F) : Prop :=
  ContDiffOn ℝ 1 f {0}ᶜ ∧ LocallyLipschitzOn {0}ᶜ (fderiv ℝ f)

private theorem off_nhds {y : Space} (hy : y ∈ ({0}ᶜ : Set Space)) : ({0}ᶜ : Set Space) ∈ 𝓝 y :=
  isOpen_compl_singleton.mem_nhds hy

private theorem off_eq : ({0}ᶜ : Set Space) = {y | y ≠ 0} := by
  ext y
  simp

private theorem locSlopeBound_of_c1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space → F}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) : LocallyLipschitzOn {0}ᶜ f := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (off_nhds hy)).exists_lipschitzOnWith
  exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩

private theorem offSlope_of_two {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space → F}
    (hf : ContDiffOn ℝ 2 f {0}ᶜ) : OffSlope f := by
  refine ⟨hf.of_le (by norm_num), ?_⟩
  intro y hy
  have h2 : ContDiffAt ℝ 2 f y := hf.contDiffAt (off_nhds hy)
  obtain ⟨K, t, ht, hK⟩ := (h2.fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  exact ⟨K, t, nhdsWithin_le_nhds ht, hK⟩

private theorem locSlopeBound_congr {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g h : Space → F}
    (hg : LocallyLipschitzOn {0}ᶜ g) (he : ∀ y ∈ ({0}ᶜ : Set Space), g y = h y) :
    LocallyLipschitzOn {0}ᶜ h := by
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := hg hy
  refine ⟨K, t ∩ {0}ᶜ, inter_mem ht self_mem_nhdsWithin, ?_⟩
  intro a ha b hb
  rw [← he a ha.2, ← he b hb.2]
  exact hK ha.1 hb.1

private theorem norm_le_near {E : Type*} [NormedAddCommGroup E] {u : Space → E} {K : NNReal} {t : Set Space}
    {y z : Space} (hK : LipschitzOnWith K u t) (hy : y ∈ t) (hz : z ∈ t) (hzy : dist z y ≤ 1) :
    ‖u z‖ ≤ ‖u y‖ + K := by
  have h1 : dist (u z) (u y) ≤ K * dist z y := hK.dist_le_mul z hz y hy
  have h2 : (K : ℝ) * dist z y ≤ K := mul_le_of_le_one_right K.2 hzy
  have h3 := norm_le_insert' (u z) (u y)
  rw [dist_eq_norm] at h1
  linarith

private theorem locSlopeBound_bilin {E₁ E₂ G : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E₁ →L[ℝ] E₂ →L[ℝ] G) {u : Space → E₁} {v : Space → E₂}
    (hu : LocallyLipschitzOn {0}ᶜ u) (hv : LocallyLipschitzOn {0}ᶜ v) :
    LocallyLipschitzOn {0}ᶜ (fun z => B (u z) (v z)) := by
  intro y hy
  obtain ⟨Ku, t, ht, hKu⟩ := hu hy
  obtain ⟨Kv, s, hs, hKv⟩ := hv hy
  have hyt : y ∈ t := mem_of_mem_nhdsWithin hy ht
  have hys : y ∈ s := mem_of_mem_nhdsWithin hy hs
  have hW : t ∩ s ∩ Metric.closedBall y 1 ∈ 𝓝[{0}ᶜ] y :=
    inter_mem (inter_mem ht hs) (nhdsWithin_le_nhds (Metric.closedBall_mem_nhds y one_pos))
  have hMu : 0 ≤ ‖u y‖ + Ku := by positivity
  have hMv : 0 ≤ ‖v y‖ + Kv := by positivity
  have hc : 0 ≤ ‖B‖ * (Ku * (‖v y‖ + Kv) + (‖u y‖ + Ku) * Kv) := by positivity
  refine ⟨Real.toNNReal (‖B‖ * (Ku * (‖v y‖ + Kv) + (‖u y‖ + Ku) * Kv)), _, hW,
    LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_⟩
  rw [Real.coe_toNNReal _ hc]
  have hua : dist (u a) (u b) ≤ Ku * dist a b := hKu.dist_le_mul a ha.1.1 b hb.1.1
  have hvb : dist (v a) (v b) ≤ Kv * dist a b := hKv.dist_le_mul a ha.1.2 b hb.1.2
  have hva : ‖v a‖ ≤ ‖v y‖ + Kv := norm_le_near hKv hys ha.1.2 ha.2
  have hub : ‖u b‖ ≤ ‖u y‖ + Ku := norm_le_near hKu hyt hb.1.1 hb.2
  rw [dist_eq_norm] at hua hvb
  rw [dist_eq_norm]
  have key : B (u a) (v a) - B (u b) (v b) = B (u a - u b) (v a) + B (u b) (v a - v b) := by
    simp only [map_sub, sub_apply]
    abel
  rw [key]
  have hd : 0 ≤ dist a b := dist_nonneg
  calc ‖B (u a - u b) (v a) + B (u b) (v a - v b)‖
      ≤ ‖B (u a - u b) (v a)‖ + ‖B (u b) (v a - v b)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u a - u b‖ * ‖v a‖ + ‖B‖ * ‖u b‖ * ‖v a - v b‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * (Ku * dist a b) * (‖v y‖ + Kv) + ‖B‖ * (‖u y‖ + Ku) * (Kv * dist a b) := by
        gcongr
    _ = ‖B‖ * (Ku * (‖v y‖ + Kv) + (‖u y‖ + Ku) * Kv) * dist a b := by ring

private theorem diff_of_c1 {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Space → F}
    (hf : ContDiffOn ℝ 1 f {0}ᶜ) {y : Space} (hy : y ∈ ({0}ᶜ : Set Space)) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (off_nhds hy)).differentiableAt (by norm_num)

private theorem OffSlope.bilin {E₁ E₂ G : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E₁ →L[ℝ] E₂ →L[ℝ] G) {f : Space → E₁} {g : Space → E₂} (hf : OffSlope f) (hg : OffSlope g) :
    OffSlope (fun y => B (f y) (g y)) := by
  refine ⟨(B.contDiff.comp_contDiffOn hf.1).clm_apply hg.1, ?_⟩
  apply locSlopeBound_congr (g := fun y => B.precompR Space (f y) (fderiv ℝ g y) + B.precompL Space (fderiv ℝ f y) (g y))
  · exact (locSlopeBound_bilin _ (locSlopeBound_of_c1 hf.1) hg.2).add (locSlopeBound_bilin _ hf.2 (locSlopeBound_of_c1 hg.1))
  · intro y hy
    exact (B.fderiv_of_bilinear (diff_of_c1 hf.1 hy) (diff_of_c1 hg.1 hy)).symm

private theorem OffSlope.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Space → F}
    (hf : OffSlope f) (hg : OffSlope g) : OffSlope (fun y => f y + g y) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  apply locSlopeBound_congr (g := fun y => fderiv ℝ f y + fderiv ℝ g y) (hf.2.add hg.2)
  intro y hy
  exact (fderiv_add (diff_of_c1 hf.1 hy) (diff_of_c1 hg.1 hy)).symm

private theorem OffSlope.sub {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f g : Space → F}
    (hf : OffSlope f) (hg : OffSlope g) : OffSlope (fun y => f y - g y) := by
  refine ⟨hf.1.sub hg.1, ?_⟩
  apply locSlopeBound_congr (g := fun y => fderiv ℝ f y - fderiv ℝ g y) (hf.2.sub hg.2)
  intro y hy
  exact (fderiv_sub (diff_of_c1 hf.1 hy) (diff_of_c1 hg.1 hy)).symm

private theorem OffSlope.mul {f g : Space → ℂ} (hf : OffSlope f) (hg : OffSlope g) :
    OffSlope (fun y => f y * g y) := by
  simpa using OffSlope.bilin (ContinuousLinearMap.mul ℝ ℂ) hf hg

private theorem OffSlope.smul {f : Space → ℂ} {g : Space → Fin 3 → ℂ} (hf : OffSlope f) (hg : OffSlope g) :
    OffSlope (fun y => f y • g y) := by
  simpa using OffSlope.bilin (ContinuousLinearMap.lsmul ℝ ℂ) hf hg

private theorem OffSlope.const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (c : F) :
    OffSlope (fun _ : Space => c) :=
  offSlope_of_two contDiffOn_const

private theorem OffSlope.plane {R : ℝ × ℝ → ℂ} (hR : ContDiff ℝ 1 R)
    (hL : ∀ r : ℝ, ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ R) (Metric.closedBall 0 r))
    {χ : Space → ℝ × ℝ} (hχ : ContDiffOn ℝ 2 χ {0}ᶜ) : OffSlope (fun y => R (χ y)) := by
  have hχ1 : ContDiffOn ℝ 1 χ {0}ᶜ := hχ.of_le (by norm_num)
  refine ⟨hR.comp_contDiffOn hχ1, ?_⟩
  have hu : LocallyLipschitzOn {0}ᶜ (fun y => fderiv ℝ R (χ y)) := by
    intro y hy
    obtain ⟨L, hL'⟩ := hL (‖χ y‖ + 1)
    have hc : ContinuousAt χ y := (hχ1.contDiffAt (off_nhds hy)).continuousAt
    obtain ⟨K, t, ht, hK⟩ := locSlopeBound_of_c1 hχ1 hy
    refine ⟨L * K, t ∩ χ ⁻¹' Metric.ball (χ y) 1,
      inter_mem ht (nhdsWithin_le_nhds (hc.preimage_mem_nhds (Metric.ball_mem_nhds _ one_pos))), ?_⟩
    refine hL'.comp (hK.mono inter_subset_left) ?_
    intro z hz
    have h1 : dist (χ z) (χ y) < 1 := hz.2
    rw [Metric.mem_closedBall, dist_zero_right]
    have h2 := norm_le_insert' (χ z) (χ y)
    rw [dist_eq_norm] at h1
    linarith
  apply locSlopeBound_congr (g := fun y => (ContinuousLinearMap.compL ℝ Space (ℝ × ℝ) ℂ) (fderiv ℝ R (χ y))
    (fderiv ℝ χ y)) (locSlopeBound_bilin _ hu (offSlope_of_two hχ).2)
  intro y hy
  have := fderiv_comp (x := y) ((hR.differentiable one_ne_zero) (χ y)) (diff_of_c1 hχ1 hy)
  rw [show (fun y => R (χ y)) = R ∘ χ from rfl, this, ContinuousLinearMap.compL_apply]


private theorem ofReal_off {g : Space → ℝ} (hg : ContDiffOn ℝ 2 g {0}ᶜ) : OffSlope (fun y => (g y : ℂ)) :=
  offSlope_of_two (Complex.ofRealCLM.contDiff.comp_contDiffOn hg)

private theorem chartCoord_two (P : ShapeParams) (hP : 0 < P.chartLength) :
    ContDiffOn ℝ 2 (chartCoord P) {0}ᶜ := by
  intro y hy
  have hy0 : y ≠ 0 := hy
  have hn : ContDiffAt ℝ 2 (fun y : Space => ‖y‖) y := contDiffAt_norm ℝ hy0
  have hd : 0 < ‖y‖ + P.chartLength := by have := norm_nonneg y; linarith
  exact (hn.div (hn.add contDiffAt_const) hd.ne').contDiffWithinAt

private theorem heightRatio_two : ContDiffOn ℝ 2 heightRatio {0}ᶜ := by
  rw [off_eq]
  exact FracInternal.ProfilePowerJumpsPieces.heightRatio_contDiffOn.of_le (by norm_num)

private theorem frame_off {v : Space → Fin 3 → ℝ} (hv : ∀ i, ContDiffOn ℝ 3 (fun y => v y i) {y | y ≠ 0}) :
    OffSlope (fun y => fun i => ((v y i : ℝ) : ℂ)) := by
  apply offSlope_of_two
  rw [off_eq]
  exact contDiffOn_pi.2 fun i => Complex.ofRealCLM.contDiff.comp_contDiffOn ((hv i).of_le (by norm_num))

private theorem phase_off (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) :
    OffSlope (fun y : Space => Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have h1 : ContDiffOn ℝ 2 (fun y : Space => P.radialPhase (‖y‖ ^ 2)) {0}ᶜ :=
    (hf.of_le (by norm_num)).comp (contDiff_norm_sq ℝ).contDiffOn
      (fun y _ => by simp only [mem_Ioi]; nlinarith [sq_nonneg ‖y‖])
  apply offSlope_of_two
  exact Complex.contDiff_exp.comp_contDiffOn
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.mul h1)).mul contDiffOn_const)

private theorem chartRadius_chartCoord (P : ShapeParams) (hP : 0 < P.chartLength) (y : Space) :
    chartRadius P (chartCoord P y) = ‖y‖ := by
  have hn := norm_nonneg y
  have hd : 0 < ‖y‖ + P.chartLength := by linarith
  unfold chartRadius chartCoord
  have h1 : 1 - ‖y‖ / (‖y‖ + P.chartLength) = P.chartLength / (‖y‖ + P.chartLength) := by
    field_simp
    ring
  rw [h1]
  field_simp

private theorem phaseSlope_chartCoord (P : ShapeParams) (hP : 0 < P.chartLength) (y : Space) :
    phaseSlope P (chartCoord P y) = 2 * ‖y‖ ^ 2 * deriv P.radialPhase (‖y‖ ^ 2) := by
  unfold phaseSlope
  rw [chartRadius_chartCoord P hP y]

private theorem slope_off (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) :
    OffSlope (fun y : Space => ((((j : ℝ) * phaseSlope P (chartCoord P y)) : ℝ) : ℂ)) := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hd : ContDiffOn ℝ 2 (deriv P.radialPhase) (Ioi (-δ)) := hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h1 : ContDiffOn ℝ 2 (fun y : Space => deriv P.radialPhase (‖y‖ ^ 2)) {0}ᶜ :=
    hd.comp (contDiff_norm_sq ℝ).contDiffOn (fun y _ => by simp only [mem_Ioi]; nlinarith [sq_nonneg ‖y‖])
  have h2 : ContDiffOn ℝ 2 (fun y : Space => (j : ℝ) * (2 * ‖y‖ ^ 2 * deriv P.radialPhase (‖y‖ ^ 2))) {0}ᶜ :=
    contDiffOn_const.mul ((contDiffOn_const.mul (contDiff_norm_sq ℝ).contDiffOn).mul h1)
  have he : (fun y : Space => ((((j : ℝ) * phaseSlope P (chartCoord P y)) : ℝ) : ℂ)) =
      fun y => (((j : ℝ) * (2 * ‖y‖ ^ 2 * deriv P.radialPhase (‖y‖ ^ 2)) : ℝ) : ℂ) := by
    funext y
    rw [phaseSlope_chartCoord P hP.chartLength_pos y]
  rw [he]
  exact ofReal_off h2

private theorem weight_smooth (e0 e1 : ℕ) : ContDiff ℝ ∞ (weightPoly e0 e1) := by
  have h : ContDiff ℝ ∞ (fun t : ℝ => (((t ^ e0 * (1 - t) ^ e1 : ℝ)) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow e0).mul ((contDiff_const.sub contDiff_id).pow e1))
  exact h

private theorem weight_off (P : ShapeParams) (hP : 0 < P.chartLength) (e0 e1 : ℕ) :
    OffSlope (fun y : Space => weightPoly e0 e1 (chartCoord P y)) :=
  offSlope_of_two ((contDiff_infty.1 (weight_smooth e0 e1) 2).comp_contDiffOn (chartCoord_two P hP))

private theorem dweight_off (P : ShapeParams) (hP : 0 < P.chartLength) (e0 e1 : ℕ) :
    OffSlope (fun y : Space => deriv (weightPoly e0 e1) (chartCoord P y)) := by
  have h : ContDiff ℝ ∞ (deriv^[1] (weightPoly e0 e1)) := ContDiff.iterate_deriv 1 (weight_smooth e0 e1)
  simp only [Function.iterate_one] at h
  exact offSlope_of_two ((contDiff_infty.1 h 2).comp_contDiffOn (chartCoord_two P hP))

private theorem spline_off (S : Spline) {a b : ℕ} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b)
    {T X : Space → ℝ} (hT : ContDiffOn ℝ 2 T {0}ᶜ) (hX : ContDiffOn ℝ 2 X {0}ᶜ) :
    OffSlope (fun y => S.evalHalf (T y) (X y)) :=
  OffSlope.plane (R := fun z => S.evalHalf z.1 z.2)
    ((joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb)))
    (joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth a b S hS ha hb) (χ := fun y => (T y, X y)) (hT.prodMk hX)

private theorem slice_t {S : Spline} {a b : ℕ} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun t' => S.evalHalf t' x) ((tDerivSpline S).evalHalf t x) t := by
  have hC : ContDiff ℝ 1 (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) :=
    (joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))
  set F : ℝ × ℝ → ℂ := fun z => S.evalHalf z.1 z.2 with hF
  have hdF : Differentiable ℝ F := hC.differentiable one_ne_zero
  have h1 := (hdF (t, x)).hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))
  have h2 : DifferentiableAt ℝ (fun t' => S.evalHalf t' x) t := h1.differentiableAt
  rw [← ((splineDerivatives_holds a b S hS).1 ha).2 t x]
  exact h2.hasDerivAt

private theorem slice_x {S : Spline} {a b : ℕ} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (t x : ℝ) :
    HasDerivAt (fun x' => S.evalHalf t x') ((xDerivSpline S).evalHalf t x) x := by
  have hC : ContDiff ℝ 1 (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) :=
    (joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))
  set F : ℝ × ℝ → ℂ := fun z => S.evalHalf z.1 z.2 with hF
  have hdF : Differentiable ℝ F := hC.differentiable one_ne_zero
  have h1 := (hdF (t, x)).hasFDerivAt.comp_hasDerivAt x ((hasDerivAt_const x t).prodMk (hasDerivAt_id x))
  have h2 : DifferentiableAt ℝ (fun x' => S.evalHalf t x') x := h1.differentiableAt
  rw [← ((splineDerivatives_holds a b S hS).2 hb).2 t x]
  exact h2.hasDerivAt

private theorem radialComp_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (hκ1 : κ.label.1 ≠ 0) (t x : ℝ) :
    reducedComps P κ A t x 0 = axisFactor x * (weightPoly A.lowOrder A.highOrder t * A.radial.evalHalf t x) := by
  simp only [reducedComps, if_neg hκ1, Matrix.cons_val_zero]
  ring

private theorem polarComp_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (hκ1 : κ.label.1 ≠ 0) (t x : ℝ) :
    reducedComps P κ A t x 1 = axisFactor x * (weightPoly A.lowOrder A.highOrder t * A.polar.evalHalf t x) := by
  simp only [reducedComps, if_neg hκ1, Matrix.cons_val_one, Matrix.cons_val_zero]
  ring

private theorem azimComp_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (hκ1 : κ.label.1 ≠ 0)
    (hA : IsJoinedSpline 2 1 A.radial) (hB : IsJoinedSpline 1 2 A.polar) (t x : ℝ) :
    reducedComps P κ A t x 2 = axisFactor x * ((Complex.I / (labelAzimuth P.azimuthOrder κ.label : ℂ)) *
      (((t * (1 - t) : ℝ) : ℂ) * (deriv (weightPoly A.lowOrder A.highOrder) t * A.radial.evalHalf t x +
          weightPoly A.lowOrder A.highOrder t * (tDerivSpline A.radial).evalHalf t x) +
        Complex.I * (((κ.phaseIndex : ℝ) * phaseSlope P t : ℝ) : ℂ) *
          (weightPoly A.lowOrder A.highOrder t * A.radial.evalHalf t x) +
        2 * (weightPoly A.lowOrder A.highOrder t * A.radial.evalHalf t x) -
        weightPoly A.lowOrder A.highOrder t * (((-6 * x : ℝ) : ℂ) * A.polar.evalHalf t x +
          polarFactor x * (xDerivSpline A.polar).evalHalf t x))) := by
  have hw : HasDerivAt (weightPoly A.lowOrder A.highOrder) (deriv (weightPoly A.lowOrder A.highOrder) t) t :=
    ((weight_smooth A.lowOrder A.highOrder).differentiable (by norm_num) t).hasDerivAt
  have e1 : deriv (fun t' => weightPoly A.lowOrder A.highOrder t' * (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) *
      A.radial.evalHalf t' x) t =
      deriv (weightPoly A.lowOrder A.highOrder) t * (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) * A.radial.evalHalf t x +
        weightPoly A.lowOrder A.highOrder t * (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) *
          (tDerivSpline A.radial).evalHalf t x :=
    ((hw.mul_const _).mul (slice_t hA (by norm_num) (by norm_num) t x)).deriv
  have hp : HasDerivAt (fun x' : ℝ => ((1 - x' ^ 2 : ℝ) : ℂ)) (((-2 * x : ℝ)) : ℂ) x := by
    have h := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
    convert h using 2
    norm_num
  have ha : HasDerivAt (fun x' : ℝ => (((1 - x' ^ 2) ^ 2 : ℝ) : ℂ)) (((-4 * x * (1 - x ^ 2)) : ℝ) : ℂ) x := by
    have h := (((hasDerivAt_pow 2 x).const_sub 1).pow 2).ofReal_comp
    convert h using 2
    norm_num
    ring
  have e2 : deriv (fun x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly A.lowOrder A.highOrder t *
      (((1 - x' ^ 2) ^ 2 : ℝ) : ℂ) * A.polar.evalHalf t x')) x =
      (((-2 * x : ℝ)) : ℂ) * (weightPoly A.lowOrder A.highOrder t * (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) *
        A.polar.evalHalf t x) + ((1 - x ^ 2 : ℝ) : ℂ) *
        (weightPoly A.lowOrder A.highOrder t * (((-4 * x * (1 - x ^ 2)) : ℝ) : ℂ) * A.polar.evalHalf t x +
          weightPoly A.lowOrder A.highOrder t * (((1 - x ^ 2) ^ 2 : ℝ) : ℂ) * (xDerivSpline A.polar).evalHalf t x) :=
    (hp.mul ((ha.const_mul _).mul (slice_x hB (by norm_num) (by norm_num) t x))).deriv
  simp only [reducedComps, if_neg hκ1, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    shiftedScale, radialScale, heightDeriv, polarFactor, axisFactor]
  rw [e1, e2]
  push_cast
  ring

private theorem keyPhase_split (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) :
    keyPhase P κ σ y = Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
      (Complex.exp ((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * pointAngle y : ℝ) * Complex.I) *
      Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) := by
  rw [keyPhase, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring


private theorem keyVector_offSlope
    (hang : ∀ k : ℤ, ContDiffOn ℝ 3 (fun y : Space => axisFactor (heightRatio y) *
      Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ)
    (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (hκ1 : κ.label.1 ≠ 0)
    (hA : IsJoinedSpline 2 1 A.radial) (hB : IsJoinedSpline 1 2 A.polar) :
    OffSlope (keyVector P κ A σ) := by
  have hT := chartCoord_two P hP.chartLength_pos
  have hX := heightRatio_two
  have sA := spline_off A.radial hA (by norm_num) (by norm_num) hT hX
  have sAt := spline_off (tDerivSpline A.radial) ((splineDerivatives_holds 2 1 _ hA).1 (by norm_num)).1
    (by norm_num) (by norm_num) hT hX
  have sB := spline_off A.polar hB (by norm_num) (by norm_num) hT hX
  have sBx := spline_off (xDerivSpline A.polar) ((splineDerivatives_holds 1 2 _ hB).2 (by norm_num)).1
    (by norm_num) (by norm_num) hT hX
  have w := weight_off P hP.chartLength_pos A.lowOrder A.highOrder
  have dw := dweight_off P hP.chartLength_pos A.lowOrder A.highOrder
  have tt : OffSlope (fun y => (((chartCoord P y * (1 - chartCoord P y) : ℝ)) : ℂ)) :=
    ofReal_off (hT.mul (contDiffOn_const.sub hT))
  have ps := slope_off P hP κ.phaseIndex
  have sx : OffSlope (fun y => (((-6 * heightRatio y : ℝ)) : ℂ)) := ofReal_off (contDiffOn_const.mul hX)
  have px : OffSlope (fun y => polarFactor (heightRatio y)) := ofReal_off (contDiffOn_const.sub (hX.pow 2))
  have G2 := (OffSlope.const (Complex.I / (labelAzimuth P.azimuthOrder κ.label : ℂ))).mul
    ((((tt.mul ((dw.mul sA).add (w.mul sAt))).add (((OffSlope.const Complex.I).mul ps).mul (w.mul sA))).add
      ((OffSlope.const (2 : ℂ)).mul (w.mul sA))).sub (w.mul ((sx.mul sB).add (px.mul sBx))))
  have AF := offSlope_of_two ((hang (labelAzimuth P.azimuthOrder κ.label)).of_le (by norm_num))
  have PH := phase_off P hP κ.phaseIndex
  have C0 := OffSlope.const (Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I))
  have F0 := frame_off FracInternal.ProfilePowerJumpsPieces.radialVec_contDiffOn
  have F1 := frame_off FracInternal.ProfilePowerJumpsPieces.polarVecQ_contDiffOn
  have F2 := frame_off FracInternal.ProfilePowerJumpsPieces.azimVecQ_contDiffOn
  have hsum := (((C0.mul (AF.mul (PH.mul (w.mul sA)))).smul F0).add
    ((C0.mul (AF.mul (PH.mul (w.mul sB)))).smul F1)).add ((C0.mul (AF.mul (PH.mul G2))).smul F2)
  convert hsum using 1
  funext y i
  simp only [keyVector, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [keyPhase_split, radialComp_eq P κ A hκ1, polarComp_eq P κ A hκ1, azimComp_eq P κ A hκ1 hA hB]
  ring

theorem typeOneKey_contDiffOn_off_of
    (hang : ∀ k : ℤ, ContDiffOn ℝ 3 (fun y : Space => axisFactor (heightRatio y) *
      Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ)
    (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (hκ1 : κ.label.1 ≠ 0) :
    ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) {0}ᶜ :=
  (keyVector_offSlope hang P hP κ (D.amp κ) σ hκ1 (hD.radial_class κ hκ hκ1) (hD.polar_class κ hκ hκ1)).1

theorem typeOneKey_slope_off_of
    (hang : ∀ k : ℤ, ContDiffOn ℝ 3 (fun y : Space => axisFactor (heightRatio y) *
      Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ)
    (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (hκ1 : κ.label.1 ≠ 0) :
    ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) K := fun _ hK hK0 =>
  ((keyVector_offSlope hang P hP κ (D.amp κ) σ hκ1 (hD.radial_class κ hκ hκ1)
    (hD.polar_class κ hκ hκ1)).2.mono hK0).exists_lipschitzOnWith_of_compact hK

theorem typeOneKey_slope_annulus_of
    (hang : ∀ k : ℤ, ContDiffOn ℝ 3 (fun y : Space => axisFactor (heightRatio y) *
      Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ)
    (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (hP : IsShapeParams P)
    (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys) (hκ1 : κ.label.1 ≠ 0) (ε R : ℝ) (hε : 0 < ε) :
    ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
  apply typeOneKey_slope_off_of hang P D κ σ hP hD hκ hκ1
  · have hc : IsCompact (Metric.closedBall (0 : Space) R ∩ {y : Space | ε ≤ ‖y‖}) :=
      (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const continuous_norm)
    convert hc using 1
    ext y
    simp only [mem_ofPred_eq, mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    tauto
  · intro y hy h0
    rw [mem_singleton_iff] at h0
    subst h0
    simp only [mem_ofPred_eq, norm_zero] at hy
    linarith [hy.1]


theorem typeOneKey_off_of
    (hang : ∀ k : ℤ, ContDiffOn ℝ 3 (fun y : Space => axisFactor (heightRatio y) *
      Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)) {0}ᶜ) :
    ∀ (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ), IsShapeParams P →
      IsTimeFieldData D → κ ∈ D.keys → κ.label.1 ≠ 0 →
        ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) {0}ᶜ ∧
        ∀ K : Set Space, IsCompact K → K ⊆ {0}ᶜ →
          ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) K :=
  fun P D κ σ hP hD hκ hκ1 => ⟨typeOneKey_contDiffOn_off_of hang P D κ σ hP hD hκ hκ1,
    typeOneKey_slope_off_of hang P D κ σ hP hD hκ hκ1⟩

end GivenShape

end CertCell

end Breakdown

import Breakdown.CertCell.ShapeAngularFactor
import Breakdown.CertCell.ShapeDecayNear
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeSplineDeriv

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline heightRatio radialVec polarVecQ azimVecQ weightPoly radialScale heightDeriv qOf)

namespace Internal.KeyDecay

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def SlopeBoundOn (f : Space → E) (K : ℝ) (s : Set Space) : Prop :=
  ∀ z ∈ s, ∀ w ∈ s, ‖f z - f w‖ ≤ K * ‖z - w‖

def BallData (f : Space → E) (y : Space) (v d l : ℝ) : Prop :=
  (∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ f z ∧ ‖f z‖ ≤ v ∧ ‖fderiv ℝ f z‖ ≤ d) ∧
    SlopeBoundOn (fderiv ℝ f) l (Metric.ball y 1)

def FarDecay (a : ℕ) (f : Space → E) : Prop :=
  ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ →
    BallData f y (C * ‖y‖⁻¹ ^ a) (C * ‖y‖⁻¹ ^ (a + 1)) (C * ‖y‖⁻¹ ^ (a + 2))

theorem slopeBoundOn_of_fderiv {f : Space → E} {y : Space} {r K : ℝ}
    (hd : ∀ z ∈ Metric.ball y r, DifferentiableAt ℝ f z) (hb : ∀ z ∈ Metric.ball y r, ‖fderiv ℝ f z‖ ≤ K) :
    SlopeBoundOn f K (Metric.ball y r) := fun z hz w hw =>
  (convex_ball y r).norm_image_sub_le_of_norm_fderiv_le hd hb hw hz

theorem slopeBoundOn_congr {f g : Space → E} {K : ℝ} {s : Set Space} (h : SlopeBoundOn g K s)
    (he : ∀ z ∈ s, f z = g z) : SlopeBoundOn f K s := fun z hz w hw => by
  rw [he z hz, he w hw]; exact h z hz w hw

theorem slopeBoundOn_mono {f : Space → E} {K K' : ℝ} {s : Set Space} (h : SlopeBoundOn f K s) (hK : K ≤ K') :
    SlopeBoundOn f K' s := fun z hz w hw => (h z hz w hw).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

theorem slopeBoundOn_add {f g : Space → E} {K1 K2 : ℝ} {s : Set Space} (hf : SlopeBoundOn f K1 s) (hg : SlopeBoundOn g K2 s) :
    SlopeBoundOn (fun z => f z + g z) (K1 + K2) s := fun z hz w hw => by
  have e : f z + g z - (f w + g w) = (f z - f w) + (g z - g w) := by abel
  rw [e]
  calc _ ≤ ‖f z - f w‖ + ‖g z - g w‖ := norm_add_le _ _
    _ ≤ K1 * ‖z - w‖ + K2 * ‖z - w‖ := add_le_add (hf z hz w hw) (hg z hz w hw)
    _ = (K1 + K2) * ‖z - w‖ := by ring

theorem norm_smulRight_le' {𝕜' F : Type*} [NormedField 𝕜'] [NormedAlgebra ℝ 𝕜'] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace 𝕜' F] [IsScalarTower ℝ 𝕜' F] (c : Space →L[ℝ] 𝕜') (v : F) :
    ‖c.smulRight v‖ ≤ ‖c‖ * ‖v‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun u => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖c u‖ * ‖v‖ ≤ ‖c‖ * ‖u‖ * ‖v‖ := mul_le_mul_of_nonneg_right (c.le_opNorm u) (norm_nonneg _)
    _ = ‖c‖ * ‖v‖ * ‖u‖ := by ring

theorem ballData_mono {f : Space → E} {y : Space} {v d l v' d' l' : ℝ} (h : BallData f y v d l)
    (hv : v ≤ v') (hd : d ≤ d') (hl : l ≤ l') : BallData f y v' d' l' :=
  ⟨fun z hz => ⟨(h.1 z hz).1, (h.1 z hz).2.1.trans hv, (h.1 z hz).2.2.trans hd⟩, slopeBoundOn_mono h.2 hl⟩

theorem ballData_add {f g : Space → E} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ}
    (hf : BallData f y v1 d1 l1) (hg : BallData g y v2 d2 l2) :
    BallData (fun z => f z + g z) y (v1 + v2) (d1 + d2) (l1 + l2) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => f z + g z) z = fderiv ℝ f z + fderiv ℝ g z :=
    fun z hz => ((hf.1 z hz).1.hasFDerivAt.add (hg.1 z hz).1.hasFDerivAt).fderiv
  refine ⟨fun z hz => ⟨(hf.1 z hz).1.add (hg.1 z hz).1, (norm_add_le _ _).trans
    (add_le_add (hf.1 z hz).2.1 (hg.1 z hz).2.1), ?_⟩, slopeBoundOn_congr (slopeBoundOn_add hf.2 hg.2) hD⟩
  rw [hD z hz]
  exact (norm_add_le _ _).trans (add_le_add (hf.1 z hz).2.2 (hg.1 z hz).2.2)

theorem ballData_const (c : E) (y : Space) : BallData (fun _ : Space => c) y ‖c‖ 0 0 := by
  refine ⟨fun z _ => ⟨differentiableAt_const _, le_rfl, by simp⟩, fun z _ w _ => by simp⟩

theorem ballData_prod {f g : Space → ℝ} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ}
    (hf : BallData f y v1 d1 l1) (hg : BallData g y v2 d2 l2) :
    BallData (fun z => (f z, g z)) y (v1 + v2) (d1 + d2) (l1 + l2) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => (f z, g z)) z = (fderiv ℝ f z).prod (fderiv ℝ g z) :=
    fun z hz => ((hf.1 z hz).1.hasFDerivAt.prodMk (hg.1 z hz).1.hasFDerivAt).fderiv
  have hv1 : ∀ z ∈ Metric.ball y 1, 0 ≤ v1 := fun z hz => (norm_nonneg _).trans (hf.1 z hz).2.1
  have hv2 : ∀ z ∈ Metric.ball y 1, 0 ≤ v2 := fun z hz => (norm_nonneg _).trans (hg.1 z hz).2.1
  have hd1 : ∀ z ∈ Metric.ball y 1, 0 ≤ d1 := fun z hz => (norm_nonneg _).trans (hf.1 z hz).2.2
  have hd2 : ∀ z ∈ Metric.ball y 1, 0 ≤ d2 := fun z hz => (norm_nonneg _).trans (hg.1 z hz).2.2
  refine ⟨fun z hz => ⟨(hf.1 z hz).1.prodMk (hg.1 z hz).1, ?_, ?_⟩, ?_⟩
  · rw [Prod.norm_def]
    exact max_le (((hf.1 z hz).2.1).trans (le_add_of_nonneg_right (hv2 z hz)))
      (((hg.1 z hz).2.1).trans (le_add_of_nonneg_left (hv1 z hz)))
  · rw [hD z hz, ContinuousLinearMap.opNorm_prod]
    exact max_le (((hf.1 z hz).2.2).trans (le_add_of_nonneg_right (hd2 z hz)))
      (((hg.1 z hz).2.2).trans (le_add_of_nonneg_left (hd1 z hz)))
  · intro z hz w hw
    rw [hD z hz, hD w hw]
    have e : (fderiv ℝ f z).prod (fderiv ℝ g z) - (fderiv ℝ f w).prod (fderiv ℝ g w) =
        (fderiv ℝ f z - fderiv ℝ f w).prod (fderiv ℝ g z - fderiv ℝ g w) := by
      ext1 u <;> simp
    rw [e, ContinuousLinearMap.opNorm_prod]
    have h1 := hf.2 z hz w hw
    have h2 := hg.2 z hz w hw
    have hn := norm_nonneg (z - w)
    have hl1 : 0 ≤ l1 * ‖z - w‖ := (norm_nonneg _).trans h1
    have hl2 : 0 ≤ l2 * ‖z - w‖ := (norm_nonneg _).trans h2
    refine max_le (h1.trans ?_) (h2.trans ?_) <;> nlinarith

section Scalar

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem slopeBoundOn_smul {φ : Space → ℂ} {L : Space → F} {k1 k2 v1 v2 : ℝ} {s : Set Space}
    (hφ : SlopeBoundOn φ k1 s) (hL : SlopeBoundOn L k2 s) (bφ : ∀ z ∈ s, ‖φ z‖ ≤ v1) (bL : ∀ z ∈ s, ‖L z‖ ≤ v2) :
    SlopeBoundOn (fun z => φ z • L z) (k1 * v2 + v1 * k2) s := fun z hz w hw => by
  have e : φ z • L z - φ w • L w = (φ z - φ w) • L z + φ w • (L z - L w) := by
    rw [sub_smul, smul_sub]; abel
  rw [e]
  have h1 : ‖(φ z - φ w) • L z‖ ≤ k1 * ‖z - w‖ * v2 := by
    rw [norm_smul]
    exact mul_le_mul (hφ z hz w hw) (bL z hz) (norm_nonneg _) ((norm_nonneg _).trans (hφ z hz w hw))
  have h2 : ‖φ w • (L z - L w)‖ ≤ v1 * (k2 * ‖z - w‖) := by
    rw [norm_smul]
    exact mul_le_mul (bφ w hw) (hL z hz w hw) (norm_nonneg _) ((norm_nonneg _).trans (bφ w hw))
  calc _ ≤ ‖(φ z - φ w) • L z‖ + ‖φ w • (L z - L w)‖ := norm_add_le _ _
    _ ≤ k1 * ‖z - w‖ * v2 + v1 * (k2 * ‖z - w‖) := add_le_add h1 h2
    _ = (k1 * v2 + v1 * k2) * ‖z - w‖ := by ring

theorem slopeBoundOn_smulRight {c : Space → (Space →L[ℝ] ℂ)} {v : Space → F} {k1 k2 v1 v2 : ℝ}
    {s : Set Space} (hc : SlopeBoundOn c k1 s) (hv : SlopeBoundOn v k2 s) (bc : ∀ z ∈ s, ‖c z‖ ≤ v1)
    (bv : ∀ z ∈ s, ‖v z‖ ≤ v2) :
    SlopeBoundOn (fun z => (c z).smulRight (v z)) (k1 * v2 + v1 * k2) s := fun z hz w hw => by
  have e : (c z).smulRight (v z) - (c w).smulRight (v w) =
      (c z - c w).smulRight (v z) + (c w).smulRight (v z - v w) := by
    ext1 x
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_add', Pi.sub_apply, Pi.add_apply,
      ContinuousLinearMap.smulRight_apply, sub_smul, smul_sub]
    abel
  rw [e]
  have h1 : ‖(c z - c w).smulRight (v z)‖ ≤ k1 * ‖z - w‖ * v2 :=
    (norm_smulRight_le' _ _).trans
      (mul_le_mul (hc z hz w hw) (bv z hz) (norm_nonneg _) ((norm_nonneg _).trans (hc z hz w hw)))
  have h2 : ‖(c w).smulRight (v z - v w)‖ ≤ v1 * (k2 * ‖z - w‖) :=
    (norm_smulRight_le' _ _).trans
      (mul_le_mul (bc w hw) (hv z hz w hw) (norm_nonneg _) ((norm_nonneg _).trans (bc w hw)))
  calc _ ≤ ‖(c z - c w).smulRight (v z)‖ + ‖(c w).smulRight (v z - v w)‖ := norm_add_le _ _
    _ ≤ k1 * ‖z - w‖ * v2 + v1 * (k2 * ‖z - w‖) := add_le_add h1 h2
    _ = (k1 * v2 + v1 * k2) * ‖z - w‖ := by ring

theorem ballData_smul {g : Space → ℂ} {A : Space → F} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ}
    (hg : BallData g y v1 d1 l1) (hA : BallData A y v2 d2 l2) :
    BallData (fun z => g z • A z) y (v1 * v2) (v1 * d2 + d1 * v2)
      ((d1 * d2 + v1 * l2) + (l1 * v2 + d1 * d2)) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => g z • A z) z =
      g z • fderiv ℝ A z + (fderiv ℝ g z).smulRight (A z) :=
    fun z hz => ((hg.1 z hz).1.hasFDerivAt.smul (hA.1 z hz).1.hasFDerivAt).fderiv
  have hgL : SlopeBoundOn g d1 (Metric.ball y 1) :=
    slopeBoundOn_of_fderiv (fun z hz => (hg.1 z hz).1) (fun z hz => (hg.1 z hz).2.2)
  have hAL : SlopeBoundOn A d2 (Metric.ball y 1) :=
    slopeBoundOn_of_fderiv (fun z hz => (hA.1 z hz).1) (fun z hz => (hA.1 z hz).2.2)
  refine ⟨fun z hz => ⟨(hg.1 z hz).1.smul (hA.1 z hz).1, ?_, ?_⟩, ?_⟩
  · rw [norm_smul]
    exact mul_le_mul (hg.1 z hz).2.1 (hA.1 z hz).2.1 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.1)
  · rw [hD z hz]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul]
      exact mul_le_mul (hg.1 z hz).2.1 (hA.1 z hz).2.2 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.1)
    · exact (norm_smulRight_le' _ _).trans
        (mul_le_mul (hg.1 z hz).2.2 (hA.1 z hz).2.1 (norm_nonneg _) ((norm_nonneg _).trans (hg.1 z hz).2.2))
  · have hL1 : SlopeBoundOn (fun z => g z • fderiv ℝ A z) (d1 * d2 + v1 * l2) (Metric.ball y 1) :=
      slopeBoundOn_smul hgL hA.2 (fun z hz => (hg.1 z hz).2.1) (fun z hz => (hA.1 z hz).2.2)
    have hL2 : SlopeBoundOn (fun z => (fderiv ℝ g z).smulRight (A z)) (l1 * v2 + d1 * d2) (Metric.ball y 1) :=
      slopeBoundOn_smulRight hg.2 hAL (fun z hz => (hg.1 z hz).2.2) (fun z hz => (hA.1 z hz).2.1)
    exact slopeBoundOn_congr (slopeBoundOn_add hL1 hL2) hD

end Scalar

end Generic


section Generic2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem slopeBoundOn_smulRightR {c : Space → (Space →L[ℝ] ℝ)} {v : Space → E} {k1 k2 v1 v2 : ℝ}
    {s : Set Space} (hc : SlopeBoundOn c k1 s) (hv : SlopeBoundOn v k2 s) (bc : ∀ z ∈ s, ‖c z‖ ≤ v1)
    (bv : ∀ z ∈ s, ‖v z‖ ≤ v2) :
    SlopeBoundOn (fun z => (c z).smulRight (v z)) (k1 * v2 + v1 * k2) s := fun z hz w hw => by
  have e : (c z).smulRight (v z) - (c w).smulRight (v w) =
      (c z - c w).smulRight (v z) + (c w).smulRight (v z - v w) := by
    ext1 x
    simp only [ContinuousLinearMap.coe_sub', ContinuousLinearMap.coe_add', Pi.sub_apply, Pi.add_apply,
      ContinuousLinearMap.smulRight_apply, sub_smul, smul_sub]
    abel
  rw [e]
  have h1 : ‖(c z - c w).smulRight (v z)‖ ≤ k1 * ‖z - w‖ * v2 := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (hc z hz w hw) (bv z hz) (norm_nonneg _) ((norm_nonneg _).trans (hc z hz w hw))
  have h2 : ‖(c w).smulRight (v z - v w)‖ ≤ v1 * (k2 * ‖z - w‖) := by
    rw [ContinuousLinearMap.norm_smulRight_apply]
    exact mul_le_mul (bc w hw) (hv z hz w hw) (norm_nonneg _) ((norm_nonneg _).trans (bc w hw))
  calc _ ≤ ‖(c z - c w).smulRight (v z)‖ + ‖(c w).smulRight (v z - v w)‖ := norm_add_le _ _
    _ ≤ k1 * ‖z - w‖ * v2 + v1 * (k2 * ‖z - w‖) := add_le_add h1 h2
    _ = (k1 * v2 + v1 * k2) * ‖z - w‖ := by ring

theorem FarDecay.add {a : ℕ} {f g : Space → E} (hf : FarDecay a f) (hg : FarDecay a g) : FarDecay a (fun z => f z + g z) := by
  obtain ⟨C1, R1, hC1, hR1, h1⟩ := hf
  obtain ⟨C2, R2, hC2, hR2, h2⟩ := hg
  refine ⟨C1 + C2, max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  exact ballData_mono (ballData_add (h1 y (le_of_max_le_left hy)) (h2 y (le_of_max_le_right hy)))
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))

theorem FarDecay.const (c : E) : FarDecay 0 (fun _ : Space => c) := by
  refine ⟨‖c‖, 1, norm_nonneg _, le_rfl, fun y _ => ?_⟩
  refine ballData_mono (ballData_const c y) (by simp) (by positivity) (by positivity)

theorem FarDecay.bounds {a : ℕ} {f : Space → E} (hf : FarDecay a f) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ →
      ‖f y‖ ≤ C * ‖y‖⁻¹ ^ a ∧ ‖fderiv ℝ f y‖ ≤ C * ‖y‖⁻¹ ^ (a + 1) ∧
        ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ C * ‖y‖⁻¹ ^ (a + 2) := by
  obtain ⟨C, R, hC, hR, h⟩ := hf
  refine ⟨C, R, hC, hR, fun y hy => ?_⟩
  obtain ⟨h1, h2⟩ := h y hy
  have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨(h1 y hy1).2.1, (h1 y hy1).2.2, ?_⟩
  have hL : LipschitzOnWith (Real.toNNReal (C * ‖y‖⁻¹ ^ (a + 2))) (fderiv ℝ f) (Metric.ball y 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (h2 z hz w hw).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hL
  rwa [Real.coe_toNNReal _ (by positivity)] at this

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]

theorem FarDecay.smul {a b c : ℕ} {g : Space → ℂ} {A : Space → F} (hg : FarDecay a g) (hA : FarDecay b A) (habc : a + b = c) :
    FarDecay c (fun z => g z • A z) := by
  subst habc
  obtain ⟨C1, R1, hC1, hR1, h1⟩ := hg
  obtain ⟨C2, R2, hC2, hR2, h2⟩ := hA
  refine ⟨4 * (C1 * C2), max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  have hp := ballData_smul (h1 y (le_of_max_le_left hy)) (h2 y (le_of_max_le_right hy))
  set w := ‖y‖⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  have hX : 0 ≤ C1 * C2 * w ^ (a + b) := by positivity
  have hX1 : 0 ≤ C1 * C2 * w ^ (a + b + 1) := by positivity
  refine ballData_mono hp ?_ ?_ ?_
  · have e : C1 * w ^ a * (C2 * w ^ b) = C1 * C2 * w ^ (a + b) := by ring
    rw [e]; nlinarith
  · have e : C1 * w ^ a * (C2 * w ^ (b + 1)) + C1 * w ^ (a + 1) * (C2 * w ^ b) =
        2 * (C1 * C2 * w ^ (a + b + 1)) := by ring
    rw [e]; nlinarith
  · have e : C1 * w ^ (a + 1) * (C2 * w ^ (b + 1)) + C1 * w ^ a * (C2 * w ^ (b + 2)) +
        (C1 * w ^ (a + 2) * (C2 * w ^ b) + C1 * w ^ (a + 1) * (C2 * w ^ (b + 1))) =
        4 * (C1 * C2) * w ^ (a + b + 2) := by ring
    rw [e]

end Generic2

section Radial

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_hasFDerivAt' {z : Space} (hz : z ≠ 0) :
    HasFDerivAt (fun x : Space => ‖x‖) (‖z‖⁻¹ • innerSL ℝ z) z := by
  have h2 := (hasStrictFDerivAt_norm_sq z).hasFDerivAt
  have hpos : 0 < ‖z‖ ^ 2 := by have := norm_pos_iff.2 hz; positivity
  have hs := (Real.hasDerivAt_sqrt hpos.ne').comp_hasFDerivAt z h2
  have e1 : (Real.sqrt ∘ fun x : Space => ‖x‖ ^ 2) = fun x => ‖x‖ :=
    funext fun x => by simp [Real.sqrt_sq (norm_nonneg x)]
  have e2 : (1 / (2 * Real.sqrt (‖z‖ ^ 2))) • (2 • innerSL ℝ z) = ‖z‖⁻¹ • innerSL ℝ z := by
    rw [Real.sqrt_sq (norm_nonneg z)]
    ext1 v
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply, smul_eq_mul, nsmul_eq_mul, Nat.cast_ofNat]
    field_simp
  rw [e1, e2] at hs
  exact hs

theorem normMap_norm' {z : Space} (hz : z ≠ 0) : ‖‖z‖⁻¹ • innerSL ℝ z‖ = 1 := by
  rw [norm_smul, innerSL_apply_norm, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hz)]

theorem unit_sub_le' {z w : Space} (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖‖z‖⁻¹ • z - ‖w‖⁻¹ • w‖ ≤ 2 * ‖z - w‖ / ‖z‖ := by
  have hz' : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hw' : 0 < ‖w‖ := norm_pos_iff.2 hw
  have e : ‖z‖⁻¹ • z - ‖w‖⁻¹ • w = ‖z‖⁻¹ • ((z - w) + (‖w‖ - ‖z‖) • (‖w‖⁻¹ • w)) := by
    rw [smul_add, smul_smul, smul_smul, smul_sub]
    have : ‖z‖⁻¹ * (‖w‖ - ‖z‖) * ‖w‖⁻¹ = ‖z‖⁻¹ - ‖w‖⁻¹ := by
      field_simp
    rw [this, sub_smul]
    abel
  rw [e, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hz']
  have h1 : ‖(z - w) + (‖w‖ - ‖z‖) • (‖w‖⁻¹ • w)‖ ≤ 2 * ‖z - w‖ := by
    refine (norm_add_le _ _).trans ?_
    have hu : ‖‖w‖⁻¹ • w‖ = 1 := by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hw'.ne']
    rw [norm_smul, hu, mul_one, Real.norm_eq_abs]
    have := abs_norm_sub_norm_le w z
    rw [norm_sub_rev w z] at this
    linarith
  rw [div_eq_inv_mul]
  exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hz'.le)

theorem radial_hasFDerivAt {ρ : ℝ → E} {v : E} {z : Space} (hz : z ≠ 0) (h : HasDerivAt ρ v ‖z‖) :
    HasFDerivAt (fun x : Space => ρ ‖x‖) ((‖z‖⁻¹ • innerSL ℝ z).smulRight v) z := by
  have := h.hasFDerivAt.comp z (norm_hasFDerivAt' hz)
  refine this.congr_fderiv ?_
  ext1 u
  simp [ContinuousLinearMap.smulRight_apply, smul_smul]

theorem radial_farDecay {a : ℕ} {ρ ρ1 ρ2 : ℝ → E} {R0 C : ℝ} (hR0 : 0 < R0)
    (h1 : ∀ r, R0 < r → HasDerivAt ρ (ρ1 r) r) (h2 : ∀ r, R0 < r → HasDerivAt ρ1 (ρ2 r) r)
    (hb : ∀ r, R0 < r → ‖ρ r‖ ≤ C * r⁻¹ ^ a ∧ ‖ρ1 r‖ ≤ C * r⁻¹ ^ (a + 1) ∧ ‖ρ2 r‖ ≤ C * r⁻¹ ^ (a + 2)) :
    FarDecay a (fun z : Space => ρ ‖z‖) := by
  set T : ℝ := (2 : ℝ) ^ (a + 2) with hT
  have hT1 : 1 ≤ T := one_le_pow₀ (by norm_num)
  refine ⟨5 * |C| * T, 2 * R0 + 2, by positivity, by linarith, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 < Y := by linarith
  have hz : ∀ z ∈ Metric.ball y 1, Y / 2 ≤ ‖z‖ ∧ R0 < ‖z‖ ∧ z ≠ 0 := by
    intro z hz
    have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : Y - 1 < ‖z‖ := by
      have := norm_sub_norm_le y z
      rw [norm_sub_rev] at this
      linarith
    refine ⟨by linarith, by linarith, fun h => ?_⟩
    rw [h, norm_zero] at h2
    linarith
  have hpow : ∀ z ∈ Metric.ball y 1, ∀ b : ℕ, b ≤ a + 2 → ‖z‖⁻¹ ^ b ≤ T * Y⁻¹ ^ b := by
    intro z hz' b hb
    have hzz := hz z hz'
    have hz0 : 0 < ‖z‖ := by linarith
    have e1 : ‖z‖⁻¹ ≤ 2 * Y⁻¹ := by
      rw [inv_le_iff_one_le_mul₀ hz0]
      have : 2 * Y⁻¹ * ‖z‖ ≥ 2 * Y⁻¹ * (Y / 2) := by gcongr; exact hzz.1
      have e : 2 * Y⁻¹ * (Y / 2) = 1 := by field_simp
      linarith
    calc ‖z‖⁻¹ ^ b ≤ (2 * Y⁻¹) ^ b := pow_le_pow_left₀ (by positivity) e1 b
      _ = 2 ^ b * Y⁻¹ ^ b := mul_pow _ _ _
      _ ≤ T * Y⁻¹ ^ b := by
          gcongr
          exact pow_le_pow_right₀ (by norm_num) hb
  have hbnd : ∀ z ∈ Metric.ball y 1, ∀ (u : ℝ) (b : ℕ), b ≤ a + 2 → u ≤ C * ‖z‖⁻¹ ^ b →
      u ≤ |C| * T * Y⁻¹ ^ b := by
    intro z hz' u b hb hu
    have hzp : 0 ≤ ‖z‖⁻¹ ^ b := by positivity
    calc u ≤ C * ‖z‖⁻¹ ^ b := hu
      _ ≤ |C| * ‖z‖⁻¹ ^ b := mul_le_mul_of_nonneg_right (le_abs_self C) hzp
      _ ≤ |C| * (T * Y⁻¹ ^ b) := mul_le_mul_of_nonneg_left (hpow z hz' b hb) (abs_nonneg C)
      _ = |C| * T * Y⁻¹ ^ b := by ring
  have hg : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => ρ ‖x‖)
      ((‖z‖⁻¹ • innerSL ℝ z).smulRight (ρ1 ‖z‖)) z := fun z hz' =>
    radial_hasFDerivAt (hz z hz').2.2 (h1 _ (hz z hz').2.1)
  have hg' : ∀ z ∈ Metric.ball y 1, HasFDerivAt (fun x : Space => ρ1 ‖x‖)
      ((‖z‖⁻¹ • innerSL ℝ z).smulRight (ρ2 ‖z‖)) z := fun z hz' =>
    radial_hasFDerivAt (hz z hz').2.2 (h2 _ (hz z hz').2.1)
  have hNlip : SlopeBoundOn (fun z : Space => ‖z‖⁻¹ • innerSL ℝ z) (4 * Y⁻¹) (Metric.ball y 1) := by
    intro z hz' w hw'
    have key : ‖z‖⁻¹ • innerSL ℝ z - ‖w‖⁻¹ • innerSL ℝ w = innerSL ℝ (‖z‖⁻¹ • z - ‖w‖⁻¹ • w) := by
      ext1 v
      simp [inner_sub_left, real_inner_smul_left]
    rw [key, innerSL_apply_norm]
    have hzz := hz z hz'
    refine (unit_sub_le' hzz.2.2 (hz w hw').2.2).trans ?_
    have hn : 0 ≤ 2 * ‖z - w‖ := by positivity
    calc 2 * ‖z - w‖ / ‖z‖ ≤ 2 * ‖z - w‖ / (Y / 2) := div_le_div_of_nonneg_left hn (by positivity) hzz.1
      _ = 4 * Y⁻¹ * ‖z - w‖ := by field_simp; ring
  have hCT : 0 ≤ |C| * T := by positivity
  have hw0 : 0 ≤ Y⁻¹ := by positivity
  have hφ : SlopeBoundOn (fun z : Space => ρ1 ‖z‖) (|C| * T * Y⁻¹ ^ (a + 2)) (Metric.ball y 1) := by
    refine slopeBoundOn_of_fderiv (fun z hz' => (hg' z hz').differentiableAt) (fun z hz' => ?_)
    rw [(hg' z hz').fderiv, ContinuousLinearMap.norm_smulRight_apply, normMap_norm' (hz z hz').2.2, one_mul]
    exact hbnd z hz' _ _ le_rfl (hb _ (hz z hz').2.1).2.2
  have hφb : ∀ z ∈ Metric.ball y 1, ‖ρ1 ‖z‖‖ ≤ |C| * T * Y⁻¹ ^ (a + 1) := fun z hz' =>
    hbnd z hz' _ _ (by omega) (hb _ (hz z hz').2.1).2.1
  have hNb : ∀ z ∈ Metric.ball y 1, ‖‖z‖⁻¹ • innerSL ℝ z‖ ≤ 1 := fun z hz' =>
    (normMap_norm' (hz z hz').2.2).le
  refine ⟨fun z hz' => ⟨(hg z hz').differentiableAt, ?_, ?_⟩, ?_⟩
  · refine (hbnd z hz' _ _ (by omega) (hb _ (hz z hz').2.1).1).trans ?_
    have : 0 ≤ |C| * T * Y⁻¹ ^ a := by positivity
    linarith
  · rw [(hg z hz').fderiv, ContinuousLinearMap.norm_smulRight_apply, normMap_norm' (hz z hz').2.2, one_mul]
    refine (hφb z hz').trans ?_
    have : 0 ≤ |C| * T * Y⁻¹ ^ (a + 1) := by positivity
    linarith
  · have hL := slopeBoundOn_smulRightR hNlip hφ hNb hφb
    refine slopeBoundOn_mono (slopeBoundOn_congr hL fun z hz' => (hg z hz').fderiv) ?_
    have e : 4 * Y⁻¹ * (|C| * T * Y⁻¹ ^ (a + 1)) + 1 * (|C| * T * Y⁻¹ ^ (a + 2)) =
        5 * |C| * T * Y⁻¹ ^ (a + 2) := by ring
    rw [e]

end Radial

section Hom

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hom_fderiv' {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y) {s : ℝ} (hs : 0 < s)
    {z : Space} (hd : DifferentiableAt ℝ A (s⁻¹ • z)) :
    fderiv ℝ A z = s⁻¹ • fderiv ℝ A (s⁻¹ • z) := by
  have h : HasFDerivAt (fun w => A (s⁻¹ • w))
      ((fderiv ℝ A (s⁻¹ • z)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space)) z :=
    hd.hasFDerivAt.comp z ((hasFDerivAt_id z).const_smul s⁻¹)
  have h2 : HasFDerivAt A ((fderiv ℝ A (s⁻¹ • z)).comp (s⁻¹ • ContinuousLinearMap.id ℝ Space)) z :=
    h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun w => (hhom s⁻¹ (inv_pos.2 hs) w).symm)
  rw [h2.fderiv]
  ext1 v
  simp

theorem hom_farDecay {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y)
    (hd : ∀ y : Space, y ≠ 0 → DifferentiableAt ℝ A y)
    (hl : LocallyLipschitzOn {y : Space | y ≠ 0} (fderiv ℝ A)) : FarDecay 0 A := by
  set K : Set Space := {w | 1 / 2 ≤ ‖w‖ ∧ ‖w‖ ≤ 2} with hKdef
  have hKc : IsCompact K := (isCompact_closedBall (0 : Space) 2).of_isClosed_subset
    ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
    (fun w hw => by simpa [Metric.mem_closedBall, dist_zero_right] using hw.2)
  have hK0 : ∀ w ∈ K, w ≠ 0 := fun w hw h => by
    have := hw.1
    rw [h, norm_zero] at this
    linarith
  obtain ⟨L, hL⟩ := (hl.mono (fun w hw => hK0 w hw)).exists_lipschitzOnWith_of_compact hKc
  obtain ⟨M1, hStrain⟩ := hKc.exists_bound_of_continuousOn (f := A)
    (fun w hw => (hd w (hK0 w hw)).continuousAt.continuousWithinAt)
  obtain ⟨M2, hM2⟩ := hKc.exists_bound_of_continuousOn hL.continuousOn
  have hL0 : (0 : ℝ) ≤ L := L.2
  set M : ℝ := |M1| + |M2| + L with hM
  have hM0 : 0 ≤ M := by positivity
  refine ⟨M, 2, hM0, by norm_num, fun y hy => ?_⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 < Y := by linarith
  have hmem : ∀ z ∈ Metric.ball y 1, Y⁻¹ • z ∈ K ∧ z ≠ 0 := by
    intro z hz
    have h1 : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
    have h2 : Y - 1 < ‖z‖ := by
      have := norm_sub_norm_le y z
      rw [norm_sub_rev] at this
      linarith
    have h3 : ‖z‖ < Y + 1 := by
      have := norm_sub_norm_le z y
      linarith
    have hn : ‖Y⁻¹ • z‖ = ‖z‖ / Y := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
      ring
    refine ⟨⟨?_, ?_⟩, fun h => by rw [h, norm_zero] at h2; linarith⟩
    · rw [hn, le_div_iff₀ hY0]; linarith
    · rw [hn, div_le_iff₀ hY0]; linarith
  have hval : ∀ z, A z = A (Y⁻¹ • z) := fun z => (hhom Y⁻¹ (inv_pos.2 hY0) z).symm
  have hder : ∀ z ∈ Metric.ball y 1, fderiv ℝ A z = Y⁻¹ • fderiv ℝ A (Y⁻¹ • z) := fun z hz =>
    hom_fderiv' hhom hY0 (hd _ (hK0 _ (hmem z hz).1))
  refine ⟨fun z hz => ⟨hd z (hmem z hz).2, ?_, ?_⟩, fun z hz w hw => ?_⟩
  · rw [hval z, pow_zero, mul_one]
    exact (hStrain _ (hmem z hz).1).trans (by linarith [le_abs_self M1, abs_nonneg M2])
  · rw [hder z hz, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0, zero_add, pow_one]
    have := hM2 _ (hmem z hz).1
    calc Y⁻¹ * ‖fderiv ℝ A (Y⁻¹ • z)‖ ≤ Y⁻¹ * M :=
          mul_le_mul_of_nonneg_left (by linarith [le_abs_self M2, abs_nonneg M1]) (inv_nonneg.2 hY0.le)
      _ = _ := by ring
  · rw [hder z hz, hder w hw, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0]
    have h1 := hL.dist_le_mul _ (hmem z hz).1 _ (hmem w hw).1
    rw [dist_eq_norm, dist_eq_norm, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hY0] at h1
    calc Y⁻¹ * ‖fderiv ℝ A (Y⁻¹ • z) - fderiv ℝ A (Y⁻¹ • w)‖ ≤ Y⁻¹ * (L * (Y⁻¹ * ‖z - w‖)) :=
          mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hY0.le)
      _ ≤ Y⁻¹ * (M * (Y⁻¹ * ‖z - w‖)) := by
          have : (0 : ℝ) ≤ Y⁻¹ * ‖z - w‖ := by positivity
          have : (L : ℝ) ≤ M := by linarith [abs_nonneg M1, abs_nonneg M2]
          gcongr
      _ = M * Y⁻¹ ^ (0 + 2) * ‖z - w‖ := by ring

theorem hom_FD_of_contDiffAt {A : Space → E} (hhom : ∀ s : ℝ, 0 < s → ∀ y, A (s • y) = A y)
    (hA : ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 2 A y) : FarDecay 0 A := by
  refine hom_farDecay hhom (fun y hy => (hA y hy).differentiableAt (by norm_num)) ?_
  intro y hy
  obtain ⟨K, t, ht, hK⟩ := ((hA y hy).fderiv_right (m := 1) (by norm_num)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

end Hom

section Comp

theorem ballData_comp {φ : Space → ℝ × ℝ} {G : ℝ × ℝ → ℂ} {y : Space} {vφ dφ lφ M0 M1 M2 : ℝ}
    {K : Set (ℝ × ℝ)} (hφ : BallData φ y vφ dφ lφ) (hK : ∀ z ∈ Metric.ball y 1, φ z ∈ K)
    (hG : Differentiable ℝ G) (b0 : ∀ p ∈ K, ‖G p‖ ≤ M0) (b1 : ∀ p ∈ K, ‖fderiv ℝ G p‖ ≤ M1)
    (hL : ∀ p ∈ K, ∀ q ∈ K, ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ M2 * ‖p - q‖) (hM2 : 0 ≤ M2) :
    BallData (fun z => G (φ z)) y M0 (M1 * dφ) (M2 * dφ * dφ + M1 * lφ) := by
  have hy1 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  have hd0 : 0 ≤ dφ := (norm_nonneg _).trans (hφ.1 y hy1).2.2
  have hStrain : 0 ≤ M1 := (norm_nonneg _).trans (b1 _ (hK y hy1))
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => G (φ z)) z = (fderiv ℝ G (φ z)).comp (fderiv ℝ φ z) :=
    fun z hz => ((hG (φ z)).hasFDerivAt.comp z (hφ.1 z hz).1.hasFDerivAt).fderiv
  have hφL : SlopeBoundOn φ dφ (Metric.ball y 1) :=
    slopeBoundOn_of_fderiv (fun z hz => (hφ.1 z hz).1) (fun z hz => (hφ.1 z hz).2.2)
  refine ⟨fun z hz => ⟨(hG (φ z)).comp z (hφ.1 z hz).1, b0 _ (hK z hz), ?_⟩, fun z hz w hw => ?_⟩
  · rw [hD z hz]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (b1 _ (hK z hz)) (hφ.1 z hz).2.2 (norm_nonneg _) hStrain)
  · rw [hD z hz, hD w hw]
    have e : (fderiv ℝ G (φ z)).comp (fderiv ℝ φ z) - (fderiv ℝ G (φ w)).comp (fderiv ℝ φ w) =
        (fderiv ℝ G (φ z) - fderiv ℝ G (φ w)).comp (fderiv ℝ φ z) +
          (fderiv ℝ G (φ w)).comp (fderiv ℝ φ z - fderiv ℝ φ w) := by
      ext1 u; simp
    rw [e]
    have h1 : ‖(fderiv ℝ G (φ z) - fderiv ℝ G (φ w)).comp (fderiv ℝ φ z)‖ ≤ M2 * dφ * dφ * ‖z - w‖ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have a1 := hL _ (hK z hz) _ (hK w hw)
      have a2 := hφL z hz w hw
      have a3 := (hφ.1 z hz).2.2
      have hM2' : 0 ≤ M2 * ‖φ z - φ w‖ := (norm_nonneg _).trans a1
      calc ‖fderiv ℝ G (φ z) - fderiv ℝ G (φ w)‖ * ‖fderiv ℝ φ z‖ ≤ M2 * ‖φ z - φ w‖ * dφ :=
            mul_le_mul a1 a3 (norm_nonneg _) hM2'
        _ ≤ M2 * (dφ * ‖z - w‖) * dφ := by gcongr
        _ = M2 * dφ * dφ * ‖z - w‖ := by ring
    have h2 : ‖(fderiv ℝ G (φ w)).comp (fderiv ℝ φ z - fderiv ℝ φ w)‖ ≤ M1 * lφ * ‖z - w‖ := by
      refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
      have := mul_le_mul (b1 _ (hK w hw)) (hφ.2 z hz w hw) (norm_nonneg _) hStrain
      linarith
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ M2 * dφ * dφ * ‖z - w‖ + M1 * lφ * ‖z - w‖ := add_le_add h1 h2
      _ = (M2 * dφ * dφ + M1 * lφ) * ‖z - w‖ := by ring

def SlopeRegular (G : ℝ × ℝ → ℂ) : Prop := ContDiff ℝ 1 G ∧ LocallyLipschitz (fderiv ℝ G)

theorem FarDecay.prod {f g : Space → ℝ} (hf : FarDecay 0 f) (hg : FarDecay 0 g) : FarDecay 0 (fun z => (f z, g z)) := by
  obtain ⟨C1, R1, hC1, hR1, h1⟩ := hf
  obtain ⟨C2, R2, hC2, hR2, h2⟩ := hg
  refine ⟨C1 + C2, max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  exact ballData_mono (ballData_prod (h1 y (le_of_max_le_left hy)) (h2 y (le_of_max_le_right hy)))
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))

theorem FarDecay.comp {φ : Space → ℝ × ℝ} {G : ℝ × ℝ → ℂ} (hφ : FarDecay 0 φ)
    (hr : ∀ z, φ z ∈ Metric.closedBall (0 : ℝ × ℝ) 1) (hG : SlopeRegular G) : FarDecay 0 (fun z => G (φ z)) := by
  obtain ⟨C, R, hC, hR, h⟩ := hφ
  set K := Metric.closedBall (0 : ℝ × ℝ) 1
  have hKc : IsCompact K := isCompact_closedBall _ _
  obtain ⟨M0, hM0⟩ := hKc.exists_bound_of_continuousOn hG.1.continuous.continuousOn
  obtain ⟨M1, hStrain⟩ := hKc.exists_bound_of_continuousOn (hG.1.continuous_fderiv one_ne_zero).continuousOn
  have hll : LocallyLipschitzOn K (fderiv ℝ G) := fun p _ => by
    obtain ⟨L, t, ht, hL⟩ := hG.2 p
    exact ⟨L, t, mem_nhdsWithin_of_mem_nhds ht, hL⟩
  obtain ⟨M2, hM2⟩ := hll.exists_lipschitzOnWith_of_compact hKc
  have hdiff : Differentiable ℝ G := hG.1.differentiable one_ne_zero
  have hL : ∀ p ∈ K, ∀ q ∈ K, ‖fderiv ℝ G p - fderiv ℝ G q‖ ≤ (M2 : ℝ) * ‖p - q‖ := by
    intro p hp q hq
    have := hM2.dist_le_mul p hp q hq
    rwa [dist_eq_norm, dist_eq_norm] at this
  have hM2' : (0 : ℝ) ≤ M2 := M2.2
  refine ⟨|M0| + |M1| * C + M2 * C * C + |M1| * C, R, by positivity, hR, fun y hy => ?_⟩
  have hb := ballData_comp (h y hy) (fun z _ => hr z) hdiff (fun p hp => (hM0 p hp).trans (le_abs_self M0))
    (fun p hp => (hStrain p hp).trans (le_abs_self M1)) hL hM2'
  have hY1 : 1 ≤ ‖y‖ := hR.trans hy
  set w := ‖y‖⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hY1
  refine ballData_mono hb ?_ ?_ ?_
  · rw [pow_zero, mul_one]
    have : 0 ≤ |M1| * C + M2 * C * C + |M1| * C := by positivity
    linarith
  · rw [zero_add, pow_one]
    have : 0 ≤ (|M0| + M2 * C * C + |M1| * C) * w := by positivity
    nlinarith
  · have e : M2 * (C * w ^ (0 + 1)) * (C * w ^ (0 + 1)) + |M1| * (C * w ^ (0 + 2)) =
        (M2 * C * C + |M1| * C) * w ^ 2 := by ring
    rw [e, zero_add]
    have : 0 ≤ (|M0| + |M1| * C) * w ^ 2 := by positivity
    nlinarith

end Comp

section Reg

theorem locSlopeBound_bilin' {X E F G : Type*} [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    (B : E →L[ℝ] F →L[ℝ] G) {f : X → E} {h : X → F} (hf : LocallyLipschitz f) (hh : LocallyLipschitz h) :
    LocallyLipschitz (fun x => B (f x) (h x)) := by
  intro x
  obtain ⟨K1, t1, ht1, hf1⟩ := hf x
  obtain ⟨K2, t2, ht2, hh2⟩ := hh x
  obtain ⟨r, hr, hrt⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht1 ht2)
  have hf' : LipschitzOnWith K1 f (Metric.ball x r) := hf1.mono fun z hz => (hrt hz).1
  have hh' : LipschitzOnWith K2 h (Metric.ball x r) := hh2.mono fun z hz => (hrt hz).2
  have hx : x ∈ Metric.ball x r := Metric.mem_ball_self hr
  set M1 : ℝ := ‖f x‖ + K1 * r
  set M2 : ℝ := ‖h x‖ + K2 * r
  have hb1 : ∀ z ∈ Metric.ball x r, ‖f z‖ ≤ M1 := by
    intro z hz
    have h1 := hf'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖f z‖ ≤ ‖f x‖ + dist (f z) (f x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (f z) (f x)
      linarith [norm_sub_rev (f z) (f x)]
    nlinarith [K1.2]
  have hb2 : ∀ z ∈ Metric.ball x r, ‖h z‖ ≤ M2 := by
    intro z hz
    have h1 := hh'.dist_le_mul z hz x hx
    have h2 : dist z x < r := hz
    have h3 : ‖h z‖ ≤ ‖h x‖ + dist (h z) (h x) := by
      rw [dist_eq_norm]
      have := norm_le_insert' (h z) (h x)
      linarith [norm_sub_rev (h z) (h x)]
    nlinarith [K2.2]
  have hStrain : 0 ≤ M1 := le_trans (norm_nonneg _) (hb1 x hx)
  have hM2 : 0 ≤ M2 := le_trans (norm_nonneg _) (hb2 x hx)
  refine ⟨Real.toNNReal (‖B‖ * (K1 * M2 + M1 * K2)), Metric.ball x r, Metric.ball_mem_nhds x hr, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have hsplit : B (f a) (h a) - B (f b) (h b) = B (f a - f b) (h a) + B (f b) (h a - h b) := by
    simp only [map_sub, ContinuousLinearMap.sub_apply]
    abel
  rw [hsplit]
  have e1 : ‖B (f a - f b) (h a)‖ ≤ ‖B‖ * ‖f a - f b‖ * ‖h a‖ := B.le_opNorm₂ _ _
  have e2 : ‖B (f b) (h a - h b)‖ ≤ ‖B‖ * ‖f b‖ * ‖h a - h b‖ := B.le_opNorm₂ _ _
  have d1 : ‖f a - f b‖ ≤ K1 * dist a b := by rw [← dist_eq_norm]; exact hf'.dist_le_mul a ha b hb
  have d2 : ‖h a - h b‖ ≤ K2 * dist a b := by rw [← dist_eq_norm]; exact hh'.dist_le_mul a ha b hb
  have n1 := hb2 a ha
  have n2 := hb1 b hb
  have hB := norm_nonneg B
  calc ‖B (f a - f b) (h a) + B (f b) (h a - h b)‖ ≤ ‖B (f a - f b) (h a)‖ + ‖B (f b) (h a - h b)‖ :=
        norm_add_le _ _
    _ ≤ ‖B‖ * (K1 * dist a b) * M2 + ‖B‖ * M1 * (K2 * dist a b) := by
        gcongr
        · exact e1.trans (by gcongr)
        · exact e2.trans (by gcongr)
    _ = ‖B‖ * (K1 * M2 + M1 * K2) * dist a b := by ring

theorem SlopeRegular.of_contDiff {G : ℝ × ℝ → ℂ} (h : ContDiff ℝ 2 G) : SlopeRegular G :=
  ⟨h.of_le (by norm_num), (h.fderiv_right (m := 1) (by norm_num)).locallyLipschitz⟩

theorem SlopeRegular.add {G H : ℝ × ℝ → ℂ} (hG : SlopeRegular G) (hH : SlopeRegular H) : SlopeRegular (fun z => G z + H z) := by
  refine ⟨hG.1.add hH.1, ?_⟩
  have e : fderiv ℝ (fun z => G z + H z) = fun z => fderiv ℝ G z + fderiv ℝ H z := by
    funext z
    exact fderiv_add ((hG.1.differentiable one_ne_zero) z) ((hH.1.differentiable one_ne_zero) z)
  rw [e]
  exact hG.2.add hH.2

theorem SlopeRegular.mul {G H : ℝ × ℝ → ℂ} (hG : SlopeRegular G) (hH : SlopeRegular H) : SlopeRegular (fun z => G z * H z) := by
  refine ⟨hG.1.mul hH.1, ?_⟩
  have e : fderiv ℝ (fun z => G z * H z) = fun z => G z • fderiv ℝ H z + H z • fderiv ℝ G z := by
    funext z
    exact (((hG.1.differentiable one_ne_zero) z).hasFDerivAt.mul
      ((hH.1.differentiable one_ne_zero) z).hasFDerivAt).fderiv
  rw [e]
  have h1 := locSlopeBound_bilin' (ContinuousLinearMap.lsmul ℝ ℂ) hG.1.locallyLipschitz hH.2
  have h2 := locSlopeBound_bilin' (ContinuousLinearMap.lsmul ℝ ℂ) hH.1.locallyLipschitz hG.2
  simpa [ContinuousLinearMap.lsmul_apply] using h1.add h2

theorem SlopeRegular.spline {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    SlopeRegular (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) := by
  refine ⟨(joinedSplineSmooth a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb)), ?_⟩
  intro z
  obtain ⟨L, hL⟩ := joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth a b S hS ha hb (‖z‖ + 1)
  refine ⟨L, _, Metric.closedBall_mem_nhds_of_mem ?_, hL⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

end Reg

section Generators

theorem heightRatio_smul {s : ℝ} (hs : 0 < s) (y : Space) : heightRatio (s • y) = heightRatio y := by
  unfold heightRatio
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, PiLp.smul_apply, smul_eq_mul]
  by_cases hy : ‖y‖ = 0
  · simp [hy]
  · field_simp

theorem coord_div_smul {s : ℝ} (hs : 0 < s) (y : Space) (i : Fin 3) : (s • y) i / ‖s • y‖ = y i / ‖y‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hs, PiLp.smul_apply, smul_eq_mul]
  by_cases hy : ‖y‖ = 0
  · simp [hy]
  · field_simp

theorem pointAngle_smul {s : ℝ} (hs : 0 < s) (y : Space) : pointAngle (s • y) = pointAngle y := by
  unfold pointAngle
  rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul]
  have e : (((s * y 0 : ℝ) : ℂ) + ((s * y 1 : ℝ) : ℂ) * Complex.I) = (s : ℂ) * ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
    push_cast; ring
  rw [e, Complex.arg_real_mul _ hs]

theorem coord_div_contDiffAt {y : Space} (hy : y ≠ 0) (i : Fin 3) :
    ContDiffAt ℝ 2 (fun z : Space => z i / ‖z‖) y := by
  have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff (n := 2)).contDiffAt.div
    (contDiffAt_norm ℝ hy) (norm_ne_zero_iff.2 hy)
  exact h

theorem ofReal_contDiffAt {f : Space → ℝ} {y : Space} (h : ContDiffAt ℝ 2 f y) :
    ContDiffAt ℝ 2 (fun z => ((f z : ℝ) : ℂ)) y :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp y h

theorem polarVecQ_smul {s : ℝ} (hs : 0 < s) (y : Space) : polarVecQ (s • y) = polarVecQ y := by
  have e0 : heightRatio (s • y) * (s • y) 0 / ‖s • y‖ = heightRatio y * y 0 / ‖y‖ := by
    rw [mul_div_assoc, mul_div_assoc, heightRatio_smul hs, coord_div_smul hs]
  have e1 : heightRatio (s • y) * (s • y) 1 / ‖s • y‖ = heightRatio y * y 1 / ‖y‖ := by
    rw [mul_div_assoc, mul_div_assoc, heightRatio_smul hs, coord_div_smul hs]
  have e2 : qOf (s • y) = qOf y := by simp only [qOf, heightRatio_smul hs]
  funext i
  simp only [polarVecQ, e0, e1, e2]

theorem azimVecQ_smul {s : ℝ} (hs : 0 < s) (y : Space) : azimVecQ (s • y) = azimVecQ y := by
  have e0 : -(s • y) 1 / ‖s • y‖ = -y 1 / ‖y‖ := by rw [neg_div, neg_div, coord_div_smul hs]
  have e1 : (s • y) 0 / ‖s • y‖ = y 0 / ‖y‖ := coord_div_smul hs y 0
  funext i
  simp only [azimVecQ, e0, e1]

theorem heightRatio_contDiffAt {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 heightRatio y :=
  coord_div_contDiffAt hy 2

theorem heightRatio_farDecay : FarDecay 0 heightRatio :=
  hom_FD_of_contDiffAt (fun s hs y => heightRatio_smul hs y) fun y hy => heightRatio_contDiffAt hy

def radialC (y : Space) : Fin 3 → ℂ := fun i => ((radialVec y i : ℝ) : ℂ)

def polarC (y : Space) : Fin 3 → ℂ := fun i => ((polarVecQ y i : ℝ) : ℂ)

def azimC (y : Space) : Fin 3 → ℂ := fun i => ((azimVecQ y i : ℝ) : ℂ)

theorem radialC_farDecay : FarDecay 0 radialC := by
  refine hom_FD_of_contDiffAt (fun s hs y => ?_) fun y hy => ?_
  · funext i
    simp only [radialC, radialVec, coord_div_smul hs]
  · refine contDiffAt_pi.2 fun i => ?_
    exact ofReal_contDiffAt (coord_div_contDiffAt hy i)

theorem polarC_farDecay : FarDecay 0 polarC := by
  refine hom_FD_of_contDiffAt (fun s hs y => ?_) fun y hy => ?_
  · funext i
    simp only [polarC, polarVecQ_smul hs]
  · refine contDiffAt_pi.2 fun i => ?_
    have h2 := heightRatio_contDiffAt hy
    fin_cases i
    · have := ofReal_contDiffAt (h2.mul (coord_div_contDiffAt hy 0))
      simpa [polarC, polarVecQ, mul_div_assoc] using this
    · have := ofReal_contDiffAt (h2.mul (coord_div_contDiffAt hy 1))
      simpa [polarC, polarVecQ, mul_div_assoc] using this
    · have := ofReal_contDiffAt ((contDiffAt_const (c := (1 : ℝ))).sub (h2.pow 2)).neg
      simpa [polarC, polarVecQ, qOf] using this

theorem azimC_farDecay : FarDecay 0 azimC := by
  refine hom_FD_of_contDiffAt (fun s hs y => ?_) fun y hy => ?_
  · funext i
    simp only [azimC, azimVecQ_smul hs]
  · refine contDiffAt_pi.2 fun i => ?_
    fin_cases i
    · have := ofReal_contDiffAt (coord_div_contDiffAt hy 1).neg
      simpa [azimC, azimVecQ, neg_div] using this
    · have := ofReal_contDiffAt (coord_div_contDiffAt hy 0)
      simpa [azimC, azimVecQ] using this
    · simpa [azimC, azimVecQ] using (contDiffAt_const (c := (0 : ℂ)))

def angularC (k : ℤ) (y : Space) : ℂ :=
  axisFactor (heightRatio y) * Complex.exp ((((k : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I)

theorem angularC_farDecay (k : ℤ) : FarDecay 0 (angularC k) := by
  refine hom_FD_of_contDiffAt (fun s hs y => ?_) fun y hy => ?_
  · simp only [angularC, heightRatio_smul hs, pointAngle_smul hs]
  · exact (angularFactor_contDiffAt k hy).of_le (by norm_num)

theorem invShift_hasDerivAt {L r : ℝ} (h : r + L ≠ 0) :
    HasDerivAt (fun r : ℝ => (r + L)⁻¹) (-((r + L)⁻¹) ^ 2) r := by
  have := ((hasDerivAt_id' r).add_const L).inv h
  exact this.congr_deriv (by field_simp)

theorem invShift_sq_hasDerivAt {L r : ℝ} (h : r + L ≠ 0) :
    HasDerivAt (fun r : ℝ => ((r + L)⁻¹) ^ 2) (-(2 * ((r + L)⁻¹) ^ 3)) r := by
  have := (invShift_hasDerivAt h).pow 2
  exact this.congr_deriv (by push_cast; ring)

theorem invShift_bound {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (n : ℕ) : ((r + L)⁻¹) ^ n ≤ r⁻¹ ^ n := by
  have : (r + L)⁻¹ ≤ r⁻¹ := inv_anti₀ hr (by linarith)
  exact pow_le_pow_left₀ (by positivity) this n

theorem tailC_farDecay {L : ℝ} (hL : 0 < L) :
    FarDecay 1 (fun z : Space => (((L * (‖z‖ + L)⁻¹ : ℝ)) : ℂ)) := by
  refine radial_farDecay (ρ := fun r : ℝ => (((L * (r + L)⁻¹ : ℝ)) : ℂ))
    (ρ1 := fun r : ℝ => (((-(L * ((r + L)⁻¹) ^ 2) : ℝ)) : ℂ))
    (ρ2 := fun r : ℝ => (((2 * L * ((r + L)⁻¹) ^ 3 : ℝ)) : ℂ)) (R0 := 1) (C := 2 * L) one_pos ?_ ?_ ?_
  · intro r hr
    exact (((invShift_hasDerivAt (L := L) (r := r) (by linarith)).const_mul L).congr_deriv
      (by ring)).ofReal_comp
  · intro r hr
    exact (((invShift_sq_hasDerivAt (L := L) (r := r) (by linarith)).const_mul L).neg.congr_deriv
      (by ring)).ofReal_comp
  · intro r hr
    have hr0 : 0 < r := by linarith
    have b1 := invShift_bound hL hr0 1
    have b2 := invShift_bound hL hr0 2
    have b3 := invShift_bound hL hr0 3
    have u0 : 0 ≤ (r + L)⁻¹ := by positivity
    rw [pow_one] at b1
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_one]
      nlinarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity)]
      nlinarith
    · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      nlinarith

theorem chartC_farDecay {L : ℝ} (hL : 0 < L) :
    FarDecay 0 (fun z : Space => (1 - L * (‖z‖ + L)⁻¹ : ℝ)) := by
  refine radial_farDecay (ρ := fun r : ℝ => (1 - L * (r + L)⁻¹ : ℝ))
    (ρ1 := fun r : ℝ => L * ((r + L)⁻¹) ^ 2)
    (ρ2 := fun r : ℝ => -(2 * L * ((r + L)⁻¹) ^ 3)) (R0 := 1) (C := 1 + 2 * L) one_pos ?_ ?_ ?_
  · intro r hr
    exact (((invShift_hasDerivAt (L := L) (r := r) (by linarith)).const_mul L).const_sub 1).congr_deriv
      (by ring)
  · intro r hr
    exact ((invShift_sq_hasDerivAt (L := L) (r := r) (by linarith)).const_mul L).congr_deriv (by ring)
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hr1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
    have b2 := invShift_bound hL hr0 2
    have b3 := invShift_bound hL hr0 3
    have u0 : 0 ≤ (r + L)⁻¹ := by positivity
    have u1 : (r + L)⁻¹ ≤ L⁻¹ := inv_anti₀ hL (by linarith)
    have hLu : L * (r + L)⁻¹ ≤ 1 := by
      calc L * (r + L)⁻¹ ≤ L * L⁻¹ := by gcongr
        _ = 1 := mul_inv_cancel₀ hL.ne'
    have w0 : 0 ≤ r⁻¹ := by positivity
    have e2 : r⁻¹ ^ 2 ≤ r⁻¹ := by rw [pow_two]; nlinarith
    have e3 : r⁻¹ ^ 3 ≤ r⁻¹ ^ 2 := by rw [pow_succ]; nlinarith [pow_nonneg w0 2]
    refine ⟨?_, ?_, ?_⟩
    · rw [Real.norm_eq_abs, abs_le, pow_zero, mul_one]
      have : 0 ≤ L * (r + L)⁻¹ := by positivity
      constructor <;> nlinarith
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), zero_add, pow_one]
      nlinarith
    · rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (by positivity), zero_add]
      nlinarith [pow_nonneg u0 3]

end Generators

section Phase

theorem phase_derivs {Φ : ℝ → ℝ} (hΦ : IsRadialPhase Φ) :
    ∀ s : ℝ, 0 < s → HasDerivAt Φ (deriv Φ s) s ∧ HasDerivAt (deriv Φ) (iteratedDeriv 2 Φ s) s ∧
      HasDerivAt (iteratedDeriv 2 Φ) (iteratedDeriv 3 Φ s) s := by
  obtain ⟨δ, hδ, hsm⟩ := hΦ.smooth
  have hU : IsOpen (Set.Ioi (-δ)) := isOpen_Ioi
  have hsm' : ContDiffOn ℝ ((2 : WithTop ℕ∞) + 1) Φ (Set.Ioi (-δ)) := by
    have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
    rw [e3]; exact hsm
  have h1 : ContDiffOn ℝ 2 (deriv Φ) (Set.Ioi (-δ)) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen hU).1 hsm').2.2
  have h1' : ContDiffOn ℝ ((1 : WithTop ℕ∞) + 1) (deriv Φ) (Set.Ioi (-δ)) := by
    have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
    rw [e2]; exact h1
  have h2 : ContDiffOn ℝ 1 (deriv (deriv Φ)) (Set.Ioi (-δ)) :=
    ((contDiffOn_succ_iff_deriv_of_isOpen hU).1 h1').2.2
  have i2 : iteratedDeriv 2 Φ = deriv (deriv Φ) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have i3 : iteratedDeriv 3 Φ = deriv (iteratedDeriv 2 Φ) := iteratedDeriv_succ
  intro s hs
  have hsU : s ∈ Set.Ioi (-δ) := by rw [Set.mem_Ioi]; linarith
  have hn : Set.Ioi (-δ) ∈ 𝓝 s := hU.mem_nhds hsU
  refine ⟨(((hsm.differentiableOn (by norm_num)) s hsU).differentiableAt hn).hasDerivAt, ?_, ?_⟩
  · rw [i2]; exact (((h1.differentiableOn (by norm_num)) s hsU).differentiableAt hn).hasDerivAt
  · rw [i3, i2]; exact (((h2.differentiableOn (by norm_num)) s hsU).differentiableAt hn).hasDerivAt

theorem abs_le_of_eq_mul {x a w M : ℝ} (h : x = a * w) (ha : |a| ≤ M) (hw : 0 ≤ w) : |x| ≤ M * w := by
  rw [h, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right ha hw

theorem sq_hasDerivAt (r : ℝ) : HasDerivAt (fun r : ℝ => r ^ 2) (2 * r) r := by
  simpa using hasDerivAt_pow 2 r

theorem comp_sq {g : ℝ → ℝ} {g' r : ℝ} (hg : HasDerivAt g g' (r ^ 2)) :
    HasDerivAt (fun x : ℝ => g (x ^ 2)) (g' * (2 * r)) r :=
  hg.comp (h := fun x : ℝ => x ^ 2) r (sq_hasDerivAt r)

theorem abs_lin2 (a b c d : ℝ) : |c * a + d * b| ≤ |c| * |a| + |d| * |b| :=
  (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])

theorem abs_lin3 (a b e c d f : ℝ) : |c * a + d * b + f * e| ≤ |c| * |a| + |d| * |b| + |f| * |e| :=
  (abs_add_le _ _).trans (add_le_add (abs_lin2 a b c d) (by rw [abs_mul]))

theorem phaseC_farDecay {Φ : ℝ → ℝ} (hΦ : IsRadialPhase Φ) (j : ℝ) :
    FarDecay 0 (fun y : Space => Complex.exp (((j * Φ (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨B, hB⟩ := hΦ.scaled_bounded
  have hd := phase_derivs hΦ
  set f1 : ℝ → ℝ := fun r => j * (deriv Φ (r ^ 2) * (2 * r)) with hf1
  set f2 : ℝ → ℝ := fun r => j * (iteratedDeriv 2 Φ (r ^ 2) * (2 * r) * (2 * r) + deriv Φ (r ^ 2) * 2) with hf2
  set ρ : ℝ → ℂ := fun r => Complex.exp (((j * Φ (r ^ 2) : ℝ) : ℂ) * Complex.I) with hρ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl).1
  refine radial_farDecay (ρ := ρ) (ρ1 := fun r => ρ r * ((f1 r : ℂ) * Complex.I))
    (ρ2 := fun r => ρ r * ((f1 r : ℂ) * Complex.I) * ((f1 r : ℂ) * Complex.I) + ρ r * ((f2 r : ℂ) * Complex.I))
    (R0 := 1) (C := 1 + 2 * |j| * B + 4 * j ^ 2 * B ^ 2 + 6 * |j| * B) one_pos ?_ ?_ ?_
  · intro r hr
    have hs : 0 < r ^ 2 := by positivity
    have hf : HasDerivAt (fun r : ℝ => j * Φ (r ^ 2)) (f1 r) r :=
      (comp_sq (hd _ hs).1).const_mul j
    exact (hf.ofReal_comp.mul_const Complex.I).cexp
  · intro r hr
    have hs : 0 < r ^ 2 := by positivity
    have hf : HasDerivAt (fun r : ℝ => j * Φ (r ^ 2)) (f1 r) r :=
      (comp_sq (hd _ hs).1).const_mul j
    have hρd : HasDerivAt ρ (ρ r * ((f1 r : ℂ) * Complex.I)) r := (hf.ofReal_comp.mul_const Complex.I).cexp
    have hf1d : HasDerivAt f1 (f2 r) r :=
      (((comp_sq (hd _ hs).2.1).mul ((hasDerivAt_id' r).const_mul 2)).const_mul j).congr_deriv
        (by simp only [hf2]; ring)
    have hc : HasDerivAt (fun r => ((f1 r : ℝ) : ℂ) * Complex.I) ((f2 r : ℂ) * Complex.I) r :=
      hf1d.ofReal_comp.mul_const Complex.I
    exact (hρd.mul hc).congr_deriv (by ring)
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hs : 0 ≤ r ^ 2 := by positivity
    obtain ⟨b1, b2, -⟩ := hB (r ^ 2) hs
    have hw : 0 ≤ r⁻¹ := by positivity
    have hw1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
    have hnρ : ‖ρ r‖ = 1 := by simp only [hρ]; exact Complex.norm_exp_ofReal_mul_I _
    have nI : ∀ x : ℝ, ‖(x : ℂ) * Complex.I‖ = |x| := fun x => by
      rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have e1 : f1 r = (2 * j * (r ^ 2 * deriv Φ (r ^ 2))) * r⁻¹ := by
      simp only [hf1]; field_simp; try ring
    have e2 : f2 r = (j * (4 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) + 2 * (r ^ 2 * deriv Φ (r ^ 2)))) *
        r⁻¹ ^ 2 := by
      simp only [hf2]; field_simp; try ring
    have a1 : |2 * j * (r ^ 2 * deriv Φ (r ^ 2))| ≤ 2 * |j| * B := by
      rw [abs_mul, abs_mul, abs_two]; gcongr
    have a2 : |j * (4 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) + 2 * (r ^ 2 * deriv Φ (r ^ 2)))| ≤
        6 * |j| * B := by
      rw [abs_mul]
      have : |4 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) + 2 * (r ^ 2 * deriv Φ (r ^ 2))| ≤ 6 * B := by
        have h := abs_lin2 ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) (r ^ 2 * deriv Φ (r ^ 2)) 4 2
        rw [abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
        linarith
      nlinarith [abs_nonneg j]
    have c1 := abs_le_of_eq_mul e1 a1 hw
    have c2 := abs_le_of_eq_mul e2 a2 (by positivity)
    have hC0 : 0 ≤ 2 * |j| * B := by positivity
    have hC1 : 0 ≤ 4 * j ^ 2 * B ^ 2 := by positivity
    have hC2 : 0 ≤ 6 * |j| * B := by positivity
    refine ⟨?_, ?_, ?_⟩
    · rw [hnρ, pow_zero, mul_one]; linarith
    · rw [norm_mul, hnρ, one_mul, nI, zero_add, pow_one]
      nlinarith
    · have n1 : ‖ρ r * ((f1 r : ℂ) * Complex.I) * ((f1 r : ℂ) * Complex.I)‖ = |f1 r| * |f1 r| := by
        rw [norm_mul, norm_mul, hnρ, one_mul, nI]
      have n2 : ‖ρ r * ((f2 r : ℂ) * Complex.I)‖ = |f2 r| := by rw [norm_mul, hnρ, one_mul, nI]
      refine (norm_add_le _ _).trans ?_
      rw [n1, n2, zero_add]
      have hsq : |f1 r| * |f1 r| ≤ (2 * |j| * B) ^ 2 * r⁻¹ ^ 2 := by
        have := mul_le_mul c1 c1 (abs_nonneg _) (by positivity)
        nlinarith
      have : (2 * |j| * B) ^ 2 = 4 * j ^ 2 * B ^ 2 := by rw [mul_pow, mul_pow, sq_abs]; ring
      rw [this] at hsq
      have hw2 : 0 ≤ r⁻¹ ^ 2 := by positivity
      nlinarith

theorem slopeC_farDecay {Φ : ℝ → ℝ} (hΦ : IsRadialPhase Φ) :
    FarDecay 0 (fun y : Space => (((2 * ‖y‖ ^ 2 * deriv Φ (‖y‖ ^ 2) : ℝ)) : ℂ)) := by
  obtain ⟨B, hB⟩ := hΦ.scaled_bounded
  have hd := phase_derivs hΦ
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl).1
  set g1 : ℝ → ℝ := fun r => 4 * r * deriv Φ (r ^ 2) + 4 * r ^ 3 * iteratedDeriv 2 Φ (r ^ 2) with hg1
  set g2 : ℝ → ℝ := fun r => 4 * deriv Φ (r ^ 2) + 20 * r ^ 2 * iteratedDeriv 2 Φ (r ^ 2) +
    8 * r ^ 4 * iteratedDeriv 3 Φ (r ^ 2) with hg2
  refine radial_farDecay (ρ := fun r : ℝ => (((2 * r ^ 2 * deriv Φ (r ^ 2) : ℝ)) : ℂ))
    (ρ1 := fun r => ((g1 r : ℝ) : ℂ)) (ρ2 := fun r => ((g2 r : ℝ) : ℂ))
    (R0 := 1) (C := 1 + 32 * B) one_pos ?_ ?_ ?_
  · intro r hr
    have hs : 0 < r ^ 2 := by positivity
    have h := (((sq_hasDerivAt r).const_mul 2).mul (comp_sq (hd _ hs).2.1))
    exact (h.congr_deriv (by simp only [hg1]; ring)).ofReal_comp
  · intro r hr
    have hs : 0 < r ^ 2 := by positivity
    have hA := ((hasDerivAt_id' r).const_mul 4).mul (comp_sq (hd _ hs).2.1)
    have hB' := ((hasDerivAt_pow 3 r).const_mul 4).mul (comp_sq (hd _ hs).2.2)
    exact ((hA.add hB').congr_deriv (by simp only [hg2]; push_cast; ring)).ofReal_comp
  · intro r hr
    have hr0 : 0 < r := by linarith
    have hs : 0 ≤ r ^ 2 := by positivity
    obtain ⟨b1, b2, b3⟩ := hB (r ^ 2) hs
    have hw : 0 ≤ r⁻¹ := by positivity
    have hw1 : r⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hr.le
    have e0 : 2 * r ^ 2 * deriv Φ (r ^ 2) = 2 * (r ^ 2 * deriv Φ (r ^ 2)) * 1 := by ring
    have e1 : g1 r = (4 * (r ^ 2 * deriv Φ (r ^ 2)) + 4 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2))) * r⁻¹ := by
      simp only [hg1]; field_simp; try ring
    have e2 : g2 r = (4 * (r ^ 2 * deriv Φ (r ^ 2)) + 20 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) +
        8 * ((r ^ 2) ^ 3 * iteratedDeriv 3 Φ (r ^ 2))) * r⁻¹ ^ 2 := by
      simp only [hg2]; field_simp; try ring
    have a0 : |2 * (r ^ 2 * deriv Φ (r ^ 2))| ≤ 2 * B := by rw [abs_mul, abs_two]; linarith
    have a1 : |4 * (r ^ 2 * deriv Φ (r ^ 2)) + 4 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2))| ≤ 8 * B := by
      have h := abs_lin2 (r ^ 2 * deriv Φ (r ^ 2)) ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) 4 4
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4)] at h
      linarith
    have a2 : |4 * (r ^ 2 * deriv Φ (r ^ 2)) + 20 * ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2)) +
        8 * ((r ^ 2) ^ 3 * iteratedDeriv 3 Φ (r ^ 2))| ≤ 32 * B := by
      have h := abs_lin3 (r ^ 2 * deriv Φ (r ^ 2)) ((r ^ 2) ^ 2 * iteratedDeriv 2 Φ (r ^ 2))
        ((r ^ 2) ^ 3 * iteratedDeriv 3 Φ (r ^ 2)) 4 20 8
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 4), abs_of_pos (by norm_num : (0 : ℝ) < 20),
        abs_of_pos (by norm_num : (0 : ℝ) < 8)] at h
      linarith
    have c0 := abs_le_of_eq_mul e0 a0 zero_le_one
    have c1 := abs_le_of_eq_mul e1 a1 hw
    have c2 := abs_le_of_eq_mul e2 a2 (by positivity)
    refine ⟨?_, ?_, ?_⟩
    · rw [Complex.norm_real, Real.norm_eq_abs, pow_zero, mul_one]; linarith
    · rw [Complex.norm_real, Real.norm_eq_abs, zero_add, pow_one]; nlinarith
    · rw [Complex.norm_real, Real.norm_eq_abs, zero_add]
      have : 0 ≤ r⁻¹ ^ 2 := by positivity
      nlinarith

end Phase

section Key

def weightLow (e0 n : ℕ) (t : ℝ) : ℂ := ((t ^ e0 * (1 - t) ^ n : ℝ) : ℂ)

def weightDeriv (e0 e1 : ℕ) (t : ℝ) : ℝ :=
  (e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1) * (-1))

theorem wR_hasDerivAt (e0 e1 : ℕ) (t : ℝ) :
    HasDerivAt (fun t : ℝ => t ^ e0 * (1 - t) ^ e1) (weightDeriv e0 e1 t) t := by
  have h1 := hasDerivAt_pow e0 t
  have h2 := ((hasDerivAt_id' t).const_sub 1).pow e1
  exact h1.mul h2

theorem spline_t_hasDerivAt {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (t x : ℝ) : HasDerivAt (fun t' => S.evalHalf t' x) ((tDerivSpline S).evalHalf t x) t := by
  have hC := (SlopeRegular.spline hS ha hb).1
  have h2 : DifferentiableAt ℝ (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) (t, x) := (hC.differentiable one_ne_zero) _
  have hp : DifferentiableAt ℝ (fun t' : ℝ => (t', x)) t := differentiableAt_id.prodMk (differentiableAt_const x)
  have hd : DifferentiableAt ℝ ((fun z : ℝ × ℝ => S.evalHalf z.1 z.2) ∘ (fun t' : ℝ => (t', x))) t :=
    h2.comp (f := fun t' : ℝ => (t', x)) t hp
  have hd' : DifferentiableAt ℝ (fun t' => S.evalHalf t' x) t := hd
  have := hd'.hasDerivAt
  rwa [((splineDerivatives_holds a b S hS).1 ha).2 t x] at this

theorem spline_x_hasDerivAt {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (t x : ℝ) : HasDerivAt (fun x' => S.evalHalf t x') ((xDerivSpline S).evalHalf t x) x := by
  have hC := (SlopeRegular.spline hS ha hb).1
  have h2 : DifferentiableAt ℝ (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) (t, x) := (hC.differentiable one_ne_zero) _
  have hp : DifferentiableAt ℝ (fun x' : ℝ => (t, x')) x := (differentiableAt_const t).prodMk differentiableAt_id
  have hd : DifferentiableAt ℝ ((fun z : ℝ × ℝ => S.evalHalf z.1 z.2) ∘ (fun x' : ℝ => (t, x'))) x :=
    h2.comp (f := fun x' : ℝ => (t, x')) x hp
  have hd' : DifferentiableAt ℝ (fun x' => S.evalHalf t x') x := hd
  have := hd'.hasDerivAt
  rwa [((splineDerivatives_holds a b S hS).2 hb).2 t x] at this

theorem realC_reg {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 2 f) : SlopeRegular (fun z => ((f z : ℝ) : ℂ)) :=
  SlopeRegular.of_contDiff (Complex.ofRealCLM.contDiff.comp hf)

theorem const_reg (c : ℂ) : SlopeRegular (fun _ : ℝ × ℝ => c) := SlopeRegular.of_contDiff contDiff_const

theorem vT_reg (e0 n : ℕ) : SlopeRegular (fun z : ℝ × ℝ => weightLow e0 n z.1) :=
  realC_reg (f := fun z : ℝ × ℝ => z.1 ^ e0 * (1 - z.1) ^ n) (by fun_prop)

def radialPart (A : KeyAmp) (e0 n : ℕ) (z : ℝ × ℝ) : ℂ := weightLow e0 n z.1 * A.radial.evalHalf z.1 z.2

def polarPart (A : KeyAmp) (e0 n : ℕ) (z : ℝ × ℝ) : ℂ := weightLow e0 n z.1 * A.polar.evalHalf z.1 z.2

def azimPart (A : KeyAmp) (e0 n : ℕ) (kc : ℂ) (z : ℝ × ℝ) : ℂ :=
  Complex.I / kc * (((z.1 * weightDeriv e0 (n + 1) z.1 : ℝ) : ℂ) * A.radial.evalHalf z.1 z.2 +
    ((z.1 * (z.1 ^ e0 * (1 - z.1) ^ (n + 1)) : ℝ) : ℂ) * (tDerivSpline A.radial).evalHalf z.1 z.2 +
    2 * weightLow e0 n z.1 * A.radial.evalHalf z.1 z.2 +
    ((6 * z.2 : ℝ) : ℂ) * weightLow e0 n z.1 * A.polar.evalHalf z.1 z.2 +
    ((-(1 - z.2 ^ 2) : ℝ) : ℂ) * weightLow e0 n z.1 * (xDerivSpline A.polar).evalHalf z.1 z.2)

def azimSlopePart (A : KeyAmp) (e0 n : ℕ) (kc jc : ℂ) (z : ℝ × ℝ) : ℂ :=
  Complex.I / kc * (Complex.I * jc * weightLow e0 n z.1 * A.radial.evalHalf z.1 z.2)

theorem parts_regular (A : KeyAmp) (e0 n : ℕ) (kc jc : ℂ) (hR : IsJoinedSpline 2 1 A.radial)
    (hP : IsJoinedSpline 1 2 A.polar) :
    SlopeRegular (radialPart A e0 n) ∧ SlopeRegular (polarPart A e0 n) ∧ SlopeRegular (azimPart A e0 n kc) ∧ SlopeRegular (azimSlopePart A e0 n kc jc) := by
  have sR := SlopeRegular.spline hR (by norm_num) (by norm_num)
  have sP := SlopeRegular.spline hP (by norm_num) (by norm_num)
  have sRt := SlopeRegular.spline ((splineDerivatives_holds 2 1 A.radial hR).1 (by norm_num)).1 (by norm_num) (by norm_num)
  have sPx := SlopeRegular.spline ((splineDerivatives_holds 1 2 A.polar hP).2 (by norm_num)).1 (by norm_num) (by norm_num)
  have v := vT_reg e0 n
  refine ⟨SlopeRegular.mul v sR, SlopeRegular.mul v sP, ?_, ?_⟩
  · have t1 := SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => z.1 * weightDeriv e0 (n + 1) z.1)
      (by unfold weightDeriv; fun_prop)) sR
    have t2 := SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => z.1 * (z.1 ^ e0 * (1 - z.1) ^ (n + 1)))
      (by fun_prop)) sRt
    have t3 := SlopeRegular.mul (SlopeRegular.mul (const_reg 2) v) sR
    have t4 := SlopeRegular.mul (SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => 6 * z.2) (by fun_prop)) v) sP
    have t5 := SlopeRegular.mul (SlopeRegular.mul (realC_reg (f := fun z : ℝ × ℝ => -(1 - z.2 ^ 2)) (by fun_prop)) v) sPx
    exact SlopeRegular.mul (const_reg _) ((((t1.add t2).add t3).add t4).add t5)
  · exact SlopeRegular.mul (const_reg _) (SlopeRegular.mul (SlopeRegular.mul (const_reg _) v) sR)

theorem R0_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (t x : ℝ) :
    reducedComps P κ A t x 0 = axisFactor x * (((1 - t : ℝ)) : ℂ) * radialPart A A.lowOrder n (t, x) := by
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_zero, radialPart, weightLow, weightPoly, hn, axisFactor]
  push_cast
  ring

theorem R1_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (t x : ℝ) :
    reducedComps P κ A t x 1 = axisFactor x * (((1 - t : ℝ)) : ℂ) * polarPart A A.lowOrder n (t, x) := by
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_one, Matrix.head_cons, polarPart, weightLow, weightPoly, hn, axisFactor]
  push_cast
  ring

theorem R2_eq (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h1 : κ.label.1 ≠ 0) (n : ℕ)
    (hn : A.highOrder = n + 1) (hR : IsJoinedSpline 2 1 A.radial) (hP : IsJoinedSpline 1 2 A.polar)
    (t x : ℝ) :
    reducedComps P κ A t x 2 = axisFactor x * (((1 - t : ℝ)) : ℂ) *
      (azimPart A A.lowOrder n (labelAzimuth P.azimuthOrder κ.label : ℂ) (t, x) +
        ((phaseSlope P t : ℝ) : ℂ) * azimSlopePart A A.lowOrder n (labelAzimuth P.azimuthOrder κ.label : ℂ)
          (κ.phaseIndex : ℂ) (t, x)) := by
  have hdt : HasDerivAt (fun t' => weightPoly A.lowOrder A.highOrder t' * axisFactor x * A.radial.evalHalf t' x)
      (((weightDeriv A.lowOrder A.highOrder t : ℝ) : ℂ) * axisFactor x * A.radial.evalHalf t x +
        weightPoly A.lowOrder A.highOrder t * axisFactor x * (tDerivSpline A.radial).evalHalf t x) t :=
    (((wR_hasDerivAt A.lowOrder A.highOrder t).ofReal_comp).mul_const (axisFactor x)).mul
      (spline_t_hasDerivAt hR (by norm_num) (by norm_num) t x)
  have hpf : HasDerivAt (fun x' : ℝ => polarFactor x') (((-(2 * x)) : ℝ) : ℂ) x :=
    ((sq_hasDerivAt x).const_sub 1).ofReal_comp
  have haf : HasDerivAt (fun x' : ℝ => axisFactor x') (((2 * (1 - x ^ 2) * (-(2 * x))) : ℝ) : ℂ) x :=
    ((((sq_hasDerivAt x).const_sub 1).pow 2).congr_deriv (by norm_num)).ofReal_comp
  have hdx : HasDerivAt (fun x' => polarFactor x' *
      (weightPoly A.lowOrder A.highOrder t * axisFactor x' * A.polar.evalHalf t x'))
      ((((-(2 * x)) : ℝ) : ℂ) * (weightPoly A.lowOrder A.highOrder t * axisFactor x * A.polar.evalHalf t x) +
        polarFactor x * (weightPoly A.lowOrder A.highOrder t * (((2 * (1 - x ^ 2) * (-(2 * x))) : ℝ) : ℂ) *
          A.polar.evalHalf t x + weightPoly A.lowOrder A.highOrder t * axisFactor x *
            (xDerivSpline A.polar).evalHalf t x)) x :=
    hpf.mul ((haf.const_mul _).mul (spline_x_hasDerivAt hP (by norm_num) (by norm_num) t x))
  rw [reducedComps, if_neg h1]
  dsimp only
  simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, shiftedScale, radialScale, heightDeriv]
  rw [hdt.deriv, hdx.deriv]
  simp only [azimPart, azimSlopePart, weightLow, weightPoly, hn, axisFactor, polarFactor]
  push_cast
  ring

end Key

section Assembly

theorem abs_heightRatio_le' (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  by_cases hy : ‖y‖ = 0
  · simp [hy]
  have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
  rw [abs_div, abs_of_pos hp, div_le_one hp]
  have h : (y 2) ^ 2 ≤ ‖y‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp only [Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
  exact abs_le_of_sq_le_sq' h hp.le |> fun h' => abs_le.2 h'

theorem chartCoord_eq (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    chartCoord P y = 1 - P.chartLength * (‖y‖ + P.chartLength)⁻¹ := by
  unfold chartCoord
  have : 0 < ‖y‖ + P.chartLength := by positivity
  field_simp
  ring

theorem one_sub_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    1 - chartCoord P y = P.chartLength * (‖y‖ + P.chartLength)⁻¹ := by
  rw [chartCoord_eq P hL]; ring

theorem phaseSlope_chartCoord (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    phaseSlope P (chartCoord P y) = 2 * ‖y‖ ^ 2 * deriv P.radialPhase (‖y‖ ^ 2) := by
  have h : chartRadius P (chartCoord P y) = ‖y‖ := by
    unfold chartRadius chartCoord
    have : 0 < ‖y‖ + P.chartLength := by positivity
    have h1 : 1 - ‖y‖ / (‖y‖ + P.chartLength) = P.chartLength / (‖y‖ + P.chartLength) := by
      field_simp; ring
    rw [h1]
    field_simp
  rw [phaseSlope, h]

theorem keyPhase_eq (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) :
    keyPhase P κ σ y = Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
      (Complex.exp (((((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) * pointAngle y : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) := by
  unfold keyPhase
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem chartPair_farDecay (P : ShapeParams) (hL : 0 < P.chartLength) :
    FarDecay 0 (fun y : Space => (chartCoord P y, heightRatio y)) := by
  have h := FarDecay.prod (chartC_farDecay hL) heightRatio_farDecay
  have e : (fun y : Space => (chartCoord P y, heightRatio y)) =
      fun z : Space => ((1 - P.chartLength * (‖z‖ + P.chartLength)⁻¹ : ℝ), heightRatio z) := by
    funext z
    rw [chartCoord_eq P hL]
  rw [e]
  exact h

theorem chartPair_mem (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    (chartCoord P y, heightRatio y) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le ?_ (abs_heightRatio_le' y)
  unfold chartCoord
  have : 0 < ‖y‖ + P.chartLength := by positivity
  rw [abs_of_nonneg (by positivity), div_le_one this]
  linarith

end Assembly

section Conclusion

theorem key_farDecay (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (A : KeyAmp) (σ : ℝ)
    (h1 : κ.label.1 ≠ 0) (n : ℕ) (hn : A.highOrder = n + 1) (hR : IsJoinedSpline 2 1 A.radial)
    (hPo : IsJoinedSpline 1 2 A.polar) : FarDecay 1 (keyVector P κ A σ) := by
  have hL := hP.chartLength_pos
  set k : ℤ := labelAzimuth P.azimuthOrder κ.label with hk
  set kc : ℂ := (labelAzimuth P.azimuthOrder κ.label : ℂ) with hkc
  set jc : ℂ := (κ.phaseIndex : ℂ) with hjc
  set e0 := A.lowOrder with he0
  set cσ : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hcσ
  obtain ⟨r0, r1, r2, r3⟩ := parts_regular A e0 n kc jc hR hPo
  have hφ := chartPair_farDecay P hL
  have hm := chartPair_mem P hL
  have g0 := FarDecay.comp hφ hm r0
  have g1 := FarDecay.comp hφ hm r1
  have g2 := FarDecay.comp hφ hm r2
  have g3 := FarDecay.comp hφ hm r3
  have hT1 := FarDecay.smul g0 radialC_farDecay rfl
  have hT2 := FarDecay.smul g1 polarC_farDecay rfl
  have hT3a := FarDecay.smul (slopeC_farDecay hP.phase) g3 rfl
  have hT3 := FarDecay.smul (FarDecay.add g2 hT3a) azimC_farDecay rfl
  have hS := FarDecay.add (FarDecay.add hT1 hT2) hT3
  have hTS := FarDecay.smul (tailC_farDecay hL) hS rfl
  have hPh := FarDecay.smul (phaseC_farDecay hP.phase (κ.phaseIndex : ℝ)) hTS rfl
  have hAn := FarDecay.smul (angularC_farDecay k) hPh rfl
  have hAll := FarDecay.smul (FarDecay.const cσ) hAn rfl
  convert hAll using 1
  funext y
  funext i
  simp only [keyVector, Pi.smul_apply, Pi.add_apply, smul_eq_mul, radialC, polarC, azimC, angularC]
  rw [keyPhase_eq, R0_eq P κ A h1 n hn, R1_eq P κ A h1 n hn, R2_eq P κ A h1 n hn hR hPo,
    one_sub_chartCoord P hL, phaseSlope_chartCoord P hL]
  ring

theorem decay_of_farDecay {f : Space → Fin 3 → ℂ} (hs : IsKeyFieldSmooth f) (hf : FarDecay 1 f) : IsKeyFieldDecay f := by
  obtain ⟨Cf, Rf, hCf, hRf, hfar⟩ := hf.bounds
  obtain ⟨Cn, hnear⟩ := hs.bounded_on_ball Rf
  set K : ℝ := |Cn| * (1 + Rf) ^ 3 + 8 * Cf with hK
  refine ⟨⟨K, fun y => ?_⟩⟩
  set Y := ‖y‖ with hY
  have hY0 : 0 ≤ Y := norm_nonneg _
  have key : ∀ (a : ℝ) (k : ℕ), k ≤ 3 → (Y ≤ Rf → a ≤ Cn) → (Rf ≤ Y → a ≤ Cf * Y⁻¹ ^ k) →
      a ≤ K / (1 + Y) ^ k := by
    intro a k hk hn hf'
    rw [le_div_iff₀ (by positivity)]
    rcases le_total Y Rf with h | h
    · have ha : a ≤ |Cn| := (hn h).trans (le_abs_self Cn)
      have p1 : (1 + Y) ^ k ≤ (1 + Rf) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      have p2 : (1 + Rf) ^ k ≤ (1 + Rf) ^ 3 := pow_le_pow_right₀ (by linarith) hk
      have p0 : 0 ≤ (1 + Y) ^ k := by positivity
      have h8 : 0 ≤ 8 * Cf := by positivity
      calc a * (1 + Y) ^ k ≤ |Cn| * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
        _ ≤ |Cn| * (1 + Rf) ^ 3 := mul_le_mul_of_nonneg_left (p1.trans p2) (abs_nonneg _)
        _ ≤ K := by rw [hK]; linarith
    · have hY1 : 1 ≤ Y := hRf.trans h
      have hYp : 0 < Y := by linarith
      have ha := hf' h
      have p0 : 0 ≤ (1 + Y) ^ k := by positivity
      have e : Y⁻¹ ^ k * (1 + Y) ^ k = ((1 + Y) * Y⁻¹) ^ k := by rw [mul_pow]; ring
      have q : (1 + Y) * Y⁻¹ ≤ 2 := by
        rw [← div_eq_mul_inv, div_le_iff₀ hYp]; linarith
      have q2 : ((1 + Y) * Y⁻¹) ^ k ≤ 8 := by
        calc ((1 + Y) * Y⁻¹) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) q k
          _ ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
          _ = 8 := by norm_num
      have hn0 : 0 ≤ |Cn| * (1 + Rf) ^ 3 := by
        have : 0 ≤ 1 + Rf := by linarith
        positivity
      calc a * (1 + Y) ^ k ≤ Cf * Y⁻¹ ^ k * (1 + Y) ^ k := mul_le_mul_of_nonneg_right ha p0
        _ = Cf * ((1 + Y) * Y⁻¹) ^ k := by rw [mul_assoc, e]
        _ ≤ Cf * 8 := mul_le_mul_of_nonneg_left q2 hCf
        _ ≤ K := by rw [hK]; linarith
  refine ⟨?_, ?_, ?_⟩
  · have := key ‖f y‖ 1 (by norm_num) (fun h => (hnear y h).1) (fun h => (hfar y h).1)
    rwa [pow_one] at this
  · exact key _ 2 (by norm_num) (fun h => (hnear y h).2.1) (fun h => (hfar y h).2.1)
  · exact key _ 3 (by norm_num) (fun h => (hnear y h).2.2) (fun h => (hfar y h).2.2)

end Conclusion

end Internal.KeyDecay

theorem typeOneKeyDecay_of_smooth (hsm : TypeOneKeySmooth) : TypeOneKeyDecay := by
  intro P D κ σ hP hD hκ h1
  have hpos := hD.highOrder_pos κ hκ
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (D.amp κ).highOrder = n + 1 := ⟨(D.amp κ).highOrder - 1, by omega⟩
  exact Internal.KeyDecay.decay_of_farDecay (hsm P D κ σ hP hD hκ h1)
    (Internal.KeyDecay.key_farDecay P hP κ (D.amp κ) σ h1 n hn (hD.radial_class κ hκ h1) (hD.polar_class κ hκ h1))

end GivenShape

end CertCell

end Breakdown

import Breakdown.CellReduction.InstMovedSmoothFactor
import Breakdown.CertCell.CellLayerClosed

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal.MovedDecay

open CertCell.GivenShape.Internal (BallBound SlopeOn slopeOn_of_fderiv FarBound ball_norm_near)

theorem radialPhase_bounds {X : ℝ → ℝ} (hX : IsRadialPhase X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℝ, 0 ≤ s → HasDerivAt X (deriv X s) s ∧
      HasDerivAt (deriv X) (deriv (deriv X) s) s ∧
      |deriv X s| * (1 + s) ≤ K ∧ |deriv (deriv X) s| * (1 + s) ^ 2 ≤ K := by
  obtain ⟨δ, hδ, hC⟩ := hX.smooth
  obtain ⟨B, hB⟩ := hX.scaled_bounded
  have hs : IsOpen (Set.Ioi (-δ)) := isOpen_Ioi
  have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
  have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  have h3 : ContDiffOn ℝ (2 + 1) X (Set.Ioi (-δ)) := by rw [e3]; exact hC
  obtain ⟨d0, -, h2⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hs).1 h3
  have h2' : ContDiffOn ℝ (1 + 1) (deriv X) (Set.Ioi (-δ)) := by rw [e2]; exact h2
  obtain ⟨d1, -, h1⟩ := (contDiffOn_succ_iff_deriv_of_isOpen hs).1 h2'
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0 le_rfl).1
  have i2 : iteratedDeriv 2 X = deriv (deriv X) := by rw [iteratedDeriv_succ, iteratedDeriv_one]
  have hsub : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioi (-δ) := fun x hx => by
    show -δ < x
    linarith [hx.1]
  obtain ⟨c1, hc1⟩ := isCompact_Icc.exists_bound_of_continuousOn (h2.continuousOn.mono hsub)
  obtain ⟨c2, hc2⟩ := isCompact_Icc.exists_bound_of_continuousOn (h1.continuousOn.mono hsub)
  have a1 := abs_nonneg c1
  have a2 := abs_nonneg c2
  refine ⟨4 * (|c1| + |c2| + B), by positivity, fun s hs0 => ?_⟩
  have hsU : s ∈ Set.Ioi (-δ) := by
    show -δ < s
    linarith
  refine ⟨((d0 s hsU).differentiableAt (hs.mem_nhds hsU)).hasDerivAt,
    ((d1 s hsU).differentiableAt (hs.mem_nhds hsU)).hasDerivAt, ?_, ?_⟩
  · obtain ⟨b1, -, -⟩ := hB s hs0
    have hX1 := abs_nonneg (deriv X s)
    rcases le_total s 1 with h | h
    · have hc := hc1 s ⟨hs0, h⟩
      rw [Real.norm_eq_abs] at hc
      have hc' : |deriv X s| ≤ |c1| := hc.trans (le_abs_self _)
      have := mul_le_mul hc' (show 1 + s ≤ 2 by linarith) (by linarith) a1
      linarith
    · rw [abs_mul, abs_of_nonneg hs0] at b1
      have := mul_le_mul_of_nonneg_left h hX1
      nlinarith
  · obtain ⟨-, b2, -⟩ := hB s hs0
    rw [i2] at b2
    have hX2 := abs_nonneg (deriv (deriv X) s)
    rcases le_total s 1 with h | h
    · have hc := hc2 s ⟨hs0, h⟩
      rw [Real.norm_eq_abs] at hc
      have hc' : |deriv (deriv X) s| ≤ |c2| := hc.trans (le_abs_self _)
      have hp : (1 + s) ^ 2 ≤ 4 := by nlinarith
      have := mul_le_mul hc' hp (by positivity) a2
      linarith
    · rw [abs_mul, abs_of_nonneg (sq_nonneg s)] at b2
      have hp : (1 + s) ^ 2 ≤ 4 * s ^ 2 := by nlinarith
      have := mul_le_mul_of_nonneg_left hp hX2
      nlinarith

theorem norm_innerSL_le : ‖(innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [innerSL_apply_norm, one_mul]

theorem normSq_hasFDerivAt (z : Space) :
    HasFDerivAt (fun x : Space => ‖x‖ ^ 2) ((2 : ℝ) • innerSL ℝ z) z :=
  (hasStrictFDerivAt_norm_sq z).hasFDerivAt.congr_fderiv (by ext v; simp)

def phaseGrad (X : ℝ → ℝ) (x : Space) : Space →L[ℝ] ℝ := (2 * deriv X (‖x‖ ^ 2)) • innerSL ℝ x

theorem phaseSq_bounds {X : ℝ → ℝ} (hX : IsRadialPhase X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : Space,
      HasFDerivAt (fun x : Space => X (‖x‖ ^ 2)) (phaseGrad X z) z ∧
      DifferentiableAt ℝ (phaseGrad X) z ∧
      ‖phaseGrad X z‖ * (1 + ‖z‖) ≤ K ∧ ‖fderiv ℝ (phaseGrad X) z‖ * (1 + ‖z‖) ^ 2 ≤ K := by
  obtain ⟨K0, hK0, h⟩ := radialPhase_bounds hX
  refine ⟨16 * K0, by positivity, fun z => ?_⟩
  obtain ⟨d1, d2, b1, b2⟩ := h (‖z‖ ^ 2) (sq_nonneg _)
  have hN := normSq_hasFDerivAt z
  have hΦ : HasFDerivAt (fun x : Space => X (‖x‖ ^ 2)) (phaseGrad X z) z := by
    have := d1.comp_hasFDerivAt z hN
    refine this.congr_fderiv ?_
    ext v
    simp [phaseGrad]
    ring
  have hg0 := d2.comp_hasFDerivAt z hN
  have hg := hg0.const_mul (2 : ℝ)
  have hL : HasFDerivAt (fun x : Space => innerSL ℝ x) (innerSL ℝ) z := (innerSL ℝ).hasFDerivAt
  have hP := hg.smul hL
  have hPd : HasFDerivAt (phaseGrad X) _ z := hP
  set r := ‖z‖ with hr
  have hr0 : 0 ≤ r := norm_nonneg z
  set u := |deriv X (r ^ 2)|
  set w := |deriv (deriv X) (r ^ 2)|
  have hu : 0 ≤ u := abs_nonneg _
  have hw : 0 ≤ w := abs_nonneg _
  have nG : ‖phaseGrad X z‖ = 2 * u * r := by
    rw [phaseGrad, norm_smul, innerSL_apply_norm, Real.norm_eq_abs, abs_mul, abs_two]
  have q1 : r * (1 + r) ≤ 2 * (1 + r ^ 2) := by nlinarith [sq_nonneg (r - 1)]
  have q2 : (1 + r) ^ 2 ≤ 2 * (1 + r ^ 2) := by nlinarith [sq_nonneg (r - 1)]
  refine ⟨hΦ, hPd.differentiableAt, ?_, ?_⟩
  · rw [nG]
    have := mul_le_mul_of_nonneg_left q1 hu
    nlinarith
  · have t : ‖fderiv ℝ (phaseGrad X) z‖ ≤ 2 * u + 4 * w * r ^ 2 := by
      rw [hPd.fderiv]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_two]
        exact mul_le_of_le_one_right (by positivity) norm_innerSL_le
      · rw [ContinuousLinearMap.norm_smulRight_apply, norm_smul, norm_smul, norm_smul, innerSL_apply_norm,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_two]
        show 2 * (w * (2 * r)) * r ≤ 4 * w * r ^ 2
        exact le_of_eq (by ring)
    have p0 : 0 ≤ (1 + r) ^ 2 := by positivity
    have s1 := mul_le_mul_of_nonneg_right t p0
    have s2 : (2 * u + 4 * w * r ^ 2) * (1 + r) ^ 2 ≤ (2 * u + 4 * w * r ^ 2) * (2 * (1 + r ^ 2)) :=
      mul_le_mul_of_nonneg_left q2 (by positivity)
    have s3 : w * r ^ 2 * (1 + r ^ 2) ≤ w * (1 + r ^ 2) ^ 2 := by
      have : r ^ 2 * (1 + r ^ 2) ≤ (1 + r ^ 2) ^ 2 := by nlinarith
      nlinarith
    nlinarith

theorem inv_le_of_ball {y z : Space} (hz : z ∈ Metric.ball y 1) : (1 + ‖z‖)⁻¹ ≤ 2 * (1 + ‖y‖)⁻¹ := by
  have h := (ball_norm_near hz).1
  have hz0 := norm_nonneg z
  rw [← div_eq_mul_inv, inv_eq_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

theorem le_mul_inv_of {x K c : ℝ} (hc : 0 < c) (h : x * c ≤ K) : x ≤ K * c⁻¹ := by
  rw [← div_eq_mul_inv, le_div_iff₀ hc]
  exact h

theorem phase_ballBound {X : ℝ → ℝ} (hX : IsRadialPhase X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : Space, ∃ v : ℝ, BallBound (fun x : Space => X (‖x‖ ^ 2)) y v
      (K * (1 + ‖y‖)⁻¹) (K * (1 + ‖y‖)⁻¹ ^ 2) := by
  obtain ⟨K, hK, h⟩ := phaseSq_bounds hX
  have hd : ∀ z, fderiv ℝ (fun x : Space => X (‖x‖ ^ 2)) z = phaseGrad X z := fun z => (h z).1.fderiv
  have hcont : Continuous (fun x : Space => X (‖x‖ ^ 2)) :=
    (show Differentiable ℝ (fun x : Space => X (‖x‖ ^ 2)) from fun z => (h z).1.differentiableAt).continuous
  refine ⟨4 * K, by positivity, fun y => ?_⟩
  obtain ⟨v, hv⟩ := (isCompact_closedBall y 1).exists_bound_of_continuousOn hcont.continuousOn
  have hy0 : 0 < 1 + ‖y‖ := by positivity
  have hw0 : 0 < (1 + ‖y‖)⁻¹ := inv_pos.2 hy0
  refine ⟨v, fun z _ => (h z).1.differentiableAt, fun z hz => hv z (Metric.ball_subset_closedBall hz),
    fun z hz => ?_, ?_⟩
  · rw [hd z]
    have h1 := le_mul_inv_of (by positivity) (h z).2.2.1
    have h2 := inv_le_of_ball hz
    calc ‖phaseGrad X z‖ ≤ K * (1 + ‖z‖)⁻¹ := h1
      _ ≤ K * (2 * (1 + ‖y‖)⁻¹) := mul_le_mul_of_nonneg_left h2 hK
      _ ≤ 4 * K * (1 + ‖y‖)⁻¹ := by nlinarith
  · have hs : SlopeOn (phaseGrad X) (4 * K * (1 + ‖y‖)⁻¹ ^ 2) (Metric.ball y 1) := by
      refine slopeOn_of_fderiv (fun z _ => (h z).2.1) fun z hz => ?_
      have h1 := le_mul_inv_of (by positivity) (h z).2.2.2
      have h2 := inv_le_of_ball hz
      have h3 : ((1 + ‖z‖) ^ 2)⁻¹ ≤ 4 * ((1 + ‖y‖)⁻¹) ^ 2 := by
        rw [← inv_pow]
        have : 0 ≤ (1 + ‖z‖)⁻¹ := by positivity
        calc ((1 + ‖z‖)⁻¹) ^ 2 ≤ (2 * (1 + ‖y‖)⁻¹) ^ 2 := pow_le_pow_left₀ this h2 2
          _ = 4 * ((1 + ‖y‖)⁻¹) ^ 2 := by ring
      calc ‖fderiv ℝ (phaseGrad X) z‖ ≤ K * ((1 + ‖z‖) ^ 2)⁻¹ := h1
        _ ≤ K * (4 * ((1 + ‖y‖)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left h3 hK
        _ = 4 * K * (1 + ‖y‖)⁻¹ ^ 2 := by ring
    exact hs.congr fun z _ => hd z

theorem expLine_hasDerivAt (β u : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (((β * u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) * ((β : ℂ) * Complex.I)) u := by
  have h1 : HasDerivAt (fun u : ℝ => (((β * u : ℝ) : ℂ) * Complex.I)) ((β : ℂ) * Complex.I) u := by
    have := (((hasDerivAt_id u).const_mul β).ofReal_comp).mul_const Complex.I
    simpa using this
  exact h1.cexp

theorem expPhase_ballBound {X : ℝ → ℝ} (hX : IsRadialPhase X) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℂ) (β : ℝ) (y : Space),
      BallBound (fun x : Space => α * Complex.exp (((β * X (‖x‖ ^ 2) : ℝ) : ℂ) * Complex.I)) y ‖α‖
        (‖α‖ * |β| * (K * (1 + ‖y‖)⁻¹))
        (‖α‖ * |β| ^ 2 * (K * (1 + ‖y‖)⁻¹) * (K * (1 + ‖y‖)⁻¹) + ‖α‖ * |β| * (K * (1 + ‖y‖)⁻¹ ^ 2)) := by
  obtain ⟨K, hK, h⟩ := phase_ballBound hX
  refine ⟨K, hK, fun α β y => ?_⟩
  obtain ⟨v, hv⟩ := h y
  have nE : ∀ u : ℝ, ‖Complex.exp (((β * u : ℝ) : ℂ) * Complex.I)‖ = 1 := fun u =>
    Complex.norm_exp_ofReal_mul_I _
  have nbI : ‖(β : ℂ) * Complex.I‖ = |β| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hgd : ∀ u : ℝ, HasDerivAt (fun u : ℝ => α * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I))
      (α * (Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) * ((β : ℂ) * Complex.I))) u := fun u =>
    (expLine_hasDerivAt β u).const_mul α
  have hf : ∀ u : ℝ, fderiv ℝ (fun u : ℝ => α * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I)) u =
      (1 : ℝ →L[ℝ] ℝ).smulRight (α * (Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) * ((β : ℂ) * Complex.I))) :=
    fun u => (hgd u).hasFDerivAt.fderiv
  have slopeE : ∀ u u' : ℝ, ‖Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) - Complex.exp (((β * u' : ℝ) : ℂ) * Complex.I)‖
      ≤ |β| * ‖u - u'‖ := fun u u' =>
    (convex_univ).norm_image_sub_le_of_norm_deriv_le (fun x _ => (expLine_hasDerivAt β x).differentiableAt)
      (fun x _ => by rw [(expLine_hasDerivAt β x).deriv, norm_mul, nE, nbI, one_mul]) (Set.mem_univ u') (Set.mem_univ u)
  have n1 : ‖(1 : ℝ →L[ℝ] ℝ)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hα := norm_nonneg α
  have hβ := abs_nonneg β
  refine hv.comp (K := Set.univ) (g := fun u : ℝ => α * Complex.exp (((β * u : ℝ) : ℂ) * Complex.I))
    (fun _ _ => Set.mem_univ _) (fun u _ => (hgd u).differentiableAt) (fun u _ => ?_) (fun u _ => ?_)
    (by positivity : 0 ≤ ‖α‖ * |β| ^ 2) (fun u _ u' _ => ?_)
  · rw [norm_mul, nE, mul_one]
  · rw [hf u, ContinuousLinearMap.norm_smulRight_apply, norm_mul, norm_mul, nE, nbI, one_mul]
    exact mul_le_of_le_one_left (by positivity) n1
  · rw [hf u, hf u']
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_
    simp only [FunLike.coe_sub, Pi.sub_apply, ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
    rw [← smul_sub, norm_smul]
    have e : α * (Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) * ((β : ℂ) * Complex.I)) -
        α * (Complex.exp (((β * u' : ℝ) : ℂ) * Complex.I) * ((β : ℂ) * Complex.I)) =
        (α * ((β : ℂ) * Complex.I)) * (Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((β * u' : ℝ) : ℂ) * Complex.I)) := by ring
    rw [e, norm_mul, norm_mul, nbI]
    have l := slopeE u u'
    have ht := norm_nonneg t
    have hu := norm_nonneg (u - u')
    calc ‖t‖ * (‖α‖ * |β| * ‖Complex.exp (((β * u : ℝ) : ℂ) * Complex.I) -
          Complex.exp (((β * u' : ℝ) : ℂ) * Complex.I)‖) ≤ ‖t‖ * (‖α‖ * |β| * (|β| * ‖u - u'‖)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left l (by positivity)) ht
      _ = ‖α‖ * |β| ^ 2 * ‖u - u'‖ * ‖t‖ := by ring

theorem le_of_near {c S N R r : ℝ} {k : ℕ} (hk : k ≤ 3) (hr0 : 0 ≤ r) (hr : r ≤ R) (hS : 0 ≤ S)
    (hc : c ≤ S) (hN : S * (1 + R) ^ 3 ≤ N) : c ≤ N * ((1 + r)⁻¹) ^ k := by
  rw [inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : (1 + r) ^ k ≤ (1 + R) ^ 3 :=
    (pow_le_pow_left₀ (by positivity) (by linarith) k).trans (pow_le_pow_right₀ (by linarith) hk)
  calc c * (1 + r) ^ k ≤ S * (1 + r) ^ k := mul_le_mul_of_nonneg_right hc (by positivity)
    _ ≤ S * (1 + R) ^ 3 := mul_le_mul_of_nonneg_left h1 hS
    _ ≤ N := hN

theorem le_of_far {M N r : ℝ} {k : ℕ} (hk : k ≤ 3) (hr : 1 ≤ r) (hM : 0 ≤ M) (hN : 8 * M ≤ N) :
    M / r ^ k ≤ N * ((1 + r)⁻¹) ^ k := by
  have hr0 : 0 < r := by linarith
  rw [inv_pow, ← div_eq_mul_inv, div_le_div_iff₀ (by positivity) (by positivity)]
  have h2 : (2 : ℝ) ^ k ≤ 8 := by
    calc (2 : ℝ) ^ k ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) hk
      _ = 8 := by norm_num
  have h1 : (1 + r) ^ k ≤ 8 * r ^ k :=
    calc (1 + r) ^ k ≤ (2 * r) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * r ^ k := mul_pow _ _ _
      _ ≤ 8 * r ^ k := mul_le_mul_of_nonneg_right h2 (by positivity)
  calc M * (1 + r) ^ k ≤ M * (8 * r ^ k) := mul_le_mul_of_nonneg_left h1 hM
    _ = 8 * M * r ^ k := by ring
    _ ≤ N * r ^ k := mul_le_mul_of_nonneg_right hN (by positivity)

theorem ballBound_global {f : Space → Fin 3 → ℂ} (hs : IsKeyFieldSmooth f) (hf : FarBound f 1) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ y : Space,
      BallBound f y (N * (1 + ‖y‖)⁻¹) (N * (1 + ‖y‖)⁻¹ ^ 2) (N * (1 + ‖y‖)⁻¹ ^ 3) := by
  obtain ⟨M, R, hM, hR, hfar⟩ := hf
  have hK : IsCompact (Metric.closedBall (0 : Space) (R + 1)) := isCompact_closedBall 0 (R + 1)
  obtain ⟨C₀, hC₀⟩ := hK.exists_bound_of_continuousOn hs.smooth.continuous.continuousOn
  obtain ⟨C₁, hC₁⟩ := hK.exists_bound_of_continuousOn (hs.smooth.continuous_fderiv one_ne_zero).continuousOn
  obtain ⟨L, hL⟩ := hs.gradient_slope_bound (R + 1)
  have hdiff : Differentiable ℝ f := hs.smooth.differentiable one_ne_zero
  have hS : 0 ≤ |C₀| + |C₁| + (L : ℝ) := by positivity
  have hS3 : 0 ≤ (|C₀| + |C₁| + (L : ℝ)) * (1 + R) ^ 3 := by
    have : 0 ≤ 1 + R := by linarith
    positivity
  refine ⟨(|C₀| + |C₁| + (L : ℝ)) * (1 + R) ^ 3 + 8 * M, by positivity, fun y => ?_⟩
  have hy0 := norm_nonneg y
  rcases le_or_gt R ‖y‖ with hy | hy
  · have hb := hfar y hy
    have h1 : (1 : ℝ) ≤ ‖y‖ := by linarith
    have hN : 8 * M ≤ (|C₀| + |C₁| + (L : ℝ)) * (1 + R) ^ 3 + 8 * M := by linarith
    refine hb.mono ?_ (le_of_far (by norm_num) h1 hM hN) (le_of_far (by norm_num) h1 hM hN)
    have := le_of_far (k := 1) (by norm_num) h1 hM hN
    simpa only [pow_one] using this
  · have hin : ∀ z ∈ Metric.ball y 1, z ∈ Metric.closedBall (0 : Space) (R + 1) := fun z hz => by
      have := (ball_norm_near hz).2
      rw [Metric.mem_closedBall, dist_zero_right]
      linarith
    have hN : (|C₀| + |C₁| + (L : ℝ)) * (1 + R) ^ 3 ≤ (|C₀| + |C₁| + (L : ℝ)) * (1 + R) ^ 3 + 8 * M := by
      linarith
    have hL0 : (0 : ℝ) ≤ L := L.2
    have a0 := abs_nonneg C₀
    have a1 := abs_nonneg C₁
    refine ⟨fun z _ => hdiff z, fun z hz => ?_, fun z hz => ?_, fun z hz w hw => ?_⟩
    · have := le_of_near (k := 1) (by norm_num) hy0 hy.le hS (c := ‖f z‖)
        ((hC₀ z (hin z hz)).trans (by linarith [le_abs_self C₀])) hN
      rwa [pow_one] at this
    · exact le_of_near (by norm_num) hy0 hy.le hS ((hC₁ z (hin z hz)).trans (by linarith [le_abs_self C₁])) hN
    · have hl := hL.norm_sub_le (hin z hz) (hin w hw)
      refine hl.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
      exact le_of_near (by norm_num) hy0 hy.le hS (by linarith) hN

theorem farBound_of_farDecay {f : Space → Fin 3 → ℂ} (h : CertCell.GivenShape.Internal.KeyDecay.FarDecay 1 f) :
    FarBound f 1 := by
  obtain ⟨C, R, hC, hR, hb⟩ := h
  refine ⟨C, max R 2, hC, le_max_right _ _, fun y hy => ?_⟩
  have hyR : R ≤ ‖y‖ := le_trans (le_max_left _ _) hy
  obtain ⟨h1, h2⟩ := hb y hyR
  have e : ∀ k : ℕ, C * ‖y‖⁻¹ ^ k = C / ‖y‖ ^ k := fun k => by rw [inv_pow, div_eq_mul_inv]
  refine ⟨fun z hz => (h1 z hz).1, fun z hz => ?_, fun z hz => ?_, ?_⟩
  · rw [← e]
    exact (h1 z hz).2.1
  · rw [← e]
    exact (h1 z hz).2.2
  · rw [← e]
    exact h2

theorem key_ballBound (P : ShapeParams) (hP : IsShapeParams P) (D : TimeFieldData) (hD : IsTimeFieldData D)
    (κ : FieldKey) (hκ : κ ∈ D.keys) (σ : ℝ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ y : Space, BallBound (keyVector P κ (D.amp κ) σ) y
      (N * (1 + ‖y‖)⁻¹) (N * (1 + ‖y‖)⁻¹ ^ 2) (N * (1 + ‖y‖)⁻¹ ^ 3) := by
  by_cases h0 : κ.label.1 = 0
  · exact ballBound_global (shapeParts_closed.type_two_smooth P D κ σ hP hD hκ h0)
      (CertCell.GivenShape.Internal.farBound_typeTwoKey P hP D hD κ hκ h0 σ)
  · have hpos := hD.highOrder_pos κ hκ
    obtain ⟨n, hn⟩ : ∃ n : ℕ, (D.amp κ).highOrder = n + 1 := ⟨(D.amp κ).highOrder - 1, by omega⟩
    exact ballBound_global (shapeParts_closed.type_one_smooth P D κ σ hP hD hκ h0)
      (farBound_of_farDecay (CertCell.GivenShape.Internal.KeyDecay.key_farDecay P hP κ (D.amp κ) σ h0 n hn
        (hD.radial_class κ hκ h0) (hD.polar_class κ hκ h0)))

theorem lsmul_norm_le (u : ℂ) (v : Fin 3 → ℂ) : ‖ContinuousLinearMap.lsmul ℝ ℂ u v‖ ≤ ‖u‖ * ‖v‖ := by
  rw [ContinuousLinearMap.lsmul_apply, norm_smul]

theorem phaseMul_ballBound {g : Space → ℂ} {f : Space → Fin 3 → ℂ} {y : Space} {m b K N w : ℝ}
    (hm : 0 ≤ m) (hb : 0 ≤ b) (hK : 0 ≤ K) (hN : 0 ≤ N) (hw : 0 ≤ w)
    (hg : BallBound g y m (m * b * (K * w)) (m * b ^ 2 * (K * w) * (K * w) + m * b * (K * w ^ 2)))
    (hf : BallBound f y (N * w) (N * w ^ 2) (N * w ^ 3)) :
    BallBound (fun z => g z • f z) y (2 * (m * (1 + b * K) ^ 2) * N * w)
      (2 * (m * (1 + b * K) ^ 2) * N * w ^ 2) (2 * (m * (1 + b * K) ^ 2) * N * w ^ 3) := by
  have h := hg.bilin (ContinuousLinearMap.lsmul ℝ ℂ) lsmul_norm_le hf
  simp only [ContinuousLinearMap.lsmul_apply] at h
  have pb : 0 ≤ b * K := mul_nonneg hb hK
  have p2 : 0 ≤ (b * K) ^ 2 := sq_nonneg _
  have pm : ∀ k : ℕ, 0 ≤ m * N * w ^ k := fun k => mul_nonneg (mul_nonneg hm hN) (pow_nonneg hw k)
  refine h.mono ?_ ?_ ?_
  · have e : 2 * (m * (1 + b * K) ^ 2) * N * w - m * (N * w) =
        m * N * w ^ 1 * (1 + 4 * (b * K) + 2 * (b * K) ^ 2) := by ring
    have : 0 ≤ m * N * w ^ 1 * (1 + 4 * (b * K) + 2 * (b * K) ^ 2) := mul_nonneg (pm 1) (by linarith)
    linarith
  · have e : 2 * (m * (1 + b * K) ^ 2) * N * w ^ 2 - (m * (N * w ^ 2) + m * b * (K * w) * (N * w)) =
        m * N * w ^ 2 * (1 + 3 * (b * K) + 2 * (b * K) ^ 2) := by ring
    have : 0 ≤ m * N * w ^ 2 * (1 + 3 * (b * K) + 2 * (b * K) ^ 2) := mul_nonneg (pm 2) (by linarith)
    linarith
  · have e : 2 * (m * (1 + b * K) ^ 2) * N * w ^ 3 - (m * b * (K * w) * (N * w ^ 2) + m * (N * w ^ 3) +
        ((m * b ^ 2 * (K * w) * (K * w) + m * b * (K * w ^ 2)) * (N * w) + m * b * (K * w) * (N * w ^ 2))) =
        m * N * w ^ 3 * (1 + (b * K) + (b * K) ^ 2) := by ring
    have : 0 ≤ m * N * w ^ 3 * (1 + (b * K) + (b * K) ^ 2) := mul_nonneg (pm 3) (by linarith)
    linarith

theorem coef_le {m b M1 B1 K : ℝ} (hm0 : 0 ≤ m) (hb0 : 0 ≤ b) (hK : 0 ≤ K) (hm : m ≤ M1) (hb : b ≤ B1) :
    m * (1 + b * K) ^ 2 ≤ M1 * (1 + B1 * K) ^ 2 := by
  have h0 : 0 ≤ 1 + b * K := add_nonneg zero_le_one (mul_nonneg hb0 hK)
  have h1 : 1 + b * K ≤ 1 + B1 * K := by linarith [mul_le_mul_of_nonneg_right hb hK]
  exact mul_le_mul hm (pow_le_pow_left₀ h0 h1 2) (sq_nonneg _) (hm0.trans hm)

theorem two_terms_le {E0 E1 Qh N0 N1 x : ℝ} (h0 : E0 ≤ Qh) (h1 : E1 ≤ Qh) (hN0 : 0 ≤ N0) (hN1 : 0 ≤ N1)
    (hx : 0 ≤ x) : 2 * E0 * N0 * x + 2 * E1 * N1 * x ≤ 2 * Qh * (N0 + N1) * x := by
  have a0 := mul_le_mul_of_nonneg_right h0 (mul_nonneg hN0 hx)
  have a1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hN1 hx)
  have e : 2 * Qh * (N0 + N1) * x = 2 * (Qh * (N0 * x)) + 2 * (Qh * (N1 * x)) := by ring
  have e0 : 2 * E0 * N0 * x = 2 * (E0 * (N0 * x)) := by ring
  have e1 : 2 * E1 * N1 * x = 2 * (E1 * (N1 * x)) := by ring
  rw [e, e0, e1]
  linarith

theorem key_uniform (P : ShapeParams) (X : ℝ → ℝ) (hP : IsShapeParams P) (hX : IsRadialPhase X)
    (D : TimeFieldData) (hD : IsTimeFieldData D) (κ : FieldKey) (hκ : κ ∈ D.keys) (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a : ℝ, |a| ≤ A → ∀ (σ : ℝ) (y : Space),
      BallBound (keyVector (movedParams P X a) κ (D.amp κ) σ) y
        (N * (1 + ‖y‖)⁻¹) (N * (1 + ‖y‖)⁻¹ ^ 2) (N * (1 + ‖y‖)⁻¹ ^ 3) := by
  obtain ⟨N0, hN0, h0⟩ := key_ballBound P hP D hD κ hκ 0
  have hP1 : IsShapeParams (movedParams P X 1) := movedParamsValid_holds P X 1 hP hX
  obtain ⟨N1, hN1, h1⟩ := key_ballBound (movedParams P X 1) hP1 D hD κ hκ 0
  obtain ⟨K, hK, hph⟩ := expPhase_ballBound hX
  have hJ0 : 0 ≤ |(κ.phaseIndex : ℝ)| := abs_nonneg _
  refine ⟨2 * ((1 + A) * (1 + |(κ.phaseIndex : ℝ)| * (1 + A) * K) ^ 2) * (N0 + N1), by positivity,
    fun a ha σ y => ?_⟩
  have hfun : keyVector (movedParams P X a) κ (D.amp κ) σ = fun z =>
      ((Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) * ((1 - a : ℝ) : ℂ)) *
          Complex.exp ((((κ.phaseIndex : ℝ) * a * X (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)) •
          keyVector P κ (D.amp κ) 0 z +
        ((Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) * (a : ℂ)) *
          Complex.exp ((((κ.phaseIndex : ℝ) * (a - 1) * X (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)) •
          keyVector (movedParams P X 1) κ (D.amp κ) 0 z := by
    funext z
    have ht := keyTimeShift_holds (movedParams P X a) κ (D.amp κ) 0 σ z
    rw [zero_add] at ht
    rw [ht, keyVector_moved P X hP.phase hX κ (D.amp κ) a 0 z]
    funext i
    simp only [movePhase, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hfun]
  set c : ℂ := Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) with hc
  have nc : ‖c‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hw0 : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
  have haA := abs_le.1 ha
  have m0 : ‖c * ((1 - a : ℝ) : ℂ)‖ ≤ 1 + A := by
    rw [norm_mul, nc, one_mul, Complex.norm_real, Real.norm_eq_abs]
    exact abs_le.2 ⟨by linarith, by linarith⟩
  have m1 : ‖c * (a : ℂ)‖ ≤ 1 + A := by
    rw [norm_mul, nc, one_mul, Complex.norm_real, Real.norm_eq_abs]
    linarith
  have b0 : |(κ.phaseIndex : ℝ) * a| ≤ |(κ.phaseIndex : ℝ)| * (1 + A) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (by linarith) hJ0
  have b1 : |(κ.phaseIndex : ℝ) * (a - 1)| ≤ |(κ.phaseIndex : ℝ)| * (1 + A) := by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨by linarith, by linarith⟩) hJ0
  have t0 := phaseMul_ballBound (norm_nonneg _) (abs_nonneg _) hK hN0 hw0 (hph (c * ((1 - a : ℝ) : ℂ)) ((κ.phaseIndex : ℝ) * a) y) (h0 y)
  have t1 := phaseMul_ballBound (norm_nonneg _) (abs_nonneg _) hK hN1 hw0
    (hph (c * (a : ℂ)) ((κ.phaseIndex : ℝ) * (a - 1)) y) (h1 y)
  have c0 := coef_le (norm_nonneg _) (abs_nonneg _) hK m0 b0
  have c1 := coef_le (norm_nonneg _) (abs_nonneg _) hK m1 b1
  refine (t0.add t1).mono ?_ ?_ ?_
  · have := two_terms_le c0 c1 hN0 hN1 (pow_nonneg hw0 1)
    simpa only [pow_one] using this
  · exact two_terms_le c0 c1 hN0 hN1 (pow_nonneg hw0 2)
  · exact two_terms_le c0 c1 hN0 hN1 (pow_nonneg hw0 3)

theorem ballBound_point {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E} {y : Space}
    {v d l : ℝ} (h : BallBound f y v d l) (hl : 0 ≤ l) :
    ‖f y‖ ≤ v ∧ DifferentiableAt ℝ f y ∧ ‖fderiv ℝ f y‖ ≤ d ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ l := by
  have hy : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨h.val y hy, h.diff y hy, h.der y hy, ?_⟩
  have hL : LipschitzOnWith (Real.toNNReal l) (fderiv ℝ f) (Metric.ball y 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (h.slope z hz w hw).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hL
  rwa [Real.coe_toNNReal _ hl] at this

theorem norm_compL_realPart_le (H : Space →L[ℝ] Space →L[ℝ] (Fin 3 → ℂ)) :
    ‖(ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp H‖ ≤ ‖realPartVec‖ * ‖H‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun T => ?_
  rw [ContinuousLinearMap.compL_apply]
  exact ContinuousLinearMap.opNorm_comp_le _ _

theorem withOrigin_valid {P : ShapeParams} {g : OriginProfile} (hP : IsShapeParams P) (hg : IsOriginProfile g) :
    IsShapeParams (withOrigin P g) :=
  ⟨hP.chartLength_pos, hP.azimuthOrder_pos, hP.phase, hg⟩

theorem withOrigin_moved (P : ShapeParams) (X : ℝ → ℝ) (a : ℝ) (g : OriginProfile) :
    withOrigin (movedParams P X a) g = movedParams (withOrigin P g) X a := rfl

theorem field_uniform (P : ShapeParams) (X : ℝ → ℝ) (hP : IsShapeParams P) (hX : IsRadialPhase X)
    (g : OriginProfile) (hg : IsOriginProfile g) (D : TimeFieldData) (hD : IsTimeFieldData D) (A : ℝ) (hA : 0 ≤ A) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ a : ℝ, |a| ≤ A → ∀ (σ : ℝ) (y : Space),
      ‖shapeInfoField (withOrigin (movedParams P X a) g) D σ y‖ ≤ N * (1 + ‖y‖)⁻¹ ∧
      DifferentiableAt ℝ (shapeInfoField (withOrigin (movedParams P X a) g) D σ) y ∧
      ‖fderiv ℝ (shapeInfoField (withOrigin (movedParams P X a) g) D σ) y‖ ≤ N * (1 + ‖y‖)⁻¹ ^ 2 ∧
      ‖shapeHess (withOrigin (movedParams P X a) g) D σ y‖ ≤ N * (1 + ‖y‖)⁻¹ ^ 3 := by
  have hPg := withOrigin_valid hP hg
  have hk : ∀ κ : FieldKey, ∃ N : ℝ, 0 ≤ N ∧ (κ ∈ D.keys → ∀ a : ℝ, |a| ≤ A → ∀ (σ : ℝ) (y : Space),
      BallBound (keyVector (movedParams (withOrigin P g) X a) κ (D.amp κ) σ) y
        (N * (1 + ‖y‖)⁻¹) (N * (1 + ‖y‖)⁻¹ ^ 2) (N * (1 + ‖y‖)⁻¹ ^ 3)) := by
    intro κ
    by_cases hκ : κ ∈ D.keys
    · obtain ⟨N, hN, h⟩ := key_uniform (withOrigin P g) X hPg hX D hD κ hκ A hA
      exact ⟨N, hN, fun _ => h⟩
    · exact ⟨0, le_rfl, fun h => absurd h hκ⟩
  choose Nk hNk hkb using hk
  have hS : 0 ≤ ∑ κ ∈ D.keys, Nk κ := Finset.sum_nonneg fun κ _ => hNk κ
  refine ⟨‖realPartVec‖ * ∑ κ ∈ D.keys, Nk κ, mul_nonneg (norm_nonneg _) hS, fun a ha σ y => ?_⟩
  rw [withOrigin_moved]
  set Q := movedParams (withOrigin P g) X a
  set w := (1 + ‖y‖)⁻¹ with hw
  have hw0 : 0 ≤ w := by positivity
  have pt : ∀ κ ∈ D.keys, ‖keyVector Q κ (D.amp κ) σ y‖ ≤ Nk κ * w ∧
      DifferentiableAt ℝ (keyVector Q κ (D.amp κ) σ) y ∧
      ‖fderiv ℝ (keyVector Q κ (D.amp κ) σ) y‖ ≤ Nk κ * w ^ 2 ∧
      ‖fderiv ℝ (fderiv ℝ (keyVector Q κ (D.amp κ) σ)) y‖ ≤ Nk κ * w ^ 3 := fun κ hκ =>
    ballBound_point (hkb κ hκ a ha σ y) (mul_nonneg (hNk κ) (pow_nonneg hw0 3))
  have hsum : HasFDerivAt (fun z => ∑ κ ∈ D.keys, keyVector Q κ (D.amp κ) σ z)
      (∑ κ ∈ D.keys, fderiv ℝ (keyVector Q κ (D.amp κ) σ) y) y :=
    HasFDerivAt.fun_sum fun κ hκ => (pt κ hκ).2.1.hasFDerivAt
  have hF : HasFDerivAt (shapeInfoField Q D σ)
      (realPartVec.comp (∑ κ ∈ D.keys, fderiv ℝ (keyVector Q κ (D.amp κ) σ) y)) y :=
    realPartVec.hasFDerivAt.comp y hsum
  have hR := norm_nonneg (realPartVec : (Fin 3 → ℂ) →L[ℝ] Space)
  refine ⟨?_, hF.differentiableAt, ?_, ?_⟩
  · show ‖realPartVec (∑ κ ∈ D.keys, keyVector Q κ (D.amp κ) σ y)‖ ≤ _
    refine (realPartVec.le_opNorm _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hR
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun κ hκ => (pt κ hκ).1
  · rw [hF.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hR
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun κ hκ => (pt κ hκ).2.2.1
  · show ‖∑ κ ∈ D.keys, (ContinuousLinearMap.compL ℝ Space (Fin 3 → ℂ) Space realPartVec).comp
      (keyHess Q κ (D.amp κ) σ y)‖ ≤ _
    refine (norm_sum_le _ _).trans ?_
    rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum fun κ hκ => (norm_compL_realPart_le _).trans
      (mul_le_mul_of_nonneg_left (pt κ hκ).2.2.2 hR)

theorem affine_norm_le {k : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (c : E) (v : Fin k → E)
    (q : Fin k → ℝ) {M Nc x : ℝ} (N : Fin k → ℝ) (hq : ∀ i, |q i| ≤ M) (hc : ‖c‖ ≤ Nc * x)
    (hv : ∀ i, ‖v i‖ ≤ N i * x) :
    ‖c + ∑ i, q i • v i‖ ≤ (Nc + |M| * ∑ i, N i) * x := by
  have hsum : ‖∑ i, q i • v i‖ ≤ ∑ i, |M| * (N i * x) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ((hq i).trans (le_abs_self M)) (hv i) (norm_nonneg _) (abs_nonneg _)
  have e : ∑ i, |M| * (N i * x) = |M| * (∑ i, N i) * x := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  calc ‖c + ∑ i, q i • v i‖ ≤ ‖c‖ + ‖∑ i, q i • v i‖ := norm_add_le _ _
    _ ≤ Nc * x + |M| * (∑ i, N i) * x := add_le_add hc (hsum.trans (le_of_eq e))
    _ = (Nc + |M| * ∑ i, N i) * x := by ring

theorem phaseRate_abs_le {k : ℕ} (rate q : Fin k → ℝ) {M : ℝ} (hq : ∀ i, |q i| ≤ M) :
    |phaseRate rate q| ≤ ∑ i, |rate i| * |M| := by
  unfold phaseRate
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((hq i).trans (le_abs_self M)) (abs_nonneg _)

end Internal.MovedDecay

theorem movedFieldUniformDecay_holds : MovedFieldUniformDecayHolds := by
  intro k P moving rate g centre gt tangent M hP hm hg hgt hc ht
  set A : ℝ := ∑ i, |rate i| * |M| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
  obtain ⟨Nc, hNc, hcb⟩ := Internal.MovedDecay.field_uniform P moving hP hm g hg centre hc A hA0
  have hti : ∀ i : Fin k, ∃ N : ℝ, 0 ≤ N ∧ ∀ a : ℝ, |a| ≤ A → ∀ (σ : ℝ) (y : Space),
      ‖shapeInfoField (withOrigin (movedParams P moving a) (gt i)) (tangent i) σ y‖ ≤ N * (1 + ‖y‖)⁻¹ ∧
      DifferentiableAt ℝ (shapeInfoField (withOrigin (movedParams P moving a) (gt i)) (tangent i) σ) y ∧
      ‖fderiv ℝ (shapeInfoField (withOrigin (movedParams P moving a) (gt i)) (tangent i) σ) y‖ ≤
        N * (1 + ‖y‖)⁻¹ ^ 2 ∧
      ‖shapeHess (withOrigin (movedParams P moving a) (gt i)) (tangent i) σ y‖ ≤ N * (1 + ‖y‖)⁻¹ ^ 3 :=
    fun i => Internal.MovedDecay.field_uniform P moving hP hm (gt i) (hgt i) (tangent i) (ht i) A hA0
  choose Nt hNt htb using hti
  refine ⟨Nc + |M| * ∑ i, Nt i, fun q hq σ y => ?_⟩
  set a := phaseRate rate q with ha
  have haA : |a| ≤ A := Internal.MovedDecay.phaseRate_abs_le rate q hq
  obtain ⟨c0, c1, c2, c3⟩ := hcb a haA σ y
  have hi := fun i => htb i a haA σ y
  have hy : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have e1 : ∀ B : ℝ, B / (1 + ‖y‖) = B * (1 + ‖y‖)⁻¹ := fun B => div_eq_mul_inv _ _
  have e2 : ∀ (B : ℝ) (n : ℕ), B / (1 + ‖y‖) ^ n = B * (1 + ‖y‖)⁻¹ ^ n := fun B n => by
    rw [inv_pow, div_eq_mul_inv]
  have hD : HasFDerivAt (affineField (movedParams P moving a) g centre gt tangent q σ)
      (fderiv ℝ (shapeInfoField (withOrigin (movedParams P moving a) g) centre σ) y +
        ∑ i, q i • fderiv ℝ (shapeInfoField (withOrigin (movedParams P moving a) (gt i)) (tangent i) σ) y) y :=
    c1.hasFDerivAt.add (HasFDerivAt.fun_sum fun i _ => ((hi i).2.1.hasFDerivAt.const_smul (q i)))
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    exact Internal.MovedDecay.affine_norm_le _ _ q Nt hq c0 fun i => (hi i).1
  · rw [hD.fderiv, e2]
    exact Internal.MovedDecay.affine_norm_le _ _ q Nt hq c2 fun i => (hi i).2.2.1
  · rw [e2]
    exact Internal.MovedDecay.affine_norm_le _ _ q Nt hq c3 fun i => (hi i).2.2.2

end Instantiation

end CellReduction

end Breakdown

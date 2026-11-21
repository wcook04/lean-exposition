import Breakdown.FracCert.StWeak
import Breakdown.Frac.PMomentum
import Breakdown.Frac.NNicePairing

open MeasureTheory Set Real Metric
open scoped ENNReal ContDiff SchwartzMap

noncomputable section

namespace Breakdown.FracCert

namespace Internal.SimDeriv

open Breakdown.Freq Breakdown.FracInternal.Momentum

theorem turn_smul (r : ℝ) (y : Space) : axialTurn (r • y) = r • axialTurn y := by
  ext i
  fin_cases i <;> simp [axialTurn]

theorem turn_add (x y : Space) : axialTurn (x + y) = axialTurn x + axialTurn y := by
  ext i
  fin_cases i <;> simp [axialTurn]; ring

theorem turn_sub (x y : Space) : axialTurn (x - y) = axialTurn x - axialTurn y := by
  ext i
  fin_cases i <;> simp [axialTurn]; ring

theorem turn_zero : axialTurn 0 = 0 := by
  simpa using turn_smul 0 0

theorem norm_turn_le (y : Space) : ‖axialTurn y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [axialTurn, Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

theorem simAdj_eq (α a μ : ℝ) (φ : Space → Space) :
    simAdj α a μ φ = fun y => axialRotation (-(a * Real.log μ))
      (μ ^ (4 * (1 / (2 * α)) - 1) • φ (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)) := by
  funext y
  simp only [simAdj, pushForward, axialRotationSpec.2.2.2.1, neg_neg]

theorem fderiv_conj (R R' : Space ≃ₗᵢ[ℝ] Space) (c k : ℝ) {f : Space → Space}
    (hf : Differentiable ℝ f) (y v : Space) :
    fderiv ℝ (fun y => R (c • f (k • R' y))) y v = R (c • fderiv ℝ f (k • R' y) (k • R' v)) := by
  have h1 : HasFDerivAt (fun y : Space => k • R' y)
      (k • (R'.toContinuousLinearEquiv : Space →L[ℝ] Space)) y :=
    (R'.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.const_smul k
  have h2 := (((hf (k • R' y)).hasFDerivAt.comp y h1).const_smul c)
  have h3 := (R.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt.comp y h2
  have h4 : HasFDerivAt (fun y => R (c • f (k • R' y)))
      ((R.toContinuousLinearEquiv : Space →L[ℝ] Space).comp (c • (fderiv ℝ f (k • R' y)).comp
        (k • (R'.toContinuousLinearEquiv : Space →L[ℝ] Space)))) y := h3
  rw [h4.fderiv]
  simp

theorem drift_simAdj (α a μ : ℝ) {f : Space → Space} (hf : Differentiable ℝ f) (y : Space) :
    driftAdjoint α a (simAdj α a μ f) y =
      let R := axialRotation (-(a * Real.log μ))
      let w := axialRotation (a * Real.log μ) y
      let c := μ ^ (4 * (1 / (2 * α)) - 1)
      let k := μ ^ (1 / (2 * α))
      (1 - 4 * (1 / (2 * α))) • R (c • f (k • w)) - (1 / (2 * α)) • R (c • fderiv ℝ f (k • w) (k • w))
        - a • (R (c • fderiv ℝ f (k • w) (k • axialTurn w)) - axialTurn (R (c • f (k • w)))) := by
  have hc : axialRotation (a * Real.log μ) (axialTurn y) = axialTurn (axialRotation (a * Real.log μ) y) :=
    (turn_rot_comm axialRotationSpec _ _).symm
  simp only [driftAdjoint, simAdj_eq, fderiv_conj _ _ _ _ hf, hc]


theorem hasDerivAt_simAdj (α a : ℝ) {f : Space → Space} (hf : Differentiable ℝ f) (y : Space)
    {τ : ℝ} (hτ : τ < 1) :
    HasDerivAt (fun τ => simAdj α a (1 - τ) f y)
      ((1 - τ)⁻¹ • driftAdjoint α a (simAdj α a (1 - τ) f) y) τ := by
  have hne : (1 - τ) ≠ 0 := by linarith
  have hμ : HasDerivAt (fun τ : ℝ => 1 - τ) (-1) τ := by
    simpa using (hasDerivAt_id τ).const_sub 1
  have hL : HasDerivAt (fun τ => Real.log (1 - τ)) ((-1) / (1 - τ)) τ := hμ.log hne
  have hθ : HasDerivAt (fun τ => -(a * Real.log (1 - τ))) (-(a * ((-1) / (1 - τ)))) τ :=
    (hL.const_mul a).neg
  have hθ2 : HasDerivAt (fun τ => a * Real.log (1 - τ)) (a * ((-1) / (1 - τ))) τ := hL.const_mul a
  have hr := rot_hasDerivAt axialRotationSpec hθ2 (hasDerivAt_const τ y)
  have hk : HasDerivAt (fun τ => (1 - τ) ^ (1 / (2 * α)))
      ((-1) * (1 / (2 * α)) * (1 - τ) ^ (1 / (2 * α) - 1)) τ := hμ.rpow_const (Or.inl hne)
  have hz := hk.smul hr
  have hfz := (hf _).hasFDerivAt.comp_hasDerivAt τ hz
  have hc : HasDerivAt (fun τ => (1 - τ) ^ (4 * (1 / (2 * α)) - 1))
      ((-1) * (4 * (1 / (2 * α)) - 1) * (1 - τ) ^ (4 * (1 / (2 * α)) - 1 - 1)) τ :=
    hμ.rpow_const (Or.inl hne)
  have hu := hc.smul hfz
  have hR := rot_hasDerivAt axialRotationSpec hθ hu
  rw [drift_simAdj α a _ hf]
  simp only [simAdj_eq]
  refine hR.congr_deriv ?_
  dsimp only [Pi.smul_apply', Pi.smul_apply, Function.comp_apply]
  rw [Real.rpow_sub_one hne (4 * (1 / (2 * α)) - 1), Real.rpow_sub_one hne (1 / (2 * α))]
  simp only [map_add, map_smul, map_zero, smul_add, smul_sub, turn_smul, add_zero, smul_smul]
  module

theorem rpow_le_sum {lo hi μ : ℝ} (s : ℝ) (hlo : 0 < lo) (h1 : lo ≤ μ) (h2 : μ ≤ hi) :
    μ ^ s ≤ lo ^ s + hi ^ s := by
  have a1 := Real.rpow_nonneg hlo.le s
  have a2 := Real.rpow_nonneg (hlo.le.trans (h1.trans h2)) s
  rcases le_total 0 s with hs | hs
  · have := Real.rpow_le_rpow (hlo.le.trans h1) h2 hs
    linarith
  · have := Real.rpow_le_rpow_of_nonpos hlo h1 hs
    linarith

theorem rapid_decay (S : 𝓢(Space, Space)) :
    ∃ C, ∀ z : Space, (1 + ‖z‖) ^ 5 * ‖S z‖ ≤ C ∧ (1 + ‖z‖) ^ 5 * ‖fderiv ℝ S z‖ ≤ C := by
  refine ⟨2 ^ 5 * (Finset.Iic ((5 : ℕ), (1 : ℕ))).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S,
    fun z => ⟨?_, ?_⟩⟩
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5 : ℕ), (1 : ℕ))) (k := 5)
      (n := 0) le_rfl (Nat.zero_le _) S z
    rwa [norm_iteratedFDeriv_zero] at h
  · have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5 : ℕ), (1 : ℕ))) (k := 5)
      (n := 1) le_rfl le_rfl S z
    rwa [norm_iteratedFDeriv_one] at h

theorem one_add_scale {m0 k : ℝ} (hm0 : 0 ≤ m0) (hm1 : m0 ≤ 1) (hk : m0 ≤ k) (w y : Space)
    (hw : ‖w‖ = ‖y‖) : m0 * (1 + ‖y‖) ≤ 1 + ‖k • w‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hm0.trans hk), hw]
  nlinarith [norm_nonneg y]

theorem abstract_bound (R : Space ≃ₗᵢ[ℝ] Space) (L : Space →L[ℝ] Space) (p w : Space)
    (c k g a e A : ℝ) (hc : 0 ≤ c) (hk : 0 ≤ k) (hg : 0 ≤ g) (hw : ‖w‖ ≤ A) :
    ‖e • R (c • p) - g • R (c • L (k • w)) - a • (R (c • L (k • axialTurn w)) - axialTurn (R (c • p)))‖
      ≤ (|e| + |a|) * c * ‖p‖ + (g + |a|) * c * k * (‖L‖ * A) := by
  have hL : ∀ u : Space, ‖u‖ ≤ A → ‖R (c • L (k • u))‖ ≤ c * k * (‖L‖ * A) := by
    intro u hu
    rw [LinearIsometryEquiv.norm_map, norm_smul, map_smul, norm_smul, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg hc, abs_of_nonneg hk, ← mul_assoc]
    gcongr
    exact (L.le_opNorm u).trans (by gcongr)
  have n1 : ‖e • R (c • p)‖ = |e| * c * ‖p‖ := by
    rw [norm_smul, LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg hc, mul_assoc]
  have n2 : ‖g • R (c • L (k • w))‖ ≤ g * (c * k * (‖L‖ * A)) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hg]
    exact mul_le_mul_of_nonneg_left (hL w hw) hg
  have n3 := hL (axialTurn w) ((norm_turn_le w).trans hw)
  have n4 : ‖axialTurn (R (c • p))‖ ≤ c * ‖p‖ := by
    refine (norm_turn_le _).trans ?_
    rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
  have n5 : ‖a • (R (c • L (k • axialTurn w)) - axialTurn (R (c • p)))‖ ≤
      |a| * (c * k * (‖L‖ * A) + c * ‖p‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add n3 n4)) (abs_nonneg a)
  calc _ ≤ ‖e • R (c • p)‖ + ‖g • R (c • L (k • w))‖
        + ‖a • (R (c • L (k • axialTurn w)) - axialTurn (R (c • p)))‖ :=
        (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
    _ ≤ |e| * c * ‖p‖ + g * (c * k * (‖L‖ * A)) + |a| * (c * k * (‖L‖ * A) + c * ‖p‖) := by
        rw [n1]
        linarith
    _ = _ := by ring

theorem drift_norm_le (α a μ : ℝ) (hα : 0 < α) (hμ : 0 < μ) {f : Space → Space}
    (hf : Differentiable ℝ f) (y : Space) :
    ‖μ⁻¹ • driftAdjoint α a (simAdj α a μ f) y‖ ≤ μ⁻¹ *
      ((|1 - 4 * (1 / (2 * α))| + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) *
        ‖f (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)‖ +
       (1 / (2 * α) + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) * μ ^ (1 / (2 * α)) *
        (‖fderiv ℝ f (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)‖ * (1 + ‖y‖))) := by
  rw [drift_simAdj α a μ hf, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hμ)]
  dsimp only
  refine mul_le_mul_of_nonneg_left ?_ (inv_pos.2 hμ).le
  refine abstract_bound _ _ _ _ _ _ _ _ _ _ (Real.rpow_nonneg hμ.le _) (Real.rpow_nonneg hμ.le _)
    (by positivity) ?_
  rw [LinearIsometryEquiv.norm_map]
  linarith

theorem simAdj_norm_eq (α a μ : ℝ) (hμ : 0 < μ) (f : Space → Space) (y : Space) :
    ‖simAdj α a μ f y‖ = μ ^ (4 * (1 / (2 * α)) - 1) *
      ‖f (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)‖ := by
  rw [simAdj_eq]
  dsimp only
  rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hμ.le _)]

theorem simAdj_bounds (α a : ℝ) (hα : 1 < α) (S : 𝓢(Space, Space)) {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ K, ∀ μ, lo ≤ μ → μ ≤ hi → ∀ y : Space,
      (1 + ‖y‖) ^ 4 * ‖simAdj α a μ S y‖ ≤ K ∧
      (1 + ‖y‖) ^ 4 * ‖μ⁻¹ • driftAdjoint α a (simAdj α a μ S) y‖ ≤ K := by
  obtain ⟨C, hC⟩ := rapid_decay S
  have hα0 : 0 < α := by linarith
  have hg0 : 0 ≤ 1 / (2 * α) := by positivity
  have hm0 : 0 < min 1 (lo ^ (1 / (2 * α))) := lt_min one_pos (Real.rpow_pos_of_pos hlo _)
  have hm1 : min 1 (lo ^ (1 / (2 * α))) ≤ 1 := min_le_left _ _
  obtain ⟨cB, hcB⟩ : ∃ cB, cB = lo ^ (4 * (1 / (2 * α)) - 1) + hi ^ (4 * (1 / (2 * α)) - 1) := ⟨_, rfl⟩
  obtain ⟨kB, hkB⟩ : ∃ kB, kB = lo ^ (1 / (2 * α)) + hi ^ (1 / (2 * α)) := ⟨_, rfl⟩
  obtain ⟨C1, hC1⟩ : ∃ C1, C1 = C / (min 1 (lo ^ (1 / (2 * α)))) ^ 5 := ⟨_, rfl⟩
  refine ⟨max (cB * C1) (lo⁻¹ * ((|1 - 4 * (1 / (2 * α))| + |a|) * cB * C1 +
    (1 / (2 * α) + |a|) * cB * kB * C1)), ?_⟩
  intro μ h1 h2 y
  have hμ : 0 < μ := hlo.trans_le h1
  have hw : ‖axialRotation (a * Real.log μ) y‖ = ‖y‖ := LinearIsometryEquiv.norm_map _ _
  have hc0 : 0 ≤ μ ^ (4 * (1 / (2 * α)) - 1) := Real.rpow_nonneg hμ.le _
  have hk0 : 0 ≤ μ ^ (1 / (2 * α)) := Real.rpow_nonneg hμ.le _
  have hcle : μ ^ (4 * (1 / (2 * α)) - 1) ≤ cB := hcB ▸ rpow_le_sum _ hlo h1 h2
  have hkle : μ ^ (1 / (2 * α)) ≤ kB := hkB ▸ rpow_le_sum _ hlo h1 h2
  have hkm : min 1 (lo ^ (1 / (2 * α))) ≤ μ ^ (1 / (2 * α)) :=
    (min_le_right _ _).trans (Real.rpow_le_rpow hlo.le h1 hg0)
  have hA1 : 1 ≤ 1 + ‖y‖ := le_add_of_nonneg_right (norm_nonneg y)
  have hz := one_add_scale hm0.le hm1 hkm (axialRotation (a * Real.log μ) y) y hw
  set z := μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y with hzdef
  have key : ∀ r : ℝ, 0 ≤ r → (1 + ‖z‖) ^ 5 * r ≤ C → (1 + ‖y‖) ^ 5 * r ≤ C1 := by
    intro r hr hrC
    rw [hC1, le_div_iff₀ (pow_pos hm0 5)]
    calc (1 + ‖y‖) ^ 5 * r * (min 1 (lo ^ (1 / (2 * α)))) ^ 5
        = (min 1 (lo ^ (1 / (2 * α))) * (1 + ‖y‖)) ^ 5 * r := by ring
      _ ≤ (1 + ‖z‖) ^ 5 * r := by gcongr
      _ ≤ C := hrC
  have hP := key _ (norm_nonneg _) (hC z).1
  have hQ := key _ (norm_nonneg _) (hC z).2
  have hP4 : (1 + ‖y‖) ^ 4 * ‖S z‖ ≤ C1 :=
    le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hA1 (by norm_num)) (norm_nonneg _)) hP
  have hQ4 : (1 + ‖y‖) ^ 4 * (‖fderiv ℝ S z‖ * (1 + ‖y‖)) ≤ C1 := by
    calc _ = (1 + ‖y‖) ^ 5 * ‖fderiv ℝ S z‖ := by ring
      _ ≤ C1 := hQ
  have hC1n : 0 ≤ C1 := le_trans (by positivity) hP4
  have hcBn : 0 ≤ cB := hc0.trans hcle
  have hkBn : 0 ≤ kB := hk0.trans hkle
  constructor
  · rw [simAdj_norm_eq α a μ hμ]
    refine le_trans ?_ (le_max_left _ _)
    calc (1 + ‖y‖) ^ 4 * (μ ^ (4 * (1 / (2 * α)) - 1) * ‖S z‖)
        = μ ^ (4 * (1 / (2 * α)) - 1) * ((1 + ‖y‖) ^ 4 * ‖S z‖) := by ring
      _ ≤ cB * C1 := mul_le_mul hcle hP4 (by positivity) hcBn
  · refine le_trans ?_ (le_max_right _ _)
    refine (mul_le_mul_of_nonneg_left (drift_norm_le α a μ hα0 hμ S.differentiable y)
      (by positivity)).trans ?_
    rw [← hzdef]
    calc (1 + ‖y‖) ^ 4 * (μ⁻¹ * ((|1 - 4 * (1 / (2 * α))| + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) * ‖S z‖ +
          (1 / (2 * α) + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) * μ ^ (1 / (2 * α)) *
            (‖fderiv ℝ S z‖ * (1 + ‖y‖))))
        = μ⁻¹ * ((|1 - 4 * (1 / (2 * α))| + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) *
            ((1 + ‖y‖) ^ 4 * ‖S z‖) + (1 / (2 * α) + |a|) * μ ^ (4 * (1 / (2 * α)) - 1) *
            μ ^ (1 / (2 * α)) * ((1 + ‖y‖) ^ 4 * (‖fderiv ℝ S z‖ * (1 + ‖y‖)))) := by ring
      _ ≤ lo⁻¹ * ((|1 - 4 * (1 / (2 * α))| + |a|) * cB * C1 + (1 / (2 * α) + |a|) * cB * kB * C1) := by
        gcongr

theorem le_one_add_rpow_six (x : ℝ) (hx : 0 ≤ x) : x ≤ 1 + x ^ (6 : ℝ) := by
  rcases le_total x 1 with h | h
  · linarith [Real.rpow_nonneg hx (6 : ℝ)]
  · have := Real.rpow_le_rpow_of_exponent_le h (by norm_num : (1 : ℝ) ≤ 6)
    rw [Real.rpow_one] at this
    linarith

theorem pair_bound (v f : Space → Space) (K : ℝ) (hK : ∀ y, (1 + ‖y‖) ^ 4 * ‖f y‖ ≤ K) (y : Space) :
    ‖inner ℝ (v y) (f y)‖ ≤ K * (1 + ‖y‖) ^ (-(4 : ℝ)) + K * ‖v y‖ ^ (6 : ℝ) := by
  have hK0 : 0 ≤ K := le_trans (by positivity) (hK 0)
  have hA : 0 < 1 + ‖y‖ := by positivity
  have e : (1 + ‖y‖) ^ (-(4 : ℝ)) = ((1 + ‖y‖) ^ 4)⁻¹ := by
    rw [Real.rpow_neg hA.le]
    norm_cast
  have hw0 : 0 ≤ ((1 + ‖y‖) ^ 4)⁻¹ := by positivity
  have hw1 : ((1 + ‖y‖) ^ 4)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg y]))
  have hf : ‖f y‖ ≤ K * ((1 + ‖y‖) ^ 4)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
    exact hK y
  have h6 := le_one_add_rpow_six ‖v y‖ (norm_nonneg _)
  have h6n : 0 ≤ ‖v y‖ ^ (6 : ℝ) := Real.rpow_nonneg (norm_nonneg _) _
  rw [e, Real.norm_eq_abs]
  calc |inner ℝ (v y) (f y)| ≤ ‖v y‖ * ‖f y‖ := abs_real_inner_le_norm _ _
    _ ≤ (1 + ‖v y‖ ^ (6 : ℝ)) * (K * ((1 + ‖y‖) ^ 4)⁻¹) :=
        mul_le_mul h6 hf (norm_nonneg _) (by positivity)
    _ = K * ((1 + ‖y‖) ^ 4)⁻¹ + K * (‖v y‖ ^ (6 : ℝ) * ((1 + ‖y‖) ^ 4)⁻¹) := by ring
    _ ≤ K * ((1 + ‖y‖) ^ 4)⁻¹ + K * ‖v y‖ ^ (6 : ℝ) := by
        gcongr
        exact mul_le_of_le_one_right h6n hw1

theorem continuous_turn : Continuous axialTurn := by
  refine (LipschitzWith.of_dist_le_mul fun x y => ?_).continuous (K := 1)
  rw [dist_eq_norm, dist_eq_norm, ← turn_sub, NNReal.coe_one, one_mul]
  exact norm_turn_le _

theorem continuous_simAdj (α a μ : ℝ) (S : 𝓢(Space, Space)) : Continuous (simAdj α a μ S) := by
  rw [simAdj_eq]
  have hR := (axialRotation (-(a * Real.log μ))).continuous
  have hR' := (axialRotation (a * Real.log μ)).continuous
  have hS := S.continuous
  fun_prop

theorem continuous_drift (α a μ : ℝ) (S : 𝓢(Space, Space)) :
    Continuous (fun y => μ⁻¹ • driftAdjoint α a (simAdj α a μ S) y) := by
  have hd : Continuous (fderiv ℝ (S : Space → Space)) :=
    (SchwartzMap.fderivCLM ℝ Space Space S).continuous
  have e : (fun y => μ⁻¹ • driftAdjoint α a (simAdj α a μ S) y) = fun y =>
      μ⁻¹ • ((1 - 4 * (1 / (2 * α))) • axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
          S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y))
        - (1 / (2 * α)) • axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
          fderiv ℝ S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)
            (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y))
        - a • (axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
          fderiv ℝ S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)
            (μ ^ (1 / (2 * α)) • axialTurn (axialRotation (a * Real.log μ) y)))
          - axialTurn (axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
            S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y))))) := by
    funext y
    rw [drift_simAdj α a μ S.differentiable]
  rw [e]
  have hR := (axialRotation (-(a * Real.log μ))).continuous
  have hR' := (axialRotation (a * Real.log μ)).continuous
  have hS := S.continuous
  have hT := continuous_turn
  have hz : Continuous fun y => μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y := by
    fun_prop
  have h1 : Continuous fun y => axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
      S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)) := by
    fun_prop
  have h2 : Continuous fun y => axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
      fderiv ℝ S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)
        (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)) := by
    fun_prop
  have h3 : Continuous fun y => axialRotation (-(a * Real.log μ)) (μ ^ (4 * (1 / (2 * α)) - 1) •
      fderiv ℝ S (μ ^ (1 / (2 * α)) • axialRotation (a * Real.log μ) y)
        (μ ^ (1 / (2 * α)) • axialTurn (axialRotation (a * Real.log μ) y))) := by
    fun_prop
  fun_prop

end Internal.SimDeriv

open Breakdown.Freq Internal.SimDeriv in
theorem simAdjDeriv : SimAdjDerivStatement := by
  intro α a hα x ψ hψ t ht
  obtain ⟨S, hS⟩ := Freq.Internal.NicePairing.rapid_of_nice hψ
  subst hS
  have hlo : 0 < (1 - t) / 2 := by linarith
  obtain ⟨K, hK⟩ := simAdj_bounds α a hα S (hi := 3 * (1 - t) / 2) hlo
  have hball : ∀ τ ∈ ball t ((1 - t) / 2), (1 - t) / 2 ≤ 1 - τ ∧ 1 - τ ≤ 3 * (1 - t) / 2 ∧ τ < 1 := by
    intro τ hτ
    rw [mem_ball, Real.dist_eq, abs_lt] at hτ
    refine ⟨by linarith, by linarith, by linarith⟩
  have hvm : AEStronglyMeasurable (velocity x : Space → Space) volume := Lp.aestronglyMeasurable _
  have hv6 : Integrable (fun y => ‖(velocity x : Space → Space) y‖ ^ (6 : ℝ)) volume := by
    have := (Lp.memLp (velocity x)).integrable_norm_rpow (by norm_num) (by norm_num)
    simpa using this
  have hw4 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4 : ℝ))) volume :=
    integrable_one_add_norm (by rw [finrank_euclideanSpace_fin]; norm_num)
  have hbi : Integrable (fun y : Space => K * (1 + ‖y‖) ^ (-(4 : ℝ)) +
      K * ‖(velocity x : Space → Space) y‖ ^ (6 : ℝ)) volume :=
    (hw4.const_mul K).add (hv6.const_mul K)
  have ht0 := hK (1 - t) (by linarith) (by linarith)
  have hFm : AEStronglyMeasurable (fun y => inner ℝ ((velocity x : Space → Space) y)
      (simAdj α a (1 - t) S y)) volume :=
    hvm.inner (continuous_simAdj α a (1 - t) S).aestronglyMeasurable
  have hFi : Integrable (fun y => inner ℝ ((velocity x : Space → Space) y)
      (simAdj α a (1 - t) S y)) volume :=
    hbi.mono' hFm (ae_of_all _ fun y => pair_bound _ _ K (fun y => (ht0 y).1) y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := t)
    (F := fun τ y => inner ℝ ((velocity x : Space → Space) y) (simAdj α a (1 - τ) S y))
    (F' := fun τ y => inner ℝ ((velocity x : Space → Space) y)
      ((1 - τ)⁻¹ • driftAdjoint α a (simAdj α a (1 - τ) S) y))
    (bound := fun y => K * (1 + ‖y‖) ^ (-(4 : ℝ)) + K * ‖(velocity x : Space → Space) y‖ ^ (6 : ℝ))
    (ball_mem_nhds t hlo)
    (Filter.Eventually.of_forall fun τ => hvm.inner (continuous_simAdj α a (1 - τ) S).aestronglyMeasurable)
    hFi (hvm.inner (continuous_drift α a (1 - t) S).aestronglyMeasurable)
    (ae_of_all _ fun y τ hτ => by
      obtain ⟨h1, h2, -⟩ := hball τ hτ
      exact pair_bound _ _ K (fun y => (hK (1 - τ) h1 h2 y).2) y)
    hbi
    (ae_of_all _ fun y τ hτ => by
      obtain ⟨-, -, h3⟩ := hball τ hτ
      have hG := hasDerivAt_simAdj α a S.differentiable y h3
      have := (innerSL ℝ ((velocity x : Space → Space) y)).hasFDerivAt.comp_hasDerivAt τ hG
      simpa only [Function.comp_def, innerSL_apply_apply] using this)
  exact key.2

end Breakdown.FracCert

/-
Copyright 2026 Anthropic, PBC
SPDX-License-Identifier: Apache-2.0

Adapted from `CCPoint/Framework/ODE/LinearODE.lean` and
`vendor/ChainPlanar/ChainPlanar/S4/Objects.lean` in the September CCPoint archive.
-/
import TorusEuler.LinearFlow

/-! # Linear ODE existence on a compact time interval -/

open Set
open scoped NNReal

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def radialClamp (R : ℝ) (x : E) : E :=
  (R / max ‖x‖ R) • x

private theorem norm_radialClamp_le {R : ℝ} (hR : 0 < R) (x : E) :
    ‖radialClamp R x‖ ≤ R ∧ ‖radialClamp R x‖ ≤ ‖x‖ := by
  have hmax : 0 < max ‖x‖ R := hR.trans_le (le_max_right _ _)
  rw [radialClamp, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hmax)]
  constructor
  · calc
      R / max ‖x‖ R * ‖x‖ = R * (‖x‖ / max ‖x‖ R) := by ring
      _ ≤ R * 1 := mul_le_mul_of_nonneg_left
        ((div_le_one hmax).2 (le_max_left _ _)) hR.le
      _ = R := mul_one _
  · exact mul_le_of_le_one_left (norm_nonneg _) ((div_le_one hmax).2 (le_max_right _ _))

private theorem radialClamp_lipschitz {R : ℝ} (hR : 0 < R) :
    LipschitzWith 2 (radialClamp (E := E) R) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  let X := max ‖x‖ R
  let Y := max ‖y‖ R
  have hX : 0 < X := hR.trans_le (le_max_right _ _)
  have hY : 0 < Y := hR.trans_le (le_max_right _ _)
  have hx : R / X ≤ 1 := (div_le_one hX).2 (le_max_right _ _)
  have hy : ‖y‖ / Y ≤ 1 := (div_le_one hY).2 (le_max_left _ _)
  have hdiff : |Y - X| ≤ ‖x - y‖ :=
    (abs_max_sub_max_le_abs _ _ _).trans (by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y)
  have hsplit : (R / X) • x - (R / Y) • y = (R / X) • (x - y) + (R / X - R / Y) • y := by
    rw [smul_sub, sub_smul]
    abel
  have hfirst : ‖(R / X) • (x - y)‖ ≤ ‖x - y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hR hX)]
    exact mul_le_of_le_one_left (norm_nonneg _) hx
  have hsecond : ‖(R / X - R / Y) • y‖ ≤ ‖x - y‖ := by
    have hfrac : R / X - R / Y = (R / X) * ((Y - X) / Y) := by
      field_simp
    rw [norm_smul, Real.norm_eq_abs, hfrac, abs_mul, abs_of_pos (div_pos hR hX),
      abs_div, abs_of_pos hY]
    calc
      R / X * (|Y - X| / Y) * ‖y‖ = R / X * |Y - X| * (‖y‖ / Y) := by ring
      _ ≤ 1 * ‖x - y‖ * 1 := by gcongr
      _ = ‖x - y‖ := by simp
  rw [dist_eq_norm, dist_eq_norm]
  change ‖(R / X) • x - (R / Y) • y‖ ≤ 2 * ‖x - y‖
  rw [hsplit, two_mul]
  exact (norm_add_le _ _).trans (add_le_add hfirst hsecond)

private theorem norm_le_exp_of_hasDerivWithinAt_Icc_left {x d : ℝ → E} {a b K : ℝ}
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (d t) (Icc a b) t)
    (hd : ∀ t ∈ Icc a b, ‖d t‖ ≤ K * ‖x t‖) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t‖ ≤ ‖x a‖ * Real.exp (K * (t - a)) := by
  rw [← gronwallBound_ε0]
  exact norm_le_gronwallBound_of_norm_deriv_right_le (fun s hs => (hx s hs).continuousWithinAt)
    (fun s hs => (hx s (Ico_subset_Icc_self hs)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hs)) le_rfl
    (fun s hs => by simpa only [add_zero] using hd s (Ico_subset_Icc_self hs)) t ht

private theorem norm_le_exp_of_hasDerivWithinAt_Icc {x d : ℝ → E} {a b t₀ K : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hK : 0 ≤ K)
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (d t) (Icc a b) t)
    (hd : ∀ t ∈ Icc a b, ‖d t‖ ≤ K * ‖x t‖) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖x t‖ ≤ ‖x t₀‖ * Real.exp (K * (b - a)) := by
  rcases le_total t₀ t with hle | hle
  · have hsub : Icc t₀ b ⊆ Icc a b := Icc_subset_Icc_left ht₀.1
    exact (norm_le_exp_of_hasDerivWithinAt_Icc_left (fun s hs => (hx s (hsub hs)).mono hsub)
      (fun s hs => hd s (hsub hs)) ⟨hle, ht.2⟩).trans
      (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (sub_le_sub ht.2 ht₀.1) hK)) (norm_nonneg _))
  · have hmaps : MapsTo (fun s : ℝ => -s) (Icc (-t₀) (-a)) (Icc a b) := by
      intro s hs
      exact ⟨le_neg.mp hs.2, (neg_le.mp hs.1).trans ht₀.2⟩
    have hy (s : ℝ) (hs : s ∈ Icc (-t₀) (-a)) :
        HasDerivWithinAt (fun r => x (-r)) (-d (-s)) (Icc (-t₀) (-a)) s := by
      simpa only [Function.comp_def, neg_one_smul] using
        (hx (-s) (hmaps hs)).scomp s (hasDerivWithinAt_neg s _) hmaps
    have hyb (s : ℝ) (hs : s ∈ Icc (-t₀) (-a)) : ‖-d (-s)‖ ≤ K * ‖x (-s)‖ := by
      simpa only [norm_neg] using hd (-s) (hmaps hs)
    have hbound := norm_le_exp_of_hasDerivWithinAt_Icc_left hy hyb
      (t := -t) ⟨neg_le_neg hle, neg_le_neg ht.1⟩
    simp only [neg_neg] at hbound
    refine hbound.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ?_ hK)) (norm_nonneg _))
    linarith [ht₀.2, ht.1]

variable [CompleteSpace E]

/-- A continuous homogeneous linear ODE has a solution on the full closed interval,
with initial data at any point of the interval. -/
theorem linearODE_exists_Icc_of_mem {A : ℝ → E →L[ℝ] E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (A t (x t)) (Icc a b) t := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hA
  let K : ℝ≥0 := Real.toNNReal C
  have hK (t : ℝ) (ht : t ∈ Icc a b) : ‖A t‖ ≤ (K : ℝ) :=
    (hC t ht).trans (Real.le_coe_toNNReal _)
  let R := max 1 (‖x₀‖ * Real.exp (K * (b - a)))
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  let L : ℝ≥0 := K * ⟨R, hR.le⟩
  let T : ℝ≥0 := ⟨b - a, sub_nonneg.mpr (ht₀.1.trans ht₀.2)⟩
  -- Truncate the vector field in space so Picard–Lindelöf applies on the full interval.
  have hPicard : IsPicardLindelof (fun t x => A t (radialClamp R x))
      (⟨t₀, ht₀⟩ : Icc a b) x₀ (L * T) 0 L (K * 2) := by
    constructor
    · intro t ht
      exact ((ContinuousLinearMap.lipschitzWith_of_opNorm_le (hK t ht)).comp
        (radialClamp_lipschitz hR)).lipschitzOnWith
    · intro x _
      exact hA.clm_apply continuousOn_const
    · intro t ht x _
      exact ((A t).le_opNorm _).trans
        (mul_le_mul (hK t ht) (norm_radialClamp_le hR x).1 (norm_nonneg _) K.coe_nonneg)
    · change (L : ℝ) * max (b - t₀) (t₀ - a) ≤ (L : ℝ) * (b - a) - 0
      rw [sub_zero]
      exact mul_le_mul_of_nonneg_left
        (max_le (sub_le_sub_left ht₀.1 b) (sub_le_sub_right ht₀.2 a)) L.coe_nonneg
  obtain ⟨x, hx₀, hx⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  have hderiv (t : ℝ) (ht : t ∈ Icc a b) : ‖A t (radialClamp R (x t))‖ ≤ K * ‖x t‖ :=
    ((A t).le_opNorm _).trans
      (mul_le_mul (hK t ht) (norm_radialClamp_le hR (x t)).2 (norm_nonneg _) K.coe_nonneg)
  refine ⟨x, hx₀, fun t ht => ?_⟩
  have hnorm : ‖x t‖ ≤ R := by
    have hbound := norm_le_exp_of_hasDerivWithinAt_Icc ht₀ K.coe_nonneg hx hderiv ht
    rw [hx₀] at hbound
    exact hbound.trans (le_max_right _ _)
  -- The a priori bound keeps the solution where the truncation is the identity.
  simpa only [radialClamp, max_eq_right hnorm, div_self hR.ne', one_smul] using hx t ht

/-- The left endpoint version of homogeneous linear ODE existence. -/
theorem linearODE_exists_Icc {A : ℝ → E →L[ℝ] E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, x a = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (A t (x t)) (Icc a b) t :=
  linearODE_exists_Icc_of_mem ⟨le_rfl, hab⟩ hA x₀

/-- A continuous forced linear ODE has a solution on the full closed time interval. -/
theorem linearODE_inhom_exists_Icc {A : ℝ → E →L[ℝ] E} {g : ℝ → E} {a b t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc a b) (hA : ContinuousOn A (Icc a b))
    (hg : ContinuousOn g (Icc a b)) (x₀ : E) :
    ∃ x : ℝ → E, x t₀ = x₀ ∧ ∀ t ∈ Icc a b,
      HasDerivWithinAt x (A t (x t) + g t) (Icc a b) t := by
  let B (t : ℝ) : (E × ℝ) →L[ℝ] (E × ℝ) :=
    (ContinuousLinearMap.inl ℝ E ℝ).comp ((A t).comp (ContinuousLinearMap.fst ℝ E ℝ) +
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (g t))
  have hB : ContinuousOn B (Icc a b) :=
    continuousOn_const.clm_comp ((hA.clm_comp continuousOn_const).add
      ((ContinuousLinearMap.smulRightL ℝ (E × ℝ) E (ContinuousLinearMap.snd ℝ E ℝ)).continuous
        |>.comp_continuousOn hg))
  obtain ⟨z, hz₀, hz⟩ := linearODE_exists_Icc_of_mem ht₀ hB (x₀, 1)
  have hz₂ (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt (fun s => (z s).2) ((0 : ℝ →L[ℝ] ℝ) (z t).2) (Icc a b) t := by
    simpa [B, Function.comp_def] using
      (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)
  have hone (t : ℝ) (ht : t ∈ Icc a b) : (z t).2 = 1 :=
    linearODE_unique_of_mem ordConnected_Icc ht₀ continuousOn_const hz₂
      (fun r _ => by simpa using hasDerivWithinAt_const r (Icc a b) (1 : ℝ))
      (by simp [hz₀]) ht
  refine ⟨fun t => (z t).1, by simp [hz₀], fun t ht => ?_⟩
  simpa [B, hone t ht, Function.comp_def] using
    (ContinuousLinearMap.fst ℝ E ℝ).hasFDerivAt.comp_hasDerivWithinAt t (hz t ht)

end TorusEuler

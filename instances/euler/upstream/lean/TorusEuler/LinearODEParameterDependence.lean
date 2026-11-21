import TorusEuler.LinearFlowExistence

/-! Uniform parameter dependence for continuous linear ODEs. -/

open Set
open scoped NNReal

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem gronwallBound_scale_initial_forcing (D K F d t : ℝ) :
    gronwallBound (D * d) K (F * d) t = gronwallBound D K F t * d := by
  by_cases hK : K = 0 <;> simp [gronwallBound, hK] <;> ring

omit [CompleteSpace E] in
/-- Uniform boundedness and Lipschitz dependence of the coefficients and
forcing give joint continuity of the closed-interval solution in time and
parameters. The parameter may include both the label and the phase. -/
theorem linearODE_parameters_joint_continuous
    {P : Type*} [PseudoMetricSpace P] {A : ℝ → P → E →L[ℝ] E} {x f : ℝ → P → E}
    {a b C : ℝ} {K L H D : ℝ≥0} (hab : a ≤ b) (hC : 0 ≤ C)
    (hA : ∀ t ∈ Icc a b, ∀ p, ‖A t p‖ ≤ K)
    (hAlip : ∀ t ∈ Icc a b, LipschitzWith L (A t))
    (hflip : ∀ t ∈ Icc a b, LipschitzWith H (f t))
    (h₀ : LipschitzWith D (x a))
    (hx : ∀ p, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => x u p)
      (A t p (x t p) + f t p) (Icc a b) t)
    (hX : ∀ t ∈ Icc a b, ∀ p, ‖x t p‖ ≤ C) :
    ∃ B : ℝ≥0, (∀ t ∈ Icc a b, LipschitzWith B (x t)) ∧
      ContinuousOn (Function.uncurry x) (Icc a b ×ˢ univ) := by
  let F := (L : ℝ) * C + H
  let B := gronwallBound D K F (b - a)
  have hF₀ : 0 ≤ F := add_nonneg (mul_nonneg L.coe_nonneg hC) H.coe_nonneg
  have hB₀ : 0 ≤ B := by
    have hmon := gronwallBound_mono D.coe_nonneg hF₀ K.coe_nonneg (sub_nonneg.mpr hab)
    rw [gronwallBound_x0] at hmon
    exact D.coe_nonneg.trans hmon
  have hDiff (t : ℝ) (ht : t ∈ Icc a b) (p q : P) :
      ‖x t p - x t q‖ ≤ B * dist p q := by
    let Δ (u : ℝ) := x u p - x u q
    let dΔ (u : ℝ) := A u p (Δ u) + (A u p - A u q) (x u q) + (f u p - f u q)
    have hΔ (u : ℝ) (hu : u ∈ Icc a b) : HasDerivWithinAt Δ (dΔ u) (Icc a b) u := by
      refine ((hx p u hu).sub (hx q u hu)).congr_deriv ?_
      simp only [dΔ, Δ, sub_apply, map_sub]
      abel
    have hinit : ‖Δ a‖ ≤ (D : ℝ) * dist p q := by
      simpa only [dist_eq_norm] using h₀.dist_le_mul p q
    have hrate (u : ℝ) (hu : u ∈ Icc a b) : ‖dΔ u‖ ≤ K * ‖Δ u‖ + F * dist p q := by
      have hap := (A u p).le_of_opNorm_le (hA u hu p) (Δ u)
      have haΔ : ‖A u p - A u q‖ ≤ (L : ℝ) * dist p q := by
        simpa only [dist_eq_norm] using (hAlip u hu).dist_le_mul p q
      have hfΔ : ‖f u p - f u q‖ ≤ (H : ℝ) * dist p q := by
        simpa only [dist_eq_norm] using (hflip u hu).dist_le_mul p q
      have haX : ‖(A u p - A u q) (x u q)‖ ≤ ((L : ℝ) * dist p q) * C :=
        ((A u p - A u q).le_opNorm _).trans
          (mul_le_mul haΔ (hX u hu q) (norm_nonneg _) (mul_nonneg L.coe_nonneg dist_nonneg))
      calc
        _ ≤ ‖A u p (Δ u)‖ + ‖(A u p - A u q) (x u q)‖ + ‖f u p - f u q‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ K * ‖Δ u‖ + ((L : ℝ) * dist p q) * C + H * dist p q :=
          add_le_add (add_le_add hap haX) hfΔ
        _ = _ := by unfold F; ring
    have hbound := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hΔ)
      (fun u hu => (hΔ u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hu))
      hinit (fun u hu => hrate u (Ico_subset_Icc_self hu)) t ht
    rw [gronwallBound_scale_initial_forcing] at hbound
    exact hbound.trans (mul_le_mul_of_nonneg_right
      (gronwallBound_mono D.coe_nonneg hF₀ K.coe_nonneg (sub_le_sub_right ht.2 a)) dist_nonneg)
  have hL (t : ℝ) (ht : t ∈ Icc a b) : LipschitzWith ⟨B, hB₀⟩ (x t) :=
    LipschitzWith.of_dist_le_mul fun p q => by
      rw [dist_eq_norm]
      exact hDiff t ht p q
  exact ⟨⟨B, hB₀⟩, hL, continuousOn_prod_of_continuousOn_lipschitzOnWith' _ ⟨B, hB₀⟩
    (fun t ht => (hL t ht).lipschitzOnWith)
    (fun p _ => HasDerivWithinAt.continuousOn (hx p))⟩

/-- The fixed-coordinate solution exists as one jointly continuous family.
Bounds on the data supply the uniform solution bound used in its dependence
on the label and phase. -/
theorem exists_jointly_continuous_parameterized_linearODE
    {P : Type*} [PseudoMetricSpace P] {A : ℝ → P → E →L[ℝ] E} {f : ℝ → P → E}
    {a b C₀ C₁ : ℝ} {K L H D : ℝ≥0} (hab : a ≤ b) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hA : ∀ t ∈ Icc a b, ∀ p, ‖A t p‖ ≤ K)
    (hAc : ∀ p, ContinuousOn (fun t => A t p) (Icc a b))
    (hAlip : ∀ t ∈ Icc a b, LipschitzWith L (A t))
    (hF : ∀ t ∈ Icc a b, ∀ p, ‖f t p‖ ≤ C₁)
    (hFc : ∀ p, ContinuousOn (fun t => f t p) (Icc a b))
    (hFlip : ∀ t ∈ Icc a b, LipschitzWith H (f t))
    (x₀ : P → E) (h₀ : LipschitzWith D x₀) (h₀b : ∀ p, ‖x₀ p‖ ≤ C₀) :
    ∃ x : ℝ → P → E, x a = x₀ ∧
      (∀ p, ∀ t ∈ Icc a b, HasDerivWithinAt (fun u => x u p)
        (A t p (x t p) + f t p) (Icc a b) t) ∧
      (∀ t ∈ Icc a b, ∀ p, ‖x t p‖ ≤ gronwallBound C₀ K C₁ (b - a)) ∧
      ∃ B : ℝ≥0, (∀ t ∈ Icc a b, LipschitzWith B (x t)) ∧
        ContinuousOn (Function.uncurry x) (Icc a b ×ˢ univ) := by
  let C := gronwallBound C₀ K C₁ (b - a)
  have hC : 0 ≤ C := by
    have hmon := gronwallBound_mono hC₀ hC₁ K.coe_nonneg (sub_nonneg.mpr hab)
    rw [gronwallBound_x0] at hmon
    exact hC₀.trans hmon
  have hxExist (p : P) := linearODE_inhom_exists_Icc ⟨le_rfl, hab⟩ (hAc p) (hFc p) (x₀ p)
  choose xp hx₀ hx using hxExist
  let x (t : ℝ) (p : P) := xp p t
  have hinit : x a = x₀ := funext hx₀
  have hsBound (t : ℝ) (ht : t ∈ Icc a b) (p : P) : ‖x t p‖ ≤ C := by
    have hinitp : ‖xp p a‖ ≤ C₀ := by simpa only [hx₀ p] using h₀b p
    have hrate (u : ℝ) (hu : u ∈ Icc a b) : ‖A u p (xp p u) + f u p‖ ≤ K * ‖xp p u‖ + C₁ :=
      (norm_add_le _ _).trans (add_le_add ((A u p).le_of_opNorm_le (hA u hu p) _) (hF u hu p))
    have hbound := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn (hx p))
      (fun u hu => (hx p u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem hu))
      hinitp (fun u hu => hrate u (Ico_subset_Icc_self hu)) t ht
    exact hbound.trans (gronwallBound_mono hC₀ hC₁ K.coe_nonneg (sub_le_sub_right ht.2 a))
  refine ⟨x, hinit, hx, hsBound, ?_⟩
  exact linearODE_parameters_joint_continuous hab hC hA hAlip hFlip (hinit.symm ▸ h₀) hx hsBound

end TorusEuler

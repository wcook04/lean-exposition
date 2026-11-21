import TorusEuler.TerminalCoefficientTimeProduct

/-! Quantitative time differentiation for the actual variational equations. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spatial cost at each time order for a linear equation with a
time-dependent coefficient. -/
def terminalLinearODECost (B : E →L[ℝ] F →L[ℝ] F) (C C₀ : ℕ → ℝ) :
    ℕ → ℕ → ℝ
  | 0 => C₀
  | q+1 =>
    let M := terminalLinearODECost B C C₀ q
    fun n => M n + terminalMixedProductCost q B C M n

theorem terminalLinearODECost_nonneg (B : E →L[ℝ] F →L[ℝ] F) {C C₀ : ℕ → ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n) :
    ∀ q n, 0 ≤ terminalLinearODECost B C C₀ q n := by
  intro q
  induction q with
  | zero => exact hC₀
  | succ q ih =>
    exact fun n => add_nonneg (ih n) (terminalMixedProductCost_nonneg q B hC ih n)

set_option maxHeartbeats 450000 in
/-- Time differentiation of a linear equation uses the coefficient and the
solution through the previous time order. -/
theorem terminalMixedJetBound_of_linearODE {a b D A A₀ : ℝ} {p : ℕ} {C C₀ : ℕ → ℝ}
    {f : ℝ → Vec3 → E} {g : ℝ → Vec3 → F}
    (B : E →L[ℝ] F →L[ℝ] F) (hab : a < b)
    (hD : 0 ≤ D) (hA : 1 ≤ A) (hA₀ : 0 ≤ A₀)
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (hgreg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc a b ×ˢ (univ : Set Vec3)))
    (hODE : ∀ t ∈ Icc a b, ∀ x, derivWithin (fun r => g r x) (Icc a b) t = B (f t x) (g t x))
    (hg₀ : TerminalMixedJetBound a b 0 p D A₀ C₀ g) (q : ℕ)
    (hf : TerminalMixedJetBound a b q p D A C f) :
    TerminalMixedJetBound a b q p D (A₀ * A ^ q) (terminalLinearODECost B C C₀ q) g := by
  induction q with
  | zero => simpa only [terminalLinearODECost, pow_zero, mul_one] using hg₀
  | succ q ih =>
    let M := terminalLinearODECost B C C₀ q
    let P := terminalMixedProductCost q B C M
    let Aold := A₀ * A ^ q
    let Anew := A₀ * A ^ (q + 1)
    have hq := ih (hf.mono_order (Nat.le_succ q))
    have hM : ∀ n, 0 ≤ M n := terminalLinearODECost_nonneg B hC hC₀ q
    have hP : ∀ n, 0 ≤ P n := terminalMixedProductCost_nonneg q B hC hM
    have hAold : 0 ≤ Aold := mul_nonneg hA₀ (pow_nonneg (zero_le_one.trans hA) _)
    have hn : Aold ≤ Anew := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hA (Nat.le_succ _)) hA₀
    have hg' := TerminalMixedJetBound.bilinear B hab hD (zero_le_one.trans hA) hAold
      hC hM (hf.mono_order (Nat.le_succ q)) hq hfreg hgreg
    have hgTime := hg'.congr (fun t ht x => (hODE t ht x).symm)
    intro i hi n t ht x
    by_cases h : i ≤ q
    · exact ((hq.mono_amplitude hD hM hn).mono_constant hD (hAold.trans hn)
        (fun m => le_add_of_nonneg_right (hP m))) i h n t ht x
    · have heq : i = q + 1 := by omega
      rw [heq, slabTimeJet_succ']
      have hbound := hgTime q le_rfl n t ht x
      rw [show A * (A₀ * A ^ q) = Anew by dsimp only [Anew]; rw [pow_succ]; ring] at hbound
      exact hbound.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hM n)) (hAold.trans hn))
        (pow_nonneg hD _))

variable {U : Velocity} {X : ℝ → Velocity} {T : ℝ}

/-- The actual inverse deformation satisfies the inverse variational equation
at every point on the slab. -/
theorem IsLabelFlowOn.terminal_hasDerivWithinAt_inverseDeformation
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x : Vec3) :
    HasDerivWithinAt (fun r => fderiv ℝ (X r 0) (X 0 r x))
      (-((fderiv ℝ (X t 0) (X 0 t x)).comp (fderiv ℝ (U t) (X 0 t x)))) (Icc 0 T) t := by
  let F (r : ℝ) := fderiv ℝ (X 0 r) x
  let G (r : ℝ) := fderiv ℝ (X r 0) (X 0 r x)
  let M := fderiv ℝ (U t) (X 0 t x)
  let dG := derivWithin G (Icc 0 T) t
  have h₀ : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hreg := hX.contDiffOn_inverseLabelDerivative hT hU hper
  have htime : ContDiffOn ℝ ∞ G (Icc 0 T) :=
    terminal_contDiffOn_timeSlice (f := fun r a => fderiv ℝ (X r 0) (X 0 r a)) hreg x
  have hG : HasDerivWithinAt G dG (Icc 0 T) t :=
    (htime.differentiableOn (by simp) t ht).hasDerivWithinAt
  have hF : HasDerivWithinAt F (M.comp (F t)) (Icc 0 T) t :=
    (hX.labelDerivative_evolves hT hU₂ hper h₀ x).2 t ht
  have hInv : ∀ r ∈ Icc 0 T, (G r).comp (F r) = ContinuousLinearMap.id ℝ Vec3 :=
    fun r hr => (hX.labelDerivative_inverse hT hU₂ hper h₀ hr x).1
  have hEq : dG.comp (F t) + (G t).comp (M.comp (F t)) = 0 := by
    have hcomp := hG.clm_comp hF
    calc
      _ = derivWithin (fun r => (G r).comp (F r)) (Icc 0 T) t :=
        (hcomp.derivWithin (uniqueDiffOn_Icc hT t ht)).symm
      _ = derivWithin (fun _ => ContinuousLinearMap.id ℝ Vec3) (Icc 0 T) t :=
        derivWithin_congr hInv (hInv t ht)
      _ = 0 := by simp
  have hFG := (hX.labelDerivative_inverse hT hU₂ hper h₀ ht x).2
  have hdG : dG = -((G t).comp M) := by
    apply ContinuousLinearMap.ext
    intro y
    have hfg : F t (G t y) = y := by
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
        congrArg (fun B : Vec3 →L[ℝ] Vec3 => B y) hFG
    have h := congrArg (fun B : Vec3 →L[ℝ] Vec3 => B (G t y)) hEq
    simp only [add_apply, ContinuousLinearMap.comp_apply, hfg,
      zero_apply] at h
    exact eq_neg_of_add_eq_zero_left h
  exact hdG ▸ hG

end

end TorusEuler

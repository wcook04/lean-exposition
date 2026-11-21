import TorusEuler.TerminalCoefficientTimeProduct

/-! Polynomial control of the actual reciprocal normalized carrier length. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

/-- Time differentiation of a reciprocal needs only polynomial growth in the
derivative amplitude and the initial reciprocal amplitude. -/
def terminalReciprocalTimeAmplitude (A B : ℝ) : ℕ → ℝ
  | 0 => B
  | q+1 =>
    let W := terminalReciprocalTimeAmplitude A B q
    W + A * (W * W)

theorem terminalReciprocalTimeAmplitude_nonneg {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∀ q, 0 ≤ terminalReciprocalTimeAmplitude A B q := by
  intro q
  induction q with
  | zero => exact hB
  | succ q ih => exact add_nonneg ih (mul_nonneg hA (mul_nonneg ih ih))

/-- A spatial order cost for the reciprocal at each bounded time order. -/
def terminalReciprocalTimeCost (C C₀ : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0 => C₀
  | q+1 =>
    let M := terminalReciprocalTimeCost C C₀ q
    let S := terminalMixedProductCost q (ContinuousLinearMap.mul ℝ ℝ) M M
    fun n => M n + terminalMixedProductCost q (-(ContinuousLinearMap.mul ℝ ℝ)) C S n

theorem terminalReciprocalTimeCost_nonneg {C C₀ : ℕ → ℝ}
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n) :
    ∀ q n, 0 ≤ terminalReciprocalTimeCost C C₀ q n := by
  intro q
  induction q with
  | zero => exact hC₀
  | succ q ih =>
    exact fun n => add_nonneg (ih n) (terminalMixedProductCost_nonneg q
      (-(ContinuousLinearMap.mul ℝ ℝ)) hC (terminalMixedProductCost_nonneg q _ ih ih) n)

set_option maxHeartbeats 750000 in
/-- A reciprocal preserves the common spatial slope when the spatial
reciprocal estimates at time order zero and the coefficient time jets
are supplied. -/
theorem terminalMixedJetBound_of_reciprocal {a b D A B : ℝ} {p : ℕ} {C C₀ : ℕ → ℝ}
    {f : ℝ → Vec3 → ℝ}
    (hab : a < b) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (hnz : ∀ t ∈ Icc a b, ∀ x, f t x ≠ 0)
    (hg₀ : TerminalMixedJetBound a b 0 p D B C₀ (fun t x => (f t x)⁻¹)) (q : ℕ)
    (hf : TerminalMixedJetBound a b q p D A C f) :
    TerminalMixedJetBound a b q p D (terminalReciprocalTimeAmplitude A B q)
      (terminalReciprocalTimeCost C C₀ q) (fun t x => (f t x)⁻¹) := by
  let g (t : ℝ) (x : Vec3) := (f t x)⁻¹
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hgreg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc a b ×ˢ (univ : Set Vec3)) :=
    hfreg.inv (fun z hz => hnz z.1 hz.1 z.2)
  induction q with
  | zero => exact hg₀
  | succ q ih =>
    let W := terminalReciprocalTimeAmplitude A B q
    let M := terminalReciprocalTimeCost C C₀ q
    let S := terminalMixedProductCost q L M M
    let P := terminalMixedProductCost q (-L) C S
    let Wnew := W + A * (W * W)
    let fd (t : ℝ) (x : Vec3) := derivWithin (fun r => f r x) (Icc a b) t
    have hq := ih (hf.mono_order (Nat.le_succ q))
    have hW : 0 ≤ W := terminalReciprocalTimeAmplitude_nonneg hA hB q
    have hM : ∀ n, 0 ≤ M n := terminalReciprocalTimeCost_nonneg hC hC₀ q
    have hS : ∀ n, 0 ≤ S n := terminalMixedProductCost_nonneg q L hM hM
    have hP : ∀ n, 0 ≤ P n := terminalMixedProductCost_nonneg q (-L) hC hS
    have hh : TerminalMixedJetBound a b q p D (W * W) S (fun t x => g t x * g t x) :=
      TerminalMixedJetBound.bilinear L hab hD hW hW hM hM hq hq hgreg hgreg
    have hRight := TerminalMixedJetBound.bilinear (-L) hab hD hA (mul_nonneg hW hW) hC hS
      hf.timeDerivative hh (contDiffOn_sliceTimeDerivWithin_Icc hab hfreg) (hgreg.mul hgreg)
    have hODE (t : ℝ) (ht : t ∈ Icc a b) (x : Vec3) :
        (-L) (fd t x) (g t x * g t x) = derivWithin (fun r => g r x) (Icc a b) t := by
      have h := ((terminal_contDiffOn_timeSlice hfreg x).differentiableOn (by simp) t ht).hasDerivWithinAt
      have hi := (h.inv (hnz t ht x)).derivWithin (uniqueDiffOn_Icc hab t ht)
      rw [show derivWithin (fun r => g r x) (Icc a b) t = _ from hi]
      change -(fd t x * (g t x * g t x)) = -fd t x / (f t x)^2
      dsimp only [g]
      rw [div_eq_mul_inv, pow_two, mul_inv_rev]; ring
    have hTime := hRight.congr hODE
    have hWright : 0 ≤ A * (W * W) := mul_nonneg hA (mul_nonneg hW hW)
    have hWold : W ≤ Wnew := le_add_of_nonneg_right hWright
    have hWinc : A * (W * W) ≤ Wnew := le_add_of_nonneg_left hW
    have hWnew : 0 ≤ Wnew := hW.trans hWold
    intro i hi n t ht x
    by_cases h : i ≤ q
    · exact ((hq.mono_amplitude hD hM hWold).mono_constant hD hWnew
        (fun m => le_add_of_nonneg_right (hP m))) i h n t ht x
    · have heq : i = q + 1 := by omega
      rw [heq, slabTimeJet_succ']
      exact ((hTime.mono_amplitude hD hP hWinc).mono_constant hD hWnew
        (fun m => le_add_of_nonneg_left (hM m))) q le_rfl n t ht x

/-- The normalized covector's squared-norm reciprocal has controlled jets
at the same spatial slope as the covector. -/
theorem terminalMixedJetBound_inv_norm_sq {a b D A B : ℝ} {q p : ℕ}
    {C C₀ : ℕ → ℝ} {κ : ℝ → Vec3 → Vec3}
    (hab : a < b) (hD : 0 ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : ∀ n, 0 ≤ C n) (hC₀ : ∀ n, 0 ≤ C₀ n)
    (hκreg : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc a b ×ˢ (univ : Set Vec3)))
    (hκnz : ∀ t ∈ Icc a b, ∀ x, κ t x ≠ 0)
    (hκ : TerminalMixedJetBound a b q p D A C κ)
    (hrec : TerminalMixedJetBound a b 0 p D B C₀ (fun t x => (‖κ t x‖ ^ 2)⁻¹)) :
    TerminalMixedJetBound a b q p D (terminalReciprocalTimeAmplitude (A*A) B q)
      (terminalReciprocalTimeCost (terminalMixedProductCost q (innerSL ℝ : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ) C C) C₀ q)
      (fun t x => (‖κ t x‖ ^ 2)⁻¹) := by
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hbound := TerminalMixedJetBound.bilinear L hab hD hA hA hC hC hκ hκ hκreg hκreg
  have hnorm := hbound.congr (fun t _ x => real_inner_self_eq_norm_sq (κ t x))
  have hreg := hκreg.norm_sq ℝ
  exact terminalMixedJetBound_of_reciprocal (f := fun t x => ‖κ t x‖ ^ 2) hab hD (mul_nonneg hA hA) hB
    (terminalMixedProductCost_nonneg q L hC hC) hC₀ hreg
    (fun t ht x => pow_ne_zero _ (norm_ne_zero_iff.mpr (hκnz t ht x))) hrec q hnorm

end

end TorusEuler

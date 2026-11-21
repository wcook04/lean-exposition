import Breakdown.Profile.StatementsSlice

open scoped ContDiff
open MeasureTheory Set Real

noncomputable section

namespace Breakdown

private lemma slice_contDiff {W : ℝ → Space → Space}
    (hW : ContDiff ℝ ∞ (fun z : ℝ × Space => W z.1 z.2)) (s : ℝ) :
    ContDiff ℝ ∞ (W s) :=
  hW.comp (contDiff_prodMk_right s)

private lemma slice_contDiff_scalar {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) (s : ℝ) :
    ContDiff ℝ ∞ (q s) :=
  hq.comp (contDiff_prodMk_right s)

private lemma norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private lemma norm_sumSecondPartialsAt_le (v : Space → Space) (x : Space) :
    ‖sumSecondPartialsAt v x‖ ≤ 3 * ‖iteratedFDeriv ℝ 2 v x‖ := by
  have key : ∀ i : Fin 3,
      ‖iteratedFDeriv ℝ 2 v x ![unitVector i, unitVector i]‖ ≤ ‖iteratedFDeriv ℝ 2 v x‖ := by
    intro i
    have h := (iteratedFDeriv ℝ 2 v x).le_opNorm ![unitVector i, unitVector i]
    simpa [Fin.prod_univ_two, norm_unitVector] using h
  unfold sumSecondPartialsAt
  rw [Fin.sum_univ_three]
  have h3 := norm_add₃_le (E := Space)
    (a := iteratedFDeriv ℝ 2 v x ![unitVector 0, unitVector 0])
    (b := iteratedFDeriv ℝ 2 v x ![unitVector 1, unitVector 1])
    (c := iteratedFDeriv ℝ 2 v x ![unitVector 2, unitVector 2])
  linarith [key 0, key 1, key 2]

private lemma norm_gradientAt_le (p : Space → ℝ) (x : Space) :
    ‖gradientAt p x‖ ≤ 3 * ‖fderiv ℝ p x‖ := by
  have key : ∀ i : Fin 3, ‖fderiv ℝ p x (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ p x‖ := by
    intro i
    rw [norm_smul, norm_unitVector, mul_one]
    simpa [norm_unitVector] using (fderiv ℝ p x).le_opNorm (unitVector i)
  unfold gradientAt
  rw [Fin.sum_univ_three]
  have h3 := norm_add₃_le (E := Space)
    (a := fderiv ℝ p x (unitVector 0) • unitVector 0)
    (b := fderiv ℝ p x (unitVector 1) • unitVector 1)
    (c := fderiv ℝ p x (unitVector 2) • unitVector 2)
  linarith [key 0, key 1, key 2]

private lemma norm_advectionAt_le (v : Space → Space) (x : Space) :
    ‖advectionAt v x‖ ≤ ‖fderiv ℝ v x‖ * ‖v x‖ :=
  (fderiv ℝ v x).le_opNorm (v x)

theorem sliceDecay_holds : SliceDecay := by
  intro W q C h s
  refine ⟨slice_contDiff h.smooth s, h.div s, C, fun y => ⟨?_, ?_⟩⟩
  · have h0 := h.decay s y 0 (by norm_num)
    simpa using h0
  · have h1 := h.decay s y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at h1
    simpa using h1

theorem similarityDerivBound_holds : SimilarityDerivBound := by
  intro W q C h
  refine ⟨6 * C + C ^ 2, fun s y => ?_⟩
  set t : ℝ := 1 + ‖y‖ with ht
  have tpos : 0 < t := by positivity
  have e : deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y + (1 / 2 : ℝ) • fderiv ℝ (W s) y y
      = sumSecondPartialsAt (W s) y - advectionAt (W s) y - gradientAt (q s) y := by
    have hr := h.residual s y
    calc deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y + (1 / 2 : ℝ) • fderiv ℝ (W s) y y
        = deriv (fun σ => W σ y) s + (1 / 2 : ℝ) • W s y + (1 / 2 : ℝ) • fderiv ℝ (W s) y y
          - SimilarityResidual W q s y := by rw [hr, sub_zero]
      _ = sumSecondPartialsAt (W s) y - advectionAt (W s) y - gradientAt (q s) y := by
          unfold SimilarityResidual
          abel
  rw [e]
  have h0 : ‖W s y‖ ≤ C / t ^ 1 := by
    have := h.decay s y 0 (by norm_num)
    simpa using this
  have h1 : ‖fderiv ℝ (W s) y‖ ≤ C / t ^ 2 := by
    have := h.decay s y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at this
    simpa using this
  have h2 : ‖iteratedFDeriv ℝ 2 (W s) y‖ ≤ C / t ^ 3 := h.decay s y 2 (by norm_num)
  have hp : ‖fderiv ℝ (q s) y‖ ≤ C / t ^ 3 := h.decay_pressure s y
  have hL := norm_sumSecondPartialsAt_le (W s) y
  have hG := norm_gradientAt_le (q s) y
  have hA := norm_advectionAt_le (W s) y
  have hA' : ‖advectionAt (W s) y‖ ≤ C / t ^ 2 * (C / t ^ 1) := by
    refine hA.trans ?_
    exact mul_le_mul h1 h0 (norm_nonneg _) ((norm_nonneg _).trans h1)
  have hsum : ‖sumSecondPartialsAt (W s) y - advectionAt (W s) y - gradientAt (q s) y‖
      ≤ ‖sumSecondPartialsAt (W s) y‖ + ‖advectionAt (W s) y‖ + ‖gradientAt (q s) y‖ := by
    refine (norm_sub_le _ _).trans ?_
    gcongr
    exact norm_sub_le _ _
  have eq1 : C / t ^ 2 * (C / t ^ 1) = C ^ 2 / t ^ 3 := by
    field_simp
  have eq2 : (6 * C + C ^ 2) / t ^ 3 = 3 * (C / t ^ 3) + C ^ 2 / t ^ 3 + 3 * (C / t ^ 3) := by
    ring
  rw [eq2]
  rw [eq1] at hA'
  nlinarith [hsum, hL, hG, hA', h2, hp]

end Breakdown

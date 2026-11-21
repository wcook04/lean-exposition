import Breakdown.CertCell.BridgeStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private lemma cnormSq_nonneg_aux {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma norm_sum_mul_le_sqrt_cnormSq {β : Type*} [Fintype β] (x y : β → ℂ) :
    ‖∑ b, x b * y b‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq y) := by
  refine (norm_sum_le _ _).trans ?_
  simpa [cnormSq, norm_mul] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun b => ‖x b‖) (fun b => ‖y b‖)

private lemma sqrt_le_mul_sqrt_of_le_sq_mul {c d γ : ℝ} (hγ : 0 ≤ γ) (h : c ≤ γ ^ 2 * d) :
    Real.sqrt c ≤ γ * Real.sqrt d := by
  calc Real.sqrt c ≤ Real.sqrt (γ ^ 2 * d) := Real.sqrt_le_sqrt h
    _ = γ * Real.sqrt d := by rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ]

private lemma norm_sub_sq_le_two_mul (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h0 := norm_nonneg (x - y)
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]

private lemma cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) :
    cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  have e0 : curlOfGrad g 0 = g (2, 1) - g (1, 2) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have e1 : curlOfGrad g 1 = g (0, 2) - g (2, 0) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have e2 : curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  simp only [cnormSq, Fin.sum_univ_three, Fintype.sum_prod_type, e0, e1, e2]
  nlinarith [norm_sub_sq_le_two_mul (g (2, 1)) (g (1, 2)), norm_sub_sq_le_two_mul (g (0, 2)) (g (2, 0)),
    norm_sub_sq_le_two_mul (g (1, 0)) (g (0, 1)), sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖,
    sq_nonneg ‖g (2, 2)‖]

private lemma rotation_term_bound (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) (γc : ℝ) (hγ : 0 ≤ γc)
    (hM : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * u l) ≤ γc ^ 2 * cnormSq u) :
    ‖(1 / 2 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * curlGradOfSecondDeriv hW (j, l) * g (i, j) * a' n‖
      ≤ Real.sqrt 2 / 2 * γc * Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g) := by
  set B : Fin 3 → Fin 3 → ℂ := fun i l => ∑ n : Fin 3, (alternatingSymbol i l n : ℂ) * a' n with hB
  have hre : (∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * curlGradOfSecondDeriv hW (j, l) * g (i, j) * a' n)
      = ∑ i : Fin 3, ∑ j : Fin 3, g (i, j) * ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * B i l := by
    simp only [hB, Fin.sum_univ_three]; ring
  have hBsq : ∑ i : Fin 3, cnormSq (B i) = 2 * cnormSq a' := by
    simp [hB, cnormSq, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have hrow : ∀ i : Fin 3, ‖∑ j : Fin 3, g (i, j) * ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * B i l‖
      ≤ γc * (Real.sqrt (cnormSq (fun j => g (i, j))) * Real.sqrt (cnormSq (B i))) := by
    intro i
    calc _ ≤ Real.sqrt (cnormSq (fun j => g (i, j)))
          * Real.sqrt (cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * B i l)) :=
          norm_sum_mul_le_sqrt_cnormSq _ _
      _ ≤ Real.sqrt (cnormSq (fun j => g (i, j))) * (γc * Real.sqrt (cnormSq (B i))) :=
          mul_le_mul_of_nonneg_left (sqrt_le_mul_sqrt_of_le_sq_mul hγ (hM _)) (Real.sqrt_nonneg _)
      _ = _ := by ring
  have hsum : ∑ i : Fin 3, Real.sqrt (cnormSq (fun j => g (i, j))) * Real.sqrt (cnormSq (B i))
      ≤ Real.sqrt (cnormSq g) * (Real.sqrt 2 * Real.sqrt (cnormSq a')) := by
    have h := Real.sum_sqrt_mul_sqrt_le Finset.univ (f := fun i : Fin 3 => cnormSq (fun j => g (i, j)))
      (g := fun i => cnormSq (B i)) (fun _ => cnormSq_nonneg_aux _) (fun _ => cnormSq_nonneg_aux _)
    have hg : ∑ i : Fin 3, cnormSq (fun j => g (i, j)) = cnormSq g := by
      simp [cnormSq, Fintype.sum_prod_type]
    rw [hg, hBsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have htot := (norm_sum_le _ _).trans (Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hrow i)
  rw [← Finset.mul_sum] at htot
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [hre, norm_mul, hhalf]
  calc 1 / 2 * ‖∑ i : Fin 3, ∑ j : Fin 3, g (i, j) * ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * B i l‖
      ≤ 1 / 2 * (γc * (Real.sqrt (cnormSq g) * (Real.sqrt 2 * Real.sqrt (cnormSq a')))) := by
        gcongr
        exact htot.trans (mul_le_mul_of_nonneg_left hsum hγ)
    _ = _ := by ring

private lemma stretchBilin_norm_le (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (σc γc : ℝ) (hσ : 0 ≤ σc) (hγ : 0 ≤ γc)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * u j) ≤ σc ^ 2 * cnormSq u)
    (hM : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * u l) ≤ γc ^ 2 * cnormSq u)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    ‖stretchBilin gW hW a g a' g'‖ ≤
      σc * Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq (curlOfGrad g'))
        + Real.sqrt 2 * γc * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq g')
        + Real.sqrt 2 / 2 * γc * Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g) := by
  unfold stretchBilin
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_))
    (rotation_term_bound hW a' g γc hγ hM))
  · rw [norm_neg]
    have e : (∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)
        = ∑ i : Fin 3, curlOfGrad g i * ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j := by
      simp only [Finset.mul_sum, mul_assoc]
    rw [e]
    calc _ ≤ Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq
          (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)) :=
          norm_sum_mul_le_sqrt_cnormSq _ _
      _ ≤ Real.sqrt (cnormSq (curlOfGrad g)) * (σc * Real.sqrt (cnormSq (curlOfGrad g'))) :=
          mul_le_mul_of_nonneg_left (sqrt_le_mul_sqrt_of_le_sq_mul hσ (hS _)) (Real.sqrt_nonneg _)
      _ = _ := by ring
  · have e : (∑ j : Fin 3, (∑ l : Fin 3, a l * curlGradOfSecondDeriv hW (j, l)) * curlOfGrad g' j)
        = ∑ j : Fin 3, (∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * a l) * curlOfGrad g' j :=
      Finset.sum_congr rfl fun j _ => by
        rw [Finset.sum_congr rfl fun l (_ : l ∈ Finset.univ) => mul_comm (a l) (curlGradOfSecondDeriv hW (j, l))]
    rw [e]
    have hc : Real.sqrt (cnormSq (curlOfGrad g')) ≤ Real.sqrt 2 * Real.sqrt (cnormSq g') := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      exact Real.sqrt_le_sqrt (cnormSq_curlOfGrad_le g')
    calc _ ≤ Real.sqrt (cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * a l))
          * Real.sqrt (cnormSq (curlOfGrad g')) := norm_sum_mul_le_sqrt_cnormSq _ _
      _ ≤ (γc * Real.sqrt (cnormSq a)) * (Real.sqrt 2 * Real.sqrt (cnormSq g')) :=
          mul_le_mul (sqrt_le_mul_sqrt_of_le_sq_mul hγ (hM _)) hc (Real.sqrt_nonneg _) (by positivity)
      _ = _ := by ring

theorem stretchTripleBound : StretchTripleBoundHolds := by
  intro gW hW σc γc hσ hγ hS hM a g a' g'
  have h1 := stretchBilin_norm_le gW hW σc γc hσ hγ hS hM a g a' g'
  have h2 := stretchBilin_norm_le gW hW σc γc hσ hγ hS hM a' g' a g
  have hs : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hk : 3 / (2 * Real.sqrt 2) = 3 * Real.sqrt 2 / 4 := by
    have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [div_eq_div_iff (by positivity) (by norm_num)]
    linear_combination (-6) * hs
  have hn : ‖stretchTriple gW hW a g a' g'‖ ≤
      (‖stretchBilin gW hW a g a' g'‖ + ‖stretchBilin gW hW a' g' a g‖) / 2 := by
    unfold stretchTriple
    rw [norm_div]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    gcongr
    exact norm_add_le _ _
  rw [hk]
  linarith [hn, h1, h2]

end Bridge

end CertCell

end Breakdown

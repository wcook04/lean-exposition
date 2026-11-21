import Breakdown.CertCell.AssemblyCrossWaveTraceFree

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private lemma tfCnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => by positivity

private lemma tfNorm_sum_mul_le {β : Type*} [Fintype β] (x y : β → ℂ) :
    ‖∑ b, x b * y b‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq y) := by
  refine (norm_sum_le _ _).trans ?_
  simpa [cnormSq, norm_mul] using
    Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun b => ‖x b‖) (fun b => ‖y b‖)

private lemma tfSqrt_le {c d γ : ℝ} (hγ : 0 ≤ γ) (h : c ≤ γ ^ 2 * d) :
    Real.sqrt c ≤ γ * Real.sqrt d := by
  calc Real.sqrt c ≤ Real.sqrt (γ ^ 2 * d) := Real.sqrt_le_sqrt h
    _ = γ * Real.sqrt d := by rw [Real.sqrt_mul (sq_nonneg γ), Real.sqrt_sq hγ]

private lemma tfCnormSq_add {β : Type*} [Fintype β] (x y : β → ℂ) :
    cnormSq (fun b => x b + y b)
      = cnormSq x + cnormSq y + 2 * (∑ b, x b * (starRingEnd ℂ) (y b)).re := by
  simp only [cnormSq]
  rw [Complex.re_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    Complex.normSq_add]

private def rotCoeff (v : Fin 3 → ℂ) (ij : Fin 3 × Fin 3) : ℂ :=
  ∑ k : Fin 3, (alternatingSymbol k ij.2 ij.1 : ℂ) * v k

private def crossVec (a : Fin 3 → ℂ) (i l : Fin 3) : ℂ :=
  ∑ n : Fin 3, (alternatingSymbol i l n : ℂ) * a n

private def spinCoeff (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (ij : Fin 3 × Fin 3) : ℂ :=
  (1 / 2 : ℂ) * ∑ l : Fin 3, C (ij.2, l) * crossVec a ij.1 l

private def pairForm (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) : ℂ :=
  ∑ j : Fin 3, (∑ l : Fin 3, a l * C (j, l)) * curlOfGrad h j
    + (1 / 2 : ℂ) * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * C (j, l) * h (i, j) * a n

private lemma pairForm_eq (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) :
    pairForm C a h = ∑ ij : Fin 3 × Fin 3,
      (rotCoeff (fun j => ∑ l : Fin 3, C (j, l) * a l) ij + spinCoeff C a ij) * h ij := by
  simp only [pairForm, rotCoeff, spinCoeff, crossVec, curlOfGrad, Fintype.sum_prod_type, Fin.sum_univ_three]
  ring

private lemma rotCoeff_cnormSq (v : Fin 3 → ℂ) : cnormSq (rotCoeff v) = 2 * cnormSq v := by
  simp [cnormSq, rotCoeff, Fintype.sum_prod_type, Fin.sum_univ_three, alternatingSymbol]
  norm_num
  ring

private lemma crossVec_cnormSq (a : Fin 3 → ℂ) : ∑ i : Fin 3, cnormSq (crossVec a i) = 2 * cnormSq a := by
  simp [cnormSq, crossVec, Fin.sum_univ_three, alternatingSymbol]
  norm_num
  ring

private lemma spinCoeff_cnormSq_le (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (γ : ℝ)
    (hM : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, C (j, l) * u l) ≤ γ ^ 2 * cnormSq u) :
    cnormSq (spinCoeff C a) ≤ γ ^ 2 / 2 * cnormSq a := by
  have e : cnormSq (spinCoeff C a)
      = 1 / 4 * ∑ i : Fin 3, cnormSq (fun j => ∑ l : Fin 3, C (j, l) * crossVec a i l) := by
    simp only [cnormSq, spinCoeff, Fintype.sum_prod_type]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [norm_mul, mul_pow]
    norm_num
  rw [e]
  have h := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hM (crossVec a i)
  rw [← Finset.mul_sum, crossVec_cnormSq] at h
  linarith

private lemma rot_spin_contract (v b : Fin 3 → ℂ) (D : Fin 3 × Fin 3 → ℂ) :
    ∑ ij : Fin 3 × Fin 3, rotCoeff v ij * ((1 / 2 : ℂ) * ∑ l : Fin 3, D (ij.2, l) * crossVec b ij.1 l)
      = (1 / 2 : ℂ) * ∑ j : Fin 3, b j * ∑ k : Fin 3, D (j, k) * v k
        - (1 / 2 : ℂ) * (∑ j : Fin 3, D (j, j)) * ∑ k : Fin 3, v k * b k := by
  simp [rotCoeff, crossVec, Fintype.sum_prod_type, Fin.sum_univ_three, alternatingSymbol]
  norm_num
  ring

private lemma spinCoeff_conj (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (ij : Fin 3 × Fin 3) :
    (starRingEnd ℂ) (spinCoeff C a ij)
      = (1 / 2 : ℂ) * ∑ l : Fin 3, (starRingEnd ℂ) (C (ij.2, l)) * crossVec (fun n => (starRingEnd ℂ) (a n)) ij.1 l := by
  simp [spinCoeff, crossVec, map_sum, map_mul, Complex.conj_ofReal, map_ofNat]

private lemma half_re_le (Z : ℂ) : 2 * ((1 / 2 : ℂ) * Z).re ≤ ‖Z‖ := by
  have e : (1 / 2 : ℂ) * Z = ((1 / 2 : ℝ) : ℂ) * Z := by push_cast; ring
  rw [e, Complex.re_ofReal_mul]
  have := Complex.re_le_norm Z
  linarith

private lemma cross_term_le (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (γ : ℝ) (hγ : 0 ≤ γ)
    (hM : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, C (j, l) * u l) ≤ γ ^ 2 * cnormSq u)
    (htr : ∑ j : Fin 3, C (j, j) = 0) :
    2 * (∑ ij : Fin 3 × Fin 3, rotCoeff (fun j => ∑ l : Fin 3, C (j, l) * a l) ij
        * (starRingEnd ℂ) (spinCoeff C a ij)).re
      ≤ γ * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq (fun j => ∑ l : Fin 3, C (j, l) * a l)) := by
  set v : Fin 3 → ℂ := fun j => ∑ l : Fin 3, C (j, l) * a l with hv
  simp only [spinCoeff_conj]
  have hc := rot_spin_contract v (fun n => (starRingEnd ℂ) (a n)) (fun jl => (starRingEnd ℂ) (C jl))
  try simp only at hc
  rw [hc]
  have htr' : ∑ j : Fin 3, (starRingEnd ℂ) (C (j, j)) = 0 := by
    rw [← map_sum, htr, map_zero]
  rw [htr']
  simp only [mul_zero, zero_mul, sub_zero]
  have hw : ∀ j : Fin 3, ∑ k : Fin 3, (starRingEnd ℂ) (C (j, k)) * v k
      = (starRingEnd ℂ) (∑ k : Fin 3, C (j, k) * (starRingEnd ℂ) (v k)) := by
    intro j
    simp [map_sum, map_mul]
  simp only [hw]
  refine (half_re_le _).trans ?_
  refine (tfNorm_sum_mul_le _ _).trans ?_
  have ha : cnormSq (fun j => (starRingEnd ℂ) (a j)) = cnormSq a := by simp [cnormSq]
  have hv2 : cnormSq (fun j => (starRingEnd ℂ) (∑ k : Fin 3, C (j, k) * (starRingEnd ℂ) (v k)))
      = cnormSq (fun j => ∑ k : Fin 3, C (j, k) * (starRingEnd ℂ) (v k)) := by
    simp only [cnormSq, Complex.norm_conj]
  have hvc : cnormSq (fun k => (starRingEnd ℂ) (v k)) = cnormSq v := by simp [cnormSq]
  rw [ha, hv2]
  have hb := tfSqrt_le hγ (hM (fun k => (starRingEnd ℂ) (v k)))
  rw [hvc] at hb
  calc Real.sqrt (cnormSq a) * Real.sqrt (cnormSq (fun j => ∑ k : Fin 3, C (j, k) * (starRingEnd ℂ) (v k)))
      ≤ Real.sqrt (cnormSq a) * (γ * Real.sqrt (cnormSq v)) :=
        mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
    _ = γ * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq v) := by ring

private lemma pairForm_bound (C : Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ) (h : Fin 3 × Fin 3 → ℂ) (γ : ℝ)
    (hγ : 0 ≤ γ)
    (hM : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, C (j, l) * u l) ≤ γ ^ 2 * cnormSq u)
    (htr : ∑ j : Fin 3, C (j, j) = 0) :
    ‖pairForm C a h‖ ≤ Real.sqrt (7 / 2) * γ * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq h) := by
  have hM2 : cnormSq (fun ij => rotCoeff (fun j => ∑ l : Fin 3, C (j, l) * a l) ij + spinCoeff C a ij)
      ≤ (Real.sqrt (7 / 2) * γ) ^ 2 * cnormSq a := by
    rw [tfCnormSq_add, rotCoeff_cnormSq]
    have h1 := spinCoeff_cnormSq_le C a γ hM
    have h2 := cross_term_le C a γ hγ hM htr
    have h3 : cnormSq (fun j => ∑ l : Fin 3, C (j, l) * a l) ≤ γ ^ 2 * cnormSq a := hM a
    have h4 := tfSqrt_le hγ h3
    have h5 : γ * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq (fun j => ∑ l : Fin 3, C (j, l) * a l))
        ≤ γ ^ 2 * cnormSq a := by
      calc γ * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq (fun j => ∑ l : Fin 3, C (j, l) * a l))
          ≤ γ * Real.sqrt (cnormSq a) * (γ * Real.sqrt (cnormSq a)) :=
            mul_le_mul_of_nonneg_left h4 (mul_nonneg hγ (Real.sqrt_nonneg _))
        _ = γ ^ 2 * (Real.sqrt (cnormSq a) * Real.sqrt (cnormSq a)) := by ring
        _ = γ ^ 2 * cnormSq a := by rw [Real.mul_self_sqrt (tfCnormSq_nonneg a)]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 7 / 2)]
    linarith
  rw [pairForm_eq]
  refine (tfNorm_sum_mul_le _ _).trans ?_
  have hs := tfSqrt_le (mul_nonneg (Real.sqrt_nonneg _) hγ) hM2
  calc _ ≤ (Real.sqrt (7 / 2) * γ * Real.sqrt (cnormSq a)) * Real.sqrt (cnormSq h) :=
        mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma symPart_bound (gW : Fin 3 × Fin 3 → ℂ) (σc : ℝ) (hσ : 0 ≤ σc)
    (hS : ∀ u : Fin 3 → ℂ,
      cnormSq (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * u j) ≤ σc ^ 2 * cnormSq u)
    (g g' : Fin 3 × Fin 3 → ℂ) :
    ‖∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j‖
      ≤ σc * Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq (curlOfGrad g')) := by
  have e : (∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)
      = ∑ i : Fin 3, curlOfGrad g i * ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [e]
  calc _ ≤ Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq
        (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)) :=
        tfNorm_sum_mul_le _ _
    _ ≤ Real.sqrt (cnormSq (curlOfGrad g)) * (σc * Real.sqrt (cnormSq (curlOfGrad g'))) :=
        mul_le_mul_of_nonneg_left (tfSqrt_le hσ (hS _)) (Real.sqrt_nonneg _)
    _ = _ := by ring

private lemma norm_four_le (X Y P Q : ℂ) : ‖-X - Y + P + Q‖ ≤ ‖X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by
  calc ‖-X - Y + P + Q‖ ≤ ‖-X - Y + P‖ + ‖Q‖ := norm_add_le _ _
    _ ≤ ‖-X - Y‖ + ‖P‖ + ‖Q‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ‖-X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by gcongr; exact norm_sub_le _ _
    _ = ‖X‖ + ‖Y‖ + ‖P‖ + ‖Q‖ := by rw [norm_neg]

theorem traceFreeTripleBound (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (σc γc : ℝ)
    (hσ : 0 ≤ σc) (hγ : 0 ≤ γc)
    (hS : ∀ u : Fin 3 → ℂ,
      cnormSq (fun i => ∑ j : Fin 3, ((gW (i, j) + gW (j, i)) / 2) * u j) ≤ σc ^ 2 * cnormSq u)
    (hM : ∀ u : Fin 3 → ℂ,
      cnormSq (fun j => ∑ l : Fin 3, curlGradOfSecondDeriv hW (j, l) * u l) ≤ γc ^ 2 * cnormSq u)
    (htr : ∑ j : Fin 3, curlGradOfSecondDeriv hW (j, j) = 0)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    ‖stretchTriple gW hW a g a' g'‖ ≤
      σc * Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq (curlOfGrad g'))
        + Real.sqrt (7 / 2) / 2 * γc * (Real.sqrt (cnormSq a) * Real.sqrt (cnormSq g')
          + Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g)) := by
  have e : stretchTriple gW hW a g a' g' =
      (-(∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g' j)
        - (∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g' i * ((gW (i, j) + gW (j, i)) / 2) * curlOfGrad g j)
        + pairForm (curlGradOfSecondDeriv hW) a g' + pairForm (curlGradOfSecondDeriv hW) a' g) / 2 := by
    simp only [stretchTriple, stretchBilin, pairForm]
    ring
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [e, norm_div, h2]
  have s1 := symPart_bound gW σc hσ hS g g'
  have s2 := symPart_bound gW σc hσ hS g' g
  have q1 := pairForm_bound (curlGradOfSecondDeriv hW) a g' γc hγ hM htr
  have q2 := pairForm_bound (curlGradOfSecondDeriv hW) a' g γc hγ hM htr
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc _ ≤ _ := norm_four_le _ _ _ _
    _ ≤ σc * Real.sqrt (cnormSq (curlOfGrad g)) * Real.sqrt (cnormSq (curlOfGrad g'))
          + σc * Real.sqrt (cnormSq (curlOfGrad g')) * Real.sqrt (cnormSq (curlOfGrad g))
          + Real.sqrt (7 / 2) * γc * Real.sqrt (cnormSq a) * Real.sqrt (cnormSq g')
          + Real.sqrt (7 / 2) * γc * Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g) :=
        add_le_add (add_le_add (add_le_add s1 s2) q1) q2
    _ = _ := by ring

end Bridge

end CertCell

end Breakdown

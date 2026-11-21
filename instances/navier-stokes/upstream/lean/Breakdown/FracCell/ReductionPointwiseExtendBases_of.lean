import Breakdown.FracCell.ReductionPointwiseDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert Assembly CellAnalysis

namespace ExtendBasesInternal

theorem integral_sum_mul (s t : ℝ) (w g : ℝ → ℝ) (hw : Continuous w) (hg : Continuous g) (c : ℕ → ℝ)
    (n : ℕ) :
    ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range n, c i * r ^ i) * g r =
      ∑ i ∈ Finset.range n, c i * ∫ r in Set.Icc s t, w r * r ^ i * g r := by
  have hpt : ∀ r, w r * (∑ i ∈ Finset.range n, c i * r ^ i) * g r =
      ∑ i ∈ Finset.range n, c i * (w r * r ^ i * g r) := by
    intro r
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ =>
    (by fun_prop : Continuous fun r => c i * (w r * r ^ i * g r)).integrableOn_Icc)]
  exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)

theorem moment_vanish (s t : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (cf : ℕ → ℕ → ℝ)
    (hlead : ∀ n, cf n n ≠ 0)
    (horth : ∀ n m, ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), cf n i * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), cf m i * r ^ i) = if n = m then 1 else 0) (j : ℕ) :
    ∀ a, a < j → ∫ r in Set.Icc s t, w r * r ^ a * (∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) = 0 := by
  intro a
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro haj
    have h0 := horth a j
    have e := integral_sum_mul s t w (fun r => ∑ i ∈ Finset.range (j + 1), cf j i * r ^ i) hw
      (by fun_prop) (cf a) (a + 1)
    beta_reduce at e
    rw [if_neg (ne_of_lt haj), e, Finset.sum_range_succ,
      Finset.sum_eq_zero (fun i hi => by
        have hia := Finset.mem_range.mp hi
        rw [ih i hia (by omega), mul_zero]), zero_add] at h0
    exact (mul_eq_zero.mp h0).resolve_left (hlead a)

theorem cross_zero (s t : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (cf : ℕ → ℕ → ℝ)
    (hlead : ∀ n, cf n n ≠ 0)
    (horth : ∀ n m, ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), cf n i * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), cf m i * r ^ i) = if n = m then 1 else 0)
    (c : ℕ → ℝ) (n m : ℕ) (hnm : n < m) :
    ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), c i * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), cf m i * r ^ i) = 0 := by
  have e := integral_sum_mul s t w (fun r => ∑ i ∈ Finset.range (m + 1), cf m i * r ^ i) hw
    (by fun_prop) c (n + 1)
  beta_reduce at e
  rw [e]
  exact Finset.sum_eq_zero (fun i hi => by
    have hin := Finset.mem_range.mp hi
    rw [moment_vanish s t w hw cf hlead horth m i (by omega), mul_zero])

theorem extend_orth (s t : ℝ) (w : ℝ → ℝ) (hw : Continuous w) (cf₀ cf : ℕ → ℕ → ℝ) (D : ℕ)
    (hlead : ∀ n, cf n n ≠ 0)
    (horth : ∀ n m, ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), cf n i * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), cf m i * r ^ i) = if n = m then 1 else 0)
    (hst : ∀ n ≤ D, ∀ m ≤ D, ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), cf₀ n i * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), cf₀ m i * r ^ i) = if n = m then 1 else 0) (n m : ℕ) :
    ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (n + 1), (if n ≤ D then cf₀ n i else cf n i) * r ^ i) *
      (∑ i ∈ Finset.range (m + 1), (if m ≤ D then cf₀ m i else cf m i) * r ^ i) =
        if n = m then 1 else 0 := by
  by_cases hn : n ≤ D <;> by_cases hm : m ≤ D <;> simp only [hn, hm, ↓reduceIte]
  · exact hst n hn m hm
  · rw [if_neg (by omega)]
    exact cross_zero s t w hw cf hlead horth (cf₀ n) n m (by omega)
  · rw [if_neg (by omega)]
    calc _ = ∫ r in Set.Icc s t, w r * (∑ i ∈ Finset.range (m + 1), cf₀ m i * r ^ i) *
          (∑ i ∈ Finset.range (n + 1), cf n i * r ^ i) := by
          congr 1
          funext r
          ring
      _ = 0 := cross_zero s t w hw cf hlead horth (cf₀ m) m n (by omega)
  · exact horth n m

theorem eval_family (w : ℝ → ℝ) (a b : ℝ) (hd : ∀ n, (orthoFamily w a b n).natDegree = n) (n : ℕ)
    (x : ℝ) : (orthoFamily w a b n).eval x =
      ∑ i ∈ Finset.range (n + 1), (orthoFamily w a b n).coeff i * x ^ i := by
  rw [Polynomial.eval_eq_sum_range, hd n]

theorem family_orth (h : OrthoFamilyStatement) (w : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hw : Continuous w)
    (hnn : ∀ x ∈ Set.Icc a b, 0 ≤ w x) (hpos : ∀ x ∈ Set.Ioo a b, 0 < w x) :
    (∀ n, 0 < (orthoFamily w a b n).coeff n) ∧
      ∀ n m, ∫ r in Set.Icc a b, w r * (∑ i ∈ Finset.range (n + 1), (orthoFamily w a b n).coeff i * r ^ i) *
        (∑ i ∈ Finset.range (m + 1), (orthoFamily w a b m).coeff i * r ^ i) = if n = m then 1 else 0 := by
  have hS := h w a b hab hw.measurable hnn hpos hw.continuousOn
  refine ⟨fun n => (hS n).2.1, fun n m => ?_⟩
  have e := (hS n).2.2 m
  unfold polyPair at e
  simp only [eval_family w a b (fun k => (hS k).1)] at e
  exact e

theorem weight_one_eq (s t : ℝ) (f g : ℝ → ℝ) :
    ∫ z in Set.Icc s t, f z * g z = ∫ z in Set.Icc s t, (fun _ => (1 : ℝ)) z * f z * g z := by
  simp only [one_mul]

end ExtendBasesInternal

open ExtendBasesInternal in
theorem extendBases_of (h : OrthoFamilyStatement) : ExtendBasesStatement := by
  intro K D B₀ hK hB
  obtain ⟨⟨hr0, hr12⟩, ⟨hz0, hz12⟩⟩ := hK
  have hwc : Continuous K.lineWeight := by
    unfold CellBox.lineWeight
    split_ifs <;> fun_prop
  have hR := family_orth h K.lineWeight K.r₁ K.r₂ hr12 hwc
    (fun x hx => by
      unfold CellBox.lineWeight
      split_ifs with h0
      · linarith [hx.1]
      · norm_num)
    (fun x hx => by
      unfold CellBox.lineWeight
      split_ifs with h0
      · linarith [hx.1]
      · norm_num)
  have hZ := family_orth h (fun _ => 1) K.z₁ K.z₂ hz12 continuous_const (fun _ _ => zero_le_one)
    (fun _ _ => one_pos)
  refine ⟨⟨fun j => ?_, fun l => ?_, fun j j' => ?_, fun l l' => ?_⟩, fun j hj i => ?_, fun l hl i => ?_⟩
  · show 0 < (if j ≤ D then B₀.radialCoef j j else (canonicalBases K).radialCoef j j)
    split_ifs with hj
    · exact hB.radial_leading j hj
    · exact hR.1 j
  · show 0 < (if l ≤ D then B₀.heightCoef l l else (canonicalBases K).heightCoef l l)
    split_ifs with hl
    · exact hB.height_leading l hl
    · exact hZ.1 l
  · exact extend_orth K.r₁ K.r₂ K.lineWeight hwc B₀.radialCoef
      (fun n i => (orthoFamily K.lineWeight K.r₁ K.r₂ n).coeff i) D (fun n => (hR.1 n).ne') hR.2
      (fun n hn m hm => hB.radial_orthonormal n hn m hm) j j'
  · refine (weight_one_eq K.z₁ K.z₂ ((extendBases K D B₀).heightPoly l)
      ((extendBases K D B₀).heightPoly l')).trans ?_
    exact extend_orth K.z₁ K.z₂ (fun _ => 1) continuous_const B₀.heightCoef
      (fun n i => (orthoFamily (fun _ => 1) K.z₁ K.z₂ n).coeff i) D (fun n => (hZ.1 n).ne') hZ.2
      (fun n hn m hm => (weight_one_eq K.z₁ K.z₂ (B₀.heightPoly n) (B₀.heightPoly m)).symm.trans
        (hB.height_orthonormal n hn m hm)) l l'
  · show (if j ≤ D then B₀.radialCoef j i else (canonicalBases K).radialCoef j i) = B₀.radialCoef j i
    exact if_pos hj
  · show (if l ≤ D then B₀.heightCoef l i else (canonicalBases K).heightCoef l i) = B₀.heightCoef l i
    exact if_pos hl

end Reduction

end CellCert

end Breakdown

import Breakdown.CertCell.InstanceStatements

open scoped ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.CellAnalysis (CellBox)

namespace Internal

namespace RowPairing

variable {count rowCount : ℕ}

def blockEntry (R : RowValues count rowCount) (box : Fin count → CellBox) (K : Fin count) (ι : ℤ × ℤ)
    (i j : ℕ) : ℂ :=
  ∫ p in (box K).rect, (p.1 : ℂ) * ∑ c : Fin 3,
    (R.testField K ι j c).eval (box K) p * starRingEnd ℂ ((R.testField K ι i c).eval (box K) p)

def blockFactor (ι : ℤ × ℤ) : ℝ := if ι = -ι then 2 else 1

def rowVec (R : RowValues count rowCount) (x : Fin rowCount → ℝ) (K : Fin count) (ι : ℤ × ℤ) :
    Fin (R.testCount K ι) → ℂ := fun j =>
  ∑ a, if (R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ) then
    (x a : ℂ) * rowPartFactor (R.realPart a) else 0

theorem blockFactor_pos (ι : ℤ × ℤ) : 0 < blockFactor ι := by
  unfold blockFactor; split_ifs <;> norm_num

theorem testBlockMatrix_apply (R : RowValues count rowCount) (box : Fin count → CellBox) (K : Fin count)
    (ι : ℤ × ℤ) (i j : Fin (R.testCount K ι)) :
    R.testBlockMatrix box K ι i j = blockEntry R box K ι i j := rfl

theorem eval_continuous (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval CellCert.CellAnalysis.CellBox.refR CellCert.CellAnalysis.CellBox.refZ
  fun_prop

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem blockEntry_integrable (R : RowValues count rowCount) (box : Fin count → CellBox) (K : Fin count)
    (ι : ℤ × ℤ) (i j : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ c : Fin 3,
      (R.testField K ι j c).eval (box K) p * starRingEnd ℂ ((R.testField K ι i c).eval (box K) p))
      (box K).rect := by
  refine ContinuousOn.integrableOn_compact (rect_compact _) (Continuous.continuousOn ?_)
  refine (Complex.continuous_ofReal.comp continuous_fst).mul (continuous_finsetSum _ fun c _ => ?_)
  exact (eval_continuous _ _).mul (Complex.continuous_conj.comp (eval_continuous _ _))

theorem integral_re_mul (s : Set (ℝ × ℝ)) (S : ℝ × ℝ → ℂ)
    (hS : IntegrableOn (fun p => (p.1 : ℂ) * S p) s) (c : ℂ) :
    ∫ p in s, p.1 * (c * S p).re = (c * ∫ p in s, (p.1 : ℂ) * S p).re := by
  have h := integral_re (𝕜 := ℂ) (hS.const_mul c)
  simp only [RCLike.re_to_complex] at h
  rw [← integral_const_mul, ← h]
  congr 1
  funext p
  rw [show c * ((p.1 : ℂ) * S p) = (p.1 : ℂ) * (c * S p) by ring, Complex.re_ofReal_mul]

theorem blockEntry_conj (R : RowValues count rowCount) (box : Fin count → CellBox) (K : Fin count)
    (ι : ℤ × ℤ) (i j : ℕ) :
    blockEntry R box K ι j i = starRingEnd ℂ (blockEntry R box K ι i j) := by
  unfold blockEntry
  rw [← integral_conj]
  congr 1
  funext p
  simp only [map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

theorem sum_fin_ite (N k : ℕ) (P : Prop) [Decidable P] (hk : P → k < N) (F : ℕ → ℂ) :
    ∑ i : Fin N, (if P ∧ k = (i : ℕ) then F i else 0) = if P then F k else 0 := by
  by_cases hP : P
  · rw [if_pos hP, Finset.sum_eq_single ⟨k, hk hP⟩]
    · simp [hP]
    · intro i _ hi
      rw [if_neg]
      rintro ⟨_, e⟩
      exact hi (Fin.ext e.symm)
    · intro h
      exact absurd (Finset.mem_univ _) h
  · simp [hP]

variable {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {tauMax : ℝ}

theorem sameBlock_label (hR : IsRowValues M R m tauMax) {a b : Fin rowCount} (h : R.SameBlock a b) :
    R.labelOf a = R.labelOf b :=
  h.2.elim id (hR.rows_one_member a b h.1)

theorem sameBlock_symm {a b : Fin rowCount} (h : R.SameBlock a b) : R.SameBlock b a :=
  ⟨h.1.symm, h.2.elim (fun e => Or.inl e.symm) (fun e => Or.inr (by rw [e, neg_neg]))⟩

theorem entry_zero {a b : Fin rowCount} (h : ¬ R.SameBlock a b) :
    R.testPairingMatrix M.box a b = 0 := by
  simp only [RowValues.testPairingMatrix, if_neg h]

theorem entry_eq (hR : IsRowValues M R m tauMax) (a b : Fin rowCount)
    (hK : R.cellOf b = R.cellOf a) (hι : R.labelOf b = R.labelOf a) :
    R.testPairingMatrix M.box a b = 2 * Real.pi * blockFactor (R.labelOf a) *
      (rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
        blockEntry R M.box (R.cellOf a) (R.labelOf a) (R.testOf b) (R.testOf a)).re := by
  have hsb : R.SameBlock a b := ⟨hK.symm, Or.inl hι.symm⟩
  have hint := blockEntry_integrable R M.box (R.cellOf a) (R.labelOf a) (R.testOf b) (R.testOf a)
  have hvb : ∀ c p, R.testValue M.box b c p =
      (R.testField (R.cellOf a) (R.labelOf a) (R.testOf b) c).eval (M.box (R.cellOf a)) p := by
    intro c p
    unfold RowValues.testValue
    rw [hK, hι]
  simp only [RowValues.testPairingMatrix]
  rw [if_pos hsb]
  simp only [if_pos hι.symm, hvb]
  unfold RowValues.testValue
  by_cases hs : R.labelOf a = -R.labelOf a
  · have hra := hR.zero_label_real a hs
    have hrb := hR.zero_label_real b (by rw [hι]; exact hs)
    have hlt : R.testOf b < R.testCount (R.cellOf a) (R.labelOf a) := by
      have := hR.test_index b
      rwa [hK, hι] at this
    have hconj := (hR.tests_conj (R.cellOf a) (R.labelOf a) (hR.row_tested a)).2 (R.testOf b) hlt
    rw [← hs] at hconj
    have hs' : R.labelOf a = -R.labelOf b := by rw [hι]; exact hs
    simp only [if_pos hs']
    have key := integral_re_mul _ _ hint ((2 : ℝ) : ℂ)
    rw [Complex.re_ofReal_mul] at key
    unfold blockEntry
    simp only [blockFactor, if_pos hs, hra, hrb, rowPartFactor, ↓reduceIte, map_one, one_mul]
    rw [mul_assoc (2 * Real.pi) 2, ← key]
    congr 2
    funext p
    congr 1
    rw [Complex.ofReal_ofNat, two_mul]
    congr 2
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    exact hconj c p
  · have hs' : ¬ R.labelOf a = -R.labelOf b := by rw [hι]; exact hs
    simp only [if_neg hs']
    have key := integral_re_mul _ _ hint
      (rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b)))
    unfold blockEntry
    simp only [blockFactor, if_neg hs, mul_one, add_zero]
    rw [← key]

theorem entry_symm (hR : IsRowValues M R m tauMax) (a b : Fin rowCount) :
    R.testPairingMatrix M.box b a = R.testPairingMatrix M.box a b := by
  by_cases hsb : R.SameBlock a b
  · have hK : R.cellOf b = R.cellOf a := hsb.1.symm
    have hι : R.labelOf b = R.labelOf a := (sameBlock_label hR hsb).symm
    rw [entry_eq hR a b hK hι, entry_eq hR b a hK.symm hι.symm, hK, hι]
    congr 1
    rw [← Complex.conj_re]
    congr 1
    rw [blockEntry_conj]
    simp only [map_mul, Complex.conj_conj]
    ring
  · rw [entry_zero hsb, entry_zero (fun h => hsb (sameBlock_symm h))]

theorem star_ite_zero (P : Prop) [Decidable P] (z : ℂ) :
    star (if P then z else 0) = if P then star z else 0 := by
  split_ifs <;> simp

theorem mulVec_rowVec (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (K : Fin M.count)
    (ι : ℤ × ℤ) (i : Fin (R.testCount K ι)) :
    (Matrix.mulVec (R.testBlockMatrix M.box K ι) (rowVec R x K ι)) i =
      ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then
        blockEntry R M.box K ι i (R.testOf a) * ((x a : ℂ) * rowPartFactor (R.realPart a)) else 0 := by
  simp only [Matrix.mulVec, dotProduct, rowVec, Finset.mul_sum, mul_ite, mul_zero, testBlockMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  refine sum_fin_ite _ (R.testOf a) _ (fun h => ?_)
    (fun n => blockEntry R M.box K ι i n * ((x a : ℂ) * rowPartFactor (R.realPart a)))
  obtain ⟨h1, h2⟩ := h
  rw [← h1, ← h2]
  exact hR.test_index a

theorem quad_rowVec (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (K : Fin M.count)
    (ι : ℤ × ℤ) :
    star (rowVec R x K ι) ⬝ᵥ (Matrix.mulVec (R.testBlockMatrix M.box K ι) (rowVec R x K ι)) =
      ∑ b, ∑ a, if (R.cellOf b = K ∧ R.labelOf b = ι) ∧ (R.cellOf a = K ∧ R.labelOf a = ι) then
        (x b : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
          blockEntry R M.box K ι (R.testOf b) (R.testOf a) * ((x a : ℂ) * rowPartFactor (R.realPart a))
        else 0 := by
  simp only [dotProduct, mulVec_rowVec hR, Pi.star_apply, rowVec, star_sum, star_ite_zero,
    Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [sum_fin_ite _ (R.testOf b) _ (fun h => by
      obtain ⟨h1, h2⟩ := h
      rw [← h1, ← h2]
      exact hR.test_index b)
    (fun n => star ((x b : ℂ) * rowPartFactor (R.realPart b)) *
      ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then
        blockEntry R M.box K ι n (R.testOf a) * ((x a : ℂ) * rowPartFactor (R.realPart a)) else 0)]
  by_cases hb : R.cellOf b = K ∧ R.labelOf b = ι
  · rw [if_pos hb, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases ha : R.cellOf a = K ∧ R.labelOf a = ι
    · rw [if_pos ha, if_pos ⟨hb, ha⟩]
      simp only [star_mul', Complex.star_def, Complex.conj_ofReal]
      ring
    · rw [if_neg ha, if_neg (fun h => ha h.2), mul_zero]
  · rw [if_neg hb]
    exact (Finset.sum_eq_zero fun a _ => if_neg (fun h => hb h.1)).symm


theorem block_quad (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (K : Fin M.count) (ι : ℤ × ℤ) :
    ∑ a, ∑ b, (if (R.cellOf a = K ∧ R.labelOf a = ι) ∧ (R.cellOf b = K ∧ R.labelOf b = ι) then
      x a * R.testPairingMatrix M.box a b * x b else 0) =
      2 * Real.pi * blockFactor ι *
        (star (rowVec R x K ι) ⬝ᵥ (Matrix.mulVec (R.testBlockMatrix M.box K ι) (rowVec R x K ι))).re := by
  rw [quad_rowVec hR, Complex.re_sum, Finset.mul_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hab : (R.cellOf a = K ∧ R.labelOf a = ι) ∧ (R.cellOf b = K ∧ R.labelOf b = ι)
  · rw [if_pos hab, if_pos ⟨hab.2, hab.1⟩]
    obtain ⟨⟨ha1, ha2⟩, hb1, hb2⟩ := hab
    rw [entry_eq hR a b (hb1.trans ha1.symm) (hb2.trans ha2.symm), ha1, ha2]
    rw [show (x b : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
        blockEntry R M.box K ι (R.testOf b) (R.testOf a) * ((x a : ℂ) * rowPartFactor (R.realPart a)) =
        ((x a * x b : ℝ) : ℂ) * (rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
          blockEntry R M.box K ι (R.testOf b) (R.testOf a)) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  · rw [if_neg hab, if_neg (fun h => hab ⟨h.2, h.1⟩), Complex.zero_re, mul_zero]

theorem rowVec_ne_zero (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (a0 : Fin rowCount)
    (hx : x a0 ≠ 0) : rowVec R x (R.cellOf a0) (R.labelOf a0) ≠ 0 := by
  intro h
  have hj := congrFun h ⟨R.testOf a0, hR.test_index a0⟩
  have key : (starRingEnd ℂ (rowPartFactor (R.realPart a0)) *
      rowVec R x (R.cellOf a0) (R.labelOf a0) ⟨R.testOf a0, hR.test_index a0⟩).re = x a0 := by
    simp only [rowVec, Finset.mul_sum, Complex.re_sum, mul_ite, mul_zero]
    rw [Finset.sum_eq_single a0]
    · rw [if_pos ⟨⟨rfl, rfl⟩, rfl⟩]
      cases h0 : R.realPart a0 <;> simp [rowPartFactor]
    · intro b _ hb
      split_ifs with hc
      · have hne : R.realPart b ≠ R.realPart a0 :=
          fun e => hb (hR.rows_distinct b a0 hc.1.1 hc.1.2 hc.2 e)
        cases hb' : R.realPart b <;> cases ha' : R.realPart a0 <;> simp_all [rowPartFactor]
      · simp
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hj] at key
  simp at key
  exact hx key.symm

theorem block_nonneg (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (a0 : Fin rowCount) :
    0 ≤ (star (rowVec R x (R.cellOf a0) (R.labelOf a0)) ⬝ᵥ
      (Matrix.mulVec (R.testBlockMatrix M.box (R.cellOf a0) (R.labelOf a0))
        (rowVec R x (R.cellOf a0) (R.labelOf a0)))).re := by
  by_cases hw : rowVec R x (R.cellOf a0) (R.labelOf a0) = 0
  · rw [hw]; simp
  · exact ((Complex.pos_iff.mp
      ((hR.block_posDef _ _ (hR.row_tested a0)).dotProduct_mulVec_pos hw)).1).le

theorem block_pos (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (a0 : Fin rowCount)
    (hx : x a0 ≠ 0) :
    0 < (star (rowVec R x (R.cellOf a0) (R.labelOf a0)) ⬝ᵥ
      (Matrix.mulVec (R.testBlockMatrix M.box (R.cellOf a0) (R.labelOf a0))
        (rowVec R x (R.cellOf a0) (R.labelOf a0)))).re :=
  (Complex.pos_iff.mp ((hR.block_posDef _ _ (hR.row_tested a0)).dotProduct_mulVec_pos
    (rowVec_ne_zero hR x a0 hx))).1

theorem quad_split (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) :
    star x ⬝ᵥ (Matrix.mulVec (R.testPairingMatrix M.box) x) =
      ∑ β ∈ Finset.univ.image (fun a => (R.cellOf a, R.labelOf a)),
        ∑ a, ∑ b, (if (R.cellOf a = β.1 ∧ R.labelOf a = β.2) ∧ (R.cellOf b = β.1 ∧ R.labelOf b = β.2) then
          x a * R.testPairingMatrix M.box a b * x b else 0) := by
  rw [Finset.sum_comm]
  simp only [star_trivial, dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  have hterm : ∀ β : Fin M.count × (ℤ × ℤ),
      (if (R.cellOf a = β.1 ∧ R.labelOf a = β.2) ∧ (R.cellOf b = β.1 ∧ R.labelOf b = β.2) then
        x a * R.testPairingMatrix M.box a b * x b else 0) =
      if (R.cellOf a, R.labelOf a) = β then x a * R.testPairingMatrix M.box a b * x b else 0 := by
    intro β
    by_cases hsb : R.SameBlock a b
    · rw [← hsb.1, ← sameBlock_label hR hsb]
      simp only [and_self, Prod.ext_iff]
    · rw [entry_zero hsb]
      simp
  simp only [hterm]
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_image_of_mem _ (Finset.mem_univ _)), ← mul_assoc]

end RowPairing

end Internal

open Internal.RowPairing in
theorem rowPairingPosDef : RowPairingPosDef := by
  intro rowCount M R m tauMax hR
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨Matrix.IsHermitian.ext fun a b => ?_, fun x hx => ?_⟩
  · rw [star_trivial]
    exact entry_symm hR a b
  · obtain ⟨a0, ha0⟩ : ∃ a, x a ≠ 0 := Function.ne_iff.mp hx
    rw [quad_split hR]
    refine Finset.sum_pos' (fun β hβ => ?_) ⟨(R.cellOf a0, R.labelOf a0),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hβ
      rw [block_quad hR]
      exact mul_nonneg (mul_pos (by positivity) (blockFactor_pos _)).le (block_nonneg hR x a)
    · rw [block_quad hR]
      exact mul_pos (mul_pos (by positivity) (blockFactor_pos _)) (block_pos hR x a0 ha0)

end Instance

end CertCell

end Breakdown

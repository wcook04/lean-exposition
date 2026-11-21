import Mathlib
import Breakdown.CertCell.CertificateStatements

open Matrix Breakdown.CellCert.Finite

noncomputable section

namespace Breakdown.CertCell.Certificate

private lemma re_real_quadratic {m : Type} [Fintype m] (K : Matrix m m ℂ) (y : m → ℝ) :
    (ofRealVec y ⬝ᵥ (K *ᵥ ofRealVec y)).re = y ⬝ᵥ (K.map Complex.re *ᵥ y) := by
  simp only [dotProduct, mulVec, ofRealVec, Complex.re_sum, Complex.re_ofReal_mul,
    Complex.re_mul_ofReal, Matrix.map_apply]

theorem realRestrictionValue : RealRestrictionValue := by
  intro n m _ _ E M y
  have hstar : star (E *ᵥ ofRealVec y) = ofRealVec y ᵥ* Eᴴ := by
    rw [Matrix.star_mulVec]
    congr 1
    funext k
    simp [ofRealVec]
  unfold complexFormValue quadValue realRestriction
  rw [hstar, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    re_real_quadratic]

theorem realRestrictionAdd : RealRestrictionAdd := by
  intro n m _ E M M'
  ext i j
  simp [realRestriction, Matrix.mul_add, Matrix.add_mul]

private lemma column_pairing {n m q : Type} [Fintype n] [Fintype m] (E : Matrix n m ℂ)
    (F : Matrix n q ℂ) (y : m → ℝ) (c : q) :
    ∑ i, star (F i c) * (E *ᵥ ofRealVec y) i
      = ∑ k, star ((Eᴴ *ᵥ fun i => F i c) k) * (y k : ℂ) := by
  have h1 : ∑ i, star (F i c) * (E *ᵥ ofRealVec y) i
      = (star fun i => F i c) ⬝ᵥ (E *ᵥ ofRealVec y) := rfl
  have h2 : star (Eᴴ *ᵥ fun i => F i c) = (star fun i => F i c) ᵥ* E := by
    rw [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [h1, Matrix.dotProduct_mulVec, ← h2]
  rfl

theorem complexColumnSplit : ComplexColumnSplit := by
  intro n m q _ _ E F t y c ht
  rw [column_pairing]
  set g := Eᴴ *ᵥ fun i => F i c
  have hre : (∑ k, star (g k) * (y k : ℂ)).re = ∑ k, (g k).re * y k := by
    simp [Complex.re_sum]
  have him : (∑ k, star (g k) * (y k : ℂ)).im = -∑ k, (g k).im * y k := by
    simp [Complex.im_sum, Finset.sum_neg_distrib]
  have hl : realColumns E t F (Sum.inl c) ⬝ᵥ y = Real.sqrt t * ∑ k, (g k).re * y k := by
    simp only [realColumns, dotProduct, Finset.mul_sum, g]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hr : realColumns E t F (Sum.inr c) ⬝ᵥ y = Real.sqrt t * ∑ k, (g k).im * y k := by
    simp only [realColumns, dotProduct, Finset.mul_sum, g]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hl, hr, Complex.sq_norm, Complex.normSq_apply, hre, him, mul_pow, mul_pow, Real.sq_sqrt ht]
  ring

end Breakdown.CertCell.Certificate

import Breakdown.CertCell.CouplingInverseFactor
import Breakdown.FracCell.CellDataDefs
import Breakdown.Cert.CoerciveStatement

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis

namespace Internal.RowRemoval

section Algebra

variable {n : Type*} [Fintype n] [DecidableEq n]

lemma quad_sub (A B : Matrix n n ℂ) (y : n → ℂ) :
    Coupling.quadForm (A - B) y = Coupling.quadForm A y - Coupling.quadForm B y := by
  simp only [Coupling.quadForm, sub_mulVec, dotProduct_sub, Complex.sub_re]

lemma quad_add (A B : Matrix n n ℂ) (y : n → ℂ) :
    Coupling.quadForm (A + B) y = Coupling.quadForm A y + Coupling.quadForm B y := by
  simp only [Coupling.quadForm, add_mulVec, dotProduct_add, Complex.add_re]

lemma quad_sum {α : Type*} (S : Finset α) (A : α → Matrix n n ℂ) (y : n → ℂ) :
    Coupling.quadForm (∑ ι ∈ S, A ι) y = ∑ ι ∈ S, Coupling.quadForm (A ι) y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [Coupling.quadForm]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, quad_add, ih]

lemma quad_smul (c : ℝ) (A : Matrix n n ℂ) (y : n → ℂ) :
    Coupling.quadForm ((c : ℂ)⁻¹ • A) y = c⁻¹ * Coupling.quadForm A y := by
  rw [← Complex.ofReal_inv]
  simp only [Coupling.quadForm, smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul]

lemma quad_neg (A : Matrix n n ℂ) (y : n → ℂ) : Coupling.quadForm A (-y) = Coupling.quadForm A y := by
  simp only [Coupling.quadForm, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]

lemma quad_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (y : n → ℂ) : 0 ≤ Coupling.quadForm A y :=
  (Complex.nonneg_iff.mp ((posSemidef_iff_dotProduct_mulVec.mp hA).2 y)).1

lemma scaled_bound {P : Matrix n n ℂ} (hP : P.PosDef) {c : ℝ} (hc : 0 < c) (x y : n → ℂ) :
    2 * (star x ⬝ᵥ y).re - c⁻¹ * Coupling.quadForm P y ≤ c * Coupling.quadForm P⁻¹ x := by
  have hDH : P * P⁻¹ = 1 := mul_nonsing_inv P ((isUnit_iff_isUnit_det P).mp hP.isUnit)
  have h := Coupling.InverseFactorInternal.cross_bound_inverse hP.isHermitian.eq
    (fun v => quad_nonneg hP.posSemidef v) hDH x (((c⁻¹ : ℝ) : ℂ) • y)
  rw [Coupling.InverseFactorInternal.real_smul_quad_re, Coupling.InverseFactorInternal.real_smul_dot_re,
    Coupling.InverseFactorInternal.re_dot_comm y x] at h
  unfold Coupling.quadForm
  have hcd : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have h2 := mul_le_mul_of_nonneg_left h hc.le
  have e1 : c * (2 * (c⁻¹ * (star x ⬝ᵥ y).re) - c⁻¹ ^ 2 * (star y ⬝ᵥ (P *ᵥ y)).re)
      = 2 * (star x ⬝ᵥ y).re - c⁻¹ * (star y ⬝ᵥ (P *ᵥ y)).re := by
    linear_combination (2 * (star x ⬝ᵥ y).re - c⁻¹ * (star y ⬝ᵥ (P *ᵥ y)).re) * hcd
  linarith

lemma assemble {α : Type*} (S : Finset α) {W B Γ : Matrix n n ℂ} (Ts Tv : α → Matrix n n ℂ)
    (cs cv : α → ℝ) {lam : ℝ} (r m e : n → ℂ) (ts tv : α → n → ℂ) (hs hv : α → ℝ)
    (hB : B.PosDef) (hΓ : Γ.PosDef) (hlam : 0 < lam)
    (hW : (W - B - ∑ ι ∈ S, ((cs ι : ℂ))⁻¹ • Ts ι - ∑ ι ∈ S, ((cv ι : ℂ))⁻¹ • Tv ι
      - ((lam : ℂ))⁻¹ • Γ).PosSemidef)
    (hTs : ∀ ι ∈ S, ∀ y, 0 ≤ (cs ι)⁻¹ * Coupling.quadForm (Ts ι) y ∧
      -(2 * (star (ts ι) ⬝ᵥ y).re) - (cs ι)⁻¹ * Coupling.quadForm (Ts ι) y ≤ cs ι * hs ι)
    (hTv : ∀ ι ∈ S, ∀ y, 0 ≤ (cv ι)⁻¹ * Coupling.quadForm (Tv ι) y ∧
      -(2 * (star (tv ι) ⬝ᵥ y).re) - (cv ι)⁻¹ * Coupling.quadForm (Tv ι) y ≤ cv ι * hv ι)
    (hr : r = m - ∑ ι ∈ S, (ts ι + tv ι) - e) :
    Coupling.quadForm W⁻¹ r ≤ Coupling.quadForm B⁻¹ m + ∑ ι ∈ S, (cs ι * hs ι + cv ι * hv ι)
      + lam * Coupling.quadForm Γ⁻¹ e := by
  have hlow : ∀ y, Coupling.quadForm B y + ∑ ι ∈ S, (cs ι)⁻¹ * Coupling.quadForm (Ts ι) y
      + ∑ ι ∈ S, (cv ι)⁻¹ * Coupling.quadForm (Tv ι) y + lam⁻¹ * Coupling.quadForm Γ y
      ≤ Coupling.quadForm W y := by
    intro y
    have h := quad_nonneg hW y
    simp only [quad_sub, quad_sum, quad_smul] at h
    linarith
  have hunit : IsUnit W.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    obtain ⟨v, hv0, hWv⟩ := exists_mulVec_eq_zero_iff.mpr h0
    have h1 := hlow v
    have hzero : Coupling.quadForm W v = 0 := by simp [Coupling.quadForm, hWv]
    have hBpos : 0 < Coupling.quadForm B v := (Complex.pos_iff.mp (hB.dotProduct_mulVec_pos hv0)).1
    have hs1 : 0 ≤ ∑ ι ∈ S, (cs ι)⁻¹ * Coupling.quadForm (Ts ι) v :=
      Finset.sum_nonneg fun ι h => (hTs ι h v).1
    have hs2 : 0 ≤ ∑ ι ∈ S, (cv ι)⁻¹ * Coupling.quadForm (Tv ι) v :=
      Finset.sum_nonneg fun ι h => (hTv ι h v).1
    have hg : 0 ≤ lam⁻¹ * Coupling.quadForm Γ v :=
      mul_nonneg (inv_nonneg.mpr hlam.le) (quad_nonneg hΓ.posSemidef v)
    linarith
  have hid : Coupling.quadForm W⁻¹ r
      = 2 * (star r ⬝ᵥ (W⁻¹ *ᵥ r)).re - Coupling.quadForm W (W⁻¹ *ᵥ r) := by
    simp only [Coupling.quadForm, mulVec_mulVec, mul_nonsing_inv W hunit, one_mulVec]
    rw [Coupling.InverseFactorInternal.re_dot_comm (W⁻¹ *ᵥ r) r]
    ring
  have hdot : ∀ y : n → ℂ, (star r ⬝ᵥ y).re = (star m ⬝ᵥ y).re
      - ∑ ι ∈ S, ((star (ts ι) ⬝ᵥ y).re + (star (tv ι) ⬝ᵥ y).re) - (star e ⬝ᵥ y).re := by
    intro y
    rw [hr]
    simp only [star_sub, star_sum, star_add, sub_dotProduct, sum_dotProduct, add_dotProduct, Complex.sub_re,
      Complex.re_sum, Complex.add_re]
  have hm := scaled_bound hB one_pos m (W⁻¹ *ᵥ r)
  have he := scaled_bound hΓ hlam (-e) (W⁻¹ *ᵥ r)
  rw [quad_neg] at he
  simp only [star_neg, neg_dotProduct, Complex.neg_re, inv_one, one_mul] at he hm
  have hsum : ∑ ι ∈ S, (-(2 * (star (ts ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re)
        - (cs ι)⁻¹ * Coupling.quadForm (Ts ι) (W⁻¹ *ᵥ r)
        + (-(2 * (star (tv ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re) - (cv ι)⁻¹ * Coupling.quadForm (Tv ι) (W⁻¹ *ᵥ r)))
      ≤ ∑ ι ∈ S, (cs ι * hs ι + cv ι * hv ι) :=
    Finset.sum_le_sum fun ι h => add_le_add (hTs ι h _).2 (hTv ι h _).2
  have hsplit : ∑ ι ∈ S, (-(2 * (star (ts ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re)
        - (cs ι)⁻¹ * Coupling.quadForm (Ts ι) (W⁻¹ *ᵥ r)
        + (-(2 * (star (tv ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re) - (cv ι)⁻¹ * Coupling.quadForm (Tv ι) (W⁻¹ *ᵥ r)))
      = -(2 * ∑ ι ∈ S, ((star (ts ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re + (star (tv ι) ⬝ᵥ (W⁻¹ *ᵥ r)).re))
        - ∑ ι ∈ S, (cs ι)⁻¹ * Coupling.quadForm (Ts ι) (W⁻¹ *ᵥ r)
        - ∑ ι ∈ S, (cv ι)⁻¹ * Coupling.quadForm (Tv ι) (W⁻¹ *ᵥ r) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun ι _ => by ring
  have hl := hlow (W⁻¹ *ᵥ r)
  rw [hid, hdot]
  linarith

lemma base_posDef {Γ M : Matrix n n ℂ} (hΓ : Γ.PosDef) (τ : n → ℝ) (hτ : ∀ i, 0 < τ i)
    (hblock : ∀ i i', Γ i i' ≠ 0 → τ i = τ i') (hM : ∀ i i', M i i' = Γ i i' / (τ i : ℂ)) : M.PosDef := by
  have hs0 : ∀ i, 0 < Real.sqrt (τ i)⁻¹ := fun i => Real.sqrt_pos.mpr (inv_pos.mpr (hτ i))
  have hss : ∀ i, Real.sqrt (τ i)⁻¹ * Real.sqrt (τ i)⁻¹ = (τ i)⁻¹ :=
    fun i => Real.mul_self_sqrt (inv_nonneg.mpr (hτ i).le)
  have hMeq : M = (diagonal fun i => ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ))ᴴ * Γ
      * diagonal fun i => ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) := by
    ext i i'
    rw [mul_diagonal, diagonal_conjTranspose, diagonal_mul, hM]
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    by_cases h : Γ i i' = 0
    · simp [h]
    · have hti := hblock i i' h
      rw [← hti, div_eq_mul_inv]
      have e2 : ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) * Γ i i' * ((Real.sqrt (τ i)⁻¹ : ℝ) : ℂ)
          = Γ i i' * ((Real.sqrt (τ i)⁻¹ * Real.sqrt (τ i)⁻¹ : ℝ) : ℂ) := by push_cast; ring
      rw [e2, hss, Complex.ofReal_inv]
  rw [hMeq]
  refine hΓ.conjTranspose_mul_mul_same ?_
  intro x x' hxx
  funext i
  have h1 := congrFun hxx i
  simp only [mulVec_diagonal] at h1
  exact mul_left_cancel₀ (by exact_mod_cast (hs0 i).ne') h1

end Algebra

section Tail

variable {n J : Type*} [Fintype n] {μ : Measure (ℝ × ℝ)}

lemma int_weighted (w : ℝ × ℝ → ℝ) (hwi : Integrable w μ) (hw0 : ∀ᵐ p ∂μ, 0 ≤ w p) {F : ℝ × ℝ → ℂ}
    (hF : AEStronglyMeasurable F μ) (D : ℝ) (hFb : ∀ᵐ p ∂μ, ‖F p‖ ≤ D) :
    Integrable (fun p => (w p : ℂ) * F p) μ := by
  refine (hwi.mul_const D).mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.1).mul hF) ?_
  filter_upwards [hw0, hFb] with p h0 hb
  rw [norm_mul, Complex.norm_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left hb h0

lemma sum_three_swap {K : Type*} (Js : Finset K) (F : n → n → K → ℂ) :
    ∑ i, ∑ i', ∑ j ∈ Js, F i i' j = ∑ j ∈ Js, ∑ i, ∑ i', F i i' j := by
  calc ∑ i, ∑ i', ∑ j ∈ Js, F i i' j = ∑ i, ∑ j ∈ Js, ∑ i', F i i' j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ j ∈ Js, ∑ i, ∑ i', F i i' j := Finset.sum_comm

lemma pt_quad (Js : Finset J) (y : n → ℂ) (wv : ℝ) (φp : n → J → ℂ) :
    ∑ i, ∑ i', star (y i) * ((wv : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φp i j) * φp i' j) * y i'
      = ((wv * ∑ j ∈ Js, ‖∑ i, y i * φp i j‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp_rw [← Complex.conj_mul', map_sum, map_mul, Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_swap]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  simp only [Complex.star_def]
  ring

lemma pt_dot (Js : Finset J) (y : n → ℂ) (wv : ℂ) (fp : J → ℂ) (φp : n → J → ℂ) :
    ∑ i, star (y i) * (wv * ∑ j ∈ Js, fp j * (starRingEnd ℂ) (φp i j))
      = wv * ∑ j ∈ Js, fp j * (starRingEnd ℂ) (∑ i, y i * φp i j) := by
  simp_rw [map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  simp only [Complex.star_def]
  ring

lemma two_mul_le_weighted {a b c : ℝ} (hc : 0 < c) : 2 * (a * b) ≤ c * a ^ 2 + c⁻¹ * b ^ 2 := by
  have hcd : c * c⁻¹ = 1 := mul_inv_cancel₀ hc.ne'
  have key : c * a ^ 2 + c⁻¹ * b ^ 2 - 2 * (a * b) = c⁻¹ * (c * a - b) ^ 2 := by
    linear_combination (2 * a * b - c * a ^ 2) * hcd
  have : 0 ≤ c⁻¹ * (c * a - b) ^ 2 := mul_nonneg (inv_nonneg.mpr hc.le) (sq_nonneg _)
  linarith

lemma int_cross (Js : Finset J) (w : ℝ × ℝ → ℝ) (f : ℝ × ℝ → J → ℂ) (φ : n → ℝ × ℝ → J → ℂ)
    (hwi : Integrable w μ) (hw0 : ∀ᵐ p ∂μ, 0 ≤ w p)
    (hfm : ∀ j ∈ Js, AEStronglyMeasurable (fun p => f p j) μ)
    (hfi : ∀ j ∈ Js, Integrable (fun p => w p * ‖f p j‖ ^ 2) μ)
    (hφm : ∀ i, ∀ j ∈ Js, AEStronglyMeasurable (fun p => φ i p j) μ)
    {C : ℝ} (hφb : ∀ᵐ p ∂μ, ∀ i, ∀ j ∈ Js, ‖φ i p j‖ ≤ C) (i : n) :
    Integrable (fun p => (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)) μ := by
  have hdom : Integrable (fun p => C * (↑Js.card * w p + ∑ j ∈ Js, w p * ‖f p j‖ ^ 2)) μ :=
    ((hwi.const_mul _).add (integrable_finsetSum _ hfi)).const_mul C
  refine hdom.mono' ((Complex.continuous_ofReal.comp_aestronglyMeasurable hwi.1).mul
    (Finset.aestronglyMeasurable_fun_sum _ fun j hj =>
      (hfm j hj).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hφm i j hj)))) ?_
  filter_upwards [hφb, hw0] with p hp h0
  rw [norm_mul, Complex.norm_of_nonneg h0]
  have hb : ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)‖ ≤ C * ∑ j ∈ Js, (1 + ‖f p j‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, Complex.norm_conj]
    have h1 : ‖f p j‖ ≤ 1 + ‖f p j‖ ^ 2 := by nlinarith [sq_nonneg (‖f p j‖ - 1), norm_nonneg (f p j)]
    calc ‖f p j‖ * ‖φ i p j‖ ≤ (1 + ‖f p j‖ ^ 2) * C :=
          mul_le_mul h1 (hp i j hj) (norm_nonneg _) (by positivity)
      _ = C * (1 + ‖f p j‖ ^ 2) := by ring
  calc w p * ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)‖ ≤ w p * (C * ∑ j ∈ Js, (1 + ‖f p j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hb h0
    _ = C * (↑Js.card * w p + ∑ j ∈ Js, w p * ‖f p j‖ ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one, ← Finset.mul_sum]
        ring

lemma tail_piece (Js : Finset J) (w : ℝ × ℝ → ℝ) (f : ℝ × ℝ → J → ℂ) (φ : n → ℝ × ℝ → J → ℂ)
    (hwi : Integrable w μ) (hw0 : ∀ᵐ p ∂μ, 0 ≤ w p)
    (hfm : ∀ j ∈ Js, AEStronglyMeasurable (fun p => f p j) μ)
    (hfi : ∀ j ∈ Js, Integrable (fun p => w p * ‖f p j‖ ^ 2) μ)
    (hφm : ∀ i, ∀ j ∈ Js, AEStronglyMeasurable (fun p => φ i p j) μ)
    {C : ℝ} (hC : 0 ≤ C) (hφb : ∀ᵐ p ∂μ, ∀ i, ∀ j ∈ Js, ‖φ i p j‖ ≤ C)
    {c : ℝ} (hc : 0 < c) (y : n → ℂ) :
    0 ≤ c⁻¹ * Coupling.quadForm
        (fun i i' => ∫ p, (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j ∂μ) y ∧
    -(2 * (star (fun i => ∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j) ∂μ) ⬝ᵥ y).re)
      - c⁻¹ * Coupling.quadForm
        (fun i i' => ∫ p, (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j ∂μ) y
      ≤ c * ∫ p, w p * ∑ j ∈ Js, ‖f p j‖ ^ 2 ∂μ := by
  have hgm : ∀ j ∈ Js, AEStronglyMeasurable (fun p => ∑ i, y i * φ i p j) μ := fun j hj =>
    Finset.aestronglyMeasurable_fun_sum _ fun i _ => aestronglyMeasurable_const.mul (hφm i j hj)
  have hgb : ∀ᵐ p ∂μ, ∀ j ∈ Js, ‖∑ i, y i * φ i p j‖ ≤ ∑ i, ‖y i‖ * C := by
    filter_upwards [hφb] with p hp j hj
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hp i j hj) (norm_nonneg _)
  have iφφ : ∀ i i', Integrable (fun p => (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j) μ := by
    intro i i'
    refine int_weighted w hwi hw0 (Finset.aestronglyMeasurable_fun_sum _ fun j hj =>
      (Complex.continuous_conj.comp_aestronglyMeasurable (hφm i j hj)).mul (hφm i' j hj)) (∑ j ∈ Js, C * C) ?_
    filter_upwards [hφb] with p hp
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => ?_)
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul (hp i j hj) (hp i' j hj) (norm_nonneg _) hC
  have ifφ := int_cross Js w f φ hwi hw0 hfm hfi hφm hφb
  have iff : Integrable (fun p => w p * ∑ j ∈ Js, ‖f p j‖ ^ 2) μ := by
    have e : (fun p => w p * ∑ j ∈ Js, ‖f p j‖ ^ 2) = fun p => ∑ j ∈ Js, w p * ‖f p j‖ ^ 2 :=
      funext fun p => Finset.mul_sum _ _ _
    rw [e]
    exact integrable_finsetSum _ hfi
  have igg : Integrable (fun p => w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2) μ := by
    refine (hwi.mul_const (∑ j ∈ Js, (∑ i, ‖y i‖ * C) ^ 2)).mono'
      (hwi.1.mul (Finset.aestronglyMeasurable_fun_sum _ fun j hj => (hgm j hj).norm.pow 2)) ?_
    filter_upwards [hgb, hw0] with p hp h0
    rw [Real.norm_of_nonneg (mul_nonneg h0 (Finset.sum_nonneg fun j _ => by positivity))]
    exact mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun j hj => pow_le_pow_left₀ (norm_nonneg _) (hp j hj) 2) h0
  have hquad : Coupling.quadForm
      (fun i i' => ∫ p, (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j ∂μ) y
      = ∫ p, w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 ∂μ := by
    unfold Coupling.quadForm
    have e1 : star y ⬝ᵥ ((fun i i' => ∫ p, (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j ∂μ) *ᵥ y)
        = ∫ p, ((w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 : ℝ) : ℂ) ∂μ := by
      calc star y ⬝ᵥ ((fun i i' => ∫ p, (w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j ∂μ) *ᵥ y)
          = ∑ i, ∑ i', ∫ p, star (y i) * ((w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j) * y i' ∂μ := by
            simp only [dotProduct, mulVec, Pi.star_apply]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun i' _ => ?_
            rw [integral_mul_const, integral_const_mul]
            ring
        _ = ∫ p, ∑ i, ∑ i', star (y i) * ((w p : ℂ) * ∑ j ∈ Js, (starRingEnd ℂ) (φ i p j) * φ i' p j) * y i' ∂μ := by
            rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun i' _ => ((iφφ i i').const_mul _).mul_const _]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [integral_finsetSum _ fun i' _ => ((iφφ i i').const_mul _).mul_const _]
        _ = ∫ p, ((w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 : ℝ) : ℂ) ∂μ := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
            exact pt_quad Js y (w p) (fun i j => φ i p j)
    rw [e1, integral_complex_ofReal, Complex.ofReal_re]
  have hdot : (star (fun i => ∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j) ∂μ) ⬝ᵥ y).re
      = (∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j) ∂μ).re := by
    rw [Coupling.InverseFactorInternal.re_dot_comm]
    congr 1
    calc star y ⬝ᵥ (fun i => ∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j) ∂μ)
        = ∑ i, ∫ p, star (y i) * ((w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)) ∂μ := by
          simp only [dotProduct, Pi.star_apply]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [integral_const_mul]
      _ = ∫ p, ∑ i, star (y i) * ((w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (φ i p j)) ∂μ := by
          rw [integral_finsetSum _ fun i _ => (ifφ i).const_mul _]
      _ = ∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j) ∂μ := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
          exact pt_dot Js y (w p : ℂ) (f p) (fun i j => φ i p j)
  have hpt : ∀ᵐ p ∂μ, 2 * ‖(w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j)‖
      ≤ c * (w p * ∑ j ∈ Js, ‖f p j‖ ^ 2) + c⁻¹ * (w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2) := by
    filter_upwards [hw0] with p h0
    rw [norm_mul, Complex.norm_of_nonneg h0]
    have hs : 2 * ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j)‖
        ≤ c * ∑ j ∈ Js, ‖f p j‖ ^ 2 + c⁻¹ * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by norm_num)).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [norm_mul, Complex.norm_conj]
      exact two_mul_le_weighted hc
    calc 2 * (w p * ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j)‖)
        = w p * (2 * ‖∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j)‖) := by ring
      _ ≤ w p * (c * ∑ j ∈ Js, ‖f p j‖ ^ 2 + c⁻¹ * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hs h0
      _ = _ := by ring
  have hint : 2 * ∫ p, ‖(w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j)‖ ∂μ
      ≤ c * ∫ p, w p * ∑ j ∈ Js, ‖f p j‖ ^ 2 ∂μ
        + c⁻¹ * ∫ p, w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 ∂μ := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_const_mul,
      ← integral_add (iff.const_mul _) (igg.const_mul _)]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => by positivity)
      ((iff.const_mul _).add (igg.const_mul _)) hpt
  have hre := Complex.abs_re_le_norm
    (∫ p, (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j) ∂μ)
  have hnorm := norm_integral_le_integral_norm
    (μ := μ) (fun p => (w p : ℂ) * ∑ j ∈ Js, f p j * (starRingEnd ℂ) (∑ i, y i * φ i p j))
  have hQ0 : 0 ≤ ∫ p, w p * ∑ j ∈ Js, ‖∑ i, y i * φ i p j‖ ^ 2 ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hw0] with p h0
    exact mul_nonneg h0 (Finset.sum_nonneg fun j _ => by positivity)
  refine ⟨?_, ?_⟩
  · rw [hquad]
    exact mul_nonneg (inv_nonneg.mpr hc.le) hQ0
  · rw [hquad, hdot]
    have := (abs_le.mp hre).1
    linarith

end Tail

section Cell

lemma pair_strain (S : Fin 3 → Fin 3 → ℂ) (V : Fin 3 → ℂ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = true), ‖pairVec S V j‖ ^ 2
      = ∑ a : Fin 3, ∑ b : Fin 3, ‖S a b‖ ^ 2 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, pairVec]
  ring

lemma pair_vel (S : Fin 3 → Fin 3 → ℂ) (V : Fin 3 → ℂ) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin 12 => decide (j.val < 9) = false), ‖pairVec S V j‖ ^ 2
      = ∑ a : Fin 3, ‖V a‖ ^ 2 := by
  rw [Finset.sum_filter]
  simp [Fin.sum_univ_succ, pairVec]

lemma proj_continuous (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (K.proj d d' F) := by
  unfold CellBox.proj
  split_ifs with h
  · obtain ⟨c, hc⟩ := h.choose_spec.1
    have e : h.choose = fun p : ℝ × ℝ => ∑ j, ∑ l, c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) :=
      funext hc
    rw [e]
    fun_prop
  · exact continuous_const

lemma lineWeight_cont (K : CellBox) : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := by
  unfold CellBox.lineWeight
  split_ifs <;> fun_prop

lemma rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

lemma rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

lemma lineWeight_bounds {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    0 ≤ K.lineWeight p.1 ∧ K.lineWeight p.1 ≤ (1 + K.r₁⁻¹) * p.1 := by
  have h1 : K.r₁ ≤ p.1 := hp.1.1
  have h0 : 0 ≤ K.r₁ := hK.r_order.1
  unfold CellBox.lineWeight
  split_ifs with h
  · rw [h, _root_.inv_zero]
    constructor <;> linarith
  · have hpos : 0 < K.r₁ := lt_of_le_of_ne h0 (Ne.symm h)
    refine ⟨zero_le_one, ?_⟩
    have : 1 ≤ K.r₁⁻¹ * p.1 := by
      rw [← inv_mul_cancel₀ hpos.ne']
      exact mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr h0)
    nlinarith

lemma weight_integrable (K : CellBox) : Integrable (fun p : ℝ × ℝ => K.lineWeight p.1) (volume.restrict K.rect) :=
  (lineWeight_cont K).continuousOn.integrableOn_compact (rect_compact K)

lemma weight_nonneg {K : CellBox} (hK : IsCellBox K) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ K.lineWeight p.1 :=
  ae_restrict_of_forall_mem (rect_measurable K) fun _ hp => (lineWeight_bounds hK hp).1

lemma tail_part {K : CellBox} (hK : IsCellBox K) {F : ℝ × ℝ → ℂ} {Big : ℝ × ℝ → ℝ}
    (hF : AEStronglyMeasurable F (volume.restrict K.rect)) (hBig : IntegrableOn (fun p => p.1 * Big p) K.rect)
    (hle : ∀ p ∈ K.rect, ‖F p‖ ^ 2 ≤ Big p) (d d' : ℕ) :
    AEStronglyMeasurable (fun p => F p - K.proj d d' F p) (volume.restrict K.rect) ∧
      Integrable (fun p => K.lineWeight p.1 * ‖F p - K.proj d d' F p‖ ^ 2) (volume.restrict K.rect) := by
  have hP := proj_continuous K d d' F
  have hm : AEStronglyMeasurable (fun p => F p - K.proj d d' F p) (volume.restrict K.rect) :=
    hF.sub hP.aestronglyMeasurable
  refine ⟨hm, ?_⟩
  have hPi : Integrable (fun p => K.lineWeight p.1 * ‖K.proj d d' F p‖ ^ 2) (volume.restrict K.rect) :=
    ((lineWeight_cont K).mul (hP.norm.pow 2)).continuousOn.integrableOn_compact (rect_compact K)
  have hdom : Integrable (fun p => 2 * ((1 + K.r₁⁻¹) * (p.1 * Big p))
      + 2 * (K.lineWeight p.1 * ‖K.proj d d' F p‖ ^ 2)) (volume.restrict K.rect) :=
    ((hBig.const_mul _).const_mul 2).add (hPi.const_mul 2)
  refine hdom.mono' ((lineWeight_cont K).aestronglyMeasurable.mul (hm.norm.pow 2)) ?_
  refine ae_restrict_of_forall_mem (rect_measurable K) fun p hp => ?_
  obtain ⟨hw0, hw1⟩ := lineWeight_bounds hK hp
  have hr0 : 0 ≤ (1 + K.r₁⁻¹) * p.1 :=
    mul_nonneg (by have := inv_nonneg.mpr hK.r_order.1; linarith) (le_trans hK.r_order.1 hp.1.1)
  have hsq : ‖F p - K.proj d d' F p‖ ^ 2 ≤ 2 * ‖F p‖ ^ 2 + 2 * ‖K.proj d d' F p‖ ^ 2 := by
    have h2 : ‖F p - K.proj d d' F p‖ ^ 2 ≤ (‖F p‖ + ‖K.proj d d' F p‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le _ _) 2
    nlinarith [sq_nonneg (‖F p‖ - ‖K.proj d d' F p‖)]
  rw [Real.norm_of_nonneg (mul_nonneg hw0 (by positivity))]
  calc K.lineWeight p.1 * ‖F p - K.proj d d' F p‖ ^ 2
      ≤ K.lineWeight p.1 * (2 * ‖F p‖ ^ 2 + 2 * ‖K.proj d d' F p‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hw0
    _ = 2 * (K.lineWeight p.1 * ‖F p‖ ^ 2) + 2 * (K.lineWeight p.1 * ‖K.proj d d' F p‖ ^ 2) := by ring
    _ ≤ 2 * ((1 + K.r₁⁻¹) * (p.1 * Big p)) + 2 * (K.lineWeight p.1 * ‖K.proj d d' F p‖ ^ 2) := by
      have : K.lineWeight p.1 * ‖F p‖ ^ 2 ≤ (1 + K.r₁⁻¹) * p.1 * Big p :=
        mul_le_mul hw1 (hle p hp) (by positivity) hr0
      nlinarith

end Cell

lemma uniform_bound {n J : Type*} [Fintype n] [Fintype J] {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (φ : n → ℝ × ℝ → J → ℂ) (h : ∀ i j, ∃ c : ℝ, ∀ p ∈ s, ‖φ i p j‖ ≤ c) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ p ∂(volume.restrict s), ∀ i j, ‖φ i p j‖ ≤ C := by
  choose c hc using h
  refine ⟨∑ i, ∑ j, |c i j|, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  refine ae_restrict_of_forall_mem hs fun p hp i j => ?_
  calc ‖φ i p j‖ ≤ |c i j| := (hc i j p hp).trans (le_abs_self _)
    _ ≤ ∑ j', |c i j'| := Finset.single_le_sum (f := fun j' => |c i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |c i' j'| := Finset.single_le_sum (f := fun i' => ∑ j', |c i' j'|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

lemma cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => by positivity

end Internal.RowRemoval

end Assembly

end CertCell

end Breakdown

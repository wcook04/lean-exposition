import Breakdown.CertCell.CouplingStatements

open Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Coupling

namespace LabelScale

def scaleVec {n : Type*} (f : n → ℝ) (x : n → ℂ) : n → ℂ := fun i => (f i : ℂ) * x i

variable {n : Type*} [Fintype n] {L : Type*}

def IsLabelBlock (M : Matrix n n ℂ) (lab : n → L) : Prop := ∀ i j, lab i ≠ lab j → M i j = 0

def IsLabelConst (lab : n → L) (f : n → ℝ) : Prop := ∀ i j, lab i = lab j → f i = f j

theorem quad_nonneg {M : Matrix n n ℂ} (hM : M.PosSemidef) (x : n → ℂ) : 0 ≤ quadForm M x :=
  (Complex.le_def.mp (hM.dotProduct_mulVec_nonneg x)).1

theorem eq_zero_of_quad_nonpos {M : Matrix n n ℂ} (hM : M.PosDef) {x : n → ℂ} (hx : quadForm M x ≤ 0) :
    x = 0 := by
  by_contra h
  have h1 := (Complex.lt_def.mp (hM.dotProduct_mulVec_pos h)).1
  unfold quadForm at hx
  simp only [Complex.zero_re] at h1
  linarith

theorem cross_swap {M : Matrix n n ℂ} (hM : M.IsHermitian) (x y : n → ℂ) :
    crossForm M x y = crossForm M y x := by
  unfold crossForm
  rw [star_dotProduct x (M *ᵥ y), star_mulVec, hM.eq, ← dotProduct_mulVec]
  exact Complex.conj_re _

theorem quad_eq_cross (M : Matrix n n ℂ) (x : n → ℂ) : quadForm M x = crossForm M x x := rfl

theorem quad_sub {M : Matrix n n ℂ} (hM : M.IsHermitian) (x y : n → ℂ) :
    quadForm M (x - y) = quadForm M x + quadForm M y - 2 * crossForm M x y := by
  have h := cross_swap hM y x
  unfold quadForm
  unfold crossForm at h ⊢
  rw [star_sub, mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub]
  simp only [Complex.sub_re]
  rw [h]
  ring

theorem quad_smul (M : Matrix n n ℂ) (t : ℝ) (x : n → ℂ) :
    quadForm M ((t : ℂ) • x) = t ^ 2 * quadForm M x := by
  unfold quadForm
  rw [star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul]
  simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul]
  rw [← mul_assoc, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
  ring

theorem crossForm_add_left (M : Matrix n n ℂ) (x y u : n → ℂ) :
    crossForm M (x + y) u = crossForm M x u + crossForm M y u := by
  unfold crossForm
  rw [star_add, add_dotProduct, Complex.add_re]

theorem crossForm_zero_left (M : Matrix n n ℂ) (u : n → ℂ) : crossForm M 0 u = 0 := by
  unfold crossForm
  simp

theorem crossForm_sum_left {ι : Type*} (s : Finset ι) (M : Matrix n n ℂ) (x : ι → n → ℂ) (u : n → ℂ) :
    crossForm M (∑ X ∈ s, x X) u = ∑ X ∈ s, crossForm M (x X) u := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [crossForm_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, crossForm_add_left, ih]

theorem block_mul_comm {M : Matrix n n ℂ} {lab : n → L} (hM : IsLabelBlock M lab) {f : n → ℂ}
    (hf : ∀ i j, lab i = lab j → f i = f j) (i j : n) : M i j * f j = f i * M i j := by
  by_cases h : lab i = lab j
  · rw [hf i j h, mul_comm]
  · rw [hM i j h]
    ring

theorem crossForm_scale {M : Matrix n n ℂ} {lab : n → L} (hM : IsLabelBlock M lab) {f : n → ℝ}
    (hf : IsLabelConst lab f) (x y : n → ℂ) :
    crossForm M x (scaleVec f y) = crossForm M (scaleVec f x) y := by
  unfold crossForm scaleVec
  congr 1
  simp only [dotProduct, mulVec, Pi.star_apply, Complex.star_def, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  have h := block_mul_comm hM (f := fun i => (f i : ℂ)) (fun i j hij => by simp only [hf i j hij]) i j
  linear_combination ((starRingEnd ℂ) (x i) * y j) * h

theorem scaleVec_scaleVec (f g : n → ℝ) (x : n → ℂ) :
    scaleVec f (scaleVec g x) = scaleVec (fun i => f i * g i) x := by
  funext i
  simp only [scaleVec, Complex.ofReal_mul]
  ring

theorem scaleVec_add (f : n → ℝ) (x y : n → ℂ) : scaleVec f (x + y) = scaleVec f x + scaleVec f y := by
  funext i
  simp only [scaleVec, Pi.add_apply]
  ring

theorem scaleVec_sum {ι : Type*} (s : Finset ι) (f : n → ℝ) (x : ι → n → ℂ) :
    scaleVec f (∑ X ∈ s, x X) = ∑ X ∈ s, scaleVec f (x X) := by
  funext i
  simp only [scaleVec, Finset.sum_apply, Finset.mul_sum]

theorem scaleVec_const (t : ℝ) (x : n → ℂ) : scaleVec (fun _ => t) x = (t : ℂ) • x := by
  funext i
  simp only [scaleVec, Pi.smul_apply, smul_eq_mul]

theorem quad_scale_const (M : Matrix n n ℂ) {t : ℝ} (ht : 0 ≤ t) (x : n → ℂ) :
    quadForm M (scaleVec (fun _ => Real.sqrt t) x) = t * quadForm M x := by
  rw [scaleVec_const, quad_smul, Real.sq_sqrt ht]

theorem weighted_combine {ι : Type*} [Fintype ι] {M : Matrix n n ℂ} {lab : n → L}
    (hM : IsLabelBlock M lab) (hP : M.PosSemidef) (a : ι → n → ℝ) (ha : ∀ X, IsLabelConst lab (a X))
    (hsum : ∀ i, ∑ X, a X i ^ 2 ≤ 1) (z : ι → n → ℂ) :
    quadForm M (∑ X, scaleVec (a X) (z X)) ≤ ∑ X, quadForm M (z X) := by
  set s := ∑ X, scaleVec (a X) (z X) with hs
  set b : n → ℝ := fun i => Real.sqrt (1 - ∑ X, a X i ^ 2) with hb
  have hbc : IsLabelConst lab b := by
    intro i j hij
    simp only [hb]
    congr 2
    exact Finset.sum_congr rfl (fun X _ => by rw [ha X i j hij])
  have hH := hP.isHermitian
  have h0 : 0 ≤ ∑ X, quadForm M (z X - scaleVec (a X) s) + quadForm M (scaleVec b s) :=
    add_nonneg (Finset.sum_nonneg (fun X _ => quad_nonneg hP _)) (quad_nonneg hP _)
  have e1 : ∀ X, quadForm M (z X - scaleVec (a X) s)
      = quadForm M (z X) + crossForm M (scaleVec (fun i => a X i * a X i) s) s
        - 2 * crossForm M (scaleVec (a X) (z X)) s := by
    intro X
    rw [quad_sub hH, crossForm_scale hM (ha X), quad_eq_cross M (scaleVec (a X) s),
      crossForm_scale hM (ha X), scaleVec_scaleVec]
  have e2 : quadForm M (scaleVec b s) = crossForm M (scaleVec (fun i => b i * b i) s) s := by
    rw [quad_eq_cross, crossForm_scale hM hbc, scaleVec_scaleVec]
  have e3 : ∑ X, scaleVec (fun i => a X i * a X i) s + scaleVec (fun i => b i * b i) s = s := by
    funext i
    simp only [Pi.add_apply, Finset.sum_apply, scaleVec]
    rw [← Finset.sum_mul, ← add_mul]
    have hi : ∑ X, a X i * a X i + b i * b i = 1 := by
      simp only [hb]
      rw [Real.mul_self_sqrt (by linarith [hsum i])]
      simp only [sq]
      ring
    rw [← Complex.ofReal_sum, ← Complex.ofReal_add, hi, Complex.ofReal_one, one_mul]
  have e4 : ∑ X, crossForm M (scaleVec (fun i => a X i * a X i) s) s
      + crossForm M (scaleVec (fun i => b i * b i) s) s = quadForm M s := by
    rw [← crossForm_sum_left, ← crossForm_add_left, e3, quad_eq_cross]
  have e5 : ∑ X, crossForm M (scaleVec (a X) (z X)) s = quadForm M s := by
    rw [← crossForm_sum_left, quad_eq_cross]
  simp only [e1] at h0
  rw [e2, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, e5] at h0
  linarith [e4]

theorem combine_four {J : Type*} [Fintype J] {M : Matrix n n ℂ} {lab : n → L}
    (hM : IsLabelBlock M lab) (hP : M.PosSemidef) (a₁ a₂ a₃ : n → ℝ) (a₄ : J → n → ℝ)
    (h₁ : IsLabelConst lab a₁) (h₂ : IsLabelConst lab a₂) (h₃ : IsLabelConst lab a₃)
    (h₄ : ∀ j, IsLabelConst lab (a₄ j))
    (hsum : ∀ i, a₁ i ^ 2 + a₂ i ^ 2 + a₃ i ^ 2 + ∑ j, a₄ j i ^ 2 ≤ 1)
    (z₁ z₂ z₃ : n → ℂ) (z₄ : J → n → ℂ) :
    quadForm M (scaleVec a₁ z₁ + scaleVec a₂ z₂ + scaleVec a₃ z₃ + ∑ j, scaleVec (a₄ j) (z₄ j))
      ≤ quadForm M z₁ + quadForm M z₂ + quadForm M z₃ + ∑ j, quadForm M (z₄ j) := by
  let a : Option (Option (Option J)) → n → ℝ := fun X => X.elim a₁ (fun Y => Y.elim a₂ (fun Z => Z.elim a₃ a₄))
  let z : Option (Option (Option J)) → n → ℂ := fun X => X.elim z₁ (fun Y => Y.elim z₂ (fun Z => Z.elim z₃ z₄))
  have ha : ∀ X, IsLabelConst lab (a X) := by
    intro X
    rcases X with _ | _ | _ | j
    · exact h₁
    · exact h₂
    · exact h₃
    · exact h₄ j
  have hs : ∀ i, ∑ X, a X i ^ 2 ≤ 1 := by
    intro i
    have := hsum i
    simp only [Fintype.sum_option, a, Option.elim]
    linarith
  have h := weighted_combine hM hP a ha hs z
  simp only [Fintype.sum_option, a, z, Option.elim] at h
  simpa only [add_assoc] using h

theorem comm_of_block {M : Matrix n n ℂ} [DecidableEq n] {lab : n → L} (hM : IsLabelBlock M lab) {f : n → ℂ}
    (hf : ∀ i j, lab i = lab j → f i = f j) : M * diagonal f = diagonal f * M := by
  ext i j
  rw [mul_diagonal, diagonal_mul]
  exact block_mul_comm hM hf i j

theorem inv_block [DecidableEq n] {M : Matrix n n ℂ} {lab : n → L} (hM : IsLabelBlock M lab)
    (hdet : IsUnit M.det) : IsLabelBlock M⁻¹ lab := by
  classical
  intro i j hij
  let f : n → ℂ := fun l => if lab l = lab j then 1 else 0
  have hf : ∀ a b, lab a = lab b → f a = f b := by
    intro a b hab
    simp only [f, hab]
  have hc := comm_of_block hM hf
  have hc' : M⁻¹ * diagonal f = diagonal f * M⁻¹ := by
    calc M⁻¹ * diagonal f = M⁻¹ * diagonal f * (M * M⁻¹) := by rw [mul_nonsing_inv M hdet, Matrix.mul_one]
      _ = M⁻¹ * (M * diagonal f) * M⁻¹ := by rw [hc]; simp only [Matrix.mul_assoc]
      _ = (M⁻¹ * M) * diagonal f * M⁻¹ := by simp only [Matrix.mul_assoc]
      _ = diagonal f * M⁻¹ := by rw [nonsing_inv_mul M hdet, Matrix.one_mul]
  have := congrFun (congrFun hc' i) j
  rw [mul_diagonal, diagonal_mul] at this
  simp only [f, hij, if_true, if_false, mul_one, zero_mul] at this
  exact this

theorem scaleVec_eq_mulVec [DecidableEq n] (f : n → ℝ) (x : n → ℂ) :
    scaleVec f x = diagonal (fun i => (f i : ℂ)) *ᵥ x := by
  funext i
  rw [mulVec_diagonal]
  rfl

theorem inverseWeightedSq_scaled [DecidableEq n] {M : Matrix n n ℂ} {lab : n → L} (hM : IsLabelBlock M lab)
    (hdet : IsUnit M.det) (c : n → ℝ) (hc : IsLabelConst lab c) (hpos : ∀ i, 0 < c i) (y : n → ℂ) :
    inverseWeightedSq (Matrix.of fun i j => M i j / (c i : ℂ)) y = quadForm M⁻¹ (scaleVec (fun i => Real.sqrt (c i)) y) := by
  have hne : ∀ i, (c i : ℂ) ≠ 0 := fun i => Complex.ofReal_ne_zero.mpr (hpos i).ne'
  have hS : (Matrix.of fun i j => M i j / (c i : ℂ)) = diagonal (fun i => (c i : ℂ)⁻¹) * M := by
    ext i j
    rw [of_apply, diagonal_mul, div_eq_inv_mul]
  have hinv : (Matrix.of fun i j => M i j / (c i : ℂ))⁻¹ = M⁻¹ * diagonal (fun i => (c i : ℂ)) := by
    apply inv_eq_right_inv
    rw [hS, Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hdet, diagonal_mul_diagonal]
    rw [← diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (hne i)
  have hMi := inv_block hM hdet
  have hsq : IsLabelConst lab (fun i => Real.sqrt (c i)) := by
    intro i j hij
    simp only [hc i j hij]
  unfold inverseWeightedSq
  rw [hinv, quad_eq_cross, quad_eq_cross, ← crossForm_scale hMi hsq, scaleVec_scaleVec,
    show (fun i => Real.sqrt (c i) * Real.sqrt (c i)) = c from funext fun i => Real.mul_self_sqrt (hpos i).le]
  unfold crossForm
  rw [← mulVec_mulVec, ← scaleVec_eq_mulVec]

theorem sum_sq_ite_mem {J : Type*} [Fintype J] [DecidableEq J] (S : Finset J) {x : ℝ} (hx : 0 ≤ x) :
    ∑ j, (if j ∈ S then Real.sqrt x else 0) ^ 2 = (S.card : ℝ) * x := by
  have : ∀ j, (if j ∈ S then Real.sqrt x else 0) ^ 2 = if j ∈ S then x else 0 := by
    intro j
    split_ifs
    · exact Real.sq_sqrt hx
    · ring
  simp only [this]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

theorem sqrt_div_mul_sqrt {w c : ℝ} (hw : 0 ≤ w) (hc : 0 < c) : Real.sqrt (w / c) * Real.sqrt c = Real.sqrt w := by
  rw [← Real.sqrt_mul (div_nonneg hw hc.le), div_mul_cancel₀ _ hc.ne']

end LabelScale

end Coupling

end CertCell

end Breakdown

module

public import QuarticQuery.Statement

/-!
# Multi-affine extension on the sign cube

`ext g μ` is the expectation of `g` under the product measure with means `μ`, read as
a polynomial, so it is defined for every real `μ`. `D a g` is the discrete derivative.
Blueprint lemmas C1–C5.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Finset

namespace QuarticQuery.ForrelationLower

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The sign of a bit, as a real. -/
noncomputable def sg (b : Bool) : ℝ := if b then -1 else 1

/-- Support for blueprint C1–C5. -/
@[simp] theorem sg_false : sg false = 1 := by simp [sg]
/-- Support for blueprint C1–C5. -/
@[simp] theorem sg_true : sg true = -1 := by simp [sg]
/-- Support for blueprint C1–C5. -/
theorem sg_not (b : Bool) : sg (!b) = - sg b := by cases b <;> simp
/-- Support for blueprint C1–C5. -/
theorem sg_sq (b : Bool) : sg b * sg b = 1 := by cases b <;> simp
/-- Support for blueprint C1–C5. -/
theorem abs_sg (b : Bool) : |sg b| = 1 := by cases b <;> simp
/-- Support for blueprint C1–C5. -/
theorem sg_eq_bitSign (b : Bool) : sg b = (bitSign b : ℝ) := by cases b <;> simp [bitSign]

/-- Weight of one bit under mean `m`. -/
noncomputable def piB (m : ℝ) (b : Bool) : ℝ := (1 + m * sg b) / 2

/-- Support for blueprint C1–C5. -/
theorem piB_add (m : ℝ) : piB m false + piB m true = 1 := by simp [piB]; ring
/-- Support for blueprint C1–C5. -/
theorem piB_nonneg {m : ℝ} (h : |m| ≤ 1) (b : Bool) : 0 ≤ piB m b := by
  have := abs_le.mp h
  cases b <;> simp only [piB, sg_false, sg_true] <;> linarith

/-- Weight of a point under the product measure with means `μ`. -/
noncomputable def bw (μ : ι → ℝ) (z : ι → Bool) : ℝ := ∏ a, piB (μ a) (z a)

/-- Multi-affine extension. -/
noncomputable def ext (g : (ι → Bool) → ℝ) (μ : ι → ℝ) : ℝ := ∑ z, g z * bw μ z

/-- Discrete derivative. -/
noncomputable def D (a : ι) (g : (ι → Bool) → ℝ) (z : ι → Bool) : ℝ :=
  (g (Function.update z a false) - g (Function.update z a true)) / 2

/-- Support for blueprint C1–C5. -/
theorem bw_nonneg {μ : ι → ℝ} (h : ∀ a, |μ a| ≤ 1) (z : ι → Bool) : 0 ≤ bw μ z :=
  prod_nonneg fun a _ => piB_nonneg (h a) _

/-- Support for blueprint C1–C5. -/
theorem sum_bw (μ : ι → ℝ) : ∑ z, bw μ z = 1 := by
  have := Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset Bool))
    (fun a b => piB (μ a) b)
  simp only [Fintype.piFinset_univ] at this
  unfold bw
  rw [← this]
  simp [add_comm (piB _ true), piB_add]

/-- C1, linearity. -/
theorem ext_add (g h : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext (fun z => g z + h z) μ = ext g μ + ext h μ := by
  simp [ext, add_mul, sum_add_distrib]

/-- Support for blueprint C1–C5. -/
theorem ext_smul (c : ℝ) (g : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext (fun z => c * g z) μ = c * ext g μ := by
  simp [ext, mul_sum, mul_assoc]

/-- Support for blueprint C1–C5. -/
theorem ext_sum {J : Type} (s : Finset J) (g : J → (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext (fun z => ∑ j ∈ s, g j z) μ = ∑ j ∈ s, ext (g j) μ := by
  simp only [ext, sum_mul]
  exact sum_comm

/-- C1, boundedness. -/
theorem abs_ext_le {g : (ι → Bool) → ℝ} {B : ℝ} (hg : ∀ z, |g z| ≤ B) {μ : ι → ℝ}
    (hμ : ∀ a, |μ a| ≤ 1) : |ext g μ| ≤ B := by
  calc |ext g μ| ≤ ∑ z, |g z * bw μ z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ z, B * bw μ z := sum_le_sum fun z _ => by
        rw [abs_mul, abs_of_nonneg (bw_nonneg hμ z)]
        exact mul_le_mul_of_nonneg_right (hg z) (bw_nonneg hμ z)
    _ = B := by rw [← mul_sum, sum_bw, mul_one]

/-- Support for blueprint C1–C5. -/
theorem ext_nonneg {g : (ι → Bool) → ℝ} (hg : ∀ z, 0 ≤ g z) {μ : ι → ℝ}
    (hμ : ∀ a, |μ a| ≤ 1) : 0 ≤ ext g μ :=
  sum_nonneg fun z _ => mul_nonneg (hg z) (bw_nonneg hμ z)

/-- Support for blueprint C1–C5. -/
theorem ext_mono {g h : (ι → Bool) → ℝ} (hg : ∀ z, g z ≤ h z) {μ : ι → ℝ}
    (hμ : ∀ a, |μ a| ≤ 1) : ext g μ ≤ ext h μ :=
  sum_le_sum fun z _ => mul_le_mul_of_nonneg_right (hg z) (bw_nonneg hμ z)

/-- Support for blueprint C1–C5. -/
theorem ext_const (c : ℝ) (μ : ι → ℝ) : ext (fun _ => c) μ = c := by
  simp [ext, ← mul_sum, sum_bw]

/-- Flip one coordinate. -/
def flip (a : ι) (z : ι → Bool) : ι → Bool := Function.update z a (!z a)

/-- Support for blueprint C1–C5. -/
@[simp] theorem flip_flip (a : ι) (z : ι → Bool) : flip a (flip a z) = z := by
  funext b
  by_cases h : b = a
  · subst h; simp [flip]
  · simp [flip, Function.update_of_ne h]

/-- Flipping, as an equivalence. -/
def flipEquiv (a : ι) : (ι → Bool) ≃ (ι → Bool) where
  toFun := flip a
  invFun := flip a
  left_inv := flip_flip a
  right_inv := flip_flip a

/-- Support for blueprint C1–C5. -/
theorem sum_flip (a : ι) (h : (ι → Bool) → ℝ) : ∑ z, h (flip a z) = ∑ z, h z :=
  (flipEquiv a).sum_comp h

/-- Support for blueprint C1–C5. -/
theorem update_flip (a : ι) (z : ι → Bool) (b : Bool) :
    Function.update (flip a z) a b = Function.update z a b := by
  simp [flip]

/-- The product over the other coordinates. -/
noncomputable def bwOff (a : ι) (μ : ι → ℝ) (z : ι → Bool) : ℝ := ∏ b ∈ univ.erase a, piB (μ b) (z b)

/-- Support for blueprint C1–C5. -/
theorem bw_eq (a : ι) (μ : ι → ℝ) (z : ι → Bool) : bw μ z = piB (μ a) (z a) * bwOff a μ z :=
  (mul_prod_erase univ _ (mem_univ a)).symm

/-- Support for blueprint C1–C5. -/
theorem bwOff_update (a : ι) (μ : ι → ℝ) (z : ι → Bool) (b : Bool) :
    bwOff a μ (Function.update z a b) = bwOff a μ z :=
  prod_congr rfl fun c hc => by rw [Function.update_of_ne (ne_of_mem_erase hc)]

/-- Support for blueprint C1–C5. -/
theorem bwOff_flip (a : ι) (μ : ι → ℝ) (z : ι → Bool) : bwOff a μ (flip a z) = bwOff a μ z :=
  bwOff_update a μ z _

/-- Support for blueprint C1–C5. -/
theorem bwOff_congr (a : ι) {μ ν : ι → ℝ} (h : ∀ b, b ≠ a → μ b = ν b) (z : ι → Bool) :
    bwOff a μ z = bwOff a ν z :=
  prod_congr rfl fun c hc => by rw [h c (ne_of_mem_erase hc)]

/-- Support for blueprint C1–C5. -/
@[simp] theorem flip_apply_self (a : ι) (z : ι → Bool) : flip a z a = !z a := by simp [flip]

/-- The odd part of a sum over the cube. -/
theorem sum_mul_sg_eq (a : ι) (e u : (ι → Bool) → ℝ) (hu : ∀ z, u (flip a z) = u z) :
    ∑ z, e z * u z = (1 / 2) * ∑ z, (e z + e (flip a z)) * u z := by
  have h := sum_flip a (fun z => e z * u z)
  simp only [hu] at h
  simp only [add_mul, sum_add_distrib, h]
  ring

/-- Support for blueprint C1–C5. -/
theorem sum_inv_eq (a : ι) (m : ℝ) (u : (ι → Bool) → ℝ) (hu : ∀ z, u (flip a z) = u z) :
    ∑ z, u z * piB m (z a) = (1 / 2) * ∑ z, u z := by
  have := sum_mul_sg_eq a (fun z => piB m (z a)) u hu
  simp only [mul_comm (u _)] at this ⊢
  rw [this]
  congr 1
  refine sum_congr rfl fun z _ => ?_
  rw [flip_apply_self]
  have : piB m (z a) + piB m (!z a) = 1 := by
    cases z a
    · simpa using piB_add m
    · simpa [add_comm] using piB_add m
  rw [this, one_mul]

/-- Support for blueprint C1–C5. -/
theorem D_flip (a : ι) (g : (ι → Bool) → ℝ) (z : ι → Bool) : D a g (flip a z) = D a g z := by
  simp [D, update_flip]

/-- `ext (D a g)` as a half-sum off `a`. -/
theorem ext_D_eq (a : ι) (g : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext (D a g) μ = (1 / 2) * ∑ z, D a g z * bwOff a μ z := by
  unfold ext
  have := sum_inv_eq a (μ a) (fun z => D a g z * bwOff a μ z)
    fun z => by simp only [D_flip, bwOff_flip]
  rw [← this]
  exact sum_congr rfl fun z _ => by rw [bw_eq a]; ring

/-- Support for blueprint C1–C5. -/
theorem add_flip_sg (a : ι) (g : (ι → Bool) → ℝ) (z : ι → Bool) :
    g z * sg (z a) + g (flip a z) * sg (flip a z a) = 2 * D a g z := by
  have h1 : Function.update z a (z a) = z := Function.update_eq_self a z
  cases hz : z a
  · have h2 : Function.update z a false = z := by rw [← hz, h1]
    simp [D, flip, hz, h2]; ring
  · have h2 : Function.update z a true = z := by rw [← hz, h1]
    simp [D, flip, hz, h2]; ring

/-- The sum form of the derivative. -/
theorem sum_sg_eq (a : ι) (g : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ∑ z, g z * (sg (z a) / 2 * bwOff a μ z) = ext (D a g) μ := by
  rw [ext_D_eq]
  have := sum_mul_sg_eq a (fun z => g z * sg (z a)) (bwOff a μ) (bwOff_flip a μ)
  have e : ∑ z, g z * (sg (z a) / 2 * bwOff a μ z) =
      (1 / 2) * ∑ z, g z * sg (z a) * bwOff a μ z := by
    rw [mul_sum]; exact sum_congr rfl fun z _ => by ring
  rw [e, this]
  simp only [add_flip_sg, mul_sum, sum_mul]
  exact sum_congr rfl fun z _ => by ring

/-- C2, the chain rule. -/
theorem hasDerivAt_ext (g : (ι → Bool) → ℝ) {c : ℝ → ι → ℝ} {c' : ι → ℝ} {t : ℝ}
    (hc : ∀ a, HasDerivAt (fun s => c s a) (c' a) t) :
    HasDerivAt (fun s => ext g (c s)) (∑ a, c' a * ext (D a g) (c t)) t := by
  have key : ∀ z : ι → Bool, HasDerivAt (fun s => bw (c s) z)
      (∑ a, c' a * (sg (z a) / 2 * bwOff a (c t) z)) t := by
    intro z
    have h : ∀ a ∈ (univ : Finset ι), HasDerivAt (fun s => piB (c s a) (z a))
        (c' a * sg (z a) / 2) t := fun a _ => by
      simpa [piB, mul_comm] using (((hc a).mul_const (sg (z a))).const_add 1).div_const 2
    have := HasDerivAt.fun_finsetProd h
    unfold bw
    convert this using 1
    refine sum_congr rfl fun a _ => ?_
    simp only [bwOff, smul_eq_mul]
    ring
  have : HasDerivAt (fun s => ext g (c s))
      (∑ z, g z * ∑ a, c' a * (sg (z a) / 2 * bwOff a (c t) z)) t :=
    HasDerivAt.fun_sum fun z _ => (key z).const_mul (g z)
  convert this using 1
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sg_eq a g (c t), mul_sum]
  exact sum_congr rfl fun z _ => by ring

/-- Support for blueprint C1–C5. -/
theorem D_D (a : ι) (g : (ι → Bool) → ℝ) : D a (D a g) = fun _ => 0 := by
  funext z
  simp [D]

/-- Support for blueprint C1–C5. -/
theorem abs_D_le {g : (ι → Bool) → ℝ} {B : ℝ} (hg : ∀ z, |g z| ≤ B) (a : ι) (z : ι → Bool) :
    |D a g z| ≤ B := by
  unfold D
  rw [abs_div, abs_of_pos (two_pos : (0 : ℝ) < 2), div_le_iff₀ two_pos]
  have := abs_sub (g (Function.update z a false)) (g (Function.update z a true))
  linarith [hg (Function.update z a false), hg (Function.update z a true)]

/-- The biased character. -/
noncomputable def xi (μ : ι → ℝ) (a : ι) (b : Bool) : ℝ := (sg b - μ a) / (1 - μ a ^ 2)

/-- Support for blueprint C1–C5. -/
theorem piB_mul_xi {μ : ι → ℝ} {a : ι} (h : |μ a| < 1) (b : Bool) :
    piB (μ a) b * xi μ a b = sg b / 2 := by
  have h2 : μ a ^ 2 < 1 := by
    exact (sq_lt_one_iff_abs_lt_one _).mpr h
  have : 1 - μ a ^ 2 ≠ 0 := by linarith
  unfold xi piB
  field_simp
  cases b <;> simp <;> ring

/-- C4. -/
theorem ext_D_eq_mul_xi (a : ι) (g : (ι → Bool) → ℝ) {μ : ι → ℝ} (h : |μ a| < 1) :
    ext (D a g) μ = ext (fun z => g z * xi μ a (z a)) μ := by
  rw [← sum_sg_eq]
  unfold ext
  refine sum_congr rfl fun z _ => ?_
  rw [bw_eq a, ← piB_mul_xi h]
  ring

/-- C5, conditioning on a coordinate. -/
theorem ext_split (a : ι) (g : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext g μ = ∑ b, piB (μ a) b * ext (fun z => g (Function.update z a b)) μ := by
  rw [Fintype.sum_bool]
  have key : ∀ b : Bool, ext (fun z => g (Function.update z a b)) μ =
      ∑ z, g (Function.update z a b) * (1 / 2 * bwOff a μ z) * 1 := by
    intro b
    unfold ext
    have := sum_inv_eq a (μ a) (fun z => g (Function.update z a b) * bwOff a μ z)
      fun z => by simp only [update_flip, bwOff_flip]
    simp only [mul_one]
    calc _ = (1 / 2) * ∑ z, g (Function.update z a b) * bwOff a μ z := by
          rw [← this]; exact sum_congr rfl fun z _ => by rw [bw_eq a]; ring
      _ = _ := by rw [mul_sum]; exact sum_congr rfl fun z _ => by ring
  rw [key, key]
  unfold ext
  have e := sum_mul_sg_eq a (fun z => g z * piB (μ a) (z a)) (bwOff a μ) (bwOff_flip a μ)
  calc ∑ z, g z * bw μ z = ∑ z, g z * piB (μ a) (z a) * bwOff a μ z :=
        sum_congr rfl fun z _ => by rw [bw_eq a]; ring
    _ = _ := by
        rw [e, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
        refine sum_congr rfl fun z _ => ?_
        have h1 : Function.update z a (z a) = z := Function.update_eq_self a z
        cases hz : z a
        · have h2 : Function.update z a false = z := by rw [← hz, h1]
          simp only [flip, hz, h2, Bool.not_false, Function.update_self]
          ring
        · have h2 : Function.update z a true = z := by rw [← hz, h1]
          simp only [flip, hz, h2, Bool.not_true, Function.update_self]
          ring

/-- A flip-invariant function does not see the mean at that coordinate. -/
theorem ext_eq_off (a : ι) (u : (ι → Bool) → ℝ) (hu : ∀ z, u (flip a z) = u z) (μ : ι → ℝ) :
    ext u μ = (1 / 2) * ∑ z, u z * bwOff a μ z := by
  unfold ext
  have := sum_inv_eq a (μ a) (fun z => u z * bwOff a μ z)
    fun z => by simp only [hu, bwOff_flip]
  rw [← this]
  exact sum_congr rfl fun z _ => by rw [bw_eq a]; ring

/-- Support for blueprint C1–C5. -/
theorem ext_congr_off (a : ι) (u : (ι → Bool) → ℝ) (hu : ∀ z, u (flip a z) = u z) {μ ν : ι → ℝ}
    (h : ∀ b, b ≠ a → μ b = ν b) : ext u μ = ext u ν := by
  rw [ext_eq_off a u hu, ext_eq_off a u hu]
  simp only [bwOff_congr a h]

/-- Affinity in one coordinate. -/
theorem ext_affine (a : ι) (g : (ι → Bool) → ℝ) (μ : ι → ℝ) :
    ext g μ = ext g (Function.update μ a 0) + μ a * ext (D a g) μ := by
  have hb : ∀ b : Bool, ∀ z, (fun z => g (Function.update z a b)) (flip a z) =
      (fun z => g (Function.update z a b)) z := fun b z => by simp only [update_flip]
  have e : ∀ b, ext (fun z => g (Function.update z a b)) (Function.update μ a 0) =
      ext (fun z => g (Function.update z a b)) μ := fun b =>
    ext_congr_off a _ (hb b) fun c hc => Function.update_of_ne hc _ _
  rw [ext_split a g μ, ext_split a g (Function.update μ a 0), Fintype.sum_bool, Fintype.sum_bool,
    e, e, Function.update_self]
  have hD : ext (D a g) μ = (ext (fun z => g (Function.update z a false)) μ -
      ext (fun z => g (Function.update z a true)) μ) / 2 := by
    unfold ext D
    rw [← sum_sub_distrib, sum_div]
    exact sum_congr rfl fun z _ => by dsimp only; ring
  rw [hD]
  simp only [piB, sg_true, sg_false]
  ring

/-- Support for blueprint C1–C5. -/
theorem D_flip_congr (a : ι) (g : (ι → Bool) → ℝ) : ∀ z, D a g (flip a z) = D a g z :=
  D_flip a g

end QuarticQuery.ForrelationLower

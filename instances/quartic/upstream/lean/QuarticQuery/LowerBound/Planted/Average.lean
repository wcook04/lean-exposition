module

public import QuarticQuery.Statement

/-!
# Finite weighted averages

The sample space of Proposition 4.2 is written as nested finite weighted sums,
so nothing here needs measure theory. `avg p g` is the `p`-weighted sum of `g`.
`avg_resample` is the one fact about independence that the proof uses: redrawing
one coordinate of a product weight does not change an average. It replaces every
conditional probability in the paper's wording.
-/

@[expose] public section

open Finset

namespace QuarticQuery

/-- The indicator of a proposition, as a real. -/
noncomputable def ind (P : Prop) : ℝ := open Classical in if P then 1 else 0

theorem ind_true {P : Prop} (h : P) : ind P = 1 := by
  simp [ind, h]

theorem ind_false {P : Prop} (h : ¬ P) : ind P = 0 := by
  simp [ind, h]

theorem ind_nonneg (P : Prop) : 0 ≤ ind P := by
  unfold ind
  split_ifs <;> norm_num

theorem ind_le_one (P : Prop) : ind P ≤ 1 := by
  unfold ind
  split_ifs <;> norm_num

section Avg

variable {α β : Type} [Fintype α] [Fintype β]

/-- The `p`-weighted sum of `g`. -/
noncomputable def avg (p g : α → ℝ) : ℝ := ∑ a, p a * g a

theorem avg_congr {p g g' : α → ℝ} (h : ∀ a, g a = g' a) : avg p g = avg p g' := by
  simp only [avg, h]

theorem avg_mono {p g g' : α → ℝ} (hp : ∀ a, 0 ≤ p a) (h : ∀ a, g a ≤ g' a) :
    avg p g ≤ avg p g' :=
  sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (h a) (hp a)

/-- Monotonicity that only looks at positive weight. -/
theorem avg_mono_of_ne {p g g' : α → ℝ} (hp : ∀ a, 0 ≤ p a) (h : ∀ a, p a ≠ 0 → g a ≤ g' a) :
    avg p g ≤ avg p g' := by
  refine sum_le_sum fun a _ => ?_
  by_cases h0 : p a = 0
  · simp [h0]
  · exact mul_le_mul_of_nonneg_left (h a h0) (hp a)

theorem avg_nonneg {p g : α → ℝ} (hp : ∀ a, 0 ≤ p a) (h : ∀ a, 0 ≤ g a) : 0 ≤ avg p g :=
  sum_nonneg fun a _ => mul_nonneg (hp a) (h a)

theorem avg_add (p g g' : α → ℝ) :
    avg p (fun a => g a + g' a) = avg p g + avg p g' := by
  simp only [avg, mul_add, sum_add_distrib]

theorem avg_sub (p g g' : α → ℝ) :
    avg p (fun a => g a - g' a) = avg p g - avg p g' := by
  simp only [avg, mul_sub, sum_sub_distrib]

theorem avg_mul_left (p g : α → ℝ) (c : ℝ) :
    avg p (fun a => c * g a) = c * avg p g := by
  simp only [avg, mul_sum]
  exact sum_congr rfl fun a _ => by ring

theorem avg_const {p : α → ℝ} (hp1 : ∑ a, p a = 1) (c : ℝ) : avg p (fun _ => c) = c := by
  simp only [avg, ← sum_mul, hp1, one_mul]

theorem avg_le_const {p g : α → ℝ} {c : ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (h : ∀ a, g a ≤ c) : avg p g ≤ c :=
  (avg_mono hp h).trans_eq (avg_const hp1 c)

theorem const_le_avg_of_ne {p g : α → ℝ} {c : ℝ} (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1)
    (h : ∀ a, p a ≠ 0 → c ≤ g a) : c ≤ avg p g :=
  (avg_const hp1 c).symm.le.trans (avg_mono_of_ne hp h)

/-- Averages over independent coordinates commute. -/
theorem avg_comm (p : α → ℝ) (q : β → ℝ) (g : α → β → ℝ) :
    avg p (fun a => avg q (g a)) = avg q (fun b => avg p (fun a => g a b)) := by
  simp only [avg, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun b _ => sum_congr rfl fun a _ => by ring

end Avg

/-! ## Product weights -/

section Prod

variable {ι β : Type} [Fintype ι]

/-- Independent coordinates, each drawn from `p`. -/
noncomputable def prodW (p : β → ℝ) (F : ι → β) : ℝ := ∏ c, p (F c)

theorem prodW_nonneg {p : β → ℝ} (hp : ∀ b, 0 ≤ p b) (F : ι → β) : 0 ≤ prodW p F :=
  prod_nonneg fun _ _ => hp _

theorem ne_zero_of_prodW_ne_zero {p : β → ℝ} {F : ι → β} (h : prodW p F ≠ 0) (c : ι) :
    p (F c) ≠ 0 :=
  fun h0 => h (prod_eq_zero (mem_univ c) h0)

variable [DecidableEq ι] [Fintype β]

theorem sum_prodW {p : β → ℝ} (hp : ∑ b, p b = 1) : ∑ F : ι → β, prodW p F = 1 := by
  have := prod_univ_sum (fun _ : ι => (univ : Finset β)) (fun _ b => p b)
  rw [Fintype.piFinset_univ] at this
  simp only [hp, prod_const_one] at this
  exact this.symm

omit [Fintype β] in
/-- Swapping the value at `i` with `b` leaves the product of the two weights fixed. -/
theorem prodW_update_mul (p : β → ℝ) (F : ι → β) (i : ι) (b : β) :
    prodW p (Function.update F i b) * p (F i) = prodW p F * p b := by
  unfold prodW
  rw [← mul_prod_erase univ (fun c => p (Function.update F i b c)) (mem_univ i),
    ← mul_prod_erase univ (fun c => p (F c)) (mem_univ i), Function.update_self]
  have : ∏ c ∈ univ.erase i, p (Function.update F i b c) = ∏ c ∈ univ.erase i, p (F c) :=
    prod_congr rfl fun c hc => by rw [Function.update_of_ne (ne_of_mem_erase hc)]
  rw [this]
  ring

/-- Ledger: def-dummy. Independence in one line: redrawing coordinate `i` from `p`
leaves every average under the product weight unchanged. -/
theorem avg_resample {p : β → ℝ} (hp : ∑ b, p b = 1) (i : ι) (g : (ι → β) → ℝ) :
    avg (prodW p) g = avg (prodW p) fun F => avg p fun b => g (Function.update F i b) := by
  let σ : (ι → β) × β → (ι → β) × β := fun a => (Function.update a.1 i a.2, a.1 i)
  have hσ : Function.Involutive σ := by
    rintro ⟨F, b⟩
    simp [σ]
  have hL : avg (prodW p) g = ∑ a : (ι → β) × β, prodW p a.1 * p a.2 * g a.1 := by
    rw [Fintype.sum_prod_type]
    refine sum_congr rfl fun F _ => ?_
    simp only
    rw [← sum_mul, ← mul_sum, hp, mul_one]
  have hR : (avg (prodW p) fun F => avg p fun b => g (Function.update F i b)) =
      ∑ a : (ι → β) × β, prodW p a.1 * (p a.2 * g (Function.update a.1 i a.2)) := by
    rw [Fintype.sum_prod_type]
    simp only [avg, mul_sum]
  rw [hL, hR, ← Equiv.sum_comp hσ.toPerm]
  refine sum_congr rfl fun a => ?_
  intro _
  simp only [Function.Involutive.coe_toPerm, σ]
  rw [prodW_update_mul]
  ring

end Prod

end QuarticQuery

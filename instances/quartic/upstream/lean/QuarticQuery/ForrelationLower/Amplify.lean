module

public import QuarticQuery.Model.Classical

/-!
# Majority amplification of a randomized program

Blueprint lemmas A1, A2. A family of trees running `τ` independent copies and answering by
majority; the error is bounded by exponential Markov with base `2`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

open Finset

namespace QuarticQuery.ForrelationLower

variable {ι : Type}

/-- Run the trees in order, then continue with the answers. -/
def runAll : List (QueryTree ι) → (List Bool → QueryTree ι) → QueryTree ι
  | [], k => k []
  | t :: ts, k => t.graft fun b => runAll ts fun bs => k (b :: bs)

/-- Support for blueprint A1–A2. -/
theorem eval_runAll (ts : List (QueryTree ι)) (k : List Bool → QueryTree ι) (x : BitInput ι) :
    (runAll ts k).eval x = (k (ts.map fun t => t.eval x)).eval x := by
  induction ts generalizing k with
  | nil => rfl
  | cons t ts ih =>
    simp only [runAll, List.map_cons]
    rw [QueryTree.eval_graft, ih]

/-- Support for blueprint A1–A2. -/
theorem depth_runAll_le (ts : List (QueryTree ι)) (bs : List Bool → Bool) {L : ℕ}
    (h : ∀ t ∈ ts, t.depth ≤ L) : (runAll ts fun r => .leaf (bs r)).depth ≤ ts.length * L := by
  induction ts generalizing bs with
  | nil => simp [runAll]
  | cons t ts ih =>
    simp only [runAll, List.length_cons]
    have h1 := QueryTree.depth_graft_le t fun b => runAll ts fun r => QueryTree.leaf (bs (b :: r))
    have h2 := ih (fun r => bs (false :: r)) fun u hu => h u (List.mem_cons_of_mem _ hu)
    have h3 := ih (fun r => bs (true :: r)) fun u hu => h u (List.mem_cons_of_mem _ hu)
    have h4 := h t List.mem_cons_self
    have h5 := max_le h2 h3
    have : (ts.length + 1) * L = ts.length * L + L := by ring
    omega

/-- Majority of a list. -/
def maj (r : List Bool) : Bool := decide (r.length < 2 * r.count true)

/-- If the majority is wrong, at least half the entries are wrong. -/
theorem maj_wrong {r : List Bool} {b : Bool} (h : maj r ≠ b) :
    r.length ≤ 2 * r.count (!b) := by
  have hc : r.count true + r.count false = r.length := by
    have := List.count_add_count_not (l := r) true
    simpa using this
  cases b
  · simp only [maj, ne_eq, decide_eq_false_iff_not, not_not, Bool.not_false] at h ⊢
    omega
  · simp only [maj, ne_eq, decide_eq_true_eq, Bool.not_true] at h ⊢
    omega

/-- Support for blueprint A1–A2. -/
theorem count_ofFn {n : ℕ} (g : Fin n → Bool) (c : Bool) :
    (List.ofFn g).count c = (univ.filter fun i => g i = c).card := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.count_cons, ih, Fin.card_filter_univ_succ]
    by_cases h : g 0 = c <;> simp [h]

variable {f : PartialBool ι}

/-- The amplified family. -/
theorem exists_amplified [Fintype ι] {L : ℕ} (h : RLe f L) (τ : ℕ) :
    ∃ (J : Type) (_ : Fintype J) (q : J → ℝ) (T : J → QueryTree ι),
      (∀ j, 0 ≤ q j) ∧ ∑ j, q j = 1 ∧ (∀ j, (T j).depth ≤ 2 * τ * L) ∧
      ∀ x b, f x = some b → ∑ j, q j * (if (T j).eval x = b then 0 else 1) ≤ (8 / 9 : ℝ) ^ τ := by
  obtain ⟨A, hA, hs⟩ := h
  let J := Fin (2 * τ) → Fin A.size
  let q : J → ℝ := fun j => ∏ i, A.weight (j i)
  let ts : J → List (QueryTree ι) := fun j => List.ofFn fun i => A.tree (j i)
  let T : J → QueryTree ι := fun j => runAll (ts j) fun r => .leaf (maj r)
  have hdepth : ∀ i, (A.tree i).depth ≤ L := fun i =>
    (Finset.le_sup (f := fun j => (A.tree j).depth) (mem_univ i)).trans hA
  refine ⟨J, inferInstance, q, T, fun j => prod_nonneg fun i _ => (A.weight_pos _).le, ?_, ?_, ?_⟩
  · have := Finset.prod_univ_sum (fun _ : Fin (2 * τ) => (univ : Finset (Fin A.size)))
      (fun _ a => A.weight a)
    simp only [Fintype.piFinset_univ, A.weight_sum, prod_const_one] at this
    exact this.symm
  · intro j
    have := depth_runAll_le (ts j) maj (L := L) (by
      intro t ht
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ht
      exact hdepth _)
    simpa [ts] using this
  · intro x b hb
    set wr : Fin A.size → ℝ := fun a => if (A.tree a).eval x = b then 1 else 2 with hwr
    have hwr1 : ∑ a, A.weight a * wr a ≤ 4 / 3 := by
      have h1 := hs x b hb
      have e : ∑ a, A.weight a * wr a = 2 - A.success x b := by
        have : ∑ a, A.weight a * wr a =
            2 * ∑ a, A.weight a - ∑ a, if (A.tree a).eval x = b then A.weight a else 0 := by
          rw [mul_sum, ← sum_sub_distrib]
          refine sum_congr rfl fun a _ => ?_
          simp only [hwr]
          split_ifs <;> ring
        rw [this, A.weight_sum]
        unfold RandomizedProgram.success
        ring
      linarith
    have hpt : ∀ j : J, (if (T j).eval x = b then (0 : ℝ) else 1) * 2 ^ τ ≤ ∏ i, wr (j i) := by
      intro j
      have hprod1 : ∀ i ∈ (univ : Finset (Fin (2 * τ))), (1 : ℝ) ≤ wr (j i) := fun i _ => by
        simp only [hwr]; split_ifs <;> norm_num
      by_cases he : (T j).eval x = b
      · simp only [he, if_true, zero_mul]
        exact prod_nonneg fun i _ => by linarith [hprod1 i (mem_univ i)]
      · simp only [he, if_false, one_mul]
        have hev : (T j).eval x = maj ((ts j).map fun t => t.eval x) := by
          simp only [T]; rw [eval_runAll]; rfl
        have hw := maj_wrong (b := b) (r := (ts j).map fun t => t.eval x) (hev ▸ he)
        have hcount : ((ts j).map fun t => t.eval x).count (!b) =
            (univ.filter fun i => (A.tree (j i)).eval x ≠ b).card := by
          have e1 : ((ts j).map fun t => t.eval x) =
              List.ofFn fun i => (A.tree (j i)).eval x := by
            simp only [ts, List.map_ofFn]
            rfl
          rw [e1, count_ofFn]
          congr 1
          refine filter_congr fun i _ => ?_
          cases (A.tree (j i)).eval x <;> cases b <;> simp
        have hlen : ((ts j).map fun t => t.eval x).length = 2 * τ := by simp [ts]
        have hc : τ ≤ (univ.filter fun i => (A.tree (j i)).eval x ≠ b).card := by omega
        have hp : ∏ i, wr (j i) = 2 ^ (univ.filter fun i => (A.tree (j i)).eval x ≠ b).card := by
          rw [← prod_filter_mul_prod_filter_not univ fun i => (A.tree (j i)).eval x ≠ b]
          have h1 : ∏ i ∈ univ.filter fun i => (A.tree (j i)).eval x ≠ b, wr (j i) =
              ∏ _i ∈ univ.filter fun i => (A.tree (j i)).eval x ≠ b, (2 : ℝ) :=
            prod_congr rfl fun i hi => by simp [hwr, (mem_filter.mp hi).2]
          have h2 : ∏ i ∈ univ.filter (fun i => ¬ (A.tree (j i)).eval x ≠ b), wr (j i) = 1 :=
            prod_eq_one fun i hi => by
              have := (mem_filter.mp hi).2
              simp only [ne_eq, not_not] at this
              simp [hwr, this]
          rw [h1, h2, prod_const, mul_one]
        rw [hp]
        exact pow_le_pow_right₀ (by norm_num) hc
    have hsum : ∑ j : J, q j * ∏ i, wr (j i) ≤ (4 / 3 : ℝ) ^ (2 * τ) := by
      have := Finset.prod_univ_sum (fun _ : Fin (2 * τ) => (univ : Finset (Fin A.size)))
        (fun _ a => A.weight a * wr a)
      simp only [Fintype.piFinset_univ, prod_const, card_univ, Fintype.card_fin] at this
      have e : ∑ j : J, q j * ∏ i, wr (j i) = (∑ a, A.weight a * wr a) ^ (2 * τ) := by
        rw [this]
        exact sum_congr rfl fun j _ => (prod_mul_distrib).symm
      rw [e]
      refine pow_le_pow_left₀ (sum_nonneg fun a _ => mul_nonneg (A.weight_pos a).le ?_) hwr1 _
      simp only [hwr]; split_ifs <;> norm_num
    have hq : ∀ j, 0 ≤ q j := fun j => prod_nonneg fun i _ => (A.weight_pos _).le
    have h2 : (∑ j, q j * (if (T j).eval x = b then (0 : ℝ) else 1)) * 2 ^ τ ≤
        (4 / 3 : ℝ) ^ (2 * τ) := by
      rw [sum_mul]
      refine le_trans (sum_le_sum fun j _ => ?_) hsum
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (hpt j) (hq j)
    have h3 : (8 / 9 : ℝ) ^ τ * 2 ^ τ = (4 / 3 : ℝ) ^ (2 * τ) := by
      rw [pow_mul, ← mul_pow]
      norm_num
    rw [← h3] at h2
    exact le_of_mul_le_mul_right h2 (by positivity)

end QuarticQuery.ForrelationLower

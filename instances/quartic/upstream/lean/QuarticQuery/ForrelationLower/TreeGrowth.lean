module

public import QuarticQuery.ForrelationLower.Cube

/-!
# Level-`k` growth of a decision tree at a biased point

Blueprint lemmas T1–T6. Azuma's inequality runs along the tree under the product measure
with means `μ`, with one union bound over a contracted index per level. The state of a
walk is the set of queried coordinates with their answers, so repeated queries need no
normal form.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Finset

namespace QuarticQuery.ForrelationLower

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- T1. The homogeneous chaos supported on `Q`. -/
noncomputable def chaos (ξ : ι → Bool → ℝ) (c : Finset ι → ℝ) (ℓ : ℕ) (Q : Finset ι)
    (z : ι → Bool) : ℝ :=
  ∑ J ∈ Q.powersetCard ℓ, c J * ∏ a ∈ J, ξ a (z a)

/-- Support for blueprint T1–T6. -/
theorem chaos_congr (ξ : ι → Bool → ℝ) (c : Finset ι → ℝ) (ℓ : ℕ) (Q : Finset ι)
    {z z' : ι → Bool} (h : ∀ a ∈ Q, z a = z' a) : chaos ξ c ℓ Q z = chaos ξ c ℓ Q z' :=
  sum_congr rfl fun J hJ => by
    congr 1
    exact prod_congr rfl fun a ha => by rw [h a ((mem_powersetCard.mp hJ).1 ha)]

/-- T1. Adding one queried coordinate. -/
theorem chaos_insert (ξ : ι → Bool → ℝ) (c : Finset ι → ℝ) (ℓ : ℕ) {Q : Finset ι} {q : ι}
    (hq : q ∉ Q) (z : ι → Bool) :
    chaos ξ c (ℓ + 1) (insert q Q) z =
      chaos ξ c (ℓ + 1) Q z + ξ q (z q) * chaos ξ (fun J => c (insert q J)) ℓ Q z := by
  unfold chaos
  rw [powersetCard_succ_insert hq, sum_union, sum_image, mul_sum]
  · congr 1
    refine sum_congr rfl fun J hJ => ?_
    have : q ∉ J := fun h => hq ((mem_powersetCard.mp hJ).1 h)
    rw [prod_insert this]
    ring
  · intro J hJ J' hJ' h
    have h1 : q ∉ J := fun h' => hq ((mem_powersetCard.mp hJ).1 h')
    have h2 : q ∉ J' := fun h' => hq ((mem_powersetCard.mp hJ').1 h')
    have := congrArg (fun s => erase s q) h
    simpa [erase_insert h1, erase_insert h2] using this
  · rw [disjoint_left]
    intro J hJ hJ'
    obtain ⟨J', hJ', rfl⟩ := mem_image.mp hJ'
    exact hq ((mem_powersetCard.mp hJ).1 (mem_insert_self q J'))

/-- Support for blueprint T1–T6. -/
@[simp] theorem chaos_zero (ξ : ι → Bool → ℝ) (c : Finset ι → ℝ) (Q : Finset ι) (z : ι → Bool) :
    chaos ξ c 0 Q z = c ∅ := by simp [chaos]

/-- Support for blueprint T1–T6. -/
@[simp] theorem chaos_succ_empty (ξ : ι → Bool → ℝ) (c : Finset ι → ℝ) (ℓ : ℕ) (z : ι → Bool) :
    chaos ξ c (ℓ + 1) ∅ z = 0 := by
  rw [chaos, powersetCard_eq_empty.mpr (by simp), sum_empty]

/-- Support for blueprint T1–T6. -/
theorem abs_chaos_le {ξ : ι → Bool → ℝ} {c : Finset ι → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hξ : ∀ a b, |ξ a b| ≤ B) (hc : ∀ J, |c J| ≤ 1) (ℓ : ℕ) (Q : Finset ι) (z : ι → Bool) :
    |chaos ξ c ℓ Q z| ≤ (Fintype.card ι * B) ^ ℓ := by
  have hcard : ((Q.powersetCard ℓ).card : ℝ) ≤ (Fintype.card ι : ℝ) ^ ℓ := by
    rw [card_powersetCard]
    have h1 : Q.card.choose ℓ ≤ Q.card ^ ℓ := Nat.choose_le_pow _ _
    have h2 : Q.card ^ ℓ ≤ Fintype.card ι ^ ℓ := Nat.pow_le_pow_left (card_le_univ Q) ℓ
    exact_mod_cast h1.trans h2
  have hterm : ∀ J ∈ Q.powersetCard ℓ, |c J * ∏ a ∈ J, ξ a (z a)| ≤ B ^ ℓ := by
    intro J hJ
    rw [abs_mul, abs_prod]
    calc |c J| * ∏ a ∈ J, |ξ a (z a)| ≤ 1 * B ^ ℓ := by
          refine mul_le_mul (hc J) ?_ (prod_nonneg fun _ _ => abs_nonneg _) zero_le_one
          calc ∏ a ∈ J, |ξ a (z a)| ≤ ∏ _a ∈ J, B :=
                Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun a _ => hξ a _
            _ = B ^ ℓ := by rw [prod_const, (mem_powersetCard.mp hJ).2]
      _ = B ^ ℓ := one_mul _
  calc |chaos ξ c ℓ Q z| ≤ ∑ J ∈ Q.powersetCard ℓ, |c J * ∏ a ∈ J, ξ a (z a)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ _J ∈ Q.powersetCard ℓ, B ^ ℓ := sum_le_sum hterm
    _ = (Q.powersetCard ℓ).card * B ^ ℓ := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (Fintype.card ι : ℝ) ^ ℓ * B ^ ℓ :=
        mul_le_mul_of_nonneg_right hcard (pow_nonneg hB _)
    _ = _ := (mul_pow _ _ _).symm

/-! ## Walks -/

/-- Support for blueprint T1–T6. -/
theorem eval_q (i : ι) (l r : QueryTree ι) (x : BitInput ι) :
    (QueryTree.query i l r).eval x = if x i then r.eval x else l.eval x := rfl

/-- The answers recorded on `Q`, then `z`. -/
def merge (Q : Finset ι) (x z : ι → Bool) : ι → Bool := fun a => if a ∈ Q then x a else z a

/-- Support for blueprint T1–T6. -/
theorem merge_update {Q : Finset ι} {q : ι} (hq : q ∉ Q) (x z : ι → Bool) (b : Bool) :
    merge Q x (Function.update z q b) = merge (insert q Q) (Function.update x q b) z := by
  funext a
  by_cases h : a = q
  · subst h; simp [merge, hq]
  · by_cases hQ : a ∈ Q <;> simp [merge, h, hQ, Function.update_of_ne h]

/-- Expectation along a tree of a terminal value. -/
noncomputable def walk (μ : ι → ℝ) (f : Finset ι → (ι → Bool) → Bool → ℝ) :
    QueryTree ι → Finset ι → (ι → Bool) → ℝ
  | .leaf b, Q, x => f Q x b
  | .query q l r, Q, x =>
    if q ∈ Q then (if x q then walk μ f r Q x else walk μ f l Q x)
    else piB (μ q) false * walk μ f l (insert q Q) (Function.update x q false) +
      piB (μ q) true * walk μ f r (insert q Q) (Function.update x q true)

/-- The walk computes a conditional expectation. -/
theorem walk_eq_ext (μ : ι → ℝ) (H : (ι → Bool) → Bool → ℝ) (T : QueryTree ι) (Q : Finset ι)
    (x : ι → Bool) :
    walk μ (fun Q x b => ext (fun z => H (merge Q x z) b) μ) T Q x =
      ext (fun z => H (merge Q x z) (T.eval (merge Q x z))) μ := by
  induction T generalizing Q x with
  | leaf b => rfl
  | query q l r ihl ihr =>
    by_cases hq : q ∈ Q
    · have e : ∀ z, merge Q x z q = x q := fun z => by simp [merge, hq]
      simp only [walk, hq, if_true]
      cases hx : x q
      · simp only [Bool.false_eq_true, if_false, ihl]
        unfold ext
        refine sum_congr rfl fun z _ => ?_
        simp [eval_q, e, hx]
      · simp only [if_true, ihr]
        unfold ext
        refine sum_congr rfl fun z _ => ?_
        simp [eval_q, e, hx]
    · rw [ext_split q, Fintype.sum_bool]
      simp only [walk, hq, if_false, ihl, ihr]
      rw [add_comm]
      congr 2
      · unfold ext
        refine sum_congr rfl fun z _ => ?_
        dsimp only
        rw [merge_update hq]
        have : merge (insert q Q) (Function.update x q true) z q = true := by simp [merge]
        simp [eval_q, this]
      · unfold ext
        refine sum_congr rfl fun z _ => ?_
        dsimp only
        rw [merge_update hq]
        have : merge (insert q Q) (Function.update x q false) z q = false := by simp [merge]
        simp [eval_q, this]

/-- A mean-zero product integrates to the part on `Q`. -/
theorem ext_prod_merge {μ : ι → ℝ} {ξ : ι → Bool → ℝ}
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (J Q : Finset ι) (x : ι → Bool) :
    ext (fun z => ∏ a ∈ J, ξ a (merge Q x z a)) μ =
      if J ⊆ Q then ∏ a ∈ J, ξ a (x a) else 0 := by
  classical
  have h1 : ∀ z : ι → Bool, (∏ a ∈ J, ξ a (merge Q x z a)) * bw μ z =
      ∏ a, ((if a ∈ J then ξ a (merge Q x z a) else 1) * piB (μ a) (z a)) := by
    intro z
    rw [prod_mul_distrib, prod_ite_mem, univ_inter]
    rfl
  have h2 := Finset.prod_univ_sum (fun _ : ι => (univ : Finset Bool))
    (fun a b => (if a ∈ J then ξ a (if a ∈ Q then x a else b) else 1) * piB (μ a) b)
  simp only [Fintype.piFinset_univ] at h2
  unfold ext
  rw [sum_congr rfl fun z _ => h1 z]
  simp only [merge]
  rw [← h2]
  have h3 : ∀ a, ∑ b, (if a ∈ J then ξ a (if a ∈ Q then x a else b) else 1) * piB (μ a) b =
      if a ∈ J then (if a ∈ Q then ξ a (x a) else 0) else 1 := by
    intro a
    rw [Fintype.sum_bool]
    by_cases hJ : a ∈ J
    · by_cases hQ : a ∈ Q
      · simp only [hJ, hQ, if_true]
        rw [← mul_add, add_comm (piB _ true), piB_add, mul_one]
      · simp only [hJ, hQ, if_true, if_false]
        linear_combination hm a
    · simp only [hJ, if_false, one_mul]
      rw [add_comm (piB _ true), piB_add]
  simp only [h3]
  by_cases hs : J ⊆ Q
  · rw [if_pos hs, prod_ite_mem, univ_inter]
    exact prod_congr rfl fun a ha => by simp [hs ha]
  · rw [if_neg hs]
    obtain ⟨a, ha, hQ⟩ := not_subset.mp hs
    exact prod_eq_zero (mem_univ a) (by simp [ha, hQ])

/-- Support for blueprint T1–T6. -/
theorem powersetCard_filter_subset (ℓ : ℕ) (Q : Finset ι) :
    (powersetCard ℓ (univ : Finset ι)).filter (· ⊆ Q) = powersetCard ℓ Q := by
  ext J
  simp only [mem_filter, mem_powersetCard]
  exact ⟨fun h => ⟨h.2, h.1.2⟩, fun h => ⟨⟨subset_univ _, h.2⟩, h.1⟩⟩

/-- The conditional expectation of the chaos on all coordinates. -/
theorem ext_chaos_merge {μ : ι → ℝ} {ξ : ι → Bool → ℝ}
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (c : Finset ι → ℝ) (ℓ : ℕ) (Q : Finset ι) (x : ι → Bool) :
    ext (fun z => chaos ξ c ℓ univ (merge Q x z)) μ = chaos ξ c ℓ Q x := by
  unfold chaos
  rw [ext_sum, ← powersetCard_filter_subset ℓ Q, sum_filter]
  refine sum_congr rfl fun J _ => ?_
  rw [ext_smul, ext_prod_merge hm]
  split_ifs <;> simp

/-- The terminal value of the walk is the chaos. -/
theorem walk_chaos {μ : ι → ℝ} {ξ : ι → Bool → ℝ}
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (v : Bool → ℝ) (c : Finset ι → ℝ) (ℓ : ℕ) (T : QueryTree ι) :
    ext (fun z => v (T.eval z) * chaos ξ c ℓ univ z) μ =
      walk μ (fun Q x b => v b * chaos ξ c ℓ Q x) T ∅ (fun _ => false) := by
  have h := walk_eq_ext μ (fun z b => v b * chaos ξ c ℓ univ z) T ∅ (fun _ => false)
  have e : ∀ z : ι → Bool, merge ∅ (fun _ => false) z = z := fun z => by
    funext a; simp [merge]
  simp only [e] at h
  rw [← h]
  congr 1
  funext Q x b
  rw [ext_smul, ext_chaos_merge hm]

/-! ## Hitting probabilities -/

open Classical in
/-- The probability that the walk meets a state in `B`. -/
noncomputable def hit (μ : ι → ℝ) (B : Finset ι → (ι → Bool) → Prop) :
    QueryTree ι → Finset ι → (ι → Bool) → ℝ
  | .leaf _, Q, x => if B Q x then 1 else 0
  | .query q l r, Q, x =>
    if B Q x then 1 else
    if q ∈ Q then (if x q then hit μ B r Q x else hit μ B l Q x)
    else piB (μ q) false * hit μ B l (insert q Q) (Function.update x q false) +
      piB (μ q) true * hit μ B r (insert q Q) (Function.update x q true)

variable {μ : ι → ℝ}

/-- Support for blueprint T1–T6. -/
theorem hit_of_mem {B : Finset ι → (ι → Bool) → Prop} (T : QueryTree ι) {Q : Finset ι}
    {x : ι → Bool} (h : B Q x) : hit μ B T Q x = 1 := by
  cases T <;> simp [hit, h]

/-- Support for blueprint T1–T6. -/
theorem hit_leaf_neg {B : Finset ι → (ι → Bool) → Prop} (b : Bool) {Q : Finset ι}
    {x : ι → Bool} (h : ¬ B Q x) : hit μ B (.leaf b) Q x = 0 := by
  simp [hit, h]

/-- Support for blueprint T1–T6. -/
theorem hit_query_neg {B : Finset ι → (ι → Bool) → Prop} (q : ι) (l r : QueryTree ι)
    {Q : Finset ι} {x : ι → Bool} (h : ¬ B Q x) : hit μ B (.query q l r) Q x =
      if q ∈ Q then (if x q then hit μ B r Q x else hit μ B l Q x)
      else piB (μ q) false * hit μ B l (insert q Q) (Function.update x q false) +
        piB (μ q) true * hit μ B r (insert q Q) (Function.update x q true) := by
  simp [hit, h]

/-- Support for blueprint T1–T6. -/
theorem hit_nonneg (hμ : ∀ a, |μ a| ≤ 1) (B : Finset ι → (ι → Bool) → Prop) (T : QueryTree ι)
    (Q : Finset ι) (x : ι → Bool) : 0 ≤ hit μ B T Q x := by
  induction T generalizing Q x with
  | leaf b => simp only [hit]; split_ifs <;> norm_num
  | query q l r ihl ihr =>
    simp only [hit]
    split_ifs
    · norm_num
    · exact ihr _ _
    · exact ihl _ _
    · exact add_nonneg (mul_nonneg (piB_nonneg (hμ q) _) (ihl _ _))
        (mul_nonneg (piB_nonneg (hμ q) _) (ihr _ _))

/-- Support for blueprint T1–T6. -/
theorem hit_empty (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool) :
    hit μ (fun _ _ => False) T Q x = 0 := by
  induction T generalizing Q x with
  | leaf b => simp [hit]
  | query q l r ihl ihr => simp [hit, ihl, ihr]

/-- Support for blueprint T1–T6. -/
theorem hit_le_one (hμ : ∀ a, |μ a| ≤ 1) (B : Finset ι → (ι → Bool) → Prop) (T : QueryTree ι)
    (Q : Finset ι) (x : ι → Bool) : hit μ B T Q x ≤ 1 := by
  induction T generalizing Q x with
  | leaf b => simp only [hit]; split_ifs <;> norm_num
  | query q l r ihl ihr =>
    simp only [hit]
    split_ifs
    · norm_num
    · exact ihr _ _
    · exact ihl _ _
    · have h0 := piB_nonneg (hμ q) false
      have h1 := piB_nonneg (hμ q) true
      have := piB_add (μ q)
      nlinarith [ihl (insert q Q) (Function.update x q false),
        ihr (insert q Q) (Function.update x q true)]

/-- Subadditivity. -/
theorem hit_or_le (hμ : ∀ a, |μ a| ≤ 1) (B C D : Finset ι → (ι → Bool) → Prop)
    (hD : ∀ Q x, D Q x → B Q x ∨ C Q x) (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool) :
    hit μ D T Q x ≤ hit μ B T Q x + hit μ C T Q x := by
  have hB0 := hit_nonneg hμ B T Q x
  have hC0 := hit_nonneg hμ C T Q x
  have hD1 := hit_le_one hμ D T Q x
  by_cases hB : B Q x
  · rw [hit_of_mem T hB]; linarith
  by_cases hC : C Q x
  · rw [hit_of_mem T hC]; linarith
  have hd : ¬ D Q x := fun h => (hD Q x h).elim hB hC
  induction T generalizing Q x with
  | leaf b => simp [hit, hB, hC, hd]
  | query q l r ihl ihr =>
    have key : ∀ (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool),
        hit μ D T Q x ≤ hit μ B T Q x + hit μ C T Q x := by
      intro T Q x
      induction T generalizing Q x with
      | leaf b =>
        simp only [hit]
        by_cases h : D Q x
        · rcases hD Q x h with h' | h' <;> simp only [h, h', if_true] <;>
            split_ifs <;> norm_num
        · simp only [h, if_false]
          split_ifs <;> norm_num
      | query q l r ihl ihr =>
        by_cases hB : B Q x
        · rw [hit_of_mem _ hB]
          linarith [hit_nonneg hμ C (QueryTree.query q l r) Q x,
            hit_le_one hμ D (QueryTree.query q l r) Q x]
        by_cases hC : C Q x
        · rw [hit_of_mem _ hC]
          linarith [hit_nonneg hμ B (QueryTree.query q l r) Q x,
            hit_le_one hμ D (QueryTree.query q l r) Q x]
        have hd : ¬ D Q x := fun h => (hD Q x h).elim hB hC
        simp only [hit, hB, hC, hd, if_false]
        split_ifs
        · exact ihr _ _
        · exact ihl _ _
        · have h0 := piB_nonneg (hμ q) false
          have h1 := piB_nonneg (hμ q) true
          have a1 := mul_le_mul_of_nonneg_left (ihl (insert q Q) (Function.update x q false)) h0
          have a2 := mul_le_mul_of_nonneg_left (ihr (insert q Q) (Function.update x q true)) h1
          linarith
    exact key _ Q x

/-- Support for blueprint T1–T6. -/
theorem hit_mono (hμ : ∀ a, |μ a| ≤ 1) {B D : Finset ι → (ι → Bool) → Prop}
    (hD : ∀ Q x, D Q x → B Q x) (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool) :
    hit μ D T Q x ≤ hit μ B T Q x := by
  have := hit_or_le hμ B (fun _ _ => False) D (fun Q x h => Or.inl (hD Q x h)) T Q x
  rwa [hit_empty, add_zero] at this

/-- Union bound over a finite family. -/
theorem hit_exists_le (hμ : ∀ a, |μ a| ≤ 1) {κ : Type} [DecidableEq κ] (s : Finset κ)
    (B : κ → Finset ι → (ι → Bool) → Prop) (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool) :
    hit μ (fun Q x => ∃ q ∈ s, B q Q x) T Q x ≤ ∑ q ∈ s, hit μ (B q) T Q x := by
  induction s using Finset.induction_on with
  | empty =>
    have := hit_mono (μ := μ) hμ (B := fun _ _ => False)
      (D := fun Q x => ∃ q ∈ (∅ : Finset κ), B q Q x) (by simp) T Q x
    rwa [hit_empty] at this
  | insert q0 s hq ih =>
    rw [sum_insert hq]
    have := hit_or_le hμ (B q0) (fun Q x => ∃ q ∈ s, B q Q x)
      (fun Q x => ∃ q ∈ insert q0 s, B q Q x) (by
        rintro Q x ⟨q, hq', h⟩
        rcases mem_insert.mp hq' with rfl | h'
        · exact Or.inl h
        · exact Or.inr ⟨q, h', h⟩) T Q x
    linarith

/-! ## One level of Azuma -/

/-- T3. Hoeffding's lemma for a mean-zero two-point variable. -/
theorem two_point_exp_le {p0 p1 a0 a1 B t : ℝ} (hp0 : 0 ≤ p0) (hp1 : 0 ≤ p1) (hp : p0 + p1 = 1)
    (hm : p0 * a0 + p1 * a1 = 0) (hB : 0 < B) (h0 : |a0| ≤ B) (h1 : |a1| ≤ B) :
    p0 * Real.exp (t * a0) + p1 * Real.exp (t * a1) ≤ Real.exp (t ^ 2 * B ^ 2 / 2) := by
  have key : ∀ a : ℝ, |a| ≤ B → Real.exp (t * a) ≤
      (B - a) / (2 * B) * Real.exp (-(t * B)) + (B + a) / (2 * B) * Real.exp (t * B) := by
    intro a ha
    obtain ⟨h1, h2⟩ := abs_le.mp ha
    have hw1 : 0 ≤ (B - a) / (2 * B) := div_nonneg (by linarith) (by linarith)
    have hw2 : 0 ≤ (B + a) / (2 * B) := div_nonneg (by linarith) (by linarith)
    have hs : (B - a) / (2 * B) + (B + a) / (2 * B) = 1 := by field_simp; ring
    have := convexOn_exp.2 (Set.mem_univ (-(t * B))) (Set.mem_univ (t * B)) hw1 hw2 hs
    simp only [smul_eq_mul] at this
    have e : (B - a) / (2 * B) * -(t * B) + (B + a) / (2 * B) * (t * B) = t * a := by
      field_simp; ring
    rwa [e] at this
  have h := add_le_add (mul_le_mul_of_nonneg_left (key a0 h0) hp0)
    (mul_le_mul_of_nonneg_left (key a1 h1) hp1)
  have e : p0 * ((B - a0) / (2 * B) * Real.exp (-(t * B)) + (B + a0) / (2 * B) * Real.exp (t * B)) +
      p1 * ((B - a1) / (2 * B) * Real.exp (-(t * B)) + (B + a1) / (2 * B) * Real.exp (t * B)) =
      Real.cosh (t * B) := by
    rw [Real.cosh_eq]
    have e2 : p0 * ((B - a0) / (2 * B) * Real.exp (-(t * B)) +
        (B + a0) / (2 * B) * Real.exp (t * B)) +
        p1 * ((B - a1) / (2 * B) * Real.exp (-(t * B)) + (B + a1) / (2 * B) * Real.exp (t * B)) =
        ((p0 + p1) * B * (Real.exp (-(t * B)) + Real.exp (t * B)) +
          (p0 * a0 + p1 * a1) * (Real.exp (t * B) - Real.exp (-(t * B)))) / (2 * B) := by ring
    rw [e2, hp, hm]
    field_simp
    ring
  rw [e] at h
  refine h.trans ?_
  have := Real.cosh_le_exp_half_sq (t * B)
  rwa [mul_pow] at this

variable {B₀ : ℝ} {ξ : ι → Bool → ℝ}

/-- T4. One level of Azuma along a tree. `Y` is the running value and `Y' q` its increment
coefficient at `q`; `Bad` is the event that some coefficient exceeds `β`. -/
theorem hit_azuma (hμ : ∀ a, |μ a| ≤ 1)
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (hB₀ : 0 < B₀) (hξ : ∀ a b, |ξ a b| ≤ B₀)
    (Y : Finset ι → (ι → Bool) → ℝ) (Y' : ι → Finset ι → (ι → Bool) → ℝ)
    (hY : ∀ q Q x b, q ∉ Q →
      Y (insert q Q) (Function.update x q b) = Y Q x + ξ q b * Y' q Q x)
    {R β lam : ℝ} (hlam : 0 ≤ lam) (hβ : 0 ≤ β) (T : QueryTree ι) (d : ℕ) (hT : T.depth ≤ d)
    (Q : Finset ι) (x : ι → Bool) :
    hit μ (fun Q x => R < Y Q x ∨ ∃ q, β < |Y' q Q x|) T Q x ≤
      Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2) +
        hit μ (fun Q x => ∃ q, β < |Y' q Q x|) T Q x := by
  set Bad : Finset ι → (ι → Bool) → Prop := fun Q x => ∃ q, β < |Y' q Q x| with hBad
  have easy : ∀ (T : QueryTree ι) (d : ℕ) (Q : Finset ι) (x : ι → Bool),
      (R < Y Q x ∨ Bad Q x) →
      hit μ (fun Q x => R < Y Q x ∨ Bad Q x) T Q x ≤
        Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2) +
          hit μ Bad T Q x := by
    intro T d Q x h
    have h1 := hit_le_one hμ (fun Q x => R < Y Q x ∨ Bad Q x) T Q x
    have h2 := hit_nonneg hμ Bad T Q x
    by_cases hb : Bad Q x
    · rw [hit_of_mem T (B := Bad) hb]
      linarith [Real.exp_pos (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2)]
    · have hbig : R < Y Q x := h.resolve_right hb
      have h3 : 1 ≤ Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2) := by
        apply Real.one_le_exp
        have : 0 ≤ lam * (Y Q x - R) := mul_nonneg hlam (by linarith)
        positivity
      linarith
  induction T generalizing d Q x with
  | leaf b =>
    by_cases hn : R < Y Q x ∨ Bad Q x
    · exact easy _ d Q x hn
    · have : ¬ Bad Q x := fun h => hn (Or.inr h)
      rw [hit_leaf_neg (B := fun Q x => R < Y Q x ∨ Bad Q x) _ hn, hit_leaf_neg (B := Bad) _ this]
      linarith [Real.exp_pos (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2)]
  | query q l r ihl ihr =>
    by_cases hn : R < Y Q x ∨ Bad Q x
    · exact easy _ d Q x hn
    obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by simp [QueryTree.depth] at hT; omega⟩
    have hl : l.depth ≤ d' := by simp [QueryTree.depth] at hT; omega
    have hr : r.depth ≤ d' := by simp [QueryTree.depth] at hT; omega
    have hb : ¬ Bad Q x := fun h => hn (Or.inr h)
    have hc : 0 ≤ lam ^ 2 * β ^ 2 * B₀ ^ 2 / 2 := by positivity
    have emono : Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d' / 2) ≤
        Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * (d' + 1 : ℕ) / 2) := by
      apply Real.exp_le_exp.mpr
      push_cast
      nlinarith
    by_cases hq : q ∈ Q
    · rw [hit_query_neg (B := fun Q x => R < Y Q x ∨ Bad Q x) _ _ _ hn,
        hit_query_neg (B := Bad) _ _ _ hb, if_pos hq, if_pos hq]
      cases hx : x q
      · simp only [Bool.false_eq_true, if_false]
        linarith [ihl d' hl Q x]
      · simp only [if_true]
        linarith [ihr d' hr Q x]
    · rw [hit_query_neg (B := fun Q x => R < Y Q x ∨ Bad Q x) _ _ _ hn,
        hit_query_neg (B := Bad) _ _ _ hb, if_neg hq, if_neg hq]
      have il := ihl d' hl (insert q Q) (Function.update x q false)
      have ir := ihr d' hr (insert q Q) (Function.update x q true)
      have h0 := piB_nonneg (hμ q) false
      have h1 := piB_nonneg (hμ q) true
      set y := Y' q Q x with hy
      have hyβ : |y| ≤ β := not_lt.mp fun h => hb ⟨q, h⟩
      set E := Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d' / 2) with hE
      have e0 : Real.exp (lam * (Y (insert q Q) (Function.update x q false) - R) +
          lam ^ 2 * β ^ 2 * B₀ ^ 2 * d' / 2) = E * Real.exp (lam * y * ξ q false) := by
        rw [hY q Q x false hq, hE, ← Real.exp_add]
        congr 1
        rw [← hy]; ring
      have e1 : Real.exp (lam * (Y (insert q Q) (Function.update x q true) - R) +
          lam ^ 2 * β ^ 2 * B₀ ^ 2 * d' / 2) = E * Real.exp (lam * y * ξ q true) := by
        rw [hY q Q x true hq, hE, ← Real.exp_add]
        congr 1
        rw [← hy]; ring
      rw [e0] at il
      rw [e1] at ir
      have tp := two_point_exp_le (t := lam * y) h0 h1 (piB_add (μ q)) (hm q) hB₀ (hξ q false)
        (hξ q true)
      have tp2 : Real.exp ((lam * y) ^ 2 * B₀ ^ 2 / 2) ≤
          Real.exp (lam ^ 2 * β ^ 2 * B₀ ^ 2 / 2) := by
        apply Real.exp_le_exp.mpr
        have : y ^ 2 ≤ β ^ 2 := sq_le_sq' (by linarith [(abs_le.mp hyβ).1]) (abs_le.mp hyβ).2
        have : lam ^ 2 * y ^ 2 * B₀ ^ 2 ≤ lam ^ 2 * β ^ 2 * B₀ ^ 2 := by gcongr
        nlinarith
      have e2 : Real.exp (lam * (Y Q x - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * (d' + 1 : ℕ) / 2) =
          E * Real.exp (lam ^ 2 * β ^ 2 * B₀ ^ 2 / 2) := by
        rw [hE, ← Real.exp_add]
        congr 1
        push_cast
        ring
      have hE0 : 0 ≤ E := (Real.exp_pos _).le
      have a1 := mul_le_mul_of_nonneg_left il h0
      have a2 := mul_le_mul_of_nonneg_left ir h1
      have a3 := mul_le_mul_of_nonneg_left (tp.trans tp2) hE0
      rw [e2]
      nlinarith

/-- T5. Tail of the running chaos along a tree. -/
theorem hit_chaos_le (hμ : ∀ a, |μ a| ≤ 1)
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (hB₀ : 0 < B₀) (hξ : ∀ a b, |ξ a b| ≤ B₀) {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * d * B₀ ^ 2 * Λ) (hn : 1 ≤ Fintype.card ι) (T : QueryTree ι)
    (hT : T.depth ≤ d) (ℓ : ℕ) (c : Finset ι → ℝ) (hc : ∀ J, |c J| ≤ 1) (x : ι → Bool) :
    hit μ (fun Q x => K ^ ℓ < |chaos ξ c ℓ Q x|) T ∅ x ≤
      (4 * Fintype.card ι : ℝ) ^ ℓ * Real.exp (-Λ) := by
  have hn' : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hn
  induction ℓ generalizing c x with
  | zero =>
    have := hit_mono (μ := μ) hμ (B := fun _ _ => False)
      (D := fun Q x => K ^ 0 < |chaos ξ c 0 Q x|)
      (fun Q x h => by
        simp only [pow_zero, chaos_zero] at h
        exact absurd (hc ∅) (not_le.mpr h)) T ∅ x
    rw [hit_empty] at this
    refine this.trans ?_
    simp [(Real.exp_pos _).le]
  | succ ℓ ih =>
    set n : ℝ := (Fintype.card ι : ℝ) with hnn
    set β := K ^ ℓ with hβ
    have hβ0 : 0 < β := pow_pos hK _
    set R := K ^ (ℓ + 1) with hR
    have hRβ : R = β * K := pow_succ K ℓ
    have hd' : (0 : ℝ) < d := by exact_mod_cast hd
    set lam := K / (β * B₀ ^ 2 * d) with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hexp : lam * (0 - R) + lam ^ 2 * β ^ 2 * B₀ ^ 2 * d / 2 = -Λ := by
      have : lam * R = K ^ 2 / (B₀ ^ 2 * d) := by
        rw [hlam, hRβ]; field_simp
      have h2 : lam ^ 2 * β ^ 2 * B₀ ^ 2 * d = K ^ 2 / (B₀ ^ 2 * d) := by
        rw [hlam]; field_simp
      have h3 : K ^ 2 / (B₀ ^ 2 * d) = 2 * Λ := by
        rw [hKsq]; field_simp
      nlinarith
    let Y₁ : Finset ι → (ι → Bool) → ℝ := fun Q x => chaos ξ c (ℓ + 1) Q x
    let Y₂ : Finset ι → (ι → Bool) → ℝ := fun Q x => - chaos ξ c (ℓ + 1) Q x
    let C₁ : ι → Finset ι → (ι → Bool) → ℝ := fun q Q x => chaos ξ (fun J => c (insert q J)) ℓ Q x
    let C₂ : ι → Finset ι → (ι → Bool) → ℝ := fun q Q x =>
      - chaos ξ (fun J => c (insert q J)) ℓ Q x
    have step : ∀ q Q (x : ι → Bool) b, q ∉ Q → chaos ξ c (ℓ + 1) (insert q Q)
        (Function.update x q b) =
        chaos ξ c (ℓ + 1) Q x + ξ q b * chaos ξ (fun J => c (insert q J)) ℓ Q x := by
      intro q Q x b hq
      rw [chaos_insert ξ c ℓ hq]
      have u1 := chaos_congr ξ c (ℓ + 1) Q (z := Function.update x q b) (z' := x)
        (fun a ha => by rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hq)])
      have u2 := chaos_congr ξ (fun J => c (insert q J)) ℓ Q (z := Function.update x q b)
        (z' := x) (fun a ha => by rw [Function.update_of_ne (ne_of_mem_of_not_mem ha hq)])
      rw [u1, u2, Function.update_self]
    have A₁ := hit_azuma hμ hm hB₀ hξ Y₁ C₁ (fun q Q x b hq => step q Q x b hq)
      (R := R) (β := β) hlam0 hβ0.le T d hT ∅ x
    have A₂ := hit_azuma hμ hm hB₀ hξ Y₂ C₂
      (fun q Q x b hq => by simp only [Y₂, C₂, step q Q x b hq]; ring)
      (R := R) (β := β) hlam0 hβ0.le T d hT ∅ x
    have z₁ : Y₁ ∅ x = 0 := chaos_succ_empty ξ c ℓ x
    have z₂ : Y₂ ∅ x = 0 := by simp [Y₂]
    rw [z₁, hexp] at A₁
    rw [z₂, hexp] at A₂
    have B₁ : hit μ (fun Q x => ∃ q, β < |C₁ q Q x|) T ∅ x ≤
        n * ((4 * n) ^ ℓ * Real.exp (-Λ)) := by
      have h := hit_exists_le (μ := μ) hμ (univ : Finset ι)
        (fun q Q x => β < |chaos ξ (fun J => c (insert q J)) ℓ Q x|) T ∅ x
      have h' : ∑ q : ι, hit μ (fun Q x => β < |chaos ξ (fun J => c (insert q J)) ℓ Q x|) T ∅ x ≤
          ∑ _q : ι, (4 * n) ^ ℓ * Real.exp (-Λ) :=
        sum_le_sum fun q _ => ih _ (fun J => hc _) x
      rw [sum_const, card_univ, nsmul_eq_mul] at h'
      simpa [C₁] using h.trans h'
    have B₂ : hit μ (fun Q x => ∃ q, β < |C₂ q Q x|) T ∅ x ≤
        n * ((4 * n) ^ ℓ * Real.exp (-Λ)) := by
      simpa [C₁, C₂, abs_neg] using B₁
    have cover := hit_or_le hμ (fun Q x => R < Y₁ Q x ∨ ∃ q, β < |C₁ q Q x|)
      (fun Q x => R < Y₂ Q x ∨ ∃ q, β < |C₂ q Q x|)
      (fun Q x => R < |chaos ξ c (ℓ + 1) Q x|)
      (fun Q x h => by
        rcases lt_abs.mp h with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr (Or.inl h)) T ∅ x
    have hp : (0 : ℝ) ≤ (4 * n) ^ ℓ * Real.exp (-Λ) := by positivity
    have hpow : (1 : ℝ) ≤ (4 * n) ^ ℓ := one_le_pow₀ (by linarith)
    have hE : 0 < Real.exp (-Λ) := Real.exp_pos _
    refine cover.trans ?_
    rw [pow_succ]
    have : 2 * Real.exp (-Λ) ≤ 2 * n * ((4 * n) ^ ℓ * Real.exp (-Λ)) := by nlinarith
    nlinarith

/-- A walk is bounded by its terminal bound. -/
theorem abs_walk_le (hμ : ∀ a, |μ a| ≤ 1) {f : Finset ι → (ι → Bool) → Bool → ℝ} {M : ℝ}
    (hf : ∀ Q x b, |f Q x b| ≤ M) (T : QueryTree ι) (Q : Finset ι) (x : ι → Bool) :
    |walk μ f T Q x| ≤ M := by
  induction T generalizing Q x with
  | leaf b => exact hf _ _ _
  | query q l r ihl ihr =>
    simp only [walk]
    split_ifs
    · exact ihr _ _
    · exact ihl _ _
    · have h0 := piB_nonneg (hμ q) false
      have h1 := piB_nonneg (hμ q) true
      have a := ihl (insert q Q) (Function.update x q false)
      have b := ihr (insert q Q) (Function.update x q true)
      calc _ ≤ |piB (μ q) false * walk μ f l (insert q Q) (Function.update x q false)| +
              |piB (μ q) true * walk μ f r (insert q Q) (Function.update x q true)| :=
            abs_add_le _ _
        _ ≤ piB (μ q) false * M + piB (μ q) true * M := by
            rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
            gcongr
        _ = M := by rw [← add_mul, piB_add, one_mul]

/-- A walk is bounded by a level plus the hitting probability of its failure. -/
theorem abs_walk_le_hit (hμ : ∀ a, |μ a| ≤ 1) {f : Finset ι → (ι → Bool) → Bool → ℝ} {M R : ℝ}
    (hR : 0 ≤ R) (hf : ∀ Q x b, |f Q x b| ≤ M) {B : Finset ι → (ι → Bool) → Prop}
    (hB : ∀ Q x b, ¬ B Q x → |f Q x b| ≤ R) (hM : 0 ≤ M) (T : QueryTree ι) (Q : Finset ι)
    (x : ι → Bool) : |walk μ f T Q x| ≤ R + M * hit μ B T Q x := by
  induction T generalizing Q x with
  | leaf b =>
    by_cases h : B Q x
    · simp only [hit, h, if_true, walk, mul_one]
      linarith [hf Q x b]
    · simpa [hit, h, walk] using hB Q x b h
  | query q l r ihl ihr =>
    by_cases h : B Q x
    · rw [hit_of_mem _ h, mul_one]
      linarith [abs_walk_le hμ hf (QueryTree.query q l r) Q x]
    simp only [walk, hit, h, if_false]
    split_ifs
    · exact ihr _ _
    · exact ihl _ _
    · have h0 := piB_nonneg (hμ q) false
      have h1 := piB_nonneg (hμ q) true
      have a := ihl (insert q Q) (Function.update x q false)
      have b := ihr (insert q Q) (Function.update x q true)
      calc _ ≤ |piB (μ q) false * walk μ f l (insert q Q) (Function.update x q false)| +
              |piB (μ q) true * walk μ f r (insert q Q) (Function.update x q true)| :=
            abs_add_le _ _
        _ ≤ piB (μ q) false * (R + M * hit μ B l (insert q Q) (Function.update x q false)) +
            piB (μ q) true * (R + M * hit μ B r (insert q Q) (Function.update x q true)) := by
            rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h1]
            gcongr
        _ = _ := by
            have := piB_add (μ q)
            linear_combination R * this

/-- T6. Growth of a tree against a chaos of bounded coefficients. -/
theorem abs_ext_tree_chaos_le (hμ : ∀ a, |μ a| ≤ 1)
    (hm : ∀ a, piB (μ a) false * ξ a false + piB (μ a) true * ξ a true = 0)
    (hB₀ : 0 < B₀) (hξ : ∀ a b, |ξ a b| ≤ B₀) {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K)
    (hKsq : K ^ 2 = 2 * d * B₀ ^ 2 * Λ) (hn : 1 ≤ Fintype.card ι) (T : QueryTree ι)
    (hT : T.depth ≤ d) (k : ℕ) (c : Finset ι → ℝ) (hc : ∀ J, |c J| ≤ 1)
    (v : Bool → ℝ) (hv : ∀ b, |v b| ≤ 1) :
    |ext (fun z => v (T.eval z) * chaos ξ c k univ z) μ| ≤
      K ^ k + (Fintype.card ι * B₀) ^ k * ((4 * Fintype.card ι : ℝ) ^ k * Real.exp (-Λ)) := by
  rw [walk_chaos hm]
  have hM : ∀ Q x b, |v b * chaos ξ c k Q x| ≤ (Fintype.card ι * B₀) ^ k := fun Q x b => by
    rw [abs_mul]
    calc _ ≤ 1 * (Fintype.card ι * B₀) ^ k :=
          mul_le_mul (hv b) (abs_chaos_le hB₀.le hξ hc k Q x) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _
  have hR : ∀ Q x b, ¬ (K ^ k < |chaos ξ c k Q x|) → |v b * chaos ξ c k Q x| ≤ K ^ k :=
    fun Q x b h => by
      rw [abs_mul]
      calc _ ≤ 1 * K ^ k := mul_le_mul (hv b) (not_lt.mp h) (abs_nonneg _) zero_le_one
        _ = _ := one_mul _
  have h := abs_walk_le_hit hμ (pow_pos hK k).le hM hR (by positivity) T ∅ (fun _ => false)
  refine h.trans ?_
  gcongr
  exact hit_chaos_le hμ hm hB₀ hξ hd hK hKsq hn T hT k c hc _

/-! ## Iterated derivatives -/

/-- Iterated discrete derivative along a list. -/
noncomputable def Dl : List ι → ((ι → Bool) → ℝ) → (ι → Bool) → ℝ
  | [], g => g
  | a :: L, g => Dl L (D a g)

/-- C4 for lists. -/
theorem ext_Dl (L : List ι) (hL : L.Nodup) (g : (ι → Bool) → ℝ) (μ : ι → ℝ)
    (hμ : ∀ a, |μ a| < 1) :
    ext (Dl L g) μ = ext (fun z => g z * (L.map fun a => xi μ a (z a)).prod) μ := by
  induction L generalizing g with
  | nil => simp [Dl]
  | cons a L ih =>
    obtain ⟨ha, hnd⟩ := List.nodup_cons.mp hL
    simp only [Dl]
    rw [ih hnd]
    have hinv : ∀ (z : ι → Bool) (b : Bool),
        (L.map fun c => xi μ c (Function.update z a b c)).prod =
          (L.map fun c => xi μ c (z c)).prod := by
      intro z b
      congr 1
      refine List.map_congr_left fun c hc => ?_
      rw [Function.update_of_ne (fun h => ha (by rw [← h]; exact hc))]
    have e : (fun z => D a g z * (L.map fun c => xi μ c (z c)).prod) =
        D a (fun z => g z * (L.map fun c => xi μ c (z c)).prod) := by
      funext z
      simp only [D, hinv]
      ring
    rw [e, ext_D_eq_mul_xi a _ (hμ a)]
    unfold ext
    refine sum_congr rfl fun z _ => ?_
    simp only [List.map_cons, List.prod_cons]
    ring

/-- Support for blueprint T1–T6. -/
theorem abs_xi_le {μ : ι → ℝ} (hμ : ∀ a, |μ a| ≤ 1 / 2) (a : ι) (b : Bool) : |xi μ a b| ≤ 2 := by
  obtain ⟨h1, h2⟩ := abs_le.mp (hμ a)
  have h3 : (3 : ℝ) / 4 ≤ 1 - μ a ^ 2 := by nlinarith
  unfold xi
  rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < 1 - μ a ^ 2), div_le_iff₀ (by linarith)]
  have h4 : |sg b - μ a| ≤ 3 / 2 := by
    rw [abs_le]
    cases b <;> simp <;> constructor <;> linarith
  linarith

/-- Support for blueprint T1–T6. -/
theorem xi_mean {μ : ι → ℝ} (hμ : ∀ a, |μ a| ≤ 1 / 2) (a : ι) :
    piB (μ a) false * xi μ a false + piB (μ a) true * xi μ a true = 0 := by
  have h : |μ a| < 1 := by linarith [hμ a]
  rw [piB_mul_xi h, piB_mul_xi h]
  simp only [sg_false, sg_true]
  norm_num

/-- The growth bound over any family of duplicate-free index lists of length `k` that are
determined by their sets. -/
theorem sum_abs_ext_Dl_le {P : Type} [Fintype P] [DecidableEq P] (Lp : P → List ι)
    (hnd : ∀ p, (Lp p).Nodup) {k : ℕ} (hlen : ∀ p, (Lp p).length = k)
    (hinj : Function.Injective fun p => (Lp p).toFinset) {μ : ι → ℝ} (hμ : ∀ a, |μ a| ≤ 1 / 2)
    {Λ K : ℝ} {d : ℕ} (hd : 0 < d) (hK : 0 < K) (hKsq : K ^ 2 = 2 * d * 2 ^ 2 * Λ)
    (hn : 1 ≤ Fintype.card ι) (T : QueryTree ι) (hT : T.depth ≤ d) (v : Bool → ℝ)
    (hv : ∀ b, |v b| ≤ 1) :
    ∑ p, |ext (Dl (Lp p) fun z => v (T.eval z)) μ| ≤
      K ^ k + (Fintype.card ι * 2) ^ k * ((4 * Fintype.card ι : ℝ) ^ k * Real.exp (-Λ)) := by
  classical
  set g : (ι → Bool) → ℝ := fun z => v (T.eval z) with hg
  have hμ1 : ∀ a, |μ a| ≤ 1 := fun a => (hμ a).trans (by norm_num)
  have hμ2 : ∀ a, |μ a| < 1 := fun a => (hμ a).trans_lt (by norm_num)
  set x : P → ℝ := fun p => ext (Dl (Lp p) g) μ with hx
  set σ : P → ℝ := fun p => if 0 ≤ x p then 1 else -1 with hσ
  have hσa : ∀ p, |σ p| = 1 := fun p => by simp only [hσ]; split_ifs <;> simp
  have hσx : ∀ p, |x p| = σ p * x p := fun p => by
    simp only [hσ]
    split_ifs with h
    · rw [abs_of_nonneg h, one_mul]
    · rw [abs_of_neg (not_le.mp h)]; ring
  set c : Finset ι → ℝ := fun J => ∑ p, if (Lp p).toFinset = J then σ p else 0 with hc
  have hcb : ∀ J, |c J| ≤ 1 := by
    intro J
    by_cases h : ∃ p, (Lp p).toFinset = J
    · obtain ⟨p, rfl⟩ := h
      have : c (Lp p).toFinset = σ p := by
        simp only [hc]
        rw [Finset.sum_eq_single p]
        · simp
        · intro p' _ hp
          rw [if_neg fun h => hp (hinj h)]
        · simp
      rw [this, hσa]
    · have : c J = 0 := sum_eq_zero fun p _ => if_neg fun h' => h ⟨p, h'⟩
      rw [this]; simp
  have hchaos : ∀ z, chaos (xi μ) c k univ z =
      ∑ p, σ p * ((Lp p).map fun a => xi μ a (z a)).prod := by
    intro z
    simp only [chaos, hc, sum_mul]
    rw [sum_comm]
    refine sum_congr rfl fun p _ => ?_
    have hmem : (Lp p).toFinset ∈ powersetCard k (univ : Finset ι) := by
      rw [mem_powersetCard]
      exact ⟨subset_univ _, by rw [List.toFinset_card_of_nodup (hnd p), hlen]⟩
    rw [Finset.sum_eq_single (Lp p).toFinset]
    · rw [if_pos rfl, List.prod_toFinset _ (hnd p)]
    · intro J _ hJ
      rw [if_neg (Ne.symm hJ), zero_mul]
    · exact fun h => absurd hmem h
  have hsum : ∑ p, |x p| = ext (fun z => v (T.eval z) * chaos (xi μ) c k univ z) μ := by
    calc ∑ p, |x p| = ∑ p, σ p * x p := sum_congr rfl fun p _ => hσx p
      _ = ∑ p, ext (fun z => σ p * (g z * ((Lp p).map fun a => xi μ a (z a)).prod)) μ :=
          sum_congr rfl fun p _ => by
            rw [ext_smul]
            simp only [hx]
            rw [ext_Dl _ (hnd p) g μ hμ2]
      _ = ext (fun z => ∑ p, σ p * (g z * ((Lp p).map fun a => xi μ a (z a)).prod)) μ :=
          (ext_sum _ _ _).symm
      _ = _ := by
          unfold ext
          refine sum_congr rfl fun z _ => ?_
          dsimp only
          rw [hchaos]
          simp only [mul_sum, hg]
          congr 1
          exact sum_congr rfl fun p _ => by ring
  have hB := abs_ext_tree_chaos_le (ξ := xi μ) (B₀ := 2) hμ1 (xi_mean hμ) two_pos (abs_xi_le hμ)
    hd hK hKsq hn T hT k c hcb v hv
  rw [← hsum] at hB
  exact (le_abs_self _).trans hB

end QuarticQuery.ForrelationLower

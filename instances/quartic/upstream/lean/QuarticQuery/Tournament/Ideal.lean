module

public import QuarticQuery.Statement
import QuarticQuery.Tournament.Drift

/-!
# The ideal tournament process

The classical process in the proof of Proposition 3.2: equations (10) to (14)
and the parameter arithmetic. No quantum object appears here.

Representation. The state is the pivot history, newest pivot first. Weights are
the function `weight a L` of the history, which is also the product the quantum
sampler realises, so nonnegativity and the upper bound need no reachability
invariant. The `T`-step law is the recursive finite sum `expectFrom`, one
first-step decomposition per stage, so no measure theory is needed.
`expectFrom_const` is the statement that the law has total mass one.

The proof uses no order or transitivity: `a i j` for non-winners is arbitrary.
-/

public section

namespace QuarticQuery.Tournament

variable {ι : Type} [Fintype ι]

/-- Comparison probabilities lie in `[0, 1]`. -/
@[expose] def UnitValued (a : ι → ι → ℝ) : Prop := ∀ i j, 0 ≤ a i j ∧ a i j ≤ 1

/-- The total weight `W`. -/
@[expose] noncomputable def total (w : ι → ℝ) : ℝ := ∑ i, w i

/-- Ledger: eq-12. Weights start at one; pivot `p` multiplies `w i` by `a i p`. -/
@[expose] def weight (a : ι → ι → ℝ) : List ι → ι → ℝ
  | [], _ => 1
  | p :: L, i => weight a L i * a i p

/-- Ledger: def-ideal-process. Expectation of `g` of the final weights and list
after `T` more steps from history `L`. At `W = 0` the state is absorbing;
otherwise pivot `p` has probability `w p / W`. -/
@[expose] noncomputable def expectFrom (a : ι → ι → ℝ) :
    ℕ → List ι → ((ι → ℝ) → List ι → ℝ) → ℝ
  | 0, L, g => g (weight a L) L
  | T + 1, L, g =>
      if total (weight a L) = 0 then expectFrom a T L g
      else ∑ p, weight a L p / total (weight a L) * expectFrom a T (p :: L) g

/-- The `T`-step expectation from the empty history. -/
@[expose] noncomputable def expectAfter (a : ι → ι → ℝ) (T : ℕ)
    (g : (ι → ℝ) → List ι → ℝ) : ℝ :=
  expectFrom a T [] g

open Classical in
/-- The probability of an event of the final weights and list. -/
@[expose] noncomputable def prob (a : ι → ι → ℝ) (T : ℕ)
    (E : (ι → ℝ) → List ι → Prop) : ℝ :=
  expectAfter a T fun w L => if E w L then 1 else 0

/-! ## Weights -/

omit [Fintype ι] in
/-- Weights stay nonnegative. -/
theorem weight_nonneg {a : ι → ι → ℝ} (h : UnitValued a) (L : List ι) (i : ι) :
    0 ≤ weight a L i := by
  induction L with
  | nil => simp [weight]
  | cons p L ih => exact mul_nonneg ih (h i p).1

omit [Fintype ι] in
/-- Weights stay at most their initial value. -/
theorem weight_le_one {a : ι → ι → ℝ} (h : UnitValued a) (L : List ι) (i : ι) :
    weight a L i ≤ 1 := by
  induction L with
  | nil => simp [weight]
  | cons p L ih => simpa [weight] using mul_le_mul ih (h i p).2 (h i p).1 zero_le_one

theorem total_nonneg {a : ι → ι → ℝ} (h : UnitValued a) (L : List ι) :
    0 ≤ total (weight a L) :=
  Finset.sum_nonneg fun i _ => weight_nonneg h L i

theorem weight_le_total {a : ι → ι → ℝ} (h : UnitValued a) (L : List ι) (i : ι) :
    weight a L i ≤ total (weight a L) :=
  Finset.single_le_sum (fun j _ => weight_nonneg h L j) (Finset.mem_univ i)

/-- At `W = 0` every weight is zero, and so the state is absorbing as stated. -/
theorem weight_eq_zero_of_total {a : ι → ι → ℝ} (h : UnitValued a) {L : List ι}
    (hW : total (weight a L) = 0) (i : ι) : weight a L i = 0 :=
  le_antisymm (hW ▸ weight_le_total h L i) (weight_nonneg h L i)

/-! ## Expectation calculus -/

theorem expectFrom_const (a : ι → ι → ℝ) (T : ℕ) (L : List ι) (c : ℝ) :
    expectFrom a T L (fun _ _ => c) = c := by
  induction T generalizing L with
  | zero => rfl
  | succ T ih =>
    simp only [expectFrom, ih]
    split_ifs with hW
    · rfl
    · rw [← Finset.sum_mul, ← Finset.sum_div]
      change total (weight a L) / total (weight a L) * c = c
      rw [div_self hW, one_mul]

theorem expectFrom_const_mul (a : ι → ι → ℝ) (T : ℕ) (L : List ι) (c : ℝ)
    (g : (ι → ℝ) → List ι → ℝ) :
    expectFrom a T L (fun w l => c * g w l) = c * expectFrom a T L g := by
  induction T generalizing L with
  | zero => rfl
  | succ T ih =>
    simp only [expectFrom, ih]
    split_ifs with hW
    · rfl
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun p _ => by ring

theorem expectFrom_add (a : ι → ι → ℝ) (T : ℕ) (L : List ι)
    (g h : (ι → ℝ) → List ι → ℝ) :
    expectFrom a T L (fun w l => g w l + h w l)
      = expectFrom a T L g + expectFrom a T L h := by
  induction T generalizing L with
  | zero => rfl
  | succ T ih =>
    simp only [expectFrom, ih]
    split_ifs with hW
    · rfl
    · rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring

/-- Monotonicity. The comparison is needed only on histories of length at most
`|L| + T`, which are the only ones the process can reach. -/
theorem expectFrom_mono {a : ι → ι → ℝ} (ha : UnitValued a) (T : ℕ) (L : List ι)
    {g h : (ι → ℝ) → List ι → ℝ}
    (hgh : ∀ l : List ι, l.length ≤ L.length + T →
      g (weight a l) l ≤ h (weight a l) l) :
    expectFrom a T L g ≤ expectFrom a T L h := by
  induction T generalizing L with
  | zero => exact hgh L le_rfl
  | succ T ih =>
    simp only [expectFrom]
    split_ifs with hW
    · exact ih L fun l hl => hgh l (by omega)
    · refine Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left ?_ ?_
      · exact ih (p :: L) fun l hl => hgh l (by simp only [List.length_cons] at hl; omega)
      · exact div_nonneg (weight_nonneg ha L p) (total_nonneg ha L)

theorem prob_nonneg {a : ι → ι → ℝ} (ha : UnitValued a) (T : ℕ)
    (E : (ι → ℝ) → List ι → Prop) : 0 ≤ prob a T E := by
  classical
  rw [← expectFrom_const a T [] 0]
  exact expectFrom_mono ha T [] fun l _ => by split_ifs <;> norm_num

theorem prob_le_one {a : ι → ι → ℝ} (ha : UnitValued a) (T : ℕ)
    (E : (ι → ℝ) → List ι → Prop) : prob a T E ≤ 1 := by
  classical
  rw [← expectFrom_const a T [] 1]
  exact expectFrom_mono ha T [] fun l _ => by split_ifs <;> norm_num

/-- Complementary events have probabilities summing to one. -/
theorem prob_add_prob_not (a : ι → ι → ℝ) (T : ℕ) (E : (ι → ℝ) → List ι → Prop) :
    prob a T E + prob a T (fun w l => ¬ E w l) = 1 := by
  classical
  unfold prob expectAfter
  rw [← expectFrom_add]
  refine (congrArg (expectFrom a T []) (funext fun w => funext fun l => ?_)).trans
    (expectFrom_const a T [] 1)
  by_cases hE : E w l <;> simp [hE]

/-- The list has at most `T` entries, almost surely. -/
theorem prob_length_le {a : ι → ι → ℝ} (ha : UnitValued a) (T : ℕ) :
    prob a T (fun _ l => l.length ≤ T) = 1 := by
  classical
  refine le_antisymm (prob_le_one ha T _) ?_
  conv_lhs => rw [← expectFrom_const a T [] 1]
  refine expectFrom_mono ha T [] fun l hl => ?_
  simp only [List.length_nil, zero_add] at hl
  simp [hl]

/-! ## Drift -/

variable [DecidableEq ι]

/-- `T` further steps from any history divide the expected total by `2 ^ T`. -/
theorem expectFrom_total_le {a : ι → ι → ℝ} (hc : IsComparison a) (ha : UnitValued a)
    (T : ℕ) (L : List ι) :
    expectFrom a T L (fun w _ => total w) ≤ total (weight a L) / 2 ^ T := by
  induction T generalizing L with
  | zero => simp [expectFrom]
  | succ T ih =>
    simp only [expectFrom]
    split_ifs with hW
    · simpa [hW] using ih L
    · have hpos : 0 < total (weight a L) := lt_of_le_of_ne (total_nonneg ha L) (Ne.symm hW)
      have hstep : ∀ p, expectFrom a T (p :: L) (fun w _ => total w)
          ≤ (∑ i, weight a L i * a i p) / 2 ^ T := fun p => ih (p :: L)
      calc
        ∑ p, weight a L p / total (weight a L) * expectFrom a T (p :: L) (fun w _ => total w)
            ≤ ∑ p, weight a L p / total (weight a L) *
                ((∑ i, weight a L i * a i p) / 2 ^ T) :=
              Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left (hstep p)
                (div_nonneg (weight_nonneg ha L p) hpos.le)
        _ = (∑ p, weight a L p / total (weight a L) * ∑ i, weight a L i * a i p) / 2 ^ T := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl fun p _ => by ring
        _ ≤ (total (weight a L) / 2) / 2 ^ T := by
              gcongr
              exact expected_weight_le_half _ hc rfl hpos
        _ = total (weight a L) / 2 ^ (T + 1) := by
              rw [pow_succ]; field_simp

/-- Ledger: claim-expected-WT. `E[W_T] ≤ m / 2 ^ T`. -/
theorem expected_final_weight {a : ι → ι → ℝ} (hc : IsComparison a) (ha : UnitValued a)
    (T : ℕ) :
    expectAfter a T (fun w _ => total w) ≤ (Fintype.card ι : ℝ) / 2 ^ T := by
  simpa [total, weight, expectAfter] using expectFrom_total_le hc ha T []

/-! ## Survival of a dominant candidate -/

/-- Equation (11): `s` beats every other candidate with probability `≥ 1 - ε`. -/
@[expose] def Dominant (a : ι → ι → ℝ) (ε : ℝ) (s : ι) : Prop :=
  ∀ j, j ≠ s → 1 - ε ≤ a s j

omit [Fintype ι] [DecidableEq ι] in
/-- An unselected dominant candidate loses at most a factor `1 - ε` per pivot. -/
theorem pow_le_weight {a : ι → ι → ℝ} {ε : ℝ} {s : ι} (ha : UnitValued a)
    (hε : ε ≤ 1) (hd : Dominant a ε s) (L : List ι) (hs : s ∉ L) :
    (1 - ε) ^ L.length ≤ weight a L s := by
  induction L with
  | nil => simp [weight]
  | cons p L ih =>
    have hps : p ≠ s := fun h => hs (h ▸ List.mem_cons_self)
    have hsL : s ∉ L := fun h => hs (List.mem_cons_of_mem p h)
    rw [List.length_cons, pow_succ]
    exact mul_le_mul (ih hsL) (hd p hps) (by linarith) (weight_nonneg ha L s)

omit [Fintype ι] [DecidableEq ι] in
/-- Ledger: claim-weight-lb. If `s` is unselected along a history of length at
most `T`, its weight is at least `(1 - ε) ^ T ≥ 1 - T ε > 1 / 2`. -/
theorem dominant_weight_lb {a : ι → ι → ℝ} {ε : ℝ} {s : ι} (ha : UnitValued a)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hd : Dominant a ε s) {T : ℕ} (hT : (T : ℝ) * ε < 1 / 2)
    (L : List ι) (hlen : L.length ≤ T) (hs : s ∉ L) :
    (1 - ε) ^ T ≤ weight a L s ∧ 1 - (T : ℝ) * ε ≤ (1 - ε) ^ T ∧ 1 / 2 < weight a L s := by
  have h1 : (1 - ε) ^ T ≤ weight a L s :=
    (pow_le_pow_of_le_one (by linarith) (by linarith) hlen).trans
      (pow_le_weight ha hε hd L hs)
  have h2 : 1 - (T : ℝ) * ε ≤ (1 - ε) ^ T := by
    have := one_add_mul_le_pow (a := -ε) (by linarith) T
    simpa [sub_eq_add_neg, mul_neg] using this
  exact ⟨h1, h2, by linarith⟩

omit [DecidableEq ι] in
/-- While `s` is unselected the total weight exceeds `1 / 2`, so the process
cannot be absorbed before selecting `s`. -/
theorem half_lt_total {a : ι → ι → ℝ} {ε : ℝ} {s : ι} (ha : UnitValued a)
    (hε0 : 0 ≤ ε) (hε : ε ≤ 1) (hd : Dominant a ε s) {T : ℕ} (hT : (T : ℝ) * ε < 1 / 2)
    (L : List ι) (hlen : L.length ≤ T) (hs : s ∉ L) :
    1 / 2 < total (weight a L) :=
  (dominant_weight_lb ha hε0 hε hd hT L hlen hs).2.2.trans_le (weight_le_total ha L s)

/-! ## Markov -/

/-- Ledger: eq-14. `Pr[s absent] ≤ Pr[W_T ≥ 1/2] ≤ 2m / 2 ^ T`. -/
theorem ideal_miss_le {a : ι → ι → ℝ} {ε : ℝ} {s : ι}
    (hc : IsComparison a) (ha : UnitValued a) (hε0 : 0 ≤ ε) (hε : ε ≤ 1)
    (hd : Dominant a ε s) {T : ℕ} (hT : (T : ℝ) * ε < 1 / 2) :
    prob a T (fun _ l => s ∉ l) ≤ prob a T (fun w _ => 1 / 2 ≤ total w) ∧
      prob a T (fun w _ => 1 / 2 ≤ total w) ≤ 2 * (Fintype.card ι : ℝ) / 2 ^ T := by
  classical
  constructor
  · refine expectFrom_mono ha T [] fun l hl => ?_
    simp only [List.length_nil, zero_add] at hl
    beta_reduce
    by_cases hs : s ∈ l
    · have hn : ¬ s ∉ l := not_not.2 hs
      simp only [hn, ↓reduceIte]
      split_ifs <;> norm_num
    · have hh := (half_lt_total ha hε0 hε hd hT l hl hs).le
      simp only [hs, hh, not_false_eq_true, ↓reduceIte, le_refl]
  · calc
      prob a T (fun w _ => 1 / 2 ≤ total w)
          ≤ expectFrom a T [] (fun w _ => 2 * total w) := by
            refine expectFrom_mono ha T [] fun l _ => ?_
            have := total_nonneg ha l
            split_ifs with h
            · linarith
            · linarith
      _ = 2 * expectAfter a T (fun w _ => total w) := expectFrom_const_mul a T [] 2 _
      _ ≤ 2 * ((Fintype.card ι : ℝ) / 2 ^ T) := by
            gcongr
            exact expected_final_weight hc ha T
      _ = 2 * (Fintype.card ι : ℝ) / 2 ^ T := by ring

/-! ## Parameters -/

/-- `T = ⌈log₂ (1000 m)⌉`. -/
@[expose] def Tval (m : ℕ) : ℕ := Nat.clog 2 (1000 * m)

/-- `ε = 1 / (1000 T)`. -/
@[expose] noncomputable def epsval (m : ℕ) : ℝ := 1 / (1000 * (Tval m : ℝ))

theorem Tval_pos {m : ℕ} (hm : 2 ≤ m) : 0 < Tval m :=
  Nat.clog_pos (by norm_num) (by omega)

theorem epsval_nonneg (m : ℕ) : 0 ≤ epsval m := by
  unfold epsval; positivity

theorem epsval_le {m : ℕ} (hm : 2 ≤ m) : epsval m ≤ 1 / 1000 := by
  have hT : (1 : ℝ) ≤ Tval m := by exact_mod_cast Tval_pos hm
  unfold epsval
  apply one_div_le_one_div_of_le (by norm_num)
  linarith

/-- Ledger: def-T-eps. `T ε = 1 / 1000`. -/
theorem Tval_mul_epsval {m : ℕ} (hm : 2 ≤ m) : (Tval m : ℝ) * epsval m = 1 / 1000 := by
  have hT : (Tval m : ℝ) ≠ 0 := by exact_mod_cast (Tval_pos hm).ne'
  unfold epsval
  field_simp

/-- Ledger: def-T-eps. `2m / 2 ^ T ≤ 1 / 500`. -/
theorem miss_bound_le (m : ℕ) : 2 * (m : ℝ) / 2 ^ Tval m ≤ 1 / 500 := by
  have h : (1000 * m : ℝ) ≤ 2 ^ Tval m := by
    exact_mod_cast Nat.le_pow_clog (by norm_num) (1000 * m)
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  linarith

/-- Ledger: def-T-eps. The numeric consequence used by the conclusion. -/
theorem total_error_lt {m : ℕ} (hm : 2 ≤ m) :
    2 * (m : ℝ) / 2 ^ Tval m + (Tval m : ℝ) * epsval m + epsval m < 1 / 3 := by
  have h1 := miss_bound_le m
  have h2 := Tval_mul_epsval hm
  have h3 := epsval_le hm
  linarith

/-- Ledger: prop-3.2. The ideal part: for arbitrary comparisons on `m ≥ 2`
candidates and a dominant `s` at the stated parameters, the `T`-step list has at
most `T` entries and misses `s` with probability at most `2m / 2 ^ T`. The
quantum implementation adds the remaining `T ε`. -/
theorem ideal_tournament {a : ι → ι → ℝ} {s : ι}
    (hc : IsComparison a) (ha : UnitValued a)
    (hm : 2 ≤ Fintype.card ι) (hd : Dominant a (epsval (Fintype.card ι)) s) :
    let m := Fintype.card ι
    let T := Tval m
    prob a T (fun _ l => l.length ≤ T) = 1 ∧
    prob a T (fun _ l => s ∉ l) ≤ 2 * (m : ℝ) / 2 ^ T ∧
    1 - 2 * (m : ℝ) / 2 ^ T ≤ prob a T (fun _ l => s ∈ l) ∧
    (∀ L : List ι, L.length ≤ T → s ∉ L → 1 / 2 < total (weight a L)) ∧
    2 * (m : ℝ) / 2 ^ T ≤ 1 / 500 ∧
    (T : ℝ) * epsval m = 1 / 1000 ∧
    2 * (m : ℝ) / 2 ^ T + (T : ℝ) * epsval m + epsval m < 1 / 3 := by
  intro m T
  have hT : (T : ℝ) * epsval m < 1 / 2 := by
    rw [Tval_mul_epsval hm]; norm_num
  have hε0 := epsval_nonneg m
  have hε : epsval m ≤ 1 := (epsval_le hm).trans (by norm_num)
  obtain ⟨h1, h2⟩ := ideal_miss_le hc ha hε0 hε hd hT
  have hmiss := h1.trans h2
  refine ⟨prob_length_le ha T, hmiss, ?_, half_lt_total ha hε0 hε hd hT,
    miss_bound_le m, Tval_mul_epsval hm, total_error_lt hm⟩
  have hsum := prob_add_prob_not a T (fun _ l => s ∈ l)
  linarith

/-! ## Sanity: comparisons need not be transitive -/

/-- The cyclic comparison on three candidates: `i` always loses to `i + 1`. -/
@[expose] noncomputable def cycleThree (i j : Fin 3) : ℝ := if j = i + 1 then 1 else 0

/-- The all-even comparison on three candidates. -/
@[expose] noncomputable def evenThree (i j : Fin 3) : ℝ := if i = j then 0 else 1 / 2

/-- A cycle is a valid comparison, and it admits no transitive order. -/
theorem cycleThree_isComparison :
    IsComparison cycleThree ∧ UnitValued cycleThree ∧
      cycleThree 0 1 = 1 ∧ cycleThree 1 2 = 1 ∧ cycleThree 2 0 = 1 := by
  have key : ∀ i j : Fin 3, i ≠ j → (j = i + 1 ↔ ¬ i = j + 1) := by decide
  have key2 : ∀ i : Fin 3, ¬ i = i + 1 := by decide
  refine ⟨⟨fun i j hne => ?_, fun i => ?_⟩, fun i j => ?_, ?_, ?_, ?_⟩
  · have := key i j hne
    unfold cycleThree
    split_ifs <;> first | (exfalso; tauto) | norm_num
  · exact ite_eq_right_of_eq_false _ _ (eq_false (key2 i))
  · unfold cycleThree
    split_ifs <;> norm_num
  all_goals exact ite_eq_left_of_eq_true _ _ (eq_true (by decide))

/-- The even comparison is valid and unit-valued. -/
theorem evenThree_isComparison : IsComparison evenThree ∧ UnitValued evenThree := by
  refine ⟨⟨fun i j h => ?_, fun i => ?_⟩, fun i j => ?_⟩
  · have h' := h.symm
    simp only [evenThree, h, h', ↓reduceIte]
    norm_num
  · simp [evenThree]
  · unfold evenThree
    split_ifs <;> norm_num

end QuarticQuery.Tournament

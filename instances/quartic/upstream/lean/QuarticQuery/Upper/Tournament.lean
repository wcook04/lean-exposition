module

public import QuarticQuery.Upper.Amplify
public import QuarticQuery.Tournament.Ideal

/-!
# Proposition 3.2: the tournament as a program

For comparison samplers on a finite candidate type and any verifier `v`, the program
samples pivots by bounded amplification, and verifies what it has listed when the
stages run out or a stage fails. Its acceptance probability is the explicit recursion
`tval`, with one stage's failure probability per history. `tval_lower` is the coupling
with `Tournament.expectFrom`: failure at a history is charged only at that history, so
history-dependent failure is allowed, and the bound is pointwise in the input.

The stage state is the uniform index and one comparison per pivot, with all workspace
retained. Its success label holds when every comparison was won.
-/

@[expose] public section

set_option linter.unusedSectionVars false

namespace QuarticQuery.Upper

open QuarticQuery.Tournament QuarticQuery.Amplification

/-! ## The stage sampler -/

section Stage

variable {Col : Type} [Fintype Col]

/-- Ledger: construct-sampler. The law of one stage: `some i` if the uniform index `i`
beat every pivot, `none` otherwise. -/
noncomputable def stageLaw (a : Col → Col → ℝ) : List Col → Option Col → ℝ
  | [], none => 0
  | [], some _ => (Fintype.card Col : ℝ)⁻¹
  | p :: L, none => stageLaw a L none + ∑ i, stageLaw a L (some i) * (1 - a i p)
  | p :: L, some i => stageLaw a L (some i) * a i p

/-- Ledger: construct-sampler. `i` succeeds with probability `w i / m`. -/
theorem stageLaw_some (a : Col → Col → ℝ) (L : List Col) (i : Col) :
    stageLaw a L (some i) = weight a L i / Fintype.card Col := by
  induction L with
  | nil => simp [stageLaw, weight]
  | cons p L ih =>
    simp only [stageLaw, weight, ih]
    ring

theorem sum_stageLaw_some (a : Col → Col → ℝ) (L : List Col) :
    ∑ i, stageLaw a L (some i) = total (weight a L) / Fintype.card Col := by
  simp only [stageLaw_some, total, Finset.sum_div]

theorem pt_some_some (i j : Col) : pt (some i) (some j) = pt i j := by
  by_cases h : i = j
  · subst h; simp [pt_self]
  · rw [pt_of_ne h, pt_of_ne (by simpa using h)]

variable {ι : Type} [Nonempty ι] [Nonempty Col]

/-- Ledger: construct-sampler. The stage state of equation (15), as a sampler. -/
theorem stage_samples {cc : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b) (L : List Col) :
    Samples (L.length * cc) fun x o => stageLaw (a x) L o := by
  classical
  induction L with
  | nil =>
    have hm : (Fintype.card Col : ℝ) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    refine (Samples.gate (ι := ι) (p := fun o : Option Col => stageLaw (fun _ _ => 0) [] o)
      (fun o => ?_) ?_).cast (by simp) |>.congr fun x o => ?_
    · cases o <;> simp [stageLaw]
    · rw [Fintype.sum_option]
      simp [stageLaw, Finset.card_univ, hm]
    · cases o <;> rfl
  | cons p L ih =>
    let K : Option Col → BitInput ι → Option Col → ℝ := fun o' x o =>
      match o' with
      | none => pt none o
      | some i => ∑ b : Bool, bern (a x i p) b * pt (if b then some i else none) o
    have hK : ∀ o', Samples cc (K o') := fun o' => by
      cases o' with
      | none => exact (Samples.pure (ι := ι) (none : Option Col)).mono (Nat.zero_le _)
      | some i => exact (hcmp i p).map fun b => if b then some i else none
    refine ((ih.bind hK).cast (by simp [Nat.succ_mul])).congr fun x o => ?_
    rw [Fintype.sum_option]
    simp only [K, Fintype.sum_bool, bern, ite_true, Bool.false_eq_true, ite_false]
    cases o with
    | none =>
      simp [stageLaw, pt_self, pt_of_ne]
    | some j =>
      have h0 : pt (none : Option Col) (some j) = 0 := pt_of_ne (by simp)
      simp only [h0, mul_zero, zero_add, add_zero, pt_some_some, stageLaw]
      rw [Finset.sum_congr rfl fun i _ => (mul_assoc _ _ _).symm,
        sum_mul_pt (fun i => stageLaw (a x) L (some i) * a x i p) j]

end Stage

/-! ## Listing and verifying -/

section Value

variable {Col : Type} [Fintype Col]

/-- The acceptance probability of verifying a list, stopping at the first success. -/
noncomputable def vall (v : Col → ℝ) : List Col → ℝ
  | [] => 0
  | c :: L => v c + (1 - v c) * vall v L

/-- The acceptance probability of `T` further stages after history `L`. -/
noncomputable def tval (a : Col → Col → ℝ) (v : Col → ℝ) (f : List Col → ℝ) :
    ℕ → List Col → ℝ
  | 0, L => vall v L
  | T + 1, L => f L * vall v L +
      (1 - f L) * ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L)

theorem vall_nonneg {v : Col → ℝ} (h : ∀ c, 0 ≤ v c ∧ v c ≤ 1) (L : List Col) : 0 ≤ vall v L := by
  induction L with
  | nil => simp [vall]
  | cons c L ih =>
    have := h c
    simp only [vall]
    nlinarith

theorem vall_le_one {v : Col → ℝ} (h : ∀ c, 0 ≤ v c ∧ v c ≤ 1) (L : List Col) : vall v L ≤ 1 := by
  induction L with
  | nil => simp [vall]
  | cons c L ih =>
    have := h c
    simp only [vall]
    nlinarith

/-- Once listed, a candidate's own verification counts. -/
theorem le_vall_of_mem {v : Col → ℝ} (h : ∀ c, 0 ≤ v c ∧ v c ≤ 1) {L : List Col} {s : Col}
    (hs : s ∈ L) : v s ≤ vall v L := by
  induction L with
  | nil => simp at hs
  | cons c L ih =>
    have hc := h c
    have h0 := vall_nonneg h L
    have h1 := vall_le_one h L
    simp only [vall]
    rcases List.mem_cons.1 hs with rfl | hL
    · nlinarith
    · have := ih hL
      nlinarith

theorem vall_le {v : Col → ℝ} (h : ∀ c, 0 ≤ v c ∧ v c ≤ 1) {ε : ℝ} (hε : ∀ c, v c ≤ ε)
    (L : List Col) : vall v L ≤ L.length * ε := by
  induction L with
  | nil => simp [vall]
  | cons c L ih =>
    have hc := h c
    have h0 := vall_nonneg h L
    have := hε c
    simp only [vall, List.length_cons]
    push_cast
    nlinarith

variable {a : Col → Col → ℝ} {v : Col → ℝ} {f : List Col → ℝ}

theorem sum_ratio_le (L : List Col) :
    ∑ p, weight a L p / total (weight a L) ≤ 1 := by
  rw [← Finset.sum_div]
  exact div_self_le_one _

theorem sum_ratio (L : List Col) (hW : total (weight a L) ≠ 0) :
    ∑ p, weight a L p / total (weight a L) = 1 := by
  rw [← Finset.sum_div]
  exact div_self hW

theorem ratio_nonneg (ha : UnitValued a) (L : List Col) (p : Col) :
    0 ≤ weight a L p / total (weight a L) :=
  div_nonneg (weight_nonneg ha L p) (total_nonneg ha L)

/-- Ledger: prop-3.2. On a zero-input every verification accepts rarely. -/
theorem tval_le (ha : UnitValued a) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ c, v c ≤ ε) (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1) (T : ℕ) (L : List Col) :
    tval a v f T L ≤ (L.length + T : ℕ) * ε := by
  induction T generalizing L with
  | zero => simpa [tval] using vall_le hv hε L
  | succ T ih =>
    simp only [tval]
    obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((L.length + (T + 1) : ℕ) : ℝ) * ε := ⟨_, rfl⟩
    rw [← hB]
    have hB0 : 0 ≤ B := by rw [hB]; positivity
    have hA : vall v L ≤ B := (vall_le hv hε L).trans (by
      rw [hB]
      gcongr
      omega)
    have hY : ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) ≤ B := by
      calc _ ≤ ∑ p, weight a L p / total (weight a L) * B :=
            Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
              ((ih (p :: L)).trans_eq (by
                rw [hB, show (p :: L).length + T = L.length + (T + 1) by
                  simp only [List.length_cons]; omega])) (ratio_nonneg ha L p)
        _ = (∑ p, weight a L p / total (weight a L)) * B := by rw [Finset.sum_mul]
        _ ≤ 1 * B := mul_le_mul_of_nonneg_right (sum_ratio_le L) hB0
        _ = B := one_mul B
    have := hf L
    nlinarith

/-- Later termination cannot remove a listed candidate. -/
theorem le_tval_of_mem (ha : UnitValued a) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1)
    (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1) (hz : ∀ L, total (weight a L) = 0 → f L = 1) {s : Col} (T : ℕ)
    {L : List Col} (hs : s ∈ L) : v s ≤ tval a v f T L := by
  induction T generalizing L with
  | zero => exact le_vall_of_mem hv hs
  | succ T ih =>
    simp only [tval]
    have hA := le_vall_of_mem hv hs
    by_cases hW : total (weight a L) = 0
    · rw [hz L hW]
      simpa using hA
    · have hY : v s ≤ ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) := by
        calc v s = (∑ p, weight a L p / total (weight a L)) * v s := by rw [sum_ratio L hW, one_mul]
          _ = ∑ p, weight a L p / total (weight a L) * v s := by rw [Finset.sum_mul]
          _ ≤ _ := Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
              (ih (List.mem_cons_of_mem p hs)) (ratio_nonneg ha L p)
      have := hf L
      nlinarith

open Classical in
/-- The ideal probability of missing `s` in `T` more steps. -/
noncomputable def missFrom (a : Col → Col → ℝ) (s : Col) (T : ℕ) (L : List Col) : ℝ :=
  expectFrom a T L fun _ l => if s ∉ l then 1 else 0

theorem missFrom_nonneg (ha : UnitValued a) (s : Col) (T : ℕ) (L : List Col) :
    0 ≤ missFrom a s T L := by
  classical
  rw [← expectFrom_const a T L 0]
  exact expectFrom_mono ha T L fun l _ => by split_ifs <;> norm_num

/-- Ledger: claim-coupling. The coupling of Proposition 3.2. From any history, the real
acceptance probability is at least `(1 - ε)` times the ideal chance of listing `s`, less
`ε` per remaining stage. Stages failing with history-dependent probability at most `ε`
before `s` is listed are charged to that history. -/
theorem tval_lower (ha : UnitValued a) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1) (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1)
    (hz : ∀ L, total (weight a L) = 0 → f L = 1) {s : Col} {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hd : Dominant a ε s) (hvs : 1 - ε ≤ v s) {T₀ : ℕ} (hT : (T₀ : ℝ) * ε < 1 / 2)
    (hfail : ∀ L : List Col, L.length ≤ T₀ → s ∉ L → f L ≤ ε) (T : ℕ) (L : List Col)
    (hL : L.length + T ≤ T₀) :
    (1 - ε) * (1 - missFrom a s T L - T * ε) ≤ tval a v f T L := by
  classical
  have hc : 0 ≤ 1 - ε := by linarith
  induction T generalizing L with
  | zero =>
    by_cases hs : s ∈ L
    · have h1 := le_vall_of_mem hv hs
      simp only [missFrom, expectFrom, tval, hs, not_true_eq_false, ite_false]
      push_cast
      nlinarith
    · have h1 := vall_nonneg hv L
      simp [missFrom, expectFrom, tval, hs, h1]
  | succ T ih =>
    have hU := missFrom_nonneg ha s (T + 1) L
    by_cases hs : s ∈ L
    · have h1 := le_tval_of_mem ha hv hf hz (T + 1) hs
      have hT0 : (0 : ℝ) ≤ ((T + 1 : ℕ) : ℝ) * ε := by positivity
      have : 1 - missFrom a s (T + 1) L - ((T + 1 : ℕ) : ℝ) * ε ≤ 1 := by linarith
      nlinarith
    · have hW := half_lt_total ha hε0 hε1 hd hT L (by omega) hs
      have hW0 : total (weight a L) ≠ 0 := by linarith
      obtain ⟨hf0, hf1⟩ := hf L
      have hfε := hfail L (by omega) hs
      have hval : missFrom a s (T + 1) L =
          ∑ p, weight a L p / total (weight a L) * missFrom a s T (p :: L) := by
        simp only [missFrom, expectFrom, hW0, ite_false]
      obtain ⟨X, hX⟩ : ∃ X, X = 1 - missFrom a s (T + 1) L - T * ε := ⟨_, rfl⟩
      have hY : (1 - ε) * X ≤
          ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) := by
        calc (1 - ε) * X
            = ∑ p, weight a L p / total (weight a L) *
                ((1 - ε) * (1 - missFrom a s T (p :: L) - T * ε)) := by
              have e : ∀ p, weight a L p / total (weight a L) *
                  ((1 - ε) * (1 - missFrom a s T (p :: L) - T * ε)) =
                  (1 - ε) * (1 - T * ε) * (weight a L p / total (weight a L)) -
                    (1 - ε) * (weight a L p / total (weight a L) * missFrom a s T (p :: L)) :=
                fun p => by ring
              rw [hX, hval, Finset.sum_congr rfl fun p _ => e p, Finset.sum_sub_distrib,
                ← Finset.mul_sum, ← Finset.mul_sum, sum_ratio L hW0]
              ring
          _ ≤ _ := Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
              (ih (p :: L) (by simp only [List.length_cons]; omega)) (ratio_nonneg ha L p)
      have hA := vall_nonneg hv L
      have hT0 : (0 : ℝ) ≤ (T : ℝ) * ε := by positivity
      have hX1 : X ≤ 1 := by rw [hX]; linarith
      have hgoal : 1 - missFrom a s (T + 1) L - ((T + 1 : ℕ) : ℝ) * ε = X - ε := by
        rw [hX]; push_cast; ring
      simp only [tval]
      rw [hgoal]
      have hprod : 0 ≤ f L * vall v L := mul_nonneg hf0 hA
      have h1f : 0 ≤ 1 - f L := by linarith
      have hstep : (1 - f L) * ((1 - ε) * X) ≤ (1 - f L) *
          ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) :=
        mul_le_mul_of_nonneg_left hY h1f
      have hkey : X - ε ≤ (1 - f L) * X := by
        by_cases hXn : 0 ≤ X
        · nlinarith
        · nlinarith
      have hc' := mul_le_mul_of_nonneg_left hkey hc
      nlinarith

end Value

/-! ## The program -/

section Program

variable {β : Type} [Fintype β]

/-- One amplified stage followed by a Bernoulli continuation, as a Bernoulli law. -/
theorem ampLaw_step (f V : ℝ) (q t : β → ℝ) (hsum : f + (1 - f) * ∑ p, q p / ∑ c, q c = 1)
    (b : Bool) :
    ∑ o, ampLaw f q o * (match o with | none => bern V b | some p => bern (t p) b) =
      bern (f * V + (1 - f) * ∑ p, q p / (∑ c, q c) * t p) b := by
  rw [Fintype.sum_option]
  simp only [ampLaw]
  cases b with
  | true =>
    simp only [bern, ite_true, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun p _ => by ring
  | false =>
    simp only [bern, Bool.false_eq_true, ite_false]
    have : ∑ p, (1 - f) * (q p / ∑ c, q c) * (1 - t p) =
        (1 - f) * ∑ p, q p / ∑ c, q c - (1 - f) * ∑ p, q p / (∑ c, q c) * t p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun p _ => by ring
    rw [this]
    linarith

end Program

variable {ι Col : Type} [Fintype ι] [Inhabited ι] [Fintype Col] [DecidableEq Col]

/-- Ledger: claim-tournament-cost. Verifying a list, at `cV` queries per candidate. -/
theorem vall_runs {cV : ℕ} {v : BitInput ι → Col → ℝ}
    (hv : ∀ c, Runs cV fun x b => bern (v x c) b) (L : List Col) :
    Runs (L.length * cV) fun x b => bern (vall (v x) L) b := by
  induction L with
  | nil =>
    refine (Runs.pure (ι := ι) false).mono (by simp) |>.congr fun x b => ?_
    cases b <;> simp [bern, vall, pt_self, pt_of_ne]
  | cons c L ih =>
    let K : Bool → BitInput ι → Bool → ℝ := fun o x b =>
      if o then pt true b else bern (vall (v x) L) b
    have hK : ∀ o, Runs (L.length * cV) (K o) := fun o => by
      cases o
      · simpa [K] using ih
      · simpa [K] using (Runs.pure (ι := ι) true).mono (Nat.zero_le _)
    refine ((hv c).bind hK).mono (by simp [Nat.succ_mul]; omega) |>.congr fun x b => ?_
    simp only [K, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false, vall]
    cases b <;> simp [bern, pt_self, pt_of_ne]
    ring

/-- The cost of one amplified stage with at most `T` pivots. -/
noncomputable def stageCost (m T cc : ℕ) (ε : ℝ) : ℕ :=
  trialCount ε * (2 * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (T * cc)))

/-- Ledger: prop-3.2, claim-tournament-cost. Proposition 3.2, with the list consumed by
a verifier. On every input the program makes at most `T (stage + cV)` queries, whatever
the comparisons are. Its acceptance probability is low if every candidate verifies with
probability at most `ε`, and high if a dominant candidate verifies with probability at
least `1 - ε`. -/
theorem tournament_runs {cc cV : ℕ} {a : BitInput ι → Col → Col → ℝ} {v : BitInput ι → Col → ℝ}
    (hm : 2 ≤ Fintype.card Col) (hc : ∀ x, IsComparison (a x)) (hu : ∀ x, UnitValued (a x))
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b)
    (hv : ∀ c, Runs cV fun x b => bern (v x c) b) (hv01 : ∀ x c, 0 ≤ v x c ∧ v x c ≤ 1) :
    let m := Fintype.card Col
    let T := Tval m
    let ε := epsval m
    ∃ val : BitInput ι → ℝ,
      Runs (T * stageCost m T cc ε + T * cV) (fun x b => bern (val x) b) ∧
      (∀ x, (∀ c, v x c ≤ ε) → val x ≤ T * ε) ∧
      (∀ x s, Dominant (a x) ε s → 1 - ε ≤ v x s →
        1 - 2 * (m : ℝ) / 2 ^ T - T * ε - ε ≤ val x) := by
  classical
  intro m T ε
  have : Nonempty Col := Fintype.card_pos_iff.1 (by omega)
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    positivity
  have hm0' : (0 : ℝ) < m := by
    have : 0 < m := by omega
    positivity
  have hε0 : 0 ≤ ε := epsval_nonneg m
  have hε1 : ε ≤ 1 / 1000 := epsval_le hm
  have hTε : (T : ℝ) * ε = 1 / 1000 := Tval_mul_epsval hm
  have hεpos : 0 < ε := by
    rcases hε0.eq_or_lt with h | h
    · rw [← h] at hTε; norm_num at hTε
    · exact h
  have hγ : (0 : ℝ) < (2 * (m : ℝ))⁻¹ := by positivity
  have hamp : ∀ L : List Col, ∃ f : BitInput ι → ℝ,
      (∀ x, 0 ≤ f x ∧ f x ≤ 1) ∧
      (∀ x, (2 * (m : ℝ))⁻¹ ≤ ∑ b, stageLaw (a x) L (some b) → f x ≤ ε) ∧
      (∀ x, ∑ b, stageLaw (a x) L (some b) = 0 → f x = 1) ∧
      Runs (trialCount ε * (2 * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (L.length * cc))))
        fun x => ampLaw (f x) fun b => stageLaw (a x) L (some b) :=
    fun L => (stage_samples hcmp L).amplify hγ hεpos
  choose f hf01 hfγ hfz hrun using hamp
  let g : BitInput ι → List Col → ℝ := fun x L => f L x
  have hg01 : ∀ x L, 0 ≤ g x L ∧ g x L ≤ 1 := fun x L => hf01 L x
  have hgz : ∀ x L, total (weight (a x) L) = 0 → g x L = 1 := fun x L h =>
    hfz L x (by rw [sum_stageLaw_some, h, zero_div])
  have hsumQ : ∀ x L, g x L + (1 - g x L) * ∑ p, stageLaw (a x) L (some p) /
      ∑ c, stageLaw (a x) L (some c) = 1 := fun x L => by
    by_cases hW : total (weight (a x) L) = 0
    · rw [hgz x L hW]; ring
    · have h : ∑ c, stageLaw (a x) L (some c) ≠ 0 := by
        rw [sum_stageLaw_some]
        exact div_ne_zero hW hm0
      rw [← Finset.sum_div, div_self h]
      ring
  have hratio : ∀ x L p, stageLaw (a x) L (some p) / ∑ c, stageLaw (a x) L (some c) =
      weight (a x) L p / total (weight (a x) L) := fun x L p => by
    rw [sum_stageLaw_some, stageLaw_some]
    exact div_div_div_cancel_right₀ hm0 _ _
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = stageCost m T cc ε := ⟨_, rfl⟩
  let val : BitInput ι → ℕ → List Col → ℝ := fun x n L => tval (a x) (v x) (g x) n L
  have hstageRuns : ∀ L : List Col, L.length ≤ T → Runs Cs
      fun x => ampLaw (f L x) fun b => stageLaw (a x) L (some b) := fun L hL => by
    refine (hrun L).mono ?_
    rw [hCs, stageCost]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_right _ hL)))
  have hrunT : ∀ (n : ℕ) (L : List Col), L.length + n ≤ T →
      Runs (n * Cs + (L.length + n) * cV) fun x b => bern (val x n L) b := by
    intro n
    induction n with
    | zero =>
      intro L _
      exact (vall_runs hv L).mono (by simp)
    | succ n ih =>
      intro L hL
      let K : Option Col → BitInput ι → Bool → ℝ := fun o x b =>
        match o with
        | none => bern (vall (v x) L) b
        | some p => bern (val x n (p :: L)) b
      have hK : ∀ o, Runs (n * Cs + (L.length + 1 + n) * cV) (K o) := fun o => by
        cases o with
        | none =>
          refine (vall_runs hv L).mono ?_
          have : L.length * cV ≤ (L.length + 1 + n) * cV :=
            Nat.mul_le_mul_right _ (by omega)
          omega
        | some p =>
          exact (ih (p :: L) (by simp only [List.length_cons]; omega)).mono (by simp)
      refine ((hstageRuns L (by omega)).bind hK).mono ?_ |>.congr fun x b => ?_
      · have e1 : (n + 1) * Cs = n * Cs + Cs := by ring
        have e2 : (L.length + (n + 1)) = L.length + 1 + n := by omega
        rw [e1, e2]
        omega
      · simp only [K]
        have := ampLaw_step (g x L) (vall (v x) L) (fun b => stageLaw (a x) L (some b))
          (fun p => val x n (p :: L)) (hsumQ x L) b
        simp only [hratio] at this
        exact this.symm
  refine ⟨fun x => val x T [], ?_, fun x hx => ?_, fun x s hd hvs => ?_⟩
  · refine (hrunT T [] (by simp)).mono ?_ |>.congr fun _ _ => rfl
    simp [hCs]
  · have := tval_le (hu x) (hv01 x) hε0 hx (hg01 x) T []
    simpa using this
  · have hT' : (T : ℝ) * ε < 1 / 2 := by rw [hTε]; norm_num
    have hfail : ∀ L : List Col, L.length ≤ T → s ∉ L → g x L ≤ ε := fun L hL hs => by
      refine hfγ L x ?_
      rw [sum_stageLaw_some]
      have hW := half_lt_total (hu x) hε0 (by linarith) hd hT' L hL hs
      rw [le_div_iff₀ hm0']
      have : (2 * (m : ℝ))⁻¹ * m = 1 / 2 := by field_simp
      linarith
    have hlow := tval_lower (hu x) (hv01 x) (hg01 x) (hgz x) hε0 (by linarith) hd hvs hT' hfail T []
      (by simp)
    have hideal := (ideal_tournament (hc x) (hu x) hm hd).2.1
    have hmiss : missFrom (a x) s T [] ≤ 2 * (m : ℝ) / 2 ^ T := by
      refine le_trans (le_of_eq ?_) hideal
      unfold missFrom prob expectAfter
      congr 1
      funext w l
      by_cases h : s ∈ l <;> simp [h]
    have hA : 0 ≤ 2 * (m : ℝ) / 2 ^ T := by positivity
    change _ ≤ tval (a x) (v x) (g x) T []
    have h1 : (1 - ε) * (1 - 2 * (m : ℝ) / 2 ^ T - T * ε) ≤
        (1 - ε) * (1 - missFrom (a x) s T [] - T * ε) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have h2 : 1 - 2 * (m : ℝ) / 2 ^ T - T * ε - ε ≤
        (1 - ε) * (1 - 2 * (m : ℝ) / 2 ^ T - T * ε) := by
      have : 0 ≤ ε * (2 * (m : ℝ) / 2 ^ T + T * ε) := by positivity
      nlinarith
    linarith

end QuarticQuery.Upper

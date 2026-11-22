module

public import QuarticQuery.Paper.QuantumTournament
public import QuarticQuery.Paper.QuantumAmplification
public import QuarticQuery.Tournament.Drift

/-!
# The identities and uniform query budget in Proposition 3.2

Compiled as part of the `QuarticQuery` library target.
`cc` counts the logical reads of `Samples`. The explicit output budget counts
ordinary bit-oracle queries, including the factor two in `compile_read`.
The final real inequality supplies a uniform constant for the paper's big-O.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Tournament QuarticQuery.Amplification

/-- Ledger: claim-coherent-access. The ordinary bit oracle as a single logical
read. This checks the input convention of the generic comparison theorem.
-/
def quantumBitRead {ι : Type} (w : ℕ) : ReadSpec ι (Basis ι w) where
  addr p := p.1
  perm p := (p.1, !p.2.1, p.2.2)
  sign _ := false
  perm_perm p := by
    rcases p with ⟨i, b, z⟩
    cases b <;> rfl
  addr_perm _ := rfl
  sign_perm _ := rfl

/-- Ledger: claim-coherent-access. The read implements the exact ordinary
bit-oracle operation from Statement.lean. -/
theorem quantumBitRead_eq {ι : Type} [Fintype ι] (w : ℕ) (x : BitInput ι) :
    (quantumBitRead (ι := ι) w).op x = bitOracleL (w := w) x := by
  ext ψ p
  rw [ReadSpec.op_apply, bitOracleL_apply, bitOracle_apply]
  rcases p with ⟨i, b, z⟩
  cases h : x i <;> simp [ReadSpec.dest, ReadSpec.coef, quantumBitRead, flipPoint, h]

/-- Ledger: claim-coherent-access. One physical bit query is admissible as one
`IsCirc` read. Query-free gates and composition are `IsCirc.gate` and
`IsCirc.comp`; a coherent comparison with c queries therefore has c reads.
-/
theorem quantumBitOracle_isCirc {ι : Type} [Fintype ι] (w : ℕ) :
    IsCirc 1 (fun x : BitInput ι => bitOracleL (w := w) x) := by
  refine IsCirc.of_eq (IsCirc.read (quantumBitRead (ι := ι) w)) ?_
  intro x ψ
  rw [quantumBitRead_eq]

/-- Ledger: def-T-eps. The exact parameters, in the source's integer logarithm
vocabulary. `Nat.clog 2 n` is the least natural T with n ≤ 2^T.
-/
theorem quantumTournament_parameters (m : ℕ) :
    Tval m = Nat.clog 2 (1000 * m) ∧
      epsval m = 1 / (1000 * (Tval m : ℝ)) := ⟨rfl, rfl⟩

/-- Ledger: eq-11. The dominant-candidate predicate says exactly (11).
-/
theorem quantumDominant_iff {Col : Type} (a : Col → Col → ℝ) (ε : ℝ) (s : Col) :
    Dominant a ε s ↔ ∀ j, j ≠ s → 1 - ε ≤ a s j := Iff.rfl

/-- Ledger: eq-13. The complete displayed drift chain for positive total weight.
Nonnegative weights are only needed to interpret the ratios as probabilities;
the algebraic equalities below hold for arbitrary real weights. -/
theorem quantumDrift {Col : Type} [Fintype Col] [DecidableEq Col]
    (w : Col → ℝ) {a : Col → Col → ℝ} (ha : IsComparison a)
    {W : ℝ} (hW : W = ∑ i, w i) (hpos : 0 < W) :
    (∑ p, (w p / W) * ∑ i, w i * a i p) =
        (1 / W) * ∑ p, ∑ i, w p * w i * a i p ∧
    (1 / W) * (∑ p, ∑ i, w p * w i * a i p) =
        (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) ∧
    (W ^ 2 - ∑ i, w i ^ 2) / (2 * W) ≤ W / 2 := by
  have hsum : (∑ p, (w p / W) * ∑ i, w i * a i p) =
      (1 / W) * ∑ p, ∑ i, w p * w i * a i p := by
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  refine ⟨hsum, hsum.symm.trans (expected_weight_eq w ha hW hpos), ?_⟩
  rw [← expected_weight_eq w ha hW hpos]
  exact expected_weight_le_half w ha hW hpos

/-- Ledger: claim-success-prob. The weight is the product of all comparison
success probabilities along the pivot history. -/
theorem quantumWeight_product {Col : Type} (a : Col → Col → ℝ) (L : List Col) (i : Col) :
    weight a L i = (L.map fun p => a i p).prod := by
  induction L with
  | nil => simp [weight]
  | cons p L ih =>
    simp only [weight, List.map_cons, List.prod_cons, ih]
    ring

/-- Ledger: claim-weight-lb. The history-length version of the surviving-weight
bound, together with positivity of total weight. -/
theorem quantumWeight_lower {Col : Type} [Fintype Col]
    {a : Col → Col → ℝ} {ε : ℝ} {s : Col} (ha : UnitValued a)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hd : Dominant a ε s)
    {T : ℕ} (hT : (T : ℝ) * ε < 1 / 2) (L : List Col)
    (hL : L.length ≤ T) (hs : s ∉ L) :
    (1 - ε) ^ L.length ≤ weight a L s ∧
    1 - (T : ℝ) * ε ≤ (1 - ε) ^ L.length ∧
    1 / 2 < weight a L s ∧ 0 < total (weight a L) := by
  have hpow := pow_le_weight ha hε1 hd L hs
  have hlen : (L.length : ℝ) * ε ≤ (T : ℝ) * ε :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hL) hε0
  have hbern : 1 - (L.length : ℝ) * ε ≤ (1 - ε) ^ L.length := by
    have h := one_add_mul_le_pow (a := -ε) (by linarith) L.length
    simpa only [sub_eq_add_neg, mul_neg] using h
  have hwt := (dominant_weight_lb ha hε0 hε1 hd hT L hL hs).2.2
  have htotal := half_lt_total ha hε0 hε1 hd hT L hL hs
  exact ⟨hpow, by linarith, hwt, by linarith⟩

/-- Ledger: claim-success-prob. Unit-valued comparisons give nonnegative
probabilities for both stage failure and every successful index. -/
theorem quantumStageLaw_nonneg {Col : Type} [Fintype Col]
    {a : Col → Col → ℝ} (ha : UnitValued a) (L : List Col) (o : Option Col) :
    0 ≤ stageLaw a L o := by
  induction L generalizing o with
  | nil =>
    cases o <;> simp only [stageLaw] <;> positivity
  | cons p L ih =>
    cases o with
    | none =>
      change 0 ≤ stageLaw a L none + ∑ i, stageLaw a L (some i) * (1 - a i p)
      refine add_nonneg (ih none) (Finset.sum_nonneg fun i _ => ?_)
      exact mul_nonneg (ih (some i)) (sub_nonneg.mpr (ha i p).2)
    | some i =>
      exact mul_nonneg (ih (some i)) (ha i p).1

/-- Ledger: claim-success-prob. Algebraic normalization of the complete stage
law, including failure. Nonnegative masses are supplied separately by
`quantumStageLaw_nonneg`. -/
theorem quantumStageLaw_total {Col : Type} [Fintype Col] [Nonempty Col]
    (a : Col → Col → ℝ) (L : List Col) : ∑ o, stageLaw a L o = 1 := by
  have hm : (Fintype.card Col : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  induction L with
  | nil =>
    rw [Fintype.sum_option]
    simp [stageLaw, Finset.card_univ, hm]
  | cons p L ih =>
    rw [Fintype.sum_option] at ih ⊢
    change stageLaw a L none + (∑ i, stageLaw a L (some i) * (1 - a i p)) +
      (∑ i, stageLaw a L (some i) * a i p) = 1
    calc
      _ = stageLaw a L none + ∑ i, stageLaw a L (some i) := by
        rw [add_assoc, ← Finset.sum_add_distrib]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring
      _ = 1 := ih

/-- Ledger: claim-success-prob. The complete stage law is a probability
distribution; its successful mass is positive, and its joint, total and
conditional successful-index probabilities have the exact paper values.
`ha` supplies positivity; `hW` makes conditioning meaningful. -/
theorem quantumStage_success {Col : Type} [Fintype Col] [Nonempty Col]
    (a : Col → Col → ℝ) (ha : UnitValued a)
    (L : List Col) (hW : 0 < total (weight a L)) :
    (∀ o, 0 ≤ stageLaw a L o) ∧
    (∑ o, stageLaw a L o) = 1 ∧
    (0 < ∑ i, stageLaw a L (some i)) ∧
    (∀ i, stageLaw a L (some i) = weight a L i / Fintype.card Col) ∧
    (∑ i, stageLaw a L (some i)) = total (weight a L) / Fintype.card Col ∧
    (∀ i, stageLaw a L (some i) / (∑ j, stageLaw a L (some j)) =
      weight a L i / total (weight a L)) := by
  have hm : (Fintype.card Col : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hmpos : (0 : ℝ) < Fintype.card Col :=
    lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hm)
  refine ⟨quantumStageLaw_nonneg ha L, quantumStageLaw_total a L, ?_,
    stageLaw_some a L, sum_stageLaw_some a L, fun i => ?_⟩
  · rw [sum_stageLaw_some]
    exact div_pos hW hmpos
  · rw [stageLaw_some, sum_stageLaw_some]
    exact div_div_div_cancel_right₀ hm _ _

/-- Ledger: construct-sampler. A coherent stage has a fixed logical read budget;
all its workspace is retained by `Samples`. Its implementation short-circuits
on a loss, so this is a successful-law statement, not literal equation (15).
-/
theorem quantumStage_samples {ι Col : Type} [Nonempty ι] [Fintype Col] [Nonempty Col]
    {cc : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b) (L : List Col) :
    Samples (L.length * cc) fun x o => stageLaw (a x) L o := stage_samples hcmp L

/-- Ledger: claim-tournament-cost. The tournament horizon is at least two.
-/
theorem quantumTval_two_le {m : ℕ} (hm : 2 ≤ m) : 2 ≤ Tval m := by
  have hpow : 1000 * m ≤ 2 ^ Tval m :=
    Nat.le_pow_clog (by norm_num) (1000 * m)
  by_contra h
  have hcases : Tval m = 0 ∨ Tval m = 1 := by omega
  rcases hcases with h0 | h1
  · rw [h0] at hpow
    norm_num at hpow
    omega
  · rw [h1] at hpow
    norm_num at hpow
    omega

/-- Ledger: claim-tournament-cost. Explicit physical bit-query bound before
simplifying the square root and logarithm. -/
theorem quantumTournament_cost_log {m : ℕ} (hm : 2 ≤ m) (cc : ℕ) :
    ((Tval m * stageCost m (Tval m) cc (epsval m) : ℕ) : ℝ) ≤
      276 * (cc : ℝ) * (Real.sqrt ((2 * (m : ℝ))⁻¹))⁻¹ *
        (Tval m : ℝ) ^ 2 * Real.log (1 / epsval m) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hγ : 0 < (2 * (m : ℝ))⁻¹ := by positivity
  have hγ1 : (2 * (m : ℝ))⁻¹ ≤ (1 / 2 : ℝ) := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : (0 : ℝ) < 2 * m)]
    linarith
  have hε0 : 0 ≤ epsval m := epsval_nonneg m
  have hTε : (Tval m : ℝ) * epsval m = 1 / 1000 := Tval_mul_epsval hm
  have hε : 0 < epsval m := by
    rcases hε0.eq_or_lt with heq | hlt
    · rw [← heq] at hTε
      norm_num at hTε
    · exact hlt
  have hε1 : epsval m < 1 / 2 := lt_of_le_of_lt (epsval_le hm) (by norm_num)
  have hB := amplification_budget_le hγ hγ1 hε hε1
  calc
    ((Tval m * stageCost m (Tval m) cc (epsval m) : ℕ) : ℝ) =
        ((trialCount (epsval m) : ℝ) *
          (2 * (iterationBound ((2 * (m : ℝ))⁻¹) : ℝ) + 1)) *
          (2 * (Tval m : ℝ) ^ 2 * (cc : ℝ)) := by
      simp only [stageCost, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring
    _ ≤ (138 * (Real.sqrt ((2 * (m : ℝ))⁻¹))⁻¹ * Real.log (1 / epsval m)) *
        (2 * (Tval m : ℝ) ^ 2 * (cc : ℝ)) :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = 276 * (cc : ℝ) * (Real.sqrt ((2 * (m : ℝ))⁻¹))⁻¹ *
        (Tval m : ℝ) ^ 2 * Real.log (1 / epsval m) := by ring

/-- Ledger: claim-tournament-cost. A uniform constant for the precise order in
Proposition 3.2. Logarithm here is natural; changing its base changes the constant.
-/
theorem quantumTournament_cost {m : ℕ} (hm : 2 ≤ m) (cc : ℕ) :
    ((Tval m * stageCost m (Tval m) cc (epsval m) : ℕ) : ℝ) ≤
      6072 * (cc : ℝ) * Real.sqrt (m : ℝ) *
        (Tval m : ℝ) ^ 2 * Real.log (Tval m : ℝ) := by
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hT : (2 : ℝ) ≤ Tval m := by exact_mod_cast quantumTval_two_le hm
  have hT0 : (0 : ℝ) < Tval m := by linarith
  have hTn : (Tval m : ℝ) ≠ 0 := ne_of_gt hT0
  have hsqrt : (Real.sqrt ((2 * (m : ℝ))⁻¹))⁻¹ ≤ 2 * Real.sqrt (m : ℝ) := by
    rw [Real.sqrt_inv, inv_inv]
    have h1 := Real.sq_sqrt (show (0 : ℝ) ≤ 2 * m by positivity)
    have h2 := Real.sq_sqrt hm0
    have hp1 := Real.sqrt_nonneg (2 * (m : ℝ))
    have hp2 := Real.sqrt_nonneg (m : ℝ)
    nlinarith
  have hlogT : 0 ≤ Real.log (Tval m : ℝ) := Real.log_nonneg (by linarith)
  have hlog2 : Real.log 2 ≤ Real.log (Tval m : ℝ) :=
    Real.log_le_log (by norm_num) hT
  have h1000 : Real.log 1000 ≤ 10 * Real.log 2 := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 1000)
      (by norm_num : (1000 : ℝ) ≤ 2 ^ (10 : ℕ))
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hinv : 1 / epsval m = 1000 * (Tval m : ℝ) := by
    unfold epsval
    field_simp
  have hlog : Real.log (1 / epsval m) ≤ 11 * Real.log (Tval m : ℝ) := by
    rw [hinv, Real.log_mul (by norm_num : (1000 : ℝ) ≠ 0) hTn]
    linarith
  have hlog0 : 0 ≤ Real.log (1 / epsval m) := by
    rw [hinv]
    apply Real.log_nonneg
    nlinarith
  have hA := quantumTournament_cost_log hm cc
  calc
    ((Tval m * stageCost m (Tval m) cc (epsval m) : ℕ) : ℝ) ≤
        276 * (cc : ℝ) * (Real.sqrt ((2 * (m : ℝ))⁻¹))⁻¹ *
          (Tval m : ℝ) ^ 2 * Real.log (1 / epsval m) := hA
    _ ≤ 276 * (cc : ℝ) * (2 * Real.sqrt (m : ℝ)) *
          (Tval m : ℝ) ^ 2 * (11 * Real.log (Tval m : ℝ)) := by
      gcongr <;> assumption
    _ = 6072 * (cc : ℝ) * Real.sqrt (m : ℝ) *
          (Tval m : ℝ) ^ 2 * Real.log (Tval m : ℝ) := by ring

/-- Ledger: prop-3.2. The paper's list probability and asymptotic query bound,
expressed by one finite integer budget and a uniform numerical upper bound.
`Runs` is the existing finite-output continuation interface; this law is chosen
before the oracle input and before the dominant candidate. -/
theorem quantumTournament {ι Col : Type} [Fintype ι] [Inhabited ι]
    [Fintype Col] [DecidableEq Col] {cc : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hm : 2 ≤ Fintype.card Col) (hc : ∀ x, IsComparison (a x))
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b) :
    let m := Fintype.card Col
    let T := Tval m
    let ε := epsval m
    ∃ C : ℕ, ∃ law : BitInput ι → QuantumCandidateList Col T → ℝ,
      (C : ℝ) ≤ 6072 * (cc : ℝ) * Real.sqrt (m : ℝ) *
        (T : ℝ) ^ 2 * Real.log (T : ℝ) ∧
      Samples (T * quantumStageReads m T cc ε) law ∧
      Runs C law ∧
      (∀ x o, 0 ≤ law x o) ∧
      (∀ x, ∑ o, law x o = 1) ∧
      ∀ x s, Dominant (a x) ε s →
        1 - 2 * (m : ℝ) / 2 ^ T - T * ε ≤
          ∑ o : QuantumCandidateList Col T, if s ∈ o.1 then law x o else 0 := by
  intro m T ε
  obtain ⟨law, hsample, hrun, hnonneg, htotal, hsuccess⟩ := quantumTournament_list hm hc hcmp
  exact ⟨T * stageCost m T cc ε, law, quantumTournament_cost hm cc,
    hsample, hrun, hnonneg, htotal, hsuccess⟩

end QuarticQuery.Paper

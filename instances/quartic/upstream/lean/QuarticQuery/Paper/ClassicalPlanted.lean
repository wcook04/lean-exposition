module

public import QuarticQuery.LowerBound.Planted.Main

/-!
# The planted experiment and the displays (18)--(23)

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

All probability expressions below are finite weighted sums under the original
product law. Nonheaviness stays inside an event. Times are zero-based: `t`
below is the paper's proposed query number `t + 1`. Column and row labels are
`Fin (2 ^ ℓ)`; a paper label `j` in `{1,...,m}` corresponds to `j - 1`.
The blank cell pattern is the fixed all-false pattern already used by `dummy`.
-/

@[expose] public section

open Finset

namespace QuarticQuery.Paper

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ℓ r S : ℕ}

/-- Ledger: def-dummy. The dummy law, represented by its expectation functional:
all address strings have product weight `μ`, all zero positions are independently
uniform, and `dummy` fixes every cell bit to false. -/
noncomputable def dummyAvg (μ : BitInput κ → ℝ)
    (g : BitInput (BitLoc ℓ r S κ) → ℝ) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J => g (dummy J A)

/-- Ledger: def-planted. The planted law adds an independent uniform column `I`
to the dummy sampling experiment and applies the already-defined planting map. -/
noncomputable def plantedAvg (μ : BitInput κ → ℝ) (f : PartialBool κ)
    (tr : BitInput κ → Fin S → Bool) (g : BitInput (BitLoc ℓ r S κ) → ℝ) : ℝ :=
  coupledAvg μ fun A J I => g (planted f tr J A I)

/-- Ledger: def-dummy. Adding the unused independent planting index does not
change the dummy expectation. -/
theorem dummyAvg_eq_coupledAvg (μ : BitInput κ → ℝ)
    (g : BitInput (BitLoc ℓ r S κ) → ℝ) :
    dummyAvg μ g = coupledAvg (ℓ := ℓ) (r := r) μ (fun A J _ => g (dummy J A)) := by
  simp only [dummyAvg, coupledAvg, avg_const (sum_unif ℓ)]

/-- Ledger: def-dummy. A normalized input weight gives a normalized dummy law. -/
theorem dummyAvg_const {μ : BitInput κ → ℝ} (hμ1 : ∑ x, μ x = 1) (c : ℝ) :
    dummyAvg (ℓ := ℓ) (r := r) (S := S) μ (fun _ => c) = c := by
  have hPA1 : ∑ A : Column ℓ → Fin r → BitInput κ, prodW (prodW μ) A = 1 :=
    sum_prodW (sum_prodW hμ1)
  simp only [dummyAvg, avg_const (sum_prodW (sum_unif ℓ)), avg_const hPA1]

/-- Ledger: def-planted. The three independent sampling stages have total mass
one. This statement makes no assumption about whether the planted input wins. -/
theorem paperCoupledAvg_const {μ : BitInput κ → ℝ} (hμ1 : ∑ x, μ x = 1) (c : ℝ) :
    coupledAvg (ℓ := ℓ) (r := r) μ (fun _ _ _ => c) = c := by
  have hPA1 : ∑ A : Column ℓ → Fin r → BitInput κ, prodW (prodW μ) A = 1 :=
    sum_prodW (sum_prodW hμ1)
  simp only [coupledAvg, avg_const (sum_unif ℓ),
    avg_const (sum_prodW (sum_unif ℓ)), avg_const hPA1]

/-- Ledger: def-planted. A normalized input weight gives a normalized planted law. -/
theorem plantedAvg_const {μ : BitInput κ → ℝ} (hμ1 : ∑ x, μ x = 1)
    (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool) (c : ℝ) :
    plantedAvg (ℓ := ℓ) (r := r) μ f tr (fun _ => c) = c :=
  paperCoupledAvg_const hμ1 c

/-- Ledger: def-dummy. Nonnegative functions have nonnegative dummy expectations. -/
theorem dummyAvg_nonneg {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    {g : BitInput (BitLoc ℓ r S κ) → ℝ} (hg : ∀ x, 0 ≤ g x) : 0 ≤ dummyAvg μ g :=
  avg_nonneg (prodW_nonneg (prodW_nonneg hμ)) fun A =>
    avg_nonneg (prodW_nonneg (unif_nonneg ℓ)) fun J => hg (dummy J A)

/-- Ledger: def-planted. Nonnegative functions have nonnegative planted expectations. -/
theorem plantedAvg_nonneg {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool)
    {g : BitInput (BitLoc ℓ r S κ) → ℝ} (hg : ∀ x, 0 ≤ g x) :
    0 ≤ plantedAvg μ f tr g :=
  avg_nonneg (prodW_nonneg (prodW_nonneg hμ)) fun A =>
    avg_nonneg (prodW_nonneg (unif_nonneg ℓ)) fun J =>
      avg_nonneg (unif_nonneg ℓ) fun I => hg (planted f tr J A I)

/-- Ledger: def-planted. Monotonicity under the explicit product sampling law. -/
theorem paperCoupledAvg_mono {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    {a b : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ}
    (h : ∀ A J I, a A J I ≤ b A J I) : coupledAvg μ a ≤ coupledAvg μ b :=
  avg_mono (prodW_nonneg (prodW_nonneg hμ)) fun A =>
    avg_mono (prodW_nonneg (unif_nonneg ℓ)) fun J => avg_mono (unif_nonneg ℓ) (h A J)

/-- Ledger: def-planted. A constant upper bound survives averaging. -/
theorem paperCoupledAvg_le_const {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    {a : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ}
    {c : ℝ} (h : ∀ A J I, a A J I ≤ c) : coupledAvg μ a ≤ c :=
  (paperCoupledAvg_mono hμ h).trans_eq (paperCoupledAvg_const hμ1 c)

/-- Ledger: def-planted. Subtraction commutes with the coupled expectation. -/
theorem paperCoupledAvg_sub (μ : BitInput κ → ℝ)
    (a b : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ) :
    coupledAvg μ (fun A J I => a A J I - b A J I) = coupledAvg μ a - coupledAvg μ b := by
  simp only [coupledAvg, avg_sub]

/-- Ledger: def-planted. Addition commutes with the coupled expectation. -/
theorem paperCoupledAvg_add (μ : BitInput κ → ℝ)
    (a b : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ) :
    coupledAvg μ (fun A J I => a A J I + b A J I) = coupledAvg μ a + coupledAvg μ b := by
  simp only [coupledAvg, avg_add]

/-- Ledger: eq-18. An absolute pointwise bound gives the absolute bound on
expectations; normalization is unnecessary for this elementary step. -/
theorem paperCoupledAvg_abs_le {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    {a b : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ}
    (h : ∀ A J I, |a A J I| ≤ b A J I) : |coupledAvg μ a| ≤ coupledAvg μ b := by
  have hupper := paperCoupledAvg_mono hμ (fun A J I => (abs_le.mp (h A J I)).2)
  have hlower := paperCoupledAvg_mono hμ (fun A J I => (abs_le.mp (h A J I)).1)
  have hneg : coupledAvg μ (fun A J I => -b A J I) = -coupledAvg μ b := by
    simp [coupledAvg, avg, mul_neg]
  rw [hneg] at hlower
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Ledger: claim-Y-values. Both Boolean values, with the support condition
needed to make every planted address a promised answer vector. -/
theorem dummy_planted_values_on_support {f : PartialBool κ} {C : Circuit κ}
    {tr : BitInput κ → Fin C.size → Bool} (htr : ∀ x, GateConsistent C x (tr x))
    {μ : BitInput κ → ℝ} (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ)
    (hA : prodW (prodW μ) A ≠ 0) :
    addressedF f C ℓ r (dummy J A) = false ∧
      addressedF f C ℓ r (planted f tr J A I) = true := by
  refine ⟨addressedF_dummy J A, addressedF_planted htr J A I ?_⟩
  intro h
  exact hdom _ (ne_zero_of_prodW_ne_zero (ne_zero_of_prodW_ne_zero hA I) h)

/-- Ledger: eq-18. The unsplit event of querying any bit of the true-address
cell, whether or not the bit's value differs from the blank pattern. -/
noncomputable def cellVisit (f : PartialBool κ) (T : QueryTree (BitLoc ℓ r S κ))
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ) : ℝ :=
  ind (∃ q ∈ T.path (dummy J A), cellOf q = some (I, trueAddr f (A I)))

/-- Ledger: eq-18. The two-sided first-difference argument, before averaging
and before splitting the cell encounter into heavy and nonheavy cases. -/
theorem output_gap_abs_le_unsplit (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool)
    (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (I : Column ℓ) :
    |ind (T.eval (planted f tr J A I) = true) - ind (T.eval (dummy J A) = true)| ≤
      foundZero T A J I + cellVisit f T J A I := by
  have hz : 0 ≤ foundZero T A J I := ind_nonneg _
  have hc : 0 ≤ cellVisit f T J A I := ind_nonneg _
  have habs : |ind (T.eval (planted f tr J A I) = true) -
      ind (T.eval (dummy J A) = true)| ≤ 1 := by
    refine abs_le.mpr ⟨?_, ?_⟩ <;>
      linarith [ind_nonneg (T.eval (planted f tr J A I) = true),
        ind_nonneg (T.eval (dummy J A) = true),
        ind_le_one (T.eval (planted f tr J A I) = true),
        ind_le_one (T.eval (dummy J A) = true)]
  by_cases he : T.eval (dummy J A) = T.eval (planted f tr J A I)
  · rw [← he, sub_self, abs_zero]
    exact add_nonneg hz hc
  obtain ⟨q, hq, hne⟩ := T.exists_mem_path_ne he
  rcases eq_of_dummy_ne_planted hne with rfl | hcell
  · have : foundZero T A J I = 1 := ind_true hq
    linarith
  · have : cellVisit f T J A I = 1 := ind_true ⟨q, hq, hcell⟩
    linarith

/-- Ledger: eq-18. The ledger's absolute-value form of (18). The printed paper
says "difference"; this symmetric packaging follows from the same coupling. -/
theorem eq_18 {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool)
    (T : QueryTree (BitLoc ℓ r S κ)) :
    |plantedAvg μ f tr (fun x => ind (T.eval x = true)) -
        dummyAvg μ (fun x => ind (T.eval x = true))| ≤
      coupledAvg μ (fun A J I => foundZero T A J I) +
        coupledAvg μ (fun A J I => cellVisit f T J A I) := by
  rw [dummyAvg_eq_coupledAvg]
  unfold plantedAvg
  have h := paperCoupledAvg_abs_le hμ (output_gap_abs_le_unsplit f tr T)
  simpa only [paperCoupledAvg_sub, paperCoupledAvg_add] using h

/-- Ledger: def-Z. The number of columns whose zero is discovered in the
complete dummy run. Repeated visits count one discovered column. -/
noncomputable def discoveredZeros (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ) (J : Column ℓ → Column ℓ) : ℕ := by
  classical
  exact (univ.filter fun i => .inl (i, J i) ∈ T.path (dummy J A)).card

/-- Ledger: def-Z. The integer-valued count agrees with the sum of the source's
per-column indicators. -/
theorem discoveredZeros_cast (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ) (J : Column ℓ → Column ℓ) :
    (discoveredZeros T A J : ℝ) = ∑ i, foundZero T A J i := by
  classical
  simpa only [discoveredZeros, foundZero, ind] using
    (Finset.natCast_card_filter (R := ℝ)
      (fun i : Column ℓ => Sum.inl (i, J i) ∈ T.path (dummy J A)) univ)

/-- Ledger: claim-EZ. Expectation of the integer-valued discovery count under
the independent address-data and zero-position sampling law. -/
noncomputable def expectedZeros (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J =>
    (discoveredZeros T A J : ℝ)

/-- Ledger: eq-19. The independent uniform planting column selects a discovered
zero with probability exactly `E Z / m`. -/
theorem erasedZero_eq_expectedZeros_div (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) :
    coupledAvg μ (fun A J I => foundZero T A J I) =
      expectedZeros μ T / ((2 ^ ℓ : ℕ) : ℝ) := by
  simp only [coupledAvg, avg_unif, ← discoveredZeros_cast, avg_mul_left, expectedZeros]
  ring

/-- Ledger: eq-19. The source's stronger coefficient two, now averaged also over
all independent address data. It is an upper bound, with no optimality claim. -/
theorem erasedZero_le_two {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    coupledAvg μ (fun A J I => foundZero T A J I) ≤
      2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 :=
  avg_le_const (prodW_nonneg (prodW_nonneg hμ)) (sum_prodW (sum_prodW hμ1))
    fun A => avg_foundZero_I_le T A hT

/-- Ledger: claim-EZ. `E Z ≤ 2G/m`, by the already-checked finite-world search
induction. This is an alternative route to the printed early/late proof. -/
theorem expectedZeros_le_two {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    expectedZeros μ T ≤ 2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := by
  have h := erasedZero_le_two hμ hμ1 T hT
  rw [erasedZero_eq_expectedZeros_div] at h
  have hm := colCard_pos ℓ
  calc expectedZeros μ T
      ≤ (2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2) * ((2 ^ ℓ : ℕ) : ℝ) :=
        (div_le_iff₀ hm).mp h
    _ = 2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := by
        field_simp [hm.ne'] <;> ring

/-- Ledger: claim-EZ. The paper's endpoint `E Z ≤ 4G/m`. The early/late
intermediate estimates are not claimed as dependencies of this proof. -/
theorem expectedZeros_le_four {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    expectedZeros μ T ≤ 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) := by
  refine (expectedZeros_le_two hμ hμ1 T hT).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (Nat.cast_nonneg G))
    (colCard_pos ℓ).le

/-- Ledger: eq-19. The paper's erased-zero display with coefficient four. -/
theorem eq_19 {μ : BitInput κ → ℝ} (hμ : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) {G : ℕ}
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    coupledAvg μ (fun A J I => foundZero T A J I) ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by
  refine (erasedZero_le_two hμ hμ1 T hT).trans ?_
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (Nat.cast_nonneg G))
    (by positivity)

/-- Ledger: def-heavy. Heaviness is a property of the complete dummy run.
All repeated queries to any of the target column's `r` strings are counted. -/
def HeavyColumn (L : ℕ) (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ) (J : Column ℓ → Column ℓ) (i : Column ℓ) : Prop :=
  L < aQueries i (T.path (dummy J A))

/-- Ledger: def-heavy. Agreement with the predicate used by the compiled source. -/
theorem heavyColumn_iff (L : ℕ) (T : QueryTree (BitLoc ℓ r S κ))
    (A : Column ℓ → Fin r → BitInput κ) (J : Column ℓ → Column ℓ) (i : Column ℓ) :
    HeavyColumn L T A J i ↔ L < aQueries i (T.path (dummy J A)) := Iff.rfl

/-- Ledger: def-simulator. At zero-based time `t`, run with at most `L` target
queries; side information answers every other query. Return the proposed cell's
address, or the all-false vector on abort, stop, or a query outside that column. -/
def addressSimulator (L t : ℕ) (T : QueryTree (BitLoc ℓ r S κ))
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (i : Column ℓ) :
    OutTree (Fin r × κ) (Address r) :=
  simTree (aTarget i) (cellGuess i) (fun _ => false) (dummy J A) T t L

/-- Ledger: def-simulator. The simulator has the stronger total query cap `L`.
The direct-product lemma only requires the resulting per-instance cap. -/
theorem addressSimulator_depth_le (L t : ℕ) (T : QueryTree (BitLoc ℓ r S κ))
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (i : Column ℓ) :
    (addressSimulator L t T J A i).depth ≤ L := depth_simTree_le T t L

/-- Ledger: eq-21. The joint event at a specified proposed query time, with
nonheaviness measured over the entire dummy run. -/
noncomputable def reachedCellAt (f : PartialBool κ) (L : ℕ)
    (T : QueryTree (BitLoc ℓ r S κ)) (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) (i : Column ℓ) (t : ℕ) : ℝ :=
  ind (¬ HeavyColumn L T A J i ∧ ∃ q, (T.path (dummy J A))[t]? = some q ∧
    cellOf q = some (i, trueAddr f (A i)))

/-- Ledger: eq-21. Per-time simulator bound with the outside information fixed.
The target strings are resampled from their original product law. -/
theorem avg_reachedCellAt_le {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {ρ : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hguess : ∀ U : OutTree (Fin r × κ) (Fin r → Bool), (U.capped fun _ => L) →
      guessSuccess f (fun _ => μ) U ≤ ρ)
    (T : QueryTree (BitLoc ℓ r S κ)) (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) (i : Column ℓ) (t : ℕ) :
    avg (prodW μ) (fun U => reachedCellAt f L T J (Function.update A i U) i t) ≤ ρ := by
  let sim := addressSimulator L t T J A i
  have hsim : sim.capped fun _ => L :=
    OutTree.capped_of_depth_le (addressSimulator_depth_le L t T J A i) fun _ => le_rfl
  calc avg (prodW μ) (fun U => reachedCellAt f L T J (Function.update A i U) i t)
      ≤ guessSuccess f (fun _ => μ) sim := by
        refine sum_le_sum fun U _ => ?_
        change prodW μ U * reachedCellAt f L T J (Function.update A i U) i t ≤
          prodW μ U *
            (if ∀ h, f (U h) = some (sim.eval (Function.uncurry U) h) then 1 else 0)
        have hnonneg : 0 ≤ prodW μ U := prodW_nonneg hμ U
        by_cases hz : prodW μ U = 0
        · simp only [hz, zero_mul, le_refl]
        have hprom : ∀ h, promised f (U h) := fun h =>
          hdom _ (ne_zero_of_prodW_ne_zero hz h)
        set x : BitInput (BitLoc ℓ r S κ) := dummy J (Function.update A i U) with hx
        by_cases hev : ¬ HeavyColumn L T (Function.update A i U) J i ∧
            ∃ q, (T.path x)[t]? = some q ∧
              cellOf q = some (i, trueAddr f (Function.update A i U i))
        · obtain ⟨hnh, q, hq, hcell⟩ := hev
          rw [Function.update_self] at hcell
          have hc : ((T.path x).take t).countP (fun q => (aTarget i q).isSome) ≤ L :=
            ((List.take_sublist t _).countP_le).trans (not_lt.mp hnh)
          have hs : sim.eval (Function.uncurry U) = trueAddr f U :=
            eval_simTree x (Function.uncurry U) (fun _ hq' => dummy_update_of_aTarget_none hq')
              (fun _ _ hq' => dummy_update_of_aTarget_some hq') T t L hq
              (cellGuess_of_cellOf hcell) hc
          have hone : ∀ h, f (U h) = some (sim.eval (Function.uncurry U) h) := fun h => by
            rw [hs]
            exact f_eq_trueAddr (hprom h)
          have hevent : reachedCellAt f L T J (Function.update A i U) i t = 1 :=
            ind_true ⟨hnh, q, hq, by rw [Function.update_self]; exact hcell⟩
          simp only [hevent, if_pos hone, mul_one, le_refl]
        · have hevent : reachedCellAt f L T J (Function.update A i U) i t = 0 :=
            ind_false hev
          rw [hevent, mul_zero]
          exact mul_nonneg hnonneg (by split_ifs <;> norm_num)
    _ ≤ ρ := hguess sim hsim

/-- Ledger: eq-21. The paper's per-column, per-time joint-event inequality under
the complete original dummy sampling law. -/
theorem eq_21 {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hard : ∀ U : QueryTree κ, U.depth ≤ L → treeSuccess f μ U ≤ 2 / 3)
    (T : QueryTree (BitLoc ℓ r S κ)) (i : Column ℓ) (t : ℕ) :
    avg (prodW (prodW μ)) (fun A => avg (prodW (unif ℓ)) fun J =>
      reachedCellAt f L T J A i t) ≤ ((2 : ℝ) / 3) ^ r := by
  rw [avg_comm]
  refine avg_le_const (prodW_nonneg (unif_nonneg ℓ)) (sum_prodW (sum_unif ℓ)) fun J => ?_
  rw [avg_resample (sum_prodW hμ1) i]
  refine avg_le_const (prodW_nonneg (prodW_nonneg hμ))
    (sum_prodW (sum_prodW hμ1)) fun A => ?_
  exact avg_reachedCellAt_le hμ hdom (fun U hU => address_guess_le hμ hard U hU) T J A i t

/-- Ledger: eq-22. The full cell event is bounded by the heavy event and the
joint nonheavy cell event. This is a pointwise union bound. -/
theorem cellVisit_le_heavy_add_reached (f : PartialBool κ) (L : ℕ)
    (T : QueryTree (BitLoc ℓ r S κ)) (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) (i : Column ℓ) :
    cellVisit f T J A i ≤ ind (HeavyColumn L T A J i) + reachedCell f L T J A i := by
  by_cases hh : HeavyColumn L T A J i
  · rw [ind_true hh]
    have hcell : cellVisit f T J A i ≤ 1 := ind_le_one _
    have hreach : 0 ≤ reachedCell f L T J A i := ind_nonneg _
    linarith
  · have heq : reachedCell f L T J A i = cellVisit f T J A i := by
      unfold reachedCell cellVisit
      apply congrArg ind
      apply propext
      exact ⟨And.right, fun h => ⟨hh, h⟩⟩
    rw [ind_false hh, zero_add, heq]

/-- Ledger: eq-22. Exact unsplit cell-encounter bound with a general capped
address-guess bound `ρ`; no conditional distribution is introduced. -/
theorem cellVisit_le {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ} {ρ : ℝ}
    (hL : 1 ≤ L) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hguess : ∀ U : OutTree (Fin r × κ) (Fin r → Bool), (U.capped fun _ => L) →
      guessSuccess f (fun _ => μ) U ≤ ρ)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    coupledAvg μ (fun A J I => cellVisit f T J A I) ≤
      (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ρ := by
  have hPA0 : ∀ A : Column ℓ → Fin r → BitInput κ, 0 ≤ prodW (prodW μ) A :=
    prodW_nonneg (prodW_nonneg hμ)
  have hPA1 : ∑ A : Column ℓ → Fin r → BitInput κ, prodW (prodW μ) A = 1 :=
    sum_prodW (sum_prodW hμ1)
  have hPJ0 := prodW_nonneg (ι := Column ℓ) (unif_nonneg ℓ)
  have hPJ1 := sum_prodW (ι := Column ℓ) (sum_unif ℓ)
  have hsplit := paperCoupledAvg_mono hμ (fun A J I =>
    cellVisit_le_heavy_add_reached f L T J A I)
  rw [paperCoupledAvg_add] at hsplit
  have hH : coupledAvg μ (fun A J I => ind (HeavyColumn L T A J I)) ≤
      (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) :=
    avg_le_const hPA0 hPA1 fun A => avg_le_const hPJ0 hPJ1 fun J =>
      avg_heavy_le hL (T.path (dummy J A)) ((T.length_path_le (dummy J A)).trans hT)
  have hN : coupledAvg μ (fun A J I => reachedCell f L T J A I) ≤ (G : ℝ) * ρ := by
    unfold coupledAvg
    rw [avg_comm]
    refine avg_le_const hPJ0 hPJ1 fun J => ?_
    rw [avg_comm]
    refine avg_le_const (unif_nonneg ℓ) (sum_unif ℓ) fun I => ?_
    rw [avg_resample (sum_prodW hμ1) I]
    exact avg_le_const hPA0 hPA1 fun A => avg_reachedCell_le hμ hdom hguess T hT J A I
  linarith

/-- Ledger: eq-22. Equation (22) with the paper's `(2/3)^r` probability. -/
theorem eq_22 {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ}
    (hL : 1 ≤ L) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hard : ∀ U : QueryTree κ, U.depth ≤ L → treeSuccess f μ U ≤ 2 / 3)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    coupledAvg μ (fun A J I => cellVisit f T J A I) ≤
      (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ((2 : ℝ) / 3) ^ r :=
  cellVisit_le hL hμ hμ1 hdom (fun U hU => address_guess_le hμ hard U hU) T hT

/-- Ledger: eq-23. Absolute probability gap, with the stronger coefficient two.
The proof packages the unsplit coupling, zero-search bound and cell bound. -/
theorem eq_23_two {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ}
    (tr : BitInput κ → Fin S → Bool) (hL : 1 ≤ L)
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hard : ∀ U : QueryTree κ, U.depth ≤ L → treeSuccess f μ U ≤ 2 / 3)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    |plantedAvg μ f tr (fun x => ind (T.eval x = true)) -
        dummyAvg μ (fun x => ind (T.eval x = true))| ≤
      2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 +
        (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ((2 : ℝ) / 3) ^ r := by
  have hc := eq_18 hμ f tr T
  have hz := erasedZero_le_two hμ hμ1 T hT
  have hcell := eq_22 hL hμ hμ1 hdom hard T hT
  linarith

/-- Ledger: eq-23. Equation (23), explicitly two-sided and at the paper's
coefficient four. The signed direction required for the contradiction follows. -/
theorem eq_23 {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ}
    (tr : BitInput κ → Fin S → Bool) (hL : 1 ≤ L)
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hard : ∀ U : QueryTree κ, U.depth ≤ L → treeSuccess f μ U ≤ 2 / 3)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    |plantedAvg μ f tr (fun x => ind (T.eval x = true)) -
        dummyAvg μ (fun x => ind (T.eval x = true))| ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 +
        (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ((2 : ℝ) / 3) ^ r := by
  have h := eq_23_two tr hL hμ hμ1 hdom hard T hT
  have h24 : 2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 :=
    div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 4) (Nat.cast_nonneg G))
      (by positivity)
  linarith


/-- Ledger: eq-23. An absolute bound is preserved by a normalized finite mixture. -/
theorem paper_avg_abs_le_const {α : Type} [Fintype α] {p g : α → ℝ} {c : ℝ}
    (hp : ∀ a, 0 ≤ p a) (hp1 : ∑ a, p a = 1) (hg : ∀ a, |g a| ≤ c) :
    |avg p g| ≤ c := by
  refine abs_le.mpr ⟨?_, ?_⟩
  · exact const_le_avg_of_ne hp hp1 fun a _ => (abs_le.mp (hg a)).1
  · exact avg_le_const hp hp1 fun a => (abs_le.mp (hg a)).2

/-- Ledger: eq-23. The same absolute probability bound for every randomized
program with worst-case query cap `G`, after averaging its fixed coins. -/
theorem eq_23_randomized {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ}
    (tr : BitInput κ → Fin S → Bool) (hL : 1 ≤ L)
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hard : ∀ U : QueryTree κ, U.depth ≤ L → treeSuccess f μ U ≤ 2 / 3)
    (P : RandomizedProgram (BitLoc ℓ r S κ)) (hP : P.depth ≤ G) :
    |plantedAvg μ f tr (fun x => P.success x true) -
        dummyAvg μ (fun x => P.success x true)| ≤
      4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 +
        (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ((2 : ℝ) / 3) ^ r := by
  let δ : ℝ := 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 +
    (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) + (G : ℝ) * ((2 : ℝ) / 3) ^ r
  have hsucc : ∀ x, avg P.weight (fun j => ind ((P.tree j).eval x = true)) =
      P.success x true := fun x => by
    refine sum_congr rfl fun j _ => ?_
    beta_reduce
    by_cases h : (P.tree j).eval x = true
    · rw [ind_true h, if_pos h, mul_one]
    · rw [ind_false h, if_neg h, mul_zero]
  have hgap : ∀ j, |coupledAvg μ (fun A J I =>
      ind ((P.tree j).eval (planted f tr J A I) = true) -
        ind ((P.tree j).eval (dummy J A) = true))| ≤ δ := by
    intro j
    have hdepth : (P.tree j).depth ≤ G :=
      (Finset.le_sup (f := fun j => (P.tree j).depth) (mem_univ j)).trans hP
    have h := eq_23 tr hL hμ hμ1 hdom hard (P.tree j) hdepth
    rw [dummyAvg_eq_coupledAvg] at h
    unfold plantedAvg at h
    rwa [← paperCoupledAvg_sub] at h
  have hmix := paper_avg_abs_le_const (fun j => (P.weight_pos j).le) P.weight_sum hgap
  have heq : (avg P.weight fun j => coupledAvg μ (fun A J I =>
      ind ((P.tree j).eval (planted f tr J A I) = true) -
        ind ((P.tree j).eval (dummy J A) = true))) =
      coupledAvg μ (fun A J I => P.success (planted f tr J A I) true -
        P.success (dummy J A) true) := by
    unfold coupledAvg
    rw [avg_comm]
    refine avg_congr fun A => ?_
    rw [avg_comm]
    refine avg_congr fun J => ?_
    rw [avg_comm]
    refine avg_congr fun I => ?_
    rw [avg_sub, hsucc, hsucc]
  rw [heq, paperCoupledAvg_sub] at hmix
  rw [dummyAvg_eq_coupledAvg]
  exact hmix

end QuarticQuery.Paper

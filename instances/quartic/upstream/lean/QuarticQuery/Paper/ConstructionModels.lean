module

public import QuarticQuery.Results.Headline

/-!
# Sections 1 and 2: the query-model definitions

Compiled as part of the `QuarticQuery` library target.
This module uses only the base development and Mathlib;
it does not import `Paper.Section2` or `ForrelationLower.Uniform`.

The definitions below translate the paper's domain-and-value presentation of a
partial function into the existing `Option Bool` presentation. The correctness
equivalences leave all behaviour outside the domain unrestricted. The oracle
statement includes the action on basis vectors, linear unitarity and inversion.
-/

public section

namespace QuarticQuery.Paper

/-! ## Equation (1) -/

/-- Ledger: eq-1. Equivalent to the paper's finite-real-constant formulation:
the constant can be chosen positive without changing the set of exponents. -/
theorem construction_universalPower_iff (α : ℝ) :
    UniversalPower α ↔
      0 ≤ α ∧ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
        (R (totalise f) : ℝ) ≤ C * Real.rpow (1 + (Q (totalise f) : ℝ)) α := by
  constructor
  · rintro ⟨hα, C, _, hC⟩
    exact ⟨hα, C, hC⟩
  · rintro ⟨hα, C, hC⟩
    refine ⟨hα, max C 1, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (le_max_right C 1), ?_⟩
    intro n hn f
    have hpow : 0 ≤ Real.rpow (1 + (Q (totalise f) : ℝ)) α :=
      Real.rpow_nonneg (by positivity) α
    exact (hC n hn f).trans
      (mul_le_mul_of_nonneg_right (le_max_left C 1) hpow)

/-- Ledger: eq-1. Verbatim infimum after the equivalent finite-constant
presentation has been substituted. Every real constant is finite. -/
theorem construction_alphaTot_eq_inf :
    alphaTot = sInf {α : ℝ | 0 ≤ α ∧ ∃ C : ℝ,
      ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
        (R (totalise f) : ℝ) ≤ C * Real.rpow (1 + (Q (totalise f) : ℝ)) α} := by
  unfold alphaTot
  congr 1
  ext α
  exact construction_universalPower_iff α

/-- Ledger: eq-1. Additional well-definedness check for the displayed infimum:
its defining set is nonempty and bounded below by zero. -/
theorem construction_exponent_set_wellDefined :
    ({α : ℝ | UniversalPower α}).Nonempty ∧
      BddBelow {α : ℝ | UniversalPower α} := by
  refine ⟨⟨4, universalPower_four⟩, ⟨0, ?_⟩⟩
  intro α hα
  exact hα.1

/-! ## Partial functions -/

open Classical in
/-- Ledger: def-partial-query. Equivalent representation of a partial Boolean
function as a domain and a value on that domain. -/
noncomputable def constructionPartial {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool) : PartialBool ι :=
  fun x => if hx : x ∈ D then some (f ⟨x, hx⟩) else none

/-- Ledger: def-partial-query. Verbatim description of the defined values in
the domain-and-value representation. -/
theorem constructionPartial_eq_some_iff {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool) (x : BitInput ι) (b : Bool) :
    constructionPartial D f x = some b ↔
      ∃ hx : x ∈ D, f ⟨x, hx⟩ = b := by
  classical
  by_cases hx : x ∈ D
  · simp only [constructionPartial, dif_pos hx, Option.some.injEq]
    constructor
    · intro h
      exact ⟨hx, h⟩
    · rintro ⟨_, h⟩
      exact h
  · simp only [constructionPartial, dif_neg hx]
    constructor
    · intro h
      cases h
    · rintro ⟨hx', _⟩
      exact (hx hx').elim

/-- Ledger: def-partial-query. Verbatim domain membership: `promised` holds
exactly on the specified domain. -/
theorem construction_promised_iff {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool) (x : BitInput ι) :
    promised (constructionPartial D f) x ↔ x ∈ D := by
  change (∃ b, constructionPartial D f x = some b) ↔ x ∈ D
  constructor
  · rintro ⟨b, hb⟩
    exact ((constructionPartial_eq_some_iff D f x b).1 hb).1
  · intro hx
    exact ⟨f ⟨x, hx⟩, (constructionPartial_eq_some_iff D f x _).2 ⟨hx, rfl⟩⟩

/-- Ledger: def-partial-query. Equivalent correctness conditions for an
arbitrary success predicate, so the translation also applies at any stated error. -/
theorem construction_correct_on_domain_iff {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool)
    (Correct : BitInput ι → Bool → Prop) :
    (∀ x b, constructionPartial D f x = some b → Correct x b) ↔
      ∀ x (hx : x ∈ D), Correct x (f ⟨x, hx⟩) := by
  constructor
  · intro h x hx
    exact h x (f ⟨x, hx⟩)
      ((constructionPartial_eq_some_iff D f x _).2 ⟨hx, rfl⟩)
  · intro h x b hb
    obtain ⟨hx, hfb⟩ := (constructionPartial_eq_some_iff D f x b).1 hb
    rw [← hfb]
    exact h x hx

/-- Ledger: def-partial-query. Verbatim randomized correctness on the domain;
the depth cap continues to range over the whole random program. -/
theorem construction_RLe_domain_iff {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool) (budget : ℕ) :
    RLe (constructionPartial D f) budget ↔
      ∃ A : RandomizedProgram ι, A.depth ≤ budget ∧
        ∀ x (hx : x ∈ D), (2 / 3 : ℝ) ≤ A.success x (f ⟨x, hx⟩) := by
  simp only [RLe, construction_correct_on_domain_iff]

/-- Ledger: def-partial-query. Verbatim deterministic correctness on the domain. -/
theorem construction_DLe_domain_iff {ι : Type}
    (D : Set (BitInput ι)) (f : D → Bool) (budget : ℕ) :
    DLe (constructionPartial D f) budget ↔
      ∃ A : QueryTree ι, A.depth ≤ budget ∧
        ∀ x (hx : x ∈ D), A.eval x = f ⟨x, hx⟩ := by
  simp only [DLe, construction_correct_on_domain_iff]

/-- Ledger: def-partial-query. Verbatim quantum correctness on the domain;
the same input-independent program has a syntactic cap on every branch. -/
theorem construction_QLe_domain_iff {ι : Type} [Fintype ι]
    (D : Set (BitInput ι)) (f : D → Bool) (budget : ℕ) :
    QLe (constructionPartial D f) budget ↔
      (∃ b : Bool, ∀ x (hx : x ∈ D), f ⟨x, hx⟩ = b) ∨
      ∃ (w : ℕ) (ψ₀ : State ι w) (A : AdaptiveProgram ι w),
        ‖ψ₀‖ = 1 ∧ A.queryCap ≤ budget ∧
        ∀ x (hx : x ∈ D), (2 / 3 : ℝ) ≤ A.outputMass x ψ₀ (f ⟨x, hx⟩) := by
  simp only [QLe, ConstantOnPromise, construction_correct_on_domain_iff]

/-- Ledger: def-partial-query. Equivalent representations in the reverse
direction: every `Option Bool` function is recovered from its domain and values. -/
theorem constructionPartial_reconstruct {ι : Type} (f : PartialBool ι) :
    constructionPartial {x | promised f x}
      (fun x => Classical.choose x.property) = f := by
  classical
  funext x
  by_cases hx : promised f x
  · have hsome := (constructionPartial_eq_some_iff {x | promised f x}
        (fun x => Classical.choose x.property) x (Classical.choose hx)).2
        ⟨hx, rfl⟩
    exact hsome.trans (Classical.choose_spec hx).symm
  · have hnone : f x = none := by
      cases hval : f x with
      | none => rfl
      | some b => exact (hx ⟨b, hval⟩).elim
    have hnot : ¬ promised
        (constructionPartial {x | promised f x} (fun x => Classical.choose x.property)) x := by
      intro h
      exact hx ((construction_promised_iff _ _ x).mp h)
    have hpartial : constructionPartial {x | promised f x}
        (fun x => Classical.choose x.property) x = none := by
      cases hval : constructionPartial {x | promised f x}
          (fun x => Classical.choose x.property) x with
      | none => rfl
      | some b => exact (hnot ⟨b, hval⟩).elim
    exact hpartial.trans hnone.symm

/-! ## The oracle -/

/-- Ledger: def-query-oracle. Verbatim basis action, self-inverse property and
unitarity, represented by a complex linear isometry equivalence. -/
theorem construction_query_oracle {ι : Type} [Fintype ι] {w : ℕ}
    (x : BitInput ι) :
    (∀ (i : ι) (b : Bool) (z : Fin (w + 1)),
      bitOracle x (ket (i, b, z)) = ket (i, xor b (x i), z)) ∧
    (∀ ψ : State ι w, bitOracle x (bitOracle x ψ) = ψ) ∧
    ∃ U : State ι w ≃ₗᵢ[ℂ] State ι w, ∀ ψ, U ψ = bitOracle x ψ := by
  refine ⟨?_, ?_, ?_⟩
  · intro i b z
    rw [bitOracle_ket]
    cases hx : x i <;> cases b <;> simp [flipPoint, hx]
  · intro ψ
    exact bitOracle_bitOracle x ψ
  · exact ⟨bitOracleL x, fun ψ => bitOracleL_apply x ψ⟩

/-! ## Logarithms -/

/-- Ledger: def-log-convention. The prose convention chooses base two;
this exact identity checks its use on the construction's powers of four. -/
theorem construction_log2_mValue (t : ℕ) :
    Real.logb 2 (mValue t : ℝ) = 2 * (t : ℝ) :=
  QuarticQuery.logb_mValue t

end QuarticQuery.Paper

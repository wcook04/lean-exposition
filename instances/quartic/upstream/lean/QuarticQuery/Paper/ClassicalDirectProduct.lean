module

public import QuarticQuery.LowerBound.DirectProduct

/-!
# The conditional-value proof in Section 4.1

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

Finite conditional probabilities are ratios of nonnegative finite weights.
Zero-mass branches have weight zero; no conditional distribution is asserted on
such a branch. The definition of `classicalValue` agrees with the attained
maximum under the normalized conditional law. Its Bellman inequality is then
multiplied by the unchanged factors, exactly as in the paper's proof.

The existing `guessSuccess_le_prod` is not used in the value or supermartingale
lemmas below. The already compiled direct-product endpoint remains available.
-/

@[expose] public section

open Finset Classical

namespace QuarticQuery.Paper

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/-- Ledger: def-value-V. Total mass of a finite one-instance weight. -/
def classicalMass (ν : BitInput κ → ℝ) : ℝ := ∑ x, ν x

/-- Ledger: def-value-V. Normalized weight, used as a probability law only when
`classicalMass ν > 0`. Division by zero supplies a harmless zero convention. -/
noncomputable def classicalLaw (ν : BitInput κ → ℝ) : BitInput κ → ℝ :=
  fun x => ν x / classicalMass ν

/-- Ledger: def-value-V. Conditional continuation value with `c` queries left.
At a transcript, take `c = L - q_h` and the restricted prior as `ν`. -/
noncomputable def classicalValue (f : PartialBool κ) (c : ℕ)
    (ν : BitInput κ → ℝ) : ℝ := budgetValue f c ν / classicalMass ν

/-- Ledger: def-value-V. Nonnegative weights have nonnegative mass. -/
theorem classicalMass_nonneg {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    0 ≤ classicalMass ν := sum_nonneg fun x _ => hν x

/-- Ledger: def-value-V. The normalized weight is a probability law on every
positive-probability transcript. -/
theorem classicalLaw_sum {ν : BitInput κ → ℝ} (hm : 0 < classicalMass ν) :
    ∑ x, classicalLaw ν x = 1 := by
  change (∑ x, ν x / classicalMass ν) = 1
  rw [← Finset.sum_div]
  exact div_self hm.ne'

/-- Ledger: def-value-V. Normalization divides every tree's success by the
same positive transcript probability. -/
theorem classical_treeSuccess_normalize (f : PartialBool κ)
    (ν : BitInput κ → ℝ) (T : QueryTree κ) :
    treeSuccess f (classicalLaw ν) T = treeSuccess f ν T / classicalMass ν := by
  unfold treeSuccess classicalLaw
  rw [Finset.sum_div]
  exact sum_congr rfl fun x _ => by ring

/-- Ledger: def-value-V. The continuation value bounds every allowed strategy. -/
theorem classicalValue_bounds_tree (f : PartialBool κ) {c : ℕ}
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x)
    (T : QueryTree κ) (hT : T.depth ≤ c) :
    treeSuccess f (classicalLaw ν) T ≤ classicalValue f c ν := by
  rw [classical_treeSuccess_normalize]
  exact div_le_div_of_nonneg_right (treeSuccess_le_budgetValue f ν hT)
    (classicalMass_nonneg hν)

/-- Ledger: def-value-V. The maximum in the paper's definition is attained;
this identifies `classicalValue`, rather than assuming its optimality. -/
theorem classicalValue_attained (f : PartialBool κ) (c : ℕ)
    (ν : BitInput κ → ℝ) :
    ∃ T : QueryTree κ, T.depth ≤ c ∧
      treeSuccess f (classicalLaw ν) T = classicalValue f c ν := by
  obtain ⟨T, hT, hle⟩ := exists_tree_budgetValue_le f c ν
  refine ⟨T, hT, ?_⟩
  rw [classical_treeSuccess_normalize]
  exact congrArg (fun a : ℝ => a / classicalMass ν)
    (le_antisymm (treeSuccess_le_budgetValue f ν hT) hle)

/-- Ledger: def-value-V. A success weight cannot exceed the total mass. -/
theorem classical_budgetValue_le_mass (f : PartialBool κ) (c : ℕ)
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    budgetValue f c ν ≤ classicalMass ν := by
  apply budgetValue_le_of_forall
  intro T _
  unfold treeSuccess classicalMass
  apply sum_le_sum
  intro x _
  split_ifs <;> simp_all

/-- Ledger: eq-16. An impossible branch has zero success value before
normalization. This is needed when cancelling its mass. -/
theorem classical_budgetValue_zero_mass (f : PartialBool κ) (c : ℕ)
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) (hm : classicalMass ν = 0) :
    budgetValue f c ν = 0 :=
  le_antisymm (by simpa [hm] using classical_budgetValue_le_mass f c hν)
    (budgetValue_nonneg f c hν)

/-- Ledger: claim-supermartingale. Each continuation value is nonnegative. -/
theorem classicalValue_nonneg (f : PartialBool κ) (c : ℕ)
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) :
    0 ≤ classicalValue f c ν :=
  div_nonneg (budgetValue_nonneg f c hν) (classicalMass_nonneg hν)

/-- Ledger: eq-16. Conditional probability of seeing bit `b` in query `q`. -/
noncomputable def classicalBranchProbability (ν : BitInput κ → ℝ)
    (q : κ) (b : Bool) : ℝ :=
  classicalMass (restrictWeight ν q b) / classicalMass ν

/-- Ledger: eq-16. A query partitions the prior mass, even with repeated
queries and zero-probability answers. -/
theorem classicalMass_split (ν : BitInput κ → ℝ) (q : κ) :
    classicalMass (restrictWeight ν q false) +
      classicalMass (restrictWeight ν q true) = classicalMass ν := by
  unfold classicalMass
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  cases hx : x q <;> simp [restrictWeight, hx]

/-- Ledger: eq-16. The two branch probabilities sum to one whenever the
current transcript has positive probability. -/
theorem classicalBranchProbability_sum (ν : BitInput κ → ℝ)
    (q : κ) (hm : 0 < classicalMass ν) :
    classicalBranchProbability ν q false + classicalBranchProbability ν q true = 1 := by
  unfold classicalBranchProbability
  rw [← add_div, classicalMass_split, div_self hm.ne']

/-- Ledger: eq-16. Branch probabilities are nonnegative. -/
theorem classicalBranchProbability_nonneg {ν : BitInput κ → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (q : κ) (b : Bool) :
    0 ≤ classicalBranchProbability ν q b :=
  div_nonneg (classicalMass_nonneg (restrictWeight_nonneg hν q b))
    (classicalMass_nonneg hν)

/-- Ledger: eq-16. Cancellation of a branch mass, including an impossible
branch. The zero branch is proved, not discarded by division. -/
theorem classical_branchValue (f : PartialBool κ) (c : ℕ)
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) (q : κ) (b : Bool) :
    classicalBranchProbability ν q b * classicalValue f c (restrictWeight ν q b) =
      budgetValue f c (restrictWeight ν q b) / classicalMass ν := by
  unfold classicalBranchProbability classicalValue
  by_cases hm : classicalMass (restrictWeight ν q b) = 0
  · rw [classical_budgetValue_zero_mass f c (restrictWeight_nonneg hν q b) hm, hm]
    simp
  · calc
      _ = (classicalMass (restrictWeight ν q b) /
            classicalMass (restrictWeight ν q b)) *
          (budgetValue f c (restrictWeight ν q b) / classicalMass ν) := by ring
      _ = _ := by rw [div_self hm, one_mul]

/-- Ledger: eq-16. Exact finite conditional-expectation form of display (16).
There is one query available now and `c` after its answer. -/
theorem classical_eq_16 (f : PartialBool κ) (c : ℕ)
    {ν : BitInput κ → ℝ} (hν : ∀ x, 0 ≤ ν x) (q : κ) :
    classicalBranchProbability ν q false *
        classicalValue f c (restrictWeight ν q false) +
      classicalBranchProbability ν q true *
        classicalValue f c (restrictWeight ν q true) ≤
      classicalValue f (c + 1) ν := by
  rw [classical_branchValue f c hν, classical_branchValue f c hν, ← add_div]
  exact div_le_div_of_nonneg_right (budgetValue_add_le f c ν q)
    (classicalMass_nonneg hν)

variable {r : ℕ}

/-- Ledger: claim-product-law. A transcript records the queried instance,
coordinate and returned bit. Repeated queries are retained. -/
abbrev ClassicalTranscript (r : ℕ) (κ : Type) := List ((Fin r × κ) × Bool)

/-- Ledger: claim-product-law. The constraints imposed on a single instance
by a fixed transcript. -/
def classicalLocalConsistent (τ : ClassicalTranscript r κ) (h : Fin r)
    (x : BitInput κ) : Prop := ∀ e ∈ τ, e.1.1 = h → x e.1.2 = e.2

/-- Ledger: claim-product-law. A transcript has this deterministic query
schedule. The next tree is chosen by the recorded answer. -/
def classicalSchedule {β : Type} :
    OutTree (Fin r × κ) β → ClassicalTranscript r κ → Prop
  | _, [] => True
  | .leaf _, _ :: _ => False
  | .query q l u, (p, b) :: τ =>
      q = p ∧ classicalSchedule (if b then u else l) τ

/-- Ledger: claim-product-law. The actual event that a deterministic tree has
the specified transcript as a prefix of its execution on `U`. -/
def classicalPrefix {β : Type} :
    OutTree (Fin r × κ) β → ClassicalTranscript r κ →
      (Fin r → BitInput κ) → Prop
  | _, [], _ => True
  | .leaf _, _ :: _, _ => False
  | .query q l u, (p, b) :: τ, U =>
      q = p ∧ U p.1 p.2 = b ∧ classicalPrefix (if b then u else l) τ U

/-- Ledger: claim-product-law. Global consistency with a new observation is
the observation together with the earlier constraints. -/
theorem classical_consistent_cons (p : Fin r × κ) (b : Bool)
    (τ : ClassicalTranscript r κ) (U : Fin r → BitInput κ) :
    (∀ h, classicalLocalConsistent ((p, b) :: τ) h (U h)) ↔
      U p.1 p.2 = b ∧ ∀ h, classicalLocalConsistent τ h (U h) := by
  constructor
  · intro h
    refine ⟨h p.1 (p, b) (by simp) rfl, ?_⟩
    intro j e he hej
    exact h j e (by simp [he]) hej
  · rintro ⟨hb, hτ⟩ j e he hej
    rcases List.mem_cons.mp he with he | he
    · subst e
      simpa only [← hej] using hb
    · exact hτ j e he hej

/-- Ledger: claim-product-law. An adaptive deterministic transcript is a
rectangle. This proves the schedule-to-constraints step. -/
theorem classical_prefix_iff {β : Type}
    (T : OutTree (Fin r × κ) β) (τ : ClassicalTranscript r κ)
    (U : Fin r → BitInput κ) :
    classicalPrefix T τ U ↔
      classicalSchedule T τ ∧ ∀ h, classicalLocalConsistent τ h (U h) := by
  induction τ generalizing T with
  | nil => simp [classicalPrefix, classicalSchedule, classicalLocalConsistent]
  | cons e τ ih =>
    rcases e with ⟨p, b⟩
    cases T with
    | leaf a => simp [classicalPrefix, classicalSchedule]
    | query q l u =>
      simp only [classicalPrefix, classicalSchedule, ih, classical_consistent_cons]
      tauto

/-- Ledger: claim-product-law. Restrict a prior to one component of the
transcript rectangle. -/
noncomputable def classicalTranscriptWeight (μ : Fin r → BitInput κ → ℝ)
    (τ : ClassicalTranscript r κ) (h : Fin r) : BitInput κ → ℝ := by
  classical
  exact fun x => if classicalLocalConsistent τ h x then μ h x else 0

/-- Ledger: claim-product-law. The probability weight of the entire
transcript rectangle factors before normalization. -/
theorem classical_rectangle_weight (μ : Fin r → BitInput κ → ℝ)
    (τ : ClassicalTranscript r κ) (U : Fin r → BitInput κ) :
    (if ∀ h, classicalLocalConsistent τ h (U h) then ∏ h, μ h (U h) else 0) =
      ∏ h, classicalTranscriptWeight μ τ h (U h) := by
  classical
  by_cases hc : ∀ h, classicalLocalConsistent τ h (U h)
  · simp [hc, classicalTranscriptWeight]
  · rw [if_neg hc]
    obtain ⟨h, hh⟩ := not_forall.mp hc
    symm
    exact prod_eq_zero (mem_univ h) (by simp [classicalTranscriptWeight, hh])

/-- Ledger: claim-product-law. The mass of a finite product weight is the
product of the individual masses. -/
theorem classical_mass_product (ν : Fin r → BitInput κ → ℝ) :
    (∑ U : Fin r → BitInput κ, ∏ h, ν h (U h)) =
      ∏ h, classicalMass (ν h) := by
  symm
  unfold classicalMass
  rw [prod_univ_sum, Fintype.piFinset_univ]

/-- Ledger: claim-product-law. Normalization of a rectangle gives the
product of the separately normalized conditional laws. The equality is
algebraic; its probabilistic use requires positive transcript mass. -/
theorem classical_product_law (ν : Fin r → BitInput κ → ℝ)
    (U : Fin r → BitInput κ) :
    (∏ h, ν h (U h)) / (∑ V : Fin r → BitInput κ, ∏ h, ν h (V h)) =
      ∏ h, classicalLaw (ν h) (U h) := by
  rw [classical_mass_product]
  simp only [classicalLaw, Finset.prod_div_distrib]

/-- Ledger: claim-product-law. The conditional joint law at an actual
positive-probability transcript of a deterministic adaptive tree. -/
theorem classical_transcript_product_law {β : Type}
    (T : OutTree (Fin r × κ) β) (τ : ClassicalTranscript r κ)
    (μ : Fin r → BitInput κ → ℝ)
    (hm : 0 < ∑ V : Fin r → BitInput κ,
      if classicalPrefix T τ V then ∏ h, μ h (V h) else 0)
    (U : Fin r → BitInput κ) :
    (if classicalPrefix T τ U then ∏ h, μ h (U h) else 0) /
        (∑ V : Fin r → BitInput κ,
          if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) =
      ∏ h, classicalLaw (classicalTranscriptWeight μ τ h) (U h) := by
  classical
  have hs : classicalSchedule T τ := by
    by_contra hn
    have hz : (∑ V : Fin r → BitInput κ,
        if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) = 0 := by
      apply sum_eq_zero
      intro V _
      rw [if_neg (fun hp => hn ((classical_prefix_iff T τ V).mp hp).1)]
    rw [hz] at hm
    exact lt_irrefl _ hm
  have hW (V : Fin r → BitInput κ) :
      (if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) =
        ∏ h, classicalTranscriptWeight μ τ h (V h) := by
    simp only [classical_prefix_iff, hs, true_and]
    exact classical_rectangle_weight μ τ V
  simp only [hW]
  exact classical_product_law (classicalTranscriptWeight μ τ) U

/-- Ledger: eq-16. Extending a transcript by an observed bit restricts
only the queried instance. This connects the finite transition to actual
transcript constraints. -/
theorem classical_transcriptWeight_append (μ : Fin r → BitInput κ → ℝ)
    (τ : ClassicalTranscript r κ) (h : Fin r) (q : κ) (b : Bool) :
    classicalTranscriptWeight μ (τ ++ [((h, q), b)]) =
      Function.update (classicalTranscriptWeight μ τ) h
        (restrictWeight (classicalTranscriptWeight μ τ h) q b) := by
  classical
  have hl (j : Fin r) (x : BitInput κ) :
      classicalLocalConsistent (τ ++ [((h, q), b)]) j x ↔
        classicalLocalConsistent τ j x ∧ (h = j → x q = b) := by
    constructor
    · intro H
      refine ⟨fun e he hej => H e (List.mem_append.mpr (Or.inl he)) hej, ?_⟩
      intro hj
      exact H ((h, q), b) (by simp) hj
    · rintro ⟨H, Hb⟩ e he hej
      rcases List.mem_append.mp he with he | he
      · exact H e he hej
      · have heq : e = ((h, q), b) := List.mem_singleton.mp he
        subst e
        exact Hb hej
  funext j x
  by_cases hj : j = h
  · subst j
    rw [Function.update_self]
    by_cases ht : classicalLocalConsistent τ h x <;>
      by_cases hb : x q = b <;>
      simp [classicalTranscriptWeight, restrictWeight, hl, ht, hb]
  · rw [Function.update_of_ne hj]
    simp [classicalTranscriptWeight, hl, Ne.symm hj]

/-- Ledger: claim-product-law. Restricted transcript weights are
nonnegative whenever the independent priors are nonnegative. -/
theorem classical_transcriptWeight_nonneg
    {μ : Fin r → BitInput κ → ℝ} (hμ : ∀ h x, 0 ≤ μ h x)
    (τ : ClassicalTranscript r κ) :
    ∀ h x, 0 ≤ classicalTranscriptWeight μ τ h x := by
  intro h x
  unfold classicalTranscriptWeight
  split_ifs
  exacts [hμ h x, le_rfl]

/-- Ledger: claim-product-law. A positive-probability actual transcript
has positive mass in every local restricted prior. Thus the positivity
needed by the product-law marginal is derived from the transcript event. -/
theorem classical_transcript_mass_pos {β : Type}
    (T : OutTree (Fin r × κ) β) (τ : ClassicalTranscript r κ)
    {μ : Fin r → BitInput κ → ℝ} (hμ : ∀ h x, 0 ≤ μ h x)
    (hm : 0 < ∑ V : Fin r → BitInput κ,
      if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) :
    ∀ h, 0 < classicalMass (classicalTranscriptWeight μ τ h) := by
  classical
  have hs : classicalSchedule T τ := by
    by_contra hn
    have hz : (∑ V : Fin r → BitInput κ,
        if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) = 0 := by
      apply sum_eq_zero
      intro V _
      rw [if_neg (fun hp => hn ((classical_prefix_iff T τ V).mp hp).1)]
    rw [hz] at hm
    exact lt_irrefl _ hm
  have hW (V : Fin r → BitInput κ) :
      (if classicalPrefix T τ V then ∏ h, μ h (V h) else 0) =
        ∏ h, classicalTranscriptWeight μ τ h (V h) := by
    simp only [classical_prefix_iff, hs, true_and]
    exact classical_rectangle_weight μ τ V
  have hp : 0 < ∏ h, classicalMass (classicalTranscriptWeight μ τ h) := by
    rw [← classical_mass_product]
    simpa only [hW] using hm
  intro h
  have hne : classicalMass (classicalTranscriptWeight μ τ h) ≠ 0 :=
    Finset.prod_ne_zero_iff.mp hp.ne' h (mem_univ h)
  exact lt_of_le_of_ne
    (classicalMass_nonneg (classical_transcriptWeight_nonneg hμ τ h)) (Ne.symm hne)

/-- Ledger: def-value-V. Number of queries to one instance in the
recorded transcript, counting repetitions. -/
def classicalQueriesTo (τ : ClassicalTranscript r κ) (h : Fin r) : ℕ :=
  (τ.filter (fun e => decide (e.1.1 = h))).length

/-- Ledger: def-value-V. The paper's `V_h(τ)` with both its transcript law
and its remaining query budget explicit. -/
noncomputable def classicalTranscriptValue (f : PartialBool κ)
    (μ : Fin r → BitInput κ → ℝ) (τ : ClassicalTranscript r κ)
    (L : ℕ) (h : Fin r) : ℝ :=
  classicalValue f (L - classicalQueriesTo τ h) (classicalTranscriptWeight μ τ h)

/-- Ledger: def-value-V. An allowed tree attains the paper's conditional
maximum at every transcript of positive probability. The equality remains
algebraically valid at the stipulated zero-mass convention. -/
theorem classicalTranscriptValue_attained (f : PartialBool κ)
    (μ : Fin r → BitInput κ → ℝ) (τ : ClassicalTranscript r κ)
    (L : ℕ) (h : Fin r) :
    ∃ T : QueryTree κ, T.depth ≤ L - classicalQueriesTo τ h ∧
      treeSuccess f (classicalLaw (classicalTranscriptWeight μ τ h)) T =
        classicalTranscriptValue f μ τ L h :=
  classicalValue_attained f _ _

/-- Ledger: def-value-V. Every allowed tree is bounded by the stated
conditional maximum. Together with attainment this proves the definition. -/
theorem classicalTranscriptValue_bounds_tree (f : PartialBool κ)
    {μ : Fin r → BitInput κ → ℝ} (hμ : ∀ h x, 0 ≤ μ h x)
    (τ : ClassicalTranscript r κ) (L : ℕ) (h : Fin r)
    (T : QueryTree κ) (hT : T.depth ≤ L - classicalQueriesTo τ h) :
    treeSuccess f (classicalLaw (classicalTranscriptWeight μ τ h)) T ≤
      classicalTranscriptValue f μ τ L h :=
  classicalValue_bounds_tree f (classical_transcriptWeight_nonneg hμ τ h) T hT

/-- Ledger: eq-16. Extending a transcript spends exactly one unit in the
queried instance, including on a repeated coordinate. -/
theorem classicalQueriesTo_append (τ : ClassicalTranscript r κ)
    (h j : Fin r) (q : κ) (b : Bool) :
    classicalQueriesTo (τ ++ [((h, q), b)]) j =
      classicalQueriesTo τ j + if h = j then 1 else 0 := by
  by_cases hj : h = j <;>
    simp [classicalQueriesTo, List.filter_append, hj]

/-- Ledger: eq-16. The remaining-budget vector changes in precisely the
same way as the budget carried by a capped tree. -/
theorem classical_budget_append (τ : ClassicalTranscript r κ)
    (L : ℕ) (h : Fin r) (q : κ) (b : Bool) :
    (fun j => L - classicalQueriesTo (τ ++ [((h, q), b)]) j) =
      Function.update (fun j => L - classicalQueriesTo τ j) h
        (L - classicalQueriesTo τ h - 1) := by
  funext j
  rw [classicalQueriesTo_append]
  by_cases hj : j = h
  · subst j
    simp [Nat.sub_sub]
  · rw [if_neg (Ne.symm hj), Function.update_of_ne hj]
    omega

/-- Ledger: eq-16. Display (16) with the actual transcript and its query
counter substituted into the conditional value. -/
theorem classical_eq_16_transcript (f : PartialBool κ)
    {μ : Fin r → BitInput κ → ℝ} (hμ : ∀ j x, 0 ≤ μ j x)
    (τ : ClassicalTranscript r κ) (L : ℕ) (h : Fin r) (q : κ)
    (hc : classicalQueriesTo τ h < L) :
    classicalBranchProbability (classicalTranscriptWeight μ τ h) q false *
        classicalTranscriptValue f μ (τ ++ [((h, q), false)]) L h +
      classicalBranchProbability (classicalTranscriptWeight μ τ h) q true *
        classicalTranscriptValue f μ (τ ++ [((h, q), true)]) L h ≤
      classicalTranscriptValue f μ τ L h := by
  have hsub : L - (classicalQueriesTo τ h + 1) = L - classicalQueriesTo τ h - 1 := by omega
  have hsucc : L - classicalQueriesTo τ h - 1 + 1 = L - classicalQueriesTo τ h := by omega
  simpa only [classicalTranscriptValue, classicalQueriesTo_append,
    ite_true, classical_transcriptWeight_append, Function.update_self, hsub, hsucc] using
    classical_eq_16 f (L - classicalQueriesTo τ h - 1)
      (classical_transcriptWeight_nonneg hμ τ h) q

/-- Ledger: eq-16. A query to instance `h` leaves every other conditional
law, budget, and continuation value unchanged. -/
theorem classicalTranscriptValue_unchanged (f : PartialBool κ)
    (μ : Fin r → BitInput κ → ℝ) (τ : ClassicalTranscript r κ)
    (L : ℕ) (h j : Fin r) (q : κ) (b : Bool) (hj : j ≠ h) :
    classicalTranscriptValue f μ (τ ++ [((h, q), b)]) L j =
      classicalTranscriptValue f μ τ L j := by
  simp [classicalTranscriptValue, classicalQueriesTo_append,
    classical_transcriptWeight_append, Function.update_of_ne hj, Ne.symm hj]

/-- Ledger: claim-supermartingale. Product of the conditional continuation
values at one state of the adaptive execution. -/
noncomputable def classicalProductValue (f : PartialBool κ)
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ) : ℝ :=
  ∏ h, classicalValue f (c h) (ν h)

/-- Ledger: eq-16. All weights remain nonnegative after one revealed bit. -/
theorem classical_update_nonneg {ν : Fin r → BitInput κ → ℝ}
    (hν : ∀ h x, 0 ≤ ν h x) (h : Fin r) (q : κ) (b : Bool) :
    ∀ j x, 0 ≤ Function.update ν h (restrictWeight (ν h) q b) j x := by
  intro j x
  by_cases hj : j = h
  · subst j
    simpa using restrictWeight_nonneg (hν h) q b x
  · simpa [Function.update_of_ne hj] using hν j x

/-- Ledger: claim-supermartingale. Exact two-branch conditional expectation
of the product: only one factor and its remaining budget change. -/
theorem classical_product_step (f : PartialBool κ)
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ)
    (hν : ∀ j x, 0 ≤ ν j x) (h : Fin r) (q : κ) (hc : 0 < c h) :
    classicalBranchProbability (ν h) q false *
        classicalProductValue f
          (Function.update ν h (restrictWeight (ν h) q false))
          (Function.update c h (c h - 1)) +
      classicalBranchProbability (ν h) q true *
        classicalProductValue f
          (Function.update ν h (restrictWeight (ν h) q true))
          (Function.update c h (c h - 1)) ≤
      classicalProductValue f ν c := by
  have hp (b : Bool) :
      classicalProductValue f (Function.update ν h (restrictWeight (ν h) q b))
          (Function.update c h (c h - 1)) =
        classicalValue f (c h - 1) (restrictWeight (ν h) q b) *
          ∏ j ∈ univ.erase h, classicalValue f (c j) (ν j) := by
    unfold classicalProductValue
    rw [← mul_prod_erase univ _ (mem_univ h), Function.update_self, Function.update_self]
    congr 1
    exact prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (ne_of_mem_erase hj),
        Function.update_of_ne (ne_of_mem_erase hj)]
  have hrest : 0 ≤ ∏ j ∈ univ.erase h, classicalValue f (c j) (ν j) :=
    prod_nonneg fun j _ => classicalValue_nonneg f _ (hν j)
  rw [hp, hp]
  calc
    _ = (classicalBranchProbability (ν h) q false *
          classicalValue f (c h - 1) (restrictWeight (ν h) q false) +
        classicalBranchProbability (ν h) q true *
          classicalValue f (c h - 1) (restrictWeight (ν h) q true)) *
          ∏ j ∈ univ.erase h, classicalValue f (c j) (ν j) := by ring
    _ ≤ classicalValue f (c h) (ν h) *
          ∏ j ∈ univ.erase h, classicalValue f (c j) (ν j) := by
      apply mul_le_mul_of_nonneg_right _ hrest
      have he := classical_eq_16 f (c h - 1) (hν h) q
      simpa only [Nat.sub_add_cancel hc] using he
    _ = classicalProductValue f ν c :=
      mul_prod_erase univ (fun j => classicalValue f (c j) (ν j)) (mem_univ h)

/-- Ledger: claim-product-law. Taking a marginal of the normalized
product law gives the separately normalized law of that instance. -/
theorem classical_product_marginal
    (ν : Fin r → BitInput κ → ℝ)
    (hm : ∀ j, 0 < classicalMass (ν j))
    (h : Fin r) (E : BitInput κ → ℝ) :
    (∑ U : Fin r → BitInput κ,
      (∏ j, classicalLaw (ν j) (U j)) * E (U h)) =
      ∑ x, classicalLaw (ν h) x * E x := by
  let w : Fin r → BitInput κ → ℝ :=
    Function.update (fun j => classicalLaw (ν j)) h
      (fun x => classicalLaw (ν h) x * E x)
  have hw (U : Fin r → BitInput κ) :
      (∏ j, w j (U j)) = (∏ j, classicalLaw (ν j) (U j)) * E (U h) := by
    rw [← mul_prod_erase univ _ (mem_univ h),
      ← mul_prod_erase univ (fun j => classicalLaw (ν j) (U j)) (mem_univ h)]
    have he : (∏ j ∈ univ.erase h, w j (U j)) =
        ∏ j ∈ univ.erase h, classicalLaw (ν j) (U j) := by
      apply prod_congr rfl
      intro j hj
      simp only [w, Function.update_of_ne (ne_of_mem_erase hj)]
    rw [he]
    simp only [w, Function.update_self]
    ring
  calc
    _ = ∑ U : Fin r → BitInput κ, ∏ j, w j (U j) :=
      sum_congr rfl fun U _ => (hw U).symm
    _ = ∏ j, classicalMass (w j) := classical_mass_product w
    _ = classicalMass (w h) * ∏ j ∈ univ.erase h, classicalMass (w j) :=
      (mul_prod_erase univ (fun j => classicalMass (w j)) (mem_univ h)).symm
    _ = ∑ x, classicalLaw (ν h) x * E x := by
      have he : (∏ j ∈ univ.erase h, classicalMass (w j)) = 1 := by
        apply prod_eq_one
        intro j hj
        change classicalMass
          (Function.update (fun i => classicalLaw (ν i)) h
            (fun x => classicalLaw (ν h) x * E x) j) = 1
        rw [Function.update_of_ne (ne_of_mem_erase hj)]
        exact classicalLaw_sum (hm j)
      rw [he, mul_one]
      simp only [w, Function.update_self, classicalMass]

/-- Ledger: eq-16. The scalar two-branch formula is the ordinary finite
expectation under the current conditional law. -/
theorem classical_two_branch_expectation (ν : BitInput κ → ℝ)
    (q : κ) (a b : ℝ) :
    (∑ x, classicalLaw ν x * (if x q then b else a)) =
      classicalBranchProbability ν q false * a +
        classicalBranchProbability ν q true * b := by
  unfold classicalLaw classicalBranchProbability classicalMass
  simp only [Finset.sum_div, Finset.sum_mul]
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro x _
  cases hx : x q <;> simp [restrictWeight, hx]

/-- Ledger: claim-supermartingale. The local product inequality as a
finite conditional expectation over the actual product conditional law.
This connects the two-branch arithmetic to the displayed expectation. -/
theorem classical_product_conditional_expectation (f : PartialBool κ)
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ)
    (hν : ∀ j x, 0 ≤ ν j x) (hm : ∀ j, 0 < classicalMass (ν j))
    (h : Fin r) (q : κ) (hc : 0 < c h) :
    (∑ U : Fin r → BitInput κ, (∏ j, classicalLaw (ν j) (U j)) *
      classicalProductValue f
        (Function.update ν h (restrictWeight (ν h) q (U h q)))
        (Function.update c h (c h - 1))) ≤
      classicalProductValue f ν c := by
  rw [classical_product_marginal ν hm h (fun x =>
    classicalProductValue f
      (Function.update ν h (restrictWeight (ν h) q (x q)))
      (Function.update c h (c h - 1)))]
  have he (x : BitInput κ) :
      classicalProductValue f
        (Function.update ν h (restrictWeight (ν h) q (x q)))
        (Function.update c h (c h - 1)) =
      (if x q then
        classicalProductValue f
          (Function.update ν h (restrictWeight (ν h) q true))
          (Function.update c h (c h - 1)) else
        classicalProductValue f
          (Function.update ν h (restrictWeight (ν h) q false))
          (Function.update c h (c h - 1))) := by
    cases x q <;> rfl
  simp only [he]
  rw [classical_two_branch_expectation]
  exact classical_product_step f ν c hν h q hc

/-- Ledger: claim-supermartingale. The paper's conditional product
inequality with the actual execution-prefix event in the conditional law
and the actual transcript values in the integrand. It holds for every query
with remaining budget, hence for the deterministic tree's next query. -/
theorem classical_transcript_conditional_expectation {β : Type}
    (T : OutTree (Fin r × κ) β) (f : PartialBool κ)
    {μ : Fin r → BitInput κ → ℝ} (hμ : ∀ j x, 0 ≤ μ j x)
    (τ : ClassicalTranscript r κ) (L : ℕ) (h : Fin r) (q : κ)
    (hm : 0 < ∑ V : Fin r → BitInput κ,
      if classicalPrefix T τ V then ∏ j, μ j (V j) else 0)
    (hc : classicalQueriesTo τ h < L) :
    (∑ U : Fin r → BitInput κ,
      ((if classicalPrefix T τ U then ∏ j, μ j (U j) else 0) /
        (∑ V : Fin r → BitInput κ,
          if classicalPrefix T τ V then ∏ j, μ j (V j) else 0)) *
        (∏ j, classicalTranscriptValue f μ (τ ++ [((h, q), U h q)]) L j)) ≤
      ∏ j, classicalTranscriptValue f μ τ L j := by
  classical
  have hlocal := classical_transcript_mass_pos T τ hμ hm
  have hpot (b : Bool) :
      (∏ j, classicalTranscriptValue f μ (τ ++ [((h, q), b)]) L j) =
        classicalProductValue f
          (Function.update (classicalTranscriptWeight μ τ) h
            (restrictWeight (classicalTranscriptWeight μ τ h) q b))
          (Function.update (fun j => L - classicalQueriesTo τ j) h
            (L - classicalQueriesTo τ h - 1)) := by
    change classicalProductValue f (classicalTranscriptWeight μ (τ ++ [((h, q), b)]))
      (fun j => L - classicalQueriesTo (τ ++ [((h, q), b)]) j) = _
    rw [classical_transcriptWeight_append, classical_budget_append]
  calc
    _ = ∑ U : Fin r → BitInput κ,
        (∏ j, classicalLaw (classicalTranscriptWeight μ τ j) (U j)) *
          classicalProductValue f
            (Function.update (classicalTranscriptWeight μ τ) h
              (restrictWeight (classicalTranscriptWeight μ τ h) q (U h q)))
            (Function.update (fun j => L - classicalQueriesTo τ j) h
              (L - classicalQueriesTo τ h - 1)) := by
      apply sum_congr rfl
      intro U _
      rw [classical_transcript_product_law T τ μ hm U, hpot]
    _ ≤ _ := classical_product_conditional_expectation f (classicalTranscriptWeight μ τ)
      (fun j => L - classicalQueriesTo τ j)
      (classical_transcriptWeight_nonneg hμ τ) hlocal h q (by omega)

/-- Ledger: claim-supermartingale. The finite expectation of the product
at termination, obtained by conditioning on each next answer. Leaves include
early stops and keep the values unchanged. -/
noncomputable def classicalTerminalValue (f : PartialBool κ) :
    OutTree (Fin r × κ) (Fin r → Bool) →
      (Fin r → BitInput κ → ℝ) → (Fin r → ℕ) → ℝ
  | .leaf _, ν, c => classicalProductValue f ν c
  | .query (h, q) l u, ν, c =>
      classicalBranchProbability (ν h) q false *
        classicalTerminalValue f l
          (Function.update ν h (restrictWeight (ν h) q false))
          (Function.update c h (c h - 1)) +
      classicalBranchProbability (ν h) q true *
        classicalTerminalValue f u
          (Function.update ν h (restrictWeight (ν h) q true))
          (Function.update c h (c h - 1))

/-- Ledger: claim-supermartingale. Iterating the conditional inequality
bounds the expected terminal product by the initial product. This proof uses
the preceding conditional inequality, not `guessSuccess_le_prod`. -/
theorem classical_terminalValue_le (f : PartialBool κ)
    (T : OutTree (Fin r × κ) (Fin r → Bool))
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ)
    (hν : ∀ h x, 0 ≤ ν h x) (hT : T.capped c) :
    classicalTerminalValue f T ν c ≤ classicalProductValue f ν c := by
  induction T generalizing ν c with
  | leaf _ => exact le_rfl
  | query p l u ihl ihu =>
    rcases p with ⟨h, q⟩
    rcases hT with ⟨hc, hl, hu⟩
    apply le_trans _ (classical_product_step f ν c hν h q hc)
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (ihl _ _ (classical_update_nonneg hν h q false) hl)
        (classicalBranchProbability_nonneg (hν h) q false))
      (mul_le_mul_of_nonneg_left
        (ihu _ _ (classical_update_nonneg hν h q true) hu)
        (classicalBranchProbability_nonneg (hν h) q true))

/-- Ledger: claim-supermartingale. The per-instance query caps bound the
total depth by the sum of the remaining budgets. -/
theorem classical_capped_depth {β : Type}
    (T : OutTree (Fin r × κ) β) (c : Fin r → ℕ) (hT : T.capped c) :
    T.depth ≤ ∑ h, c h := by
  induction T generalizing c with
  | leaf _ => exact Nat.zero_le _
  | query p l u ihl ihu =>
    rcases p with ⟨h, q⟩
    rcases hT with ⟨hc, hl, hu⟩
    change 0 < c h at hc
    change l.capped (Function.update c h (c h - 1)) at hl
    change u.capped (Function.update c h (c h - 1)) at hu
    have hsum :
        (∑ j, Function.update c h (c h - 1) j) + 1 = ∑ j, c j := by
      rw [← add_sum_erase univ _ (mem_univ h),
        ← add_sum_erase univ c (mem_univ h), Function.update_self]
      have he : (∑ j ∈ univ.erase h, Function.update c h (c h - 1) j) =
          ∑ j ∈ univ.erase h, c j := by
        apply sum_congr rfl
        intro j hj
        rw [Function.update_of_ne (ne_of_mem_erase hj)]
      rw [he]
      omega
    have hleft := ihl _ hl
    have hright := ihu _ hu
    simp only [OutTree.depth]
    omega

/-- Ledger: claim-supermartingale. With a separate cap `L`, the process
has at most `r * L` query steps; an earlier stop can be kept constant. -/
theorem classical_capped_depth_uniform {β : Type}
    (T : OutTree (Fin r × κ) β) (L : ℕ) (hT : T.capped fun _ => L) :
    T.depth ≤ r * L := by
  simpa using classical_capped_depth T (fun _ => L) hT

/-- Ledger: claim-final-bound. Conditional success at a leaf is at most the
product of the best separate constant guesses, itself at most the product
of the allowed continuation values. -/
theorem classical_final_bound (f : PartialBool κ)
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ)
    (hν : ∀ h x, 0 ≤ ν h x) (s : Fin r → Bool) :
    guessSuccess f (fun h => classicalLaw (ν h)) (.leaf s) ≤
        ∏ h, max (constSuccess f (classicalLaw (ν h)) false)
          (constSuccess f (classicalLaw (ν h)) true) ∧
      (∏ h, max (constSuccess f (classicalLaw (ν h)) false)
          (constSuccess f (classicalLaw (ν h)) true)) ≤
        classicalProductValue f ν c := by
  have hn (h : Fin r) (x : BitInput κ) : 0 ≤ classicalLaw (ν h) x :=
    div_nonneg (hν h x) (classicalMass_nonneg (hν h))
  constructor
  · rw [guessSuccess_leaf]
    apply prod_le_prod₀ (fun h _ => constSuccess_nonneg f (hn h) (s h))
    intro h _
    cases s h
    · exact le_max_left _ _
    · exact le_max_right _ _
  · apply prod_le_prod₀
      (fun h _ => (constSuccess_nonneg f (hn h) false).trans (le_max_left _ _))
    intro h _
    apply max_le
    · exact classicalValue_bounds_tree f (hν h) (.leaf false) (Nat.zero_le _)
    · exact classicalValue_bounds_tree f (hν h) (.leaf true) (Nat.zero_le _)

/-- Ledger: eq-16. A nonnegative zero-mass weight vanishes pointwise. -/
theorem classical_weight_zero_of_mass_zero {ν : BitInput κ → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (hm : classicalMass ν = 0) (x : BitInput κ) :
    ν x = 0 := by
  have hx : ν x ≤ classicalMass ν :=
    single_le_sum (fun y _ => hν y) (mem_univ x)
  exact le_antisymm (by simpa [hm] using hx) (hν x)

/-- Ledger: eq-16. Conditioning and one-bit restriction agree pointwise,
including branches of probability zero. -/
theorem classical_restrict_law {ν : BitInput κ → ℝ}
    (hν : ∀ x, 0 ≤ ν x) (q : κ) (b : Bool) (x : BitInput κ) :
    restrictWeight (classicalLaw ν) q b x =
      classicalBranchProbability ν q b * classicalLaw (restrictWeight ν q b) x := by
  have hr : restrictWeight (classicalLaw ν) q b x =
      restrictWeight ν q b x / classicalMass ν := by
    unfold restrictWeight classicalLaw
    split_ifs <;> simp
  rw [hr]
  unfold classicalBranchProbability classicalLaw
  by_cases hm : classicalMass (restrictWeight ν q b) = 0
  · rw [classical_weight_zero_of_mass_zero (restrictWeight_nonneg hν q b) hm x, hm]
    simp
  · calc
      _ = (classicalMass (restrictWeight ν q b) /
          classicalMass (restrictWeight ν q b)) *
          (restrictWeight ν q b x / classicalMass ν) := by rw [div_self hm, one_mul]
      _ = _ := by ring

/-- Ledger: claim-supermartingale. Scaling one instance weight scales
joint success by the same factor. -/
theorem classical_guessSuccess_scale (f : PartialBool κ)
    (T : OutTree (Fin r × κ) (Fin r → Bool))
    (ν : Fin r → BitInput κ → ℝ) (h : Fin r)
    (a : ℝ) (w : BitInput κ → ℝ) :
    guessSuccess f (Function.update ν h (fun x => a * w x)) T =
      a * guessSuccess f (Function.update ν h w) T := by
  unfold guessSuccess
  rw [mul_sum]
  apply sum_congr rfl
  intro U _
  have hp : (∏ j, Function.update ν h (fun x => a * w x) j (U j)) =
      a * ∏ j, Function.update ν h w j (U j) := by
    rw [← mul_prod_erase univ _ (mem_univ h),
      ← mul_prod_erase univ (fun j => Function.update ν h w j (U j)) (mem_univ h),
      Function.update_self, Function.update_self]
    have he :
        (∏ j ∈ univ.erase h, Function.update ν h (fun x => a * w x) j (U j)) =
        ∏ j ∈ univ.erase h, Function.update ν h w j (U j) := by
      apply prod_congr rfl
      intro j hj
      rw [Function.update_of_ne (ne_of_mem_erase hj),
        Function.update_of_ne (ne_of_mem_erase hj)]
    rw [he]
    ring
  rw [hp]
  ring

/-- Ledger: claim-supermartingale. Actual normalized success has the same
conditional split as the product-value process. -/
theorem classical_guessSuccess_query (f : PartialBool κ)
    (ν : Fin r → BitInput κ → ℝ) (hν : ∀ j x, 0 ≤ ν j x)
    (h : Fin r) (q : κ) (l u : OutTree (Fin r × κ) (Fin r → Bool)) :
    guessSuccess f (fun j => classicalLaw (ν j)) (.query (h, q) l u) =
      classicalBranchProbability (ν h) q false *
        guessSuccess f (fun j => classicalLaw
          (Function.update ν h (restrictWeight (ν h) q false) j)) l +
      classicalBranchProbability (ν h) q true *
        guessSuccess f (fun j => classicalLaw
          (Function.update ν h (restrictWeight (ν h) q true) j)) u := by
  have hu (b : Bool) :
      Function.update (fun j => classicalLaw (ν j)) h
          (restrictWeight (classicalLaw (ν h)) q b) =
      Function.update (fun j => classicalLaw (ν j)) h
          (fun x => classicalBranchProbability (ν h) q b *
            classicalLaw (restrictWeight (ν h) q b) x) := by
    funext j x
    by_cases hj : j = h
    · subst j
      simp only [Function.update_self]
      exact classical_restrict_law (hν h) q b x
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  have hl (b : Bool) :
      Function.update (fun j => classicalLaw (ν j)) h
          (classicalLaw (restrictWeight (ν h) q b)) =
      (fun j => classicalLaw (Function.update ν h (restrictWeight (ν h) q b) j)) := by
    funext j x
    by_cases hj : j = h
    · subst j
      simp only [Function.update_self]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj]
  rw [guessSuccess_query, hu, hu,
    classical_guessSuccess_scale, classical_guessSuccess_scale, hl, hl]

/-- Ledger: claim-final-bound. The actual execution's success probability
is bounded by the expected terminal product. This is the missing semantic
bridge between a recursive potential and the real algorithm. -/
theorem classical_success_le_terminal (f : PartialBool κ)
    (T : OutTree (Fin r × κ) (Fin r → Bool))
    (ν : Fin r → BitInput κ → ℝ) (c : Fin r → ℕ)
    (hν : ∀ j x, 0 ≤ ν j x) (hT : T.capped c) :
    guessSuccess f (fun j => classicalLaw (ν j)) T ≤
      classicalTerminalValue f T ν c := by
  induction T generalizing ν c with
  | leaf s =>
    exact (classical_final_bound f ν c hν s).1.trans
      (classical_final_bound f ν c hν s).2
  | query p l u ihl ihu =>
    rcases p with ⟨h, q⟩
    rcases hT with ⟨_, hl, hu⟩
    rw [classical_guessSuccess_query f ν hν, classicalTerminalValue]
    exact add_le_add
      (mul_le_mul_of_nonneg_left
        (ihl _ _ (classical_update_nonneg hν h q false) hl)
        (classicalBranchProbability_nonneg (hν h) q false))
      (mul_le_mul_of_nonneg_left
        (ihu _ _ (classical_update_nonneg hν h q true) hu)
        (classicalBranchProbability_nonneg (hν h) q true))

/-- Ledger: lem-4.1. The capped direct-product endpoint by the paper's
conditional-value route. The prior has mass one. The previously compiled
weighted direct-product theorem is not used in this proof. -/
theorem classical_direct_product {f : PartialBool κ} {μ : BitInput κ → ℝ}
    {L : ℕ} {β : ℝ} (hμ : ∀ x, 0 ≤ μ x) (hμ1 : classicalMass μ = 1)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    (T : OutTree (Fin r × κ) (Fin r → Bool)) (hT : T.capped fun _ => L) :
    guessSuccess f (fun _ => μ) T ≤ β ^ r := by
  have hLaw : classicalLaw μ = μ := by
    funext x
    simp [classicalLaw, hμ1]
  calc
    _ = guessSuccess f (fun _ : Fin r => classicalLaw μ) T := by rw [hLaw]
    _ ≤ classicalTerminalValue f T (fun _ => μ) (fun _ => L) :=
      classical_success_le_terminal f T _ _ (fun _ => hμ) hT
    _ ≤ classicalProductValue f (fun _ : Fin r => μ) (fun _ => L) :=
      classical_terminalValue_le f T _ _ (fun _ => hμ) hT
    _ ≤ ∏ _ : Fin r, β := by
      apply prod_le_prod₀ (fun _ _ => classicalValue_nonneg f L hμ)
      intro j _
      simpa only [classicalValue, hμ1, div_one] using budgetValue_le_of_forall hard
    _ = β ^ r := by simp

/-- Ledger: lem-4.1. Averaging the paper-route proof over independent
finite side information and all internal coins preserves the bound. -/
theorem classical_direct_product_average {S : Type} [Fintype S]
    {f : PartialBool κ} {μ : BitInput κ → ℝ} {L : ℕ} {β : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hμ1 : classicalMass μ = 1)
    (hard : ∀ T : QueryTree κ, T.depth ≤ L → treeSuccess f μ T ≤ β)
    {p : S → ℝ} (hp : ∀ s, 0 ≤ p s) (hp1 : ∑ s, p s = 1)
    (T : S → OutTree (Fin r × κ) (Fin r → Bool))
    (hT : ∀ s, (T s).capped fun _ => L) :
    ∑ s, p s * guessSuccess f (fun _ => μ) (T s) ≤ β ^ r := by
  calc
    _ ≤ ∑ s, p s * β ^ r := sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (classical_direct_product hμ hμ1 hard _ (hT s)) (hp s)
    _ = β ^ r := by rw [← sum_mul, hp1, one_mul]

/-- Ledger: eq-17. The corrected record is the definition of the integer
budget. Its lower-bound assertion belongs separately to Proposition 4.2. -/
theorem classical_eq_17 (m L : ℕ) : Gvalue m L = m * L / 100 := rfl

/-- Ledger: eq-17. The same definitional budget written with exactly the
paper's real quotient and natural floor. -/
theorem classical_eq_17_floor (m L : ℕ) :
    Gvalue m L = ⌊(m : ℝ) * (L : ℝ) / 100⌋₊ := by
  simpa only [Gvalue, Nat.cast_mul, Nat.cast_ofNat] using
    (Nat.floor_div_eq_div (K := ℝ) (m * L) 100).symm

end QuarticQuery.Paper

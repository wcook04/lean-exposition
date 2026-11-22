module

public import QuarticQuery.Paper.ClassicalPlanted

/-!
# Conditional uniformity of an undiscovered zero

Compiled as part of the `QuarticQuery` library target.
Toolchain: leanprover/lean4:v4.36.0-rc2, with the repository's lake manifest.

A transcript records the queried coordinates and their answers. Its scheduling
predicate is defined recursively from the actual decision tree. The proof below
factors the likelihood of that concrete transcript, then divides only when the
transcript has positive probability. It includes the full address data and all
other zero positions in the averaged sample space.
-/

@[expose] public section

open Finset

namespace QuarticQuery.Paper

/-- Ledger: claim-uniform-zero. The proposed queries in a transcript must follow
the tree branches selected by the recorded answers. -/
def prefixSchedule {ι : Type} : QueryTree ι → List (ι × Bool) → Prop
  | _, [] => True
  | .leaf _, _ :: _ => False
  | .query q l u, (p, b) :: τ => p = q ∧ prefixSchedule (if b then u else l) τ

/-- Ledger: claim-uniform-zero. Exact transcript-prefix event: the schedule is
legal and every recorded answer agrees with the input. -/
def observedPrefix {ι : Type} (T : QueryTree ι) (τ : List (ι × Bool)) (x : BitInput ι) : Prop :=
  prefixSchedule T τ ∧ ∀ qb ∈ τ, x qb.1 = qb.2

/-- Ledger: claim-uniform-zero. The event definition obeys the actual next-query
semantics, including its answer-dependent continuation. -/
theorem observedPrefix_query_cons {ι : Type} (q p : ι) (l u : QueryTree ι)
    (b : Bool) (τ : List (ι × Bool)) (x : BitInput ι) :
    observedPrefix (.query q l u) ((p, b) :: τ) x ↔
      p = q ∧ x q = b ∧ observedPrefix (if b then u else l) τ x := by
  constructor
  · rintro ⟨⟨hp, hs⟩, ha⟩
    subst p
    exact ⟨rfl, ha (q, b) (by simp), hs, fun qb hqb => ha qb (by simp [hqb])⟩
  · rintro ⟨hp, hx, hs, ha⟩
    subst p
    refine ⟨⟨rfl, hs⟩, ?_⟩
    intro qb hqb
    rcases List.mem_cons.mp hqb with h | h
    · subst h
      exact hx
    · exact ha qb h

/-- Ledger: claim-uniform-zero. No nonempty query transcript can be produced by
a leaf. Together with the preceding recursion this pins down the event. -/
theorem observedPrefix_leaf_cons {ι : Type} (b : Bool) (qb : ι × Bool)
    (τ : List (ι × Bool)) (x : BitInput ι) :
    ¬ observedPrefix (.leaf b) (qb :: τ) x := by
  intro h
  exact h.1

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ℓ r S : ℕ}

/-- Ledger: claim-uniform-zero. Positions of column `i` absent from the entire
recorded query list; repeated queries remove a position only once. -/
noncomputable def unqueriedRows (i : Column ℓ) (τ : List (BitLoc ℓ r S κ × Bool)) :
    Finset (Column ℓ) := by
  classical
  exact univ.filter fun j : Column ℓ => ∀ b : Bool, (.inl (i, j), b) ∉ τ

/-- Ledger: claim-uniform-zero. Before the zero in column `i` is discovered,
every recorded answer from `X_i` is true. -/
def NoZeroSeen (i : Column ℓ) (τ : List (BitLoc ℓ r S κ × Bool)) : Prop :=
  ∀ j b, (.inl (i, j), b) ∈ τ → b = true

/-- Ledger: claim-uniform-zero. A reference input for which column `i` is all
ones. It is only a likelihood-factorization device; all other bits are dummy. -/
def allOneDummy (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ)
    (i : Column ℓ) (q : BitLoc ℓ r S κ) : Bool :=
  if xColumn i q then true else dummy J A q

/-- Ledger: claim-uniform-zero. Replacing the hidden zero by a zero at `j`
changes the all-one reference only at the single bit `(i,j)`. -/
theorem allOneDummy_eq_update_of_ne (J : Column ℓ → Column ℓ)
    (A : Column ℓ → Fin r → BitInput κ) (i j : Column ℓ)
    (q : BitLoc ℓ r S κ) (hq : q ≠ .inl (i, j)) :
    allOneDummy J A i q = dummy (Function.update J i j) A q := by
  rcases q with ⟨c, p⟩ | q
  · by_cases hc : c = i
    · subst hc
      have hp : p ≠ j := by intro hp; exact hq (by rw [hp])
      simp [allOneDummy, xColumn, dummy, hp]
    · simp [allOneDummy, xColumn, dummy, hc, Function.update_of_ne hc]
  · rcases q with ⟨c, h, a⟩ | q
    · rfl
    · rfl

/-- Ledger: claim-uniform-zero. The concrete transcript's likelihood separates
into the unqueried-position constraint and a factor independent of the proposed
zero position. No posterior-uniformity assumption appears here. -/
theorem observedPrefix_dummy_fiber (T : QueryTree (BitLoc ℓ r S κ))
    (τ : List (BitLoc ℓ r S κ × Bool)) (i : Column ℓ) (hτ : NoZeroSeen i τ)
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (j : Column ℓ) :
    observedPrefix T τ (dummy (Function.update J i j) A) ↔
      j ∈ unqueriedRows i τ ∧ observedPrefix T τ (allOneDummy J A i) := by
  classical
  have hne_of_mem : ∀ (hmem : j ∈ unqueriedRows i τ) (qb : BitLoc ℓ r S κ × Bool),
      qb ∈ τ → qb.1 ≠ .inl (i, j) := by
    intro hmem qb hqb heq
    have hmissing : ∀ b, (.inl (i, j), b) ∉ τ := by simpa [unqueriedRows] using hmem
    apply hmissing qb.2
    have hpair : qb = (.inl (i, j), qb.2) := by
      apply Prod.ext
      · exact heq
      · rfl
    rwa [← hpair]
  constructor
  · rintro ⟨hs, ha⟩
    have hmissing : ∀ b, (.inl (i, j), b) ∉ τ := by
      intro b hb
      have hbtrue := hτ j b hb
      have hans := ha (.inl (i, j), b) hb
      simp [dummy, hbtrue] at hans
    have hmem : j ∈ unqueriedRows i τ := by simpa [unqueriedRows] using hmissing
    refine ⟨hmem, hs, ?_⟩
    intro qb hqb
    rw [allOneDummy_eq_update_of_ne J A i j qb.1 (hne_of_mem hmem qb hqb)]
    exact ha qb hqb
  · rintro ⟨hmem, hs, ha⟩
    refine ⟨hs, ?_⟩
    intro qb hqb
    rw [← allOneDummy_eq_update_of_ne J A i j qb.1 (hne_of_mem hmem qb hqb)]
    exact ha qb hqb

/-- Ledger: claim-uniform-zero. Sum of finite-set membership indicators. -/
theorem sum_ind_mem {α : Type} [Fintype α] [DecidableEq α] (U : Finset α) :
    ∑ j : α, ind (j ∈ U) = (U.card : ℝ) := by
  calc ∑ j : α, ind (j ∈ U) = ∑ j ∈ U, ind (j ∈ U) := by
        symm
        exact sum_subset (subset_univ U) fun j _ hj => ind_false hj
    _ = ∑ _j ∈ U, (1 : ℝ) := sum_congr rfl fun j hj => ind_true hj
    _ = (U.card : ℝ) := by simp

/-- Ledger: claim-uniform-zero. Uniform probability of the rectangular event
`j ∈ U` together with a fixed outside-data event. -/
theorem unif_mem_event (U : Finset (Column ℓ)) (H : Prop) :
    avg (unif ℓ) (fun j => ind (j ∈ U ∧ H)) =
      (U.card : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) * ind H := by
  classical
  by_cases hH : H
  · have heq : ∀ j, ind (j ∈ U ∧ H) = ind (j ∈ U) := fun j => by simp [ind, hH]
    rw [avg_congr heq, avg_unif, sum_ind_mem, ind_true hH]
    ring
  · have heq : ∀ j, ind (j ∈ U ∧ H) = 0 := fun j => by simp [ind, hH]
    rw [avg_congr heq, avg_const (sum_unif ℓ), ind_false hH]
    simp

/-- Ledger: claim-uniform-zero. The corresponding numerator with the hidden
position specified as `p`. -/
theorem unif_mem_event_eq (U : Finset (Column ℓ)) (H : Prop) (p : Column ℓ) :
    avg (unif ℓ) (fun j => ind ((j ∈ U ∧ H) ∧ j = p)) =
      (1 / ((2 ^ ℓ : ℕ) : ℝ)) * ind (p ∈ U) * ind H := by
  classical
  rw [avg_unif]
  have hsum : ∑ j : Column ℓ, ind ((j ∈ U ∧ H) ∧ j = p) = ind (p ∈ U) * ind H := by
    rw [sum_eq_single p]
    · by_cases hp : p ∈ U <;> by_cases hH : H <;> simp [ind, hp, hH]
    · intro j _ hj
      exact ind_false (fun h => hj h.2)
    · simp
  rw [hsum]
  ring

/-- Ledger: claim-uniform-zero. The probability of a full adaptive transcript
prefix in the dummy experiment, before choosing the irrelevant planting column. -/
noncomputable def dummyTraceMass (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) (τ : List (BitLoc ℓ r S κ × Bool)) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J =>
    ind (observedPrefix T τ (dummy J A))

/-- Ledger: claim-uniform-zero. The joint probability of the transcript and the
specified zero position in column `i`. -/
noncomputable def dummyTraceZeroMass (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) (τ : List (BitLoc ℓ r S κ × Bool))
    (i p : Column ℓ) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J =>
    ind (observedPrefix T τ (dummy J A) ∧ J i = p)

/-- Ledger: claim-uniform-zero. The outside-data likelihood factor. It depends
on the observed transcript and all independent outside variables. -/
noncomputable def referenceTraceMass (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) (τ : List (BitLoc ℓ r S κ × Bool))
    (i : Column ℓ) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J =>
    ind (observedPrefix T τ (allOneDummy J A i))

/-- Ledger: claim-uniform-zero. The denominator likelihood factors as
`(# unqueried positions / m)` times the outside-data likelihood. -/
theorem dummyTraceMass_factor (μ : BitInput κ → ℝ) (T : QueryTree (BitLoc ℓ r S κ))
    (τ : List (BitLoc ℓ r S κ × Bool)) (i : Column ℓ) (hτ : NoZeroSeen i τ) :
    dummyTraceMass μ T τ =
      ((unqueriedRows i τ).card : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) * referenceTraceMass μ T τ i := by
  unfold dummyTraceMass referenceTraceMass
  have hinner : ∀ A : Column ℓ → Fin r → BitInput κ,
      (avg (prodW (unif ℓ)) fun J => ind (observedPrefix T τ (dummy J A))) =
      ((unqueriedRows i τ).card : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) *
        avg (prodW (unif ℓ)) (fun J => ind (observedPrefix T τ (allOneDummy J A i))) := by
    intro A
    rw [avg_resample (sum_unif ℓ) i]
    calc (avg (prodW (unif ℓ)) fun J => avg (unif ℓ) fun j =>
          ind (observedPrefix T τ (dummy (Function.update J i j) A)))
        = avg (prodW (unif ℓ)) (fun J =>
            ((unqueriedRows i τ).card : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) *
              ind (observedPrefix T τ (allOneDummy J A i))) := by
          refine avg_congr fun J => ?_
          simp only [observedPrefix_dummy_fiber T τ i hτ J A]
          exact unif_mem_event _ _
      _ = _ := avg_mul_left _ _ _
  simp only [hinner, avg_mul_left]

/-- Ledger: claim-uniform-zero. The numerator likelihood is constant on the
unqueried positions and zero on all queried positions. -/
theorem dummyTraceZeroMass_factor (μ : BitInput κ → ℝ)
    (T : QueryTree (BitLoc ℓ r S κ)) (τ : List (BitLoc ℓ r S κ × Bool))
    (i p : Column ℓ) (hτ : NoZeroSeen i τ) :
    dummyTraceZeroMass μ T τ i p =
      (1 / ((2 ^ ℓ : ℕ) : ℝ)) * ind (p ∈ unqueriedRows i τ) * referenceTraceMass μ T τ i := by
  unfold dummyTraceZeroMass referenceTraceMass
  have hinner : ∀ A : Column ℓ → Fin r → BitInput κ,
      (avg (prodW (unif ℓ)) fun J => ind (observedPrefix T τ (dummy J A) ∧ J i = p)) =
      (1 / ((2 ^ ℓ : ℕ) : ℝ)) * ind (p ∈ unqueriedRows i τ) *
        avg (prodW (unif ℓ)) (fun J => ind (observedPrefix T τ (allOneDummy J A i))) := by
    intro A
    rw [avg_resample (sum_unif ℓ) i]
    calc (avg (prodW (unif ℓ)) fun J => avg (unif ℓ) fun j =>
          ind (observedPrefix T τ (dummy (Function.update J i j) A) ∧
            Function.update J i j i = p))
        = avg (prodW (unif ℓ)) (fun J =>
            ((1 / ((2 ^ ℓ : ℕ) : ℝ)) * ind (p ∈ unqueriedRows i τ)) *
              ind (observedPrefix T τ (allOneDummy J A i))) := by
          refine avg_congr fun J => ?_
          simp only [Function.update_self, observedPrefix_dummy_fiber T τ i hτ J A]
          exact unif_mem_event_eq _ _ _
      _ = _ := avg_mul_left _ _ _
  simp only [hinner, avg_mul_left]

/-- Ledger: claim-uniform-zero. Conditional on a positive-probability full
adaptive transcript in which column `i`'s zero has not appeared, its zero is
uniform among the as-yet unqueried positions. The conditioning denominator is
explicit, so no event of probability zero is silently conditioned upon. -/
theorem uniform_zero_given_transcript (μ : BitInput κ → ℝ)
    (_hμ : ∀ x, 0 ≤ μ x) (_hμ1 : ∑ x, μ x = 1)
    (T : QueryTree (BitLoc ℓ r S κ)) (τ : List (BitLoc ℓ r S κ × Bool))
    (i p : Column ℓ) (hτ : NoZeroSeen i τ) (hpos : 0 < dummyTraceMass μ T τ) :
    dummyTraceZeroMass μ T τ i p / dummyTraceMass μ T τ =
      if p ∈ unqueriedRows i τ then 1 / ((unqueriedRows i τ).card : ℝ) else 0 := by
  classical
  have hm : (((2 ^ ℓ : ℕ) : ℝ)) ≠ 0 := (colCard_pos ℓ).ne'
  have hreference : referenceTraceMass μ T τ i ≠ 0 := by
    intro hz
    rw [dummyTraceMass_factor μ T τ i hτ, hz, mul_zero] at hpos
    exact (lt_irrefl 0) hpos
  by_cases hp : p ∈ unqueriedRows i τ
  · have hcardNat : 0 < (unqueriedRows i τ).card := card_pos.mpr ⟨p, hp⟩
    have hcard : ((unqueriedRows i τ).card : ℝ) ≠ 0 := by exact_mod_cast hcardNat.ne'
    rw [if_pos hp, dummyTraceZeroMass_factor μ T τ i p hτ,
      dummyTraceMass_factor μ T τ i hτ, ind_true hp]
    field_simp [hm, hcard, hreference] <;> ring
  · rw [if_neg hp, dummyTraceZeroMass_factor μ T τ i p hτ, ind_false hp]
    simp

end QuarticQuery.Paper

module

public import QuarticQuery.Statement

/-!
# The optimal power

Section 5 of the nearly quartic separation preprint. The heart is the quantifier
order: `k` is chosen from `α`, then `m = 4 ^ t` grows. The analysis is pure real
arithmetic, so complexity theory enters only through `FamilyBoundsAt`, which
packages equation (2) for one fixed `k`.

Everything here is conditional on that package, on the upper bound
`UniversalPower 4`, and on the reindexing invariance of `R` and `Q`, each taken
as a named hypothesis. The finite facts at the end feed Proposition 4.2.
-/

public section

namespace QuarticQuery

open Filter Asymptotics

/-! ## Exponentials beat polynomials -/

/-- `K * (2 t) ^ e` is eventually below `2 ^ (ε t)`. -/
theorem eventually_poly_lt_exp (K e ε : ℝ) (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ t : ℕ in atTop, K * (2 * (t : ℝ)) ^ e < (2 : ℝ) ^ (ε * t) := by
  have ha : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos one_lt_two)
  have hc : 0 < K * (2 : ℝ) ^ e := mul_pos hK (Real.rpow_pos_of_pos two_pos _)
  have ho := (isLittleO_rpow_exp_pos_mul_atTop e ha).def
    (c := 1 / (2 * (K * (2 : ℝ) ^ e))) (by positivity)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually ho,
    eventually_ge_atTop 1] with t ht ht1
  have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hexp : (2 : ℝ) ^ (ε * t) = Real.exp (ε * Real.log 2 * t) := by
    rw [Real.rpow_def_of_pos two_pos]
    congr 1
    ring
  have hE : 0 < Real.exp (ε * Real.log 2 * t) := Real.exp_pos _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg ht0 _), Real.norm_of_nonneg hE.le] at ht
  rw [hexp, Real.mul_rpow two_pos.le ht0]
  calc K * ((2 : ℝ) ^ e * (t : ℝ) ^ e) = (K * (2 : ℝ) ^ e) * (t : ℝ) ^ e := by ring
    _ ≤ (K * (2 : ℝ) ^ e) * (1 / (2 * (K * (2 : ℝ) ^ e)) * Real.exp (ε * Real.log 2 * t)) :=
        mul_le_mul_of_nonneg_left ht hc.le
    _ = Real.exp (ε * Real.log 2 * t) / 2 := by field_simp
    _ < Real.exp (ε * Real.log 2 * t) := by linarith

/-- The abstract gap, uniform in the two values: past a threshold depending only
on the constants, the bounds force `r > D (1 + q) ^ α`. -/
theorem exists_threshold_gap {c C D s α : ℝ} (b : ℕ)
    (hc : 0 < c) (hC : 0 < C) (hD : 0 < D) (hα : 0 ≤ α) (hs : α / 2 < s) :
    ∃ T : ℕ, ∀ t, T ≤ t → ∀ r q : ℝ, 0 ≤ q →
      q ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b →
      c * ((4 : ℝ) ^ t) ^ s / (2 * (t : ℝ)) ^ 2 ≤ r →
      D * (1 + q) ^ α < r := by
  have hε : 0 < 2 * s - α := by linarith
  have hC1 : 0 < 1 + C := by linarith
  have hK : 0 < D * (1 + C) ^ α / c := by positivity
  obtain ⟨T, hT⟩ := eventually_atTop.1
    ((eventually_poly_lt_exp _ (2 + (b : ℝ) * α) _ hK hε).and (eventually_ge_atTop 1))
  refine ⟨T, fun t ht r q hq hqle hrge => ?_⟩
  obtain ⟨hkey, ht1⟩ := hT t ht
  have ht1' : (1 : ℝ) ≤ t := by exact_mod_cast ht1
  set W : ℝ := 2 * (t : ℝ) with hW
  have hW1 : 1 ≤ W := by rw [hW]; linarith
  have hW0 : 0 < W := by linarith
  have hP1 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ one_le_two
  have hA1 : (1 : ℝ) ≤ 2 ^ t * W ^ b := one_le_mul_of_one_le_of_one_le hP1 (one_le_pow₀ hW1)
  have hbase : 1 + q ≤ (1 + C) * ((2 : ℝ) ^ t * W ^ b) := by nlinarith
  have hpow : (1 + q) ^ α ≤ (1 + C) ^ α * (((2 : ℝ) ^ t) ^ α * (W ^ b) ^ α) := by
    calc (1 + q) ^ α ≤ ((1 + C) * ((2 : ℝ) ^ t * W ^ b)) ^ α :=
          Real.rpow_le_rpow (by linarith) hbase hα
      _ = _ := by
          rw [Real.mul_rpow hC1.le (by positivity), Real.mul_rpow (by positivity) (by positivity)]
  have hPα : ((2 : ℝ) ^ t) ^ α = (2 : ℝ) ^ (α * t) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    congr 1
    ring
  have hWb : (W ^ b) ^ α = W ^ ((b : ℝ) * α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hW0.le]
  have hsplit : ((4 : ℝ) ^ t) ^ s = (2 : ℝ) ^ (α * t) * (2 : ℝ) ^ ((2 * s - α) * t) := by
    rw [← Real.rpow_add two_pos, show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul,
      ← Real.rpow_natCast, ← Real.rpow_mul two_pos.le]
    congr 1
    push_cast
    ring
  have hWe : W ^ (2 + (b : ℝ) * α) = W ^ 2 * W ^ ((b : ℝ) * α) := by
    rw [Real.rpow_add hW0, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [hWe] at hkey
  set Pa : ℝ := (2 : ℝ) ^ (α * t) with hPa
  set E : ℝ := (2 : ℝ) ^ ((2 * s - α) * t) with hE
  set Y : ℝ := W ^ ((b : ℝ) * α) with hY
  set Z : ℝ := (1 + C) ^ α with hZ
  have hPapos : 0 < Pa := Real.rpow_pos_of_pos two_pos _
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hW0 _
  have hZpos : 0 < Z := Real.rpow_pos_of_pos hC1 _
  rw [hPα, hWb] at hpow
  rw [hsplit] at hrge
  have hkey' : D * Z * (W ^ 2 * Y) < c * E := by
    have := mul_lt_mul_of_pos_right hkey hc
    have hne := hc.ne'
    calc D * Z * (W ^ 2 * Y) = D * Z / c * (W ^ 2 * Y) * c := by field_simp
      _ < E * c := this
      _ = c * E := by ring
  have hlt : D * (Z * (Pa * Y)) < c * (Pa * E) / W ^ 2 := by
    rw [lt_div_iff₀ (by positivity)]
    calc D * (Z * (Pa * Y)) * W ^ 2 = Pa * (D * Z * (W ^ 2 * Y)) := by ring
      _ < Pa * (c * E) := mul_lt_mul_of_pos_left hkey' hPapos
      _ = c * (Pa * E) := by ring
  calc D * (1 + q) ^ α ≤ D * (Z * (Pa * Y)) := mul_le_mul_of_nonneg_left hpow hD.le
    _ < c * (Pa * E) / W ^ 2 := hlt
    _ ≤ r := hrge

/-- Ledger: claim-exponent-ratio. Abstract sequences with `Q_t ≲ 2 ^ t (2 t) ^ b`
and `R_t ≳ (4 ^ t) ^ s / (2 t) ^ 2` eventually beat `D (1 + Q_t) ^ α` whenever
`s > α / 2`. -/
theorem eventually_gt_rpow {c C D s α : ℝ} (b : ℕ) {Rt Qt : ℕ → ℝ}
    (hc : 0 < c) (hC : 0 < C) (hD : 0 < D) (hα : 0 ≤ α) (hs : α / 2 < s)
    (hQ0 : ∀ t, 0 ≤ Qt t)
    (hQ : ∀ᶠ t : ℕ in atTop, Qt t ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b)
    (hR : ∀ᶠ t : ℕ in atTop, c * ((4 : ℝ) ^ t) ^ s / (2 * (t : ℝ)) ^ 2 ≤ Rt t) :
    ∀ᶠ t : ℕ in atTop, D * (1 + Qt t) ^ α < Rt t := by
  obtain ⟨T, hT⟩ := exists_threshold_gap b hc hC hD hα hs
  filter_upwards [hQ, hR, eventually_ge_atTop T] with t h1 h2 h3
  exact hT t h3 _ _ (hQ0 t) h1 h2

/-! ## Exponent arithmetic -/

/-- The power of `1 + Q` forced by the family at `k`. -/
@[expose] noncomputable def familyExponent (k : ℕ) : ℝ := 4 - 2 / (k : ℝ)

theorem familyExponent_two : familyExponent 2 = 3 := by norm_num [familyExponent]
theorem familyExponent_three : familyExponent 3 = 10 / 3 := by norm_num [familyExponent]
theorem familyExponent_four : familyExponent 4 = 7 / 2 := by norm_num [familyExponent]

theorem familyExponent_lt_four {k : ℕ} (hk : 0 < k) : familyExponent k < 4 := by
  have : (0 : ℝ) < 2 / (k : ℝ) := by positivity
  simp only [familyExponent]
  linarith

theorem familyExponent_tendsto : Tendsto familyExponent atTop (nhds 4) := by
  have h : Tendsto (fun k : ℕ => (2 : ℝ) / (k : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h' : Tendsto (fun k : ℕ => (4 : ℝ) - 2 / (k : ℝ)) atTop (nhds (4 - 0)) := h.const_sub 4
  rw [sub_zero] at h'
  exact h'

/-- `2 - 1 / k > α / 2` says exactly that `4 - 2 / k` exceeds `α`. -/
theorem half_lt_iff_lt_familyExponent {α : ℝ} {k : ℕ} :
    α / 2 < 2 - 1 / (k : ℝ) ↔ α < familyExponent k := by
  simp only [familyExponent]
  constructor <;> intro h
  · have : 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
    linarith
  · have : 2 / (k : ℝ) = 2 * (1 / (k : ℝ)) := by ring
    linarith

/-- Ledger: claim-exponent-ratio. Each `α < 4` is beaten by some fixed `k ≥ 2`. -/
theorem exists_nat_exponent {α : ℝ} (hα : α < 4) :
    ∃ k : ℕ, 2 ≤ k ∧ α / 2 < 2 - 1 / (k : ℝ) := by
  obtain ⟨k, hk⟩ := ((familyExponent_tendsto.eventually (lt_mem_nhds hα)).and
    (eventually_ge_atTop 2)).exists
  exact ⟨k, hk.2, half_lt_iff_lt_familyExponent.2 hk.1⟩

/-! ## The family package -/

/-- Equation (2) at one `k`: a single circuit realising `P k t` carries both the
quantum upper bound and the randomized lower bound. -/
@[expose] def FamilyBoundsAt (k : ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∃ b t₀ : ℕ, ∀ t, t₀ ≤ t →
    ∃ Cir : Circuit (ForrelationCoord k t), CircuitRealises Cir (P k t) ∧
      (Q (totalise (Fkm k t Cir)) : ℝ) ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
      c * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤
        (R (totalise (Fkm k t Cir)) : ℝ)

/-- Equation (2) for every fixed `k ≥ 2`. -/
@[expose] def FamilyBounds : Prop := ∀ k : ℕ, 2 ≤ k → FamilyBoundsAt k

instance bitLoc_nonempty (ℓ r S : ℕ) (κ : Type) : Nonempty (BitLoc ℓ r S κ) :=
  ⟨.inl (⟨0, Nat.two_pow_pos ℓ⟩, ⟨0, Nat.two_pow_pos ℓ⟩)⟩

/-- A universal bound over `Fin n` holds on any nonempty finite coordinate type. -/
theorem transport_bound
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    {D α : ℝ}
    (h : ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ D * Real.rpow (1 + (Q (totalise f) : ℝ)) α)
    {ι : Type} [Fintype ι] [Nonempty ι] (f : TotalBool ι) :
    (R (totalise f) : ℝ) ≤ D * Real.rpow (1 + (Q (totalise f) : ℝ)) α := by
  let e := Fintype.equivFin ι
  let g : TotalBool (Fin (Fintype.card ι)) := fun x => f fun i => x (e i)
  have hg : totalise g = reindex e (totalise f) := rfl
  have := h _ Fintype.card_pos g
  rwa [hg, hRreindex, hQreindex] at this

/-- Ledger: claim-no-smaller-exponent. One fixed `k` already excludes every
constant `D` at each `α` with `2 - 1 / k > α / 2`. -/
theorem not_bound_of_familyBoundsAt
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    {k : ℕ} {α D : ℝ} (hfam : FamilyBoundsAt k) (hα : 0 ≤ α)
    (hs : α / 2 < 2 - 1 / (k : ℝ)) (hD : 0 < D) :
    ¬ ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ D * Real.rpow (1 + (Q (totalise f) : ℝ)) α := by
  intro hbound
  obtain ⟨c, C, hc, hC, b, t₀, hfam⟩ := hfam
  obtain ⟨T, hT⟩ := exists_threshold_gap b hc hC hD hα hs
  obtain ⟨Cir, -, hQle, hRge⟩ := hfam (max T t₀) (le_max_right _ _)
  have hgap := hT _ (le_max_left _ _) _ _ (Nat.cast_nonneg _) hQle hRge
  exact absurd (transport_bound hRreindex hQreindex hbound (Fkm k (max T t₀) Cir)) (not_le.2 hgap)

/-- Ledger: claim-no-smaller-exponent. The finite form: a single `k` with
`2 - 1 / k > α / 2` refutes `UniversalPower α`. -/
theorem not_universalPower_of_familyBoundsAt
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    {k : ℕ} {α : ℝ} (hfam : FamilyBoundsAt k) (hs : α / 2 < 2 - 1 / (k : ℝ)) :
    ¬ UniversalPower α := by
  rintro ⟨hα, D, hD, hbound⟩
  exact not_bound_of_familyBoundsAt hRreindex hQreindex hfam hα hs hD hbound

/-- Ledger: claim-no-smaller-exponent. No exponent below four is universal. -/
theorem not_universalPower_of_family
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    (hfam : FamilyBounds) {α : ℝ} (hα : α < 4) : ¬ UniversalPower α := by
  obtain ⟨k, hk, hs⟩ := exists_nat_exponent hα
  exact not_universalPower_of_familyBoundsAt hRreindex hQreindex (hfam k hk) hs

/-- Ledger: thm-1.1. `α_tot = 4`, from the family, the upper bound at four and
reindexing invariance. Every member of the set is at least four and four is a
member, so no monotonicity is needed. -/
theorem alphaTot_eq_four_of
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    (hfam : FamilyBounds) (hupper : UniversalPower 4) : alphaTot = 4 := by
  have hleast : IsLeast {α : ℝ | UniversalPower α} 4 := ⟨hupper, fun α hα => by
    by_contra hlt
    exact not_universalPower_of_family hRreindex hQreindex hfam (not_le.1 hlt) hα⟩
  exact hleast.csInf_eq

/-- Ledger: cor-cubic-refuted. With the shift: no `C` gives
`R ≤ C (1 + Q) ^ 3`. Here `k = 3` and `5 / 3 > 3 / 2`; no use of `Q ≥ 1` or of the
upper bound. -/
theorem cubic_refuted
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    (hfam : FamilyBoundsAt 3) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (1 + (Q (totalise f) : ℝ)) ^ 3 := by
  rintro ⟨C, hC⟩
  refine not_bound_of_familyBoundsAt hRreindex hQreindex (k := 3) (α := 3) (D := max C 1)
    hfam (by norm_num) (by norm_num) (by positivity) fun n hn f => ?_
  have h3 : Real.rpow (1 + (Q (totalise f) : ℝ)) 3 = (1 + (Q (totalise f) : ℝ)) ^ 3 := by
    rw [Real.rpow_eq_pow, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [h3]
  exact (hC n hn f).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

/-- Ledger: cor-cubic-refuted. The bare form of [3, Conjecture 2]: no `C` gives
`R ≤ C Q ^ 3`, because `Q ^ 3 ≤ (1 + Q) ^ 3`. -/
theorem cubic_refuted_bare
    (hRreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      R (reindex e f) = R f)
    (hQreindex : ∀ (ι κ : Type) [Fintype ι] [Fintype κ] (e : ι ≃ κ) (f : PartialBool ι),
      Q (reindex e f) = Q f)
    (hfam : FamilyBoundsAt 3) :
    ¬ ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n → ∀ f : TotalBool (Fin n),
      (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 := by
  rintro ⟨C, hC⟩
  refine cubic_refuted hRreindex hQreindex hfam ⟨max C 1, fun n hn f => ?_⟩
  have hQ0 : (0 : ℝ) ≤ Q (totalise f) := Nat.cast_nonneg _
  calc (R (totalise f) : ℝ) ≤ C * (Q (totalise f) : ℝ) ^ 3 := hC n hn f
    _ ≤ max C 1 * (Q (totalise f) : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
    _ ≤ max C 1 * (1 + (Q (totalise f) : ℝ)) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 (by linarith) 3) (by positivity)

/-! ## Finite parameter facts -/

theorem mValue_cast (t : ℕ) : (mValue t : ℝ) = (4 : ℝ) ^ t := by
  simp [mValue, pow_mul]

theorem mValue_eq_pow_four (t : ℕ) : mValue t = 4 ^ t := by
  simp [mValue, pow_mul]

/-- Ledger: eq-6. `log₂ m = 2 t`. -/
theorem logb_mValue (t : ℕ) : Real.logb 2 (mValue t : ℝ) = 2 * (t : ℝ) := by
  have : (mValue t : ℝ) = (2 : ℝ) ^ (2 * t) := by simp [mValue]
  rw [this, Real.logb_pow, Real.logb_self_eq_one one_lt_two]
  push_cast
  ring

/-- `L` with the logarithm evaluated. -/
theorem Lvalue_eq (k t : ℕ) :
    Lvalue k t = ⌊((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2⌋₊ := by
  rw [Lvalue, logb_mValue, mValue_cast, Real.rpow_eq_pow]

theorem four_mul_sq_le_two_pow {t : ℕ} (ht : 8 ≤ t) : 4 * t ^ 2 ≤ 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      rw [pow_succ 2 n]
      nlinarith

/-- `(2 t) ^ 2 ≤ m ^ (1 - 1 / k)` from `t = 8`, the first point where `L ≥ 1`
at `k = 2`. -/
theorem sq_le_rpow {k t : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t) :
    (2 * (t : ℝ)) ^ 2 ≤ ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) := by
  have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hhalf : (1 : ℝ) / 2 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le two_pos hk'
    linarith
  have hroot : ((4 : ℝ) ^ t) ^ ((1 : ℝ) / 2) = (2 : ℝ) ^ t := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, ← pow_mul, pow_mul', ← Real.sqrt_eq_rpow,
      Real.sqrt_sq (by positivity)]
  have h4 : (1 : ℝ) ≤ (4 : ℝ) ^ t := one_le_pow₀ (by norm_num)
  have hnat : (4 * (t : ℝ) ^ 2) ≤ (2 : ℝ) ^ t := by
    exact_mod_cast four_mul_sq_le_two_pow ht
  calc (2 * (t : ℝ)) ^ 2 = 4 * (t : ℝ) ^ 2 := by ring
    _ ≤ (2 : ℝ) ^ t := hnat
    _ = ((4 : ℝ) ^ t) ^ ((1 : ℝ) / 2) := hroot.symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le h4 hhalf

/-- `1 ≤ L` from `t = 8`, for every `k ≥ 2`. -/
theorem one_le_Lvalue {k t : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t) : 1 ≤ Lvalue k t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  rw [Lvalue_eq, Nat.one_le_floor_iff, one_le_div (by positivity)]
  exact sq_le_rpow hk ht

/-- `L ≤ m` for `t ≥ 1` and `k ≥ 1`. -/
theorem Lvalue_le_mValue {k t : ℕ} (hk : 1 ≤ k) (ht : 1 ≤ t) : Lvalue k t ≤ mValue t := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hW : (1 : ℝ) ≤ (2 * (t : ℝ)) ^ 2 := one_le_pow₀ (by linarith)
  have hm : (1 : ℝ) ≤ (4 : ℝ) ^ t := one_le_pow₀ (by norm_num)
  have hexp : 1 - 1 / (k : ℝ) ≤ 1 := by
    have : 0 ≤ 1 / (k : ℝ) := by positivity
    linarith
  have hx : ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤ (mValue t : ℝ) := by
    rw [mValue_cast]
    calc ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2
        ≤ ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) :=
          div_le_self (by positivity) hW
      _ ≤ ((4 : ℝ) ^ t) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hm hexp
      _ = (4 : ℝ) ^ t := Real.rpow_one _
  rw [Lvalue_eq]
  exact_mod_cast (Nat.floor_le_of_le hx)

/-- Ledger: claim-floor. Floor removal with explicit constant `1 / 400`: the
first floor costs a factor two since `x ≥ 1`, the second since `m L ≥ 200`. -/
theorem Gvalue_ge {k t : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t) :
    (1 / 400 : ℝ) * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤
      (Gvalue (mValue t) (Lvalue k t) : ℝ) := by
  have ht0 : (0 : ℝ) < t := by exact_mod_cast (by omega : 0 < t)
  have hL1 := one_le_Lvalue hk ht
  have hm8 : 200 ≤ mValue t := by
    rw [mValue_eq_pow_four]
    calc 200 ≤ 4 ^ 8 := by norm_num
      _ ≤ 4 ^ t := Nat.pow_le_pow_right (by norm_num) ht
  have hpos4 : (0 : ℝ) < (4 : ℝ) ^ t := by positivity
  set x : ℝ := ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 with hx
  have hx1 : 1 ≤ x := by
    rw [hx, one_le_div (by positivity)]
    exact sq_le_rpow hk ht
  have hLeq : Lvalue k t = ⌊x⌋₊ := Lvalue_eq k t
  have hLge : x / 2 ≤ (Lvalue k t : ℝ) := by
    rw [hLeq]
    have h1 := Nat.lt_floor_add_one x
    have h2 : (1 : ℝ) ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.le_floor (by simpa using hx1)
    linarith
  set p := mValue t * Lvalue k t with hp
  have hp200 : 200 ≤ p := by nlinarith
  have hG : p ≤ 200 * Gvalue (mValue t) (Lvalue k t) := by
    simp only [Gvalue, ← hp]
    omega
  have hGr : (p : ℝ) ≤ 200 * (Gvalue (mValue t) (Lvalue k t) : ℝ) := by exact_mod_cast hG
  have hpc : (p : ℝ) = (4 : ℝ) ^ t * (Lvalue k t : ℝ) := by
    rw [hp, Nat.cast_mul, mValue_cast]
  have hsplit : ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) =
      (4 : ℝ) ^ t * ((4 : ℝ) ^ t) ^ (1 - 1 / (k : ℝ)) := by
    conv_rhs => lhs; rw [← Real.rpow_one ((4 : ℝ) ^ t)]
    rw [← Real.rpow_add hpos4]
    congr 1
    ring
  have hmain : (1 / 400 : ℝ) * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 =
      (4 : ℝ) ^ t * (x / 2) / 200 := by
    rw [hsplit, hx]
    ring
  rw [hmain]
  have := mul_le_mul_of_nonneg_left hLge hpos4.le
  rw [← hpc] at this
  linarith

/-- Ledger: cor-R-omega. `R > G` gives the Omega form with constant `1 / 400`. -/
theorem rpow_le_of_Gvalue_lt {k t r : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t)
    (hr : Gvalue (mValue t) (Lvalue k t) < r) :
    (1 / 400 : ℝ) * ((4 : ℝ) ^ t) ^ (2 - 1 / (k : ℝ)) / (2 * (t : ℝ)) ^ 2 ≤ (r : ℝ) :=
  (Gvalue_ge hk ht).trans (by exact_mod_cast hr.le)

/-- Ledger: eq-2. Proposition 3.3 and Proposition 4.2 with one circuit at each
`t` assemble into the package. -/
theorem familyBoundsAt_of_parts {k : ℕ} (hk : 2 ≤ k) {C : ℝ} (hC : 0 < C) {b t₀ : ℕ}
    (h : ∀ t, t₀ ≤ t → ∃ Cir : Circuit (ForrelationCoord k t), CircuitRealises Cir (P k t) ∧
      (Q (totalise (Fkm k t Cir)) : ℝ) ≤ C * 2 ^ t * (2 * (t : ℝ)) ^ b ∧
      Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t Cir))) :
    FamilyBoundsAt k := by
  refine ⟨1 / 400, C, by norm_num, hC, b, max t₀ 8, fun t ht => ?_⟩
  obtain ⟨Cir, h1, h2, h3⟩ := h t (le_trans (le_max_left _ _) ht)
  exact ⟨Cir, h1, h2, rpow_le_of_Gvalue_lt hk (le_trans (le_max_right _ _) ht) h3⟩

/-! ## The discrepancy estimate -/

/-- Ledger: claim-tail. `(2/3) ^ (40 t) ≤ m ^ (-10)`, through
`(4/9) ^ (20 t) ≤ (1/2) ^ (20 t)`. -/
theorem twoThirds_pow_le (t : ℕ) :
    ((2 : ℝ) / 3) ^ (40 * t) ≤ ((mValue t : ℝ) ^ 10)⁻¹ := by
  have h1 : ((2 : ℝ) / 3) ^ (40 * t) = ((4 : ℝ) / 9) ^ (20 * t) := by
    rw [show 40 * t = 2 * (20 * t) by ring, pow_mul]
    norm_num
  have h2 : ((mValue t : ℝ) ^ 10)⁻¹ = ((1 : ℝ) / 2) ^ (20 * t) := by
    rw [mValue_cast, one_div, inv_pow, ← pow_mul, show t * 10 = 10 * t by ring,
      show 20 * t = 2 * (10 * t) by ring, pow_mul 2]
    norm_num
  rw [h1, h2]
  exact pow_le_pow_left₀ (by norm_num) (by norm_num) _

/-- Ledger: claim-numeric. Equation (23) for `m = 4 ^ t`, `r = 40 t`, `1 ≤ L ≤ m`,
`G ≤ m L / 100`: at most `6 / 100`. No lower bound on `t` is needed. -/
theorem discrepancy_le {t : ℕ} {L G : ℝ} (hL1 : 1 ≤ L)
    (hLm : L ≤ (mValue t : ℝ)) (hG : G ≤ (mValue t : ℝ) * L / 100) :
    4 * G / (mValue t : ℝ) ^ 2 + G / ((mValue t : ℝ) * L) +
        G * ((2 : ℝ) / 3) ^ (40 * t) ≤ 6 / 100 := by
  set m : ℝ := (mValue t : ℝ) with hm
  have hm1 : 1 ≤ m := hL1.trans hLm
  have hm0 : 0 < m := by linarith
  have hL0 : 0 < L := by linarith
  have h1 : 4 * G / m ^ 2 ≤ 4 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have h2 : G / (m * L) ≤ 1 / 100 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have htail : ((2 : ℝ) / 3) ^ (40 * t) ≤ (m ^ 10)⁻¹ := twoThirds_pow_le t
  have hinv0 : 0 ≤ ((2 : ℝ) / 3) ^ (40 * t) := by positivity
  have h3 : G * ((2 : ℝ) / 3) ^ (40 * t) ≤ 1 / 100 := by
    have hGm : G ≤ m ^ 2 / 100 := by nlinarith
    have hm210 : m ^ 2 ≤ m ^ 10 := pow_le_pow_right₀ hm1 (by norm_num)
    calc G * ((2 : ℝ) / 3) ^ (40 * t) ≤ m ^ 2 / 100 * ((2 : ℝ) / 3) ^ (40 * t) :=
          mul_le_mul_of_nonneg_right hGm hinv0
      _ ≤ m ^ 2 / 100 * (m ^ 10)⁻¹ := mul_le_mul_of_nonneg_left htail (by positivity)
      _ ≤ m ^ 10 / 100 * (m ^ 10)⁻¹ :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 / 100 := by field_simp
  linarith

/-- Ledger: claim-numeric. The strict form Proposition 4.2 uses. -/
theorem discrepancy_lt_third {t : ℕ} {L G : ℝ} (hL1 : 1 ≤ L)
    (hLm : L ≤ (mValue t : ℝ)) (hG : G ≤ (mValue t : ℝ) * L / 100) :
    4 * G / (mValue t : ℝ) ^ 2 + G / ((mValue t : ℝ) * L) +
        G * ((2 : ℝ) / 3) ^ (40 * t) < 1 / 3 := by
  have := discrepancy_le hL1 hLm hG
  linarith

/-- Ledger: claim-numeric. The estimate at the actual `L` and `G`, from `t = 8`. -/
theorem discrepancy_parameters {k t : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t) :
    4 * (Gvalue (mValue t) (Lvalue k t) : ℝ) / (mValue t : ℝ) ^ 2 +
        (Gvalue (mValue t) (Lvalue k t) : ℝ) / ((mValue t : ℝ) * (Lvalue k t : ℝ)) +
        (Gvalue (mValue t) (Lvalue k t) : ℝ) * ((2 : ℝ) / 3) ^ (40 * t) < 1 / 3 := by
  refine discrepancy_lt_third (by exact_mod_cast one_le_Lvalue hk ht)
    (by exact_mod_cast Lvalue_le_mValue (by omega) (by omega)) ?_
  have : (Gvalue (mValue t) (Lvalue k t) : ℝ) ≤ ((mValue t * Lvalue k t : ℕ) : ℝ) / 100 := by
    simpa [Gvalue] using (Nat.cast_div_le (α := ℝ) (m := mValue t * Lvalue k t) (n := 100))
  simpa using this

end QuarticQuery

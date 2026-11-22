module

public import QuarticQuery.LowerBound.Minimax
public import QuarticQuery.LowerBound.Planted.Simulator
public import QuarticQuery.Model.Classical
public import QuarticQuery.Results.Exponent

/-!
# Proposition 4.2 in generic form

The final assembly. For one tree of depth at most `G`, the output-one probabilities
on the coupled inputs differ by at most the discrepancy (23). If a randomized
program had error at most `1/3`, averaging over its trees would give a gap of at
least `1/3`. Only `exists_transcript` is used from the circuit, and its size plays
no part.
-/

@[expose] public section

open Finset

namespace QuarticQuery

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ℓ r S : ℕ}

/-- The joint average over `A`, `J` and the independent `I`. -/
noncomputable def coupledAvg (μ : BitInput κ → ℝ)
    (g : (Column ℓ → Fin r → BitInput κ) → (Column ℓ → Column ℓ) → Column ℓ → ℝ) : ℝ :=
  avg (prodW (prodW μ)) fun A => avg (prodW (unif ℓ)) fun J => avg (unif ℓ) (g A J)

/-- Ledger: eq-18. One run: output change is charged to the zero, a heavy column,
or the joint event. -/
theorem output_gap_le (f : PartialBool κ) (tr : BitInput κ → Fin S → Bool) (L : ℕ)
    (T : QueryTree (BitLoc ℓ r S κ)) (A : Column ℓ → Fin r → BitInput κ)
    (J : Column ℓ → Column ℓ) (I : Column ℓ) :
    ind (T.eval (planted f tr J A I) = true) - ind (T.eval (dummy J A) = true) ≤
      foundZero T A J I + ind (L < aQueries I (T.path (dummy J A))) +
        reachedCell f L T J A I := by
  have n1 : 0 ≤ foundZero T A J I := ind_nonneg _
  have n2 := ind_nonneg (L < aQueries I (T.path (dummy J A)))
  have n3 : 0 ≤ reachedCell f L T J A I := ind_nonneg _
  by_cases he : T.eval (dummy J A) = T.eval (planted f tr J A I)
  · rw [← he]
    linarith
  obtain ⟨q, hq, hne⟩ := T.exists_mem_path_ne he
  have h1 := ind_le_one (T.eval (planted f tr J A I) = true)
  have h2 := ind_nonneg (T.eval (dummy J A) = true)
  rcases eq_of_dummy_ne_planted hne with rfl | hc
  · have : foundZero T A J I = 1 := ind_true hq
    linarith
  · by_cases hh : L < aQueries I (T.path (dummy J A))
    · rw [ind_true hh] at n2 ⊢
      linarith
    · have : reachedCell f L T J A I = 1 := ind_true ⟨hh, q, hq, hc⟩
      linarith

/-- Ledger: eq-23. One deterministic tree of depth at most `G`: the output-one
probabilities differ by at most `2 G / m² + G / (m L) + G ρ`. -/
theorem tree_gap_le {f : PartialBool κ} (tr : BitInput κ → Fin S → Bool) {μ : BitInput κ → ℝ}
    {L G : ℕ} {ρ : ℝ} (hL : 1 ≤ L) (hμ : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hguess : ∀ U : OutTree (Fin r × κ) (Fin r → Bool), (U.capped fun _ => L) →
      guessSuccess f (fun _ => μ) U ≤ ρ)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G) :
    coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I =>
        ind (T.eval (planted f tr J A I) = true) - ind (T.eval (dummy J A) = true)) ≤
      2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 + (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) +
        (G : ℝ) * ρ := by
  have hPU0 := prodW_nonneg (ι := Fin r) hμ
  have hPU1 : ∑ U : Fin r → BitInput κ, prodW μ U = 1 := sum_prodW hμ1
  have hPA0 : ∀ A : Column ℓ → Fin r → BitInput κ, 0 ≤ prodW (prodW μ) A :=
    prodW_nonneg hPU0
  have hPA1 : ∑ A : Column ℓ → Fin r → BitInput κ, prodW (prodW μ) A = 1 := sum_prodW hPU1
  have hPJ0 : ∀ J : Column ℓ → Column ℓ, 0 ≤ prodW (unif ℓ) J := prodW_nonneg (unif_nonneg ℓ)
  have hPJ1 : ∑ J : Column ℓ → Column ℓ, prodW (unif ℓ) J = 1 := sum_prodW (sum_unif ℓ)
  have hmono : coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I =>
        ind (T.eval (planted f tr J A I) = true) - ind (T.eval (dummy J A) = true)) ≤
      coupledAvg μ (fun A J I => foundZero T A J I +
        ind (L < aQueries I (T.path (dummy J A))) + reachedCell f L T J A I) :=
    avg_mono hPA0 fun A => avg_mono hPJ0 fun J => avg_mono (unif_nonneg ℓ) fun I =>
      output_gap_le f tr L T A J I
  have hsplit : coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I => foundZero T A J I +
        ind (L < aQueries I (T.path (dummy J A))) + reachedCell f L T J A I) =
      coupledAvg μ (fun A J I => foundZero T A J I) +
      coupledAvg μ (fun A J I => ind (L < aQueries I (T.path (dummy J A)))) +
      coupledAvg μ (fun A J I => reachedCell f L T J A I) := by
    simp only [coupledAvg, avg_add]
  have hZ : coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I => foundZero T A J I) ≤
      2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 :=
    avg_le_const hPA0 hPA1 fun A => avg_foundZero_I_le T A hT
  have hH : coupledAvg (ℓ := ℓ) (r := r) μ
      (fun A J I => ind (L < aQueries I (T.path (dummy J A)))) ≤
      (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) :=
    avg_le_const hPA0 hPA1 fun A => avg_le_const hPJ0 hPJ1 fun J =>
      avg_heavy_le hL _ ((T.length_path_le _).trans hT)
  have hN : coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I => reachedCell f L T J A I) ≤
      (G : ℝ) * ρ := by
    unfold coupledAvg
    rw [avg_comm]
    refine avg_le_const hPJ0 hPJ1 fun J => ?_
    rw [avg_comm]
    refine avg_le_const (unif_nonneg ℓ) (sum_unif ℓ) fun I => ?_
    rw [avg_resample hPU1 I]
    exact avg_le_const hPA0 hPA1 fun A =>
      avg_reachedCell_le hμ hdom hguess T hT J A I
  rw [hsplit] at hmono
  linarith

/-- Ledger: prop-4.2-generic. The core statement, for any budget `G` whose
discrepancy (23) is below `1/3`. -/
theorem addressedF_not_RLe (f : PartialBool κ) (C : Circuit κ) (hC : CircuitRealises C f)
    {ℓ r L G : ℕ} (hL : ¬ RLe f L) (hL1 : 1 ≤ L)
    (hdisc : 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 + (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) +
      (G : ℝ) * ((2 : ℝ) / 3) ^ r < 1 / 3) :
    ¬ RLe (totalise (addressedF f C ℓ r)) G := by
  rintro ⟨P, hP, hs⟩
  obtain ⟨μ, hμ0, hμ1, hdom, hguess⟩ := exists_address_guess_bound hL
  let tr : BitInput κ → Fin C.size → Bool := fun x => Classical.choose (hC.exists_transcript x)
  have htr : ∀ x, GateConsistent C x (tr x) := fun x =>
    Classical.choose_spec (hC.exists_transcript x)
  have hadd : ∀ x, P.success x true + P.success x false = 1 := fun x => by
    unfold RandomizedProgram.success
    rw [← sum_add_distrib, ← P.weight_sum]
    refine sum_congr rfl fun j _ => ?_
    cases (P.tree j).eval x <;> simp
  have hsucc : ∀ x, avg P.weight (fun k => ind ((P.tree k).eval x = true)) =
      P.success x true := fun x => by
    refine sum_congr rfl fun k _ => ?_
    beta_reduce
    by_cases h : (P.tree k).eval x = true
    · rw [ind_true h, if_pos h, mul_one]
    · rw [ind_false h, if_neg h, mul_zero]
  have h0 : ∀ (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ),
      P.success (dummy J A) true ≤ 1 / 3 := fun J A => by
    have := hs (dummy J A) false (by rw [totalise, addressedF_dummy])
    linarith [hadd (dummy (S := C.size) J A)]
  have h1 : ∀ (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ),
      prodW (prodW μ) A ≠ 0 → 2 / 3 ≤ P.success (planted f tr J A I) true := fun J A I hA =>
    hs _ true (by
      rw [totalise, addressedF_planted htr J A I fun h =>
        hdom _ (ne_zero_of_prodW_ne_zero (ne_zero_of_prodW_ne_zero hA I) h)])
  have hPU0 := prodW_nonneg (ι := Fin r) hμ0
  have hPU1 : ∑ U : Fin r → BitInput κ, prodW μ U = 1 := sum_prodW hμ1
  have hPA0 : ∀ A : Column ℓ → Fin r → BitInput κ, 0 ≤ prodW (prodW μ) A :=
    prodW_nonneg hPU0
  have hPA1 : ∑ A : Column ℓ → Fin r → BitInput κ, prodW (prodW μ) A = 1 := sum_prodW hPU1
  have hPJ0 : ∀ J : Column ℓ → Column ℓ, 0 ≤ prodW (unif ℓ) J := prodW_nonneg (unif_nonneg ℓ)
  have hPJ1 : ∑ J : Column ℓ → Column ℓ, prodW (unif ℓ) J = 1 := sum_prodW (sum_unif ℓ)
  set δ : ℝ := 2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 + (G : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) +
    (G : ℝ) * ((2 : ℝ) / 3) ^ r with hδ
  have hδlt : δ < 1 / 3 := by
    have hG : (0 : ℝ) ≤ (G : ℝ) := Nat.cast_nonneg G
    have hm : (0 : ℝ) ≤ ((2 ^ ℓ : ℕ) : ℝ) ^ 2 := by positivity
    have : 2 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 ≤ 4 * (G : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (by linarith) hm
    rw [hδ]
    linarith
  have hgap : ∀ k, coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I =>
      ind ((P.tree k).eval (planted f tr J A I) = true) -
        ind ((P.tree k).eval (dummy J A) = true)) ≤ δ := fun k =>
    tree_gap_le tr hL1 hμ0 hμ1 hdom (fun U hU => hguess r U hU) (P.tree k)
      ((Finset.le_sup (f := fun j => (P.tree j).depth) (mem_univ k)).trans hP)
  have hmix := avg_le_const (fun k => (P.weight_pos k).le) P.weight_sum hgap
  have hlow : (1 : ℝ) / 3 ≤ avg P.weight fun k => coupledAvg (ℓ := ℓ) (r := r) μ (fun A J I =>
      ind ((P.tree k).eval (planted f tr J A I) = true) -
        ind ((P.tree k).eval (dummy J A) = true)) := by
    unfold coupledAvg
    rw [avg_comm]
    refine const_le_avg_of_ne hPA0 hPA1 fun A hA => ?_
    rw [avg_comm]
    refine const_le_avg_of_ne hPJ0 hPJ1 fun J _ => ?_
    rw [avg_comm]
    refine const_le_avg_of_ne (unif_nonneg ℓ) (sum_unif ℓ) fun I _ => ?_
    rw [avg_sub, hsucc, hsucc]
    linarith [h0 J A, h1 J A I hA]
  linarith

/-- Ledger: prop-4.2-generic. Proposition 4.2 at `G = ⌊m L / 100⌋`, for any `ℓ` and
`r` whose discrepancy (23) is below `1/3`. -/
theorem addressedF_lower (f : PartialBool κ) (C : Circuit κ) (hC : CircuitRealises C f)
    {ℓ r L : ℕ} (hL : ¬ RLe f L)
    (hdisc : 4 * (Gvalue (2 ^ ℓ) L : ℝ) / ((2 ^ ℓ : ℕ) : ℝ) ^ 2 +
      (Gvalue (2 ^ ℓ) L : ℝ) / (((2 ^ ℓ : ℕ) : ℝ) * (L : ℝ)) +
      (Gvalue (2 ^ ℓ) L : ℝ) * ((2 : ℝ) / 3) ^ r < 1 / 3) (hL1 : 1 ≤ L) :
    ¬ RLe (totalise (addressedF f C ℓ r)) (Gvalue (2 ^ ℓ) L) :=
  addressedF_not_RLe f C hC hL hL1 hdisc

/-- Ledger: prop-4.2-generic. The non-asymptotic form at `ℓ = 2 t`, `r = 40 t`: if
`1 ≤ L ≤ m` and `L < R f`, then `⌊m L / 100⌋ < R F`. -/
theorem Gvalue_lt_R_addressedF (f : PartialBool κ) (C : Circuit κ) (hC : CircuitRealises C f)
    {t L : ℕ} (hL1 : 1 ≤ L) (hLm : L ≤ mValue t) (hLR : L < R f) :
    Gvalue (mValue t) L < R (totalise (addressedF f C (2 * t) (40 * t))) := by
  have hnot : ¬ RLe f L := lt_R_iff.mp hLR L le_rfl
  have hG : (Gvalue (mValue t) L : ℝ) ≤ (mValue t : ℝ) * (L : ℝ) / 100 := by
    have := Nat.cast_div_le (α := ℝ) (m := mValue t * L) (n := 100)
    simpa [Gvalue] using this
  have hd := discrepancy_lt_third (t := t) (L := (L : ℝ)) (by exact_mod_cast hL1)
    (by exact_mod_cast hLm) hG
  exact lt_R_of_not_RLe (addressedF_lower f C hC hnot hd hL1)

/-- Ledger: prop-4.2. The concrete instance: the family's `L < R (P k t)` gives
`G < R (F_{k,m})` from `t = 8`, for every circuit realising `P`. -/
theorem Gvalue_lt_R_Fkm {k t : ℕ} (hk : 2 ≤ k) (ht : 8 ≤ t)
    (C : Circuit (ForrelationCoord k t)) (hC : CircuitRealises C (P k t))
    (hLR : Lvalue k t < R (P k t)) :
    Gvalue (mValue t) (Lvalue k t) < R (totalise (Fkm k t C)) :=
  Gvalue_lt_R_addressedF (P k t) C hC (one_le_Lvalue hk ht)
    (Lvalue_le_mValue (by omega) (by omega)) hLR

end QuarticQuery

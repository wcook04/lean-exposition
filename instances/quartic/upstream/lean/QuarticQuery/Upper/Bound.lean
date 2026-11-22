module

public import QuarticQuery.Upper.Verify

/-!
# The explicit query count

`budget` is bounded by `C_k 2^t (2t)^6` with a crude explicit constant. Logarithms are
bounded by their arguments, which is enough, since `1/ε` and `r/ε` are polynomial in `t`.
`Q_Fkm_le` is Proposition 3.3 for the circuit `forrCircuit`, in the form
`familyBoundsAt_of_parts` consumes.
-/

@[expose] public section

namespace QuarticQuery.Upper

open QuarticQuery.Forrelation QuarticQuery.Tournament QuarticQuery.Amplification

/-- Ledger: lem-3.1. A polynomial bound on the number of trials. -/
theorem trialCount_le {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) : (trialCount η : ℝ) ≤ 4 / η + 1 := by
  have hl : 0 ≤ Real.log (1 / η) := Real.log_nonneg (by rw [le_div_iff₀ h0]; linarith)
  have hq := quarter_le_log
  have hlp : 0 < Real.log (40 / 31) := by linarith
  have hx : Real.log (1 / η) / Real.log (40 / 31) ≤ 4 / η := by
    rw [div_le_iff₀ hlp]
    have h2 : Real.log (1 / η) ≤ 1 / η := Real.log_le_self (by positivity)
    have h3 : 1 / η ≤ 4 / η * Real.log (40 / 31) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (by linarith) h0.le
    linarith
  have := Nat.ceil_lt_add_one (a := Real.log (1 / η) / Real.log (40 / 31)) (div_nonneg hl hlp.le)
  unfold trialCount
  linarith

/-- Ledger: lem-3.1. The iteration bound from a square bound on `γ⁻¹`. -/
theorem iterationBound_inv_le {y : ℝ} {b : ℕ} (hb : y ≤ (b : ℝ) ^ 2) :
    iterationBound y⁻¹ ≤ 10 * b + 1 := by
  unfold iterationBound
  rw [Nat.ceil_le, Real.sqrt_inv, div_inv_eq_mul]
  have h : Real.sqrt y ≤ b := by
    rw [Real.sqrt_le_iff]
    exact ⟨Nat.cast_nonneg b, hb⟩
  push_cast
  linarith

theorem Tval_mValue_le (t : ℕ) : Tval (mValue t) ≤ 2 * t + 10 := by
  refine Nat.clog_le_of_le_pow ?_
  rw [mValue, add_comm, pow_add]
  exact Nat.mul_le_mul_right _ (by norm_num)

/-- The constant of `budget_le`. -/
def budgetConst (k : ℕ) : ℕ :=
  let R := 1 + 1920000 * 2 ^ (10 * k)
  let Cc := 40 * R * k + 4
  let CK := 42 + 20 * forrConstant k
  6 * (48002 * 258 * Cc) + 6 * (40 * R * k + 48002 * 69 * CK)

/-- The exact dependence of the existing repetition algorithm on the Forrelation order. -/
theorem budgetConst_eq_expanded (k : ℕ) :
    budgetConst k = 2972284080 * k * (1 + 1920000 * 2 ^ (10 * k)) +
      79491312000 * (k + 1) ^ 2 + 1131887160 := by
  simp only [budgetConst, forrConstant]
  ring

/-- An explicit exponential envelope for the existing algorithm; no new decoder is used. -/
theorem budgetConst_le_exponential {k : ℕ} (hk : 1 ≤ k) :
    budgetConst k ≤ 2 ^ 53 * k * 2 ^ (10 * k) := by
  have hkP : k ≤ 2 ^ (10 * k) := by
    calc k ≤ 2 ^ k := (Nat.lt_two_pow_self (n := k)).le
      _ ≤ 2 ^ (10 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hP : 1 ≤ 2 ^ (10 * k) := Nat.one_le_two_pow
  rw [budgetConst_eq_expanded]
  generalize 2 ^ (10 * k) = P at *
  have hkp : k ≤ k * P := by nlinarith
  have h1kp : 1 ≤ k * P := by nlinarith
  have hk2 : k ^ 2 ≤ k * P := by
    simpa only [pow_two] using Nat.mul_le_mul_left k hkP
  have hpol : (k + 1) ^ 2 ≤ 4 * k * P := by nlinarith
  have hsum : 2972284080 * k * (1 + 1920000 * P) +
        79491312000 * (k + 1) ^ 2 + 1131887160 ≤
      (2972284080 * (1 + 1920000) + 4 * 79491312000 + 1131887160) * k * P := by
    nlinarith
  exact hsum.trans (by norm_num; nlinarith)

/-- Ledger: claim-tournament-cost, prop-3.3. The query count of the algorithm. -/
theorem budget_le {k t : ℕ} {C : Circuit (ForrelationCoord k t)} (ht : 1 ≤ t)
    (hSz : C.size ≤ forrConstant k * mValue t * (2 * t) ^ 2) :
    budget k t (repetitions k (epsval (mValue t) / (40 * t : ℕ))) (Fintype.card (Tests t C)) ≤
      budgetConst k * 2 ^ t * (2 * t) ^ 6 := by
  obtain ⟨τ, hτd⟩ : ∃ τ, τ = 2 * t := ⟨_, rfl⟩
  obtain ⟨p, hpd⟩ : ∃ p, p = 2 ^ t := ⟨_, rfl⟩
  have hτ2 : 2 ≤ τ := by omega
  have hτ1 : 1 ≤ τ := by omega
  have hp1 : 1 ≤ p := by rw [hpd]; exact Nat.one_le_two_pow
  have hm2 : mValue t = p ^ 2 := by
    rw [mValue, hpd, mul_comm, pow_mul]
  have hm' : 2 ≤ mValue t := by
    rw [mValue]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (2 * t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨T, hTd⟩ : ∃ T, T = Tval (mValue t) := ⟨_, rfl⟩
  obtain ⟨ε, hεd⟩ : ∃ ε, ε = epsval (mValue t) := ⟨_, rfl⟩
  have hT : T ≤ 6 * τ := by
    have := Tval_mValue_le t
    omega
  have hTpos : 0 < T := by rw [hTd]; exact Tval_pos hm'
  have hTR : (0 : ℝ) < T := by exact_mod_cast hTpos
  have hTle : (T : ℝ) ≤ 6 * τ := by exact_mod_cast hT
  have hτR : (2 : ℝ) ≤ τ := by exact_mod_cast hτ2
  have hε : ε = 1 / (1000 * (T : ℝ)) := by rw [hεd, hTd, epsval]
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hε1 : ε ≤ 1 := by
    rw [hε, div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
    linarith
  obtain ⟨N, hNd⟩ : ∃ N, N = trialCount ε := ⟨_, rfl⟩
  have hN : N ≤ 24001 * τ := by
    have h := trialCount_le hε0 hε1
    rw [← hNd] at h
    have e : 4 / ε = 4000 * (T : ℝ) := by
      rw [hε]
      field_simp
      norm_num
    rw [e] at h
    have : (N : ℝ) ≤ 24001 * τ := by linarith
    exact_mod_cast this
  obtain ⟨n, hnd⟩ : ∃ n, n = repetitions k (ε / (40 * t : ℕ)) := ⟨_, rfl⟩
  obtain ⟨R, hRd⟩ : ∃ R, R = 1 + 1920000 * 2 ^ (10 * k) := ⟨_, rfl⟩
  have hn : n ≤ R * τ ^ 2 := by
    have hr : (0 : ℝ) < (40 * t : ℕ) := by
      have : 0 < 40 * t := by omega
      exact_mod_cast this
    have hr1 : (1 : ℝ) ≤ (40 * t : ℕ) := by
      have : 1 ≤ 40 * t := by omega
      exact_mod_cast this
    have hη0 : 0 < ε / (40 * t : ℕ) := div_pos hε0 hr
    have hη1 : ε / (40 * t : ℕ) ≤ 1 := (div_le_self hε0.le hr1).trans hε1
    have h := repetitions_le k hη0 hη1
    have hlog : Real.log (1 / (ε / (40 * t : ℕ))) ≤ 1 / (ε / (40 * t : ℕ)) :=
      Real.log_le_self (by positivity)
    have hinv : 1 / (ε / (40 * t : ℕ)) ≤ 120000 * (τ : ℝ) ^ 2 := by
      have e : 1 / (ε / (40 * t : ℕ)) = 20 * (τ : ℝ) * (1000 * T) := by
        rw [hε, hτd]
        push_cast
        field_simp
        ring
      rw [e]
      nlinarith
    have ha : (0 : ℝ) < 2 ^ (10 * k) := by positivity
    have hstep := mul_le_mul_of_nonneg_left (hlog.trans hinv) (by positivity :
      (0 : ℝ) ≤ 16 * 2 ^ (10 * k))
    have hY : (1 : ℝ) ≤ (τ : ℝ) ^ 2 := by nlinarith
    rw [← hnd] at h
    have hgoal : (n : ℝ) ≤ (R : ℝ) * (τ : ℝ) ^ 2 := by
      rw [hRd]
      push_cast
      nlinarith
    exact_mod_cast hgoal
  obtain ⟨S, hSd⟩ : ∃ S, S = C.size := ⟨_, rfl⟩
  have hS : S ≤ forrConstant k * mValue t * τ ^ 2 := by
    rw [hSd, hτd]
    exact hSz
  obtain ⟨K, hKd⟩ : ∃ K, K = Fintype.card (Tests t C) := ⟨_, rfl⟩
  obtain ⟨CK, hCKd⟩ : ∃ CK, CK = 42 + 20 * forrConstant k := ⟨_, rfl⟩
  have hK : K ≤ CK * mValue t * τ ^ 3 := by
    have e : K = 2 ^ (2 * t) + (2 ^ (2 * t) - 1) + 40 * t * (S + 2) := by
      rw [hKd, hSd]
      exact card_testIndex _ _ _
    have hm : 2 ^ (2 * t) = mValue t := rfl
    have h40 : 40 * t = 20 * τ := by omega
    rw [e, hm, h40]
    have h1 : 1 ≤ mValue t := by omega
    have hτ3 : τ ≤ τ ^ 3 := Nat.le_self_pow (by norm_num) τ
    have h3 : 1 ≤ τ ^ 3 := Nat.one_le_pow _ _ hτ1
    have hA : mValue t ≤ mValue t * τ ^ 3 := Nat.le_mul_of_pos_right _ (by omega)
    have hB : τ ≤ mValue t * τ ^ 3 := by
      calc τ ≤ τ ^ 3 := hτ3
        _ ≤ mValue t * τ ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    have hC : 20 * τ * (S + 2) ≤ 20 * forrConstant k * (mValue t * τ ^ 3) + 40 * τ := by
      calc 20 * τ * (S + 2) ≤ 20 * τ * (forrConstant k * mValue t * τ ^ 2 + 2) := by gcongr
        _ = _ := by ring
    have hgoal : CK * mValue t * τ ^ 3 =
        42 * (mValue t * τ ^ 3) + 20 * forrConstant k * (mValue t * τ ^ 3) := by
      rw [hCKd]
      ring
    omega
  obtain ⟨b, hbd⟩ : ∃ b, b = CK * p * τ ^ 2 := ⟨_, rfl⟩
  have hCK1 : 1 ≤ CK := by omega
  have hb1 : 1 ≤ b := by
    rw [hbd]
    exact Nat.mul_pos (Nat.mul_pos hCK1 hp1) (Nat.pow_pos hτ1)
  have hKb : K ≤ b ^ 2 := by
    refine hK.trans ?_
    rw [hbd, hm2]
    have h1 : CK * p ^ 2 * τ ^ 3 ≤ CK * p ^ 2 * τ ^ 3 * (CK * τ) :=
      Nat.le_mul_of_pos_right _ (Nat.mul_pos hCK1 hτ1)
    calc _ ≤ _ := h1
      _ = _ := by ring
  have hKpos : 0 < K := by
    rw [hKd]
    have : Nonempty (Tests t C) := ⟨.inl ⟨0, Nat.two_pow_pos _⟩⟩
    exact Fintype.card_pos
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hM₂ : iterationBound (K : ℝ)⁻¹ ≤ 10 * b + 1 :=
    iterationBound_inv_le (by exact_mod_cast hKb)
  have hM₁ : iterationBound ((2 * (mValue t : ℝ))⁻¹) ≤ 10 * (2 * p) + 1 := by
    refine iterationBound_inv_le ?_
    have : 2 * mValue t ≤ (2 * p) ^ 2 := by
      rw [hm2]
      nlinarith
    exact_mod_cast this
  have h2M₁ : 2 * iterationBound ((2 * (mValue t : ℝ))⁻¹) + 1 ≤ 43 * p := by omega
  have h2M₂ : 2 * iterationBound (K : ℝ)⁻¹ + 1 ≤ 23 * b := by omega
  have htest : testCost t ≤ 3 * τ := by
    unfold testCost
    omega
  obtain ⟨a, had⟩ : ∃ a, a = addrCost k t n := ⟨_, rfl⟩
  have hadd : a ≤ 20 * R * k * τ ^ 3 := by
    have h40 : 40 * t = 20 * τ := by omega
    rw [had, addrCost, h40]
    calc 20 * τ * (n * k) ≤ 20 * τ * (R * τ ^ 2 * k) := by gcongr
      _ = _ := by ring
  obtain ⟨Cc, hCcd⟩ : ∃ Cc, Cc = 40 * R * k + 4 := ⟨_, rfl⟩
  have hcc : cmpCost k t n ≤ Cc * τ ^ 3 := by
    have e : cmpCost k t n = 2 * a + 2 * τ + 2 := by
      rw [cmpCost, ← had]
      omega
    have hτ3 : τ ≤ τ ^ 3 := Nat.le_self_pow (by norm_num) τ
    have hexp : Cc * τ ^ 3 = 2 * (20 * R * k * τ ^ 3) + 4 * τ ^ 3 := by
      rw [hCcd]
      ring
    omega
  have hstage : stageCost (mValue t) T (cmpCost k t n) ε ≤ 48002 * 258 * Cc * p * τ ^ 5 := by
    rw [stageCost, ← hNd]
    calc N * (2 * ((2 * iterationBound ((2 * (mValue t : ℝ))⁻¹) + 1) * (T * cmpCost k t n)))
        ≤ (24001 * τ) * (2 * ((43 * p) * ((6 * τ) * (Cc * τ ^ 3)))) := by gcongr
      _ = _ := by ring
  have hsearch : searchCost t K ε ≤ 48002 * 69 * CK * p * τ ^ 4 := by
    rw [searchCost, ← hNd]
    calc N * (2 * ((2 * iterationBound (K : ℝ)⁻¹ + 1) * testCost t))
        ≤ (24001 * τ) * (2 * ((23 * b) * (3 * τ))) := by gcongr
      _ = _ := by rw [hbd]; ring
  have hcV : 2 * a + searchCost t K ε ≤ (40 * R * k + 48002 * 69 * CK) * p * τ ^ 4 := by
    have h1 : 2 * a ≤ 40 * R * k * p * τ ^ 4 := by
      calc 2 * a ≤ 2 * (20 * R * k * τ ^ 3) := by gcongr
        _ = 40 * R * k * 1 * τ ^ 3 := by ring
        _ ≤ 40 * R * k * p * τ ^ 4 := by
            gcongr
            omega
    calc _ ≤ 40 * R * k * p * τ ^ 4 + 48002 * 69 * CK * p * τ ^ 4 := Nat.add_le_add h1 hsearch
      _ = _ := by ring
  rw [budget, ← hTd, ← hεd, ← hnd, ← hKd, ← hpd, ← hτd, ← had]
  have hconst : budgetConst k = 6 * (48002 * 258 * Cc) + 6 * (40 * R * k + 48002 * 69 * CK) := by
    rw [hCcd, hCKd, hRd]
    rfl
  rw [hconst]
  calc T * stageCost (mValue t) T (cmpCost k t n) ε + T * (2 * a + searchCost t K ε)
      ≤ (6 * τ) * (48002 * 258 * Cc * p * τ ^ 5) +
          (6 * τ) * ((40 * R * k + 48002 * 69 * CK) * p * τ ^ 4) := by gcongr
    _ = 6 * (48002 * 258 * Cc) * p * τ ^ 6 +
          6 * (40 * R * k + 48002 * 69 * CK) * p * τ ^ 5 := by ring
    _ ≤ 6 * (48002 * 258 * Cc) * p * τ ^ 6 +
          6 * (40 * R * k + 48002 * 69 * CK) * p * τ ^ 6 := by
        gcongr ?_ + _ * p * ?_
        · exact le_refl _
        · exact Nat.pow_le_pow_right hτ1 (by norm_num)
    _ = _ := by ring

/-- Ledger: prop-3.3. Proposition 3.3 for the circuit `forrCircuit`: for each fixed
`k = l + 1 ≥ 1`, at every `t ≥ 1`. -/
theorem Fkm_forrCircuit_QLe (l t : ℕ) (ht : 1 ≤ t) :
    QLe (totalise (Fkm (l + 1) t (forrCircuit l t))) (budgetConst (l + 1) * 2 ^ t * (2 * t) ^ 6) :=
  (Fkm_QLe (by omega) ht (forrCircuit_realises l t) le_rfl).mono
    (budget_le ht (forrCircuit_size_le l t ht))

/-- Ledger: prop-3.3. Proposition 3.3: `Q(F_{k,m}) ≤ C_k 2^t (2t)^6`, with `m = 4^t`. -/
theorem Q_Fkm_le (l t : ℕ) (ht : 1 ≤ t) :
    (Q (totalise (Fkm (l + 1) t (forrCircuit l t))) : ℝ) ≤
      (budgetConst (l + 1) : ℝ) * 2 ^ t * (2 * (t : ℝ)) ^ 6 := by
  have h := Q_le_of_QLe (Fkm_forrCircuit_QLe l t ht)
  have hc : ((Q (totalise (Fkm (l + 1) t (forrCircuit l t))) : ℕ) : ℝ) ≤
      ((budgetConst (l + 1) * 2 ^ t * (2 * t) ^ 6 : ℕ) : ℝ) := by exact_mod_cast h
  simpa using hc

/-- The quantum upper bound with its order dependence exposed, for `m = 4^t`. -/
theorem Q_Fkm_le_exponential (l t : ℕ) (ht : 1 ≤ t) :
    (Q (totalise (Fkm (l + 1) t (forrCircuit l t))) : ℝ) ≤
      (2 : ℝ) ^ 53 * (l + 1 : ℕ) * 2 ^ (10 * (l + 1)) *
        2 ^ t * (2 * (t : ℝ)) ^ 6 := by
  refine (Q_Fkm_le l t ht).trans ?_
  have hB : (budgetConst (l + 1) : ℝ) ≤
      (2 : ℝ) ^ 53 * (l + 1 : ℕ) * 2 ^ (10 * (l + 1)) := by
    exact_mod_cast budgetConst_le_exponential (k := l + 1) (by omega)
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hB (by positivity)) (by positivity)

theorem budgetConst_pos (k : ℕ) : 0 < budgetConst k := by
  simp only [budgetConst]
  positivity

/-- Ledger: eq-2. Equation (2) at `k = l + 1 ≥ 2`, conditional only on the randomized lower
bound for the same circuit. This is the input `familyBoundsAt_of_parts` asks for. -/
theorem familyBoundsAt_of_lower (l : ℕ) (hk : 2 ≤ l + 1) {t₀ : ℕ}
    (hR : ∀ t, t₀ ≤ t → Gvalue (mValue t) (Lvalue (l + 1) t) <
      R (totalise (Fkm (l + 1) t (forrCircuit l t)))) :
    FamilyBoundsAt (l + 1) := by
  refine familyBoundsAt_of_parts hk (C := (budgetConst (l + 1) : ℝ)) (b := 6) (t₀ := max t₀ 1)
    (by exact_mod_cast budgetConst_pos _) fun t ht => ?_
  exact ⟨forrCircuit l t, forrCircuit_realises l t, Q_Fkm_le l t (by omega),
    hR t (by omega)⟩

end QuarticQuery.Upper

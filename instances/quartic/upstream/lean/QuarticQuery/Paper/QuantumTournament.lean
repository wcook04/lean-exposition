module

public import QuarticQuery.Upper.Tournament
public import QuarticQuery.Paper.QuantumAmplification

/-!
# Proposition 3.2 in the paper's list-valued form

Compiled as part of the `QuarticQuery` library target.
This is an independent, renamed adaptation of the earlier
Paper/Section3.lean, with an explicit coherent output register and fresh retained workspaces.
The physical bit-query compilation is stated separately from its logical reads.

`Upper.tournament_runs` consumes the tournament's list with a verifier in continuation
form. Here the same stages are composed with a continuation that outputs the list
itself, so the program's classical result is a list of at most `T` candidates, and the
guarantee is list membership with probability at least `1 - 2m/2^T - Tε`, as in the
paper.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Tournament QuarticQuery.Amplification

/-! ## Lists of at most `T` candidates as an output alphabet -/

/-- Ledger: prop-3.2. Lists of at most `T` candidates. -/
abbrev QuantumCandidateList (Col : Type) (T : ℕ) := {l : List Col // l.length ≤ T}

/-- Ledger: prop-3.2. Supporting list-law identity. -/
theorem quantumCandidateList_code_injective {Col : Type} {T : ℕ} :
    Function.Injective fun l : QuantumCandidateList Col T => fun i : Fin (T + 1) => l.1[i.val]? := by
  intro l l' h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < T + 1
  · exact congrFun h ⟨n, hn⟩
  · have h1 := l.2
    have h2 := l'.2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- Ledger: prop-3.2. Supporting list-law identity. -/
noncomputable instance instFintypeQuantumCandidateList {Col : Type} [Fintype Col] [DecidableEq Col] {T : ℕ} :
    Fintype (QuantumCandidateList Col T) :=
  Fintype.ofInjective _ quantumCandidateList_code_injective

/-- Ledger: prop-3.2. A coherent law on bounded lists is a probability law.
The explicit subtype keeps this signature in the existing list vocabulary.
-/
theorem quantumCandidateList_probability {ι Col : Type} [Fintype Col]
    [DecidableEq Col] {T c : ℕ}
    {law : BitInput ι → {L : List Col // L.length ≤ T} → ℝ}
    (h : Samples c law) :
    (∀ x o, 0 ≤ law x o) ∧ (∀ x, ∑ o, law x o = 1) :=
  ⟨h.nonneg, h.sum_eq_one⟩

/-- Ledger: prop-3.2. Supporting list-law identity. -/
theorem quantumPoint_val {Col : Type} {T : ℕ} (a b : QuantumCandidateList Col T) : pt a.1 b.1 = pt a b := by
  by_cases h : a = b
  · subst h; rw [pt_self, pt_self]
  · rw [pt_of_ne h, pt_of_ne fun e => h (Subtype.ext e)]

/-! ## The law of the listed candidates -/

section Law

variable {Col : Type} [Fintype Col]

/-- Ledger: prop-3.2. The law of the list after `n` further stages from history `L`: a stage fails with
probability `g L` and the list is returned; otherwise pivot `p` is appended with
probability `w_p / W`. -/
noncomputable def quantumListLaw (a : Col → Col → ℝ) (g : List Col → ℝ) :
    ℕ → List Col → List Col → ℝ
  | 0, L, out => pt L out
  | n + 1, L, out => g L * pt L out +
      (1 - g L) * ∑ p, weight a L p / total (weight a L) * quantumListLaw a g n (p :: L) out

variable [DecidableEq Col]

/-- Ledger: prop-3.2. Supporting list-law identity. -/
theorem quantumPoint_sum {T : ℕ} (L : List Col) (hL : L.length ≤ T) (h : List Col → ℝ) :
    ∑ o : QuantumCandidateList Col T, pt L o.1 * h o.1 = h L := by
  rw [Finset.sum_eq_single (⟨L, hL⟩ : QuantumCandidateList Col T)]
  · simp [pt_self]
  · intro o _ ho
    rw [pt_of_ne fun e => ho (Subtype.ext e.symm), zero_mul]
  · simp

/-- Ledger: prop-3.2. Verifying the returned list is the continuation value `tval`. -/
theorem quantumListLaw_vall {T : ℕ} (a : Col → Col → ℝ) (g : List Col → ℝ) (v : Col → ℝ)
    (n : ℕ) (L : List Col) (hL : L.length + n ≤ T) :
    ∑ o : QuantumCandidateList Col T, quantumListLaw a g n L o.1 * vall v o.1 = tval a v g n L := by
  induction n generalizing L with
  | zero => simpa [quantumListLaw, tval] using quantumPoint_sum L (by omega) (vall v)
  | succ n ih =>
    simp only [quantumListLaw, tval]
    rw [show (∑ o : QuantumCandidateList Col T, (g L * pt L o.1 + (1 - g L) *
        ∑ p, weight a L p / total (weight a L) * quantumListLaw a g n (p :: L) o.1) * vall v o.1) =
        g L * ∑ o : QuantumCandidateList Col T, pt L o.1 * vall v o.1 + (1 - g L) *
        ∑ p, weight a L p / total (weight a L) *
          ∑ o : QuantumCandidateList Col T, quantumListLaw a g n (p :: L) o.1 * vall v o.1 by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      congr 1
      exact Finset.sum_comm]
    rw [quantumPoint_sum L (by omega)]
    have hs : ∀ p, ∑ o : QuantumCandidateList Col T, quantumListLaw a g n (p :: L) o.1 * vall v o.1 =
        tval a v g n (p :: L) := fun p => ih (p :: L) (by simp only [List.length_cons]; omega)
    simp only [hs]

/-- Ledger: prop-3.2. Every entry of the list law is nonnegative. -/
theorem quantumListLaw_nonneg {a : Col → Col → ℝ} {g : List Col → ℝ}
    (ha : UnitValued a) (hg : ∀ L, 0 ≤ g L ∧ g L ≤ 1)
    (n : ℕ) (L out : List Col) : 0 ≤ quantumListLaw a g n L out := by
  induction n generalizing L with
  | zero => exact pt_nonneg L out
  | succ n ih =>
    have hgL := hg L
    change 0 ≤ g L * pt L out + (1 - g L) *
      ∑ p, weight a L p / total (weight a L) * quantumListLaw a g n (p :: L) out
    apply add_nonneg (mul_nonneg hgL.1 (pt_nonneg L out))
    apply mul_nonneg (by linarith)
    exact Finset.sum_nonneg fun p _ =>
      mul_nonneg (ratio_nonneg ha L p) (ih (p :: L))

/-- Ledger: prop-3.2. The bounded-list law has total probability one.
The zero-weight hypothesis is necessary because division in Lean is totalized.
-/
theorem quantumListLaw_total {T : ℕ} (a : Col → Col → ℝ) (g : List Col → ℝ)
    (hz : ∀ L, total (weight a L) = 0 → g L = 1)
    (n : ℕ) (L : List Col) (hL : L.length + n ≤ T) :
    ∑ o : QuantumCandidateList Col T, quantumListLaw a g n L o.1 = 1 := by
  induction n generalizing L with
  | zero =>
    simpa only [quantumListLaw, mul_one] using
      quantumPoint_sum (T := T) L (by omega) (fun _ => (1 : ℝ))
  | succ n ih =>
    have hpt : ∑ o : QuantumCandidateList Col T, pt L o.1 = 1 := by
      simpa only [mul_one] using
        quantumPoint_sum (T := T) L (by omega) (fun _ => (1 : ℝ))
    have hsum : (∑ o : QuantumCandidateList Col T, quantumListLaw a g (n + 1) L o.1) =
        g L * (∑ o : QuantumCandidateList Col T, pt L o.1) +
        (1 - g L) * ∑ p, weight a L p / total (weight a L) *
          ∑ o : QuantumCandidateList Col T, quantumListLaw a g n (p :: L) o.1 := by
      simp only [quantumListLaw, Finset.sum_add_distrib, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
      congr 1
      exact Finset.sum_comm
    have hs : ∀ p, (∑ o : QuantumCandidateList Col T,
        quantumListLaw a g n (p :: L) o.1) = 1 :=
      fun p => ih (p :: L) (by simp only [List.length_cons]; omega)
    rw [hsum, hpt]
    simp only [hs, mul_one]
    by_cases hW : total (weight a L) = 0
    · rw [hz L hW]
      ring
    · rw [sum_ratio L hW]
      ring

/-- Ledger: prop-3.2. The verifier "is `s` listed" turns `vall` into membership. -/
theorem quantumVall_indicator (s : Col) (l : List Col) :
    vall (fun c => if s = c then 1 else 0) l = if s ∈ l then 1 else 0 := by
  induction l with
  | nil => simp [vall]
  | cons c l ih =>
    simp only [vall, ih, List.mem_cons]
    by_cases h : s = c <;> simp [h]

variable {a : Col → Col → ℝ} {v : Col → ℝ} {f : List Col → ℝ}

/-- Ledger: claim-coupling. The coupling of `tval_lower` for a verifier that accepts `s` with certainty: no
factor `1 - ε` is lost. -/
theorem quantumList_coupling (ha : UnitValued a) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1)
    (hf : ∀ L, 0 ≤ f L ∧ f L ≤ 1) (hz : ∀ L, total (weight a L) = 0 → f L = 1) {s : Col}
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hd : Dominant a ε s) (hvs : v s = 1) {T₀ : ℕ}
    (hT : (T₀ : ℝ) * ε < 1 / 2) (hfail : ∀ L : List Col, L.length ≤ T₀ → s ∉ L → f L ≤ ε)
    (T : ℕ) (L : List Col) (hL : L.length + T ≤ T₀) :
    1 - missFrom a s T L - T * ε ≤ tval a v f T L := by
  classical
  induction T generalizing L with
  | zero =>
    by_cases hs : s ∈ L
    · have h1 := le_vall_of_mem hv hs
      simp only [missFrom, expectFrom, tval, hs, not_true_eq_false, ite_false]
      push_cast
      linarith
    · have h1 := vall_nonneg hv L
      simp [missFrom, expectFrom, tval, hs, h1]
  | succ T ih =>
    have hU := missFrom_nonneg ha s (T + 1) L
    by_cases hs : s ∈ L
    · have h1 := le_tval_of_mem ha hv hf hz (T + 1) hs
      have hT0 : (0 : ℝ) ≤ ((T + 1 : ℕ) : ℝ) * ε := by positivity
      linarith
    · have hW := half_lt_total ha hε0 hε1 hd hT L (by omega) hs
      have hW0 : total (weight a L) ≠ 0 := by linarith
      obtain ⟨hf0, hf1⟩ := hf L
      have hfε := hfail L (by omega) hs
      have hval : missFrom a s (T + 1) L =
          ∑ p, weight a L p / total (weight a L) * missFrom a s T (p :: L) := by
        simp only [missFrom, expectFrom, hW0, ite_false]
      obtain ⟨X, hX⟩ : ∃ X, X = 1 - missFrom a s (T + 1) L - T * ε := ⟨_, rfl⟩
      have hY : X ≤ ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) := by
        calc X
            = ∑ p, weight a L p / total (weight a L) *
                (1 - missFrom a s T (p :: L) - T * ε) := by
              have e : ∀ p, weight a L p / total (weight a L) *
                  (1 - missFrom a s T (p :: L) - T * ε) =
                  (1 - T * ε) * (weight a L p / total (weight a L)) -
                    (weight a L p / total (weight a L) * missFrom a s T (p :: L)) :=
                fun p => by ring
              rw [hX, hval, Finset.sum_congr rfl fun p _ => e p, Finset.sum_sub_distrib,
                ← Finset.mul_sum, sum_ratio L hW0]
              ring
          _ ≤ _ := Finset.sum_le_sum fun p _ => mul_le_mul_of_nonneg_left
              (ih (p :: L) (by simp only [List.length_cons]; omega)) (ratio_nonneg ha L p)
      have hA := vall_nonneg hv L
      have hX1 : X ≤ 1 := by
        have : (0 : ℝ) ≤ T * ε := by positivity
        rw [hX]; linarith
      have hgoal : 1 - missFrom a s (T + 1) L - ((T + 1 : ℕ) : ℝ) * ε = X - ε := by
        rw [hX]; push_cast; ring
      simp only [tval]
      rw [hgoal]
      have hprod : 0 ≤ f L * vall v L := mul_nonneg hf0 hA
      have h1f : 0 ≤ 1 - f L := by linarith
      have hstep : (1 - f L) * X ≤ (1 - f L) *
          ∑ p, weight a L p / total (weight a L) * tval a v f T (p :: L) :=
        mul_le_mul_of_nonneg_left hY h1f
      have hkey : X - ε ≤ (1 - f L) * X := by
        by_cases hXn : 0 ≤ X
        · nlinarith
        · nlinarith
      linarith

end Law

/-- Ledger: claim-tournament-cost. Logical reads per amplified stage at the
maximum history length. The compiled `stageCost` is twice this quantity.
-/
noncomputable def quantumStageReads (m T cc : ℕ) (ε : ℝ) : ℕ :=
  trialCount ε * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (T * cc))

/-- Ledger: claim-tournament-cost. Exact read-to-bit-query conversion for the
complete tournament. -/
theorem quantumStageReads_compile (m T cc : ℕ) (ε : ℝ) :
    2 * (T * quantumStageReads m T cc ε) = T * stageCost m T cc ε := by
  unfold quantumStageReads stageCost
  ring

/-! ## Proposition 3.2 -/

variable {ι Col : Type} [Fintype ι] [Inhabited ι] [Fintype Col] [DecidableEq Col]

/-- Ledger: prop-3.2. Proposition 3.2 in the paper's list-valued form. Fix `m ≥ 2`
candidates, `T = ⌈log₂(1000 m)⌉` and `ε = 1/(1000 T)`. Comparisons are coherent
samplers of `cc` reads each (all workspace retained), with probabilities `a x i j`
satisfying (10) at every oracle input `x`. There is a program making at most
`T · stageCost` bit queries on every branch of every input whose classical result is a
list of at most `T` candidates, such that, pointwise in `x`, every `i_*` with
`a x i_* j ≥ 1 - ε` for all `j ≠ i_*` is in the list with probability at least
`1 - 2m/2^T - Tε`.

This theorem gives a coherent sampler with an actual bounded-list output label,
then compiles it to the adaptive bit-query model. Its query bound is the explicit expression
`T · stageCost m T cc ε = T · trialCount ε · 2 (2 ⌈10 √(2m)⌉ + 1) · T cc`, which is bounded by `6072 cc √m T² log T` in `QuantumTournamentFacts.lean`. Unit
values of `a` follow from the samplers and are not assumed. -/
theorem quantumTournament_list {cc : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hm : 2 ≤ Fintype.card Col) (hc : ∀ x, IsComparison (a x))
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b) :
    let m := Fintype.card Col
    let T := Tval m
    let ε := epsval m
    ∃ law : BitInput ι → QuantumCandidateList Col T → ℝ,
      Samples (T * quantumStageReads m T cc ε) law ∧
      Runs (T * stageCost m T cc ε) law ∧
      (∀ x o, 0 ≤ law x o) ∧
      (∀ x, ∑ o, law x o = 1) ∧
      ∀ x s, Dominant (a x) ε s →
        1 - 2 * (m : ℝ) / 2 ^ T - T * ε ≤ ∑ o : QuantumCandidateList Col T, if s ∈ o.1 then law x o else 0 := by
  classical
  intro m T ε
  have : Nonempty Col := Fintype.card_pos_iff.1 (by omega)
  have hu : ∀ x, UnitValued (a x) := by
    intro x
    unfold UnitValued
    intro i j
    have h1 := (hcmp i j).nonneg x true
    have h0 := (hcmp i j).nonneg x false
    simp [bern] at h1 h0
    exact ⟨h1, by linarith⟩
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
      Samples (trialCount ε * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (L.length * cc)))
        fun x => ampLaw (f x) fun b => stageLaw (a x) L (some b) :=
    fun L => quantum_amplify_samples (stage_samples hcmp L) hγ hεpos
  choose f hf01 hfγ hfz hrun using hamp
  have hg01 : ∀ x L, 0 ≤ f L x ∧ f L x ≤ 1 := fun x L => hf01 L x
  have hgz : ∀ x L, total (weight (a x) L) = 0 → f L x = 1 := fun x L h =>
    hfz L x (by rw [sum_stageLaw_some, h, zero_div])
  have hratio : ∀ x L p, stageLaw (a x) L (some p) / ∑ c, stageLaw (a x) L (some c) =
      weight (a x) L p / total (weight (a x) L) := fun x L p => by
    rw [sum_stageLaw_some, stageLaw_some]
    exact div_div_div_cancel_right₀ hm0 _ _
  let Cs := quantumStageReads m T cc ε
  have hstageSamples : ∀ L : List Col, L.length ≤ T → Samples Cs
      fun x => ampLaw (f L x) fun b => stageLaw (a x) L (some b) := fun L hL => by
    refine (hrun L).mono ?_
    change trialCount ε * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (L.length * cc)) ≤
      trialCount ε * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (T * cc))
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hL))
  have hsampleT : ∀ (n : ℕ) (L : List Col), L.length + n ≤ T →
      Samples (n * Cs) fun x (o : QuantumCandidateList Col T) => quantumListLaw (a x) (fun L => f L x) n L o.1 := by
    intro n
    induction n with
    | zero =>
      intro L hL
      refine ((Samples.pure (ι := ι) (⟨L, by omega⟩ : QuantumCandidateList Col T)).mono (Nat.zero_le _)).congr
        fun x o => ?_
      simp only [quantumListLaw]
      exact quantumPoint_val (⟨L, by omega⟩ : QuantumCandidateList Col T) o
    | succ n ih =>
      intro L hL
      let K : Option Col → BitInput ι → QuantumCandidateList Col T → ℝ := fun o x out =>
        o.elim (pt L out.1) fun p => quantumListLaw (a x) (fun L => f L x) n (p :: L) out.1
      have hK : ∀ o, Samples (n * Cs) (K o) := fun o => by
        cases o with
        | none =>
          refine ((Samples.pure (ι := ι) (⟨L, by omega⟩ : QuantumCandidateList Col T)).mono (Nat.zero_le _)).congr
            fun x o => ?_
          exact quantumPoint_val (⟨L, by omega⟩ : QuantumCandidateList Col T) o
        | some p =>
          exact ih (p :: L) (by simp only [List.length_cons]; omega)
      refine ((hstageSamples L (by omega)).bind hK).mono ?_ |>.congr fun x out => ?_
      · exact le_of_eq (by ring)
      · rw [Fintype.sum_option]
        simp only [K, Option.elim, ampLaw, hratio, quantumListLaw, Finset.mul_sum, mul_assoc]
  refine ⟨fun x o => quantumListLaw (a x) (fun L => f L x) T [] o.1,
    ?_, ?_, ?_, ?_, fun x s hd => ?_⟩
  · exact hsampleT T [] (by simp)
  · have hphysical := (hsampleT T [] (by simp)).runs
    exact hphysical.mono (le_of_eq (quantumStageReads_compile m T cc ε))
  · intro x o
    exact quantumListLaw_nonneg (hu x) (hg01 x) T [] o.1
  · intro x
    exact quantumListLaw_total (a x) (fun L => f L x) (hgz x) T [] (by simp)
  · have hT' : (T : ℝ) * ε < 1 / 2 := by rw [hTε]; norm_num
    obtain ⟨v, hv⟩ : ∃ v : Col → ℝ, v = fun c => if s = c then 1 else 0 := ⟨_, rfl⟩
    have hv01 : ∀ c, 0 ≤ v c ∧ v c ≤ 1 := fun c => by
      rw [hv]
      dsimp only
      split_ifs <;> norm_num
    have hfail : ∀ L : List Col, L.length ≤ T → s ∉ L → f L x ≤ ε := fun L hL hs => by
      refine hfγ L x ?_
      rw [sum_stageLaw_some]
      have hW := half_lt_total (hu x) hε0 (by linarith) hd hT' L hL hs
      rw [le_div_iff₀ hm0']
      have : (2 * (m : ℝ))⁻¹ * m = 1 / 2 := by field_simp
      linarith
    have hlow := quantumList_coupling (f := fun L => f L x) (hu x) hv01 (hg01 x) (hgz x) hε0
      (by linarith) hd (by rw [hv]; simp) hT' hfail T [] (by simp)
    have hideal := (ideal_tournament (hc x) (hu x) hm hd).2.1
    have hmiss : missFrom (a x) s T [] ≤ 2 * (m : ℝ) / 2 ^ T := by
      refine le_trans (le_of_eq ?_) hideal
      unfold missFrom prob expectAfter
      congr 1
      funext w l
      by_cases h : s ∈ l <;> simp [h]
    have hsum : ∑ o : QuantumCandidateList Col T,
        (if s ∈ o.1 then quantumListLaw (a x) (fun L => f L x) T [] o.1 else 0) =
        tval (a x) v (fun L => f L x) T [] := by
      rw [← quantumListLaw_vall (T := T) (a x) (fun L => f L x) v T [] (by simp)]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hv, quantumVall_indicator]
      split_ifs <;> simp
    beta_reduce
    rw [hsum]
    linarith

end QuarticQuery.Paper

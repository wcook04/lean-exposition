module

public import QuarticQuery.Upper.Tournament
public import QuarticQuery.Paper.QuantumUpper

/-!
# Proposition 3.2 in the paper's list-valued form

`Upper.tournament_runs` consumes the tournament's list with a verifier in continuation
form. Here the same stages are composed with a continuation that outputs the list
itself, so the program's classical result is a list of at most `T` candidates, and the
guarantee is list membership with probability at least `1 - 2m/2^T - Tε`, as in the
paper.

`QuantumUpper` also exports a coherent list-output witness, an explicit physical
query bound, and a separate literal tensor-state preparation. The latter has the
same successful-index law as the short-circuit sampler without asserting equality
of their complete states. The declarations below preserve the earlier interface.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Tournament QuarticQuery.Amplification

/-! ## Lists of at most `T` candidates as an output alphabet -/

/-- Lists of at most `T` candidates. -/
abbrev BList (Col : Type) (T : ℕ) := {l : List Col // l.length ≤ T}

theorem bList_code_injective {Col : Type} {T : ℕ} :
    Function.Injective fun l : BList Col T => fun i : Fin (T + 1) => l.1[i.val]? := by
  intro l l' h
  apply Subtype.ext
  apply List.ext_getElem?
  intro n
  by_cases hn : n < T + 1
  · exact congrFun h ⟨n, hn⟩
  · have h1 := l.2
    have h2 := l'.2
    rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

noncomputable instance instFintypeBList {Col : Type} [Fintype Col] [DecidableEq Col] {T : ℕ} :
    Fintype (BList Col T) :=
  Fintype.ofInjective _ bList_code_injective

theorem pt_val {Col : Type} {T : ℕ} (a b : BList Col T) : pt a.1 b.1 = pt a b := by
  by_cases h : a = b
  · subst h; rw [pt_self, pt_self]
  · rw [pt_of_ne h, pt_of_ne fun e => h (Subtype.ext e)]

/-! ## The law of the listed candidates -/

section Law

variable {Col : Type} [Fintype Col]

/-- The law of the list after `n` further stages from history `L`: a stage fails with
probability `g L` and the list is returned; otherwise pivot `p` is appended with
probability `w_p / W`. -/
noncomputable def listLaw (a : Col → Col → ℝ) (g : List Col → ℝ) :
    ℕ → List Col → List Col → ℝ
  | 0, L, out => pt L out
  | n + 1, L, out => g L * pt L out +
      (1 - g L) * ∑ p, weight a L p / total (weight a L) * listLaw a g n (p :: L) out

variable [DecidableEq Col]

theorem sum_pt_bList {T : ℕ} (L : List Col) (hL : L.length ≤ T) (h : List Col → ℝ) :
    ∑ o : BList Col T, pt L o.1 * h o.1 = h L := by
  rw [Finset.sum_eq_single (⟨L, hL⟩ : BList Col T)]
  · simp [pt_self]
  · intro o _ ho
    rw [pt_of_ne fun e => ho (Subtype.ext e.symm), zero_mul]
  · simp

/-- Verifying the returned list is the continuation value `tval`. -/
theorem sum_listLaw_vall {T : ℕ} (a : Col → Col → ℝ) (g : List Col → ℝ) (v : Col → ℝ)
    (n : ℕ) (L : List Col) (hL : L.length + n ≤ T) :
    ∑ o : BList Col T, listLaw a g n L o.1 * vall v o.1 = tval a v g n L := by
  induction n generalizing L with
  | zero => simpa [listLaw, tval] using sum_pt_bList L (by omega) (vall v)
  | succ n ih =>
    simp only [listLaw, tval]
    rw [show (∑ o : BList Col T, (g L * pt L o.1 + (1 - g L) *
        ∑ p, weight a L p / total (weight a L) * listLaw a g n (p :: L) o.1) * vall v o.1) =
        g L * ∑ o : BList Col T, pt L o.1 * vall v o.1 + (1 - g L) *
        ∑ p, weight a L p / total (weight a L) *
          ∑ o : BList Col T, listLaw a g n (p :: L) o.1 * vall v o.1 by
      simp only [add_mul, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
      congr 1
      exact Finset.sum_comm]
    rw [sum_pt_bList L (by omega)]
    have hs : ∀ p, ∑ o : BList Col T, listLaw a g n (p :: L) o.1 * vall v o.1 =
        tval a v g n (p :: L) := fun p => ih (p :: L) (by simp only [List.length_cons]; omega)
    simp only [hs]

/-- The verifier "is `s` listed" turns `vall` into membership. -/
theorem vall_indicator (s : Col) (l : List Col) :
    vall (fun c => if s = c then 1 else 0) l = if s ∈ l then 1 else 0 := by
  induction l with
  | nil => simp [vall]
  | cons c l ih =>
    simp only [vall, ih, List.mem_cons]
    by_cases h : s = c <;> simp [h]

variable {a : Col → Col → ℝ} {v : Col → ℝ} {f : List Col → ℝ}

/-- The coupling of `tval_lower` for a verifier that accepts `s` with certainty: no
factor `1 - ε` is lost. -/
theorem tval_lower_one (ha : UnitValued a) (hv : ∀ c, 0 ≤ v c ∧ v c ≤ 1)
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

This is the paper's statement with its query bound left as the explicit expression
`T · stageCost m T cc ε = T · trialCount ε · 2 (2 ⌈10 √(2m)⌉ + 1) · T cc`, which is
`O(cc √m T log T · T)`; the asymptotic simplification is not formalised here. Unit
values of `a` follow from the samplers and are not assumed. -/
theorem prop_3_2 {cc : ℕ} {a : BitInput ι → Col → Col → ℝ}
    (hm : 2 ≤ Fintype.card Col) (hc : ∀ x, IsComparison (a x))
    (hcmp : ∀ i p, Samples cc fun x b => bern (a x i p) b) :
    let m := Fintype.card Col
    let T := Tval m
    let ε := epsval m
    ∃ law : BitInput ι → BList Col T → ℝ,
      Runs (T * stageCost m T cc ε) law ∧
      ∀ x s, Dominant (a x) ε s →
        1 - 2 * (m : ℝ) / 2 ^ T - T * ε ≤ ∑ o : BList Col T, if s ∈ o.1 then law x o else 0 := by
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
      Runs (trialCount ε * (2 * ((2 * iterationBound ((2 * (m : ℝ))⁻¹) + 1) * (L.length * cc))))
        fun x => ampLaw (f x) fun b => stageLaw (a x) L (some b) :=
    fun L => (stage_samples hcmp L).amplify hγ hεpos
  choose f hf01 hfγ hfz hrun using hamp
  have hg01 : ∀ x L, 0 ≤ f L x ∧ f L x ≤ 1 := fun x L => hf01 L x
  have hgz : ∀ x L, total (weight (a x) L) = 0 → f L x = 1 := fun x L h =>
    hfz L x (by rw [sum_stageLaw_some, h, zero_div])
  have hratio : ∀ x L p, stageLaw (a x) L (some p) / ∑ c, stageLaw (a x) L (some c) =
      weight (a x) L p / total (weight (a x) L) := fun x L p => by
    rw [sum_stageLaw_some, stageLaw_some]
    exact div_div_div_cancel_right₀ hm0 _ _
  obtain ⟨Cs, hCs⟩ : ∃ Cs, Cs = stageCost m T cc ε := ⟨_, rfl⟩
  have hstageRuns : ∀ L : List Col, L.length ≤ T → Runs Cs
      fun x => ampLaw (f L x) fun b => stageLaw (a x) L (some b) := fun L hL => by
    refine (hrun L).mono ?_
    rw [hCs, stageCost]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _
      (Nat.mul_le_mul_right _ hL)))
  have hrunT : ∀ (n : ℕ) (L : List Col), L.length + n ≤ T →
      Runs (n * Cs) fun x (o : BList Col T) => listLaw (a x) (fun L => f L x) n L o.1 := by
    intro n
    induction n with
    | zero =>
      intro L hL
      refine ((Runs.pure (ι := ι) (⟨L, by omega⟩ : BList Col T)).mono (Nat.zero_le _)).congr
        fun x o => ?_
      simp only [listLaw]
      exact pt_val (⟨L, by omega⟩ : BList Col T) o
    | succ n ih =>
      intro L hL
      let K : Option Col → BitInput ι → BList Col T → ℝ := fun o x out =>
        o.elim (pt L out.1) fun p => listLaw (a x) (fun L => f L x) n (p :: L) out.1
      have hK : ∀ o, Runs (n * Cs) (K o) := fun o => by
        cases o with
        | none =>
          refine ((Runs.pure (ι := ι) (⟨L, by omega⟩ : BList Col T)).mono (Nat.zero_le _)).congr
            fun x o => ?_
          exact pt_val (⟨L, by omega⟩ : BList Col T) o
        | some p =>
          exact ih (p :: L) (by simp only [List.length_cons]; omega)
      refine ((hstageRuns L (by omega)).bind hK).mono ?_ |>.congr fun x out => ?_
      · exact le_of_eq (by ring)
      · rw [Fintype.sum_option]
        simp only [K, Option.elim, ampLaw, hratio, listLaw, Finset.mul_sum, mul_assoc]
  refine ⟨fun x o => listLaw (a x) (fun L => f L x) T [] o.1, ?_, fun x s hd => ?_⟩
  · exact (hrunT T [] (by simp)).mono (by rw [hCs])
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
    have hlow := tval_lower_one (f := fun L => f L x) (hu x) hv01 (hg01 x) (hgz x) hε0
      (by linarith) hd (by rw [hv]; simp) hT' hfail T [] (by simp)
    have hideal := (ideal_tournament (hc x) (hu x) hm hd).2.1
    have hmiss : missFrom (a x) s T [] ≤ 2 * (m : ℝ) / 2 ^ T := by
      refine le_trans (le_of_eq ?_) hideal
      unfold missFrom prob expectAfter
      congr 1
      funext w l
      by_cases h : s ∈ l <;> simp [h]
    have hsum : ∑ o : BList Col T,
        (if s ∈ o.1 then listLaw (a x) (fun L => f L x) T [] o.1 else 0) =
        tval (a x) v (fun L => f L x) T [] := by
      rw [← sum_listLaw_vall (T := T) (a x) (fun L => f L x) v T [] (by simp)]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [hv, vall_indicator]
      split_ifs <;> simp
    beta_reduce
    rw [hsum]
    linarith

end QuarticQuery.Paper

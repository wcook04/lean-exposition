module

public import QuarticQuery.LowerBound.DirectProduct
public import QuarticQuery.LowerBound.Planted.Heavy

/-!
# Reaching the planted cell (equations 21 and 22)

The simulator runs a tree with the target strings hidden. Queries outside the
target are answered from free side information, and queries into it become
queries of an `OutTree`. It aborts before spending more than its budget, and at
time `t` it outputs the address of the proposed cell. It makes at most `L`
queries on every input. The bound is on a joint event: "the run has not
overspent and reached the true cell" implies "the capped simulator guessed the
true address". Nothing conditions on a column being nonheavy, which is the point
of the AND example in the worked notes.
-/

@[expose] public section

open Finset

namespace QuarticQuery

section Abstract

variable {ι ρ β : Type}

/-- Ledger: eq-21. Run to time `t` with `c` target queries left. `tgt` names the
target coordinate of a location, `guess` reads an output from the location
proposed at time `t`, and `base` answers everything outside the target. -/
def simTree (tgt : ι → Option ρ) (guess : ι → Option β) (dflt : β) (base : BitInput ι) :
    QueryTree ι → ℕ → ℕ → OutTree ρ β
  | .leaf _, _, _ => .leaf dflt
  | .query q _ _, 0, _ => .leaf ((guess q).getD dflt)
  | .query q l u, t + 1, c =>
      match tgt q with
      | none =>
          if base q then simTree tgt guess dflt base u t c
          else simTree tgt guess dflt base l t c
      | some p =>
          match c with
          | 0 => .leaf dflt
          | c + 1 => .query p (simTree tgt guess dflt base l t c)
              (simTree tgt guess dflt base u t c)

variable {tgt : ι → Option ρ} {guess : ι → Option β} {dflt : β} {base : BitInput ι}

/-- Ledger: eq-21. The simulator spends at most its budget. -/
theorem depth_simTree_le (T : QueryTree ι) (t c : ℕ) :
    (simTree tgt guess dflt base T t c).depth ≤ c := by
  induction T generalizing t c with
  | leaf b => simp [simTree, OutTree.depth]
  | query q l u ihl ihu =>
    cases t with
    | zero => simp [simTree, OutTree.depth]
    | succ t =>
      simp only [simTree]
      cases hq : tgt q with
      | none =>
        simp only
        split_ifs
        · exact ihu t c
        · exact ihl t c
      | some p =>
        cases c with
        | zero => simp [OutTree.depth]
        | succ c =>
          have h1 := ihl t c
          have h2 := ihu t c
          simp only [OutTree.depth]
          omega

/-- Ledger: eq-21. If the run on `x` proposes at time `t` a location naming `s`,
having spent at most `c` target queries before it, the simulator outputs `s`. -/
theorem eval_simTree (x : BitInput ι) (V : BitInput ρ)
    (hbase : ∀ q, tgt q = none → x q = base q) (hV : ∀ q p, tgt q = some p → x q = V p)
    (T : QueryTree ι) (t c : ℕ) {q : ι} {s : β} (hq : (T.path x)[t]? = some q)
    (hs : guess q = some s)
    (hc : ((T.path x).take t).countP (fun q => (tgt q).isSome) ≤ c) :
    (simTree tgt guess dflt base T t c).eval V = s := by
  induction T generalizing t c with
  | leaf b => simp at hq
  | query q₀ l u ihl ihu =>
    cases t with
    | zero =>
      have : q₀ = q := by simpa [QueryTree.path_query] using hq
      subst this
      simp [simTree, OutTree.eval, hs]
    | succ t =>
      rw [QueryTree.path_query, List.getElem?_cons_succ] at hq
      rw [QueryTree.path_query, List.take_succ_cons, List.countP_cons] at hc
      simp only [simTree]
      cases htq : tgt q₀ with
      | none =>
        simp only [htq, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, add_zero] at hc
        simp only
        rw [← hbase q₀ htq]
        cases hx : x q₀
        · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hq hc ⊢
          exact ihl t c hq hc
        · simp only [hx, ↓reduceIte] at hq hc ⊢
          exact ihu t c hq hc
      | some p =>
        simp only [htq, Option.isSome_some, ↓reduceIte] at hc
        cases c with
        | zero => omega
        | succ c =>
          simp only [OutTree.eval]
          rw [← hV q₀ p htq]
          cases hx : x q₀
          · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hq hc ⊢
            exact ihl t c hq (by omega)
          · simp only [hx, ↓reduceIte] at hq hc ⊢
            exact ihu t c hq (by omega)

end Abstract

section Concrete

variable {κ : Type} [Fintype κ] [DecidableEq κ] {ℓ r S : ℕ}

/-- The address named by a cell location in column `I`. -/
def cellGuess (I : Column ℓ) (q : BitLoc ℓ r S κ) : Option (Address r) :=
  match cellOf q with
  | some (c, s) => if c = I then some s else none
  | none => none

/-- Ledger: eq-21. The joint event: column `I` is not heavy on the dummy run, and
that run visits the cell of `I` at the true address. -/
noncomputable def reachedCell (f : PartialBool κ) (L : ℕ) (T : QueryTree (BitLoc ℓ r S κ))
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ) : ℝ :=
  ind (¬ L < aQueries I (T.path (dummy J A)) ∧
    ∃ q ∈ T.path (dummy J A), cellOf q = some (I, trueAddr f (A I)))

/-- A cell location of column `I` names its address. -/
theorem cellGuess_of_cellOf {I : Column ℓ} {q : BitLoc ℓ r S κ} {s : Address r}
    (h : cellOf q = some (I, s)) : cellGuess I q = some s := by
  simp [cellGuess, h]

/-- Outside the strings of column `I`, replacing them changes nothing. -/
theorem dummy_update_of_aTarget_none {J : Column ℓ → Column ℓ}
    {A : Column ℓ → Fin r → BitInput κ} {I : Column ℓ} {U : Fin r → BitInput κ}
    {q : BitLoc ℓ r S κ} (h : aTarget I q = none) :
    dummy J (Function.update A I U) q = dummy J A q := by
  rcases q with q | ⟨c, a, q⟩ | q
  · rfl
  · have hc : c ≠ I := by
      intro hc
      simp [aTarget, hc] at h
    simp [dummy, Function.update_of_ne hc]
  · rfl

/-- Inside them, the input reads the redrawn strings. -/
theorem dummy_update_of_aTarget_some {J : Column ℓ → Column ℓ}
    {A : Column ℓ → Fin r → BitInput κ} {I : Column ℓ} {U : Fin r → BitInput κ}
    {q : BitLoc ℓ r S κ} {p : Fin r × κ} (h : aTarget I q = some p) :
    dummy J (Function.update A I U) q = Function.uncurry U p := by
  rcases q with q | ⟨c, a, q⟩ | q
  · simp [aTarget] at h
  · by_cases hc : c = I
    · subst hc
      simp only [aTarget, if_true, Option.some.injEq] at h
      subst h
      simp [dummy, Function.uncurry]
    · simp [aTarget, hc] at h
  · simp [aTarget] at h

/-- Ledger: eq-22. Redrawing the strings of column `I`, the joint event has weight
at most `G ρ`, where `ρ` bounds every capped guesser. The side information is `A`
off column `I` and `J`, which stay fixed. The union is over times `t < G`. -/
theorem avg_reachedCell_le {f : PartialBool κ} {μ : BitInput κ → ℝ} {L G : ℕ} {ρ : ℝ}
    (hμ : ∀ x, 0 ≤ μ x) (hdom : ∀ x, μ x ≠ 0 → promised f x)
    (hguess : ∀ U : OutTree (Fin r × κ) (Fin r → Bool), (U.capped fun _ => L) →
      guessSuccess f (fun _ => μ) U ≤ ρ)
    (T : QueryTree (BitLoc ℓ r S κ)) (hT : T.depth ≤ G)
    (J : Column ℓ → Column ℓ) (A : Column ℓ → Fin r → BitInput κ) (I : Column ℓ) :
    avg (prodW μ) (fun U => reachedCell f L T J (Function.update A I U) I) ≤ (G : ℝ) * ρ := by
  let sims : ℕ → OutTree (Fin r × κ) (Fin r → Bool) := fun t =>
    simTree (aTarget I) (cellGuess I) (fun _ => false) (dummy J A) T t L
  have hsims : ∀ t, (sims t).capped fun _ => L := fun t =>
    OutTree.capped_of_depth_le (depth_simTree_le T t L) fun _ => le_rfl
  have hpoint : ∀ U : Fin r → BitInput κ,
      prodW μ U * reachedCell f L T J (Function.update A I U) I ≤
        ∑ t ∈ range G, prodW μ U *
          if ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) then 1 else 0 := by
    intro U
    have hnn : ∀ t, 0 ≤ (prodW μ U *
        if ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) then (1 : ℝ) else 0) :=
      fun t => mul_nonneg (prodW_nonneg hμ U) (by split_ifs <;> norm_num)
    by_cases hz : prodW μ U = 0
    · rw [hz, zero_mul]
      exact sum_nonneg fun t _ => by simp
    have hprom : ∀ h, promised f (U h) := fun h => hdom _ (ne_zero_of_prodW_ne_zero hz h)
    set x : BitInput (BitLoc ℓ r S κ) := dummy J (Function.update A I U) with hx
    by_cases hev : ¬ L < aQueries I (T.path x) ∧
        ∃ q ∈ T.path x, cellOf q = some (I, trueAddr f (Function.update A I U I))
    · obtain ⟨hnh, q, hq, hcell⟩ := hev
      rw [Function.update_self] at hcell
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hq
      have htG : t < G := by
        have h1 := (List.getElem?_eq_some_iff.mp ht).1
        exact lt_of_lt_of_le h1 ((T.length_path_le x).trans hT)
      have hc : ((T.path x).take t).countP (fun q => (aTarget I q).isSome) ≤ L :=
        ((List.take_sublist t _).countP_le).trans (not_lt.mp hnh)
      have hs : (sims t).eval (Function.uncurry U) = trueAddr f U :=
        eval_simTree x (Function.uncurry U) (fun _ hq' => dummy_update_of_aTarget_none hq')
          (fun _ _ hq' => dummy_update_of_aTarget_some hq') T t L ht
          (cellGuess_of_cellOf hcell) hc
      have hone : ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) := fun h => by
        rw [hs]
        exact f_eq_trueAddr (hprom h)
      calc prodW μ U * reachedCell f L T J (Function.update A I U) I
          = prodW μ U * ((1 : ℝ)) := by
            rw [reachedCell, ind_true ⟨hnh, q, hq, by rw [Function.update_self]; exact hcell⟩]
        _ = prodW μ U *
            (if ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) then 1 else 0) := by
            rw [if_pos hone]
        _ ≤ _ := single_le_sum (f := fun t => prodW μ U *
            if ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) then (1 : ℝ) else 0)
            (fun t _ => hnn t) (mem_range.mpr htG)
    · rw [reachedCell, ind_false hev, mul_zero]
      exact sum_nonneg fun t _ => hnn t
  calc avg (prodW μ) (fun U => reachedCell f L T J (Function.update A I U) I)
      ≤ ∑ U : Fin r → BitInput κ, ∑ t ∈ range G, prodW μ U *
          (if ∀ h, f (U h) = some ((sims t).eval (Function.uncurry U) h) then 1 else 0) :=
        sum_le_sum fun U _ => hpoint U
    _ = ∑ t ∈ range G, guessSuccess f (fun _ => μ) (sims t) := by
        rw [sum_comm]
        rfl
    _ ≤ ∑ _t ∈ range G, ρ := sum_le_sum fun t _ => hguess _ (hsims t)
    _ = (G : ℝ) * ρ := by simp

end Concrete

end QuarticQuery

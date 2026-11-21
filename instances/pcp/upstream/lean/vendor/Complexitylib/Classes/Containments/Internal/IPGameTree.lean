/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module
public import Complexitylib.Classes.Containments.Internal.IPSubsetPSPACE
public import Complexitylib.Classes.Containments.Internal.WitnessEnum
public import Complexitylib.Classes.Containments.Internal.TranscriptEnc

/-!
# The game tree of an interactive protocol

⚠️ Unreviewed by Bolton

The value of a protocol on an input is the acceptance probability against an *optimal* prover —
a maximum over strategies, which are functions on transcripts. This file replaces that maximum
by a finite recursion over the transcript tree, which is the object a polynomial-space machine
walks.

The tree is indexed by the transcript so far. At a node the coins still in play are those
*consistent* with the recorded verifier messages (`Complexity.Protocol.consFinset`); a round
splits them by the verifier's next message and the prover picks, for each such message, the reply
maximizing the count below. Everything is counted rather than averaged: `Complexity.Protocol.gval`
is the number of coin strings that end up accepting, so the value is that count over `2 ^ coins`.

## Main definitions

- `Complexity.Protocol.runFrom` — the interaction continued from a partial transcript
- `Complexity.Protocol.consFinset` — the coins consistent with a transcript
- `Complexity.Protocol.sval` — the accepting count of a fixed strategy, as a tree recursion
- `Complexity.Protocol.gval` — the same with the prover playing optimally

## Main results

- `Complexity.Protocol.transcript_eq_runFrom` — the two ways of running agree
- `Complexity.Protocol.consFinset_append` — a round filters the coins by the verifier's message
- `Complexity.Protocol.view_eq` — the verifier's view, with the transcript encoding unfolded
- `Complexity.Protocol.gval_succ_strsLe` — the sum ranges over every short string
- `Complexity.Protocol.consistent_iff_replay` — consistency is a replay of the verifier
- `Complexity.Protocol.gvalR_zero`, `Complexity.Protocol.gvalR_succ` — the recursion a stack
  machine walks
-/

@[expose] public section

namespace Complexity

namespace Protocol

variable (prot : Protocol) (x : List Bool)

/-- **The verifier's view, unfolded.** The transcript reaches the verifier through the
concatenation `Complexity.encBody`, so extending the transcript only ever appends to it. -/
theorem view_eq (r : List Bool) (τ : Transcript) :
    view x r τ = pair (pair x r) (false :: (encBody τ ++ [true])) := by
  rw [view, protocolView, bitstringEncode_transcript]

/-! ## Running from a partial transcript -/

/-- The interaction continued for `n` more rounds from the transcript `τ`. -/
def runFrom (S : ProverStrategy) (r : List Bool) : ℕ → Transcript → Transcript
  | 0, τ => τ
  | n + 1, τ =>
      runFrom S r n (τ ++ [prot.vmsg (view x r τ), S (τ ++ [prot.vmsg (view x r τ)])])

@[simp] theorem runFrom_zero (S : ProverStrategy) (r : List Bool) (τ : Transcript) :
    prot.runFrom x S r 0 τ = τ := rfl

theorem runFrom_succ (S : ProverStrategy) (r : List Bool) (n : ℕ) (τ : Transcript) :
    prot.runFrom x S r (n + 1) τ
      = prot.runFrom x S r n
          (τ ++ [prot.vmsg (view x r τ), S (τ ++ [prot.vmsg (view x r τ)])]) := rfl

/-- The continuation appends its last round at the end, exactly as
`Complexity.Protocol.transcript` does. -/
theorem runFrom_succ' (S : ProverStrategy) (r : List Bool) :
    ∀ (n : ℕ) (τ : Transcript),
      prot.runFrom x S r (n + 1) τ
        = prot.runFrom x S r n τ
            ++ [prot.vmsg (view x r (prot.runFrom x S r n τ)),
              S (prot.runFrom x S r n τ ++ [prot.vmsg (view x r (prot.runFrom x S r n τ))])]
  | 0, τ => rfl
  | n + 1, τ => by
      rw [runFrom_succ prot x S r (n + 1) τ, runFrom_succ' S r n, runFrom_succ prot x S r n τ]

/-- **The two ways of running agree.** -/
theorem transcript_eq_runFrom (S : ProverStrategy) (r : List Bool) :
    ∀ n, prot.transcript S x r n = prot.runFrom x S r n []
  | 0 => rfl
  | n + 1 => by
      rw [transcript, runFrom_succ' prot x S r n [], transcript_eq_runFrom S r n]

/-! ## The coins still in play -/

/-- A coin string is consistent with a transcript when every verifier message recorded in it is
the one the verifier would have sent. -/
def Consistent (r : List Bool) (τ : Transcript) : Prop :=
  ∀ j, 2 * j < τ.length → τ[2 * j]! = prot.vmsg (view x r (τ.take (2 * j)))

theorem consistent_nil (r : List Bool) : prot.Consistent x r [] := by
  intro j hj
  simp at hj

/-- Extending a transcript by one round adds exactly one condition: the verifier's message. -/
theorem consistent_append (r : List Bool) (τ : Transcript) (i : ℕ) (hτ : τ.length = 2 * i)
    (v a : List Bool) :
    prot.Consistent x r (τ ++ [v, a]) ↔
      prot.Consistent x r τ ∧ v = prot.vmsg (view x r τ) := by
  have hlen : (τ ++ [v, a]).length = 2 * i + 2 := by
    rw [List.length_append, hτ]
    simp
  constructor
  · intro h
    refine ⟨fun j hj => ?_, ?_⟩
    · have hj2 : 2 * j < τ.length := hj
      have h1 : (τ ++ [v, a])[2 * j]! = τ[2 * j]! := by
        rw [getElem!_pos _ _ (by omega), getElem!_pos _ _ (by omega),
          List.getElem_append_left (by omega)]
      have h2 : (τ ++ [v, a]).take (2 * j) = τ.take (2 * j) :=
        List.take_append_of_le_length (by omega)
      have := h j (by omega)
      rw [h1, h2] at this
      exact this
    · have := h i (by omega)
      rw [getElem!_pos _ _ (by omega), List.getElem_append_right (by omega),
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)] at this
      simpa [hτ] using this
  · rintro ⟨h1, h2⟩ j hj
    rw [hlen] at hj
    rcases Nat.lt_or_ge (2 * j) τ.length with hlt | hge
    · rw [getElem!_pos _ _ (by omega), List.getElem_append_left (by omega),
        List.take_append_of_le_length (by omega), ← getElem!_pos _ _ (by omega)]
      exact h1 j hlt
    · have hji : j = i := by omega
      subst hji
      rw [getElem!_pos _ _ (by omega), List.getElem_append_right (by omega),
        List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      simpa [hτ] using h2

open Classical in
/-- The coins consistent with a transcript. -/
noncomputable def consFinset (t : ℕ) (τ : Transcript) : Finset (Fin t → Bool) :=
  Finset.univ.filter fun r => prot.Consistent x (BitString.toList r) τ

theorem consFinset_nil (t : ℕ) : prot.consFinset x t [] = Finset.univ := by
  classical
  rw [consFinset]
  exact Finset.filter_true_of_mem fun r _ => prot.consistent_nil x _

open Classical in
/-- **A round filters the coins by the verifier's message.** The reply the prover chooses plays
no part: the coins in play below a node depend only on the verifier messages above it. -/
theorem consFinset_append (t : ℕ) (τ : Transcript) (i : ℕ) (hτ : τ.length = 2 * i)
    (v a : List Bool) :
    prot.consFinset x t (τ ++ [v, a])
      = (prot.consFinset x t τ).filter
          fun r => prot.vmsg (view x (BitString.toList r) τ) = v := by
  classical
  rw [consFinset, consFinset, Finset.filter_filter]
  refine Finset.filter_congr fun r _ => ?_
  rw [prot.consistent_append x _ τ i hτ v a]
  exact ⟨fun h => ⟨h.1, h.2.symm⟩, fun h => ⟨h.1, h.2.symm⟩⟩

/-! ## The tree recursion -/

open Classical in
/-- The verifier messages still possible at a node. -/
noncomputable def vset (t : ℕ) (τ : Transcript) : Finset (List Bool) :=
  (prot.consFinset x t τ).image fun r => prot.vmsg (view x (BitString.toList r) τ)

open Classical in
/-- The coins consistent with `τ` that accept when the prover plays `S` for the remaining `n`
rounds, as a recursion down the tree. -/
noncomputable def sval (t : ℕ) (S : ProverStrategy) : ℕ → Transcript → ℕ
  | 0, τ => ((prot.consFinset x t τ).filter fun r =>
      view x (BitString.toList r) τ ∈ prot.verdict).card
  | n + 1, τ => ∑ v ∈ vset prot x t τ, sval t S n (τ ++ [v, S (τ ++ [v])])

open Classical in
/-- The same count with the prover playing optimally: at each node it picks, for every possible
verifier message, the reply maximizing the count below. -/
noncomputable def gval (t m : ℕ) : ℕ → Transcript → ℕ
  | 0, τ => ((prot.consFinset x t τ).filter fun r =>
      view x (BitString.toList r) τ ∈ prot.verdict).card
  | n + 1, τ =>
      ∑ v ∈ vset prot x t τ, (strsLe m).sup fun a => gval t m n (τ ++ [v, a])

open Classical in
theorem sval_succ (t : ℕ) (S : ProverStrategy) (n : ℕ) (τ : Transcript) :
    prot.sval x t S (n + 1) τ
      = ∑ v ∈ prot.vset x t τ, prot.sval x t S n (τ ++ [v, S (τ ++ [v])]) := by
  rw [sval]

open Classical in
theorem gval_succ (t m n : ℕ) (τ : Transcript) :
    prot.gval x t m (n + 1) τ
      = ∑ v ∈ prot.vset x t τ, (strsLe m).sup fun a => prot.gval x t m n (τ ++ [v, a]) := by
  rw [gval]

open Classical in
/-- **What the recursion counts.** -/
theorem sval_eq_card (t : ℕ) (S : ProverStrategy) :
    ∀ (n i : ℕ) (τ : Transcript), τ.length = 2 * i →
      prot.sval x t S n τ
        = ((prot.consFinset x t τ).filter fun r =>
            view x (BitString.toList r) (prot.runFrom x S (BitString.toList r) n τ)
              ∈ prot.verdict).card := by
  classical
  intro n
  induction n with
  | zero => intro i τ _; rfl
  | succ n ih =>
      intro i τ hτ
      rw [sval_succ]
      have hfib := Finset.card_eq_sum_card_fiberwise
        (f := fun r : Fin t → Bool => prot.vmsg (view x (BitString.toList r) τ))
        (s := (prot.consFinset x t τ).filter fun r =>
          view x (BitString.toList r) (prot.runFrom x S (BitString.toList r) (n + 1) τ)
            ∈ prot.verdict)
        (t := prot.vset x t τ)
        (fun r hr => by
          rw [vset]
          exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp hr).1)
      rw [hfib]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [ih (i + 1) (τ ++ [v, S (τ ++ [v])]) (by simp [hτ]; omega),
        prot.consFinset_append x t τ i hτ v (S (τ ++ [v])), Finset.filter_filter,
        Finset.filter_filter]
      refine congrArg Finset.card (Finset.filter_congr fun r _ => ?_)
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h1⟩
        rw [runFrom_succ, h1]
        exact h2
      · rintro ⟨h2, h1⟩
        have h1' : prot.vmsg (view x (BitString.toList r) τ) = v := h1
        refine ⟨h1', ?_⟩
        rw [runFrom_succ, h1'] at h2
        exact h2

open Classical in
/-- The count at the root is the acceptance probability's numerator. -/
theorem sval_root (t : ℕ) (S : ProverStrategy) :
    prot.sval x t S (prot.rounds x.length) []
      = (Finset.univ.filter fun r : Fin t → Bool =>
          prot.Accepts S x (BitString.toList r)).card := by
  classical
  rw [sval_eq_card prot x t S _ 0 [] rfl, consFinset_nil]
  refine congrArg Finset.card (Finset.filter_congr fun r _ => ?_)
  rw [Accepts, transcript_eq_runFrom]

/-! ## The optimum is attained -/

open Classical in
/-- **A bounded strategy cannot beat the optimum.** -/
theorem sval_le_gval (t m : ℕ) {S : ProverStrategy} (hS : S.Bounded m) :
    ∀ (n : ℕ) (τ : Transcript), prot.sval x t S n τ ≤ prot.gval x t m n τ := by
  intro n
  induction n with
  | zero => intro τ; exact le_rfl
  | succ n ih =>
      intro τ
      rw [sval_succ, gval_succ]
      refine Finset.sum_le_sum fun v _ => ?_
      exact le_trans (ih _)
        (Finset.le_sup (f := fun a => prot.gval x t m n (τ ++ [v, a]))
          (mem_strsLe.mpr (hS (τ ++ [v]))))

open Classical in
/-- A reply attaining the maximum at a node whose depth says `R` rounds are planned. -/
noncomputable def optReply (t m R : ℕ) (σ : Transcript) : List Bool :=
  Classical.choose (Finset.exists_mem_eq_sup (strsLe m) (strsLe_nonempty m)
    (fun a => prot.gval x t m (R - σ.length / 2 - 1) (σ ++ [a])))

open Classical in
theorem optReply_mem (t m R : ℕ) (σ : Transcript) : prot.optReply x t m R σ ∈ strsLe m :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup (strsLe m) (strsLe_nonempty m)
    (fun a => prot.gval x t m (R - σ.length / 2 - 1) (σ ++ [a])))).1

open Classical in
theorem optReply_sup (t m R : ℕ) (σ : Transcript) :
    ((strsLe m).sup fun a => prot.gval x t m (R - σ.length / 2 - 1) (σ ++ [a]))
      = prot.gval x t m (R - σ.length / 2 - 1) (σ ++ [prot.optReply x t m R σ]) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup (strsLe m) (strsLe_nonempty m)
    (fun a => prot.gval x t m (R - σ.length / 2 - 1) (σ ++ [a])))).2

/-- The strategy that always plays a maximizing reply. -/
noncomputable def optStrategy (t m R : ℕ) : ProverStrategy := prot.optReply x t m R

theorem optStrategy_bounded (t m R : ℕ) : (prot.optStrategy x t m R).Bounded m := fun σ =>
  mem_strsLe.mp (prot.optReply_mem x t m R σ)

open Classical in
/-- **The optimum is attained.** -/
theorem sval_optStrategy (t m R : ℕ) :
    ∀ (n i : ℕ) (τ : Transcript), n + i = R → τ.length = 2 * i →
      prot.sval x t (prot.optStrategy x t m R) n τ = prot.gval x t m n τ := by
  intro n
  induction n with
  | zero => intro i τ _ _; rfl
  | succ n ih =>
      intro i τ hni hτ
      rw [sval_succ, gval_succ]
      refine Finset.sum_congr rfl fun v _ => ?_
      have hσ : (τ ++ [v]).length / 2 = i := by
        rw [List.length_append, hτ]
        simp
        omega
      have hidx : R - (τ ++ [v]).length / 2 - 1 = n := by
        rw [hσ]
        omega
      have hopt : prot.optStrategy x t m R (τ ++ [v]) = prot.optReply x t m R (τ ++ [v]) := rfl
      rw [ih (i + 1) (τ ++ [v, prot.optStrategy x t m R (τ ++ [v])]) (by omega)
        (by simp [hτ]; omega), hopt, ← hidx]
      have hsup := optReply_sup prot x t m R (τ ++ [v])
      simp only [List.append_assoc, List.cons_append, List.nil_append] at hsup
      exact hsup.symm

/-! ## The value decides the language -/

open Classical in
theorem acceptEvent_eq_filter (S : ProverStrategy) :
    prot.acceptEvent S x
      = Finset.univ.filter fun r : Fin (prot.coins x.length) → Bool =>
          prot.Accepts S x (BitString.toList r) := by
  classical
  rw [acceptEvent]

open Classical in
/-- The optimum is the largest accepting count a bounded strategy achieves. -/
theorem card_acceptEvent_le_gval (S : ProverStrategy) (hS : S.Bounded (prot.msgLen x.length)) :
    (prot.acceptEvent S x).card
      ≤ prot.gval x (prot.coins x.length) (prot.msgLen x.length) (prot.rounds x.length) [] := by
  classical
  rw [acceptEvent_eq_filter, ← sval_root]
  exact sval_le_gval prot x _ _ hS _ []

open Classical in
/-- And it is achieved: the maximizing strategy is bounded and attains it. -/
theorem gval_eq_card_acceptEvent :
    prot.gval x (prot.coins x.length) (prot.msgLen x.length) (prot.rounds x.length) []
      = (prot.acceptEvent
          (prot.optStrategy x (prot.coins x.length) (prot.msgLen x.length)
            (prot.rounds x.length)) x).card := by
  classical
  rw [acceptEvent_eq_filter, ← sval_root]
  exact (sval_optStrategy prot x _ _ _ _ 0 [] (by omega) rfl).symm

open Classical in
/-- **The tree value decides the language.** Completeness puts the optimum above two thirds of
the coin space and soundness below one third, so a comparison against a half separates them. -/
theorem mem_iff_gval {L : Language}
    (hcomp : ∀ y ∈ L, ∃ S : ProverStrategy, S.Bounded (prot.msgLen y.length) ∧
      2 / 3 ≤ eventProb (prot.acceptEvent S y))
    (hsound : ∀ y ∉ L, ∀ S : ProverStrategy, S.Bounded (prot.msgLen y.length) →
      eventProb (prot.acceptEvent S y) ≤ 1 / 3) :
    x ∈ L ↔ 2 ^ prot.coins x.length
      < 2 * prot.gval x (prot.coins x.length) (prot.msgLen x.length)
          (prot.rounds x.length) [] := by
  classical
  have hpos : 0 < 2 ^ prot.coins x.length := Nat.two_pow_pos _
  constructor
  · intro hx
    obtain ⟨S, hSb, hSp⟩ := hcomp x hx
    have hle := card_acceptEvent_le_gval prot x S hSb
    rw [eventProb, div_le_div_iff₀ (by norm_num) (by positivity)] at hSp
    have hSp' : 2 * 2 ^ prot.coins x.length ≤ (prot.acceptEvent S x).card * 3 := by
      exact_mod_cast hSp
    omega
  · intro hlt
    by_contra hx
    have hSb := prot.optStrategy_bounded x (prot.coins x.length) (prot.msgLen x.length)
      (prot.rounds x.length)
    have hSp := hsound x hx _ hSb
    rw [eventProb, div_le_div_iff₀ (by positivity) (by norm_num)] at hSp
    have hSp' : (prot.acceptEvent (prot.optStrategy x (prot.coins x.length)
        (prot.msgLen x.length) (prot.rounds x.length)) x).card * 3
        ≤ 1 * 2 ^ prot.coins x.length := by exact_mod_cast hSp
    rw [gval_eq_card_acceptEvent] at hlt
    omega

/-! ## Every message in the tree is short -/

open Classical in
/-- A verifier message the tree branches on respects the length bound. -/
theorem vset_length (t : ℕ) (τ : Transcript) {v : List Bool} (hv : v ∈ prot.vset x t τ) :
    v.length ≤ prot.msgLen x.length := by
  classical
  rw [vset, Finset.mem_image] at hv
  obtain ⟨r, _, rfl⟩ := hv
  exact prot.vmsg_len x (BitString.toList r) τ

/-- Hence every message on a path down the tree does. -/
theorem runFrom_length (S : ProverStrategy) (hS : S.Bounded (prot.msgLen x.length))
    (r : List Bool) :
    ∀ (n : ℕ) (τ : Transcript), (∀ u ∈ τ, u.length ≤ prot.msgLen x.length) →
      ∀ u ∈ prot.runFrom x S r n τ, u.length ≤ prot.msgLen x.length := by
  intro n
  induction n with
  | zero => intro τ hτ; exact hτ
  | succ n ih =>
      intro τ hτ
      refine ih _ fun u hu => ?_
      rcases List.mem_append.mp hu with hu | hu
      · exact hτ u hu
      · rcases List.mem_cons.mp hu with rfl | hu
        · exact prot.vmsg_len x r τ
        · rcases List.mem_cons.mp hu with rfl | hu
          · exact hS _
          · simp at hu

/-- And the transcript never holds more than two messages per round. -/
theorem runFrom_card (S : ProverStrategy) (r : List Bool) :
    ∀ (n : ℕ) (τ : Transcript), (prot.runFrom x S r n τ).length = τ.length + 2 * n := by
  intro n
  induction n with
  | zero => intro τ; simp
  | succ n ih =>
      intro τ
      rw [runFrom_succ, ih]
      simp
      omega

/-! ## The tree in the form a machine walks it -/

open Classical in
/-- A node no coin string reaches contributes nothing. -/
theorem gval_eq_zero (t m : ℕ) (n : ℕ) (σ : Transcript)
    (h : prot.consFinset x t σ = ∅) : prot.gval x t m n σ = 0 := by
  classical
  cases n with
  | zero =>
      rw [gval, h]
      simp
  | succ n =>
      rw [gval_succ, vset, h]
      simp

open Classical in
/-- **The sum may range over every short string.** A verifier message no coin string would send
splits off an empty set of coins, so its whole subtree is zero; and `Protocol.vmsg_len` keeps the
messages that *are* sent inside `Complexity.strsLe`. The recursion is then a walk over a fixed
finite index set, which is what a machine can enumerate. -/
theorem gval_succ_strsLe (t : ℕ) (n i : ℕ) (τ : Transcript) (hτ : τ.length = 2 * i) :
    prot.gval x t (prot.msgLen x.length) (n + 1) τ
      = ∑ v ∈ strsLe (prot.msgLen x.length),
          (strsLe (prot.msgLen x.length)).sup fun a =>
            prot.gval x t (prot.msgLen x.length) n (τ ++ [v, a]) := by
  classical
  rw [gval_succ]
  refine Finset.sum_subset (fun v hv => mem_strsLe.mpr (prot.vset_length x t τ hv)) ?_
  intro v _ hv
  have hempty : ∀ a : List Bool, prot.consFinset x t (τ ++ [v, a]) = ∅ := by
    intro a
    rw [prot.consFinset_append x t τ i hτ v a]
    refine Finset.filter_eq_empty_iff.mpr fun r hr hc => hv ?_
    rw [vset]
    exact Finset.mem_image.mpr ⟨r, hr, hc⟩
  refine Nat.le_zero.mp (Finset.sup_le fun a _ => ?_)
  exact Nat.le_of_eq (gval_eq_zero prot x t _ n (τ ++ [v, a]) (hempty a))

open Classical in
/-- **The leaf count, over bitstrings.** The coin space is exactly the strings of the coin
length, so the count a machine has to make at a leaf is a scan over `Complexity.strsOfLen`. -/
theorem gval_zero_strsOfLen (t m : ℕ) (τ : Transcript) :
    prot.gval x t m 0 τ
      = ((strsOfLen t).filter fun s =>
          prot.Consistent x s τ ∧ view x s τ ∈ prot.verdict).card := by
  classical
  rw [gval, consFinset, Finset.filter_filter]
  refine Finset.card_bij (fun r _ => BitString.toList r) ?_ ?_ ?_
  · intro r hr
    rw [Finset.mem_filter] at hr ⊢
    exact ⟨mem_strsOfLen.mpr (BitString.length_toList r), hr.2⟩
  · intro r _ r' _ h
    exact BitString.toList_inj.mp h
  · intro s hs
    rw [Finset.mem_filter] at hs
    have hlen : s.length = t := mem_strsOfLen.mp hs.1
    refine ⟨BitString.ofList s hlen, ?_, BitString.toList_ofList s hlen⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [BitString.toList_ofList]
    exact hs.2

/-! ## Replaying the verifier -/

/-- Walk the rounds, checking that every message the verifier is recorded as having sent is the
one it would have sent. The body of the transcript's encoding is carried along, so nothing is
re-encoded. -/
def replay (prot : Protocol) (x s : List Bool) :
    List (List Bool × List Bool) → List Bool → Bool
  | [], _ => true
  | p :: ps, body =>
      decide (p.1 = prot.vmsg (pair (pair x s) (false :: (body ++ [true])))) &&
        replay prot x s ps (body ++ encMsg p.1 ++ encMsg p.2)

@[simp] theorem replay_nil (s body : List Bool) : prot.replay x s [] body = true := rfl

theorem replay_cons (s : List Bool) (p : List Bool × List Bool)
    (ps : List (List Bool × List Bool)) (body : List Bool) :
    prot.replay x s (p :: ps) body
      = (decide (p.1 = prot.vmsg (pair (pair x s) (false :: (body ++ [true])))) &&
          prot.replay x s ps (body ++ encMsg p.1 ++ encMsg p.2)) := rfl

/-- **Consistency is a replay.** Walking the rounds and re-deriving the verifier's messages
decides whether a coin string could have produced the transcript. -/
theorem consistent_append_iff_replay (s : List Bool) :
    ∀ (ps : List (List Bool × List Bool)) (τ : Transcript) (i : ℕ), τ.length = 2 * i →
      (prot.Consistent x s (τ ++ flatRounds ps) ↔
        prot.Consistent x s τ ∧ prot.replay x s ps (encBody τ) = true) := by
  intro ps
  induction ps with
  | nil =>
      intro τ i _
      simp
  | cons p ps ih =>
      intro τ i hτ
      obtain ⟨v, a⟩ := p
      have hsplit : τ ++ flatRounds ((v, a) :: ps) = (τ ++ [v, a]) ++ flatRounds ps := by
        rw [flatRounds_cons]
        simp
      have hτ' : (τ ++ [v, a]).length = 2 * (i + 1) := by
        rw [List.length_append, hτ]
        simp
        omega
      rw [hsplit, ih (τ ++ [v, a]) (i + 1) hτ',
        prot.consistent_append x s τ i hτ v a, replay_cons, encBody_append_two, view_eq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, ?_⟩
        rw [Bool.and_eq_true, decide_eq_true_iff]
        refine ⟨h2, ?_⟩
        simpa [List.append_assoc] using h3
      · rintro ⟨h1, h2⟩
        rw [Bool.and_eq_true, decide_eq_true_iff] at h2
        refine ⟨⟨h1, h2.1⟩, ?_⟩
        simpa [List.append_assoc] using h2.2

/-- **Consistency at the root.** -/
theorem consistent_iff_replay (s : List Bool) (ps : List (List Bool × List Bool)) :
    prot.Consistent x s (flatRounds ps) ↔ prot.replay x s ps [] = true := by
  have h := prot.consistent_append_iff_replay x s ps [] 0 rfl
  rw [List.nil_append, encBody_nil] at h
  rw [h]
  simp [prot.consistent_nil x s]

/-! ## The tree indexed by rounds -/

open Classical in
/-- **The tree value, indexed by the rounds already played.** This is the recursion a stack
machine walks: one frame per round, a sum over the verifier's possible messages and a maximum
over the prover's replies, bottoming out in a count over the coin strings. -/
noncomputable def gvalR (t n : ℕ) (ps : List (List Bool × List Bool)) : ℕ :=
  prot.gval x t (prot.msgLen x.length) n (flatRounds ps)

open Classical in
theorem gvalR_zero (t : ℕ) (ps : List (List Bool × List Bool)) :
    prot.gvalR x t 0 ps
      = ((strsOfLen t).filter fun s =>
          prot.replay x s ps [] = true ∧
            pair (pair x s) (false :: (encBodyR ps ++ [true])) ∈ prot.verdict).card := by
  classical
  rw [gvalR, gval_zero_strsOfLen]
  refine congrArg Finset.card (Finset.filter_congr fun s _ => ?_)
  rw [prot.consistent_iff_replay x s ps, view_eq, encBodyR]

open Classical in
theorem gvalR_succ (t n : ℕ) (ps : List (List Bool × List Bool)) :
    prot.gvalR x t (n + 1) ps
      = ∑ v ∈ strsLe (prot.msgLen x.length),
          (strsLe (prot.msgLen x.length)).sup fun a =>
            prot.gvalR x t n (ps ++ [(v, a)]) := by
  classical
  rw [gvalR, gval_succ_strsLe prot x t n ps.length (flatRounds ps) (by simp)]
  refine Finset.sum_congr rfl fun v _ => ?_
  refine Finset.sup_congr rfl fun a _ => ?_
  rw [gvalR, flatRounds_append]

theorem gvalR_root (t n : ℕ) : prot.gvalR x t n [] = prot.gval x t (prot.msgLen x.length) n [] :=
  rfl

/-! ## The recursion against the counters -/

open Classical in
/-- **The branching, as two counter loops.** `Complexity.nextStr` visits every message the
verifier or the prover may send exactly once, so the sum and the maximum are ordinary loops. -/
theorem gvalR_succ_enum (t n : ℕ) (ps : List (List Bool × List Bool)) :
    prot.gvalR x t (n + 1) ps
      = ∑ i ∈ Finset.range (2 ^ (prot.msgLen x.length + 1) - 1),
          (Finset.range (2 ^ (prot.msgLen x.length + 1) - 1)).sup fun j =>
            prot.gvalR x t n (ps ++ [(nextStr^[i] [], nextStr^[j] [])]) := by
  classical
  rw [gvalR_succ, strsLe_eq_image (prot.msgLen x.length),
    Finset.sum_image fun i hi j hj h =>
      nextStr_injOn (prot.msgLen x.length) (Finset.mem_coe.mpr hi) (Finset.mem_coe.mpr hj) h]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sup_image]
  rfl

open Classical in
/-- **The leaf, as a counter loop.** -/
theorem gvalR_zero_enum (t : ℕ) (ps : List (List Bool × List Bool)) :
    prot.gvalR x t 0 ps
      = ((Finset.range (2 ^ t)).filter fun i =>
          prot.replay x (bumpBits^[i] (List.replicate t false)) ps [] = true ∧
            pair (pair x (bumpBits^[i] (List.replicate t false)))
              (false :: (encBodyR ps ++ [true])) ∈ prot.verdict).card := by
  classical
  rw [gvalR_zero, strsOfLen_eq_image, Finset.filter_image,
    Finset.card_image_of_injOn (fun i hi j hj h =>
      bumpBits_injOn t (Finset.mem_coe.mpr (Finset.mem_of_mem_filter i hi))
        (Finset.mem_coe.mpr (Finset.mem_of_mem_filter j hj)) h)]

/-! ## The value never exceeds the coin space -/

open Classical in
/-- **The tree value never exceeds the number of coins still in play.** The verifier's next
message partitions those coins, so summing over the messages cannot double-count. -/
theorem gval_le_card (t : ℕ) :
    ∀ (n i : ℕ) (τ : Transcript), τ.length = 2 * i →
      prot.gval x t (prot.msgLen x.length) n τ ≤ (prot.consFinset x t τ).card := by
  classical
  intro n
  induction n with
  | zero =>
      intro i τ _
      rw [gval]
      exact Finset.card_filter_le _ _
  | succ n ih =>
      intro i τ hτ
      rw [gval_succ]
      have hfib := Finset.card_eq_sum_card_fiberwise
        (f := fun r : Fin t → Bool => prot.vmsg (view x (BitString.toList r) τ))
        (s := prot.consFinset x t τ) (t := prot.vset x t τ)
        (fun r hr => by
          rw [vset]
          exact Finset.mem_image_of_mem _ hr)
      rw [hfib]
      refine Finset.sum_le_sum fun v _ => ?_
      refine Finset.sup_le fun a _ => ?_
      have hle := ih (i + 1) (τ ++ [v, a]) (by simp [hτ]; omega)
      rwa [prot.consFinset_append x t τ i hτ v a] at hle

open Classical in
theorem gval_le_two_pow (t n i : ℕ) (τ : Transcript) (hτ : τ.length = 2 * i) :
    prot.gval x t (prot.msgLen x.length) n τ ≤ 2 ^ t := by
  classical
  refine le_trans (gval_le_card prot x t n i τ hτ) ?_
  rw [consFinset]
  refine le_trans (Finset.card_filter_le _ _) ?_
  rw [Finset.card_univ, card_finArrowBool]

theorem gvalR_le_two_pow (t n : ℕ) (ps : List (List Bool × List Bool)) :
    prot.gvalR x t n ps ≤ 2 ^ t :=
  gval_le_two_pow prot x t n ps.length (flatRounds ps) (by simp)

end Protocol

/-! ## The containment, reduced to evaluating the tree -/

open Classical in
/-- **`IP ⊆ PSPACE`, reduced to one computation.** Membership in a language of `IP` is a
comparison of the game-tree value against half the coin space, so a polynomial-space evaluation
of that value settles the containment. -/
theorem IP_subset_PSPACE_of_gval
    (h : ∀ (prot : Protocol) (rp cp mp : Polynomial ℕ), (∀ n, prot.rounds n = rp.eval n) →
      (∀ n, prot.coins n = cp.eval n) → (∀ n, prot.msgLen n = mp.eval n) →
      {x : List Bool | 2 ^ prot.coins x.length
        < 2 * prot.gval x (prot.coins x.length) (prot.msgLen x.length)
            (prot.rounds x.length) []} ∈ PSPACE) :
    IP ⊆ PSPACE := by
  intro L hL
  obtain ⟨prot, rp, cp, mp, hr, hc, hm, hcomp, hsound⟩ := hL
  have hset : L = {x : List Bool | 2 ^ prot.coins x.length
      < 2 * prot.gval x (prot.coins x.length) (prot.msgLen x.length)
          (prot.rounds x.length) []} :=
    Set.ext fun x => Protocol.mem_iff_gval prot x hcomp hsound
  rw [hset]
  exact h prot rp cp mp hr hc hm

end Complexity

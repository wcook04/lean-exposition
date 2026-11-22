module

public import QuarticQuery.Paper.ConstructionTests
public import QuarticQuery.Upper.Compile

/-!
# Exact local tests controlled by an arbitrary superposition

Compiled as part of the `QuarticQuery` library target.

`Upper.test_samples` prepares a particular uniform distribution. The preprint's
Lemma 2.2 also permits an index register supplied in an arbitrary superposition.
The direct sum below proves that state-level statement: arbitrary complex
coefficients of the index register are retained, each block runs the appropriate
exact test, and every wrong output amplitude is zero. Workspace is retained.

The read count is `max 3 (ℓ + 1)`. The existing physical compiler charges at most
two ordinary bit queries per read, uniformly for arbitrary input states and
continuations. This file makes no extra claim about a clean XOR oracle whose
ancillas have already been reset.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper
open scoped BigOperators

section Coherent

variable {Γ : Type} [Fintype Γ] {Z : Γ → Type} [∀ e, Fintype (Z e)]

/-- Ledger: lem-2.2.ii. The initial indexed state, with arbitrary complex
coefficients and the fixed initial workspace in each index block. -/
@[expose] noncomputable def constructionIndexStart (o : ∀ e, Z e) (a : Γ → ℂ) :
    Reg (Σ e, Z e) :=
  WithLp.toLp 2 fun p => a p.1 * (rket (o p.1)).ofLp p.2

/-- Ledger: lem-2.2.ii. The indexed state's `e`-block is exactly its complex
coefficient times the fixed starting ket. -/
theorem construction_slice_indexStart (o : ∀ e, Z e) (a : Γ → ℂ) (e : Γ) :
    slice e (constructionIndexStart o a) = a e • rket (o e) := by
  ext z
  rfl

end Coherent

/-- Ledger: lem-2.2.ii. An exact measured Boolean law has zero amplitude at every
basis vector labelled with the incorrect answer. -/
theorem construction_support_of_exact_law {Z : Type} [Fintype Z]
    (ψ : Reg Z) (out : Z → Bool) (b : Bool)
    (h : ∀ c, pt b c = lawOf ψ out c) (z : Z) (hz : out z ≠ b) :
    ψ.ofLp z = 0 := by
  classical
  have hzero : lawOf ψ out (out z) = 0 := by
    rw [← h (out z)]
    exact pt_of_ne (Ne.symm hz)
  have hle : ‖ψ.ofLp z‖ ^ 2 ≤ lawOf ψ out (out z) := by
    have hsingle := Finset.single_le_sum
      (f := fun w : Z => if out w = out z then ‖ψ.ofLp w‖ ^ 2 else 0)
      (fun w _ => by split_ifs <;> positivity) (Finset.mem_univ z)
    simpa only [lawOf, if_pos rfl, ite_true] using hsingle
  rw [hzero] at hle
  have hnorm : ‖ψ.ofLp z‖ = 0 := by
    nlinarith [norm_nonneg (ψ.ofLp z)]
  exact norm_eq_zero.mp hnorm

/-- Ledger: lem-2.2.ii. A finite family of exact samplers with one read budget
has a single coherent controlled implementation for arbitrary index amplitudes.
This strengthens the earlier uniform-index-only statement. -/
theorem construction_controlled_exact_samples {ι Γ : Type} [Fintype Γ]
    (n : ℕ) (g : BitInput ι → Γ → Bool)
    (h : ∀ e : Γ, Samples n fun x b => pt (g x e) b) :
    ∃ (Z : Γ → Type) (instZ : ∀ e, Fintype (Z e)),
      let _ := instZ
      ∃ (o : ∀ e, Z e) (out : ∀ e, Z e → Bool)
        (F : ∀ e, BitInput ι → Reg (Z e) ≃ₗᵢ[ℂ] Reg (Z e)),
        (∀ e, IsCirc n (F e)) ∧
        IsCirc n (fun x => sigmaOp fun e => F e x) ∧
        (∀ (x : BitInput ι) (a : Γ → ℂ) (e : Γ),
          slice e (sigmaOp (fun e => F e x) (constructionIndexStart o a)) =
            a e • F e x (rket (o e))) ∧
        (∀ (x : BitInput ι) (e : Γ) (z : Z e),
          out e z ≠ g x e → (F e x (rket (o e))).ofLp z = 0) := by
  classical
  choose Z instZ o out F hF hL using h
  let _ := instZ
  refine ⟨Z, instZ, o, out, F, hF, IsCirc.sigma hF, ?_, ?_⟩
  · intro x a e
    rw [slice_sigmaOp, construction_slice_indexStart, map_smul]
  · intro x e z hz
    exact construction_support_of_exact_law (F e x (rket (o e))) (out e)
      (g x e) (hL e x) z hz

/-- Ledger: lem-2.2.ii. Verbatim coherent-evaluation scope: all complex
superpositions of test indices are permitted, with one common index type and
read budget for every `(i,s)`. The work registers are retained. -/
theorem construction_lemma_2_2_ii {κ : Type} (C : Circuit κ) (ℓ r : ℕ)
    (i : Column ℓ) (s : Address r) :
    ∃ (Z : TestIndex ℓ r C.size → Type) (instZ : ∀ e, Fintype (Z e)),
      let _ := instZ
      ∃ (o : ∀ e, Z e) (out : ∀ e, Z e → Bool)
        (F : ∀ e, BitInput (BitLoc ℓ r C.size κ) → Reg (Z e) ≃ₗᵢ[ℂ] Reg (Z e)),
        (∀ e, IsCirc (max 3 (ℓ + 1)) (F e)) ∧
        IsCirc (max 3 (ℓ + 1)) (fun x => sigmaOp fun e => F e x) ∧
        (∀ (x : BitInput (BitLoc ℓ r C.size κ))
            (a : TestIndex ℓ r C.size → ℂ) (e : TestIndex ℓ r C.size),
          slice e (sigmaOp (fun e => F e x) (constructionIndexStart o a)) =
            a e • F e x (rket (o e))) ∧
        (∀ (x : BitInput (BitLoc ℓ r C.size κ))
            (e : TestIndex ℓ r C.size) (z : Z e),
          out e z ≠ localTest C ℓ r x i s e →
            (F e x (rket (o e))).ofLp z = 0) := by
  haveI : Nonempty (BitLoc ℓ r C.size κ) :=
    ⟨.inl (⟨0, Nat.two_pow_pos ℓ⟩, ⟨0, Nat.two_pow_pos ℓ⟩)⟩
  apply construction_controlled_exact_samples (max 3 (ℓ + 1))
    (fun x e => localTest C ℓ r x i s e)
  intro e
  exact ((Samples.tree (localTestTree C ℓ r i s e)).mono
    (localTestTree_depth_le C ℓ r i s e)).congr fun x b => by
      rw [localTestTree_eval]

/-- Ledger: lem-2.2.ii. Exact physical query accounting for the controlled
implementation: every read costs at most two ordinary bit-oracle queries.
The conclusion preserves all continuation probabilities for arbitrary states. -/
theorem construction_controlled_compile {ι Γ : Type} [Fintype ι] [Inhabited ι]
    [Fintype Γ] {Z : Γ → Type} [∀ e, Fintype (Z e)] {n w : ℕ}
    (F : ∀ e, BitInput ι → Reg (Z e) ≃ₗᵢ[ℂ] Reg (Z e))
    (hF : ∀ e, IsCirc n (F e)) (emb : (Σ e, Z e) ↪ Fin (w + 1)) :
    ∃ P : AdaptiveProgram ι w → AdaptiveProgram ι w, ∀ next,
      (P next).queryCap ≤ 2 * n + next.queryCap ∧
      ∀ x ψ b, (P next).outputMass x (clEmb emb ψ) b =
        next.outputMass x (clEmb emb (sigmaOp (fun e => F e x) ψ)) b :=
  compile_circ emb (IsCirc.sigma hF)

/-! ## The whole lemma, in one statement -/

/-- Ledger: lem-2.2. The exact count, conjunction, depth and arbitrary-index
coherent statements are assembled. The logarithmic size bound is supplied by
`construction_K_bound` with the circuit-size hypothesis of Lemma 2.1(iii). -/
theorem construction_lemma_2_2 {κ : Type} {f : PartialBool κ}
    (C : Circuit κ) (ℓ r : ℕ) (hC : CircuitRealises C f) :
    Fintype.card (TestIndex ℓ r C.size) =
      2 ^ ℓ + (2 ^ ℓ - 1) + r * (C.size + 2) ∧
    (∀ (x : BitInput (BitLoc ℓ r C.size κ)) (i : Column ℓ) (s : Address r),
      PaperWinsAt f C ℓ r x i s ↔
        ∀ e : TestIndex ℓ r C.size, localTest C ℓ r x i s e = true) ∧
    (∀ (i : Column ℓ) (s : Address r) (e : TestIndex ℓ r C.size),
      (∀ x, (localTestTree C ℓ r i s e).eval x = localTest C ℓ r x i s e) ∧
      (localTestTree C ℓ r i s e).depth ≤ max 3 (ℓ + 1)) ∧
    (∀ (i : Column ℓ) (s : Address r),
      ∃ (Z : TestIndex ℓ r C.size → Type) (instZ : ∀ e, Fintype (Z e)),
        let _ := instZ
        ∃ (o : ∀ e, Z e) (out : ∀ e, Z e → Bool)
          (F : ∀ e, BitInput (BitLoc ℓ r C.size κ) → Reg (Z e) ≃ₗᵢ[ℂ] Reg (Z e)),
          (∀ e, IsCirc (max 3 (ℓ + 1)) (F e)) ∧
          IsCirc (max 3 (ℓ + 1)) (fun x => sigmaOp fun e => F e x) ∧
          (∀ (x : BitInput (BitLoc ℓ r C.size κ))
              (a : TestIndex ℓ r C.size → ℂ) (e : TestIndex ℓ r C.size),
            slice e (sigmaOp (fun e => F e x) (constructionIndexStart o a)) =
              a e • F e x (rket (o e))) ∧
          (∀ (x : BitInput (BitLoc ℓ r C.size κ))
              (e : TestIndex ℓ r C.size) (z : Z e),
            out e z ≠ localTest C ℓ r x i s e →
              (F e x (rket (o e))).ofLp z = 0)) := by
  have hclassical := construction_lemma_2_2_i C ℓ r hC
  exact ⟨card_testIndex ℓ r C.size, hclassical.1, hclassical.2,
    fun i s => construction_lemma_2_2_ii C ℓ r i s⟩

end QuarticQuery.Paper

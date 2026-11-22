module

public import QuarticQuery.Bridge.DecisionTree
public import QuarticQuery.Bridge.Deferred
public import Complexity.Computability.QueryComplexity.Quantum.Adversary
import all Complexity.Computability.QueryComplexity.SpectralSensitivity
import Complexity.Foundations.BooleanAnalysis.MaximalSupport

/-!
# Appendix A: degree, block sensitivity, sensitivity graph and Midrijanis

Compiled as part of the `QuarticQuery` library target.

Definitions use the exact pinned complexitylib/cslib meanings. The bridge for
Lemma A.3.bs uses the polynomial proof of `bs(f) ≤ 16 T²`; it does not formalise
the appendix's star-matrix proof. The sensitivity-graph bridge uses the library's
two-vector, absolute-overlap progress measure. The maximal-monomial statements
and the proof of Lemma A.5 follow Midrijanis's argument, expressed in the
equivalent Fourier basis.

The additional pointwise restriction and round-count lemmas make explicit why
the blocks obtained in separate rounds belong to the same original input.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Cslib Finset
open Cslib.BitString Cslib.QueryComplexity

variable {n : ℕ}

/-! ## Degree and block sensitivity -/

/-- Ledger: def-deg. Degree is the least degree of a real multilinear
representation, with zero assigned to constant functions. -/
theorem appendixA_degree_le_iff (f : TotalBool (Fin n)) (d : ℕ) :
    degree f ≤ d ↔ (fun x => bitVal ℝ (f x)) ∈ lowDegree ℝ (Fin n) d :=
  degree_le_iff_mem_lowDegree

/-- Ledger: def-deg. The finite-cube degree equals the Fourier degree. This is
the exact change-of-basis bridge used by the maximal-support argument. -/
theorem appendixA_degree_le_iff_fourier (f : TotalBool (Fin n)) (d : ℕ) :
    degree f ≤ d ↔
      ∀ S : Finset (Fin n), d < #S →
        fourierCoeff (fun x => bitVal ℝ (f x)) S = 0 :=
  (appendixA_degree_le_iff f d).trans mem_lowDegree_iff_fourierCoeff_eq_zero

/-- Ledger: def-deg. Both Boolean constants, including the zero function, have
degree zero. -/
theorem appendixA_degree_const (b : Bool) :
    degree (fun _ : BitInput (Fin n) => b) = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact degree_le_iff_mem_lowDegree.2 (const_mem_lowDegree 0 (bitVal ℝ b))

/-- Ledger: def-deg. Changing output bits to signs preserves the degree. The
input change from bit monomials to sign characters is in
`appendixA_degree_le_iff_fourier`. -/
theorem appendixA_degree_eq_sign (f : TotalBool (Fin n)) :
    degree f = Cslib.BitString.totalDegree (fun x => signVal (f x)) :=
  degree_eq_totalDegree_signVal f

/-- Ledger: def-bs. The library's inequality definition already forces a
sensitive block to be nonempty. -/
theorem appendixA_isSensitiveBlock_iff (f : TotalBool (Fin n))
    (x : BitInput (Fin n)) (B : Finset (Fin n)) :
    IsSensitiveBlock f x B ↔ B.Nonempty ∧ f (flipBlock B x) ≠ f x := by
  exact ⟨fun h => ⟨h.nonempty, h⟩, fun h => h.2⟩

/-- Ledger: def-bs. The maximum is over inputs and over finite families of
pairwise disjoint sensitive blocks, with cardinality as the quantity maximised. -/
theorem appendixA_blockSensitivity_eq (f : TotalBool (Fin n)) :
    blockSensitivity f =
      Finset.univ.sup (fun x : BitInput (Fin n) =>
        (sensitiveFamilies f x).sup Finset.card) := rfl

/-- Ledger: def-bs. A constant function has no sensitive block. -/
theorem appendixA_blockSensitivity_const (b : Bool) :
    blockSensitivity (fun _ : BitInput (Fin n) => b) = 0 := by
  have h := blockSensitivity_le_two_mul_degree_sq
    (fun _ : BitInput (Fin n) => b)
  rw [appendixA_degree_const] at h
  simpa using h

/-! ## The unnormalised sensitivity adjacency matrix -/

/-- Ledger: def-Sf. The real 0/1 adjacency matrix of the sensitivity graph. -/
noncomputable def appendixA_sensitivityMatrix (f : TotalBool (Fin n)) :
    Matrix (BitInput (Fin n)) (BitInput (Fin n)) ℝ :=
  (sensitivityGraph f).adjMatrix ℝ

/-- Ledger: def-Sf. An edge changes exactly one input bit and changes the
function value. This is the paper's adjacency criterion. -/
theorem appendixA_sensitivityGraph_adj_iff (f : TotalBool (Fin n))
    (x y : BitInput (Fin n)) :
    (sensitivityGraph f).Adj x y ↔
      f x ≠ f y ∧ ∃ i : Fin n, Function.update x i (!x i) = y := by
  rw [sensitivityGraph_adj]
  constructor
  · rintro ⟨i, hs, hxy⟩
    refine ⟨?_, ⟨i, hxy⟩⟩
    change f (Function.update x i (!x i)) ≠ f x at hs
    rw [hxy] at hs
    exact hs.symm
  · rintro ⟨hxy, i, hi⟩
    refine ⟨i, ?_, hi⟩
    change f (Function.update x i (!x i)) ≠ f x
    rw [hi]
    exact hxy.symm

/-- Ledger: def-Sf. Spectral sensitivity is the Euclidean operator norm of
this unnormalised adjacency matrix. -/
theorem appendixA_spectralSensitivity_eq (f : TotalBool (Fin n)) :
    spectralSensitivity f =
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_sensitivityMatrix f)‖ := (rfl)

/-- Ledger: def-Sf. A constant function has no sensitivity edges. -/
theorem appendixA_spectralSensitivity_const (b : Bool) :
    spectralSensitivity (fun _ : BitInput (Fin n) => b) = 0 := by
  have hs : sensitivity (fun _ : BitInput (Fin n) => b) = 0 := by
    simp [sensitivity, sensitivityAt, sensitiveCoords, IsSensitiveCoord]
  apply le_antisymm _ (spectralSensitivity_nonneg _)
  simpa only [hs, Nat.cast_zero] using
    spectralSensitivity_le_sensitivity (fun _ : BitInput (Fin n) => b)

/-! ## Adaptive algorithms and Lemma A.3 -/

/-- Ledger: lem-A.3. Transport an adaptive total-function algorithm to the
fixed-sequence model, preserving its query budget. The constant alternative is
kept explicitly, including for the empty coordinate type. -/
theorem appendixA_QLe_total_cases {f : TotalBool (Fin n)} {t : ℕ}
    (h : QLe (totalise f) t) :
    (∃ b : Bool, ∀ x, f x = b) ∨
      ∃ (W : Type) (_ : Fintype W)
        (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
        (ψ : Cslib.Quantum.State n W) (S : Finset (Fin n × Bool × W)),
        ‖ψ‖ = 1 ∧
          ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ x t) S -
            bitVal ℝ (f x)| ≤ 1 / 3 := by
  rcases h with ⟨b, hb⟩ | ⟨w, ψ, A, hψ, hA, hc⟩
  · exact Or.inl ⟨b, fun x => hb x (f x) rfl⟩
  · obtain ⟨W, _, entry, U, S, hspec⟩ := exists_fixedSequence A hA
    refine Or.inr ⟨W, inferInstance, U, entry ψ, S,
      by rw [entry.norm_map, hψ], fun x => ?_⟩
    rw [hspec]
    have hsum := A.outputMass_true_add_false x ψ
    have hx := hc x (f x) rfl
    rw [hψ] at hsum
    have ht := A.outputMass_nonneg x ψ true
    have hf := A.outputMass_nonneg x ψ false
    cases hfx : f x
    · rw [hfx] at hx
      simp only [bitVal_false, sub_zero]
      rw [abs_of_nonneg ht]
      linarith
    · rw [hfx] at hx
      simp only [bitVal_true]
      rw [abs_le]
      constructor <;> linarith

/-- Ledger: lem-A.3.bs. Uniform numerical block-sensitivity bound, also for
constants. Route: the polynomial method, not the appendix's star matrix. -/
theorem appendixA_blockSensitivity_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (h : QLe (totalise f) t) : blockSensitivity f ≤ 16 * t ^ 2 := by
  rcases appendixA_QLe_total_cases h with ⟨b, hb⟩ | ⟨W, _, U, ψ, S, hψ, hc⟩
  · have hfun : f = fun _ => b := funext hb
    rw [hfun, appendixA_blockSensitivity_const]
    exact Nat.zero_le _
  · exact Cslib.Quantum.blockSensitivity_le_sixteen_mul_sq U hψ t S hc

/-- Ledger: lem-A.3.lambda. Uniform numerical spectral-sensitivity bound,
also for constants. Route: the library's two-vector progress proof for the
sensitivity graph. -/
theorem appendixA_spectralSensitivity_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (h : QLe (totalise f) t) : spectralSensitivity f ≤ 36 * t := by
  rcases appendixA_QLe_total_cases h with ⟨b, hb⟩ | ⟨W, _, U, ψ, S, hψ, hc⟩
  · have hfun : f = fun _ => b := funext hb
    rw [hfun, appendixA_spectralSensitivity_const]
    positivity
  · exact Cslib.Quantum.spectralSensitivity_le_thirty_six_mul U hψ t S hc

/-- Ledger: lem-A.3. The two numerical inequalities imply the paper's two
dimension-uniform big-O bounds. The block-sensitivity proof is alternative. -/
theorem appendixA_lemmaA3 (f : TotalBool (Fin n)) :
    blockSensitivity f ≤ 16 * Q (totalise f) ^ 2 ∧
      spectralSensitivity f ≤ 36 * Q (totalise f) :=
  ⟨appendixA_blockSensitivity_le_of_QLe (QLe_Q _),
    appendixA_spectralSensitivity_le_of_QLe (QLe_Q _)⟩

/-! ## Maximal supports and disjoint sensitive blocks -/

/-- Ledger: claim-round-block. Every nonempty inclusion-maximal nonzero
Fourier support contains a nonempty sensitive block at every input. A support
of maximum degree satisfies these hypotheses. -/
theorem appendixA_sensitiveBlock_of_maximal_support {f : TotalBool (Fin n)}
    {S : Finset (Fin n)} (hS : S.Nonempty)
    (hcoeff : fourierCoeff (fun x => bitVal ℝ (f x)) S ≠ 0)
    (hmax : ∀ T, S ⊂ T → fourierCoeff (fun x => bitVal ℝ (f x)) T = 0)
    (x : BitInput (Fin n)) :
    ∃ B : Finset (Fin n), B ⊆ S ∧ B.Nonempty ∧ IsSensitiveBlock f x B := by
  obtain ⟨y, hy, hfy⟩ := exists_ne_on_face_of_fourierCoeff_maximal hS hcoeff hmax x
  let B : Finset (Fin n) := {i | y i ≠ x i}
  have hBS : B ⊆ S := by
    intro i hi
    by_contra hiS
    exact (mem_filter.1 hi).2 (hy i hiS)
  have hB : IsSensitiveBlock f x B := by
    change f (flipBlock ({i | y i ≠ x i} : Finset (Fin n)) x) ≠ f x
    rw [flipBlock_filter_ne]
    exact fun h => hfy (congrArg (bitVal ℝ) h)
  exact ⟨B, hBS, hB.nonempty, hB⟩

/-- Ledger: claim-round-block. A maximum-degree support supplies a block at
every input. This is the maximal-monomial ingredient of Midrijanis's proof. -/
theorem appendixA_exists_maximal_round_support (f : TotalBool (Fin n))
    (hf : degree f ≠ 0) :
    ∃ S : Finset (Fin n), #S = degree f ∧
      ∀ x, ∃ B : Finset (Fin n), B ⊆ S ∧ B.Nonempty ∧ IsSensitiveBlock f x B := by
  obtain ⟨S, hScard, hS⟩ :=
    exists_card_eq_degree_forall_exists_isSensitiveBlock_subset f hf
  refine ⟨S, hScard, fun x => ?_⟩
  obtain ⟨B, hBS, hB⟩ := hS x
  exact ⟨B, hBS, hB.nonempty, hB⟩

/-- Ledger: claim-round-block. A sensitive block in the still-free
coordinates of the restriction is sensitive at the same original full input. -/
theorem appendixA_sensitiveBlock_of_restriction {f : TotalBool (Fin n)}
    (x : BitInput (Fin n)) (F B : Finset (Fin n)) (hBF : Disjoint B F)
    (hB : IsSensitiveBlock (fun y => f (F.piecewise x y)) x B) :
    IsSensitiveBlock f x B := by
  have heq : F.piecewise x (flipBlock B x) = flipBlock B x := by
    funext i
    by_cases hiF : i ∈ F
    · have hiB : i ∉ B := fun hi => Finset.disjoint_left.1 hBF hi hiF
      simp [hiF, flipBlock_apply_of_notMem hiB]
    · simp [hiF]
  have heq0 : F.piecewise x x = x := by
    funext i
    by_cases hi : i ∈ F <;> simp [hi]
  change f (F.piecewise x (flipBlock B x)) ≠ f (F.piecewise x x) at hB
  rwa [heq, heq0] at hB

/-- Ledger: claim-round-block. Subsets of the disjoint sets queried in
different rounds are disjoint. -/
theorem appendixA_roundBlocks_pairwise_disjoint {r : ℕ}
    (S B : Fin r → Finset (Fin n))
    (hS : Pairwise fun i j => Disjoint (S i) (S j)) (hB : ∀ i, B i ⊆ S i) :
    Pairwise fun i j => Disjoint (B i) (B j) := by
  intro i j hij
  exact Disjoint.mono (hB i) (hB j) (hS hij)

/-- Ledger: claim-round-block. One nonempty sensitive block from each
disjoint round bounds the number of rounds at the original input. -/
theorem appendixA_round_count_le {r : ℕ} {f : TotalBool (Fin n)}
    (x : BitInput (Fin n)) (B : Fin r → Finset (Fin n))
    (hB : Pairwise fun i j => Disjoint (B i) (B j))
    (hs : ∀ i, IsSensitiveBlock f x (B i)) : r ≤ blockSensitivityAt f x := by
  have hinj : Function.Injective B := by
    intro i j hij
    by_contra hne
    obtain ⟨k, hk⟩ := (hs i).nonempty
    exact Finset.disjoint_left.1 (hB hne) hk (hij ▸ hk)
  have hF : IsSensitiveFamily f x (Finset.univ.image B) := by
    constructor
    · intro C hC
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hC
      exact hs i
    · intro C hC D hD hCD
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.1 hC
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 hD
      exact hB (fun hij => hCD (congrArg B hij))
  have hcard : (Finset.univ.image B).card = r := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [← hcard]
  exact card_le_blockSensitivityAt hF

/-- Ledger: claim-round-block. The library's induction form of the same
round accounting: querying a support containing a sensitive block decreases
remaining block sensitivity by at least one. -/
theorem appendixA_round_decreases_blockSensitivity {f : TotalBool (Fin n)}
    {S B : Finset (Fin n)} (a z : BitInput (Fin n)) (hBS : B ⊆ S)
    (hB : IsSensitiveBlock f (S.piecewise a z) B) :
    blockSensitivityAt (fun y => f (S.piecewise a y)) z + 1 ≤
      blockSensitivityAt f (S.piecewise a z) :=
  blockSensitivityAt_comp_piecewise_add_one_le a z hBS hB

/-- Ledger: lem-A.5. Midrijanis's exact decision-tree bound, stated for the
project's totalisation and deterministic-query minimum. -/
theorem appendixA_lemmaA5 (f : TotalBool (Fin n)) :
    D (totalise f) ≤ blockSensitivity f * degree f := by
  rw [D_totalise_eq_complexity]
  simpa only [Nat.mul_comm] using
    Cslib.DecisionTree.complexity_le_degree_mul_blockSensitivity f

end QuarticQuery.Paper

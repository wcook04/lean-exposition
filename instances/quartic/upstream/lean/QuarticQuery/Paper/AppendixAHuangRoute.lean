module

public import QuarticQuery.Paper.AppendixAHuangMatrix
public import QuarticQuery.Paper.AppendixARestriction
public import QuarticQuery.Paper.AppendixAAdversary
public import QuarticQuery.Paper.AppendixASensitivity

/-!
# Appendix A: the face and recursive-matrix route to Lemma A.4

Compiled as part of the `QuarticQuery` library target.

This file connects the genuine maximum-degree face, the literal recursive
signed cube, and the original function's sensitivity matrix. The extension by
zero is explicit. It does not invoke complexitylib's spectral degree endpoint.
The equal-multiplicity proof inside `AppendixAHuangMatrix` uses the parity
involution instead of deducing multiplicities from the zero trace.
-/

public section

namespace QuarticQuery.Paper

open Finset Function Cslib
open Cslib.BitString Cslib.QueryComplexity
open scoped Matrix

variable {n : ℕ}

/-- Ledger: lem-A.4. An injective coordinate embedding preserves the norm of
an extended vector and identifies its quadratic form with the corresponding
principal submatrix. This is the extension-by-zero norm estimate. -/
theorem appendixA_quadratic_embedding {β : Type} [Fintype β]
    (Γ : AppendixAMatrix n) (φ : β → BitInput (Fin n)) (hφ : Injective φ)
    (u : β → ℝ) :
    ∑ a, ∑ b, u a * u b * Γ (φ a) (φ b) ≤
      appendixAMatrixNorm Γ * ∑ a, u a ^ 2 := by
  classical
  let w : BitInput (Fin n) → ℝ := extend φ u (fun _ => 0)
  have hwimage (a : β) : w (φ a) = u a := hφ.extend_apply u (fun _ => 0) a
  have hwout (x : BitInput (Fin n)) (hx : x ∉ Set.range φ) : w x = 0 :=
    extend_apply' u (fun _ => 0) x hx
  have hsq : (∑ a, u a ^ 2) = ∑ x, w x ^ 2 := by
    exact Fintype.sum_of_injective φ hφ (fun a => u a ^ 2) (fun x => w x ^ 2)
      (fun x hx => by rw [hwout x hx]; simp)
      (fun a => by rw [hwimage])
  have hinner (a : β) : (∑ b, u a * u b * Γ (φ a) (φ b)) =
      ∑ y, u a * w y * Γ (φ a) y := by
    exact Fintype.sum_of_injective φ hφ _ _
      (fun y hy => by rw [hwout y hy]; simp)
      (fun b => by rw [hwimage])
  have hform : (∑ a, ∑ b, u a * u b * Γ (φ a) (φ b)) =
      ∑ x, ∑ y, w x * w y * Γ x y := by
    calc
      (∑ a, ∑ b, u a * u b * Γ (φ a) (φ b)) =
          ∑ a, ∑ y, u a * w y * Γ (φ a) y :=
        sum_congr rfl fun a _ => hinner a
      _ = ∑ x, ∑ y, w x * w y * Γ x y :=
        Fintype.sum_of_injective φ hφ _ _
          (fun x hx => by rw [hwout x hx]; simp)
          (fun a => by rw [hwimage])
  have h := appendixA_quadratic_le_norm Γ w
  rwa [← hform, ← hsq] at h

/-- Ledger: lem-A.4. A large induced subgraph of a `d`-cube embedded into the
sensitivity graph forces spectral sensitivity at least `sqrt d`.
The witness comes from the literal recursive Huang matrix. -/
theorem appendixA_spectral_of_cube_embedding (f : TotalBool (Fin n))
    (d : ℕ) (hd : 0 < d) (φ : HuangVertex d → BitInput (Fin n))
    (hφ : Injective φ) (U : Finset (HuangVertex d))
    (hU : 2 ^ (d - 1) < #U)
    (hEdge : ∀ x ∈ U, ∀ y ∈ U, huangAdjacent d x y →
      (sensitivityGraph f).Adj (φ x) (φ y)) :
    √(d : ℝ) ≤ spectralSensitivity f := by
  classical
  obtain ⟨v, hv, hv0, hsupp⟩ := huang_supported_positive_eigenvector d hd U hU
  have hRayleigh := huang_absolute_rayleigh d v hv
  let Γ : AppendixAMatrix n := (sensitivityGraph f).adjMatrix ℝ
  have hCompare : (∑ x, ∑ y, |v x| * huangCubeMatrix d x y * |v y|) ≤
      ∑ x, ∑ y, |v x| * |v y| * Γ (φ x) (φ y) := by
    refine sum_le_sum fun x _ => sum_le_sum fun y _ => ?_
    by_cases hx : x ∈ U
    · by_cases hy : y ∈ U
      · have hentry : huangCubeMatrix d x y ≤ Γ (φ x) (φ y) := by
          rw [huangCubeMatrix_eq_ite]
          by_cases hxy : huangAdjacent d x y
          · have hs := hEdge x hx y hy hxy
            simp [hxy, Γ, SimpleGraph.adjMatrix_apply, hs]
          · simp only [hxy, if_false]
            change (0 : ℝ) ≤ if (sensitivityGraph f).Adj (φ x) (φ y) then 1 else 0
            split_ifs <;> norm_num
        calc
          |v x| * huangCubeMatrix d x y * |v y| =
              (|v x| * |v y|) * huangCubeMatrix d x y := by ring
          _ ≤ (|v x| * |v y|) * Γ (φ x) (φ y) :=
            mul_le_mul_of_nonneg_left hentry (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      · simp [hsupp y hy]
    · simp [hsupp x hx]
  have hNorm := appendixA_quadratic_embedding Γ φ hφ (fun x => |v x|)
  have hΓnorm : appendixAMatrixNorm Γ = spectralSensitivity f :=
    (appendixA_spectralSensitivity_eq f).symm
  rw [hΓnorm] at hNorm
  have hPositive : 0 < ∑ x, |v x| ^ 2 := by
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 := by
      by_contra h
      push_neg at h
      exact hv0 (funext h)
    exact (sq_pos_of_ne_zero (abs_ne_zero.2 hx)).trans_le
      (single_le_sum (fun y _ => sq_nonneg (|v y|)) (mem_univ x))
  exact le_of_mul_le_mul_right (hRayleigh.trans (hCompare.trans hNorm)) hPositive

/-- Ledger: lem-A.4. The paper's degree-versus-spectral-sensitivity route:
restrict a maximum monomial, take a large explicit parity fiber, apply the
literal recursive signed-cube theorem and extend its vector by zero.
Constant functions are included. -/
theorem appendixA4_paper_route (f : TotalBool (Fin n)) :
    (degree f : ℝ) ≤ spectralSensitivity f ^ 2 := by
  classical
  rcases Nat.eq_zero_or_pos (degree f) with h0 | hpos
  · rw [h0, Nat.cast_zero]
    positivity
  obtain ⟨S, hS, hcoeff⟩ := appendixA_topFourierSupport f hpos.ne'
  let z : BitInput (Fin n) := fun _ => false
  let g : TotalBool (Fin #S) := appendixAFaceFin f S z
  have hne : fourierCoeff (fun y => signVal (g y)) univ ≠ 0 := by
    rw [appendixA_faceFin_fourier f S z]
    exact appendixA_topFourier_survives_ne_zero f S hS hcoeff z
  obtain ⟨c, hc, he⟩ := appendixA_parityFiber_explicit hne
  let V : Finset (BitInput (Fin #S)) := {y | (g y ^^ parityOn univ y) = c}
  change 2 ^ #S < 2 * #V at hc
  let e : HuangVertex #S ≃ BitInput (Fin #S) := huangVertexEquivInput #S
  let U : Finset (HuangVertex #S) := V.map e.symm.toEmbedding
  have hmem (x : HuangVertex #S) : x ∈ U ↔ e x ∈ V := by
    change x ∈ V.map e.symm.toEmbedding ↔ e x ∈ V
    rw [mem_map]
    constructor
    · rintro ⟨y, hy, hxy⟩
      change e.symm y = x at hxy
      rw [← hxy, e.apply_symm_apply]
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  have hd : 0 < #S := by omega
  have hpow : 2 ^ #S = 2 * 2 ^ (#S - 1) := by
    cases hcard : #S with
    | zero => omega
    | succ d => simp [pow_succ, Nat.mul_comm]
  have hU : 2 ^ (#S - 1) < #U := by
    change 2 ^ (#S - 1) < #(V.map e.symm.toEmbedding)
    rw [card_map]
    omega
  let φ : HuangVertex #S → BitInput (Fin n) := appendixAFaceEmbedding S z ∘ e
  have hφ : Injective φ := (appendixAFaceEmbedding_injective S z).comp e.injective
  have hEdges : ∀ x ∈ U, ∀ y ∈ U, huangAdjacent #S x y →
      (sensitivityGraph f).Adj (φ x) (φ y) := by
    intro x hx y hy hxy
    have hcube : appendixACubeEdge (e x) (e y) :=
      (huangAdjacent_iff_cubeEdge #S x y).1 hxy
    obtain ⟨i, hflip⟩ := (appendixACubeEdge_iff_update (e x) (e y)).1 hcube
    have hxV : (g (e x) ^^ parityOn univ (e x)) = c := (mem_filter.1 ((hmem x).1 hx)).2
    have hyV : (g (e y) ^^ parityOn univ (e y)) = c := (mem_filter.1 ((hmem y).1 hy)).2
    have hsens : IsSensitiveCoord g (e x) i :=
      he (e x) hxV i (mem_univ i) (by rw [hflip]; exact hyV)
    refine sensitivityGraph_adj.2 ⟨(S.equivFin.symm i).val,
      appendixAFaceEmbedding_sensitive f S z (e x) i hsens, ?_⟩
    change update (appendixAFaceEmbedding S z (e x)) (S.equivFin.symm i).val
      (!(appendixAFaceEmbedding S z (e x) (S.equivFin.symm i))) =
        appendixAFaceEmbedding S z (e y)
    rw [← appendixAFaceEmbedding_update, hflip]
  have hroot := appendixA_spectral_of_cube_embedding f #S hd φ hφ U hU hEdges
  rw [← hS]
  calc
    (#S : ℝ) = √(#S : ℝ) ^ 2 := (Real.sq_sqrt (Nat.cast_nonneg _)).symm
    _ ≤ spectralSensitivity f ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hroot 2

end QuarticQuery.Paper

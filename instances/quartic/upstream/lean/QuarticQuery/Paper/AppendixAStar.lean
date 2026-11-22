module

public import QuarticQuery.Paper.AppendixASpectralAdversary
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import all Mathlib.Basic.Real.Basic

/-!
# Appendix A: the star adversary for block sensitivity

Compiled as part of the `QuarticQuery` library target.

The proof follows the star-matrix argument of Lemma A.3. Applying the star to
the unit vector at its centre gives a vector with one unit coordinate at each
leaf, so the square of the star's norm is at least its number of leaves. A
matching Cauchy--Schwarz bound also gives the paper's exact star-norm identity. A
coordinate mask retains at most one undirected edge, since the sensitive blocks
are disjoint. The general nonnegative adversary theorem gives `bs(f) ≤ 35² Q²`.
No polynomial lower bound is used in this module's final theorem.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Cslib Finset
open Cslib.BitString Cslib.QueryComplexity
open scoped BigOperators Matrix

section FiniteMatrices

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Ledger: lem-A.3.bs. The adjacency matrix of a single undirected edge. -/
noncomputable def appendixA_edgeMatrix (a b : α) : Matrix α α ℝ := fun u v =>
  (if u = a then 1 else 0) * (if v = b then 1 else 0) +
  (if u = b then 1 else 0) * (if v = a then 1 else 0)

/-- Ledger: lem-A.3.bs. A single-edge matrix is symmetric. -/
theorem appendixA_edgeMatrix_symm (a b u v : α) :
    appendixA_edgeMatrix a b u v = appendixA_edgeMatrix a b v u := by
  unfold appendixA_edgeMatrix
  ring

/-- Ledger: lem-A.3.bs. A single-edge matrix has nonnegative entries. -/
theorem appendixA_edgeMatrix_nonneg (a b u v : α) :
    0 ≤ appendixA_edgeMatrix a b u v := by
  unfold appendixA_edgeMatrix
  positivity

/-- Ledger: lem-A.3.bs. Multiplying a vector by an edge exchanges the two
endpoint coordinates and sets all other coordinates to zero. -/
theorem appendixA_edgeMatrix_mulVec (a b u : α) (z : α → ℝ) :
    (appendixA_edgeMatrix a b *ᵥ z) u =
      (if u = a then z b else 0) + (if u = b then z a else 0) := by
  by_cases hua : u = a <;> by_cases hub : u = b <;>
    simp [appendixA_edgeMatrix, Matrix.mulVec, dotProduct, hua, hub,
      add_mul, ite_mul, Finset.sum_add_distrib]

/-- Ledger: lem-A.3.bs. The Euclidean operator norm of one undirected edge
is at most one. The distinctness hypothesis excludes a doubled loop. -/
theorem appendixA_edgeMatrix_norm_le_one (a b : α) (hab : a ≠ b) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_edgeMatrix a b)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have hsquare (u : α) :
      ((if u = a then z b else 0) + (if u = b then z a else 0)) ^ 2 =
        (if u = a then (z b) ^ 2 else 0) +
          (if u = b then (z a) ^ 2 else 0) := by
    by_cases hua : u = a <;> by_cases hub : u = b <;> simp_all
  have hnorm :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_edgeMatrix a b) z‖ ^ 2 =
        (z a) ^ 2 + (z b) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ u, ((appendixA_edgeMatrix a b *ᵥ z.ofLp) u) ^ 2) = _
    simp_rw [appendixA_edgeMatrix_mulVec]
    change (∑ u, ((if u = a then z b else 0) +
      (if u = b then z a else 0)) ^ 2) = _
    simp_rw [hsquare]
    simp [Finset.sum_add_distrib, add_comm]
  have hle : (z a) ^ 2 + (z b) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (z a) ^ 2 + (z b) ^ 2 = ∑ u ∈ ({a, b} : Finset α), (z u) ^ 2 := by
        simp [hab]
      _ ≤ ∑ u : α, (z u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun u _ _ => sq_nonneg (z u))
  nlinarith [norm_nonneg z,
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_edgeMatrix a b) z)]

/-- Ledger: lem-A.3.bs. A star is the sum of its centre-to-leaf edge matrices. -/
noncomputable def appendixA_starMatrix (c : α) (L : Finset α) : Matrix α α ℝ :=
  ∑ y ∈ L, appendixA_edgeMatrix c y

/-- Ledger: lem-A.3.bs. The star is symmetric. -/
theorem appendixA_starMatrix_symm (c : α) (L : Finset α) (u v : α) :
    appendixA_starMatrix c L u v = appendixA_starMatrix c L v u := by
  simp only [appendixA_starMatrix, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun y _ => appendixA_edgeMatrix_symm c y u v

/-- Ledger: lem-A.3.bs. The star has nonnegative entries. -/
theorem appendixA_starMatrix_nonneg (c : α) (L : Finset α) (u v : α) :
    0 ≤ appendixA_starMatrix c L u v := by
  simp only [appendixA_starMatrix, Matrix.sum_apply]
  exact Finset.sum_nonneg fun y _ => appendixA_edgeMatrix_nonneg c y u v

/-- Ledger: lem-A.3.bs. The centre receives the sum of the leaf coordinates;
each leaf receives the centre coordinate. -/
theorem appendixA_starMatrix_mulVec (c u : α) (L : Finset α) (z : α → ℝ) :
    (appendixA_starMatrix c L *ᵥ z) u =
      (if u = c then ∑ y ∈ L, z y else 0) + (if u ∈ L then z c else 0) := by
  simp only [Matrix.mulVec, dotProduct, appendixA_starMatrix, Matrix.sum_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  change (∑ y ∈ L, (appendixA_edgeMatrix c y *ᵥ z) u) = _
  simp_rw [appendixA_edgeMatrix_mulVec]
  rw [Finset.sum_add_distrib]
  have hfirst : (∑ y ∈ L, if u = c then z y else 0) =
      if u = c then ∑ y ∈ L, z y else 0 := by
    by_cases hu : u = c <;> simp [hu]
  rw [hfirst]
  simp [eq_comm]

/-- Ledger: lem-A.3.bs. Applying a star to its centre basis vector gives
the indicator of its leaf set. -/
theorem appendixA_starMatrix_mulVec_center (c : α) (L : Finset α) (hc : c ∉ L) :
    appendixA_starMatrix c L *ᵥ Pi.single c (1 : ℝ) =
      fun u => if u ∈ L then 1 else 0 := by
  rw [Matrix.mulVec_single_one]
  funext u
  simp only [Matrix.col_apply, appendixA_starMatrix, Matrix.sum_apply]
  calc
    (∑ y ∈ L, appendixA_edgeMatrix c y u c) =
        ∑ y ∈ L, if u = y then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro y hy
      have hyc : y ≠ c := fun h => hc (h ▸ hy)
      simp [appendixA_edgeMatrix, hyc, hyc.symm]
    _ = if u ∈ L then 1 else 0 := by simp [eq_comm]

/-- Ledger: lem-A.3.bs. The square of the star's Euclidean norm is at least
the number of leaves. This is the half of `‖Γ‖ = √b` needed by the proof. -/
theorem appendixA_star_card_le_norm_sq (c : α) (L : Finset α) (hc : c ∉ L) :
    (L.card : ℝ) ≤
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L)‖ ^ 2 := by
  let e : EuclideanSpace ℝ α := WithLp.toLp 2 (Pi.single c (1 : ℝ))
  have he : ‖e‖ = 1 := by
    simp [e, EuclideanSpace.norm_eq, Pi.single_apply]
  have hsq :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L) e‖ ^ 2 = L.card := by
    rw [show e = WithLp.toLp 2 (Pi.single c (1 : ℝ)) from rfl,
      Matrix.toEuclideanCLM_toLp, appendixA_starMatrix_mulVec_center c L hc,
      EuclideanSpace.real_norm_sq_eq]
    simp
  have hle := (Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L)).le_opNorm e
  rw [he, mul_one] at hle
  rw [← hsq]
  exact pow_le_pow_left₀ (norm_nonneg _) hle 2

/-- Ledger: lem-A.3.bs. Cauchy--Schwarz bounds the Euclidean operator norm
of a star by the square root of its number of leaves. -/
theorem appendixA_star_norm_le_sqrt_card (c : α) (L : Finset α) (hc : c ∉ L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L)‖ ≤
      Real.sqrt (L.card : ℝ) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun z => ?_
  have hpoint (u : α) :
      ((if u = c then ∑ y ∈ L, z y else 0) +
        (if u ∈ L then z c else 0)) ^ 2 =
      (if u = c then (∑ y ∈ L, z y) ^ 2 else 0) +
        (if u ∈ L then (z c) ^ 2 else 0) := by
    by_cases huc : u = c <;> by_cases huL : u ∈ L <;> simp_all
  have hnorm :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L) z‖ ^ 2 =
        (∑ y ∈ L, z y) ^ 2 + (L.card : ℝ) * (z c) ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    change (∑ u, ((appendixA_starMatrix c L *ᵥ z.ofLp) u) ^ 2) = _
    simp_rw [appendixA_starMatrix_mulVec]
    change (∑ u, ((if u = c then ∑ y ∈ L, z y else 0) +
      (if u ∈ L then z c else 0)) ^ 2) = _
    simp_rw [hpoint]
    simp [Finset.sum_add_distrib, nsmul_eq_mul]
  have hcs : (∑ y ∈ L, z y) ^ 2 ≤ (L.card : ℝ) * ∑ y ∈ L, (z y) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq L (fun _ : α => (1 : ℝ)) (fun y => z y)
  have hsub : (z c) ^ 2 + ∑ y ∈ L, (z y) ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      (z c) ^ 2 + ∑ y ∈ L, (z y) ^ 2 =
          ∑ y ∈ insert c L, (z y) ^ 2 := by rw [Finset.sum_insert hc]
      _ ≤ ∑ y : α, (z y) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun y _ _ => sq_nonneg (z y))
  have hbound :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L) z‖ ^ 2 ≤
        (L.card : ℝ) * ‖z‖ ^ 2 := by
    rw [hnorm]
    calc
      (∑ y ∈ L, z y) ^ 2 + (L.card : ℝ) * (z c) ^ 2 ≤
          (L.card : ℝ) * (∑ y ∈ L, (z y) ^ 2) + (L.card : ℝ) * (z c) ^ 2 :=
        by linarith [hcs]
      _ = (L.card : ℝ) * ((z c) ^ 2 + ∑ y ∈ L, (z y) ^ 2) := by ring
      _ ≤ (L.card : ℝ) * ‖z‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hsub (Nat.cast_nonneg _)
  have hroot : (Real.sqrt (L.card : ℝ) * ‖z‖) ^ 2 = (L.card : ℝ) * ‖z‖ ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hnonneg : 0 ≤ Real.sqrt (L.card : ℝ) * ‖z‖ :=
    mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
  nlinarith [norm_nonneg
    (Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L) z)]

/-- Ledger: lem-A.3.bs. The paper's exact star-norm identity, valid also
for the empty star. -/
theorem appendixA_star_norm_eq_sqrt_card (c : α) (L : Finset α) (hc : c ∉ L) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_starMatrix c L)‖ =
      Real.sqrt (L.card : ℝ) := by
  apply le_antisymm (appendixA_star_norm_le_sqrt_card c L hc)
  exact (Real.sqrt_le_left (norm_nonneg _)).2 (appendixA_star_card_le_norm_sq c L hc)

/-- Ledger: lem-A.3.bs. If every leaf has opposite output to the centre,
the star vanishes on same-output pairs. -/
theorem appendixA_star_same_output_zero (f : α → Bool) (c : α) (L : Finset α)
    (hf : ∀ y ∈ L, f y ≠ f c) (u v : α) (huv : f u = f v) :
    appendixA_starMatrix c L u v = 0 := by
  have hc : c ∉ L := fun hc => hf c hc rfl
  simp only [appendixA_starMatrix, Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro y hy
  have hfy := hf y hy
  by_cases huc : u = c <;> by_cases huy : u = y <;>
    by_cases hvc : v = c <;> by_cases hvy : v = y <;>
    simp_all [appendixA_edgeMatrix]

end FiniteMatrices

variable {n : ℕ}

/-- Ledger: lem-A.3.bs. Coordinate masking keeps an edge exactly when its
endpoints differ in that coordinate. -/
theorem appendixA_mask_edge (x y : BitInput (Fin n)) (i : Fin n) :
    appendixAGammaCoord (appendixA_edgeMatrix x y) i =
      if x i ≠ y i then appendixA_edgeMatrix x y else 0 := by
  by_cases hxy : x i ≠ y i
  · rw [if_pos hxy]
    ext u v
    by_cases hux : u = x <;> by_cases huy : u = y <;>
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
      simp_all [appendixAGammaCoord, appendixA_edgeMatrix, ne_comm, eq_comm]
  · rw [if_neg hxy]
    ext u v
    by_cases hux : u = x <;> by_cases huy : u = y <;>
      by_cases hvx : v = x <;> by_cases hvy : v = y <;>
      simp_all [appendixAGammaCoord, appendixA_edgeMatrix, ne_comm, eq_comm]

/-- Ledger: lem-A.3.bs. A coordinate mask of a star retains precisely its
leaves that differ from the centre at that coordinate. -/
theorem appendixA_mask_star (x : BitInput (Fin n)) (L : Finset (BitInput (Fin n)))
    (i : Fin n) :
    appendixAGammaCoord (appendixA_starMatrix x L) i =
      ∑ y ∈ L.filter (fun y => x i ≠ y i), appendixA_edgeMatrix x y := by
  have hlin : appendixAGammaCoord (appendixA_starMatrix x L) i =
      ∑ y ∈ L, appendixAGammaCoord (appendixA_edgeMatrix x y) i := by
    ext u v
    by_cases huv : u i ≠ v i <;>
      simp [appendixAGammaCoord, appendixA_starMatrix, Matrix.sum_apply, huv]
  rw [hlin]
  simp_rw [appendixA_mask_edge]
  simp only [Finset.sum_filter]

/-- Ledger: lem-A.3.bs. If a coordinate meets at most one centre-to-leaf
edge, the coordinate-masked star has norm at most one. -/
theorem appendixA_mask_star_norm_le_one (x : BitInput (Fin n))
    (L : Finset (BitInput (Fin n))) (hx : x ∉ L) (i : Fin n)
    (hcount : (L.filter (fun y => x i ≠ y i)).card ≤ 1) :
    appendixAMatrixNorm (appendixAGammaCoord (appendixA_starMatrix x L) i) ≤ 1 := by
  rw [appendixA_mask_star, appendixAMatrixNorm, map_sum]
  refine (norm_sum_le _ _).trans ?_
  calc
    (∑ y ∈ L.filter (fun y => x i ≠ y i),
        ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (appendixA_edgeMatrix x y)‖) ≤
        ∑ _y ∈ L.filter (fun y => x i ≠ y i), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro y hy
      apply appendixA_edgeMatrix_norm_le_one
      intro hxy
      apply hx
      simpa only [hxy] using (Finset.mem_filter.1 hy).1
    _ = ((L.filter (fun y => x i ≠ y i)).card : ℝ) := by simp
    _ ≤ 1 := by exact_mod_cast hcount

/-- Ledger: lem-A.3.bs. Flipping blocks at a fixed input is injective in
the block: each coordinate records whether it was flipped. -/
theorem appendixA_flipBlock_injective (x : BitInput (Fin n)) :
    Function.Injective (fun B : Finset (Fin n) => flipBlock B x) := by
  intro B C h
  ext i
  have hi := congrFun h i
  by_cases hiB : i ∈ B <;> by_cases hiC : i ∈ C <;>
    cases hxi : x i <;> simp_all [flipBlock]

/-- Ledger: lem-A.3.bs. The leaves coming from disjoint sensitive blocks
are opposite-output inputs; each coordinate appears on at most one star edge. -/
theorem appendixA_sensitiveFamily_star_properties {f : TotalBool (Fin n)}
    (x : BitInput (Fin n)) (F : Finset (Finset (Fin n))) (hF : IsSensitiveFamily f x F) :
    let L := F.image (fun B => flipBlock B x)
    x ∉ L ∧ L.card = F.card ∧ (∀ y ∈ L, f y ≠ f x) ∧
      ∀ i : Fin n, (L.filter (fun y => x i ≠ y i)).card ≤ 1 := by
  dsimp only
  refine ⟨?_, Finset.card_image_of_injective _ (appendixA_flipBlock_injective x), ?_, ?_⟩
  · intro hx
    obtain ⟨B, hB, hBx⟩ := Finset.mem_image.1 hx
    exact hF.1 B hB (congrArg f hBx)
  · intro y hy
    obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hy
    exact hF.1 B hB
  · intro i
    apply Finset.card_le_one.2
    intro y hy z hz
    obtain ⟨hyL, hyi⟩ := Finset.mem_filter.1 hy
    obtain ⟨hzL, hzi⟩ := Finset.mem_filter.1 hz
    obtain ⟨B, hBF, rfl⟩ := Finset.mem_image.1 hyL
    obtain ⟨C, hCF, rfl⟩ := Finset.mem_image.1 hzL
    by_contra hne
    have hBC : B ≠ C := fun h => hne (congrArg (fun B => flipBlock B x) h)
    have hiB : i ∈ B := by
      by_contra hi
      exact hyi (flipBlock_apply_of_notMem hi).symm
    have hiC : i ∈ C := by
      by_contra hi
      exact hzi (flipBlock_apply_of_notMem hi).symm
    exact Finset.disjoint_left.1 (hF.2 hBF hCF hBC) hiB hiC

/-- Ledger: lem-A.3.bs. The star adversary bounds the size of every
sensitive family by `35² t²` for a `t`-query adaptive algorithm. -/
theorem appendixA_sensitiveFamily_card_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) (x : BitInput (Fin n))
    (F : Finset (Finset (Fin n))) (hF : IsSensitiveFamily f x F) :
    F.card ≤ 1225 * t ^ 2 := by
  let L := F.image (fun B => flipBlock B x)
  obtain ⟨hx, hcard, hf, hcoord⟩ := appendixA_sensitiveFamily_star_properties x F hF
  change x ∉ L at hx
  change L.card = F.card at hcard
  change ∀ y ∈ L, f y ≠ f x at hf
  change ∀ i : Fin n, (L.filter (fun y => x i ≠ y i)).card ≤ 1 at hcoord
  have hnorm : appendixAMatrixNorm (appendixA_starMatrix x L) ≤ 35 * (t : ℝ) := by
    simpa only [mul_one] using appendixA_matrixNorm_le_of_QLe hq
      (appendixA_starMatrix x L) (appendixA_starMatrix_symm x L)
      (appendixA_starMatrix_nonneg x L) (appendixA_star_same_output_zero f x L hf)
      (M := 1) zero_le_one
      (fun i => appendixA_mask_star_norm_le_one x L hx i (hcoord i))
  have hbase := appendixA_star_card_le_norm_sq x L hx
  change (L.card : ℝ) ≤ appendixAMatrixNorm (appendixA_starMatrix x L) ^ 2 at hbase
  rw [hcard] at hbase
  have hsquare := pow_le_pow_left₀
    (show 0 ≤ appendixAMatrixNorm (appendixA_starMatrix x L) from norm_nonneg _) hnorm 2
  have hbound : (F.card : ℝ) ≤ 1225 * (t : ℝ) ^ 2 := by nlinarith
  exact_mod_cast hbound

/-- Ledger: lem-A.3.bs. The appendix's star proof of the uniform
block-sensitivity bound, including constant functions. -/
theorem appendixA_blockSensitivity_star_le_of_QLe {f : TotalBool (Fin n)} {t : ℕ}
    (hq : QLe (totalise f) t) : blockSensitivity f ≤ 1225 * t ^ 2 := by
  unfold blockSensitivity
  apply Finset.sup_le
  intro x hx
  unfold blockSensitivityAt
  apply Finset.sup_le
  intro F hF
  exact appendixA_sensitiveFamily_card_le_of_QLe hq x F (mem_sensitiveFamilies.1 hF)

/-- Ledger: lem-A.3.bs. The star proof at the attained quantum-query minimum. -/
theorem appendixA_blockSensitivity_star_le_Q_sq (f : TotalBool (Fin n)) :
    blockSensitivity f ≤ 1225 * Q (totalise f) ^ 2 :=
  appendixA_blockSensitivity_star_le_of_QLe (QLe_Q _)

/-! ## The sensitivity-graph adversary -/

/-- Ledger: lem-A.3.lambda. The coordinate mask of the sensitivity matrix
contains precisely the sensitive edges in that coordinate. -/
theorem appendixA_sensitivity_mask_apply (f : TotalBool (Fin n)) (i : Fin n)
    (x y : BitInput (Fin n)) :
    appendixAGammaCoord (appendixA_sensitivityMatrix f) i x y =
      if IsSensitiveCoord f x i ∧ Function.update x i (!x i) = y then 1 else 0 := by
  have heq : (x i ≠ y i ∧ (sensitivityGraph f).Adj x y) ↔
      IsSensitiveCoord f x i ∧ Function.update x i (!x i) = y := by
    constructor
    · rintro ⟨hxy, hadj⟩
      obtain ⟨j, hj, hy⟩ := sensitivityGraph_adj.1 hadj
      have hji : j = i := by
        by_contra hji
        apply hxy
        calc
          x i = (Function.update x j (!x j)) i :=
            (Function.update_of_ne (Ne.symm hji) _ _).symm
          _ = y i := congrFun hy i
      subst j
      exact ⟨hj, hy⟩
    · rintro ⟨hi, hy⟩
      refine ⟨?_, sensitivityGraph_adj.2 ⟨i, hi, hy⟩⟩
      rw [← hy, Function.update_self]
      cases x i <;> decide
  by_cases h : IsSensitiveCoord f x i ∧ Function.update x i (!x i) = y
  · obtain ⟨hxy, hadj⟩ := heq.2 h
    simp [appendixAGammaCoord, appendixA_sensitivityMatrix, hxy, hadj, h]
  · by_cases hxy : x i ≠ y i
    · have hadj : ¬ (sensitivityGraph f).Adj x y := fun ha => h (heq.1 ⟨hxy, ha⟩)
      simp [appendixAGammaCoord, appendixA_sensitivityMatrix, hxy, hadj, h]
    · simp [appendixAGammaCoord, hxy, h]

/-- Ledger: lem-A.3.lambda. A masked sensitivity matrix reads at most one
coordinate of the vector in each row. -/
theorem appendixA_sensitivity_mask_mulVec (f : TotalBool (Fin n)) (i : Fin n)
    (z : BitInput (Fin n) → ℝ) (x : BitInput (Fin n)) :
    (appendixAGammaCoord (appendixA_sensitivityMatrix f) i *ᵥ z) x =
      if IsSensitiveCoord f x i then z (Function.update x i (!x i)) else 0 := by
  simp only [Matrix.mulVec, dotProduct, appendixA_sensitivity_mask_apply]
  by_cases hi : IsSensitiveCoord f x i <;> simp [hi, ite_mul, eq_comm]

/-- Ledger: lem-A.3.lambda. The coordinate edges form a partial matching:
their adjacency operator contracts Euclidean norm. -/
theorem appendixA_sensitivity_mask_norm_le_one (f : TotalBool (Fin n)) (i : Fin n) :
    appendixAMatrixNorm (appendixAGammaCoord (appendixA_sensitivityMatrix f) i) ≤ 1 := by
  unfold appendixAMatrixNorm
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => ?_
  rw [one_mul]
  have hsum : (∑ x : BitInput (Fin n), (z (Function.update x i (!x i))) ^ 2) =
      ∑ x : BitInput (Fin n), (z x) ^ 2 := by
    refine Fintype.sum_equiv (flipBlock_involutive ({i} : Finset (Fin n))).toPerm
      _ _ (fun x => ?_)
    simp only [Function.Involutive.coe_toPerm, flipBlock_singleton]
  have hsq :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (appendixAGammaCoord (appendixA_sensitivityMatrix f) i) z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    change (∑ x, ((appendixAGammaCoord (appendixA_sensitivityMatrix f) i *ᵥ
      z.ofLp) x) ^ 2) ≤ ∑ x, (z x) ^ 2
    simp_rw [appendixA_sensitivity_mask_mulVec]
    change (∑ x, (if IsSensitiveCoord f x i then
      z (Function.update x i (!x i)) else 0) ^ 2) ≤ ∑ x, (z x) ^ 2
    calc
      (∑ x, (if IsSensitiveCoord f x i then
          z (Function.update x i (!x i)) else 0) ^ 2) ≤
          ∑ x, (z (Function.update x i (!x i))) ^ 2 := by
        apply Finset.sum_le_sum
        intro x hx
        split_ifs <;> simp [sq_nonneg]
      _ = ∑ x, (z x) ^ 2 := hsum
  nlinarith [norm_nonneg z,
    norm_nonneg (Matrix.toEuclideanCLM (𝕜 := ℝ)
      (appendixAGammaCoord (appendixA_sensitivityMatrix f) i) z)]

/-- Ledger: lem-A.3.lambda. The paper's application of Lemma A.2 with
Γ equal to the sensitivity adjacency matrix, preserving the adaptive cap. -/
theorem appendixA_spectralSensitivity_adversary_le_of_QLe
    {f : TotalBool (Fin n)} {t : ℕ} (hq : QLe (totalise f) t) :
    spectralSensitivity f ≤ 35 * t := by
  have hsym : ∀ x y, appendixA_sensitivityMatrix f x y =
      appendixA_sensitivityMatrix f y x := by
    intro x y
    exact (((sensitivityGraph f).isSymm_adjMatrix (α := ℝ)).apply x y).symm
  have hΓ : ∀ x y, 0 ≤ appendixA_sensitivityMatrix f x y := by
    intro x y
    simp only [appendixA_sensitivityMatrix, SimpleGraph.adjMatrix_apply]
    split_ifs <;> norm_num
  have hzero : ∀ x y, f x = f y → appendixA_sensitivityMatrix f x y = 0 := by
    intro x y hxy
    have hn : ¬ (sensitivityGraph f).Adj x y := fun h =>
      ((appendixA_sensitivityGraph_adj_iff f x y).1 h).1 hxy
    simp [appendixA_sensitivityMatrix, hn]
  rw [appendixA_spectralSensitivity_eq]
  change appendixAMatrixNorm (appendixA_sensitivityMatrix f) ≤ 35 * (t : ℝ)
  simpa only [mul_one] using appendixA_matrixNorm_le_of_QLe hq
    (appendixA_sensitivityMatrix f) hsym hΓ hzero (M := 1) zero_le_one
    (appendixA_sensitivity_mask_norm_le_one f)

/-- Ledger: lem-A.3.lambda. The sensitivity-graph application of the full
nonnegative adversary theorem, at the attained quantum-query minimum. -/
theorem appendixA_spectralSensitivity_adversary_le_Q (f : TotalBool (Fin n)) :
    spectralSensitivity f ≤ 35 * Q (totalise f) :=
  appendixA_spectralSensitivity_adversary_le_of_QLe (QLe_Q _)

/-- Ledger: lem-A.3. Both parts of Lemma A.3 obtained from the full
nonnegative spectral adversary bound: the star and the sensitivity graph. -/
theorem appendixA_lemmaA3_adversary (f : TotalBool (Fin n)) :
    blockSensitivity f ≤ 1225 * Q (totalise f) ^ 2 ∧
      spectralSensitivity f ≤ 35 * Q (totalise f) :=
  ⟨appendixA_blockSensitivity_star_le_Q_sq f,
    appendixA_spectralSensitivity_adversary_le_Q f⟩

end QuarticQuery.Paper

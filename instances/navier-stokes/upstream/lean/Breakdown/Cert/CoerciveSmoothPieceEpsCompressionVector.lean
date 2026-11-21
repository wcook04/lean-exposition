import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionProduct
import Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore

def vecMat (d : Fin 3 → ℂ) (c : ℤ × ℤ → Fin 3 → ℂ) (β : ℤ × ℤ) : Fin 3 → Fin 3 × Fin 3 → ℂ :=
  fun i kl => if i = kl.1 then (if β = 0 then d kl.2 else c β kl.2) else 0

theorem applyMat_vecMat (d : Fin 3 → ℂ) (c : ℤ × ℤ → Fin 3 → ℂ) (β : ℤ × ℤ) (u : Fin 3 × Fin 3 → ℂ)
    (i : Fin 3) :
    applyMat (vecMat d c β) u i = ∑ l : Fin 3, (if β = 0 then d l else c β l) * u (i, l) := by
  unfold applyMat vecMat
  rw [Fintype.sum_prod_type]
  simp

theorem norm_sum_mul_le (a b : Fin 3 → ℂ) :
    ‖∑ l, a l * b l‖ ≤ Real.sqrt (cnormSq a) * Real.sqrt (cnormSq b) := by
  unfold cnormSq
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem cnormSq_rows_le (a : Fin 3 → ℂ) (u : Fin 3 × Fin 3 → ℂ) :
    cnormSq (fun i : Fin 3 => ∑ l, a l * u (i, l)) ≤ cnormSq a * cnormSq u := by
  have hrow : ∀ i : Fin 3, ‖∑ l, a l * u (i, l)‖ ^ 2 ≤ cnormSq a * cnormSq (fun l => u (i, l)) := by
    intro i
    have h := norm_sum_mul_le a (fun l => u (i, l))
    have h0 : 0 ≤ ‖∑ l, a l * u (i, l)‖ := norm_nonneg _
    calc ‖∑ l, a l * u (i, l)‖ ^ 2 ≤ (Real.sqrt (cnormSq a) * Real.sqrt (cnormSq (fun l => u (i, l)))) ^ 2 :=
          pow_le_pow_left₀ h0 h 2
      _ = cnormSq a * cnormSq (fun l => u (i, l)) := by
          rw [mul_pow, Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _),
            Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _)]
  have hu : cnormSq u = ∑ i : Fin 3, cnormSq (fun l => u (i, l)) := by
    unfold cnormSq
    rw [Fintype.sum_prod_type]
  rw [hu, Finset.mul_sum]
  unfold cnormSq at hrow ⊢
  exact Finset.sum_le_sum fun i _ => hrow i

theorem symbolMat_vecMat (H : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ H) (d : Fin 3 → ℂ)
    (c : ℤ × ℤ → Fin 3 → ℂ) (τ φ : ℝ) (u : Fin 3 × Fin 3 → ℂ) :
    applyMat (symbolMat H (vecMat d c) τ φ) u
      = fun i => ∑ l : Fin 3, (d l + ∑ α ∈ H.erase 0, torusPhase α τ φ * c α l) * u (i, l) := by
  funext i
  unfold applyMat symbolMat vecMat
  rw [Fintype.sum_prod_type]
  refine Finset.sum_eq_single_of_mem i (Finset.mem_univ _) (fun k _ hk => ?_) |>.trans ?_
  · refine Finset.sum_eq_zero fun l _ => ?_
    simp [Ne.symm hk]
  · refine Finset.sum_congr rfl fun l _ => ?_
    simp only [if_true]
    congr 1
    rw [← Finset.add_sum_erase H _ h0]
    have hp : torusPhase 0 τ φ = 1 := by simp [torusPhase]
    rw [if_pos rfl, hp, one_mul]
    congr 1
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα)]

theorem vec_product_sum (H : Finset (ℤ × ℤ)) (h0 : (0 : ℤ × ℤ) ∈ H) (d : Fin 3 → ℂ)
    (c : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ) (ι : ℤ × ℤ) :
    (fun i => ∑ j : Fin 3, (g ι (i, j) * d j + ∑ α ∈ H.erase 0, g (ι - α) (i, j) * c α j))
      = ∑ β ∈ H, applyMat (vecMat d c β) (g (ι - β)) := by
  funext i
  rw [Finset.sum_apply]
  simp only [applyMat_vecMat]
  rw [← Finset.add_sum_erase H _ h0]
  simp only [↓reduceIte, sub_zero, Finset.sum_add_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα), mul_comm]

theorem rows_bound (a : Fin 3 → ℂ) (u : Fin 3 × Fin 3 → ℂ) :
    Real.sqrt (cnormSq (fun i : Fin 3 => ∑ l, a l * u (i, l))) ≤ Real.sqrt (cnormSq a) * Real.sqrt (cnormSq u) := by
  rw [← Real.sqrt_mul (Internal.FieldModes.cnormSq_nonneg a)]
  exact Real.sqrt_le_sqrt (cnormSq_rows_le a u)

theorem compression_vec (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (hT : ∀ ι ∈ T, -ι ∉ T)
    (hHneg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics) (h0 : (0 : ℤ × ℤ) ∈ h.harmonics)
    (d : Fin 3 → ℂ) (c : ℤ × ℤ → Fin 3 → ℂ) (S : ℝ) (hS0 : 0 ≤ S)
    (hU : ∀ τ φ, cnormSq (fun l => d l + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * c α l) ≤ S ^ 2)
    (hcneg : ∀ β, cnormSq (c (-β)) = cnormSq (c β))
    (x f : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ)
    (hf : ∀ ι, f ι = fun i => ∑ j : Fin 3,
      (g ι (i, j) * d j + ∑ α ∈ h.harmonics.erase 0, g (ι - α) (i, j) * c α j))
    (hx : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)))
    (hg : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (g ι)))
    (e : ℝ) (he : 0 ≤ e) :
    ∃ c' : ℤ × ℤ → Fin 3 → ℂ,
      (∀ ι, PieceWeights.inPiece T ι →
        Real.sqrt (cnormSq (f ι - c' ι))
          ≤ edgeSum h T (fun β => Real.sqrt (cnormSq (c β))) (fun κ => Real.sqrt (cnormSq (g κ))) ι) ∧
      Summable (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c' ι)).re) ∧
      |∑' ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c' ι)).re|
        ≤ e * S * pieceNorm T (fun κ => Real.sqrt (cnormSq (g κ)))
          * pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ))) := by
  have hrow : ∀ β, β ≠ 0 → ∀ u, applyMat (vecMat d c β) u = fun i => ∑ l, c β l * u (i, l) := by
    intro β hβ u
    funext i
    rw [applyMat_vecMat]
    simp only [if_neg hβ]
  refine compression_of_product h T hT hHneg (vecMat d c) S hS0 ?_ x f g ?_ _ ?_ ?_ hx hg e he
  · intro τ φ u
    rw [symbolMat_vecMat _ h0]
    exact (cnormSq_rows_le _ u).trans
      (mul_le_mul_of_nonneg_right (hU τ φ) (Internal.FieldModes.cnormSq_nonneg u))
  · intro ι
    rw [hf ι, vec_product_sum _ h0]
  · intro β _ hβ u
    rw [hrow β hβ u]
    exact rows_bound _ _
  · intro β _ hβ u
    have hβ' : -β ≠ 0 := neg_ne_zero.mpr hβ
    rw [hrow (-β) hβ' u, ← hcneg β]
    exact rows_bound _ _

def matMat (D : Fin 3 → Fin 3 → ℂ) (C : ℤ × ℤ → Fin 3 × Fin 3 → ℂ) (β : ℤ × ℤ) : Fin 3 → Fin 3 → ℂ :=
  fun i j => if β = 0 then D i j else C β (i, j)

theorem matSqMat_eq (C : Fin 3 × Fin 3 → ℂ) : matSqMat (fun i j => C (i, j)) = cnormSq C := by
  unfold matSqMat cnormSq
  rw [Fintype.sum_prod_type]

theorem mat_bound (C : Fin 3 × Fin 3 → ℂ) (u : Fin 3 → ℂ) :
    Real.sqrt (cnormSq (applyMat (fun i j => C (i, j)) u)) ≤ Real.sqrt (cnormSq C) * Real.sqrt (cnormSq u) := by
  rw [← Real.sqrt_mul (Internal.FieldModes.cnormSq_nonneg C), ← matSqMat_eq]
  exact Real.sqrt_le_sqrt (cnormSq_applyMat_le _ _)

theorem compression_mat (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (hT : ∀ ι ∈ T, -ι ∉ T)
    (hHneg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics) (h0 : (0 : ℤ × ℤ) ∈ h.harmonics)
    (D : Fin 3 → Fin 3 → ℂ) (C : ℤ × ℤ → Fin 3 × Fin 3 → ℂ) (S : ℝ) (hS0 : 0 ≤ S)
    (hU : ∀ τ φ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j, (D i j + ∑ α ∈ h.harmonics.erase 0,
      torusPhase α τ φ * C α (i, j)) * u j) ≤ S ^ 2 * cnormSq u)
    (hcneg : ∀ β, cnormSq (C (-β)) = cnormSq (C β))
    (x f g : ℤ × ℤ → Fin 3 → ℂ)
    (hf : ∀ ι, f ι = fun i => ∑ j : Fin 3,
      (D i j * g ι j + ∑ α ∈ h.harmonics.erase 0, C α (i, j) * g (ι - α) j))
    (hx : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)))
    (hg : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (g ι)))
    (e : ℝ) (he : 0 ≤ e) :
    ∃ c' : ℤ × ℤ → Fin 3 → ℂ,
      (∀ ι, PieceWeights.inPiece T ι →
        Real.sqrt (cnormSq (f ι - c' ι))
          ≤ edgeSum h T (fun β => Real.sqrt (cnormSq (C β))) (fun κ => Real.sqrt (cnormSq (g κ))) ι) ∧
      Summable (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c' ι)).re) ∧
      |∑' ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c' ι)).re|
        ≤ e * S * pieceNorm T (fun κ => Real.sqrt (cnormSq (g κ)))
          * pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ))) := by
  have hp0 : ∀ τ φ, torusPhase 0 τ φ = 1 := fun τ φ => by simp [torusPhase]
  have hne : ∀ β, β ≠ 0 → matMat D C β = fun i j => C β (i, j) := by
    intro β hβ
    funext i j
    simp only [matMat, if_neg hβ]
  refine compression_of_product h T hT hHneg (matMat D C) S hS0 ?_ x f g ?_ _ ?_ ?_ hx hg e he
  · intro τ φ u
    have e1 : applyMat (symbolMat h.harmonics (matMat D C) τ φ) u
        = fun i => ∑ j, (D i j + ∑ α ∈ h.harmonics.erase 0, torusPhase α τ φ * C α (i, j)) * u j := by
      funext i
      unfold applyMat symbolMat
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [← Finset.add_sum_erase h.harmonics _ h0]
      simp only [matMat, ↓reduceIte, hp0, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [if_neg (Finset.ne_of_mem_erase hα)]
    rw [e1]
    exact hU τ φ u
  · intro ι
    rw [hf ι]
    funext i
    rw [Finset.sum_apply, ← Finset.add_sum_erase h.harmonics _ h0]
    unfold applyMat
    simp only [matMat, ↓reduceIte, sub_zero, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα)]
  · intro β _ hβ u
    rw [hne β hβ]
    exact mat_bound _ _
  · intro β _ hβ u
    rw [hne (-β) (neg_ne_zero.mpr hβ), ← hcneg β]
    exact mat_bound _ _

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown

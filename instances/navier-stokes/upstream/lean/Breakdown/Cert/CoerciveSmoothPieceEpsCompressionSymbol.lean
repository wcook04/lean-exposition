import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionGrid

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore


theorem halfSq_nonneg {p : Type} [Fintype p] (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → p → ℂ) (ι : ℤ × ℤ) :
    0 ≤ halfSq T x ι := by
  classical
  unfold halfSq
  split_ifs
  · exact Internal.FieldModes.cnormSq_nonneg _
  · exact le_rfl

def matSqMat {q : Type} [Fintype q] (A : Fin 3 → q → ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

theorem cnormSq_applyMat_le {q : Type} [Fintype q] (A : Fin 3 → q → ℂ) (u : q → ℂ) :
    cnormSq (applyMat A u) ≤ matSqMat A * cnormSq u := by
  unfold cnormSq applyMat matSqMat
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, A i j * u j‖ ≤ Real.sqrt (∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ j, ‖u j‖ ^ 2) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc ‖∑ j, A i j * u j‖ ^ 2 ≤ (Real.sqrt (∑ j, ‖A i j‖ ^ 2) * Real.sqrt (∑ j, ‖u j‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (∑ j, ‖A i j‖ ^ 2) * ∑ j, ‖u j‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _),
          Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]

theorem cdot_finset_sum {κ : Type} (s : Finset κ) (x : Fin 3 → ℂ) (F : κ → Fin 3 → ℂ) :
    cdot x (∑ b ∈ s, F b) = ∑ b ∈ s, cdot x (F b) := by
  unfold cdot
  simp only [Finset.sum_apply, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

open Classical in
def pairPiece {q : Type} [Fintype q] (T : Set (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ) (x : ℤ × ℤ → Fin 3 → ℂ)
    (g : ℤ × ℤ → q → ℂ) (β ι : ℤ × ℤ) : ℂ :=
  if ι ∈ T ∧ ι - β ∈ T then cdot (x ι) (applyMat (A β) (g (ι - β))) else 0

theorem halfPairing_eq {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (T : Set (ℤ × ℤ))
    (A : ℤ × ℤ → Fin 3 → q → ℂ) (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) (ι : ℤ × ℤ) :
    halfPairing H T A x g ι = ∑ β ∈ H, pairPiece T A x g β ι := by
  classical
  unfold halfPairing halfPart pairPiece
  by_cases hι : ι ∈ T
  · rw [if_pos hι, cdot_finset_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    by_cases hb : ι - β ∈ T
    · rw [if_pos hb, if_pos ⟨hι, hb⟩]
    · rw [if_neg hb, if_neg (fun h => hb h.2)]
      unfold cdot
      simp
  · rw [if_neg hι]
    exact (Finset.sum_eq_zero fun β _ => if_neg (fun h => hι h.1)).symm

theorem pairPiece_summable {q : Type} [Fintype q] (T : Set (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → q → ℂ)
    (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) (hx : Summable (halfSq T x)) (hg : Summable (halfSq T g))
    (β : ℤ × ℤ) : Summable (pairPiece T A x g β) := by
  classical
  have hgs : Summable (fun ι => halfSq T g (ι - β)) := (Equiv.subRight β).summable_iff.mpr hg
  have hb : Summable (fun ι => Real.sqrt (matSqMat (A β)) * ((halfSq T x ι + halfSq T g (ι - β)) / 2)) :=
    ((hx.add hgs).div_const 2).mul_left _
  refine Summable.of_norm_bounded hb fun ι => ?_
  have hf0 := Real.sqrt_nonneg (matSqMat (A β))
  unfold pairPiece
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have e1 : halfSq T x ι = cnormSq (x ι) := if_pos h1
    have e2 : halfSq T g (ι - β) = cnormSq (g (ι - β)) := if_pos h2
    rw [e1, e2]
    have c1 := Internal.Field.norm_cdot_le_sqrt (x ι) (applyMat (A β) (g (ι - β)))
    have c2 : Real.sqrt (cnormSq (applyMat (A β) (g (ι - β))))
        ≤ Real.sqrt (matSqMat (A β)) * Real.sqrt (cnormSq (g (ι - β))) := by
      rw [← Real.sqrt_mul (show 0 ≤ matSqMat (A β) from
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
      exact Real.sqrt_le_sqrt (cnormSq_applyMat_le _ _)
    have a0 := Real.sqrt_nonneg (cnormSq (x ι))
    have b0 := Real.sqrt_nonneg (cnormSq (g (ι - β)))
    have sa := Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg (x ι))
    have sb := Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg (g (ι - β)))
    have c3 := mul_le_mul_of_nonneg_left c2 a0
    nlinarith [sq_nonneg (Real.sqrt (cnormSq (x ι)) - Real.sqrt (cnormSq (g (ι - β)))),
      mul_nonneg hf0 (mul_nonneg a0 b0)]
  · rw [norm_zero]
    exact mul_nonneg hf0 (div_nonneg (add_nonneg (halfSq_nonneg T x ι) (halfSq_nonneg T g _)) (by norm_num))

open Classical in
theorem partial_eq {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (T : Set (ℤ × ℤ))
    (A : ℤ × ℤ → Fin 3 → q → ℂ) (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) (s : Finset (ℤ × ℤ)) :
    ∑ ι ∈ s, halfPairing H T A x g ι
      = ∑ ι ∈ s.filter (· ∈ T), ∑ t ∈ H ×ˢ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T),
          if ι = t.1 + t.2 then dotq (x ι) (applyMat (A t.1) (g t.2)) else 0 := by
  classical
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ι hι => ?_
  unfold halfPairing halfPart
  split_ifs with hT
  · rw [cdot_finset_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun β hβ => ?_
    have key : ∀ κ, (ι = β + κ) ↔ (κ = ι - β) := fun κ => by
      constructor <;> intro h <;> subst h <;> abel
    simp only [key]
    rw [Finset.sum_ite_eq']
    by_cases hb : ι - β ∈ T
    · have hm : ι - β ∈ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T) := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(ι, β), ?_, rfl⟩, hb⟩
        exact Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨hι, hT⟩, hβ⟩
      rw [if_pos hb, if_pos hm]
      rfl
    · have hm : ι - β ∉ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T) :=
        fun h => hb (Finset.mem_filter.mp h).2
      rw [if_neg hb, if_neg hm]
      unfold cdot
      simp
  · rfl

theorem symbol_pairing_bound {q : Type} [Fintype q] (H : Finset (ℤ × ℤ)) (T : Set (ℤ × ℤ))
    (A : ℤ × ℤ → Fin 3 → q → ℂ) (S : ℝ) (hS0 : 0 ≤ S)
    (hsym : ∀ τ φ u, cnormSq (applyMat (symbolMat H A τ φ) u) ≤ S ^ 2 * cnormSq u)
    (x : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ) (hx : Summable (halfSq T x)) (hg : Summable (halfSq T g)) :
    Summable (halfPairing H T A x g) ∧
      ‖∑' ι, halfPairing H T A x g ι‖ ≤ S * Real.sqrt (∑' ι, halfSq T x ι) * Real.sqrt (∑' ι, halfSq T g ι) := by
  classical
  have hsum : Summable (halfPairing H T A x g) := by
    have e : halfPairing H T A x g = fun ι => ∑ β ∈ H, pairPiece T A x g β ι := funext (halfPairing_eq H T A x g)
    rw [e]
    exact summable_sum fun β _ => pairPiece_summable T A x g hx hg β
  refine ⟨hsum, ?_⟩
  have hbound : ∀ s : Finset (ℤ × ℤ), ‖∑ ι ∈ s, halfPairing H T A x g ι‖
      ≤ S * Real.sqrt (∑' ι, halfSq T x ι) * Real.sqrt (∑' ι, halfSq T g ι) := by
    intro s
    rw [partial_eq]
    refine (finite_symbol_pairing_bound H A S hS0 hsym _ _ x g).trans ?_
    have hF : ∑ ι ∈ s.filter (· ∈ T), cnormSq (x ι) ≤ ∑' ι, halfSq T x ι := by
      calc ∑ ι ∈ s.filter (· ∈ T), cnormSq (x ι) = ∑ ι ∈ s.filter (· ∈ T), halfSq T x ι :=
            Finset.sum_congr rfl fun ι h => (if_pos (Finset.mem_filter.mp h).2).symm
        _ ≤ _ := hx.sum_le_tsum _ (fun ι _ => halfSq_nonneg T x ι)
    have hK : ∑ κ ∈ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T), cnormSq (g κ)
        ≤ ∑' ι, halfSq T g ι := by
      calc ∑ κ ∈ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T), cnormSq (g κ)
          = ∑ κ ∈ (((s.filter (· ∈ T)) ×ˢ H).image (fun p => p.1 - p.2)).filter (· ∈ T), halfSq T g κ :=
            Finset.sum_congr rfl fun ι h => (if_pos (Finset.mem_filter.mp h).2).symm
        _ ≤ _ := hg.sum_le_tsum _ (fun ι _ => halfSq_nonneg T g ι)
    gcongr
  exact le_of_tendsto' (Filter.Tendsto.norm hsum.hasSum) hbound

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown

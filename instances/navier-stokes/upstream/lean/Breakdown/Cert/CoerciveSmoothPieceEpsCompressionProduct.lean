import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionSymbol

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCompression

open Internal.SmoothPieceEpsCore

theorem cnormSq_add (a b : Fin 3 → ℂ) : cnormSq (a + b) = cnormSq a + cnormSq b + 2 * (cdot a b).re := by
  unfold cnormSq cdot
  simp only [Pi.add_apply, Complex.sq_norm, Complex.normSq_add, Complex.re_sum, Finset.sum_add_distrib,
    Finset.mul_sum]

theorem sqrt_cnormSq_add_le (a b : Fin 3 → ℂ) :
    Real.sqrt (cnormSq (a + b)) ≤ Real.sqrt (cnormSq a) + Real.sqrt (cnormSq b) := by
  have ha := Internal.FieldModes.cnormSq_nonneg a
  have hb := Internal.FieldModes.cnormSq_nonneg b
  have hc := Internal.Field.norm_cdot_le_sqrt a b
  have hre := Complex.re_le_norm (cdot a b)
  have hsa := Real.sq_sqrt ha
  have hsb := Real.sq_sqrt hb
  have h0 : 0 ≤ Real.sqrt (cnormSq a) + Real.sqrt (cnormSq b) :=
    add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  rw [Real.sqrt_le_left h0]
  rw [cnormSq_add]
  nlinarith

theorem sqrt_cnormSq_sum_le {κ : Type} (s : Finset κ) (F : κ → Fin 3 → ℂ) :
    Real.sqrt (cnormSq (∑ b ∈ s, F b)) ≤ ∑ b ∈ s, Real.sqrt (cnormSq (F b)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : cnormSq (0 : Fin 3 → ℂ) = 0 := by simp [cnormSq]
    simp [this]
  | insert b s hb ih =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb]
    exact (sqrt_cnormSq_add_le _ _).trans (by linarith)

theorem sum_neg_reindex {M : Type} [AddCommMonoid M] (H : Finset (ℤ × ℤ)) (hH : ∀ β ∈ H, -β ∈ H)
    (F : ℤ × ℤ → M) : ∑ β ∈ H, F β = ∑ β ∈ H, F (-β) :=
  Finset.sum_bij' (fun β _ => -β) (fun β _ => -β) (fun β hβ => hH β hβ) (fun β hβ => hH β hβ)
    (fun β _ => neg_neg β) (fun β _ => neg_neg β) (fun β _ => by simp)

theorem sqrt_mul_add_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt b + Real.sqrt c * Real.sqrt d ≤ Real.sqrt (a + c) * Real.sqrt (b + d) := by
  rw [← Real.sqrt_mul (add_nonneg ha hc)]
  refine le_trans (le_abs_self _) (Real.abs_le_sqrt ?_)
  have h1 := Real.sq_sqrt ha
  have h2 := Real.sq_sqrt hb
  have h3 := Real.sq_sqrt hc
  have h4 := Real.sq_sqrt hd
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt c * Real.sqrt b)]

theorem halfSq_le {p : Type} [Fintype p] (T T' : Set (ℤ × ℤ)) (hTT : ∀ ι ∈ T', PieceWeights.inPiece T ι)
    (x : ℤ × ℤ → p → ℂ) (ι : ℤ × ℤ) :
    halfSq T' x ι ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι) := by
  classical
  unfold halfSq
  split_ifs with h
  · have h1 : ModeWeights.ind (PieceWeights.inPiece T ι) = 1 := by
      unfold ModeWeights.ind; rw [if_pos (hTT ι h)]
    rw [h1, one_mul]
  · exact mul_nonneg (ind_nonneg T ι) (Internal.FieldModes.cnormSq_nonneg _)

theorem ind_split {p : Type} [Fintype p] (T : Set (ℤ × ℤ)) (hT : ∀ ι ∈ T, -ι ∉ T) (x : ℤ × ℤ → p → ℂ)
    (ι : ℤ × ℤ) :
    ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι) = halfSq T x ι + halfSq (-T) x ι := by
  classical
  unfold ModeWeights.ind PieceWeights.inPiece halfSq
  by_cases h1 : ι ∈ T
  · have h2 : ι ∉ -T := by
      rw [Set.mem_neg]; exact hT ι h1
    simp [h1, h2]
  · by_cases h2 : -ι ∈ T
    · have h3 : ι ∈ -T := by rw [Set.mem_neg]; exact h2
      simp [h1, h2, h3]
    · have h3 : ι ∉ -T := by rw [Set.mem_neg]; exact h2
      simp [h1, h2, h3]

theorem compression_of_product {q : Type} [Fintype q] (h : HarmonicBounds) (T : Set (ℤ × ℤ))
    (hT : ∀ ι ∈ T, -ι ∉ T) (hHneg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics)
    (A : ℤ × ℤ → Fin 3 → q → ℂ) (S : ℝ) (hS0 : 0 ≤ S)
    (hsym : ∀ τ φ u, cnormSq (applyMat (symbolMat h.harmonics A τ φ) u) ≤ S ^ 2 * cnormSq u)
    (x f : ℤ × ℤ → Fin 3 → ℂ) (g : ℤ × ℤ → q → ℂ)
    (hf : ∀ ι, f ι = ∑ β ∈ h.harmonics, applyMat (A β) (g (ι - β)))
    (X : ℤ × ℤ → ℝ)
    (hX : ∀ β ∈ h.harmonics, β ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (A β) u)) ≤ X β * Real.sqrt (cnormSq u))
    (hXneg : ∀ β ∈ h.harmonics, β ≠ 0 → ∀ u,
      Real.sqrt (cnormSq (applyMat (A (-β)) u)) ≤ X β * Real.sqrt (cnormSq u))
    (hx : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)))
    (hg : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (g ι)))
    (e : ℝ) (he : 0 ≤ e) :
    ∃ c : ℤ × ℤ → Fin 3 → ℂ,
      (∀ ι, PieceWeights.inPiece T ι →
        Real.sqrt (cnormSq (f ι - c ι)) ≤ edgeSum h T X (fun κ => Real.sqrt (cnormSq (g κ))) ι) ∧
      Summable (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re) ∧
      |∑' ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re|
        ≤ e * S * pieceNorm T (fun κ => Real.sqrt (cnormSq (g κ)))
          * pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ))) := by
  classical
  have hnegT : ∀ ι, ι ∈ -T ↔ -ι ∈ T := fun ι => Set.mem_neg
  set H := h.harmonics
  let c : ℤ × ℤ → Fin 3 → ℂ := fun ι =>
    if ι ∈ T then halfPart H T A g ι else if -ι ∈ T then halfPart H (-T) A g ι else 0
  refine ⟨c, ?_, ?_⟩
  · intro ι hι
    by_cases h1 : ι ∈ T
    · have ec : f ι - c ι = ∑ β ∈ H, if ι - β ∈ T then 0 else applyMat (A β) (g (ι - β)) := by
        simp only [c, if_pos h1, hf ι, halfPart, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs <;> simp
      rw [ec]
      refine (sqrt_cnormSq_sum_le _ _).trans ?_
      unfold edgeSum
      rw [if_pos h1]
      refine Finset.sum_le_sum fun β hβ => ?_
      split_ifs with h2
      · have : cnormSq (0 : Fin 3 → ℂ) = 0 := by simp [cnormSq]
        rw [this, Real.sqrt_zero]
      · have hb : β ≠ 0 := by
          rintro rfl
          exact h2 (by simpa using h1)
        exact hX β hβ hb _
    · have h2 : -ι ∈ T := hι.resolve_left h1
      have ec : f ι - c ι = ∑ β ∈ H, if ι - β ∈ -T then 0 else applyMat (A β) (g (ι - β)) := by
        simp only [c, if_neg h1, if_pos h2, hf ι, halfPart, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun β _ => ?_
        split_ifs <;> simp
      rw [ec, sum_neg_reindex H hHneg]
      refine (sqrt_cnormSq_sum_le _ _).trans ?_
      unfold edgeSum
      rw [if_neg h1, if_pos h2]
      refine Finset.sum_le_sum fun β hβ => ?_
      have hm : ι - -β ∈ -T ↔ -ι - β ∈ T := by
        rw [hnegT]
        constructor <;> intro hh <;> convert hh using 1 <;> abel
      have hs : ι - -β = ι + β := by abel
      by_cases h3 : -ι - β ∈ T
      · rw [if_pos (hm.2 h3), if_pos h3]
        have : cnormSq (0 : Fin 3 → ℂ) = 0 := by simp [cnormSq]
        rw [this, Real.sqrt_zero]
      · rw [if_neg (fun hh => h3 (hm.1 hh)), if_neg h3, hs]
        have hb : β ≠ 0 := by
          rintro rfl
          exact h3 (by simpa using h2)
        exact hXneg β hβ hb _
  · have hxT : Summable (halfSq T x) := hx.of_nonneg_of_le (halfSq_nonneg T x)
      (halfSq_le T T (fun ι h => Or.inl h) x)
    have hxN : Summable (halfSq (-T) x) := hx.of_nonneg_of_le (halfSq_nonneg (-T) x)
      (halfSq_le T (-T) (fun ι h => Or.inr ((hnegT ι).1 h)) x)
    have hgT : Summable (halfSq T g) := hg.of_nonneg_of_le (halfSq_nonneg T g)
      (halfSq_le T T (fun ι h => Or.inl h) g)
    have hgN : Summable (halfSq (-T) g) := hg.of_nonneg_of_le (halfSq_nonneg (-T) g)
      (halfSq_le T (-T) (fun ι h => Or.inr ((hnegT ι).1 h)) g)
    obtain ⟨sT, bT⟩ := symbol_pairing_bound H T A S hS0 hsym x g hxT hgT
    obtain ⟨sN, bN⟩ := symbol_pairing_bound H (-T) A S hS0 hsym x g hxN hgN
    have hterm : ∀ ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re
        = (Complex.I * (e : ℂ) * halfPairing H T A x g ι).re
          - (Complex.I * (e : ℂ) * halfPairing H (-T) A x g ι).re := by
      intro ι
      unfold halfPairing PieceWeights.sgn
      by_cases h1 : ι ∈ T
      · have h2 : ι ∉ -T := by rw [hnegT]; exact hT ι h1
        simp [c, h1, h2]
      · by_cases h2 : -ι ∈ T
        · have h3 : ι ∈ -T := by rw [hnegT]; exact h2
          simp [c, h1, h2, h3]
        · have h3 : ι ∉ -T := by rw [hnegT]; exact h2
          simp [c, h1, h2, h3]
    have HT := Complex.hasSum_re (sT.hasSum.mul_left (Complex.I * (e : ℂ)))
    have HN := Complex.hasSum_re (sN.hasSum.mul_left (Complex.I * (e : ℂ)))
    have Hall := HT.sub HN
    have e1 : (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re)
        = fun ι => (Complex.I * (e : ℂ) * halfPairing H T A x g ι).re
          - (Complex.I * (e : ℂ) * halfPairing H (-T) A x g ι).re := funext hterm
    rw [e1]
    refine ⟨Hall.summable, ?_⟩
    rw [Hall.tsum_eq]
    have a1 := Internal.FieldModes.abs_re_I_mul_le e (∑' ι, halfPairing H T A x g ι)
    have a2 := Internal.FieldModes.abs_re_I_mul_le e (∑' ι, halfPairing H (-T) A x g ι)
    rw [abs_of_nonneg he] at a1 a2
    have hxs := Real.sqrt_nonneg (∑' ι, halfSq T x ι)
    have hgs := Real.sqrt_nonneg (∑' ι, halfSq T g ι)
    have hcs := sqrt_mul_add_le (∑' ι, halfSq T x ι) (∑' ι, halfSq T g ι) (∑' ι, halfSq (-T) x ι)
      (∑' ι, halfSq (-T) g ι) (tsum_nonneg (halfSq_nonneg T x)) (tsum_nonneg (halfSq_nonneg T g))
      (tsum_nonneg (halfSq_nonneg (-T) x)) (tsum_nonneg (halfSq_nonneg (-T) g))
    have px : pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ)))
        = Real.sqrt (∑' ι, halfSq T x ι + ∑' ι, halfSq (-T) x ι) := by
      unfold pieceNorm
      rw [← hxT.tsum_add hxN]
      congr 1
      refine tsum_congr fun ι => ?_
      rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _), ind_split T hT x ι]
    have pg : pieceNorm T (fun κ => Real.sqrt (cnormSq (g κ)))
        = Real.sqrt (∑' ι, halfSq T g ι + ∑' ι, halfSq (-T) g ι) := by
      unfold pieceNorm
      rw [← hgT.tsum_add hgN]
      congr 1
      refine tsum_congr fun ι => ?_
      rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _), ind_split T hT g ι]
    rw [px, pg]
    have k1 := mul_le_mul_of_nonneg_left bT he
    have k2 := mul_le_mul_of_nonneg_left bN he
    have k3 := mul_le_mul_of_nonneg_left hcs (mul_nonneg he hS0)
    calc |(Complex.I * (e : ℂ) * ∑' ι, halfPairing H T A x g ι).re
          - (Complex.I * (e : ℂ) * ∑' ι, halfPairing H (-T) A x g ι).re|
        ≤ |(Complex.I * (e : ℂ) * ∑' ι, halfPairing H T A x g ι).re|
          + |(Complex.I * (e : ℂ) * ∑' ι, halfPairing H (-T) A x g ι).re| := abs_sub _ _
      _ ≤ e * ‖∑' ι, halfPairing H T A x g ι‖ + e * ‖∑' ι, halfPairing H (-T) A x g ι‖ := add_le_add a1 a2
      _ ≤ e * S * (Real.sqrt (∑' ι, halfSq T x ι) * Real.sqrt (∑' ι, halfSq T g ι)
          + Real.sqrt (∑' ι, halfSq (-T) x ι) * Real.sqrt (∑' ι, halfSq (-T) g ι)) := by nlinarith
      _ ≤ _ := by nlinarith [k3]

end Internal.SmoothPieceEpsCompression

end Coercive

end Breakdown

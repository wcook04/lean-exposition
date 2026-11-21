import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionVector
import Breakdown.Cert.CoerciveSmoothPieceEpsRestDefs
import Breakdown.Cert.ExtendedCoercivePieceEpsTransport

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceEpsStretch

open Coercive Coercive.Internal.SmoothPieceEpsCore Coercive.Internal.SmoothPieceEpsCompression
  Coercive.Internal.PieceAbsorb Internal.ExtendedPieceEpsTransport

def symPart (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) : ℤ × ℤ → Fin 3 → Fin 3 → ℂ :=
  fun β i j => (A β i j + A β j i) / 2

def antiPart (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) : ℤ × ℤ → Fin 3 → Fin 3 → ℂ :=
  fun β i j => (A β i j - A β j i) / 2

theorem sym_add_anti (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) (β : ℤ × ℤ) (i j : Fin 3) :
    A β i j = symPart A β i j + antiPart A β i j := by
  unfold symPart antiPart
  ring

theorem symPart_conj (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) (hA : ∀ β i j, A (-β) i j = starRingEnd ℂ (A β i j))
    (β : ℤ × ℤ) (i j : Fin 3) : symPart A (-β) i j = starRingEnd ℂ (symPart A β j i) := by
  unfold symPart
  rw [hA, hA]
  simp only [map_div₀, map_add, map_ofNat]
  ring

theorem symbolMat_anti (H : Finset (ℤ × ℤ)) (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) (τ φ : ℝ) (i j : Fin 3) :
    symbolMat H (antiPart A) τ φ i j = (symbolMat H A τ φ i j - symbolMat H A τ φ j i) / 2 := by
  unfold symbolMat antiPart
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem cdot_add_right (x a b : Fin 3 → ℂ) : cdot x (a + b) = cdot x a + cdot x b := by
  simp only [cdot, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem pairPiece_split (T : Set (ℤ × ℤ)) (A B K : ℤ × ℤ → Fin 3 → Fin 3 → ℂ)
    (hABK : ∀ β i j, A β i j = B β i j + K β i j) (x g : ℤ × ℤ → Fin 3 → ℂ) (β ι : ℤ × ℤ) :
    pairPiece T A x g β ι = pairPiece T B x g β ι + pairPiece T K x g β ι := by
  classical
  unfold pairPiece
  split_ifs
  · have e : applyMat (A β) (g (ι - β)) = applyMat (B β) (g (ι - β)) + applyMat (K β) (g (ι - β)) := by
      funext i
      simp only [applyMat, Pi.add_apply, hABK, add_mul, Finset.sum_add_distrib]
    rw [e, cdot_add_right]
  · rw [add_zero]

theorem pairPiece_conj (T : Set (ℤ × ℤ)) (B : ℤ × ℤ → Fin 3 → Fin 3 → ℂ)
    (hB : ∀ β i j, B (-β) i j = starRingEnd ℂ (B β j i)) (x : ℤ × ℤ → Fin 3 → ℂ) (β ι : ℤ × ℤ) :
    starRingEnd ℂ (pairPiece T B x x β ι) = pairPiece T B x x (-β) (ι - β) := by
  classical
  have e : ι - β - -β = ι := by abel
  unfold pairPiece
  rw [e]
  by_cases h : ι ∈ T ∧ ι - β ∈ T
  · rw [if_pos h, if_pos ⟨h.2, h.1⟩]
    simp only [cdot, applyMat, hB, map_sum, map_mul, Complex.conj_conj, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨h'.2, h'.1⟩), map_zero]

theorem tsum_pair_im (H : Finset (ℤ × ℤ)) (hH : ∀ β ∈ H, -β ∈ H) (T : Set (ℤ × ℤ))
    (B : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) (hB : ∀ β i j, B (-β) i j = starRingEnd ℂ (B β j i))
    (x : ℤ × ℤ → Fin 3 → ℂ) (hx : Summable (halfSq T x)) :
    (∑' ι, halfPairing H T B x x ι).im = 0 := by
  have hs : ∀ β, Summable (pairPiece T B x x β) := pairPiece_summable T B x x hx hx
  have e : ∑' ι, halfPairing H T B x x ι = ∑ β ∈ H, ∑' ι, pairPiece T B x x β ι := by
    simp_rw [halfPairing_eq]
    exact Summable.tsum_finsetSum fun β _ => hs β
  rw [← Complex.conj_eq_iff_im, e, map_sum]
  calc ∑ β ∈ H, starRingEnd ℂ (∑' ι, pairPiece T B x x β ι)
      = ∑ β ∈ H, ∑' ι, pairPiece T B x x (-β) ι := by
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [Complex.conj_tsum]
        simp_rw [pairPiece_conj T B hB x β]
        exact (Equiv.subRight β).tsum_eq (pairPiece T B x x (-β))
    _ = ∑ β ∈ H, ∑' ι, pairPiece T B x x β ι :=
        (sum_neg_reindex H hH (fun β => ∑' ι, pairPiece T B x x β ι)).symm

theorem anti_rows_bound (r : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℂ) :
    cnormSq (fun i => ∑ j, (((r i j - r j i) / 2 : ℝ) : ℂ) * u j)
      ≤ ((r 2 1 - r 1 2) ^ 2 + (r 0 2 - r 2 0) ^ 2 + (r 1 0 - r 0 1) ^ 2) / 4 * cnormSq u := by
  unfold cnormSq
  simp only [Fin.sum_univ_three, Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, sub_self, zero_div, zero_mul,
    sub_zero, add_zero, zero_add]
  nlinarith [sq_nonneg ((r 2 1 - r 1 2) * (u 0).re + (r 0 2 - r 2 0) * (u 1).re + (r 1 0 - r 0 1) * (u 2).re),
    sq_nonneg ((r 2 1 - r 1 2) * (u 0).im + (r 0 2 - r 2 0) * (u 1).im + (r 1 0 - r 0 1) * (u 2).im)]

theorem curl_components (φ : ℝ) (L : Space →L[ℝ] Space) :
    ‖curlVec L‖ ^ 2 = (axialRot (-φ) (L (axialRot φ (unitVector 1))) 2 - axialRot (-φ) (L (axialRot φ (unitVector 2))) 1) ^ 2
      + (axialRot (-φ) (L (axialRot φ (unitVector 2))) 0 - axialRot (-φ) (L (axialRot φ (unitVector 0))) 2) ^ 2
      + (axialRot (-φ) (L (axialRot φ (unitVector 0))) 1 - axialRot (-φ) (L (axialRot φ (unitVector 1))) 0) ^ 2 := by
  rw [← RotationInternal.axialRot_norm (-φ) (curlVec L), Internal.MuSmooth.space_norm_sq, Fin.sum_univ_three]
  simp only [← Internal.CurlEnergy.curlVec_axialRot φ L]
  simp [Fin.sum_univ_three, alternatingSymbol]
  ring

theorem compression_self_split (h : HarmonicBounds) (T : Set (ℤ × ℤ))
    (hT : ∀ ι ∈ T, -ι ∉ T) (hHneg : ∀ β ∈ h.harmonics, -β ∈ h.harmonics)
    (A : ℤ × ℤ → Fin 3 → Fin 3 → ℂ) (hA : ∀ β i j, A (-β) i j = starRingEnd ℂ (A β i j))
    (S : ℝ) (hS0 : 0 ≤ S)
    (hsym : ∀ τ φ u, cnormSq (applyMat (symbolMat h.harmonics (antiPart A) τ φ) u) ≤ S ^ 2 * cnormSq u)
    (x f : ℤ × ℤ → Fin 3 → ℂ)
    (hf : ∀ ι, f ι = ∑ β ∈ h.harmonics, applyMat (A β) (x (ι - β)))
    (X : ℤ × ℤ → ℝ)
    (hX : ∀ β ∈ h.harmonics, β ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (A β) u)) ≤ X β * Real.sqrt (cnormSq u))
    (hXneg : ∀ β ∈ h.harmonics, β ≠ 0 → ∀ u,
      Real.sqrt (cnormSq (applyMat (A (-β)) u)) ≤ X β * Real.sqrt (cnormSq u))
    (hx : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * cnormSq (x ι)))
    (e : ℝ) (he : 0 ≤ e) :
    ∃ c : ℤ × ℤ → Fin 3 → ℂ,
      (∀ ι, PieceWeights.inPiece T ι →
        Real.sqrt (cnormSq (f ι - c ι)) ≤ edgeSum h T X (fun κ => Real.sqrt (cnormSq (x κ))) ι) ∧
      Summable (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re) ∧
      |∑' ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re|
        ≤ e * S * pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ))) ^ 2 := by
  classical
  have hnegT : ∀ ι, ι ∈ -T ↔ -ι ∈ T := fun ι => Set.mem_neg
  set H := h.harmonics
  let c : ℤ × ℤ → Fin 3 → ℂ := fun ι =>
    if ι ∈ T then halfPart H T A x ι else if -ι ∈ T then halfPart H (-T) A x ι else 0
  refine ⟨c, ?_, ?_⟩
  · intro ι hι
    by_cases h1 : ι ∈ T
    · have ec : f ι - c ι = ∑ β ∈ H, if ι - β ∈ T then 0 else applyMat (A β) (x (ι - β)) := by
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
      have ec : f ι - c ι = ∑ β ∈ H, if ι - β ∈ -T then 0 else applyMat (A β) (x (ι - β)) := by
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
    have hB := symPart_conj A hA
    have hsplit : ∀ (T' : Set (ℤ × ℤ)) ι, halfPairing H T' A x x ι
        = halfPairing H T' (symPart A) x x ι + halfPairing H T' (antiPart A) x x ι := by
      intro T' ι
      rw [halfPairing_eq, halfPairing_eq, halfPairing_eq, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun β _ => pairPiece_split T' A (symPart A) (antiPart A) (sym_add_anti A) x x β ι
    have symSum : ∀ T' : Set (ℤ × ℤ), Summable (halfSq T' x) → Summable (halfPairing H T' (symPart A) x x) := by
      intro T' hT'
      have ee : halfPairing H T' (symPart A) x x = fun ι => ∑ β ∈ H, pairPiece T' (symPart A) x x β ι :=
        funext (halfPairing_eq H T' (symPart A) x x)
      rw [ee]
      exact summable_sum fun β _ => pairPiece_summable T' (symPart A) x x hT' hT' β
    obtain ⟨sT, bT⟩ := symbol_pairing_bound H T (antiPart A) S hS0 hsym x x hxT hxT
    obtain ⟨sN, bN⟩ := symbol_pairing_bound H (-T) (antiPart A) S hS0 hsym x x hxN hxN
    have rT := tsum_pair_im H hHneg T (symPart A) hB x hxT
    have rN := tsum_pair_im H hHneg (-T) (symPart A) hB x hxN
    have aT : HasSum (halfPairing H T A x x)
        (∑' ι, halfPairing H T (symPart A) x x ι + ∑' ι, halfPairing H T (antiPart A) x x ι) := by
      have hh := ((symSum T hxT).hasSum).add sT.hasSum
      convert hh using 1
      funext ι
      exact hsplit T ι
    have aN : HasSum (halfPairing H (-T) A x x)
        (∑' ι, halfPairing H (-T) (symPart A) x x ι + ∑' ι, halfPairing H (-T) (antiPart A) x x ι) := by
      have hh := ((symSum (-T) hxN).hasSum).add sN.hasSum
      convert hh using 1
      funext ι
      exact hsplit (-T) ι
    have hterm : ∀ ι, (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re
        = (Complex.I * (e : ℂ) * halfPairing H T A x x ι).re
          - (Complex.I * (e : ℂ) * halfPairing H (-T) A x x ι).re := by
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
    have HT := Complex.hasSum_re (aT.mul_left (Complex.I * (e : ℂ)))
    have HN := Complex.hasSum_re (aN.mul_left (Complex.I * (e : ℂ)))
    have Hall := HT.sub HN
    have e1 : (fun ι => (Complex.I * ((PieceWeights.sgn T ι * e : ℝ) : ℂ) * cdot (x ι) (c ι)).re)
        = fun ι => (Complex.I * (e : ℂ) * halfPairing H T A x x ι).re
          - (Complex.I * (e : ℂ) * halfPairing H (-T) A x x ι).re := funext hterm
    rw [e1]
    refine ⟨Hall.summable, ?_⟩
    rw [Hall.tsum_eq]
    have key : ∀ z : ℂ, (Complex.I * (e : ℂ) * z).re = -(e * z.im) := by
      intro z
      simp [Complex.mul_re, Complex.mul_im]
    rw [key, key, Complex.add_im, Complex.add_im, rT, rN, zero_add, zero_add]
    have pT : Real.sqrt (∑' ι, halfSq T x ι) * Real.sqrt (∑' ι, halfSq T x ι) = ∑' ι, halfSq T x ι :=
      Real.mul_self_sqrt (tsum_nonneg (halfSq_nonneg T x))
    have pN : Real.sqrt (∑' ι, halfSq (-T) x ι) * Real.sqrt (∑' ι, halfSq (-T) x ι) = ∑' ι, halfSq (-T) x ι :=
      Real.mul_self_sqrt (tsum_nonneg (halfSq_nonneg (-T) x))
    have px : pieceNorm T (fun κ => Real.sqrt (cnormSq (x κ))) ^ 2
        = ∑' ι, halfSq T x ι + ∑' ι, halfSq (-T) x ι := by
      unfold pieceNorm
      rw [Real.sq_sqrt (tsum_nonneg fun ι => mul_nonneg (ind_nonneg T ι) (sq_nonneg _)),
        ← hxT.tsum_add hxN]
      refine tsum_congr fun ι => ?_
      rw [Real.sq_sqrt (Internal.FieldModes.cnormSq_nonneg _), ind_split T hT x ι]
    have iT := (Complex.abs_im_le_norm (∑' ι, halfPairing H T (antiPart A) x x ι)).trans bT
    have iN := (Complex.abs_im_le_norm (∑' ι, halfPairing H (-T) (antiPart A) x x ι)).trans bN
    rw [mul_assoc S, pT] at iT
    rw [mul_assoc S, pN] at iN
    rw [px]
    calc |-(e * (∑' ι, halfPairing H T (antiPart A) x x ι).im)
          - -(e * (∑' ι, halfPairing H (-T) (antiPart A) x x ι).im)|
        = e * |(∑' ι, halfPairing H (-T) (antiPart A) x x ι).im
            - (∑' ι, halfPairing H T (antiPart A) x x ι).im| := by
          rw [show ∀ a b : ℝ, -(e * a) - -(e * b) = e * (b - a) from fun a b => by ring, abs_mul,
            abs_of_nonneg he]
      _ ≤ e * (|(∑' ι, halfPairing H (-T) (antiPart A) x x ι).im|
            + |(∑' ι, halfPairing H T (antiPart A) x x ι).im|) :=
          mul_le_mul_of_nonneg_left (abs_sub _ _) he
      _ ≤ e * (S * ∑' ι, halfSq (-T) x ι + S * ∑' ι, halfSq T x ι) :=
          mul_le_mul_of_nonneg_left (add_le_add iN iT) he
      _ = e * S * (∑' ι, halfSq T x ι + ∑' ι, halfSq (-T) x ι) := by ring

def stretchCoeff (W : ℝ → Space → Space) (σ : ℝ) (y : Space) : ℤ × ℤ → Fin 3 → Fin 3 → ℂ :=
  matMat (fun i j => ((fderiv ℝ (meanField W) y (unitVector j) i : ℝ) : ℂ)) (fun α => modeGrad α (gradField W) σ y)

section Bound

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
  {w₀ epsSup epsGradSup ratio : ℝ} {v : ℝ → Space → Space}

theorem stretch_compression_of (hPars : ModeSquareSumHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    (hm : IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio) (hW : IsWeakSecondDerivState W HW D)
    (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    ∀ᵐ z ∂slabMeasure,
      ∃ c : ℤ × ℤ → Fin 3 → ℂ,
        (∀ ι, PieceWeights.inPiece (m.epsP β).modes ι →
          Real.sqrt (cnormSq (modeVel ι (stretchRest W v) z.1 z.2 - c ι))
            ≤ edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α z.1 z.2)
              (fun κ => vortAmp (gradField v) κ z.1 z.2) ι) ∧
        Summable (fun ι => (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
          * cdot (vortMode v ι z.1 z.2) (c ι)).re) ∧
        |∑' ι, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
          * cdot (vortMode v ι z.1 z.2) (c ι)).re| ≤ (m.epsP β).wt z.2 * ((1 / 2) * vortSup W z.2)
            * pieceNorm (m.epsP β).modes (fun κ => vortAmp (gradField v) κ z.1 z.2) ^ 2 := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 1
  have hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2) := contDiff_infty.mp hv.smooth 2
  have hWs := hW.smooth
  have hWp := hW.periodic
  have hD0 : 0 ≤ D := by
    have h0 := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h0
    exact le_trans (norm_nonneg _) h0
  have hB : ∀ s x, ‖fderiv ℝ (W s) x‖ ≤ D := fun s x =>
    (hW.decay s x).2.1.trans (div_le_self hD0 (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg x))))
  have h0 : (0 : ℤ × ℤ) ∈ h.harmonics := hm.harmonics_zero
  have hs : ∀ α ∈ h.harmonics.erase 0, -α ∈ h.harmonics.erase 0 := fun α hα =>
    Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.ne_of_mem_erase hα),
      hm.harmonics_neg α (Finset.mem_of_mem_erase hα)⟩
  have hh : ∀ σ y i, W σ y i = (modeVel (0, 0) W σ y i).re + ∑ α ∈ h.harmonics.erase 0, (modeVel α W σ y i).re := by
    intro σ y i
    rw [hm.harmonics_span σ y i]
    exact (Finset.add_sum_erase h.harmonics (fun α => (modeVel α W σ y i).re) h0).symm
  have hp0 : ∀ τ φ, torusPhase 0 τ φ = 1 := fun τ φ => by simp [torusPhase]
  filter_upwards [summable_ae_weak hPars hSP hm hv] with z hsum
  obtain ⟨s1, _, _⟩ := hsum
  have hE := fun τ φ i j => Internal.OnceExpansion.gradW_expansion_once hWs hB hWp (h.harmonics.erase 0) hs hh
    z.1 τ φ z.2 i j
  have hvc : Continuous (fun z : ℝ × Space => vortField v z.1 z.2) := vortField_continuous hv2
  have hf0 : ∀ ι, modeVel ι (stretchRest W v) z.1 z.2 = fun i => ∑ j : Fin 3,
      ((((fderiv ℝ (meanField W) z.2 (unitVector j) i : ℝ)) : ℂ) * vortMode v ι z.1 z.2 j
        + ∑ α ∈ h.harmonics.erase 0, modeGrad α (gradField W) z.1 z.2 (i, j) * vortMode v (ι - α) z.1 z.2 j) := by
    intro ι
    funext i
    simp only [vortMode_eq_modeVel hv1]
    exact Coercive.Internal.MuSmooth.mode_product (h.harmonics.erase 0) W (vortField v) hvc z.1 z.2
      (fun i j => fderiv ℝ (meanField W) z.2 (unitVector j) i)
      (fun α => modeGrad α (gradField W) z.1 z.2) hE ι i
  have hf : ∀ ι, modeVel ι (stretchRest W v) z.1 z.2
      = ∑ b ∈ h.harmonics, applyMat (stretchCoeff W z.1 z.2 b) (vortMode v (ι - b) z.1 z.2) := by
    intro ι
    rw [hf0 ι]
    funext i
    rw [Finset.sum_apply, ← Finset.add_sum_erase h.harmonics _ h0]
    unfold applyMat stretchCoeff
    simp only [matMat, ↓reduceIte, sub_zero, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun α hα => ?_
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_neg (Finset.ne_of_mem_erase hα)]
  have hselfAdj : ∀ b i j, stretchCoeff W z.1 z.2 (-b) i j = starRingEnd ℂ (stretchCoeff W z.1 z.2 b i j) := by
    intro b i j
    unfold stretchCoeff matMat
    by_cases hb : b = 0
    · subst hb
      simp [Complex.conj_ofReal]
    · rw [if_neg (neg_ne_zero.mpr hb), if_neg hb]
      exact Coercive.Internal.MuSmooth.modeGrad_neg b (gradField W) z.1 z.2 (i, j)
  have hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖curlVec (fderiv ℝ (W p.1) (axialRot p.2 z.2))‖) :=
    ⟨h.supVort z.2, by rintro _ ⟨p, rfl⟩; exact hm.supVort_ge p.1 p.2 z.2⟩
  have hle : ∀ τ φ : ℝ, ‖curlVec (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2))‖ ≤ vortSup W z.2 :=
    fun τ φ => le_ciSup hbdd (z.1 + τ, φ)
  have hS0 : 0 ≤ vortSup W z.2 := (norm_nonneg _).trans (hle 0 0)
  have hsym : ∀ τ φ (u : Fin 3 → ℂ), cnormSq (applyMat (symbolMat h.harmonics (antiPart (stretchCoeff W z.1 z.2)) τ φ) u)
      ≤ ((1 / 2) * vortSup W z.2) ^ 2 * cnormSq u := by
    intro τ φ u
    have hM : ∀ i j, symbolMat h.harmonics (stretchCoeff W z.1 z.2) τ φ i j
        = ((axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector j))) i : ℝ) : ℂ) := by
      intro i j
      rw [hE τ φ i j]
      unfold symbolMat stretchCoeff
      rw [← Finset.add_sum_erase h.harmonics _ h0]
      simp only [matMat, ↓reduceIte, hp0, one_mul]
      congr 1
      refine Finset.sum_congr rfl fun α hα => ?_
      rw [if_neg (Finset.ne_of_mem_erase hα)]
      rfl
    have happ : applyMat (symbolMat h.harmonics (antiPart (stretchCoeff W z.1 z.2)) τ φ) u
        = fun i => ∑ j, ((((axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector j))) i
          - axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2) (axialRot φ (unitVector i))) j) / 2 : ℝ)) : ℂ)
            * u j := by
      funext i
      unfold applyMat
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [symbolMat_anti, hM, hM]
      push_cast
      ring
    rw [happ]
    refine (anti_rows_bound (fun i j => axialRot (-φ) (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2)
      (axialRot φ (unitVector j))) i) u).trans ?_
    have hc := curl_components φ (fderiv ℝ (W (z.1 + τ)) (axialRot φ z.2))
    have hsq := pow_le_pow_left₀ (norm_nonneg _) (hle τ φ) 2
    rw [hc] at hsq
    have hu := Internal.FieldModes.cnormSq_nonneg u
    calc _ ≤ vortSup W z.2 ^ 2 / 4 * cnormSq u := mul_le_mul_of_nonneg_right (by linarith) hu
      _ = ((1 / 2) * vortSup W z.2) ^ 2 * cnormSq u := by ring
  have hcneg : ∀ b, cnormSq (modeGrad (-b) (gradField W) z.1 z.2) = cnormSq (modeGrad b (gradField W) z.1 z.2) := by
    intro b
    unfold cnormSq
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [Coercive.Internal.MuSmooth.modeGrad_neg, Complex.norm_conj]
  have hX : ∀ b ∈ h.harmonics, b ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (stretchCoeff W z.1 z.2 b) u))
      ≤ gradAmp (gradField W) b z.1 z.2 * Real.sqrt (cnormSq u) := by
    intro b _ hb u
    have e : stretchCoeff W z.1 z.2 b = fun i j => modeGrad b (gradField W) z.1 z.2 (i, j) := by
      funext i j
      simp only [stretchCoeff, matMat, if_neg hb]
    rw [e]
    exact mat_bound _ _
  have hXneg : ∀ b ∈ h.harmonics, b ≠ 0 → ∀ u, Real.sqrt (cnormSq (applyMat (stretchCoeff W z.1 z.2 (-b)) u))
      ≤ gradAmp (gradField W) b z.1 z.2 * Real.sqrt (cnormSq u) := by
    intro b _ hb u
    have e : stretchCoeff W z.1 z.2 (-b) = fun i j => modeGrad (-b) (gradField W) z.1 z.2 (i, j) := by
      funext i j
      simp only [stretchCoeff, matMat, if_neg (neg_ne_zero.mpr hb)]
    rw [e]
    refine (mat_bound _ _).trans_eq ?_
    unfold gradAmp
    rw [hcneg]
  obtain ⟨c', h1, h2, h3⟩ := compression_self_split h (m.epsP β).modes (piece_disjoint_weak hm hv β)
    hm.harmonics_neg (stretchCoeff W z.1 z.2) hselfAdj ((1 / 2) * vortSup W z.2) (by positivity) hsym
    (fun ι => vortMode v ι z.1 z.2) (fun ι => modeVel ι (stretchRest W v) z.1 z.2) hf
    (fun α => gradAmp (gradField W) α z.1 z.2) hX hXneg (ind_summable_weak _ _ s1) ((m.epsP β).wt z.2)
    (hm.eps_wt_nonneg β z.2)
  exact ⟨c', h1, h2, h3⟩

end Bound

end Internal.PieceEpsStretch

end CoerciveWeak

end Breakdown

import Breakdown.Cert.CoercivePieceAbsorbEdge

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceAbsorb

private theorem modeAverage_neg {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage (-ι) f b = (starRingEnd ℂ) (modeAverage ι f b) := by
  unfold modeAverage
  rw [map_mul, ← intervalIntegral.intervalIntegral_conj]
  congr 1
  · simp only [map_div₀, map_one, map_mul, Complex.conj_ofReal, map_ofNat]
  · refine intervalIntegral.integral_congr fun τ _ => ?_
    rw [← intervalIntegral.intervalIntegral_conj]
    refine intervalIntegral.integral_congr fun φ _ => ?_
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
    congr 2
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    push_cast
    ring

private theorem gradAmp_neg (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    gradAmp G (-ι) σ y = gradAmp G ι σ y := by
  simp only [gradAmp, cnormSq, modeGrad, modeAverage_neg, Complex.norm_conj]

private theorem frameFreq_neg (P a : ℝ) (ι : ℤ × ℤ) : PieceWeights.frameFreq P a (-ι) = -PieceWeights.frameFreq P a ι := by
  unfold PieceWeights.frameFreq
  simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
  ring

private theorem sum_neg_eq (s : Finset (ℤ × ℤ)) (hneg : ∀ α ∈ s, -α ∈ s) (F : ℤ × ℤ → ℝ) :
    ∑ α ∈ s, F (-α) = ∑ α ∈ s, F α :=
  Finset.sum_nbij' (fun α => -α) (fun α => -α) (fun a ha => hneg a ha) (fun a ha => hneg a ha)
    (fun a _ => neg_neg a) (fun a _ => neg_neg a) (fun _ _ => rfl)

private theorem abs_ind_mul_le (p : Prop) (z : ℝ) : |ModeWeights.ind p * z| ≤ |z| := by
  rw [abs_mul, abs_of_nonneg (ind_nonneg p)]
  exact mul_le_of_le_one_left (abs_nonneg z) (ind_le_one p)

open Classical in
private theorem ind_inPiece_le (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    ModeWeights.ind (PieceWeights.inPiece T ι) ≤ (if ι ∈ T then 1 else 0) + (if -ι ∈ T then 1 else 0) := by
  unfold ModeWeights.ind PieceWeights.inPiece
  by_cases h1 : ι ∈ T <;> by_cases h2 : -ι ∈ T <;> simp [h1, h2]


open Classical in
private theorem split_sum_ite (s : Finset (ℤ × ℤ)) (B : ℤ × ℤ → ℝ) (c : ℤ × ℤ → Prop) :
    ∑ α ∈ s, B α = ∑ α ∈ s, (if c α then 0 else B α) + ∑ α ∈ s, (if c α then B α else 0) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun α _ => by split_ifs <;> ring

open Classical in
private theorem sum_ite_le (s : Finset (ℤ × ℤ)) (Y B : ℤ × ℤ → ℝ) (hYB : ∀ α ∈ s, Y α ≤ B α) (c : ℤ × ℤ → Prop) :
    ∑ α ∈ s, (if c α then Y α else 0) ≤ ∑ α ∈ s, (if c α then B α else 0) :=
  Finset.sum_le_sum fun α hα => by
    split_ifs
    · exact hYB α hα
    · exact le_rfl

open Classical in
private theorem coef_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (hT : ∀ ι, ι ∈ T → -ι ∉ T)
    (Y : ℤ × ℤ → ℝ) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (hY0 : ∀ α ∈ h.harmonics, 0 ≤ Y α) (hYB : ∀ α ∈ h.harmonics, Y α ≤ B α y)
    (hYs : ∀ α ∈ h.harmonics, Y (-α) = Y α) (hneg : ∀ α ∈ h.harmonics, -α ∈ h.harmonics) (κ : ℤ × ℤ) :
    ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α
      ≤ ModeWeights.ind (PieceWeights.inPiece T κ) * (∑ α ∈ h.harmonics, B α y - PieceWeights.inward h T B κ y)
        + PieceWeights.outward h T B κ y := by
  have e1 : ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α
      ≤ ∑ α ∈ h.harmonics, (if κ + α ∈ T then Y α else 0)
        + ∑ α ∈ h.harmonics, (if -κ - α ∈ T then Y α else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun α hα => ?_
    have hi := ind_inPiece_le T (κ + α)
    rw [neg_add'] at hi
    have hy := hY0 α hα
    split_ifs at hi ⊢ <;> nlinarith
  have m1 : ∑ α ∈ h.harmonics, (if κ + α ∈ T then Y α else 0)
      = ∑ α ∈ h.harmonics, (if κ - α ∈ T then Y α else 0) := by
    rw [← sum_neg_eq h.harmonics hneg]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [← sub_eq_add_neg, hYs α hα]
  have m2 : ∑ α ∈ h.harmonics, (if -κ - α ∈ T then Y α else 0)
      = ∑ α ∈ h.harmonics, (if -κ + α ∈ T then Y α else 0) := by
    rw [← sum_neg_eq h.harmonics hneg]
    refine Finset.sum_congr rfl fun α hα => ?_
    rw [sub_neg_eq_add, hYs α hα]
  have l1 := sum_ite_le h.harmonics Y (fun α => B α y) hYB (fun α => κ + α ∈ T)
  have l2 := sum_ite_le h.harmonics Y (fun α => B α y) hYB (fun α => κ - α ∈ T)
  have l3 := sum_ite_le h.harmonics Y (fun α => B α y) hYB (fun α => -κ - α ∈ T)
  have l4 := sum_ite_le h.harmonics Y (fun α => B α y) hYB (fun α => -κ + α ∈ T)
  have s1 := split_sum_ite h.harmonics (fun α => B α y) (fun α => κ - α ∈ T)
  have s2 := split_sum_ite h.harmonics (fun α => B α y) (fun α => -κ - α ∈ T)
  beta_reduce at l1 l2 l3 l4 s1 s2
  unfold PieceWeights.inward PieceWeights.outward PieceWeights.backSum PieceWeights.fwdSum
  by_cases h1 : κ ∈ T
  · have h2 := hT κ h1
    have hi : ModeWeights.ind (PieceWeights.inPiece T κ) = 1 := by
      unfold ModeWeights.ind PieceWeights.inPiece
      simp [h1]
    simp only [h1, h2, ↓reduceIte, hi, one_mul, zero_add]
    linarith
  · by_cases h2 : -κ ∈ T
    · have hi : ModeWeights.ind (PieceWeights.inPiece T κ) = 1 := by
        unfold ModeWeights.ind PieceWeights.inPiece
        simp [h2]
      simp only [h1, h2, ↓reduceIte, hi, one_mul, add_zero]
      linarith
    · have hi : ModeWeights.ind (PieceWeights.inPiece T κ) = 0 := by
        unfold ModeWeights.ind PieceWeights.inPiece
        simp [h1, h2]
      simp only [h1, h2, ↓reduceIte, hi, zero_mul, zero_add]
      linarith

open Classical in
private theorem pressure_le (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (hT : ∀ ι, ι ∈ T → -ι ∉ T)
    (Y : ℤ × ℤ → ℝ) (B : ℤ × ℤ → Space → ℝ) (y : Space)
    (hY0 : ∀ α ∈ h.harmonics, 0 ≤ Y α) (hYB : ∀ α ∈ h.harmonics, Y α ≤ B α y)
    (hYs : ∀ α ∈ h.harmonics, Y (-α) = Y α) (hneg : ∀ α ∈ h.harmonics, -α ∈ h.harmonics)
    (x : ℤ × ℤ → ℝ) (hx : Summable fun ι => x ι ^ 2) :
    Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * (∑ α ∈ h.harmonics, Y α * x (ι - α)) ^ 2) ∧
    Summable (fun κ => (ModeWeights.ind (PieceWeights.inPiece T κ) * (∑ α ∈ h.harmonics, B α y)
          * (∑ α ∈ h.harmonics, B α y - PieceWeights.inward h T B κ y)
          + (∑ α ∈ h.harmonics, B α y) * PieceWeights.outward h T B κ y) * x κ ^ 2) ∧
    ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * (∑ α ∈ h.harmonics, Y α * x (ι - α)) ^ 2
      ≤ ∑' κ, (ModeWeights.ind (PieceWeights.inPiece T κ) * (∑ α ∈ h.harmonics, B α y)
          * (∑ α ∈ h.harmonics, B α y - PieceWeights.inward h T B κ y)
          + (∑ α ∈ h.harmonics, B α y) * PieceWeights.outward h T B κ y) * x κ ^ 2 := by
  set hs := ∑ α ∈ h.harmonics, B α y with hhs
  have hYle : ∑ α ∈ h.harmonics, Y α ≤ hs := Finset.sum_le_sum hYB
  have hY0s : 0 ≤ ∑ α ∈ h.harmonics, Y α := Finset.sum_nonneg hY0
  have hs0 : 0 ≤ hs := hY0s.trans hYle
  have hshift : ∀ α : ℤ × ℤ, Summable fun ι => x (ι - α) ^ 2 := fun α =>
    (Equiv.subRight α).summable_iff.2 hx
  have hpt : ∀ ι, ModeWeights.ind (PieceWeights.inPiece T ι) * (∑ α ∈ h.harmonics, Y α * x (ι - α)) ^ 2
      ≤ ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2 := by
    intro ι
    have cs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul h.harmonics (r := fun α => Y α * x (ι - α)) (f := Y)
      (g := fun α => Y α * x (ι - α) ^ 2) hY0 (fun α hα => mul_nonneg (hY0 α hα) (sq_nonneg _))
      (fun α _ => le_of_eq (by ring))
    have hg0 : 0 ≤ ∑ α ∈ h.harmonics, Y α * x (ι - α) ^ 2 :=
      Finset.sum_nonneg fun α hα => mul_nonneg (hY0 α hα) (sq_nonneg _)
    have h2 : (∑ α ∈ h.harmonics, Y α * x (ι - α)) ^ 2 ≤ hs * ∑ α ∈ h.harmonics, Y α * x (ι - α) ^ 2 :=
      cs.trans (mul_le_mul_of_nonneg_right hYle hg0)
    calc _ ≤ ModeWeights.ind (PieceWeights.inPiece T ι) * (hs * ∑ α ∈ h.harmonics, Y α * x (ι - α) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (ind_nonneg _)
      _ = _ := by
          rw [Finset.mul_sum, Finset.mul_sum]
          exact Finset.sum_congr rfl fun α _ => by ring
  have hGs : ∀ α, Summable fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2 := by
    intro α
    refine (summable_bdd_mul (f := fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α)
      (p := fun ι => x (ι - α)) (K := |hs * Y α|) (fun ι => ?_) (hshift α)).congr fun ι => rfl
    rw [mul_assoc]
    exact abs_ind_mul_le _ _
  have hFs : Summable fun ι => ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2 :=
    summable_sum fun α _ => hGs α
  have hLs : Summable (fun ι => ModeWeights.ind (PieceWeights.inPiece T ι) * (∑ α ∈ h.harmonics, Y α * x (ι - α)) ^ 2) :=
    Summable.of_nonneg_of_le (fun ι => mul_nonneg (ind_nonneg _) (sq_nonneg _)) hpt hFs
  have hHs : ∀ α, Summable fun κ => hs * (ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α) * x κ ^ 2 := by
    intro α
    refine summable_bdd_mul (K := |hs * Y α|) (fun κ => ?_) hx
    rw [mul_comm (ModeWeights.ind _) (Y α), ← mul_assoc, mul_comm (hs * Y α)]
    exact abs_ind_mul_le _ _
  have hre : ∀ α, ∑' ι, ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2
      = ∑' κ, hs * (ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α) * x κ ^ 2 := by
    intro α
    rw [← (Equiv.addRight α).tsum_eq]
    refine tsum_congr fun κ => ?_
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    ring
  have hmid : ∑' ι, ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2
      = ∑' κ, hs * (∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α) * x κ ^ 2 := by
    rw [Summable.tsum_finsetSum fun α _ => hGs α]
    simp only [hre]
    rw [← Summable.tsum_finsetSum fun α _ => hHs α]
    refine tsum_congr fun κ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  have hK : ∀ κ, |ModeWeights.ind (PieceWeights.inPiece T κ) * hs * (hs - PieceWeights.inward h T B κ y)
      + hs * PieceWeights.outward h T B κ y|
      ≤ |hs| * (|hs| + ∑ α ∈ h.harmonics, |B α y|) + |hs| * (2 * ∑ α ∈ h.harmonics, |B α y|) := by
    intro κ
    have i1 := abs_inward_le h T B κ y
    have i2 := abs_outward_le h T B κ y
    have i3 := abs_ind_mul_le (PieceWeights.inPiece T κ) (hs * (hs - PieceWeights.inward h T B κ y))
    calc _ ≤ |ModeWeights.ind (PieceWeights.inPiece T κ) * hs * (hs - PieceWeights.inward h T B κ y)|
          + |hs * PieceWeights.outward h T B κ y| := abs_add_le _ _
      _ ≤ |hs * (hs - PieceWeights.inward h T B κ y)| + |hs * PieceWeights.outward h T B κ y| := by
          rw [mul_assoc]
          exact add_le_add i3 le_rfl
      _ ≤ _ := by
          rw [abs_mul, abs_mul]
          refine add_le_add (mul_le_mul_of_nonneg_left ((abs_sub _ _).trans (add_le_add le_rfl i1)) (abs_nonneg _))
            (mul_le_mul_of_nonneg_left i2 (abs_nonneg _))
  have hRs := summable_bdd_mul (fun κ => hK κ) hx
  refine ⟨hLs, hRs, ?_⟩
  calc _ ≤ ∑' ι, ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T ι) * hs * Y α * x (ι - α) ^ 2 :=
        hLs.tsum_le_tsum hpt hFs
    _ = _ := hmid
    _ ≤ _ := by
        refine Summable.tsum_le_tsum (fun κ => ?_) ((summable_sum (s := h.harmonics) fun α _ => hHs α).congr fun κ => ?_) hRs
        · have hc := coef_le h T hT Y B y hY0 hYB hYs hneg κ
          have : hs * ∑ α ∈ h.harmonics, ModeWeights.ind (PieceWeights.inPiece T (κ + α)) * Y α
              ≤ ModeWeights.ind (PieceWeights.inPiece T κ) * hs * (hs - PieceWeights.inward h T B κ y)
                + hs * PieceWeights.outward h T B κ y := by
            nlinarith [mul_le_mul_of_nonneg_left hc hs0]
          exact mul_le_mul_of_nonneg_right this (sq_nonneg _)
        · rw [Finset.mul_sum, Finset.sum_mul]


section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

open Classical in
theorem mu_piece_le {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (β : Fin nM) (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => pieceMuDensity m P h β ι y (gradAmp G ι σ y) (velAmp v ι σ y)
        - pieceMuPos m P v β ι σ y) ∧
      Summable (fun ι => pieceMuRestMode m h W v G β ι σ y) ∧
      ∑' ι, (pieceMuDensity m P h β ι y (gradAmp G ι σ y) (velAmp v ι σ y) - pieceMuPos m P v β ι σ y)
        ≤ ∑' ι, pieceMuRestMode m h W v G β ι σ y + pieceMuBlock m W v G β σ y := by
  obtain ⟨-, -, hx1, -, hx0⟩ := hg
  have ha : 0 ≤ (m.muP β).wt y := hm.mu_wt_nonneg β y
  have ha' : 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := norm_nonneg _
  obtain ⟨hsh, ht4⟩ := hm.mu_free_pos β y
  have heta := hm.mu_eta_pos β
  have hT : ∀ ι, ι ∈ (m.muP β).modes → -ι ∉ (m.muP β).modes := by
    obtain ⟨Ω, hΩ, hΩT⟩ := hm.mu_oneSided β
    intro ι h1 h2
    have e1 := hΩT ι h1
    have e2 := hΩT (-ι) h2
    rw [frameFreq_neg] at e2
    linarith
  have hX0 : ∀ α ∈ h.harmonics, 0 ≤ velAmp W α σ y := fun _ _ => Real.sqrt_nonneg _
  have hXB : ∀ α ∈ h.harmonics, velAmp W α σ y ≤ h.ampW α y := fun α hα => hm.ampW_ge α hα σ y
  have hY0 : ∀ α ∈ h.harmonics, 0 ≤ gradAmp (gradField W) α σ y := fun _ _ => Real.sqrt_nonneg _
  have hYB : ∀ α ∈ h.harmonics, gradAmp (gradField W) α σ y ≤ h.ampGradW α y :=
    fun α hα => hm.ampGradW_ge α hα σ y
  have hYs : ∀ α ∈ h.harmonics, gradAmp (gradField W) (-α) σ y = gradAmp (gradField W) α σ y :=
    fun α _ => gradAmp_neg _ α σ y
  have hA0 : 0 ≤ (m.muP β).t4 y * (m.muP β).wt y / 2 := div_nonneg (mul_nonneg ht4.le ha) two_pos.le
  have hB0 : 0 ≤ (m.muP β).wt y / (2 * (m.muP β).t4 y) := div_nonneg ha (by positivity)
  have hcE : (m.muP β).wt y ^ 2 ≤ 4 * ((m.muP β).t4 y * (m.muP β).wt y / 2) * ((m.muP β).wt y / (2 * (m.muP β).t4 y)) :=
    le_of_eq (by field_simp; ring)
  obtain ⟨sE, iE⟩ := edge_le h (m.muP β).modes (fun α => velAmp W α σ y) h.ampW y hX0 hXB
    (fun ι => velAmp v ι σ y) (fun ι => gradAmp G ι σ y) hx0 hx1 hA0 hB0 hcE
  obtain ⟨sL, sR, iP⟩ := pressure_le h (m.muP β).modes hT (fun α => gradAmp (gradField W) α σ y) h.ampGradW y
    hY0 hYB hYs hm.harmonics_neg (fun ι => velAmp v ι σ y) hx0
  beta_reduce at sE iE sL sR iP
  have hD : ∀ ι, pieceMuDensity m P h β ι y (gradAmp G ι σ y) (velAmp v ι σ y) - pieceMuPos m P v β ι σ y
      = -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * ((m.muP β).t4 y * (m.muP β).wt y / 2)
            * PieceWeights.inward h (m.muP β).modes h.ampW ι y * velAmp v ι σ y ^ 2
          + (m.muP β).wt y / (2 * (m.muP β).t4 y) * PieceWeights.outward h (m.muP β).modes h.ampW ι y
            * gradAmp G ι σ y ^ 2)
        + -((ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (∑ α ∈ h.harmonics, h.ampGradW α y)
              * (∑ α ∈ h.harmonics, h.ampGradW α y - PieceWeights.inward h (m.muP β).modes h.ampGradW ι y)
              + (∑ α ∈ h.harmonics, h.ampGradW α y) * PieceWeights.outward h (m.muP β).modes h.ampGradW ι y)
            * velAmp v ι σ y ^ 2) / (2 * (m.muP β).eta)
        + -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2) * velAmp v ι σ y ^ 2)
        + -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
              * (ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y)
              * gradAmp G ι σ y ^ 2
            + ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
              * (((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
                / (4 * (m.muP β).share y) + (m.muP β).wt y * |(m.muP β).frame|) * velAmp v ι σ y ^ 2) := by
    intro ι
    unfold pieceMuDensity pieceMuPos PieceWeights.harmonicSum
    ring
  have hR : ∀ ι, pieceMuRestMode m h W v G β ι σ y
      = -((m.muP β).wt y * velAmp v ι σ y
          * edgeSum h (m.muP β).modes (fun α => velAmp W α σ y) (fun κ => gradAmp G κ σ y) ι)
        + -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * (∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / (2 * (m.muP β).eta)
        + -(ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
            * ((1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2) * velAmp v ι σ y ^ 2) := by
    intro ι
    unfold pieceMuRestMode
    ring
  have kW := abs_inward_le h (m.muP β).modes h.ampW
  have kW' := abs_outward_le h (m.muP β).modes h.ampW
  have s1 : Summable fun ι => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((m.muP β).t4 y * (m.muP β).wt y / 2) * PieceWeights.inward h (m.muP β).modes h.ampW ι y
      * velAmp v ι σ y ^ 2 := by
    refine summable_bdd_mul (K := |(m.muP β).t4 y * (m.muP β).wt y / 2| * ∑ α ∈ h.harmonics, |h.ampW α y|)
      (fun ι => ?_) hx0
    rw [mul_assoc, abs_mul, abs_mul]
    calc _ ≤ 1 * (|(m.muP β).t4 y * (m.muP β).wt y / 2| * |PieceWeights.inward h (m.muP β).modes h.ampW ι y|) :=
          mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg (ind_nonneg _)]; exact ind_le_one _) (by positivity)
      _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_left (kW ι y) (abs_nonneg _)
  have s2 : Summable fun ι => (m.muP β).wt y / (2 * (m.muP β).t4 y)
      * PieceWeights.outward h (m.muP β).modes h.ampW ι y * gradAmp G ι σ y ^ 2 := by
    refine summable_bdd_mul (K := |(m.muP β).wt y / (2 * (m.muP β).t4 y)| * (2 * ∑ α ∈ h.harmonics, |h.ampW α y|))
      (fun ι => ?_) hx1
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (kW' ι y) (abs_nonneg _)
  have s3 := (sR.neg).div_const (2 * (m.muP β).eta)
  have s4 : Summable fun ι => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * ((1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2) * velAmp v ι σ y ^ 2 :=
    summable_bdd_mul (K := |(1 / 2) * (m.muP β).eta * (m.muP β).wt y ^ 2|) (fun ι => abs_ind_mul_le _ _) hx0
  have s5 : Summable fun ι => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y)
      * gradAmp G ι σ y ^ 2 :=
    summable_bdd_mul (fun ι => abs_ind_mul_le _ _) hx1
  have s6 : Summable fun ι => ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
        / (4 * (m.muP β).share y) + (m.muP β).wt y * |(m.muP β).frame|) * velAmp v ι σ y ^ 2 :=
    summable_bdd_mul (fun ι => abs_ind_mul_le _ _) hx0
  have s7 := (sL.neg).div_const (2 * (m.muP β).eta)
  have sQ := (((s1.add s2).neg.add s3).add s4.neg).add (s5.add s6).neg
  have sRr := ((sE.neg).add s7).add s4.neg
  refine ⟨sQ.congr fun ι => (hD ι).symm, sRr.congr fun ι => (hR ι).symm, ?_⟩
  rw [tsum_congr hD, tsum_congr hR]
  have HL := ((((s1.hasSum.add s2.hasSum).neg.add (sR.hasSum.neg.div_const (2 * (m.muP β).eta))).add
    s4.hasSum.neg).add (s5.hasSum.add s6.hasSum).neg)
  have HR := ((sE.hasSum.neg.add (sL.hasSum.neg.div_const (2 * (m.muP β).eta))).add s4.hasSum.neg)
  have hFS : frameSpeedSup W (m.muP β).frame y ≤ (m.muP β).speed y :=
    ciSup_le fun p => hm.muSpeed_ge β p.1 p.2 y
  have hS1 : 0 ≤ pieceNorm (m.muP β).modes (fun κ => gradAmp G κ σ y) := Real.sqrt_nonneg _
  have hS0 : 0 ≤ pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y) := Real.sqrt_nonneg _
  have hAb : 0 ≤ ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y :=
    mul_nonneg (ind_nonneg _) hsh.le
  have hBb : 0 ≤ ((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
      / (4 * (m.muP β).share y) := div_nonneg (sq_nonneg _) (by linarith)
  have hcb : ((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
      ≤ 4 * (ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y)
        * (((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
          / (4 * (m.muP β).share y)) := by
    by_cases hp : 0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y
    · have hi : ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) = 1 := by
        unfold ModeWeights.ind
        simp [hp]
      rw [hi]
      exact le_of_eq (by field_simp)
    · have a0 : (m.muP β).wt y = 0 := by linarith [not_lt.1 hp]
      have a0' : PieceWeights.wtGrad (m.muP β).wt y = 0 := by linarith [not_lt.1 hp]
      rw [a0, a0']
      simp
  have iB := block_le (m.muP β).modes (fun κ => gradAmp G κ σ y) (fun κ => velAmp v κ σ y) hx1 hx0 hAb hBb hcb
  have hsq := pieceNorm_sq (m.muP β).modes (fun κ => velAmp v κ σ y) hx0
  beta_reduce at iB hsq
  have hb1 : ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y)
      * gradAmp G ι σ y ^ 2
      = (ModeWeights.ind (0 < (m.muP β).wt y + PieceWeights.wtGrad (m.muP β).wt y) * (m.muP β).share y)
        * ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * gradAmp G ι σ y ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ι => by ring
  have hb2 : ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
      * (((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
        / (4 * (m.muP β).share y) + (m.muP β).wt y * |(m.muP β).frame|) * velAmp v ι σ y ^ 2
      = (((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y) ^ 2
        / (4 * (m.muP β).share y) + (m.muP β).wt y * |(m.muP β).frame|)
        * ∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * velAmp v ι σ y ^ 2 := by
    rw [← tsum_mul_left]
    exact tsum_congr fun ι => by ring
  have hmono : ((m.muP β).wt y * frameSpeedSup W (m.muP β).frame y + PieceWeights.wtGrad (m.muP β).wt y)
      * pieceNorm (m.muP β).modes (fun κ => gradAmp G κ σ y) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)
      ≤ ((m.muP β).wt y * (m.muP β).speed y + PieceWeights.wtGrad (m.muP β).wt y)
      * pieceNorm (m.muP β).modes (fun κ => gradAmp G κ σ y) * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y) := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hS1) hS0
    linarith [mul_le_mul_of_nonneg_left hFS ha]
  have hPdiv : -(∑' ι, (ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι) * (∑ α ∈ h.harmonics, h.ampGradW α y)
          * (∑ α ∈ h.harmonics, h.ampGradW α y - PieceWeights.inward h (m.muP β).modes h.ampGradW ι y)
          + (∑ α ∈ h.harmonics, h.ampGradW α y) * PieceWeights.outward h (m.muP β).modes h.ampGradW ι y)
          * velAmp v ι σ y ^ 2) / (2 * (m.muP β).eta)
      ≤ -(∑' ι, ModeWeights.ind (PieceWeights.inPiece (m.muP β).modes ι)
          * (∑ α ∈ h.harmonics, gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y) ^ 2) / (2 * (m.muP β).eta) := by
    rw [neg_div, neg_div]
    exact neg_le_neg (div_le_div_of_nonneg_right iP (mul_pos two_pos heta).le)
  have hblk : pieceMuBlock m W v G β σ y = -(((m.muP β).wt y * frameSpeedSup W (m.muP β).frame y
      + PieceWeights.wtGrad (m.muP β).wt y) * pieceNorm (m.muP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y))
      - (m.muP β).wt y * |(m.muP β).frame| * pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y) ^ 2 := rfl
  have hsq' := congrArg (fun t => (m.muP β).wt y * |(m.muP β).frame| * t) hsq
  beta_reduce at hsq'
  rw [HL.tsum_eq, HR.tsum_eq, hblk]
  linarith [iE, hPdiv, iB, hb1, hb2, hmono, hsq']

end Pieces

end Internal.PieceAbsorb

end Coercive

end Breakdown

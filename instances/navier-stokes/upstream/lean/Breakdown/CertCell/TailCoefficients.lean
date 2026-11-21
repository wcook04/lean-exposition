import Breakdown.CertCell.TailStatements

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open PieceWeights

private theorem ind_eq_bit {q : Prop} {b : Bool} (hq : q ↔ b = true) : ModeWeights.ind q = bit b := by
  unfold ModeWeights.ind bit
  by_cases hb : b = true
  · rw [if_pos (hq.2 hb), if_pos hb]
  · rw [if_neg (fun h' => hb (hq.1 h')), if_neg hb]

private theorem ind_nonneg (q : Prop) : 0 ≤ ModeWeights.ind q := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

private theorem bit_nonneg (b : Bool) : 0 ≤ bit b := by
  unfold bit
  split_ifs <;> norm_num

private theorem bit_mul_le {b : Bool} {x y : ℝ} (hxy : b = true → x ≤ y) : bit b * x ≤ bit b * y := by
  cases b
  · simp [bit]
  · simpa [bit] using hxy rfl

private theorem ampOf_zero (h : HarmonicBounds) : ampOf h 0 = h.ampW := rfl

private theorem ampOf_one (h : HarmonicBounds) : ampOf h 1 = h.ampGradW := rfl

private theorem ampOf_two (h : HarmonicBounds) : ampOf h 2 = h.ampVort := rfl

private theorem ampOf_three (h : HarmonicBounds) : ampOf h 3 = h.ampGradVort := rfl

section

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
  {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
  {w₀ epsSup epsGradSup ratio : ℝ} {B : SetPieceBounds C nE nM} {mm : ℕ} {I : Set (ℤ × ℤ)}
  {Z : Set (ℝ × ℝ)} {ι : ℤ × ℤ} {p : ℝ × ℝ}

private theorem harmonicSum_nonneg (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (y : Space) : 0 ≤ harmonicSum h y := by
  unfold harmonicSum
  apply Finset.sum_nonneg
  intro β hβ
  exact (Real.sqrt_nonneg _).trans (hA.ampGradW_ge β hβ 0 y)

private theorem inward_gradW_nonneg (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (T : Set (ℤ × ℤ)) (ξ : ℤ × ℤ) (y : Space) : 0 ≤ inward h T h.ampGradW ξ y := by
  have hb : ∀ ζ, 0 ≤ backSum h T h.ampGradW ζ y := by
    intro ζ
    unfold backSum
    apply Finset.sum_nonneg
    intro β hβ
    split_ifs
    · exact le_rfl
    · exact (Real.sqrt_nonneg _).trans (hA.ampGradW_ge β hβ 0 y)
  unfold inward
  split_ifs
  · exact hb _
  · exact hb _
  · exact le_rfl

private theorem shareHat_le (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hB : B.IsValidOn m P h mm I Z) (hι : ι ∈ I) (hp : p ∈ Z) :
    m.shareHat h (labelHarmonic mm ι) (planePoint p) ≤ B.shareHatHigh m p := by
  unfold PieceWeights.shareHat SetPieceBounds.shareHatHigh
  refine Finset.sum_le_sum fun β _ => ?_
  obtain ⟨-, h2, -, -, -, -, -, hs⟩ := hA.eps_free_pos β (planePoint p)
  have ho := hB.eps_outward ι hι p hp β 0
  rw [ampOf_zero] at ho
  rw [ind_eq_bit (hB.eps_member ι hι β)]
  have hi := ind_nonneg (0 < (m.epsP β).wt (planePoint p))
  gcongr

private theorem curl_le (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hB : B.IsValidOn m P h mm I Z) (hι : ι ∈ I) (hp : p ∈ Z) :
    B.curlLow m h p ≤ m.coefA P h (labelHarmonic mm ι) (planePoint p)
      - m.convZ (m.classOf (labelHarmonic mm ι)) (planePoint p) := by
  have he : ∀ β, ModeWeights.ind (inPiece (m.epsP β).modes (labelHarmonic mm ι)) = bit (B.epsMember β) :=
    fun β => ind_eq_bit (hB.eps_member ι hι β)
  rw [hB.class_eq ι hι]
  unfold SetPieceBounds.curlLow PieceWeights.coefA
  simp only [he]
  apply sub_le_sub_right
  apply sub_le_sub
  · apply add_le_add le_rfl
    refine Finset.sum_le_sum fun β _ => bit_mul_le fun hb => ?_
    obtain ⟨h1, h2, hl, h0, ht1, ht2, ht3, hs⟩ := hA.eps_free_pos β (planePoint p)
    have hw := hA.eps_wt_nonneg β (planePoint p)
    have hf := hB.eps_freq ι hι β hb
    have i0 := hB.eps_inward ι hι p hp β 0
    have i1 := hB.eps_inward ι hι p hp β 1
    have i2 := hB.eps_inward ι hι p hp β 2
    have i3 := hB.eps_inward ι hι p hp β 3
    rw [ampOf_zero] at i0
    rw [ampOf_one] at i1
    rw [ampOf_two] at i2
    rw [ampOf_three] at i3
    gcongr
  · refine Finset.sum_le_sum fun β _ => ?_
    obtain ⟨-, -, -, -, ht1, -, -, -⟩ := hA.eps_free_pos β (planePoint p)
    have hw := hA.eps_wt_nonneg β (planePoint p)
    have o1 := hB.eps_outward ι hι p hp β 1
    rw [ampOf_one] at o1
    gcongr

private theorem grad_le (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hB : B.IsValidOn m P h mm I Z) (hι : ι ∈ I) (hp : p ∈ Z) :
    B.gradLow m h w p ≤ m.coefAA h w (labelHarmonic mm ι) (planePoint p) := by
  have he : ∀ β, ModeWeights.ind (inPiece (m.epsP β).modes (labelHarmonic mm ι)) = bit (B.epsMember β) :=
    fun β => ind_eq_bit (hB.eps_member ι hι β)
  have hu : ∀ β, ModeWeights.ind (inPiece (m.muP β).modes (labelHarmonic mm ι)) = bit (B.muMember β) :=
    fun β => ind_eq_bit (hB.mu_member ι hι β)
  unfold SetPieceBounds.gradLow PieceWeights.coefAA
  rw [hB.class_eq ι hι]
  simp only [he, hu]
  apply sub_le_sub
  · apply sub_le_sub_left
    refine Finset.sum_le_sum fun β _ => ?_
    obtain ⟨-, -, -, -, -, -, ht3, -⟩ := hA.eps_free_pos β (planePoint p)
    have hw := hA.eps_wt_nonneg β (planePoint p)
    have o2 := hB.eps_outward ι hι p hp β 2
    rw [ampOf_two] at o2
    gcongr
  · refine Finset.sum_le_sum fun β _ => ?_
    obtain ⟨-, ht4⟩ := hA.mu_free_pos β (planePoint p)
    have hw := hA.mu_wt_nonneg β (planePoint p)
    have o0 := hB.mu_outward ι hι p hp β 0
    rw [ampOf_zero] at o0
    gcongr

private theorem vel_le (hA : CoerciveWeak.IsAdmissibleWeak m P h w W HW w₀ epsSup epsGradSup ratio)
    (hB : B.IsValidOn m P h mm I Z) (hι : ι ∈ I) (hp : p ∈ Z) :
    B.velLow m h p ≤ m.coefB P h (labelHarmonic mm ι) (planePoint p) := by
  have he : ∀ β, ModeWeights.ind (inPiece (m.epsP β).modes (labelHarmonic mm ι)) = bit (B.epsMember β) :=
    fun β => ind_eq_bit (hB.eps_member ι hι β)
  have hu : ∀ β, ModeWeights.ind (inPiece (m.muP β).modes (labelHarmonic mm ι)) = bit (B.muMember β) :=
    fun β => ind_eq_bit (hB.mu_member ι hι β)
  have hs := harmonicSum_nonneg hA (planePoint p)
  unfold SetPieceBounds.velLow PieceWeights.coefB
  rw [hB.class_eq ι hι]
  simp only [he, hu]
  apply sub_le_sub
  · apply add_le_add
    · apply sub_le_sub_left
      refine Finset.sum_le_sum fun β _ => ?_
      obtain ⟨-, -, -, -, -, ht2, -, -⟩ := hA.eps_free_pos β (planePoint p)
      have hw := hA.eps_wt_nonneg β (planePoint p)
      have o3 := hB.eps_outward ι hι p hp β 3
      rw [ampOf_three] at o3
      gcongr
    · refine Finset.sum_le_sum fun β _ => bit_mul_le fun hb => ?_
      obtain ⟨-, ht4⟩ := hA.mu_free_pos β (planePoint p)
      have hη := hA.mu_eta_pos β
      have hc := hA.cμ_lt_one
      have hw := hA.mu_wt_nonneg β (planePoint p)
      have hf := hB.mu_freq ι hι β hb
      have i0 := hB.mu_inward ι hι p hp β 0
      rw [ampOf_zero] at i0
      have hin := inward_gradW_nonneg hA (m.muP β).modes (labelHarmonic mm ι) (planePoint p)
      have hsq : harmonicSum h (planePoint p)
          * (harmonicSum h (planePoint p) - inward h (m.muP β).modes h.ampGradW (labelHarmonic mm ι) (planePoint p))
          / (2 * (m.muP β).eta) ≤ harmonicSum h (planePoint p) ^ 2 / (2 * (m.muP β).eta) := by
        apply div_le_div_of_nonneg_right _ (by linarith)
        nlinarith [mul_nonneg hs hin]
      gcongr
  · refine Finset.sum_le_sum fun β _ => ?_
    have hη := hA.mu_eta_pos β
    have o1 := hB.mu_outward ι hι p hp β 1
    rw [ampOf_one] at o1
    gcongr

theorem uniformCoefficientBounds : UniformCoefficientBounds := by
  intro C nE nM m P h w W HW w₀ epsSup epsGradSup ratio hA B mm I Z hB ι hι p hp
  have hc := hB.class_eq ι hι
  refine ⟨?_, ?_, ?_, ?_, ?_, le_rfl⟩
  · show m.convD B.cls (planePoint p) - m.c ≤ m.convD (m.classOf (labelHarmonic mm ι)) (planePoint p) - m.c
    rw [hc]
  · show 1 - B.shareHatHigh m p - m.convD B.cls (planePoint p)
      ≤ 1 - m.shareHat h (labelHarmonic mm ι) (planePoint p) - m.convD (m.classOf (labelHarmonic mm ι)) (planePoint p)
    rw [hc]
    linarith [shareHat_le hA hB hι hp]
  · exact curl_le hA hB hι hp
  · exact grad_le hA hB hι hp
  · exact vel_le hA hB hι hp

end

end TailBand

end CertCell

end Breakdown

import Breakdown.CertCell.RowsMatchNormalTurn

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.SegmentNormal

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula LocalField
  LocalField.Internal.FaceTraceFree SegmentLine

namespace Internal

theorem radial_trace_split (K : CellBox) {c o lo hi : ℝ} (hR : Icc (min c o) (max c o) ×ˢ Icc lo hi = K.rect)
    {F₀ F₁ F₂ D₀ D₁ D₂ : ℝ × ℝ → ℂ} (t : ℝ → ℝ)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), F₀ p + F₁ p + F₂ p = 0)
    (hD : ∀ᵐ p ∂(volume.restrict K.rect), D₀ p + D₁ p + D₂ p = 0)
    (i₁ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₁ p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₁ p) * ((t p.2 : ℝ) : ℂ)) K.rect)
    (i₂ : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F₂ p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₂ p) * ((t p.2 : ℝ) : ℂ)) K.rect) :
    radialStripMoment c o lo hi F₀ D₀ t =
      -radialStripMoment c o lo hi F₁ D₁ t - radialStripMoment c o lo hi F₂ D₂ t := by
  unfold radialStripMoment
  rw [hR]
  have hae : ∀ᵐ p ∂(volume.restrict K.rect),
      ((((1 / (c - o) : ℝ)) : ℂ) * F₀ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₀ p) * ((t p.2 : ℝ) : ℂ)
        = -(((((1 / (c - o) : ℝ)) : ℂ) * F₁ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₁ p) * ((t p.2 : ℝ) : ℂ))
          - ((((1 / (c - o) : ℝ)) : ℂ) * F₂ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₂ p) * ((t p.2 : ℝ) : ℂ) := by
    filter_upwards [hF, hD] with p h1 h2
    linear_combination ((((1 / (c - o) : ℝ)) : ℂ) * ((t p.2 : ℝ) : ℂ)) * h1
      + ((((p.1 - o) / (c - o) : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ)) * h2
  have n₁ : IntegrableOn (fun p => -(((((1 / (c - o) : ℝ)) : ℂ) * F₁ p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * D₁ p) * ((t p.2 : ℝ) : ℂ))) K.rect := i₁.neg
  rw [integral_congr_ae hae, integral_sub n₁ i₂, integral_neg]
  ring

theorem radial_identity {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hf : IsLocalSecondOrderField v G H) (n : ℤ)
    {c o lo hi : ℝ} (hc : 0 < c) (ho : 0 ≤ o) (hco : c ≠ o) (hlh : lo < hi) (hlo : 0 ≤ lo)
    {t : ℝ → ℝ} (ht : ContDiff ℝ ∞ t) :
    radialStripMoment c o lo hi (gradMode m n G 0 0) (modeThird m n H 0 0 0) t =
      -((1 / c : ℝ) : ℂ) * (radialStripMoment c o lo hi (fun p => modeVec m n v p.1 p.2 0) (gradMode m n G 0 0) t
          + ((azimuth m n : ℂ) * Complex.I) *
            radialStripMoment c o lo hi (fun p => modeVec m n v p.1 p.2 1) (gradMode m n G 1 0) t)
        - ((t hi : ℝ) : ℂ) * cornerMoment c o hi lo (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0)
            (gradMode m n G 2 2) (modeThird m n H 2 0 2)
        + ((t lo : ℝ) : ℂ) * cornerMoment c o lo hi (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0)
            (gradMode m n G 2 2) (modeThird m n H 2 0 2)
        + radialStripMoment c o lo hi (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0) (deriv t) := by
  obtain ⟨K, hKdef⟩ : ∃ K : CellBox, K = ⟨min c o, max c o, lo, hi⟩ := ⟨_, rfl⟩
  have hr1 : K.r₁ = min c o := by rw [hKdef]
  have hr2 : K.r₂ = max c o := by rw [hKdef]
  have hz1 : K.z₁ = lo := by rw [hKdef]
  have hz2 : K.z₂ = hi := by rw [hKdef]
  have hK : IsCellBox K := ⟨⟨hr1 ▸ le_min hc.le ho, hr1 ▸ hr2 ▸ min_lt_max.2 hco⟩, ⟨hz1 ▸ hlo, hz1 ▸ hz2 ▸ hlh⟩⟩
  have hR : Icc (min c o) (max c o) ×ˢ Icc lo hi = K.rect := by rw [hKdef]; rfl
  have hax : K.r₁ = 0 → o = 0 := fun h => by
    by_contra hne
    have h0 : 0 < min c o := lt_min hc (lt_of_le_of_ne ho (Ne.symm hne))
    rw [hr1] at h
    exact h0.ne' h
  have hco' : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁) := by
    rw [hr1, hr2]
    rcases lt_or_gt_of_ne hco with h | h
    · left
      rw [min_eq_left h.le, max_eq_right h.le]
      exact ⟨rfl, rfl, hc.ne'⟩
    · right
      rw [min_eq_right h.le, max_eq_left h.le]
      exact ⟨rfl, rfl⟩
  have hT : Continuous (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (ht.continuous.comp continuous_snd)
  have hcT : Continuous (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * ((t p.2 : ℝ) : ℂ)) := continuous_const.mul hT
  have iI : ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * gradMode m n G a a p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a a 0 p) * ((t p.2 : ℝ) : ℂ)) K.rect := by
    intro a
    have h1 := (grad_rect_int K hK (m := m) hf n a a).mul_continuousOn hcT.continuousOn (rect_compact K)
    have h2 := offset_int K (third_weighted_int K hK (m := m) hf n a a 0) hax _ hcT
    refine (h1.add h2).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    push_cast
    ring
  have hsplit := radial_trace_split K hR t
    (F₀ := gradMode m n G 0 0) (F₁ := gradMode m n G 1 1) (F₂ := gradMode m n G 2 2)
    (D₀ := modeThird m n H 0 0 0) (D₁ := modeThird m n H 1 1 0) (D₂ := modeThird m n H 2 2 0)
    (by filter_upwards [grad_trace_zero K hK (m := m) hf n] with p hp
        simpa [Fin.sum_univ_three] using hp)
    (by filter_upwards [third_trace_zero K hK (m := m) hf n 0] with p hp
        simpa [Fin.sum_univ_three] using hp)
    (iI 1) (iI 2)
  have hV : ∀ a : Fin 3, IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect := fun a =>
    ((localModeStripIntegrable m v G H hf n (max c o) lo hi).1 a).mono_set (by
      rw [← hR]
      exact prod_mono (Icc_subset_Icc_left (le_min hc.le ho)) subset_rfl)
  have hturn := strip_turn K hK c o hco' (gradMode m n G 1 1) (modeThird m n H 1 1 0)
    (fun p => modeVec m n v p.1 p.2 0) (fun p => modeVec m n v p.1 p.2 1) (gradMode m n G 0 0)
    (gradMode m n G 1 0) 1 ((azimuth m n : ℂ) * Complex.I) t ht.continuous
    (ae_pos_on K hK (by
      filter_upwards [localAngularMode m v G H hf n] with p hp hpos
      rw [(hp hpos).2.1]
      ring))
    (ae_pos_on K hK (by
      filter_upwards [localTurnSecond m v G H hf n] with p hp hpos
      rw [(hp hpos).2.1]
      ring))
    (hV 0) (hV 1) ((localModeIntegrable m v G H hf K hK n 0).2 0) ((localModeIntegrable m v G H hf K hK n 1).2 0)
    (grad_rect_int K hK (m := m) hf n 1 1) (third_weighted_int K hK (m := m) hf n 1 1 0)
    (fun ψ hψ h1 h2 => (localTurnRadialWeak K hK m v G H hf n 1).2.2 ψ hψ h1 h2 t ht.continuous)
  rw [hz1, hz2] at hturn
  obtain ⟨i1, i2, i3⟩ := localRadialStripIbp m v G H hf K hK n 2 c o hco'
  have BP := lineForm_byParts (π := Prod.snd) (s := K.rect)
    (A := fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
    (B := fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p)
    continuous_snd (rect_compact K) i1 hlh True
    (fun g hg _ => i2.mul_continuousOn (Complex.continuous_ofReal.comp (hg.comp continuous_snd)).continuousOn
      (rect_compact K))
    (fun h hh h1 h2 _ => i3 h hh (hz1 ▸ h1) (hz2 ▸ h2)) ht (Or.inl trivial)
  have iA : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn (fun p : ℝ × ℝ =>
      (((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
        * ((f p.2 : ℝ) : ℂ)) K.rect := fun f hf' =>
    i1.mul_continuousOn (Complex.continuous_ofReal.comp (hf'.comp continuous_snd)).continuousOn (rect_compact K)
  have iB : ∀ f : ℝ → ℝ, Continuous f → IntegrableOn (fun p : ℝ × ℝ =>
      (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p)
        * ((f p.2 : ℝ) : ℂ)) K.rect := fun f hf' =>
    i2.mul_continuousOn (Complex.continuous_ofReal.comp (hf'.comp continuous_snd)).continuousOn (rect_compact K)
  have hdt : Continuous (deriv t) := ht.continuous_deriv (by simp)
  have hcomb := lineForm_comb (π := Prod.snd) (s := K.rect)
    (A := fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
    (B := fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p)
    (f := deriv t) (g := t) (deriv t) (fun _ => 0) (fun _ => 0) t (fun _ => 0) (fun _ => 0) 1 0
    (fun u => by ring) (fun u => by ring)
    (by simpa using iA _ hdt) (by simpa using iB _ ht.continuous) (by simp)
  have e22 : radialStripMoment c o lo hi (gradMode m n G 2 2) (modeThird m n H 2 2 0) t =
      edgeSign c o * lineForm Prod.snd K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p) (fun _ => 0) t := by
    unfold radialStripMoment lineForm
    rw [hR]
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [ae_pos_on K hK (localModeThirdSwap m v G H hf n 2)] with p hp
    rw [hp]
    push_cast
    ring
  have e2d : radialStripMoment c o lo hi (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0) (deriv t) =
      edgeSign c o * lineForm Prod.snd K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p) (deriv t) (fun _ => 0) := by
    unfold radialStripMoment lineForm
    rw [hR]
    congr 1
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  have eC1 : cornerMoment c o hi lo (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0)
      (gradMode m n G 2 2) (modeThird m n H 2 0 2) =
      edgeSign c o * lineForm Prod.snd K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p)
        (fun _ => 1 / (hi - lo)) (fun u => (u - lo) / (hi - lo)) := by
    unfold cornerMoment lineForm
    rw [edgeSign_of_lt hlh, min_eq_right hlh.le, max_eq_left hlh.le, hR, mul_one]
    congr 1
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  have eC0 : cornerMoment c o lo hi (fun p => modeVec m n v p.1 p.2 2) (gradMode m n G 2 0)
      (gradMode m n G 2 2) (modeThird m n H 2 0 2) =
      -(edgeSign c o * lineForm Prod.snd K.rect
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 2 + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G 2 0 p)
        (fun p => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G 2 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H 2 0 2 p)
        (fun _ => 1 / (lo - hi)) (fun u => (u - hi) / (lo - hi))) := by
    unfold cornerMoment lineForm
    rw [edgeSign_of_gt hlh, min_eq_left hlh.le, max_eq_right hlh.le, hR]
    rw [mul_neg_one, neg_mul]
    congr 2
    refine setIntegral_congr_fun (rect_measurable K) (fun p _ => ?_)
    simp only
    push_cast
    ring
  rw [hsplit, hturn, e22, e2d, eC1, eC0]
  push_cast at BP hcomb ⊢
  linear_combination (edgeSign c o) * hcomb - (edgeSign c o) * BP

end Internal

end Breakdown.CertCell.SegmentNormal

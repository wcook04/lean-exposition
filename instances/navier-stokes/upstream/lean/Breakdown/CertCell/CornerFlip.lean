import Breakdown.CertCell.BridgeStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal

def heightNegEquiv : ℝ × ℝ ≃ᵐ ℝ × ℝ :=
  (MeasurableEquiv.refl ℝ).prodCongr (MeasurableEquiv.neg ℝ)

theorem heightNegEquiv_apply (p : ℝ × ℝ) : heightNegEquiv p = (p.1, -p.2) := rfl

theorem heightNegEquiv_measurePreserving :
    MeasurePreserving heightNegEquiv (volume : Measure (ℝ × ℝ)) volume :=
  (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))

theorem heightNeg_preimage (a b h : ℝ) :
    heightNegEquiv ⁻¹' (Set.Icc a b ×ˢ Set.Icc (min 0 (-h)) (max 0 (-h)))
      = Set.Icc a b ×ˢ Set.Icc (min 0 h) (max 0 h) := by
  ext ⟨r, z⟩
  simp only [Set.mem_preimage, heightNegEquiv_apply, Set.mem_prod, Set.mem_Icc]
  rcases le_total 0 h with hh | hh
  · rw [min_eq_right (by linarith : -h ≤ 0), max_eq_left (by linarith : -h ≤ 0), min_eq_left hh,
      max_eq_right hh]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  · rw [min_eq_left (by linarith : (0 : ℝ) ≤ -h), max_eq_right (by linarith : (0 : ℝ) ≤ -h),
      min_eq_right hh, max_eq_left hh]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩

theorem flipped_setIntegral (g : ℝ × ℝ → ℂ) (a b h : ℝ) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (min 0 h) (max 0 h), g (p.1, -p.2)
      = ∫ p in Set.Icc a b ×ˢ Set.Icc (min 0 (-h)) (max 0 (-h)), g p := by
  rw [← heightNegEquiv_measurePreserving.setIntegral_preimage_emb heightNegEquiv.measurableEmbedding g,
    heightNeg_preimage]
  rfl

theorem edgeSign_zero_flip (h : ℝ) (I : ℂ)
    (hI : h = 0 → I = 0) :
    CellCert.CellFormula.edgeSign 0 h * (-I) = CellCert.CellFormula.edgeSign 0 (-h) * I := by
  unfold CellCert.CellFormula.edgeSign
  rcases lt_trichotomy h 0 with hh | hh | hh
  · rw [if_pos hh, if_neg (by linarith)]
    ring
  · rw [hI hh]
    ring
  · rw [if_neg (by linarith), if_pos (by linarith)]
    ring

theorem flat_integral_zero (g : ℝ × ℝ → ℂ) (a b : ℝ) :
    ∫ p in Set.Icc a b ×ˢ Set.Icc (min (0 : ℝ) (-0)) (max 0 (-0)), g p = 0 := by
  apply setIntegral_measure_zero
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  simp

end Internal

open Internal in
theorem cornerFlip : CornerFlipHolds := by
  intro F Fr Fz Frz cr orr h s
  unfold CellCert.CellFormula.cornerMoment
  set g : ℝ × ℝ → ℂ := fun p =>
    ((((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (0 - -h) : ℝ)) : ℂ) * F p
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - -h) / (0 - -h) : ℝ) : ℂ) * Fz p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (0 - -h) : ℝ)) : ℂ) * Fr p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - -h) / (0 - -h) : ℝ) : ℂ) * Frz p) with hg
  have hpt : ∀ p : ℝ × ℝ,
      ((((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * (s * F (p.1, -p.2))
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ) * (-(s * Fz (p.1, -p.2)))
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * (s * Fr (p.1, -p.2))
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ)
          * (-(s * Frz (p.1, -p.2))))
        = (fun q => -s * g q) (p.1, -p.2) := by
    intro p
    simp only [hg]
    push_cast
    ring
  simp_rw [hpt]
  rw [flipped_setIntegral (fun q => -s * g q), integral_const_mul]
  have hflip := edgeSign_zero_flip h (∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ
      Set.Icc (min 0 (-h)) (max 0 (-h)), g p)
    (fun h0 => by subst h0; exact flat_integral_zero g _ _)
  calc CellCert.CellFormula.edgeSign cr orr * CellCert.CellFormula.edgeSign 0 h
        * (-s * ∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min 0 (-h)) (max 0 (-h)), g p)
      = s * (CellCert.CellFormula.edgeSign cr orr * (CellCert.CellFormula.edgeSign 0 h
        * (-∫ p in Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min 0 (-h)) (max 0 (-h)), g p))) := by
          ring
    _ = _ := by
          rw [hflip]
          ring

end Bridge

end CertCell

end Breakdown

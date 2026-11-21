import Breakdown.CertCell.LabelRowProfileSspLocal
import Breakdown.CertCell.LabelRowProfileSspParts

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.RowSsp

theorem turnVector_combo (k : ℝ) (x y : Fin 3 → ℂ) (a : Fin 3) :
    turnVector k (fun b => x b + Complex.I * y b) a = turnVector k x a + Complex.I * turnVector k y a := by
  fin_cases a <;> simp [turnVector] <;> ring

theorem combo_parts {K : CellBox} {f g : ℝ × ℝ → ℂ} {F : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f K.rect ∧ ∫ p in K.rect, f p = 0) (hg : IntegrableOn g K.rect ∧ ∫ p in K.rect, g p = 0)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), F p = f p + Complex.I * g p) :
    IntegrableOn F K.rect ∧ ∫ p in K.rect, F p = 0 := by
  have hi : IntegrableOn (fun p => f p + Complex.I * g p) K.rect := hf.1.add (hg.1.const_mul Complex.I)
  refine ⟨hi.congr_fun_ae (by filter_upwards [hF] with p hp; exact hp.symm), ?_⟩
  rw [integral_congr_ae hF, integral_add hf.1 (hg.1.const_mul Complex.I), integral_const_mul, hf.2, hg.2]
  ring

end Internal.RowSsp

open Internal.RowSsp Internal.ModeParts Internal.RowParts in
theorem labelRowProfile_sumSecondPartials (h1 : HarmonicLiftStatement) (K : CellBox) (hK : IsCellBox K) (m : ℕ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (hv : IsPeriodicSecondOrder v G H)
    (ι : ℤ × ℤ) (hax : K.IsAxis → ι.1 = 0) (φ : Fin 3 → CellPoly)
    (hφ : IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ) :
    rowPairing K (labelRowProfile K m ι v G H Pg).lap φ = rowBoundaryGrad K (labelRowProfile K m ι v G H Pg) φ
      - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, (labelRowProfile K m ι v G H Pg).grad p a b
          * (starRingEnd ℂ) (testGrad K (labelAzimuth m ι : ℝ) φ p a b) := by
  have hmode : harmonicMode (labelTime ι) ι.1 = ι := by
    refine Prod.ext rfl ?_
    simp only [harmonicMode, labelTime]
    omega
  have heven : Even (ι.1 + labelTime ι) := ⟨ι.2, by simp only [labelTime]; ring⟩
  obtain ⟨hc, hs, hlift⟩ := h1 m v G H hv (labelTime ι)
  have hl := hlift ι.1 heven
  rw [hmode] at hl
  have hpos : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
    filter_upwards [ae_restrict_mem (rect_measurable K), ae_first_ne_zero_rect K] with p hp hne
    exact lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm hne)
  have hK0 : ∀ᵐ p ∂(volume.restrict K.rect),
      (∀ a b, gradAt m ι G a b p = gradMode m ι.1 (harmonicCos (labelTime ι) G) a b p
        + Complex.I * gradMode m ι.1 (harmonicSin (labelTime ι) G) a b p) ∧
      (∀ a b c, slopeAt m ι H a b c p = modeThird m ι.1 (harmonicCos (labelTime ι) H) a b c p
        + Complex.I * modeThird m ι.1 (harmonicSin (labelTime ι) H) a b c p) := by
    filter_upwards [ae_restrict_of_ae hl, hpos] with p h hp
    exact ⟨(h hp).2.1, (h hp).2.2⟩
  have hk : (labelAzimuth m ι : ℝ) = azimuth m ι.1 := by
    simp [labelAzimuth, azimuth]
  refine row_parts_identity K hK (labelAzimuth m ι : ℝ) (fun a b p => gradAt m ι G a b p)
    (fun a b c p => slopeAt m ι H a b c p) (labelRowProfile K m ι v G H Pg) (fun p => rfl) (fun p => rfl)
    (fun e z => rfl) (fun e r => rfl) ?_ ?_ ?_ ?_ ?_ φ
  · intro a b
    have hi := (gradMode_integrableOn hc K hK m ι.1 a b).add
      ((gradMode_integrableOn hs K hK m ι.1 a b).const_mul Complex.I)
    refine hi.congr_fun_ae ?_
    filter_upwards [hK0] with p hp
    exact ((hp.1 a b)).symm
  · intro a b c
    have hi := (weighted_modeThird_integrableOn hc K hK m ι.1 a b c).add
      ((weighted_modeThird_integrableOn hs K hK m ι.1 a b c).const_mul Complex.I)
    refine hi.congr_fun_ae ?_
    filter_upwards [hK0] with p hp
    simp only [Pi.add_apply]
    rw [hp.2 a b c]
    ring
  · intro a χ τ hχ h1' h2' hτ
    refine combo_parts (radial_parts hc K hK m ι.1 a hχ h1' h2' hτ) (radial_parts hs K hK m ι.1 a hχ h1' h2' hτ) ?_
    filter_upwards [hK0] with p hp
    rw [hp.1 a 0, hp.2 a 0 0]
    ring
  · intro a A χ hA hχ h1' h2'
    refine combo_parts (height_parts hc K hK m ι.1 a hA hχ h1' h2') (height_parts hs K hK m ι.1 a hA hχ h1' h2') ?_
    filter_upwards [hK0] with p hp
    rw [hp.1 a 2, hp.2 a 2 2]
    ring
  · intro a
    filter_upwards [hK0, hpos, ae_restrict_of_ae (angular_column hc m ι.1 a),
      ae_restrict_of_ae (angular_column hs m ι.1 a)] with p hp hp0 hca hsa
    have e1 : (fun b => gradAt m ι G b 1 p) = fun b => gradMode m ι.1 (harmonicCos (labelTime ι) G) b 1 p
        + Complex.I * gradMode m ι.1 (harmonicSin (labelTime ι) G) b 1 p := funext fun b => hp.1 b 1
    rw [e1, turnVector_combo, hk, hp.2 a 1 1, hp.1 a 0]
    linear_combination hca hp0 + Complex.I * hsa hp0

end CellCalculus

end CertCell

end Breakdown

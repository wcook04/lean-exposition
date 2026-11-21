import Breakdown.CertCell.RowLowPartVolume

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem rowLow_core (hexpS : SegmentTestExpansionStatement) (hexpC : CellBasisExpansionStatement)
    (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) (h3 : HarmonicSideDataStatement)
    (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout) (hL : IsHarmonicLayout m K B L.modes L)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space)
    (hv : IsPeriodicSecondOrder v G H) (hp : IsPeriodicPressure Pg) (ι : ℤ × ℤ) (hmodes : L.modes = {ι.1})
    (P : ℝ) (φ : Fin 3 → CellPoly) (hsol : IsTestSolenoidal K (labelAzimuth m ι : ℝ) φ)
    (hreg : IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ) (hshape : IsTestOfShape K L.degSide φ)
    (hdeg : L.degSide + 2 ≤ L.degCoef) (hps : IsPressureSegmentation L) :
    rowVolume K (labelAzimuth m ι : ℝ) (labelTimeFreq P ι) (labelRowProfile K m ι v G H Pg) φ
        - rowBoundaryGrad K (labelRowProfile K m ι v G H Pg) φ + rowBoundaryPres K (labelRowProfile K m ι v G H Pg) φ
      = ∑ d, ownRowVector L (labelAzimuth m ι : ℝ) (labelTimeFreq P ι) φ d
          * harmonicData L (labelTime ι) v G H Pg d := by
  have hL0 := hL
  obtain ⟨c0, S0, hord, -, hLc⟩ := hL
  have hK := hLc.box_valid
  have hordL : L.order = m := hLc.order_eq.trans hord
  have hq1 := hLc.degSide_pos
  obtain ⟨hφa, hφ0, hφ2⟩ := shape_polys hq1 hshape
  choose hs hsP hsE using fun a b =>
    strain_shape hK (labelAzimuth m ι : ℝ) (q := L.degSide) (Q := L.degCoef) hdeg hφa hreg a b
  choose hw hwP hwE using fun a => vel_shape (K := K) (q := L.degSide) (Q := L.degCoef) hdeg (hφa a)
  rw [own_sum, strain_block_data hexpC h1 Pg hv hLc hordL ι hmodes _ φ hs hsP hsE,
    vel_block_data hexpC h1 Pg hv hLc hordL ι hmodes _ φ hw hwP hwE,
    volume_data h1 Pg hv m ι hK _ _ φ hs hsP hsE hw hwP hwE]
  have hn0 : ι.1 ∈ L.modes := by rw [hmodes]; exact Finset.mem_singleton_self _
  have hG : (∑ i : L.modes × Fin L.segCount × Fin 3 × Fin (L.degSide + 1),
      sideGradRow L φ i.2.1 i.2.2.1 i.2.2.2 *
        harmonicData L (labelTime ι) v G H Pg (Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))))
      = -rowBoundaryGrad K (labelRowProfile K m ι v G H Pg) φ := by
    refine (sum_modes L hmodes _).trans ?_
    have hside := (h3 m K B L hL0 v G H Pg hv hp (labelTime ι) ⟨ι.1, hn0⟩ (even_label ι)).2
    have hm : harmonicMode (labelTime ι) ((⟨ι.1, hn0⟩ : L.modes) : ℤ) = ι := harmonicMode_label ι
    rw [hm] at hside
    simp only [Fintype.sum_prod_type]
    refine Eq.trans (Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun a _ =>
      Finset.sum_congr rfl (fun d _ => congrArg (fun x => sideGradRow L φ s a d * x) (hside s a d))))) ?_
    exact grad_block hexpS hLc φ hφa (fun a => gradAt m ι G a 0) (fun a => slopeAt m ι H a 0 0)
      (fun a => slopeAt m ι H a 0 2) (fun a => gradAt m ι G a 2) (fun a => slopeAt m ι H a 2 0)
      (fun a => slopeAt m ι H a 2 2) (labelRowProfile K m ι v G H Pg) (fun _ _ => rfl) (fun _ _ => rfl)
      (fun a => gradAt_int h1 hv m ι hK a 0) (fun a => slopeAt_w_int h1 hv m ι hK a 0 0)
      (fun a => w_int_fst (gradAt_int h1 hv m ι hK a 2)) (fun a => slopeAt_w_int h1 hv m ι hK a 2 2)
  have hPr : (∑ i : L.modes × Fin L.presCount × Fin L.degSide,
      sidePresRow L φ i.2.1 i.2.2 *
        harmonicData L (labelTime ι) v G H Pg (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))))
      = rowBoundaryPres K (labelRowProfile K m ι v G H Pg) φ := by
    refine (sum_modes L hmodes _).trans ?_
    simp only [Fintype.sum_prod_type, data_sidePressure]
    set ν := labelTime ι with hν
    set κ : ℂ := presMode m ι.1 (fun _ => 1) 0 0 with hκ
    set ec : ℝ := (L.gaugeValue (cosTuple ν v G H Pg) / L.gaugeUnit).re with hec
    set es : ℝ := (L.gaugeValue (sinTuple ν v G H Pg) / L.gaugeUnit).re with hes
    have hQc := (hp.harmonic_gradient ν).1
    have hQs := (hp.harmonic_gradient ν).2
    have ic : IntegrableOn (L.pressMode ι.1 (cosTuple ν v G H Pg)) K.rect := by
      rw [pressMode_cos, hordL]
      exact (MeshDataAffineModes.gradient_modes_integrable m _ hQc ι.1 ec K.r₁ K.r₂ K.z₁ K.z₂).1
    have is : IntegrableOn (L.pressMode ι.1 (sinTuple ν v G H Pg)) K.rect := by
      rw [pressMode_sin, hordL]
      exact (MeshDataAffineModes.gradient_modes_integrable m _ hQs ι.1 es K.r₁ K.r₂ K.z₁ K.z₂).1
    have igc : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * L.pressureGradMode ι.1 (cosTuple ν v G H Pg) a p) K.rect := by
      intro a
      rw [pgm_cos, hordL]
      exact (MeshDataAffineModes.gradient_modes_integrable m _ hQc ι.1 0 K.r₁ K.r₂ K.z₁ K.z₂).2 a
    have igs : ∀ a, IntegrableOn (fun p => (p.1 : ℂ) * L.pressureGradMode ι.1 (sinTuple ν v G H Pg) a p) K.rect := by
      intro a
      rw [pgm_sin, hordL]
      exact (MeshDataAffineModes.gradient_modes_integrable m _ hQs ι.1 0 K.r₁ K.r₂ K.z₁ K.z₂).2 a
    have hP : ∀ᵐ p ∂(volume.restrict K.rect), L.pressMode ι.1 (cosTuple ν v G H Pg) p
        + Complex.I * L.pressMode ι.1 (sinTuple ν v G H Pg) p
        = labelPressure m ι Pg p - ((ec : ℂ) * κ + Complex.I * ((es : ℂ) * κ)) := by
      filter_upwards [ae_restrict_of_ae (presMode_shift m _ hQc ι.1 ec),
        ae_restrict_of_ae (presMode_shift m _ hQs ι.1 es)] with p h1' h2'
      rw [pressMode_cos, pressMode_sin, hordL]
      simp only
      rw [h1', h2']
      unfold labelPressure
      ring
    have hd : ∀ a, ∀ᵐ p ∂(volume.restrict K.rect), L.pressureGradMode ι.1 (cosTuple ν v G H Pg) a p
        + Complex.I * L.pressureGradMode ι.1 (sinTuple ν v G H Pg) a p = velAt m ι Pg a p := by
      intro a
      filter_upwards [pres_lift_rect h2 hp m ι hK] with p hq
      rw [pgm_cos, pgm_sin, hordL, hq a]
    have hC : ((ec : ℂ) * κ + Complex.I * ((es : ℂ) * κ)) * fluxConj K φ = 0 := by
      by_cases hk : (ι.1 : ℝ) * m = 0
      · have hk' : ((labelAzimuth m ι : ℤ) : ℝ) = 0 := by
          unfold labelAzimuth; push_cast; exact hk
        rw [hk'] at hsol
        rw [flux_zero hK φ hφ0 hφ2 hsol, mul_zero]
      · rw [hκ, presMode_one m ι.1 hk]
        ring
    exact pres_block hexpS hLc hps φ hφ0 hφ2 _ _ _ _ _ _ (labelPressure m ι Pg) (fun p => velAt m ι Pg 0 p)
      (fun p => velAt m ι Pg 2 p) _ (labelRowProfile K m ι v G H Pg) (fun _ _ => rfl) (fun _ _ => rfl)
      ic is (labelPressure_int hp m ι) (igc 0) (igs 0) (presVel_w_int h2 hp m ι hK 0) (igc 2) (igs 2)
      (presVel_w_int h2 hp m ι hK 2) hP (hd 0) (hd 2) hC
  rw [hG, hPr]
  ring

theorem transfer_profile {K : CellBox} {k freq : ℝ} {R R' : RowProfile} (hR : IsRowProfile K k R) {φ : Fin 3 → CellPoly}
    (hsol : IsTestSolenoidal K k φ) (hreg : IsAxisRegularTest K k φ)
    (hlap : rowPairing K R'.lap φ = rowBoundaryGrad K R' φ - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      R'.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
    (hpres : rowPairing K R'.presGrad φ = rowBoundaryPres K R' φ)
    (hae : ∀ᵐ p ∂(volume.restrict K.rect), R.vel p = R'.vel p ∧ R.grad p = R'.grad p ∧ R.lap p = R'.lap p ∧
      R.presGrad p = R'.presGrad p) :
    rowVolume K k freq R φ - rowBoundaryGrad K R φ + rowBoundaryPres K R φ
      = rowVolume K k freq R' φ - rowBoundaryGrad K R' φ + rowBoundaryPres K R' φ := by
  have hl := hR.laplacian_parts φ hreg
  have hpr := hR.pressure_parts φ hsol hreg
  have e1 : rowVolume K k freq R φ = rowVolume K k freq R' φ := by
    unfold rowVolume
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp.1, hp.2.1]
  have e2 : rowPairing K R.lap φ = rowPairing K R'.lap φ := by
    unfold rowPairing
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp.2.2.1]
  have e3 : rowPairing K R.presGrad φ = rowPairing K R'.presGrad φ := by
    unfold rowPairing
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp.2.2.2]
  have e4 : (∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
      = ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, R'.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b) := by
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp.2.1]
  rw [e2, e4] at hl
  rw [e3] at hpr
  rw [e1, ← hpr, ← hpres]
  linear_combination hl - hlap

end Breakdown.CertCell.CellCalculus.RowLow.Internal

namespace Breakdown.CertCell.CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem rowLowPart_of_parts (hexpS : SegmentTestExpansionStatement) (hexpC : CellBasisExpansionStatement)
    (h1 : HarmonicLiftStatement) (h2 : HarmonicPressureLiftStatement) (h3 : HarmonicSideDataStatement)
    (hlap : ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : ℝ → Space → Space)
      (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
      (Pg : ℝ → Space → Space), IsPeriodicSecondOrder v G H → ∀ (ι : ℤ × ℤ), (K.IsAxis → ι.1 = 0) →
      ∀ φ : Fin 3 → CellPoly, IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ →
        rowPairing K (labelRowProfile K m ι v G H Pg).lap φ
          = rowBoundaryGrad K (labelRowProfile K m ι v G H Pg) φ - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3,
            ∑ b : Fin 3, (labelRowProfile K m ι v G H Pg).grad p a b *
              (starRingEnd ℂ) (testGrad K (labelAzimuth m ι : ℝ) φ p a b))
    (hpres : ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : ℝ → Space → Space)
      (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
      (Pg : ℝ → Space → Space), IsPeriodicPressure Pg → ∀ (ι : ℤ × ℤ), (K.IsAxis → ι.1 = 0) →
      ∀ φ : Fin 3 → CellPoly, IsTestSolenoidal K (labelAzimuth m ι : ℝ) φ →
        IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ →
        rowPairing K (labelRowProfile K m ι v G H Pg).presGrad φ = rowBoundaryPres K (labelRowProfile K m ι v G H Pg) φ) :
    RowLowPartStatement := by
  intro m K B L hL v G H Pg hv hp ι hmodes hax P R hR hae φ hsol hreg hshape hdeg hps
  have hK : IsCellBox K := by
    obtain ⟨_, _, _, _, hLc⟩ := hL
    exact hLc.box_valid
  rw [RowLow.Internal.transfer_profile (R' := labelRowProfile K m ι v G H Pg) hR hsol hreg
    (hlap K hK m v G H Pg hv ι hax φ hreg) (hpres K hK m v G H Pg hp ι hax φ hsol hreg) hae]
  exact RowLow.Internal.rowLow_core hexpS hexpC h1 h2 h3 m K B L hL v G H Pg hv hp ι hmodes P φ hsol hreg hshape
    hdeg hps

end Breakdown.CertCell.CellCalculus

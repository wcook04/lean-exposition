import Breakdown.CertCell.EnergyLeafBoundForm
import Breakdown.CertCell.LocalFieldDefs2

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.HarmonicEnergyValue

theorem axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have hs : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ Set.univ := by
    ext p
    simp
  rw [ae_iff, hs, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem label_mode (ι : ℤ × ℤ) : harmonicMode (labelTime ι) ι.1 = ι := by
  unfold harmonicMode labelTime
  refine Prod.ext rfl ?_
  show (ι.1 + (2 * ι.2 - ι.1)) / 2 = ι.2
  omega

theorem label_even (ι : ℤ × ℤ) : Even (ι.1 + labelTime ι) :=
  ⟨ι.2, by unfold labelTime; ring⟩

end Internal.HarmonicEnergyValue

open Internal.HarmonicEnergyValue in
theorem harmonicEnergyFormValue_of (h1 : HarmonicLiftStatement) (h2 : LocalRepresentsStatement)
    (h3 : LocalModeDataPairStatement) (h4 : LocalEnergyValueStatement) (h5 : EnergyAeCongrStatement) :
    HarmonicEnergyFormValueStatement := by
  intro m K B ι L hL _ v G H Pg hP hPg e eω
  obtain ⟨c, S, hco, hSm, hcl⟩ := hL
  subst hco
  obtain ⟨hc, hs, hmode⟩ := h1 c.order v G H hP (labelTime ι)
  have hac : IsLocalAdmissible (cosTuple (labelTime ι) v G H Pg) := ⟨hc, (hPg.harmonic_gradient _).1⟩
  have has : IsLocalAdmissible (sinTuple (labelTime ι) v G H Pg) := ⟨hs, (hPg.harmonic_gradient _).2⟩
  have hK : IsCellBox K := hcl.box_valid
  have hB : IsCellBases K B := hcl.bases_valid
  have hM := h3 c.order K B (layoutIndex L) _ _ _ _ _ _ _ _ hK hB hc hs (h2 c K S B L hcl _ hac)
    (h2 c K S B L hcl _ has)
  have hV := h4 c.order K B (layoutIndex L) _ _ _ hK hB hcl.degSide_pos hcl.degSide_le hM
    (fun _ => e) (fun _ => eω)
  have hdata : harmonicData L (labelTime ι) v G H Pg = fun d =>
      L.trueData (cosTuple (labelTime ι) v G H Pg) d + Complex.I * L.trueData (sinTuple (labelTime ι) v G H Pg) d :=
    rfl
  have hmem : ι.1 ∈ L.modes := by
    rw [hcl.modes_eq, hSm]
    exact Finset.mem_singleton_self _
  rw [hdata, hV, Fintype.sum_eq_single ⟨ι.1, hmem⟩ (fun n hn => absurd (Subtype.ext (by
    have h : (n : ℤ) ∈ ({ι.1} : Finset ℤ) := by
      rw [← hSm, ← hcl.modes_eq]
      exact n.2
    exact Finset.mem_singleton.1 h)) hn)]
  have hm := hmode ι.1 (label_even ι)
  rw [label_mode ι] at hm
  have hae : ∀ᵐ p ∂(volume.restrict K.rect),
      (∀ a b, gradAt c.order ι G a b p = gradMode c.order ι.1 (harmonicCos (labelTime ι) G) a b p
        + Complex.I * gradMode c.order ι.1 (harmonicSin (labelTime ι) G) a b p) ∧
      (∀ a b c', slopeAt c.order ι H a b c' p = modeThird c.order ι.1 (harmonicCos (labelTime ι) H) a b c' p
        + Complex.I * modeThird c.order ι.1 (harmonicSin (labelTime ι) H) a b c' p) := by
    rw [ae_restrict_iff' (show MeasurableSet K.rect from measurableSet_Icc.prod measurableSet_Icc)]
    filter_upwards [hm, axis_null] with p hp hp0 hpr
    have hpr' : p ∈ Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂ := hpr
    have h0 : 0 < p.1 := lt_of_le_of_ne (le_trans hK.r_order.1 hpr'.1.1) (Ne.symm hp0)
    exact ⟨(hp h0).2.1, (hp h0).2.2⟩
  clear hV hM hmode hm h1 h2 h3 h4 hac has hc hs hdata
  unfold labelStrainEnergy labelVorticityEnergy
  refine congrArg₂ (· + ·) (congrArg (e * ·) (Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_))
    (congrArg (eω * ·) (Finset.sum_congr rfl fun i _ => ?_))
  · have hg : (fun p => gradMode c.order ι.1 (harmonicCos (labelTime ι) G) a b p
        + Complex.I * gradMode c.order ι.1 (harmonicSin (labelTime ι) G) a b p) =ᵐ[volume.restrict K.rect]
        gradAt c.order ι G a b := hae.mono fun p hp => (hp.1 a b).symm
    have hs : ∀ c', (fun p => modeThird c.order ι.1 (harmonicCos (labelTime ι) H) a b c' p
        + Complex.I * modeThird c.order ι.1 (harmonicSin (labelTime ι) H) a b c' p) =ᵐ[volume.restrict K.rect]
        slopeAt c.order ι H a b c' := fun c' => hae.mono fun p hp => (hp.2 a b c').symm
    have ht : (fun p : ℝ × ℝ => (p.1 : ℂ) * (modeThird c.order ι.1 (harmonicCos (labelTime ι) H) a b 1 p
        + Complex.I * modeThird c.order ι.1 (harmonicSin (labelTime ι) H) a b 1 p)) =ᵐ[volume.restrict K.rect]
        turnedSlopeAt c.order ι H a b := hae.mono fun p hp => by simp only [turnedSlopeAt, hp.2]
    rw [(h5 K hK _ _ _ _ _ _ hg (hs 0)).1, (h5 K hK _ _ _ _ _ _ hg (hs 2)).2.1,
      (h5 K hK L.degCoef L.degSide _ _ _ _ ht ht).2.2]
  · have hg : (fun p => curlComp (fun a b => gradMode c.order ι.1 (harmonicCos (labelTime ι) G) a b p
        + Complex.I * gradMode c.order ι.1 (harmonicSin (labelTime ι) G) a b p) i) =ᵐ[volume.restrict K.rect]
        fun p => curlComp (fun a b => gradAt c.order ι G a b p) i := hae.mono fun p hp => by simp only [hp.1]
    have hs : ∀ c', (fun p => curlComp (fun a b => modeThird c.order ι.1 (harmonicCos (labelTime ι) H) a b c' p
        + Complex.I * modeThird c.order ι.1 (harmonicSin (labelTime ι) H) a b c' p) i)
        =ᵐ[volume.restrict K.rect] fun p => curlComp (fun a b => slopeAt c.order ι H a b c' p) i :=
      fun c' => hae.mono fun p hp => by simp only [hp.2]
    have ht : (fun p : ℝ × ℝ => curlComp (fun a b => (p.1 : ℂ) *
        (modeThird c.order ι.1 (harmonicCos (labelTime ι) H) a b 1 p
          + Complex.I * modeThird c.order ι.1 (harmonicSin (labelTime ι) H) a b 1 p)) i)
        =ᵐ[volume.restrict K.rect] fun p => curlComp (fun a b => turnedSlopeAt c.order ι H a b p) i :=
      hae.mono fun p hp => by simp only [turnedSlopeAt, hp.2]
    rw [(h5 K hK _ _ _ _ _ _ hg (hs 0)).1, (h5 K hK _ _ _ _ _ _ hg (hs 2)).2.1,
      (h5 K hK L.degCoef L.degSide _ _ _ _ ht ht).2.2]

end Breakdown.CertCell.CellCalculus

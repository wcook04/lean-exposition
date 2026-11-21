import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.TailPointwise
import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.TailCoefficients

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCalculus


namespace Internal.OffModeCover

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem null_axis_plane : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ 0 := by
  have hnull : volume ((Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  rw [ae_iff]
  refine measure_mono_null ?_ hnull
  intro p hp
  exact ⟨Set.mem_univ _, by simpa using hp⟩

theorem quad_withStretch_antitone (a : TailBand.PointCoef)
    (s sa mg wg len c₁ c₂ g₁ g₂ u₁ u₂ x2 xc x1 xo x0 : ℝ) (hc : c₁ ≤ c₂) (hg : g₁ ≤ g₂) (hu : u₁ ≤ u₂) :
    (a.withStretch s sa mg wg len c₂ g₂ u₂).quad x2 xc x1 xo x0
      ≤ (a.withStretch s sa mg wg len c₁ g₁ u₁).quad x2 xc x1 xo x0 := by
  simp only [TailBand.PointCoef.quad, TailBand.PointCoef.withStretch]
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg xo), mul_le_mul_of_nonneg_right hg (sq_nonneg x1),
    mul_le_mul_of_nonneg_right hu (sq_nonneg x0)]

theorem offModeDensity_antitone {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds} {w : Space → ℝ}
    {mc : ModeCharges} {e₁ e₂ : TailBand.EntryCharges} {mm : ℕ} {ι : ℤ × ℤ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {p : ℝ × ℝ}
    (hs : e₁.stretchConst = e₂.stretchConst) (hc : e₁.curlCharge p ≤ e₂.curlCharge p)
    (hg : e₁.gradCharge p ≤ e₂.gradCharge p) (hu : e₁.velCharge p ≤ e₂.velCharge p) :
    TailBand.offModeDensity m P h w mc e₂ mm ι v G H p ≤ TailBand.offModeDensity m P h w mc e₁ mm ι v G H p := by
  unfold TailBand.offModeDensity TailBand.labelQuad
  rw [hs]
  exact quad_withStretch_antitone _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hc hg hu

theorem offModesVanish_of_sound_of_dominates (hS : TailBand.OffModeConditionSound)
    (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (O : OffModeCover D)
    (hadm : ∃ e₁ e₂ e₃ : ℝ, ∀ q ∈ D.cert.params, CoerciveWeak.IsAdmissibleWeak (D.pieces q) (D.cert.period q)
      (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight e₁ e₂ e₃)
    (hmesh : IsCellMesh D.mesh) (hO : IsOffModeCover D R O)
    (hdom : ∀ q ∈ D.cert.params, ∀ v G H, ∀ K, ∀ ι ∉ D.mesh.resolved K, ∀ j ∈ O.choose K ι,
      ∀ p ∈ (D.mesh.box K).rect ∩ (O.conditions j).region,
        TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (O.conditions j).charges D.azimuthOrder ι v G H p
        ≤ TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p) :
    OffModesVanish D R := by
  intro q hq v G H g hv K
  obtain ⟨e₁, e₂, e₃, he⟩ := hadm
  unfold CellCalculus.offNeg
  refine ENNReal.tsum_eq_zero.mpr fun ι => ?_
  split_ifs with hι
  · rfl
  have mrect : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  have hchk : ∀ j ∈ O.choose K ι, ∀ᵐ p ∂volume, p ∈ (O.conditions j).region →
      0 ≤ TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
        (O.conditions j).charges D.azimuthOrder ι v G H p := by
    intro j hj
    have hval := hO.valid q hq K ι hι j hj
    exact (ae_restrict_iff' hval.region_measurable).1
      (hS (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn D.given D.givenHess D.cert.weight
        e₁ e₂ e₃ (he q hq) D.azimuthOrder (O.conditions j) (D.charges (some K)) hval D.cert.symmetries v G H g hv ι
        (hO.mode_mem K ι hι j hj))
  have hall := (Filter.eventually_all_finset (O.choose K ι)).2 hchk
  have hae : ∀ᵐ p ∂volume, p ∈ (D.mesh.box K).rect → p ∈ halfPlane →
      0 ≤ TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
        (R.entryCharges K ι) D.azimuthOrder ι v G H p := by
    filter_upwards [hall] with p hp hpr hph
    obtain ⟨j, hj, hpj⟩ := Set.mem_iUnion₂.1 (hO.region_sup K ι hι ⟨hpr, hph⟩)
    exact (hp j hj hpj).trans (hdom q hq v G H K ι hι j hj p ⟨hpr, hpj⟩)
  have hbox := hmesh.box_valid K
  refine (lintegral_congr_ae ?_).trans lintegral_zero
  filter_upwards [ae_restrict_of_ae hae, ae_restrict_mem mrect, ae_restrict_of_ae null_axis_plane]
    with p hp hpr hp2
  have hr : 0 ≤ p.1 := le_trans hbox.r_order.1 hpr.1.1
  have hz : 0 ≤ p.2 := le_trans hbox.z_order.1 hpr.2.1
  rcases hr.eq_or_lt with h0 | hpos
  · simp [← h0]
  · have hd := hp hpr ⟨hpos, lt_of_le_of_ne hz (Ne.symm hp2)⟩
    exact ENNReal.ofReal_eq_zero.mpr (neg_nonpos.mpr (mul_nonneg hd hpos.le))

end Internal.OffModeCover

open Internal.OffModeCover in
theorem offModesVanish_of_sound (hS : TailBand.OffModeConditionSound) : OffModesVanishHolds := by
  intro k C nE nM D R O _ _ hadm hmesh hO
  refine offModesVanish_of_sound_of_dominates hS D R O hadm hmesh hO ?_
  intro q _ v G H K ι hι j hj p hp
  obtain ⟨h1, h2, h3, h4⟩ := hO.charges_le K ι hι j hj p hp
  exact offModeDensity_antitone (e₁ := R.entryCharges K ι) (e₂ := (O.conditions j).charges) h4 h1 h2 h3

theorem offModeConditionSound_holds : TailBand.OffModeConditionSound :=
  TailBand.offModeConditionSound_of TailBand.angularModeBounds TailBand.pointwiseQuadraticTest
    TailBand.uniformCoefficientBounds

theorem offModesVanishHolds : OffModesVanishHolds :=
  offModesVanish_of_sound offModeConditionSound_holds

end Assembly

end CertCell

end Breakdown

import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.FracCell.HeightModeWeak

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

namespace Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open FracInternal.HeightModeWeak

theorem localGradient_locInt {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    LocallyIntegrable G volume :=
  loc_of_cols hs.measurable_gradient fun j =>
    (memLp_col hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)

theorem localSecondColumn_locInt {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (j : Fin 3) :
    LocallyIntegrable (fun y => H y (unitVector j)) volume :=
  loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
    (memLp_col2 hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)

theorem localGradient_weak {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
    (localGradient_locInt hs).integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
    (localSecondColumn_locInt hs j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
      (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
    intro i
    rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
    simpa using hs.weak_second φ hφ i j
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_expand u]
  simp only [map_sum, map_smul, key]

theorem localHeightSmoothWeak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p =
      -∫ p, (ψ p : ℂ) * modeThird m n H a b 2 p := by
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (colQ a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, colQ_circle]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a b 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (colQ a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) axialUnit) : ℂ) := by
    intro p
    simp only [modeThird, colQ_circle]
    rfl
  simp only [hth, hgm]
  exact scale _ (cylModeWeak (Space →L[ℝ] Space) G H (localGradient_locInt hs) (localSecondColumn_locInt hs)
    (localGradient_weak hs) (colQ a b) (colQ_smooth a b) m n ψ hψ hc hpos).2

theorem localWeightedModes_int {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) (Icc 0 R ×ˢ Icc (-Z) Z) ∧
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b 2 p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have w1 := FracInternal.ModeHeightAxis.weighted_int R Z (localGradient_locInt hs)
    (LowEntry.Internal.gradKernel m n a b) (LowEntry.Internal.gradKernel_cont m n a b)
    (LowEntry.Internal.gradKernel_bound m n a b)
  have w2 := FracInternal.ModeHeightAxis.weighted_int R Z (localSecondColumn_locInt hs 2)
    (LowEntry.Internal.gradKernel m n a b) (LowEntry.Internal.gradKernel_cont m n a b)
    (LowEntry.Internal.gradKernel_bound m n a b)
  have hthird : ∀ p, modeThird m n H a b 2 p = gradMode m n (fun y => H y (unitVector 2)) a b p :=
    fun p => rfl
  constructor
  · have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi,
          LowEntry.Internal.gradKernel m n a b θ (G (cylPoint p.1 θ p.2))) := by
      funext p
      rw [LowEntry.Internal.gradMode_eq]
      ring
    rw [e]
    exact w1.const_mul _
  · have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b 2 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi,
          LowEntry.Internal.gradKernel m n a b θ (H (cylPoint p.1 θ p.2) (unitVector 2))) := by
      funext p
      rw [hthird, LowEntry.Internal.gradMode_eq]
      ring
    rw [e]
    exact w2.const_mul _

theorem localProductWeak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) (n : ℤ) (a b : Fin 3)
    (φ χ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioi 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * gradMode m n G a b p) =
      -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a b 2 p) := by
  set u : ℝ → ℝ := fun r => φ r * r with hu_def
  have hu : ContDiff ℝ ∞ u := hφ.mul contDiff_id
  have hus : tsupport u ⊆ tsupport φ := tsupport_mul_subset_left
  have huc : HasCompactSupport u := hφc.mul_right
  set ψ : ℝ × ℝ → ℝ := fun q => u q.1 * χ q.2 with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := (hu.comp contDiff_fst).mul (hχ.comp contDiff_snd)
  have hψsub : tsupport ψ ⊆ tsupport u ×ˢ tsupport χ := by
    refine closure_minimal (fun q hq => ?_) ((isClosed_tsupport _).prod (isClosed_tsupport _))
    have hq' : u q.1 * χ q.2 ≠ 0 := hq
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hq'), subset_tsupport _ (right_ne_zero_of_mul hq')⟩
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (huc.isCompact.prod hχc.isCompact) (fun q hq => ?_)
    by_contra hne
    exact hq (hψsub (subset_tsupport _ hne))
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p hp => hφs (hus (hψsub hp).1)
  have key := localHeightSmoothWeak (m := m) hs n a b ψ hψ hψc hpos
  have e1 : (fun p : ℝ × ℝ => ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * gradMode m n G a b p)) =
      fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p := by
    funext p
    rw [hψ_def, prod_fderiv hu hχ p, hu_def]
    push_cast
    ring
  have e2 : (fun p : ℝ × ℝ => ((φ p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a b 2 p)) =
      fun p => (ψ p : ℂ) * modeThird m n H a b 2 p := by
    funext p
    simp only [hψ_def, hu_def]
    push_cast
    ring
  rw [e1, e2]
  exact key

end Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy
open FracInternal.HeightModeWeak _root_.Breakdown.CertCell.LocalField.Internal

theorem localHeightModeWeak : LocalHeightModeWeakStatement := by
  intro m v G H hs K hK n a b t s ht hsc hax
  obtain ⟨T, hT, hTt⟩ := weight_split K t ht hax
  set Fw : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * gradMode m n G a b p with hFw
  set Dw : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * heightGradMode m n H a b p with hDw
  have hF : ∀ R Z : ℝ, IntegrableOn Fw (Icc 0 R ×ˢ Icc (-Z) Z) :=
    fun R Z => (localWeightedModes_int hs n a b R Z).1
  have hD : ∀ R Z : ℝ, IntegrableOn Dw (Icc 0 R ×ˢ Icc (-Z) Z) :=
    fun R Z => (localWeightedModes_int hs n a b R Z).2
  have hrect : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := (hp : p ∈ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂)
    exact ⟨⟨hK.r_order.1.trans h1, h2⟩, ⟨by linarith [hK.z_order.1], h4⟩⟩
  have hRc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hFr : IntegrableOn Fw K.rect := (hF _ _).mono_set hrect
  have hDr : IntegrableOn Dw K.rect := (hD _ _).mono_set hrect
  have conv : ∀ (k : ℝ → ℝ) (W : ℝ × ℝ → ℂ), Set.EqOn (fun p : ℝ × ℝ => ((t p.1 * k p.2 : ℝ) : ℂ) * W p)
      (fun p => ((T p.1 * k p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * W p)) K.rect := by
    intro k W p hp
    simp only
    rw [hTt p.1 hp.1]
    push_cast
    ring
  have int_of : ∀ (k : ℝ → ℝ), Continuous k → ∀ W : ℝ × ℝ → ℂ,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * W p) K.rect →
      IntegrableOn (fun p : ℝ × ℝ => ((t p.1 * k p.2 : ℝ) : ℂ) * W p) K.rect := by
    intro k hk W hW
    refine (hW.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hk.comp continuous_snd))).continuousOn hRc).congr_fun ?_ hRm
    intro p hp
    exact (conv k W hp).symm
  refine ⟨int_of s hsc _ hFr, int_of s hsc _ hDr, fun hs1 hs0 hs2 => ?_⟩
  have hdsc : Continuous (deriv s) := hs1.continuous_deriv le_rfl
  have hw : ∀ φ χ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * Dw p :=
    fun φ χ h1 h2 h3 h4 h5 => localProductWeak hs n a b φ χ h1 h2 h3 h4 h5
  have hz := slice_zero hF hD hw hK.z_order.2.le s hs1 hs0 hs2
  have iD : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * s p.2 : ℝ) : ℂ) * Dw p) K.rect :=
    hDr.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hsc.comp continuous_snd))).continuousOn hRc
  have iF : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) K.rect :=
    hFr.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hdsc.comp continuous_snd))).continuousOn hRc
  rw [setIntegral_congr_fun hRm (conv s _), setIntegral_congr_fun hRm (conv (deriv s) _)]
  apply eq_neg_of_add_eq_zero_left
  have iDF : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * s p.2 : ℝ) : ℂ) * Dw p +
      ((T p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) K.rect := iD.add iF
  rw [← integral_add iD iF, CellBox.rect, iter_r iDF]
  have hae : ∀ᵐ r ∂(volume.restrict (Ioc K.r₁ K.r₂)),
      (∫ z in Icc K.z₁ K.z₂, (((T r * s z : ℝ) : ℂ) * Dw (r, z) + ((T r * deriv s z : ℝ) : ℂ) * Fw (r, z))) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hz] with r hr hmem
    have h0 := hr (lt_of_le_of_lt hK.r_order.1 hmem.1)
    have e : (fun z => ((T r * s z : ℝ) : ℂ) * Dw (r, z) + ((T r * deriv s z : ℝ) : ℂ) * Fw (r, z)) =
        fun z => (T r : ℂ) * (((s z : ℝ) : ℂ) * Dw (r, z) + ((deriv s z : ℝ) : ℂ) * Fw (r, z)) := by
      funext z
      push_cast
      ring
    rw [e, integral_const_mul, h0, mul_zero]
  rw [integral_Icc_eq_integral_Ioc]
  exact integral_eq_zero_of_ae hae

end LocalField

end CertCell

end Breakdown

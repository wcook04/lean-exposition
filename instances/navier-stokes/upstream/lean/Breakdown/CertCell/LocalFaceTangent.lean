import Breakdown.CertCell.LocalFieldDefs2
import Breakdown.CertCell.LocalModeWeak
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.FracCert.SecondTraceSolenoidal

open scoped ContDiff Real
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula
  CellCert.CellAnalysis.LowEntry.Internal

private theorem secondEntrySymm {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsLocalSecondOrderField v G H) :
    ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
  have hm : ∀ i j : Fin 3, AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    fun i j => (hs.measurable_second.apply_continuousLinearMap (unitVector i)).apply_continuousLinearMap
      (unitVector j)
  have hloc : ∀ i j : Fin 3, LocallyIntegrable (fun y => H y (unitVector i) (unitVector j)) volume := by
    intro i j
    have h2 : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
      refine (memLp_two_iff_integrable_sq_norm (hm i j)).2 (hs.second_two.mono' ((hm i j).norm.pow 2) ?_)
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (Finset.single_le_sum (f := fun k => ‖H y (unitVector i) (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun a => ∑ k : Fin 3, ‖H y (unitVector a) (unitVector k)‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i))
    exact h2.locallyIntegrable (by norm_num)
  have key : ∀ i j : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, φ y • H y (unitVector j) (unitVector i) =
        ∫ y, SecondTraceSolenoidalInternal.dirDeriv i (SecondTraceSolenoidalInternal.dirDeriv j φ) y • v y := by
    intro i j φ hφ
    have e1 := hs.weak_second φ hφ i j
    have e2 := hs.weak_gradient (SecondTraceSolenoidalInternal.dirDeriv j φ)
      (SecondTraceSolenoidalInternal.test_dirDeriv hφ j) i
    have e3 : ∫ y, φ y • H y (unitVector j) (unitVector i) =
        -∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i) := by
      rw [e1, neg_neg]
    rw [e3]
    exact e2.symm
  have hij : ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
    intro i j
    refine ae_eq_of_integral_contDiff_smul_eq (hloc j i) (hloc i j) fun φ hφ hcφ => ?_
    rw [key i j φ ⟨hφ, hcφ⟩, key j i φ ⟨hφ, hcφ⟩, SecondTraceSolenoidalInternal.dirDeriv_comm hφ]
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  exact hij i

private theorem spaceSumUnits (u : Space) : u = ∑ k : Fin 3, u k • unitVector k := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem bilinSymmOfUnits (M : Space →L[ℝ] Space →L[ℝ] Space)
    (h : ∀ i j : Fin 3, M (unitVector j) (unitVector i) = M (unitVector i) (unitVector j)) (u w : Space) :
    M u w = M w u := by
  rw [spaceSumUnits u, spaceSumUnits w]
  simp only [Fin.sum_univ_three, map_add, map_smul, add_apply, smul_apply]
  rw [h 0 1, h 0 2, h 1 2]
  module

private theorem frameThirdPeriodic (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird (θ + 2 * π) M a b c = frameThird θ M a b c := by
  simp only [frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem modeThirdCentred (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) : modeThird m n H a b c p = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ) := by
  unfold modeThird
  rw [per_interval]
  intro θ
  simp only [phase_per, cylPoint_per, frameThirdPeriodic]

theorem localModeThirdSwap : LocalModeThirdSwapStatement := by
  intro m v G H hs n a
  have h1 : ∀ᵐ q ∂muU, ∀ i j : Fin 3,
      H (cylArg q) (unitVector j) (unitVector i) = H (cylArg q) (unitVector i) (unitVector j) :=
    qmp.ae (secondEntrySymm hs)
  rw [muU_def] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  filter_upwards [h2] with p hp hp1
  have hp' := hp ⟨hp1, trivial⟩
  rw [modeThirdCentred, modeThirdCentred]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hp'] with θ hθ
  have hθ' : ∀ i j : Fin 3, H (cylPoint p.1 θ p.2) (unitVector j) (unitVector i) =
      H (cylPoint p.1 θ p.2) (unitVector i) (unitVector j) := hθ
  simp only [frameThird]
  rw [bilinSymmOfUnits _ hθ' (frameUnit θ 0) (frameUnit θ 2)]

end Breakdown.CertCell.LocalField

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula
  CellCert.CellAnalysis.LowEntry.Internal

private theorem rectCompact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

private theorem rectMeasurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

private theorem rectInStrip (K : CellBox) (hK : IsCellBox K) : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ :=
  prod_mono (Icc_subset_Icc hK.r_order.1 le_rfl) (Icc_subset_Icc (by linarith [hK.z_order.1, hK.z_order.2]) le_rfl)

private theorem integrableProductWeight (K : CellBox) {F : ℝ × ℝ → ℂ} {f k : ℝ → ℝ}
    (hF : IntegrableOn (fun p : ℝ × ℝ => ((f p.1 : ℝ) : ℂ) * F p) K.rect) (hk : Continuous k) :
    IntegrableOn (fun p : ℝ × ℝ => ((f p.1 * k p.2 : ℝ) : ℂ) * F p) K.rect := by
  have h := hF.continuousOn_mul (g := fun p : ℝ × ℝ => ((k p.2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hk.comp continuous_snd)).continuousOn (rectCompact K)
  refine h.congr_fun (fun p _ => ?_) (rectMeasurable K)
  simp only
  push_cast
  ring

private theorem affineWeightMode (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {X : Space → (Space →L[ℝ] Space)}
    (hX1 : AEStronglyMeasurable X volume) (hX2 : Integrable (fun y => entrySq (X y))) (a b : Fin 3) (c o : ℝ)
    (hco : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁)) :
    IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n X a b p) K.rect := by
  have gi := gradMode_int K hK m n hX1 hX2 a b
  by_cases h0 : K.r₁ = 0
  · obtain ⟨rfl, rfl⟩ : c = K.r₂ ∧ o = K.r₁ := by
      rcases hco with h | h
      · exact absurd h0 h.2.2
      · exact h
    refine IntegrableOn.congr_fun (Integrable.const_mul gi ((1 / (K.r₂ - K.r₁) : ℝ) : ℂ)) (fun p _ => ?_)
      (rectMeasurable K)
    simp only [CellBox.lineWeight, h0, if_true]
    push_cast
    ring
  · have g1 : IntegrableOn (gradMode m n X a b) K.rect := by
      refine gi.congr_fun (fun p _ => ?_) (rectMeasurable K)
      simp only [CellBox.lineWeight, h0, if_false]
      push_cast
      ring
    exact g1.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)).continuousOn
      (rectCompact K)

private theorem axialColumnSquare {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · unfold entrySq
    exact Finset.aestronglyMeasurable_sum (f := fun i y => ‖H y axialUnit (unitVector i)‖ ^ 2) Finset.univ
      fun i _ => (((hm.apply_continuousLinearMap axialUnit).apply_continuousLinearMap (unitVector i)).norm.pow 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold entrySq; positivity)]
    unfold entrySq
    exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (2 : Fin 3))

theorem localRadialStripIbp_of (hS : StripIbpStatement) : LocalRadialStripIbpStatement := by
  intro m v G H hs K hK n a c o hco
  have hr := hK.r_order
  have hz := hK.z_order
  have hstrip := localModeStripIntegrable m v G H hs n K.r₂ (-K.z₂) K.z₂
  have iV : IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect :=
    (hstrip.1 a).mono_set (rectInStrip K hK)
  have iG2 : IntegrableOn (gradMode m n G a 2) K.rect := (hstrip.2 a 2).mono_set (rectInStrip K hK)
  have iG0 := affineWeightMode K hK m n hs.measurable_gradient hs.gradient_two a 0 c o hco
  have iS : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect :=
    affineWeightMode K hK m n (hs.measurable_second.apply_continuousLinearMap axialUnit)
      (axialColumnSquare hs.measurable_second hs.second_two) a 0 c o hco
  have iV' : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a) K.rect :=
    iV.const_mul _
  have iG2' : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p) K.rect :=
    iG2.const_mul _
  refine ⟨iV'.add iG0, iG2'.add iS, fun h hh h1 h2 => ?_⟩
  have W := localModeWeakIdentity m v G H hs n a
  have e1 := hS (fun p => modeVec m n v p.1 p.2 a) (gradMode m n G a 2) (fun _ => 1 / (c - o)) K.r₁ K.r₂ K.z₁ K.z₂
    hr.1 hr.2 hz.2 contDiff_const iV' iG2' (fun ψ q1 q2 q3 => (W ψ q1 q2 q3).2.1) h hh h1 h2
  have e2 := hS (gradMode m n G a 0) (modeThird m n H a 0 2) (fun r => (r - o) / (c - o)) K.r₁ K.r₂ K.z₁ K.z₂
    hr.1 hr.2 hz.2 ((contDiff_id.sub contDiff_const).div_const _) iG0 iS (fun ψ q1 q2 q3 => (W ψ q1 q2 q3).2.2.2)
    h hh h1 h2
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have j1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
      + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) K.rect :=
    (integrableProductWeight K (f := fun _ => 1 / (c - o)) iV' hdc).add
      (integrableProductWeight K (f := fun _ => 1 / (c - o)) iG2' hh.continuous)
  have j2 : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
      + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect :=
    (integrableProductWeight K (f := fun r => (r - o) / (c - o)) iG0 hdc).add
      (integrableProductWeight K (f := fun r => (r - o) / (c - o)) iS hh.continuous)
  have e : (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) * ((deriv h p.2 : ℝ) : ℂ)
              + (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) * ((h p.2 : ℝ) : ℂ))) =
      fun p => ((((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
        + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p)
        + ((((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
        + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) := by
    funext p
    push_cast
    ring
  rw [e, integral_add j1 j2]
  have e1' : ∫ p in K.rect, ((((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
      + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) = 0 := e1
  have e2' : ∫ p in K.rect, ((((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
      + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) = 0 := e2
  rw [e1', e2', add_zero]

theorem localRadialStripIbp : LocalRadialStripIbpStatement :=
  localRadialStripIbp_of stripIbp_holds

end Breakdown.CertCell.LocalField

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula
  CellCert.CellAnalysis.LowEntry.Internal

private theorem polyEvalHeightContinuous (q : Polynomial ℝ) :
    Continuous (fun p : ℝ × ℝ => ((q.eval p.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (q.continuous.comp continuous_snd)

private theorem stripMomentByParts {c o z₁ z₂ : ℝ} (hz : z₁ < z₂) {V G0 G2 S02 S20 : ℝ × ℝ → ℂ}
    (hA : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p)
      (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂))
    (hB : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p)
      (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂))
    (hS : ∀ᵐ p ∂(volume.restrict (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂)), S20 p = S02 p)
    (hI : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h z₁ = 0 → h z₂ = 0 →
      ∫ p in Icc (min c o) (max c o) ×ˢ Icc z₁ z₂,
        ((((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((deriv h p.2 : ℝ) : ℂ)
          + (((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p) * ((h p.2 : ℝ) : ℂ)) = 0)
    (q : Polynomial ℝ) (t : ℝ → ℝ) (ht : ∀ u, t u = q.eval u) :
    radialStripMoment c o z₁ z₂ G2 S20 t =
      ((t z₂ : ℝ) : ℂ) * cornerMoment c o z₂ z₁ V G0 G2 S02
        - ((t z₁ : ℝ) : ℂ) * cornerMoment c o z₁ z₂ V G0 G2 S02
        - radialStripMoment c o z₁ z₂ V G0 (deriv t) := by
  obtain rfl : t = fun u => q.eval u := funext ht
  set R := Icc (min c o) (max c o) ×ˢ Icc z₁ z₂ with hRdef
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  set A := fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p with hAdef
  set B := fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p with hBdef
  have iA : ∀ g : ℝ × ℝ → ℂ, Continuous g → Integrable (fun p => A p * g p) (volume.restrict R) :=
    fun g hg => hA.mul_continuousOn hg.continuousOn hR
  have iB : ∀ g : ℝ × ℝ → ℂ, Continuous g → Integrable (fun p => B p * g p) (volume.restrict R) :=
    fun g hg => hB.mul_continuousOn hg.continuousOn hR
  have hz' : z₂ - z₁ ≠ 0 := sub_ne_zero.2 hz.ne'
  have hz'' : z₁ - z₂ ≠ 0 := sub_ne_zero.2 hz.ne
  have hdt : ∀ u, deriv (fun u => q.eval u) u = q.derivative.eval u := fun u => (q.hasDerivAt u).deriv
  set h : ℝ → ℝ := fun u => q.eval u - q.eval z₂ * ((u - z₁) / (z₂ - z₁)) - q.eval z₁ * ((u - z₂) / (z₁ - z₂))
    with hh
  have hdh : ∀ u, HasDerivAt h
      (q.derivative.eval u - q.eval z₂ * (1 / (z₂ - z₁)) - q.eval z₁ * (1 / (z₁ - z₂))) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (u - z₁) / (z₂ - z₁)) (1 / (z₂ - z₁)) u :=
      ((hasDerivAt_id u).sub_const z₁).div_const _
    have h0 : HasDerivAt (fun u : ℝ => (u - z₂) / (z₁ - z₂)) (1 / (z₁ - z₂)) u :=
      ((hasDerivAt_id u).sub_const z₂).div_const _
    exact ((q.hasDerivAt u).sub (h1.const_mul _)).sub (h0.const_mul _)
  have hq : ContDiff ℝ ∞ (fun u => q.eval u) := by
    rw [show (fun u => q.eval u) = fun u => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * u ^ i from
      funext fun u => q.eval_eq_sum_range u]
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)
  have hC1 : ContDiff ℝ ∞ h :=
    (hq.sub (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _))).sub
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _))
  have h1 : h z₁ = 0 := by simp only [hh]; field_simp; ring
  have h2 : h z₂ = 0 := by simp only [hh]; field_simp; ring
  have key := hI h hC1 h1 h2
  have cP1 : Continuous (fun p : ℝ × ℝ => (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)) := by fun_prop
  have cP0 : Continuous (fun p : ℝ × ℝ => (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) := by fun_prop
  have ekey : (fun p : ℝ × ℝ => A p * ((deriv h p.2 : ℝ) : ℂ) + B p * ((h p.2 : ℝ) : ℂ)) =
      fun p => ((A p * ((q.derivative.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        + ((B p * ((q.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
          + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))) := by
    funext p
    rw [(hdh p.2).deriv]
    simp only [hh]
    push_cast
    ring
  have iAD : Integrable (fun p => A p * ((q.derivative.eval p.2 : ℝ) : ℂ)) (volume.restrict R) :=
    iA _ (polyEvalHeightContinuous q.derivative)
  have iBT : Integrable (fun p => B p * ((q.eval p.2 : ℝ) : ℂ)) (volume.restrict R) :=
    iB _ (polyEvalHeightContinuous q)
  have iB1 : Integrable (fun p => B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)) (volume.restrict R) := iB _ cP1
  have iB0 : Integrable (fun p => B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) (volume.restrict R) := iB _ cP0
  have hA' : Integrable A (volume.restrict R) := hA
  rw [ekey] at key
  have e1 : (∫ p in R, (((A p * ((q.derivative.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        + ((B p * ((q.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
          + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))))) =
      ((∫ p in R, A p * ((q.derivative.eval p.2 : ℝ) : ℂ))
          + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * (∫ p in R, A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * ∫ p in R, A p)
        + ((∫ p in R, B p * ((q.eval p.2 : ℝ) : ℂ))
          + (-((q.eval z₂ : ℝ) : ℂ)) * (∫ p in R, B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ))
          + (-((q.eval z₁ : ℝ) : ℂ)) * ∫ p in R, B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) := by
    have jA1 : Integrable (fun p => A p * ((q.derivative.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p) (volume.restrict R) := iAD.add (hA'.const_mul _)
    have jA2 : Integrable (fun p => (A p * ((q.derivative.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p) + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        (volume.restrict R) := jA1.add (hA'.const_mul _)
    have jB1 : Integrable (fun p => B p * ((q.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ))) (volume.restrict R) :=
      iBT.add (iB1.const_mul _)
    have jB2 : Integrable (fun p => (B p * ((q.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
        + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))) (volume.restrict R) :=
      jB1.add (iB0.const_mul _)
    rw [integral_add jA2 jB2, integral_add jA1 (hA'.const_mul _), integral_add iAD (hA'.const_mul _),
      integral_add jB1 (iB0.const_mul _), integral_add iBT (iB1.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e1] at key
  have eC : ∀ cz oz : ℝ, cornerMoment c o cz oz V G0 G2 S02 = edgeSign c o * edgeSign cz oz *
      ∫ p in Icc (min c o) (max c o) ×ˢ Icc (min cz oz) (max cz oz),
        (A p * ((1 / (cz - oz) : ℝ) : ℂ) + B p * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) := by
    intro cz oz
    unfold cornerMoment
    congr 2
    funext p
    simp only [hAdef, hBdef]
    ring
  have eV : radialStripMoment c o z₁ z₂ V G0 (deriv fun u => q.eval u) =
      edgeSign c o * ∫ p in R, A p * ((q.derivative.eval p.2 : ℝ) : ℂ) := by
    unfold radialStripMoment
    congr 2
    funext p
    rw [hdt]
  have eL : radialStripMoment c o z₁ z₂ G2 S20 (fun u => q.eval u) =
      edgeSign c o * ∫ p in R, B p * ((q.eval p.2 : ℝ) : ℂ) := by
    unfold radialStripMoment
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hS] with p hp
    simp only [hBdef]
    rw [hp]
  have s1 : edgeSign z₂ z₁ = 1 := by simp [edgeSign, hz]
  have s0 : edgeSign z₁ z₂ = -1 := by simp [edgeSign, not_lt.2 hz.le]
  rw [eL, eV, eC, eC, min_eq_right hz.le, max_eq_left hz.le, min_eq_left hz.le, max_eq_right hz.le, s1, s0,
    integral_add (hA'.mul_const _) iB1, integral_add (hA'.mul_const _) iB0, integral_mul_const, integral_mul_const]
  beta_reduce
  push_cast at key ⊢
  linear_combination (edgeSign c o) * key

private theorem offAxisAe : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h0 : volume (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp h
  exact hp ⟨h, trivial⟩

private theorem aeOnRectOfPositive {K : CellBox} (hK : IsCellBox K) {S20 S02 : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → S20 p = S02 p) : ∀ᵐ p ∂(volume.restrict K.rect), S20 p = S02 p := by
  have hm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae offAxisAe, ae_restrict_mem hm] with p h1 h2 h3
  exact h1 (lt_of_le_of_ne (hK.r_order.1.trans h3.1.1) (Ne.symm h2))

theorem localRadialTangent_of (hI : LocalRadialStripIbpStatement) : LocalRadialTangentStatement := by
  intro k N c K S B L hL x hx n e a t he hax ht
  obtain ⟨q, hq⟩ := ht
  have hK := hL.box_valid
  have hf : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have hr : K.r₁ < K.r₂ := hK.r_order.2
  have hsw := aeOnRectOfPositive hK (localModeThirdSwap L.order _ _ _ hf n a)
  unfold CellLayout.cornerValue CellLayout.sideVelocityValue radialFaceMoment CellLayout.sideRadialIndex
  rw [if_pos he]
  simp only [CellLayout.gradModeOf, CellLayout.secondModeOf, hL.box_eq]
  obtain he0 | he1 : e.val = 0 ∨ e.val = 1 := by omega
  · have hne := hax he0
    simp only [he0, if_true, eq_false (show (0 : Fin 2) ≠ 1 by decide), if_false]
    have hRr : Icc (min K.r₁ K.r₂) (max K.r₁ K.r₂) ×ˢ Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_left hr.le, max_eq_right hr.le]; rfl
    obtain ⟨i1, i2, i3⟩ := hI L.order _ _ _ hf K hK n a K.r₁ K.r₂ (Or.inl ⟨rfl, rfl, hne⟩)
    rw [← hRr] at i1 i2 i3 hsw
    exact stripMomentByParts hz i1 i2 hsw i3 q t hq
  · simp only [he1, one_ne_zero, if_false, if_true, eq_false (show (1 : Fin 2) ≠ 0 by decide)]
    have hRr : Icc (min K.r₂ K.r₁) (max K.r₂ K.r₁) ×ˢ Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_right hr.le, max_eq_left hr.le]; rfl
    obtain ⟨i1, i2, i3⟩ := hI L.order _ _ _ hf K hK n a K.r₂ K.r₁ (Or.inr ⟨rfl, rfl⟩)
    rw [← hRr] at i1 i2 i3 hsw
    exact stripMomentByParts hz i1 i2 hsw i3 q t hq

theorem localRadialTangent : LocalRadialTangentStatement :=
  localRadialTangent_of localRadialStripIbp

end Breakdown.CertCell.LocalField

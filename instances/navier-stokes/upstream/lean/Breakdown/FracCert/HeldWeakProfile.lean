import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.Frac.NNicePairing

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldWeakProfileInternal

theorem residual_eq {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (u : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (Q : Space → Space) (y : Space) :
    d.fullField α p u G H P κ y + G y (u y) + d.defect α p y + Q y =
      driftField α (d.rotationRate p) u G y
        + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
        + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + u y)
        + ∑ i, d.heldMultiplier p κ i • d.actuator i y + Q y := by
  simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField,
    FracCertData.defect, symProduct, FracCertData.heldMultiplier, add_smul, Finset.sum_add_distrib,
    add_apply, map_add, smul_smul]
  norm_num
  abel

theorem integrable_inner_of {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

end HeldWeakProfileInternal

open HeldWeakProfileInternal

theorem heldWeakProfile_of (h1 : EmbedWeakStatement) (h2 : HeldNonzeroStatement)
    (h3 : GradientOrthogonalStatement) (s1 : ProfileEmbedDataStatement) (s2 : WeakPowerNiceStatement)
    (s3 : DriftNicePairingStatement) (s4 : HeldQuadraticL2Statement) (s5 : NiceSolenoidalStatement) :
    HeldWeakProfileStatement := by
  intro α hα1 hα2 k N d hd p hp u G H P κ hsol hsize hzero
  obtain ⟨m1, m6, mG, iG, wG, dG⟩ := s1 α hα1 hα2 d hd p hp
  have hs := hsol.state.second
  obtain ⟨U₁, hU₁v, hU₁g⟩ := h1 (d.profile p) (d.gradProfile p) m1 m6 mG iG wG dG
  obtain ⟨U₂, hU₂v, hU₂g⟩ := h1 u G hs.measurable_velocity hs.velocity_six hs.measurable_gradient
    hs.gradient_two hs.weak_gradient hs.divergence
  have hv : (Freq.velocity (U₁ + U₂) : Space → Space) =ᵐ[volume] fun y => d.profile p y + u y := by
    rw [map_add]
    filter_upwards [Lp.coeFn_add (Freq.velocity U₁) (Freq.velocity U₂), hU₁v, hU₂v] with y h hy1 hy2
    rw [h, Pi.add_apply, hy1, hy2]
  refine ⟨d.rotationRate p, U₁ + U₂, ?_, ?_⟩
  · intro h0
    apply h2 α hα1 hα2 d hd p hp u G H P κ hsol hsize
    rw [h0, map_zero] at hv
    filter_upwards [hv, Lp.coeFn_zero Space 6 volume] with y h h'
    rw [← h, h']
    rfl
  intro φ hφ
  have hg : ∀ j, (Freq.partialX j (U₁ + U₂) : Space → Space) =ᵐ[volume]
      fun y => (d.gradProfile p y + G y) (unitVector j) := by
    intro j
    rw [map_add]
    filter_upwards [Lp.coeFn_add (Freq.partialX j U₁) (Freq.partialX j U₂), hU₁g j, hU₂g j]
      with y h hy1 hy2
    rw [h, Pi.add_apply, hy1, hy2]
    rfl
  have htri : Freq.trilinear (U₁ + U₂) (U₁ + U₂) φ =
      ∫ y, inner ℝ ((d.gradProfile p y + G y) (d.profile p y + u y)) (φ y) := by
    unfold Freq.trilinear
    apply integral_congr_ae
    have hg' : ∀ᵐ y ∂volume, ∀ j, (Freq.partialX j (U₁ + U₂) : Space → Space) y =
        (d.gradProfile p y + G y) (unitVector j) := ae_all_iff.2 hg
    filter_upwards [hv, hg'] with y h1y h2y
    simp only [h1y, h2y]
    exact Freq.Internal.NicePairing.sum_coord_inner _ _ _
  obtain ⟨Q, hQg, hQ⟩ := hsol.equation
  have hE : ∀ᵐ y ∂volume, driftField α (d.rotationRate p) u G y
      + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
      + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + u y) + Q y = 0 := by
    filter_upwards [hQ] with y hy
    rw [residual_eq, hzero] at hy
    simpa using hy
  have hdU := hsol.state.drift
  have hdW := hd.profile_drift p hp
  have hP := hsol.state.power.1
  have hPp := (hd.profile_power p hp).1
  have hq := s4 α hα1 hα2 d hd p hp u G H hs
  have hQ2 : MemLp Q 2 volume := by
    refine ((((hdU.add hdW).add hP).add hPp).add hq).neg.ae_eq ?_
    filter_upwards [hE] with y hy
    exact neg_eq_of_add_eq_zero_right hy
  have hφs := s5 φ hφ
  have hφ2 := hφs.1
  have hQ0 := h3 Q φ hQg hQ2 hφs
  have hα0 : 0 < α := by linarith
  obtain ⟨iU, eU⟩ := s3 α (d.rotationRate p) hα0 u G hs.measurable_velocity hs.velocity_six
    hs.measurable_gradient hs.gradient_two hs.weak_gradient φ hφ
  obtain ⟨iW, eW⟩ := s3 α (d.rotationRate p) hα0 (d.profile p) (d.gradProfile p) m1 m6 mG iG wG φ hφ
  obtain ⟨jU, fU⟩ := s2 α hα1 hα2 u P hs.measurable_velocity hs.velocity_six hsol.state.power φ hφ
  obtain ⟨jW, fW⟩ := s2 α hα1 hα2 (d.profile p) (d.profilePower p) m1 m6 (hd.profile_power p hp) φ hφ
  have ia := integrable_inner_of hdU hφ2
  have ib := integrable_inner_of hdW hφ2
  have ic := integrable_inner_of hP hφ2
  have id' := integrable_inner_of hPp hφ2
  have ie := integrable_inner_of hq hφ2
  have iq := integrable_inner_of hQ2 hφ2
  have hsum : ∫ y, inner ℝ (driftField α (d.rotationRate p) u G y
      + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
      + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + u y) + Q y) (φ y) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hE] with y hy
    rw [hy, inner_zero_left]
    rfl
  simp only [inner_add_left] at hsum
  have e5 := integral_add ((((ia.add ib).add ic).add id').add ie) iq
  have e4 := integral_add (((ia.add ib).add ic).add id') ie
  have e3 := integral_add ((ia.add ib).add ic) id'
  have e2 := integral_add (ia.add ib) ic
  have e1 := integral_add ia ib
  simp only [Pi.add_apply] at e1 e2 e3 e4 e5
  rw [e5, e4, e3, e2, e1] at hsum
  have hD : ∫ y, inner ℝ ((Freq.velocity (U₁ + U₂) : Space → Space) y)
      (FracCert.driftAdjoint α (d.rotationRate p) φ y) =
      (∫ y, inner ℝ (d.profile p y) (FracCert.driftAdjoint α (d.rotationRate p) φ y)) +
        ∫ y, inner ℝ (u y) (FracCert.driftAdjoint α (d.rotationRate p) φ y) := by
    rw [← integral_add iW iU]
    apply integral_congr_ae
    filter_upwards [hv] with y hy
    rw [hy, inner_add_left]
  have hA : ∫ y, inner ℝ ((Freq.velocity (U₁ + U₂) : Space → Space) y) (fractionalPowerAt α φ y) =
      (∫ y, inner ℝ (d.profile p y) (fractionalPowerAt α φ y)) +
        ∫ y, inner ℝ (u y) (fractionalPowerAt α φ y) := by
    rw [← integral_add jW jU]
    apply integral_congr_ae
    filter_upwards [hv] with y hy
    rw [hy, inner_add_left]
  rw [hD, hA, htri]
  linarith

theorem heldWeakProfile_of_power (h1 : EmbedWeakStatement) (h2 : HeldNonzeroStatement)
    (h3 : GradientOrthogonalStatement) (h4 : QuadraticSquareIntegrableStatement) (h5 : WeakPowerNiceStatement) :
    HeldWeakProfileStatement :=
  heldWeakProfile_of h1 h2 h3 profileEmbedData h5 driftNicePairing (heldQuadraticL2_of h4) niceSolenoidal

theorem heldWeakProfile (h1 : EmbedWeakStatement) (h2 : HeldNonzeroStatement)
    (h3 : GradientOrthogonalStatement) (h4 : QuadraticSquareIntegrableStatement) : HeldWeakProfileStatement :=
  heldWeakProfile_of_power h1 h2 h3 h4 weakPowerNice

end SteadyCert

end Breakdown

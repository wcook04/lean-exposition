import Breakdown.FracCert.StMildProfile
import Breakdown.FracCert.FlowPairing
import Breakdown.Frac.RMildOfWeak
import Breakdown.Frac.RExports
import Breakdown.Frac.NNiceField
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.NNiceEmbed
import Breakdown.Frac.RBilinDilate
import Breakdown.Frac.RDilation
import Breakdown.Frac.RHeat
import Breakdown.Frac.PAxial
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.BilinRotate
import Breakdown.FreqTr.VelocityInjective
import Breakdown.FreqTr.VelocityRotate
import Breakdown.FreqTr.PairingEmbed
import Breakdown.FreqTr.MildOfWeak
import Breakdown.FreqTr.Rotation
import Breakdown.FreqTr.BilinTestFormula

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracInternal.MildProfileOrbit

open Breakdown.Freq Breakdown.FracCert

def vpair (x : X) (φ : Space → Space) : ℝ := ∫ y, inner ℝ ((velocity x : Space → Space) y) (φ y)

theorem vpair_smul (x : X) (c : ℝ) (φ : Space → Space) : vpair x (c • φ) = c * vpair x φ := by
  unfold vpair
  rw [← integral_const_mul]
  congr 1
  funext y
  rw [Pi.smul_apply, inner_smul_right]

theorem exists_negTrace_eq {ρ : Space → Space} (hρ : IsNiceField ρ) : ∃ ρ', IsNiceField ρ' ∧ negSsp ρ' = ρ := by
  obtain ⟨m, hm, rfl⟩ := hρ
  have hm' : IsNiceSymbol (fun ξ => (sspFactor ξ)⁻¹ • m ξ) := by
    refine Freq.FracInternal.NiceEmbed.isNiceSymbol_smul hm _ (fun ξ hξ => ?_)
      (fun ξ => by simp [sspFactor, norm_neg])
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hne : sspFactor ξ ≠ 0 := by unfold sspFactor; positivity
    have hcd : ContDiff ℝ ∞ sspFactor := by
      unfold sspFactor
      exact contDiff_const.mul (contDiff_norm_sq ℝ)
    exact hcd.contDiffAt.inv hne
  refine ⟨_, ⟨_, hm', rfl⟩, ?_⟩
  rw [Freq.FracInternal.NiceEmbed.negTraceSecondDeriv_niceField hm']
  congr 1
  funext ξ
  by_cases h : ξ = 0
  · obtain ⟨-, -, ⟨r, hr, hz⟩, -, -⟩ := hm
    have h0 : m ξ = 0 := hz ξ (by rw [h, norm_zero]; exact hr)
    rw [h0, smul_zero, smul_zero]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h
    have hne : sspFactor ξ ≠ 0 := by unfold sspFactor; positivity
    rw [smul_smul, mul_inv_cancel₀ hne, one_smul]

open Freq.Internal.VelocityInjective in
theorem vpair_negTrace {ρ : Space → Space} (hρ : IsNiceField ρ) (x : X) :
    vpair x (negSsp ρ) = inner ℝ x (embedX ρ) := by
  obtain ⟨-, hρd, hLn, -, -⟩ := niceFieldProps (5 / 4) (by norm_num) (by norm_num) ρ hρ
  obtain ⟨S, hS⟩ := Freq.Internal.NicePairing.rapid_of_nice hLn
  have hG : MemLp (negSsp ρ) (6 / 5) volume := by rw [← hS]; exact S.memLp _ _
  have hspec : VelocitySpec velocity := Freq.Internal.BilinTestFormula.velocity_spec velocity_holds
  let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
  have hPe : ∀ y : X, vpair y (negSsp ρ) = P (velocity y) (hG.toLp _) := by
    intro y
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with z hz
    rw [hz]
    rfl
  have heq : (fun y : X => inner ℝ y (embedX ρ)) = fun y => P (velocity y) (hG.toLp _) := by
    apply Continuous.ext_on testDense_holds.2 (by fun_prop)
      ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds y hy
    show inner ℝ (embedX ψ) (embedX ρ) = P (velocity (embedX ψ)) (hG.toLp _)
    rw [← hPe]
    have hψd : IsDecayField ψ := Freq.Internal.VelocityRotate.decay_of_test hψ
    rw [pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2 ψ ρ hψd hρd,
      nicePairingByParts ψ ρ hψd hρ]
    unfold fieldPairing vpair
    apply integral_congr_ae
    filter_upwards [(hspec ψ hψ) ▸ Freq.Internal.VelocityInjective.toLp6_test ψ hψ] with z hz
    rw [hz]
  rw [hPe, ← congrFun heq x]

theorem rep_frac {α : ℝ} (hα : 1 < α) (hα2 : α < 3 / 2) {ρ : Space → Space} (hρ : IsNiceField ρ) :
    ∃ y z : X, (∀ x, vpair x ρ = inner ℝ x y) ∧
      (∀ x, vpair x (fractionalPowerAt α ρ) = inner ℝ x z) ∧ IsFracOf α y z := by
  obtain ⟨ρ', hρ', rfl⟩ := exists_negTrace_eq hρ
  obtain ⟨-, -, -, hAn, hcomm⟩ := niceFieldProps α hα hα2 ρ' hρ'
  refine ⟨embedX ρ', embedX (fractionalPowerAt α ρ'), fun x => vpair_negTrace hρ' x, fun x => ?_,
    (fracNiceEmbedPower α hα hα2 niceEmbedSymbol
      (fun m hm => fracPower_niceField α hα hα2 m hm) ρ' hρ').2⟩
  rw [hcomm]
  exact vpair_negTrace hAn x

theorem isFracOf_unique {α : ℝ} {χ ψ ψ' : X} (h : IsFracOf α χ ψ) (h' : IsFracOf α χ ψ') :
    ψ = ψ' := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [h, h'] with ξ a b
  rw [a, b]

theorem tri_smul (u v : X) (c : ℝ) (w : Space → Space) :
    trilinear u v (c • w) = c * trilinear u v w := by
  unfold trilinear
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, inner_smul_right, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => by ring

set_option maxHeartbeats 1000000 in
theorem tri_dil {α : ℝ} (hα : 1 < α) {l : ℝ} (hl : 0 < l) (u v : X) (w : Space → Space) :
    trilinear (fracDilX α l u) (fracDilX α l v) w =
      l ^ (2 - 1 / (2 * α)) * ((l ^ (1 / (2 * α))) ^ 3)⁻¹ *
        trilinear u v (fun z => w ((l ^ (1 / (2 * α)))⁻¹ • z)) := by
  have h2 := fracDilationAlgebra_holds α hα
  have hU := fracVelocityDilate_holds α hα l hl u
  have hV : ∀ᵐ y ∂volume, ∀ j : Fin 3, (partialX j (fracDilX α l v) : Space → Space) y =
      l • (partialX j v : Space → Space) (l ^ (1 / (2 * α)) • y) :=
    ae_all_iff.2 (fun j => FracInternal.BilinDilate.partialX_fracDilX h2 hl j v)
  have hk' : l ^ (2 - 1 / (2 * α)) = l ^ (1 - 1 / (2 * α)) * l := by
    rw [show (2 - 1 / (2 * α)) = (1 - 1 / (2 * α)) + 1 by ring, Real.rpow_add hl, Real.rpow_one]
  generalize hcdef : l ^ (1 / (2 * α)) = c at hV ⊢
  have hc : 0 < c := hcdef ▸ Real.rpow_pos_of_pos hl _
  have hsc : ∀ f : Space → Space, ∀ x, scaleField α l f x = l ^ (1 - 1 / (2 * α)) • f (c • x) := by
    intro f x
    rw [← hcdef]
    rfl
  generalize l ^ (2 - 1 / (2 * α)) = k at hk' ⊢
  generalize l ^ (1 - 1 / (2 * α)) = q at hk' hsc
  let G : Space → ℝ := fun y => ∑ j : Fin 3, (velocity u : Space → Space) y j *
    inner ℝ ((partialX j v : Space → Space) y) (w (c⁻¹ • y))
  have e1 : (fun x => ∑ j : Fin 3, (velocity (fracDilX α l u) : Space → Space) x j *
      inner ℝ ((partialX j (fracDilX α l v) : Space → Space) x) (w x)) =ᵐ[volume]
      fun x => k * G (c • x) := by
    filter_upwards [hU, hV] with x hx1 hx2
    show _ = k * ∑ j : Fin 3, (velocity u : Space → Space) (c • x) j *
      inner ℝ ((partialX j v : Space → Space) (c • x)) (w (c⁻¹ • c • x))
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul, hx1, hx2 j, hsc, hk']
    simp only [PiLp.smul_apply, smul_eq_mul, real_inner_smul_left]
    ring
  unfold trilinear
  exact (integral_congr_ae e1).trans (FracInternal.BilinDilate.integral_scale' (k := k) hc G)

set_option maxHeartbeats 1000000 in
theorem tri_sim {α : ℝ} (hα : 1 < α) (a : ℝ) {μ : ℝ} (hμ : 0 < μ) (U : X) (ψ : Space → Space) :
    trilinear U U (simAdj α a μ ψ) = μ * trilinear (simOp α a μ U) (simOp α a μ U) ψ := by
  have hRs : axialRotation (-(a * Real.log μ)) = (axialRotation (a * Real.log μ)).symm := by
    rw [axialRotationSpec.2.2.2.1]
  have hsim : simOp α a μ U = fracDilX α μ⁻¹ (rotX (axialRotation (a * Real.log μ)) U) := rfl
  have hadj : simAdj α a μ ψ = pushForward (axialRotation (a * Real.log μ)).symm
      (μ ^ (4 * (1 / (2 * α)) - 1) • fun y => ψ (μ ^ (1 / (2 * α)) • y)) := by
    unfold simAdj
    rw [hRs]
    rfl
  rw [hadj, hsim]
  generalize axialRotation (a * Real.log μ) = R
  have hpush : pushForward R (pushForward R.symm
      (μ ^ (4 * (1 / (2 * α)) - 1) • fun y => ψ (μ ^ (1 / (2 * α)) • y))) =
      μ ^ (4 * (1 / (2 * α)) - 1) • fun y => ψ (μ ^ (1 / (2 * α)) • y) := by
    funext y
    simp [pushForward]
  have hrot := Freq.Internal.BilinRotate.trilinear_rot rotation_holds fieldOpRealized_holds
    velocityCov_holds.1 R U U (pushForward R.symm
      (μ ^ (4 * (1 / (2 * α)) - 1) • fun y => ψ (μ ^ (1 / (2 * α)) • y)))
  rw [hpush] at hrot
  rw [← hrot, tri_smul, tri_dil hα (inv_pos.2 hμ) (rotX R U) (rotX R U) ψ]
  have hc : ((μ⁻¹) ^ (1 / (2 * α)))⁻¹ = μ ^ (1 / (2 * α)) := by
    rw [Real.inv_rpow hμ.le, inv_inv]
  rw [hc]
  have hpow : μ * ((μ⁻¹) ^ (2 - 1 / (2 * α)) * (((μ⁻¹) ^ (1 / (2 * α))) ^ 3)⁻¹) =
      μ ^ (4 * (1 / (2 * α)) - 1) := by
    rw [Real.inv_rpow hμ.le, Real.inv_rpow hμ.le, inv_pow, inv_inv, ← Real.rpow_neg hμ.le,
      ← Real.rpow_mul_natCast hμ.le, ← Real.rpow_add hμ]
    conv_lhs => arg 1; rw [← Real.rpow_one μ]
    rw [← Real.rpow_add hμ]
    congr 1
    push_cast
    ring
  rw [← hpow]
  ring

set_option maxHeartbeats 1000000 in
theorem simOp_coe {α : ℝ} (hα : 1 < α) (a : ℝ) {μ : ℝ} (hμ : 0 < μ) (x : X) :
    (simOp α a μ x : L2C) =
      SteadyCert.flowOp (1 / (2 * α)) a (1 - 3 / (2 * α)) (-Real.log μ) (x : L2C) := by
  have h2 := fracDilationAlgebra_holds α hα
  set R := axialRotation (a * Real.log μ) with hR
  have hl : 0 < μ⁻¹ := inv_pos.2 hμ
  have hc : (μ⁻¹) ^ (-(1 / (2 * α))) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
  have hsim : simOp α a μ x = fracDilX α μ⁻¹ (rotX R x) := rfl
  have hrot : ((rotX R x : X) : L2C) =ᵐ[volume] fun ξ => rotC R ((x : L2C) (R.symm ξ)) := by
    rw [Freq.Internal.Rotation.rotX_coe fieldOpRealized_holds R x]
    exact Freq.Internal.Rotation.rotL2_realized fieldOpRealized_holds R (x : L2C)
  rw [hsim, h2.2.2.2.2 μ⁻¹ hl]
  apply Lp.ext
  filter_upwards [Freq.FracInternal.Dilation.fracDilL2_ae (α := α) hl ((rotX R x : X) : L2C),
    Freq.Internal.Rotation.ae_comp (Freq.Internal.Rotation.qmp_smul hc) hrot,
    SteadyCert.Internal.FlowPairing.flowOp_ae (1 / (2 * α)) a (1 - 3 / (2 * α)) (-Real.log μ)
      (x : L2C)] with ξ e1 e2 e3
  rw [e1, e3, e2]
  simp only [SteadyCert.flowPull, SteadyCert.flowValue,
    SteadyCert.Internal.FlowPairing.flowLin_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply]
  have hA : -(a * -Real.log μ) = a * Real.log μ := by ring
  have hB : (μ⁻¹) ^ (1 - 3 / (2 * α)) = Real.exp ((1 - 3 / (2 * α)) * -Real.log μ) := by
    rw [Real.inv_rpow hμ.le, ← Real.rpow_neg hμ.le, Real.rpow_def_of_pos hμ]
    congr 1
    ring
  have hC : (μ⁻¹) ^ (-(1 / (2 * α))) = Real.exp (-(1 / (2 * α) * -Real.log μ)) := by
    rw [Real.inv_rpow hμ.le, ← Real.rpow_neg hμ.le, neg_neg, Real.rpow_def_of_pos hμ]
    congr 1
    ring
  have hD : axialRotation (a * -Real.log μ) = R.symm := by
    rw [hR, axialRotationSpec.2.2.2.1]
    congr 1
    ring
  rw [hA, hB, hC, hD, map_smul]

theorem simOp_cont {α : ℝ} (hα : 1 < α) (a : ℝ) (x : X) :
    ContinuousOn (fun s => simOp α a (1 - s) x) (Iio 1) := by
  rw [Topology.IsInducing.subtypeVal.continuousOn_iff]
  have hf : ContinuousOn (fun s : ℝ => -Real.log (1 - s)) (Iio 1) :=
    ((continuousOn_const.sub continuousOn_id).log fun s hs => (sub_pos.2 hs).ne').neg
  have hg := (SteadyCert.flowContinuity (1 / (2 * α)) a (1 - 3 / (2 * α)) (x : L2C)).comp_continuousOn hf
  refine hg.congr fun s hs => ?_
  exact simOp_coe hα a (sub_pos.2 hs) x

theorem alg_step {μ D I Q K : ℝ} (hμ : μ ≠ 0) (e : D + μ * I + μ * Q = 0) (hK : K = -Q) :
    μ⁻¹ * D + I = K := by
  have hD : D = -(μ * I) - μ * Q := by linarith
  rw [hK, hD]
  field_simp
  ring

set_option maxHeartbeats 8000000 in
theorem mild_identity {α : ℝ} (hα : 1 < α) (hα2 : α < 5 / 4) (h1 : NiceHeatStatement)
    (h3 : BilinPairingStatement) (h4 : PowerSimAdjStatement)
    (h5 : SimAdjPairingStatement) (h6 : SimAdjDerivStatement) (h7 : NiceSimAdjClosedStatement)
    (h9 : SimOpComposeStatement) {a : ℝ} {U : X} (hU : IsWeakRotatingProfile α a U)
    {T : ℝ} (hT0 : 0 ≤ T) (hT1 : T < 1) (ub : ℝ → X) (hub : ∀ s, ub s = simOp α a (1 - s) U)
    (hint : IntervalIntegrable (fun s => fracBilinX α (T - s) (ub s) (ub s)) volume 0 T)
    (φ : Space → Space) (hφ : IsNiceField φ) :
    vpair (ub T - fracHeatX α T U - ∫ s in (0 : ℝ)..T, fracBilinX α (T - s) (ub s) (ub s)) φ = 0 := by
  have hα32 : α < 3 / 2 := by linarith
  have h0 : (0 : ℝ) < α := by linarith
  have hH := fracHeatSemigroup α
  obtain ⟨y0, -, hy0, -, -⟩ := rep_frac hα hα32 hφ
  have hcont : ContinuousOn ub (Icc 0 T) := by
    have e : ub = fun s => simOp α a (1 - s) U := funext hub
    rewrite [e]
    exact (simOp_cont hα a U).mono fun s hs => lt_of_le_of_lt hs.2 hT1
  obtain ⟨w, hw⟩ : ∃ w : ℝ → X, ∀ r, w r = fracHeatX α (T - r) y0 := ⟨_, fun _ => rfl⟩
  have hrep : ∀ s, s ≤ T → ∀ x : X, vpair x (heatField α (T - s) φ) = inner ℝ x (w s) := by
    intro s hs x
    have e := (h1 α (T - s) hα (sub_nonneg.2 hs) φ hφ).2 x
    rewrite [hw]
    exact e.symm.trans ((hy0 _).trans (hH.2.2.2.2.1 _ x y0))
  have hderiv : ∀ s ∈ Ioo 0 T, HasDerivAt (fun r => inner ℝ (ub r) (w r))
      (inner ℝ (fracBilinX α (T - s) (ub s) (ub s)) y0) s := by
    intro s hs
    have hτ : 0 < T - s := sub_pos.2 hs.2
    have hs1 : s < 1 := lt_trans hs.2 hT1
    have hμ : 0 < 1 - s := sub_pos.2 hs1
    obtain ⟨hf, hhf⟩ : ∃ hf, hf = heatField α (T - s) φ := ⟨_, rfl⟩
    have hhn : IsNiceField hf := hhf ▸ (h1 α (T - s) hα hτ.le φ hφ).1
    have hrep' : ∀ x : X, vpair x hf = inner ℝ x (w s) := hhf ▸ hrep s hs.2.le
    have hwd : HasDerivAt w (FracInternal.MildWeak.aHeatX α (T - s) y0) s := by
      have e : w = fun r => fracHeatX α (T - r) y0 := funext hw
      rewrite [e]
      have hl0 : HasDerivAt (fun r : ℝ => T - r) (-1) s := (hasDerivAt_id' s).const_sub T
      have := (FracInternal.MildWeak.frac_heat_hasDerivAt h0 hH hτ y0).scomp s hl0
      simpa [Function.comp_def] using this
    have hd : HasDerivAt (fun r => inner ℝ (ub r) (w s))
        (vpair U ((1 - s)⁻¹ • driftAdjoint α a (simAdj α a (1 - s) hf))) s := by
      have := h6 α a hα U hf hhn s hs1
      refine this.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hs1] with r hr
      refine (hrep' (ub r)).symm.trans ?_
      rewrite [hub]
      exact h5 α a (1 - r) hα (sub_pos.2 hr) U hf hhn
    have hm := Freq.Internal.MildOfWeak.hasDerivAt_inner_moving
      (hcont.continuousAt (Icc_mem_nhds hs.1 hs.2)) hwd hd
    refine hm.congr_deriv ?_
    have hχn : IsNiceField (simAdj α a (1 - s) hf) := h7 α a (1 - s) h0 hμ hf hhn
    have weak := hU.2 _ hχn
    obtain ⟨-, -, -, hAn, -⟩ := niceFieldProps α hα hα32 hf hhn
    obtain ⟨y1, z1, hy1, hz1, hfr⟩ := rep_frac hα hα32 hhn
    have hyw : y1 = w s := ext_inner_left ℝ fun x => ((hy1 x).symm.trans (hrep' x))
    rewrite [hyw, hw] at hfr
    have hz : z1 = FracInternal.MildWeak.aHeatX α (T - s) y0 :=
      isFracOf_unique hfr (FracInternal.MildWeak.isFracOf_heat h0 hH hτ y0)
    have hA : vpair U (fractionalPowerAt α (simAdj α a (1 - s) hf)) =
        (1 - s) * inner ℝ (ub s) (FracInternal.MildWeak.aHeatX α (T - s) y0) := by
      rewrite [h4 α a (1 - s) hα hμ hf hhn, vpair_smul, ← hz, ← hz1, hub]
      congr 1
      exact (h5 α a (1 - s) hα hμ U _ hAn).symm
    have hT : trilinear U U (simAdj α a (1 - s) hf) = (1 - s) * trilinear (ub s) (ub s) hf := by
      rewrite [hub]
      exact tri_sim hα a hμ U hf
    have hK : inner ℝ (fracBilinX α (T - s) (ub s) (ub s)) y0 = -trilinear (ub s) (ub s) hf := by
      rewrite [← hy0, hhf]
      exact h3 α (T - s) hα hτ (ub s) φ hφ
    have e : vpair U (driftAdjoint α a (simAdj α a (1 - s) hf)) +
        vpair U (fractionalPowerAt α (simAdj α a (1 - s) hf)) +
        trilinear U U (simAdj α a (1 - s) hf) = 0 := weak
    rewrite [hA, hT] at e
    rewrite [vpair_smul]
    exact alg_step hμ.ne' e hK
  have hΦc : ContinuousOn (fun r => inner ℝ (ub r) (w r)) (Icc 0 T) := by
    refine hcont.inner ?_
    have e : w = fun r => fracHeatX α (T - r) y0 := funext hw
    rewrite [e]
    refine (hH.2.2.2.1 y0).comp (continuous_const.sub continuous_id).continuousOn ?_
    intro r hr
    simp only [mem_Ici]
    linarith [hr.2]
  have hfi : IntervalIntegrable (fun s => inner ℝ (fracBilinX α (T - s) (ub s) (ub s)) y0)
      volume 0 T := ⟨hint.1.inner_const y0, hint.2.inner_const y0⟩
  have hF := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT0 hΦc hderiv hfi
  rewrite [← Freq.Internal.MildOfWeak.inner_intervalIntegral hint y0] at hF
  have hwT : w T = y0 := by
    have h00 : fracHeatX α (T - T) y0 = y0 := by
      rw [show T - T = 0 from sub_self T, hH.1]
      rfl
    exact (hw T).trans h00
  have hw0 : w 0 = fracHeatX α T y0 := by
    have h00 : fracHeatX α (T - 0) y0 = fracHeatX α T y0 := by
      rw [show T - 0 = T from sub_zero T]
    exact (hw 0).trans h00
  have hu0 : ub 0 = U := by
    have h00 : simOp α a (1 - 0) U = U := by
      rw [show (1 : ℝ) - 0 = 1 from sub_zero 1]
      exact (h9 α a hα).1 U
    exact (hub 0).trans h00
  have eT : inner ℝ (ub T) (w T) = inner ℝ (ub T) y0 := by
    rewrite [hwT]
    rfl
  have e0 : inner ℝ (ub 0) (w 0) = inner ℝ (fracHeatX α T U) y0 := by
    rewrite [hw0, hu0]
    exact (hH.2.2.2.2.1 _ _ _).symm
  rewrite [hy0, inner_sub_left, inner_sub_left]
  rewrite [eT, e0] at hF
  rewrite [hF]
  exact sub_self _

end Breakdown.FracInternal.MildProfileOrbit

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.FracInternal.MildProfileOrbit

set_option maxHeartbeats 1000000 in
theorem mildOfWeakProfile_of (h1 : NiceHeatStatement) (h2 : NiceAnnihilatorStatement)
    (h3 : BilinPairingStatement) (h4 : PowerSimAdjStatement) (h5 : SimAdjPairingStatement)
    (h6 : SimAdjDerivStatement) (h7 : NiceSimAdjClosedStatement) (_h8 : NiceDriftClosedStatement)
    (h9 : SimOpComposeStatement) : MildOfWeakProfileStatement := by
  intro α hα hα2 a U hU F hF t ht0 ht1
  obtain ⟨hG, hK⟩ := hF
  have hBb := (fracBilin_holds α hα).2
  have hBc : FracBilinContinuous α := fun u v => hK ▸ F.K_cont u v
  have hcont : ContinuousOn (fun s => simOp α a (1 - s) U) (Icc 0 t) :=
    (simOp_cont hα a U).mono fun s hs => lt_of_le_of_lt hs.2 ht1
  refine ⟨hcont, fun T hT => ?_⟩
  rw [hG, hK]
  have hint := FracInternal.MildWeak.frac_bilin_int hα.le hBb hBc hcont hT
  refine ⟨hint, ?_⟩
  have hT1 : T < 1 := lt_of_le_of_lt hT.2 ht1
  beta_reduce
  simp only [sub_zero, (h9 α a hα).1]
  have hz := h2 _ (fun φ hφ => mild_identity hα hα2 h1 h3 h4 h5 h6 h7 h9 hU hT.1 hT1
    (fun s => simOp α a (1 - s) U) (fun _ => rfl) hint φ hφ)
  rw [sub_sub, sub_eq_zero] at hz
  exact hz

end Breakdown.FracCert

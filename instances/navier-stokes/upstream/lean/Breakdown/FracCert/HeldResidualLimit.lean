import Breakdown.FracCert.HeldResidualLimitParts
import Breakdown.FracCert.BallShift
import Breakdown.FracCert.SecondSymbol
import Breakdown.FracCert.HeldStateLimitACross
import Breakdown.FracCert.HeldStateLimitATest
import Breakdown.FracCert.HeldStateLimitADefect
import Breakdown.FracCert.HeldStateLimitAProfile
import Breakdown.FracCert.HeldStateLimitAFree
import Breakdown.FracCert.HeldStateLimitBWeak
import Breakdown.FracCert.DriftPowerSolenoidal
import Breakdown.FracCert.GradientOrthogonal
import Breakdown.FracCert.QuadraticSquare
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.FracCert.InverseSquare

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldResidualLimitInternal

theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp

theorem inv_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (fun y => ‖y‖⁻¹ • v y) 2 volume := by
  have hI := (inverseSquareBound v G hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient).1
  have hm : AEStronglyMeasurable (fun y => ‖y‖⁻¹ • v y) volume :=
    (measurable_norm.inv).aestronglyMeasurable.smul hs.measurable_velocity
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine hI.congr (Eventually.of_forall fun y => ?_)
  simp only [norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, div_eq_inv_mul]

theorem weight_memLp {m : ℕ} {w : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m (fun y => ‖y‖ • w y) G H) :
    MemLp w 2 volume := by
  refine (inv_memLp hs).ae_eq ?_
  filter_upwards [ae_ne_zero] with y hy
  simp only [smul_smul, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy), one_smul]

theorem residual_parts {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (y : Space) :
    d.heldResidual α p v G H P κ y = (driftField α (d.rotationRate p) v G y + P y) + d.defect α p y
      + (d.gradProfile p y (v y) + G y (d.profile p y) + G y (v y)) + ∑ i, κ i • d.actuator i y := by
  have h2 : (2 : ℝ) * (1 / 2) = 1 := by norm_num
  simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField,
    FracCertData.splitField, symProduct, smul_add, smul_smul, h2, one_smul]
  abel

theorem residual_expand {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) :
    d.heldResidual α p v G H P κ = fun y =>
      driftField α (d.rotationRate p) v G y + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
        + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + v y)
        + ∑ i, (d.multiplier p i + κ i) • d.actuator i y := by
  funext y
  simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField,
    FracCertData.splitField, FracCertData.defect, symProduct, add_smul, Finset.sum_add_distrib,
    add_apply, map_add, smul_smul]
  norm_num
  abel

theorem residual_memLp {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p v G H P) (κ : Fin k → ℝ) :
    MemLp (d.heldResidual α p v G H P κ) 2 volume := by
  rw [residual_expand]
  have hs : MemLp (fun y => ∑ i, (d.multiplier p i + κ i) • d.actuator i y) 2 volume :=
    memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i + κ i)
  exact ((((hst.drift.add (hd.profile_drift p hp)).add hst.power.1).add (hd.profile_power p hp).1).add
    (heldQuadraticL2_of quadraticSquareIntegrable α hα1 hα2 d hd p hp v G H hst.second)).add hs

theorem cross_memLp {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} {d : FracCertData k N}
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField d.order v G H) :
    MemLp (fun y => d.gradProfile p y (v y) + G y (d.profile p y) + G y (v y)) 2 volume := by
  obtain ⟨C, hC⟩ := crossUniformBound α hα1 hα2 d hd (d.energy G H)
  exact (hC p hp v G H hs le_rfl).1

theorem defect_memLp {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p v G H P) : MemLp (d.defect α p) 2 volume := by
  have h := ((residual_memLp hα1 hα2 d hd hp hst 0).sub (hst.drift.add hst.power.1)).sub
    (cross_memLp hα1 hα2 hd hp hst.second)
  refine h.ae_eq (Eventually.of_forall fun y => ?_)
  simp only [Pi.sub_apply, Pi.add_apply, residual_parts, Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero]
  abel

theorem pair_parts {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p v G H P) (κ : Fin k → ℝ) {ζ : Space → Space} (hζ : MemLp ζ 2 volume) :
    ∫ y, inner ℝ (d.heldResidual α p v G H P κ y) (ζ y) =
      (∫ y, inner ℝ (driftField α (d.rotationRate p) v G y + P y) (ζ y)) + (∫ y, inner ℝ (d.defect α p y) (ζ y))
        + (∫ y, inner ℝ (d.gradProfile p y (v y) + G y (d.profile p y) + G y (v y)) (ζ y))
        + ∑ i, κ i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
  have iA := HeldLimitInternal.inner_integrable (hst.drift.add hst.power.1) hζ
  have iD := HeldLimitInternal.inner_integrable (defect_memLp hα1 hα2 d hd hp hst) hζ
  have iC := HeldLimitInternal.inner_integrable (cross_memLp hα1 hα2 hd hp hst.second) hζ
  have iK : ∀ i, Integrable (fun y => κ i * inner ℝ (d.actuator i y) (ζ y)) :=
    fun i => (HeldLimitInternal.inner_integrable (hd.actuator_two i) hζ).const_mul (κ i)
  have e : (fun y => inner ℝ (d.heldResidual α p v G H P κ y) (ζ y)) = fun y =>
      inner ℝ (driftField α (d.rotationRate p) v G y + P y) (ζ y) + inner ℝ (d.defect α p y) (ζ y)
        + inner ℝ (d.gradProfile p y (v y) + G y (d.profile p y) + G y (v y)) (ζ y)
        + ∑ i, κ i * inner ℝ (d.actuator i y) (ζ y) := by
    funext y
    rw [residual_parts, inner_add_left, inner_add_left, inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  rw [e, integral_add, integral_add, integral_add, integral_finsetSum]
  · simp only [integral_const_mul]
  all_goals first
    | exact fun i _ => iK i
    | exact iA
    | exact iD
    | exact iC
    | exact iA.add iD
    | exact (iA.add iD).add iC
    | exact integrable_finsetSum _ fun i _ => iK i

theorem held_orthogonal {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {u : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    {κ : Fin k → ℝ} (hsol : d.IsHeldSolution α p u G H P κ) (ζ : Space → Space) (hζ : IsSolenoidalL2 ζ) :
    ∫ y, inner ℝ (d.heldResidual α p u G H P κ y) (ζ y) = 0 := by
  have hres := residual_memLp hα1 hα2 d hd hp hsol.state κ
  obtain ⟨Q, hQg, hQ⟩ := hsol.equation
  have hQe : (fun y => -d.heldResidual α p u G H P κ y) =ᵐ[volume] Q := by
    filter_upwards [hQ] with y hy
    exact neg_eq_of_add_eq_zero_right hy
  have hQ2 : MemLp Q 2 volume := hres.neg.ae_eq hQe
  have h0 := gradientOrthogonal Q ζ hQg hQ2 hζ
  have e : ∫ y, inner ℝ (d.heldResidual α p u G H P κ y) (ζ y) = -∫ y, inner ℝ (Q y) (ζ y) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hQe] with y hy
    rw [← hy, inner_neg_left, neg_neg]
  rw [e, h0, neg_zero]

theorem combine4 {f1 f2 f3 f4 : Space → ℝ} (c₁ c₂ a : ℝ) (h1 : Integrable f1 volume)
    (h2 : Integrable f2 volume) (h3 : Integrable f3 volume) (h4 : Integrable f4 volume) :
    ∫ y, (c₁ * f1 y + c₂ * f2 y + a * (f3 y - f4 y)) =
      c₁ * (∫ y, f1 y) + c₂ * (∫ y, f2 y) + a * ((∫ y, f3 y) - ∫ y, f4 y) := by
  have i1 : Integrable (fun y => c₁ * f1 y) volume := h1.const_mul c₁
  have i2 : Integrable (fun y => c₂ * f2 y) volume := h2.const_mul c₂
  have i34 : Integrable (fun y => a * (f3 y - f4 y)) volume := (h3.sub h4).const_mul a
  have i12 : Integrable (fun y => c₁ * f1 y + c₂ * f2 y) volume := i1.add i2
  rw [integral_add i12 i34, integral_add i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sub h3 h4]

open ProfileTestInternal in
theorem drift_test_limit (α : ℝ) {a : ℕ → ℝ} {a₀ : ℝ} (ha : Tendsto a atTop (nhds a₀))
    {u : ℕ → Space → Space} {u₀ : Space → Space} {G : ℕ → Space → (Space →L[ℝ] Space)}
    {G₀ : Space → (Space →L[ℝ] Space)} {K : ℝ}
    (hGm : ∀ n, AEStronglyMeasurable (G n) volume) (hGi : ∀ n, Integrable (fun y => entrySq (G n y)))
    (hGK : ∀ n, ∫ y, entrySq (G n y) ≤ K) (hG₀m : AEStronglyMeasurable G₀ volume)
    (hG₀i : Integrable (fun y => entrySq (G₀ y)))
    (hGw : ∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
      Integrable (fun y => entrySq (E y)) →
      Tendsto (fun n => ∫ y, entryInner (G n y) (E y)) atTop (nhds (∫ y, entryInner (G₀ y) (E y))))
    (hum : ∀ n, AEStronglyMeasurable (u n) volume) (hu₀m : AEStronglyMeasurable u₀ volume)
    (hui : ∀ n r, IntegrableOn (fun y => ‖u n y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (hu₀i : ∀ r, IntegrableOn (fun y => ‖u₀ y‖ ^ 2) (Metric.ball (0 : Space) r) volume)
    (hloc : ∀ r, Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u n y - u₀ y‖ ^ 2) atTop (nhds 0))
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) :
    Integrable (fun y => inner ℝ (driftField α a₀ u₀ G₀ y) (ψ y)) volume ∧
    Tendsto (fun n => ∫ y, inner ℝ (driftField α (a n) (u n) (G n) y) (ψ y)) atTop
      (nhds (∫ y, inner ℝ (driftField α a₀ u₀ G₀ y) (ψ y))) := by
  set T := HeldWeakProfilePartsInternal.turnCLM
  have hzero : ∀ (g : Space → Space) (r : ℝ),
      Tendsto (fun _ : ℕ => ∫ y in Metric.ball (0 : Space) r, ‖g y - g y‖ ^ 2) atTop (nhds 0) := by
    intro g r
    simp
  have t1 := fixed_pair_limit (ContinuousLinearMap.id ℝ Space) hum hu₀m hui hu₀i hloc hψ
  have t4 := fixed_pair_limit T hum hu₀m hui hu₀i hloc hψ
  have t2 := ApplyPairingInternal.apply_pairing_limit (A := G) (A₀ := G₀)
    (a := fun _ => fun y => y) (a₀ := fun y => y) hGm hGi hGK hGw
    (fun _ => (continuous_id.aestronglyMeasurable (μ := volume))) (continuous_id.aestronglyMeasurable (μ := volume))
    (fun _ r => CrossTestInternal.cont_sq continuous_id r) (CrossTestInternal.cont_sq continuous_id)
    (hzero (fun y => y)) hψ
  have t3 := ApplyPairingInternal.apply_pairing_limit (A := G) (A₀ := G₀)
    (a := fun _ => fun y => T y) (a₀ := fun y => T y) hGm hGi hGK hGw
    (fun _ => (T.continuous.aestronglyMeasurable (μ := volume))) (T.continuous.aestronglyMeasurable (μ := volume))
    (fun _ r => CrossTestInternal.cont_sq T.continuous r) (CrossTestInternal.cont_sq T.continuous)
    (hzero (fun y => T y)) hψ
  have ints : ∀ (v : Space → Space) (B : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
      (∀ r, IntegrableOn (fun y => ‖v y‖ ^ 2) (Metric.ball (0 : Space) r) volume) →
      AEStronglyMeasurable B volume → Integrable (fun y => entrySq (B y)) →
      Integrable (fun y => inner ℝ (ContinuousLinearMap.id ℝ Space (v y)) (ψ y)) volume ∧
      Integrable (fun y => inner ℝ (B y y) (ψ y)) volume ∧
      Integrable (fun y => inner ℝ (B y (T y)) (ψ y)) volume ∧
      Integrable (fun y => inner ℝ (T (v y)) (ψ y)) volume := by
    intro v B hvm hvi hBm hBi
    exact ⟨pair_int_fixed _ hvm hvi hψ,
      pair_int hBm hBi (b := fun y => y) (continuous_id.aestronglyMeasurable (μ := volume))
        (CrossTestInternal.cont_sq continuous_id) hψ,
      pair_int hBm hBi (b := fun y => T y) (T.continuous.aestronglyMeasurable (μ := volume))
        (CrossTestInternal.cont_sq T.continuous) hψ,
      pair_int_fixed T hvm hvi hψ⟩
  have expand : ∀ (c : ℝ) (v : Space → Space) (B : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable v volume →
      (∀ r, IntegrableOn (fun y => ‖v y‖ ^ 2) (Metric.ball (0 : Space) r) volume) →
      AEStronglyMeasurable B volume → Integrable (fun y => entrySq (B y)) →
      ∫ y, inner ℝ (driftField α c v B y) (ψ y) =
        (1 - 1 / (2 * α)) * (∫ y, inner ℝ (ContinuousLinearMap.id ℝ Space (v y)) (ψ y))
          + (1 / (2 * α)) * (∫ y, inner ℝ (B y y) (ψ y))
          + c * ((∫ y, inner ℝ (B y (T y)) (ψ y)) - ∫ y, inner ℝ (T (v y)) (ψ y)) := by
    intro c v B hvm hvi hBm hBi
    obtain ⟨i1, i2, i3, i4⟩ := ints v B hvm hvi hBm hBi
    rw [← combine4 _ _ _ i1 i2 i3 i4]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left, ContinuousLinearMap.id_apply,
      HeldWeakProfilePartsInternal.turnCLM_apply, T]
  refine ⟨?_, ?_⟩
  · obtain ⟨i1, i2, i3, i4⟩ := ints u₀ G₀ hu₀m hu₀i hG₀m hG₀i
    have h := (((i1.const_mul (1 - 1 / (2 * α))).add (i2.const_mul (1 / (2 * α)))).add
      ((i3.sub i4).const_mul a₀))
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left, ContinuousLinearMap.id_apply,
      HeldWeakProfilePartsInternal.turnCLM_apply, T, Pi.add_apply, Pi.sub_apply]
  · rw [expand a₀ u₀ G₀ hu₀m hu₀i hG₀m hG₀i]
    exact (((t1.const_mul _).add (t2.const_mul _)).add (ha.mul (t3.sub t4))).congr
      (fun n => (expand (a n) (u n) (G n) (hum n) (hui n) (hGm n) (hGi n)).symm)

theorem apply_locInt {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hGi : Integrable (fun y => entrySq (G y))) {c : Space → Space} (hc : Continuous c) (K : Set Space)
    (hK : IsCompact K) : IntegrableOn (fun y => G y (c y)) K volume := by
  have hb : Integrable (fun y => entrySq (G y) + ‖c y‖ ^ 2) (volume.restrict K) :=
    hGi.integrableOn.add ((hc.norm.pow 2).continuousOn.integrableOn_compact hK)
  refine hb.mono' (ApplyPairingInternal.apply_meas hGm hc.aestronglyMeasurable).restrict
    (Eventually.of_forall fun y => ?_)
  have h1 := ApplyPairingInternal.apply_norm_le (G y) (c y)
  have h0 : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs := Real.sq_sqrt h0
  nlinarith [sq_nonneg (Real.sqrt (entrySq (G y)) - ‖c y‖), Real.sqrt_nonneg (entrySq (G y)), norm_nonneg (c y)]

theorem drift_locInt (α a : ℝ) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hv6 : MemLp v 6 volume) (hGm : AEStronglyMeasurable G volume)
    (hGi : Integrable (fun y => entrySq (G y))) : LocallyIntegrable (driftField α a v G) volume := by
  set T := HeldWeakProfilePartsInternal.turnCLM
  have hv : LocallyIntegrable v volume := hv6.locallyIntegrable (by norm_num)
  rw [locallyIntegrable_iff]
  intro K hK
  have i1 := hv.integrableOn_isCompact hK
  have i2 := apply_locInt hGm hGi continuous_id K hK
  have i3 := apply_locInt hGm hGi T.continuous K hK
  have i4 : IntegrableOn (fun y => T (v y)) K volume := T.integrable_comp i1
  have h := ((i1.smul (1 - 1 / (2 * α))).add (i2.smul (1 / (2 * α)))).add ((i3.sub i4).smul a)
  refine Integrable.congr h (Eventually.of_forall fun y => ?_)
  simp only [driftField, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, id, HeldWeakProfilePartsInternal.turnCLM_apply, T]

theorem drift_identify (α : ℝ) {a : ℕ → ℝ} {a₀ : ℝ} (ha : Tendsto a atTop (𝓝 a₀)) {m : ℕ}
    {u : ℕ → Space → Space} {G : ℕ → Space → (Space →L[ℝ] Space)}
    {H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {v₀ : Space → Space} {G₀ : Space → (Space →L[ℝ] Space)}
    {H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D₀ : Space → Space} {K : ℝ}
    (hs : ∀ n, IsSecondOrderField m (u n) (G n) (H n)) (hs₀ : IsSecondOrderField m v₀ G₀ H₀)
    (hGK : ∀ n, ∫ y, entrySq (G n y) ≤ K)
    (hGw : ∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
      Integrable (fun y => entrySq (E y)) →
      Tendsto (fun n => ∫ y, entryInner (G n y) (E y)) atTop (𝓝 (∫ y, entryInner (G₀ y) (E y))))
    (hloc : ∀ r, Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖u n y - v₀ y‖ ^ 2) atTop (𝓝 0))
    (hD₀ : MemLp D₀ 2 volume)
    (hDw : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (driftField α (a n) (u n) (G n) y) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (D₀ y) (g y)))) :
    D₀ =ᵐ[volume] driftField α a₀ v₀ G₀ := by
  have hdt := fun ψ (hψ : IsTestVectorField ψ) => drift_test_limit α ha
    (fun n => (hs n).measurable_gradient) (fun n => (hs n).gradient_two) hGK
    hs₀.measurable_gradient hs₀.gradient_two hGw
    (fun n => (hs n).measurable_velocity) hs₀.measurable_velocity
    (fun n r => CrossTestInternal.local_sq (hs n) r) (CrossTestInternal.local_sq hs₀) hloc hψ
  set D := driftField α a₀ v₀ G₀ with hDdef
  have hlocf : LocallyIntegrable (fun y => D₀ y - D y) volume :=
    (hD₀.locallyIntegrable (by norm_num)).sub
      (drift_locInt α _ hs₀.velocity_six hs₀.measurable_gradient hs₀.gradient_two)
  have hid : ∀ᵐ y ∂volume, D₀ y - D y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hlocf (fun g hg hgs => ?_)
    have hint : Integrable (fun y => g y • (D₀ y - D y)) volume :=
      hlocf.integrable_smul_left_of_hasCompactSupport hg.continuous hgs
    ext i
    have hψ : IsTestVectorField (fun y => g y • unitVector i) := ⟨hg.smul contDiff_const, hgs.smul_right⟩
    have hψ2 : MemLp (fun y => g y • unitVector i) 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
    have e1 := tendsto_nhds_unique (hDw _ hψ2) (hdt _ hψ).2
    have hYi := ActiveEnclosureInternal.pair_integrable hD₀ hψ2
    have hDi := (hdt _ hψ).1
    have e2 : ∫ y, inner ℝ (D₀ y - D y) (g y • unitVector i) = 0 := by
      have : (fun y => inner ℝ (D₀ y - D y) (g y • unitVector i)) =
          fun y => inner ℝ (D₀ y) (g y • unitVector i) - inner ℝ (D y) (g y • unitVector i) := by
        funext y; rw [inner_sub_left]
      rw [this, integral_sub hYi hDi, e1, sub_self]
    have e3 : (∫ y, g y • (D₀ y - D y)) i = inner ℝ (∫ y, g y • (D₀ y - D y)) (unitVector i) := by
      rw [ApplyPairingInternal.unit_inner]
    rw [e3, real_inner_comm, ← integral_inner hint]
    simp only [PiLp.zero_apply]
    rw [← e2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left, real_inner_smul_right, real_inner_comm]
  filter_upwards [hid] with y hy
  exact sub_eq_zero.1 hy

end HeldResidualLimitInternal

namespace LocalStrongInternal

theorem ind_sq (r : ℝ) (f g : Space → Space) :
    ∫ y in Metric.ball (0 : Space) r, ‖f y - g y‖ ^ 2 =
      ∫ y, ‖(Metric.ball (0 : Space) r).indicator f y - (Metric.ball (0 : Space) r).indicator g y‖ ^ 2 := by
  rw [← integral_indicator measurableSet_ball]
  congr 1
  funext y
  by_cases hy : y ∈ Metric.ball (0 : Space) r <;> simp [hy]

theorem ind_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (r : ℝ) :
    MemLp ((Metric.ball (0 : Space) r).indicator v) 2 volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  exact (memLp_indicator_iff_restrict measurableSet_ball).2
    ((hs.velocity_six.restrict _).mono_exponent (by norm_num))

theorem ind_weight_memLp {w : Space → Space} (hw : MemLp w 2 volume) (r : ℝ) :
    MemLp ((Metric.ball (0 : Space) r).indicator (fun y => ‖y‖ • w y)) 2 volume := by
  refine hw.of_le_mul (c := max r 0) ?_ (Eventually.of_forall fun y => ?_)
  · exact ((continuous_norm.aestronglyMeasurable).smul hw.1).indicator measurableSet_ball
  · by_cases hy : y ∈ Metric.ball (0 : Space) r
    · rw [Set.indicator_of_mem hy, norm_smul, norm_norm]
      have : ‖y‖ < r := by simpa using hy
      exact mul_le_mul_of_nonneg_right (this.le.trans (le_max_left _ _)) (norm_nonneg _)
    · rw [Set.indicator_of_notMem hy, norm_zero]
      exact mul_nonneg (le_max_right _ _) (norm_nonneg _)

theorem ball_weak {u : ℕ → Space → Space} {w₀ : Space → Space}
    (hw : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (w₀ y) (g y))))
    (r : ℝ) {g : Space → Space} (hg : MemLp g 2 volume) (hgz : ∀ y, r ≤ ‖y‖ → g y = 0) :
    Tendsto (fun n => ∫ y, inner ℝ (u n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (‖y‖ • w₀ y) (g y))) := by
  have hg' : MemLp (fun y => ‖y‖ • g y) 2 volume := by
    refine hg.of_le_mul (c := max r 0) ((continuous_norm.aestronglyMeasurable).smul hg.1)
      (Eventually.of_forall fun y => ?_)
    rw [norm_smul, norm_norm]
    by_cases h : r ≤ ‖y‖
    · rw [hgz y h]
      simp
    · have h := lt_of_not_ge h
      exact mul_le_mul_of_nonneg_right (h.le.trans (le_max_left _ _)) (norm_nonneg _)
  have e1 : ∀ n, ∫ y, inner ℝ (u n y) (g y) = ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (‖y‖ • g y) := fun n => by
    refine integral_congr_ae ?_
    filter_upwards [HeldResidualLimitInternal.ae_ne_zero] with y hy
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy),
      one_mul]
  have e0 : ∫ y, inner ℝ (‖y‖ • w₀ y) (g y) = ∫ y, inner ℝ (w₀ y) (‖y‖ • g y) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left, real_inner_smul_right]
  rw [e0]
  exact (hw _ hg').congr fun n => (e1 n).symm

theorem lsc_ball (r ε : ℝ) (hε : 0 < ε) {u : ℕ → Space → Space} {a₀ b : Space → Space}
    (hw : ∀ g : Space → Space, MemLp g 2 volume → (∀ y, r ≤ ‖y‖ → g y = 0) →
      Tendsto (fun n => ∫ y, inner ℝ (u n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (a₀ y) (g y))))
    (hu : ∀ n, MemLp ((Metric.ball (0 : Space) r).indicator (u n)) 2 volume)
    (ha : MemLp ((Metric.ball (0 : Space) r).indicator a₀) 2 volume)
    (hb : MemLp ((Metric.ball (0 : Space) r).indicator b) 2 volume)
    (hfr : ∃ᶠ n in atTop, ∫ y in Metric.ball (0 : Space) r, ‖u n y - b y‖ ^ 2 < ε) :
    ∫ y in Metric.ball (0 : Space) r, ‖a₀ y - b y‖ ^ 2 ≤ ε := by
  set B := Metric.ball (0 : Space) r with hBdef
  set A : Space → Space := fun y => B.indicator a₀ y - B.indicator b y with hAdef
  have hA : MemLp A 2 volume := ha.sub hb
  have hAz : ∀ y, y ∉ B → A y = 0 := fun y hy => by
    simp only [hAdef, Set.indicator_of_notMem hy, sub_zero]
  have hAz' : ∀ y, r ≤ ‖y‖ → A y = 0 := fun y hy => hAz y (by rw [hBdef, Metric.mem_ball, dist_zero_right]; exact not_lt.2 hy)
  have hpt : ∀ (f : Space → Space) y, inner ℝ (f y) (A y) = inner ℝ (B.indicator f y) (A y) := by
    intro f y
    by_cases hy : y ∈ B
    · rw [Set.indicator_of_mem hy]
    · rw [hAz y hy, inner_zero_right, inner_zero_right]
  set X := ∫ y in B, ‖a₀ y - b y‖ ^ 2 with hXdef
  have hX : X = ∫ y, ‖A y‖ ^ 2 := ind_sq r a₀ b
  have hX0 : 0 ≤ X := setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _
  have hXi : (∫ y, inner ℝ (a₀ y) (A y)) - ∫ y, inner ℝ (b y) (A y) = X := by
    have i1 := HeldLimitInternal.inner_integrable ha hA
    have i2 := HeldLimitInternal.inner_integrable hb hA
    rw [integral_congr_ae (Eventually.of_forall (hpt a₀)), integral_congr_ae (Eventually.of_forall (hpt b)),
      ← integral_sub i1 i2, hX]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [← inner_sub_left, real_inner_self_eq_norm_sq, hAdef]
  have hconv : Tendsto (fun n => ∫ y, inner ℝ (B.indicator (u n) y - B.indicator b y) (A y)) atTop (𝓝 X) := by
    rw [← hXi]
    refine ((hw A hA hAz').sub_const (∫ y, inner ℝ (b y) (A y))).congr fun n => ?_
    have i1 := HeldLimitInternal.inner_integrable (hu n) hA
    have i2 := HeldLimitInternal.inner_integrable hb hA
    rw [integral_congr_ae (Eventually.of_forall (hpt (u n))), integral_congr_ae (Eventually.of_forall (hpt b)),
      ← integral_sub i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_sub_left]
  have hbound : ∀ n, ∫ y, inner ℝ (B.indicator (u n) y - B.indicator b y) (A y) ≤
      Real.sqrt (∫ y in B, ‖u n y - b y‖ ^ 2) * Real.sqrt X := by
    intro n
    rw [ind_sq r (u n) b, hX]
    exact (le_abs_self _).trans (ApplyPairingInternal.abs_pair_le ((hu n).sub hb) hA)
  have hle : X ≤ Real.sqrt ε * Real.sqrt X := by
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    have hev := hconv.eventually (lt_mem_nhds hcon)
    obtain ⟨n, hn1, hn2⟩ := (hfr.and_eventually hev).exists
    have h1 := hbound n
    have h2 : Real.sqrt (∫ y in B, ‖u n y - b y‖ ^ 2) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hn1.le
    have h3 := mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg X)
    linarith
  have hs1 := Real.sq_sqrt hX0
  have hs2 := Real.sq_sqrt hε.le
  have hsx := Real.sqrt_nonneg X
  have hse := Real.sqrt_nonneg ε
  nlinarith [mul_nonneg hsx hse]

theorem loc_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (r : ℝ) :
    MemLp v 2 (volume.restrict (Metric.ball (0 : Space) r)) :=
  (memLp_indicator_iff_restrict measurableSet_ball).1 (ind_memLp hs r)

theorem loc_weight_memLp {w : Space → Space} (hw : MemLp w 2 volume) (r : ℝ) :
    MemLp (fun y => ‖y‖ • w y) 2 (volume.restrict (Metric.ball (0 : Space) r)) :=
  (memLp_indicator_iff_restrict measurableSet_ball).1 (ind_weight_memLp hw r)

theorem sq_int {f g : Space → Space} {r : ℝ} (hf : MemLp f 2 (volume.restrict (Metric.ball (0 : Space) r)))
    (hg : MemLp g 2 (volume.restrict (Metric.ball (0 : Space) r))) :
    IntegrableOn (fun y => ‖f y - g y‖ ^ 2) (Metric.ball (0 : Space) r) volume :=
  (hf.sub hg).integrable_norm_pow (p := 2) (by norm_num)

theorem entry_int {G K : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hK : AEStronglyMeasurable K volume) (hGi : Integrable (fun y => entrySq (G y)))
    (hKi : Integrable (fun y => entrySq (K y))) : Integrable (fun y => entrySq (G y - K y)) := by
  have hent : Continuous entrySq := by unfold entrySq; fun_prop
  refine ((hGi.add hKi).const_mul 2).mono' (hent.comp_aestronglyMeasurable (hG.sub hK))
    (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ entrySq (G y - K y) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  exact ActiveEnclosureInternal.entrySq_sub_le _ _

theorem frequent_small {m : ℕ} {u : ℕ → Space → Space} {G : ℕ → Space → (Space →L[ℝ] Space)}
    {H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {w₀ : Space → Space}
    (hs : ∀ n, IsSecondOrderField m (u n) (G n) (H n)) (hw₀ : MemLp w₀ 2 volume)
    (hw : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) atTop (𝓝 (∫ y, inner ℝ (w₀ y) (g y))))
    (r : ℝ) (hnet : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S,
      ∫ y in Metric.ball (0 : Space) r, (‖u n y - u k y‖ ^ 2 + entrySq (G n y - G k y)) < ε)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n in atTop, ∫ y in Metric.ball (0 : Space) r, ‖u n y - ‖y‖ • w₀ y‖ ^ 2 < 4 * ε := by
  obtain ⟨S, hS⟩ := hnet ε hε
  have hk : ∃ k ∈ S, ∃ᶠ n in atTop,
      ∫ y in Metric.ball (0 : Space) r, (‖u n y - u k y‖ ^ 2 + entrySq (G n y - G k y)) < ε := by
    by_contra hcon
    simp only [not_exists, not_and, Filter.not_frequently] at hcon
    obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset S).2 hcon).exists
    obtain ⟨k, hkS, hk⟩ := hS n
    exact hn k hkS hk
  obtain ⟨k, -, hfr⟩ := hk
  have hfr' : ∃ᶠ n in atTop, ∫ y in Metric.ball (0 : Space) r, ‖u n y - u k y‖ ^ 2 < ε := by
    refine hfr.mono fun n hn => lt_of_le_of_lt ?_ hn
    refine setIntegral_mono (sq_int (loc_memLp (hs n) r) (loc_memLp (hs k) r))
      ((sq_int (loc_memLp (hs n) r) (loc_memLp (hs k) r)).add
        (entry_int (hs n).measurable_gradient (hs k).measurable_gradient (hs n).gradient_two
          (hs k).gradient_two).integrableOn) fun y => ?_
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hl := lsc_ball r ε hε (u := u) (a₀ := fun y => ‖y‖ • w₀ y) (b := u k)
    (fun g hg hgz => ball_weak hw r hg hgz) (fun n => ind_memLp (hs n) r) (ind_weight_memLp hw₀ r)
    (ind_memLp (hs k) r) hfr'
  refine hfr'.mono fun n hn => ?_
  have i1 := sq_int (loc_memLp (hs n) r) (loc_memLp (hs k) r)
  have i2 := sq_int (loc_weight_memLp hw₀ r) (loc_memLp (hs k) r)
  have i0 := sq_int (loc_memLp (hs n) r) (loc_weight_memLp hw₀ r)
  have hmono : ∫ y in Metric.ball (0 : Space) r, ‖u n y - ‖y‖ • w₀ y‖ ^ 2 ≤
      ∫ y in Metric.ball (0 : Space) r, (2 * ‖u n y - u k y‖ ^ 2 + 2 * ‖‖y‖ • w₀ y - u k y‖ ^ 2) := by
    refine setIntegral_mono i0 ((i1.const_mul 2).add (i2.const_mul 2)) fun y => ?_
    have h := norm_sub_le_norm_sub_add_norm_sub (u n y) (u k y) (‖y‖ • w₀ y)
    rw [norm_sub_rev (u k y)] at h
    have h2 := mul_le_mul h h (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))
    nlinarith [sq_nonneg (‖u n y - u k y‖ - ‖‖y‖ • w₀ y - u k y‖)]
  rw [integral_add (i1.const_mul 2) (i2.const_mul 2), integral_const_mul, integral_const_mul] at hmono
  linarith

end LocalStrongInternal

open LocalStrongInternal in
theorem localStrongSubseq : LocalStrongSubseqStatement := by
  intro m u G H w₀ B hs hB hw₀ hw
  have hvi : ∀ n, Integrable (fun y => ‖u n y‖ ^ 2 / ‖y‖ ^ 2) := fun n =>
    (inverseSquareBound (u n) (G n) (hs n).measurable_velocity (hs n).velocity_six (hs n).gradient_two
      (hs n).weak_gradient).1
  have hbnd : ∀ n, (∫ y, ‖u n y‖ ^ 2 / ‖y‖ ^ 2) + (∫ y, entrySq (G n y)) + (∫ y, fullSecondSq (H n y)) ≤ 5 * B := by
    intro n
    have h1 := (inverseSquareBound (u n) (G n) (hs n).measurable_velocity (hs n).velocity_six
      (hs n).gradient_two (hs n).weak_gradient).2
    have hfs := secondSymbolEnergy m (u n) (G n) (H n) (hs n)
    have h2 : ∫ y, fullSecondSq (H n y) = ∫ y, ‖secondTrace (H n y)‖ ^ 2 := hfs.2.2.1.trans hfs.2.2.2.symm
    have hE : 0 ≤ ∫ y, entrySq (G n y) := integral_nonneg fun y => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hT : 0 ≤ ∫ y, ‖secondTrace (H n y)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have := hB n
    rw [h2]
    linarith
  have hnet := ballNet_of (ballCompact_of ballShift) m u G H (5 * B) hs hvi hbnd
  have hfreq : ∀ j : ℕ, ∃ᶠ n in atTop,
      ∫ y in Metric.ball (0 : Space) ((j : ℝ) + 1), ‖u n y - ‖y‖ • w₀ y‖ ^ 2 < 1 / ((j : ℝ) + 1) := by
    intro j
    have hpos : (0 : ℝ) < 1 / (4 * ((j : ℝ) + 1)) := by positivity
    refine (frequent_small hs hw₀ hw ((j : ℝ) + 1) (fun ε hε => hnet ((j : ℝ) + 1) ε hε) _ hpos).mono
      fun n hn => hn.trans_eq ?_
    field_simp
  obtain ⟨φ, hφ, hP⟩ := Filter.extraction_forall_of_frequently hfreq
  refine ⟨φ, hφ, fun r => ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_one_div_add_atTop_nhds_zero_nat
    (Eventually.of_forall fun n => setIntegral_nonneg measurableSet_ball fun _ _ => sq_nonneg _) ?_
  filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn
  have hr : r ≤ (n : ℝ) + 1 := by
    have := Nat.le_ceil r
    have h2 : (⌈r⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  refine le_trans ?_ (hP n).le
  refine setIntegral_mono_set (sq_int (loc_memLp (hs (φ n)) _) (loc_weight_memLp hw₀ _))
    (Eventually.of_forall fun _ => sq_nonneg _) (Metric.ball_subset_ball hr).eventuallyLE

open HeldResidualLimitInternal in
theorem heldResidualLimit_of (h1 : LocalStrongSubseqStatement) :
    HeldResidualLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R B κ₀ hsol hR hB hκ w₀ G₀ H₀ P₀ D₀ hlin hD₀ hGw hHw
    hUw hPw hDw ζ hζ
  have hsec : ∀ n, IsSecondOrderField d.order (u n) (G n) (H n) := fun n => (hsol n).state.second
  have hw₀ : MemLp w₀ 2 volume := weight_memLp hlin.second
  have hen : ∀ n, d.energy (G n) (H n) ≤ R ^ 2 := by
    intro n
    have h := HeldLimitInternal.size_sq d hd (G n) (H n) (κ n)
    have hs2 : d.size (G n) (H n) (κ n) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hR n) 2
    have hk : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ n i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  have hbd : ∀ n, (∫ y, entrySq (G n y)) + (∫ y, ‖secondTrace (H n y)‖ ^ 2) ≤ R ^ 2 / d.weightMin + R ^ 2 := by
    intro n
    obtain ⟨_, hf⟩ := ActiveEnclosureInternal.energy_facts hd (hsec n)
    have hwm := hd.weightMin_pos
    have hG : ∫ y, entrySq (G n y) ≤ R ^ 2 / d.weightMin := by
      rw [le_div_iff₀ hwm]
      nlinarith [hen n]
    have hT : ∫ y, ‖secondTrace (H n y)‖ ^ 2 ≤ R ^ 2 := by
      have hw0 : 0 ≤ ∫ y, d.weight y * entrySq (G n y) := integral_nonneg fun y =>
        mul_nonneg (hwm.le.trans (hd.weight_lower y)) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      have := hen n
      unfold FracCertData.energy weightedEnergy at this
      linarith
    linarith
  obtain ⟨φ, hφ, hloc⟩ := h1 d.order u G H w₀ _ hsec hbd hw₀ hUw
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hrot : Tendsto (fun n => d.rotationRate (p n)) atTop (𝓝 (d.rotationRate q)) :=
    (hd.rotationRate_continuous q hq).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩)
  have hE : ∀ E : Space → (Space →L[ℝ] Space), AEStronglyMeasurable E volume →
      Integrable (fun y => entrySq (E y)) →
      Tendsto (fun n => ∫ y, entryInner (G (φ n) y) (E y)) atTop (𝓝 (∫ y, entryInner (G₀ y) (E y))) :=
    fun E hEm hEi => WeakFieldLimit.entryInner_tendsto (G := fun n => G (φ n))
      (fun n i => ActiveEnclosureInternal.col_memLp (hsec (φ n)).measurable_gradient (hsec (φ n)).gradient_two i)
      (fun i => ActiveEnclosureInternal.col_memLp hlin.second.measurable_gradient hlin.second.gradient_two i)
      (fun i g hg => (hGw i g hg).comp hφt) E hEm hEi
  have hGK : ∀ n, ∫ y, entrySq (G (φ n) y) ≤ R ^ 2 / d.weightMin + R ^ 2 := fun n => by
    have h0 : 0 ≤ ∫ y, ‖secondTrace (H (φ n) y)‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
    linarith [hbd (φ n)]
  have hid := drift_identify α (hrot.comp hφt) (fun n => hsec (φ n)) hlin.second hGK hE hloc hD₀
    (fun g hg => (hDw g hg).comp hφt)
  have hA : Tendsto (fun n => ∫ y, inner ℝ (driftField α (d.rotationRate (p (φ n))) (u (φ n)) (G (φ n)) y
      + P (φ n) y) (ζ y)) atTop
      (𝓝 (∫ y, inner ℝ (driftField α (d.rotationRate q) (fun y => ‖y‖ • w₀ y) G₀ y + P₀ y) (ζ y))) := by
    have e1 : ∀ n, ∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (u n) (G n) y + P n y) (ζ y) =
        (∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (u n) (G n) y) (ζ y)) + ∫ y, inner ℝ (P n y) (ζ y) := by
      intro n
      simp only [inner_add_left]
      exact integral_add (HeldLimitInternal.inner_integrable (hsol n).state.drift hζ.1)
        (HeldLimitInternal.inner_integrable (hsol n).state.power.1 hζ.1)
    have e0 : ∫ y, inner ℝ (driftField α (d.rotationRate q) (fun y => ‖y‖ • w₀ y) G₀ y + P₀ y) (ζ y) =
        (∫ y, inner ℝ (D₀ y) (ζ y)) + ∫ y, inner ℝ (P₀ y) (ζ y) := by
      simp only [inner_add_left]
      rw [integral_add (HeldLimitInternal.inner_integrable hlin.drift hζ.1)
        (HeldLimitInternal.inner_integrable hlin.power.1 hζ.1)]
      congr 1
      refine integral_congr_ae ?_
      filter_upwards [hid] with y hy
      rw [hy]
    rw [e0]
    exact (((hDw ζ hζ.1).add (hPw ζ hζ.1)).comp hφt).congr fun n => (e1 (φ n)).symm
  have hdef : DefectPairingLimitStatement := defectPairingLimit_of
    (profileFreePairingLimit_of (profileFreeBound_of driftPowerSolenoidal)
      (profileFreeTestLimit_of profilePowerTestLimit))
  have hD := hdef α hα1 hα2 d hd (fun n => p (φ n)) q (fun n => hp (φ n)) hq (hpq.comp hφt) ζ hζ
  have hcross : CrossPairingLimitStatement :=
    crossPairingLimit_of crossUniformBound (crossTestLimit_of profileLocalLimit)
  have hC := hcross α hα1 hα2 d hd (fun n => p (φ n)) q (fun n => hp (φ n)) hq (hpq.comp hφt)
    (fun n => u (φ n)) (fun n => G (φ n)) (fun n => H (φ n)) (fun y => ‖y‖ • w₀ y) G₀ H₀ (R ^ 2)
    (fun n => hsec (φ n)) hlin.second (fun n => hen (φ n)) hE hloc ζ hζ
  have hK : Tendsto (fun n => ∑ i, κ (φ n) i * ∫ y, inner ℝ (d.actuator i y) (ζ y)) atTop
      (𝓝 (∑ i, κ₀ i * ∫ y, inner ℝ (d.actuator i y) (ζ y))) :=
    tendsto_finsetSum _ fun i _ => (((continuous_apply i).tendsto κ₀).comp (hκ.comp hφt)).mul_const _
  have hsum := ((hA.add hD).add hC).add hK
  have h0 : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop
      (𝓝 ((∫ y, inner ℝ (driftField α (d.rotationRate q) (fun y => ‖y‖ • w₀ y) G₀ y + P₀ y) (ζ y))
        + (∫ y, inner ℝ (d.defect α q y) (ζ y))
        + (∫ y, inner ℝ (d.gradProfile q y ((fun y => ‖y‖ • w₀ y) y) + G₀ y (d.profile q y)
          + G₀ y ((fun y => ‖y‖ • w₀ y) y)) (ζ y))
        + ∑ i, κ₀ i * ∫ y, inner ℝ (d.actuator i y) (ζ y))) := by
    refine hsum.congr fun n => ?_
    rw [← pair_parts hα1 hα2 d hd (hp (φ n)) (hsol (φ n)).state (κ (φ n)) hζ.1]
    exact held_orthogonal hα1 hα2 d hd (hp (φ n)) (hsol (φ n)) ζ hζ
  rw [pair_parts hα1 hα2 d hd hq hlin κ₀ hζ.1]
  exact tendsto_nhds_unique h0 tendsto_const_nhds

theorem heldResidualLimit_holds : HeldResidualLimitStatement :=
  heldResidualLimit_of localStrongSubseq

end SteadyCert

end Breakdown

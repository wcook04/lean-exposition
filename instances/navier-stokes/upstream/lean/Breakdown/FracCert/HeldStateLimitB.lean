import Breakdown.FracCert.HeldStateLimitBParts
import Breakdown.FracCert.HeldStateLimitBBound
import Breakdown.FracCert.HeldStateLimitBWeak
import Breakdown.FracCert.HeldStateLimitBExtract
import Breakdown.FracCert.DriftSymbolWeak
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.FracCert.GradientOrthogonal
import Breakdown.FracCert.QuadraticSquare

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

private theorem pair_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

private theorem residual_expand {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
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

private theorem residual_memLp {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p v G H P) (κ : Fin k → ℝ) :
    MemLp (d.heldResidual α p v G H P κ) 2 volume := by
  rw [residual_expand]
  have hs : MemLp (fun y => ∑ i, (d.multiplier p i + κ i) • d.actuator i y) 2 volume :=
    memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i + κ i)
  exact ((((hst.drift.add (hd.profile_drift p hp)).add hst.power.1).add (hd.profile_power p hp).1).add
    (heldQuadraticL2_of quadraticSquareIntegrable α hα1 hα2 d hd p hp v G H hst.second)).add hs

private theorem residual_sum {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (y : Space) :
    d.heldResidual α p v G H P κ y = d.heldResidual α p v G H P 0 y + ∑ i, κ i • d.actuator i y := by
  simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField, Pi.zero_apply,
    zero_smul, Finset.sum_const_zero, add_zero]
  abel

private theorem residual_pairing {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (ζ : Space → Space) (h0 : MemLp (d.heldResidual α p v G H P 0) 2 volume)
    (hζ : MemLp ζ 2 volume) (ha : ∀ i, MemLp (d.actuator i) 2 volume) :
    ∫ y, inner ℝ (d.heldResidual α p v G H P κ y) (ζ y) =
      (∫ y, inner ℝ (d.heldResidual α p v G H P 0 y) (ζ y)) +
        ∑ i, κ i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
  have e : (fun y => inner ℝ (d.heldResidual α p v G H P κ y) (ζ y)) = fun y =>
      inner ℝ (d.heldResidual α p v G H P 0 y) (ζ y) + ∑ i, κ i * inner ℝ (d.actuator i y) (ζ y) := by
    funext y
    rw [residual_sum, inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  have i1 := pair_integrable h0 hζ
  have i2 : Integrable (fun y => ∑ i, κ i * inner ℝ (d.actuator i y) (ζ y)) :=
    integrable_finsetSum _ (fun i _ => (pair_integrable (ha i) hζ).const_mul (κ i))
  rw [e, integral_add i1 i2, integral_finsetSum _ (fun i _ => (pair_integrable (ha i) hζ).const_mul (κ i))]
  simp only [integral_const_mul]

private theorem held_orthogonal {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
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

private theorem energy_nonneg' {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : 0 ≤ d.energy G H := by
  unfold FracCertData.energy weightedEnergy
  refine add_nonneg (integral_nonneg fun y => sq_nonneg _) (integral_nonneg fun y => ?_)
  refine mul_nonneg ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact le_trans hd.weightMin_pos.le (hd.weight_lower y)

private theorem multiplier_coord_bound {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ)
    {R : ℝ} (hR : d.size G H κ ≤ R) (i : Fin k) : d.multiplierScale * |κ i| ≤ R := by
  have hμ := hd.multiplierScale_pos
  have h0 : 0 ≤ d.size G H κ := Real.sqrt_nonneg _
  have hsq : d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
    unfold FracCertData.size sizeNorm
    rw [Real.sq_sqrt]
    · rfl
    · exact add_nonneg (energy_nonneg' d hd G H)
        (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
  have h1 : (d.multiplierScale * |κ i|) ^ 2 ≤ d.size G H κ ^ 2 := by
    rw [hsq, mul_pow, sq_abs]
    have : κ i ^ 2 ≤ ∑ j, κ j ^ 2 :=
      Finset.single_le_sum (f := fun j => κ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [energy_nonneg' d hd G H, sq_nonneg d.multiplierScale]
  exact ((pow_le_pow_iff_left₀ (mul_nonneg hμ.le (abs_nonneg _)) h0 two_ne_zero).1 h1).trans hR

theorem heldStateLimit_of_bounds (h1 : HeldUniformBoundStatement) (h2 : HeldBoundedLimitStatement) :
    HeldStateLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R hsol hsize
  obtain ⟨B, hB⟩ := h1 α hα1 hα2 d hd R
  have hμ := hd.multiplierScale_pos
  have hbd : ∀ n, κ n ∈ Metric.closedBall (0 : Fin k → ℝ) (R / d.multiplierScale) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hR0 : 0 ≤ R := le_trans (Real.sqrt_nonneg _) (hsize n)
    refine (pi_norm_le_iff_of_nonneg (div_nonneg hR0 hμ.le)).2 fun i => ?_
    rw [Real.norm_eq_abs, le_div_iff₀ hμ, mul_comm]
    exact multiplier_coord_bound d hd _ _ _ (hsize n) i
  obtain ⟨κ₀, -, φ₁, hφ₁, hκ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  obtain ⟨φ₂, hφ₂, u₀, G₀, H₀, P₀, hst, hlsc, hG, horth⟩ :=
    h2 α hα1 hα2 d hd (fun n => p (φ₁ n)) q (fun n => hp (φ₁ n)) hq (hpq.comp hφ₁.tendsto_atTop)
      (fun n => u (φ₁ n)) (fun n => G (φ₁ n)) (fun n => H (φ₁ n)) (fun n => P (φ₁ n)) (fun n => κ (φ₁ n))
      R B κ₀ (fun n => hsol (φ₁ n)) (fun n => hsize (φ₁ n))
      (fun n => hB (p (φ₁ n)) (hp (φ₁ n)) _ _ _ _ _ (hsol (φ₁ n)) (hsize (φ₁ n))) hκ
  refine ⟨fun n => φ₁ (φ₂ n), hφ₁.comp hφ₂, u₀, G₀, H₀, P₀, hst, hlsc, hG, ?_⟩
  intro ζ hζ
  have h0 := residual_memLp hα1 hα2 d hd hq hst 0
  have hlim : ∫ y, inner ℝ (d.heldResidual α q u₀ G₀ H₀ P₀ 0 y) (ζ y) =
      -∑ i, κ₀ i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
    have e := residual_pairing d α q u₀ G₀ H₀ P₀ κ₀ ζ h0 hζ.1 hd.actuator_two
    rw [horth ζ hζ] at e
    linarith
  have hseq : (fun n => ∫ y, inner ℝ (d.heldResidual α (p (φ₁ (φ₂ n))) (u (φ₁ (φ₂ n))) (G (φ₁ (φ₂ n)))
      (H (φ₁ (φ₂ n))) (P (φ₁ (φ₂ n))) 0 y) (ζ y)) =
      fun n => -∑ i, κ (φ₁ (φ₂ n)) i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
    funext n
    have hn := hsol (φ₁ (φ₂ n))
    have e := residual_pairing d α _ _ _ _ _ (κ (φ₁ (φ₂ n))) ζ
      (residual_memLp hα1 hα2 d hd (hp (φ₁ (φ₂ n))) hn.state 0) hζ.1 hd.actuator_two
    rw [held_orthogonal hα1 hα2 d hd (hp (φ₁ (φ₂ n))) hn ζ hζ] at e
    linarith
  rw [hseq, hlim]
  refine Filter.Tendsto.neg (tendsto_finsetSum _ fun i _ => ?_)
  exact ((((continuous_apply i).tendsto κ₀).comp (hκ.comp hφ₂.tendsto_atTop))).mul_const _

private theorem trace_memLp' {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (fun y => secondTrace (H y)) 2 volume := by
  have h := (Internal.DriftSymbolWeak.memLp_negSecondTrace hs).neg
  exact h.ae_eq (ae_of_all _ fun y => by simp [negSecondTrace])

open WeakFieldLimit in
theorem heldBoundedLimit_of (h : HeldLimitIdentifyStatement) : HeldBoundedLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R B κ₀ hsol hsize hB hκ
  obtain ⟨φ, hφ, u₀, G₀, H₀, P₀, hst, hGw, hTw, horth⟩ :=
    h α hα1 hα2 d hd p q hp hq hpq u G H P κ R B κ₀ hsol hsize hB hκ
  have hGc : ∀ n i, MemLp (fun y => G (φ n) y (unitVector i)) 2 volume := fun n i =>
    LinearStateClosedInternal.col_memLp (hsol (φ n)).state.second.measurable_gradient
      (hsol (φ n)).state.second.gradient_two i
  have hG₀c : ∀ i, MemLp (fun y => G₀ y (unitVector i)) 2 volume := fun i =>
    LinearStateClosedInternal.col_memLp hst.second.measurable_gradient hst.second.gradient_two i
  refine ⟨φ, hφ, u₀, G₀, H₀, P₀, hst, ?_, fun E hE hEi => entryInner_tendsto hGc hG₀c hGw E hE hEi, horth⟩
  intro ε hε
  have h1 := weighted_entry_lsc hGc hG₀c hGw hd.weight_measurable
    (fun y => hd.weightMin_pos.le.trans (hd.weight_lower y)) hd.weight_upper (ε / 2) (by linarith)
  have h2 := weighted_lsc (fun n => trace_memLp' (hsol (φ n)).state.second) (trace_memLp' hst.second)
    (w := fun _ => (1 : ℝ)) (wmax := 1) measurable_const (fun _ => zero_le_one) (fun _ => le_refl 1) hTw
    (ε / 2) (by linarith)
  filter_upwards [h1, h2] with n h1 h2
  simp only [one_mul] at h2
  unfold FracCertData.energy weightedEnergy
  linarith

end SteadyCert

end Breakdown

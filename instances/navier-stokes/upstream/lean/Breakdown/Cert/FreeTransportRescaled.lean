import Breakdown.Cert.GradInvSpec
import Breakdown.Cert.FreeTransportReading

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.PropagatorDerivative

def spaceSsp (g : Space → Space) (y : Space) : Space :=
  ∑ j : Fin 3, fderiv ℝ (fun w => fderiv ℝ g w (unitVector j)) y (unitVector j)

def rescaledTest (χ : ℝ → Space → Space) (r : ℝ) (z : Space) : Space := χ r (Real.exp (r / 2) • z)

theorem isHalfSspOf_heat_smoothH {s : ℝ} (hs : 0 < s) (x : HBar) :
    IsHalfSspOf (heatX s x) (smoothH s x) := by
  have h1 := Freq.Internal.Phi.scalarOp_ae fieldOpRealized (Freq.Internal.Phi.continuous_phiFactor s)
    (Freq.Internal.Phi.phiFactor_le hs) (x : L2C)
  rw [← GradInv.Internal.smoothH_coe hs] at h1
  have h2 := Freq.Internal.Phi.scalarOp_ae fieldOpRealized (Freq.Internal.Phi.continuous_heatFactor s)
    (Freq.Internal.Phi.heatFactor_le s) (x : L2C)
  have e : (heatX s x : L2C) = fieldOp id (fun ξ => heatFactor s ξ • ContinuousLinearMap.id ℝ CSpace) x :=
    heat_holds.2.2.2.2.2 s x
  rw [← e] at h2
  filter_upwards [h1, h2] with ξ a b
  rw [a, b, smul_smul]
  congr 1
  simp only [phiFactor, heatFactor, max_eq_left hs.le]

theorem velocity_slicePropagator_ae {r : ℝ} (hr : 0 < r) (x : HBar) :
    (velocity (slicePropagator r x) : Space → Space) =ᵐ[volume]
      dilateField (Real.exp (-r)) (toPhysH (heatX (1 - Real.exp (-r)) x) : Space → Space) := by
  have hs : 0 < 1 - Real.exp (-r) := GradInv.Internal.one_sub_exp_pos hr
  have hμ : 0 < Real.exp (-r) := Real.exp_pos _
  have h1 := velocityCov_holds.2 _ hμ (smoothH (1 - Real.exp (-r)) x)
  have h2 := velocityInverts_holds _ _ (isHalfSspOf_heat_smoothH hs x)
  have hq : Measure.QuasiMeasurePreserving (fun y : Space => Real.sqrt (Real.exp (-r)) • y) volume volume :=
    Measure.quasiMeasurePreserving_smul volume (Real.sqrt_pos.2 hμ).ne'
  have h3 : dilateField (Real.exp (-r)) (velocity (smoothH (1 - Real.exp (-r)) x) : Space → Space) =ᵐ[volume]
      dilateField (Real.exp (-r)) (toPhysH (heatX (1 - Real.exp (-r)) x) : Space → Space) := by
    filter_upwards [hq.ae_eq h2] with y hy
    simp only [dilateField, Function.comp_apply] at hy ⊢
    rw [hy]
    rfl
  have e : slicePropagator r x = dilX (Real.exp (-r)) (smoothH (1 - Real.exp (-r)) x) := rfl
  rw [e]
  exact h1.trans h3

theorem integral_inner_dilateField {μ : ℝ} (hμ : 0 < μ) (g G : Space → Space) :
    ∫ y, inner ℝ (dilateField μ g y) (G y) =
      μ⁻¹ * ∫ z, inner ℝ (g z) (G ((Real.sqrt μ)⁻¹ • z)) := by
  have hc : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ
  have e : (fun y => inner ℝ (dilateField μ g y) (G y)) =
      fun y => Real.sqrt μ * (fun z => inner ℝ (g z) (G ((Real.sqrt μ)⁻¹ • z))) (Real.sqrt μ • y) := by
    funext y
    simp only [dilateField, real_inner_smul_left, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  rw [e, integral_const_mul, Measure.integral_comp_smul (μ := volume)
    (f := fun z => inner ℝ (g z) (G ((Real.sqrt μ)⁻¹ • z))) (R := Real.sqrt μ), finrank_euclideanSpace_fin,
    smul_eq_mul, ← mul_assoc]
  congr 1
  have h2 : Real.sqrt μ ^ 2 = μ := Real.sq_sqrt hμ.le
  have h3 : Real.sqrt μ ^ 3 = μ * Real.sqrt μ := by rw [pow_succ, h2]
  rw [abs_of_pos (inv_pos.2 (pow_pos hc 3)), h3]
  field_simp

theorem sqrt_exp_neg (r : ℝ) : Real.sqrt (Real.exp (-r)) = Real.exp (-(r / 2)) := by
  rw [show Real.exp (-r) = Real.exp (-(r / 2)) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf]
  exact Real.sqrt_sq (Real.exp_pos _).le

theorem integral_inner_velocity_slicePropagator {r : ℝ} (hr : 0 < r) (x : HBar) (G : Space → Space) :
    ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (G y) =
      Real.exp r * ∫ z, inner ℝ ((toPhysH (heatX (1 - Real.exp (-r)) x) : Space → Space) z)
        (G (Real.exp (r / 2) • z)) := by
  have hae : (fun y => inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (G y)) =ᵐ[volume]
      fun y => inner ℝ (dilateField (Real.exp (-r)) (toPhysH (heatX (1 - Real.exp (-r)) x) : Space → Space) y)
        (G y) :=
    (velocity_slicePropagator_ae hr x).mono fun y hy => by
      show inner ℝ _ (G y) = inner ℝ _ (G y)
      rw [hy]
  have e1 : (Real.exp (-r))⁻¹ = Real.exp r := by rw [Real.exp_neg, inv_inv]
  have e2 : (Real.exp (-(r / 2)))⁻¹ = Real.exp (r / 2) := by rw [Real.exp_neg, inv_inv]
  rw [integral_congr_ae hae, integral_inner_dilateField (Real.exp_pos _), sqrt_exp_neg, e1, e2]

theorem integral_inner_eq_inner_toLp (f : L2R) {G : Space → Space} (hG : MemLp G 2 volume) :
    ∫ z, inner ℝ ((f : Space → Space) z) (G z) = inner ℝ f (toLpOrZero 2 G) := by
  rw [L2.inner_def]
  have h : (toLpOrZero 2 G : Space → Space) =ᵐ[volume] G := by
    unfold toLpOrZero
    rw [dif_pos hG]
    exact hG.coeFn_toLp
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

theorem toLpOrZero_add {A B : Space → Space} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    toLpOrZero 2 (A + B) = toLpOrZero 2 A + toLpOrZero 2 B := by
  unfold toLpOrZero
  rw [dif_pos (hA.add hB), dif_pos hA, dif_pos hB]
  exact MemLp.toLp_add hA hB

theorem toLpOrZero_smul (c : ℝ) {A : Space → Space} (hA : MemLp A 2 volume) :
    toLpOrZero 2 (c • A) = c • toLpOrZero 2 A := by
  unfold toLpOrZero
  rw [dif_pos (hA.const_smul c), dif_pos hA]
  exact MemLp.toLp_const_smul c hA

theorem isSpaceTimeTestVector_rescaled {χ : ℝ → Space → Space} (hχ : IsSpaceTimeTestVector χ) :
    IsSpaceTimeTestVector (rescaledTest χ) := by
  have hm : ContDiff ℝ ∞ (fun p : ℝ × Space => ((p.1, Real.exp (p.1 / 2) • p.2) : ℝ × Space)) :=
    contDiff_fst.prodMk (((contDiff_fst.div_const 2).exp).smul contDiff_snd)
  refine ⟨hχ.1.comp hm, ?_⟩
  have hc : Continuous (fun p : ℝ × Space => ((p.1, Real.exp (-(p.1 / 2)) • p.2) : ℝ × Space)) :=
    continuous_fst.prodMk (((continuous_fst.div_const 2).neg.rexp).smul continuous_snd)
  refine HasCompactSupport.intro (hχ.2.isCompact.image hc) fun p hp => ?_
  refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => χ z.1 z.2)
    (x := ((p.1, Real.exp (p.1 / 2) • p.2) : ℝ × Space)) fun ht => hp ?_
  refine ⟨_, ht, Prod.ext rfl ?_⟩
  show Real.exp (-(p.1 / 2)) • Real.exp (p.1 / 2) • p.2 = p.2
  rw [smul_smul, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_smul]

theorem deriv_rescaled {χ : ℝ → Space → Space} (hχ : ContDiff ℝ ∞ (fun z : ℝ × Space => χ z.1 z.2))
    (τ : ℝ) (z : Space) :
    deriv (fun r => rescaledTest χ r z) τ =
      deriv (fun r => χ r (Real.exp (τ / 2) • z)) τ +
        (1 / 2 : ℝ) • fderiv ℝ (χ τ) (Real.exp (τ / 2) • z) (Real.exp (τ / 2) • z) := by
  have hd : DifferentiableAt ℝ (fun q : ℝ × Space => χ q.1 q.2) (τ, Real.exp (τ / 2) • z) :=
    (hχ.differentiable (by simp)) _
  have hγ : HasDerivAt (fun r : ℝ => ((r, Real.exp (r / 2) • z) : ℝ × Space))
      ((1 : ℝ), (Real.exp (τ / 2) * (1 / 2)) • z) τ := by
    refine (hasDerivAt_id' τ).prodMk ?_
    have h1 : HasDerivAt (fun r : ℝ => r / 2) (1 / 2) τ := (hasDerivAt_id' τ).div_const 2
    exact h1.exp.smul_const z
  have h2 := (hd.hasFDerivAt.comp_hasDerivAt τ hγ).deriv
  have h3a := (hd.hasFDerivAt.comp τ (hasFDerivAt_prodMk_left τ (Real.exp (τ / 2) • z))).hasDerivAt.deriv
  have h3 : deriv (fun r => χ r (Real.exp (τ / 2) • z)) τ =
      fderiv ℝ (fun q : ℝ × Space => χ q.1 q.2) (τ, Real.exp (τ / 2) • z)
        (ContinuousLinearMap.inl ℝ ℝ Space 1) := h3a
  have h4 : fderiv ℝ (χ τ) (Real.exp (τ / 2) • z) =
      (fderiv ℝ (fun q : ℝ × Space => χ q.1 q.2) (τ, Real.exp (τ / 2) • z)).comp
        (ContinuousLinearMap.inr ℝ ℝ Space) :=
    (hd.hasFDerivAt.comp (Real.exp (τ / 2) • z) (hasFDerivAt_prodMk_right τ (Real.exp (τ / 2) • z))).fderiv
  have e : (((1 : ℝ), (Real.exp (τ / 2) * (1 / 2)) • z) : ℝ × Space) =
      ContinuousLinearMap.inl ℝ ℝ Space 1 +
        ContinuousLinearMap.inr ℝ ℝ Space ((1 / 2 : ℝ) • Real.exp (τ / 2) • z) := by
    refine Prod.ext ?_ ?_
    · simp
    · simp only [Prod.snd_add, ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, zero_add,
        smul_smul, mul_comm]
  have h5 : deriv (fun r => rescaledTest χ r z) τ =
      deriv ((fun q : ℝ × Space => χ q.1 q.2) ∘ fun r : ℝ => ((r, Real.exp (r / 2) • z) : ℝ × Space)) τ := rfl
  rw [h5, h2, e, map_add, h3, h4, ContinuousLinearMap.comp_apply, map_smul, map_smul]

private theorem fderiv_comp_const_smul {g : Space → Space} (hg : Differentiable ℝ g) (c : ℝ) (w v : Space) :
    fderiv ℝ (fun w => g (c • w)) w v = c • fderiv ℝ g (c • w) v := by
  have h := ((hg (c • id w)).hasFDerivAt.comp w ((hasFDerivAt_id w).const_smul c)).fderiv
  have e : (fun w => g (c • w)) = g ∘ HSMul.hSMul c := rfl
  rw [e, h]
  simp

theorem spaceSsp_rescaled {χ : ℝ → Space → Space} (hχ : ContDiff ℝ ∞ (fun z : ℝ × Space => χ z.1 z.2))
    (τ : ℝ) (z : Space) :
    spaceSsp (rescaledTest χ τ) z = Real.exp τ • spaceSsp (χ τ) (Real.exp (τ / 2) • z) := by
  have hg : ContDiff ℝ ∞ (χ τ) := Internal.FreePerturbation.contDiff_slice hχ τ
  have hgd : Differentiable ℝ (χ τ) := hg.differentiable (by simp)
  have hj : ∀ j : Fin 3, Differentiable ℝ (fun u => fderiv ℝ (χ τ) u (unitVector j)) := fun j =>
    ((contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const).differentiable (by simp)
  have hc : Real.exp (τ / 2) * Real.exp (τ / 2) = Real.exp τ := by rw [← Real.exp_add]; ring_nf
  have e1 : rescaledTest χ τ = fun w => χ τ (Real.exp (τ / 2) • w) := rfl
  have key : ∀ j : Fin 3,
      fderiv ℝ (fun w => fderiv ℝ (rescaledTest χ τ) w (unitVector j)) z (unitVector j) =
        Real.exp τ • fderiv ℝ (fun u => fderiv ℝ (χ τ) u (unitVector j)) (Real.exp (τ / 2) • z) (unitVector j) := by
    intro j
    have e2 : (fun w => fderiv ℝ (rescaledTest χ τ) w (unitVector j)) =
        fun w => Real.exp (τ / 2) • (fun u => fderiv ℝ (χ τ) u (unitVector j)) (Real.exp (τ / 2) • w) := by
      funext w
      rw [e1, fderiv_comp_const_smul hgd]
    have hdiff : DifferentiableAt ℝ
        (fun w => (fun u => fderiv ℝ (χ τ) u (unitVector j)) (Real.exp (τ / 2) • w)) z :=
      ((hj j).comp (differentiable_id.const_smul (Real.exp (τ / 2)))) z
    have hfd : fderiv ℝ (fun w => Real.exp (τ / 2) •
        (fun u => fderiv ℝ (χ τ) u (unitVector j)) (Real.exp (τ / 2) • w)) z =
        Real.exp (τ / 2) • fderiv ℝ (fun w => (fun u => fderiv ℝ (χ τ) u (unitVector j)) (Real.exp (τ / 2) • w)) z :=
      (hdiff.hasFDerivAt.const_smul (Real.exp (τ / 2))).fderiv
    rw [e2, hfd, smul_apply, fderiv_comp_const_smul (hj j), smul_smul, hc]
  simp only [spaceSsp]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => key j

theorem memLp_slice {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) (r : ℝ) :
    MemLp (φ r) 2 volume :=
  (Internal.FreePerturbation.contDiff_slice hφ.1 r).continuous.memLp_of_hasCompactSupport (Internal.FreePerturbation.hasCompactSupport_slice hφ.2 r)

theorem memLp_timeDeriv {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) (τ : ℝ) :
    MemLp (fun y => deriv (fun r => φ r y) τ) 2 volume := by
  have e : (fun y => deriv (fun r => φ r y) τ) = fun y =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) (ContinuousLinearMap.inl ℝ ℝ Space 1) := by
    funext y
    have hd : DifferentiableAt ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) := (hφ.1.differentiable (by simp)) _
    exact (hd.hasFDerivAt.comp τ (hasFDerivAt_prodMk_left τ y)).hasDerivAt.deriv
  rw [e]
  have hc : Continuous (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) _
  exact (hc.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
    (Internal.FreePerturbation.hasCompactSupport_slice (φ := fun s y =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)) hs τ)

theorem memLp_spaceSsp {g : Space → Space} (hg : ContDiff ℝ ∞ g) (hgs : HasCompactSupport g) :
    MemLp (spaceSsp g) 2 volume := by
  have hj : ∀ j : Fin 3, Continuous (fun y => fderiv ℝ (fun w => fderiv ℝ g w (unitVector j)) y (unitVector j)) ∧
      HasCompactSupport (fun y => fderiv ℝ (fun w => fderiv ℝ g w (unitVector j)) y (unitVector j)) := by
    intro j
    have h1 : ContDiff ℝ ∞ (fun w => fderiv ℝ g w (unitVector j)) :=
      (contDiff_infty_iff_fderiv.1 hg).2.clm_apply contDiff_const
    have h2 : HasCompactSupport (fun w => fderiv ℝ g w (unitVector j)) := hgs.fderiv_apply (𝕜 := ℝ) _
    exact ⟨(h1.continuous_fderiv (by simp)).clm_apply continuous_const, h2.fderiv_apply (𝕜 := ℝ) _⟩
  have e : spaceSsp g =
      (fun y => fderiv ℝ (fun w => fderiv ℝ g w (unitVector 0)) y (unitVector 0)) +
      (fun y => fderiv ℝ (fun w => fderiv ℝ g w (unitVector 1)) y (unitVector 1)) +
      (fun y => fderiv ℝ (fun w => fderiv ℝ g w (unitVector 2)) y (unitVector 2)) := by
    funext y
    simp only [spaceSsp, Fin.sum_univ_three, Pi.add_apply]
  rw [e]
  exact (((hj 0).1.add (hj 1).1).add (hj 2).1).memLp_of_hasCompactSupport
    (((hj 0).2.add (hj 1).2).add (hj 2).2)

private theorem toLpOrZero_sub {A B : Space → Space} (hA : MemLp A 2 volume) (hB : MemLp B 2 volume) :
    toLpOrZero 2 (A - B) = toLpOrZero 2 A - toLpOrZero 2 B := by
  unfold toLpOrZero
  rw [dif_pos (hA.sub hB), dif_pos hA, dif_pos hB]
  exact MemLp.toLp_sub hA hB

private theorem norm_toLpOrZero_le {f : Space → Space} (hf : MemLp f 2 volume) {C ρ : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y, ‖f y‖ ≤ C) (hs : ∀ y, ρ < ‖y‖ → f y = 0) :
    ‖(toLpOrZero 2 f : L2R)‖ ≤ (volume (Metric.closedBall (0 : Space) ρ) ^ (1 / 2 : ℝ)).toReal * C := by
  have hB : MeasurableSet (Metric.closedBall (0 : Space) ρ) := Metric.isClosed_closedBall.measurableSet
  have e0 : ‖(toLpOrZero 2 f : L2R)‖ = (eLpNorm f 2 volume).toReal := by
    unfold toLpOrZero
    rw [dif_pos hf]
    exact Lp.norm_toLp f hf
  have e1 : f = (Metric.closedBall (0 : Space) ρ).indicator f := by
    funext y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) ρ
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      refine hs y ?_
      rw [Metric.mem_closedBall, dist_zero_right, not_le] at hy
      exact hy
  have h2 : eLpNorm f 2 volume ≤
      volume (Metric.closedBall (0 : Space) ρ) ^ (1 / 2 : ℝ) * ENNReal.ofReal C := by
    rw [e1, eLpNorm_indicator_eq_eLpNorm_restrict hB]
    have h3 := eLpNorm_le_of_ae_bound (μ := volume.restrict (Metric.closedBall (0 : Space) ρ)) (p := 2)
      (ae_of_all _ hb)
    rw [Measure.restrict_apply_univ] at h3
    simpa using h3
  have hfin : volume (Metric.closedBall (0 : Space) ρ) ^ (1 / 2 : ℝ) * ENNReal.ofReal C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne)
      ENNReal.ofReal_ne_top
  rw [e0]
  refine (ENNReal.toReal_mono hfin h2).trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC]

private theorem support_bound {φ : ℝ → Space → Space}
    (hφ : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) :
    ∃ ρ : ℝ, ∀ y : Space, ρ < ‖y‖ → ∀ s, φ s y = 0 := by
  obtain ⟨ρ, hρ⟩ := hφ.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  refine ⟨ρ, fun y hy s => ?_⟩
  refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) (x := (s, y)) fun ht => ?_
  have h1 := hρ ht
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  exact absurd ((norm_snd_le ((s, y) : ℝ × Space)).trans h1) (not_le.2 hy)

private theorem remainder_bound {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ r : ℝ, ∀ y : Space,
      ‖φ r y - φ τ y - (r - τ) • deriv (fun s => φ s y) τ‖ ≤ M * |r - τ| ^ 2 := by
  have hDc : ContDiff ℝ ∞ (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1)) :=
    (contDiff_infty_iff_fderiv.1 hφ.1).2.clm_apply contDiff_const
  have hDs : HasCompactSupport (fun z : ℝ × Space =>
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inl ℝ ℝ Space 1)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) _
  obtain ⟨M, hM⟩ := (hDc.continuous_fderiv (by simp)).bounded_above_of_compact_support
    (hDs.fderiv (𝕜 := ℝ))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hderiv : ∀ (s : ℝ) (y : Space), HasDerivAt (fun t => φ t y)
      (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)) s := by
    intro s y
    have hd : DifferentiableAt ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) := (hφ.1.differentiable (by simp)) _
    exact (hd.hasFDerivAt.comp s (hasFDerivAt_prodMk_left s y)).hasDerivAt
  have hincr : ∀ (s t : ℝ) (y : Space),
      ‖fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) (ContinuousLinearMap.inl ℝ ℝ Space 1) -
        fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (t, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)‖ ≤
        M * |s - t| := by
    intro s t y
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (s := Set.univ)
      (x := ((t, y) : ℝ × Space)) (y := ((s, y) : ℝ × Space))
      (fun z _ => (hDc.differentiable (by simp)) z) (fun z _ => hM z) convex_univ trivial trivial
    have e : ‖((s, y) : ℝ × Space) - (t, y)‖ = |s - t| := by
      rw [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero, Real.norm_eq_abs]
      exact max_eq_left (abs_nonneg _)
    rw [e] at h
    exact h
  refine ⟨M, hM0, fun τ r y => ?_⟩
  have hg : ∀ t : ℝ, HasDerivAt (fun t => φ t y - (t - τ) •
      fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) (ContinuousLinearMap.inl ℝ ℝ Space 1))
      (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (t, y) (ContinuousLinearMap.inl ℝ ℝ Space 1) -
        fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)) t := by
    intro t
    have h2 := ((hasDerivAt_id t).sub_const τ).smul_const
      (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) (ContinuousLinearMap.inl ℝ ℝ Space 1))
    exact ((hderiv t y).sub h2).congr_deriv (by rw [one_smul])
  have hb : ∀ t ∈ Metric.closedBall τ |r - τ|,
      ‖fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (t, y) (ContinuousLinearMap.inl ℝ ℝ Space 1) -
        fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y) (ContinuousLinearMap.inl ℝ ℝ Space 1)‖ ≤
        M * |r - τ| := by
    intro t ht
    rw [Metric.mem_closedBall, Real.dist_eq] at ht
    exact (hincr t τ y).trans (mul_le_mul_of_nonneg_left ht hM0)
  have h := (convex_closedBall τ |r - τ|).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun t _ => (hg t).hasDerivWithinAt) hb (Metric.mem_closedBall_self (abs_nonneg _))
    (by rw [Metric.mem_closedBall, Real.dist_eq])
  have e1 : (φ r y - (r - τ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y)
        (ContinuousLinearMap.inl ℝ ℝ Space 1)) -
      (φ τ y - (τ - τ) • fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (τ, y)
        (ContinuousLinearMap.inl ℝ ℝ Space 1)) =
      φ r y - φ τ y - (r - τ) • deriv (fun s => φ s y) τ := by
    rw [(hderiv τ y).deriv, sub_self, zero_smul, sub_zero]
    abel
  rw [e1, Real.norm_eq_abs] at h
  calc _ ≤ M * |r - τ| * |r - τ| := h
    _ = M * |r - τ| ^ 2 := by ring

theorem hasDerivAt_toLp_of_test {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) (τ : ℝ) :
    HasDerivAt (fun r => (toLpOrZero 2 (φ r) : L2R)) (toLpOrZero 2 (fun y => deriv (fun r => φ r y) τ)) τ := by
  have hR := remainder_bound hφ
  have hS := support_bound hφ.2
  have hd := memLp_timeDeriv hφ τ
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun r => ‖r - τ‖ ^ 2) ?_
    (Asymptotics.isLittleO_pow_sub_sub τ one_lt_two)
  refine Asymptotics.IsBigO.of_bound
    ((volume (Metric.closedBall (0 : Space) hS.choose) ^ (1 / 2 : ℝ)).toReal * hR.choose)
    (Eventually.of_forall fun r => ?_)
  have hm : MemLp (φ r - φ τ - (r - τ) • fun y => deriv (fun r => φ r y) τ) 2 volume :=
    ((memLp_slice hφ r).sub (memLp_slice hφ τ)).sub (hd.const_smul _)
  have e : toLpOrZero 2 (φ r) - toLpOrZero 2 (φ τ) - (r - τ) • toLpOrZero 2 (fun y => deriv (fun r => φ r y) τ) =
      (toLpOrZero 2 (φ r - φ τ - (r - τ) • fun y => deriv (fun r => φ r y) τ) : L2R) := by
    rw [toLpOrZero_sub ((memLp_slice hφ r).sub (memLp_slice hφ τ)) (hd.const_smul _),
      toLpOrZero_sub (memLp_slice hφ r) (memLp_slice hφ τ), toLpOrZero_smul _ hd]
  have hz : ∀ y : Space, hS.choose < ‖y‖ →
      (φ r - φ τ - (r - τ) • fun y => deriv (fun r => φ r y) τ) y = 0 := by
    intro y hy
    have h0 : (fun s => φ s y) = fun _ => (0 : Space) := funext (hS.choose_spec y hy)
    show φ r y - φ τ y - (r - τ) • deriv (fun s => φ s y) τ = 0
    rw [hS.choose_spec y hy r, hS.choose_spec y hy τ, h0, deriv_const, smul_zero, sub_zero, sub_zero]
  have hb := norm_toLpOrZero_le hm (mul_nonneg hR.choose_spec.1 (sq_nonneg |r - τ|))
    (fun y => hR.choose_spec.2 τ r y) hz
  rw [e]
  rw [Real.norm_eq_abs (‖r - τ‖ ^ 2), abs_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs]
  refine hb.trans (le_of_eq ?_)
  rw [sq_abs]
  ring

private theorem inner_realVec_eq (b : CSpace) (v : Space) :
    inner ℝ (realVec b) v = RCLike.re (inner ℂ (complexifyVec v) b) := by
  simp [realVec, complexifyVec, PiLp.inner_apply, Fin.sum_univ_three, Complex.mul_re, mul_comm]

private theorem inner_freqTrR_eq (c f : L2C) :
    inner ℂ (freqTrR c) f = inner ℂ c (freqTrInvR f) := by
  show inner ℂ (freqTrL2 c) f = inner ℂ c (freqTrL2.symm f)
  calc inner ℂ (freqTrL2 c) f = inner ℂ (freqTrL2 c) (freqTrL2 (freqTrL2.symm f)) := by
        rw [LinearIsometryEquiv.apply_symm_apply]
    _ = inner ℂ c (freqTrL2.symm f) := LinearIsometryEquiv.inner_map_map _ _ _

theorem integral_inner_toPhys_eq (f : L2C) {G : Space → Space} (hG : MemLp G 2 volume) :
    ∫ y, inner ℝ ((toPhys f : Space → Space) y) (G y) =
      RCLike.re (inner ℂ (freqTrR (complexify (toLpOrZero 2 G))) f) := by
  rw [inner_freqTrR_eq, L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
  have h1 : (toLpOrZero 2 G : Space → Space) =ᵐ[volume] G := by
    unfold toLpOrZero
    rw [dif_pos hG]
    exact hG.coeFn_toLp
  have h2 : (complexify (toLpOrZero 2 G) : Space → CSpace) =ᵐ[volume]
      fun y => complexifyVec ((toLpOrZero 2 G : Space → Space) y) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have h3 : (toPhys f : Space → Space) =ᵐ[volume]
      fun y => realVec ((freqTrInvR f : Space → CSpace) y) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  refine integral_congr_ae ?_
  filter_upwards [h1, h2, h3] with y a b c
  rw [c, b, a, inner_realVec_eq]

open LineDeriv FourierTransform SchwartzMap in
theorem integral_inner_ssp_of_isSspOf {g h : X} (hl : IsSspOf g h) {G : Space → Space}
    (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G) :
    ∫ y, inner ℝ ((toPhys h : Space → Space) y) (G y) =
      -∫ y, inner ℝ ((toPhys g : Space → Space) y) (spaceSsp G y) := by
  have hm : MemLp G 2 volume := hG.continuous.memLp_of_hasCompactSupport hGs
  have hmL : MemLp (spaceSsp G) 2 volume := memLp_spaceSsp hG hGs
  rw [integral_inner_toPhys_eq _ hm, integral_inner_toPhys_eq _ hmL]
  have hsm : ContDiff ℝ ∞ (fun x => complexifyVec (G x)) := complexifyVec.contDiff.comp hG
  have hcs : HasCompactSupport (fun x => complexifyVec (G x)) := hGs.comp_left (map_zero complexifyVec)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : 𝓢(Space, CSpace), ⇑Φ = fun x => complexifyVec (G x) :=
    ⟨hcs.toSchwartzMap hsm, rfl⟩
  have d0 : Differentiable ℝ G := Internal.EmbedNegSsp.differentiable_of_smooth hG
  have d1 : ∀ j, Differentiable ℝ (Internal.EmbedNegSsp.pd G j) := fun j =>
    Internal.EmbedNegSsp.differentiable_of_smooth (Internal.EmbedNegSsp.contDiff_pd hG j)
  have c1 : ∀ j, ⇑(∂_{unitVector j} Φ : 𝓢(Space, CSpace)) =
      fun x => complexifyVec (Internal.EmbedNegSsp.pd G j x) :=
    Internal.EmbedNegSsp.coe_lineDeriv_eq d0 hΦ
  have c2 : ∀ j, ⇑(∂_{unitVector j} (∂_{unitVector j} Φ) : 𝓢(Space, CSpace)) =
      fun x => complexifyVec (Internal.EmbedNegSsp.pd (Internal.EmbedNegSsp.pd G j) j x) := fun j =>
    Internal.EmbedNegSsp.coe_lineDeriv_eq (d1 j) (c1 j) j
  obtain ⟨Ψ, hΨdef⟩ : ∃ Ψ : 𝓢(Space, CSpace), Ψ = ∑ j, ∂_{unitVector j} (∂_{unitVector j} Φ) := ⟨_, rfl⟩
  have hΨ : ⇑Ψ = fun x => complexifyVec (spaceSsp G x) := by
    funext x
    rw [hΨdef]
    simp only [_root_.sum_apply, c2, spaceSsp, map_sum]
    rfl
  have hFΨ : ∀ ξ, 𝓕 Ψ ξ = (-(sspFactor ξ)) • 𝓕 Φ ξ := by
    intro ξ
    rw [hΨdef]
    simp only [fourier_sum, _root_.sum_apply, Internal.EmbedNegSsp.freqTr_pd_apply, smul_smul]
    rw [← Finset.sum_smul, ← Complex.coe_smul]
    congr 1
    have hn : ‖ξ‖ ^ 2 = ∑ j, ξ j ^ 2 := EuclideanSpace.real_norm_sq_eq ξ
    simp only [sspFactor, hn, Fin.sum_univ_three]
    push_cast
    linear_combination (4 * (Real.pi : ℂ) ^ 2 * (((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 +
      ((ξ 2 : ℝ) : ℂ) ^ 2)) * Complex.I_sq
  rw [Internal.EmbedNegSsp.complexify_toLpOrZero hΦ, Internal.EmbedNegSsp.complexify_toLpOrZero hΨ,
    Internal.EmbedNegSsp.freqTrR_toLp, Internal.EmbedNegSsp.freqTrR_toLp, ← map_neg]
  refine congrArg RCLike.re ?_
  rw [L2.inner_def, L2.inner_def, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hl, (𝓕 Φ).coeFn_toLp 2, (𝓕 Ψ).coeFn_toLp 2] with ξ a b c
  rw [a, b, c, hFΨ, ← Complex.coe_smul, ← Complex.coe_smul, inner_smul_right, inner_smul_left,
    Complex.conj_ofReal]
  push_cast
  ring

theorem pairing_eq_inner_rescaled (x : HBar) {χ : ℝ → Space → Space} (hχ : IsSpaceTimeTestVector χ)
    {r : ℝ} (hr : 0 < r) :
    ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y) =
      Real.exp r * inner ℝ (toPhysH (heatX (1 - Real.exp (-r)) x)) (toLpOrZero 2 (rescaledTest χ r)) := by
  rw [integral_inner_velocity_slicePropagator hr x (χ r)]
  exact congrArg (fun a => Real.exp r * a)
    (integral_inner_eq_inner_toLp _ (memLp_slice (isSpaceTimeTestVector_rescaled hχ) r))

theorem inner_sspHeat_eq {s : ℝ} (hs : 0 < s) (x : HBar) (c : ℝ) {G : Space → Space}
    (hG : ContDiff ℝ ∞ G) (hGs : HasCompactSupport G) :
    inner ℝ (toPhysH (c • -(Freq.Internal.MildOfWeak.sspHeatX s x))) (toLpOrZero 2 G) =
      c * inner ℝ (toPhysH (heatX s x)) (toLpOrZero 2 (spaceSsp G)) := by
  have hGm : MemLp G 2 volume := hG.continuous.memLp_of_hasCompactSupport hGs
  have h := integral_inner_ssp_of_isSspOf
    (Freq.Internal.MildOfWeak.isSspOf_heat fieldOpRealized heat_holds hs x) hG hGs
  have h1 : inner ℝ (toPhysH (Freq.Internal.MildOfWeak.sspHeatX s x)) (toLpOrZero 2 G) =
      -inner ℝ (toPhysH (heatX s x)) (toLpOrZero 2 (spaceSsp G)) := by
    rw [← integral_inner_eq_inner_toLp _ hGm, ← integral_inner_eq_inner_toLp _ (memLp_spaceSsp hG hGs)]
    exact h
  rw [map_smul, map_neg, real_inner_smul_left, inner_neg_left, h1, neg_neg]

theorem rescaled_sum_eq {χ : ℝ → Space → Space} (hχ : ContDiff ℝ ∞ (fun z : ℝ × Space => χ z.1 z.2))
    (τ : ℝ) :
    (fun z => deriv (fun r => χ r (Real.exp (τ / 2) • z)) τ + spaceSsp (χ τ) (Real.exp (τ / 2) • z) +
      χ τ (Real.exp (τ / 2) • z) +
        (1 / 2 : ℝ) • fderiv ℝ (χ τ) (Real.exp (τ / 2) • z) (Real.exp (τ / 2) • z)) =
      (fun z => deriv (fun r => rescaledTest χ r z) τ) + Real.exp (-τ) • spaceSsp (rescaledTest χ τ) +
        rescaledTest χ τ := by
  funext z
  simp only [Pi.add_apply, Pi.smul_apply]
  rw [deriv_rescaled hχ τ z, spaceSsp_rescaled hχ τ z, smul_smul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, one_smul]
  simp only [rescaledTest]
  abel

theorem integral_inner_sum (f : L2R) {D L R : Space → Space} (hD : MemLp D 2 volume)
    (hL : MemLp L 2 volume) (hR : MemLp R 2 volume) (c : ℝ) :
    ∫ z, inner ℝ ((f : Space → Space) z) ((D + c • L + R) z) =
      inner ℝ f (toLpOrZero 2 D) + c * inner ℝ f (toLpOrZero 2 L) + inner ℝ f (toLpOrZero 2 R) := by
  rw [integral_inner_eq_inner_toLp _ ((hD.add (hL.const_smul c)).add hR),
    toLpOrZero_add (hD.add (hL.const_smul c)) hR, toLpOrZero_add hD (hL.const_smul c), toLpOrZero_smul c hL,
    inner_add_right, inner_add_right, real_inner_smul_right]

theorem pairing_value_eq (x : HBar) {χ : ℝ → Space → Space} (hχ : IsSpaceTimeTestVector χ)
    {τ : ℝ} (hτ : 0 < τ) :
    ∫ y, inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)
        (deriv (fun r => χ r y) τ + spaceSsp (χ τ) y + χ τ y + (1 / 2 : ℝ) • fderiv ℝ (χ τ) y y) =
      Real.exp τ * (inner ℝ (toPhysH (heatX (1 - Real.exp (-τ)) x))
          (toLpOrZero 2 (fun z => deriv (fun r => rescaledTest χ r z) τ)) +
        Real.exp (-τ) * inner ℝ (toPhysH (heatX (1 - Real.exp (-τ)) x))
          (toLpOrZero 2 (spaceSsp (rescaledTest χ τ))) +
        inner ℝ (toPhysH (heatX (1 - Real.exp (-τ)) x)) (toLpOrZero 2 (rescaledTest χ τ))) := by
  have hχt := isSpaceTimeTestVector_rescaled hχ
  have hD : MemLp (fun z => deriv (fun r => rescaledTest χ r z) τ) 2 volume := memLp_timeDeriv hχt τ
  have hL : MemLp (spaceSsp (rescaledTest χ τ)) 2 volume :=
    memLp_spaceSsp (Internal.FreePerturbation.contDiff_slice hχt.1 τ)
      (Internal.FreePerturbation.hasCompactSupport_slice hχt.2 τ)
  have hR : MemLp (rescaledTest χ τ) 2 volume := memLp_slice hχt τ
  exact (integral_inner_velocity_slicePropagator hτ x _).trans (congrArg (fun a => Real.exp τ * a)
    ((congrArg (fun g : Space → Space => ∫ z, inner ℝ
      ((toPhysH (heatX (1 - Real.exp (-τ)) x) : Space → Space) z) (g z)) (rescaled_sum_eq hχ.1 τ)).trans
      (integral_inner_sum _ hD hL hR _)))

theorem hasDerivAt_pairing_slicePropagator (x : HBar) {χ : ℝ → Space → Space}
    (hχ : IsSpaceTimeTestVector χ) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y))
      (∫ y, inner ℝ ((velocity (slicePropagator τ x) : Space → Space) y)
        (deriv (fun r => χ r y) τ + spaceSsp (χ τ) y + χ τ y + (1 / 2 : ℝ) • fderiv ℝ (χ τ) y y)) τ := by
  have hsτ : 0 < 1 - Real.exp (-τ) := GradInv.Internal.one_sub_exp_pos hτ
  have hχt := isSpaceTimeTestVector_rescaled hχ
  have hH : HasDerivAt (fun r => heatX r x) (-(Freq.Internal.MildOfWeak.sspHeatX (1 - Real.exp (-τ)) x))
      (1 - Real.exp (-τ)) :=
    Freq.Internal.MildOfWeak.heat_hasDerivAt fieldOpRealized heat_holds hsτ x
  have hs' : HasDerivAt (fun r : ℝ => 1 - Real.exp (-r)) (Real.exp (-τ)) τ := by
    have := ((hasDerivAt_neg τ).exp).const_sub 1
    simpa using this
  have hc : HasDerivAt (fun r => heatX (1 - Real.exp (-r)) x)
      (Real.exp (-τ) • -(Freq.Internal.MildOfWeak.sspHeatX (1 - Real.exp (-τ)) x)) τ :=
    HasDerivAt.scomp (g₁ := fun r => heatX r x) τ hH hs'
  have hF : HasDerivAt (fun r => toPhysH (heatX (1 - Real.exp (-r)) x))
      (toPhysH (Real.exp (-τ) • -(Freq.Internal.MildOfWeak.sspHeatX (1 - Real.exp (-τ)) x))) τ :=
    toPhysH.hasFDerivAt.comp_hasDerivAt τ hc
  have hC := hasDerivAt_toLp_of_test hχt τ
  have hP := (Real.hasDerivAt_exp τ).mul (hF.inner ℝ hC)
  have hk := inner_sspHeat_eq hsτ x (Real.exp (-τ)) (Internal.FreePerturbation.contDiff_slice hχt.1 τ)
    (Internal.FreePerturbation.hasCompactSupport_slice hχt.2 τ)
  have hev : (fun r => ∫ y, inner ℝ ((velocity (slicePropagator r x) : Space → Space) y) (χ r y)) =ᶠ[𝓝 τ]
      fun r => Real.exp r * inner ℝ (toPhysH (heatX (1 - Real.exp (-r)) x)) (toLpOrZero 2 (rescaledTest χ r)) := by
    filter_upwards [Ioi_mem_nhds hτ] with r hr
    exact pairing_eq_inner_rescaled x hχ hr
  refine (hP.congr_of_eventuallyEq hev).congr_deriv ?_
  rw [pairing_value_eq x hχ hτ, hk]
  ring

end Internal.PropagatorDerivative

end Breakdown.Cert

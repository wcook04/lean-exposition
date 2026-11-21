import Breakdown.Cert.ConvectionContinuity
import Breakdown.Cert.ExtendedNodes

open scoped ContDiff ENNReal NNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedConvectionContinuity

open Internal.Convection Internal.ConvectionContinuity

theorem profile_eq {k : ℕ} (d : ExtendedCertificateData k) :
    d.toCertificateData.profile = d.profile := rfl

theorem decay_nonneg {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) : 0 ≤ d.decay := by
  have h := (hd.profile_decay q hq 0 0).1
  simp only [norm_zero, add_zero, div_one] at h
  exact (norm_nonneg _).trans h

theorem slice_contDiff {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    (q : Fin k → ℝ) (σ : ℝ) : ContDiff ℝ 1 (d.profile q σ) :=
  hd.profile_smooth.comp (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id))

theorem square_le_tailWeight {D : ℝ} (hD : 0 ≤ D) (y : Space) :
    D / (1 + ‖y‖) ^ 2 ≤ D * tailWeight y := by
  have hpos : 0 < 1 + ‖y‖ := by positivity
  have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have e : D / (1 + ‖y‖) ^ 2 = D * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    rw [Real.rpow_neg hpos.le, Real.rpow_two, div_eq_mul_inv]
  rw [e, tailWeight]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)) hD

theorem second_part_first_order {W : Space → Space} (hW : ContDiff ℝ 1 W) {B : ℝ} (hB : 0 ≤ B)
    (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B * tailWeight y) (h : X) :
    MemLp (fun y => fderiv ℝ W y ((velocity h : Space → Space) y)) 2 volume ∧
      eLpNorm (fun y => fderiv ℝ W y ((velocity h : Space → Space) y)) 2 volume ≤
        ENNReal.ofReal (B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
  have hcf : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by norm_num)
  have hf : AEStronglyMeasurable (fderiv ℝ W) volume := hcf.aestronglyMeasurable
  have hg : AEStronglyMeasurable (velocity h : Space → Space) volume := Lp.aestronglyMeasurable _
  have hm : AEStronglyMeasurable (fun y => fderiv ℝ W y ((velocity h : Space → Space) y)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hf.prodMk hg)
  have hH : eLpNorm (fun y => fderiv ℝ W y ((velocity h : Space → Space) y)) 2 volume ≤
      ((1 : ℝ≥0) : ℝ≥0∞) * eLpNorm (fderiv ℝ W) 3 volume *
        eLpNorm (velocity h : Space → Space) 6 volume := by
    have := exponentTriple_three_six
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg (fun L x => L x) 1
      (ae_of_all _ fun y => by rw [one_mul]; exact ContinuousLinearMap.le_opNNNorm _ _)
  have hw : eLpNorm (fderiv ℝ W) 3 volume ≤ ENNReal.ofReal B * eLpNorm tailWeight 3 volume := by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (ae_of_all _ fun y => ?_) 3
    rw [Real.norm_eq_abs, abs_of_pos (tailWeight_pos y)]
    exact h1 y
  have hwc : eLpNorm tailWeight 3 volume = ENNReal.ofReal tailCube :=
    (ENNReal.ofReal_toReal tailWeight_memLp.eLpNorm_lt_top.ne).symm
  have hv : eLpNorm (velocity h : Space → Space) 6 volume ≤
      ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    rw [← Lp.enorm_def, ← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (ContinuousLinearMap.le_opNorm _ _)
  have hwc0 := tailCube_nonneg
  have hbound : eLpNorm (fun y => fderiv ℝ W y ((velocity h : Space → Space) y)) 2 volume ≤
      ENNReal.ofReal (B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
    refine hH.trans ?_
    rw [ENNReal.coe_one, one_mul]
    calc eLpNorm (fderiv ℝ W) 3 volume * eLpNorm (velocity h : Space → Space) 6 volume
        ≤ (ENNReal.ofReal B * ENNReal.ofReal tailCube) *
            ENNReal.ofReal (‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← hwc]
          exact mul_le_mul' hw hv
      _ = ENNReal.ofReal (B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖ * ‖h‖) := by
          rw [← ENNReal.ofReal_mul hB, ← ENNReal.ofReal_mul (mul_nonneg hB hwc0), mul_assoc _ ‖_‖]
  exact ⟨⟨hm, hbound.trans_lt ENNReal.ofReal_lt_top⟩, hbound⟩

theorem slice_bound_first_order {W : Space → Space} (hW : ContDiff ℝ 1 W) {A B : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (h0 : ∀ y, ‖W y‖ ≤ A) (h1 : ∀ y, ‖fderiv ℝ W y‖ ≤ B * tailWeight y) (h : X) :
    MemLp (sliceConvection W h) 2 volume ∧
      eLpNorm (sliceConvection W h) 2 volume ≤
        ENNReal.ofReal ((3 * A + B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖h‖) := by
  set t : Fin 3 → Space → Space := fun j y => (W y) j • (partialX j h : Space → Space) y with ht
  have hsum : (fun y => ∑ j : Fin 3, t j y) = ∑ j : Fin 3, t j := by
    funext y
    simp [Finset.sum_apply]
  have heq : sliceConvection W h = (∑ j : Fin 3, t j) +
      fun y => fderiv ℝ W y ((velocity h : Space → Space) y) := by
    rw [← hsum]
    rfl
  have hc : Continuous W := hW.continuous
  have h1m : MemLp (∑ j : Fin 3, t j) 2 volume :=
    memLp_finsetSum' _ fun j _ => (first_part hc hA h0 h j).1
  have h1b : eLpNorm (∑ j : Fin 3, t j) 2 volume ≤ ENNReal.ofReal (3 * (A * ‖h‖)) := by
    refine (eLpNorm_sum_le (fun j _ => (first_part hc hA h0 h j).1.1) (by norm_num)).trans ?_
    calc ∑ j : Fin 3, eLpNorm (t j) 2 volume ≤ ∑ _j : Fin 3, ENNReal.ofReal (A * ‖h‖) :=
          Finset.sum_le_sum fun j _ => (first_part hc hA h0 h j).2
      _ = ENNReal.ofReal (3 * (A * ‖h‖)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
  have h2 := second_part_first_order hW hB h1 h
  rw [heq]
  refine ⟨h1m.add h2.1, ?_⟩
  refine (eLpNorm_add_le h1m.1 h2.1.1 (by norm_num)).trans ?_
  refine (add_le_add h1b h2.2).trans ?_
  have hwc0 := tailCube_nonneg
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

theorem slice_memLp {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {q : Fin k → ℝ} (hq : q ∈ d.params) (σ : ℝ) (h : X) :
    MemLp (sliceConvection (d.profile q σ) h) 2 volume := by
  have hD := decay_nonneg hd hq
  refine (slice_bound_first_order (slice_contDiff hd q σ) hD hD (fun y => ?_) (fun y => ?_) h).1
  · refine (hd.profile_decay q hq σ y).1.trans ?_
    exact div_le_self hD (by linarith [norm_nonneg y])
  · exact (hd.profile_decay q hq σ y).2.1.trans (square_le_tailWeight hD y)

theorem convection_spec (h : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {q : Fin k → ℝ} (hq : q ∈ d.params) :
    ConvectionSpec d.toCertificateData q (convection d.toCertificateData q) := by
  have hex := (h d hd q hq).1
  unfold convection
  rw [dif_pos hex]
  exact hex.choose_spec

set_option maxHeartbeats 400000 in
theorem norm_sub_apply_le (h : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {p q : Fin k → ℝ} (hp : p ∈ d.params) (hq : q ∈ d.params)
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y, ‖d.profile q σ y - d.profile p σ y‖ ≤ A)
    (h1 : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ B * tailWeight y)
    (u : XX) :
    ‖convection d.toCertificateData q u - convection d.toCertificateData p u‖ ≤
      ‖solProj‖ * (3 * A + B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖gradCLM u‖ := by
  have hK : 0 ≤ 3 * A + B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖ := by
    have := tailCube_nonneg
    positivity
  have hgr : ((gradCLM u : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u
  have hsub : ((convection d.toCertificateData q u - convection d.toCertificateData p u : HH) :
      TimeCircle → HBar) =ᵐ[volume]
      ((convection d.toCertificateData q u : HH) : TimeCircle → HBar) -
        ((convection d.toCertificateData p u : HH) : TimeCircle → HBar) :=
    Lp.coeFn_sub _ _
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [hsub, convection_spec h hd hq u, convection_spec h hd hp u, hgr]
    with t hs hcq hcp hg
  simp only [hs, Pi.sub_apply, hcq, hcp, hg, profile_eq]
  have hσ := circleRep_mem t
  have dq : Differentiable ℝ (d.profile q (circleRep t)) :=
    (slice_contDiff hd q (circleRep t)).differentiable (by norm_num)
  have dp : Differentiable ℝ (d.profile p (circleRep t)) :=
    (slice_contDiff hd p (circleRep t)).differentiable (by norm_num)
  simp only [solField_sub (slice_memLp hd hq _ _) (slice_memLp hd hp _ _),
    ← sliceConvection_sub dq dp]
  have hb := slice_bound_first_order
    ((slice_contDiff hd q (circleRep t)).sub (slice_contDiff hd p (circleRep t))) hA hB
    (fun y => h0 _ hσ y)
    (fun y => by rw [fderiv_fun_sub (dq y) (dp y)]; exact h1 _ hσ y)
    (gradPart ((u : TimeCircle → XBar) t))
  refine (norm_solField_le hb.1 (mul_nonneg hK (norm_nonneg _)) hb.2).trans (le_of_eq ?_)
  ring

theorem joint_continuous {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d) :
    Continuous (fun z : (Fin k → ℝ) × (ℝ × Space) =>
      (d.profile z.1 z.2.1 z.2.2, fderiv ℝ (d.profile z.1 z.2.1) z.2.2)) := by
  refine hd.profile_smooth.continuous.prodMk ?_
  have hf : ContDiff ℝ 1 (Function.uncurry
      (fun (z : (Fin k → ℝ) × (ℝ × Space)) (y : Space) => d.profile z.1 z.2.1 y)) :=
    hd.profile_smooth.comp (by fun_prop : ContDiff ℝ 1
      (fun w : ((Fin k → ℝ) × (ℝ × Space)) × Space => (w.1.1, (w.1.2.1, w.2))))
  exact (hf.fderiv (contDiff_snd.comp contDiff_snd) (by norm_num) :
    ContDiff ℝ 0 _).continuous

theorem eventually_close {k : ℕ} {d : ExtendedCertificateData k} (hd : IsExtendedCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.params) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q in 𝓝 p, q ∈ d.params → ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖d.profile q σ y - d.profile p σ y‖ ≤ η ∧
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ η * tailWeight y := by
  have hD := decay_nonneg hd hp
  set R := (2 * d.decay / η) ^ 2 + 2 * d.decay / η with hR
  have hR0 : 0 ≤ R := by positivity
  set c := η * (1 + R) ^ (-(3 / 2 : ℝ)) with hc
  have hc0 : 0 < c := mul_pos hη (Real.rpow_pos_of_pos (by linarith) _)
  have hcη : c ≤ η := by
    have : (1 + R) ^ (-(3 / 2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    calc c ≤ η * 1 := mul_le_mul_of_nonneg_left this hη.le
      _ = η := mul_one η
  set Φ := fun z : (Fin k → ℝ) × (ℝ × Space) =>
    (d.profile z.1 z.2.1 z.2.2, fderiv ℝ (d.profile z.1 z.2.1) z.2.2) with hΦ
  have hΦc : Continuous Φ := joint_continuous hd
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hev : ∀ᶠ q in 𝓝 p, ∀ z ∈ Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R,
      dist (Φ (q, z)) (Φ (p, z)) < c := by
    refine hK.eventually_forall_of_forall_eventually fun z _ => ?_
    have e1 : ∀ᶠ w in 𝓝 (p, z), Φ w ∈ Metric.ball (Φ (p, z)) (c / 2) :=
      (hΦc.tendsto (p, z)).eventually (Metric.ball_mem_nhds _ (by positivity))
    have t2 : Tendsto (fun w : (Fin k → ℝ) × (ℝ × Space) => Φ (p, w.2)) (𝓝 (p, z))
        (𝓝 (Φ (p, z))) :=
      (hΦc.comp (continuous_const.prodMk continuous_snd)).tendsto' _ _ rfl
    have e2 : ∀ᶠ w in 𝓝 (p, z), Φ (p, w.2) ∈ Metric.ball (Φ (p, z)) (c / 2) :=
      t2.eventually (Metric.ball_mem_nhds _ (by positivity))
    filter_upwards [e1, e2] with w h1 h2
    rw [Metric.mem_ball] at h1 h2
    calc dist (Φ (w.1, w.2)) (Φ (p, w.2)) ≤ dist (Φ w) (Φ (p, z)) + dist (Φ (p, w.2)) (Φ (p, z)) :=
          dist_triangle_right _ _ _
      _ < c / 2 + c / 2 := add_lt_add h1 h2
      _ = c := add_halves c
  filter_upwards [hev] with q hq hqb σ hσ y
  by_cases hy : ‖y‖ ≤ R
  · have hz : (σ, y) ∈ Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R :=
      ⟨⟨hσ.1, hσ.2.le⟩, mem_closedBall_zero_iff.2 hy⟩
    have hd' := hq (σ, y) hz
    rw [Prod.dist_eq] at hd'
    have d1 : dist (d.profile q σ y) (d.profile p σ y) < c := (le_max_left _ _).trans_lt hd'
    have d2 : dist (fderiv ℝ (d.profile q σ) y) (fderiv ℝ (d.profile p σ) y) < c :=
      (le_max_right _ _).trans_lt hd'
    rw [dist_eq_norm] at d1 d2
    refine ⟨d1.le.trans hcη, d2.le.trans ?_⟩
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by norm_num)
  · have htb := tail_bounds hD hη (norm_nonneg y) hR (lt_of_not_ge hy)
    constructor
    · calc ‖d.profile q σ y - d.profile p σ y‖ ≤ ‖d.profile q σ y‖ + ‖d.profile p σ y‖ :=
            norm_sub_le _ _
        _ ≤ d.decay / (1 + ‖y‖) + d.decay / (1 + ‖y‖) :=
            add_le_add (hd.profile_decay q hqb σ y).1 (hd.profile_decay p hp σ y).1
        _ = 2 * d.decay / (1 + ‖y‖) := by ring
        _ ≤ η := htb.1
    · calc ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖
          ≤ ‖fderiv ℝ (d.profile q σ) y‖ + ‖fderiv ℝ (d.profile p σ) y‖ := norm_sub_le _ _
        _ ≤ d.decay / (1 + ‖y‖) ^ 2 + d.decay / (1 + ‖y‖) ^ 2 :=
            add_le_add (hd.profile_decay q hqb σ y).2.1 (hd.profile_decay p hp σ y).2.1
        _ = 2 * d.decay / (1 + ‖y‖) ^ 2 := by ring
        _ ≤ η * tailWeight y := htb.2

theorem op_bound (h : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {p q : Fin k → ℝ} (hp : p ∈ d.params) (hq : q ∈ d.params)
    {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖d.profile q σ y - d.profile p σ y‖ ≤ η ∧
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ η * tailWeight y) :
    ‖convection d.toCertificateData q - convection d.toCertificateData p‖ ≤
      η * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
        ‖(gradCLM : XX →L[ℝ] HH)‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hη constant_nonneg) fun u => ?_
  have hc : 0 ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) :=
    mul_nonneg (norm_nonneg _) (add_nonneg (mul_nonneg (by norm_num) hη)
      (mul_nonneg (mul_nonneg hη tailCube_nonneg) (norm_nonneg _)))
  calc ‖(convection d.toCertificateData q - convection d.toCertificateData p) u‖ =
        ‖convection d.toCertificateData q u - convection d.toCertificateData p u‖ :=
        congrArg norm (_root_.sub_apply _ _ _)
    _ ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖gradCLM u‖ :=
        norm_sub_apply_le h hd hp hq hη hη (fun σ hσ y => (hclose σ hσ y).1)
          (fun σ hσ y => (hclose σ hσ y).2) u
    _ ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * (‖gradCLM‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (gradCLM.le_opNorm u) hc
    _ = η * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
          ‖(gradCLM : XX →L[ℝ] HH)‖) * ‖u‖ := by ring

theorem convection_close (h : ExtendedConvectionHolds) {k : ℕ} {d : ExtendedCertificateData k}
    (hd : IsExtendedCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.params) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ d.params, dist q p < δ →
      ‖convection d.toCertificateData q - convection d.toCertificateData p‖ < ε :=
  (Metric.eventually_nhds_iff.1 (eventually_close hd hp
      (div_pos hε (mul_pos two_pos (by linarith [constant_nonneg])) :
        0 < ε / (2 * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
          ‖(gradCLM : XX →L[ℝ] HH)‖ + 1))))).imp fun _ hδ =>
    ⟨hδ.1, fun _ hq hqp => (op_bound h hd hp hq (div_pos hε (mul_pos two_pos
      (by linarith [constant_nonneg]))).le (hδ.2 hqp hq)).trans_lt
        (small_factor_lt constant_nonneg hε)⟩

end Internal.ExtendedConvectionContinuity

open Internal.ExtendedConvectionContinuity

theorem extendedConvectionContinuityHolds_of (h : ExtendedConvectionHolds) :
    ExtendedConvectionContinuityHolds :=
  fun _ hd => Internal.ConvectionContinuity.continuousOn_of_norm_sub fun _ hp _ hε =>
    convection_close h hd hp hε

end Breakdown.Cert

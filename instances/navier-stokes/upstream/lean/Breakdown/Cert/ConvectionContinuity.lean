import Breakdown.Cert.Nodes
import Breakdown.Cert.Convection

open scoped ContDiff ENNReal NNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ConvectionContinuity

open Internal.Convection

def tailWeight (y : Space) : ℝ := (1 + ‖y‖) ^ (-(3 / 2 : ℝ))

theorem tailWeight_pos (y : Space) : 0 < tailWeight y :=
  Real.rpow_pos_of_pos (by positivity) _

theorem tailWeight_memLp : MemLp tailWeight 3 volume := by
  have hm : AEStronglyMeasurable tailWeight volume :=
    Measurable.aestronglyMeasurable (by unfold tailWeight; fun_prop)
  refine (integrable_norm_rpow_iff hm (by norm_num) (by norm_num)).1 ?_
  have hi := integrable_one_add_norm (E := Space) (μ := volume) (r := 9 / 2) (by simp; norm_num)
  refine hi.congr (ae_of_all _ fun y => ?_)
  have hpos : 0 < 1 + ‖y‖ := by positivity
  simp only [tailWeight]
  rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hpos _), ← Real.rpow_mul hpos.le]
  norm_num

def tailCube : ℝ := (eLpNorm tailWeight 3 volume).toReal

theorem tailCube_nonneg : 0 ≤ tailCube := ENNReal.toReal_nonneg

theorem first_part {W : Space → Space} (hW : Continuous W) {A : ℝ} (hA : 0 ≤ A)
    (h0 : ∀ y, ‖W y‖ ≤ A) (h : X) (j : Fin 3) :
    MemLp (fun y => (W y) j • (partialX j h : Space → Space) y) 2 volume ∧
      eLpNorm (fun y => (W y) j • (partialX j h : Space → Space) y) 2 volume ≤
        ENNReal.ofReal (A * ‖h‖) := by
  have hm : AEStronglyMeasurable (fun y => (W y) j • (partialX j h : Space → Space) y) volume :=
    ((EuclideanSpace.proj j).continuous.comp hW).aestronglyMeasurable.smul
      (Lp.aestronglyMeasurable _)
  have hb : ∀ᵐ y ∂volume, ‖(W y) j • (partialX j h : Space → Space) y‖ ≤
      A * ‖(partialX j h : Space → Space) y‖ := by
    refine ae_of_all _ fun y => ?_
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le _ _).trans (h0 y)) (norm_nonneg _)
  refine ⟨(Lp.memLp _).of_le_mul hm hb, ?_⟩
  refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hb 2).trans ?_
  rw [← Lp.enorm_def, ← ofReal_norm, ← ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (norm_partialX_le j h) hA)

theorem second_part {W : Space → Space} (hW : ContDiff ℝ 2 W) {B : ℝ} (hB : 0 ≤ B)
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

theorem slice_bound_general {W : Space → Space} (hW : ContDiff ℝ 2 W) {A B : ℝ} (hA : 0 ≤ A)
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
  have h2 := second_part hW hB h1 h
  rw [heq]
  refine ⟨h1m.add h2.1, ?_⟩
  refine (eLpNorm_add_le h1m.1 h2.1.1 (by norm_num)).trans ?_
  refine (add_le_add h1b h2.2).trans ?_
  have hwc0 := tailCube_nonneg
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  ring

theorem sliceConvection_sub {f g : Space → Space} (hf : Differentiable ℝ f)
    (hg : Differentiable ℝ g) (h : X) :
    sliceConvection (fun y => f y - g y) h = sliceConvection f h - sliceConvection g h := by
  funext y
  simp only [sliceConvection, Pi.sub_apply, fderiv_fun_sub (hf y) (hg y),
    _root_.sub_apply, PiLp.sub_apply, sub_smul, Finset.sum_sub_distrib]
  abel

theorem solField_sub {F G : Space → Space} (hF : MemLp F 2 volume) (hG : MemLp G 2 volume) :
    solField F - solField G = solField (F - G) := by
  have e : toLpOrZero 2 (F - G) = toLpOrZero 2 F - toLpOrZero 2 G := by
    simp only [toLpOrZero, dif_pos hF, dif_pos hG, dif_pos (hF.sub hG)]
    exact MemLp.toLp_sub hF hG
  simp only [solField, e, map_sub]

theorem norm_solField_le {F : Space → Space} (hF : MemLp F 2 volume) {c : ℝ} (hc : 0 ≤ c)
    (hb : eLpNorm F 2 volume ≤ ENNReal.ofReal c) : ‖solField F‖ ≤ ‖solProj‖ * c := by
  calc ‖solField F‖ ≤ ‖solProj‖ * ‖toLpOrZero 2 F‖ := solProj.le_opNorm _
    _ = ‖solProj‖ * (eLpNorm F 2 volume).toReal := by
        rw [toLpOrZero, dif_pos hF, Lp.norm_toLp]
    _ ≤ ‖solProj‖ * c :=
        mul_le_mul_of_nonneg_left (ENNReal.toReal_le_of_le_ofReal hc hb) (norm_nonneg _)

theorem convection_spec (h : ConvectionHolds) {k : ℕ} {d : CertificateData k}
    (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box) :
    ConvectionSpec d p (convection d p) := by
  have hex := (h d hd p hp).1
  unfold convection
  rw [dif_pos hex]
  exact hex.choose_spec

theorem circleRep_mem (t : TimeCircle) : circleRep t ∈ Set.Ico (0 : ℝ) 1 := by
  have := (AddCircle.equivIco (1 : ℝ) 0 t).2
  simpa [circleRep] using this

set_option maxHeartbeats 400000 in
theorem norm_sub_apply_le (h : ConvectionHolds) {k : ℕ} {d : CertificateData k}
    (hd : IsCertificate d) {p q : Fin k → ℝ} (hp : p ∈ d.box) (hq : q ∈ d.box) {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (h0 : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y, ‖d.profile q σ y - d.profile p σ y‖ ≤ A)
    (h1 : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ B * tailWeight y)
    (u : XX) :
    ‖convection d q u - convection d p u‖ ≤
      ‖solProj‖ * (3 * A + B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖gradCLM u‖ := by
  have hWq := isCoefficient_profile hd hq
  have hWp := isCoefficient_profile hd hp
  have hK : 0 ≤ 3 * A + B * tailCube * ‖(velocity : X →L[ℝ] L6R)‖ := by
    have := tailCube_nonneg
    positivity
  have hgr : ((gradCLM u : HH) : TimeCircle → HBar) =ᵐ[volume]
      fun t => gradPart ((u : TimeCircle → XBar) t) :=
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) gradPart u
  have hsub : ((convection d q u - convection d p u : HH) : TimeCircle → HBar) =ᵐ[volume]
      ((convection d q u : HH) : TimeCircle → HBar) - ((convection d p u : HH) : TimeCircle → HBar) :=
    Lp.coeFn_sub _ _
  refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
  filter_upwards [hsub, convection_spec h hd hq u, convection_spec h hd hp u, hgr]
    with t hs hcq hcp hg
  simp only [hs, Pi.sub_apply, hcq, hcp, hg]
  have hσ := circleRep_mem t
  have dq : Differentiable ℝ (d.profile q (circleRep t)) :=
    (slice_contDiff hWq (circleRep t)).differentiable (by norm_num)
  have dp : Differentiable ℝ (d.profile p (circleRep t)) :=
    (slice_contDiff hWp (circleRep t)).differentiable (by norm_num)
  simp only [solField_sub (slice_bound hWq _ _).1 (slice_bound hWp _ _).1, ← sliceConvection_sub dq dp]
  have hb := slice_bound_general
    ((slice_contDiff hWq (circleRep t)).sub (slice_contDiff hWp (circleRep t))) hA hB
    (fun y => h0 _ hσ y)
    (fun y => by rw [fderiv_fun_sub (dq y) (dp y)]; exact h1 _ hσ y)
    (gradPart ((u : TimeCircle → XBar) t))
  refine (norm_solField_le hb.1 (mul_nonneg hK (norm_nonneg _)) hb.2).trans (le_of_eq ?_)
  ring


theorem tail_bounds {D η t R : ℝ} (hD : 0 ≤ D) (hη : 0 < η) (ht : 0 ≤ t)
    (hR : R = (2 * D / η) ^ 2 + 2 * D / η) (htR : R < t) :
    2 * D / (1 + t) ≤ η ∧ 2 * D / (1 + t) ^ 2 ≤ η * (1 + t) ^ (-(3 / 2 : ℝ)) := by
  set a := 2 * D / η with ha
  have ha0 : 0 ≤ a := by positivity
  have hea : η * a = 2 * D := by rw [ha]; field_simp
  have hpos : 0 < 1 + t := by linarith
  constructor
  · rw [div_le_iff₀ hpos, ← hea]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    nlinarith
  · have hs : a ≤ Real.sqrt (1 + t) := (Real.le_sqrt ha0 hpos.le).2 (by nlinarith)
    have hw : (1 + t) ^ (-(3 / 2 : ℝ)) * (1 + t) ^ 2 = Real.sqrt (1 + t) := by
      rw [← Real.rpow_two, ← Real.rpow_add hpos, Real.sqrt_eq_rpow]
      norm_num
    rw [div_le_iff₀ (by positivity), mul_assoc, hw, ← hea]
    exact mul_le_mul_of_nonneg_left hs hη.le

theorem joint_continuous {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) :
    Continuous (fun z : (Fin k → ℝ) × (ℝ × Space) =>
      (d.profile z.1 z.2.1 z.2.2, fderiv ℝ (d.profile z.1 z.2.1) z.2.2)) := by
  refine hd.profile_smooth.continuous.prodMk ?_
  have hf : ContDiff ℝ 2 (Function.uncurry
      (fun (z : (Fin k → ℝ) × (ℝ × Space)) (y : Space) => d.profile z.1 z.2.1 y)) :=
    hd.profile_smooth.comp (by fun_prop : ContDiff ℝ 2
      (fun w : ((Fin k → ℝ) × (ℝ × Space)) × Space => (w.1.1, (w.1.2.1, w.2))))
  exact (hf.fderiv (contDiff_snd.comp contDiff_snd) (by norm_num) :
    ContDiff ℝ 1 _).continuous

theorem eventually_close {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p : Fin k → ℝ} (hp : p ∈ d.box) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ q in 𝓝 p, q ∈ d.box → ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖d.profile q σ y - d.profile p σ y‖ ≤ η ∧
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ η * tailWeight y := by
  have hWp := isCoefficient_profile hd hp
  have hD := coefficient_nonneg hWp
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
  have hWq := isCoefficient_profile hd hqb
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
    have hpos : 0 < 1 + ‖y‖ := by positivity
    constructor
    · calc ‖d.profile q σ y - d.profile p σ y‖ ≤ ‖d.profile q σ y‖ + ‖d.profile p σ y‖ :=
            norm_sub_le _ _
        _ ≤ d.decay / (1 + ‖y‖) + d.decay / (1 + ‖y‖) :=
            add_le_add (hWq.bound_zero σ y) (hWp.bound_zero σ y)
        _ = 2 * d.decay / (1 + ‖y‖) := by ring
        _ ≤ η := htb.1
    · calc ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖
          ≤ ‖fderiv ℝ (d.profile q σ) y‖ + ‖fderiv ℝ (d.profile p σ) y‖ := norm_sub_le _ _
        _ ≤ d.decay / (1 + ‖y‖) ^ 2 + d.decay / (1 + ‖y‖) ^ 2 :=
            add_le_add (hWq.bound_one σ y) (hWp.bound_one σ y)
        _ = 2 * d.decay / (1 + ‖y‖) ^ 2 := by ring
        _ ≤ η * tailWeight y := htb.2

theorem continuousOn_of_norm_sub {k : ℕ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : Set (Fin k → ℝ)} {T : (Fin k → ℝ) → E →L[ℝ] F}
    (hT : ∀ p ∈ S, ∀ ε > 0, ∃ δ > 0, ∀ q ∈ S, dist q p < δ → ‖T q - T p‖ < ε) :
    ContinuousOn T S := by
  intro p hp
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := hT p hp ε hε
  exact ⟨δ, hδ, fun {q} hq hqp => by rw [dist_eq_norm]; exact h q hq hqp⟩

theorem small_factor_lt {M ε : ℝ} (hM : 0 ≤ M) (hε : 0 < ε) : ε / (2 * (M + 1)) * M < ε := by
  have hM1 : (0 : ℝ) < M + 1 := by linarith
  have e : ε / (2 * (M + 1)) * (M + 1) = ε / 2 := by
    rw [div_mul_eq_mul_div, mul_div_mul_right ε 2 hM1.ne']
  have hη : 0 < ε / (2 * (M + 1)) := div_pos hε (mul_pos two_pos hM1)
  have e2 : ε / (2 * (M + 1)) * M = ε / 2 - ε / (2 * (M + 1)) := by
    rw [← e]
    ring
  rw [e2]
  linarith

theorem constant_nonneg :
    0 ≤ ‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖(gradCLM : XX →L[ℝ] HH)‖ :=
  mul_nonneg (mul_nonneg (norm_nonneg _)
    (add_nonneg (by norm_num) (mul_nonneg tailCube_nonneg (norm_nonneg _)))) (ContinuousLinearMap.opNorm_nonneg _)

theorem op_bound (h : ConvectionHolds) {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {p q : Fin k → ℝ} (hp : p ∈ d.box) (hq : q ∈ d.box) {η : ℝ} (hη : 0 ≤ η)
    (hclose : ∀ σ ∈ Set.Ico (0 : ℝ) 1, ∀ y,
      ‖d.profile q σ y - d.profile p σ y‖ ≤ η ∧
      ‖fderiv ℝ (d.profile q σ) y - fderiv ℝ (d.profile p σ) y‖ ≤ η * tailWeight y) :
    ‖convection d q - convection d p‖ ≤
      η * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
        ‖(gradCLM : XX →L[ℝ] HH)‖) := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hη constant_nonneg) fun u => ?_
  have hc : 0 ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) :=
    mul_nonneg (norm_nonneg _) (add_nonneg (mul_nonneg (by norm_num) hη)
      (mul_nonneg (mul_nonneg hη tailCube_nonneg) (norm_nonneg _)))
  calc ‖(convection d q - convection d p) u‖ = ‖convection d q u - convection d p u‖ :=
        congrArg norm (_root_.sub_apply _ _ _)
    _ ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * ‖gradCLM u‖ :=
        norm_sub_apply_le h hd hp hq hη hη (fun σ hσ y => (hclose σ hσ y).1)
          (fun σ hσ y => (hclose σ hσ y).2) u
    _ ≤ ‖solProj‖ * (3 * η + η * tailCube * ‖(velocity : X →L[ℝ] L6R)‖) * (‖gradCLM‖ * ‖u‖) :=
        mul_le_mul_of_nonneg_left (gradCLM.le_opNorm u) hc
    _ = η * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
          ‖(gradCLM : XX →L[ℝ] HH)‖) * ‖u‖ := by ring

theorem convection_close (h : ConvectionHolds) {k : ℕ} {d : CertificateData k}
    (hd : IsCertificate d) {p : Fin k → ℝ} (hp : p ∈ d.box) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ d.box, dist q p < δ → ‖convection d q - convection d p‖ < ε :=
  (Metric.eventually_nhds_iff.1 (eventually_close hd hp
      (div_pos hε (mul_pos two_pos (by linarith [constant_nonneg])) :
        0 < ε / (2 * (‖solProj‖ * (3 + tailCube * ‖(velocity : X →L[ℝ] L6R)‖) *
          ‖(gradCLM : XX →L[ℝ] HH)‖ + 1))))).imp fun _ hδ =>
    ⟨hδ.1, fun _ hq hqp => (op_bound h hd hp hq (div_pos hε (mul_pos two_pos
      (by linarith [constant_nonneg]))).le (hδ.2 hqp hq)).trans_lt
        (small_factor_lt constant_nonneg hε)⟩

end Internal.ConvectionContinuity

open Internal.ConvectionContinuity

theorem convectionContinuityHolds_of (h : ConvectionHolds) : ConvectionContinuityHolds :=
  fun _ hd => continuousOn_of_norm_sub fun _ hp _ hε => convection_close h hd hp hε

end Breakdown.Cert

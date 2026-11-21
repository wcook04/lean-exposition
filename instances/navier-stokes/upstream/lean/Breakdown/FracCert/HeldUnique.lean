import Breakdown.FracCert.HeldUniqueParts
import Breakdown.Frac.SpaceDecay
import Breakdown.FracCert.InverseSquare

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldUniqueInternal

theorem axialTurn_sub (a b : Space) : axialTurn (a - b) = axialTurn a - axialTurn b := by
  ext i
  fin_cases i <;> simp [axialTurn] <;> ring

theorem drift_sub (α a : ℝ) (u u' : Space → Space) (G G' : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun z => u z - u' z) (fun z => G z - G' z) y =
      driftField α a u G y - driftField α a u' G' y := by
  simp only [driftField, ContinuousLinearMap.sub_apply, axialTurn_sub]
  module

theorem secondTrace_sub (A B : Space →L[ℝ] Space →L[ℝ] Space) :
    secondTrace (A - B) = secondTrace A - secondTrace B := by
  simp [secondTrace, ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]

theorem full_sub {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (u u' : Space → Space)
    (G G' : Space → (Space →L[ℝ] Space)) (H H' : Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (P P' : Space → Space) (κ κ' : Fin k → ℝ) (y : Space) :
    d.fullField α p (fun z => u z - u' z) (fun z => G z - G' z) (fun z => H z - H' z) (fun z => P z - P' z)
      (fun i => κ i - κ' i) y = d.fullField α p u G H P κ y - d.fullField α p u' G' H' P' κ' y := by
  simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField, drift_sub,
    secondTrace_sub, symProduct, ContinuousLinearMap.sub_apply, map_sub, sub_smul, Finset.sum_sub_distrib]
  module

theorem quad_split (u u' : Space → Space) (G G' : Space → (Space →L[ℝ] Space)) (y : Space) :
    G y (u y) - G' y (u' y) = symProduct u G (fun z => u z - u' z) (fun z => G z - G' z) y +
      symProduct u' G' (fun z => u z - u' z) (fun z => G z - G' z) y := by
  simp only [symProduct, ContinuousLinearMap.sub_apply, map_sub]
  module

theorem entryInner_sub (A B C : Space →L[ℝ] Space) : entryInner (A - B) C = entryInner A C - entryInner B C := by
  simp [entryInner, ContinuousLinearMap.sub_apply, inner_sub_left, Finset.sum_sub_distrib]

theorem entryInner_int {G χ : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hχ : AEStronglyMeasurable χ volume) (hG2 : Integrable fun y => entrySq (G y))
    (hχ2 : Integrable fun y => entrySq (χ y)) : Integrable fun y => entryInner (G y) (χ y) := by
  unfold entryInner
  refine integrable_finsetSum _ fun i _ => ?_
  refine Integrable.mono' (hG2.add hχ2) ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG).inner
      ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hχ)
  · have a1 : ‖G y (unitVector i)‖ ^ 2 ≤ entrySq (G y) :=
      Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have a2 : ‖χ y (unitVector i)‖ ^ 2 ≤ entrySq (χ y) :=
      Finset.single_le_sum (f := fun j => ‖χ y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have a3 := norm_inner_le_norm (𝕜 := ℝ) (G y (unitVector i)) (χ y (unitVector i))
    have a4 := two_mul_le_add_sq ‖G y (unitVector i)‖ ‖χ y (unitVector i)‖
    simp only [Pi.add_apply]
    nlinarith [norm_nonneg (G y (unitVector i)), norm_nonneg (χ y (unitVector i))]

theorem l2Norm_eq {F : Space → Space} (hF : MemLp F 2 volume) : l2Norm F = ‖hF.toLp F‖ := by
  rw [norm_eq_sqrt_real_inner, MeasureTheory.L2.inner_def, l2Norm]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

theorem l2Pair_eq {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    l2Pair F E = inner ℝ (hF.toLp F) (hE.toLp E) := by
  rw [MeasureTheory.L2.inner_def, l2Pair]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp, hE.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem l2Norm_nonneg (F : Space → Space) : 0 ≤ l2Norm F := Real.sqrt_nonneg _

theorem rows_bound {k N : ℕ} (d : FracCertData k N) (α : ℝ) (hd : IsFracCert α d) {f : Space → Space}
    (hf : MemLp f 2 volume) : d.rows f ≤ Real.sqrt d.rowMax * l2Norm f := by
  have hE : ∀ a, MemLp (d.row a) 2 volume := hd.row_two
  have he : Orthonormal ℝ (fun a => (hE a).toLp (d.row a)) := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [← l2Pair_eq (hE a) (hE b)]
    exact hd.row_orthonormal a b
  have hb := Orthonormal.sum_inner_products_le (x := hf.toLp f) (s := Finset.univ) he
  have hsum : ∑ a, d.rowWeight a * l2Pair f (d.row a) ^ 2 ≤ d.rowMax * l2Norm f ^ 2 := by
    calc ∑ a, d.rowWeight a * l2Pair f (d.row a) ^ 2 ≤ ∑ a, d.rowMax * l2Pair f (d.row a) ^ 2 :=
          Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hd.rowWeight_le a) (sq_nonneg _)
      _ = d.rowMax * ∑ a, ‖inner ℝ ((hE a).toLp (d.row a)) (hf.toLp f)‖ ^ 2 := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [l2Pair_eq hf (hE a), Real.norm_eq_abs, sq_abs, real_inner_comm]
      _ ≤ d.rowMax * ‖hf.toLp f‖ ^ 2 := mul_le_mul_of_nonneg_left hb hd.rowMax_pos.le
      _ = d.rowMax * l2Norm f ^ 2 := by rw [l2Norm_eq hf]
  unfold FracCertData.rows rowSize
  calc Real.sqrt _ ≤ Real.sqrt (d.rowMax * l2Norm f ^ 2) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt d.rowMax * l2Norm f := by
        rw [Real.sqrt_mul hd.rowMax_pos.le, Real.sqrt_sq (l2Norm_nonneg f)]

theorem bound_nonneg (sc th cp t x y : ℝ) (hsc : 0 ≤ sc) (hth0 : 0 ≤ th) (hth1 : th < 1) (hcp : 0 ≤ cp)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) : 0 ≤ boundConst sc th cp t x y 0 := by
  have hD : 0 < 1 - th ^ 2 := by nlinarith
  unfold boundConst
  exact mul_nonneg (Real.rpow_nonneg hcp _)
    (add_nonneg (mul_nonneg (by norm_num) (div_nonneg (by positivity) hD.le)) (Real.sqrt_nonneg _))

theorem bound_scale (sc th cp t x y N s : ℝ) (hsc : 0 ≤ sc) (hth0 : 0 ≤ th) (hth1 : th < 1) (hcp : 0 ≤ cp)
    (hx0 : 0 ≤ x) (hy0 : 0 ≤ y) (hxN : x ≤ N) (hyN : y ≤ N * s) :
    boundConst sc th cp t x y 0 ≤ N * boundConst sc th cp t 1 s 0 := by
  have hN : 0 ≤ N := hx0.trans hxN
  have hD : 0 < 1 - th ^ 2 := by nlinarith
  have hc : 0 ≤ cp ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hcp _
  unfold boundConst
  have hz : t * (0 : ℝ) ^ 2 = 0 := by ring
  simp only [hz, add_zero, mul_one]
  set D := 1 - th ^ 2 with hDdef
  set A := (sc * x + 2 * th * y) / D with hAdef
  set A₁ := (sc + 2 * th * s) / D with hA₁def
  have hA0 : 0 ≤ A := div_nonneg (by positivity) hD.le
  have hA : A ≤ N * A₁ := by
    rw [hAdef, hA₁def, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hD.le
    nlinarith
  have hsq : Real.sqrt (1 / 4 * A ^ 2 + y ^ 2 / D) ≤ N * Real.sqrt (1 / 4 * A₁ ^ 2 + s ^ 2 / D) := by
    rw [← Real.sqrt_sq hN, ← Real.sqrt_mul (sq_nonneg N)]
    apply Real.sqrt_le_sqrt
    have h1 : A ^ 2 ≤ (N * A₁) ^ 2 := pow_le_pow_left₀ hA0 hA 2
    have h2 : y ^ 2 ≤ (N * s) ^ 2 := pow_le_pow_left₀ hy0 hyN 2
    have h3 : y ^ 2 / D ≤ (N * s) ^ 2 / D := div_le_div_of_nonneg_right h2 hD.le
    have h4 : N ^ 2 * (1 / 4 * A₁ ^ 2 + s ^ 2 / D) = 1 / 4 * (N * A₁) ^ 2 + (N * s) ^ 2 / D := by
      field_simp
    rw [h4]
    linarith
  calc cp ^ (-(1 / 2 : ℝ)) * (1 / 2 * A + Real.sqrt (1 / 4 * A ^ 2 + y ^ 2 / D))
      ≤ cp ^ (-(1 / 2 : ℝ)) * (1 / 2 * (N * A₁) + N * Real.sqrt (1 / 4 * A₁ ^ 2 + s ^ 2 / D)) :=
        mul_le_mul_of_nonneg_left (by linarith) hc
    _ = N * (cp ^ (-(1 / 2 : ℝ)) * (1 / 2 * A₁ + Real.sqrt (1 / 4 * A₁ ^ 2 + s ^ 2 / D))) := by ring

theorem test_sq_int {φ : Space → Space} (hφ : IsTestVectorField φ) : Integrable fun y => ‖φ y‖ ^ 2 := by
  have hc0 : Continuous φ := hφ.1.continuous
  have hc : Continuous fun y => ‖φ y‖ ^ 2 := hc0.norm.pow 2
  have hs : HasCompactSupport fun y => ‖φ y‖ ^ 2 := by
    have h := hφ.2.norm
    exact h.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  exact hc.integrable_of_hasCompactSupport hs

theorem l2_test_int {P φ : Space → Space} (hP : MemLp P 2 volume) (hφ : IsTestVectorField φ) :
    Integrable fun y => inner ℝ (P y) (φ y) := by
  have hP2 : Integrable fun y => ‖P y‖ ^ 2 := (memLp_two_iff_integrable_sq_norm hP.1).mp hP
  refine Integrable.mono' (hP2.add (test_sq_int hφ)) (hP.1.inner hφ.1.continuous.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  have a3 := norm_inner_le_norm (𝕜 := ℝ) (P y) (φ y)
  have a4 := two_mul_le_add_sq ‖P y‖ ‖φ y‖
  simp only [Pi.add_apply]
  nlinarith [norm_nonneg (P y), norm_nonneg (φ y)]

theorem six_power_int {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {v : Space → Space} (hv : MemLp v 6 volume)
    {φ : Space → Space} (hφ : IsTestVectorField φ) :
    Integrable fun y => inner ℝ (v y) (fractionalPowerAt α φ y) := by
  obtain ⟨hc, C, hC⟩ := fracCompactDecay α h1 h2 φ hφ.1 hφ.2
  have hv6 : Integrable fun y => ‖v y‖ ^ (6 : ℝ) := by
    have h := (integrable_norm_rpow_iff hv.1 (by norm_num) (by norm_num)).mpr hv
    have e : ((6 : ℝ≥0∞)).toReal = 6 := by norm_num
    rw [e] at h
    exact h
  have hg : Integrable fun y : Space => (1 + ‖y‖) ^ (-((3 + 2 * α) * (6 / 5))) := by
    apply integrable_one_add_norm
    rw [finrank_euclideanSpace, Fintype.card_fin]
    push_cast
    linarith
  have hpq : (6 : ℝ).HolderConjugate (6 / 5) := (Real.holderConjugate_iff_eq_conjExponent (by norm_num)).mpr (by norm_num)
  refine Integrable.mono' ((hv6.div_const 6).add ((hg.const_mul (|C| ^ (6 / 5 : ℝ))).div_const (6 / 5)))
    (hv.1.inner hc.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  have hb0 : 0 ≤ |C| * (1 + ‖y‖) ^ (-(3 + 2 * α)) :=
    mul_nonneg (abs_nonneg C) (Real.rpow_nonneg (by positivity) _)
  have hAb : ‖fractionalPowerAt α φ y‖ ≤ |C| * (1 + ‖y‖) ^ (-(3 + 2 * α)) :=
    (hC y).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_nonneg (by positivity) _))
  have hin := norm_inner_le_norm (𝕜 := ℝ) (v y) (fractionalPowerAt α φ y)
  have hy := Real.young_inequality_of_nonneg (norm_nonneg (v y)) hb0 hpq
  have hpow : (|C| * (1 + ‖y‖) ^ (-(3 + 2 * α))) ^ (6 / 5 : ℝ) =
      |C| ^ (6 / 5 : ℝ) * (1 + ‖y‖) ^ (-((3 + 2 * α) * (6 / 5))) := by
    rw [Real.mul_rpow (abs_nonneg C) (Real.rpow_nonneg (by positivity) _), ← Real.rpow_mul (by positivity), neg_mul]
  rw [hpow] at hy
  have hm : ‖v y‖ * ‖fractionalPowerAt α φ y‖ ≤ ‖v y‖ * (|C| * (1 + ‖y‖) ^ (-(3 + 2 * α))) :=
    mul_le_mul_of_nonneg_left hAb (norm_nonneg _)
  simp only [Pi.add_apply]
  linarith


end HeldUniqueInternal

open HeldUniqueInternal in
theorem weakPowerDifference : WeakPowerDifferenceStatement := by
  intro α h1 h2 m v G H P u K L R hv hu hP hR
  refine ⟨hP.1.sub hR.1, fun φ hφ => ?_⟩
  have e1 := hP.2 φ hφ
  have e2 := hR.2 φ hφ
  simp only [inner_sub_left]
  rw [integral_sub (l2_test_int hP.1 hφ) (l2_test_int hR.1 hφ),
    integral_sub (six_power_int h1 (by linarith) hv.velocity_six hφ) (six_power_int h1 (by linarith) hu.velocity_six hφ),
    e1, e2]

namespace GradientDifferenceInternal

theorem cut_int {c f : Space → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c)
    (hf : AEStronglyMeasurable f volume)
    (hf2 : ∀ K : Set Space, IsCompact K → IntegrableOn (fun y => f y ^ 2) K) :
    Integrable fun y => c y * f y := by
  obtain ⟨M, hM⟩ := hc.bounded_above_of_compact_support hcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hK := hcs.isCompact
  have hfin : volume (tsupport c) ≠ ⊤ := hK.measure_lt_top.ne
  have hon : IntegrableOn (fun y => c y * f y) (tsupport c) := by
    refine Integrable.mono' (((integrableOn_const (C := (1 : ℝ)) hfin).add (hf2 _ hK)).const_mul M)
      (hc.aestronglyMeasurable.mul hf).restrict (Filter.Eventually.of_forall fun y => ?_)
    have h1 : ‖c y‖ ≤ M := hM y
    have h2 : |f y| ≤ 1 + f y ^ 2 := by
      rcases le_total 0 (f y) with h | h
      · rw [abs_of_nonneg h]; nlinarith
      · rw [abs_of_nonpos h]; nlinarith
    rw [norm_mul, Real.norm_eq_abs (f y)]
    simp only [Pi.add_apply]
    calc ‖c y‖ * |f y| ≤ M * |f y| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      _ ≤ M * (1 + f y ^ 2) := mul_le_mul_of_nonneg_left h2 hM0
  exact hon.integrable_of_forall_notMem_eq_zero fun y hy => by
    simp [image_eq_zero_of_notMem_tsupport hy]

theorem unit_norm (j : Fin 3) : ‖unitVector j‖ = 1 := by
  simp [unitVector]

theorem comp_sq_int {Q : Space → Space} (hQ : IsLocalSquareIntegrable (fun y => ‖Q y‖ ^ 2))
    (hQm : AEStronglyMeasurable Q volume) (j : Fin 3) :
    ∀ K : Set Space, IsCompact K → IntegrableOn (fun y => inner ℝ (Q y) (unitVector j) ^ 2) K := by
  intro K hK
  refine Integrable.mono' (hQ K hK) ((hQm.inner aestronglyMeasurable_const).pow 2).restrict
    (Filter.Eventually.of_forall fun y => ?_)
  have h := norm_inner_le_norm (𝕜 := ℝ) (Q y) (unitVector j)
  rw [unit_norm, mul_one, Real.norm_eq_abs] at h
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 : 0 ≤ |inner ℝ (Q y) (unitVector j)| := abs_nonneg _
  calc inner ℝ (Q y) (unitVector j) ^ 2 = |inner ℝ (Q y) (unitVector j)| ^ 2 := (sq_abs _).symm
    _ ≤ ‖Q y‖ ^ 2 := pow_le_pow_left₀ h0 h 2

theorem test_deriv_cont {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous fun y => fderiv ℝ φ y (unitVector j) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem test_deriv_supp {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    HasCompactSupport fun y => fderiv ℝ φ y (unitVector j) :=
  hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)

theorem potential_regular (Q : Space → Space) (hQ : IsGradientField Q) :
    ∃ q : Space → ℝ, AEStronglyMeasurable q volume ∧ IsLocalSquareIntegrable (fun y => q y ^ 2) ∧
      ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
        ∫ y, fderiv ℝ φ y (unitVector j) * q y = -∫ y, φ y * inner ℝ (Q y) (unitVector j) := by
  obtain ⟨q, hq2, hQ2, hQm, hid⟩ := hQ
  by_cases hqm : AEStronglyMeasurable q volume
  · exact ⟨q, hqm, hq2, hid⟩
  refine ⟨fun _ => 0, aestronglyMeasurable_const, fun K _ => by simp, fun ψ hψ j => ?_⟩
  simp only [mul_zero, integral_zero]
  have hbad : ∃ n : ℕ, ¬ AEStronglyMeasurable q (volume.restrict (Metric.ball (0 : Space) n)) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    apply hqm
    have h := (aestronglyMeasurable_iUnion_iff (μ := (volume : Measure Space))
      (s := fun n : ℕ => Metric.ball (0 : Space) n) (f := q)).mpr hall
    rwa [Metric.iUnion_ball_nat, Measure.restrict_univ] at h
  obtain ⟨n, hn⟩ := hbad
  let b : ContDiffBump (0 : Space) := ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩
  let φ : Space → ℝ := fun y => innerSL ℝ (unitVector j) y * b y
  have hφ : IsTestScalar φ :=
    ⟨(innerSL ℝ (unitVector j)).contDiff.mul b.contDiff, b.hasCompactSupport.mul_left⟩
  have hφd : ∀ y ∈ Metric.ball (0 : Space) ((n : ℝ) + 1), fderiv ℝ φ y (unitVector j) = 1 := by
    intro y hy
    have hev : φ =ᶠ[nhds y] fun z => innerSL ℝ (unitVector j) z := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hy] with z hz
      simp only [φ]
      rw [b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz), mul_one]
    rw [hev.fderiv_eq, ContinuousLinearMap.fderiv, innerSL_apply_apply, real_inner_self_eq_norm_sq, unit_norm]
    norm_num
  have hφbad : ¬ Integrable fun y => fderiv ℝ φ y (unitVector j) * q y := by
    intro hI
    apply hn
    have hon : IntegrableOn q (Metric.ball (0 : Space) n) := by
      refine (hI.integrableOn (s := Metric.ball (0 : Space) n)).congr_fun (fun y hy => ?_) measurableSet_ball
      have hy' : y ∈ Metric.ball (0 : Space) ((n : ℝ) + 1) := Metric.ball_subset_ball (by linarith) hy
      simp only
      rw [hφd y hy', one_mul]
    exact hon.aestronglyMeasurable
  have hφ0 : ∫ y, φ y * inner ℝ (Q y) (unitVector j) = 0 := by
    have h := hid φ hφ j
    rw [integral_undef hφbad] at h
    linarith
  have hint : ∀ χ : Space → ℝ, IsTestScalar χ → Integrable fun y => χ y * inner ℝ (Q y) (unitVector j) :=
    fun χ hχ => cut_int hχ.1.continuous hχ.2 (hQm.inner aestronglyMeasurable_const) (comp_sq_int hQ2 hQm j)
  by_cases hψi : Integrable fun y => fderiv ℝ ψ y (unitVector j) * q y
  · have hsum : IsTestScalar (fun y => ψ y + φ y) := ⟨hψ.1.add hφ.1, hψ.2.add hφ.2⟩
    have hsbad : ¬ Integrable fun y => fderiv ℝ (fun y => ψ y + φ y) y (unitVector j) * q y := by
      intro hI
      apply hφbad
      have e : (fun y => fderiv ℝ φ y (unitVector j) * q y) = fun y =>
          fderiv ℝ (fun y => ψ y + φ y) y (unitVector j) * q y - fderiv ℝ ψ y (unitVector j) * q y := by
        funext y
        have hfun : (fun y => ψ y + φ y) = ψ + φ := rfl
        rw [hfun, fderiv_add ((hψ.1.differentiable (by simp)) y) ((hφ.1.differentiable (by simp)) y)]
        simp only [ContinuousLinearMap.add_apply]
        ring
      rw [e]
      exact hI.sub hψi
    have h := hid _ hsum j
    rw [integral_undef hsbad] at h
    have e2 : (fun y => (ψ y + φ y) * inner ℝ (Q y) (unitVector j)) = fun y =>
        ψ y * inner ℝ (Q y) (unitVector j) + φ y * inner ℝ (Q y) (unitVector j) := by
      funext y; ring
    rw [e2, integral_add (hint ψ hψ) (hint φ hφ), hφ0] at h
    linarith
  · have h := hid ψ hψ j
    rw [integral_undef hψi] at h
    linarith

end GradientDifferenceInternal

open GradientDifferenceInternal in
theorem gradientDifference : GradientDifferenceStatement := by
  intro Q Q' hQ hQ'
  obtain ⟨q, hqm, hq2, hid⟩ := potential_regular Q hQ
  obtain ⟨q', hqm', hq2', hid'⟩ := potential_regular Q' hQ'
  obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
  obtain ⟨_, _, hQ2', hQm', _⟩ := hQ'
  refine ⟨fun y => q y - q' y, fun K hK => ?_, fun K hK => ?_, hQm.sub hQm', fun φ hφ j => ?_⟩
  · refine Integrable.mono' (((hq2 K hK).add (hq2' K hK)).const_mul 2) ((hqm.sub hqm').pow 2).restrict
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (q y + q' y)]
  · refine Integrable.mono' (((hQ2 K hK).add (hQ2' K hK)).const_mul 2) ((hQm.sub hQm').norm.pow 2).restrict
      (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simp only [Pi.add_apply]
    have h := norm_sub_le (Q y) (Q' y)
    have h0 : 0 ≤ ‖Q y - Q' y‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖Q y‖ - ‖Q' y‖), norm_nonneg (Q y), norm_nonneg (Q' y)]
  · have i1 := cut_int (test_deriv_cont hφ j) (test_deriv_supp hφ j) hqm hq2
    have i2 := cut_int (test_deriv_cont hφ j) (test_deriv_supp hφ j) hqm' hq2'
    have i3 := cut_int hφ.1.continuous hφ.2 (hQm.inner aestronglyMeasurable_const) (comp_sq_int hQ2 hQm j)
    have i4 := cut_int hφ.1.continuous hφ.2 (hQm'.inner aestronglyMeasurable_const) (comp_sq_int hQ2' hQm' j)
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) * (q y - q' y)) = fun y =>
        fderiv ℝ φ y (unitVector j) * q y - fderiv ℝ φ y (unitVector j) * q' y := by
      funext y; ring
    have e2 : (fun y => φ y * inner ℝ (Q y - Q' y) (unitVector j)) = fun y =>
        φ y * inner ℝ (Q y) (unitVector j) - φ y * inner ℝ (Q' y) (unitVector j) := by
      funext y; rw [inner_sub_left]; ring
    simp only
    rw [e1, e2, integral_sub i1 i2, integral_sub i3 i4, hid φ hφ j, hid' φ hφ j]
    ring


open HeldUniqueInternal in
theorem heldUnique (h1 : AprioriBoundStatement) (h2 : SecondOrderLinearStatement)
    (h4 : ProductSquareStatement) : HeldUniqueStatement := by
  have h3 : InverseSquareBoundStatement := inverseSquareBound
  have h5 : GradientDifferenceStatement := gradientDifference
  have h6 : WeakPowerDifferenceStatement := weakPowerDifference
  intro α hα1 hα2 k N d hd p hp u G H P κ u' G' H' P' κ' hu hu' hsmall
  obtain ⟨⟨hs, hpow, hdr⟩, ⟨Q, hQ, hQe⟩, hpin⟩ := hu
  obtain ⟨⟨hs', hpow', hdr'⟩, ⟨Q', hQ', hQe'⟩, hpin'⟩ := hu'
  have hsw : IsSecondOrderField d.order (fun y => u y - u' y) (fun y => G y - G' y) (fun y => H y - H' y) := by
    simpa [sub_eq_add_neg] using h2 _ _ _ _ _ _ _ (-1) hs hs'
  have hlin : d.IsLinearState α p (fun y => u y - u' y) (fun y => G y - G' y) (fun y => H y - H' y)
      (fun y => P y - P' y) := by
    refine ⟨hsw, h6 α hα1 hα2 _ _ _ _ _ _ _ _ _ hs hs' hpow hpow', ?_⟩
    have e : driftField α (d.rotationRate p) (fun y => u y - u' y) (fun y => G y - G' y) =
        fun y => driftField α (d.rotationRate p) u G y - driftField α (d.rotationRate p) u' G' y :=
      funext (drift_sub α _ u u' G G')
    rw [e]
    exact hdr.sub hdr'
  have hpins : d.pins (fun y => G y - G' y) = 0 := by
    funext i
    have i1 := entryInner_int hs.measurable_gradient (hd.pin_measurable i).1 hs.gradient_two (hd.pin_two i).1
    have i2 := entryInner_int hs'.measurable_gradient (hd.pin_measurable i).1 hs'.gradient_two (hd.pin_two i).1
    have e1 := hpin i
    have e2 := hpin' i
    simp only [FracCertData.pins, pinValue, Pi.zero_apply] at e1 e2 ⊢
    rw [show (fun y => entryInner (G y - G' y) (d.pin i y)) =
        fun y => entryInner (G y) (d.pin i y) - entryInner (G' y) (d.pin i y) from
        funext fun y => entryInner_sub _ _ _, integral_sub i1 i2, e1, e2, sub_zero]
  obtain ⟨F, hFdef⟩ : ∃ F, F = d.fullField α p (fun y => u y - u' y) (fun y => G y - G' y)
      (fun y => H y - H' y) (fun y => P y - P' y) (fun i => κ i - κ' i) := ⟨_, rfl⟩
  have hS1 := h4 _ _ _ _ _ _ _ hs hsw
  have hS2 := h4 _ _ _ _ _ _ _ hs' hsw
  obtain ⟨B, hBdef⟩ : ∃ B : Space → Space, B = fun y => symProduct u G (fun z => u z - u' z) (fun z => G z - G' z) y +
      symProduct u' G' (fun z => u z - u' z) (fun z => G z - G' z) y := ⟨_, rfl⟩
  have hBm : MemLp B 2 volume := by rw [hBdef]; exact hS1.add hS2
  have hFe : ∀ᵐ y ∂volume, F y + (Q y - Q' y) = -B y := by
    filter_upwards [hQe, hQe'] with y e1 e2
    rw [hFdef, full_sub, hBdef]
    simp only
    rw [← quad_split]
    apply eq_neg_of_add_eq_zero_left
    have : d.fullField α p u G H P κ y - d.fullField α p u' G' H' P' κ' y + (Q y - Q' y) +
        (G y (u y) - G' y (u' y)) = (d.fullField α p u G H P κ y + G y (u y) + d.defect α p y + Q y) -
        (d.fullField α p u' G' H' P' κ' y + G' y (u' y) + d.defect α p y + Q' y) := by abel
    rw [this, e1, e2, sub_zero]
  have hFQm : MemLp (fun y => F y + (Q y - Q' y)) 2 volume :=
    hBm.neg.ae_eq (hFe.mono fun y hy => hy.symm)
  have hnorm : l2Norm (fun y => F y + (Q y - Q' y)) = l2Norm B := by
    unfold l2Norm
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hFe] with y hy
    rw [hy, norm_neg]
  have hQd := h5 Q Q' hQ hQ'
  have hX : projectedNorm F ≤ l2Norm B := by
    unfold projectedNorm
    refine csInf_le ⟨0, fun r hr => ?_⟩ ⟨fun y => Q y - Q' y, hQd, hFQm, hnorm.symm⟩
    obtain ⟨_, _, _, hr⟩ := hr
    rw [hr]
    exact l2Norm_nonneg _
  have hX0 : 0 ≤ projectedNorm F := by
    unfold projectedNorm
    refine Real.sInf_nonneg fun r hr => ?_
    obtain ⟨_, _, _, hr⟩ := hr
    rw [hr]
    exact l2Norm_nonneg _
  have hY : d.rowsModGrad F ≤ Real.sqrt d.rowMax * l2Norm B := by
    unfold FracCertData.rowsModGrad rowSeminorm
    have hmem : rowSize d.row d.rowWeight (fun y => F y + (Q y - Q' y)) ∈
        {r | ∃ Q, IsGradientField Q ∧ r = rowSize d.row d.rowWeight (fun y => F y + Q y)} := ⟨_, hQd, rfl⟩
    refine (csInf_le ⟨0, fun r hr => ?_⟩ hmem).trans ?_
    · obtain ⟨_, _, hr⟩ := hr
      rw [hr]
      exact Real.sqrt_nonneg _
    · have := rows_bound d α hd hFQm
      rw [hnorm] at this
      exact this
  have hY0 : 0 ≤ d.rowsModGrad F := by
    unfold FracCertData.rowsModGrad rowSeminorm
    refine Real.sInf_nonneg fun r hr => ?_
    obtain ⟨_, _, hr⟩ := hr
    rw [hr]
    exact Real.sqrt_nonneg _
  have hA := h1 α hα1 hα2 d hd p hp _ _ _ _ hlin (fun i => κ i - κ' i)
  rw [← hFdef, hpins] at hA
  have hv : vecNorm (0 : Fin k → ℝ) = 0 := by simp [vecNorm]
  have e0 : Real.sqrt (d.rowsModGrad F ^ 2 + d.pinWeight * vecNorm (0 : Fin k → ℝ) ^ 2) = d.rowsModGrad F := by
    rw [hv, show d.pinWeight * (0 : ℝ) ^ 2 = 0 by ring, add_zero, Real.sqrt_sq hY0]
  rw [e0] at hA
  have hth0 : 0 ≤ d.contraction := Real.sqrt_nonneg _
  have hrc : 0 ≤ d.rowConst :=
    bound_nonneg _ _ _ _ _ _ hd.formScale_nonneg hth0 hd.contraction_lt hd.reducedGap_pos.le
      zero_le_one (Real.sqrt_nonneg _)
  have hbd : d.boundFn (projectedNorm F) (d.rowsModGrad F) 0 ≤ l2Norm B * d.rowConst :=
    bound_scale _ _ _ _ _ _ _ _ hd.formScale_nonneg hth0 hd.contraction_lt hd.reducedGap_pos.le hX0 hY0 hX
      (by rw [mul_comm]; exact hY)
  set a := Real.sqrt (d.energy G H) with ha
  set a' := Real.sqrt (d.energy G' H') with ha'
  set ew := Real.sqrt (d.energy (fun y => G y - G' y) (fun y => H y - H' y)) with hew
  set sz := d.size (fun y => G y - G' y) (fun y => H y - H' y) (fun i => κ i - κ' i) with hsz
  have htri : l2Norm B ≤ l2Norm (symProduct u G (fun z => u z - u' z) (fun z => G z - G' z)) +
      l2Norm (symProduct u' G' (fun z => u z - u' z) (fun z => G z - G' z)) := by
    rw [l2Norm_eq hBm, l2Norm_eq hS1, l2Norm_eq hS2]
    have e : hBm.toLp B = hS1.toLp _ + hS2.toLp _ := by
      rw [← MemLp.toLp_add hS1 hS2]
      exact MemLp.toLp_congr _ _ (Filter.Eventually.of_forall fun y => by rw [hBdef]; rfl)
    rw [e]
    exact norm_add_le _ _
  have hP1 := hd.productConst_bound _ _ _ hs _ _ _ hsw
  have hP2 := hd.productConst_bound _ _ _ hs' _ _ _ hsw
  have hNq : l2Norm B ≤ d.productConst * (a + a') * ew := by
    have := add_le_add hP1 hP2
    nlinarith
  have hE0 : 0 ≤ d.energy (fun y => G y - G' y) (fun y => H y - H' y) := by
    unfold FracCertData.energy weightedEnergy
    refine add_nonneg (integral_nonneg fun y => sq_nonneg _) (integral_nonneg fun y => ?_)
    exact mul_nonneg (hd.weightMin_pos.le.trans (hd.weight_lower y))
      (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hK0 : 0 ≤ d.multiplierScale ^ 2 * ∑ i, (κ i - κ' i) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun j _ => sq_nonneg _)
  have hew_le : ew ≤ sz := by
    rw [hew, hsz]
    unfold FracCertData.size sizeNorm
    exact Real.sqrt_le_sqrt (by unfold FracCertData.energy at hE0 ⊢; linarith)
  have hsz0 : 0 ≤ sz := by rw [hsz]; exact Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have ha0' : 0 ≤ a' := Real.sqrt_nonneg _
  have hchain : sz ≤ (a + a') * (d.rowConst * d.productConst) * sz := by
    have s1 : sz ≤ l2Norm B * d.rowConst := hA.trans hbd
    have s2 : l2Norm B * d.rowConst ≤ (d.productConst * (a + a') * ew) * d.rowConst :=
      mul_le_mul_of_nonneg_right hNq hrc
    have s3 : (d.productConst * (a + a') * ew) * d.rowConst ≤ (d.productConst * (a + a') * sz) * d.rowConst :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hew_le
        (mul_nonneg hd.productConst_nonneg (add_nonneg ha0 ha0'))) hrc
    calc sz ≤ (d.productConst * (a + a') * sz) * d.rowConst := s1.trans (s2.trans s3)
      _ = (a + a') * (d.rowConst * d.productConst) * sz := by ring
  have hszz : sz = 0 := by nlinarith
  have hin : d.energy (fun y => G y - G' y) (fun y => H y - H' y) + d.multiplierScale ^ 2 * ∑ i, (κ i - κ' i) ^ 2 ≤ 0 := by
    have := hszz
    rw [hsz] at this
    unfold FracCertData.size sizeNorm at this
    rw [Real.sqrt_eq_zero'] at this
    exact this
  have hEw : d.energy (fun y => G y - G' y) (fun y => H y - H' y) = 0 := by linarith
  have hKw : d.multiplierScale ^ 2 * ∑ i, (κ i - κ' i) ^ 2 = 0 := by linarith
  constructor
  · have hent : ∫ y, entrySq (G y - G' y) ≤ 0 := by
      have hint : Integrable fun y => d.weight y * entrySq (G y - G' y) := by
        refine Integrable.mono' (hsw.gradient_two.const_mul d.weightMax) ?_ (Filter.Eventually.of_forall fun y => ?_)
        · exact hd.weight_measurable.aestronglyMeasurable.mul hsw.gradient_two.aestronglyMeasurable
        · have hw0 : 0 ≤ d.weight y := hd.weightMin_pos.le.trans (hd.weight_lower y)
          have he0 : 0 ≤ entrySq (G y - G' y) := Finset.sum_nonneg fun j _ => sq_nonneg _
          rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 he0)]
          exact mul_le_mul_of_nonneg_right (hd.weight_upper y) he0
      have hlow : d.weightMin * ∫ y, entrySq (G y - G' y) ≤ ∫ y, d.weight y * entrySq (G y - G' y) := by
        rw [← integral_const_mul]
        refine integral_mono (hsw.gradient_two.const_mul _) hint fun y => ?_
        exact mul_le_mul_of_nonneg_right (hd.weight_lower y) (Finset.sum_nonneg fun j _ => sq_nonneg _)
      have htr : 0 ≤ ∫ y, ‖secondTrace (H y - H' y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
      have : (∫ y, ‖secondTrace (H y - H' y)‖ ^ 2) + ∫ y, d.weight y * entrySq (G y - G' y) = 0 := by
        have h := hEw
        unfold FracCertData.energy weightedEnergy at h
        beta_reduce at h
        exact h
      have hm : d.weightMin * ∫ y, entrySq (G y - G' y) ≤ 0 := by linarith
      by_contra hc
      have hc' := lt_of_not_ge hc
      nlinarith [hd.weightMin_pos]
    obtain ⟨hI, hIb⟩ := h3 _ _ hsw.measurable_velocity hsw.velocity_six hsw.gradient_two hsw.weak_gradient
    have hI0 : ∫ y, ‖u y - u' y‖ ^ 2 / ‖y‖ ^ 2 = 0 :=
      le_antisymm (by linarith) (integral_nonneg fun y => div_nonneg (sq_nonneg _) (sq_nonneg _))
    rw [integral_eq_zero_iff_of_nonneg (fun y => div_nonneg (sq_nonneg _) (sq_nonneg _)) hI] at hI0
    have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [hI0, hne] with y hy hy0
    have hy' : ‖u y - u' y‖ ^ 2 / ‖y‖ ^ 2 = 0 := hy
    rw [div_eq_zero_iff] at hy'
    rcases hy' with h | h
    · exact sub_eq_zero.mp (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h))
    · exact absurd (norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h)) hy0
  · have hs0 : ∑ i, (κ i - κ' i) ^ 2 = 0 := by
      rcases mul_eq_zero.mp hKw with h | h
      · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h) hd.multiplierScale_pos.ne'
      · exact h
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (κ j - κ' j))).mp hs0 i (Finset.mem_univ i)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

end SteadyCert

end Breakdown

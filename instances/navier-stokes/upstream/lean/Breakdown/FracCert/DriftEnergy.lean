import Breakdown.FracCert.DriftEnergyLocal
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Real Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

private theorem norm_axialTurn_le (y : Space) : ‖axialTurn y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [axialTurn, Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

private theorem continuous_axialTurn : Continuous axialTurn := by
  have h : axialTurn = fun y => (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
    funext y
    ext j
    fin_cases j <;> simp [axialTurn, unitVector]
  rw [h]
  fun_prop

private theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem fderiv_cutoff_far {r : ℝ} (hr : 0 < r) {y : Space} (hy : 2 * r < ‖y‖) :
    fderiv ℝ (radialCutoff r) y = 0 := by
  have h : radialCutoff r =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact radialCutoff_eq_zero hr hz.le
  rw [h.fderiv_eq]
  simp

private theorem fderiv_cutoff_near {r : ℝ} (hr : 0 < r) {y : Space} (hy : ‖y‖ < r) :
    fderiv ℝ (radialCutoff r) y = 0 := by
  have h : radialCutoff r =ᶠ[𝓝 y] fun _ => (1 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hy] with z hz
    exact radialCutoff_eq_one hr hz.le
  rw [h.fderiv_eq]
  simp

private theorem cutoff_bounds : ∃ c : ℝ, 0 ≤ c ∧ ∀ r : ℝ, 1 ≤ r → ∀ y : Space,
    ‖fderiv ℝ (radialCutoff r) y‖ ≤ c ∧ ‖fderiv ℝ (radialCutoff r) y‖ * ‖y‖ ≤ 2 * c := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hc0 : 0 ≤ c := by
    have := hc 1 one_pos 0
    rw [div_one] at this
    exact (norm_nonneg _).trans this
  refine ⟨c, hc0, fun r hr y => ⟨?_, ?_⟩⟩
  · exact (hc r (by linarith) y).trans (div_le_self hc0 hr)
  · by_cases hy : 2 * r < ‖y‖
    · rw [fderiv_cutoff_far (by linarith) hy, norm_zero, zero_mul]
      linarith
    · push Not at hy
      have h1 := hc r (by linarith) y
      have hr0 : 0 < r := by linarith
      calc ‖fderiv ℝ (radialCutoff r) y‖ * ‖y‖ ≤ c / r * (2 * r) :=
            mul_le_mul h1 hy (norm_nonneg _) ((norm_nonneg _).trans h1)
        _ = 2 * c := by field_simp

private theorem aesm_apply_second {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable H volume) (i j : Fin 3) :
    AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
  ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
    (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous).comp_aestronglyMeasurable hH

private theorem aesm_apply_first {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) (i : Fin 3) :
    AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
  (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable hG

private theorem memLp_negSecondTrace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hterm : ∀ j : Fin 3, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume := by
    intro j
    have hm := aesm_apply_second hv.measurable_second j j
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine hv.second_two.mono' (hm.norm.pow 2) (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    calc ‖H y (unitVector j) (unitVector j)‖ ^ 2
        ≤ ∑ k : Fin 3, ‖H y (unitVector j) (unitVector k)‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖H y (unitVector j) (unitVector k)‖ ^ 2)
            (fun k _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i : Fin 3, ∑ k : Fin 3, ‖H y (unitVector i) (unitVector k)‖ ^ 2 :=
          Finset.single_le_sum (f := fun i => ∑ k : Fin 3, ‖H y (unitVector i) (unitVector k)‖ ^ 2)
            (fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ j)
  have hs : MemLp (fun y => ∑ j : Fin 3, H y (unitVector j) (unitVector j)) 2 volume :=
    memLp_finsetSum Finset.univ (fun j _ => hterm j)
  exact hs.neg

private theorem boundary_bound (α a c : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (χ : Space → ℝ) (y : Space) (hc1 : ‖fderiv ℝ χ y‖ ≤ c) (hc2 : ‖fderiv ℝ χ y‖ * ‖y‖ ≤ 2 * c) :
    |driftBoundary α a v G χ y| ≤ c * (3 / 2) * (‖driftField α a v G y‖ ^ 2 + entrySq (G y))
      + c * (|1 / (2 * α)| + |a|) * entrySq (G y) := by
  set L := fderiv ℝ χ y
  set D := driftField α a v G y
  have hc0 : 0 ≤ c := (norm_nonneg _).trans hc1
  have he : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hterm : ∀ i : Fin 3, |L (unitVector i) * inner ℝ D (G y (unitVector i))|
      ≤ c * ((‖D‖ ^ 2 + entrySq (G y)) / 2) := by
    intro i
    rw [abs_mul]
    have h1 : |L (unitVector i)| ≤ c := by
      have := L.le_opNorm (unitVector i)
      rw [norm_unitVector, mul_one, Real.norm_eq_abs] at this
      exact this.trans hc1
    have h2 : |inner ℝ D (G y (unitVector i))| ≤ (‖D‖ ^ 2 + entrySq (G y)) / 2 := by
      have h3 := abs_real_inner_le_norm D (G y (unitVector i))
      have h4 : ‖G y (unitVector i)‖ ^ 2 ≤ entrySq (G y) :=
        Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _)
          (Finset.mem_univ i)
      nlinarith [sq_nonneg (‖D‖ - ‖G y (unitVector i)‖)]
    exact mul_le_mul h1 h2 (abs_nonneg _) hc0
  have hsum : |∑ i : Fin 3, L (unitVector i) * inner ℝ D (G y (unitVector i))|
      ≤ c * (3 / 2) * (‖D‖ ^ 2 + entrySq (G y)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_refl _
  have hw : ‖(1 / (2 * α)) • y + a • axialTurn y‖ ≤ (|1 / (2 * α)| + |a|) * ‖y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := norm_axialTurn_le y
    nlinarith [abs_nonneg a, abs_nonneg (1 / (2 * α)), norm_nonneg y]
  have hsec : |(1 / 2) * L ((1 / (2 * α)) • y + a • axialTurn y) * entrySq (G y)|
      ≤ c * (|1 / (2 * α)| + |a|) * entrySq (G y) := by
    rw [abs_mul, abs_mul, abs_of_nonneg he, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h5 : |L ((1 / (2 * α)) • y + a • axialTurn y)| ≤ 2 * c * (|1 / (2 * α)| + |a|) := by
      have := L.le_opNorm ((1 / (2 * α)) • y + a • axialTurn y)
      rw [Real.norm_eq_abs] at this
      refine this.trans ?_
      calc ‖L‖ * ‖(1 / (2 * α)) • y + a • axialTurn y‖ ≤ ‖L‖ * ((|1 / (2 * α)| + |a|) * ‖y‖) :=
            mul_le_mul_of_nonneg_left hw (norm_nonneg _)
        _ = (‖L‖ * ‖y‖) * (|1 / (2 * α)| + |a|) := by ring
        _ ≤ 2 * c * (|1 / (2 * α)| + |a|) :=
            mul_le_mul_of_nonneg_right hc2 (by positivity)
    have := mul_le_mul_of_nonneg_right h5 he
    nlinarith
  unfold driftBoundary
  refine (abs_sub _ _).trans ?_
  exact add_le_add hsum hsec

private theorem axialTurn_eq (y : Space) : axialTurn y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
  ext j
  fin_cases j <;> simp [axialTurn, unitVector]

private theorem contDiff_axialTurn : ContDiff ℝ ∞ axialTurn := by
  have h : axialTurn = fun y => (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := funext axialTurn_eq
  rw [h]
  fun_prop

private theorem contDiff_driftFlux (α a : ℝ) (u : Space → Space) (hu : ContDiff ℝ ∞ u) (χ : Space → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (i : Fin 3) : ContDiff ℝ ∞ (driftFlux α a u χ i) := by
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hw := contDiff_axialTurn
  have hD : ContDiff ℝ ∞ (driftField α a u (fderiv ℝ u)) := by
    unfold driftField
    exact ((hu.const_smul _).add ((hDu.clm_apply contDiff_id).const_smul _)).add
      (((hDu.clm_apply hw).sub (hw.comp hu)).const_smul _)
  have hin : ContDiff ℝ ∞ (fun y => inner ℝ (driftField α a u (fderiv ℝ u) y) (fderiv ℝ u y (unitVector i))) :=
    hD.inner ℝ (hDu.clm_apply contDiff_const)
  have hc1 : ContDiff ℝ ∞ (fun y : Space => y i) := by
    simpa using (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff (n := ∞)
  have hc2 : ContDiff ℝ ∞ (fun y : Space => axialTurn y i) := by
    have := ((EuclideanSpace.proj (𝕜 := ℝ) i).contDiff (n := ∞)).comp hw
    simpa [Function.comp_def] using this
  have hE : ContDiff ℝ ∞ (fun y => entrySq (fderiv ℝ u y)) := by
    unfold entrySq
    exact ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (hDu.clm_apply contDiff_const)
  unfold driftFlux
  exact hχ.mul (hin.neg.add ((contDiff_const.mul ((contDiff_const.mul hc1).add (contDiff_const.mul hc2))).mul hE))

private theorem integral_fderiv_eq_zero {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (e : Space) : ∫ y, fderiv ℝ f y e = 0 := by
  have hfd : Continuous (fun y => fderiv ℝ f y e) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := e)
    (f := fun _ : Space => (1 : ℝ)) (g := f) (by simp) (by simpa using hfd.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply ℝ hc e))
    (by simpa using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hf.differentiable (by simp)) x)
  simpa using h

private theorem compactSupport_of_factor {χ g : Space → ℝ} (hχ : HasCompactSupport χ)
    (h : ∀ y, χ y = 0 → g y = 0) : HasCompactSupport g :=
  hχ.mono' fun y hy => subset_tsupport _ fun h0 => hy (h y h0)

theorem driftLocalSmooth_of (hdiv : DriftDivergenceStatement) : DriftLocalSmoothStatement := by
  intro α a u hu χ hχ
  have hpt := hdiv α a u hu χ hχ.1
  have hreg : ∀ i, ContDiff ℝ 1 (driftFlux α a u χ i) := fun i =>
    (contDiff_driftFlux α a u hu χ hχ.1 i).of_le (by simp)
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hD2u : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ u)) := hDu.fderiv_right (by simp)
  have c0 : Continuous u := hu.continuous
  have c1 : Continuous (fderiv ℝ u) := hDu.continuous
  have c2 : Continuous (fderiv ℝ (fderiv ℝ u)) := hD2u.continuous
  have cχ : Continuous χ := hχ.1.continuous
  have cdχ : Continuous (fderiv ℝ χ) := hχ.1.continuous_fderiv (by simp)
  have cw : Continuous axialTurn := continuous_axialTurn
  have cD : Continuous (driftField α a u (fderiv ℝ u)) := by
    unfold driftField
    fun_prop
  have cT : Continuous (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z)) := by
    unfold negSecondTrace secondTrace
    fun_prop
  have cE : Continuous (fun y => entrySq (fderiv ℝ u y)) := by
    unfold entrySq
    fun_prop
  have cB : Continuous (driftBoundary α a u (fderiv ℝ u) χ) := by
    unfold driftBoundary
    fun_prop
  have i1 : Integrable (fun y => χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
      (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y)) :=
    (cχ.mul (cD.inner cT)).integrable_of_hasCompactSupport
      (compactSupport_of_factor hχ.2 fun y h => by simp [h])
  have i2 : Integrable (fun y => χ y * entrySq (fderiv ℝ u y)) :=
    (cχ.mul cE).integrable_of_hasCompactSupport (compactSupport_of_factor hχ.2 fun y h => by simp [h])
  have i3 : Integrable (driftBoundary α a u (fderiv ℝ u) χ) :=
    cB.integrable_of_hasCompactSupport ((HasCompactSupport.fderiv ℝ hχ.2).mono' fun y hy => subset_tsupport _ fun h0 => hy (by
      simp [driftBoundary, h0]))
  have hzero : ∫ y, ∑ i : Fin 3, fderiv ℝ (driftFlux α a u χ i) y (unitVector i) = 0 := by
    rw [integral_finsetSum]
    · refine Finset.sum_eq_zero fun i _ => integral_fderiv_eq_zero (hreg i) ?_ _
      exact compactSupport_of_factor hχ.2 fun y h => by simp [driftFlux, h]
    · intro i _
      exact ((hreg i).continuous_fderiv (by simp)).clm_apply continuous_const |>.integrable_of_hasCompactSupport
        (HasCompactSupport.fderiv_apply ℝ (compactSupport_of_factor hχ.2 fun y h => by simp [driftFlux, h]) _)
  simp_rw [hpt] at hzero
  have e1 : ∫ y, (χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
      (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y)
        - (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y)) - driftBoundary α a u (fderiv ℝ u) χ y)
      = (∫ y, (χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
      (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y)
        - (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y)))) - ∫ y, driftBoundary α a u (fderiv ℝ u) χ y :=
    integral_sub (i1.sub (i2.const_mul _)) i3
  have e2 : ∫ y, (χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
      (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y)
        - (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y)))
      = (∫ y, χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
      (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y))
        - ∫ y, (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y)) :=
    integral_sub i1 (i2.const_mul _)
  have e3 : ∫ y, (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y))
      = (1 - 3 / (4 * α)) * ∫ y, χ y * entrySq (fderiv ℝ u y) := integral_const_mul _ _
  linarith

private def turnMap : Space →L[ℝ] Space :=
  (-(EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 3))).smulRight (unitVector 0) +
    (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 3)).smulRight (unitVector 1)

private theorem turnMap_eq (y : Space) : turnMap y = axialTurn y := by
  ext j
  fin_cases j <;> simp [turnMap, axialTurn, unitVector]

private theorem expand_vec (x : Space) : x = x 0 • unitVector 0 + x 1 • unitVector 1 + x 2 • unitVector 2 := by
  ext j
  fin_cases j <;> simp [unitVector]

private theorem turnMap_units : turnMap (unitVector 0) = unitVector 1 ∧ turnMap (unitVector 1) = -unitVector 0 ∧
    turnMap (unitVector 2) = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext j <;> fin_cases j <;> simp [turnMap, unitVector]

private theorem turnMap_expand (z : Space) : turnMap z = (-(z 1)) • unitVector 0 + (z 0) • unitVector 1 := by
  ext j
  fin_cases j <;> simp [turnMap, unitVector]

set_option maxRecDepth 20000 in
theorem driftDivergence : DriftDivergenceStatement := by
  intro α a u hu χ hχ y
  have hDu : ContDiff ℝ ∞ (fderiv ℝ u) := hu.fderiv_right (by simp)
  have hfu : ∀ z, HasFDerivAt u (fderiv ℝ u z) z := fun z => (hu.differentiable (by simp) z).hasFDerivAt
  have hfA : ∀ z, HasFDerivAt (fderiv ℝ u) (fderiv ℝ (fderiv ℝ u) z) z :=
    fun z => (hDu.differentiable (by simp) z).hasFDerivAt
  have hfχ : HasFDerivAt χ (fderiv ℝ χ y) y := (hχ.differentiable (by simp) y).hasFDerivAt
  have hW : ∀ z, HasFDerivAt axialTurn turnMap z := by
    intro z
    have h : axialTurn = ⇑turnMap := funext fun y => (turnMap_eq y).symm
    rw [h]
    exact turnMap.hasFDerivAt
  have hsym : ∀ v w : Space, fderiv ℝ (fderiv ℝ u) y v w = fderiv ℝ (fderiv ℝ u) y w v :=
    fun v w => (hu.contDiffAt.isSymmSndFDerivAt (by simp; exact WithTop.coe_le_coe.mpr le_top)) v w
  have hD := ((((hfu y).const_smul (1 - 1 / (2 * α))).add
    (((hfA y).clm_apply (hasFDerivAt_id y)).const_smul (1 / (2 * α)))).add
    ((((hfA y).clm_apply (hW y)).sub ((hW (u y)).comp y (hfu y))).const_smul a))
  have hF := fun i : Fin 3 => hfχ.mul
    ((hD.inner ℝ ((hfA y).clm_apply (hasFDerivAt_const (unitVector i) y))).neg.add
      ((((((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := y)).const_mul (1 / (2 * α))).add
        ((((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt (x := axialTurn y)).comp y (hW y)).const_mul a)).const_mul (1 / 2)).mul
        (HasFDerivAt.fun_sum (u := Finset.univ) fun j _ =>
          ((hfA y).clm_apply (hasFDerivAt_const (unitVector j) y)).norm_sq)))
  rw [Finset.sum_congr rfl fun i _ => congrArg (fun L => L (unitVector i))
    (HasFDerivAt.fderiv (f := driftFlux α a u χ i) (hF i))]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, neg_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply, sub_apply, FunLike.coe_sum,
    Finset.sum_apply, innerSL_apply_apply, smul_eq_mul, ContinuousLinearMap.id_apply, zero_apply]
  set A := fderiv ℝ u y with hA
  set B := fderiv ℝ (fderiv ℝ u) y with hB
  have hBy : ∀ v, B v y = y 0 • B v (unitVector 0) + y 1 • B v (unitVector 1) + y 2 • B v (unitVector 2) :=
    fun v => (congrArg (B v) (expand_vec y)).trans (by simp only [map_add, map_smul])
  have hBw : ∀ v, B v (axialTurn y) = (-(y 1)) • B v (unitVector 0) + y 0 • B v (unitVector 1) :=
    fun v => (congrArg (B v) ((turnMap_eq y).symm.trans (turnMap_expand y))).trans (by simp only [map_add, map_smul])
  obtain ⟨ht0, ht1, ht2⟩ := turnMap_units
  have hs10 := hsym (unitVector 1) (unitVector 0)
  have hs20 := hsym (unitVector 2) (unitVector 0)
  have hs21 := hsym (unitVector 2) (unitVector 1)
  have hAy : A y = y 0 • A (unitVector 0) + y 1 • A (unitVector 1) + y 2 • A (unitVector 2) :=
    (congrArg A (expand_vec y)).trans (by simp only [map_add, map_smul])
  have hAw : A (axialTurn y) = (-(y 1)) • A (unitVector 0) + y 0 • A (unitVector 1) :=
    (congrArg A ((turnMap_eq y).symm.trans (turnMap_expand y))).trans (by simp only [map_add, map_smul])
  have hCy : fderiv ℝ χ y y = y 0 * fderiv ℝ χ y (unitVector 0) + y 1 * fderiv ℝ χ y (unitVector 1)
      + y 2 * fderiv ℝ χ y (unitVector 2) :=
    (congrArg (fderiv ℝ χ y) (expand_vec y)).trans (by simp only [map_add, map_smul, smul_eq_mul])
  have hproj : ∀ (i : Fin 3) (x : Space), EuclideanSpace.proj (𝕜 := ℝ) i x = x i := fun i x => rfl
  have haxe : ∀ z : Space, axialTurn z = (-(z 1)) • unitVector 0 + (z 0) • unitVector 1 :=
    fun z => (turnMap_eq z).symm.trans (turnMap_expand z)
  simp only [Pi.add_apply, Pi.smul_apply, Pi.mul_apply, Pi.neg_apply, Pi.sub_apply, Function.comp_apply, id,
    map_zero, zero_add, add_zero, hproj, nsmul_eq_mul, Fin.sum_univ_three,
    driftField, negSecondTrace, secondTrace, entrySq, driftBoundary, ← hA, ← hB, ht0, ht1, ht2, map_neg]
  simp only [hBy, hBw, hAy, hAw, hCy]
  simp only [map_add, map_smul, map_neg, map_sub, hs10, hs20, hs21, haxe, hCy, turnMap_expand]
  simp [EuclideanSpace.norm_sq_eq, PiLp.inner_apply, Fin.sum_univ_three, unitVector, hproj]
  ring

theorem driftLocal_of (hS : DriftLocalSmoothStatement) (hA : DriftLocalApproxStatement) :
    DriftLocalStatement := by
  intro α a m v G H hv χ hχ
  obtain ⟨u, hu, h1, h2, h3⟩ := hA α a m v G H hv χ hχ
  have h4 := (h2.const_mul (1 - 3 / (4 * α))).add h3
  refine tendsto_nhds_unique h1 (h4.congr' (Eventually.of_forall fun n => ?_))
  exact (hS α a (u n) (hu n) χ hχ).symm

theorem driftEnergy_of (hL : DriftLocalStatement) : DriftEnergyStatement := by
  intro α _ _ a m v G H hv hD
  obtain ⟨c, hc0, hc⟩ := cutoff_bounds
  set D := driftField α a v G with hDdef
  set k : ℝ := 1 - 3 / (4 * α) with hk
  set χ : ℕ → Space → ℝ := fun n => radialCutoff ((n : ℝ) + 1) with hχ
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hr1 : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 1 := fun n => by
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have hχc : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => contDiff_radialCutoff (hr n)
  have hχtest : ∀ n, IsTestScalar (χ n) := fun n => ⟨hχc n, hasCompactSupport_radialCutoff (hr n)⟩
  have hχb : ∀ n y, ‖χ n y‖ ≤ 1 := fun n y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have hT := memLp_negSecondTrace hv
  have hD2 : Integrable (fun y => ‖D y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hD.1).1 hD
  have hT2 : Integrable (fun y => ‖negSecondTrace H y‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hT.1).1 hT
  have he := hv.gradient_two
  have hfm : AEStronglyMeasurable (fun y => inner ℝ (D y) (negSecondTrace H y)) volume :=
    hD.1.inner hT.1
  have hf : Integrable (fun y => inner ℝ (D y) (negSecondTrace H y)) := by
    refine ((hD2.add hT2).div_const 2).mono' hfm (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    have h3 := abs_real_inner_le_norm (D y) (negSecondTrace H y)
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (‖D y‖ - ‖negSecondTrace H y‖)]
  have heventually : ∀ y : Space, ∀ᶠ n : ℕ in atTop, χ n y = 1 ∧ fderiv ℝ (χ n) y = 0 := by
    intro y
    refine eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩
    have h1 : ‖y‖ < (n : ℝ) + 1 := by
      have := Nat.le_ceil ‖y‖
      have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    exact ⟨radialCutoff_eq_one (hr n) h1.le, fderiv_cutoff_near (hr n) h1⟩
  have hlim1 : Tendsto (fun n : ℕ => ∫ y, χ n y * inner ℝ (D y) (negSecondTrace H y)) atTop
      (𝓝 (∫ y, inner ℝ (D y) (negSecondTrace H y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖inner ℝ (D y) (negSecondTrace H y)‖)
      (fun n => ((hχc n).continuous.aestronglyMeasurable.mul hfm)) hf.norm
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχb n y)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [heventually y] with n hn
      rw [hn.1, one_mul]
  have hem : AEStronglyMeasurable (fun y => entrySq (G y)) volume := he.1
  have hlim2 : Tendsto (fun n : ℕ => ∫ y, χ n y * entrySq (G y)) atTop (𝓝 (∫ y, entrySq (G y))) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖entrySq (G y)‖)
      (fun n => ((hχc n).continuous.aestronglyMeasurable.mul hem)) he.norm
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hχb n y)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [heventually y] with n hn
      rw [hn.1, one_mul]
  have hBm : ∀ n, AEStronglyMeasurable (driftBoundary α a v G (χ n)) volume := by
    intro n
    have hfd : Continuous (fun y => fderiv ℝ (χ n) y) := (hχc n).continuous_fderiv (by simp)
    unfold driftBoundary
    refine AEStronglyMeasurable.sub ?_ ?_
    · refine Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ => ?_
      exact (hfd.clm_apply continuous_const).aestronglyMeasurable.mul
        (hD.1.inner (aesm_apply_first hv.measurable_gradient i))
    · refine AEStronglyMeasurable.mul ?_ hem
      refine (continuous_const.mul (hfd.clm_apply ?_)).aestronglyMeasurable
      exact (continuous_id.const_smul (1 / (2 * α))).add (continuous_axialTurn.const_smul a)
  have hlim3 : Tendsto (fun n : ℕ => ∫ y, driftBoundary α a v G (χ n) y) atTop (𝓝 (∫ _y : Space, (0 : ℝ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => c * (3 / 2) * (‖D y‖ ^ 2 + entrySq (G y)) + c * (|1 / (2 * α)| + |a|) * entrySq (G y))
      hBm (((hD2.add he).const_mul _).add (he.const_mul _))
      (fun n => Eventually.of_forall fun y => ?_) (Eventually.of_forall fun y => ?_)
    · rw [Real.norm_eq_abs]
      exact boundary_bound α a c v G (χ n) y ((hc _ (hr1 n) y).1) ((hc _ (hr1 n) y).2)
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [heventually y] with n hn
      simp [driftBoundary, hn.2]
  rw [integral_zero] at hlim3
  have hloc : ∀ n : ℕ, ∫ y, χ n y * inner ℝ (D y) (negSecondTrace H y)
      = k * (∫ y, χ n y * entrySq (G y)) + ∫ y, driftBoundary α a v G (χ n) y :=
    fun n => hL α a m v G H hv (χ n) (hχtest n)
  have hlim4 : Tendsto (fun n : ℕ => ∫ y, χ n y * inner ℝ (D y) (negSecondTrace H y)) atTop
      (𝓝 (k * (∫ y, entrySq (G y)) + 0)) := by
    have := (hlim2.const_mul k).add hlim3
    refine this.congr' (Eventually.of_forall fun n => ?_)
    exact (hloc n).symm
  have := tendsto_nhds_unique hlim1 hlim4
  rw [add_zero] at this
  exact this

theorem driftEnergy : DriftEnergyStatement :=
  driftEnergy_of (driftLocal_of (driftLocalSmooth_of driftDivergence) driftLocalApprox)

end SteadyCert

end Breakdown

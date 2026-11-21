import Breakdown.FracCert.FreeSymbolExistsSmooth

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolEquationInternal

open FreeSymbolSmoothInternal

def hbase (α a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) : Freq.CSpace :=
  ∫ τ in Set.Ioi (0 : ℝ), kernel α a s ξ τ

def turnCL : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurn
      map_add' := fun x y => by ext i; fin_cases i <;> simp [axialTurn] <;> ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [axialTurn] }

def axisCL : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => EuclideanSpace.single 2 (y 2)
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }

def turnCLC : Freq.CSpace →L[ℝ] Freq.CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurnC
      map_add' := fun x y => by ext i; fin_cases i <;> simp [axialTurnC] <;> ring
      map_smul' := fun c x => by ext i; fin_cases i <;> simp [axialTurnC] }

def axisCLC : Freq.CSpace →L[ℝ] Freq.CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => EuclideanSpace.single 2 (y 2)
      map_add' := fun x y => by ext i; fin_cases i <;> simp
      map_smul' := fun c x => by ext i; fin_cases i <;> simp }

theorem turnCL_apply (y : Space) : turnCL y = axialTurn y := rfl

theorem axisCL_apply (y : Space) : axisCL y = EuclideanSpace.single 2 (y 2) := rfl

theorem turnCLC_apply (z : Freq.CSpace) : turnCLC z = axialTurnC z := rfl

theorem axisCLC_apply (z : Freq.CSpace) : axisCLC z = EuclideanSpace.single 2 (z 2) := rfl

theorem rot_zero (y : Space) : axialRotationFormula 0 y = y := by
  ext i
  fin_cases i <;> simp [axialRotationFormula]

theorem rotC_zero' (z : Freq.CSpace) : axialRotationC 0 z = z := by
  ext i
  fin_cases i <;> simp [axialRotationC]

theorem rot_decomp (θ : ℝ) (y : Space) : axialRotationFormula θ y =
    Real.cos θ • y + Real.sin θ • turnCL y + (1 - Real.cos θ) • axisCL y := by
  ext i
  fin_cases i <;> simp [axialRotationFormula, turnCL, axisCL, axialTurn] <;> ring

theorem rotC_decomp (θ : ℝ) (z : Freq.CSpace) : axialRotationC θ z =
    Real.cos θ • z + Real.sin θ • turnCLC z + (1 - Real.cos θ) • axisCLC z := by
  ext i
  fin_cases i <;> simp [axialRotationC, turnCLC, axisCLC, axialTurnC, -Complex.ofReal_cos, -Complex.ofReal_sin] <;> ring

theorem cos_deriv (a : ℝ) : HasDerivAt (fun t : ℝ => Real.cos (a * t)) 0 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).const_mul a).cos
  simpa using this

theorem sin_deriv (a : ℝ) : HasDerivAt (fun t : ℝ => Real.sin (a * t)) a 0 := by
  have := ((hasDerivAt_id (0 : ℝ)).const_mul a).sin
  simpa using this

theorem rotC_deriv (a : ℝ) {A : ℝ → Freq.CSpace} {A' : Freq.CSpace} (hA : HasDerivAt A A' 0) :
    HasDerivAt (fun t => axialRotationC (a * t) (A t)) (A' + a • axialTurnC (A 0)) 0 := by
  simp_rw [rotC_decomp]
  have h1 := (cos_deriv a).smul hA
  have h2 := (sin_deriv a).smul (turnCLC.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA)
  have h3 := ((cos_deriv a).const_sub 1).smul (axisCLC.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hA)
  refine ((h1.add h2).add h3).congr_deriv ?_
  simp [turnCLC_apply]

theorem rot_deriv (a : ℝ) (ξ : Space) :
    HasDerivAt (fun t => axialRotationFormula (a * t) ξ) (a • axialTurn ξ) 0 := by
  simp_rw [rot_decomp]
  have h1 := (cos_deriv a).smul_const ξ
  have h2 := (sin_deriv a).smul_const (turnCL ξ)
  have h3 := ((cos_deriv a).const_sub 1).smul_const (axisCL ξ)
  refine ((h1.add h2).add h3).congr_deriv ?_
  simp [turnCL_apply]

def flowPt (α a : ℝ) (ξ : Space) (t : ℝ) : Space :=
  Real.exp ((-t) / (2 * α)) • axialRotationFormula (a * t) ξ

theorem flow_zero (α a : ℝ) (ξ : Space) : flowPt α a ξ 0 = ξ := by
  ext i
  fin_cases i <;> simp [flowPt, axialRotationFormula]

theorem flow_deriv (α a : ℝ) (ξ : Space) :
    HasDerivAt (flowPt α a ξ) (-(1 / (2 * α)) • ξ + a • axialTurn ξ) 0 := by
  have he : HasDerivAt (fun t : ℝ => Real.exp ((-t) / (2 * α))) (-(1 / (2 * α))) 0 := by
    refine (((hasDerivAt_id' (0 : ℝ)).neg).div_const (2 * α)).exp.congr_deriv ?_
    simp [neg_div]
  refine (he.smul (rot_deriv a ξ)).congr_deriv ?_
  simp [rot_zero, add_comm]

theorem rot_smul' (θ c : ℝ) (y : Space) : axialRotationFormula θ (c • y) = c • axialRotationFormula θ y := by
  ext i
  fin_cases i <;> simp [axialRotationFormula] <;> ring

theorem rot_rot (θ φ : ℝ) (y : Space) :
    axialRotationFormula θ (axialRotationFormula φ y) = axialRotationFormula (θ + φ) y := by
  ext i
  fin_cases i <;> simp [axialRotationFormula, Real.cos_add, Real.sin_add] <;> ring

theorem rotC_rotC (θ φ : ℝ) (z : Freq.CSpace) :
    axialRotationC θ (axialRotationC φ z) = axialRotationC (θ + φ) z := by
  ext i
  fin_cases i <;> simp [axialRotationC, Real.cos_add, Real.sin_add, -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    push_cast <;> ring

theorem kernel_shift (α a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) (t τ : ℝ) :
    kernel α a s (flowPt α a ξ t) τ =
      Real.exp (-((1 - 2 / α) * t)) • axialRotationC (a * t) (kernel α a s ξ (τ - t)) := by
  unfold kernel flowPt
  rw [rot_smul', rot_rot, smul_smul, ← Real.exp_add, rotC_smul, rotC_rotC, smul_smul, ← Real.exp_add]
  rw [show τ / (2 * α) + -t / (2 * α) = (τ - t) / (2 * α) by ring, show -(a * τ) + a * t = -(a * (τ - t)) by ring,
    show -((1 - 2 / α) * t) + -((1 - 2 / α) * (τ - t)) = -((1 - 2 / α) * τ) by ring,
    show a * t + a * (τ - t) = a * τ by ring]

theorem kernel_cont (α a : ℝ) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) (ξ : Space) :
    Continuous (kernel α a s ξ) :=
  (kernel_smooth α a hs).continuous.comp (continuous_const.prodMk continuous_id)

theorem core_eq_interval {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ∃ R : ℝ, 0 < R ∧ ∀ (ξ : Space) (ε T : ℝ), 0 < ε → ε < ‖ξ‖ → 2 * α * (R / ε) ≤ T →
      hbase α a s ξ = ∫ τ in (0 : ℝ)..T, kernel α a s ξ τ := by
  obtain ⟨R, hR, hfar⟩ := kernel_far (a := a) hα hs
  refine ⟨R, hR, fun ξ ε T hε hξ hT => ?_⟩
  have hT0 : 0 ≤ T := le_trans (by positivity) hT
  unfold hbase
  rw [intervalIntegral.integral_of_le hT0]
  refine setIntegral_eq_of_subset_of_ae_sdiff_eq_zero (μ := volume) (f := fun τ => kernel α a s ξ τ)
      (measurableSet_Ioi (a := (0 : ℝ))).nullMeasurableSet
      (Set.Ioc_subset_Ioi_self : Set.Ioc (0 : ℝ) T ⊆ Set.Ioi 0) (Filter.Eventually.of_forall fun τ hτ => ?_)
  have hτT : T < τ := by
    by_contra h
    exact hτ.2 ⟨hτ.1, le_of_not_gt h⟩
  exact hfar ξ ε hε hξ τ (lt_of_le_of_lt hT hτT)

theorem core_contDiffAt {α a : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s)
    {ξ0 : Space} (hξ0 : ξ0 ≠ 0) : ContDiffAt ℝ ∞ (hbase α a s) ξ0 := by
  obtain ⟨R, hR, hint⟩ := core_eq_interval (a := a) hα hs
  set ε : ℝ := ‖ξ0‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  have hc : ContDiff ℝ ∞ (fun ξ => ∫ τ in (0 : ℝ)..(2 * α * (R / ε)), kernel α a s ξ τ) :=
    contDiff_infty.2 fun n => Coercive.StretchInternal.contDiff_intervalIntegral_param 0 _ n
      (kernel α a s) ((kernel_smooth α a hs).of_le (by exact_mod_cast le_top))
  have hopen : IsOpen {ξ : Space | ε < ‖ξ‖} := isOpen_lt continuous_const continuous_norm
  have hmem : ξ0 ∈ {ξ : Space | ε < ‖ξ‖} := by
    show ε < ‖ξ0‖
    have : 0 < ‖ξ0‖ := norm_pos_iff.2 hξ0
    linarith
  refine hc.contDiffAt.congr_of_eventuallyEq (Filter.eventually_of_mem (hopen.mem_nhds hmem) fun ξ hξ => ?_)
  exact hint ξ ε _ hεpos hξ le_rfl

theorem core_deriv {α a : ℝ} (hα1 : 1 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) {ξ : Space}
    (hξ : ξ ≠ 0) :
    fderiv ℝ (hbase α a s) ξ (-(1 / (2 * α)) • ξ + a • axialTurn ξ) =
      Real.exp (-((1 - 2 / α) * 0)) • (kernel α a s ξ 0 + a • axialTurnC (hbase α a s ξ)) +
        (-(1 - 2 / α)) • hbase α a s ξ := by
  have hα : 0 < α := by linarith
  obtain ⟨R, hR, hint⟩ := core_eq_interval (a := a) hα hs
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set ε : ℝ := ‖ξ‖ / 4 with hε
  have hεpos : 0 < ε := by positivity
  set T : ℝ := 2 * α * (R / ε) + 1 with hT
  have hKc : Continuous (kernel α a s ξ) := kernel_cont α a hs ξ
  set A : ℝ → Freq.CSpace := fun t => (∫ σ in (-t)..0, (kernel α a s ξ) σ) + hbase α a s ξ with hA
  set F : ℝ → Freq.CSpace := fun t => Real.exp (-((1 - 2 / α) * t)) • axialRotationC (a * t) (A t) with hF
  have heq : (fun t => hbase α a s (flowPt α a ξ t)) =ᶠ[nhds 0] F := by
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhds (0 : ℝ) := Ioo_mem_nhds (by norm_num) (by norm_num)
    refine Filter.eventually_of_mem hmem fun t ht => ?_
    have hnorm : ε < ‖flowPt α a ξ t‖ := by
      rw [flowPt, norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have h1 : -(1 / 2) < -t / (2 * α) := by
        rw [lt_div_iff₀ (by linarith)]
        nlinarith [ht.1, ht.2]
      have h2 : 1 / 2 < Real.exp (-t / (2 * α)) := by linarith [Real.add_one_le_exp (-t / (2 * α))]
      nlinarith
    show hbase α a s (flowPt α a ξ t) = F t
    rw [hint _ ε T hεpos hnorm (by linarith)]
    simp_rw [kernel_shift]
    rw [intervalIntegral.integral_smul]
    set L : Freq.CSpace →L[ℝ] Freq.CSpace := Real.cos (a * t) • ContinuousLinearMap.id ℝ Freq.CSpace +
      Real.sin (a * t) • turnCLC + (1 - Real.cos (a * t)) • axisCLC with hLdef
    have hL : ∀ z, axialRotationC (a * t) z = L z := by
      intro z
      rw [rotC_decomp]
      simp [L]
    simp_rw [hL]
    have hii : IntervalIntegrable (fun x => kernel α a s ξ (x - t)) volume 0 T :=
      (hKc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
    rw [L.intervalIntegral_comp_comm hii,
      intervalIntegral.integral_comp_sub_right (kernel α a s ξ) t,
      ← intervalIntegral.integral_add_adjacent_intervals (hKc.intervalIntegrable (0 - t) 0)
        (hKc.intervalIntegrable 0 (T - t)),
      ← hint ξ ε (T - t) hεpos (by linarith) (by linarith [ht.2]), zero_sub, ← hL]
  have h1 : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, (kernel α a s ξ) x) ((kernel α a s ξ) 0) (-(0 : ℝ)) := by
    rw [neg_zero]
    exact (hKc.integral_hasStrictDerivAt 0 0).hasDerivAt
  have h2 : HasDerivAt (fun t : ℝ => ∫ x in (0 : ℝ)..(-t), (kernel α a s ξ) x) ((-1 : ℝ) • (kernel α a s ξ) 0) 0 :=
    h1.scomp (0 : ℝ) (hasDerivAt_id' (0 : ℝ)).neg
  have h3 : HasDerivAt (fun t : ℝ => ∫ σ in (-t)..0, (kernel α a s ξ) σ) ((kernel α a s ξ) 0) 0 := by
    refine (h2.neg.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    exact intervalIntegral.integral_symm _ _
  have hG := rotC_deriv a (h3.add_const (hbase α a s ξ))
  have hE : HasDerivAt (fun t : ℝ => Real.exp (-((1 - 2 / α) * t))) (Real.exp (-((1 - 2 / α) * 0)) * (-(1 - 2 / α))) 0 :=
    ((hasDerivAt_id' (0 : ℝ)).const_mul (1 - 2 / α)).neg.exp.congr_deriv (by simp)
  have hFd := hE.smul hG
  have hd : DifferentiableAt ℝ (hbase α a s) ξ := (core_contDiffAt hα hs hξ).differentiableAt (by simp)
  have hfd : HasFDerivAt (hbase α a s) (fderiv ℝ (hbase α a s) ξ) (flowPt α a ξ 0) := by
    rw [flow_zero]
    exact hd.hasFDerivAt
  have hch := hfd.comp_hasDerivAt (0 : ℝ) (flow_deriv α a ξ)
  have hu := (hFd.congr_of_eventuallyEq heq).unique hch
  rw [← hu]
  simp [rotC_zero', smul_smul]

theorem pow_deriv {α a : ℝ} (hα : 0 < α) {ξ : Space} (hξ : ξ ≠ 0) :
    fderiv ℝ (freqPow (2 * α)) ξ (-(1 / (2 * α)) • ξ + a • axialTurn ξ) = -freqPow (2 * α) ξ := by
  have hd := (pow_smoothAt (2 * α) hξ).differentiableAt (by simp)
  have hfd : HasFDerivAt (freqPow (2 * α)) (fderiv ℝ (freqPow (2 * α)) ξ) (flowPt α a ξ 0) := by
    rw [flow_zero]
    exact hd.hasFDerivAt
  have hch := hfd.comp_hasDerivAt (0 : ℝ) (flow_deriv α a ξ)
  have hfun : (fun t => freqPow (2 * α) (flowPt α a ξ t)) = fun t => Real.exp (-t) * freqPow (2 * α) ξ := by
    funext t
    unfold flowPt
    rw [pow_scale hα]
  have hk : HasDerivAt (fun t => freqPow (2 * α) (flowPt α a ξ t))
      (Real.exp (-0) * (-1) * freqPow (2 * α) ξ) 0 := by
    rw [hfun]
    exact ((hasDerivAt_id' (0 : ℝ)).neg.exp).mul_const _
  have hu := hk.unique hch
  rw [← hu]
  simp

theorem kernel_zero (α a : ℝ) (s : Space → Freq.CSpace) (ξ : Space) :
    kernel α a s ξ 0 = Real.exp (-freqPow (2 * α) ξ) • s ξ := by
  simp [kernel, damped, rotC_zero', rot_zero]

theorem turnC_smul (c : ℝ) (z : Freq.CSpace) : axialTurnC (c • z) = c • axialTurnC z := by
  rw [← turnCLC_apply, ← turnCLC_apply, map_smul]

theorem equation {α a : ℝ} (hα1 : 1 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) (ξ : Space)
    (hξ : ξ ≠ 0) : profileSymbolLhs α a (freeSolution α a s) ξ = s ξ := by
  have hα : 0 < α := by linarith
  have hw : freeSolution α a s = fun η => Real.exp (freqPow (2 * α) η) • hbase α a s η :=
    funext (solution_eq hα a s)
  have hk : HasFDerivAt (freqPow (2 * α)) (fderiv ℝ (freqPow (2 * α)) ξ) ξ :=
    ((pow_smoothAt _ hξ).differentiableAt (by simp)).hasFDerivAt
  have hc : HasFDerivAt (hbase α a s) (fderiv ℝ (hbase α a s) ξ) ξ :=
    ((core_contDiffAt hα hs hξ).differentiableAt (by simp)).hasFDerivAt
  have hW := hk.exp.smul hc
  have hD : ∀ v, fderiv ℝ (freeSolution α a s) ξ v =
      Real.exp (freqPow (2 * α) ξ) • fderiv ℝ (hbase α a s) ξ v +
        (Real.exp (freqPow (2 * α) ξ) * fderiv ℝ (freqPow (2 * α)) ξ v) • hbase α a s ξ := by
    intro v
    rw [hw]
    change fderiv ℝ ((fun x => Real.exp (freqPow (2 * α) x)) • hbase α a s) ξ v = _
    rw [hW.fderiv]
    simp
  have hV : fderiv ℝ (freeSolution α a s) ξ (-(1 / (2 * α)) • ξ + a • axialTurn ξ) =
      -(1 / (2 * α)) • fderiv ℝ (freeSolution α a s) ξ ξ + a • fderiv ℝ (freeSolution α a s) ξ (axialTurn ξ) := by
    simp
  unfold profileSymbolLhs
  have key : (1 - 2 / α) • freeSolution α a s ξ - (1 / (2 * α)) • fderiv ℝ (freeSolution α a s) ξ ξ +
      a • (fderiv ℝ (freeSolution α a s) ξ (axialTurn ξ) - axialTurnC (freeSolution α a s ξ)) +
      freqPow (2 * α) ξ • freeSolution α a s ξ =
      (1 - 2 / α) • freeSolution α a s ξ + fderiv ℝ (freeSolution α a s) ξ (-(1 / (2 * α)) • ξ + a • axialTurn ξ)
        - a • axialTurnC (freeSolution α a s ξ) + freqPow (2 * α) ξ • freeSolution α a s ξ := by
    rw [hV]
    module
  rw [key, hD, core_deriv hα1 hs hξ, pow_deriv hα hξ, kernel_zero,
    show freeSolution α a s ξ = Real.exp (freqPow (2 * α) ξ) • hbase α a s ξ from solution_eq hα a s ξ, turnC_smul]
  simp only [mul_zero, neg_zero, Real.exp_zero, one_smul, Real.exp_neg]
  match_scalars <;> field_simp <;> ring

end FreeSymbolEquationInternal

theorem freeSolutionEquation : FreeSolutionEquationStatement := fun _ hα1 _ _ _ hs ξ hξ =>
  FreeSymbolEquationInternal.equation hα1 hs ξ hξ

end SteadyCert

end Breakdown

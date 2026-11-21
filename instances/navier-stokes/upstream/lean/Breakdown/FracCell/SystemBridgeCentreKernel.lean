import Breakdown.FracCell.FieldJointSmooth
import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCell.SystemBridgesSums
import Breakdown.FracCell.ReductionLossKernelBound_of_cellSums
import Breakdown.FracCell.GivenToolkit
import Breakdown.FracCell.SystemBridgeSumWeights

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellSystem.CentreKernel.Internal

section Partials

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def partB (f : ℝ × E → F) : ℝ × E → F := fun q => deriv (fun b => f (b, q.2)) q.1

def partY (f : ℝ × E → F) : ℝ × E → (E →L[ℝ] F) := fun q => fderiv ℝ (fun y => f (q.1, y)) q.2

theorem deriv_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : ℝ × E → G} {b : ℝ} {y : E}
    (h : DifferentiableAt ℝ φ (b, y)) : deriv (fun b' => φ (b', y)) b = fderiv ℝ φ (b, y) (1, 0) := by
  have h1 : HasDerivAt (fun b' : ℝ => (b', y)) ((1 : ℝ), (0 : E)) b :=
    (hasDerivAt_id b).prodMk (hasDerivAt_const b y)
  exact (h.hasFDerivAt.comp_hasDerivAt b h1).deriv

theorem slice_hasDeriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : ℝ × E → G} {b : ℝ} {y : E}
    (h : DifferentiableAt ℝ φ (b, y)) :
    HasFDerivAt (fun y' => φ (b, y')) ((fderiv ℝ φ (b, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)) y :=
  h.hasFDerivAt.comp y (hasFDerivAt_prodMk_right b y)

theorem slice_deriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : ℝ × E → G} {b : ℝ} {y : E}
    (h : DifferentiableAt ℝ φ (b, y)) (v : E) : fderiv ℝ (fun y' => φ (b, y')) y v = fderiv ℝ φ (b, y) (0, v) := by
  rw [(slice_hasDeriv h).fderiv]
  rfl

variable {f : ℝ × E → F} {U : Set (ℝ × E)}

theorem diff_of {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) {q : ℝ × E} (hq : q ∈ U) :
    DifferentiableAt ℝ f q :=
  (hf.differentiableOn (by simp) q hq).differentiableAt (hU.mem_nhds hq)

theorem deriv_smooth {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) : ContDiffOn ℝ n (fderiv ℝ f) U :=
  hf.fderiv_of_isOpen hU le_rfl

theorem partB_eq {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) {q : ℝ × E} (hq : q ∈ U) :
    partB f q = fderiv ℝ f q (1, 0) := by
  obtain ⟨b, y⟩ := q
  exact deriv_slice (diff_of hf hU hq)

theorem partY_eq {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) {q : ℝ × E} (hq : q ∈ U) :
    partY f q = (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ E) := by
  obtain ⟨b, y⟩ := q
  exact (slice_hasDeriv (diff_of hf hU hq)).fderiv

theorem partB_smooth {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) : ContDiffOn ℝ n (partB f) U := by
  have h : ContDiffOn ℝ n (fun q => fderiv ℝ f q (1, 0)) U :=
    (deriv_smooth hf hU).clm_apply contDiffOn_const
  exact h.congr fun q hq => partB_eq hf hU hq

theorem partY_smooth {n : ℕ} (hf : ContDiffOn ℝ (n + 1) f U) (hU : IsOpen U) : ContDiffOn ℝ n (partY f) U := by
  have h : ContDiffOn ℝ n (fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ E)) U :=
    (deriv_smooth hf hU).clm_comp contDiffOn_const
  exact h.congr fun q hq => partY_eq hf hU hq

theorem partYB_comm {n : ℕ} (hf : ContDiffOn ℝ (n + 2) f U) (hU : IsOpen U) {b : ℝ} {y : E} (hq : (b, y) ∈ U) :
    partY (partB f) (b, y) = partB (partY f) (b, y) := by
  have hf1 : ContDiffOn ℝ ((n + 1 : ℕ) + 1) f U := by exact_mod_cast hf
  have hD : ContDiffOn ℝ (n + 1 : ℕ) (fderiv ℝ f) U := deriv_smooth hf1 hU
  have hD' : ContDiffOn ℝ (n + 1) (fderiv ℝ f) U := by exact_mod_cast hD
  have hDd : DifferentiableAt ℝ (fderiv ℝ f) (b, y) := diff_of hD' hU hq
  have hsym : IsSymmSndFDerivAt ℝ f (b, y) :=
    ((hf.contDiffAt (hU.mem_nhds hq)).isSymmSndFDerivAt (by simp))
  have hev : partB f =ᶠ[nhds (b, y)] fun q => fderiv ℝ f q (1, 0) :=
    Filter.eventually_of_mem (hU.mem_nhds hq) fun q hq' => partB_eq hf1 hU hq'
  have hev' : partY f =ᶠ[nhds (b, y)] fun q => (fderiv ℝ f q).comp (ContinuousLinearMap.inr ℝ ℝ E) :=
    Filter.eventually_of_mem (hU.mem_nhds hq) fun q hq' => partY_eq hf1 hU hq'
  have hB : DifferentiableAt ℝ (partB f) (b, y) := diff_of (by exact_mod_cast partB_smooth hf1 hU) hU hq
  have hY : DifferentiableAt ℝ (partY f) (b, y) := diff_of (by exact_mod_cast partY_smooth hf1 hU) hU hq
  ext v
  show fderiv ℝ (fun y' => partB f (b, y')) y v = deriv (fun b' => partY f (b', y)) b v
  rw [slice_deriv hB, deriv_slice hY, hev.fderiv_eq, hev'.fderiv_eq]
  rw [fderiv_clm_apply hDd (differentiableAt_const _), fderiv_clm_comp hDd (differentiableAt_const _)]
  simp only [fderiv_fun_const, fderiv_const_apply, Pi.zero_apply, ContinuousLinearMap.zero_apply, map_zero, zero_add,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.flip_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.inr_apply, ContinuousLinearMap.comp_zero]
  exact hsym (0, v) (1, 0)

def goodSet (f : ℝ × E → F) : Set (ℝ × E) := {q | ContDiffAt ℝ 5 f q}

theorem goodSet_open : IsOpen (goodSet f) :=
  isOpen_iff_mem_nhds.2 fun q hq => (ContDiffAt.eventually (show ContDiffAt ℝ 5 f q from hq) (by simp)).mono fun _ h => h

theorem goodSet_smooth : ContDiffOn ℝ 5 f (goodSet f) := fun q hq => (show ContDiffAt ℝ 5 f q from hq).contDiffWithinAt

theorem good_diff {q : ℝ × E} (hq : q ∈ goodSet f) : DifferentiableAt ℝ f q :=
  (show ContDiffAt ℝ 5 f q from hq).differentiableAt (by norm_num)

theorem slice_diff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {φ : ℝ × E → G} {b : ℝ} {y : E}
    (h : DifferentiableAt ℝ φ (b, y)) : DifferentiableAt ℝ (fun y' => φ (b, y')) y :=
  (slice_hasDeriv h).differentiableAt

theorem good_smooth (n : ℕ) (hn : n + 1 ≤ 5) : ContDiffOn ℝ (n + 1) f (goodSet f) :=
  goodSet_smooth.of_le (by exact_mod_cast hn)

end Partials

open Reduction


def Kb (f : Space → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ (∀ y, 0 ≤ f y) ∧ AEMeasurable f volume ∧
    ∀ x : Space, Integrable (fun y => f y ^ 2 / (4 * Real.pi * ‖x - y‖)) ∧
      (∫ y, f y ^ 2 / (4 * Real.pi * ‖x - y‖)) ≤ L ^ 2

theorem den_meas (x : Space) : Measurable (fun y : Space => 4 * Real.pi * ‖x - y‖) :=
  measurable_const.mul (measurable_const.sub measurable_id).norm

theorem den_nonneg (x y : Space) : 0 ≤ 4 * Real.pi * ‖x - y‖ := by positivity

theorem integrand_aem {f : Space → ℝ} (hf : AEMeasurable f volume) (x : Space) :
    AEStronglyMeasurable (fun y => f y ^ 2 / (4 * Real.pi * ‖x - y‖)) volume :=
  ((hf.pow_const 2).div (den_meas x).aemeasurable).aestronglyMeasurable

theorem kb_of_kernelBound {V : Space → ℝ} {L : ℝ} (h : KernelBound V (L ^ 2)) (hL : 0 ≤ L) :
    Kb (fun y => Real.sqrt (V y)) L := by
  obtain ⟨h0, hm, hx⟩ := h
  have e : ∀ y, Real.sqrt (V y) ^ 2 = V y := fun y => Real.sq_sqrt (h0 y)
  refine ⟨hL, fun y => Real.sqrt_nonneg _, hm.sqrt.aemeasurable, fun x => ?_⟩
  simp only [e]
  exact hx x

theorem kb_zero : Kb (fun _ => 0) 0 := by
  refine ⟨le_rfl, fun _ => le_rfl, aemeasurable_const, fun x => ?_⟩
  simp

theorem kb_smul {f : Space → ℝ} {L c : ℝ} (h : Kb f L) (hc : 0 ≤ c) : Kb (fun y => c * f y) (c * L) := by
  obtain ⟨hL, h0, hm, hx⟩ := h
  refine ⟨mul_nonneg hc hL, fun y => mul_nonneg hc (h0 y), hm.const_mul c, fun x => ?_⟩
  have e : (fun y => (c * f y) ^ 2 / (4 * Real.pi * ‖x - y‖)) = fun y => c ^ 2 * (f y ^ 2 / (4 * Real.pi * ‖x - y‖)) := by
    funext y; ring
  rw [e]
  refine ⟨(hx x).1.const_mul _, ?_⟩
  rw [integral_const_mul]
  calc c ^ 2 * ∫ y, f y ^ 2 / (4 * Real.pi * ‖x - y‖) ≤ c ^ 2 * L ^ 2 :=
        mul_le_mul_of_nonneg_left (hx x).2 (by positivity)
    _ = (c * L) ^ 2 := by ring

theorem kb_mono {f v : Space → ℝ} {L L' : ℝ} (h : Kb f L) (hv : AEMeasurable v volume) (hv0 : ∀ y, 0 ≤ v y)
    (hle : ∀ᵐ y ∂volume, v y ≤ f y) (hLL : L ≤ L') : Kb v L' := by
  obtain ⟨hL, h0, hm, hx⟩ := h
  refine ⟨hL.trans hLL, hv0, hv, fun x => ?_⟩
  have hpt : ∀ᵐ y ∂volume, v y ^ 2 / (4 * Real.pi * ‖x - y‖) ≤ f y ^ 2 / (4 * Real.pi * ‖x - y‖) := by
    filter_upwards [hle] with y hy
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (hv0 y) hy 2) (den_nonneg x y)
  have hi : Integrable (fun y => v y ^ 2 / (4 * Real.pi * ‖x - y‖)) := by
    refine (hx x).1.mono' (integrand_aem hv x) ?_
    filter_upwards [hpt] with y hy
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_two_nonneg _) (den_nonneg x y))]
    exact hy
  refine ⟨hi, ?_⟩
  calc (∫ y, v y ^ 2 / (4 * Real.pi * ‖x - y‖)) ≤ ∫ y, f y ^ 2 / (4 * Real.pi * ‖x - y‖) :=
        integral_mono_ae hi (hx x).1 hpt
    _ ≤ L ^ 2 := (hx x).2
    _ ≤ L' ^ 2 := pow_le_pow_left₀ hL hLL 2

theorem sq_split (a b s r : ℝ) (hs : 0 < s) (hr : 0 < r) :
    (a + b) ^ 2 ≤ (s + r) / s * a ^ 2 + (s + r) / r * b ^ 2 := by
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_div _ _ hs.ne' hr.ne', le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (r * a - s * b), mul_pos hs hr]

theorem kb_add {f g : Space → ℝ} {L M : ℝ} (hf : Kb f L) (hg : Kb g M) : Kb (fun y => f y + g y) (L + M) := by
  obtain ⟨hL, hf0, hfm, hfx⟩ := hf
  obtain ⟨hM, hg0, hgm, hgx⟩ := hg
  refine ⟨add_nonneg hL hM, fun y => add_nonneg (hf0 y) (hg0 y), hfm.add hgm, fun x => ?_⟩
  set w : Space → ℝ := fun y => 4 * Real.pi * ‖x - y‖ with hw
  have key : ∀ s r : ℝ, 0 < s → 0 < r →
      ∀ y, (f y + g y) ^ 2 / w y ≤ (s + r) / s * (f y ^ 2 / w y) + (s + r) / r * (g y ^ 2 / w y) := by
    intro s r hs hr y
    rw [mul_div_assoc', mul_div_assoc', ← add_div]
    exact div_le_div_of_nonneg_right (sq_split _ _ _ _ hs hr) (den_nonneg x y)
  have hi : Integrable (fun y => (f y + g y) ^ 2 / w y) := by
    refine (((hfx x).1.const_mul 2).add ((hgx x).1.const_mul 2)).mono' (integrand_aem (hfm.add hgm) x) ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (pow_two_nonneg _) (den_nonneg x y))]
    have := key 1 1 one_pos one_pos y
    norm_num at this
    exact this
  refine ⟨hi, ?_⟩
  have hbound : ∀ η : ℝ, 0 < η → (∫ y, (f y + g y) ^ 2 / w y) ≤ (L + M + 2 * η) * (L + M) := by
    intro η hη
    have hs : 0 < L + η := by linarith
    have hr : 0 < M + η := by linarith
    calc (∫ y, (f y + g y) ^ 2 / w y)
        ≤ ∫ y, ((L + η + (M + η)) / (L + η) * (f y ^ 2 / w y) + (L + η + (M + η)) / (M + η) * (g y ^ 2 / w y)) :=
          integral_mono hi (((hfx x).1.const_mul _).add ((hgx x).1.const_mul _)) (key _ _ hs hr)
      _ = (L + η + (M + η)) / (L + η) * (∫ y, f y ^ 2 / w y) + (L + η + (M + η)) / (M + η) * ∫ y, g y ^ 2 / w y := by
          rw [integral_add ((hfx x).1.const_mul _) ((hgx x).1.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ (L + η + (M + η)) / (L + η) * L ^ 2 + (L + η + (M + η)) / (M + η) * M ^ 2 := by
          gcongr
          · exact (hfx x).2
          · exact (hgx x).2
      _ ≤ (L + M + 2 * η) * (L + M) := by
          have h1 : L ^ 2 / (L + η) ≤ L := by rw [div_le_iff₀ hs]; nlinarith
          have h2 : M ^ 2 / (M + η) ≤ M := by rw [div_le_iff₀ hr]; nlinarith
          have e1 : (L + η + (M + η)) / (L + η) * L ^ 2 = (L + M + 2 * η) * (L ^ 2 / (L + η)) := by ring
          have e2 : (L + η + (M + η)) / (M + η) * M ^ 2 = (L + M + 2 * η) * (M ^ 2 / (M + η)) := by ring
          rw [e1, e2, ← mul_add]
          exact mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hpos : 0 < 2 * (L + M) + 1 := by linarith
  have := hbound (ε / (2 * (L + M) + 1)) (div_pos hε hpos)
  have h3 : 2 * (ε / (2 * (L + M) + 1)) * (L + M) ≤ ε := by
    rw [show 2 * (ε / (2 * (L + M) + 1)) * (L + M) = ε * (2 * (L + M) / (2 * (L + M) + 1)) by ring]
    exact mul_le_of_le_one_right hε.le ((div_le_one hpos).2 (by linarith))
  nlinarith

theorem kb_sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ) (L : ι → ℝ) (h : ∀ i ∈ s, Kb (f i) (L i)) :
    Kb (fun y => ∑ i ∈ s, f i y) (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using kb_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact kb_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem kernelBound_of_kb {f : Space → ℝ} {L K : ℝ} (h : Kb f L) (hm : Measurable f) (hK : L ≤ K) :
    KernelBound (fun y => f y ^ 2) (K ^ 2) := by
  obtain ⟨hL, h0, _, hx⟩ := h
  refine ⟨fun y => pow_two_nonneg _, hm.pow_const 2, fun x => ⟨(hx x).1, (hx x).2.trans (pow_le_pow_left₀ hL hK 2)⟩⟩

theorem kb_of_sq (f : Space → ℝ) {L : ℝ} (h : KernelBound (fun y => f y ^ 2) (L ^ 2)) (hL : 0 ≤ L)
    (h0 : ∀ y, 0 ≤ f y) (hm : Measurable f) : Kb f L :=
  ⟨hL, h0, hm.aemeasurable, h.2.2⟩


theorem ofReal_setIntegral_le (g : ℝ → ℝ) (s : Set ℝ) (hg : ∀ u ∈ s, 0 ≤ g u) (hs : MeasurableSet s) :
    ENNReal.ofReal (∫ u in s, g u) ≤ ∫⁻ u in s, ENNReal.ofReal (g u) := by
  by_cases hi : IntegrableOn g s
  · rw [ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall hg))]
  · rw [integral_undef hi, ENNReal.ofReal_zero]
    exact bot_le

theorem lower_integral_id : ∫⁻ u in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal u = ENNReal.ofReal (1 / 2) := by
  have hi : IntegrableOn (fun u : ℝ => u) (Set.Ioc 0 1) :=
    (continuous_id.integrableOn_Icc (a := (0:ℝ)) (b := 1)).mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hi ((ae_restrict_iff' measurableSet_Ioc).2
    (Filter.Eventually.of_forall fun u hu => le_of_lt hu.1))]
  congr 1
  rw [← intervalIntegral.integral_of_le zero_le_one, integral_id]
  norm_num

theorem kb_remainder (a : ℝ → Space → ℝ) (β0 δ L : ℝ) (hL0 : 0 ≤ L)
    (hK : ∀ t, |t - β0| ≤ |δ| → KernelBound (fun y => a t y ^ 2) (L ^ 2))
    (hjoint : AEMeasurable (fun q : Space × ℝ => a (β0 + q.2 * δ) q.1) (volume.prod volume))
    (R : Space → ℝ) (hR0 : ∀ y, 0 ≤ R y) (hRm : AEMeasurable R volume)
    (hR : ∀ᵐ y ∂volume, R y ^ 2 ≤ δ ^ 4 / 2 * ∫ u in Set.Ioc (0 : ℝ) 1, u * a (β0 + u * δ) y ^ 2) :
    Kb R (δ ^ 2 / 2 * L) := by
  refine ⟨by positivity, hR0, hRm, fun x => ?_⟩
  set d : Space → ℝ := fun y => 4 * Real.pi * ‖x - y‖ with hd
  set F : Space → ℝ → ENNReal := fun y u => ENNReal.ofReal (u * a (β0 + u * δ) y ^ 2 / d y) with hF
  have hjr : AEMeasurable (fun q : Space × ℝ => a (β0 + q.2 * δ) q.1)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Set.Ioc 0 1))) := by
    have e : ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Set.Ioc 0 1))) =
        ((volume : Measure Space).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioc 0 1) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    exact hjoint.restrict
  have hFm : AEMeasurable (Function.uncurry F)
      ((volume : Measure Space).prod ((volume : Measure ℝ).restrict (Set.Ioc 0 1))) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      ((measurable_snd.aemeasurable.mul (hjr.pow_const 2)).div ((den_meas x).comp measurable_fst).aemeasurable)
  have hstep1 : ∀ᵐ y ∂volume, ENNReal.ofReal (R y ^ 2 / d y) ≤
      ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ u in Set.Ioc (0 : ℝ) 1, F y u := by
    filter_upwards [hR] with y hy
    have hd0 : 0 ≤ d y := den_nonneg x y
    calc ENNReal.ofReal (R y ^ 2 / d y)
        ≤ ENNReal.ofReal (δ ^ 4 / 2 * ∫ u in Set.Ioc (0 : ℝ) 1, u * a (β0 + u * δ) y ^ 2 / d y) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [integral_div, ← mul_div_assoc]
          exact div_le_div_of_nonneg_right hy hd0
      _ = ENNReal.ofReal (δ ^ 4 / 2) * ENNReal.ofReal (∫ u in Set.Ioc (0 : ℝ) 1, u * a (β0 + u * δ) y ^ 2 / d y) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ u in Set.Ioc (0 : ℝ) 1, F y u := by
          gcongr
          exact ofReal_setIntegral_le _ _ (fun u hu => div_nonneg (mul_nonneg (le_of_lt hu.1)
            (pow_two_nonneg _)) hd0) measurableSet_Ioc
  have hstep3 : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∫⁻ y, F y u ≤ ENNReal.ofReal u * ENNReal.ofReal (L ^ 2) := by
    intro u hu
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have ht : |β0 + u * δ - β0| ≤ |δ| := by
      rw [add_sub_cancel_left, abs_mul, abs_of_nonneg hu0]
      exact mul_le_of_le_one_left (abs_nonneg _) hu.2
    obtain ⟨h0, _, hx⟩ := hK _ ht
    have e : ∀ y, F y u = ENNReal.ofReal u * ENNReal.ofReal (a (β0 + u * δ) y ^ 2 / d y) := by
      intro y
      show ENNReal.ofReal (u * a (β0 + u * δ) y ^ 2 / d y) = _
      rw [← ENNReal.ofReal_mul hu0, mul_div_assoc]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    gcongr
    rw [← ofReal_integral_eq_lintegral_ofReal (hx x).1 (Filter.Eventually.of_forall fun y =>
      div_nonneg (h0 y) (den_nonneg x y))]
    exact ENNReal.ofReal_le_ofReal (hx x).2
  have hlin : ∫⁻ y, ENNReal.ofReal (R y ^ 2 / d y) ≤ ENNReal.ofReal ((δ ^ 2 / 2 * L) ^ 2) := by
    calc ∫⁻ y, ENNReal.ofReal (R y ^ 2 / d y)
        ≤ ∫⁻ y, ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ u in Set.Ioc (0 : ℝ) 1, F y u := lintegral_mono_ae hstep1
      _ = ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ y, ∫⁻ u in Set.Ioc (0 : ℝ) 1, F y u :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ u in Set.Ioc (0 : ℝ) 1, ∫⁻ y, F y u := by
          rw [lintegral_lintegral_swap hFm]
      _ ≤ ENNReal.ofReal (δ ^ 4 / 2) * ∫⁻ u in Set.Ioc (0 : ℝ) 1, ENNReal.ofReal u * ENNReal.ofReal (L ^ 2) := by
          exact mul_le_mul_right (setLIntegral_mono' measurableSet_Ioc hstep3) _
      _ = ENNReal.ofReal (δ ^ 4 / 2) * (ENNReal.ofReal (1 / 2) * ENNReal.ofReal (L ^ 2)) := by
          rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lower_integral_id]
      _ = ENNReal.ofReal ((δ ^ 2 / 2 * L) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  have hnn : 0 ≤ᵐ[volume] fun y => R y ^ 2 / d y :=
    Filter.Eventually.of_forall fun y => div_nonneg (pow_two_nonneg _) (den_nonneg x y)
  have hi : Integrable (fun y => R y ^ 2 / d y) :=
    ⟨integrand_aem hRm x, (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hlin ENNReal.ofReal_lt_top)⟩
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn (integrand_aem hRm x)]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) hlin

theorem weighted_sq (A : ℝ → ℝ) (hA : Continuous A) :
    (∫ u in (0 : ℝ)..1, u * A u) ^ 2 ≤ 1 / 2 * ∫ u in (0 : ℝ)..1, u * A u ^ 2 := by
  set J := ∫ u in (0 : ℝ)..1, u * A u with hJ
  have h1 : IntervalIntegrable (fun u : ℝ => u * A u ^ 2) volume 0 1 := (continuous_id.mul (hA.pow 2)).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun u : ℝ => u * A u) volume 0 1 := (continuous_id.mul hA).intervalIntegrable _ _
  have h3 : IntervalIntegrable (fun u : ℝ => u) volume 0 1 := continuous_id.intervalIntegrable _ _
  have hpos : 0 ≤ ∫ u in (0 : ℝ)..1, u * (A u - 2 * J) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun u hu => mul_nonneg hu.1 (sq_nonneg _)
  have e : (fun u : ℝ => u * (A u - 2 * J) ^ 2) = fun u => (u * A u ^ 2 - (4 * J) * (u * A u)) + (4 * J ^ 2) * u := by
    funext u; ring
  rw [e, intervalIntegral.integral_add (h1.sub (h2.const_mul _)) (h3.const_mul _),
    intervalIntegral.integral_sub h1 (h2.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, integral_id, ← hJ] at hpos
  nlinarith

theorem remainder_sq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] (g : ℝ → E)
    (hg : ContDiff ℝ 2 g) (β0 δ : ℝ) :
    ‖g (β0 + δ) - δ • deriv g (β0 + δ) - g β0‖ ^ 2 ≤
      δ ^ 4 / 2 * ∫ u in Set.Ioc (0 : ℝ) 1, u * ‖deriv (deriv g) (β0 + u * δ)‖ ^ 2 := by
  have hg' : ContDiff ℝ (1 + 1) g := by rw [one_add_one_eq_two]; exact hg
  have h1 : ContDiff ℝ 1 (deriv g) := ((contDiff_succ_iff_deriv (n := 1)).1 hg').2.2
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hd : Differentiable ℝ (deriv g) := h1.differentiable (by norm_num)
  have hc2 : Continuous (deriv (deriv g)) := h1.continuous_deriv le_rfl
  set φ : ℝ → E := fun u => g (β0 + u * δ) - (u * δ) • deriv g (β0 + u * δ) with hφ
  set φ' : ℝ → E := fun u => -((u * δ ^ 2) • deriv (deriv g) (β0 + u * δ)) with hφ'
  have hder : ∀ u, HasDerivAt φ (φ' u) u := by
    intro u
    have ha : HasDerivAt (fun u : ℝ => β0 + u * δ) δ u := by
      simpa using ((hasDerivAt_id u).mul_const δ).const_add β0
    have hg1 : HasDerivAt (fun u => g (β0 + u * δ)) (δ • deriv g (β0 + u * δ)) u :=
      (hgd (β0 + u * δ)).hasDerivAt.scomp u ha
    have hg2 : HasDerivAt ((deriv g) ∘ (fun u : ℝ => β0 + u * δ)) (δ • deriv (deriv g) (β0 + u * δ)) u :=
      HasDerivAt.scomp u (hd (β0 + u * δ)).hasDerivAt ha
    have hm : HasDerivAt (fun u : ℝ => u * δ) δ u := by simpa using (hasDerivAt_id u).mul_const δ
    have hp := hm.smul hg2
    refine (hg1.sub hp).congr_deriv ?_
    simp only [hφ', Function.comp_apply]
    module
  have hcont' : Continuous φ' := by
    refine Continuous.neg (Continuous.smul (by fun_prop) (hc2.comp (by fun_prop)))
  have hftc : ∫ u in (0 : ℝ)..1, φ' u = φ 1 - φ 0 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hder u) (hcont'.intervalIntegrable _ _)
  have hval : φ 1 - φ 0 = g (β0 + δ) - δ • deriv g (β0 + δ) - g β0 := by
    simp [hφ]
  set A : ℝ → ℝ := fun u => ‖deriv (deriv g) (β0 + u * δ)‖ with hA
  have hAc : Continuous A := (hc2.comp (by fun_prop)).norm
  have hnorm : ‖g (β0 + δ) - δ • deriv g (β0 + δ) - g β0‖ ≤ δ ^ 2 * ∫ u in (0 : ℝ)..1, u * A u := by
    rw [← hval, ← hftc]
    refine (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans (le_of_eq ?_)
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun u hu => ?_
    have hu0 : 0 ≤ u := by
      rw [Set.uIcc_of_le zero_le_one] at hu
      exact hu.1
    simp only [hφ', hA, norm_neg, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity : 0 ≤ u * δ ^ 2)]
    ring
  have hJ0 : 0 ≤ ∫ u in (0 : ℝ)..1, u * A u :=
    intervalIntegral.integral_nonneg zero_le_one fun u hu => mul_nonneg hu.1 (norm_nonneg _)
  have hcs := weighted_sq A hAc
  rw [← intervalIntegral.integral_of_le zero_le_one]
  calc ‖g (β0 + δ) - δ • deriv g (β0 + δ) - g β0‖ ^ 2 ≤ (δ ^ 2 * ∫ u in (0 : ℝ)..1, u * A u) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = δ ^ 4 * (∫ u in (0 : ℝ)..1, u * A u) ^ 2 := by ring
    _ ≤ δ ^ 4 * (1 / 2 * ∫ u in (0 : ℝ)..1, u * A u ^ 2) := mul_le_mul_of_nonneg_left hcs (by positivity)
    _ = δ ^ 4 / 2 * ∫ u in (0 : ℝ)..1, u * ‖deriv (deriv g) (β0 + u * δ)‖ ^ 2 := by ring

open SteadyCert Assembly GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula


theorem index_split {k : ℕ} {E : Type*} [AddCommGroup E] [Module ℝ E] (D : ProfileData k)
    (hzero : (0 : Fin k → ℕ) ∈ D.index) (hamp : ∀ i, Pi.single i 1 ∈ D.index) (p : Fin k → ℝ)
    (w : (Fin k → ℕ) → E) :
    ∑ μ ∈ D.index, ProfileData.monomialOf p μ • w μ =
      w 0 + ∑ i, p i • w (Pi.single i 1) +
        ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf p μ • w μ := by
  classical
  have hlow : D.index.filter (fun μ => ¬ 2 ≤ ∑ i, μ i) =
      insert (0 : Fin k → ℕ) (Finset.univ.image (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ))) := by
    ext μ
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_image, Finset.mem_univ, true_and, not_le]
    constructor
    · rintro ⟨_, hlt⟩
      by_cases h0 : ∑ i, μ i = 0
      · left
        funext j
        exact (Finset.sum_eq_zero_iff.1 h0) j (Finset.mem_univ j)
      · right
        have h1 : ∑ i, μ i = 1 := by omega
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra hc
          push Not at hc
          simp [hc] at h1
        have hle : μ i ≤ 1 := h1 ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        refine ⟨i, funext fun j => ?_⟩
        by_cases hj : j = i
        · subst hj
          rw [Pi.single_eq_same]
          omega
        · have hsum := Finset.add_sum_erase Finset.univ μ (Finset.mem_univ i)
          rw [h1] at hsum
          have h0' : ∑ x ∈ Finset.univ.erase i, μ x = 0 := by omega
          have := (Finset.sum_eq_zero_iff.1 h0') j (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
          rw [Pi.single_eq_of_ne hj, this]
    · rintro (h | ⟨i, rfl⟩)
      · subst h
        exact ⟨hzero, by simp⟩
      · exact ⟨hamp i, by simp [Finset.sum_pi_single']⟩
  have hnot : (0 : Fin k → ℕ) ∉ Finset.univ.image (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ)) := by
    simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
    intro i h
    have := congrFun h i
    simp at this
  have hinj : Set.InjOn (fun i : Fin k => (Pi.single i 1 : Fin k → ℕ)) (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ h
    by_contra hij
    have := congrFun h i
    simp [Pi.single_apply, hij] at this
  have hmono1 : ∀ i, ProfileData.monomialOf p (Pi.single i 1) = p i := by
    intro i
    unfold ProfileData.monomialOf
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · simp
  have hmono0 : ProfileData.monomialOf p (0 : Fin k → ℕ) = 1 := by simp [ProfileData.monomialOf]
  rw [← Finset.sum_filter_add_sum_filter_not D.index (fun μ => 2 ≤ ∑ i, μ i), hlow, Finset.sum_insert hnot,
    Finset.sum_image hinj]
  simp only [hmono1, hmono0, one_smul]
  abel

theorem monomial_zero_filter {k : ℕ} (μ : Fin k → ℕ) (hμ : 2 ≤ ∑ i, μ i) :
    ProfileData.monomialOf (0 : Fin k → ℝ) μ = 0 := by
  obtain ⟨j, hj⟩ : ∃ j, μ j ≠ 0 := by
    by_contra hc
    push Not at hc
    simp [hc] at hμ
  exact Finset.prod_eq_zero (Finset.mem_univ j) (by simp [zero_pow hj])

theorem hbase {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X)
    (hWamp : ∀ i β, IsSumWeight c.order (gradSq (ampField D X.splitStep i β)))
    (hWhi : ∀ μ ∈ D.index, 2 ≤ ∑ i, μ i → ∀ β, IsSumWeight c.order (gradSq (fieldOf D.chart (D.part μ) β)))
    (hWcurv : ∀ β, IsSumWeight c.order (gradSq (phaseCurvField D.chart (D.part 0) β))) :
    ∀ p ∈ box c.radius, KernelBound (fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2) (X.centreKernel ^ 2) := by
  intro p hp
  have hL := h.losses
  have hP : IsChartParams D.chart := h.given.profile.chart
  have hzero : (0 : Fin k → ℕ) ∈ D.index := h.given.profile.index_zero
  have hrad : ∀ i, |p i| ≤ c.radius i := hp
  have hrad0 : ∀ i, 0 ≤ c.radius i := fun i => (abs_nonneg _).trans (hrad i)
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = ∑ i, X.splitStep i * p i := ⟨_, rfl⟩
  have hphase : D.phase p = D.phase 0 + δ := by
    simp only [hδ, ProfileData.phase, ProfileData.rate, hL.split_step, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, add_zero]
    rw [mul_add, Finset.mul_sum, neg_add, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hδw : |δ| ≤ splitWidth c.radius X.splitStep := by
    rw [hδ]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hrad i) (abs_nonneg _)
  have hδr : |δ| ≤ X.splitRange := hδw.trans hL.split_width
  have hβr : |D.phase p - D.phase 0| ≤ X.splitRange := by rw [hphase, add_sub_cancel_left]; exact hδr
  obtain ⟨hk1, hk2, hk3⟩ := hL.split_kernels_nonneg
  have hKamp : ∀ i, KernelBound (gradSq (ampField D X.splitStep i (D.phase p))) (X.ampKernel i ^ 2) := fun i =>
    kernelBound_of_cellSums c.order _ _ (cellSumData_of c.order _ _ (hL.amp_values i) (hL.amp_le_bound i _ hβr)
      (hWamp i _)) _ (hL.amp_boxes i)
  have hKhi : ∀ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i),
      KernelBound (gradSq (fieldOf D.chart (D.part μ) (D.phase p))) (X.higherKernel μ ^ 2) := by
    intro μ hμ
    rw [Finset.mem_filter] at hμ
    exact kernelBound_of_cellSums c.order _ _ (cellSumData_of c.order _ _ (hL.higher_values μ hμ.1 hμ.2)
      (hL.higher_bounded μ hμ.1 hμ.2 _ hβr) (hWhi μ hμ.1 hμ.2 _)) _ (hL.higher_boxes μ hμ.1 hμ.2)
  have hKcurv : ∀ t, |t - D.phase 0| ≤ |δ| →
      KernelBound (gradSq (phaseCurvField D.chart (D.part 0) t)) (X.curvKernel ^ 2) := fun t ht =>
    kernelBound_of_cellSums c.order _ _ (cellSumData_of c.order _ _ hL.curv_values (hL.curv_bounded t (ht.trans hδr))
      (hWcurv t)) _ hL.curv_boxes
  have hΔ : (fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2) =
      fun y => ‖fderiv ℝ (D.profile p) y - fderiv ℝ (D.profile 0) y‖ ^ 2 := by
    funext y
    show ‖fderiv ℝ (c.toFracCertData.profile p) y - fderiv ℝ c.centre y‖ ^ 2 = _
    rw [h.given.profile_instance.profile_eq, h.given.centre_instance.centre_eq]
  rw [hΔ]
  set F : (Fin k → ℕ) → ℝ × Space → Space := fun μ q => fieldOf D.chart (D.part μ) q.1 q.2 with hFdef
  have hS : ∀ tb xb : List ℝ, ∀ᵐ y ∂(volume : Measure Space), chartT D.chart y ∉ tb ∧ |heightRatio y| ∉ xb :=
    fun tb xb => (FracInternal.ae_generic D.chart hP.L0_pos tb xb).mono fun y hy => ⟨hy.2.2.2.1, hy.2.2.2.2⟩
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ μ ∈ D.index, ∀ n ∈ (D.part μ).modes,
      ∀ S ∈ [((D.part μ).amp n).radialAmp, ((D.part μ).amp n).polarAmp, ((D.part μ).amp n).streamAmp,
        ((D.part μ).amp n).swirlAmp], chartT D.chart y ∉ S.mesh.tBreaks ∧ |heightRatio y| ∉ S.mesh.xBreaks := by
    rw [Filter.eventually_all_finset]
    intro μ _
    rw [Filter.eventually_all_finset]
    intro n _
    filter_upwards [hS ((D.part μ).amp n).radialAmp.mesh.tBreaks ((D.part μ).amp n).radialAmp.mesh.xBreaks,
      hS ((D.part μ).amp n).polarAmp.mesh.tBreaks ((D.part μ).amp n).polarAmp.mesh.xBreaks,
      hS ((D.part μ).amp n).streamAmp.mesh.tBreaks ((D.part μ).amp n).streamAmp.mesh.xBreaks,
      hS ((D.part μ).amp n).swirlAmp.mesh.tBreaks ((D.part μ).amp n).swirlAmp.mesh.xBreaks] with y h1 h2 h3 h4
    intro S hS'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hS'
    rcases hS' with rfl | rfl | rfl | rfl <;> assumption
  have hgen : ∀ᵐ y ∂(volume : Measure Space), ∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ) := by
    filter_upwards [FracInternal.ae_generic D.chart hP.L0_pos [] [], hall] with y h0 hg
    intro μ hμ b
    have hy0 : y ≠ 0 := fun h => h0.2.1 (by simp [h])
    have hx0 : heightRatio y ≠ 0 := div_ne_zero h0.2.2.1 (norm_ne_zero_iff.2 hy0)
    exact (FracInternal.FieldJoint.joint_fieldOf D.chart hP (D.part μ) hy0 h0.2.1 hx0 (hg μ hμ) b).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hU : ∀ μ, IsOpen (goodSet (F μ)) := fun μ => goodSet_open
  have hF5 : ∀ μ, ContDiffOn ℝ ((4 : ℕ) + 1) (F μ) (goodSet (F μ)) := fun μ => good_smooth 4 (by norm_num)
  have hF32 : ContDiffOn ℝ ((3 : ℕ) + 2) (F 0) (goodSet (F 0)) := by exact_mod_cast hF5 0
  have hB4 : ContDiffOn ℝ (4 : ℕ) (partB (F 0)) (goodSet (F 0)) := partB_smooth (hF5 0) (hU 0)
  have hB22 : ContDiffOn ℝ ((2 : ℕ) + 2) (partB (F 0)) (goodSet (F 0)) := by exact_mod_cast hB4
  have hB31 : ContDiffOn ℝ ((3 : ℕ) + 1) (partB (F 0)) (goodSet (F 0)) := by exact_mod_cast hB4
  have hBB : ContDiffOn ℝ (3 : ℕ) (partB (partB (F 0))) (goodSet (F 0)) := partB_smooth hB31 (hU 0)
  have hBB21 : ContDiffOn ℝ ((2 : ℕ) + 1) (partB (partB (F 0))) (goodSet (F 0)) := by exact_mod_cast hBB
  have hYBB : ContDiffOn ℝ (2 : ℕ) (partY (partB (partB (F 0)))) (goodSet (F 0)) := partY_smooth hBB21 (hU 0)
  have hY4 : ContDiffOn ℝ (4 : ℕ) (partY (F 0)) (goodSet (F 0)) := partY_smooth (hF5 0) (hU 0)
  have hfd : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) → ∀ μ ∈ D.index, ∀ b : ℝ,
      DifferentiableAt ℝ (fieldOf D.chart (D.part μ) b) y :=
    fun y hy μ hμ b => slice_diff (good_diff (hy μ hμ b))
  have hI1 : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) → ∀ q : Fin k → ℝ,
      fderiv ℝ (D.profile q) y =
        ∑ μ ∈ D.index, ProfileData.monomialOf q μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase q)) y := by
    intro y hy q
    show fderiv ℝ (fun y' => ∑ μ ∈ D.index, ProfileData.monomialOf q μ • fieldOf D.chart (D.part μ) (D.phase q) y') y = _
    exact (HasFDerivAt.fun_sum fun μ hμ => (hfd y hy μ hμ _).hasFDerivAt.const_smul (ProfileData.monomialOf q μ)).fderiv
  have hI3 : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) → ∀ i,
      fderiv ℝ (ampField D X.splitStep i (D.phase p)) y =
        fderiv ℝ (fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p)) y +
          X.splitStep i • deriv (fun b => partY (F 0) (b, y)) (D.phase p) := by
    intro y hy i
    have hPd : DifferentiableAt ℝ (fun y' => partB (F 0) (D.phase p, y')) y :=
      slice_diff (diff_of hB31 (hU 0) (hy 0 hzero _))
    show fderiv ℝ (fun y' => fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p) y' +
      X.splitStep i • partB (F 0) (D.phase p, y')) y = _
    refine (((hfd y hy _ (hL.amp_index i) (D.phase p)).hasFDerivAt.add
      (hPd.hasFDerivAt.const_smul (X.splitStep i))).fderiv).trans ?_
    congr 2
    exact partYB_comm hF32 (hU 0) (hy 0 hzero _)
  have hI4 : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) → ∀ t,
      fderiv ℝ (phaseCurvField D.chart (D.part 0) t) y = deriv (deriv (fun b => partY (F 0) (b, y))) t := by
    intro y hy t
    show partY (partB (partB (F 0))) (t, y) = _
    rw [partYB_comm hB22 (hU 0) (hy 0 hzero t)]
    show deriv (fun b => partY (partB (F 0)) (b, y)) t = _
    congr 1
    funext b
    exact partYB_comm hF32 (hU 0) (hy 0 hzero b)
  have hI5 : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) →
      ContDiff ℝ 2 (fun b => partY (F 0) (b, y)) := by
    intro y hy
    have := hY4.comp_contDiff (contDiff_id.prodMk contDiff_const) (fun b => hy 0 hzero b)
    exact this.of_le (by norm_num)
  set Amp : Fin k → Space → (Space →L[ℝ] Space) := fun i y => fderiv ℝ (ampField D X.splitStep i (D.phase p)) y
    with hAmp
  set Hi : (Fin k → ℕ) → Space → (Space →L[ℝ] Space) := fun μ y => fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) y
    with hHi
  set Δ : Space → (Space →L[ℝ] Space) := fun y => fderiv ℝ (D.profile p) y - fderiv ℝ (D.profile 0) y with hΔdef
  set Rv : Space → (Space →L[ℝ] Space) := fun y => Δ y - ∑ i, p i • Amp i y -
    ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf p μ • Hi μ y with hRv
  have hRgen : ∀ y, (∀ μ ∈ D.index, ∀ b : ℝ, (b, y) ∈ goodSet (F μ)) →
      Rv y = fderiv ℝ (fieldOf D.chart (D.part 0) (D.phase p)) y - δ • deriv (fun b => partY (F 0) (b, y)) (D.phase p) -
        fderiv ℝ (fieldOf D.chart (D.part 0) (D.phase 0)) y := by
    intro y hy
    have e1 := hI1 y hy p
    have e0 := hI1 y hy 0
    rw [index_split D hzero hL.amp_index p] at e1
    rw [index_split D hzero hL.amp_index 0] at e0
    have hz1 : ∑ i, (0 : Fin k → ℝ) i • fderiv ℝ (fieldOf D.chart (D.part (Pi.single i 1)) (D.phase 0)) y = 0 := by
      simp
    have hz2 : ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf (0 : Fin k → ℝ) μ •
        fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase 0)) y = 0 :=
      Finset.sum_eq_zero fun μ hμ => by rw [monomial_zero_filter μ (Finset.mem_filter.1 hμ).2, zero_smul]
    rw [hz1, hz2] at e0
    have hamp_sum : ∑ i, p i • Amp i y = ∑ i, p i • fderiv ℝ (fieldOf D.chart (D.part (Pi.single i 1)) (D.phase p)) y +
        δ • deriv (fun b => partY (F 0) (b, y)) (D.phase p) := by
      simp only [hAmp, hI3 y hy, smul_add, Finset.sum_add_distrib, smul_smul, hδ, Finset.sum_smul]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]
    simp only [hRv, hΔdef, hamp_sum, e1, e0, hHi]
    abel
  have hmeasD : Measurable Δ := (measurable_fderiv ℝ _).sub (measurable_fderiv ℝ _)
  have hmeasAmp : ∀ i, Measurable (Amp i) := fun i => measurable_fderiv ℝ _
  have hmeasHi : ∀ μ, Measurable (Hi μ) := fun μ => measurable_fderiv ℝ _
  have hmeasR : Measurable Rv := (hmeasD.sub (Finset.measurable_sum _ fun i _ =>
      ((hmeasAmp i).const_smul (p i) : Measurable fun y => p i • Amp i y))).sub
      (Finset.measurable_sum _ fun μ _ =>
        ((hmeasHi μ).const_smul (ProfileData.monomialOf p μ) : Measurable fun y => ProfileData.monomialOf p μ • Hi μ y))
  set r : Space → ℝ := fun y => ‖Rv y‖ with hr
  set aC : ℝ → Space → ℝ := fun t y => ‖fderiv ℝ (phaseCurvField D.chart (D.part 0) t) y‖ with haC
  have hjoint : AEMeasurable (fun q : Space × ℝ => aC (D.phase 0 + q.2 * δ) q.1) (volume.prod volume) := by
    have hΦ : Continuous (fun q : Space × ℝ => (D.phase 0 + q.2 * δ, q.1)) := by fun_prop
    have hSo : IsOpen ((fun q : Space × ℝ => (D.phase 0 + q.2 * δ, q.1)) ⁻¹' goodSet (F 0)) := (hU 0).preimage hΦ
    have hc : ContinuousOn (fun q : Space × ℝ => ‖partY (partB (partB (F 0))) (D.phase 0 + q.2 * δ, q.1)‖)
        ((fun q : Space × ℝ => (D.phase 0 + q.2 * δ, q.1)) ⁻¹' goodSet (F 0)) :=
      (hYBB.continuousOn.comp hΦ.continuousOn fun q hq => hq).norm
    have hae : ∀ᵐ q ∂((volume : Measure Space).prod (volume : Measure ℝ)),
        q ∈ (fun q : Space × ℝ => (D.phase 0 + q.2 * δ, q.1)) ⁻¹' goodSet (F 0) :=
      (Measure.quasiMeasurePreserving_fst.ae hgen).mono fun q hq => hq 0 hzero _
    have := hc.aemeasurable hSo.measurableSet (μ := (volume : Measure Space).prod (volume : Measure ℝ))
    rw [Measure.restrict_eq_self_of_ae_mem hae] at this
    exact this
  have kbR : Kb r (δ ^ 2 / 2 * X.curvKernel) := by
    refine kb_remainder aC (D.phase 0) δ X.curvKernel hk3 (fun t ht => hKcurv t ht) hjoint r
      (fun y => norm_nonneg _) hmeasR.norm.aemeasurable ?_
    filter_upwards [hgen] with y hy
    have hT := remainder_sq (fun b => partY (F 0) (b, y)) (hI5 y hy) (D.phase 0) δ
    rw [← hphase] at hT
    have hcv : ∀ u : ℝ, aC (D.phase 0 + u * δ) y =
        ‖deriv (deriv (fun b => partY (F 0) (b, y))) (D.phase 0 + u * δ)‖ :=
      fun u => by simp only [haC]; rw [hI4 y hy]
    simp only [hcv, hr]
    rw [hRgen y hy]
    exact hT
  have kbA : ∀ i, Kb (fun y => ‖Amp i y‖) (X.ampKernel i) := fun i =>
    kb_of_sq (fun y => ‖Amp i y‖) (hKamp i) (hk1 i) (fun _ => norm_nonneg _) (hmeasAmp i).norm
  have kbH : ∀ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), Kb (fun y => ‖Hi μ y‖) (X.higherKernel μ) :=
    fun μ hμ => kb_of_sq (fun y => ‖Hi μ y‖) (hKhi μ hμ) (hk2 μ) (fun _ => norm_nonneg _) (hmeasHi μ).norm
  have kbAll := kb_add (kb_add (kb_sum Finset.univ (fun i y => c.radius i * ‖Amp i y‖)
      (fun i => c.radius i * X.ampKernel i) fun i _ => kb_smul (kbA i) (hrad0 i))
    (kb_sum (D.index.filter (fun μ => 2 ≤ ∑ i, μ i)) (fun μ y => (∏ i, c.radius i ^ μ i) * ‖Hi μ y‖)
      (fun μ => (∏ i, c.radius i ^ μ i) * X.higherKernel μ)
      fun μ hμ => kb_smul (kbH μ hμ) (Finset.prod_nonneg fun i _ => pow_nonneg (hrad0 i) _))) kbR
  have hle : ∑ i, c.radius i * X.ampKernel i +
      ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, c.radius i ^ μ i) * X.higherKernel μ +
      δ ^ 2 / 2 * X.curvKernel ≤ X.centreKernel := by
    have hsq : δ ^ 2 ≤ splitWidth c.radius X.splitStep ^ 2 := sq_le_sq' (abs_le.1 hδw).1 (abs_le.1 hδw).2
    have := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hsq (by norm_num : (0:ℝ) ≤ 2)) hk3
    linarith [hL.centreKernel_ge]
  have hpt : ∀ y, ‖Δ y‖ ≤ ∑ i, c.radius i * ‖Amp i y‖ +
      ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), (∏ i, c.radius i ^ μ i) * ‖Hi μ y‖ + r y := by
    intro y
    have e : Δ y = ∑ i, p i • Amp i y +
        ∑ μ ∈ D.index.filter (fun μ => 2 ≤ ∑ i, μ i), ProfileData.monomialOf p μ • Hi μ y + Rv y := by
      simp only [hRv]
      abel
    rw [e]
    refine norm_add₃_le.trans (add_le_add (add_le_add ?_ ?_) le_rfl)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hrad i) (norm_nonneg _)
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun μ _ => ?_)
      rw [norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      unfold ProfileData.monomialOf
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) fun i _ => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hrad i) _
  have kbD : Kb (fun y => ‖Δ y‖) X.centreKernel :=
    kb_mono kbAll hmeasD.norm.aemeasurable (fun _ => norm_nonneg _) (Filter.Eventually.of_forall hpt) hle
  exact kernelBound_of_kb kbD hmeasD.norm le_rfl

end Breakdown.CellCert.CellSystem.CentreKernel.Internal

namespace Breakdown.CellCert.CellSystem

open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula
open _root_.Breakdown.CellCert.Finite

theorem centreKernelSplit_of {k N : ℕ} (c : FracCellData k N) (D : ProfileData k) (A : AuxData k)
    (M : CellMesh) (MD : ModelData M k) (RD : RowData M N) (X : CellSystemData k N M)
    (h : CellSystemCondition c D A M MD RD X) :
    ∀ p ∈ box c.radius, KernelBound (fun y => ‖c.gradProfile p y - c.centreGrad y‖ ^ 2) (X.centreKernel ^ 2) := by
  obtain ⟨-, -, hWamp, hWhi, hWcurv, -⟩ :=
    sumWeights_of c D A M MD RD h.given 1 one_pos X.splitStep h.losses.amp_index
  exact CentreKernel.Internal.hbase c D A M MD RD X h hWamp hWhi hWcurv

end Breakdown.CellCert.CellSystem

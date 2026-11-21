import Breakdown.FracCert.GradientOrthogonalParts
import Breakdown.FracCert.SecondTraceSolenoidal
import Breakdown.FracCell.Defs
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace CentrePairingActuatorInternal

open SteadyCert SteadyCert.GradientOrthogonalInternal

def lift (u : Space → ℝ) : Space → Space := fun x => u x • unitVector 0

theorem lift_inner (u w : Space → ℝ) (x z : Space) : inner ℝ (lift u x) (lift w z) = u x * w z := by
  simp [lift, inner_smul_left, inner_smul_right, unitVector]
  ring

theorem memLp_lift {u : Space → ℝ} (hu : MemLp u 2 volume) : MemLp (lift u) 2 volume :=
  (ContinuousLinearMap.toSpanSingleton ℝ (unitVector 0)).comp_memLp' hu

theorem lift_shift_int (φ u : Space → ℝ) (x : Space) :
    ∫ y, φ y • lift u (x + y) = (∫ y, φ y * u (x + y)) • unitVector 0 := by
  simp only [lift, smul_smul]
  exact integral_smul_const _ _

theorem exch {ζ u : Space → ℝ} (hζ : MemLp ζ 2 volume) (hu : MemLp u 2 volume) {φ : Space → ℝ}
    (hφ : IsTestScalar φ) :
    ∫ y, φ y * pairShift (lift ζ) (lift u) y = ∫ x, ζ x * ∫ y, φ y * u (x + y) := by
  rw [exchange_pair (memLp_lift hζ) (memLp_lift hu) φ hφ.1.continuous hφ.2]
  congr 1
  funext x
  rw [lift_shift_int]
  simp [lift, inner_smul_left, inner_smul_right, unitVector]
  ring

theorem shift_test {φ : Space → ℝ} (hφ : IsTestScalar φ) (x : Space) :
    IsTestScalar (fun z => φ (z - x)) ∧ ∀ z w, fderiv ℝ (fun z => φ (z - x)) z w = fderiv ℝ φ (z - x) w := by
  refine ⟨⟨hφ.1.comp (contDiff_id.sub contDiff_const), hφ.2.comp_homeomorph (Homeomorph.subRight x)⟩, ?_⟩
  intro z w
  have hd : DifferentiableAt ℝ φ (z - x) := (hφ.1.differentiable (by simp)).differentiableAt
  have : HasFDerivAt (fun z => φ (z - x)) ((fderiv ℝ φ (z - x)).comp (ContinuousLinearMap.id ℝ Space - 0)) z :=
    hd.hasFDerivAt.comp z ((hasFDerivAt_id z).sub (hasFDerivAt_const x z))
  rw [this.fderiv]
  simp

theorem bound_zero {φ : Space → ℝ} (hφ : HasCompactSupport φ) : ∃ r : ℝ, ∀ y, r < ‖y‖ → φ y = 0 := by
  obtain ⟨r, hr⟩ := hφ.isBounded.subset_closedBall (0 : Space)
  refine ⟨r, fun y hy => image_eq_zero_of_notMem_tsupport fun hm => ?_⟩
  have := hr hm
  rw [Metric.mem_closedBall, dist_zero_right] at this
  linarith

theorem shift_support {φ a : Space → ℝ} (hφ : HasCompactSupport φ) {R : ℝ} (hR : ∀ y, R < ‖y‖ → a y = 0) :
    HasCompactSupport (fun x => ∫ y, φ y * a (x + y)) := by
  obtain ⟨r, hr⟩ := bound_zero hφ
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (R + r)) fun x hx => ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
  have h0 : ∀ y, φ y * a (x + y) = 0 := by
    intro y
    by_cases hy : r < ‖y‖
    · rw [hr y hy, zero_mul]
    · have h1 := norm_sub_norm_le x (-y)
      rw [norm_neg, sub_neg_eq_add] at h1
      rw [hR (x + y) (by linarith [not_lt.1 hy]), mul_zero]
  simp only [h0, integral_zero]

theorem parts_scalar {a f h g : Space → ℝ} (ha : MemLp a 2 volume) (hf : MemLp f 2 volume)
    (hh : MemLp h 2 volume) (hg : MemLp g 2 volume) {R : ℝ} (hR : ∀ y, R < ‖y‖ → a y = 0) (j : Fin 3)
    (hag : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * a y = -∫ y, ψ y * g y)
    (hfh : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * f y = -∫ y, ψ y * h y) :
    ∫ y, h y * a y = -∫ y, f y * g y := by
  set P : Space → ℝ := fun y => pairShift (lift h) (lift a) y + pairShift (lift f) (lift g) y with hP
  have hc1 := continuous_pairShift (memLp_lift hh) (memLp_lift ha)
  have hc2 := continuous_pairShift (memLp_lift hf) (memLp_lift hg)
  have hPc : Continuous P := hc1.add hc2
  have hint : ∀ φ : Space → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → ∫ y, φ y • P y = 0 := by
    intro φ hφs hφc
    have hφ : IsTestScalar φ := ⟨hφs, hφc⟩
    set A : Space → ℝ := fun x => ∫ y, φ y * a (x + y) with hA
    set B : Space → ℝ := fun x => ∫ y, φ y * g (x + y) with hB
    obtain ⟨hAs, hAd⟩ := deriv_shift φ hφ a ha
    have hAB : ∀ x, fderiv ℝ A x (unitVector j) = B x := by
      intro x
      rw [hAd x j]
      obtain ⟨hψ, hψd⟩ := shift_test hφ x
      have e := hag _ hψ
      simp only [hψd] at e
      have t1 := integral_add_left_eq_self (μ := volume)
        (fun z => fderiv ℝ φ (z - x) (unitVector j) * a z) x
      have t2 := integral_add_left_eq_self (μ := volume) (fun z => φ (z - x) * g z) x
      simp only [add_sub_cancel_left] at t1 t2
      rw [t1, e, ← t2, neg_neg]
    have hAt : IsTestScalar A := ⟨hAs, shift_support hφc hR⟩
    have e2 := hfh A hAt
    simp only [hAB] at e2
    have i1 : Integrable (fun y => φ y * pairShift (lift h) (lift a) y) :=
      (hφs.continuous.mul hc1).integrable_of_hasCompactSupport (hφc.mul_right)
    have i2 : Integrable (fun y => φ y * pairShift (lift f) (lift g) y) :=
      (hφs.continuous.mul hc2).integrable_of_hasCompactSupport (hφc.mul_right)
    have s1 : ∫ y, φ y * pairShift (lift h) (lift a) y = ∫ x, h x * A x := exch hh ha hφ
    have s2 : ∫ y, φ y * pairShift (lift f) (lift g) y = ∫ x, f x * B x := exch hf hg hφ
    have c1 : ∫ x, h x * A x = ∫ y, A y * h y := by
      congr 1; funext x; ring
    have c2 : ∫ x, f x * B x = ∫ y, B y * f y := by
      congr 1; funext x; ring
    calc ∫ y, φ y • P y
        = ∫ y, (φ y * pairShift (lift h) (lift a) y + φ y * pairShift (lift f) (lift g) y) := by
          congr 1; funext y; simp only [hP, smul_eq_mul, mul_add]
      _ = (∫ y, φ y * pairShift (lift h) (lift a) y) + ∫ y, φ y * pairShift (lift f) (lift g) y :=
          integral_add i1 i2
      _ = (∫ y, A y * h y) + ∫ y, B y * f y := by rw [s1, s2, c1, c2]
      _ = 0 := by rw [e2]; ring
  have hae : ∀ᵐ y ∂volume, P y = 0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero hPc.locallyIntegrable hint
  have h0 : P = fun _ => 0 := (Continuous.ae_eq_iff_eq volume hPc continuous_const).1 hae
  have := congrFun h0 0
  simp only [hP, pairShift, lift_inner, add_zero] at this
  linarith



theorem unit_norm' (j : Fin 3) : ‖unitVector j‖ = 1 := by simp [unitVector]

theorem memLp_mulb {φ a : Space → ℝ} (ha : MemLp a 2 volume) (hφ : Continuous φ) {M : ℝ}
    (hM : ∀ y, |φ y| ≤ M) : MemLp (fun y => φ y * a y) 2 volume :=
  (ha.const_mul M).of_le (hφ.aestronglyMeasurable.mul ha.1) (ae_of_all _ fun y => by
    simp only [Real.norm_eq_abs, abs_mul]
    have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y)
    rw [abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _))

open SteadyCert.SecondTraceSolenoidalInternal in
theorem tint {ψ u : Space → ℝ} (hψ : IsTestScalar ψ) (hu : MemLp u 2 volume) :
    Integrable (fun y => ψ y * u y) := by
  simpa only [smul_eq_mul] using integrable_test_smul hu one_le_two hψ

open SteadyCert.SecondTraceSolenoidalInternal in
theorem parts_h1 {a f h g : Space → ℝ} (ha : MemLp a 2 volume) (hf : MemLp f 2 volume)
    (hh : MemLp h 2 volume) (hg : MemLp g 2 volume) (j : Fin 3)
    (hag : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * a y = -∫ y, ψ y * g y)
    (hfh : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * f y = -∫ y, ψ y * h y) :
    ∫ y, h y * a y = -∫ y, f y * g y := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have c0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have χs : ∀ n : ℕ, ContDiff ℝ ∞ (radialCutoff ((n : ℝ) + 1)) := fun n => contDiff_radialCutoff (hr n)
  have dχs : ∀ n : ℕ, ContDiff ℝ ∞ (dirDeriv j (radialCutoff ((n : ℝ) + 1))) :=
    fun n => contDiff_dirDeriv (χs n) j
  have χb : ∀ (n : ℕ) y, |radialCutoff ((n : ℝ) + 1) y| ≤ 1 := fun n y =>
    abs_le.2 ⟨by linarith [radialCutoff_nonneg ((n : ℝ) + 1) y], radialCutoff_le_one _ _⟩
  have dχb : ∀ (n : ℕ) y, |dirDeriv j (radialCutoff ((n : ℝ) + 1)) y| ≤ c * (1 / ((n : ℝ) + 1)) := by
    intro n y
    calc |dirDeriv j (radialCutoff ((n : ℝ) + 1)) y|
        ≤ ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y‖ * ‖unitVector j‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * (1 / ((n : ℝ) + 1)) := by
          rw [unit_norm', mul_one, mul_one_div]; exact hc _ (hr n) y
  have dχb' : ∀ (n : ℕ) y, |dirDeriv j (radialCutoff ((n : ℝ) + 1)) y| ≤ c := fun n y =>
    (dχb n y).trans (mul_le_of_le_one_right c0 (by
      rw [div_le_one (hr n)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have hagn : ∀ n : ℕ, ∀ ψ : Space → ℝ, IsTestScalar ψ →
      ∫ y, fderiv ℝ ψ y (unitVector j) * (radialCutoff ((n : ℝ) + 1) y * a y)
        = -∫ y, ψ y * (radialCutoff ((n : ℝ) + 1) y * g y + dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y) := by
    intro n ψ hψ
    have hp : IsTestScalar (fun y => ψ y * radialCutoff ((n : ℝ) + 1) y) := ⟨hψ.1.mul (χs n), hψ.2.mul_right⟩
    have hq : IsTestScalar (fun y => dirDeriv j ψ y * radialCutoff ((n : ℝ) + 1) y) :=
      ⟨(test_dirDeriv hψ j).1.mul (χs n), (test_dirDeriv hψ j).2.mul_right⟩
    have hq' : IsTestScalar (fun y => ψ y * dirDeriv j (radialCutoff ((n : ℝ) + 1)) y) :=
      ⟨hψ.1.mul (dχs n), hψ.2.mul_right⟩
    have e := hag _ hp
    have hd : ∀ y, fderiv ℝ (fun y => ψ y * radialCutoff ((n : ℝ) + 1) y) y (unitVector j)
        = dirDeriv j ψ y * radialCutoff ((n : ℝ) + 1) y + ψ y * dirDeriv j (radialCutoff ((n : ℝ) + 1)) y := by
      intro y
      have hm : HasFDerivAt (fun y => ψ y * radialCutoff ((n : ℝ) + 1) y)
          (ψ y • fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y + radialCutoff ((n : ℝ) + 1) y • fderiv ℝ ψ y) y :=
        ((hψ.1.differentiable (by simp)) y).hasFDerivAt.mul (((χs n).differentiable (by simp)) y).hasFDerivAt
      rw [hm.fderiv]
      simp only [dirDeriv, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    simp only [hd] at e
    have i1 := tint hq ha
    have i2 := tint hq' ha
    have i3 := tint hp hg
    have e1 : ∫ y, (dirDeriv j ψ y * radialCutoff ((n : ℝ) + 1) y + ψ y * dirDeriv j (radialCutoff ((n : ℝ) + 1)) y) * a y
        = (∫ y, dirDeriv j ψ y * radialCutoff ((n : ℝ) + 1) y * a y)
          + ∫ y, ψ y * dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y := by
      rw [← integral_add i1 i2]; congr 1; funext y; ring
    have e2 : ∫ y, ψ y * (radialCutoff ((n : ℝ) + 1) y * g y + dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y)
        = (∫ y, ψ y * radialCutoff ((n : ℝ) + 1) y * g y)
          + ∫ y, ψ y * dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y := by
      rw [← integral_add i3 i2]; congr 1; funext y; ring
    have e3 : ∫ y, fderiv ℝ ψ y (unitVector j) * (radialCutoff ((n : ℝ) + 1) y * a y)
        = ∫ y, dirDeriv j ψ y * radialCutoff ((n : ℝ) + 1) y * a y := by
      congr 1; funext y; simp only [dirDeriv]; ring
    have e4 : ∫ y, ψ y * radialCutoff ((n : ℝ) + 1) y * g y = ∫ y, (ψ y * radialCutoff ((n : ℝ) + 1) y) * g y := rfl
    rw [e1] at e
    rw [e2, e3]
    linarith
  have hsum : ∀ n : ℕ, ∫ y, h y * (radialCutoff ((n : ℝ) + 1) y * a y)
      = -∫ y, f y * (radialCutoff ((n : ℝ) + 1) y * g y + dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y) := by
    intro n
    refine parts_scalar (memLp_mulb ha (χs n).continuous (χb n)) hf hh
      ((memLp_mulb hg (χs n).continuous (χb n)).add (memLp_mulb ha (dχs n).continuous (dχb' n)))
      (R := 2 * ((n : ℝ) + 1)) (fun y hy => ?_) j (hagn n) hfh
    rw [radialCutoff_eq_zero (hr n) hy.le, zero_mul]
  have hone : ∀ y : Space, Tendsto (fun n : ℕ => radialCutoff ((n : ℝ) + 1) y) atTop (𝓝 1) := by
    intro y
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩)
    have h1 := Nat.le_ceil ‖y‖
    have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    exact (radialCutoff_eq_one (hr n) (by linarith)).symm
  have hzero : ∀ y : Space, Tendsto (fun n : ℕ => dirDeriv j (radialCutoff ((n : ℝ) + 1)) y) atTop (𝓝 0) := by
    intro y
    have ht : Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) atTop (𝓝 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact dχb n y) ht
  have L1 : Tendsto (fun n : ℕ => ∫ y, h y * (radialCutoff ((n : ℝ) + 1) y * a y)) atTop (𝓝 (∫ y, h y * a y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖h y * a y‖) (fun n => ?_)
      (hh.integrable_mul ha).norm (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · exact hh.1.mul ((χs n).continuous.aestronglyMeasurable.mul ha.1)
    · simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (abs_nonneg _) (χb n y)) (abs_nonneg _)
    · simpa using (tendsto_const_nhds (x := h y)).mul ((hone y).mul (tendsto_const_nhds (x := a y)))
  have L2 : Tendsto (fun n : ℕ => ∫ y, f y * (radialCutoff ((n : ℝ) + 1) y * g y
      + dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y)) atTop (𝓝 (∫ y, f y * g y)) := by
    refine tendsto_integral_of_dominated_convergence (fun y => ‖f y * g y‖ + c * ‖f y * a y‖) (fun n => ?_)
      ((hf.integrable_mul hg).norm.add ((hf.integrable_mul ha).norm.const_mul c))
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · exact hf.1.mul (((χs n).continuous.aestronglyMeasurable.mul hg.1).add
        ((dχs n).continuous.aestronglyMeasurable.mul ha.1))
    · simp only [Real.norm_eq_abs, abs_mul]
      have h1 := χb n y
      have h2 := dχb' n y
      have h3 := abs_add_le (radialCutoff ((n : ℝ) + 1) y * g y) (dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y)
      rw [abs_mul, abs_mul] at h3
      have hf0 := abs_nonneg (f y)
      have hg0 := abs_nonneg (g y)
      have ha0 := abs_nonneg (a y)
      have k1 : |radialCutoff ((n : ℝ) + 1) y| * |g y| ≤ |g y| := mul_le_of_le_one_left hg0 h1
      have k2 : |dirDeriv j (radialCutoff ((n : ℝ) + 1)) y| * |a y| ≤ c * |a y| := mul_le_mul_of_nonneg_right h2 ha0
      calc |f y| * |radialCutoff ((n : ℝ) + 1) y * g y + dirDeriv j (radialCutoff ((n : ℝ) + 1)) y * a y|
          ≤ |f y| * (|g y| + c * |a y|) := mul_le_mul_of_nonneg_left (by linarith) hf0
        _ = |f y| * |g y| + c * (|f y| * |a y|) := by ring
    · have := (tendsto_const_nhds (x := f y)).mul (((hone y).mul (tendsto_const_nhds (x := g y))).add
        ((hzero y).mul (tendsto_const_nhds (x := a y))))
      simpa using this
  have L2' := L2.neg
  simp only [← hsum] at L2'
  exact tendsto_nhds_unique L1 L2'

open SteadyCert.SecondTraceSolenoidalInternal in
theorem comp_weak {u D : Space → Space} (hu : MemLp u 2 volume) (hD : MemLp D 2 volume) (j i : Fin 3)
    (hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) • u y = -∫ y, ψ y • D y) :
    ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * inner ℝ (unitVector i) (u y)
      = -∫ y, ψ y * inner ℝ (unitVector i) (D y) := by
  intro ψ hψ
  have h1 : Integrable (fun y => fderiv ℝ ψ y (unitVector j) • u y) :=
    integrable_test_smul hu one_le_two (test_dirDeriv hψ j)
  have h2 : Integrable (fun y => ψ y • D y) := integrable_test_smul hD one_le_two hψ
  have e := congrArg (fun z => inner ℝ (unitVector i) z) (hw ψ hψ)
  simp only [inner_neg_right] at e
  rw [← integral_inner h1, ← integral_inner h2] at e
  simpa only [inner_smul_right] using e

theorem comp_expand (u w : Space) :
    inner ℝ u w = ∑ i : Fin 3, inner ℝ (unitVector i) u * inner ℝ (unitVector i) w := by
  simp [unitVector, PiLp.inner_apply, Fin.sum_univ_three]
  ring

open SteadyCert.SecondTraceSolenoidalInternal in
theorem pair_h1 {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H)
    {b : Space → Space} {Db : Space → (Space →L[ℝ] Space)} (hb : MemLp b 2 volume) (hbw : IsWeakGradientOf b Db)
    (hDm : AEStronglyMeasurable Db volume) (hD2 : Integrable (fun y => entrySq (Db y))) :
    l2Pair b (negSecondTrace H) = ∫ y, entryInner (G y) (Db y) := by
  have hG : ∀ j, MemLp (fun y => G y (unitVector j)) 2 volume :=
    memLp_column hs.measurable_gradient hs.gradient_two
  have hD : ∀ j, MemLp (fun y => Db y (unitVector j)) 2 volume := memLp_column hDm hD2
  have hH : ∀ j, MemLp (fun y => H y (unitVector j) (unitVector j)) 2 volume :=
    memLp_entry hs.measurable_second hs.second_two
  have cm : ∀ {F : Space → Space}, MemLp F 2 volume → ∀ i : Fin 3,
      MemLp (fun y => inner ℝ (unitVector i) (F y)) 2 volume := fun hF i => hF.const_inner (unitVector i)
  have key : ∀ i j : Fin 3, ∫ y, inner ℝ (unitVector i) (H y (unitVector j) (unitVector j)) * inner ℝ (unitVector i) (b y)
      = -∫ y, inner ℝ (unitVector i) (G y (unitVector j)) * inner ℝ (unitVector i) (Db y (unitVector j)) := by
    intro i j
    refine parts_h1 (cm hb i) (cm (hG j) i) (cm (hH j) i) (cm (hD j) i) j ?_ ?_
    · exact comp_weak hb (hD j) j i (fun ψ hψ => hbw ψ hψ j)
    · exact comp_weak (hG j) (hH j) j i (fun ψ hψ => hs.weak_second ψ hψ j j)
  have int1 : ∀ i j : Fin 3, Integrable (fun y => inner ℝ (unitVector i) (H y (unitVector j) (unitVector j))
      * inner ℝ (unitVector i) (b y)) := fun i j => (cm (hH j) i).integrable_mul (cm hb i)
  have int2 : ∀ i j : Fin 3, Integrable (fun y => inner ℝ (unitVector i) (G y (unitVector j))
      * inner ℝ (unitVector i) (Db y (unitVector j))) := fun i j => (cm (hG j) i).integrable_mul (cm (hD j) i)
  have pL : ∀ y, inner ℝ (b y) (negSecondTrace H y) = -∑ j : Fin 3, ∑ i : Fin 3,
      inner ℝ (unitVector i) (H y (unitVector j) (unitVector j)) * inner ℝ (unitVector i) (b y) := by
    intro y
    simp only [negSecondTrace, secondTrace, inner_neg_right, inner_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [comp_expand]
    exact Finset.sum_congr rfl fun i _ => by ring
  have pR : ∀ y, entryInner (G y) (Db y) = ∑ j : Fin 3, ∑ i : Fin 3,
      inner ℝ (unitVector i) (G y (unitVector j)) * inner ℝ (unitVector i) (Db y (unitVector j)) := by
    intro y
    simp only [entryInner]
    exact Finset.sum_congr rfl fun j _ => comp_expand _ _
  unfold l2Pair
  simp only [pL, pR]
  rw [integral_neg, integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun i _ => int1 i j),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun i _ => int2 i j)]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun i _ => int1 i j), integral_finsetSum _ (fun i _ => int2 i j),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [key i j, neg_neg]


end CentrePairingActuatorInternal

open SteadyCert CentrePairingActuatorInternal in
theorem actuatorPairing (α : ℝ) {k N : ℕ} (c : FracCellData k N) (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) (i : Fin k) :
    l2Pair (c.actuator i) (negSecondTrace H) = ∫ y, entryInner (G y) (c.actuatorGrad i y) := by
  obtain ⟨hw, hm, h2⟩ := hc.actuator_gradient i
  exact pair_h1 hs (hc.base.actuator_two i) hw hm h2

end CellCert

end Breakdown

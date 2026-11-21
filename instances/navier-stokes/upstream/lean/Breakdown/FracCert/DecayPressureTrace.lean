import Breakdown.FracCert.DecayPressureDiv

open MeasureTheory Set Real Filter
open scoped ENNReal ContDiff FourierTransform

noncomputable section

namespace Breakdown.FracCert.DecayPressureTrace

open Breakdown.Freq Breakdown.SmoothFlow Breakdown.FundSol Breakdown.FracCert.WeakRegularInternal
open Breakdown.SmoothFlow.Internal Breakdown.SmoothFlow.PowerInternal

private theorem sum_sq_coord (ξ : Space) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) = (((‖ξ‖ ^ 2 : ℝ)) : ℂ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs]
  rw [← Complex.ofReal_pow, sq_abs, Complex.ofReal_pow]
  ring

private theorem divergenceAt_add' {f g : Space → Space} {y : Space} (hf : DifferentiableAt ℝ f y)
    (hg : DifferentiableAt ℝ g y) :
    divergenceAt (fun x => f x + g x) y = divergenceAt f y + divergenceAt g y := by
  unfold divergenceAt
  rw [fderiv_fun_add hf hg, ← Finset.sum_add_distrib]
  simp

theorem pressureTrace_of (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) :
    PressureTraceStatement := by
  intro α hα1 hα2 a U hU hM hD y
  have hwm := (h3 U hM).1
  set f := cleanSymbol (symbolX U) with hfdef
  have hf : ∀ k, MemLp f 1 (weightL1Measure k) := memLp_clean U hwm
  have hsol : IsSolenoidalSymbol f := fun ξ => ⟨cleanSymbol_div _ ξ, cleanSymbol_conjSym _ ξ⟩
  set g : Space → ℂ := pressureSymbol f with hgdef
  have hS : ∀ k, MemLp (fun ξ => g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
      (weightL1Measure k) := memLp_pressureSymbol_single hf hsol
  have hgS : ∀ ξ, ‖g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)‖ = ‖g ξ‖ := fun ξ => by
    rw [norm_smul]; simp
  have hgi : Integrable g := by
    have h := (EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).integrable_comp
      (integrable_of_weight (hS 0))
    refine h.congr (Eventually.of_forall fun ξ => ?_)
    simp
  have hgm : AEStronglyMeasurable g volume := hgi.aestronglyMeasurable
  have hgf : Integrable (fun ξ => g ξ • freqVec ξ) := by
    have h := integrable_pow_mul_of_weight (hS 1) (n := 1) le_rfl
    refine h.mono' (hgm.smul (Continuous.aestronglyMeasurable (by
      unfold freqVec complexifyVec; fun_prop))) (Eventually.of_forall fun ξ => ?_)
    rw [norm_smul, norm_freqVec, hgS, pow_one, mul_comm]
  set G : Space → CSpace := fun ξ => (2 * (π : ℂ) * Complex.I * g ξ) • freqVec ξ with hGdef
  have hGw : MemLp G 1 (weightL1Measure 1) := by
    have hB := (memLp_weight_shift' (k := 1) (j := 1) (hS (1 + 1))).const_smul ((2 * π : ℝ) : ℂ)
    refine hB.of_le ?_ (Eventually.of_forall fun ξ => ?_)
    · refine AEStronglyMeasurable.mono_ac (weight_ac_volume 1) ?_
      exact (hgm.const_mul _).smul (Continuous.aestronglyMeasurable (by
        unfold freqVec complexifyVec; fun_prop))
    · have hp : ‖(2 * (π : ℂ) * Complex.I)‖ = 2 * π := by
        simp [Complex.norm_I, abs_of_pos Real.pi_pos]
      have lhs : ‖G ξ‖ = 2 * π * (‖g ξ‖ * ‖ξ‖) := by
        simp only [hGdef, norm_smul, norm_freqVec, norm_mul, hp]
        ring
      have h2p : (0 : ℝ) < 2 * π := by positivity
      have h1p : (0 : ℝ) < 1 + ‖ξ‖ := by positivity
      have rhs : ‖((((2 * π : ℝ)) : ℂ) • fun ξ : Space => ((1 + ‖ξ‖) ^ 1 : ℝ) •
          g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) ξ‖ = 2 * π * ((1 + ‖ξ‖) * ‖g ξ‖) := by
        simp only [Pi.smul_apply, norm_smul, hgS, pow_one, Real.norm_eq_abs, Complex.norm_real,
          abs_of_pos h2p, abs_of_pos h1p]
      rw [lhs, rhs]
      have := norm_nonneg (g ξ)
      nlinarith [norm_nonneg ξ]
  have hA : MemLp (advectionSymbol f) 1 (weightL1Measure 1) := memLp_advectionSymbol hf 1
  have hV : ContDiff ℝ ∞ (profileField U) := by
    unfold profileField
    rw [← physField_clean U]
    exact (h4 _ (moments_clean U hwm) (cleanSymbol_conjSym _)).1
  have hQ : ContDiff ℝ ∞ (profilePressure U) := pressureSmooth_of h3 U hM
  have hVd : Differentiable ℝ (profileField U) := hV.differentiable (by simp)
  have hDd : Differentiable ℝ (fderiv ℝ (profileField U)) :=
    ((contDiff_infty_iff_fderiv.1 hV).2).differentiable (by simp)
  have hQ1 : ContDiff ℝ ∞ (fderiv ℝ (profilePressure U)) := (contDiff_infty_iff_fderiv.1 hQ).2
  have hgradd : Differentiable ℝ (gradientAt (profilePressure U)) := by
    have hc : ContDiff ℝ ∞ (fun x => ∑ k : Fin 3,
        fderiv ℝ (profilePressure U) x (unitVector k) • unitVector k) :=
      ContDiff.sum fun k _ => (hQ1.clm_apply contDiff_const).smul contDiff_const
    exact hc.differentiable (by simp)
  have hadvd : Differentiable ℝ (advectionAt (profileField U)) := fun x =>
    (hDd x).clm_apply (hVd x)
  have hQe : profilePressure U = physScalar g := by
    unfold profilePressure; rw [hgdef, hfdef, pressure_clean U]
  have hgrad : ∀ x, gradientAt (profilePressure U) x = physField G x := by
    intro x; rw [hQe]; exact gradientAt_physScalar hgi hgf x
  have hadv : ∀ x, advectionAt (profileField U) x = physField (advectionSymbol f) x := by
    intro x
    unfold profileField
    rw [← physField_clean U]
    exact advectionAt_physField hf hsol x
  have hsum : (fun x => advectionAt (profileField U) x + gradientAt (profilePressure U) x) =
      physField (fun ξ => advectionSymbol f ξ + G ξ) := by
    funext x
    rw [physField_add (integrable_of_weight hA) (integrable_of_weight hGw), hadv, hgrad]
  have hdiv0 : divergenceAt (physField (fun ξ => advectionSymbol f ξ + G ξ)) y = 0 := by
    refine divergenceAt_physField (hA.add hGw) (fun ξ => ?_) y
    by_cases hξ : ξ = 0
    · subst hξ; simp
    have hn : (((‖ξ‖ ^ 2 : ℝ)) : ℂ) ≠ 0 := by
      have : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.2 hξ
      exact_mod_cast pow_ne_zero 2 this
    have hI : (2 * (π : ℂ) * Complex.I) ≠ 0 := by
      simp [Complex.I_ne_zero, Real.pi_ne_zero]
    have e1 : ∑ i, ((ξ i : ℝ) : ℂ) * (advectionSymbol f ξ + G ξ) i =
        ∑ i, ((ξ i : ℝ) : ℂ) * advectionSymbol f ξ i +
          (2 * (π : ℂ) * Complex.I * g ξ) * ∑ i, ((ξ i : ℝ) : ℂ) * ((ξ i : ℝ) : ℂ) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hGdef, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, freqVec, complexifyVec]
      simp
      ring
    show ∑ i, ((ξ i : ℝ) : ℂ) * (advectionSymbol f ξ + G ξ) i = 0
    rw [e1, sum_sq_coord, hgdef]
    unfold pressureSymbol
    field_simp
    ring
  rw [DecayPressureDiv.trace_eq_div_grad hQ y]
  have hadd := divergenceAt_add' (hadvd y) (hgradd y)
  rw [hsum, hdiv0] at hadd
  linarith

theorem productWeightedSmooth_of (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) :
    ProductWeightedSmoothStatement := by
  intro α hα1 hα2 a U hU hM hD i j
  have hwm := (h3 U hM).1
  have hV : ContDiff ℝ ∞ (profileField U) := by
    unfold profileField
    rw [← physField_clean U]
    exact (h4 _ (moments_clean U hwm) (cleanSymbol_conjSym _)).1
  have hcomp : ∀ l : Fin 3, ContDiff ℝ ∞ (fun y => profileField U y l) := fun l =>
    (EuclideanSpace.proj l : Space →L[ℝ] ℝ).contDiff.comp hV
  have hproj : ∀ (k : ℕ) (l : Fin 3) (y : Space),
      ‖iteratedFDeriv ℝ k (fun y => profileField U y l) y‖ ≤ ‖iteratedFDeriv ℝ k (profileField U) y‖ := by
    intro k l y
    have h := (EuclideanSpace.proj l : Space →L[ℝ] ℝ).norm_iteratedFDeriv_comp_left (n := k)
      (hV.contDiffAt (x := y)) ENat.LEInfty.out
    have hn : ‖(EuclideanSpace.proj l : Space →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
        simpa using PiLp.norm_apply_le v l
    exact h.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ k (profileField U) y)])
  refine ⟨Complex.ofRealCLM.contDiff.comp ((hcomp i).mul (hcomp j)), fun m => ?_⟩
  choose C hC using hD
  refine ⟨∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (|C k| * |C (m - k)|), fun y => ?_⟩
  have hpos : (0 : ℝ) < 1 + ‖y‖ := by positivity
  have hdec : ∀ k, ‖iteratedFDeriv ℝ k (profileField U) y‖ ≤
      |C k| * (1 + ‖y‖) ^ (-(2 * α - 1 + k)) := fun k =>
    (hC k y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg hpos.le _))
  have hmul := norm_iteratedFDeriv_mul_le (hcomp i) (hcomp j) y (n := m) ENat.LEInfty.out
  have hre : ‖iteratedFDeriv ℝ m (fun y => ((profileField U y i * profileField U y j : ℝ) : ℂ)) y‖ ≤
      ‖iteratedFDeriv ℝ m (fun y => profileField U y i * profileField U y j) y‖ := by
    have h := Complex.ofRealCLM.norm_iteratedFDeriv_comp_left (n := m)
      (((hcomp i).mul (hcomp j)).contDiffAt (x := y)) ENat.LEInfty.out
    have hn : ‖Complex.ofRealCLM‖ ≤ 1 := by simp
    exact h.trans (by nlinarith [norm_nonneg (iteratedFDeriv ℝ m
      (fun y => profileField U y i * profileField U y j) y)])
  have hterm : ∀ k ∈ Finset.range (m + 1),
      (m.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y => profileField U y i) y‖ *
        ‖iteratedFDeriv ℝ (m - k) (fun y => profileField U y j) y‖ ≤
      (m.choose k : ℝ) * (|C k| * |C (m - k)|) * (1 + ‖y‖) ^ (-(4 * α - 2 + m)) := by
    intro k hk
    have hkm : k ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
    have e : (1 + ‖y‖) ^ (-(2 * α - 1 + k)) * (1 + ‖y‖) ^ (-(2 * α - 1 + ((m - k : ℕ) : ℝ))) =
        (1 + ‖y‖) ^ (-(4 * α - 2 + m)) := by
      rw [← Real.rpow_add hpos]
      congr 1
      rw [Nat.cast_sub hkm]
      ring
    have a1 := (hproj k i y).trans (hdec k)
    have a2 := (hproj (m - k) j y).trans (hdec (m - k))
    have hch : (0 : ℝ) ≤ (m.choose k : ℝ) := Nat.cast_nonneg _
    calc (m.choose k : ℝ) * ‖iteratedFDeriv ℝ k (fun y => profileField U y i) y‖ *
          ‖iteratedFDeriv ℝ (m - k) (fun y => profileField U y j) y‖
        = (m.choose k : ℝ) * (‖iteratedFDeriv ℝ k (fun y => profileField U y i) y‖ *
          ‖iteratedFDeriv ℝ (m - k) (fun y => profileField U y j) y‖) := by ring
      _ ≤ (m.choose k : ℝ) * ((|C k| * (1 + ‖y‖) ^ (-(2 * α - 1 + k))) *
          (|C (m - k)| * (1 + ‖y‖) ^ (-(2 * α - 1 + ((m - k : ℕ) : ℝ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul a1 a2 (norm_nonneg _)
            (by positivity)) hch
      _ = (m.choose k : ℝ) * (|C k| * |C (m - k)|) * (1 + ‖y‖) ^ (-(4 * α - 2 + m)) := by
          rw [← e]; ring
  have hsum := hmul.trans (Finset.sum_le_sum hterm)
  rw [← Finset.sum_mul] at hsum
  have hwpos : 0 < (1 + ‖y‖) ^ (4 * α - 2 + (m : ℝ)) := Real.rpow_pos_of_pos hpos _
  calc (1 + ‖y‖) ^ (4 * α - 2 + (m : ℝ)) *
        ‖iteratedFDeriv ℝ m (fun y => ((profileField U y i * profileField U y j : ℝ) : ℂ)) y‖
      ≤ (1 + ‖y‖) ^ (4 * α - 2 + (m : ℝ)) *
        ((∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (|C k| * |C (m - k)|)) *
          (1 + ‖y‖) ^ (-(4 * α - 2 + m))) :=
        mul_le_mul_of_nonneg_left (hre.trans hsum) hwpos.le
    _ = ∑ k ∈ Finset.range (m + 1), (m.choose k : ℝ) * (|C k| * |C (m - k)|) := by
        rw [Real.rpow_neg hpos.le]
        field_simp

end Breakdown.FracCert.DecayPressureTrace

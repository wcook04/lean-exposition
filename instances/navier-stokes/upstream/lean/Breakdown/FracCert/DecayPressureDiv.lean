import Breakdown.FracCert.DecayPressureParts
import Breakdown.FracCert.WeakRegular
import Breakdown.Uniqueness.FundSolEnergyAux
import Breakdown.Frac.RegPowerPhysCurve

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert.DecayPressureDiv

open Breakdown.Freq Breakdown.FundSol Breakdown.FundSol.Internal

private def traceL : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector i))

private theorem traceL_apply (L : Space →L[ℝ] Space) :
    traceL L = ∑ i : Fin 3, L (unitVector i) i := by
  simp [traceL]

private theorem div_eq (f : Space → Space) (x : Space) :
    divergenceAt f x = traceL (fderiv ℝ f x) := by
  rw [traceL_apply]; rfl

private def turnL : Space →L[ℝ] Space :=
  (-(EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ)).smulRight (unitVector 0) +
    (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).smulRight (unitVector 1)

private theorem turnL_eq (w : Space) : turnL w = (-(w 1)) • unitVector 0 + (w 0) • unitVector 1 := by
  simp [turnL]

private theorem turnL_apply (y : Space) : turnL y = axialTurn y := by
  rw [turnL_eq]
  ext i
  fin_cases i <;> simp [axialTurn, unitVector]

private theorem trace_comm_turn (L : Space →L[ℝ] Space) :
    traceL (L.comp turnL) = traceL (turnL.comp L) := by
  rw [traceL_apply, traceL_apply]
  simp only [Fin.sum_univ_three, ContinuousLinearMap.comp_apply, turnL_eq]
  simp [unitVector]
  ring

theorem trace_eq_div_grad {P : Space → ℝ} (hP : ContDiff ℝ ∞ P) (y : Space) :
    scalarSumSecondPartials P y = divergenceAt (gradientAt P) y := by
  have hg : gradientAt P = fun x => ∑ k : Fin 3, dirDeriv (unitVector k) P x • unitVector k := rfl
  have hd : ∀ k : Fin 3, DifferentiableAt ℝ (dirDeriv (unitVector k) P) y :=
    fun k => (contDiff_dirDeriv hP _).differentiable (by simp) y
  have hfd : fderiv ℝ (gradientAt P) y =
      ∑ k : Fin 3, (fderiv ℝ (dirDeriv (unitVector k) P) y).smulRight (unitVector k) := by
    rw [hg, fderiv_fun_sum (fun k _ => (hd k).smul_const _)]
    exact Finset.sum_congr rfl fun k _ => fderiv_smul_const (hd k) _
  unfold divergenceAt scalarSumSecondPartials
  rw [hfd]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [secondPartial_eq_dirDeriv hP]
  simp [unitVector, dirDeriv, Pi.single_apply]

theorem trace_of_residual {α a : ℝ} {V : Space → Space} {P : Space → ℝ} (hV : ContDiff ℝ ∞ V)
    (hP : ContDiff ℝ ∞ P) (hF : Differentiable ℝ (fractionalPowerAt α V))
    (hdivV : ∀ y, divergenceAt V y = 0) (hdivF : ∀ y, divergenceAt (fractionalPowerAt α V) y = 0)
    (hres : ∀ y, rotatingProfileResidual α a 1 V P y = 0) (y : Space) :
    scalarSumSecondPartials P y = -divergenceAt (advectionAt V) y := by
  have hVd : Differentiable ℝ V := hV.differentiable (by simp)
  have hD : ContDiff ℝ ∞ (fderiv ℝ V) := (contDiff_infty_iff_fderiv.1 hV).2
  have hDd : Differentiable ℝ (fderiv ℝ V) := hD.differentiable (by simp)
  have hsymm : ∀ v w : Space, fderiv ℝ (fderiv ℝ V) y v w = fderiv ℝ (fderiv ℝ V) y w v :=
    hV.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      exact ENat.LEInfty.out)
  have hdivd : ∀ v, traceL (fderiv ℝ (fderiv ℝ V) y v) = 0 := by
    have hz : (fun x => traceL (fderiv ℝ V x)) = fun _ => (0 : ℝ) :=
      funext fun x => by rw [← div_eq]; exact hdivV x
    have hh : HasFDerivAt (fun x => traceL (fderiv ℝ V x)) (traceL.comp (fderiv ℝ (fderiv ℝ V) y)) y :=
      traceL.hasFDerivAt.comp y (hDd y).hasFDerivAt
    rw [hz] at hh
    have hu := (hasFDerivAt_const (0 : ℝ) y).unique hh
    intro v
    have := congrArg (fun L : Space →L[ℝ] ℝ => L v) hu
    simpa using this.symm
  have hflip : ∀ w : Space, traceL ((fderiv ℝ (fderiv ℝ V) y).flip w) = 0 := by
    intro w
    have e : (fderiv ℝ (fderiv ℝ V) y).flip w = fderiv ℝ (fderiv ℝ V) y w := by
      ext1 v
      simp only [ContinuousLinearMap.flip_apply]
      exact hsymm v w
    rw [e]; exact hdivd w
  have hA1 : HasFDerivAt (fun x => fderiv ℝ V x x)
      ((fderiv ℝ V y).comp (ContinuousLinearMap.id ℝ Space) + (fderiv ℝ (fderiv ℝ V) y).flip y) y :=
    (hDd y).hasFDerivAt.clm_apply (hasFDerivAt_id y)
  have hA2 : HasFDerivAt (fun x => fderiv ℝ V x (turnL x))
      ((fderiv ℝ V y).comp turnL + (fderiv ℝ (fderiv ℝ V) y).flip (turnL y)) y :=
    (hDd y).hasFDerivAt.clm_apply turnL.hasFDerivAt
  have hA3 : HasFDerivAt (fun x => turnL (V x)) (turnL.comp (fderiv ℝ V y)) y :=
    turnL.hasFDerivAt.comp y (hVd y).hasFDerivAt
  have hA5 : HasFDerivAt (fun x => fderiv ℝ V x (V x)) (fderiv ℝ (advectionAt V) y) y :=
    ((hDd y).clm_apply (hVd y)).hasFDerivAt
  have hG := (((((hVd y).hasFDerivAt.const_smul (1 - 1 / (2 * α))).add
    (hA1.const_smul (1 / (2 * α)))).add ((hA2.sub hA3).const_smul a)).add
    ((hF y).hasFDerivAt.const_smul (1 : ℝ))).add hA5
  have hgrad : gradientAt P = fun x => -((1 - 1 / (2 * α)) • V x + (1 / (2 * α)) • fderiv ℝ V x x
      + a • (fderiv ℝ V x (turnL x) - turnL (V x)) + (1 : ℝ) • fractionalPowerAt α V x
      + fderiv ℝ V x (V x)) := by
    funext x
    have h := hres x
    unfold rotatingProfileResidual at h
    simp only [← turnL_apply] at h
    exact eq_neg_of_add_eq_zero_right h
  have hN := hG.neg.congr_of_eventuallyEq (f₁ := gradientAt P)
    (Filter.Eventually.of_forall fun x => by rw [hgrad]; rfl)
  rw [trace_eq_div_grad hP y, div_eq, hN.fderiv, div_eq (advectionAt V)]
  simp only [map_neg, map_add, map_sub, map_smul, smul_eq_mul, hflip]
  have h1 : traceL (fderiv ℝ V y) = 0 := by rw [← div_eq]; exact hdivV y
  have h2 : traceL (fderiv ℝ (fractionalPowerAt α V) y) = 0 := by rw [← div_eq]; exact hdivF y
  have h3 : traceL ((fderiv ℝ V y).comp (ContinuousLinearMap.id ℝ Space)) = 0 := by
    rw [ContinuousLinearMap.comp_id]; exact h1
  rw [h1, h2, h3, trace_comm_turn]
  ring

end Breakdown.FracCert.DecayPressureDiv

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.FracCert.DecayPressureDiv

theorem residualDivergence_of (hPow : PowerDivergenceFreeStatement) (h2 : PowerDecayStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) :
    ResidualDivergenceStatement := by
  intro α hα1 hα2 a U hU hM hD P hP hres y
  have hwm := (h3 U hM).1
  have hphys := WeakRegularInternal.physField_clean U
  have hV : ContDiff ℝ ∞ (profileField U) := by
    unfold profileField
    rw [← hphys]
    exact (h4 _ (WeakRegularInternal.moments_clean U hwm) (WeakRegularInternal.cleanSymbol_conjSym _)).1
  have hdivV : ∀ y, divergenceAt (profileField U) y = 0 := by
    intro y
    unfold profileField
    rw [← hphys]
    exact Breakdown.SmoothFlow.divergenceAt_physField (WeakRegularInternal.memLp_clean U hwm 1)
      (WeakRegularInternal.cleanSymbol_div _) y
  have hF : Differentiable ℝ (fractionalPowerAt α (profileField U)) :=
    ((h2 α hα1 hα2 a U hU hM hD).1).differentiable (by simp)
  exact trace_of_residual hV hP hF hdivV (hPow α hα1 hα2 a U hU hM hD) hres y

open Breakdown.SmoothFlow in
theorem powerDivergenceFree_of (h3 : SymbolL1OfMomentsStatement) : PowerDivergenceFreeStatement := by
  intro α hα1 hα2 a U hU hM hD y
  have hwm := (h3 U hM).1
  have hF : fractionalPowerAt α (profileField U) =
      physField (powerSymbol α (WeakRegularInternal.cleanSymbol (symbolX U))) := by
    funext x
    unfold profileField
    rw [← WeakRegularInternal.physField_clean U]
    exact powerPhysPower_of α hα1 (by linarith)
      (Periodic.planeWaveEigen_of α hα1 (by linarith) (symbolScalar normalizer) normalizer) _
      (WeakRegularInternal.memLp_clean U hwm 3) x
  rw [hF]
  refine divergenceAt_physField (PowerInternal.memLp_powerSymbol' (by linarith) (by linarith)
    (WeakRegularInternal.memLp_clean U hwm (1 + 3))) (fun ξ => ?_) y
  have h0 := WeakRegularInternal.cleanSymbol_div (symbolX U) ξ
  have e : ∑ i, ((ξ i : ℝ) : ℂ) * ((((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) •
      WeakRegularInternal.cleanSymbol (symbolX U) ξ) i =
      (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) *
        ∑ i, ((ξ i : ℝ) : ℂ) * WeakRegularInternal.cleanSymbol (symbolX U) ξ i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul]
    ring
  unfold powerSymbol
  rw [e, h0, mul_zero]

end Breakdown.FracCert

import Breakdown.FracCert.DecayPressureTrace
import Breakdown.FracCert.DecayPressureModel
import Breakdown.FracCert.DecayPressureRep
import Breakdown.FracCert.DecayPressureVanish

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert.DecayPressure

open Breakdown.Freq Breakdown.FundSol

private theorem fderiv_apply_eq_inner (ψ : Space → ℝ) (y w : Space) :
    fderiv ℝ ψ y w = inner ℝ (gradientAt ψ y) w := by
  have hw : w = ∑ i : Fin 3, w i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
  conv_lhs => rw [hw]
  simp [gradientAt, sum_inner, real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left,
    map_sum, mul_comm]

private theorem norm_fderiv_le_grad (ψ : Space → ℝ) (y : Space) :
    ‖fderiv ℝ ψ y‖ ≤ ‖gradientAt ψ y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => by
    rw [fderiv_apply_eq_inner]; exact norm_inner_le_norm _ _

private theorem norm_turn_le (y : Space) : ‖axialTurn y‖ ≤ ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp [axialTurn, Fin.sum_univ_three]
  nlinarith [sq_nonneg (y 2)]

private theorem weight_facts (α r : ℝ) (hα : 1 < α) (hr : 0 ≤ r) :
    (1 + r) ^ (-(2 * α)) * r ≤ (1 + r) ^ (-(2 * α - 1)) ∧
    (1 + r) ^ (-(2 * α)) ≤ (1 + r) ^ (-(2 * α - 1)) ∧
    (1 + r) ^ (-(4 * α - 1)) ≤ (1 + r) ^ (-(2 * α - 1)) ∧
    (1 + r) ^ (-(2 * α - 1)) ≤ 1 ∧ 0 ≤ (1 + r) ^ (-(2 * α)) := by
  have h1 : (1 : ℝ) ≤ 1 + r := by linarith
  have hpos : (0 : ℝ) < 1 + r := by linarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have e : (1 + r) ^ (-(2 * α - 1)) = (1 + r) ^ (-(2 * α)) * (1 + r) := by
      rw [show -(2 * α - 1) = -(2 * α) + 1 by ring, Real.rpow_add hpos, Real.rpow_one]
    rw [e]
    exact mul_le_mul_of_nonneg_left (by linarith) (Real.rpow_nonneg hpos.le _)
  · exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
  · exact Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)
  · exact Real.rpow_nonneg hpos.le _

private theorem grad_bound {α a : ℝ} (hα : 1 < α) (V : Space → Space) (P : Space → ℝ)
    (hres : ∀ y, rotatingProfileResidual α a 1 V P y = 0) {C0 C1 CA : ℝ}
    (h0 : ∀ y, ‖V y‖ ≤ C0 * (1 + ‖y‖) ^ (-(2 * α - 1)))
    (h1 : ∀ y, ‖fderiv ℝ V y‖ ≤ C1 * (1 + ‖y‖) ^ (-(2 * α)))
    (hA : ∀ y, ‖fractionalPowerAt α V y‖ ≤ CA * (1 + ‖y‖) ^ (-(4 * α - 1))) :
    ∃ K : ℝ, ∀ y, ‖gradientAt P y‖ ≤ K * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
  refine ⟨|1 - 1 / (2 * α)| * |C0| + |1 / (2 * α)| * |C1| + |a| * (|C1| + |C0|) + |CA|
    + |C1| * |C0|, fun y => ?_⟩
  obtain ⟨e1, e2, e3, e4, e5⟩ := weight_facts α ‖y‖ hα (norm_nonneg y)
  set w := (1 + ‖y‖) ^ (-(2 * α - 1)) with hwdef
  set u := (1 + ‖y‖) ^ (-(2 * α)) with hudef
  have hw0 : 0 ≤ w := le_trans e5 e2
  have hg : gradientAt P y = -((1 - 1 / (2 * α)) • V y + (1 / (2 * α)) • fderiv ℝ V y y
      + a • (fderiv ℝ V y (axialTurn y) - axialTurn (V y))
      + (1 : ℝ) • fractionalPowerAt α V y + advectionAt V y) := by
    have h := hres y
    unfold rotatingProfileResidual at h
    exact eq_neg_of_add_eq_zero_right h
  have hv : ‖V y‖ ≤ |C0| * w := (h0 y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hw0)
  have hd : ‖fderiv ℝ V y‖ ≤ |C1| * u :=
    (h1 y).trans (mul_le_mul_of_nonneg_right (le_abs_self _) e5)
  have hp : ‖fractionalPowerAt α V y‖ ≤ |CA| * w :=
    (hA y).trans (mul_le_mul (le_abs_self _) e3 (Real.rpow_nonneg (by positivity) _) (abs_nonneg _))
  have t1 : ‖(1 - 1 / (2 * α)) • V y‖ ≤ |1 - 1 / (2 * α)| * (|C0| * w) := by
    rw [norm_smul, Real.norm_eq_abs]; exact mul_le_mul_of_nonneg_left hv (abs_nonneg _)
  have t2 : ‖(1 / (2 * α)) • fderiv ℝ V y y‖ ≤ |1 / (2 * α)| * (|C1| * w) := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    calc ‖fderiv ℝ V y y‖ ≤ ‖fderiv ℝ V y‖ * ‖y‖ := (fderiv ℝ V y).le_opNorm y
      _ ≤ (|C1| * u) * ‖y‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
      _ = |C1| * (u * ‖y‖) := by ring
      _ ≤ |C1| * w := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
  have t3 : ‖a • (fderiv ℝ V y (axialTurn y) - axialTurn (V y))‖ ≤ |a| * ((|C1| + |C0|) * w) := by
    rw [norm_smul, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have k1 : ‖fderiv ℝ V y (axialTurn y)‖ ≤ ‖fderiv ℝ V y‖ * ‖y‖ :=
      ((fderiv ℝ V y).le_opNorm _).trans (mul_le_mul_of_nonneg_left (norm_turn_le y) (norm_nonneg _))
    have k2 : ‖fderiv ℝ V y‖ * ‖y‖ ≤ |C1| * w :=
      calc ‖fderiv ℝ V y‖ * ‖y‖ ≤ (|C1| * u) * ‖y‖ := mul_le_mul_of_nonneg_right hd (norm_nonneg _)
        _ = |C1| * (u * ‖y‖) := by ring
        _ ≤ |C1| * w := mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
    calc ‖fderiv ℝ V y (axialTurn y) - axialTurn (V y)‖
        ≤ ‖fderiv ℝ V y (axialTurn y)‖ + ‖axialTurn (V y)‖ := norm_sub_le _ _
      _ ≤ |C1| * w + |C0| * w := add_le_add (k1.trans k2) ((norm_turn_le _).trans hv)
      _ = (|C1| + |C0|) * w := by ring
  have t4 : ‖(1 : ℝ) • fractionalPowerAt α V y‖ ≤ |CA| * w := by rw [one_smul]; exact hp
  have t5 : ‖advectionAt V y‖ ≤ |C1| * |C0| * w := by
    unfold advectionAt
    have hu1 : u ≤ 1 := e2.trans e4
    calc ‖fderiv ℝ V y (V y)‖ ≤ ‖fderiv ℝ V y‖ * ‖V y‖ := (fderiv ℝ V y).le_opNorm _
      _ ≤ (|C1| * u) * (|C0| * w) := mul_le_mul hd hv (norm_nonneg _) (by positivity)
      _ ≤ (|C1| * 1) * (|C0| * w) := by gcongr
      _ = |C1| * |C0| * w := by ring
  rw [hg, norm_neg]
  refine ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add t1 t2)) t3)) t4)) t5)).trans
    (le_of_eq (by ring))

end Breakdown.FracCert.DecayPressure

namespace Breakdown.FracCert

open Breakdown.FundSol Breakdown.FracCert.DecayPressure

theorem pressureDecay_of_parts (hA : PressureModelStatement) (hC : ResidualDivergenceStatement)
    (hB : DecayingGradientVanishesStatement) (h2 : PowerDecayStatement) :
    PressureDecayStatement := by
  intro α hα1 hα2 a U hU hM hD P hP hres j
  obtain ⟨Q, hQ, hQtr, hQd⟩ := hA α hα1 hα2 a U hU hM hD
  have hPtr := hC α hα1 hα2 a U hU hM hD P hP hres
  obtain ⟨C0, hC0⟩ := hD 0
  obtain ⟨C1, hC1⟩ := hD 1
  obtain ⟨-, hpow⟩ := h2 α hα1 hα2 a U hU hM hD
  obtain ⟨CA, hCA⟩ := hpow 0
  obtain ⟨CQ, hCQ⟩ := hQd 0
  have e0 : (-(2 * α - 1 + ((0 : ℕ) : ℝ))) = -(2 * α - 1) := by push_cast; ring
  have e1 : (-(2 * α - 1 + ((1 : ℕ) : ℝ))) = -(2 * α) := by push_cast; ring
  have e2 : (-(4 * α - 1 + ((0 : ℕ) : ℝ))) = -(4 * α - 1) := by push_cast; ring
  obtain ⟨K, hK⟩ := grad_bound (a := a) hα1 (profileField U) P hres (C0 := C0) (C1 := C1)
    (CA := CA)
    (fun y => by have h := hC0 y; rw [e0, norm_iteratedFDeriv_zero] at h; exact h)
    (fun y => by have h := hC1 y; rw [e1, norm_iteratedFDeriv_one] at h; exact h)
    (fun y => by have h := hCA y; rw [e2, norm_iteratedFDeriv_zero] at h; exact h)
  have hPd : Differentiable ℝ P := hP.differentiable (by simp)
  have hQdf : Differentiable ℝ Q := hQ.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (P - Q) y = fderiv ℝ P y - fderiv ℝ Q y :=
    fun y => fderiv_sub (hPd y) (hQdf y)
  have htr : ∀ y, scalarSumSecondPartials (P - Q) y = 0 := by
    intro y
    have e : iteratedFDeriv ℝ 2 (P - Q) y = iteratedFDeriv ℝ 2 P y - iteratedFDeriv ℝ 2 Q y :=
      iteratedFDeriv_sub_apply (hP.contDiffAt.of_le ENat.LEInfty.out)
        (hQ.contDiffAt.of_le ENat.LEInfty.out)
    have hp := hPtr y
    have hq := hQtr y
    simp only [scalarSumSecondPartials, secondPartial] at hp hq ⊢
    simp only [e, ContinuousMultilinearMap.sub_apply, Finset.sum_sub_distrib, hp, hq, sub_self]
  have hgr : ∀ y, ‖fderiv ℝ (P - Q) y‖ ≤ (K + |CQ|) * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
    intro y
    obtain ⟨-, -, w3, -, w5⟩ := weight_facts α ‖y‖ hα1 (norm_nonneg y)
    rw [hfd y]
    have hq : ‖fderiv ℝ Q y‖ ≤ |CQ| * (1 + ‖y‖) ^ (-(2 * α - 1)) := by
      have h := hCQ y
      rw [e2, norm_iteratedFDeriv_one] at h
      exact h.trans (mul_le_mul (le_abs_self _) w3 (Real.rpow_nonneg (by positivity) _)
        (abs_nonneg _))
    have hp : ‖fderiv ℝ P y‖ ≤ K * (1 + ‖y‖) ^ (-(2 * α - 1)) :=
      (norm_fderiv_le_grad P y).trans (hK y)
    calc ‖fderiv ℝ P y - fderiv ℝ Q y‖ ≤ ‖fderiv ℝ P y‖ + ‖fderiv ℝ Q y‖ := norm_sub_le _ _
      _ ≤ K * (1 + ‖y‖) ^ (-(2 * α - 1)) + |CQ| * (1 + ‖y‖) ^ (-(2 * α - 1)) := add_le_add hp hq
      _ = (K + |CQ|) * (1 + ‖y‖) ^ (-(2 * α - 1)) := by ring
  have h0 := hB (P - Q) (hP.sub hQ) htr (K + |CQ|) (2 * α - 1) (by linarith) hgr
  have hfun : fderiv ℝ P = fderiv ℝ Q := by
    funext y
    have h := h0 y
    rw [hfd y] at h
    exact sub_eq_zero.1 h
  obtain ⟨C, hCj⟩ := hQd j
  refine ⟨C, fun y => ?_⟩
  rw [← norm_iteratedFDeriv_fderiv, hfun, norm_iteratedFDeriv_fderiv]
  exact hCj y

theorem pressureDecay_of_model (hA : PressureModelStatement) (hPow : PowerDivergenceFreeStatement)
    (h2 : PowerDecayStatement) (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) :
    PressureDecayStatement :=
  pressureDecay_of_parts hA (residualDivergence_of hPow h2 h3 h4)
    DecayPressureVanish.decayingGradientVanishes h2

theorem pressureDecay_of_pressureModel (hA : PressureModelStatement) (h2 : PowerDecayStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) : PressureDecayStatement :=
  pressureDecay_of_model hA (powerDivergenceFree_of h3) h2 h3 h4

theorem pressureModel_of (hL : PressureTraceStatement) (hM : ModelPressureDecayStatement)
    (h3 : SymbolL1OfMomentsStatement) : PressureModelStatement :=
  fun α hα1 hα2 a U hU hmo hD =>
    ⟨profilePressure U, pressureSmooth_of h3 U hmo, hL α hα1 hα2 a U hU hmo hD,
      hM α hα1 hα2 a U hU hmo hD⟩

theorem pressureDecay_of_split (hL : PressureTraceStatement) (hM : ModelPressureDecayStatement)
    (h2 : PowerDecayStatement) (h3 : SymbolL1OfMomentsStatement)
    (h4 : FieldSmoothOfMomentsStatement) : PressureDecayStatement :=
  pressureDecay_of_pressureModel (pressureModel_of hL hM h3) h2 h3 h4

theorem pressureDecay_of_reduced (h1 : HomogeneousMultiplierStatement) (h2 : PowerDecayStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement)
    (hP : ProductWeightedSmoothStatement) (hR : PressureRepresentationStatement) :
    PressureDecayStatement :=
  pressureDecay_of_split (DecayPressureTrace.pressureTrace_of h3 h4)
    (DecayPressureModel.modelPressureDecay_of h1 hP hR) h2 h3 h4

theorem pressureDecay_of_representation (h1 : HomogeneousMultiplierStatement)
    (h2 : PowerDecayStatement) (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement)
    (hR : PressureRepresentationStatement) : PressureDecayStatement :=
  pressureDecay_of_reduced h1 h2 h3 h4 (DecayPressureTrace.productWeightedSmooth_of h3 h4) hR

theorem pressureDecay_of (h1 : HomogeneousMultiplierStatement) (h2 : PowerDecayStatement)
    (h3 : SymbolL1OfMomentsStatement) (h4 : FieldSmoothOfMomentsStatement) :
    PressureDecayStatement :=
  pressureDecay_of_representation h1 h2 h3 h4 (DecayPressureRep.pressureRepresentation_of h3)

end Breakdown.FracCert

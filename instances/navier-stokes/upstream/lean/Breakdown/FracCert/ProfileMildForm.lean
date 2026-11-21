import Breakdown.FracCert.DecayFixedPointParts
import Breakdown.FracCert.ProfileMildFormParts
import Breakdown.FracCert.MildNiceHeat
import Breakdown.FracCert.WeakNiceSim
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.Frac.PAxial
import Breakdown.Frac.NNiceEmbed
import Breakdown.FreqTr.Rotation
import Breakdown.FracCert.WeakSimDeriv

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace ProfileMildFormInternal

theorem simAdj_one (α a : ℝ) (φ : Space → Space) : simAdj α a 1 φ = φ := by
  funext y
  simp [simAdj, pushForward, axialRotationSpec.2.1]
  rfl

theorem heatField_zero (α : ℝ) {φ : Space → Space} (hφ : IsNiceField φ) : heatField α 0 φ = φ := by
  obtain ⟨m, hm, rfl⟩ := hφ
  rw [MildNiceHeatInternal.heatField_niceField α 0 hm]
  congr 1
  funext ξ
  simp [MildNiceHeatInternal.heatSym]

theorem orbit_zero (α a : ℝ) (x : X) {φ : Space → Space} (hφ : IsNiceField φ) :
    orbitPairing α a x φ 0 = ∫ y, inner ℝ ((velocity x : Space → Space) y) (φ y) := by
  simp only [orbitPairing, neg_zero, Real.exp_zero, sub_self, simAdj_one, heatField_zero α hφ]

theorem nice_orbit (α a : ℝ) (hα : 1 < α) {φ : Space → Space} (hφ : IsNiceField φ) {τ : ℝ}
    (hτ : 0 ≤ τ) : IsNiceField (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ)) := by
  have h1 : 0 ≤ 1 - Real.exp (-τ) := by
    have : Real.exp (-τ) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  exact (niceHeat α _ hα h1 _ (niceSimAdjClosed α a _ (by linarith) (Real.exp_pos τ) φ hφ)).1

theorem pairing_symbol (x : X) {n : Space → CSpace} (hn : IsNiceSymbol n) :
    ∫ y, inner ℝ ((velocity x : Space → Space) y) (niceField n y) = symbolPairing (x : L2C) n := by
  rw [← MildNiceHeatInternal.negTrace_traceInv hn,
    ← MildNiceHeatInternal.pairing_nice ⟨_, MildNiceHeatInternal.isNiceSymbol_traceInv hn, rfl⟩,
    Submodule.coe_inner, MeasureTheory.L2.inner_def, symbolPairing]
  apply integral_congr_ae
  filter_upwards [niceEmbedSymbol _ (MildNiceHeatInternal.isNiceSymbol_traceInv hn)] with ξ hξ
  rw [hξ, smul_smul]
  congr 2
  simp only [MildNiceHeatInternal.traceInv, sspFactor]
  by_cases h : ‖ξ‖ = 0
  · simp [h]
  · field_simp
    ring

theorem orbit_field (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (τ : ℝ) :
    IsNiceSymbol (orbitSymbol α a m τ) ∧
      heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) (niceField m)) =
        niceField (orbitSymbol α a m τ) := by
  have hl : 0 < Real.exp τ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos (Real.exp_pos τ) _
  have hn := Internal.WeakNiceSim.nice_rot (axialRotation (-(a * τ)))
    (Internal.WeakNiceSim.nice_const (Internal.WeakNiceSim.nice_dilate (inv_pos.2 hl) hm)
      (Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3))
  have hs : simAdj α a (Real.exp τ) (niceField m) = niceField (fun ξ => rotC (axialRotation (-(a * τ)))
      ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
        m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ))) := by
    funext y
    have h := Internal.WeakNiceSim.transport (axialRotation (-(a * τ)))
      (Real.exp τ ^ (4 * (1 / (2 * α)) - 1)) hl m y
    simp only [simAdj, pushForward, Real.log_exp]
    exact h
  exact ⟨MildNiceHeatInternal.isNiceSymbol_heat α _ hn,
    by rw [hs, MildNiceHeatInternal.heatField_niceField α _ hn]; rfl⟩

open Breakdown.FracInternal.NiceField Breakdown.FracInternal.NiceDrift in
theorem nice_drift (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    IsNiceSymbol (driftSym α a m) := by
  have hs := (driftS α a (symbolS hm)).smooth ⊤
  rw [driftS_apply α a hm] at hs
  refine ⟨hs, ?_, ?_, driftSym_conj α a hm, driftSym_div α a hm⟩
  · exact HasCompactSupport.intro' hm.2.1 (isClosed_tsupport m) fun ξ hξ =>
      driftSym_zero α a (notMem_tsupport_iff_eventuallyEq.1 hξ)
  · obtain ⟨r, hr, hz⟩ := hm.2.2.1
    refine ⟨r, hr, fun ξ hξ => driftSym_zero α a ?_⟩
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hξ] with y hy
    exact hz y hy

theorem orbitPairing_eq (α a : ℝ) (x : X) {m : Space → CSpace} (hm : IsNiceSymbol m) :
    orbitPairing α a x (niceField m) = fun τ => symbolPairing (x : L2C) (orbitSymbol α a m τ) := by
  funext τ
  rw [orbitPairing, (orbit_field α a hm τ).2]
  exact pairing_symbol x (orbit_field α a hm τ).1

theorem orbitGenerator_eq {α : ℝ} (a : ℝ) (hα : 1 < α) (hα2 : α < 5 / 4) (x : X) {m : Space → CSpace}
    (hm : IsNiceSymbol m) :
    orbitGenerator α a x (niceField m) = orbitSymbolGenerator α a (x : L2C) m := by
  funext τ
  obtain ⟨hn, he⟩ := orbit_field α a hm τ
  rw [orbitGenerator, he, Breakdown.FracInternal.NiceDrift.drift_eq α a hn,
    Breakdown.FracInternal.NiceDrift.driftS_apply α a hn,
    fracPower_niceField α hα (by linarith) _ hn, pairing_symbol x (nice_drift α a hn),
    pairing_symbol x (FracInternal.NiceEmbed.isNiceSymbol_frac α hn), orbitSymbolGenerator]

theorem orbitPairingDeriv_of (h : OrbitSymbolDerivStatement) : OrbitPairingDerivStatement := by
  rintro α a h1 h2 x φ ⟨m, hm, rfl⟩ τ hτ
  rw [orbitPairing_eq α a x hm, orbitGenerator_eq a h1 h2 x hm]
  exact h α a h1 h2 _ (Lp.memLp _) m hm τ hτ

theorem orbitGeneratorIntegrable_of (h : OrbitSymbolIntegrableStatement) :
    OrbitGeneratorIntegrableStatement := by
  rintro α a h1 h2 x φ ⟨m, hm, rfl⟩
  rw [orbitGenerator_eq a h1 h2 x hm]
  exact h α a h1 h2 _ (Lp.memLp _) m hm

theorem orbitPairingLimit_of (h : OrbitSymbolLimitStatement) : OrbitPairingLimitStatement := by
  rintro α a h1 h2 x φ ⟨m, hm, rfl⟩
  rw [orbitPairing_eq α a x hm]
  exact h α a h1 h2 _ (Lp.memLp _) m hm

theorem heat_le (α : ℝ) (hα : 1 < α) {τ : ℝ} (hτ : 1 ≤ τ) (ξ : Space) :
    Real.exp (-((1 - Real.exp (-τ)) * (2 * π * ‖ξ‖) ^ (2 * α))) ≤ 4 * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
  set P := (2 * π * ‖ξ‖) ^ (2 * α) with hPdef
  set t := ‖ξ‖ with htdef
  have ht0 : 0 ≤ t := norm_nonneg _
  have hP0 : 0 ≤ P := by positivity
  have he1 : Real.exp (-1) * Real.exp 1 = 1 := by rw [← Real.exp_add]; simp
  have hd9 := Real.exp_one_gt_d9
  have he : Real.exp (-τ) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  have he2 : Real.exp (-1) < 1 / 2 := by nlinarith [Real.exp_pos (-1)]
  have hE1 : Real.exp (-((1 - Real.exp (-τ)) * P)) ≤ Real.exp (-(P / 2)) :=
    Real.exp_le_exp.2 (by nlinarith)
  have hE2 : Real.exp (-(P / 2)) ≤ (1 + P / 2)⁻¹ := by
    rw [Real.exp_neg]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (P / 2)])
  have htP : t ^ 2 ≤ 1 + P := by
    by_cases ht : t ≤ 1
    · nlinarith
    · rw [not_le] at ht
      have h1 : t ^ 2 ≤ t ^ (2 * α) := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le ht.le (by push_cast; linarith)
      have h2 : t ^ (2 * α) ≤ P := by
        rw [hPdef, Real.mul_rpow (by positivity) ht0]
        have : 1 ≤ (2 * π) ^ (2 * α) := Real.one_le_rpow (by nlinarith [Real.pi_gt_three]) (by linarith)
        nlinarith [Real.rpow_nonneg ht0 (2 * α)]
      linarith
  have hq : (1 + P / 2)⁻¹ * (1 + t) ^ 2 ≤ 4 := by
    rw [inv_mul_le_iff₀ (by positivity)]
    nlinarith
  have hq2 : (1 + P / 2)⁻¹ ≤ 4 * ((1 + t) ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ (by positivity)]
    exact hq
  linarith

theorem coef_le (α : ℝ) (hα : 1 < α) {τ : ℝ} (hτ : 0 ≤ τ) :
    Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3 ≤ 1 := by
  rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add,
    Real.exp_le_one_iff]
  have h3 : τ * (4 * (1 / (2 * α)) - 1) + ((3 : ℕ) : ℝ) * -(τ * (1 / (2 * α))) =
      τ * (1 / (2 * α) - 1) := by push_cast; ring
  rw [h3]
  have : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact mul_nonpos_of_nonneg_of_nonpos hτ (by linarith)

theorem symbol_bound (α a : ℝ) (hα : 1 < α) {m : Space → CSpace} {M r : ℝ}
    (hM : ∀ ξ, ‖m ξ‖ ≤ M) (hr : 0 < r) (hz : ∀ ξ : Space, ‖ξ‖ < r → m ξ = 0)
    {τ : ℝ} (hτ : 1 ≤ τ) (ξ : Space) :
    ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • orbitSymbol α a m τ ξ‖ ≤
      M * (2 * π * r)⁻¹ * 4 * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hl1 : 1 ≤ Real.exp τ ^ (1 / (2 * α)) :=
    Real.one_le_rpow (Real.one_le_exp (by linarith)) (by apply div_nonneg <;> linarith)
  have hl0 : 0 < Real.exp τ ^ (1 / (2 * α)) := by linarith
  by_cases hmz : m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ) = 0
  · simp only [orbitSymbol, hmz, smul_zero, map_zero, norm_zero]
    positivity
  · have hzr : r ≤ ‖(Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ‖ :=
      not_lt.1 (fun h => hmz (hz _ h))
    rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (by positivity)] at hzr
    have hξr : r ≤ ‖ξ‖ := hzr.trans (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hl1))
    have hc := coef_le α hα (τ := τ) (by linarith)
    have hE := heat_le α hα hτ ξ
    have hw : (2 * π * ‖ξ‖)⁻¹ ≤ (2 * π * r)⁻¹ :=
      inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos])
    rw [orbitSymbol, norm_smul, norm_smul, Internal.Rotation.norm_rotC, norm_smul,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (2 * π * ‖ξ‖)⁻¹),
      Real.norm_of_nonneg (Real.exp_pos _).le,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp τ ^ (4 * (1 / (2 * α)) - 1) *
        (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3)]
    calc (2 * π * ‖ξ‖)⁻¹ * (Real.exp (-((1 - Real.exp (-τ)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
          ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) *
            ‖m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)‖))
        ≤ (2 * π * r)⁻¹ * ((4 * ((1 + ‖ξ‖) ^ 2)⁻¹) * (1 * M)) := by
          gcongr
          exact hM _
      _ = M * (2 * π * r)⁻¹ * 4 * ((1 + ‖ξ‖) ^ 2)⁻¹ := by ring

theorem symbol_eventually_zero (α a : ℝ) (hα : 1 < α) {m : Space → CSpace} {r : ℝ} (hr : 0 < r)
    (hz : ∀ ξ : Space, ‖ξ‖ < r → m ξ = 0) (ξ : Space) :
    ∀ᶠ τ in atTop, m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ) = 0 := by
  have hα0 : 0 < 2 * α := by linarith
  filter_upwards [eventually_gt_atTop (2 * α * (‖ξ‖ / r)), eventually_ge_atTop 0] with τ hτ hτ0
  apply hz
  have hl0 : 0 < Real.exp τ ^ (1 / (2 * α)) := Real.rpow_pos_of_pos (Real.exp_pos τ) _
  rw [norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (inv_pos.2 hl0).le,
    inv_mul_lt_iff₀ hl0]
  have h1 : ‖ξ‖ / r < τ * (1 / (2 * α)) := by
    rw [mul_one_div, lt_div_iff₀ hα0]
    linarith
  have h2 : ‖ξ‖ < τ * (1 / (2 * α)) * r := (div_lt_iff₀ hr).1 h1
  have h3 : τ * (1 / (2 * α)) < Real.exp τ ^ (1 / (2 * α)) := by
    rw [← Real.exp_mul]
    linarith [Real.add_one_le_exp (τ * (1 / (2 * α)))]
  nlinarith

open Breakdown.FracInternal.NiceDrift in
theorem driftSym_eq (α a : ℝ) (n : Space → CSpace) (ξ : Space) :
    driftSym α a n ξ = (1 - 1 / (2 * α)) • n ξ + (1 / (2 * α)) • fderiv ℝ n ξ ξ -
      a • (fderiv ℝ n ξ (axialTurn ξ) - turnC (n ξ)) := by
  have h1 := congrArg (fderiv ℝ n ξ) (vec_expand ξ)
  rw [map_sum] at h1
  simp only [map_smul] at h1
  have h2 := congrArg (fderiv ℝ n ξ) (turn_expand ξ)
  rw [map_add, map_smul, map_smul] at h2
  rw [driftSym, h1, h2]
  simp only [Fin.sum_univ_three]
  module

open Breakdown.FracInternal.NiceDrift in
theorem rot_turn (θ : ℝ) (y : Space) :
    axialRotation θ (axialTurn y) = axialTurn (axialRotation θ y) := by
  rw [axialRotationSpec.1, axialRotationSpec.1]
  ext i
  fin_cases i <;> simp [axialRotationFormula, axialTurn] <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem turnC_rotC (θ : ℝ) (w : CSpace) :
    turnC (rotC (axialRotation θ) w) = rotC (axialRotation θ) (turnC w) := by
  ext i
  fin_cases i <;> simp [Internal.Rotation.rotC_apply, turnC_0, turnC_1, turnC_2, axialRotationSpec.1,
    axialRotationFormula, unitVector, Fin.sum_univ_three] <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem rpow_form (α : ℝ) (ξ : Space) :
    (2 * π * ‖ξ‖) ^ (2 * α) = (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α := by
  rw [Real.rpow_mul (by positivity)]
  congr 1
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

open Breakdown.FracInternal.NiceDrift in
theorem fderiv_orbit (α a : ℝ) (hα : 1 < α) {m : Space → CSpace} (hm : Differentiable ℝ m)
    (τ : ℝ) (ξ v : Space) :
    fderiv ℝ (orbitSymbol α a m τ) ξ v =
      Real.exp (-((1 - Real.exp (-τ)) * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α)) •
          rotC (axialRotation (-(a * τ)))
            ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
              fderiv ℝ m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)
                ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm v)) +
        (Real.exp (-((1 - Real.exp (-τ)) * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α)) *
          -((1 - Real.exp (-τ)) * (α * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ (α - 1) * (4 * π ^ 2 * (2 * inner ℝ ξ v))))) •
          rotC (axialRotation (-(a * τ)))
            ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
              m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)) := by
  have hfun : orbitSymbol α a m τ = fun ξ =>
      Real.exp (-((1 - Real.exp (-τ)) * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α)) •
        rotC (axialRotation (-(a * τ)))
          ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
            m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)) := by
    funext ξ
    rw [orbitSymbol, rpow_form]
  have hQ := (((hasFDerivAt_id ξ).norm_sq).const_mul (4 * π ^ 2)).rpow_const
    (p := α) (Or.inr hα.le)
  have hE := ((hQ.const_mul (1 - Real.exp (-τ))).neg).exp
  have hz : HasFDerivAt (fun ξ : Space => (Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)
      ((Real.exp τ ^ (1 / (2 * α)))⁻¹ •
        ((axialRotation (-(a * τ))).symm.toContinuousLinearEquiv : Space →L[ℝ] Space)) ξ :=
    (((axialRotation (-(a * τ))).symm.toContinuousLinearEquiv : Space →L[ℝ] Space).hasFDerivAt (x := ξ)).const_smul
      ((Real.exp τ ^ (1 / (2 * α)))⁻¹)
  have hg := (rotC (axialRotation (-(a * τ)))).hasFDerivAt.comp ξ
    (((hm _).hasFDerivAt.comp ξ hz).const_smul
      (Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3))
  have h' : HasFDerivAt (fun ξ => Real.exp (-((1 - Real.exp (-τ)) * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α)) •
        rotC (axialRotation (-(a * τ)))
          ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
            m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ))) _ ξ := hE.smul hg
  rw [hfun, h'.fderiv]
  simp

open Breakdown.FracInternal.NiceDrift in
theorem driftSym_orbit (α a : ℝ) (hα : 1 < α) {m : Space → CSpace} (hm : Differentiable ℝ m)
    (τ : ℝ) (ξ : Space) :
    driftSym α a (orbitSymbol α a m τ) ξ =
      Real.exp (-((1 - Real.exp (-τ)) * (2 * π * ‖ξ‖) ^ (2 * α))) •
        rotC (axialRotation (-(a * τ)))
          ((Real.exp τ ^ (4 * (1 / (2 * α)) - 1) * (Real.exp τ ^ (1 / (2 * α)))⁻¹ ^ 3) •
            ((1 - 1 / (2 * α) - (1 - Real.exp (-τ)) * (2 * π * ‖ξ‖) ^ (2 * α)) •
                m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ) +
              (1 / (2 * α)) • fderiv ℝ m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)
                ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ) -
              a • (fderiv ℝ m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)
                  (axialTurn ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ)) -
                turnC (m ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ))))) := by
  have hα0 : α ≠ 0 := by linarith
  have h1 : inner ℝ ξ (axialTurn ξ) = 0 := by
    simp [axialTurn, PiLp.inner_apply, Fin.sum_univ_three]
    ring
  have h2 : inner ℝ ξ ξ = ‖ξ‖ ^ 2 := real_inner_self_eq_norm_sq ξ
  have hQ : α * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ (α - 1) * (4 * π ^ 2 * (2 * ‖ξ‖ ^ 2)) =
      2 * α * (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ α := by
    by_cases hξ : ‖ξ‖ = 0
    · simp [hξ, Real.zero_rpow hα0]
    · have hpos : 0 < 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
      rw [Real.rpow_sub_one hpos.ne']
      field_simp
  have hturn : (Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm (axialTurn ξ) =
      axialTurn ((Real.exp τ ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * τ))).symm ξ) := by
    rw [axialRotationSpec.2.2.2.1, rot_turn, Internal.SimDeriv.turn_smul]
  have hT : ∀ (E c : ℝ) (w : CSpace), turnC (E • rotC (axialRotation (-(a * τ))) (c • w)) =
      E • rotC (axialRotation (-(a * τ))) (c • turnC w) := by
    intro E c w
    rw [ContinuousLinearMap.map_smul_of_tower turnC, turnC_rotC, ContinuousLinearMap.map_smul_of_tower turnC]
  rw [driftSym_eq, fderiv_orbit α a hα hm τ ξ ξ, fderiv_orbit α a hα hm τ ξ (axialTurn ξ), h1, h2,
    hQ, hturn, orbitSymbol, hT, rpow_form]
  simp only [map_add, map_sub, map_smul, mul_zero, neg_zero, zero_smul, add_zero]
  match_scalars <;> field_simp <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem rot_decomp (θ : ℝ) :
    (rotC (axialRotation θ)) = Real.cos θ • (-((turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ))) +
      Real.sin θ • turnC.restrictScalars ℝ +
      (ContinuousLinearMap.id ℝ CSpace + (turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ)) := by
  refine ContinuousLinearMap.ext fun w => ?_
  ext i
  fin_cases i <;> simp [Internal.Rotation.rotC_apply, turnC_0, turnC_1, turnC_2, axialRotationSpec.1,
    axialRotationFormula, unitVector, Fin.sum_univ_three] <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem rot_hasDeriv (θ : ℝ) :
    HasDerivAt (fun θ => rotC (axialRotation θ))
      ((turnC.restrictScalars ℝ).comp (rotC (axialRotation θ))) θ := by
  have h := (((Real.hasDerivAt_cos θ).smul_const
      (-((turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ)))).add
      ((Real.hasDerivAt_sin θ).smul_const (turnC.restrictScalars ℝ))).add_const
      (ContinuousLinearMap.id ℝ CSpace + (turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ))
  have hf : (fun θ => rotC (axialRotation θ)) = fun θ => Real.cos θ • (-((turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ))) +
      Real.sin θ • turnC.restrictScalars ℝ +
      (ContinuousLinearMap.id ℝ CSpace + (turnC.restrictScalars ℝ).comp (turnC.restrictScalars ℝ)) := by
    funext θ
    exact rot_decomp θ
  rw [hf]
  refine h.congr_deriv ?_
  rw [rot_decomp]
  refine ContinuousLinearMap.ext fun w => ?_
  ext i
  fin_cases i <;> simp [turnC_0, turnC_1, turnC_2] <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem orbit_hasDeriv (α a : ℝ) (hα : 1 < α) {m : Space → CSpace} (hm : Differentiable ℝ m)
    (τ : ℝ) (ξ : Space) :
    HasDerivAt (fun s => orbitSymbol α a m s ξ)
      (-driftSym α a (orbitSymbol α a m τ) ξ -
        ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m τ ξ) τ := by
  have hα0 : α ≠ 0 := by linarith
  have hc : ∀ s : ℝ, Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3 =
      Real.exp (s * (1 / (2 * α) - 1)) := by
    intro s
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hl : ∀ s : ℝ, (Real.exp s ^ (1 / (2 * α)))⁻¹ = Real.exp (-(s * (1 / (2 * α)))) := by
    intro s
    rw [← Real.exp_mul, Real.exp_neg]
  have hR : ∀ s : ℝ, (axialRotation (-(a * s))).symm ξ = axialRotation (a * s) ξ := by
    intro s
    rw [axialRotationSpec.2.2.2.1, neg_neg]
  have hfun : (fun s => orbitSymbol α a m s ξ) = fun s =>
      Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) •
        rotC (axialRotation (-(a * s))) (Real.exp (s * (1 / (2 * α) - 1)) •
          m (Real.exp (-(s * (1 / (2 * α)))) • axialRotation (a * s) ξ)) := by
    funext s
    rw [orbitSymbol, hc, hl, hR]
  have hE := ((((hasDerivAt_neg τ).exp).const_sub 1).mul_const ((2 * π * ‖ξ‖) ^ (2 * α))).neg.exp
  have hz := (((hasDerivAt_id' τ).mul_const (1 / (2 * α))).neg.exp).smul
    ((axialRotationSpec.2.2.2.2.2 (a * τ) ξ).scomp τ ((hasDerivAt_id' τ).const_mul a))
  have hmz := (hm _).hasFDerivAt.comp_hasDerivAt τ hz
  have hW := ((hasDerivAt_id' τ).mul_const (1 / (2 * α) - 1)).exp.smul hmz
  have hRot := (rot_hasDeriv (-(a * τ))).scomp τ ((hasDerivAt_id' τ).const_mul a).neg
  have hRW := hRot.clm_apply hW
  have hF := hE.smul hRW
  rw [hfun]
  refine hF.congr_deriv ?_
  simp only [Pi.smul_apply', Pi.smul_apply, Pi.neg_apply, Function.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars']
  rw [driftSym_orbit α a hα hm τ ξ, orbitSymbol, hc τ, hl τ, hR τ,
    Internal.SimDeriv.turn_smul]
  simp only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    map_add, map_sub, map_smul, map_neg, ContinuousLinearMap.map_smul_of_tower turnC, turnC_rotC, smul_add,
    smul_sub, smul_neg]
  match_scalars <;> field_simp <;> ring

open Breakdown.FracInternal.NiceDrift in
theorem weight_integrable {f : Space → CSpace} (hf : MemLp f 2 volume) :
    Integrable (fun ξ : Space => ‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹) := by
  have hfin : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by simp; norm_num
  have hI1 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hI2 := integrable_one_add_norm (E := Space) (μ := volume) hfin
  refine Integrable.mono' (hI1.add hI2) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact hf.1.norm.mul (Measurable.aestronglyMeasurable (by fun_prop))
  · have hq0 : 0 ≤ ((1 + ‖ξ‖) ^ 2)⁻¹ := by positivity
    have hq : (1 + ‖ξ‖) ^ (-(4 : ℝ)) = (((1 + ‖ξ‖) ^ 2)⁻¹) ^ 2 := by
      rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
        inv_pow, ← pow_mul]
    simp only [Pi.add_apply]
    rw [hq, Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hq0)]
    nlinarith [sq_nonneg (‖f ξ‖ - ((1 + ‖ξ‖) ^ 2)⁻¹), norm_nonneg (f ξ), mul_nonneg (norm_nonneg (f ξ)) hq0]

open Breakdown.FracInternal.NiceDrift in
theorem pair_le {f : Space → CSpace} (hf : MemLp f 2 volume) {g : Space → CSpace}
    (hg : AEStronglyMeasurable g volume) {K : ℝ}
    (hK : ∀ ξ : Space, ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ‖ ≤ K * ((1 + ‖ξ‖) ^ 2)⁻¹) :
    Integrable (fun ξ => inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ)) ∧
      |symbolPairing f g| ≤ K * ∫ ξ, ‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
  have hw := weight_integrable hf
  have hb : ∀ ξ : Space, ‖inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ)‖ ≤
      K * (‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹) := by
    intro ξ
    rw [Real.norm_eq_abs]
    calc |inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ)| ≤ ‖f ξ‖ * ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖f ξ‖ * (K * ((1 + ‖ξ‖) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left (hK ξ) (norm_nonneg _)
      _ = K * (‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹) := by ring
  have hmeas : AEStronglyMeasurable (fun ξ => inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • g ξ)) volume :=
    hf.1.inner ((Measurable.aestronglyMeasurable (f := fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ))
      (by fun_prop)).smul hg)
  have hint := Integrable.mono' (hw.const_mul K) hmeas (Eventually.of_forall hb)
  refine ⟨hint, ?_⟩
  rw [symbolPairing, ← Real.norm_eq_abs, ← integral_const_mul]
  exact norm_integral_le_of_norm_le (hw.const_mul K) (Eventually.of_forall hb)

open Breakdown.FracInternal.NiceDrift in
theorem orbit_meas (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (s : ℝ) :
    Measurable (orbitSymbol α a m s) := by
  have := hm.1.continuous.measurable
  unfold orbitSymbol
  fun_prop

open Breakdown.FracInternal.NiceDrift in
theorem drift_meas (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (s : ℝ) :
    Measurable (driftSym α a (orbitSymbol α a m s)) := by
  have hn := orbit_meas α a hm s
  have hd : ∀ v, Measurable (fun ξ => fderiv ℝ (orbitSymbol α a m s) ξ v) :=
    fun v => measurable_fderiv_apply_const ℝ _ v
  unfold driftSym
  fun_prop

open Breakdown.FracInternal.NiceDrift in
theorem power_meas (α a : ℝ) {m : Space → CSpace} (hm : IsNiceSymbol m) (s : ℝ) :
    Measurable (fun ξ : Space => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ) := by
  have hn := orbit_meas α a hm s
  fun_prop

open Breakdown.FracInternal.NiceDrift in
theorem support_facts {m : Space → CSpace} (hm : IsNiceSymbol m) :
    ∃ r R : ℝ, 0 < r ∧ r ≤ R ∧ ∀ z : Space, (‖z‖ < r ∨ R < ‖z‖) → m z = 0 ∧ fderiv ℝ m z = 0 := by
  obtain ⟨r, hr, hz⟩ := hm.2.2.1
  obtain ⟨R, hR⟩ := hm.2.1.isCompact.isBounded.subset_closedBall (0 : Space)
  refine ⟨r, max R r, hr, le_max_right _ _, fun z hzr => ?_⟩
  have hev : m =ᶠ[𝓝 z] 0 := by
    rcases hzr with h | h
    · filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with y hy
      exact hz y hy
    · apply notMem_tsupport_iff_eventuallyEq.1
      intro hmem
      have := hR hmem
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R r]
  refine ⟨hev.eq_of_nhds, ?_⟩
  rw [hev.fderiv_eq]
  simp

open Breakdown.FracInternal.NiceDrift in
theorem bracket_le (α a : ℝ) (hα : 1 < α) {M M2 t P : ℝ} (hP : 0 ≤ P) (ht : |t| ≤ 2)
    (hM0 : 0 ≤ M) (hM20 : 0 ≤ M2) (u : Space) (w : CSpace) (L : Space →L[ℝ] CSpace)
    (hw : ‖w‖ ≤ M) (hL : ‖u‖ * ‖L‖ ≤ M2) :
    ‖(1 - 1 / (2 * α) - t * P) • w + (1 / (2 * α)) • L u - a • (L (axialTurn u) - turnC w)‖ ≤
      (1 + 2 * P) * (M + M2 + |a| * (M2 + ‖turnC‖ * M)) := by
  have hk0 : 0 < 1 / (2 * α) := by positivity
  have hk1 : 1 / (2 * α) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1 : ‖(1 - 1 / (2 * α) - t * P) • w‖ ≤ (1 + 2 * P) * M := by
    rw [norm_smul, Real.norm_eq_abs]
    have : |1 - 1 / (2 * α) - t * P| ≤ 1 + 2 * P := by
      have htP : |t * P| ≤ 2 * P := by rw [abs_mul, abs_of_nonneg hP]; nlinarith [abs_nonneg t]
      calc |1 - 1 / (2 * α) - t * P| ≤ |1 - 1 / (2 * α)| + |t * P| := abs_sub _ _
        _ ≤ 1 + 2 * P := by
          rw [abs_of_pos (by linarith : (0:ℝ) < 1 - 1 / (2 * α))]
          linarith
    exact mul_le_mul this hw (norm_nonneg _) (by positivity)
  have hLu : ‖L u‖ ≤ M2 := (L.le_opNorm u).trans (by rw [mul_comm]; exact hL)
  have hLt : ‖L (axialTurn u)‖ ≤ M2 := (L.le_opNorm _).trans (by
    calc ‖L‖ * ‖axialTurn u‖ ≤ ‖L‖ * ‖u‖ :=
          mul_le_mul_of_nonneg_left (Internal.SimDeriv.norm_turn_le u) (norm_nonneg _)
      _ ≤ M2 := by rw [mul_comm]; exact hL)
  have h2 : ‖(1 / (2 * α)) • L u‖ ≤ M2 := by
    rw [norm_smul, Real.norm_of_nonneg hk0.le]
    nlinarith [norm_nonneg (L u)]
  have hT : ‖turnC w‖ ≤ ‖turnC‖ * M :=
    (turnC.le_opNorm w).trans (mul_le_mul_of_nonneg_left hw (norm_nonneg _))
  have h3 : ‖a • (L (axialTurn u) - turnC w)‖ ≤ |a| * (M2 + ‖turnC‖ * M) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans (add_le_add hLt hT)) (abs_nonneg a)
  have hA : 0 ≤ |a| * (M2 + ‖turnC‖ * M) := by positivity
  calc _ ≤ ‖(1 - 1 / (2 * α) - t * P) • w‖ + ‖(1 / (2 * α)) • L u‖ + ‖a • (L (axialTurn u) - turnC w)‖ :=
        (norm_sub_le _ _).trans (by linarith [norm_add_le ((1 - 1 / (2 * α) - t * P) • w) ((1 / (2 * α)) • L u)])
    _ ≤ (1 + 2 * P) * M + M2 + |a| * (M2 + ‖turnC‖ * M) := by linarith
    _ ≤ _ := by nlinarith

def decayEnvelope (α r R s : ℝ) : ℝ :=
  (2 * π * r)⁻¹ * Real.exp (-s) * (1 + R * Real.exp (s * (1 / (2 * α)))) ^ 2 *
    (1 + 2 * ((2 * π * R) ^ (2 * α) * Real.exp s)) *
    (Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) +
      Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1))))

theorem scalar_le (α : ℝ) (hα : 1 < α) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s ρ : ℝ}
    (hlo : r * Real.exp s ^ (1 / (2 * α)) ≤ ρ) (hhi : ρ ≤ R * Real.exp s ^ (1 / (2 * α))) :
    (2 * π * ρ)⁻¹ * Real.exp (-((1 - Real.exp (-s)) * (2 * π * ρ) ^ (2 * α))) *
        (Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
        (1 + 2 * (2 * π * ρ) ^ (2 * α)) * (1 + ρ) ^ 2 ≤ decayEnvelope α r R s := by
  have hα0 : 0 < 2 * α := by linarith
  have hL : Real.exp s ^ (1 / (2 * α)) = Real.exp (s * (1 / (2 * α))) := (Real.exp_mul _ _).symm
  have hc : Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3 =
      Real.exp (-s) * Real.exp (s * (1 / (2 * α))) := by
    rw [← Real.exp_mul, ← Real.exp_mul, ← Real.exp_neg, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  rw [hL] at hlo hhi
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  have hAR : 0 ≤ (2 * π * R) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
  have hL0 : 0 < Real.exp (s * (1 / (2 * α))) := Real.exp_pos _
  have hLp : Real.exp (s * (1 / (2 * α))) ^ (2 * α) = Real.exp s := by
    rw [← Real.exp_mul]
    congr 1
    field_simp
  have hρ : 0 < ρ := lt_of_lt_of_le (by positivity) hlo
  have hPlo : (2 * π * r) ^ (2 * α) * Real.exp s ≤ (2 * π * ρ) ^ (2 * α) := by
    rw [← hLp, ← Real.mul_rpow (by positivity) hL0.le]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) hα0.le
  have hPhi : (2 * π * ρ) ^ (2 * α) ≤ (2 * π * R) ^ (2 * α) * Real.exp s := by
    rw [← hLp, ← Real.mul_rpow (by positivity) hL0.le]
    exact Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) hα0.le
  have hE : Real.exp (-((1 - Real.exp (-s)) * (2 * π * ρ) ^ (2 * α))) ≤
      Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) +
        Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1))) := by
    have hes : (1 - Real.exp (-s)) * Real.exp s = Real.exp s - 1 := by
      rw [sub_mul, one_mul, ← Real.exp_add]
      simp
    by_cases ht : 0 ≤ 1 - Real.exp (-s)
    · have : Real.exp (-((1 - Real.exp (-s)) * (2 * π * ρ) ^ (2 * α))) ≤
          Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) := by
        apply Real.exp_le_exp.2
        rw [← hes]
        nlinarith [mul_le_mul_of_nonneg_left hPlo ht]
      linarith [Real.exp_pos (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1)))]
    · push Not at ht
      have : Real.exp (-((1 - Real.exp (-s)) * (2 * π * ρ) ^ (2 * α))) ≤
          Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1))) := by
        apply Real.exp_le_exp.2
        rw [← hes]
        nlinarith [mul_le_mul_of_nonpos_left hPhi ht.le]
      linarith [Real.exp_pos (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1)))]
  have hw : (2 * π * ρ)⁻¹ ≤ (2 * π * r)⁻¹ * (Real.exp (s * (1 / (2 * α))))⁻¹ := by
    rw [← mul_inv]
    exact inv_anti₀ (by positivity) (by nlinarith [Real.pi_pos])
  rw [hc]
  calc _ ≤ (2 * π * r)⁻¹ * (Real.exp (s * (1 / (2 * α))))⁻¹ *
        (Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) +
          Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1)))) *
        (Real.exp (-s) * Real.exp (s * (1 / (2 * α)))) * (1 + 2 * ((2 * π * R) ^ (2 * α) * Real.exp s)) *
        (1 + R * Real.exp (s * (1 / (2 * α)))) ^ 2 := by
        gcongr
    _ = decayEnvelope α r R s := by
        unfold decayEnvelope
        field_simp

theorem cube_exp_le {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) : u ^ 3 * Real.exp (-(A * u)) ≤ 6 / A ^ 3 := by
  have h := Real.pow_div_factorial_le_exp (A * u) (mul_nonneg hA.le hu) 3
  have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
  rw [h6] at h
  have h' : (A * u) ^ 3 ≤ 6 * Real.exp (A * u) := by linarith
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ (Real.exp_pos _) (pow_pos hA 3)]
  rw [mul_pow] at h'
  linarith

theorem bnd_le (α : ℝ) (hα : 1 < α) {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) {s : ℝ} (hs : 0 ≤ s) :
    decayEnvelope α r R s ≤ ((2 * π * r)⁻¹ * (1 + R) ^ 2 * (1 + 2 * (2 * π * R) ^ (2 * α)) * 2 *
      Real.exp ((2 * π * r) ^ (2 * α)) * (6 / ((2 * π * r) ^ (2 * α)) ^ 3)) * Real.exp (-s) := by
  have hR0 : 0 < R := lt_of_lt_of_le hr hrR
  have hAr : 0 < (2 * π * r) ^ (2 * α) := Real.rpow_pos_of_pos (by positivity) _
  have hArR : (2 * π * r) ^ (2 * α) ≤ (2 * π * R) ^ (2 * α) :=
    Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos]) (by linarith)
  have hu1 : 1 ≤ Real.exp s := Real.one_le_exp hs
  have hk : Real.exp (s * (1 / (2 * α))) ≤ Real.exp s := by
    apply Real.exp_le_exp.2
    have : 1 / (2 * α) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    nlinarith
  have h1 : (1 + R * Real.exp (s * (1 / (2 * α)))) ^ 2 ≤ ((1 + R) * Real.exp s) ^ 2 := by
    have : 1 + R * Real.exp (s * (1 / (2 * α))) ≤ (1 + R) * Real.exp s := by nlinarith
    exact pow_le_pow_left₀ (by positivity) this 2
  have h2 : 1 + 2 * ((2 * π * R) ^ (2 * α) * Real.exp s) ≤ (1 + 2 * (2 * π * R) ^ (2 * α)) * Real.exp s := by
    nlinarith
  have h3 : Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) +
      Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1))) ≤
      2 * Real.exp ((2 * π * r) ^ (2 * α)) * Real.exp (-((2 * π * r) ^ (2 * α) * Real.exp s)) := by
    have e1 : Real.exp (-((2 * π * R) ^ (2 * α) * (Real.exp s - 1))) ≤
        Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) :=
      Real.exp_le_exp.2 (by nlinarith)
    have e2 : Real.exp (-((2 * π * r) ^ (2 * α) * (Real.exp s - 1))) =
        Real.exp ((2 * π * r) ^ (2 * α)) * Real.exp (-((2 * π * r) ^ (2 * α) * Real.exp s)) := by
      rw [← Real.exp_add]
      ring_nf
    linarith
  have h4 := cube_exp_le hAr (Real.exp_pos s).le
  have hpos : 0 ≤ (2 * π * r)⁻¹ * Real.exp (-s) := by positivity
  calc decayEnvelope α r R s ≤ (2 * π * r)⁻¹ * Real.exp (-s) * ((1 + R) * Real.exp s) ^ 2 *
        ((1 + 2 * (2 * π * R) ^ (2 * α)) * Real.exp s) *
        (2 * Real.exp ((2 * π * r) ^ (2 * α)) * Real.exp (-((2 * π * r) ^ (2 * α) * Real.exp s))) := by
        unfold decayEnvelope
        gcongr
    _ = ((2 * π * r)⁻¹ * (1 + R) ^ 2 * (1 + 2 * (2 * π * R) ^ (2 * α)) * 2 *
          Real.exp ((2 * π * r) ^ (2 * α))) *
        (Real.exp s ^ 3 * Real.exp (-((2 * π * r) ^ (2 * α) * Real.exp s))) * Real.exp (-s) := by ring
    _ ≤ ((2 * π * r)⁻¹ * (1 + R) ^ 2 * (1 + 2 * (2 * π * R) ^ (2 * α)) * 2 *
          Real.exp ((2 * π * r) ^ (2 * α))) * (6 / ((2 * π * r) ^ (2 * α)) ^ 3) * Real.exp (-s) := by
        gcongr
    _ = _ := by ring

end ProfileMildFormInternal

open ProfileMildFormInternal in
theorem orbitSymbolLimit : OrbitSymbolLimitStatement := by
  intro α a h1 h2 f hf m hm
  obtain ⟨M, hM⟩ := hm.1.continuous.bounded_above_of_compact_support hm.2.1
  obtain ⟨r, hr, hz⟩ := hm.2.2.1
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hmm : Measurable m := hm.1.continuous.measurable
  set K := M * (2 * π * r)⁻¹ * 4 with hK
  have hK0 : 0 ≤ K := by positivity
  have hfin : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by simp; norm_num
  have hI1 := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hI2 := (integrable_one_add_norm (E := Space) (μ := volume) hfin).const_mul (K ^ 2)
  have hI : Integrable (fun ξ : Space => ‖f ξ‖ ^ 2 + K ^ 2 * ((1 + ‖ξ‖) ^ 4)⁻¹) := by
    refine hI1.add (hI2.congr (Eventually.of_forall fun ξ => ?_))
    simp only
    rw [Real.rpow_neg (by positivity), show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have key := tendsto_integral_filter_of_dominated_convergence (μ := volume) (l := atTop)
    (F := fun τ ξ => inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • orbitSymbol α a m τ ξ))
    (f := fun _ => (0 : ℝ)) (fun ξ => ‖f ξ‖ ^ 2 + K ^ 2 * ((1 + ‖ξ‖) ^ 4)⁻¹) ?_ ?_ hI ?_
  · simpa [symbolPairing] using key
  · refine Eventually.of_forall fun τ => hf.1.inner ?_
    apply Measurable.aestronglyMeasurable
    unfold orbitSymbol
    fun_prop
  · filter_upwards [eventually_ge_atTop 1] with τ hτ
    refine Eventually.of_forall fun ξ => ?_
    have hb := symbol_bound α a h1 hM hr hz hτ ξ
    have hq : ((1 + ‖ξ‖) ^ 4)⁻¹ = (((1 + ‖ξ‖) ^ 2)⁻¹) ^ 2 := by
      rw [inv_pow, ← pow_mul]
    have hq0 : 0 ≤ ((1 + ‖ξ‖) ^ 2)⁻¹ := by positivity
    have hi : ‖inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • orbitSymbol α a m τ ξ)‖ ≤
        ‖f ξ‖ * (K * ((1 + ‖ξ‖) ^ 2)⁻¹) := by
      rw [Real.norm_eq_abs]
      exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
    rw [hq]
    nlinarith [sq_nonneg (‖f ξ‖ - K * ((1 + ‖ξ‖) ^ 2)⁻¹), norm_nonneg (f ξ),
      mul_nonneg (norm_nonneg (f ξ)) (mul_nonneg hK0 hq0)]
  · refine Eventually.of_forall fun ξ => tendsto_const_nhds.congr' ?_
    filter_upwards [symbol_eventually_zero α a h1 hr hz ξ] with τ hτ
    simp only [orbitSymbol, hτ, smul_zero, map_zero, inner_zero_right]


open ProfileMildFormInternal in
theorem profileMildForm_of (hD : OrbitPairingDerivStatement) (hI : OrbitGeneratorIntegrableStatement)
    (hL : OrbitPairingLimitStatement) : ProfileMildFormStatement := by
  intro α h1 h2 a U hW hM φ hφ
  have hF := integral_Ioi_of_hasDerivAt_of_tendsto' (fun τ hτ => hD α a h1 h2 U φ hφ τ hτ)
    (hI α a h1 h2 U φ hφ) (hL α a h1 h2 U φ hφ)
  have heq : ∫ τ in Ioi (0 : ℝ), trilinear U U
      (heatField α (1 - Real.exp (-τ)) (simAdj α a (Real.exp τ) φ)) =
      ∫ τ in Ioi (0 : ℝ), orbitGenerator α a U φ τ := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    have hw := hW.2 _ (nice_orbit α a h1 hφ (le_of_lt hτ))
    simp only [orbitGenerator]
    linarith
  rw [heq, hF, zero_sub, neg_neg, orbit_zero α a U hφ]
  apply integral_congr_ae
  filter_upwards [(symbolL1OfMoments U hM).2] with y hy
  rw [hy, profileField]

open ProfileMildFormInternal in
theorem profileMildForm_of_symbol (hD : OrbitSymbolDerivStatement) (hI : OrbitSymbolIntegrableStatement) :
    ProfileMildFormStatement :=
  profileMildForm_of (orbitPairingDeriv_of hD) (orbitGeneratorIntegrable_of hI)
    (orbitPairingLimit_of orbitSymbolLimit)

open Breakdown.FracInternal.NiceDrift ProfileMildFormInternal in
theorem orbitSymbolDeriv_of (hB : OrbitSymbolBoundStatement) : OrbitSymbolDerivStatement := by
  intro α a h1 h2 f hf m hm τ hτ
  obtain ⟨B, -, hBloc, hBd⟩ := hB α a h1 h2 m hm
  obtain ⟨ε, hε, C, hC⟩ := hBloc τ hτ
  have hmd : Differentiable ℝ m := hm.1.differentiable (by simp)
  have hδ : 0 < min ε 1 := lt_min hε one_pos
  have hball : ∀ s ∈ Metric.ball τ (min ε 1), -1 < s ∧ B s ≤ C := by
    intro s hs
    rw [Metric.mem_ball, Real.dist_eq] at hs
    have h1' : |s - τ| < 1 := hs.trans_le (min_le_right _ _)
    have h2' : |s - τ| < ε := hs.trans_le (min_le_left _ _)
    refine ⟨by linarith [neg_abs_le (s - τ)], hC s ?_⟩
    rw [Metric.mem_ball, Real.dist_eq]
    exact h2'
  have hwm : Measurable (fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ)) := by fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := τ)
    (F := fun s ξ => inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) • orbitSymbol α a m s ξ))
    (F' := fun s ξ => inner ℝ (f ξ) (((2 * π * ‖ξ‖)⁻¹ : ℝ) •
      (-driftSym α a (orbitSymbol α a m s) ξ - ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ)))
    (bound := fun ξ => 2 * max C 0 * (‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹)) (Metric.ball_mem_nhds τ hδ)
    (Eventually.of_forall fun s => hf.1.inner
      (hwm.aestronglyMeasurable.smul (orbit_meas α a hm s).aestronglyMeasurable))
    (pair_le hf (orbit_meas α a hm τ).aestronglyMeasurable
      (fun ξ => (hBd τ (by linarith) ξ).2.2)).1
    (hf.1.inner (hwm.aestronglyMeasurable.smul
      ((drift_meas α a hm τ).neg.sub (power_meas α a hm τ)).aestronglyMeasurable))
    (Eventually.of_forall fun ξ s hs => by
      obtain ⟨hs1, hsC⟩ := hball s hs
      obtain ⟨hb1, hb2, -⟩ := hBd s hs1 ξ
      have hq0 : 0 ≤ ((1 + ‖ξ‖) ^ 2)⁻¹ := by positivity
      have hn : ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) •
          (-driftSym α a (orbitSymbol α a m s) ξ - ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ)‖ ≤
          2 * max C 0 * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
        rw [smul_sub, smul_neg]
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
        have : B s * ((1 + ‖ξ‖) ^ 2)⁻¹ ≤ max C 0 * ((1 + ‖ξ‖) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right (hsC.trans (le_max_left _ _)) hq0
        linarith
      rw [Real.norm_eq_abs]
      calc _ ≤ ‖f ξ‖ * ‖((2 * π * ‖ξ‖)⁻¹ : ℝ) •
            (-driftSym α a (orbitSymbol α a m s) ξ - ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ)‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ‖f ξ‖ * (2 * max C 0 * ((1 + ‖ξ‖) ^ 2)⁻¹) := mul_le_mul_of_nonneg_left hn (norm_nonneg _)
        _ = 2 * max C 0 * (‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹) := by ring)
    ((weight_integrable hf).const_mul _)
    (Eventually.of_forall fun ξ s _ => by
      have h := ((hasDerivAt_const s (f ξ)).inner ℝ
        ((ProfileMildFormInternal.orbit_hasDeriv α a h1 hmd s ξ).const_smul ((2 * π * ‖ξ‖)⁻¹ : ℝ)))
      refine h.congr_deriv ?_
      simp)
  refine key.2.congr_deriv ?_
  have iD := (pair_le hf (drift_meas α a hm τ).aestronglyMeasurable
    (fun ξ => (hBd τ (by linarith) ξ).1)).1
  have iP := (pair_le hf (power_meas α a hm τ).aestronglyMeasurable
    (fun ξ => (hBd τ (by linarith) ξ).2.1)).1
  rw [orbitSymbolGenerator, symbolPairing, symbolPairing, ← integral_neg, ← integral_sub iD.fun_neg iP]
  apply integral_congr_ae
  refine Eventually.of_forall fun ξ => ?_
  simp only [smul_sub, smul_neg, inner_sub_right, inner_neg_right]

open Breakdown.FracInternal.NiceDrift ProfileMildFormInternal in
theorem orbitSymbolIntegrable_of (hB : OrbitSymbolBoundStatement) : OrbitSymbolIntegrableStatement := by
  intro α a h1 h2 f hf m hm
  obtain ⟨B, hBi, -, hBd⟩ := hB α a h1 h2 m hm
  have hD := orbitSymbolDeriv_of hB α a h1 h2 f hf m hm
  have hmeas : AEStronglyMeasurable (orbitSymbolGenerator α a f m) (volume.restrict (Ioi 0)) := by
    refine (measurable_deriv (fun s => symbolPairing f (orbitSymbol α a m s))).aestronglyMeasurable.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    exact (hD s (le_of_lt hs)).deriv
  refine Integrable.mono' ((hBi.mul_const (∫ ξ, ‖f ξ‖ * ((1 + ‖ξ‖) ^ 2)⁻¹)).const_mul 2) hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
  have hs1 : -1 < s := by linarith [hs.out]
  have e1 := (pair_le hf (drift_meas α a hm s).aestronglyMeasurable (fun ξ => (hBd s hs1 ξ).1)).2
  have e2 := (pair_le hf (power_meas α a hm s).aestronglyMeasurable (fun ξ => (hBd s hs1 ξ).2.1)).2
  rw [Real.norm_eq_abs, orbitSymbolGenerator]
  have := abs_sub (-symbolPairing f (driftSym α a (orbitSymbol α a m s)))
    (symbolPairing f (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • orbitSymbol α a m s ξ))
  rw [abs_neg] at this
  linarith

open ProfileMildFormInternal in
theorem profileMildForm_of_bound (hB : OrbitSymbolBoundStatement) : ProfileMildFormStatement :=
  profileMildForm_of_symbol (orbitSymbolDeriv_of hB) (orbitSymbolIntegrable_of hB)

open Breakdown.FracInternal.NiceDrift ProfileMildFormInternal in
theorem orbitSymbolBound_of (hS : OrbitScalarBoundStatement) : OrbitSymbolBoundStatement := by
  intro α a h1 h2 m hm
  obtain ⟨r, R, hr, hrR, hsupp⟩ := support_facts hm
  obtain ⟨M, hM⟩ := hm.1.continuous.bounded_above_of_compact_support hm.2.1
  obtain ⟨M2, hM2⟩ : ∃ M2 : ℝ, ∀ z : Space, ‖z‖ * ‖fderiv ℝ m z‖ ≤ M2 := by
    obtain ⟨C, hC⟩ := (continuous_norm.smul (hm.1.continuous_fderiv (𝕜 := ℝ) (by simp))).bounded_above_of_compact_support
      ((hm.2.1.fderiv (𝕜 := ℝ)).smul_left (f := fun z : Space => ‖z‖))
    refine ⟨C, fun z => ?_⟩
    have := hC z
    rwa [Pi.smul_apply', norm_smul, Real.norm_of_nonneg (norm_nonneg _)] at this
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hM20 : 0 ≤ M2 := le_trans (by positivity) (hM2 0)
  have hmd : Differentiable ℝ m := hm.1.differentiable (by simp)
  have hK0 : 0 ≤ M + M2 + |a| * (M2 + ‖turnC‖ * M) := by positivity
  obtain ⟨B, hBi, hBloc, hBd⟩ := hS α h1 h2 r R hr hrR
  refine ⟨fun s => (M + M2 + |a| * (M2 + ‖turnC‖ * M)) * B s, hBi.const_mul _, ?_, ?_⟩
  · intro τ₀ h
    obtain ⟨ε, hε, C, hC⟩ := hBloc τ₀ h
    exact ⟨ε, hε, (M + M2 + |a| * (M2 + ‖turnC‖ * M)) * C, fun s hs => mul_le_mul_of_nonneg_left (hC s hs) hK0⟩
  intro s hs ξ
  have hl : 0 < Real.exp s ^ (1 / (2 * α)) := Real.rpow_pos_of_pos (Real.exp_pos s) _
  obtain ⟨z, hzdef⟩ : ∃ z : Space, z = (Real.exp s ^ (1 / (2 * α)))⁻¹ • (axialRotation (-(a * s))).symm ξ :=
    ⟨_, rfl⟩
  have hz : ‖z‖ = (Real.exp s ^ (1 / (2 * α)))⁻¹ * ‖ξ‖ := by
    rw [hzdef, norm_smul, LinearIsometryEquiv.norm_map, Real.norm_of_nonneg (inv_pos.2 hl).le]
  have hB0 : 0 ≤ B s := le_trans (by positivity) (hBd s hs (r * Real.exp s ^ (1 / (2 * α))) le_rfl
    (mul_le_mul_of_nonneg_right hrR hl.le))
  have he3 : Real.exp (-s) < 3 := by
    have := Real.exp_one_lt_d9
    have : Real.exp (-s) < Real.exp 1 := Real.exp_lt_exp.2 (by linarith)
    linarith
  have ht : |1 - Real.exp (-s)| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith [Real.exp_pos (-s)]
  have hP : 0 ≤ (2 * π * ‖ξ‖) ^ (2 * α) := by positivity
  have hq0 : 0 ≤ ((1 + ‖ξ‖) ^ 2)⁻¹ := by positivity
  have hc0 : 0 ≤ Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3 := by positivity
  by_cases hzero : m z = 0 ∧ fderiv ℝ m z = 0
  · have hRHS : 0 ≤ (M + M2 + |a| * (M2 + ‖turnC‖ * M)) * B s * ((1 + ‖ξ‖) ^ 2)⁻¹ := by positivity
    rw [ProfileMildFormInternal.driftSym_orbit α a h1 hmd s ξ, orbitSymbol, ← hzdef, hzero.1, hzero.2]
    simp only [smul_zero, map_zero, ContinuousLinearMap.zero_apply, sub_zero, add_zero, norm_zero]
    exact ⟨hRHS, hRHS, hRHS⟩
  · have hband : r ≤ ‖z‖ ∧ ‖z‖ ≤ R := by
      by_contra hc
      apply hzero
      apply hsupp
      rcases not_and_or.1 hc with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    have hlo : r * Real.exp s ^ (1 / (2 * α)) ≤ ‖ξ‖ := by
      have := hband.1
      rw [hz, inv_mul_eq_div, le_div_iff₀ hl] at this
      exact this
    have hhi : ‖ξ‖ ≤ R * Real.exp s ^ (1 / (2 * α)) := by
      have := hband.2
      rw [hz, inv_mul_eq_div, div_le_iff₀ hl] at this
      exact this
    have hX : (2 * π * ‖ξ‖)⁻¹ * Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
        (Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
        (1 + 2 * (2 * π * ‖ξ‖) ^ (2 * α)) ≤ B s * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      exact hBd s hs ‖ξ‖ hlo hhi
    have hY := bracket_le α a h1 hP ht hM0 hM20 z (m z) (fderiv ℝ m z) (hM z) (hM2 z)
    have hmz := hM z
    have hfin : ∀ N : ℝ, N ≤ (1 + 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * (M + M2 + |a| * (M2 + ‖turnC‖ * M)) →
        (2 * π * ‖ξ‖)⁻¹ * (Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
          ((Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) * N)) ≤
        (M + M2 + |a| * (M2 + ‖turnC‖ * M)) * B s * ((1 + ‖ξ‖) ^ 2)⁻¹ := by
      intro N hN
      calc _ ≤ (2 * π * ‖ξ‖)⁻¹ * (Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
            ((Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
              ((1 + 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * (M + M2 + |a| * (M2 + ‖turnC‖ * M))))) := by
            gcongr
        _ = (M + M2 + |a| * (M2 + ‖turnC‖ * M)) *
            ((2 * π * ‖ξ‖)⁻¹ * Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
              (Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
              (1 + 2 * (2 * π * ‖ξ‖) ^ (2 * α))) := by ring
        _ ≤ (M + M2 + |a| * (M2 + ‖turnC‖ * M)) * (B s * ((1 + ‖ξ‖) ^ 2)⁻¹) :=
            mul_le_mul_of_nonneg_left hX hK0
        _ = _ := by ring
    have hw0 : 0 ≤ (2 * π * ‖ξ‖)⁻¹ := by positivity
    have hMK : M ≤ M + M2 + |a| * (M2 + ‖turnC‖ * M) := by
      have : 0 ≤ |a| * (M2 + ‖turnC‖ * M) := by positivity
      linarith
    refine ⟨?_, ?_, ?_⟩
    · rw [ProfileMildFormInternal.driftSym_orbit α a h1 hmd s ξ, ← hzdef, norm_smul, norm_smul,
        Internal.Rotation.norm_rotC, norm_smul, Real.norm_of_nonneg hw0,
        Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hc0]
      exact hfin _ hY
    · rw [orbitSymbol, ← hzdef, norm_smul, norm_smul, norm_smul, Internal.Rotation.norm_rotC, norm_smul,
        Real.norm_of_nonneg hw0, Real.norm_of_nonneg hP, Real.norm_of_nonneg (Real.exp_pos _).le,
        Real.norm_of_nonneg hc0]
      have h := hfin ((2 * π * ‖ξ‖) ^ (2 * α) * ‖m z‖) (by nlinarith [mul_le_mul_of_nonneg_left hmz hP, mul_le_mul_of_nonneg_left hMK hP, hK0, hP])
      calc _ = (2 * π * ‖ξ‖)⁻¹ * (Real.exp (-((1 - Real.exp (-s)) * (2 * π * ‖ξ‖) ^ (2 * α))) *
            ((Real.exp s ^ (4 * (1 / (2 * α)) - 1) * (Real.exp s ^ (1 / (2 * α)))⁻¹ ^ 3) *
              ((2 * π * ‖ξ‖) ^ (2 * α) * ‖m z‖))) := by ring
        _ ≤ _ := h
    · rw [orbitSymbol, ← hzdef, norm_smul, norm_smul, Internal.Rotation.norm_rotC, norm_smul,
        Real.norm_of_nonneg hw0, Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg hc0]
      exact hfin _ (by nlinarith [hmz, hMK, mul_nonneg hP hK0])

open ProfileMildFormInternal in
theorem profileMildForm_of_scalar (hS : OrbitScalarBoundStatement) : ProfileMildFormStatement :=
  profileMildForm_of_bound (orbitSymbolBound_of hS)

open ProfileMildFormInternal in
theorem orbitScalarBound : OrbitScalarBoundStatement := by
  intro α h1 h2 r R hr hrR
  have hc : Continuous (decayEnvelope α r R) := by
    unfold decayEnvelope
    fun_prop
  refine ⟨decayEnvelope α r R, ?_, ?_, fun s _ ρ hlo hhi => scalar_le α h1 hr hrR hlo hhi⟩
  · refine Integrable.mono' ((integrableOn_exp_neg_Ioi 0).const_mul ((2 * π * r)⁻¹ * (1 + R) ^ 2 *
      (1 + 2 * (2 * π * R) ^ (2 * α)) * 2 * Real.exp ((2 * π * r) ^ (2 * α)) * (6 / ((2 * π * r) ^ (2 * α)) ^ 3))) hc.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with s hs
    have hs0 : 0 ≤ s := le_of_lt hs
    have hR0 : 0 < R := lt_of_lt_of_le hr hrR
    have hb0 : 0 ≤ decayEnvelope α r R s := by
      unfold decayEnvelope
      have : 0 ≤ (2 * π * R) ^ (2 * α) := Real.rpow_nonneg (by positivity) _
      positivity
    rw [Real.norm_of_nonneg hb0]
    exact bnd_le α h1 hr hrR hs0
  · intro τ₀ _
    have hev := hc.continuousAt.eventually (gt_mem_nhds (lt_add_one (decayEnvelope α r R τ₀)))
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    exact ⟨ε, hε, decayEnvelope α r R τ₀ + 1, fun s hs => (hball hs).le⟩

theorem profileMildForm : ProfileMildFormStatement :=
  profileMildForm_of_scalar orbitScalarBound

end Breakdown.FracCert

import Breakdown.FracCert.DecayFixedPointParts
import Breakdown.FracCert.DecayFixedPointGradient
import Breakdown.FracCert.DecayFixedPointWeight
import Breakdown.FracCert.WeakRegular
import Breakdown.FracCert.WeakSymbolL1
import Breakdown.FracCert.WeakFieldSmooth
import Breakdown.FracCert.WeakLowFrequency

open MeasureTheory Set Real
open scoped ENNReal ContDiff FourierTransform SchwartzMap

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

namespace DecayFixedPointInternal

theorem profileField_continuous (U : X) (hM : HasAllMoments U) : Continuous (profileField U) := by
  have h0 := (symbolL1OfMoments U hM).1 0
  simp only [pow_zero, one_mul] at h0
  exact WeakRegularInternal.continuous_physField_of
    ((integrable_norm_iff (WeakRegularInternal.aesm_symbolX U)).1 h0)

theorem profileField_bounded (U : X) (hM : HasAllMoments U) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖profileField U y‖ ≤ C := by
  have hw := WeakRegularInternal.moments_clean U (symbolL1OfMoments U hM).1
  obtain ⟨-, hb⟩ := fieldSmoothOfMoments _ hw (WeakRegularInternal.cleanSymbol_conjSym _)
  obtain ⟨C, hC⟩ := hb 0
  refine ⟨max C 0, le_max_right _ _, fun y => ?_⟩
  have h := hC y
  rw [norm_iteratedFDeriv_zero, WeakRegularInternal.physField_clean] at h
  exact h.trans (le_max_left _ _)

theorem tensorSq_continuous {V : Space → Space} (hV : Continuous V) : Continuous (tensorSq V) := by
  unfold tensorSq
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((continuous_apply j).comp ((PiLp.continuous_ofLp 2 _).comp hV)).mul
    ((continuous_apply k).comp ((PiLp.continuous_ofLp 2 _).comp hV))

theorem tensorSq_norm_le {V : Space → Space} {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ y, ‖V y‖ ≤ C) (y : Space) :
    ‖tensorSq V y‖ ≤ C * C := by
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 hC0)).2 fun k => ?_
  rw [tensorSq, norm_mul]
  exact mul_le_mul ((PiLp.norm_apply_le _ _).trans (hC y)) ((PiLp.norm_apply_le _ _).trans (hC y))
    (norm_nonneg _) hC0

theorem farField_continuous (hB : FarFieldBoundStatement) (α : ℝ) (h1 : 1 < α) (h2 : α < 5 / 4) (a : ℝ)
    (U : X) (hM : HasAllMoments U) : Continuous (farFieldOp α a (tensorSq (profileField U))) := by
  obtain ⟨C, hC0, hC⟩ := profileField_bounded U hM
  have hne : (0 : ℝ) ≠ 2 * α - 1 + ((0 : ℕ) : ℝ) := by push_cast; linarith
  obtain ⟨K, hK⟩ := hB α h1 h2 a 0 0 0 le_rfl (by norm_num) le_rfl (by norm_num) hne
  have hF := tensorSq_norm_le hC0 hC
  have h := hK (tensorSq (profileField U)) (C * C) (C * C)
    (contDiff_zero.2 (tensorSq_continuous (profileField_continuous U hM)))
    (fun y => by rw [Real.rpow_zero, one_mul, norm_iteratedFDeriv_zero]; exact hF y)
    (fun y => by rw [Real.rpow_zero, one_mul]; exact hF y)
  exact contDiff_zero.1 h.1

theorem pairing_integrable {Θ : Space → Space} (hc : Continuous Θ)
    (hL : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume) {m : Space → CSpace} (hsm : ContDiff ℝ ∞ m)
    (hcs : HasCompactSupport m) : Integrable (fun y => inner ℝ (Θ y) (physField m y)) := by
  rw [WeakRegularInternal.physField_of_rapid (s := m) (hcs.toSchwartzMap hsm) rfl]
  exact WeakRegularInternal.integrable_pairing hc hL _

theorem annulus_of_parts {Θ : Space → Space} (hc : Continuous Θ)
    (hL : MemLp (fun y => (1 + ‖y‖)⁻¹ • Θ y) 2 volume)
    (hA : ∀ φ, IsNiceField φ → ∫ y, inner ℝ (Θ y) (φ y) = 0)
    (hB : ∀ q : Space → CSpace, (∀ ξ, q (-ξ) = conjVec (q ξ)) → ContDiff ℝ ∞ q →
      HasCompactSupport q → (∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0) →
      (∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ) → ∫ y, inner ℝ (Θ y) (physField q y) = 0)
    (m : Space → CSpace) (hh : ∀ ξ, m (-ξ) = conjVec (m ξ)) (hsm : ContDiff ℝ ∞ m)
    (hcs : HasCompactSupport m) (hr0 : ∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → m ξ = 0) :
    ∫ y, inner ℝ (Θ y) (physField m y) = 0 := by
  obtain ⟨r, hr, h0⟩ := hr0
  obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ ξ, R ≤ ‖ξ‖ → m ξ = 0 := by
    obtain ⟨R, hR⟩ := hcs.isCompact.isBounded.subset_closedBall 0
    refine ⟨R + 1, fun ξ hξ => image_eq_zero_of_notMem_tsupport fun h => ?_⟩
    have := hR h
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith
  obtain ⟨hp, -⟩ := Internal.NiceDense.nice_symField_projField hsm hr h0 hR
  set p := Internal.NiceDense.symField (Internal.NiceDense.projField m) with hpdef
  have hq : ∀ ξ, m ξ - p ξ = longitudinal ξ (m ξ) := WeakRegularInternal.sub_symField_projField hh
  set q : Space → CSpace := fun ξ => m ξ - p ξ with hqdef
  have hqh : ∀ ξ, q (-ξ) = conjVec (q ξ) := by
    intro ξ
    simp only [q, map_sub, hh, hp.2.2.2.1]
  have hqs : ContDiff ℝ ∞ q := hsm.sub hp.1
  have hqc : HasCompactSupport q := hcs.sub hp.2.1
  have hq0 : ∃ r : ℝ, 0 < r ∧ ∀ ξ, ‖ξ‖ < r → q ξ = 0 :=
    ⟨r, hr, fun ξ h => by simp only [q]; rw [hq, h0 ξ h, map_zero]⟩
  have hqf : ∃ c : Space → ℂ, ∀ ξ, q ξ = c ξ • freqVec ξ := by
    refine ⟨fun ξ => (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) (m ξ), fun ξ => ?_⟩
    simp only [q]
    rw [hq]
    ext i
    simp [longitudinal]
    ring
  let Mp := hp.2.1.toSchwartzMap hp.1
  let Mq := hqc.toSchwartzMap hqs
  have ep : physField p = fun y => realVec ((𝓕⁻ Mp) y) := WeakRegularInternal.physField_of_rapid Mp rfl
  have eq' : physField q = fun y => realVec ((𝓕⁻ Mq) y) := WeakRegularInternal.physField_of_rapid Mq rfl
  have em : physField m = fun y => realVec ((𝓕⁻ (Mp + Mq)) y) := by
    refine WeakRegularInternal.physField_of_rapid (Mp + Mq) ?_
    funext ξ
    show p ξ + (m ξ - p ξ) = m ξ
    abel
  have hsplit : ∀ y, physField m y = physField p y + physField q y := by
    intro y
    rw [em, ep, eq']
    simp only [FourierTransform.fourierInv_add, add_apply, map_add]
  have i1 := pairing_integrable hc hL hp.1 hp.2.1
  have i2 := pairing_integrable hc hL hqs hqc
  have e1 : ∫ y, inner ℝ (Θ y) (physField p y) = 0 := hA (niceField p) ⟨p, hp, rfl⟩
  have e2 := hB q hqh hqs hqc hq0 hqf
  simp_rw [hsplit, inner_add_right]
  rw [integral_add i1 i2, e1, e2, add_zero]

end DecayFixedPointInternal

open DecayFixedPointInternal in
theorem profileFixedPoint_of_annulus (hB : FarFieldBoundStatement) (hV : VelocityInverseWeightStatement)
    (hW : FarFieldWeightedStatement) (hA : FixedPointAnnulusStatement) : ProfileFixedPointStatement := by
  intro α h1 h2 a U hU hM y
  have hc : Continuous (fun y => profileField U y - farFieldOp α a (tensorSq (profileField U)) y) :=
    (profileField_continuous U hM).sub (farField_continuous hB α h1 h2 a U hM)
  have hm : MemLp (fun y => (1 + ‖y‖)⁻¹ •
      (profileField U y - farFieldOp α a (tensorSq (profileField U)) y)) 2 volume := by
    have h := (hV U hM).sub (hW α h1 h2 a U hM)
    have e : (fun y => (1 + ‖y‖)⁻¹ • (profileField U y - farFieldOp α a (tensorSq (profileField U)) y)) =
        (fun y => (1 + ‖y‖)⁻¹ • physField (symbolX U) y) -
          (fun y => (1 + ‖y‖)⁻¹ • farFieldOp α a (tensorSq (profileField U)) y) := by
      funext y
      simp only [Pi.sub_apply, smul_sub, profileField]
    rw [e]
    exact h
  have h0 := lowFrequencyRemoval _ hc hm (fun m hh hs hcs hr => hA α h1 h2 a U hU hM m hh hs hcs hr) y
  exact sub_eq_zero.1 h0

open DecayFixedPointInternal in
theorem fixedPointAnnulus_of (hB : FarFieldBoundStatement) (hV : VelocityInverseWeightStatement)
    (hW : FarFieldWeightedStatement) (hD : ProfileMildFormStatement) (hP : FarFieldPairingStatement)
    (hG1 : ProfileGradientFreeStatement) (hG2 : FarFieldGradientFreeStatement) :
    FixedPointAnnulusStatement := by
  intro α h1 h2 a U hU hM m hh hsm hcs hr0
  have hcV := profileField_continuous U hM
  have hcW := farField_continuous hB α h1 h2 a U hM
  have hLV : MemLp (fun y => (1 + ‖y‖)⁻¹ • profileField U y) 2 volume := hV U hM
  have hLW := hW α h1 h2 a U hM
  have hc : Continuous (fun y => profileField U y - farFieldOp α a (tensorSq (profileField U)) y) :=
    hcV.sub hcW
  have hL : MemLp (fun y => (1 + ‖y‖)⁻¹ •
      (profileField U y - farFieldOp α a (tensorSq (profileField U)) y)) 2 volume := by
    have e : (fun y => (1 + ‖y‖)⁻¹ • (profileField U y - farFieldOp α a (tensorSq (profileField U)) y)) =
        (fun y => (1 + ‖y‖)⁻¹ • profileField U y) -
          (fun y => (1 + ‖y‖)⁻¹ • farFieldOp α a (tensorSq (profileField U)) y) := by
      funext y
      simp only [Pi.sub_apply, smul_sub]
    rw [e]
    exact hLV.sub hLW
  refine annulus_of_parts hc hL ?_ ?_ m hh hsm hcs hr0
  · rintro φ ⟨n, hn, rfl⟩
    have iV := pairing_integrable hcV hLV hn.1 hn.2.1
    have iW := pairing_integrable hcW hLW hn.1 hn.2.1
    show ∫ y, inner ℝ (profileField U y - farFieldOp α a (tensorSq (profileField U)) y) (physField n y) = 0
    simp_rw [inner_sub_left]
    rw [integral_sub iV iW]
    have eV : ∫ y, inner ℝ (profileField U y) (physField n y) = _ := hD α h1 h2 a U hU hM _ ⟨n, hn, rfl⟩
    have eW : ∫ y, inner ℝ (farFieldOp α a (tensorSq (profileField U)) y) (physField n y) = _ :=
      hP α h1 h2 a U hM _ ⟨n, hn, rfl⟩
    rw [eV, eW, sub_self]
  · intro q hqh hqs hqc hq0 hqf
    have iV := pairing_integrable hcV hLV hqs hqc
    have iW := pairing_integrable hcW hLW hqs hqc
    simp_rw [inner_sub_left]
    rw [integral_sub iV iW, hG1 U hM q hqh hqs hqc hq0 hqf, hG2 α h1 h2 a U hM q hqh hqs hqc hq0 hqf, sub_zero]

theorem profileFixedPoint_of (hB : FarFieldBoundStatement) (hW : FarFieldWeightedStatement)
    (hD : ProfileMildFormStatement) (hP : FarFieldPairingStatement) (hG : FarFieldGradientFreeStatement) :
    ProfileFixedPointStatement :=
  profileFixedPoint_of_annulus hB profileInverseWeight hW
    (fixedPointAnnulus_of hB profileInverseWeight hW hD hP profileGradientFree hG)

end Breakdown.FracCert

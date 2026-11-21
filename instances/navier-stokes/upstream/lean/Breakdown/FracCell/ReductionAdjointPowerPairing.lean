import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.PowerSymbol
import Breakdown.FracCert.PowerSymbolRapid
import Breakdown.FracCert.SecondPairRapid
import Breakdown.FracCert.SecondSymbol
import Breakdown.FracCert.SplitFormBounds

open MeasureTheory Real
open scoped ContDiff ENNReal FourierTransform

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace PowerPairingInternal

def secondDiff (f : Space → Space) (z x : Space) : Space :=
  (1 / 2 : ℝ) • ((2 : ℝ) • f x - f (x + z) - f (x - z))

def cosWeight (z ξ : Space) : ℝ := 1 - Real.cos (2 * π * inner ℝ ξ z)

def kern (ε : ℝ) (z : Space) : ℝ := ‖z‖ ^ (-(3 + 2 * ε))

theorem lowPowerAt_eq (ε : ℝ) (f : Space → Space) (x : Space) :
    lowPowerAt ε f x = (lowPowerNormalizer ε)⁻¹ • ∫ z, kern ε z • secondDiff f z x := rfl

theorem hat_trace {ζ : Space → Space} {Dζ : Space → (Space →L[ℝ] Space)}
    {Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsAdjointRegular ζ Dζ Hζ) :
    (fieldSymbol (negSecondTrace Hζ) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow 2 ξ • (fieldSymbol ζ : Space → Freq.CSpace) ξ := by
  obtain ⟨hζ2, -, -, hDm, hDw, hD2, -, hHm, hHw, hH2⟩ := h
  have hmG : ∀ i, MemLp (WeakProfile.gradComponent Dζ i) 2 volume :=
    fun i => Internal.SecondSymbol.memLp_comp hDm hD2 i
  have hmH : ∀ i j, MemLp (fun y => Hζ y (unitVector i) (unitVector j)) 2 volume :=
    fun i j => Internal.SecondSymbol.memLp_second hHm hH2 i j
  have hA : ∀ k, (Internal.SecondSymbol.hatOf (fun y => Hζ y (unitVector k) (unitVector k)) :
      Space → Freq.CSpace) =ᵐ[volume] fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) •
        (WeakProfile.Internal.GradientFreqTr.hatComp Dζ k : Space → Freq.CSpace) ξ :=
    fun k => Internal.SecondSymbol.hat_deriv hmG (hmH k k) (fun φ hφ => hHw φ hφ k k)
  set G₀ : Space → (Space →L[ℝ] Space) := fun y => (innerSL ℝ (unitVector 0)).smulRight (ζ y) with hG₀
  have e0 : ∀ y, G₀ y (unitVector 0) = ζ y := fun y => by
    simp [hG₀, unitVector]
  have hmG0 : ∀ i, MemLp (WeakProfile.gradComponent G₀ i) 2 volume := fun i =>
    hζ2.const_smul (innerSL ℝ (unitVector 0) (unitVector i))
  have hgc : WeakProfile.gradComponent G₀ 0 = ζ := funext fun y => e0 y
  have hB : ∀ k, (WeakProfile.Internal.GradientFreqTr.hatComp Dζ k : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => ((2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • (fieldSymbol ζ : Space → Freq.CSpace) ξ := by
    intro k
    have := Internal.SecondSymbol.hat_deriv (G := G₀) (f' := fun y => Dζ y (unitVector k)) (i := 0) (k := k)
      hmG0 (hmG k) (fun φ hφ => by simp only [e0]; exact hDw φ hφ k)
    have hc : WeakProfile.Internal.GradientFreqTr.hatComp G₀ 0 = fieldSymbol ζ := by
      unfold WeakProfile.Internal.GradientFreqTr.hatComp
      rw [hgc]
      rfl
    rw [hc] at this
    exact this
  have hS : (fieldSymbol (negSecondTrace Hζ) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => -∑ k, (Internal.SecondSymbol.hatOf (fun y => Hζ y (unitVector k) (unitVector k)) :
        Space → Freq.CSpace) ξ :=
    Internal.SecondSymbol.hat_negSum (f := fun k y => Hζ y (unitVector k) (unitVector k)) (fun k => hmH k k)
  filter_upwards [hS, ae_all_iff.2 hA, ae_all_iff.2 hB] with ξ a b c
  rw [a]
  simp only [b, c, smul_smul]
  rw [← Finset.sum_smul, ← neg_smul, ← Complex.coe_smul]
  congr 1
  rw [Internal.SecondSymbol.freqPow_two, Freq.Internal.H1Consistency.norm_sq_eq ξ]
  simp only [Fin.sum_univ_three]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem band_cos {m : Space → Freq.CSpace} (hm : IsBandSymbol m) (z : Space) :
    IsBandSymbol (fun ξ => cosWeight z ξ • m ξ) := by
  obtain ⟨hs, hc, ⟨r, hr, hz⟩, hh⟩ := hm
  have hw : ContDiff ℝ ∞ (fun ξ : Space => cosWeight z ξ) :=
    contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul (ContDiff.inner ℝ contDiff_id contDiff_const)))
  have hev : ∀ ξ, cosWeight z (-ξ) = cosWeight z ξ := fun ξ => by
    unfold cosWeight
    rw [inner_neg_left, mul_neg, Real.cos_neg]
  refine ⟨hw.smul hs, hc.mono fun ξ hξ h0 => hξ (by show cosWeight z ξ • m ξ = 0; rw [h0, smul_zero]),
    ⟨r, hr, fun ξ hξ => ?_⟩, fun ξ => ?_⟩
  · show cosWeight z ξ • m ξ = 0
    rw [hz ξ hξ, smul_zero]
  · show cosWeight z (-ξ) • m (-ξ) = Freq.conjVec (cosWeight z ξ • m ξ)
    rw [hh ξ, ContinuousLinearMap.map_smul, hev]

theorem int_exp {m : Space → Freq.CSpace} (hm : IsBandSymbol m) (w : Space) :
    Integrable (fun v : Space => Complex.exp (↑(2 * π * inner ℝ v w) * Complex.I) • m v) := by
  have hmi : Integrable m := hm.1.continuous.integrable_of_hasCompactSupport hm.2.1
  have hmc := hm.1.continuous
  refine hmi.norm.mono' ?_ (ae_of_all _ fun v => ?_)
  · exact (Continuous.smul (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const)) hmc).aestronglyMeasurable
  · rw [norm_smul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem niceField_secondDiff {m : Space → Freq.CSpace} (hm : IsBandSymbol m) (z : Space) :
    secondDiff (Freq.niceField m) z = Freq.niceField (fun ξ => cosWeight z ξ • m ξ) := by
  funext x
  unfold secondDiff Freq.niceField
  rw [← map_smul, ← map_sub, ← map_sub, ← map_smul]
  congr 1
  simp only [Real.fourierInv_eq']
  have i2 : Integrable (fun v : Space => (2 : ℝ) • (Complex.exp (↑(2 * π * inner ℝ v x) * Complex.I) • m v)) :=
    (int_exp hm x).smul (2 : ℝ)
  have i3 : Integrable (fun v : Space => (2 : ℝ) • (Complex.exp (↑(2 * π * inner ℝ v x) * Complex.I) • m v) -
      Complex.exp (↑(2 * π * inner ℝ v (x + z)) * Complex.I) • m v) := i2.sub (int_exp hm (x + z))
  rw [← integral_smul (2 : ℝ), ← integral_sub i2 (int_exp hm (x + z)), ← integral_sub i3 (int_exp hm (x - z)),
    ← integral_smul]
  refine integral_congr_ae (ae_of_all _ fun v => ?_)
  simp only [inner_add_right, inner_sub_right]
  set a := inner ℝ v x
  set b := inner ℝ v z
  have h1 : Complex.exp (↑(2 * π * (a + b)) * Complex.I) =
      Complex.exp (↑(2 * π * a) * Complex.I) * Complex.exp (↑(2 * π * b) * Complex.I) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h2 : Complex.exp (↑(2 * π * (a - b)) * Complex.I) =
      Complex.exp (↑(2 * π * a) * Complex.I) * Complex.exp (-(↑(2 * π * b) * Complex.I)) := by
    rw [← Complex.exp_add]; congr 1; push_cast; ring
  have h3 : Complex.cos (2 * ↑π * ↑b) =
      (Complex.exp (2 * ↑π * ↑b * Complex.I) + Complex.exp (-(2 * ↑π * ↑b * Complex.I))) / 2 := by
    rw [Complex.cos]; ring_nf
  have hc : cosWeight z v = 1 - Real.cos (2 * π * b) := rfl
  rw [hc, h1, h2]
  simp only [← Complex.coe_smul, smul_smul, ← sub_smul]
  congr 1
  push_cast
  rw [h3]
  ring

theorem memLp_secondDiff {f : Space → Space} (hf : MemLp f 2 volume) (z : Space) :
    MemLp (secondDiff f z) 2 volume := by
  have h1 : MemLp (fun x => f (x + z)) 2 volume := hf.comp_measurePreserving (measurePreserving_add_right volume z)
  have h2 : MemLp (fun x => f (x - z)) 2 volume := hf.comp_measurePreserving (measurePreserving_sub_right volume z)
  exact ((((hf.const_smul (2 : ℝ)).sub h1).sub h2).const_smul (1 / 2 : ℝ)).ae_eq
    (Filter.Eventually.of_forall fun x => by simp [secondDiff])

open PowerSymbolInternal in
theorem pair_secondDiff {f φ : Space → Space} (hf : MemLp f 2 volume) (hφ : MemLp φ 2 volume) (z : Space) :
    ∫ y, inner ℝ (secondDiff f z y) (φ y) = ∫ y, inner ℝ (f y) (secondDiff φ z y) := by
  have ip := fun {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) =>
    Internal.SplitFormBounds.integrable_pair hF hE
  have fp : MemLp (fun y => f (y + z)) 2 volume := hf.comp_measurePreserving (measurePreserving_add_right volume z)
  have fm : MemLp (fun y => f (y - z)) 2 volume := hf.comp_measurePreserving (measurePreserving_sub_right volume z)
  have φp : MemLp (fun y => φ (y + z)) 2 volume := hφ.comp_measurePreserving (measurePreserving_add_right volume z)
  have φm : MemLp (fun y => φ (y - z)) 2 volume := hφ.comp_measurePreserving (measurePreserving_sub_right volume z)
  have e1 : (fun y => inner ℝ (secondDiff f z y) (φ y)) = fun y =>
      (1 / 2 : ℝ) * (2 * inner ℝ (f y) (φ y) - inner ℝ (f (y + z)) (φ y) - inner ℝ (f (y - z)) (φ y)) := by
    funext y
    simp only [secondDiff, real_inner_smul_left, inner_sub_left]
  have e2 : (fun y => inner ℝ (f y) (secondDiff φ z y)) = fun y =>
      (1 / 2 : ℝ) * (2 * inner ℝ (f y) (φ y) - inner ℝ (f y) (φ (y + z)) - inner ℝ (f y) (φ (y - z))) := by
    funext y
    simp only [secondDiff, real_inner_smul_right, inner_sub_right]
  have b1 : ∫ y, inner ℝ (f (y + z)) (φ y) = ∫ y, inner ℝ (f y) (φ (y - z)) := by
    rw [← integral_add_right_eq_self (fun y => inner ℝ (f y) (φ (y - z))) z]
    simp
  have b2 : ∫ y, inner ℝ (f (y - z)) (φ y) = ∫ y, inner ℝ (f y) (φ (y + z)) := by
    rw [← integral_sub_right_eq_self (fun y => inner ℝ (f y) (φ (y + z))) z]
    simp
  have A : Integrable (fun y => 2 * inner ℝ (f y) (φ y)) := (ip hf hφ).const_mul 2
  have A1 : Integrable (fun y => 2 * inner ℝ (f y) (φ y) - inner ℝ (f (y + z)) (φ y)) := A.sub (ip fp hφ)
  have A2 : Integrable (fun y => 2 * inner ℝ (f y) (φ y) - inner ℝ (f y) (φ (y + z))) := A.sub (ip hf φp)
  rw [e1, e2, integral_const_mul, integral_const_mul, integral_sub A1 (ip fm hφ), integral_sub A (ip fp hφ),
    integral_sub A2 (ip hf φm), integral_sub A (ip hf φp), b1, b2]
  ring

open PowerSymbolInternal in
theorem hat_secondDiff {f : Space → Space} (hf : MemLp f 2 volume) (z : Space) :
    (fieldSymbol (secondDiff f z) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => cosWeight z ξ • (fieldSymbol f : Space → Freq.CSpace) ξ := by
  have hcont : Continuous (fun ξ : Space => cosWeight z ξ) :=
    continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul (continuous_id.inner continuous_const)))
  have hev : ∀ ξ, cosWeight z (-ξ) = cosWeight z ξ := fun ξ => by
    unfold cosWeight
    rw [inner_neg_left, mul_neg, Real.cos_neg]
  refine bandUnique _ _ ((Lp.memLp _).locallyIntegrable (by norm_num))
    (((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hcont) (symbolConjSym _) ?_ ?_
  · filter_upwards [symbolConjSym f] with ξ hξ
    show cosWeight z (-ξ) • _ = Freq.conjVec (cosWeight z ξ • _)
    rw [hξ, ContinuousLinearMap.map_smul, hev]
  · intro m hm
    obtain ⟨G, hG, -⟩ := band_field hm
    have hφ : MemLp (Freq.niceField m) 2 volume := hG ▸ G.memLp 2
    rw [← bandPair _ (memLp_secondDiff hf z) m hm, pair_secondDiff hf hφ z, niceField_secondDiff hm z,
      bandPair f hf _ (band_cos hm z)]
    congr 1
    funext ξ
    rw [real_inner_smul_left, real_inner_smul_right]

theorem cosWeight_bounds (z ξ : Space) :
    0 ≤ cosWeight z ξ ∧ cosWeight z ξ ≤ 2 ∧ cosWeight z ξ ^ 2 ≤ freqPow 2 ξ ^ 2 * ‖z‖ ^ 4 / 4 := by
  have hc1 := Real.cos_le_one (2 * π * inner ℝ ξ z)
  have hc2 := Real.neg_one_le_cos (2 * π * inner ℝ ξ z)
  have hq := Real.one_sub_sq_div_two_le_cos (x := 2 * π * inner ℝ ξ z)
  have hi : |inner ℝ ξ z| ≤ ‖ξ‖ * ‖z‖ := abs_real_inner_le_norm ξ z
  unfold cosWeight
  refine ⟨by linarith, by linarith, ?_⟩
  rw [Internal.SecondSymbol.freqPow_two]
  set t := inner ℝ ξ z
  have h0 : 0 ≤ 1 - Real.cos (2 * π * t) := by linarith
  have h1 : 1 - Real.cos (2 * π * t) ≤ (2 * π * t) ^ 2 / 2 := by linarith
  have h2 : (1 - Real.cos (2 * π * t)) ^ 2 ≤ ((2 * π * t) ^ 2 / 2) ^ 2 := pow_le_pow_left₀ h0 h1 2
  have ht2 : t ^ 2 ≤ (‖ξ‖ * ‖z‖) ^ 2 := sq_le_sq' (by linarith [(abs_le.1 hi).1]) (abs_le.1 hi).2
  have ht4 : t ^ 4 ≤ (‖ξ‖ * ‖z‖) ^ 4 := by
    have := pow_le_pow_left₀ (sq_nonneg t) ht2 2
    calc t ^ 4 = (t ^ 2) ^ 2 := by ring
      _ ≤ ((‖ξ‖ * ‖z‖) ^ 2) ^ 2 := this
      _ = _ := by ring
  calc (1 - Real.cos (2 * π * t)) ^ 2 ≤ ((2 * π * t) ^ 2 / 2) ^ 2 := h2
    _ = (2 * π) ^ 4 * t ^ 4 / 4 := by ring
    _ ≤ (2 * π) ^ 4 * (‖ξ‖ * ‖z‖) ^ 4 / 4 := by gcongr
    _ = ((2 * π) ^ 2 * ‖ξ‖ ^ 2) ^ 2 * ‖z‖ ^ 4 / 4 := by ring

theorem secondDiff_sq_le {ζ : Space → Space} {Dζ : Space → (Space →L[ℝ] Space)}
    {Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsAdjointRegular ζ Dζ Hζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Space, ∫ x, ‖secondDiff ζ z x‖ ^ 2 ≤ C * min 1 (‖z‖ ^ 4) := by
  have hζ2 := h.1
  have sqi : ∀ g : Freq.L2C, Integrable (fun ξ => ‖(g : Space → Freq.CSpace) ξ‖ ^ 2) := fun g =>
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)
  set F := (fieldSymbol ζ : Space → Freq.CSpace) with hFd
  set S := (fieldSymbol (negSecondTrace Hζ) : Space → Freq.CSpace) with hSd
  have iF : Integrable (fun ξ => ‖F ξ‖ ^ 2) := sqi _
  have iS : Integrable (fun ξ => ‖S ξ‖ ^ 2) := sqi _
  refine ⟨4 * (∫ ξ, ‖F ξ‖ ^ 2) + ∫ ξ, ‖S ξ‖ ^ 2,
    by have a := integral_nonneg (μ := volume) (f := fun ξ => ‖F ξ‖ ^ 2) (fun ξ => sq_nonneg _)
       have b := integral_nonneg (μ := volume) (f := fun ξ => ‖S ξ‖ ^ 2) (fun ξ => sq_nonneg _)
       linarith,
    fun z => ?_⟩
  have hT := hat_trace h
  have hD := hat_secondDiff hζ2 z
  rw [Internal.SecondSymbol.integral_sq_hat (memLp_secondDiff hζ2 z)]
  have ipt : ∀ᵐ ξ ∂volume, ‖(Internal.SecondSymbol.hatOf (secondDiff ζ z) : Space → Freq.CSpace) ξ‖ ^ 2 ≤
      min 1 (‖z‖ ^ 4) * (4 * ‖F ξ‖ ^ 2 + ‖S ξ‖ ^ 2) := by
    filter_upwards [hT, hD] with ξ a b
    have b' : (Internal.SecondSymbol.hatOf (secondDiff ζ z) : Space → Freq.CSpace) ξ = cosWeight z ξ • F ξ := b
    have a' : S ξ = freqPow 2 ξ • F ξ := a
    obtain ⟨c0, c2, c4⟩ := cosWeight_bounds z ξ
    have hfp : 0 ≤ freqPow 2 ξ := Real.rpow_nonneg (by have := norm_nonneg ξ; positivity) _
    have hF0 := sq_nonneg ‖F ξ‖
    rw [b', a', norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hfp, abs_of_nonneg c0]
    rcases le_total 1 (‖z‖ ^ 4) with hz | hz
    · rw [min_eq_left hz]
      have : cosWeight z ξ ^ 2 ≤ 4 := by nlinarith
      nlinarith [sq_nonneg (freqPow 2 ξ * ‖F ξ‖)]
    · rw [min_eq_right hz]
      have hz0 : 0 ≤ ‖z‖ ^ 4 := by positivity
      nlinarith [mul_le_mul_of_nonneg_right c4 hF0, sq_nonneg (freqPow 2 ξ * ‖F ξ‖),
        mul_nonneg hz0 hF0, mul_nonneg hz0 (sq_nonneg (freqPow 2 ξ * ‖F ξ‖))]
  calc ∫ ξ, ‖(Internal.SecondSymbol.hatOf (secondDiff ζ z) : Space → Freq.CSpace) ξ‖ ^ 2
      ≤ ∫ ξ, min 1 (‖z‖ ^ 4) * (4 * ‖F ξ‖ ^ 2 + ‖S ξ‖ ^ 2) :=
        integral_mono_ae (sqi _) (((iF.const_mul 4).add iS).const_mul _) ipt
    _ = _ := by
        rw [integral_const_mul, integral_add (iF.const_mul 4) iS, integral_const_mul]
        ring

theorem pow_near {ε r : ℝ} (hr : 0 ≤ r) (h0 : 0 < ε) :
    r ^ (-(3 + 2 * ε)) * r ^ 2 = r ^ (-(1 + 2 * ε)) := by
  rcases hr.eq_or_lt with h | h
  · subst h
    rw [Real.zero_rpow (by linarith), Real.zero_rpow (by linarith)]
    ring
  · rw [show r ^ 2 = r ^ (2 : ℝ) by rw [Real.rpow_two], ← Real.rpow_add h]
    congr 1
    ring

theorem kern_integrable {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Integrable (fun z : Space => kern ε z * min 1 (‖z‖ ^ 2)) := by
  have hm : AEStronglyMeasurable (fun z : Space => kern ε z * min 1 (‖z‖ ^ 2)) volume := by
    unfold kern
    exact ((measurable_norm.pow_const _).mul (measurable_const.min (measurable_norm.pow_const 2))).aestronglyMeasurable
  refine PowerSymbolRapid.Internal.integrable_near_far hm (a := 1 + 2 * ε) (b := 3 + 2 * ε) (C := 1)
    (by linarith) (by linarith) (fun z hz => ?_) (fun z hz => ?_)
  · have hk : 0 ≤ kern ε z := Real.rpow_nonneg (norm_nonneg _) _
    have hz2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    rw [min_eq_right hz2, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk (sq_nonneg _)), one_mul]
    exact (pow_near (norm_nonneg z) h0).le
  · have hk : 0 ≤ kern ε z := Real.rpow_nonneg (norm_nonneg _) _
    have hz2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    rw [min_eq_left hz2, mul_one, Real.norm_eq_abs, abs_of_nonneg hk, one_mul]
    rfl

theorem kern_integrable_inv {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) :
    Integrable (fun z : Space => kern ε z / min 1 (‖z‖ ^ 2) * min 1 (‖z‖ ^ 4)) := by
  refine (kern_integrable h0 h1).congr (ae_of_all _ fun z => ?_)
  show kern ε z * min 1 (‖z‖ ^ 2) = kern ε z / min 1 (‖z‖ ^ 2) * min 1 (‖z‖ ^ 4)
  rcases le_total 1 ‖z‖ with hz | hz
  · have a2 : 1 ≤ ‖z‖ ^ 2 := by nlinarith
    have a4 : 1 ≤ ‖z‖ ^ 4 := by nlinarith
    rw [min_eq_left a2, min_eq_left a4]
    ring
  · have a2 : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
    have a4 : ‖z‖ ^ 4 ≤ 1 := by nlinarith [norm_nonneg z, sq_nonneg (‖z‖ ^ 2)]
    rw [min_eq_right a2, min_eq_right a4]
    rcases (norm_nonneg z).eq_or_lt with h | h
    · rw [← h]; simp
    · field_simp

theorem kern_nonneg (ε : ℝ) (z : Space) : 0 ≤ kern ε z := Real.rpow_nonneg (norm_nonneg _) _

theorem measurable_kern (ε : ℝ) : Measurable (kern ε) := measurable_norm.pow_const _

theorem measurable_secondDiff {g : Space → Space} (hg : StronglyMeasurable g) :
    Measurable (fun p : Space × Space => secondDiff g p.2 p.1) := by
  have m0 := hg.measurable
  unfold secondDiff
  fun_prop

theorem square_point_bound {ε : ℝ} (h0 : 0 < ε) {g : Space → Space} (hg : StronglyMeasurable g) (x : Space) :
    (∫⁻ z, ‖kern ε z • secondDiff g z x‖ₑ) ^ 2 ≤
      (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) *
        ∫⁻ z, ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2 := by
  have mD : Measurable (fun z => secondDiff g z x) := by
    have m0 := hg.measurable
    unfold secondDiff
    fun_prop
  have mk := measurable_kern ε
  have mf : AEMeasurable (fun z : Space => ENNReal.ofReal (Real.sqrt (kern ε z * min 1 (‖z‖ ^ 2)))) volume := by
    fun_prop
  have mh : AEMeasurable (fun z : Space => ENNReal.ofReal (Real.sqrt (kern ε z / min 1 (‖z‖ ^ 2))) *
      ‖secondDiff g z x‖ₑ) volume := by
    fun_prop
  have wnn : ∀ z : Space, 0 ≤ min 1 (‖z‖ ^ 2) := fun z => le_min zero_le_one (sq_nonneg _)
  have hpt : ∀ z, ‖kern ε z • secondDiff g z x‖ₑ ≤ ENNReal.ofReal (Real.sqrt (kern ε z * min 1 (‖z‖ ^ 2))) *
      (ENNReal.ofReal (Real.sqrt (kern ε z / min 1 (‖z‖ ^ 2))) * ‖secondDiff g z x‖ₑ) := by
    intro z
    rw [enorm_smul, Real.enorm_eq_ofReal (kern_nonneg ε z), ← mul_assoc,
      ← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← Real.sqrt_mul' _ (div_nonneg (kern_nonneg ε z) (wnn z))]
    gcongr
    rcases eq_or_ne z 0 with rfl | hz
    · rw [show kern ε 0 = 0 by unfold kern; rw [norm_zero, Real.zero_rpow (by linarith)]]
      exact Real.sqrt_nonneg _
    · have hw0 : 0 < min 1 (‖z‖ ^ 2) := lt_min one_pos (by positivity)
      rw [show kern ε z * min 1 (‖z‖ ^ 2) * (kern ε z / min 1 (‖z‖ ^ 2)) = kern ε z ^ 2 by field_simp,
        Real.sqrt_sq (kern_nonneg ε z)]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two mf mh
  simp only [Pi.mul_apply] at hH
  have e1 : ∀ z : Space, ENNReal.ofReal (Real.sqrt (kern ε z * min 1 (‖z‖ ^ 2))) ^ (2 : ℝ) =
      ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2)) := fun z => by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _) (by norm_num), Real.rpow_two,
      Real.sq_sqrt (mul_nonneg (kern_nonneg ε z) (wnn z))]
  have e2 : ∀ z : Space, (ENNReal.ofReal (Real.sqrt (kern ε z / min 1 (‖z‖ ^ 2))) * ‖secondDiff g z x‖ₑ) ^ (2 : ℝ) =
      ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2 := fun z => by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ENNReal.ofReal_rpow_of_nonneg (Real.sqrt_nonneg _)
      (by norm_num), Real.rpow_two, Real.sq_sqrt (div_nonneg (kern_nonneg ε z) (wnn z)), ENNReal.rpow_two]
  simp only [e1, e2] at hH
  calc (∫⁻ z, ‖kern ε z • secondDiff g z x‖ₑ) ^ 2
      ≤ (∫⁻ z, ENNReal.ofReal (Real.sqrt (kern ε z * min 1 (‖z‖ ^ 2))) *
          (ENNReal.ofReal (Real.sqrt (kern ε z / min 1 (‖z‖ ^ 2))) * ‖secondDiff g z x‖ₑ)) ^ 2 := by
        gcongr with z
        exact hpt z
    _ ≤ ((∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) ^ (1 / (2 : ℝ)) *
          (∫⁻ z, ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2) ^ (1 / (2 : ℝ))) ^ 2 := by
        gcongr
    _ = _ := by
        rw [mul_pow, ← ENNReal.rpow_natCast, ← ENNReal.rpow_natCast (n := 2), ← ENNReal.rpow_mul,
          ← ENNReal.rpow_mul]
        norm_num

theorem core_bound {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {g : Space → Space} (hg : StronglyMeasurable g) {C : ℝ}
    (hb : ∀ z, ∫⁻ x, ‖secondDiff g z x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * min 1 (‖z‖ ^ 4))) :
    ∫⁻ x, (∫⁻ z, ‖kern ε z • secondDiff g z x‖ₑ) ^ 2 < ⊤ := by
  have hA : (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) < ⊤ := (kern_integrable h0 h1).lintegral_lt_top
  have hI : (∫⁻ z, ENNReal.ofReal (C * (kern ε z / min 1 (‖z‖ ^ 2) * min 1 (‖z‖ ^ 4)))) < ⊤ :=
    ((kern_integrable_inv h0 h1).const_mul C).lintegral_lt_top
  have hmeas : Measurable (fun p : Space × Space =>
      ENNReal.ofReal (kern ε p.2 / min 1 (‖p.2‖ ^ 2)) * ‖secondDiff g p.2 p.1‖ₑ ^ 2) := by
    have := measurable_secondDiff hg
    have mk := measurable_kern ε
    fun_prop
  calc ∫⁻ x, (∫⁻ z, ‖kern ε z • secondDiff g z x‖ₑ) ^ 2
      ≤ ∫⁻ x, (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) *
          ∫⁻ z, ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2 :=
        lintegral_mono fun x => square_point_bound h0 hg x
    _ = (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) *
          ∫⁻ x, ∫⁻ z, ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2 :=
        lintegral_const_mul' _ _ hA.ne
    _ = (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) *
          ∫⁻ z, ∫⁻ x, ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ‖secondDiff g z x‖ₑ ^ 2 := by
        rw [lintegral_lintegral_swap hmeas.aemeasurable]
    _ ≤ (∫⁻ z, ENNReal.ofReal (kern ε z * min 1 (‖z‖ ^ 2))) *
          ∫⁻ z, ENNReal.ofReal (C * (kern ε z / min 1 (‖z‖ ^ 2) * min 1 (‖z‖ ^ 4))) := by
        gcongr with z
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        have hq : 0 ≤ kern ε z / min 1 (‖z‖ ^ 2) := div_nonneg (kern_nonneg ε z) (le_min zero_le_one (sq_nonneg _))
        calc ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ∫⁻ x, ‖secondDiff g z x‖ₑ ^ 2
            ≤ ENNReal.ofReal (kern ε z / min 1 (‖z‖ ^ 2)) * ENNReal.ofReal (C * min 1 (‖z‖ ^ 4)) := by
              gcongr
              exact hb z
          _ = _ := by
              rw [← ENNReal.ofReal_mul hq]
              congr 1
              ring
    _ < ⊤ := ENNReal.mul_lt_top hA hI

theorem secondDiff_ae {ζ g : Space → Space} (hae : ζ =ᵐ[volume] g) (z : Space) :
    secondDiff ζ z =ᵐ[volume] secondDiff g z := by
  have h1 := (measurePreserving_add_right volume z).quasiMeasurePreserving.ae_eq hae
  have h2 := (measurePreserving_sub_right volume z).quasiMeasurePreserving.ae_eq hae
  filter_upwards [hae, h1, h2] with x a b c
  simp only [Function.comp] at b c
  simp only [secondDiff, a, b, c]

theorem integrand_ae {ε : ℝ} {ζ g : Space → Space} (hae : ζ =ᵐ[volume] g) (x : Space) (hx : ζ x = g x) :
    (fun z => kern ε z • secondDiff ζ z x) =ᵐ[volume] fun z => kern ε z • secondDiff g z x := by
  have h1 := (measurePreserving_add_left volume x).quasiMeasurePreserving.ae_eq hae
  have h2 := (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq h1
  filter_upwards [h1, h2] with z b c
  simp only [Function.comp] at b c
  simp only [secondDiff, hx, b, sub_eq_add_neg, c]

theorem lowPower_memLp {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {ζ : Space → Space}
    {Dζ : Space → (Space →L[ℝ] Space)} {Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsAdjointRegular ζ Dζ Hζ) (hm : AEStronglyMeasurable ζ volume) :
    MemLp (lowPowerAt ε ζ) 2 volume := by
  have hg := hm.stronglyMeasurable_mk
  have hae := hm.ae_eq_mk
  obtain ⟨C, -, hbd⟩ := secondDiff_sq_le h
  have hb : ∀ z, ∫⁻ x, ‖secondDiff (hm.mk ζ) z x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * min 1 (‖z‖ ^ 4)) := by
    intro z
    have hmz := memLp_secondDiff h.1 z
    have hint := (memLp_two_iff_integrable_sq_norm hmz.1).1 hmz
    calc ∫⁻ x, ‖secondDiff (hm.mk ζ) z x‖ₑ ^ 2 = ∫⁻ x, ‖secondDiff ζ z x‖ₑ ^ 2 :=
          lintegral_congr_ae ((secondDiff_ae hae z).mono fun x hx => by dsimp only; rw [hx])
      _ = ENNReal.ofReal (∫ x, ‖secondDiff ζ z x‖ ^ 2) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
          congr 1
          funext x
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hbd z)
  have hfin := core_bound h0 h1 hg hb
  have hT : lowPowerAt ε ζ =ᵐ[volume] lowPowerAt ε (hm.mk ζ) := by
    filter_upwards [hae] with x hx
    rw [lowPowerAt_eq, lowPowerAt_eq, integral_congr_ae (integrand_ae hae x hx)]
  refine MemLp.ae_eq hT.symm ?_
  have hF : StronglyMeasurable (fun p : Space × Space => kern ε p.2 • secondDiff (hm.mk ζ) p.2 p.1) :=
    (((measurable_kern ε).comp measurable_snd).smul (measurable_secondDiff hg)).stronglyMeasurable
  have hAE : AEStronglyMeasurable (lowPowerAt ε (hm.mk ζ)) volume :=
    ((hF.integral_prod_right' (ν := volume)).aestronglyMeasurable.const_smul (lowPowerNormalizer ε)⁻¹)
  refine ⟨hAE, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have hc : ‖(lowPowerNormalizer ε)⁻¹‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
  calc ∫⁻ x, ‖lowPowerAt ε (hm.mk ζ) x‖ₑ ^ (ENNReal.toReal 2)
      ≤ ∫⁻ x, ‖(lowPowerNormalizer ε)⁻¹‖ₑ ^ 2 * (∫⁻ z, ‖kern ε z • secondDiff (hm.mk ζ) z x‖ₑ) ^ 2 := by
        refine lintegral_mono fun x => ?_
        rw [lowPowerAt_eq, enorm_smul, show ENNReal.toReal 2 = (2 : ℕ) by norm_num, ENNReal.rpow_natCast, mul_pow]
        gcongr
        exact enorm_integral_le_lintegral_enorm _
    _ = ‖(lowPowerNormalizer ε)⁻¹‖ₑ ^ 2 * ∫⁻ x, (∫⁻ z, ‖kern ε z • secondDiff (hm.mk ζ) z x‖ₑ) ^ 2 :=
        lintegral_const_mul' _ _ hc
    _ < ⊤ := ENNReal.mul_lt_top hc.lt_top hfin

theorem coord_isometry (w : Space) (hw : w ≠ 0) :
    ∃ R : Space ≃ₗᵢ[ℝ] Space, ∀ z : Space, inner ℝ w z = ‖w‖ * (R z) 0 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  set u : Space := ‖w‖⁻¹ • w with hu
  set e : Space := EuclideanSpace.single 0 1 with he
  have hue : ‖u‖ = ‖e‖ := by simp [hu, he, norm_smul, hn]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Space ≃ₗᵢ[ℝ] Space, ρ u = e := ⟨_, Submodule.reflection_sub hue⟩
  refine ⟨ρ, fun z => ?_⟩
  have h1 : (ρ z) 0 = inner ℝ (ρ z) e := by
    simp [he, EuclideanSpace.inner_single_right]
  have h2 : inner ℝ (ρ z) e = inner ℝ z u := by
    rw [← hρ, LinearIsometryEquiv.inner_map_map]
  rw [h1, h2, hu, real_inner_smul_right, ← mul_assoc, mul_inv_cancel₀ hn, one_mul, real_inner_comm]

theorem kern_cos_integral {ε : ℝ} (h0 : 0 < ε) (_h1 : ε < 1) (ξ : Space) :
    ∫ z, kern ε z * cosWeight z ξ = lowPowerNormalizer ε * freqPow (2 * ε) ξ := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [cosWeight, freqPow, Real.zero_rpow (show (2 * ε) ≠ 0 by positivity)]
  set w : Space := (2 * π) • ξ with hwd
  have hw : w ≠ 0 := smul_ne_zero (by positivity) hξ
  have hs : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hsn : ‖w‖ = 2 * π * ‖ξ‖ := by rw [hwd, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  obtain ⟨R, hR⟩ := coord_isometry w hw
  set F : Space → ℝ := fun y => ‖y‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (‖w‖ * y 0)) with hF
  have e1 : (fun z => kern ε z * cosWeight z ξ) = fun z => F (R z) := by
    funext z
    simp only [hF, kern, cosWeight, LinearIsometryEquiv.norm_map]
    congr 3
    rw [← hR z, hwd, real_inner_smul_left]
  rw [e1, R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding F]
  set N₀ : Space → ℝ := fun y => ‖y‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (y 0)) with hN₀
  have e2 : F = fun y => ‖w‖ ^ (3 + 2 * ε) * N₀ (‖w‖ • y) := by
    funext y
    simp only [hF, hN₀, norm_smul, norm_norm, PiLp.smul_apply, smul_eq_mul]
    rw [Real.mul_rpow hs.le (norm_nonneg _), ← mul_assoc, ← mul_assoc, ← Real.rpow_add hs, add_neg_cancel,
      Real.rpow_zero, one_mul]
  rw [e2, integral_const_mul, Measure.integral_comp_smul, finrank_euclideanSpace_fin]
  have hN : ∫ y, N₀ y = lowPowerNormalizer ε := rfl
  rw [hN, smul_eq_mul, freqPow, ← hsn, abs_of_pos (by positivity)]
  rw [show ‖w‖ ^ (3 + 2 * ε) = ‖w‖ ^ (2 * ε) * ‖w‖ ^ 3 by
    rw [← Real.rpow_natCast, ← Real.rpow_add hs]; congr 1; push_cast; ring]
  field_simp

theorem normalizer_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < lowPowerNormalizer ε := by
  have hnn : ∀ z : Space, 0 ≤ ‖z‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (z 0)) := fun z =>
    mul_nonneg (kern_nonneg ε z) (by linarith [Real.cos_le_one (z 0)])
  have hI : Integrable (fun z : Space => ‖z‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (z 0))) := by
    refine ((kern_integrable h0 h1).const_mul 2).mono' ?_ (ae_of_all _ fun z => ?_)
    · exact ((measurable_kern ε).mul (measurable_const.sub
        (Real.continuous_cos.measurable.comp (measurable_pi_apply 0 |>.comp (PiLp.continuous_ofLp 2 _).measurable)))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (hnn z)]
      have hk := kern_nonneg ε z
      have hc := Real.cos_le_one (z 0)
      have hc2 := Real.neg_one_le_cos (z 0)
      have hq := Real.one_sub_sq_div_two_le_cos (x := z 0)
      have h00 : |z 0| ≤ ‖z‖ := by
        have := abs_real_inner_le_norm z (EuclideanSpace.single 0 1)
        simpa [EuclideanSpace.inner_single_right] using this
      have h0sq : z 0 ^ 2 ≤ ‖z‖ ^ 2 := by
        have := sq_le_sq' (abs_le.1 h00).1 (abs_le.1 h00).2
        exact this
      show ‖z‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (z 0)) ≤ 2 * (kern ε z * min 1 (‖z‖ ^ 2))
      unfold kern
      have hk' : 0 ≤ ‖z‖ ^ (-(3 + 2 * ε)) := Real.rpow_nonneg (norm_nonneg _) _
      rcases le_total 1 (‖z‖ ^ 2) with hz | hz
      · rw [min_eq_left hz]
        nlinarith [mul_le_mul_of_nonneg_left (show 1 - Real.cos (z 0) ≤ 2 by linarith) hk']
      · rw [min_eq_right hz]
        nlinarith [mul_le_mul_of_nonneg_left (show 1 - Real.cos (z 0) ≤ 2 * ‖z‖ ^ 2 by nlinarith) hk']
  unfold lowPowerNormalizer
  rw [integral_pos_iff_support_of_nonneg hnn hI]
  set e : Space := EuclideanSpace.single 0 1
  refine lt_of_lt_of_le (Metric.measure_ball_pos volume e (by norm_num : (0 : ℝ) < 1 / 2)) (measure_mono ?_)
  intro z hz
  rw [Metric.mem_ball, dist_eq_norm] at hz
  have hi : |inner ℝ (z - e) e| ≤ ‖z - e‖ * ‖e‖ := abs_real_inner_le_norm _ _
  have he : ‖e‖ = 1 := by simp [e]
  have hv : inner ℝ (z - e) e = z 0 - 1 := by simp [e, EuclideanSpace.inner_single_right, inner_sub_left]
  rw [hv, he, mul_one] at hi
  have hlo : 1 / 2 < z 0 := by linarith [(abs_lt.1 (lt_of_le_of_lt hi hz)).1]
  have hhi : z 0 < 3 / 2 := by linarith [(abs_lt.1 (lt_of_le_of_lt hi hz)).2]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hlo
    linarith
  have hcos : Real.cos (z 0) < 1 := by
    have := Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) (by linarith [Real.pi_gt_three]) (by linarith : (0:ℝ) < z 0)
    rwa [Real.cos_zero] at this
  show ‖z‖ ^ (-(3 + 2 * ε)) * (1 - Real.cos (z 0)) ≠ 0
  exact (mul_pos (Real.rpow_pos_of_pos (norm_pos_iff.2 hz0) _) (by linarith)).ne'

theorem prod_int_phys {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {g : Space → Space} (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 volume) {C : ℝ}
    (hbr : ∀ z, ∫ x, ‖secondDiff g z x‖ ^ 2 ≤ C * min 1 (‖z‖ ^ 4))
    {φ : Space → Space} (hφ : MemLp φ 2 volume) (hφc : Continuous φ) :
    Integrable (fun p : Space × Space => inner ℝ (kern ε p.2 • secondDiff g p.2 p.1) (φ p.1))
      (volume.prod volume) := by
  have hmeas : Measurable (fun p : Space × Space => kern ε p.2 • secondDiff g p.2 p.1) :=
    ((measurable_kern ε).comp measurable_snd).smul (measurable_secondDiff hg)
  have h1f : AEStronglyMeasurable (fun p : Space × Space => inner ℝ (kern ε p.2 • secondDiff g p.2 p.1) (φ p.1))
      (volume.prod volume) :=
    hmeas.aestronglyMeasurable.inner (hφc.comp continuous_fst).aestronglyMeasurable
  have hC : 0 ≤ C := by
    have := hbr (EuclideanSpace.single 0 1)
    have hn : ‖(EuclideanSpace.single 0 1 : Space)‖ = 1 := by simp
    rw [hn] at this
    norm_num at this
    exact le_trans (integral_nonneg fun _ => sq_nonneg _) this
  set Φ : ℝ := Real.sqrt (∫ y, ‖φ y‖ ^ 2) with hΦ
  rw [integrable_prod_iff' h1f]
  refine ⟨ae_of_all _ fun z => ?_, ?_⟩
  · have hkD : MemLp (fun y => kern ε z • secondDiff g z y) 2 volume :=
      ((memLp_secondDiff hg2 z).const_smul (kern ε z)).ae_eq (Filter.Eventually.of_forall fun y => rfl)
    exact Internal.SplitFormBounds.integrable_pair hkD hφ
  refine ((kern_integrable h0 h1).mul_const (Real.sqrt C * Φ)).mono' (h1f.norm.prod_swap.integral_prod_right')
    (ae_of_all _ fun z => ?_)
  have hD := memLp_secondDiff hg2 z
  have hk := kern_nonneg ε z
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  have hCst := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun y => norm_nonneg (secondDiff g z y)) (ae_of_all _ fun y => norm_nonneg (φ y))
    (by simpa using hD.norm) (by simpa using hφ.norm)
  simp only [Real.rpow_two, one_div] at hCst
  have hint : Integrable (fun y => ‖secondDiff g z y‖ * ‖φ y‖) := hD.norm.integrable_mul hφ.norm
  have hsq : Real.sqrt (∫ y, ‖secondDiff g z y‖ ^ 2) ≤ Real.sqrt C * min 1 (‖z‖ ^ 2) := by
    rw [← Real.sqrt_sq (le_min zero_le_one (sq_nonneg ‖z‖)), ← Real.sqrt_mul hC]
    refine Real.sqrt_le_sqrt ((hbr z).trans (le_of_eq ?_))
    congr 1
    rcases le_total 1 (‖z‖ ^ 2) with h | h
    · rw [min_eq_left h, min_eq_left (by nlinarith : (1 : ℝ) ≤ ‖z‖ ^ 4)]; ring
    · rw [min_eq_right h, min_eq_right (by nlinarith [sq_nonneg ‖z‖] : ‖z‖ ^ 4 ≤ 1)]; ring
  calc ∫ y, ‖inner ℝ (kern ε z • secondDiff g z y) (φ y)‖
      ≤ ∫ y, kern ε z * (‖secondDiff g z y‖ * ‖φ y‖) := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _) (hint.const_mul _)
          (ae_of_all _ fun y => ?_)
        show ‖inner ℝ (kern ε z • secondDiff g z y) (φ y)‖ ≤ kern ε z * (‖secondDiff g z y‖ * ‖φ y‖)
        rw [real_inner_smul_left, norm_mul, Real.norm_eq_abs, abs_of_nonneg hk, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hk
    _ = kern ε z * ∫ y, ‖secondDiff g z y‖ * ‖φ y‖ := integral_const_mul _ _
    _ ≤ kern ε z * (Real.sqrt (∫ y, ‖secondDiff g z y‖ ^ 2) * Φ) := by
        refine mul_le_mul_of_nonneg_left ?_ hk
        have h' := hCst
        rw [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at h'
        exact h'
    _ ≤ kern ε z * (Real.sqrt C * min 1 (‖z‖ ^ 2) * Φ) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (Real.sqrt_nonneg _)) hk
    _ = kern ε z * min 1 (‖z‖ ^ 2) * (Real.sqrt C * Φ) := by ring

theorem prod_int_freq {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) (F : Freq.L2C) {m : Space → Freq.CSpace}
    (hm : IsBandSymbol m) :
    Integrable (fun p : Space × Space => kern ε p.1 * cosWeight p.1 p.2 *
      inner ℝ ((F : Space → Freq.CSpace) p.2) (m p.2)) (volume.prod volume) := by
  obtain ⟨R, hR⟩ := hm.2.1.isCompact.isBounded.subset_closedBall 0
  have hmL : MemLp m 2 volume := hm.1.continuous.memLp_of_hasCompactSupport hm.2.1
  have hFL : MemLp (F : Space → Freq.CSpace) 2 volume := Lp.memLp F
  set K : ℝ := 2 + 2 * π ^ 2 * R ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have hdom : Integrable (fun p : Space × Space => (K * (kern ε p.1 * min 1 (‖p.1‖ ^ 2))) *
      (‖(F : Space → Freq.CSpace) p.2‖ * ‖m p.2‖)) (volume.prod volume) :=
    ((kern_integrable h0 h1).const_mul K).mul_prod (hFL.norm.integrable_mul hmL.norm)
  have hcw : Continuous (fun p : Space × Space => cosWeight p.1 p.2) :=
    continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul (continuous_snd.inner continuous_fst)))
  refine hdom.mono' ?_ (ae_of_all _ fun p => ?_)
  · have a1 : AEStronglyMeasurable (fun p : Space × Space => kern ε p.1 * cosWeight p.1 p.2) (volume.prod volume) :=
      (((measurable_kern ε).comp measurable_fst).mul hcw.measurable).aestronglyMeasurable
    have a2 : AEStronglyMeasurable (fun p : Space × Space => (F : Space → Freq.CSpace) p.2) (volume.prod volume) :=
      (Lp.aestronglyMeasurable F).comp_snd
    have a3 : AEStronglyMeasurable (fun p : Space × Space => m p.2) (volume.prod volume) :=
      (hm.1.continuous.comp continuous_snd).aestronglyMeasurable
    exact a1.mul (a2.inner a3)
  · obtain ⟨z, ξ⟩ := p
    show ‖kern ε z * cosWeight z ξ * inner ℝ ((F : Space → Freq.CSpace) ξ) (m ξ)‖ ≤
      K * (kern ε z * min 1 (‖z‖ ^ 2)) * (‖(F : Space → Freq.CSpace) ξ‖ * ‖m ξ‖)
    obtain ⟨c0, c2, c4⟩ := cosWeight_bounds z ξ
    have hk := kern_nonneg ε z
    have hin := abs_real_inner_le_norm ((F : Space → Freq.CSpace) ξ) (m ξ)
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hk, abs_of_nonneg c0]
    by_cases hmξ : m ξ = 0
    · simp [hmξ]
    have hξR : ‖ξ‖ ≤ R := by
      have := hR (subset_tsupport _ hmξ)
      simpa using this
    have hcK : cosWeight z ξ ≤ K * min 1 (‖z‖ ^ 2) := by
      have hfp : freqPow 2 ξ = (2 * π) ^ 2 * ‖ξ‖ ^ 2 := Internal.SecondSymbol.freqPow_two ξ
      have hfpR : freqPow 2 ξ ≤ (2 * π) ^ 2 * R ^ 2 := by
        rw [hfp]; gcongr
      have hfp0 : 0 ≤ freqPow 2 ξ := by rw [hfp]; positivity
      rcases le_total 1 (‖z‖ ^ 2) with hz | hz
      · rw [min_eq_left hz]; nlinarith [sq_nonneg R]
      · rw [min_eq_right hz]
        have hz4 : ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 := by ring
        have hz0 : 0 ≤ ‖z‖ ^ 2 := sq_nonneg _
        have hsq : cosWeight z ξ ^ 2 ≤ (freqPow 2 ξ * ‖z‖ ^ 2 / 2) ^ 2 := by nlinarith
        have hc' : cosWeight z ξ ≤ freqPow 2 ξ * ‖z‖ ^ 2 / 2 :=
          (pow_le_pow_iff_left₀ c0 (by positivity) two_ne_zero).1 hsq
        nlinarith [mul_le_mul_of_nonneg_right hfpR hz0, sq_nonneg π]
    have hprod : 0 ≤ ‖(F : Space → Freq.CSpace) ξ‖ * ‖m ξ‖ := by positivity
    calc kern ε z * cosWeight z ξ * |inner ℝ ((F : Space → Freq.CSpace) ξ) (m ξ)|
        ≤ kern ε z * (K * min 1 (‖z‖ ^ 2)) * (‖(F : Space → Freq.CSpace) ξ‖ * ‖m ξ‖) := by
          gcongr
      _ = _ := by ring

open PowerSymbolInternal in
theorem symbol_of {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {g : Space → Space} (hg : StronglyMeasurable g)
    (hg2 : MemLp g 2 volume) {C : ℝ}
    (hb : ∀ z, ∫⁻ x, ‖secondDiff g z x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * min 1 (‖z‖ ^ 4)))
    (hbr : ∀ z, ∫ x, ‖secondDiff g z x‖ ^ 2 ≤ C * min 1 (‖z‖ ^ 4))
    (hT2 : MemLp (lowPowerAt ε g) 2 volume) :
    (fieldSymbol (lowPowerAt ε g) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow (2 * ε) ξ • (fieldSymbol g : Space → Freq.CSpace) ξ := by
  have hs : (0 : ℝ) < 2 * ε := by linarith
  have hcont : Continuous (fun ξ : Space => freqPow (2 * ε) ξ) := by
    unfold freqPow
    exact (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr hs.le)
  refine bandUnique _ _ ((Lp.memLp _).locallyIntegrable (by norm_num))
    (((Lp.memLp _).locallyIntegrable (by norm_num)).continuous_smul hcont) (symbolConjSym _) ?_ ?_
  · filter_upwards [symbolConjSym g] with ξ hξ
    show freqPow (2 * ε) (-ξ) • _ = Freq.conjVec (freqPow (2 * ε) ξ • _)
    rw [hξ, ContinuousLinearMap.map_smul]
    simp [freqPow, norm_neg]
  intro m hm
  obtain ⟨G, hG, -⟩ := band_field hm
  have hφ2 : MemLp (Freq.niceField m) 2 volume := hG ▸ G.memLp 2
  have hφc : Continuous (Freq.niceField m) := hG ▸ G.continuous
  have hmeas : Measurable (fun p : Space × Space => kern ε p.2 • secondDiff g p.2 p.1) :=
    ((measurable_kern ε).comp measurable_snd).smul (measurable_secondDiff hg)
  have hfin := core_bound h0 h1 hg hb
  have hae : ∀ᵐ y ∂volume, Integrable (fun z => kern ε z • secondDiff g z y) := by
    have hM : Measurable (fun y => (∫⁻ z, ‖kern ε z • secondDiff g z y‖ₑ) ^ 2) :=
      (hmeas.enorm.lintegral_prod_right').pow_const 2
    filter_upwards [ae_lt_top hM hfin.ne] with y hy
    refine ⟨(hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_⟩
    show ∫⁻ z, ‖kern ε z • secondDiff g z y‖ₑ < ⊤
    by_contra hc
    rw [not_lt, top_le_iff] at hc
    rw [hc] at hy
    simp at hy
  have hN := (normalizer_pos h0 h1).ne'
  have step4 : ∀ z, ∫ y, inner ℝ (kern ε z • secondDiff g z y) (Freq.niceField m y) =
      ∫ ξ, kern ε z * cosWeight z ξ * inner ℝ ((fieldSymbol g : Space → Freq.CSpace) ξ) (m ξ) := by
    intro z
    simp only [real_inner_smul_left]
    rw [integral_const_mul, bandPair _ (memLp_secondDiff hg2 z) m hm]
    rw [integral_congr_ae ((hat_secondDiff hg2 z).mono fun ξ hξ => by
      show inner ℝ _ (m ξ) = inner ℝ (cosWeight z ξ • (fieldSymbol g : Space → Freq.CSpace) ξ) (m ξ)
      rw [hξ])]
    simp only [real_inner_smul_left]
    rw [← integral_const_mul]
    congr 1
    funext ξ
    ring
  rw [← bandPair _ hT2 m hm]
  calc ∫ y, inner ℝ (lowPowerAt ε g y) (Freq.niceField m y)
      = ∫ y, (lowPowerNormalizer ε)⁻¹ * ∫ z, inner ℝ (kern ε z • secondDiff g z y) (Freq.niceField m y) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with y hy
        rw [lowPowerAt_eq, real_inner_smul_left, real_inner_comm, ← integral_inner hy]
        congr 1
        exact integral_congr_ae (ae_of_all _ fun z => real_inner_comm _ _)
    _ = (lowPowerNormalizer ε)⁻¹ * ∫ z, ∫ y, inner ℝ (kern ε z • secondDiff g z y) (Freq.niceField m y) := by
        rw [integral_const_mul, integral_integral_swap (prod_int_phys h0 h1 hg hg2 hbr hφ2 hφc)]
    _ = (lowPowerNormalizer ε)⁻¹ * ∫ z, ∫ ξ, kern ε z * cosWeight z ξ *
          inner ℝ ((fieldSymbol g : Space → Freq.CSpace) ξ) (m ξ) := by
        simp only [step4]
    _ = (lowPowerNormalizer ε)⁻¹ * ∫ ξ, ∫ z, kern ε z * cosWeight z ξ *
          inner ℝ ((fieldSymbol g : Space → Freq.CSpace) ξ) (m ξ) := by
        rw [integral_integral_swap (prod_int_freq h0 h1 (fieldSymbol g) hm)]
    _ = ∫ ξ, inner ℝ (freqPow (2 * ε) ξ • (fieldSymbol g : Space → Freq.CSpace) ξ) (m ξ) := by
        rw [← integral_const_mul]
        congr 1
        funext ξ
        rw [integral_mul_const, kern_cos_integral h0 h1, real_inner_smul_left]
        field_simp

theorem lowPower_symbol {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) {ζ : Space → Space}
    {Dζ : Space → (Space →L[ℝ] Space)} {Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (h : IsAdjointRegular ζ Dζ Hζ) (hm : AEStronglyMeasurable ζ volume) :
    (fieldSymbol (lowPowerAt ε ζ) : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow (2 * ε) ξ • (fieldSymbol ζ : Space → Freq.CSpace) ξ := by
  have hg := hm.stronglyMeasurable_mk
  have hae := hm.ae_eq_mk
  have hg2 : MemLp (hm.mk ζ) 2 volume := h.1.ae_eq hae
  obtain ⟨C, -, hbd⟩ := secondDiff_sq_le h
  have hbr : ∀ z, ∫ x, ‖secondDiff (hm.mk ζ) z x‖ ^ 2 ≤ C * min 1 (‖z‖ ^ 4) := by
    intro z
    have e : ∫ x, ‖secondDiff (hm.mk ζ) z x‖ ^ 2 = ∫ x, ‖secondDiff ζ z x‖ ^ 2 :=
      integral_congr_ae ((secondDiff_ae hae z).mono fun x hx => by simp only [hx])
    rw [e]
    exact hbd z
  have hb : ∀ z, ∫⁻ x, ‖secondDiff (hm.mk ζ) z x‖ₑ ^ 2 ≤ ENNReal.ofReal (C * min 1 (‖z‖ ^ 4)) := by
    intro z
    have hmz := memLp_secondDiff hg2 z
    have hint := (memLp_two_iff_integrable_sq_norm hmz.1).1 hmz
    calc ∫⁻ x, ‖secondDiff (hm.mk ζ) z x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖secondDiff (hm.mk ζ) z x‖ ^ 2) := by
          rw [ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => sq_nonneg _)]
          congr 1
          funext x
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (hbr z)
  have hT : lowPowerAt ε ζ =ᵐ[volume] lowPowerAt ε (hm.mk ζ) := by
    filter_upwards [hae] with x hx
    rw [lowPowerAt_eq, lowPowerAt_eq, integral_congr_ae (integrand_ae hae x hx)]
  have hTζ := lowPower_memLp h0 h1 h hm
  have hT2 : MemLp (lowPowerAt ε (hm.mk ζ)) 2 volume := hTζ.ae_eq hT
  have key := symbol_of h0 h1 hg hg2 hb hbr hT2
  have e1 : fieldSymbol (lowPowerAt ε ζ) = fieldSymbol (lowPowerAt ε (hm.mk ζ)) := by
    unfold fieldSymbol Freq.toLpOrZero
    rw [dif_pos hTζ, dif_pos hT2, MemLp.toLp_congr hTζ hT2 hT]
  have e2 : fieldSymbol ζ = fieldSymbol (hm.mk ζ) := by
    unfold fieldSymbol Freq.toLpOrZero
    rw [dif_pos h.1, dif_pos hg2, MemLp.toLp_congr h.1 hg2 hae]
  rw [e1, e2]
  exact key

end PowerPairingInternal

open PowerPairingInternal in
theorem powerPairing : PowerPairingStatement := by
  intro α hα1 hα2 m ζ Dζ Hζ hreg hζm v G H P hv hP
  have h0 : 0 < α - 1 := by linarith
  have h1 : α - 1 < 1 := by linarith
  have hT := lowPower_memLp h0 h1 hreg hζm
  refine ⟨hT, ?_⟩
  have wps : WeakPowerSymbolStatement := weakPowerSymbol_of_band secondSymbolEnergy
    (PowerSymbolInternal.bandWeakPower_of rapidWeakPower) (PowerSymbolInternal.bandSecondPair_of rapidSecondPair)
  have e1 := wps α hα1 (by linarith) m v G H P hv hP
  have e2 := lowPower_symbol h0 h1 hreg hζm
  rw [Internal.SplitFormBounds.pair_symbol hP.1 hreg.1,
    Internal.SplitFormBounds.pair_symbol (Internal.SplitFormBounds.memLp_trace hv) hT]
  refine integral_congr_ae ?_
  filter_upwards [e1, e2] with ξ a b
  rw [a, b, real_inner_smul_left, real_inner_smul_right, show 2 * α - 2 = 2 * (α - 1) by ring]
  rfl

end Reduction

end CellCert

end Breakdown

import Breakdown.Uniqueness.RegLocalAuxSymm
import Breakdown.Uniqueness.RegLocalAuxHs
import Breakdown.Uniqueness.RegCurveAuxBilin

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem freqVec_apply' (ξ : Space) (i : Fin 3) : freqVec ξ i = ((ξ i : ℝ) : ℂ) := rfl

private theorem inner_freqVec' (ξ : Space) (w : CSpace) :
    inner ℂ (freqVec ξ) w = ∑ i, ((ξ i : ℝ) : ℂ) * w i := by
  simp [PiLp.inner_apply, freqVec_apply', Complex.conj_ofReal, mul_comm]

private theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [EuclideanSpace.norm_eq, freqVec_apply', Complex.norm_real]

private theorem inner_freqVec_divFreeC (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) (divFreeC ξ z) = 0 := by
  by_cases h0 : ξ = 0
  · subst h0
    have : freqVec 0 = 0 := map_zero complexifyVec
    rw [this, inner_zero_left]
  have hn : ‖ξ‖ ≠ 0 := norm_ne_zero_iff.mpr h0
  have hP : divFreeC ξ z = z - ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) z) • freqVec ξ := by
    rw [inner_freqVec']
    rfl
  rw [hP, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_freqVec]
  have hc : (((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ((‖ξ‖ : ℝ) : ℂ) ^ 2 = 1 := by
    have hn' : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
    push_cast
    field_simp
  linear_combination (-(inner ℂ (freqVec ξ) z)) * hc

theorem norm_divFreeC_le_self (ξ : Space) (z : CSpace) : ‖divFreeC ξ z‖ ≤ ‖z‖ := by
  set P := divFreeC ξ z with hPdef
  have hP : P = z - ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * ∑ i, ((ξ i : ℝ) : ℂ) * z i) • freqVec ξ := rfl
  have h1 : inner ℂ P (freqVec ξ) = 0 := by
    rw [← inner_conj_symm, inner_freqVec_divFreeC, map_zero]
  have h2 : inner ℂ P P = inner ℂ P z := by
    nth_rewrite 2 [hP]
    rw [inner_sub_right, inner_smul_right, h1, mul_zero, sub_zero]
  have h3 : ‖P‖ ^ 2 ≤ ‖P‖ * ‖z‖ := by
    have e : ((‖P‖ ^ 2 : ℝ) : ℂ) = inner ℂ P P := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    have : ‖P‖ ^ 2 = RCLike.re (inner ℂ P z) := by
      rw [← h2, ← e, RCLike.re_to_complex, Complex.ofReal_re]
    rw [this]
    exact re_inner_le_norm P z
  rcases (norm_nonneg P).eq_or_lt with h | h
  · rw [← h]
    exact norm_nonneg z
  · nlinarith

private theorem divFreeC_sub (ξ : Space) (z w : CSpace) :
    divFreeC ξ (z - w) = divFreeC ξ z - divFreeC ξ w := by
  simp only [divFreeC, PiLp.sub_apply, mul_sub, Finset.sum_sub_distrib, sub_smul]
  abel

private theorem hsNormSq_le_of_norm_le {k : ℕ} {f g : Space → CSpace} (h : ∀ ξ, ‖f ξ‖ ≤ ‖g ξ‖) :
    hsNormSq k f ≤ hsNormSq k g := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (h ξ)

private theorem hsNormSq_mono {k m : ℕ} (hkm : k ≤ m) (f : Space → CSpace) :
    hsNormSq k f ≤ hsNormSq m f := by
  unfold hsNormSq
  refine lintegral_mono fun ξ => ?_
  gcongr
  unfold hsWeight
  exact pow_le_pow_right₀ (by nlinarith [sq_nonneg ‖ξ‖]) hkm

private theorem rpow_half_sq (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

private theorem sq_le_of_le_rpow {w x : ℝ≥0∞} {C : ℝ} (h : w ≤ ENNReal.ofReal C * x ^ (1 / 2 : ℝ)) :
    w ^ 2 ≤ ENNReal.ofReal ((|C| + 1) ^ 2) * x := by
  have hC : ENNReal.ofReal C ≤ ENNReal.ofReal (|C| + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith [le_abs_self C])
  calc w ^ 2 ≤ (ENNReal.ofReal C * x ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ENNReal.ofReal C ^ 2 * x := by rw [mul_pow, rpow_half_sq]
    _ ≤ ENNReal.ofReal (|C| + 1) ^ 2 * x := by gcongr
    _ = ENNReal.ofReal ((|C| + 1) ^ 2) * x := by
      rw [ENNReal.ofReal_pow (by positivity)]

private theorem hsNormSq_advectionBilin_le' (m : ℕ) (hm : 3 ≤ m) : ∃ K : ℝ, 0 < K ∧
    ∀ u v : Space → CSpace, AEStronglyMeasurable u volume → AEStronglyMeasurable v volume →
      hsNormSq (m - 1) (advectionBilin u v) ≤ ENNReal.ofReal K * hsNormSq m u * hsNormSq m v := by
  obtain ⟨C0, h0⟩ := hsNormSq_advectionBilin_le (m - 1)
  obtain ⟨C1, h1⟩ := freqL1Norm_le_hsNormSq
  obtain ⟨C2, h2⟩ := weightedFreqL1_le 1
  refine ⟨(|C0| + 1) * ((|C1| + 1) ^ 2 + (|C2| + 1) ^ 2), by positivity, fun u v hu hv => ?_⟩
  have hW : freqL1Norm u ^ 2 ≤ ENNReal.ofReal ((|C1| + 1) ^ 2) * hsNormSq m u :=
    (sq_le_of_le_rpow (h1 u)).trans (by gcongr; exact hsNormSq_mono (by omega) u)
  have hg : gradFreqL1Norm v ≤ ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 1) * ‖v ξ‖ₑ := by
    unfold gradFreqL1Norm
    refine lintegral_mono fun ξ => ?_
    gcongr
    simp
  have hG : gradFreqL1Norm v ^ 2 ≤ ENNReal.ofReal ((|C2| + 1) ^ 2) * hsNormSq m v :=
    (sq_le_of_le_rpow (hg.trans (h2 v))).trans (by gcongr; exact hsNormSq_mono (by omega) v)
  have hC0 : ENNReal.ofReal C0 ≤ ENNReal.ofReal (|C0| + 1) :=
    ENNReal.ofReal_le_ofReal (by linarith [le_abs_self C0])
  have hmu : hsNormSq (m - 1) u ≤ hsNormSq m u := hsNormSq_mono (by omega) u
  have hidx : m - 1 + 1 = m := by omega
  calc hsNormSq (m - 1) (advectionBilin u v)
      ≤ ENNReal.ofReal C0 * (freqL1Norm u ^ 2 * hsNormSq (m - 1 + 1) v +
          hsNormSq (m - 1) u * gradFreqL1Norm v ^ 2) := h0 u v hu hv
    _ ≤ ENNReal.ofReal (|C0| + 1) * (ENNReal.ofReal ((|C1| + 1) ^ 2) * hsNormSq m u * hsNormSq m v +
          hsNormSq m u * (ENNReal.ofReal ((|C2| + 1) ^ 2) * hsNormSq m v)) := by
        rw [hidx]
        gcongr
    _ = ENNReal.ofReal ((|C0| + 1) * ((|C1| + 1) ^ 2 + (|C2| + 1) ^ 2)) * hsNormSq m u *
          hsNormSq m v := by
        rw [ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add (p := (|C1| + 1) ^ 2) (q := (|C2| + 1) ^ 2) (by positivity) (by positivity)]
        ring

private theorem norm_nonlinSymbol_le (f : Space → CSpace) (ξ : Space) :
    ‖nonlinSymbol f ξ‖ ≤ ‖advectionBilin f f ξ‖ := by
  simp only [nonlinSymbol, norm_neg, advectionSymbol]
  exact norm_divFreeC_le_self ξ _

theorem hsNormSq_nonlinSymbol_le (m : ℕ) (hm : 3 ≤ m) : ∃ C : ℝ, 0 < C ∧ ∀ f : Space → CSpace,
    AEStronglyMeasurable f volume →
      hsNormSq (m - 1) (nonlinSymbol f) ≤ ENNReal.ofReal C * hsNormSq m f ^ 2 := by
  obtain ⟨K, hK, h⟩ := hsNormSq_advectionBilin_le' m hm
  refine ⟨K, hK, fun f hf => ?_⟩
  calc hsNormSq (m - 1) (nonlinSymbol f) ≤ hsNormSq (m - 1) (advectionBilin f f) :=
        hsNormSq_le_of_norm_le (norm_nonlinSymbol_le f)
    _ ≤ ENNReal.ofReal K * hsNormSq m f * hsNormSq m f := h f f hf hf
    _ = ENNReal.ofReal K * hsNormSq m f ^ 2 := by ring

private theorem weightedVolume_zero : weightedVolume 0 = volume := by
  have : (fun ξ : Space => ENNReal.ofReal ((1 + ‖ξ‖) ^ 0)) = 1 := by
    funext ξ
    simp
  rw [weightedVolume, this, withDensity_one]

private theorem advectionBilin_sub_ae {m : ℕ} (hm : 3 ≤ m) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hf' : hsNormSq m f < ⊤) (hg' : hsNormSq m g < ⊤) :
    advectionBilin f f - advectionBilin g g =ᵐ[volume]
      advectionBilin (f - g) f + advectionBilin g (f - g) := by
  obtain ⟨B, hB⟩ := exists_bilin_advection 0
  have mf : MemLp f 1 (weightedVolume (0 + 1)) :=
    memLp_weightedVolume_of_hsNormSq hf ((hsNormSq_mono (by omega) f).trans_lt hf')
  have mg : MemLp g 1 (weightedVolume (0 + 1)) :=
    memLp_weightedVolume_of_hsNormSq hg ((hsNormSq_mono (by omega) g).trans_lt hg')
  have md := mf.sub mg
  obtain ⟨a1, e1⟩ := hB f f mf mf
  obtain ⟨a2, e2⟩ := hB g g mg mg
  obtain ⟨a3, e3⟩ := hB (f - g) f md mf
  obtain ⟨a4, e4⟩ := hB g (f - g) mg md
  have key : (a1.sub a2).toLp (advectionBilin f f - advectionBilin g g) =
      (a3.add a4).toLp (advectionBilin (f - g) f + advectionBilin g (f - g)) := by
    rw [MemLp.toLp_sub a1 a2, MemLp.toLp_add a3 a4, ← e1, ← e2, ← e3, ← e4, MemLp.toLp_sub mf mg]
    simp only [map_sub, sub_apply]
    abel
  have := (MemLp.toLp_eq_toLp_iff _ _).mp key
  rwa [weightedVolume_zero] at this

theorem hsNormSq_nonlinSymbol_sub_le (m : ℕ) (hm : 3 ≤ m) : ∃ C : ℝ, 0 < C ∧
    ∀ f g : Space → CSpace, AEStronglyMeasurable f volume → AEStronglyMeasurable g volume →
      hsNormSq m f < ⊤ → hsNormSq m g < ⊤ →
      hsNormSq (m - 1) (nonlinSymbol f - nonlinSymbol g) ≤
        ENNReal.ofReal C * (hsNormSq m f + hsNormSq m g) * hsNormSq m (f - g) := by
  obtain ⟨K, hK, h⟩ := hsNormSq_advectionBilin_le' m hm
  refine ⟨2 * K, by positivity, fun f g hf hg hf' hg' => ?_⟩
  have hpt : ∀ ξ, ‖(nonlinSymbol f - nonlinSymbol g) ξ‖ ≤
      ‖(advectionBilin f f - advectionBilin g g) ξ‖ := by
    intro ξ
    simp only [Pi.sub_apply, nonlinSymbol, advectionSymbol]
    rw [show -divFreeC ξ (advectionBilin f f ξ) - -divFreeC ξ (advectionBilin g g ξ) =
        -divFreeC ξ (advectionBilin f f ξ - advectionBilin g g ξ) by rw [divFreeC_sub]; abel, norm_neg]
    exact norm_divFreeC_le_self ξ _
  have hae := advectionBilin_sub_ae hm hf hg hf' hg'
  have hd : AEStronglyMeasurable (f - g) volume := hf.sub hg
  have hEq : hsNormSq (m - 1) (advectionBilin f f - advectionBilin g g) =
      hsNormSq (m - 1) (advectionBilin (f - g) f + advectionBilin g (f - g)) := by
    unfold hsNormSq
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ξ hξ
    rw [hξ]
  obtain ⟨B, hB⟩ := exists_bilin_advection 0
  have mf : MemLp f 1 (weightedVolume (0 + 1)) :=
    memLp_weightedVolume_of_hsNormSq hf ((hsNormSq_mono (by omega) f).trans_lt hf')
  have mg : MemLp g 1 (weightedVolume (0 + 1)) :=
    memLp_weightedVolume_of_hsNormSq hg ((hsNormSq_mono (by omega) g).trans_lt hg')
  obtain ⟨a3, -⟩ := hB (f - g) f (mf.sub mg) mf
  obtain ⟨a4, -⟩ := hB g (f - g) mg (mf.sub mg)
  rw [weightedVolume_zero] at a3 a4
  calc hsNormSq (m - 1) (nonlinSymbol f - nonlinSymbol g)
      ≤ hsNormSq (m - 1) (advectionBilin f f - advectionBilin g g) := hsNormSq_le_of_norm_le hpt
    _ = hsNormSq (m - 1) (advectionBilin (f - g) f + advectionBilin g (f - g)) := hEq
    _ ≤ 2 * hsNormSq (m - 1) (advectionBilin (f - g) f) +
          2 * hsNormSq (m - 1) (advectionBilin g (f - g)) := hsNormSq_add_le _ a3.1 a4.1
    _ ≤ 2 * (ENNReal.ofReal K * hsNormSq m (f - g) * hsNormSq m f) +
          2 * (ENNReal.ofReal K * hsNormSq m g * hsNormSq m (f - g)) := by
        gcongr
        · exact h _ _ hd hf
        · exact h _ _ hg hd
    _ = ENNReal.ofReal (2 * K) * (hsNormSq m f + hsNormSq m g) * hsNormSq m (f - g) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        ring

end Breakdown.SmoothFlow

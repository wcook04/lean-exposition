import Breakdown.FracCell.Defs
import Breakdown.FracCert.SecondTraceSolenoidal
import Breakdown.FracCell.ModelFormParts
import Breakdown.Uniqueness.CutoffBounds
import Breakdown.FracCell.CentrePairingActuator

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CentreIdentityParts

open SteadyCert SteadyCert.SecondTraceSolenoidalInternal

def gradPart {k N : ℕ} (c : FracCellData k N) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (q l a b j d : Fin 3) (y : Space) : ℝ :=
  c.centreSecond y (unitVector j) (unitVector l) q * v y a * G y (unitVector d) b
    + c.centreGrad y (unitVector l) q * G y (unitVector j) a * G y (unitVector d) b
    + c.centreGrad y (unitVector l) q * v y a * H y (unitVector j) (unitVector d) b

def valuePart {k N : ℕ} (c : FracCellData k N) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (q a b d e j : Fin 3) (y : Space) : ℝ :=
  c.centreGrad y (unitVector j) q * G y (unitVector b) a * G y (unitVector e) d
    + c.centre y q * H y (unitVector j) (unitVector b) a * G y (unitVector e) d
    + c.centre y q * G y (unitVector b) a * H y (unitVector j) (unitVector e) d

section TripleLocalHelpers

open Filter Topology
open scoped Convolution

private theorem memLp_cut {f w ψ : Space → ℝ} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp : 2 ≤ p)
    (hψc : Continuous ψ) (hψs : HasCompactSupport ψ) (hw : AEStronglyMeasurable w volume)
    {C : ℝ} (hC : ∀ᵐ y ∂volume, |w y| ≤ C) :
    MemLp (fun y => ψ y * (w y * f y)) 2 volume := by
  obtain ⟨B, hB⟩ := hψc.bounded_above_of_compact_support hψs
  have h1 : MemLp (fun y => ψ y * (w y * f y)) p volume := by
    refine hf.of_le_mul (c := B * C) (hψc.aestronglyMeasurable.mul (hw.mul hf.1)) ?_
    filter_upwards [hC] with y hy
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, ← mul_assoc]
    have hb : |ψ y| ≤ B := by simpa [Real.norm_eq_abs] using hB y
    exact mul_le_mul_of_nonneg_right (mul_le_mul hb hy (abs_nonneg _) ((abs_nonneg _).trans hb)) (abs_nonneg _)
  refine h1.mono_exponent_of_measure_support_ne_top (s := tsupport ψ) (fun y hy => ?_)
    hψs.isCompact.measure_lt_top.ne hp
  rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]

private theorem int_cut {f w χ : Space → ℝ} (hf : LocallyIntegrable f volume) (hχc : Continuous χ)
    (hχs : HasCompactSupport χ) (hw : AEStronglyMeasurable w volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, |w y| ≤ C) : Integrable (fun y => χ y * (w y * f y)) := by
  have hi : Integrable (fun y => χ y * f y) := by
    simpa [smul_eq_mul] using hf.integrable_smul_left_of_hasCompactSupport hχc hχs
  refine (hi.norm.const_mul C).mono' (hχc.aestronglyMeasurable.mul (hw.mul hf.aestronglyMeasurable)) ?_
  filter_upwards [hC] with y hy
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul]
  have e : |χ y| * (|w y| * |f y|) = |w y| * (|χ y| * |f y|) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_right hy (by positivity)

private theorem conv_bound (φ : ContDiffBump (0 : Space)) {g : Space → ℝ} (hg : LocallyIntegrable g volume) {C : ℝ}
    (hC : ∀ᵐ y ∂volume, |g y| ≤ C) (x : Space) :
    |(φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) x| ≤ C := by
  have hex := (φ.hasCompactSupport_normed (μ := volume)).convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (φ.continuous_normed (μ := volume)) hg x
  have hi : Integrable (fun t => φ.normed volume t * g (x - t)) := by
    simpa [ConvolutionExistsAt, smul_eq_mul] using hex
  have hC' : ∀ᵐ t ∂(volume : Measure Space), |g (x - t)| ≤ C :=
    (Measure.measurePreserving_sub_left volume x).quasiMeasurePreserving.ae hC
  rw [convolution_def]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  calc |∫ t, φ.normed volume t * g (x - t)| ≤ ∫ t, |φ.normed volume t * g (x - t)| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ t, φ.normed volume t * C := by
        refine integral_mono_ae hi.abs (φ.integrable_normed.mul_const C) ?_
        filter_upwards [hC'] with t ht
        rw [abs_mul, abs_of_nonneg (φ.nonneg_normed t)]
        exact mul_le_mul_of_nonneg_left ht (φ.nonneg_normed t)
    _ = C := by rw [integral_mul_const, φ.integral_normed, one_mul]

private theorem conv_fderiv (φ : ContDiffBump (0 : Space)) {a a' : Space → ℝ} (hloc : LocallyIntegrable a volume)
    (j : Fin 3)
    (haw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * a y = -∫ y, ψ y * a' y)
    (y : Space) :
    fderiv ℝ (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a) y (unitVector j) =
      (φ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a') y := by
  have hcf : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  have hd1 : ContDiff ℝ 1 (φ.normed volume) := hcd.of_le (by simp)
  have hder := hcf.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hd1 hloc y
  rw [hder.fderiv]
  have hex := (hcf.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).precompL Space)
    (hcd.continuous_fderiv (by simp)) hloc y
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hex.integrable_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  set ψ : Space → ℝ := fun s => φ.normed volume (y - s) with hψ
  have hψt : IsTestScalar ψ := by
    refine ⟨hcd.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hcf.comp_homeomorph (Homeomorph.subLeft y)
  have hψd : ∀ s, fderiv ℝ ψ s (unitVector j) = -fderiv ℝ (φ.normed volume) (y - s) (unitVector j) := by
    intro s
    have h1 : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (y - s)) (y - s) :=
      ((hcd.differentiable (by simp)) (y - s)).hasFDerivAt
    have h2 : HasFDerivAt ψ ((fderiv ℝ (φ.normed volume) (y - s)).comp (-ContinuousLinearMap.id ℝ Space)) s :=
      h1.comp s ((hasFDerivAt_id s).const_sub y)
    rw [h2.fderiv]
    simp
  have hwj := haw ψ hψt
  simp only [hψd, neg_mul, integral_neg] at hwj
  exact neg_injective hwj



private theorem prod_two {a a' f f' : Space → ℝ} (j : Fin 3) (ha : Continuous a) {M : ℝ} (hM : ∀ y, |a y| ≤ M)
    (ha' : AEStronglyMeasurable a' volume) {M' : ℝ} (hM' : ∀ᵐ y ∂volume, |a' y| ≤ M')
    (haw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * a y = -∫ y, ψ y * a' y)
    (hf : LocallyIntegrable f volume) (hf' : LocallyIntegrable f' volume)
    (hfw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * f y = -∫ y, ψ y * f' y)
    (ψ : Space → ℝ) (hψ : IsTestScalar ψ) :
    ∫ y, (fderiv ℝ ψ y (unitVector j) * a y + ψ y * a' y) * f y = -∫ y, ψ y * a y * f' y := by
  have haloc : LocallyIntegrable a volume := ha.locallyIntegrable
  have ha'loc : LocallyIntegrable a' volume :=
    (memLp_top_of_bound ha' M' (by simpa [Real.norm_eq_abs] using hM')).locallyIntegrable le_top
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_div_iff₀ (by positivity) this]
      linarith⟩
  have hφr : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have hφK : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := by
    refine Eventually.of_forall fun n => le_of_eq ?_
    show 1 / ((n : ℝ) + 1) = 2 * (1 / (2 * ((n : ℝ) + 1)))
    field_simp
  set A : ℕ → Space → ℝ := fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a with hA
  set D : ℕ → Space → ℝ := fun n => (φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] a' with hD
  have hAs : ∀ n, ContDiff ℝ ∞ (A n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _ (φ n).contDiff_normed haloc
  have hDc : ∀ n, Continuous (D n) := fun n =>
    ((φ n).hasCompactSupport_normed).continuous_convolution_left _ (φ n).continuous_normed ha'loc
  have hAb : ∀ n y, |A n y| ≤ M := fun n y => conv_bound (φ n) haloc (ae_of_all _ hM) y
  have hDb : ∀ n y, |D n y| ≤ M' := fun n y => conv_bound (φ n) ha'loc hM' y
  have hAd : ∀ n y, fderiv ℝ (A n) y (unitVector j) = D n y := fun n y => conv_fderiv (φ n) haloc j haw y
  have hAt : ∀ y, Tendsto (fun n => A n y) atTop (𝓝 (a y)) := fun y =>
    ContDiffBump.convolution_tendsto_right_of_continuous hφr ha y
  have hDt : ∀ᵐ y ∂volume, Tendsto (fun n => D n y) atTop (𝓝 (a' y)) :=
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := φ) (K := 2) hφr hφK ha'loc
  have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
  have hψ'c : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
    (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ's : HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector j)) := hψ.2.fderiv_apply (𝕜 := ℝ) _
  have heq : ∀ n, ∫ y, (fderiv ℝ ψ y (unitVector j) * A n y + ψ y * D n y) * f y
      = -∫ y, ψ y * A n y * f' y := by
    intro n
    have ht : IsTestScalar (fun y => ψ y * A n y) := ⟨hψ.1.mul (hAs n), hψ.2.mul_right⟩
    have e := hfw _ ht
    have hpd : ∀ y, fderiv ℝ (fun y => ψ y * A n y) y (unitVector j)
        = fderiv ℝ ψ y (unitVector j) * A n y + ψ y * D n y := by
      intro y
      have h : HasFDerivAt (fun y => ψ y * A n y) (ψ y • fderiv ℝ (A n) y + A n y • fderiv ℝ ψ y) y :=
        (hψd y).hasFDerivAt.mul (((hAs n).differentiable (by simp)) y).hasFDerivAt
      rw [h.fderiv]
      simp only [hAd, FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    simp only [hpd] at e
    exact e
  set B : Space → ℝ := fun y => M * |fderiv ℝ ψ y (unitVector j)| + M' * |ψ y| with hB
  have hBc : Continuous B := (continuous_const.mul hψ'c.abs).add (continuous_const.mul hψ.1.continuous.abs)
  have hBs : HasCompactSupport B := by
    refine HasCompactSupport.intro' hψ.2.isCompact ?_ ?_
    · exact isClosed_tsupport _
    · intro y hy
      have h1 : ψ y = 0 := image_eq_zero_of_notMem_tsupport hy
      have h2 : fderiv ℝ ψ y = 0 := by
        have := hψ.2.fderiv (𝕜 := ℝ)
        exact image_eq_zero_of_notMem_tsupport (fun h => hy (tsupport_fderiv_subset ℝ h))
      simp [hB, h1, h2]
  have L1 : Tendsto (fun n => ∫ y, (fderiv ℝ ψ y (unitVector j) * A n y + ψ y * D n y) * f y) atTop
      (𝓝 (∫ y, (fderiv ℝ ψ y (unitVector j) * a y + ψ y * a' y) * f y)) := by
    have hdom : Integrable (fun y => B y * (1 * f y)) := int_cut hf hBc hBs aestronglyMeasurable_const
      (C := 1) (ae_of_all _ fun y => by simp)
    have hB0 : ∀ y, 0 ≤ B y := fun y => by
      have h0 : 0 ≤ M := (abs_nonneg _).trans (hAb 0 y)
      have h0' : 0 ≤ M' := (abs_nonneg _).trans (hDb 0 y)
      simp only [hB]; positivity
    refine tendsto_integral_of_dominated_convergence (fun y => ‖B y * (1 * f y)‖) (fun n => ?_) hdom.norm
      (fun n => ae_of_all _ fun y => ?_) ?_
    · exact (((hψ'c.mul (hAs n).continuous).add (hψ.1.continuous.mul (hDc n))).aestronglyMeasurable).mul
        hf.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, one_mul, abs_mul, abs_of_nonneg (hB0 y)]
      refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, hB]
      have h1 := mul_le_mul_of_nonneg_left (hAb n y) (abs_nonneg (fderiv ℝ ψ y (unitVector j)))
      have h2 := mul_le_mul_of_nonneg_left (hDb n y) (abs_nonneg (ψ y))
      linarith
    · filter_upwards [hDt] with y hy
      exact ((tendsto_const_nhds.mul (hAt y)).add (tendsto_const_nhds.mul hy)).mul tendsto_const_nhds
  have L2 : Tendsto (fun n => ∫ y, ψ y * A n y * f' y) atTop (𝓝 (∫ y, ψ y * a y * f' y)) := by
    have hdom : Integrable (fun y => ψ y * (1 * f' y)) := int_cut hf' hψ.1.continuous hψ.2
      aestronglyMeasurable_const (C := 1) (ae_of_all _ fun y => by simp)
    refine tendsto_integral_of_dominated_convergence (fun y => M * ‖ψ y * (1 * f' y)‖) (fun n => ?_)
      (hdom.norm.const_mul M) (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · exact ((hψ.1.continuous.mul (hAs n).continuous).aestronglyMeasurable).mul hf'.aestronglyMeasurable
    · rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, one_mul, abs_mul]
      have h1 := hAb n y
      have e : |ψ y| * |A n y| * |f' y| = |A n y| * (|ψ y| * |f' y|) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    · exact (tendsto_const_nhds.mul (hAt y)).mul tendsto_const_nhds
  simp only [heq] at L1
  exact tendsto_nhds_unique L1 L2.neg

end TripleLocalHelpers

theorem triple_local {a a' f f' g g' : Space → ℝ} (j : Fin 3) {p : ℝ≥0∞}
    (ha : Continuous a) (hab : ∃ M : ℝ, ∀ y, |a y| ≤ M)
    (ha' : AEStronglyMeasurable a' volume) (ha'b : ∃ M : ℝ, ∀ᵐ y ∂volume, |a' y| ≤ M)
    (haw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * a y = -∫ y, φ y * a' y)
    (hf : MemLp f p volume) (hp : 2 ≤ p) (hf' : MemLp f' 2 volume)
    (hfw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * f y = -∫ y, φ y * f' y)
    (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    (hgw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * g y = -∫ y, φ y * g' y) :
    ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * (a y * f y * g y)
      = -∫ y, φ y * (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y) := by
  intro φ hφ
  obtain ⟨M, hM⟩ := hab
  obtain ⟨M', hM'⟩ := ha'b
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (one_le_two.trans hp)
  have hf'l : LocallyIntegrable f' volume := hf'.locallyIntegrable one_le_two
  have ham : AEStronglyMeasurable a volume := ha.aestronglyMeasurable
  have hMa : ∀ᵐ y ∂volume, |a y| ≤ M := ae_of_all _ hM
  have hφc : Continuous φ := hφ.1.continuous
  have hφ'c : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ's : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := hφ.2.fderiv_apply (𝕜 := ℝ) _
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  set P : Space → ℝ := fun y => φ y * (a y * f y) with hP
  set Q : Space → ℝ := fun y => fderiv ℝ φ y (unitVector j) * (a y * f y) + φ y * (a' y * f y)
    + φ y * (a y * f' y) with hQ
  have mP : MemLp P 2 volume := memLp_cut hf hp hφc hφ.2 ham hMa
  have m1 : MemLp (fun y => fderiv ℝ φ y (unitVector j) * (a y * f y)) 2 volume := memLp_cut hf hp hφ'c hφ's ham hMa
  have m2 : MemLp (fun y => φ y * (a' y * f y)) 2 volume := memLp_cut hf hp hφc hφ.2 ha' hM'
  have m3 : MemLp (fun y => φ y * (a y * f' y)) 2 volume := memLp_cut hf' le_rfl hφc hφ.2 ham hMa
  have mQ : MemLp Q 2 volume := (m1.add m2).add m3
  have hPw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * P y = -∫ y, ψ y * Q y := by
    intro ψ hψ
    have hψd : Differentiable ℝ ψ := hψ.1.differentiable (by simp)
    have hψc : Continuous ψ := hψ.1.continuous
    have hψ'c : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
      (hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hψ's : HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector j)) := hψ.2.fderiv_apply (𝕜 := ℝ) _
    have ht : IsTestScalar (fun y => ψ y * φ y) := ⟨hψ.1.mul hφ.1, hψ.2.mul_right⟩
    have e := prod_two j ha hM ha' hM' haw hfl hf'l hfw _ ht
    have hpd : ∀ y, fderiv ℝ (fun y => ψ y * φ y) y (unitVector j)
        = fderiv ℝ ψ y (unitVector j) * φ y + ψ y * fderiv ℝ φ y (unitVector j) := by
      intro y
      have h : HasFDerivAt (fun y => ψ y * φ y) (ψ y • fderiv ℝ φ y + φ y • fderiv ℝ ψ y) y :=
        (hψd y).hasFDerivAt.mul (hφd y).hasFDerivAt
      rw [h.fderiv]
      simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply, Pi.smul_apply,
        smul_eq_mul]
      ring
    simp only [hpd] at e
    have i1 : Integrable (fun y => fderiv ℝ ψ y (unitVector j) * P y) := by
      have := int_cut hfl (hψ'c.mul hφc) hψ's.mul_right ham hMa
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [hP, Pi.mul_apply]; ring
    have i2 : Integrable (fun y => ψ y * (fderiv ℝ φ y (unitVector j) * (a y * f y) + φ y * (a' y * f y))) := by
      have h1 := int_cut hfl (hψc.mul hφ'c) hψ.2.mul_right ham hMa
      have h2 := int_cut hfl (hψc.mul hφc) hψ.2.mul_right ha' hM'
      refine (h1.add h2).congr (ae_of_all _ fun y => ?_)
      simp only [Pi.add_apply, Pi.mul_apply]; ring
    have i3 : Integrable (fun y => ψ y * (φ y * (a y * f' y))) := by
      have := int_cut hf'l (hψc.mul hφc) hψ.2.mul_right ham hMa
      refine this.congr (ae_of_all _ fun y => ?_)
      simp only [Pi.mul_apply]; ring
    have s1 : ∫ y, ((fderiv ℝ ψ y (unitVector j) * φ y + ψ y * fderiv ℝ φ y (unitVector j)) * a y
        + ψ y * φ y * a' y) * f y
        = (∫ y, fderiv ℝ ψ y (unitVector j) * P y)
          + ∫ y, ψ y * (fderiv ℝ φ y (unitVector j) * (a y * f y) + φ y * (a' y * f y)) := by
      rw [← integral_add i1 i2]
      congr 1; funext y; simp only [hP]; ring
    have s2 : ∫ y, ψ y * Q y = (∫ y, ψ y * (fderiv ℝ φ y (unitVector j) * (a y * f y) + φ y * (a' y * f y)))
        + ∫ y, ψ y * (φ y * (a y * f' y)) := by
      rw [← integral_add i2 i3]
      congr 1; funext y; simp only [hQ]; ring
    have s3 : ∫ y, ψ y * φ y * a y * f' y = ∫ y, ψ y * (φ y * (a y * f' y)) := by
      congr 1; funext y; ring
    rw [s1, s3] at e
    rw [s2]
    linarith
  have hpart := CentrePairingActuatorInternal.parts_h1 mP hg hg' mQ j hPw hgw
  have t1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * (a y * f y) * g y) := m1.integrable_mul hg
  have t2 : Integrable (fun y => φ y * (a' y * f y) * g y) := m2.integrable_mul hg
  have t3 : Integrable (fun y => φ y * (a y * f' y) * g y) := m3.integrable_mul hg
  have t4 : Integrable (fun y => g' y * P y) := hg'.integrable_mul mP
  have eQ : ∫ y, g y * Q y = (∫ y, fderiv ℝ φ y (unitVector j) * (a y * f y) * g y)
      + (∫ y, φ y * (a' y * f y) * g y) + ∫ y, φ y * (a y * f' y) * g y := by
    have t12 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * (a y * f y) * g y
        + φ y * (a' y * f y) * g y) := t1.add t2
    rw [← integral_add t1 t2, ← integral_add t12 t3]
    congr 1; funext y; simp only [hQ]; ring
  have eR : ∫ y, φ y * (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y)
      = (∫ y, φ y * (a' y * f y) * g y) + (∫ y, φ y * (a y * f' y) * g y) + ∫ y, g' y * P y := by
    have t23 : Integrable (fun y => φ y * (a' y * f y) * g y + φ y * (a y * f' y) * g y) := t2.add t3
    rw [← integral_add t2 t3, ← integral_add t23 t4]
    congr 1; funext y; simp only [hP]; ring
  have eL : ∫ y, fderiv ℝ φ y (unitVector j) * (a y * f y * g y)
      = ∫ y, fderiv ℝ φ y (unitVector j) * (a y * f y) * g y := by
    congr 1; funext y; ring
  rw [eL, eR]
  rw [eQ] at hpart
  linarith

theorem triple_parts {a a' f f' g g' : Space → ℝ} (j : Fin 3) {p : ℝ≥0∞}
    (ha : Continuous a) (hab : ∃ M : ℝ, ∀ y, |a y| ≤ M)
    (ha' : AEStronglyMeasurable a' volume) (ha'b : ∃ M : ℝ, ∀ᵐ y ∂volume, |a' y| ≤ M)
    (haw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * a y = -∫ y, φ y * a' y)
    (hf : MemLp f p volume) (hp : 2 ≤ p) (hf' : MemLp f' 2 volume)
    (hfw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * f y = -∫ y, φ y * f' y)
    (hg : MemLp g 2 volume) (hg' : MemLp g' 2 volume)
    (hgw : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) * g y = -∫ y, φ y * g' y)
    (h0 : Integrable (fun y => a y * f y * g y)) (h1 : Integrable (fun y => a' y * f y * g y))
    (h2 : Integrable (fun y => a y * f' y * g y)) (h3 : Integrable (fun y => a y * f y * g' y)) :
    ∫ y, (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y) = 0 := by
  have hloc := triple_local j ha hab ha' ha'b haw hf hp hf' hfw hg hg' hgw
  have hD : Integrable (fun y => a' y * f y * g y + a y * f' y * g y + a y * f y * g' y) := (h1.add h2).add h3
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have c0 : 0 ≤ c := by
    have := (norm_nonneg _).trans (hc 1 one_pos 0)
    simpa using this
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have χs : ∀ n : ℕ, ContDiff ℝ ∞ (radialCutoff ((n : ℝ) + 1)) := fun n => contDiff_radialCutoff (hr n)
  have χt : ∀ n : ℕ, IsTestScalar (radialCutoff ((n : ℝ) + 1)) := fun n =>
    ⟨χs n, hasCompactSupport_radialCutoff (hr n)⟩
  have χb : ∀ (n : ℕ) y, |radialCutoff ((n : ℝ) + 1) y| ≤ 1 := fun n y =>
    abs_le.2 ⟨by linarith [radialCutoff_nonneg ((n : ℝ) + 1) y], radialCutoff_le_one _ _⟩
  have dχb : ∀ (n : ℕ) y, |fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j)| ≤ c * (1 / ((n : ℝ) + 1)) := by
    intro n y
    calc |fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j)|
        ≤ ‖fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y‖ * ‖unitVector j‖ := by
          rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * (1 / ((n : ℝ) + 1)) := by
          rw [ModelFormInternal.norm_unitVector, mul_one, mul_one_div]; exact hc _ (hr n) y
  have dχb' : ∀ (n : ℕ) y, |fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j)| ≤ c := fun n y =>
    (dχb n y).trans (mul_le_of_le_one_right c0 (by
      rw [div_le_one (hr n)]; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))
  have hone : ∀ y : Space, Filter.Tendsto (fun n : ℕ => radialCutoff ((n : ℝ) + 1) y) Filter.atTop (nhds 1) := by
    intro y
    refine tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨⌈‖y‖⌉₊, fun n hn => ?_⟩)
    have h1 := Nat.le_ceil ‖y‖
    have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    exact (radialCutoff_eq_one (hr n) (by linarith)).symm
  have hzero : ∀ y : Space, Filter.Tendsto (fun n : ℕ => fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j))
      Filter.atTop (nhds 0) := by
    intro y
    have ht : Filter.Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds 0) := by
      simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
    exact squeeze_zero_norm (fun n => by rw [Real.norm_eq_abs]; exact dχb n y) ht
  have L1 : Filter.Tendsto (fun n : ℕ => ∫ y, radialCutoff ((n : ℝ) + 1) y *
      (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y)) Filter.atTop
      (nhds (∫ y, (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y))) := by
    refine MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun y => ‖a' y * f y * g y + a y * f' y * g y + a y * f y * g' y‖) (fun n => ?_) hD.norm
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · exact (χs n).continuous.aestronglyMeasurable.mul hD.1
    · rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (by rw [Real.norm_eq_abs]; exact χb n y)
    · simpa using (hone y).mul (tendsto_const_nhds (x := a' y * f y * g y + a y * f' y * g y + a y * f y * g' y))
  have L2 : Filter.Tendsto (fun n : ℕ => ∫ y, fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j) *
      (a y * f y * g y)) Filter.atTop (nhds 0) := by
    have := MeasureTheory.tendsto_integral_of_dominated_convergence (μ := volume)
      (F := fun (n : ℕ) y => fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j) * (a y * f y * g y))
      (f := fun _ => (0 : ℝ)) (fun y => c * ‖a y * f y * g y‖) (fun n => ?_) (h0.norm.const_mul c)
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · simpa using this
    · exact (((χs n).continuous_fderiv (by simp)).clm_apply continuous_const).aestronglyMeasurable.mul h0.1
    · rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (dχb' n y) (norm_nonneg _)
    · simpa using (hzero y).mul (tendsto_const_nhds (x := a y * f y * g y))
  have heq : ∀ n : ℕ, ∫ y, radialCutoff ((n : ℝ) + 1) y *
      (a' y * f y * g y + a y * f' y * g y + a y * f y * g' y)
      = -∫ y, fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (unitVector j) * (a y * f y * g y) := by
    intro n
    rw [hloc _ (χt n), neg_neg]
  simp only [heq] at L1
  have L2' := L2.neg
  rw [neg_zero] at L2'
  exact tendsto_nhds_unique L1 L2'

theorem unit_inner (x : Space) (i : Fin 3) : inner ℝ (unitVector i) x = x i := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem weak_coord {u D : Space → Space} {p r : ℝ≥0∞} (hu : MemLp u p volume) (hp : 1 ≤ p)
    (hD : MemLp D r volume) (hr : 1 ≤ r) (j i : Fin 3)
    (hw : ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) • u y = -∫ y, ψ y • D y) :
    ∀ ψ : Space → ℝ, IsTestScalar ψ → ∫ y, fderiv ℝ ψ y (unitVector j) * u y i = -∫ y, ψ y * D y i := by
  intro ψ hψ
  have h1 : Integrable (fun y => fderiv ℝ ψ y (unitVector j) • u y) :=
    integrable_test_smul hu hp (test_dirDeriv hψ j)
  have h2 : Integrable (fun y => ψ y • D y) := integrable_test_smul hD hr hψ
  have e := congrArg (fun z => inner ℝ (unitVector i) z) (hw ψ hψ)
  simp only [inner_neg_right] at e
  rw [← integral_inner h1, ← integral_inner h2] at e
  simpa only [inner_smul_right, unit_inner] using e

theorem memLp_coord {F : Space → Space} {p : ℝ≥0∞} (hF : MemLp F p volume) (i : Fin 3) :
    MemLp (fun y => F y i) p volume :=
  (EuclideanSpace.proj (𝕜 := ℝ) i : Space →L[ℝ] ℝ).comp_memLp' hF

theorem memLp_second {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (i j : Fin 3) :
    MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous).comp_aestronglyMeasurable
      hs.measurable_second
  refine (memLp_two_iff_integrable_sq_norm hm).2 (hs.second_two.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (Finset.single_le_sum (f := fun k => ‖H y (unitVector i) (unitVector k)‖ ^ 2)
    (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (f := fun a => ∑ k : Fin 3, ‖H y (unitVector a) (unitVector k)‖ ^ 2)
      (fun a _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i))

theorem int_bdd {a f g : Space → ℝ} {M : ℝ} (ha : AEStronglyMeasurable a volume) (hM : ∀ y, |a y| ≤ M)
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) : Integrable (fun y => a y * f y * g y) := by
  refine ((hf.integrable_mul hg).norm.const_mul M).mono' ((ha.mul hf.1).mul hg.1) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, mul_assoc, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hM y) (abs_nonneg _)

theorem coord_le (x : Space) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  rwa [Real.norm_eq_abs] at h

theorem centre_coord_bounds {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∃ C : ℝ, ∀ y (q j l : Fin 3), |c.centre y q| ≤ C ∧ |c.centreGrad y (unitVector j) q| ≤ C ∧
      |c.centreSecond y (unitVector j) (unitVector l) q| ≤ C := by
  obtain ⟨C, hC⟩ := hc.centre_bounds
  have hC0 := ModelFormInternal.centre_nonneg hC
  refine ⟨C, fun y q j l => ⟨?_, ?_, ?_⟩⟩
  · exact (coord_le _ q).trans ((hC y).1.trans (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 1 (by norm_num))))
  · refine (coord_le _ q).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [ModelFormInternal.norm_unitVector, mul_one]
    exact (hC y).2.1.trans (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 2 (by norm_num)))
  · refine (coord_le _ q).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
    rw [ModelFormInternal.norm_unitVector, mul_one]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ModelFormInternal.norm_unitVector, mul_one]
    exact (hC y).2.2.trans (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 3 (by norm_num)))

theorem centre_parts {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) (q j : Fin 3) :
    ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) * c.centre y q = -∫ y, φ y * c.centreGrad y (unitVector j) q := by
  intro φ hφ
  have hg1 : ContDiff ℝ 1 (fun y => c.centre y q) :=
    (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).contDiff.comp hc.centre_smooth
  have hdg : ∀ y, fderiv ℝ (fun y => c.centre y q) y (unitVector j) = c.centreGrad y (unitVector j) q := by
    intro y
    have hd : HasFDerivAt (fun y => c.centre y q)
        ((EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).comp (c.centreGrad y)) y :=
      (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).hasFDerivAt.comp y
        ((hc.centre_smooth.differentiable one_ne_zero) y).hasFDerivAt
    rw [hd.fderiv]
    rfl
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have cφ' : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have cg' : Continuous (fun y => fderiv ℝ (fun y => c.centre y q) y (unitVector j)) :=
    (hg1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) * c.centre y q) :=
    (cφ'.mul hg1.continuous).integrable_of_hasCompactSupport (hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)).mul_right
  have i2 : Integrable (fun y => φ y * fderiv ℝ (fun y => c.centre y q) y (unitVector j)) :=
    (hφ.1.continuous.mul cg').integrable_of_hasCompactSupport hφ.2.mul_right
  have i3 : Integrable (fun y => φ y * c.centre y q) :=
    (hφ.1.continuous.mul hg1.continuous).integrable_of_hasCompactSupport hφ.2.mul_right
  have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (v := unitVector j) i1 i2 i3
    (fun x _ => hφd x) (fun x _ => (hg1.differentiable one_ne_zero) x)
  simp only [hdg] at e
  rw [e, neg_neg]

theorem valuePart_integral {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) (q a b d e j : Fin 3) :
    Integrable (valuePart c G H q a b d e j) ∧ ∫ y, valuePart c G H q a b d e j y = 0 := by
  obtain ⟨C, hC⟩ := centre_coord_bounds hc
  have hUc : Continuous (fun y => c.centre y q) :=
    (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).continuous.comp hc.centre_smooth.continuous
  have hAc : Continuous (fun y => c.centreGrad y (unitVector j) q) :=
    (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).continuous.comp
      ((hc.centre_smooth.continuous_fderiv one_ne_zero).clm_apply continuous_const)
  have hGc : ∀ i l : Fin 3, MemLp (fun y => G y (unitVector l) i) 2 volume := fun i l =>
    memLp_coord (memLp_column hs.measurable_gradient hs.gradient_two l) i
  have hHc : ∀ i l : Fin 3, MemLp (fun y => H y (unitVector j) (unitVector l) i) 2 volume := fun i l =>
    memLp_coord (memLp_second hs j l) i
  have hw : ∀ i l : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) * G y (unitVector l) i = -∫ y, φ y * H y (unitVector j) (unitVector l) i :=
    fun i l => weak_coord (memLp_column hs.measurable_gradient hs.gradient_two l) one_le_two (memLp_second hs j l)
      one_le_two j i (fun ψ hψ => hs.weak_second ψ hψ l j)
  have i1 := int_bdd hAc.aestronglyMeasurable (fun y => (hC y q j j).2.1) (hGc a b) (hGc d e)
  have i2 := int_bdd hUc.aestronglyMeasurable (fun y => (hC y q j j).1) (hHc a b) (hGc d e)
  have i3 := int_bdd hUc.aestronglyMeasurable (fun y => (hC y q j j).1) (hGc a b) (hHc d e)
  have i0 := int_bdd hUc.aestronglyMeasurable (fun y => (hC y q j j).1) (hGc a b) (hGc d e)
  refine ⟨(i1.add i2).add i3, ?_⟩
  exact triple_parts j hUc ⟨C, fun y => (hC y q j j).1⟩ hAc.aestronglyMeasurable
    ⟨C, ae_of_all _ fun y => (hC y q j j).2.1⟩ (centre_parts hc q j) (hGc a b) le_rfl (hHc a b) (hw a b)
    (hGc d e) (hHc d e) (hw d e) i0 i1 i2 i3

theorem weighted_sq {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) {w : Space → ℝ}
    (hw : AEStronglyMeasurable w volume) {B : ℝ} (hB : ∀ y, |w y| * ‖y‖ ≤ B) (a : Fin 3) :
    Integrable (fun y => (w y * v y a) ^ 2) := by
  obtain ⟨hIi, -⟩ := inverseSquareBound v G hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  refine (hIi.const_mul (B ^ 2)).mono' ((hw.mul (memLp_coord hs.velocity_six a).1).pow 2) ?_
  filter_upwards [hne] with y hy0
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hb : |w y| ≤ B / ‖y‖ := by rw [le_div_iff₀ hy]; exact hB y
  have hv : |v y a| ≤ ‖v y‖ := coord_le _ a
  have hw0 : 0 ≤ |w y| := abs_nonneg _
  calc (w y * v y a) ^ 2 = |w y| ^ 2 * |v y a| ^ 2 := by rw [mul_pow, sq_abs, sq_abs]
    _ ≤ (B / ‖y‖) ^ 2 * ‖v y‖ ^ 2 :=
        mul_le_mul (pow_le_pow_left₀ hw0 hb 2) (pow_le_pow_left₀ (abs_nonneg _) hv 2) (sq_nonneg _) (sq_nonneg _)
    _ = B ^ 2 * (‖v y‖ ^ 2 / ‖y‖ ^ 2) := by rw [div_pow]; ring

theorem decay_mul_le (y : Space) {s : ℝ} (hs : 1 ≤ s) : (1 + ‖y‖) ^ (-s) * ‖y‖ ≤ 1 := by
  have hpos : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have h1 : (1 + ‖y‖) ^ (-s) ≤ (1 + ‖y‖) ^ (-(1 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg y]) (by linarith)
  have e : (1 + ‖y‖) ^ (-(1 : ℝ)) = (1 + ‖y‖)⁻¹ := Real.rpow_neg_one _
  calc (1 + ‖y‖) ^ (-s) * ‖y‖ ≤ (1 + ‖y‖)⁻¹ * ‖y‖ :=
        mul_le_mul_of_nonneg_right (e ▸ h1) (norm_nonneg y)
    _ ≤ (1 + ‖y‖)⁻¹ * (1 + ‖y‖) := mul_le_mul_of_nonneg_left (by linarith) (inv_nonneg.2 hpos.le)
    _ = 1 := inv_mul_cancel₀ hpos.ne'

theorem gradPart_integral {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) (q l a b j d : Fin 3) :
    Integrable (gradPart c v G H q l a b j d) ∧ ∫ y, gradPart c v G H q l a b j d y = 0 := by
  obtain ⟨C, hC⟩ := hc.centre_bounds
  have hC0 := ModelFormInternal.centre_nonneg hC
  have hgradv : ∀ y (i : Fin 3), ‖c.centreGrad y (unitVector i)‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro y i
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ModelFormInternal.norm_unitVector, mul_one]
    exact (hC y).2.1
  have hsecv : ∀ y (i i' : Fin 3), ‖c.centreSecond y (unitVector i) (unitVector i')‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y i i'
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ModelFormInternal.norm_unitVector, mul_one]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [ModelFormInternal.norm_unitVector, mul_one]
    exact (hC y).2.2
  have hAcol : Continuous (fun y => c.centreGrad y (unitVector l)) :=
    (hc.centre_smooth.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hAc : Continuous (fun y => c.centreGrad y (unitVector l) q) :=
    (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).continuous.comp hAcol
  have hKcol : AEStronglyMeasurable (fun y => c.centreSecond y (unitVector j) (unitVector l)) volume :=
    ((ContinuousLinearMap.apply ℝ Space (unitVector l)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous).comp_aestronglyMeasurable
      hc.centre_second.2
  have hKm : AEStronglyMeasurable (fun y => c.centreSecond y (unitVector j) (unitVector l) q) volume :=
    (EuclideanSpace.proj (𝕜 := ℝ) q : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hKcol
  have hAb : ∀ y, |c.centreGrad y (unitVector l) q| ≤ C := fun y =>
    (coord_le _ q).trans ((hgradv y l).trans
      (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 2 (by norm_num))))
  have hKb : ∀ y, |c.centreSecond y (unitVector j) (unitVector l) q| ≤ C := fun y =>
    (coord_le _ q).trans ((hsecv y j l).trans
      (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 3 (by norm_num))))
  have hAtop : MemLp (fun y => c.centreGrad y (unitVector l)) ⊤ volume :=
    memLp_top_of_bound hAcol.aestronglyMeasurable C (ae_of_all _ fun y => (hgradv y l).trans
      (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 2 (by norm_num))))
  have hKtop : MemLp (fun y => c.centreSecond y (unitVector j) (unitVector l)) ⊤ volume :=
    memLp_top_of_bound hKcol C (ae_of_all _ fun y => (hsecv y j l).trans
      (mul_le_of_le_one_right hC0 (ModelFormInternal.rpow_neg_le_one y 3 (by norm_num))))
  have haw := weak_coord hAtop le_top hKtop le_top j q (fun ψ hψ => hc.centre_second.1 ψ hψ l j)
  have hGc : ∀ i i' : Fin 3, MemLp (fun y => G y (unitVector i') i) 2 volume := fun i i' =>
    memLp_coord (memLp_column hs.measurable_gradient hs.gradient_two i') i
  have hHc : MemLp (fun y => H y (unitVector j) (unitVector d) b) 2 volume := memLp_coord (memLp_second hs j d) b
  have hwG : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) * G y (unitVector d) b = -∫ y, φ y * H y (unitVector j) (unitVector d) b :=
    weak_coord (memLp_column hs.measurable_gradient hs.gradient_two d) one_le_two (memLp_second hs j d)
      one_le_two j b (fun ψ hψ => hs.weak_second ψ hψ d j)
  have hwv : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, fderiv ℝ φ y (unitVector j) * v y a = -∫ y, φ y * G y (unitVector j) a :=
    weak_coord hs.velocity_six (by norm_num) (memLp_column hs.measurable_gradient hs.gradient_two j) one_le_two j a
      (fun ψ hψ => hs.weak_gradient ψ hψ j)
  have hAv : MemLp (fun y => c.centreGrad y (unitVector l) q * v y a) 2 volume := by
    refine (memLp_two_iff_integrable_sq (hAc.aestronglyMeasurable.mul (memLp_coord hs.velocity_six a).1)).2 ?_
    refine weighted_sq hs hAc.aestronglyMeasurable (B := C) (fun y => ?_) a
    calc |c.centreGrad y (unitVector l) q| * ‖y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖y‖ :=
          mul_le_mul_of_nonneg_right ((coord_le _ q).trans (hgradv y l)) (norm_nonneg y)
      _ = C * ((1 + ‖y‖) ^ (-(2 : ℝ)) * ‖y‖) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (decay_mul_le y (by norm_num)) hC0
      _ = C := mul_one C
  have hKv : MemLp (fun y => c.centreSecond y (unitVector j) (unitVector l) q * v y a) 2 volume := by
    refine (memLp_two_iff_integrable_sq (hKm.mul (memLp_coord hs.velocity_six a).1)).2 ?_
    refine weighted_sq hs hKm (B := C) (fun y => ?_) a
    calc |c.centreSecond y (unitVector j) (unitVector l) q| * ‖y‖ ≤ C * (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖ :=
          mul_le_mul_of_nonneg_right ((coord_le _ q).trans (hsecv y j l)) (norm_nonneg y)
      _ = C * ((1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left (decay_mul_le y (by norm_num)) hC0
      _ = C := mul_one C
  have i0 : Integrable (fun y => c.centreGrad y (unitVector l) q * v y a * G y (unitVector d) b) :=
    hAv.integrable_mul (hGc b d)
  have i1 : Integrable (fun y => c.centreSecond y (unitVector j) (unitVector l) q * v y a * G y (unitVector d) b) :=
    hKv.integrable_mul (hGc b d)
  have i2 := int_bdd hAc.aestronglyMeasurable hAb (hGc a j) (hGc b d)
  have i3 : Integrable (fun y => c.centreGrad y (unitVector l) q * v y a * H y (unitVector j) (unitVector d) b) :=
    hAv.integrable_mul hHc
  refine ⟨(i1.add i2).add i3, ?_⟩
  exact triple_parts j hAc ⟨C, hAb⟩ hKm ⟨C, ae_of_all _ hKb⟩ haw (memLp_coord hs.velocity_six a) (by norm_num)
    (hGc a j) hwv (hGc b d) hHc hwG i0 i1 i2 i3


theorem second_symm_field {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector i) (unitVector j) = H y (unitVector j) (unitVector i) := by
  have hm : ∀ i j : Fin 3, AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume := fun i j =>
    ((ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous).comp_aestronglyMeasurable
      hs.measurable_second
  have hloc : ∀ i j : Fin 3, LocallyIntegrable (fun y => H y (unitVector i) (unitVector j)) volume := by
    intro i j
    have h2 : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
      refine (memLp_two_iff_integrable_sq_norm (hm i j)).2 (hs.second_two.mono' ((hm i j).norm.pow 2) ?_)
      refine Filter.Eventually.of_forall fun y => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact (Finset.single_le_sum (f := fun k => ‖H y (unitVector i) (unitVector k)‖ ^ 2)
        (fun k _ => sq_nonneg _) (Finset.mem_univ j)).trans
        (Finset.single_le_sum (f := fun a => ∑ k : Fin 3, ‖H y (unitVector a) (unitVector k)‖ ^ 2)
          (fun a _ => Finset.sum_nonneg fun k _ => sq_nonneg _) (Finset.mem_univ i))
    exact h2.locallyIntegrable (by norm_num)
  have key : ∀ i j : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, φ y • H y (unitVector j) (unitVector i) = ∫ y, dirDeriv i (dirDeriv j φ) y • v y := by
    intro i j φ hφ
    have e1 := hs.weak_second φ hφ i j
    have e2 := hs.weak_gradient (dirDeriv j φ) (test_dirDeriv hφ j) i
    have e3 : ∫ y, φ y • H y (unitVector j) (unitVector i) = -∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i) := by
      rw [e1, neg_neg]
    rw [e3]
    exact e2.symm
  have hij : ∀ i j : Fin 3, ∀ᵐ y ∂volume, H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
    intro i j
    refine ae_eq_of_integral_contDiff_smul_eq (hloc j i) (hloc i j) fun φ hφ hcφ => ?_
    rw [key i j φ ⟨hφ, hcφ⟩, key j i φ ⟨hφ, hcφ⟩, dirDeriv_comm hφ]
  have hall : ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact hij i
  filter_upwards [hall] with y hy i j
  exact hy j i

end CentreIdentityParts

end CellCert

end Breakdown

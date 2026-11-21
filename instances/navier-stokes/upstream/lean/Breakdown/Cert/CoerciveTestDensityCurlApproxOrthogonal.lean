import Breakdown.Cert.CoerciveTestDensityCurlApproxBase

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof Freq.Internal.NiceApprox

private def testPot (k : ℕ) (y : Space) (i : Fin 3) : Space → Space := fun x => kern k (y - x) • unitVector i

private def testCurl (k : ℕ) (y : Space) (i : Fin 3) : Space → Space := curlField (testPot k y i)

private theorem contDiff_kern (k : ℕ) : ContDiff ℝ ∞ (kern k) := (bump k).contDiff_normed

private theorem hasCompactSupport_kern (k : ℕ) : HasCompactSupport (kern k) := (bump k).hasCompactSupport_normed

private theorem contDiff_testPot (k : ℕ) (y : Space) (i : Fin 3) : ContDiff ℝ ∞ (testPot k y i) :=
  ((contDiff_kern k).comp (contDiff_const.sub contDiff_id)).smul contDiff_const

private theorem hasCompactSupport_testPot (k : ℕ) (y : Space) (i : Fin 3) :
    HasCompactSupport (testPot k y i) := by
  have h : HasCompactSupport (fun x => kern k (y - x)) :=
    (hasCompactSupport_kern k).comp_homeomorph (Homeomorph.subLeft y)
  exact h.smul_right

private theorem isTestField_testCurl (k : ℕ) (y : Space) (i : Fin 3) : IsTestField (testCurl k y i) :=
  ⟨contDiff_curlField (contDiff_testPot k y i), hasCompactSupport_curlField (hasCompactSupport_testPot k y i),
    divergence_curlField (contDiff_testPot k y i)⟩

private theorem fderiv_testPot (k : ℕ) (y : Space) (i : Fin 3) (x v : Space) :
    fderiv ℝ (testPot k y i) x v = -(fderiv ℝ (kern k) (y - x) v) • unitVector i := by
  have h1 : HasFDerivAt (fun x => kern k (y - x)) ((fderiv ℝ (kern k) (y - x)).comp
      (-(ContinuousLinearMap.id ℝ Space))) x :=
    ((contDiff_kern k).differentiable (by simp) (y - x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_sub y)
  have h2 := h1.smul_const (unitVector i)
  rw [show testPot k y i = fun x => kern k (y - x) • unitVector i from rfl, h2.fderiv]
  simp

private def curlComp (i : Fin 3) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l •
    ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector j)))

private theorem curlVec_apply (G : Space →L[ℝ] Space) (i : Fin 3) : curlVec G i = curlComp i G := by
  simp [curlVec, curlComp, unitVector, Pi.single_apply]

private theorem inner_testCurl (k : ℕ) (y : Space) (i : Fin 3) (x : Space) (w : Space) :
    inner ℝ w (testCurl k y i x) = ∑ j : Fin 3, ∑ l : Fin 3,
      alternatingSymbol i j l * (fderiv ℝ (kern k) (y - x) (unitVector j) * w l) := by
  simp only [testCurl, curlField, pd, fderiv_testPot]
  fin_cases i <;> simp [Fin.sum_univ_three, crossL_apply, unitVector, alternatingSymbol, inner] <;> ring

private theorem curl_conv_apply (k : ℕ) {g : Space → Space} (hg : LocallyIntegrable g volume) (y : Space)
    (i : Fin 3) :
    curlVec (fderiv ℝ (convolution (kern k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) y) i =
      ∫ x, inner ℝ (g x) (testCurl k y i x) := by
  have hd := (hasCompactSupport_kern k).hasFDerivAt_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) ((contDiff_kern k).of_le (by simp)) hg y
  rw [hd.fderiv]
  have hKc : Continuous (fderiv ℝ (kern k)) := (contDiff_kern k).continuous_fderiv (by simp)
  have hKs : HasCompactSupport (fderiv ℝ (kern k)) := (hasCompactSupport_kern k).fderiv (𝕜 := ℝ)
  have hex := hKs.convolutionExists_left ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) hKc hg y
  rw [convolution_def, curlVec_apply, ← ContinuousLinearMap.integral_comp_comm _ hex.integrable,
    ← integral_sub_left_eq_self _ volume y]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [sub_sub_cancel]
  rw [inner_testCurl]
  simp [curlComp, mul_comm]

private theorem slice_orth {F Q : ℝ → Space → Space}
    (hFm : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) (hQ : IsSolenoidalPartOf F Q)
    {w : Space → Space} (hw : IsTestField w) :
    ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∫ y, inner ℝ (Q σ y) (w y) = ∫ y, inner ℝ (F σ y) (w y) := by
  have hQm := memLp_of hQ.1 hQ.2.2.1
  have hwm : MemLp w 2 volume := hw.1.continuous.memLp_of_hasCompactSupport hw.2.1
  have iQ := integrableOn_slicePairing hQm hwm
  have iF := integrableOn_slicePairing hFm hwm
  have h := ae_zero_of_periodic_tests (iQ.sub iF) (fun a ha has hsub => by
    have e := hQ.2.2.2.2 _ (isPeriodicTestField_prod ha has hw)
    simp only [real_inner_smul_right, integral_const_mul] at e
    have c : ContinuousOn (periodicExt a) (Icc (0 : ℝ) 1) :=
      (periodicExt_contDiff ha has).continuous.continuousOn
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub (iQ.continuousOn_mul c isCompact_Icc) (iF.continuousOn_mul c isCompact_Icc), e,
      sub_self])
  filter_upwards [h] with σ hσ
  exact sub_eq_zero.1 hσ

private theorem continuous_curl_conv (k : ℕ) {g : Space → Space} (hg : LocallyIntegrable g volume) :
    Continuous (fun y =>
      curlVec (fderiv ℝ (convolution (kern k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) y)) := by
  have hc := (hasCompactSupport_kern k).contDiff_convolution_left
    (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume) (n := ⊤) (contDiff_kern k) hg
  have hfd := hc.continuous_fderiv (by simp)
  unfold curlVec
  refine continuous_finsetSum _ fun i _ => ?_
  have hs : Continuous fun y => ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
      ((fderiv ℝ (convolution (kern k) g (ContinuousLinearMap.lsmul ℝ ℝ) volume) y)
        (unitVector j)).ofLp l := by
    refine continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => ?_
    exact continuous_const.mul
      ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp (hfd.clm_apply continuous_const))
  exact hs.smul continuous_const

theorem curl_moll_solenoidal_part {F Q : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (_hp : IsTimePeriodic F)
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) (hQ : IsSolenoidalPartOf F Q) (k : ℕ) :
    ∀ᵐ z ∂periodMeasure, curlVec (fderiv ℝ (moll k Q z.1) z.2) =
      curlVec (fderiv ℝ (moll k F z.1) z.2) := by
  have hFm := memLp_of_continuous hF.continuous hR
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense Space
  have hall : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ p : D × Fin 3,
      ∫ y, inner ℝ (Q σ y) (testCurl k p.1 p.2 y) = ∫ y, inner ℝ (F σ y) (testCurl k p.1 p.2 y) := by
    have := hDc.to_subtype
    rw [ae_all_iff]
    intro p
    exact slice_orth hFm hQ (isTestField_testCurl k p.1 p.2)
  have hgood : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ y,
      curlVec (fderiv ℝ (moll k Q σ) y) = curlVec (fderiv ℝ (moll k F σ) y) := by
    filter_upwards [hall, slice_memLp (memLp_of hQ.1 hQ.2.2.1)] with σ h1 h2
    have lQ : LocallyIntegrable (Q σ) volume := h2.locallyIntegrable (by norm_num)
    have lF : LocallyIntegrable (F σ) volume :=
      (hF.continuous.comp (continuous_const.prodMk continuous_id)).locallyIntegrable
    have hD : Set.EqOn (fun y => curlVec (fderiv ℝ (moll k Q σ) y))
        (fun y => curlVec (fderiv ℝ (moll k F σ) y)) D := fun y hy => by
      ext i
      simp only [moll]
      rw [curl_conv_apply k lQ, curl_conv_apply k lF]
      exact h1 (⟨y, hy⟩, i)
    intro y
    exact congrFun (Continuous.ext_on hDd (continuous_curl_conv k lQ) (continuous_curl_conv k lF) hD) y
  have hnull := ae_iff.1 hgood
  obtain ⟨N, hsub, hNm, hN0⟩ := exists_measurable_superset_of_null hnull
  rw [ae_iff]
  refine measure_mono_null (t := N ×ˢ (univ : Set Space)) ?_ ?_
  · intro z hz
    exact ⟨hsub (fun h => hz (h z.2)), trivial⟩
  · rw [Measure.prod_prod, hN0, zero_mul]

end Internal.CurlGraphMollify

end Breakdown.Coercive

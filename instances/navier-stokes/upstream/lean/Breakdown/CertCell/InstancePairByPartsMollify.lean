import Breakdown.CertCell.InstancePairStatements
import Breakdown.FracCell.ReductionLossRotationLeaves
import Breakdown.Cert.ReadingEnergy

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace InstancePair

namespace Internal.ByPartsMollify

theorem memLp_two_of_lintegral {u : Space → Space} (hm : AEStronglyMeasurable u volume)
    (h : ∫⁻ y, ENNReal.ofReal (‖u y‖ ^ 2) < ⊤) : MemLp u 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm hm).2 ⟨hm.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => by positivity)]
  exact h

theorem column_memLp {A : Space → (Space →L[ℝ] Space)} (j : Fin 3)
    (hm : AEStronglyMeasurable (fun y => A y (unitVector j)) volume)
    (hA : ∫⁻ y, ENNReal.ofReal (matSq (A y)) < ⊤) : MemLp (fun y => A y (unitVector j)) 2 volume := by
  refine memLp_two_of_lintegral hm (lt_of_le_of_lt (lintegral_mono fun y => ?_) hA)
  refine ENNReal.ofReal_le_ofReal ?_
  unfold matSq
  exact Finset.single_le_sum (f := fun i => ‖A y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

theorem tendsto_integral_inner {u : ℕ → Space → Space} {g a : Space → Space}
    (hu : ∀ n, MemLp (u n) 2 volume) (hg : MemLp g 2 volume) (ha : MemLp a 2 volume)
    (h : Tendsto (fun n => eLpNorm (fun x => u n x - g x) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, inner ℝ (a y) (u n y)) atTop (𝓝 (∫ y, inner ℝ (a y) (g y))) := by
  have hL : Tendsto (fun n => (hu n).toLp (u n)) atTop (𝓝 (hg.toLp g)) := by
    rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
    refine h.congr fun n => ?_
    refine eLpNorm_congr_ae ?_
    filter_upwards [(hu n).coeFn_toLp, hg.coeFn_toLp] with x h1 h2
    rw [Pi.sub_apply, h1, h2]
  have ht := (tendsto_const_nhds (x := ha.toLp a)).inner (𝕜 := ℝ) hL
  have e : ∀ (w : Space → Space) (hw : MemLp w 2 volume),
      inner ℝ (ha.toLp a) (hw.toLp w) = ∫ y, inner ℝ (a y) (w y) := by
    intro w hw
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [ha.coeFn_toLp, hw.coeFn_toLp] with x h1 h2
    rw [h1, h2]
  rw [e g hg] at ht
  exact ht.congr fun n => e (u n) (hu n)

theorem integrable_inner_of_memLp {a b : Space → Space} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    Integrable (fun y => inner ℝ (a y) (b y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (ha.toLp a) (hb.toLp b)).congr ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
  rw [h1, h2]

theorem fderiv_coord {φ : Space → Space} {y : Space} (hφ : DifferentiableAt ℝ φ y) (j k : Fin 3) :
    fderiv ℝ (fun z => φ z k) y (unitVector j) = fderiv ℝ φ y (unitVector j) k := by
  have h := ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y hφ.hasFDerivAt).fderiv
  simp only [Function.comp_def] at h
  show fderiv ℝ (fun z => (EuclideanSpace.proj k : Space →L[ℝ] ℝ) (φ z)) y (unitVector j) = _
  rw [h]
  simp

theorem coord_contDiff {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun z => φ z k) :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hφ

theorem coord_hasCompactSupport {φ : Space → Space} (hφ : HasCompactSupport φ) (k : Fin 3) :
    HasCompactSupport (fun z => φ z k) :=
  hφ.comp_left (g := fun x : Space => x k) (by simp)

theorem integrable_coord_smul {F : Space → Space} (hF : LocallyIntegrable F volume) {ψ : Space → ℝ}
    (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (k : Fin 3) :
    Integrable (fun y => ψ y * F y k) volume := by
  have h := (hF.integrable_smul_left_of_hasCompactSupport hψ hψc)
  have h2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp h
  refine h2.congr (Eventually.of_forall fun y => ?_)
  simp

theorem coord_by_parts {G0 : Space → (Space →L[ℝ] Space)} {H0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : ∀ j, IsWeakGradient (fun y => G0 y (unitVector j)) (fun y => (H0 y).flip (unitVector j)))
    {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (j k : Fin 3) :
    ∫ y, φ y k * H0 y (unitVector j) (unitVector j) k =
      -∫ y, fderiv ℝ φ y (unitVector j) k * G0 y (unitVector j) k := by
  have hψ := coord_contDiff hφ k
  have hψc := coord_hasCompactSupport hφc k
  have hw := (hG j).2.2 (fun z => φ z k) ⟨hψ, hψc⟩ j
  have hP : Integrable (fun y => φ y k • ((H0 y).flip (unitVector j)) (unitVector j)) volume := by
    have h := ((hG j).2.1.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc).apply_continuousLinearMap
      (unitVector j)
    refine h.congr (Eventually.of_forall fun y => ?_)
    simp
  have hdc : Continuous (fun y => fderiv ℝ (fun z => φ z k) y (unitVector j)) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdcs : HasCompactSupport (fun y => fderiv ℝ (fun z => φ z k) y (unitVector j)) :=
    (hψc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
  have hQ : Integrable (fun y => fderiv ℝ (fun z => φ z k) y (unitVector j) • G0 y (unitVector j)) volume :=
    (hG j).1.integrable_smul_left_of_hasCompactSupport hdc hdcs
  have hk := congrArg (EuclideanSpace.proj k : Space →L[ℝ] ℝ) hw
  rw [← (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hP, map_neg,
    ← (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hQ] at hk
  have hd : ∀ y, fderiv ℝ (fun z => φ z k) y (unitVector j) = fderiv ℝ φ y (unitVector j) k :=
    fun y => fderiv_coord ((hφ.differentiable (by simp)) y) j k
  simp only [hd] at hk
  simpa using hk


theorem second_column_locallyIntegrable {G0 : Space → (Space →L[ℝ] Space)}
    {H0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : ∀ j, IsWeakGradient (fun y => G0 y (unitVector j)) (fun y => (H0 y).flip (unitVector j))) (j : Fin 3) :
    LocallyIntegrable (fun y => H0 y (unitVector j) (unitVector j)) volume :=
  Cert.Internal.ReadingEnergy.locallyIntegrable_column (hG j).2.1 j

theorem trace_pairing_test {G0 : Space → (Space →L[ℝ] Space)} {H0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : ∀ j, IsWeakGradient (fun y => G0 y (unitVector j)) (fun y => (H0 y).flip (unitVector j)))
    {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) :
    ∫ y, inner ℝ (secondDerivTrace (H0 y)) (φ y) =
      -∑ j : Fin 3, ∫ y, inner ℝ (G0 y (unitVector j)) (fderiv ℝ φ y (unitVector j)) := by
  have hI1 : ∀ j k, Integrable (fun y => φ y k * H0 y (unitVector j) (unitVector j) k) volume := fun j k =>
    integrable_coord_smul (second_column_locallyIntegrable hG j) (coord_contDiff hφ k).continuous
      (coord_hasCompactSupport hφc k) k
  have hdc : ∀ j k, Continuous (fun y => fderiv ℝ φ y (unitVector j) k) := fun j k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
  have hdcs : ∀ j k, HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j) k) := fun j k =>
    (hφc.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector j) k) (by simp)
  have hI2 : ∀ j k, Integrable (fun y => fderiv ℝ φ y (unitVector j) k * G0 y (unitVector j) k) volume :=
    fun j k => integrable_coord_smul (hG j).1 (hdc j k) (hdcs j k) k
  have e1 : ∀ y, inner ℝ (secondDerivTrace (H0 y)) (φ y) =
      ∑ j, ∑ k, φ y k * H0 y (unitVector j) (unitVector j) k := by
    intro y
    simp only [secondDerivTrace, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [Finset.mul_sum]
  have e2 : ∀ j y, inner ℝ (G0 y (unitVector j)) (fderiv ℝ φ y (unitVector j)) =
      ∑ k, fderiv ℝ φ y (unitVector j) k * G0 y (unitVector j) k := by
    intro j y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ fun k _ => hI1 j k), ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ (fun k _ => hI1 j k), integral_finsetSum _ (fun k _ => hI2 j k),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => coord_by_parts hG hφ hφc j k


theorem trace_pairing_by_parts {f : Space → Space} {Df : Space → (Space →L[ℝ] Space)}
    {G0 : Space → (Space →L[ℝ] Space)} {H0 : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hf : IsWeakGradient f Df) {B R : ℝ} (hB : ∀ y, ‖f y‖ ≤ B) (hR : ∀ y, R < ‖y‖ → f y = 0)
    (hDf : ∫⁻ y, ENNReal.ofReal (matSq (Df y)) < ⊤)
    (hG : ∀ j, IsWeakGradient (fun y => G0 y (unitVector j)) (fun y => (H0 y).flip (unitVector j)))
    (hGf : ∫⁻ y, ENNReal.ofReal (matSq (G0 y)) < ⊤)
    (hH : ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (H0 y)‖ ^ 2) < ⊤) :
    ∫ y, inner ℝ (-secondDerivTrace (H0 y)) (f y) = ∫ y, matInner (G0 y) (Df y) := by
  obtain ⟨ρ, hρs, hρc, hρ1, hρL⟩ := CellCert.Reduction.rotationMollifier
  have hout : ∀ y, y ∉ Metric.closedBall (0 : Space) R → f y = 0 := fun y hy =>
    hR y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)
  have hfcs : HasCompactSupport f := HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) hout
  have hfL : MemLp f 2 volume := by
    have htop : MemLp f ⊤ volume := memLp_top_of_bound hf.1.aestronglyMeasurable B (Eventually.of_forall hB)
    exact htop.mono_exponent_of_measure_support_ne_top hout measure_closedBall_lt_top.ne le_top
  set φ : ℕ → Space → Space := fun n => convolution (ρ n) f (ContinuousLinearMap.lsmul ℝ ℝ) volume with hφdef
  have hφs : ∀ n, ContDiff ℝ ∞ (φ n) := fun n => (hρc n).contDiff_convolution_left _ (hρs n) hf.1
  have hφc : ∀ n, HasCompactSupport (φ n) := fun n => (hρc n).convolution _ hfcs
  have hcol : ∀ j, LocallyIntegrable (fun y => Df y (unitVector j)) volume :=
    Cert.Internal.ReadingEnergy.locallyIntegrable_column hf.2.1
  have hweak : SteadyCert.IsWeakGradientOf f Df := by
    intro ψ hψ j
    rw [hf.2.2 ψ ⟨hψ.1, hψ.2⟩ j, neg_neg]
  have hder : ∀ n y j, fderiv ℝ (φ n) y (unitVector j) =
      convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume y := by
    intro n y j
    have h := CellCert.Reduction.convGradient (ρ n) (hρs n) (hρc n) (hρ1 n) f Df hf.1 hcol hweak Set.univ
      MeasurableSet.univ y (Set.subset_univ _) j
    simpa only [Set.indicator_univ] using h
  have hφL : ∀ n, MemLp (φ n) 2 volume := fun n => (hφs n).continuous.memLp_of_hasCompactSupport (hφc n)
  have hdL : ∀ n j, MemLp (convolution (ρ n) (fun z => Df z (unitVector j))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume) 2 volume := by
    intro n j
    have e : convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume =
        fun y => fderiv ℝ (φ n) y (unitVector j) := funext fun y => (hder n y j).symm
    rw [e]
    exact (((hφs n).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (((hφc n).fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector j)) (by simp))
  have hDfL : ∀ j, MemLp (fun y => Df y (unitVector j)) 2 volume := fun j =>
    column_memLp j (hcol j).aestronglyMeasurable hDf
  have hGL : ∀ j, MemLp (fun y => G0 y (unitVector j)) 2 volume := fun j =>
    column_memLp j (hG j).1.aestronglyMeasurable hGf
  have hTm : AEStronglyMeasurable (fun y => secondDerivTrace (H0 y)) volume := by
    have e : (fun y => secondDerivTrace (H0 y)) = fun y => ∑ j, H0 y (unitVector j) (unitVector j) := rfl
    rw [e]
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (second_column_locallyIntegrable hG j).aestronglyMeasurable
  have hTL : MemLp (fun y => secondDerivTrace (H0 y)) 2 volume := memLp_two_of_lintegral hTm hH
  have ha := tendsto_integral_inner hφL hfL hTL (hρL f hfL)
  have hb : ∀ j, Tendsto (fun n => ∫ y, inner ℝ (G0 y (unitVector j))
      (convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume y)) atTop
      (𝓝 (∫ y, inner ℝ (G0 y (unitVector j)) (Df y (unitVector j)))) :=
    fun j => tendsto_integral_inner (fun n => hdL n j) (hDfL j) (hGL j) (hρL _ (hDfL j))
  have hsum := (tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun j _ => hb j).neg
  have heq : ∀ n, ∫ y, inner ℝ (secondDerivTrace (H0 y)) (φ n y) = -∑ j, ∫ y, inner ℝ (G0 y (unitVector j))
      (convolution (ρ n) (fun z => Df z (unitVector j)) (ContinuousLinearMap.lsmul ℝ ℝ) volume y) := by
    intro n
    rw [trace_pairing_test hG (hφs n) (hφc n)]
    simp only [hder]
  have hlim := tendsto_nhds_unique ha (hsum.congr fun n => (heq n).symm)
  have hfi : ∀ y, matInner (G0 y) (Df y) = ∑ j, inner ℝ (G0 y (unitVector j)) (Df y (unitVector j)) :=
    fun y => rfl
  simp_rw [inner_neg_left, hfi]
  rw [integral_neg, hlim, neg_neg,
    integral_finsetSum _ fun j _ => integrable_inner_of_memLp (hGL j) (hDfL j)]

end Internal.ByPartsMollify

end InstancePair

end CertCell

end Breakdown

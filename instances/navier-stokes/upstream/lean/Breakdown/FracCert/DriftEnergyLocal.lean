import Breakdown.FracCert.StFree
import Breakdown.Cert.CoerciveSmoothApproxPeriodBound

open scoped ContDiff ENNReal
open MeasureTheory Real Filter Topology
open scoped Convolution Pointwise

noncomputable section

namespace Breakdown

namespace SteadyCert

def driftBoundary (α a : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (χ : Space → ℝ)
    (y : Space) : ℝ :=
  ∑ i : Fin 3, fderiv ℝ χ y (unitVector i) * inner ℝ (driftField α a v G y) (G y (unitVector i))
    - (1 / 2) * fderiv ℝ χ y ((1 / (2 * α)) • y + a • axialTurn y) * entrySq (G y)

def DriftLocalStatement : Prop :=
  ∀ (α a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ χ : Space → ℝ, IsTestScalar χ →
    ∫ y, χ y * inner ℝ (driftField α a v G y) (negSecondTrace H y) =
      (1 - 3 / (4 * α)) * (∫ y, χ y * entrySq (G y)) + ∫ y, driftBoundary α a v G χ y

def DriftLocalSmoothStatement : Prop :=
  ∀ (α a : ℝ) (u : Space → Space), ContDiff ℝ ∞ u → ∀ χ : Space → ℝ, IsTestScalar χ →
    ∫ y, χ y * inner ℝ (driftField α a u (fderiv ℝ u) y)
        (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y) =
      (1 - 3 / (4 * α)) * (∫ y, χ y * entrySq (fderiv ℝ u y))
        + ∫ y, driftBoundary α a u (fderiv ℝ u) χ y

def DriftLocalApproxStatement : Prop :=
  ∀ (α a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ χ : Space → ℝ, IsTestScalar χ →
    ∃ u : ℕ → Space → Space, (∀ n, ContDiff ℝ ∞ (u n)) ∧
      Tendsto (fun n => ∫ y, χ y * inner ℝ (driftField α a (u n) (fderiv ℝ (u n)) y)
          (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ (u n)) z) y)) atTop
        (𝓝 (∫ y, χ y * inner ℝ (driftField α a v G y) (negSecondTrace H y))) ∧
      Tendsto (fun n => ∫ y, χ y * entrySq (fderiv ℝ (u n) y)) atTop
        (𝓝 (∫ y, χ y * entrySq (G y))) ∧
      Tendsto (fun n => ∫ y, driftBoundary α a (u n) (fderiv ℝ (u n)) χ y) atTop
        (𝓝 (∫ y, driftBoundary α a v G χ y))

def driftFlux (α a : ℝ) (u : Space → Space) (χ : Space → ℝ) (i : Fin 3) (y : Space) : ℝ :=
  χ y * (-(inner ℝ (driftField α a u (fderiv ℝ u) y) (fderiv ℝ u y (unitVector i)))
    + (1 / 2) * ((1 / (2 * α)) * y i + a * axialTurn y i) * entrySq (fderiv ℝ u y))

def DriftDivergenceStatement : Prop :=
  ∀ (α a : ℝ) (u : Space → Space), ContDiff ℝ ∞ u → ∀ χ : Space → ℝ, ContDiff ℝ ∞ χ →
    ∀ y, ∑ i : Fin 3, fderiv ℝ (driftFlux α a u χ i) y (unitVector i) =
      χ y * inner ℝ (driftField α a u (fderiv ℝ u) y) (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ u) z) y)
        - (1 - 3 / (4 * α)) * (χ y * entrySq (fderiv ℝ u y)) - driftBoundary α a u (fderiv ℝ u) χ y


private def approxBump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / (2 * ((n : ℝ) + 1)), 1 / ((n : ℝ) + 1), by positivity, by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    linarith⟩

private def smoothen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) (f : Space → E) :
    Space → E :=
  (approxBump n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f

private theorem approxBump_rOut_le (n : ℕ) : (approxBump n).rOut ≤ 1 := by
  show 1 / ((n : ℝ) + 1) ≤ 1
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

private theorem approxBump_rOut_tendsto : Tendsto (fun n => (approxBump n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0)
  exact tendsto_one_div_add_atTop_nhds_zero_nat

private theorem smoothen_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (n : ℕ) {f : Space → E} (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (smoothen n f) :=
  (approxBump n).hasCompactSupport_normed.contDiff_convolution_left _ (approxBump n).contDiff_normed hf

private theorem smoothen_partial (n : ℕ) {f g : Space → Space} (hf : LocallyIntegrable f volume)
    (j : Fin 3) (hw : ∀ φ : Space → ℝ, IsTestScalar φ →
      ∫ y, (fderiv ℝ φ y (unitVector j)) • f y = -∫ y, φ y • g y) (y : Space) :
    fderiv ℝ (smoothen n f) y (unitVector j) = smoothen n g y := by
  set φ := approxBump n
  have hcf : HasCompactSupport (φ.normed volume) := φ.hasCompactSupport_normed
  have hcd : ContDiff ℝ ∞ (φ.normed volume) := φ.contDiff_normed
  have hd1 : ContDiff ℝ 1 (φ.normed volume) := hcd.of_le (by simp)
  have hder := hcf.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hd1 hf y
  unfold smoothen
  rw [hder.fderiv]
  have hex := (hcf.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Space →L[ℝ] Space).precompL Space)
    (hcd.continuous_fderiv (by simp)) hf y
  rw [convolution_eq_swap, ContinuousLinearMap.integral_apply hex.integrable_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.precompL_apply, ContinuousLinearMap.lsmul_apply]
  set ψ : Space → ℝ := fun s => φ.normed volume (y - s) with hψ
  have hψt : IsTestScalar ψ :=
    ⟨hcd.comp (contDiff_const.sub contDiff_id), hcf.comp_homeomorph (Homeomorph.subLeft y)⟩
  have hψd : ∀ s, fderiv ℝ ψ s (unitVector j) = -fderiv ℝ (φ.normed volume) (y - s) (unitVector j) := by
    intro s
    have h1 : HasFDerivAt (φ.normed volume) (fderiv ℝ (φ.normed volume) (y - s)) (y - s) :=
      ((hcd.differentiable (by simp)) (y - s)).hasFDerivAt
    have h2 : HasFDerivAt ψ ((fderiv ℝ (φ.normed volume) (y - s)).comp
        (-ContinuousLinearMap.id ℝ Space)) s :=
      h1.comp s ((hasFDerivAt_id s).const_sub y)
    rw [h2.fderiv]
    simp
  have hwj := hw ψ hψt
  simp only [hψd, neg_smul, integral_neg] at hwj
  exact neg_injective hwj

private theorem approxBump_lintegral (n : ℕ) : ∫⁻ t, ‖(approxBump n).normed volume t‖ₑ = 1 := by
  calc ∫⁻ t, ‖(approxBump n).normed volume t‖ₑ
        = ∫⁻ t, ENNReal.ofReal ((approxBump n).normed volume t) :=
        lintegral_congr fun t => by
          rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg ((approxBump n).nonneg_normed t)]
    _ = ENNReal.ofReal (∫ t, (approxBump n).normed volume t) :=
        (ofReal_integral_eq_lintegral_ofReal (approxBump n).integrable_normed
          (Eventually.of_forall (approxBump n).nonneg_normed)).symm
    _ = 1 := by rw [(approxBump n).integral_normed, ENNReal.ofReal_one]

private theorem smoothen_sq_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ)
    {h : Space → E} (hh : AEStronglyMeasurable h volume) :
    ∫⁻ x, ‖∫ t, (approxBump n).normed volume t • h (x - t)‖ₑ ^ 2 ≤ ∫⁻ x, ‖h x‖ₑ ^ 2 := by
  set ρ := (approxBump n).normed volume with hρ
  set F : Space → ℝ≥0∞ := fun z => ‖h z‖ₑ ^ 2 with hFdef
  have hF : AEMeasurable F volume := hh.enorm.pow_const 2
  have hρc : Continuous ρ := (approxBump n).continuous_normed
  have hone : ∫⁻ t, ‖ρ t‖ₑ = 1 := approxBump_lintegral n
  have hpt : ∀ x : Space, ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2 ≤
      (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * F (x - t) := by
    intro x
    have h1 : ‖∫ t, ρ t • h (x - t)‖ₑ ≤ ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ :=
      (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (by simp only [enorm_smul]))
    have hm : AEMeasurable (fun t => ‖h (x - t)‖ₑ) volume :=
      hh.enorm.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume x)
    calc ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2 ≤ (∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * ‖h (x - t)‖ₑ ^ 2 :=
          Coercive.Internal.SmoothApprox.sq_lintegral_mul_le_prod hρc.enorm.aemeasurable hm
  have hK0 : AEMeasurable (fun p : Space × Space => ‖ρ p.2‖ₑ * F (p.1 - p.2))
      ((volume : Measure Space).prod volume) :=
    (hρc.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  calc ∫⁻ x, ‖∫ t, ρ t • h (x - t)‖ₑ ^ 2
      ≤ ∫⁻ x, (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * F (x - t) := lintegral_mono hpt
    _ = (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ∫⁻ x, ‖ρ t‖ₑ * F (x - t) := by
        rw [lintegral_const_mul' _ _ (by rw [hone]; exact ENNReal.one_ne_top),
          lintegral_lintegral_swap (f := fun x t => ‖ρ t‖ₑ * F (x - t)) hK0]
    _ = (∫⁻ t, ‖ρ t‖ₑ) * ∫⁻ t, ‖ρ t‖ₑ * ∫⁻ x, F x := by
        congr 1
        refine lintegral_congr fun t => ?_
        rw [lintegral_const_mul' _ _ enorm_ne_top, lintegral_sub_right_eq_self]
    _ = ∫⁻ x, ‖h x‖ₑ ^ 2 := by
        rw [lintegral_mul_const _ hρc.enorm.measurable, ← mul_assoc, hone, one_mul, one_mul]

private theorem eLpNorm_two_sq_space {E : Type*} [NormedAddCommGroup E] (μ : Measure Space)
    (f : Space → E) : eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  have := eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) two_ne_zero
  simpa using this

private theorem eLpNorm_tendsto_of_sq_space {E : Type*} [NormedAddCommGroup E] {F : ℕ → Space → E}
    (h : Tendsto (fun n => ∫⁻ x, ‖F n x‖ₑ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) 2 volume) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero] at h ⊢
  intro ε hε
  filter_upwards [h (ε ^ 2) (ENNReal.pow_pos hε 2)] with n hn
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq_space]
  exact hn

private theorem smoothen_sub_eLpNorm_le (n : ℕ) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f g : Space → E} (hf : LocallyIntegrable f volume)
    (hg : LocallyIntegrable g volume) :
    eLpNorm (fun x => smoothen n f x - smoothen n g x) 2 volume ≤ eLpNorm (f - g) 2 volume := by
  have hcs := (approxBump n).hasCompactSupport_normed (μ := volume)
  have hcc := (approxBump n).continuous_normed (μ := volume)
  have e : ∀ x, smoothen n f x - smoothen n g x =
      ∫ t, (approxBump n).normed volume t • (f - g) (x - t) := by
    intro x
    have I1 : Integrable (fun t => (approxBump n).normed volume t • f (x - t)) volume :=
      hcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hcc hf x
    have I2 : Integrable (fun t => (approxBump n).normed volume t • g (x - t)) volume :=
      hcs.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hcc hg x
    simp only [smoothen, convolution_def, ContinuousLinearMap.lsmul_apply, Pi.sub_apply, smul_sub]
    exact (integral_sub I1 I2).symm
  have hy := smoothen_sq_le n (hf.aestronglyMeasurable.sub hg.aestronglyMeasurable)
  rw [← ENNReal.pow_le_pow_left_iff two_ne_zero, eLpNorm_two_sq_space, eLpNorm_two_sq_space]
  simp only [e]
  exact hy


private theorem smoothen_sq_tendsto_of_continuous {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {g : Space → E} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => ∫⁻ x, ‖smoothen n g x - g x‖ₑ ^ 2) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  set S : Set Space := Metric.closedBall 0 1 + tsupport g with hSdef
  have hS : IsCompact S := (isCompact_closedBall 0 1).add hgc
  have hconv : ∀ n, Continuous (smoothen n g) := fun n =>
    (smoothen_contDiff n hg.locallyIntegrable).continuous
  have hsupp : ∀ n x, x ∉ S → smoothen n g x - g x = 0 := by
    intro n x hx
    have h1 : smoothen n g x = 0 := by
      by_contra h
      exact hx (Set.add_subset_add
        (((approxBump n).support_normed_eq (μ := volume)).subset.trans
          (Metric.ball_subset_closedBall.trans
            (Metric.closedBall_subset_closedBall (approxBump_rOut_le n))))
        (subset_tsupport g) (support_convolution_subset _ h))
    have h2 : g x = 0 := by
      by_contra h
      exact hx ⟨0, Metric.mem_closedBall_self (by norm_num), x, subset_tsupport g h, zero_add x⟩
    simp [h1, h2]
  have hbd : ∀ n x, ‖smoothen n g x‖ ≤ M := by
    intro n x
    have := dist_convolution_le (μ := volume) (x₀ := x) (R := 2) (z₀ := (0 : E))
      ((norm_nonneg _).trans (hM 0))
      (((approxBump n).support_normed_eq (μ := volume)).subset.trans
        (Metric.ball_subset_ball ((approxBump_rOut_le n).trans (by norm_num))))
      ((approxBump n).nonneg_normed) ((approxBump n).integral_normed) hg.aestronglyMeasurable
      (fun y _ => by simpa using hM y)
    simpa [smoothen] using this
  have hlim := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n x => ‖smoothen n g x - g x‖ₑ ^ 2)
    (f := fun _ => 0) (S.indicator fun _ => ENNReal.ofReal ((M + M) ^ 2))
    (fun n => (((hconv n).sub hg).enorm.measurable.pow_const 2))
    (fun n => Eventually.of_forall fun x => by
      by_cases hx : x ∈ S
      · dsimp only
        rw [Set.indicator_of_mem hx, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
        exact ENNReal.ofReal_le_ofReal
          (pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le_of_le (hbd n x) (hM x)) 2)
      · simp [hsupp n x hx])
    (by
      rw [lintegral_indicator_const hS.measurableSet]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.measure_lt_top.ne)
    (Eventually.of_forall fun x => by
      have hc := ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume)
        approxBump_rOut_tendsto hg x
      have := ((ENNReal.continuous_pow 2).tendsto _).comp
        ((hc.sub (tendsto_const_nhds (x := g x))).enorm)
      simpa [Function.comp_def, smoothen] using this)
  simpa using hlim

private theorem smoothen_eLpNorm_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {f : Space → E} (hf : MemLp f 2 volume) :
    Tendsto (fun n => eLpNorm (fun x => smoothen n f x - f x) 2 volume) atTop (𝓝 0) := by
  have hfl : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hε3 : ε / 3 ≠ 0 := (ENNReal.div_pos hε.ne' (by norm_num)).ne'
  obtain ⟨g, hgc, hfg, hgcont, hgm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε3
  have hgl : LocallyIntegrable g volume := hgcont.locallyIntegrable
  have hlim := eLpNorm_tendsto_of_sq_space
    (F := fun n x => smoothen n g x - g x) (smoothen_sq_tendsto_of_continuous hgcont hgc)
  filter_upwards [ENNReal.tendsto_nhds_zero.1 hlim (ε / 3) (pos_iff_ne_zero.2 hε3)] with n hn
  have hcf : Continuous (smoothen n f) := (smoothen_contDiff n hfl).continuous
  have hcg : Continuous (smoothen n g) := (smoothen_contDiff n hgl).continuous
  have e : (fun x => smoothen n f x - f x) =
      (fun x => smoothen n f x - smoothen n g x) + (fun x => smoothen n g x - g x) + (g - f) := by
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    abel
  rw [e]
  calc _ ≤ eLpNorm (fun x => smoothen n f x - smoothen n g x) 2 volume +
        eLpNorm (fun x => smoothen n g x - g x) 2 volume + eLpNorm (g - f) 2 volume := by
        refine (eLpNorm_add_le (((hcf.sub hcg).aestronglyMeasurable).add
          (hcg.sub hgcont).aestronglyMeasurable) (hgm.1.sub hf.1) (by norm_num)).trans ?_
        gcongr
        exact eLpNorm_add_le (hcf.sub hcg).aestronglyMeasurable (hcg.sub hgcont).aestronglyMeasurable
          (by norm_num)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        gcongr
        · exact (smoothen_sub_eLpNorm_le n hfl hgl).trans hfg
        · rw [eLpNorm_sub_comm]
          exact hfg
    _ = ε := ENNReal.add_thirds ε

private theorem smoothen_local_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {K : Set Space} (hK : IsCompact K) {f : Space → E}
    (hf : MemLp f 2 (volume.restrict (Metric.cthickening 1 K))) :
    Tendsto (fun n => eLpNorm (fun x => smoothen n f x - f x) 2 (volume.restrict K)) atTop (𝓝 0) := by
  have hB : IsCompact (Metric.cthickening 1 K) := hK.cthickening
  set f' := (Metric.cthickening 1 K).indicator f with hf'def
  have hf' : MemLp f' 2 volume := (memLp_indicator_iff_restrict hB.measurableSet).2 hf
  have hlim := smoothen_eLpNorm_tendsto hf'
  have heq : ∀ n, eLpNorm (fun x => smoothen n f x - f x) 2 (volume.restrict K) =
      eLpNorm (fun x => smoothen n f' x - f' x) 2 (volume.restrict K) := by
    intro n
    refine eLpNorm_congr_ae ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun x hx => ?_))
    have hxB : x ∈ Metric.cthickening 1 K := Metric.self_subset_cthickening K hx
    have e1 : f' x = f x := Set.indicator_of_mem hxB f
    have e2 : smoothen n f' x = smoothen n f x := by
      simp only [smoothen, convolution_def, ContinuousLinearMap.lsmul_apply]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      by_cases ht : (approxBump n).normed volume t = 0
      · simp [ht]
      · have ht' : t ∈ Metric.ball (0 : Space) (approxBump n).rOut := by
          rw [← (approxBump n).support_normed_eq (μ := volume)]
          exact ht
        have hxt : x - t ∈ Metric.cthickening 1 K := by
          refine Metric.mem_cthickening_of_dist_le (x - t) x 1 K hx ?_
          rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]
          rw [Metric.mem_ball, dist_zero_right] at ht'
          exact ht'.le.trans (approxBump_rOut_le n)
        simp only [hf'def, Set.indicator_of_mem hxt]
    show smoothen n f x - f x = smoothen n f' x - f' x
    rw [e1, e2]
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le)
    (fun n => ?_)
  rw [heq n]
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

private def SqLim {E : Type*} [NormedAddCommGroup E] (K : Set Space) (F : ℕ → Space → E)
    (f : Space → E) : Prop :=
  (∀ n, MemLp (F n) 2 (volume.restrict K)) ∧ MemLp f 2 (volume.restrict K) ∧
    Tendsto (fun n => eLpNorm (fun y => F n y - f y) 2 (volume.restrict K)) atTop (𝓝 0)

private theorem memLp_restrict_of_continuous {E : Type*} [NormedAddCommGroup E] {K : Set Space}
    (hK : IsCompact K) {f : Space → E} (hf : Continuous f) : MemLp f 2 (volume.restrict K) := by
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact MemLp.of_bound hf.aestronglyMeasurable C
    ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall hC))

private theorem SqLim.smoothen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {K : Set Space} (hK : IsCompact K) {f : Space → E}
    (hfl : LocallyIntegrable f volume) (hf : MemLp f 2 (volume.restrict (Metric.cthickening 1 K))) :
    SqLim K (fun n => smoothen n f) f :=
  ⟨fun n => memLp_restrict_of_continuous hK (smoothen_contDiff n hfl).continuous,
    hf.mono_measure (Measure.restrict_mono (Metric.self_subset_cthickening K) le_rfl),
    smoothen_local_tendsto hK hf⟩

private theorem SqLim.congr {E : Type*} [NormedAddCommGroup E] {K : Set Space}
    {F F' : ℕ → Space → E} {f f' : Space → E} (h : SqLim K F f) (h1 : ∀ n y, F' n y = F n y)
    (h2 : ∀ y, f' y = f y) : SqLim K F' f' := by
  obtain rfl : F' = F := funext fun n => funext (h1 n)
  obtain rfl : f' = f := funext h2
  exact h

private theorem SqLim.add {E : Type*} [NormedAddCommGroup E] {K : Set Space}
    {F G : ℕ → Space → E} {f g : Space → E} (h1 : SqLim K F f) (h2 : SqLim K G g) :
    SqLim K (fun n y => F n y + G n y) (fun y => f y + g y) := by
  refine ⟨fun n => (h1.1 n).add (h2.1 n), h1.2.1.add h2.2.1, ?_⟩
  have hle : ∀ n, eLpNorm (fun y => (F n y + G n y) - (f y + g y)) 2 (volume.restrict K) ≤
      eLpNorm (fun y => F n y - f y) 2 (volume.restrict K) +
        eLpNorm (fun y => G n y - g y) 2 (volume.restrict K) := by
    intro n
    have e : (fun y => (F n y + G n y) - (f y + g y)) =
        (fun y => F n y - f y) + (fun y => G n y - g y) := by
      funext y
      simp only [Pi.add_apply]
      abel
    rw [e]
    exact eLpNorm_add_le ((h1.1 n).1.sub h1.2.1.1) ((h2.1 n).1.sub h2.2.1.1) one_le_two
  have := h1.2.2.add h2.2.2
  rw [add_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) hle

private theorem SqLim.of_le {E E' : Type*} [NormedAddCommGroup E] [NormedAddCommGroup E']
    {K : Set Space} (hK : IsCompact K) {F : ℕ → Space → E} {f : Space → E}
    {T : ℕ → Space → E'} {t : Space → E'} (h : SqLim K F f)
    (hT : ∀ n, MemLp (T n) 2 (volume.restrict K)) (ht : MemLp t 2 (volume.restrict K)) (C : ℝ)
    (hle : ∀ n, ∀ y ∈ K, ‖T n y - t y‖ ≤ C * ‖F n y - f y‖) : SqLim K T t := by
  refine ⟨hT, ht, ?_⟩
  have hb : ∀ n, eLpNorm (fun y => T n y - t y) 2 (volume.restrict K) ≤
      ENNReal.ofReal C * eLpNorm (fun y => F n y - f y) 2 (volume.restrict K) := fun n =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall (hle n))) 2
  have := ENNReal.Tendsto.const_mul h.2.2 (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal C)
  rw [mul_zero] at this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds this (fun _ => zero_le) hb

private theorem SqLim.smul_fun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Space} (hK : IsCompact K) {F : ℕ → Space → E} {f : Space → E} (h : SqLim K F f)
    {c : Space → ℝ} (hc : Continuous c) :
    SqLim K (fun n y => c y • F n y) (fun y => c y • f y) := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hb : ∀ g : Space → E, MemLp g 2 (volume.restrict K) →
      MemLp (fun y => c y • g y) 2 (volume.restrict K) := fun g hg =>
    hg.of_le_mul (hc.aestronglyMeasurable.smul hg.1)
      ((ae_restrict_iff' hK.measurableSet).2 (Eventually.of_forall fun y hy => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _)))
  refine h.of_le hK (fun n => hb _ (h.1 n)) (hb _ h.2.1) C (fun n y hy => ?_)
  rw [← smul_sub, norm_smul]
  exact mul_le_mul_of_nonneg_right (hC y hy) (norm_nonneg _)

private theorem SqLim.clm {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] {K : Set Space} (hK : IsCompact K)
    {F : ℕ → Space → E} {f : Space → E} (h : SqLim K F f) (L : E →L[ℝ] E') :
    SqLim K (fun n y => L (F n y)) (fun y => L (f y)) := by
  have hb : ∀ g : Space → E, MemLp g 2 (volume.restrict K) →
      MemLp (fun y => L (g y)) 2 (volume.restrict K) := fun g hg =>
    hg.of_le_mul (L.continuous.comp_aestronglyMeasurable hg.1)
      (Eventually.of_forall fun y => L.le_opNorm (g y))
  refine h.of_le hK (fun n => hb _ (h.1 n)) (hb _ h.2.1) ‖L‖ (fun n y _ => ?_)
  rw [← map_sub]
  exact L.le_opNorm _

private theorem SqLim.neg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Space} (hK : IsCompact K) {F : ℕ → Space → E} {f : Space → E} (h : SqLim K F f) :
    SqLim K (fun n y => -F n y) (fun y => -f y) :=
  (h.clm hK (-ContinuousLinearMap.id ℝ E)).congr (fun n y => by simp) (fun y => by simp)

private theorem SqLim.sub {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set Space} (hK : IsCompact K) {F G : ℕ → Space → E} {f g : Space → E}
    (h1 : SqLim K F f) (h2 : SqLim K G g) :
    SqLim K (fun n y => F n y - G n y) (fun y => f y - g y) :=
  (h1.add (h2.neg hK)).congr (fun _ _ => sub_eq_add_neg _ _) (fun _ => sub_eq_add_neg _ _)

private theorem SqLim.sum3 {E : Type*} [NormedAddCommGroup E] {K : Set Space}
    {F : Fin 3 → ℕ → Space → E} {f : Fin 3 → Space → E} (h : ∀ i, SqLim K (F i) (f i)) :
    SqLim K (fun n y => ∑ i : Fin 3, F i n y) (fun y => ∑ i : Fin 3, f i y) :=
  (((h 0).add (h 1)).add (h 2)).congr (fun _ _ => Fin.sum_univ_three _) (fun _ => Fin.sum_univ_three _)

private theorem SqLim.tendsto_inner {K : Set Space} {F G : ℕ → Space → Space}
    {f g : Space → Space} (hF : SqLim K F f) (hG : SqLim K G g) :
    Tendsto (fun n => ∫ y in K, inner ℝ (F n y) (G n y)) atTop
      (𝓝 (∫ y in K, inner ℝ (f y) (g y))) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have h1 : Tendsto (fun n => (hF.1 n).toLp (F n)) atTop (𝓝 (hF.2.1.toLp f)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hF.1 f hF.2.1).2 hF.2.2
  have h2 : Tendsto (fun n => (hG.1 n).toLp (G n)) atTop (𝓝 (hG.2.1.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hG.1 g hG.2.1).2 hG.2.2
  have h3 := Filter.Tendsto.inner (𝕜 := ℝ) h1 h2
  have e : ∀ (A B : Space → Space) (hA : MemLp A 2 (volume.restrict K))
      (hB : MemLp B 2 (volume.restrict K)),
      inner ℝ (hA.toLp A) (hB.toLp B) = ∫ y in K, inner ℝ (A y) (B y) := by
    intro A B hA hB
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with y hy1 hy2
    rw [hy1, hy2]
  simp only [e] at h3
  exact h3

private theorem SqLim.integrableOn_inner {K : Set Space} {A B : Space → Space}
    (hA : MemLp A 2 (volume.restrict K)) (hB : MemLp B 2 (volume.restrict K)) :
    IntegrableOn (fun y => inner ℝ (A y) (B y)) K := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  refine (L2.integrable_inner (hA.toLp A) (hB.toLp B)).congr ?_
  filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with y hy1 hy2
  rw [hy1, hy2]

private def IntLim (P : ℕ → Space → ℝ) (p : Space → ℝ) : Prop :=
  (∀ n, Integrable (P n)) ∧ Integrable p ∧ Tendsto (fun n => ∫ y, P n y) atTop (𝓝 (∫ y, p y))

private theorem IntLim.congr {P P' : ℕ → Space → ℝ} {p p' : Space → ℝ} (h : IntLim P p)
    (h1 : ∀ n y, P' n y = P n y) (h2 : ∀ y, p' y = p y) : IntLim P' p' := by
  obtain rfl : P' = P := funext fun n => funext (h1 n)
  obtain rfl : p' = p := funext h2
  exact h

private theorem IntLim.add {P Q : ℕ → Space → ℝ} {p q : Space → ℝ} (h1 : IntLim P p)
    (h2 : IntLim Q q) : IntLim (fun n y => P n y + Q n y) (fun y => p y + q y) := by
  refine ⟨fun n => (h1.1 n).add (h2.1 n), h1.2.1.add h2.2.1, ?_⟩
  have e : ∀ n, ∫ y, P n y + Q n y = (∫ y, P n y) + ∫ y, Q n y := fun n =>
    integral_add (h1.1 n) (h2.1 n)
  simp_rw [e, integral_add h1.2.1 h2.2.1]
  exact h1.2.2.add h2.2.2

private theorem IntLim.sub {P Q : ℕ → Space → ℝ} {p q : Space → ℝ} (h1 : IntLim P p)
    (h2 : IntLim Q q) : IntLim (fun n y => P n y - Q n y) (fun y => p y - q y) := by
  refine ⟨fun n => (h1.1 n).sub (h2.1 n), h1.2.1.sub h2.2.1, ?_⟩
  have e : ∀ n, ∫ y, P n y - Q n y = (∫ y, P n y) - ∫ y, Q n y := fun n =>
    integral_sub (h1.1 n) (h2.1 n)
  simp_rw [e, integral_sub h1.2.1 h2.2.1]
  exact h1.2.2.sub h2.2.2

private theorem IntLim.sum3 {P : Fin 3 → ℕ → Space → ℝ} {p : Fin 3 → Space → ℝ}
    (h : ∀ i, IntLim (P i) (p i)) :
    IntLim (fun n y => ∑ i : Fin 3, P i n y) (fun y => ∑ i : Fin 3, p i y) :=
  (((h 0).add (h 1)).add (h 2)).congr (fun _ _ => Fin.sum_univ_three _) (fun _ => Fin.sum_univ_three _)

private theorem IntLim.base {K : Set Space} (hK : IsCompact K) {c : Space → ℝ} (hc : Continuous c)
    (hc0 : ∀ y, y ∉ K → c y = 0) {F G : ℕ → Space → Space} {f g : Space → Space}
    (hF : SqLim K F f) (hG : SqLim K G g) :
    IntLim (fun n y => c y * inner ℝ (F n y) (G n y)) (fun y => c y * inner ℝ (f y) (g y)) := by
  have hcF := hF.smul_fun hK hc
  have e : ∀ (A B : Space → Space), (fun y => c y * inner ℝ (A y) (B y)) =
      (fun y => inner ℝ (c y • A y) (B y)) := fun A B => funext fun y => (real_inner_smul_left _ _ _).symm
  have hsupp : ∀ (A B : Space → Space), Function.support (fun y => c y * inner ℝ (A y) (B y)) ⊆ K :=
    fun A B y hy => by
      by_contra hyK
      exact hy (by simp [hc0 y hyK])
  have hint : ∀ (A B : Space → Space), MemLp (fun y => c y • A y) 2 (volume.restrict K) →
      MemLp B 2 (volume.restrict K) → Integrable (fun y => c y * inner ℝ (A y) (B y)) := by
    intro A B hA hB
    refine (integrableOn_iff_integrable_of_support_subset (hsupp A B)).1 ?_
    rw [e]
    exact SqLim.integrableOn_inner hA hB
  have hset : ∀ (A B : Space → Space), ∫ y, c y * inner ℝ (A y) (B y) =
      ∫ y in K, inner ℝ (c y • A y) (B y) := by
    intro A B
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := K) (fun y hy => by simp [hc0 y hy])]
    exact setIntegral_congr_fun hK.measurableSet (fun y _ => (real_inner_smul_left _ _ _).symm)
  refine ⟨fun n => hint _ _ (hcF.1 n) (hG.1 n), hint _ _ hcF.2.1 hG.2.1, ?_⟩
  simp_rw [hset]
  exact hcF.tendsto_inner hG

private theorem clm_expand (A : Space →L[ℝ] Space) (w : Space) :
    A w = ∑ i : Fin 3, w i • A (unitVector i) := by
  have hw : ∑ i : Fin 3, w i • unitVector i = w := by
    simpa [unitVector] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
  conv_lhs => rw [← hw]
  simp [map_sum, map_smul]

private def turnMap : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurn
      map_add' := fun x y => by
        ext i
        fin_cases i <;> simp [axialTurn] <;> ring
      map_smul' := fun c x => by
        ext i
        fin_cases i <;> simp [axialTurn] }

private theorem turnMap_apply (w : Space) : turnMap w = axialTurn w := rfl

private theorem coord_continuous (i : Fin 3) : Continuous (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous

private def driftOf (α a : ℝ) (y w : Space) (c : Fin 3 → Space) : Space :=
  (1 - 1 / (2 * α)) • w + (1 / (2 * α)) • ∑ i : Fin 3, y i • c i +
    a • (∑ i : Fin 3, axialTurn y i • c i - turnMap w)

private theorem driftField_eq (α a : ℝ) (u : Space → Space) (A : Space → (Space →L[ℝ] Space))
    (y : Space) : driftField α a u A y = driftOf α a y (u y) (fun i => A y (unitVector i)) := by
  simp only [driftField, driftOf, turnMap_apply]
  rw [← clm_expand (A y) y, ← clm_expand (A y) (axialTurn y)]

private theorem SqLim.driftOf {K : Set Space} (hK : IsCompact K) (α a : ℝ)
    {U : ℕ → Space → Space} {w : Space → Space} {C : Fin 3 → ℕ → Space → Space}
    {c : Fin 3 → Space → Space} (hU : SqLim K U w) (hC : ∀ i, SqLim K (C i) (c i)) :
    SqLim K (fun n y => driftOf α a y (U n y) (fun i => C i n y))
      (fun y => driftOf α a y (w y) (fun i => c i y)) := by
  have h1 := hU.smul_fun hK (continuous_const (y := 1 - 1 / (2 * α)))
  have h2 := (SqLim.sum3 fun i => (hC i).smul_fun hK (coord_continuous i)).smul_fun hK
    (continuous_const (y := 1 / (2 * α)))
  have h3 := ((SqLim.sum3 fun i => (hC i).smul_fun hK
    ((coord_continuous i).comp turnMap.continuous)).sub hK (hU.clm hK turnMap)).smul_fun hK
    (continuous_const (y := a))
  exact (h1.add h2).add h3

private theorem mul_entrySq_eq (c : ℝ) (A : Space →L[ℝ] Space) :
    c * entrySq A = ∑ i : Fin 3, c * inner ℝ (A (unitVector i)) (A (unitVector i)) := by
  simp only [entrySq, Finset.mul_sum, real_inner_self_eq_norm_sq]

private theorem driftBoundary_eq (α a : ℝ) (u : Space → Space) (A : Space → (Space →L[ℝ] Space))
    (χ : Space → ℝ) (y : Space) :
    driftBoundary α a u A χ y =
      ∑ i : Fin 3, fderiv ℝ χ y (unitVector i) * inner ℝ (driftField α a u A y) (A y (unitVector i))
      - ∑ i : Fin 3, ((1 / 2) * fderiv ℝ χ y ((1 / (2 * α)) • y + a • axialTurn y)) *
          inner ℝ (A y (unitVector i)) (A y (unitVector i)) := by
  rw [driftBoundary, ← mul_entrySq_eq]

theorem driftLocalApprox : DriftLocalApproxStatement := by
  intro α a m v G H hv χ hχ
  set K := tsupport χ with hKdef
  have hK : IsCompact K := hχ.2
  set B := Metric.cthickening 1 K with hBdef
  have hB : IsCompact B := hK.cthickening
  have : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.2 hB.measure_lt_top.ne
  have hvl : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  set Gc : Fin 3 → Space → Space := fun i y => G y (unitVector i) with hGc
  set Hc : Fin 3 → Fin 3 → Space → Space := fun j i y => H y (unitVector j) (unitVector i) with hHc
  have hGm : ∀ i, MemLp (Gc i) 2 volume := by
    intro i
    have hm : AEStronglyMeasurable (Gc i) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
        hv.measurable_gradient
    refine (memLp_two_iff_integrable_sq_norm hm).2 (hv.gradient_two.mono' (hm.norm.pow 2) ?_)
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Finset.single_le_sum (f := fun i => ‖G z (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ i)
  have hHm : ∀ j i, MemLp (Hc j i) 2 volume := by
    intro j i
    have hm : AEStronglyMeasurable (Hc j i) volume :=
      (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
        ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous.comp_aestronglyMeasurable
          hv.measurable_second)
    refine (memLp_two_iff_integrable_sq_norm hm).2 (hv.second_two.mono' (hm.norm.pow 2) ?_)
    refine Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc ‖Hc j i z‖ ^ 2 ≤ ∑ k : Fin 3, ‖H z (unitVector j) (unitVector k)‖ ^ 2 :=
          Finset.single_le_sum (f := fun k => ‖H z (unitVector j) (unitVector k)‖ ^ 2)
            (fun k _ => by positivity) (Finset.mem_univ i)
      _ ≤ ∑ l : Fin 3, ∑ k : Fin 3, ‖H z (unitVector l) (unitVector k)‖ ^ 2 :=
          Finset.single_le_sum (f := fun l => ∑ k : Fin 3, ‖H z (unitVector l) (unitVector k)‖ ^ 2)
            (fun l _ => Finset.sum_nonneg fun k _ => by positivity) (Finset.mem_univ j)
  set u : ℕ → Space → Space := fun n => smoothen n v with hudef
  have hu : ∀ n, ContDiff ℝ ∞ (u n) := fun n => smoothen_contDiff n hvl
  have hDu : ∀ n y i, fderiv ℝ (u n) y (unitVector i) = smoothen n (Gc i) y := fun n y i =>
    smoothen_partial n hvl i (fun φ hφ => hv.weak_gradient φ hφ i) y
  have hD2u : ∀ n y j i, fderiv ℝ (fderiv ℝ (u n)) y (unitVector j) (unitVector i) =
      smoothen n (Hc j i) y := by
    intro n y j i
    have hd : Differentiable ℝ (fderiv ℝ (u n)) :=
      ((hu n).fderiv_right (m := ∞) (le_of_eq rfl)).differentiable (by simp)
    have h1 := fderiv_clm_apply (hd y) (differentiableAt_const (unitVector i))
    have h2 : (fun z => fderiv ℝ (u n) z (unitVector i)) = smoothen n (Gc i) :=
      funext fun z => hDu n z i
    rw [h2] at h1
    have h3 : fderiv ℝ (smoothen n (Gc i)) y (unitVector j) =
        fderiv ℝ (fderiv ℝ (u n)) y (unitVector j) (unitVector i) := by
      rw [h1]
      simp
    rw [← h3]
    exact smoothen_partial n ((hGm i).locallyIntegrable one_le_two) j
      (fun φ hφ => hv.weak_second φ hφ i j) y
  have Lu : SqLim K u v :=
    SqLim.smoothen hK hvl ((hv.velocity_six.restrict B).mono_exponent (by norm_num))
  have LDu : ∀ i, SqLim K (fun n y => fderiv ℝ (u n) y (unitVector i)) (Gc i) := fun i =>
    (SqLim.smoothen hK ((hGm i).locallyIntegrable one_le_two) ((hGm i).restrict B)).congr
      (fun n y => hDu n y i) (fun _ => rfl)
  have LD2u : ∀ j i, SqLim K (fun n y => fderiv ℝ (fderiv ℝ (u n)) y (unitVector j) (unitVector i))
      (Hc j i) := fun j i =>
    (SqLim.smoothen hK ((hHm j i).locallyIntegrable one_le_two) ((hHm j i).restrict B)).congr
      (fun n y => hD2u n y j i) (fun _ => rfl)
  have Ldrift : SqLim K (fun n y => driftField α a (u n) (fderiv ℝ (u n)) y) (driftField α a v G) :=
    (SqLim.driftOf hK α a Lu LDu).congr (fun n y => driftField_eq α a (u n) (fderiv ℝ (u n)) y)
      (fun y => driftField_eq α a v G y)
  have Ltrace : SqLim K (fun n y => negSecondTrace (fun z => fderiv ℝ (fderiv ℝ (u n)) z) y)
      (negSecondTrace H) :=
    ((SqLim.sum3 fun j => LD2u j j).neg hK).congr (fun n y => by simp [negSecondTrace, secondTrace])
      (fun y => by simp [negSecondTrace, secondTrace, hHc])
  have hχc : Continuous χ := hχ.1.continuous
  have hχ0 : ∀ y, y ∉ K → χ y = 0 := fun y hy => image_eq_zero_of_notMem_tsupport hy
  have hdχc : Continuous (fderiv ℝ χ) := hχ.1.continuous_fderiv (by simp)
  have hdχ0 : ∀ y, y ∉ K → fderiv ℝ χ y = 0 := fun y hy => fderiv_of_notMem_tsupport (𝕜 := ℝ) hy
  refine ⟨u, hu, ?_, ?_, ?_⟩
  · exact (IntLim.base hK hχc hχ0 Ldrift Ltrace).2.2
  · have := IntLim.sum3 fun i => IntLim.base hK hχc hχ0 (LDu i) (LDu i)
    exact (this.congr (fun _ _ => mul_entrySq_eq _ _) (fun _ => mul_entrySq_eq _ _)).2.2
  · have hw : Continuous (fun y : Space => (1 / (2 * α)) • y + a • axialTurn y) := by
      simpa only [turnMap_apply] using
        (show Continuous (fun y : Space => (1 / (2 * α)) • y + a • turnMap y) by fun_prop)
    have h1 := IntLim.sum3 fun i => IntLim.base hK (c := fun y => fderiv ℝ χ y (unitVector i))
      (hdχc.clm_apply continuous_const) (fun y hy => by simp [hdχ0 y hy]) Ldrift (LDu i)
    have h2 := IntLim.sum3 fun i => IntLim.base hK
      (c := fun y => (1 / 2) * fderiv ℝ χ y ((1 / (2 * α)) • y + a • axialTurn y))
      (continuous_const.mul (hdχc.clm_apply hw)) (fun y hy => by simp [hdχ0 y hy]) (LDu i) (LDu i)
    exact ((h1.sub h2).congr (fun _ _ => driftBoundary_eq _ _ _ _ _ _)
      (fun _ => driftBoundary_eq _ _ _ _ _ _)).2.2


end SteadyCert

end Breakdown

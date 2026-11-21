import TorusEuler.EulerAdvectionBounds
import TorusEuler.OffOriginLimits
import Mathlib.Analysis.Calculus.ParametricIntegral

open Filter MeasureTheory Metric Set
open scoped ContDiff Topology

namespace TorusEuler

/-- Periodic separation of the compact target and far source persists on
a common open neighborhood of the target. -/
theorem exists_periodically_separated_neighborhood
    {K S : Set Vec3} (hK : IsCompact K) (hS : IsCompact S)
    (hsep : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin) :
    ∃ r > (0 : ℝ), ∀ x ∈ cthickening r K, ∀ y ∈ S, ∀ n : Fin 3 → ℤ,
      r < dist (latticeVector n) (x - y) := by
  let D := (fun p : Vec3 × Vec3 => p.1 - p.2) '' (K ×ˢ S)
  have hD : IsCompact D := (hK.prod hS).image (continuous_fst.sub continuous_snd)
  have hDo : D ⊆ offOrigin := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    exact hsep x hx y hy
  obtain ⟨r, hr, _, _, _, _, hd⟩ := exists_offOrigin_compact_neighborhood hD hDo
  have hr₂ := half_pos hr
  refine ⟨r / 2 / 2, half_pos hr₂, fun x hx y hy n => ?_⟩
  obtain ⟨z, hz, hzx⟩ := mem_thickening_iff.mp
    (cthickening_subset_thickening' hr₂ (half_lt_self hr₂) K hx)
  have hzD : z - y ∈ D := ⟨(z, y), ⟨hz, hy⟩, rfl⟩
  have hdz : dist (x - y) (z - y) < r / 2 := by simpa only [dist_sub_right] using hzx
  have htriangle := dist_triangle (latticeVector n) (x - y) (z - y)
  linarith only [hr, hd (z - y) hzD n, hdz, htriangle]

section KernelIntegral

variable {X Y A B : Type*} [MeasurableSpace Y]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]

/-- A far kernel applied to a tensor density and integrated over its source measure. -/
noncomputable def farKernelIntegral (μ : Measure Y) (K : X → Y → A →L[ℝ] B)
    (P : Y → A) (x : X) : B :=
  ∫ y, K x y (P y) ∂μ

/-- The separated kernel estimate from Proposition 8.4, applicable to an
individual spatial derivative kernel. -/
theorem norm_farKernelIntegral_sub_le
    {μ : Measure Y} {K : X → Y → A →L[ℝ] B} {P Q : Y → A}
    {x : X} {C : ℝ} (hK : ∀ᵐ y ∂μ, ‖K x y‖ ≤ C)
    (hP : Integrable P μ) (hQ : Integrable Q μ)
    (hPm : AEStronglyMeasurable (fun y => K x y (P y)) μ)
    (hQm : AEStronglyMeasurable (fun y => K x y (Q y)) μ) :
    ‖farKernelIntegral μ K P x - farKernelIntegral μ K Q x‖ ≤
      C * ∫ y, ‖P y - Q y‖ ∂μ := by
  have hBound (R : Y → A) : ∀ᵐ y ∂μ, ‖K x y (R y)‖ ≤ C * ‖R y‖ :=
    hK.mono fun y hy => ((K x y).le_opNorm (R y)).trans
      (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  have hPi := (hP.norm.const_mul C).mono' hPm (hBound P)
  have hQi := (hQ.norm.const_mul C).mono' hQm (hBound Q)
  rw [farKernelIntegral, farKernelIntegral, ← integral_sub hPi hQi, ← integral_const_mul]
  simp_rw [← map_sub]
  exact norm_integral_le_of_norm_le ((hP.sub hQ).norm.const_mul C) (hBound (fun y => P y - Q y))

/-- Uniform boundedness of the far kernel converts convergence of the density
in L¹ into uniform convergence of the corresponding far fields. -/
theorem tendstoUniformlyOn_farKernelIntegral_of_l1
    {ι : Type*} {l : Filter ι} {S : Set X} {μ : Measure Y}
    {K : X → Y → A →L[ℝ] B} {P : ι → Y → A} {Q : Y → A} {C : ℝ}
    (hK : ∀ x ∈ S, ∀ᵐ y ∂μ, ‖K x y‖ ≤ C)
    (hP : ∀ i, Integrable (P i) μ) (hQ : Integrable Q μ)
    (hPm : ∀ i x, x ∈ S → AEStronglyMeasurable (fun y => K x y (P i y)) μ)
    (hQm : ∀ x ∈ S, AEStronglyMeasurable (fun y => K x y (Q y)) μ)
    (hL1 : Tendsto (fun i => ∫ y, ‖P i y - Q y‖ ∂μ) l (𝓝 0)) :
    TendstoUniformlyOn (fun i => farKernelIntegral μ K (P i))
      (farKernelIntegral μ K Q) l S := by
  have hprod := (tendsto_const_nhds (x := C)).mul hL1
  rw [mul_zero, Metric.tendsto_nhds] at hprod
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [hprod ε hε] with i hi x hx
  rw [dist_comm, dist_eq_norm]
  have hb := norm_farKernelIntegral_sub_le (hK x hx) (hP i) hQ (hPm i x hx) (hQm x hx)
  rw [Real.dist_eq, sub_zero] at hi
  exact (hb.trans (le_abs_self _)).trans_lt hi

variable [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Differentiation of the far kernel integral on a common open neighborhood,
with an explicit uniform bound for the derivative operator. -/
theorem hasFDerivAt_farKernelIntegral
    {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    {μ : Measure Y} {K : X → Y → A →L[ℝ] B}
    {DK : X → Y → A →L[ℝ] (X →L[ℝ] B)} {P : Y → A}
    (hP : Integrable P μ)
    (hKm : ∀ z ∈ U, AEStronglyMeasurable (fun y => K z y (P y)) μ)
    (hDKm : AEStronglyMeasurable (fun y => DK x y (P y)) μ)
    {C M : ℝ} (hK : ∀ᵐ y ∂μ, ‖K x y‖ ≤ C)
    (hDK : ∀ᵐ y ∂μ, ∀ z ∈ U, ‖DK z y‖ ≤ M)
    (hDiff : ∀ᵐ y ∂μ, ∀ z ∈ U,
      HasFDerivAt (fun v => K v y (P y)) (DK z y (P y)) z) :
    HasFDerivAt (farKernelIntegral μ K P) (farKernelIntegral μ DK P x) x := by
  have hUn : U ∈ 𝓝 x := hU.mem_nhds hx
  have hInt := (hP.norm.const_mul C).mono' (hKm x hx) (hK.mono fun y hy =>
    ((K x y).le_opNorm (P y)).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _)))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le hUn
    (eventually_of_mem hUn hKm) hInt hDKm
    (hDK.mono fun y hy z hz => ((DK z y).le_opNorm (P y)).trans
      (mul_le_mul_of_nonneg_right (hy z hz) (norm_nonneg _)))
    (hP.norm.const_mul M) hDiff

variable [CompleteSpace B]

/-- Smooth, uniformly bounded spatial kernel jets may be integrated against
an L¹ density. The result identifies each jet as an ambient spatial derivative
on the open far-field neighborhood. -/
theorem contDiffOn_farKernelIntegral_of_spatial_jets
    {U : Set X} (hU : IsOpen U) {μ : Measure Y} {P : Y → A} (hP : Integrable P μ)
    {K : ∀ k : ℕ, X → Y → A →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X) B}
    (hKm : ∀ k x, x ∈ U → AEStronglyMeasurable (K k x) μ)
    (hK : ∀ k, ∃ M : ℝ, ∀ᵐ y ∂μ, ∀ x ∈ U, ‖K k x y‖ ≤ M)
    (hDK : ∀ k, ∀ᵐ y ∂μ, ∀ x ∈ U, ∀ a : A,
      HasFDerivAt (fun z => K k z y a) ((K (k + 1) x y a).curryLeft) x)
    (m : ℕ) :
    let f x := (farKernelIntegral μ (K 0) P x).curry0
    ContDiffOn ℝ m f U ∧ ∀ k ≤ m, EqOn (iteratedFDeriv ℝ k f) (farKernelIntegral μ (K k) P) U := by
  let J : X → FormalMultilinearSeries ℝ X B := fun x k => farKernelIntegral μ (K k) P x
  have hKmP (k : ℕ) (x : X) (hx : x ∈ U) :
      AEStronglyMeasurable (fun y => K k x y (P y)) μ := by
    have hEval : Continuous (fun z : (A →L[ℝ]
        ContinuousMultilinearMap ℝ (fun _ : Fin k => X) B) × A => z.1 z.2) := by fun_prop
    exact hEval.comp_aestronglyMeasurable ((hKm k x hx).prodMk hP.aestronglyMeasurable)
  have hD (k : ℕ) (x : X) (hx : x ∈ U) :
      HasFDerivAt (fun z => J z k) ((J x (k + 1)).curryLeft) x := by
    let equiv := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => X) B
    obtain ⟨C, hC⟩ := hK k
    obtain ⟨M, hM⟩ := hK (k + 1)
    have hbound : ∀ᵐ y ∂μ, ∀ z ∈ U, ‖equiv (K (k + 1) z y (P y))‖ ≤ M * ‖P y‖ := by
      refine hM.mono fun y hy z hz => ?_
      rw [equiv.norm_map]
      exact ((K (k + 1) z y).le_opNorm (P y)).trans
        (mul_le_mul_of_nonneg_right (hy z hz) (norm_nonneg _))
    have hBase := (hP.norm.const_mul C).mono' (hKmP k x hx)
      (hC.mono fun y hy => ((K k x y).le_opNorm (P y)).trans
        (mul_le_mul_of_nonneg_right (hy x hx) (norm_nonneg _)))
    have hUn := hU.mem_nhds hx
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le hUn
      (eventually_of_mem hUn (hKmP k)) hBase
      (equiv.continuous.comp_aestronglyMeasurable (hKmP (k + 1) x hx))
      hbound (hP.norm.const_mul M) ((hDK k).mono fun y hy z hz => hy z hz (P y))
    have hcomm := LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := μ)
      (E := X [×(k + 1)]→L[ℝ] B) (F := X →L[ℝ] (X [×k]→L[ℝ] B))
      equiv.toLinearIsometry (fun y => K (k + 1) x y (P y))
    change (∫ y, equiv (K (k + 1) x y (P y)) ∂μ) = equiv (farKernelIntegral μ (K (k + 1)) P x)
      at hcomm
    rw [hcomm] at h
    exact h
  have hJ : HasFTaylorSeriesUpToOn m (fun x => (J x 0).curry0) J U :=
    ⟨fun _ _ => rfl, fun k _ x hx => (hD k x hx).hasFDerivWithinAt,
      fun k _ x hx => (hD k x hx).continuousAt.continuousWithinAt⟩
  refine ⟨hJ.contDiffOn, fun k hk x hx => ?_⟩
  rw [← iteratedFDerivWithin_of_isOpen k hU hx]
  exact (hJ.eq_iteratedFDerivWithin_of_uniqueDiffOn (by exact_mod_cast hk) hU.uniqueDiffOn hx).symm

end KernelIntegral

/-- The tensor of uniformly convergent velocities on a compact source set
converges in L¹ there. A cutoff can be included in the far kernel. -/
theorem tendsto_l1_tensor_of_uniform_velocity
    {ι Y V A : Type*} {l : Filter ι} [PseudoMetricSpace Y] [MeasurableSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A] [NormedSpace ℝ A]
    {μ : Measure Y} {S : Set Y} (hS : IsCompact S) (hμ : μ S < ⊤)
    (tensor : V →L[ℝ] V →L[ℝ] A)
    {v : ι → Y → V} {w : Y → V}
    (hv : TendstoUniformlyOn v w l S) (hw : ContinuousOn w S) :
    Tendsto (fun i => ∫ y in S, ‖tensor (v i y) (v i y) - tensor (w y) (w y)‖ ∂μ)
      l (𝓝 0) := by
  obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hw
  have hA := tensor.uniformContinuous.comp_tendstoUniformlyOn hv
  have hb : TendstoUniformlyOn (fun i y => tensor (v i y) (v i y))
      (fun y => tensor (w y) (w y)) l S :=
    tendstoUniformlyOn_clm_apply_of_bounded hA hv
      (mul_nonneg (norm_nonneg tensor) (le_max_right M 0)) (le_max_right M 0)
      (fun y hy => (tensor.le_opNorm (w y)).trans
        (mul_le_mul_of_nonneg_left ((hM y hy).trans (le_max_left _ _)) (norm_nonneg _)))
      (fun y hy => (hM y hy).trans (le_max_left _ _))
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  let C := μ.real S
  have hC : 0 < C + 1 := add_pos_of_nonneg_of_pos ENNReal.toReal_nonneg zero_lt_one
  have hδ : 0 < ε / (C + 1) := div_pos hε hC
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hb _ hδ] with i hi
  rw [Real.dist_eq, sub_zero]
  calc
    |∫ y in S, ‖tensor (v i y) (v i y) - tensor (w y) (w y)‖ ∂μ|
        ≤ (ε / (C + 1)) * C := norm_setIntegral_le_of_norm_le_const
      (f := fun y => ‖tensor (v i y) (v i y) - tensor (w y) (w y)‖) hμ fun y hy => by
      rw [norm_norm, ← dist_eq_norm, dist_comm]
      exact (hi y hy).le
    _ < (ε / (C + 1)) * (C + 1) := mul_lt_mul_of_pos_left (lt_add_one C) hδ
    _ = ε := div_mul_cancel₀ _ hC.ne'

/-- Uniform velocity convergence gives uniform convergence of the far
contribution of any bounded separated kernel. In Proposition 8.4 this is
applied to the pressure kernel and its spatial jets, with the far cutoff
included in the operator. -/
theorem tendstoUniformlyOn_farKernelIntegral_of_uniform_velocity
    {ι X Y V A B : Type*} {l : Filter ι} {L : Set X}
    [MetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {μ : Measure Y} [IsLocallyFiniteMeasure μ] {S : Set Y} (hS : IsCompact S)
    (tensor : V →L[ℝ] V →L[ℝ] A) {v : ι → Y → V} {w : Y → V}
    (hv : TendstoUniformlyOn v w l S) (hvc : ∀ i, ContinuousOn (v i) S)
    (hwc : ContinuousOn w S) {K : X → Y → A →L[ℝ] B} {C : ℝ}
    (hK : ∀ x ∈ L, ∀ᵐ y ∂(μ.restrict S), ‖K x y‖ ≤ C)
    (hKm : ∀ x ∈ L, AEStronglyMeasurable (K x) (μ.restrict S)) :
    TendstoUniformlyOn
      (fun i => farKernelIntegral (μ.restrict S) K (fun y => tensor (v i y) (v i y)))
      (farKernelIntegral (μ.restrict S) K (fun y => tensor (w y) (w y))) l L := by
  have hT : Continuous (fun a => tensor a a) := by fun_prop
  have hInt {b : Y → V} (hb : ContinuousOn b S) :
      IntegrableOn (fun y => tensor (b y) (b y)) S μ :=
    (hT.comp_continuousOn hb).integrableOn_compact hS
  have hEval : Continuous (fun z : (A →L[ℝ] B) × A => z.1 z.2) := by fun_prop
  have hMeas {b : Y → V} (hb : ContinuousOn b S) (x : X) (hx : x ∈ L) :
      AEStronglyMeasurable (fun y => K x y (tensor (b y) (b y))) (μ.restrict S) :=
    hEval.comp_aestronglyMeasurable ((hKm x hx).prodMk (hInt hb).aestronglyMeasurable)
  exact tendstoUniformlyOn_farKernelIntegral_of_l1 hK (fun i => hInt (hvc i)) (hInt hwc)
    (fun i => hMeas (hvc i)) (hMeas hwc)
    (tendsto_l1_tensor_of_uniform_velocity hS hS.measure_lt_top tensor hv hwc)

/-- Under the separated kernel hypotheses, global uniform velocity convergence
gives uniform convergence of the actual spatial derivatives of the far
pressure contribution. The near contribution requires separate estimates. -/
theorem tendstoUniformlyOn_farKernel_spatial_derivatives_of_uniform_velocity
    {ι X Y V A B : Type*} {l : Filter ι} {U : Set X}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [MetricSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
    {μ : Measure Y} [IsLocallyFiniteMeasure μ] {S : Set Y} (hS : IsCompact S) (hU : IsOpen U)
    (tensor : V →L[ℝ] V →L[ℝ] A) {v : ι → Y → V} {w : Y → V}
    (hv : TendstoUniformlyOn v w l S) (hvc : ∀ i, ContinuousOn (v i) S)
    (hwc : ContinuousOn w S)
    {K : ∀ k : ℕ, X → Y → A →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => X) B}
    (hKm : ∀ k x, x ∈ U → AEStronglyMeasurable (K k x) (μ.restrict S))
    (hK : ∀ k, ∃ M : ℝ, ∀ᵐ y ∂(μ.restrict S), ∀ x ∈ U, ‖K k x y‖ ≤ M)
    (hDK : ∀ k, ∀ᵐ y ∂(μ.restrict S), ∀ x ∈ U, ∀ a : A,
      HasFDerivAt (fun z => K k z y a) ((K (k + 1) x y a).curryLeft) x)
    (m : ℕ) :
    let far (b : Y → V) (x : X) :=
      (farKernelIntegral (μ.restrict S) (K 0) (fun y => tensor (b y) (b y)) x).curry0
    ContDiffOn ℝ m (far w) U ∧ ∀ k ≤ m,
      TendstoUniformlyOn (fun i => iteratedFDeriv ℝ k (far (v i))) (iteratedFDeriv ℝ k (far w)) l U := by
  have hT : Continuous (fun a => tensor a a) := by fun_prop
  have hInt {b : Y → V} (hb : ContinuousOn b S) :
      IntegrableOn (fun y => tensor (b y) (b y)) S μ :=
    (hT.comp_continuousOn hb).integrableOn_compact hS
  have hjets {b : Y → V} (hb : ContinuousOn b S) :=
    contDiffOn_farKernelIntegral_of_spatial_jets hU (hInt hb) hKm hK hDK m
  refine ⟨(hjets hwc).1, fun k hk => ?_⟩
  obtain ⟨M, hM⟩ := hK k
  have hc := tendstoUniformlyOn_farKernelIntegral_of_uniform_velocity hS tensor hv hvc hwc
    (fun x hx => hM.mono fun y hy => hy x hx) (hKm k)
  exact (hc.congr (Eventually.of_forall fun i => ((hjets (hvc i)).2 k hk).symm)).congr_right
    ((hjets hwc).2 k hk).symm

end TorusEuler

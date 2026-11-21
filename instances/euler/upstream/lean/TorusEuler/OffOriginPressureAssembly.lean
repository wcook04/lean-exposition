import TorusEuler.OffOriginMultiplierKernel
import TorusEuler.OffOriginNearPressure
import TorusEuler.PeriodicLerayHolderLift
import TorusEuler.SmoothPeriodicHolder
import TorusEuler.PressureHessianMultiplier
import Mathlib.Analysis.Complex.OperatorNorm

/-! The near and far pressure limits in Proposition 8.4. -/

open Filter MeasureTheory Metric Set
open scoped ContDiff FourierTransform SchwartzMap Topology

namespace TorusEuler

noncomputable section

section PeriodicJetBounds

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem pressureJet_periodic {f : Vec3 → E} (hf : SpatiallyPeriodic f) (d : ℕ) :
    SpatiallyPeriodic (iteratedFDeriv ℝ d f) := by
  intro n x
  rw [← iteratedFDeriv_comp_add_right]
  exact congrArg (fun g : Vec3 → E => iteratedFDeriv ℝ d g x) (funext (hf n))

private theorem exists_norm_iteratedFDeriv_le_of_smooth_periodic {f : Vec3 → E}
    (hf : ContDiff ℝ ∞ f) (hp : SpatiallyPeriodic f) (d : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖iteratedFDeriv ℝ d f x‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_centeredCell.exists_bound_of_continuousOn
    (hf.continuous_iteratedFDeriv (m := d) (by simp)).continuousOn
  refine ⟨max 0 M, le_max_left _ _, fun x => ?_⟩
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell x
  have h := pressureJet_periodic hp d n (x - latticeVector n)
  rw [sub_add_cancel] at h
  exact h ▸ ((hM _ hn).trans (le_max_right _ _))

private theorem norm_sub_le_sqrt_dist_of_bounded_jet
    {f : Vec3 → E} (hf : ContDiff ℝ 1 f)
    {M D : ℝ} (hM : ∀ x, ‖f x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D)
    (x y : Vec3) :
    ‖f x - f y‖ ≤ (2 * M + D) * Real.sqrt ‖x - y‖ := by
  have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hD₀ : 0 ≤ D := (norm_nonneg _).trans (hD 0)
  have hL : ‖f x - f y‖ ≤ D * ‖x - y‖ :=
    convex_univ.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hf.differentiable one_ne_zero z) (fun z _ => hD z) (mem_univ y) (mem_univ x)
  rcases le_total ‖x - y‖ 1 with hsmall | hlarge
  · have hsqrt : ‖x - y‖ ≤ Real.sqrt ‖x - y‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      rw [Real.sq_sqrt (norm_nonneg _), pow_two]
      exact mul_le_of_le_one_right (norm_nonneg _) hsmall
    exact (hL.trans (mul_le_mul_of_nonneg_left hsqrt hD₀)).trans
      (mul_le_mul_of_nonneg_right (by linarith) (Real.sqrt_nonneg _))
  · have hsqrt : 1 ≤ Real.sqrt ‖x - y‖ := by
      simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hlarge
    calc
      _ ≤ 2 * M := (norm_sub_le _ _).trans (by linarith [hM x, hM y])
      _ ≤ (2 * M + D) * Real.sqrt ‖x - y‖ :=
        (by linarith : 2 * M ≤ 2 * M + D).trans
          (le_mul_of_one_le_right (by positivity) hsqrt)

end PeriodicJetBounds

section Differentiation

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private def pressureConvolutionJetMap (d : ℕ) :
    (E →L[ℂ] F) →L[ℝ] (Vec3 [×d]→L[ℝ] E) →L[ℝ] (Vec3 [×d]→L[ℝ] F) :=
  (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin d => Vec3) E F).comp
    (ContinuousLinearMap.restrictScalarsL ℂ E F ℝ ℝ)

omit [CompleteSpace F] in
private theorem norm_pressureConvolutionJetMap_le (d : ℕ) (K : E →L[ℂ] F)
    (J : Vec3 [×d]→L[ℝ] E) : ‖pressureConvolutionJetMap d K J‖ ≤ ‖K‖ * ‖J‖ := by
  change ‖(K.restrictScalars ℝ).compContinuousMultilinearMap J‖ ≤ ‖K‖ * ‖J‖
  simpa only [ContinuousLinearMap.norm_restrictScalars] using
    (ContinuousLinearMap.norm_compContinuousMultilinearMap_le (K.restrictScalars ℝ) J)

omit [CompleteSpace F] in
private theorem integrable_pressureConvolutionJet
    (d : ℕ) {K : Vec3 → E →L[ℂ] F} (hK : Integrable K)
    {J : Vec3 → (Vec3 [×d]→L[ℝ] E)} (hJ : Continuous J)
    {M : ℝ} (hM : ∀ y, ‖J y‖ ≤ M) :
    Integrable (fun y => pressureConvolutionJetMap d (K y) (J y)) := by
  have hcont : Continuous (fun p : (E →L[ℂ] F) × (Vec3 [×d]→L[ℝ] E) =>
      pressureConvolutionJetMap d p.1 p.2) :=
    ((pressureConvolutionJetMap d).continuous.comp continuous_fst).clm_apply continuous_snd
  apply (hK.norm.mul_const M).mono'
    (hcont.comp_aestronglyMeasurable (hK.aestronglyMeasurable.prodMk hJ.aestronglyMeasurable))
  exact Eventually.of_forall fun y => (norm_pressureConvolutionJetMap_le d (K y) (J y)).trans
    (mul_le_mul_of_nonneg_left (hM y) (norm_nonneg _))

/-- A bounded smooth input can be differentiated under an integrable
operator-valued convolution kernel at every spatial order. -/
theorem contDiff_operatorLiftConvolution_of_bounded_jets {K : Vec3 → E →L[ℂ] F}
    (hK : Integrable K) {g : Vec3 → E} (hg : ContDiff ℝ ∞ g)
    (M : ℕ → ℝ) (hM : ∀ d x, ‖iteratedFDeriv ℝ d g x‖ ≤ M d) :
    ContDiff ℝ ∞ (operatorLiftConvolution K g) ∧
      ∀ d x, iteratedFDeriv ℝ d (operatorLiftConvolution K g) x =
        ∫ y, pressureConvolutionJetMap d (K y) (iteratedFDeriv ℝ d g (x - y)) := by
  let J : Vec3 → FormalMultilinearSeries ℝ Vec3 F := fun x d =>
    ∫ y, pressureConvolutionJetMap d (K y) (iteratedFDeriv ℝ d g (x - y))
  have hInt (d : ℕ) (x : Vec3) :
      Integrable (fun y => pressureConvolutionJetMap d (K y) (iteratedFDeriv ℝ d g (x - y))) :=
    integrable_pressureConvolutionJet d hK
      ((hg.continuous_iteratedFDeriv (m := d) (by simp)).comp (continuous_const.sub continuous_id))
      (fun y => hM d (x - y))
  have hderiv (d : ℕ) (x : Vec3) : HasFDerivAt (fun z => J z d) (J x (d + 1)).curryLeft x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => Vec3) F
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (𝕜 := ℝ) (μ := volume)
      (F := fun z y => pressureConvolutionJetMap d (K y) (iteratedFDeriv ℝ d g (z - y)))
      (F' := fun z y => C (pressureConvolutionJetMap (d + 1) (K y)
        (iteratedFDeriv ℝ (d + 1) g (z - y))))
      (s := univ) (bound := fun y => ‖K y‖ * M (d + 1))
      Filter.univ_mem
      (Eventually.of_forall fun z => (hInt d z).aestronglyMeasurable) (hInt d x)
      (C.continuous.comp_aestronglyMeasurable (hInt (d + 1) x).aestronglyMeasurable)
      (Eventually.of_forall fun y z _ => by
        rw [LinearIsometryEquiv.norm_map]
        exact (norm_pressureConvolutionJetMap_le _ _ _).trans
          (mul_le_mul_of_nonneg_left (hM (d + 1) (z - y)) (norm_nonneg _)))
      (hK.norm.mul_const _)
      (Eventually.of_forall fun y z _ => by
        let L := pressureConvolutionJetMap d (K y)
        have hbase := (hg.differentiable_iteratedFDeriv (mod_cast ENat.natCast_lt_top d)
          (z - y)).hasFDerivAt
        rw [fderiv_iteratedFDeriv] at hbase
        have hcomp := L.hasFDerivAt.comp z (hbase.comp z ((hasFDerivAt_id z).sub_const y))
        have hcomp_eq : L.comp
            ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (d + 1) => Vec3) E
              (iteratedFDeriv ℝ (d + 1) g (z - y))).comp (ContinuousLinearMap.id ℝ Vec3)) =
            C (pressureConvolutionJetMap (d + 1) (K y)
              (iteratedFDeriv ℝ (d + 1) g (z - y))) := by
          apply ContinuousLinearMap.ext
          intro u
          apply ContinuousMultilinearMap.ext
          intro v
          rfl
        simp only [Function.comp_apply, id_eq] at hcomp
        rw [hcomp_eq] at hcomp
        exact hcomp)
    have hcomm := LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure Vec3))
      (E := Vec3 [×(d + 1)]→L[ℝ] F) (F := Vec3 →L[ℝ] (Vec3 [×d]→L[ℝ] F))
      C.toLinearIsometry (fun y => pressureConvolutionJetMap (d + 1) (K y)
        (iteratedFDeriv ℝ (d + 1) g (x - y)))
    change (∫ y, C (pressureConvolutionJetMap (d + 1) (K y)
      (iteratedFDeriv ℝ (d + 1) g (x - y)))) = (J x (d + 1)).curryLeft at hcomm
    rw [hcomm] at h
    exact h
  have hzero (x : Vec3) : (J x 0).curry0 = operatorLiftConvolution K g x := by
    let C := continuousMultilinearCurryFin0 ℝ Vec3 F
    calc
      _ = ∫ y, C (pressureConvolutionJetMap 0 (K y) (iteratedFDeriv ℝ 0 g (x - y))) :=
        (LinearIsometry.integral_comp_comm (𝕜 := ℝ) (μ := (volume : Measure Vec3))
          C.toLinearIsometry _).symm
      _ = _ := by congr 1
  have hJ (m : ℕ) : HasFTaylorSeriesUpToOn m (operatorLiftConvolution K g) J univ :=
    ⟨fun x _ => hzero x, fun d _ x _ => (hderiv d x).hasFDerivWithinAt,
      fun d _ x _ => (hderiv d x).continuousAt.continuousWithinAt⟩
  refine ⟨contDiff_infty.mpr fun m => contDiffOn_univ.mp (hJ m).contDiffOn, fun d x => ?_⟩
  rw [← iteratedFDerivWithin_univ]
  exact ((hJ d).eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl uniqueDiffOn_univ (mem_univ _)).symm

end Differentiation

section NearMultiplier

private abbrev PressureInput := ComplexPressureTensor

private def pressureNearBlock (j : ℕ) (f : Vec3 → PressureInput) : Vec3 → ℂ :=
  operatorLiftConvolution (dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j) f

private theorem pressureNearBlock_integrableKernel (j : ℕ) :
    Integrable (dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j) :=
  integrable_scaledMultiplierKernel (by positivity)
    (𝓕⁻ pressureTensorAnnularSymbol : 𝓢(Vec3, PressureInput →L[ℂ] ℂ)).integrable

private theorem pressureNearBlock_meanZero (j : ℕ) :
    (∫ y, dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j y) = 0 := by
  let hc := annularLocalize_compact dyadicMultiplierCutoff_zero pressureTensorSymbol
  let hs := annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
    contDiffOn_pressureTensorSymbol
  change (∫ y, scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs) y) = 0
  rw [integral_scaledCompactMultiplierKernel hc hs (by positivity)]
  exact annularLocalize_zero_of_small dyadicMultiplierCutoff_unit pressureTensorSymbol 0 (by norm_num)

/-- The fixed half moment of the annular kernel times the dyadic scale factor. -/
private def pressureNearBlockMass (j : ℕ) : ℝ :=
  ∫ y, ‖dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j y‖ * Real.sqrt ‖y‖

private theorem pressureNearBlockMass_nonneg (j : ℕ) : 0 ≤ pressureNearBlockMass j :=
  integral_nonneg fun _ => by positivity

private theorem summable_pressureNearBlockMass : Summable pressureNearBlockMass := by
  let K := (𝓕⁻ pressureTensorAnnularSymbol : 𝓢(Vec3, PressureInput →L[ℂ] ℂ))
  let J := ∫ y, ‖K y‖ * Real.sqrt ‖y‖
  have hbase : (Real.sqrt (2 : ℝ))⁻¹ < 1 := (inv_lt_one₀ (Real.sqrt_pos.2 (by norm_num))).2
    (by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)])
  refine ((summable_geometric_of_lt_one (inv_nonneg.mpr (Real.sqrt_nonneg 2)) hbase).mul_right J).congr ?_
  intro j
  have hsqrt : Real.sqrt ((2 : ℝ) ^ j) = Real.sqrt 2 ^ j := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
  unfold pressureNearBlockMass dyadicEuclideanMultiplierKernel
  rw [integral_sqrtNorm_scaledMultiplierKernel (by positivity)]
  simp only [K, J, Real.sqrt_inv, hsqrt, inv_pow]

private theorem contDiff_pressureNearBlock (j : ℕ) {f : Vec3 → PressureInput}
    (hf : ContDiff ℝ ∞ f) (M : ℕ → ℝ) (hM : ∀ d x, ‖iteratedFDeriv ℝ d f x‖ ≤ M d) :
    ContDiff ℝ ∞ (pressureNearBlock j f) :=
  (contDiff_operatorLiftConvolution_of_bounded_jets (pressureNearBlock_integrableKernel j) hf M hM).1

private theorem norm_iteratedFDeriv_pressureNearBlock_le (j d : ℕ) {f : Vec3 → PressureInput}
    (hf : ContDiff ℝ ∞ f) (M : ℕ → ℝ) (hM : ∀ d x, ‖iteratedFDeriv ℝ d f x‖ ≤ M d)
    (x : Vec3) :
    ‖iteratedFDeriv ℝ d (pressureNearBlock j f) x‖ ≤
      (2 * M d + M (d + 1)) * pressureNearBlockMass j := by
  let K := dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j
  let J := iteratedFDeriv ℝ d f
  let L := (pressureConvolutionJetMap d (E := PressureInput) (F := ℂ)).flip (J x)
  have hK := pressureNearBlock_integrableKernel j
  have hJ : ContDiff ℝ 1 J := hf.iteratedFDeriv_right (by simp)
  have hD (z : Vec3) : ‖fderiv ℝ J z‖ ≤ M (d + 1) := by
    rw [norm_fderiv_iteratedFDeriv]
    exact hM (d + 1) z
  have hI₁ : Integrable (fun y => pressureConvolutionJetMap d (K y) (J (x - y))) :=
    integrable_pressureConvolutionJet d hK (hJ.continuous.comp (continuous_const.sub continuous_id))
      (fun y => hM d (x - y))
  have hI₂ : Integrable (fun y => pressureConvolutionJetMap d (K y) (J x)) :=
    L.integrable_comp hK
  have hCancel : (∫ y, pressureConvolutionJetMap d (K y) (J x)) = 0 := by
    calc
      _ = L (∫ y, K y) := L.integral_comp_comm hK
      _ = _ := by rw [pressureNearBlock_meanZero j, map_zero]
  have hDiff : (∫ y, pressureConvolutionJetMap d (K y) (J (x - y) - J x)) =
      ∫ y, pressureConvolutionJetMap d (K y) (J (x - y)) := by
    simp_rw [map_sub]
    rw [integral_sub hI₁ hI₂, hCancel, sub_zero]
  have hMoment := integrable_sqrtNorm_mul_norm_scaledMultiplierKernel (Λ := (2 : ℝ) ^ j)
    (by positivity) (𝓕⁻ pressureTensorAnnularSymbol : 𝓢(Vec3, PressureInput →L[ℂ] ℂ))
  change ‖iteratedFDeriv ℝ d (operatorLiftConvolution K f) x‖ ≤ _
  rw [(contDiff_operatorLiftConvolution_of_bounded_jets hK hf M hM).2 d x, ← hDiff,
    pressureNearBlockMass, ← integral_const_mul]
  apply norm_integral_le_of_norm_le (hMoment.const_mul _)
  refine Eventually.of_forall fun y => (norm_pressureConvolutionJetMap_le d (K y) _).trans ?_
  have hSmall := norm_sub_le_sqrt_dist_of_bounded_jet hJ (hM d) hD (x - y) x
  have hy : ‖x - y - x‖ = ‖y‖ := by
    rw [show x - y - x = -y by abel, norm_neg]
  rw [hy] at hSmall
  refine (mul_le_mul_of_nonneg_left hSmall (norm_nonneg _)).trans_eq ?_
  change ‖K y‖ * ((2 * M d + M (d + 1)) * Real.sqrt ‖y‖) =
    (2 * M d + M (d + 1)) * (‖K y‖ * Real.sqrt ‖y‖)
  ring

private def complexPressureTensorDyadicLift (f : Vec3 → PressureInput) (x : Vec3) : ℂ :=
  ∑' j, pressureNearBlock j f x

/-- The lifted torus pressure obtained by the actual dyadic pressure multiplier. -/
def pressureTensorDyadicLift (f : Vec3 → ComplexPressureTensor) (x : Vec3) : ℝ :=
  (complexPressureTensorDyadicLift f x).re

private theorem contDiff_complexPressureTensorDyadicLift {f : Vec3 → PressureInput}
    (hf : ContDiff ℝ ∞ f) (M : ℕ → ℝ) (hM : ∀ d x, ‖iteratedFDeriv ℝ d f x‖ ≤ M d) :
    ContDiff ℝ ∞ (complexPressureTensorDyadicLift f) ∧
      ∀ d x, iteratedFDeriv ℝ d (complexPressureTensorDyadicLift f) x =
        ∑' j, iteratedFDeriv ℝ d (pressureNearBlock j f) x := by
  have h := contDiffOn_tsum_of_jet_majorants (U := (univ : Set Vec3)) isOpen_univ
    (fun j => contDiff_pressureNearBlock j hf M hM)
    (b := fun d j => (2 * M d + M (d + 1)) * pressureNearBlockMass j)
    (fun _ => summable_pressureNearBlockMass.mul_left _)
    (fun d j x _ => norm_iteratedFDeriv_pressureNearBlock_le j d hf M hM x)
  exact ⟨contDiffOn_univ.mp h.1, fun d x => h.2 d (mem_univ x)⟩

/-- Smooth periodic tensor inputs yield a smooth pressure lift. -/
theorem contDiff_pressureTensorDyadicLift {f : Vec3 → ComplexPressureTensor}
    (hf : ContDiff ℝ ∞ f) (hp : SpatiallyPeriodic f) :
    ContDiff ℝ ∞ (pressureTensorDyadicLift f) := by
  choose M hM₀ hM using (fun d => exists_norm_iteratedFDeriv_le_of_smooth_periodic hf hp d)
  exact Complex.reCLM.contDiff.comp (contDiff_complexPressureTensorDyadicLift hf M hM).1

/-- The contribution of a smooth periodic tensor is controlled in a spatial
pressure jet by the two corresponding consecutive input jet bounds. -/
theorem norm_iteratedFDeriv_pressureTensorDyadicLift_le {f : Vec3 → ComplexPressureTensor}
    (hf : ContDiff ℝ ∞ f) (M : ℕ → ℝ) (hM : ∀ d x, ‖iteratedFDeriv ℝ d f x‖ ≤ M d)
    (d : ℕ) (x : Vec3) :
    ‖iteratedFDeriv ℝ d (pressureTensorDyadicLift f) x‖ ≤
      (2 * M d + M (d + 1)) * ∑' j, pressureNearBlockMass j := by
  have h := contDiff_complexPressureTensorDyadicLift hf M hM
  have hc := Complex.reCLM.norm_iteratedFDeriv_comp_left
    ((h.1.of_le (show (d : ℕ∞ω) ≤ ∞ by simp)).contDiffAt (x := x)) le_rfl
  have hMass := summable_pressureNearBlockMass.mul_left (2 * M d + M (d + 1))
  have hBounds := fun j => norm_iteratedFDeriv_pressureNearBlock_le j d hf M hM x
  have hSummable := hMass.of_nonneg_of_le (fun j => norm_nonneg _) hBounds
  have hn : ‖iteratedFDeriv ℝ d (complexPressureTensorDyadicLift f) x‖ ≤
      (2 * M d + M (d + 1)) * ∑' j, pressureNearBlockMass j := by
    rw [h.2 d x, ← tsum_mul_left]
    exact (norm_tsum_le_tsum_norm hSummable).trans (hSummable.tsum_le_tsum hBounds hMass)
  change ‖iteratedFDeriv ℝ d (Complex.reCLM ∘ complexPressureTensorDyadicLift f) x‖ ≤ _
  calc
    _ ≤ ‖Complex.reCLM‖ * ‖iteratedFDeriv ℝ d (complexPressureTensorDyadicLift f) x‖ := hc
    _ ≤ ‖iteratedFDeriv ℝ d (complexPressureTensorDyadicLift f) x‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (by rw [Complex.reCLM_norm])
    _ ≤ _ := hn

end NearMultiplier

section NearAgreement

local notation "Labels" => UnitAddTorus (Fin 3)

private theorem summable_pressureNearBlock_apply {f : Vec3 → ComplexPressureTensor}
    (hf : ContDiff ℝ ∞ f) (hp : SpatiallyPeriodic f) (x : Vec3) :
    Summable (fun j => pressureNearBlock j f x) := by
  choose M hM₀ hM using (fun d => exists_norm_iteratedFDeriv_le_of_smooth_periodic hf hp d)
  apply Summable.of_norm_bounded (summable_pressureNearBlockMass.mul_left (2 * M 0 + M 1))
  intro j
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add] using
    norm_iteratedFDeriv_pressureNearBlock_le j 0 hf M hM x

/-- The smooth dyadic lift is pointwise the bounded half-Hölder pressure
multiplier on the periodic descent of the tensor. -/
theorem pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier
    {f : Vec3 → ComplexPressureTensor} (hf : ContDiff ℝ ∞ f) (hp : SpatiallyPeriodic f)
    (q : HalfHolder Labels ComplexPressureTensor)
    (hq : ∀ x, HalfHolder.eval (toUnitTorus x) q = f x) :
    pressureTensorDyadicLift f = fun x => HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier q) := by
  funext x
  let hc := annularLocalize_compact dyadicMultiplierCutoff_zero pressureTensorSymbol
  let hs := annularLocalize_smooth dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
    contDiffOn_pressureTensorSymbol
  have hfull := tendsto_operatorLiftConvolution_compactSymbolDyadicBlocks
    (fun z hz => dyadicMultiplierCutoff_zero z hz.le) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit hc hs
    (annularLocalize_zero_of_small dyadicMultiplierCutoff_unit pressureTensorSymbol 0 (by norm_num))
    (fun z hz => annularLocalize_zero_of_large dyadicMultiplierCutoff_zero pressureTensorSymbol z
      (by linarith)) q x
  have hLift : (fun z => continuousHalfHolder q (toUnitTorus z)) = f := funext hq
  change Tendsto (fun N => ∑ j ∈ Finset.range N,
    operatorLiftConvolution (dyadicEuclideanMultiplierKernel pressureTensorAnnularSymbol j)
      (fun z => continuousHalfHolder q (toUnitTorus z)) x) atTop
    (𝓝 (HalfHolder.eval (toUnitTorus x)
      ((homogeneousDyadicBlocks dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
        dyadicMultiplierCutoff_zero contDiffOn_pressureTensorSymbol).toMultiplier q))) at hfull
  rw [hLift] at hfull
  have hsum := (summable_pressureNearBlock_apply hf hp x).hasSum.tendsto_sum_nat
  have heq := tendsto_nhds_unique hsum hfull
  unfold pressureTensorDyadicLift complexPressureTensorDyadicLift pressureTensorMultiplier
  rw [ContinuousLinearMap.comp_apply, HalfHolder.eval_map]
  change (∑' j, pressureNearBlock j f x).re =
    Complex.reCLM (HalfHolder.eval (toUnitTorus x) (complexPressureTensorMultiplier q))
  unfold complexPressureTensorMultiplier
  rw [heq]
  simp [homogeneousHalfHolderMultiplier, pressureTensorSymbol_zero]

private theorem pressureTensorDyadicLift_sub {f g : Vec3 → ComplexPressureTensor}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hfp : SpatiallyPeriodic f) (hgp : SpatiallyPeriodic g) :
    pressureTensorDyadicLift (f - g) = pressureTensorDyadicLift f - pressureTensorDyadicLift g := by
  obtain ⟨fq, hfq, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hfp
    (spatialHolderHalf_of_contDiff_periodic hf hfp 0)
  obtain ⟨gq, hgq, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hgp
    (spatialHolderHalf_of_contDiff_periodic hg hgp 0)
  have hp : SpatiallyPeriodic (f - g) := fun n x => by
    simp only [Pi.sub_apply, hfp n x, hgp n x]
  have hq (x : Vec3) : HalfHolder.eval (toUnitTorus x) (fq - gq) = (f - g) x := by
    simp only [map_sub, hfq, hgq, Pi.sub_apply]
  change pressureTensorDyadicLift (fun x => f x - g x) = _
  rw [pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier (hf.sub hg) hp (fq - gq) hq,
    pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier hf hfp fq hfq,
    pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier hg hgp gq hgq]
  funext x
  simp only [map_sub, Pi.sub_apply]

/-- The pressure multiplier takes uniform convergence of every spatial tensor
jet on the cell to uniform convergence of every pressure jet on the lift. -/
theorem tendstoUniformly_pressureTensorDyadicLift_iteratedFDeriv
    {ι : Type*} {l : Filter ι} {f : ι → Vec3 → ComplexPressureTensor}
    {g : Vec3 → ComplexPressureTensor}
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) (hg : ContDiff ℝ ∞ g)
    (hfp : ∀ i, SpatiallyPeriodic (f i)) (hgp : SpatiallyPeriodic g)
    (hj : ∀ d, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (f i))
      (iteratedFDeriv ℝ d g) l centeredCell) (d : ℕ) :
    TendstoUniformly (fun i => iteratedFDeriv ℝ d (pressureTensorDyadicLift (f i)))
      (iteratedFDeriv ℝ d (pressureTensorDyadicLift g)) l := by
  let C := ∑' j, pressureNearBlockMass j
  have hC : 0 ≤ C := tsum_nonneg pressureNearBlockMass_nonneg
  rw [← tendstoUniformlyOn_univ]
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  let δ := ε / (3 * C + 1)
  have hδ : 0 < δ := div_pos hε (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hj d) δ hδ,
    Metric.tendstoUniformlyOn_iff.1 (hj (d + 1)) δ hδ] with i hi hi' x hx
  have hfd : ContDiff ℝ ∞ (f i - g) := (hf i).sub hg
  have hp : SpatiallyPeriodic (f i - g) := fun n y => by simp only [Pi.sub_apply, hfp i n y, hgp n y]
  have hsmall (e : ℕ) (he : ∀ y ∈ centeredCell,
      dist (iteratedFDeriv ℝ e g y) (iteratedFDeriv ℝ e (f i) y) < δ) (y : Vec3) :
      ‖iteratedFDeriv ℝ e (f i - g) y‖ ≤ δ := by
    obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell y
    have hper := pressureJet_periodic hp e n (y - latticeVector n)
    rw [sub_add_cancel] at hper
    rw [hper, iteratedFDeriv_sub_apply (((hf i).of_le (by simp)).contDiffAt)
      ((hg.of_le (by simp)).contDiffAt), ← dist_eq_norm, dist_comm]
    exact (he _ hn).le
  choose N hN₀ hN using (fun e => exists_norm_iteratedFDeriv_le_of_smooth_periodic hfd hp e)
  let M (e : ℕ) := if e = d ∨ e = d + 1 then δ else N e
  have hM (e : ℕ) (y : Vec3) : ‖iteratedFDeriv ℝ e (f i - g) y‖ ≤ M e := by
    unfold M
    split
    · rename_i he
      rcases he with he | he <;> subst e
      · exact hsmall d hi y
      · exact hsmall (d + 1) hi' y
    · exact hN e y
  rw [dist_comm, dist_eq_norm, ← iteratedFDeriv_sub_apply
    (((contDiff_pressureTensorDyadicLift (hf i) (hfp i)).of_le (by simp)).contDiffAt)
    (((contDiff_pressureTensorDyadicLift hg hgp).of_le (by simp)).contDiffAt),
    ← pressureTensorDyadicLift_sub (hf i) hg (hfp i) hgp]
  have hbound := norm_iteratedFDeriv_pressureTensorDyadicLift_le hfd M hM d x
  refine hbound.trans_lt ?_
  have hcoef : (2 * M d + M (d + 1)) * C = 3 * C * δ := by simp [M]; ring
  change (2 * M d + M (d + 1)) * C < ε
  rw [hcoef]
  calc
    _ < (3 * C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ = ε := by rw [mul_comm, div_mul_cancel₀ _ (by positivity : 3 * C + 1 ≠ 0)]

end NearAgreement

section TensorJets

/-- The complex coordinates of the real tensor (uotimes u). -/
def pressureVelocityTensor (v : Vec3 → Vec3) (x : Vec3) : ComplexPressureTensor :=
  velocityPressureTensor (v x) (v x)

private theorem contDiffOn_pressureVelocityTensor {U : Set Vec3} {v : Vec3 → Vec3}
    (h : ContDiffOn ℝ ∞ v U) : ContDiffOn ℝ ∞ (pressureVelocityTensor v) U :=
  (velocityPressureTensor.contDiff.comp_contDiffOn h).clm_apply h

private theorem spatiallyPeriodic_pressureVelocityTensor {v : Vec3 → Vec3}
    (h : SpatiallyPeriodic v) : SpatiallyPeriodic (pressureVelocityTensor v) :=
  fun n x => by simp only [pressureVelocityTensor, h n x]

private theorem norm_iteratedFDeriv_velocityPressureTensor_bilinear_le
    {f g : Vec3 → Vec3} (hf : ContDiffOn ℝ ∞ f offOrigin)
    (hg : ContDiffOn ℝ ∞ g offOrigin) (d : ℕ) {x : Vec3} (hx : x ∈ offOrigin)
    {P Q : ℝ} (hP : 0 ≤ P)
    (hfB : ∀ i ≤ d, ‖iteratedFDeriv ℝ i f x‖ ≤ P)
    (hgB : ∀ i ≤ d, ‖iteratedFDeriv ℝ i g x‖ ≤ Q) :
    ‖iteratedFDeriv ℝ d (fun y => velocityPressureTensor (f y) (g y)) x‖ ≤
      ‖velocityPressureTensor‖ * ((2 : ℝ) ^ d * P * Q) := by
  have h := velocityPressureTensor.norm_iteratedFDerivWithin_le_of_bilinear hf hg
    isOpen_offOrigin.uniqueDiffOn hx (n := d) (by simp)
  simp_rw [iteratedFDerivWithin_of_isOpen _ isOpen_offOrigin hx] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ velocityPressureTensor.opNorm_nonneg)
  calc
    _ ≤ ∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ) * P * Q := by
      apply Finset.sum_le_sum
      intro i hi
      have hid : i ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hfB i hid) (Nat.cast_nonneg _))
        (hgB (d - i) (Nat.sub_le _ _)) (norm_nonneg _) (by positivity)
    _ = _ := by
      have hd : (∑ i ∈ Finset.range (d + 1), (d.choose i : ℝ)) = (2 : ℝ) ^ d := by
        exact_mod_cast Nat.sum_range_choose d
      rw [← Finset.sum_mul, ← Finset.sum_mul, hd]

set_option maxHeartbeats 800000 in
/-- Uniform convergence of velocity jets on a compact set implies convergence
of the actual tensor jets on that set. -/
theorem tendstoUniformlyOn_iteratedFDeriv_pressureVelocityTensor
    {ι : Type*} {l : Filter ι} {S : Set Vec3} (hS : IsCompact S) (hSo : S ⊆ offOrigin)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) offOrigin) (hw : ContDiffOn ℝ ∞ w offOrigin)
    (hJ : ∀ d, TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (v i)) (iteratedFDeriv ℝ d w) l S)
    (d : ℕ) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (pressureVelocityTensor (v i)))
      (iteratedFDeriv ℝ d (pressureVelocityTensor w)) l S := by
  have hB (j : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ S, ‖iteratedFDeriv ℝ j w x‖ ≤ M := by
    have hc : ContinuousOn (iteratedFDeriv ℝ j w) S := by
      intro x hx
      exact (((hw.contDiffAt (isOpen_offOrigin.mem_nhds (hSo hx))).continuousAt_iteratedFDeriv
        (k := j) (by simp)).continuousWithinAt)
    obtain ⟨M, hM⟩ := hS.exists_bound_of_continuousOn hc
    exact ⟨max 0 M, le_max_left _ _, fun x hx => (hM x hx).trans (le_max_right _ _)⟩
  choose M hM₀ hM using hB
  let R := ∑ j ∈ Finset.range (d + 1), M j
  have hR : 0 ≤ R := Finset.sum_nonneg fun j _ => hM₀ j
  have hRw (j : ℕ) (hj : j ≤ d) (x : Vec3) (hx : x ∈ S) : ‖iteratedFDeriv ℝ j w x‖ ≤ R :=
    (hM j x hx).trans (Finset.single_le_sum (fun j _ => hM₀ j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  let C := ‖velocityPressureTensor‖ * (2 : ℝ) ^ d * (2 * R + 1)
  have hC : 0 ≤ C := by unfold C; positivity
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  let δ := min 1 (ε / (C + 1))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε (by positivity))
  have hsmall : ∀ᶠ i in l, ∀ j ∈ Finset.range (d + 1), ∀ x ∈ S,
      ‖iteratedFDeriv ℝ j (v i) x - iteratedFDeriv ℝ j w x‖ < δ := by
    rw [eventually_all_finset]
    intro j _
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hJ j) δ hδ] with i hi x hx
    rw [← dist_eq_norm, dist_comm]
    exact hi x hx
  filter_upwards [hsmall] with i hi x hx
  have hxo := hSo hx
  let e := v i - w
  have hE : ContDiffOn ℝ ∞ e offOrigin := (hv i).sub hw
  have hEB (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j e x‖ ≤ δ := by
    unfold e
    rw [iteratedFDeriv_sub_apply
      ((hv i).contDiffAt (isOpen_offOrigin.mem_nhds hxo) |>.of_le (by simp))
      (hw.contDiffAt (isOpen_offOrigin.mem_nhds hxo) |>.of_le (by simp))]
    exact (hi j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) x hx).le
  have hV (j : ℕ) (hj : j ≤ d) : ‖iteratedFDeriv ℝ j (v i) x‖ ≤ R + 1 := by
    have ht := norm_le_norm_sub_add (iteratedFDeriv ℝ j (v i) x) (iteratedFDeriv ℝ j w x)
    exact ht.trans (by linarith [hRw j hj x hx, hi j (Finset.mem_range.mpr
      (Nat.lt_succ_of_le hj)) x hx, min_le_left (1 : ℝ) (ε / (C + 1))])
  let A := fun y => velocityPressureTensor (e y) (v i y)
  let B := fun y => velocityPressureTensor (w y) (e y)
  have hAB : pressureVelocityTensor (v i) - pressureVelocityTensor w = A + B := by
    funext y
    simp only [pressureVelocityTensor, A, B, e, Pi.sub_apply, Pi.add_apply,
      map_sub, sub_apply]
    abel
  have hAd : ContDiffAt ℝ d A x :=
    ((velocityPressureTensor.contDiff.comp_contDiffOn hE).clm_apply (hv i)
      |>.contDiffAt (isOpen_offOrigin.mem_nhds hxo)).of_le (by simp)
  have hBd : ContDiffAt ℝ d B x :=
    ((velocityPressureTensor.contDiff.comp_contDiffOn hw).clm_apply hE
      |>.contDiffAt (isOpen_offOrigin.mem_nhds hxo)).of_le (by simp)
  rw [dist_comm, dist_eq_norm, ← iteratedFDeriv_sub_apply
    ((contDiffOn_pressureVelocityTensor (hv i)).contDiffAt (isOpen_offOrigin.mem_nhds hxo)
      |>.of_le (by simp))
    ((contDiffOn_pressureVelocityTensor hw).contDiffAt (isOpen_offOrigin.mem_nhds hxo)
      |>.of_le (by simp)), hAB, iteratedFDeriv_add_apply hAd hBd]
  have hA := norm_iteratedFDeriv_velocityPressureTensor_bilinear_le hE (hv i) d hxo hδ.le hEB hV
  have hB := norm_iteratedFDeriv_velocityPressureTensor_bilinear_le hw hE d hxo hR
    (fun j hj => hRw j hj x hx) hEB
  calc
    _ ≤ ‖iteratedFDeriv ℝ d A x‖ + ‖iteratedFDeriv ℝ d B x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add hA hB
    _ = C * δ := by unfold C; ring
    _ < (C + 1) * δ := mul_lt_mul_of_pos_right (lt_add_one _) hδ
    _ ≤ ε := by
      exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans_eq
        (by rw [mul_comm, div_mul_cancel₀ _ (by positivity : C + 1 ≠ 0)])

private def nearPressureCutoffTensor (χ : Vec3 → ℝ) (v : Vec3 → Vec3) (x : Vec3) :
    ComplexPressureTensor := χ x • pressureVelocityTensor v x

private theorem contDiff_nearPressureCutoffTensor {χ : Vec3 → ℝ} {v : Vec3 → Vec3}
    (hχ : ContDiff ℝ ∞ χ) (hsupp : tsupport χ ⊆ offOrigin)
    (hv : ContDiffOn ℝ ∞ v offOrigin) :
    ContDiff ℝ ∞ (nearPressureCutoffTensor χ v) :=
  contDiff_infty.mpr fun m =>
    contDiff_cutoff_smul_of_contDiffOn_offOrigin (hχ.of_le (by simp)) hsupp
      ((contDiffOn_pressureVelocityTensor hv).of_le (by simp))

private theorem spatiallyPeriodic_nearPressureCutoffTensor {χ : Vec3 → ℝ} {v : Vec3 → Vec3}
    (hχ : SpatiallyPeriodic χ) (hv : SpatiallyPeriodic v) :
    SpatiallyPeriodic (nearPressureCutoffTensor χ v) :=
  fun n x => by simp only [nearPressureCutoffTensor, hχ n x, spatiallyPeriodic_pressureVelocityTensor hv n x]

private theorem tendstoUniformlyOn_nearPressureCutoffTensor
    {ι : Type*} {l : Filter ι} {χ : Vec3 → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hsupp : tsupport χ ⊆ offOrigin) {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : ∀ i, ContDiffOn ℝ ∞ (v i) offOrigin) (hw : ContDiffOn ℝ ∞ w offOrigin)
    (hJ : ∀ S : Set Vec3, IsCompact S → S ⊆ offOrigin → ∀ d,
      TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (v i)) (iteratedFDeriv ℝ d w) l S) (d : ℕ) :
    TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (nearPressureCutoffTensor χ (v i)))
      (iteratedFDeriv ℝ d (nearPressureCutoffTensor χ w)) l centeredCell :=
  tendstoUniformlyOn_cutoff_smul_spatial_jets isCompact_centeredCell hχ hsupp
    (fun i => (contDiffOn_pressureVelocityTensor (hv i)).of_le (by simp))
    ((contDiffOn_pressureVelocityTensor hw).of_le (by simp))
    (fun j _ => tendstoUniformlyOn_iteratedFDeriv_pressureVelocityTensor
      (isCompact_centeredCell.inter_right (isClosed_tsupport χ)) (inter_subset_right.trans hsupp)
      hv hw (hJ _ (isCompact_centeredCell.inter_right (isClosed_tsupport χ))
        (inter_subset_right.trans hsupp)) j) d le_rfl

end TensorJets

section FarAssembly

/-- The compact part of the fundamental cell where the far tensor may be nonzero. -/
def farPressureSourceSet (χ : Vec3 → ℝ) : Set Vec3 :=
  closure multiplierKernelCell ∩ tsupport (fun y => 1 - χ y)

/-- The tensor density entering the far pressure after a scalar cutoff. -/
noncomputable def farPressureCutoffTensor (χ : Vec3 → ℝ) (v : Vec3 → Vec3) (y : Vec3) :
    ComplexPressureTensor :=
  (1 - χ y) • velocityPressureTensor (v y) (v y)

theorem isCompact_farPressureSourceSet (χ : Vec3 → ℝ) :
    IsCompact (farPressureSourceSet χ) :=
  isCompact_closure_multiplierKernelCell.inter_right (isClosed_tsupport _)

theorem farPressureCutoffTensor_eq_zero_of_notMem {χ : Vec3 → ℝ} {v : Vec3 → Vec3}
    {y : Vec3} (hy : y ∈ multiplierKernelCell) (hys : y ∉ farPressureSourceSet χ) :
    farPressureCutoffTensor χ v y = 0 := by
  have hy' : y ∉ tsupport (fun z => 1 - χ z) := fun h => hys ⟨subset_closure hy, h⟩
  have hzero : 1 - χ y = 0 := by
    by_contra h
    exact hy' (subset_closure h)
  simp [farPressureCutoffTensor, hzero]

theorem exists_open_farPressureSourceSet_separated {K : Set Vec3} (hK : IsCompact K)
    {χ : Vec3 → ℝ}
    (hsep : ∀ x ∈ K, ∀ y ∈ tsupport (fun z => 1 - χ z), x - y ∈ offOrigin) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧
      ∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin := by
  obtain ⟨r, hr, hb⟩ := exists_periodically_separated_neighborhood hK
    (isCompact_farPressureSourceSet χ) (fun x hx y hy => hsep x hx y hy.2)
  refine ⟨thickening r K, isOpen_thickening, self_subset_thickening hr K, ?_⟩
  intro x hx y hy
  rintro ⟨n, hn⟩
  have h := hb x (thickening_subset_cthickening r K hx) y hy n
  rw [hn, dist_self] at h
  exact hr.not_gt h

set_option maxHeartbeats 500000 in
/-- Integration against an integrable separated tensor gives a smooth pressure
at every target point, including when the tensor itself is only integrable. -/
theorem contDiffOn_periodicFarPressure_of_separated_integrable {U S : Set Vec3}
    (hS : IsCompact S) (hsep : ∀ x ∈ U, ∀ y ∈ S, x - y ∈ offOrigin)
    {P : Vec3 → ComplexPressureTensor} (hP : IntegrableOn P (S ∩ multiplierKernelCell)) :
    ContDiffOn ℝ ∞ (periodicFarPressure S P) U := by
  let μ := (volume : Measure Vec3).restrict multiplierKernelCell
  let ν := μ.restrict S
  have hν : ν = (volume : Measure Vec3).restrict (S ∩ multiplierKernelCell) :=
    Measure.restrict_restrict hS.isClosed.measurableSet
  have hPi : Integrable P ν := by rw [hν]; exact hP
  let J := periodicFarMultiplierJet pressureTensorAnnularSymbol pressureTensorRealOutput
  have hf : periodicFarPressure S P = (fun x => (farKernelIntegral ν (J 0) P x).curry0) := by
    funext x
    let C := continuousMultilinearCurryFin0 ℝ Vec3 ℝ
    change (∫ y in S ∩ multiplierKernelCell,
      pressureTensorRealOutput (dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol
        (x - y)) (P y)) = C (∫ y, J 0 x y (P y) ∂ν)
    rw [← hν]
    calc
      _ = ∫ y, C (J 0 x y (P y)) ∂ν := rfl
      _ = _ := LinearIsometry.integral_comp_comm (μ := ν) C.toLinearIsometry _
  intro x hx
  obtain ⟨W, hW, hxW, hMeas, hNorm, hDeriv⟩ :=
    exists_periodicFarMultiplierJet_bounds pressureTensorAnnularSymbol pressureTensorRealOutput
      (isCompact_singleton : IsCompact ({x} : Set Vec3)) hS (fun z hz y hy =>
        (mem_singleton_iff.mp hz).symm ▸ hsep x hx y hy) μ
  have hs : ContDiffOn ℝ ∞ (periodicFarPressure S P) W := by
    apply contDiffOn_infty.mpr
    intro d
    rw [hf]
    exact (contDiffOn_farKernelIntegral_of_spatial_jets hW hPi hMeas hNorm hDeriv d).1
  exact (hs.contDiffAt (hW.mem_nhds (hxW (mem_singleton x)))).contDiffWithinAt

/-- A supported far tensor has the same lifted multiplier pressure and kernel pressure
on every open neighborhood separated from the source. -/
theorem eqOn_lift_farPressureTensorMultiplier {χ : Vec3 → ℝ} {v : Vec3 → Vec3}
    {U : Set Vec3}
    (hsep : ∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin)
    (F : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor)
    (hF : ∀ y ∈ multiplierKernelCell,
      HalfHolder.eval (toUnitTorus y) F = farPressureCutoffTensor χ v y) :
    EqOn (fun x => HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier F))
      (periodicFarPressure (farPressureSourceSet χ) (farPressureCutoffTensor χ v)) U := by
  intro x hx
  change HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier F) = _
  rw [eval_pressureTensorMultiplier_eq_periodicFarPressure F x
    (isCompact_farPressureSourceSet χ) (hsep x hx)
    (fun y hy hys => (hF y hy).trans (farPressureCutoffTensor_eq_zero_of_notMem hy hys))]
  unfold periodicFarPressure
  apply setIntegral_congr_fun
  · exact (isCompact_farPressureSourceSet χ).isClosed.measurableSet.inter
      (ZSpan.fundamentalDomain_measurableSet _)
  · intro y hy
    exact congrArg (fun T : ComplexPressureTensor => pressureTensorRealOutput
      (dyadicPeriodicMultiplierKernel pressureTensorAnnularSymbol (x - y)) T) (hF y hy.2)

/-- The two descriptions of the far pressure have equal gradient jets on the
open separated target. -/
theorem eqOn_iteratedFDeriv_gradient_lift_farPressureTensorMultiplier
    {χ : Vec3 → ℝ} {v : Vec3 → Vec3} {U : Set Vec3} (hU : IsOpen U)
    (hsep : ∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin)
    (F : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor)
    (hF : ∀ y ∈ multiplierKernelCell,
      HalfHolder.eval (toUnitTorus y) F = farPressureCutoffTensor χ v y) (d : ℕ) :
    EqOn
      (iteratedFDeriv ℝ d (gradient (fun x =>
        HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier F))))
      (iteratedFDeriv ℝ d (gradient (periodicFarPressure
        (farPressureSourceSet χ) (farPressureCutoffTensor χ v)))) U := by
  intro x hx
  have hlocal := (eqOn_lift_farPressureTensorMultiplier hsep F hF).eventuallyEq_of_mem
    (hU.mem_nhds hx)
  have hjet := (hlocal.iteratedFDeriv ℝ (d + 1)).eq_of_nhds
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [norm_iteratedFDeriv_gradient_sub_eq, hjet, sub_self, norm_zero]

private theorem continuousOn_farPressureCutoffTensor {χ : Vec3 → ℝ} {v : Vec3 → Vec3}
    {S : Set Vec3} (hχ : ContinuousOn χ S) (hv : ContinuousOn v S) :
    ContinuousOn (farPressureCutoffTensor χ v) S :=
  (continuousOn_const.sub hχ).smul
    ((velocityPressureTensor.continuous.comp_continuousOn hv).clm_apply hv)

private theorem tendsto_l1_farPressureCutoffTensor {ι : Type*} {l : Filter ι} {S : Set Vec3}
    (hS : IsCompact S) {χ : Vec3 → ℝ} (hχ : ∀ y, χ y ∈ Icc (0 : ℝ) 1)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : TendstoUniformlyOn v w l S) (hvc : ∀ i, ContinuousOn (v i) S)
    (hwc : ContinuousOn w S) :
    Tendsto (fun i => ∫ y in S ∩ multiplierKernelCell,
      ‖farPressureCutoffTensor χ (v i) y - farPressureCutoffTensor χ w y‖) l (𝓝 0) := by
  let μ := (volume : Measure Vec3).restrict multiplierKernelCell
  let V (b : Vec3 → Vec3) (y : Vec3) := velocityPressureTensor (b y) (b y)
  have hm : μ S < ⊤ :=
    ((Measure.restrict_le_self : μ ≤ volume) S).trans_lt hS.measure_lt_top
  have ht := tendsto_l1_tensor_of_uniform_velocity (μ := μ) hS hm velocityPressureTensor hv hwc
  have hrest : μ.restrict S = (volume : Measure Vec3).restrict (S ∩ multiplierKernelCell) :=
    Measure.restrict_restrict hS.isClosed.measurableSet
  rw [hrest] at ht
  refine squeeze_zero (fun i => integral_nonneg fun _ => norm_nonneg _) (fun i => ?_) ht
  have hVi (b : Vec3 → Vec3) (hb : ContinuousOn b S) :
      IntegrableOn (V b) (S ∩ multiplierKernelCell) :=
    ((velocityPressureTensor.continuous.comp_continuousOn hb).clm_apply hb
      |>.integrableOn_compact hS).mono_set inter_subset_left
  apply integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
    (((hVi (v i) (hvc i)).sub (hVi w hwc)).norm)
  exact Eventually.of_forall fun y => by
    change ‖(1 - χ y) • V (v i) y - (1 - χ y) • V w y‖ ≤ ‖V (v i) y - V w y‖
    rw [← smul_sub, norm_smul, Real.norm_of_nonneg (sub_nonneg.mpr (hχ y).2)]
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith [(hχ y).1])

/-- The cutoff far pressure gradient converges with every spatial derivative, using only
uniform convergence of the velocity on the source cell. -/
theorem exists_tendstoUniformlyOn_cutoffFarPressureGradient_spatial_derivatives
    {ι : Type*} {l : Filter ι} {K : Set Vec3} (hK : IsCompact K)
    {χ : Vec3 → ℝ} (hχc : Continuous χ) (hχ : ∀ y, χ y ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ x ∈ K, ∀ y ∈ tsupport (fun z => 1 - χ z), x - y ∈ offOrigin)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : TendstoUniformlyOn v w l (closure multiplierKernelCell))
    (hvc : ∀ i, ContinuousOn (v i) (closure multiplierKernelCell))
    (hwc : ContinuousOn w (closure multiplierKernelCell)) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧
      (∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin) ∧
      ∀ d : ℕ, TendstoUniformlyOn
        (fun i => iteratedFDeriv ℝ d (gradient (periodicFarPressure
          (farPressureSourceSet χ) (farPressureCutoffTensor χ (v i)))))
        (iteratedFDeriv ℝ d (gradient (periodicFarPressure
          (farPressureSourceSet χ) (farPressureCutoffTensor χ w)))) l U := by
  let S := farPressureSourceSet χ
  have hS := isCompact_farPressureSourceSet χ
  have hSc : S ⊆ closure multiplierKernelCell := inter_subset_left
  have hsepS : ∀ x ∈ K, ∀ y ∈ S, x - y ∈ offOrigin := fun x hx y hy => hsep x hx y hy.2
  obtain ⟨U₀, hU₀, hKU₀, hsep₀⟩ := exists_open_farPressureSourceSet_separated hK hsep
  obtain ⟨U₁, hU₁, hKU₁, hB⟩ :=
    exists_norm_iteratedFDeriv_periodicFarPressureGradient_sub_le hK hS hsepS
  have hL1 := tendsto_l1_farPressureCutoffTensor hS hχ (hv.mono hSc)
    (fun i => (hvc i).mono hSc) (hwc.mono hSc)
  have hint (b : Vec3 → Vec3) (hb : ContinuousOn b S) :
      IntegrableOn (farPressureCutoffTensor χ b) (S ∩ multiplierKernelCell) :=
    ((continuousOn_farPressureCutoffTensor hχc.continuousOn hb).integrableOn_compact hS
      ).mono_set inter_subset_left
  refine ⟨U₀ ∩ U₁, hU₀.inter hU₁, fun x hx => ⟨hKU₀ hx, hKU₁ hx⟩,
    fun x hx => hsep₀ x hx.1, fun d => ?_⟩
  obtain ⟨C, _, hBd⟩ := hB d
  have hc := tendsto_const_nhds (x := C) |>.mul hL1
  rw [mul_zero, Metric.tendsto_nhds] at hc
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [hc ε hε] with i hi x hx
  rw [dist_comm, dist_eq_norm]
  have hb := hBd _ _ (hint (v i) ((hvc i).mono hSc)) (hint w (hwc.mono hSc)) x hx.2
  rw [Real.dist_eq, sub_zero] at hi
  exact (hb.trans (le_abs_self _)).trans_lt hi

/-- On a compact target the actual Fourier multiplier on the cutoff far tensors has
the convergent gradient jets of the separated pressure integral. -/
theorem tendstoUniformlyOn_lift_farPressureTensorMultiplier_spatial_derivatives
    {ι : Type*} {l : Filter ι} {K : Set Vec3} (hK : IsCompact K)
    {χ : Vec3 → ℝ} (hχc : Continuous χ) (hχ : ∀ y, χ y ∈ Icc (0 : ℝ) 1)
    (hsep : ∀ x ∈ K, ∀ y ∈ tsupport (fun z => 1 - χ z), x - y ∈ offOrigin)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : TendstoUniformlyOn v w l (closure multiplierKernelCell))
    (hvc : ∀ i, ContinuousOn (v i) (closure multiplierKernelCell))
    (hwc : ContinuousOn w (closure multiplierKernelCell))
    (F : ι → HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor)
    (hF : ∀ᶠ i in l, ∀ y ∈ multiplierKernelCell,
      HalfHolder.eval (toUnitTorus y) (F i) = farPressureCutoffTensor χ (v i) y) (d : ℕ) :
    TendstoUniformlyOn
      (fun i => iteratedFDeriv ℝ d (gradient (fun x =>
        HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier (F i)))))
      (iteratedFDeriv ℝ d (gradient (periodicFarPressure
        (farPressureSourceSet χ) (farPressureCutoffTensor χ w)))) l K := by
  obtain ⟨U, hU, hKU, hsepU, hlim⟩ :=
    exists_tendstoUniformlyOn_cutoffFarPressureGradient_spatial_derivatives
      hK hχc hχ hsep hv hvc hwc
  refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 (hlim d) ε hε, hF]
    with i hi hFi x hx
  rw [eqOn_iteratedFDeriv_gradient_lift_farPressureTensorMultiplier
    hU hsepU (F i) hFi d (hKU hx)]
  exact hi x (hKU hx)

end FarAssembly

section PressureLimit

private theorem contDiffOn_gradient_of_smooth {f : Vec3 → ℝ} {U : Set Vec3}
    (hU : IsOpen U) (hf : ContDiffOn ℝ ∞ f U) : ContDiffOn ℝ ∞ (gradient f) U := by
  let R : (Vec3 →L[ℝ] ℝ) →L[ℝ] Vec3 :=
    (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv.toContinuousLinearMap
  exact R.contDiff.comp_contDiffOn (hf.fderiv_of_isOpen hU (by simp))

private theorem eqOn_pressureTensorDyadicLift_cutoff_add_far {K : Set Vec3}
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχp : SpatiallyPeriodic χ)
    (hsupp : tsupport χ ⊆ offOrigin) {v : Vec3 → Vec3} (hv : ContDiff ℝ ∞ v)
    (hvp : SpatiallyPeriodic v)
    (hsep : ∀ x ∈ K, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin) :
    EqOn (pressureTensorDyadicLift (pressureVelocityTensor v))
      (pressureTensorDyadicLift (nearPressureCutoffTensor χ v) +
        periodicFarPressure (farPressureSourceSet χ) (farPressureCutoffTensor χ v)) K := by
  let N := nearPressureCutoffTensor χ v
  let F := farPressureCutoffTensor χ v
  have ht : ContDiff ℝ ∞ (pressureVelocityTensor v) :=
    (velocityPressureTensor.contDiff.comp hv).clm_apply hv
  have htp := spatiallyPeriodic_pressureVelocityTensor hvp
  have hN := contDiff_nearPressureCutoffTensor hχ hsupp hv.contDiffOn
  have hNp := spatiallyPeriodic_nearPressureCutoffTensor hχp hvp
  have hF : ContDiff ℝ ∞ F := (contDiff_const.sub hχ).smul ht
  have hFp : SpatiallyPeriodic F := fun n x => by
    simp only [F, farPressureCutoffTensor, hχp n x, hvp n x]
  obtain ⟨qn, hqn, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hNp
    (spatialHolderHalf_of_contDiff_periodic hN hNp 0)
  obtain ⟨qf, hqf, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hFp
    (spatialHolderHalf_of_contDiff_periodic hF hFp 0)
  have hq (x : Vec3) : HalfHolder.eval (toUnitTorus x) (qn + qf) = pressureVelocityTensor v x := by
    rw [map_add, hqn, hqf]
    change χ x • pressureVelocityTensor v x + (1 - χ x) • pressureVelocityTensor v x = _
    rw [← add_smul, add_sub_cancel, one_smul]
  have hfull := pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier ht htp (qn + qf) hq
  have hnear := pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier hN hNp qn hqn
  have hfar := eqOn_lift_farPressureTensorMultiplier hsep qf (fun y _ => hqf y)
  intro x hx
  rw [hfull, Pi.add_apply, hnear]
  change HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier (qn + qf)) =
    HalfHolder.eval (toUnitTorus x) (pressureTensorMultiplier qn) +
      periodicFarPressure (farPressureSourceSet χ) (farPressureCutoffTensor χ v) x
  rw [map_add, map_add]
  exact congrArg (_ + ·) (hfar hx)

private theorem contDiffOn_cutoffFarPressure {χ : Vec3 → ℝ} (hc : Continuous χ)
    {v : Vec3 → Vec3} (hv : Continuous v) {U : Set Vec3}
    (hsep : ∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin) :
    ContDiffOn ℝ ∞ (periodicFarPressure (farPressureSourceSet χ) (farPressureCutoffTensor χ v)) U :=
  contDiffOn_periodicFarPressure_of_separated_integrable (isCompact_farPressureSourceSet χ) hsep
    ((continuousOn_farPressureCutoffTensor hc.continuousOn hv.continuousOn
      |>.integrableOn_compact (isCompact_farPressureSourceSet χ)).mono_set inter_subset_left)

set_option maxHeartbeats 1000000 in
/-- Given the global velocity limit and compact-local convergence of every
velocity jet, the actual periodic pressure gradients converge in every spatial
jet on a neighborhood of each compact set off the singular lattice. -/
theorem exists_tendstoUniformlyOn_pressureGradient_of_velocity_jets
    {ι : Type*} {l : Filter ι} {K : Set Vec3} (hK : IsCompact K) (hKo : K ⊆ offOrigin)
    {v : ι → Vec3 → Vec3} {w : Vec3 → Vec3}
    (hv : ∀ i, ContDiff ℝ ∞ (v i)) (hvp : ∀ i, SpatiallyPeriodic (v i))
    (hw : Continuous w) (hws : ContDiffOn ℝ ∞ w offOrigin) (hwp : SpatiallyPeriodic w)
    (hglobal : TendstoUniformlyOn v w l (closure multiplierKernelCell))
    (hlocal : ∀ S : Set Vec3, IsCompact S → S ⊆ offOrigin → ∀ d,
      TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (v i)) (iteratedFDeriv ℝ d w) l S) :
    ∃ U : Set Vec3, IsOpen U ∧ K ⊆ U ∧ U ⊆ offOrigin ∧ ∃ p : Vec3 → ℝ,
      ContDiffOn ℝ ∞ p U ∧ ContDiffOn ℝ ∞ (gradient p) U ∧ ∀ d : ℕ,
        TendstoUniformlyOn (fun i => iteratedFDeriv ℝ d (gradient
          (pressureTensorDyadicLift (pressureVelocityTensor (v i)))))
          (iteratedFDeriv ℝ d (gradient p)) l U := by
  obtain ⟨χ, _, _, hχ, hχp, hχB, _, _, _, _, _, _, hsupp, hsep⟩ :=
    exists_periodic_offOrigin_cutoff hK hKo
  obtain ⟨V, hV, hKV, hsepV, hfarLim⟩ := exists_tendstoUniformlyOn_cutoffFarPressureGradient_spatial_derivatives
    hK hχ.continuous hχB hsep hglobal (fun i => (hv i).continuous.continuousOn) hw.continuousOn
  let U := V ∩ offOrigin
  have hU : IsOpen U := hV.inter isOpen_offOrigin
  have hKU : K ⊆ U := fun x hx => ⟨hKV hx, hKo hx⟩
  have hsepU : ∀ x ∈ U, ∀ y ∈ farPressureSourceSet χ, x - y ∈ offOrigin :=
    fun x hx => hsepV x hx.1
  let near (b : Vec3 → Vec3) := pressureTensorDyadicLift (nearPressureCutoffTensor χ b)
  let far (b : Vec3 → Vec3) := periodicFarPressure (farPressureSourceSet χ)
    (farPressureCutoffTensor χ b)
  have hn (b : Vec3 → Vec3) (hb : ContDiffOn ℝ ∞ b offOrigin) (hbp : SpatiallyPeriodic b) :
      ContDiff ℝ ∞ (near b) :=
    contDiff_pressureTensorDyadicLift (contDiff_nearPressureCutoffTensor hχ hsupp hb)
      (spatiallyPeriodic_nearPressureCutoffTensor hχp hbp)
  have hf (b : Vec3 → Vec3) (hb : Continuous b) : ContDiffOn ℝ ∞ (far b) U :=
    contDiffOn_cutoffFarPressure hχ.continuous hb hsepU
  have hP : ContDiffOn ℝ ∞ (near w + far w) U := (hn w hws hwp).contDiffOn.add (hf w hw)
  refine ⟨U, hU, hKU, inter_subset_right, near w + far w, hP, contDiffOn_gradient_of_smooth hU hP,
    fun d => ?_⟩
  have hnearLim := tendstoUniformly_pressureTensorDyadicLift_iteratedFDeriv
    (fun i => contDiff_nearPressureCutoffTensor hχ hsupp (hv i).contDiffOn)
    (contDiff_nearPressureCutoffTensor hχ hsupp hws)
    (fun i => spatiallyPeriodic_nearPressureCutoffTensor hχp (hvp i))
    (spatiallyPeriodic_nearPressureCutoffTensor hχp hwp)
    (tendstoUniformlyOn_nearPressureCutoffTensor hχ hsupp
      (fun i => (hv i).contDiffOn) hws hlocal) (d + 1)
  have hnLim : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (d + 1) (near (v i)))
      (iteratedFDeriv ℝ (d + 1) (near w)) l U := hnearLim.tendstoUniformlyOn
  have hfLim : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (d + 1) (far (v i)))
      (iteratedFDeriv ℝ (d + 1) (far w)) l U := by
    have h := (hfarLim d).mono (show U ⊆ V from inter_subset_left)
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε => ?_
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 h ε hε] with i hi x hx
    specialize hi x hx
    rw [dist_eq_norm, norm_iteratedFDeriv_gradient_sub_eq] at hi
    rwa [dist_eq_norm]
  have hsum (b : Vec3 → Vec3) (hbc : Continuous b) (hb : ContDiffOn ℝ ∞ b offOrigin)
      (hbp : SpatiallyPeriodic b) :
      EqOn (iteratedFDeriv ℝ (d + 1) (near b + far b))
        (iteratedFDeriv ℝ (d + 1) (near b) + iteratedFDeriv ℝ (d + 1) (far b)) U := by
    intro x hx
    rw [iteratedFDeriv_add_apply ((hn b hb hbp).contDiffAt.of_le (by simp))
      (((hf b hbc).contDiffAt (hU.mem_nhds hx)).of_le (by simp)), Pi.add_apply]
  have hpLim : TendstoUniformlyOn (fun i => iteratedFDeriv ℝ (d + 1) (near (v i) + far (v i)))
      (iteratedFDeriv ℝ (d + 1) (near w + far w)) l U :=
    ((hnLim.add hfLim).congr (Eventually.of_forall fun i =>
      (hsum (v i) (hv i).continuous (hv i).contDiffOn (hvp i)).symm)).congr_right (hsum w hw hws hwp).symm
  apply tendstoUniformlyOn_iteratedFDeriv_gradient d
  refine hpLim.congr (Eventually.of_forall fun i x hx => ?_)
  have heq := (eqOn_pressureTensorDyadicLift_cutoff_add_far hχ hχp hsupp (hv i) (hvp i) hsepU
    ).eventuallyEq_of_mem (hU.mem_nhds hx)
  exact ((heq.iteratedFDeriv ℝ (d + 1)).eq_of_nhds).symm

end PressureLimit

section PoissonPressure

open ContinuousLinearMap UnitAddTorus

private def pressureAssemblyTensorEntry (i j : Fin 3) : ComplexPressureTensor →L[ℂ] ℂ :=
  (ContinuousLinearMap.proj j : (Fin 3 → ℂ) →L[ℂ] ℂ).comp
    (ContinuousLinearMap.proj i : ComplexPressureTensor →L[ℂ] (Fin 3 → ℂ))

private def coordinateHessian (f : Vec3 → ℂ) (i j : Fin 3) (x : Vec3) : ℂ :=
  fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) x (EuclideanSpace.single i 1)

private theorem continuous_coordinateHessian {f : Vec3 → ℂ} (hf : ContDiff ℝ 2 f) (i j : Fin 3) :
    Continuous (coordinateHessian f i j) := by
  have hd : ContDiff ℝ 1 (fun y => fderiv ℝ f y (EuclideanSpace.single j 1)) :=
    (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem complexLaplacian_eq_trace_coordinateHessian {f : Vec3 → ℂ}
    (hf : ContDiff ℝ 2 f) (x : Vec3) :
    complexLaplacian f x = ∑ i : Fin 3, coordinateHessian f i i x := by
  have hgrad : ContDiff ℝ 1 (complexGradient f) :=
    contDiff_pi.mpr fun i => (hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  unfold complexLaplacian complexDivergence
  apply Finset.sum_congr rfl
  intro i _
  let P : ComplexVec3 →L[ℝ] ℂ := ContinuousLinearMap.proj i
  have hP : P ∘ complexGradient f = fun y => fderiv ℝ f y (EuclideanSpace.single i 1) := rfl
  unfold coordinateHessian
  rw [← hP, fderiv_comp x P.differentiableAt ((hgrad.differentiable (by simp)) x),
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply]
  rfl

/-- The periodic double divergence of a tensor in complex spatial coordinates. -/
def pressureTensorDoubleDivergence (a : Vec3 → ComplexPressureTensor) (x : Vec3) : ℂ :=
  ∑ i : Fin 3, ∑ j : Fin 3, coordinateHessian (fun y => a y i j) i j x

/-- The physical torus Poisson equation identifies the normalized pressure multiplier.
The physical derivatives are taken in the periodic Euclidean lift. -/
theorem complexPressureTensorMultiplier_eq_of_periodicPoisson
    {a : Vec3 → ComplexPressureTensor} {p : Vec3 → ℂ}
    (ha : ContDiff ℝ 2 a) (hpa : SpatiallyPeriodic a)
    (hp : ContDiff ℝ 2 p) (hpp : SpatiallyPeriodic p)
    (f : HalfHolder (UnitAddTorus (Fin 3)) ComplexPressureTensor)
    (q : C(UnitAddTorus (Fin 3), ℂ))
    (hf : ∀ x : Vec3, HalfHolder.eval (toUnitTorus x) f = a x)
    (hq : ∀ x : Vec3, q (toUnitTorus x) = p x)
    (hmean : (∫ x in centeredCell, p x) = 0)
    (hPoisson : ∀ x : Vec3, complexLaplacian p x = -pressureTensorDoubleDivergence a x) :
    continuousHalfHolder (complexPressureTensorMultiplier f) = q := by
  apply complexPressureTensorMultiplier_eq_of_fourierPoisson f q
  · rw [fourierCoeff_eq_centeredCell]
    simp [fourierMode, mFourier_zero, hq, hmean]
  intro k
  let w := fourierMode (-k)
  have hW : Continuous w := (contDiff_fourierMode (-k)).continuous
  have hc (i j : Fin 3) : ContDiff ℝ 2 (fun y => a y i j) :=
    ((pressureAssemblyTensorEntry i j).restrictScalars ℝ).contDiff.comp ha
  have hpc (i j : Fin 3) : SpatiallyPeriodic (fun y => a y i j) := by
    intro n x
    exact congrArg (fun A : ComplexPressureTensor => A i j) (hpa n x)
  have hInt (i j : Fin 3) : IntegrableOn (fun x =>
      w x * coordinateHessian (fun y => a y i j) i j x) centeredCell :=
    (hW.mul (continuous_coordinateHessian (hc i j) i j)).continuousOn.integrableOn_compact
      isCompact_centeredCell
  have hIntTensor : IntegrableOn (fun x => w x • a x) centeredCell :=
    (hW.smul ha.continuous).continuousOn.integrableOn_compact isCompact_centeredCell
  have hCoeff (i j : Fin 3) :
      mFourierCoeff (continuousHalfHolder f) k i j = ∫ x in centeredCell, w x * a x i j := by
    rw [fourierCoeff_eq_centeredCell]
    simp_rw [show ∀ x, continuousHalfHolder f (toUnitTorus x) = a x from hf]
    let L := pressureAssemblyTensorEntry i j
    change L (∫ x in centeredCell, w x • a x) = _
    rw [← L.integral_comp_comm hIntTensor]
    rfl
  have hpCoeff : mFourierCoeff q k = ∫ x in centeredCell, w x * p x := by
    rw [fourierCoeff_eq_centeredCell]
    simp only [hq, smul_eq_mul]
    rfl
  rw [hpCoeff, ← centeredCell_fourier_laplacian hp hpp k]
  change (∫ x in centeredCell, w x * (∑ i : Fin 3, coordinateHessian p i i x)) = _
  simp_rw [← complexLaplacian_eq_trace_coordinateHessian hp, hPoisson,
    pressureTensorDoubleDivergence, mul_neg, Finset.mul_sum]
  rw [integral_neg, integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hInt i j))]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => hInt i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hCoeff i j]
  exact centeredCell_fourier_coordinate_hessian (hc i j) (hpc i j) k i j


/-- The smooth dyadic pressure is the real part of the normalized periodic Poisson solution. -/
theorem pressureTensorDyadicLift_eq_realPart_of_periodicPoisson
    {a : Vec3 → ComplexPressureTensor} {p : Vec3 → ℂ}
    (ha : ContDiff ℝ ∞ a) (hap : SpatiallyPeriodic a)
    (hp : ContDiff ℝ 2 p) (hpp : SpatiallyPeriodic p)
    (hmean : (∫ x in centeredCell, p x) = 0)
    (hPoisson : ∀ x : Vec3, complexLaplacian p x = -pressureTensorDoubleDivergence a x) :
    pressureTensorDyadicLift a = fun x => (p x).re := by
  obtain ⟨f, hf, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hap
    (spatialHolderHalf_of_contDiff_periodic ha hap 0)
  obtain ⟨q, hq⟩ := hpp.exists_continuousTorusFunction hp.continuous
  have heq := complexPressureTensorMultiplier_eq_of_periodicPoisson (ha.of_le (by simp))
    hap hp hpp f q hf hq hmean hPoisson
  rw [pressureTensorDyadicLift_eq_lift_pressureTensorMultiplier ha hap f hf]
  funext x
  unfold pressureTensorMultiplier
  rw [ContinuousLinearMap.comp_apply, HalfHolder.eval_map]
  change (continuousHalfHolder (complexPressureTensorMultiplier f) (toUnitTorus x)).re = _
  rw [heq, hq]

set_option maxHeartbeats 800000 in
/-- The normalized periodic pressure gradients have all compact off-origin
terminal limits from the global velocity limit and the local spatial jet limits. -/
theorem hasOffOriginLimits_normalizedPressureGradient_of_velocity_jets
    {T : ℝ} {u : Velocity} {w : Vec3 → Vec3} {p : ℝ → Vec3 → ℂ}
    (hu : ∀ t ∈ Ico 0 T, ContDiff ℝ ∞ (u t) ∧ SpatiallyPeriodic (u t))
    (hp : ∀ t ∈ Ico 0 T, ContDiff ℝ 2 (p t) ∧ SpatiallyPeriodic (p t) ∧
      (∫ x in centeredCell, p t x) = 0 ∧
      ∀ x : Vec3, complexLaplacian (p t) x = -pressureTensorDoubleDivergence (pressureVelocityTensor (u t)) x)
    (hw : Continuous w) (hws : ContDiffOn ℝ ∞ w offOrigin) (hwp : SpatiallyPeriodic w)
    (hglobal : TendstoUniformlyOn u w (𝓝[Ico 0 T] T) (closure multiplierKernelCell))
    (hlocal : ∀ S : Set Vec3, IsCompact S → S ⊆ offOrigin → ∀ d,
      TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (u t)) (iteratedFDeriv ℝ d w)
        (𝓝[Ico 0 T] T) S) :
    HasOffOriginLimits T (fun t => gradient (fun x => (p t x).re)) := by
  intro K hK hKo m
  let v (t : ℝ) : Vec3 → Vec3 := if t ∈ Ico 0 T then u t else 0
  have hv (t : ℝ) : ContDiff ℝ ∞ (v t) ∧ SpatiallyPeriodic (v t) := by
    by_cases ht : t ∈ Ico 0 T
    · simpa only [v, ite_eq_left ht] using hu t ht
    · simp only [v, ite_eq_right ht]
      exact ⟨contDiff_const (c := (0 : Vec3)), fun _ _ => rfl⟩
  have hv_eq : ∀ᶠ t in 𝓝[Ico 0 T] T, v t = u t := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ite_eq_left ht
  have hglob : TendstoUniformlyOn v w (𝓝[Ico 0 T] T) (closure multiplierKernelCell) :=
    hglobal.congr (hv_eq.mono fun t ht x _ => congrFun ht.symm x)
  have hloc (S : Set Vec3) (hS : IsCompact S) (hSo : S ⊆ offOrigin) (d : ℕ) :
      TendstoUniformlyOn (fun t => iteratedFDeriv ℝ d (v t)) (iteratedFDeriv ℝ d w)
        (𝓝[Ico 0 T] T) S :=
    (hlocal S hS hSo d).congr (hv_eq.mono fun t ht x _ =>
      congrArg (fun f : Vec3 → Vec3 => iteratedFDeriv ℝ d f x) ht.symm)
  obtain ⟨U, hU, hKU, hUo, q, _, hq, hlim⟩ :=
    exists_tendstoUniformlyOn_pressureGradient_of_velocity_jets hK hKo
      (fun t => (hv t).1) (fun t => (hv t).2) hw hws hwp hglob hloc
  refine ⟨U, gradient q, hU, hKU, hUo, hq.of_le (by simp), fun d _ => ?_⟩
  apply ((hlim d).mono hKU).congr
  filter_upwards [self_mem_nhdsWithin, hv_eq] with t ht hvt
  have hP := hp t ht
  have heq : pressureTensorDyadicLift (pressureVelocityTensor (u t)) = fun x => (p t x).re :=
    pressureTensorDyadicLift_eq_realPart_of_periodicPoisson
      ((velocityPressureTensor.contDiff.comp (hu t ht).1).clm_apply (hu t ht).1)
      (spatiallyPeriodic_pressureVelocityTensor (hu t ht).2) hP.1 hP.2.1 hP.2.2.1 hP.2.2.2
  intro x _
  rw [hvt, heq]

end PoissonPressure

end
end TorusEuler

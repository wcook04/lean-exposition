import TorusEuler.EulerAdvectionBounds
import TorusEuler.IntegratedLimit
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Topology.Algebra.IsUniformGroup.Basic

/-! The limit equations and velocity symmetries in Proposition 8.1. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

/-- Periodicity and oddness pass to pointwise limits on the lift. -/
theorem periodic_odd_of_pointwise_limit {U : ℕ → Vec3 → Vec3} {u : Vec3 → Vec3}
    (hU : ∀ x, Tendsto (fun j => U j x) atTop (𝓝 (u x)))
    (hPer : ∀ j, SpatiallyPeriodic (U j)) (hOdd : ∀ j, Function.Odd (U j)) :
    SpatiallyPeriodic u ∧ Function.Odd u := by
  constructor
  · intro n x
    exact tendsto_nhds_unique_of_eventuallyEq (hU (x + latticeVector n)) (hU x)
      (Eventually.of_forall fun j => hPer j n x)
  · intro x
    exact tendsto_nhds_unique_of_eventuallyEq (hU (-x)) (hU x).neg
      (Eventually.of_forall fun j => hOdd j x)

/-- The divergence is a continuous linear contraction of the spatial derivative. -/
theorem divergence_eq_zero_of_tendsto_fderiv {U : ℕ → Vec3 → Vec3} {u : Vec3 → Vec3} {x : Vec3}
    (hD : Tendsto (fun j => fderiv ℝ (U j) x) atTop (𝓝 (fderiv ℝ u x)))
    (hDiv : ∀ j, divergence (U j) x = 0) : divergence u x = 0 := by
  have hCoord (i : Fin 3) : Tendsto
      (fun j => (fderiv ℝ (U j) x (EuclideanSpace.single i 1)) i) atTop
      (𝓝 ((fderiv ℝ u x (EuclideanSpace.single i 1)) i)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).comp
      (ContinuousLinearMap.apply ℝ Vec3 (EuclideanSpace.single i 1)).continuous).continuousAt.tendsto.comp hD
  exact tendsto_nhds_unique_of_eventuallyEq (tendsto_finsetSum Finset.univ (fun i _ => hCoord i))
    tendsto_const_nhds (Eventually.of_forall hDiv)

/-- A joint velocity derivative restricts to the ambient spatial derivative on a time slice. -/
theorem contDiffOn_spatialDerivative_of_joint_contDiff {I : Set ℝ} {u : Velocity} {n : WithTop ℕ∞}
    (hI : UniqueDiffOn ℝ I) (hu : ContDiffOn ℝ (n + 1) (Function.uncurry u) (I ×ˢ univ)) :
    ContDiffOn ℝ n (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) (I ×ˢ univ) := by
  let D := fderivWithin ℝ (Function.uncurry u) (I ×ˢ univ)
  let C := (compL ℝ Vec3 (ℝ × Vec3) Vec3).flip (inr ℝ ℝ Vec3)
  have hD : ContDiffOn ℝ n D (I ×ˢ univ) :=
    hu.fderivWithin (hI.prod uniqueDiffOn_univ) le_rfl
  apply (C.contDiff.comp_contDiffOn hD).congr
  rintro ⟨t, x⟩ ht
  have h := (hu.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt.comp_hasFDerivAt x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x)
    (Eventually.of_forall fun y => mem_prod.mpr ⟨ht.1, mem_univ y⟩)
  exact h.fderiv

/-- A joint velocity derivative restricts to the within-slab partial time derivative. -/
theorem contDiffOn_timeDerivative_of_joint_contDiff {T : ℝ} {u : Velocity} {n : WithTop ℕ∞}
    (hu : ContDiffOn ℝ (n + 1) (Function.uncurry u) (Ico 0 T ×ˢ univ)) :
    ContDiffOn ℝ n (Function.uncurry (timeDerivative T u)) (Ico 0 T ×ˢ univ) := by
  let I := Ico (0 : ℝ) T
  let D := fderivWithin ℝ (Function.uncurry u) (I ×ˢ univ)
  let C := ContinuousLinearMap.apply ℝ Vec3 ((1, 0) : ℝ × Vec3)
  have hI := uniqueDiffOn_Ico (0 : ℝ) T
  have hD : ContDiffOn ℝ n D (I ×ˢ univ) := hu.fderivWithin (hI.prod uniqueDiffOn_univ) le_rfl
  apply (C.contDiff.comp_contDiffOn hD).congr
  rintro ⟨t, x⟩ ht
  have h := (hu.differentiableOn (by simp) (t, x) ht).hasFDerivWithinAt.comp_hasDerivWithinAt t
    ((hasDerivWithinAt_id t I).prodMk (hasDerivWithinAt_const t I x))
    (fun r hr => mem_prod.mpr ⟨hr, mem_univ x⟩)
  exact h.derivWithin (hI t ht.1)

/-- The limit momentum equation on a compact prefix. The supplied approximate momentum
equation uses the within-time derivative and includes the residual with its original sign. -/
theorem hasDerivWithinAt_eulerMomentum_of_uniformLimits
    {S : ℝ} (hS : 0 ≤ S) {x : Vec3} {U R : ℕ → Velocity} {P : ℕ → Pressure}
    {u g : Velocity}
    (hU : TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hDU : TendstoUniformlyOn (fun j z => fderiv ℝ (U j z.1) z.2)
      (fun z => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hG : TendstoUniformlyOn (fun j z => gradient (P j z.1) z.2) (Function.uncurry g)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (R j)) (fun _ => 0)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hUc : ∀ j, ContinuousOn (fun r => U j r x) (Icc 0 S))
    (hDUc : ∀ j, ContinuousOn (fun r => fderiv ℝ (U j r) x) (Icc 0 S))
    (hGc : ∀ j, ContinuousOn (fun r => gradient (P j r) x) (Icc 0 S))
    (hRc : ∀ j, ContinuousOn (fun r => R j r x) (Icc 0 S))
    (hEq : ∀ j r, r ∈ Icc 0 S → HasDerivWithinAt (fun s => U j s x)
      (R j r x - (fderiv ℝ (U j r) x (U j r x) + gradient (P j r) x)) (Icc 0 S) r) :
    ∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => u r x)
      (-(fderiv ℝ (u t) x (u t x) + g t x)) (Icc 0 S) t := by
  let I := Icc (0 : ℝ) S
  let adv (j : ℕ) (r : ℝ) := fderiv ℝ (U j r) x (U j r x)
  let D (j : ℕ) (r : ℝ) := adv j r + gradient (P j r) x
  let d (r : ℝ) := fderiv ℝ (u r) x (u r x) + g r x
  have hmaps : I ⊆ (fun r => (r, x)) ⁻¹' (I ×ˢ (univ : Set Vec3)) :=
    fun r hr => mem_prod.mpr ⟨hr, mem_univ x⟩
  have hUt := (hU.comp (fun r => (r, x))).mono hmaps
  have hDUt := (hDU.comp (fun r => (r, x))).mono hmaps
  have hGt := (hG.comp (fun r => (r, x))).mono hmaps
  have hRt := (hR.comp (fun r => (r, x))).mono hmaps
  have huc := hUt.continuousOn (Frequently.of_forall hUc)
  have hduc := hDUt.continuousOn (Frequently.of_forall hDUc)
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hduc
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn huc
  have hAdvection := tendstoUniformlyOn_clm_apply_of_bounded hDUt hUt
    (le_max_right C 0) (le_max_right M 0)
    (fun r hr => (hC r hr).trans (le_max_left _ _))
    (fun r hr => (hM r hr).trans (le_max_left _ _))
  have hD : TendstoUniformlyOn D d atTop I := hAdvection.add hGt
  have hDc (j : ℕ) : ContinuousOn (D j) I :=
    ((hDUc j).clm_apply (hUc j)).add (hGc j)
  have hInt (j : ℕ) (t : ℝ) (ht : t ∈ I) :
      U j t x = U j 0 x - (∫ r in (0 : ℝ)..t, D j r) + ∫ r in (0 : ℝ)..t, R j r x := by
    have hsub : Icc (0 : ℝ) t ⊆ I := Icc_subset_Icc_right ht.2
    have hDint := ((hDc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hRint := ((hRc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 ((hUc j).mono hsub)
      (fun r hr => (hEq j r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds hr.1 (hr.2.trans_le ht.2)) Ioo_subset_Icc_self))
      (hRint.sub hDint)
    rw [intervalIntegral.integral_sub hRint hDint] at hFTC
    calc
      U j t x = U j 0 x + (U j t x - U j 0 x) := by abel
      _ = _ := by rw [← hFTC]; abel
  exact (integratedLimit_of_uniformConvergence hS hUt hD hRt hDc hRc hInt).2

/-- The half-open time derivative is identified by its values on earlier closed prefixes. -/
theorem timeDerivative_eq_of_prefix_dynamics {T : ℝ} {u d : Velocity}
    (hdynamics : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x) (d t x) (Icc 0 S) t) :
    ∀ t ∈ Ico 0 T, ∀ x, timeDerivative T u t x = d t x := by
  intro t ht x
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hneighborhood : Icc 0 S ∈ 𝓝[Ico 0 T] t := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds htS)]
      with r hr hrS
    exact ⟨hr.1, (show r < S from hrS).le⟩
  have hderiv := (hdynamics S hST t ⟨ht.1, htS.le⟩ x).mono_of_mem_nhdsWithin hneighborhood
  exact hderiv.derivWithin (uniqueDiffOn_Ico _ _ t ht)

/-- The momentum equation on the half-open solution interval. -/
theorem eulerMomentum_of_prefix_dynamics {T : ℝ} {u : Velocity} {p : Pressure}
    (hdynamics : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x)
        (-(fderiv ℝ (u t) x (u t x) + gradient (p t) x)) (Icc 0 S) t) :
    ∀ t ∈ Ico 0 T, ∀ x, timeDerivative T u t x +
      fderiv ℝ (u t) x (u t x) + gradient (p t) x = 0 := by
  intro t ht x
  rw [timeDerivative_eq_of_prefix_dynamics hdynamics t ht x]
  abel

/-- Assembly of the actual Euler solution predicate from the preterminal estimates.
Joint smoothness of the velocity and normalized pressure is supplied. -/
theorem isEulerSolution_of_prefix_limits {T : ℝ} {u : Velocity} {p : Pressure}
    {U : ℕ → Velocity} (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)))
    (hp : ContDiffOn ℝ ∞ (Function.uncurry p) (Ico 0 T ×ˢ (univ : Set Vec3)))
    (hpPer : ∀ t ∈ Ico 0 T, SpatiallyPeriodic (p t))
    (hpMean : ∀ t ∈ Ico 0 T, (∫ x in centeredCell, p t x) = 0)
    (hPer : ∀ j t, t ∈ Ico 0 T → SpatiallyPeriodic (U j t))
    (hOdd : ∀ j t, t ∈ Ico 0 T → Function.Odd (U j t))
    (hDiv : ∀ j t, t ∈ Ico 0 T → ∀ x, divergence (U j t) x = 0)
    (hU : ∀ S < T, TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hDU : ∀ S < T, TendstoUniformlyOn (fun j z => fderiv ℝ (U j z.1) z.2)
      (fun z => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hdynamics : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x)
        (-(fderiv ℝ (u t) x (u t x) + gradient (p t) x)) (Icc 0 S) t) :
    IsEulerSolution T u p ∧ ∀ t ∈ Ico 0 T, Function.Odd (u t) := by
  have hsym (t : ℝ) (ht : t ∈ Ico 0 T) : SpatiallyPeriodic (u t) ∧ Function.Odd (u t) :=
    periodic_odd_of_pointwise_limit
      (fun x => (hU t ht.2).tendsto_at (x := (t, x)) (mem_prod.mpr ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩))
      (fun j => hPer j t ht) (fun j => hOdd j t ht)
  refine ⟨⟨hT, hu, hp, fun t ht => (hsym t ht).1, hpPer, hpMean,
    eulerMomentum_of_prefix_dynamics hdynamics, ?_⟩, fun t ht => (hsym t ht).2⟩
  intro t ht x
  exact divergence_eq_zero_of_tendsto_fderiv
    ((hDU t ht.2).tendsto_at (x := (t, x)) (mem_prod.mpr ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩))
    (fun j => hDiv j t ht x)

/-- A scalar pressure is recovered, up to its value at zero, by the radial line integral
of its actual spatial gradient. -/
theorem pressure_sub_at_zero_eq_lineIntegral {p : Vec3 → ℝ} {g : Vec3 → Vec3}
    (hP : ∀ x, HasGradientAt p (g x) x) (hg : Continuous g) (x : Vec3) :
    p x - p 0 = ∫ s in (0 : ℝ)..1, ⟪g (s • x), x⟫_ℝ := by
  have hD (s : ℝ) : HasDerivAt (fun r : ℝ => p (r • x)) ⟪g (s • x), x⟫_ℝ s := by
    have hs : HasDerivAt (fun r : ℝ => r • x) x s :=
      (hasDerivAt_id s).smul_const x |>.congr_deriv (one_smul ℝ x)
    exact (hP (s • x)).hasFDerivAt.comp_hasDerivAt s hs
  have hcont : Continuous (fun s : ℝ => ⟪g (s • x), x⟫_ℝ) :=
    (hg.comp (continuous_id.smul continuous_const)).inner continuous_const
  simpa only [one_smul, zero_smul] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hD s)
      (hcont.intervalIntegrable 0 1)).symm

section CompactIntegral

universe u

variable {E F : Type u} {A : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup A] [NormedSpace ℝ A] [MeasurableSpace A] [BorelSpace A]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {μ : Measure A} [IsLocallyFiniteMeasure μ]
  {s : Set E} {K : Set A}

omit [NormedSpace ℝ A] in
private theorem hasFDerivWithinAt_setIntegral_compact {f : E × A → F}
    {d : E × A → E →L[ℝ] F} (hs : Convex ℝ s) (hsClosed : IsClosed s) (hK : IsCompact K)
    (hf : ContinuousOn f (s ×ˢ K)) (hd : ContinuousOn d (s ×ˢ K))
    (hD : ∀ x ∈ s, ∀ a ∈ K, HasFDerivWithinAt (fun y => f (y, a)) (d (x, a)) s x)
    {x : E} (hx : x ∈ s) :
    HasFDerivWithinAt (fun y => ∫ a in K, f (y, a) ∂μ) (∫ a in K, d (x, a) ∂μ) s x := by
  have hfInt (y : E) (hy : y ∈ s) : IntegrableOn (fun a => f (y, a)) K μ :=
    ContinuousOn.integrableOn_compact hK
      (hf.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun a ha => mem_prod.mpr ⟨hy, ha⟩))
  have hdInt : IntegrableOn (fun a => d (x, a)) K μ :=
    ContinuousOn.integrableOn_compact hK
      (hd.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun a ha => mem_prod.mpr ⟨hx, ha⟩))
  let B := s ∩ Metric.closedBall x 1
  have hB : IsCompact B := (isCompact_closedBall x 1).inter_left hsClosed
  have hdx := (hB.prod hK).uniformContinuousOn_of_continuous
    (hd.mono (prod_mono_left (inter_subset_left : B ⊆ s)))
  rw [hasFDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  let c := ε / (μ.real K + 1)
  have hpos : 0 < μ.real K + 1 := add_pos_of_nonneg_of_pos measureReal_nonneg zero_lt_one
  have hc : 0 < c := div_pos hε hpos
  obtain ⟨δ, hδ, hclose⟩ := Metric.uniformContinuousOn_iff.mp hdx c hc
  let r := min 1 (δ / 2)
  have hr : 0 < r := lt_min zero_lt_one (half_pos hδ)
  have hr₁ : r ≤ 1 := min_le_left _ _
  have hrδ : r < δ := (min_le_right _ _).trans_lt (half_lt_self hδ)
  let B' := s ∩ Metric.closedBall x r
  have hconv : Convex ℝ B' := hs.inter (convex_closedBall x r)
  have hxB' : x ∈ B' := ⟨hx, Metric.mem_closedBall_self hr.le⟩
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x hr)] with y hy hyball
  have hyB' : y ∈ B' := ⟨hy, Metric.ball_subset_closedBall hyball⟩
  have hBound (a : A) (ha : a ∈ K) :
      ‖f (y, a) - f (x, a) - d (x, a) (y - x)‖ ≤ c * ‖y - x‖ := by
    have hNorm (z : E) (hz : z ∈ B') : ‖d (z, a) - d (x, a)‖ ≤ c := by
      have hzB : z ∈ B := ⟨hz.1, Metric.closedBall_subset_closedBall hr₁ hz.2⟩
      have hxB : x ∈ B := ⟨hx, Metric.mem_closedBall_self zero_le_one⟩
      have hdist : dist (z, a) (x, a) < δ := by
        rw [dist_prod_same_right]
        exact (Metric.mem_closedBall.mp hz.2).trans_lt hrδ
      have hlt := hclose (z, a) (mem_prod.mpr ⟨hzB, ha⟩) (x, a) (mem_prod.mpr ⟨hxB, ha⟩) hdist
      rw [dist_eq_norm] at hlt
      exact hlt.le
    have hEstimate := hconv.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (((hD z hz.1 a ha).sub (d (x, a)).hasFDerivAt.hasFDerivWithinAt).mono
        (inter_subset_left : B' ⊆ s))) hNorm hxB' hyB'
    change ‖(f (y, a) - d (x, a) y) - (f (x, a) - d (x, a) x)‖ ≤ c * ‖y - x‖ at hEstimate
    rwa [sub_sub_sub_comm, ← map_sub] at hEstimate
  have hApp := (ContinuousLinearMap.apply ℝ F (y - x)).integral_comp_comm hdInt
  have hAppInt : IntegrableOn (fun a => d (x, a) (y - x)) K μ :=
    (ContinuousLinearMap.apply ℝ F (y - x)).integrable_comp hdInt
  change (∫ a in K, d (x, a) (y - x) ∂μ) = (∫ a in K, d (x, a) ∂μ) (y - x) at hApp
  have hSubInt : IntegrableOn (fun a => f (y, a) - f (x, a)) K μ :=
    (hfInt y hy).sub (hfInt x hx)
  rw [← hApp, ← integral_sub (hfInt y hy) (hfInt x hx), ← integral_sub hSubInt hAppInt]
  have hcμ : c * μ.real K ≤ ε := by
    calc
      c * μ.real K ≤ c * (μ.real K + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) hc.le
      _ = ε := div_mul_cancel₀ _ hpos.ne'
  calc
    _ ≤ (c * ‖y - x‖) * μ.real K := norm_setIntegral_le_of_norm_le_const hK.measure_lt_top hBound
    _ = (c * μ.real K) * ‖y - x‖ := by ring
    _ ≤ ε * ‖y - x‖ := mul_le_mul_of_nonneg_right hcμ (norm_nonneg _)

private theorem hasFDerivWithinAt_setIntegral_of_contDiffOn {f : E × A → F}
    (hs : Convex ℝ s) (hsClosed : IsClosed s) (hUnique : UniqueDiffOn ℝ s) (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ univ)) {x : E} (hx : x ∈ s) :
    let C := (compL ℝ E (E × A) F).flip (inl ℝ E A)
    HasFDerivWithinAt (fun y => ∫ a in K, f (y, a) ∂μ)
      (∫ a in K, C (fderivWithin ℝ f (s ×ˢ univ) (x, a)) ∂μ) s x := by
  let C := (compL ℝ E (E × A) F).flip (inl ℝ E A)
  change HasFDerivWithinAt (fun y => ∫ a in K, f (y, a) ∂μ)
    (∫ a in K, C (fderivWithin ℝ f (s ×ˢ univ) (x, a)) ∂μ) s x
  have hs' : UniqueDiffOn ℝ (s ×ˢ (univ : Set A)) := hUnique.prod uniqueDiffOn_univ
  have hsub : s ×ˢ K ⊆ s ×ˢ (univ : Set A) := prod_mono_right (subset_univ _)
  refine hasFDerivWithinAt_setIntegral_compact (μ := μ)
    (d := fun z => C (fderivWithin ℝ f (s ×ˢ univ) z)) hs hsClosed hK
      (hf.continuousOn.mono hsub) ?_ ?_ hx
  · exact C.continuous.comp_continuousOn ((hf.continuousOn_fderivWithin hs' (by simp)).mono hsub)
  · intro y hy a _
    have h := (hf.differentiableOn (by simp) (y, a) ⟨hy, mem_univ a⟩).hasFDerivWithinAt
    exact h.comp y (hasFDerivAt_prodMk_left (𝕜 := ℝ) y a).hasFDerivWithinAt
      (fun z hz => mem_prod.mpr ⟨hz, mem_univ a⟩)

private theorem contDiffOn_setIntegral_compact (m : ℕ) {f : E × A → F}
    (hs : Convex ℝ s) (hsClosed : IsClosed s) (hUnique : UniqueDiffOn ℝ s) (hK : IsCompact K)
    (hf : ContDiffOn ℝ ∞ f (s ×ˢ univ)) :
    ContDiffOn ℝ m (fun x => ∫ a in K, f (x, a) ∂μ) s := by
  induction m generalizing F with
  | zero =>
    rw [Nat.cast_zero, contDiffOn_zero]
    exact fun x hx => (hasFDerivWithinAt_setIntegral_of_contDiffOn
      (μ := μ) hs hsClosed hUnique hK hf hx).continuousWithinAt
  | succ m ih =>
    let C := (compL ℝ E (E × A) F).flip (inl ℝ E A)
    let d : E × A → E →L[ℝ] F := fun z => C (fderivWithin ℝ f (s ×ˢ univ) z)
    have hd : ContDiffOn ℝ ∞ d (s ×ˢ univ) := C.contDiff.comp_contDiffOn
      (hf.fderivWithin (hUnique.prod uniqueDiffOn_univ) (by simp))
    rw [Nat.cast_succ, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn hUnique]
    refine ⟨by simp, fun x => ∫ a in K, d (x, a) ∂μ, ih hd, ?_⟩
    exact fun x hx => hasFDerivWithinAt_setIntegral_of_contDiffOn hs hsClosed hUnique hK hf hx

end CompactIntegral

/-- The mean-zero pressure is jointly smooth when its actual gradient is jointly smooth
on the half-open time slab. Both integrals in the normalized line formula are over fixed
compact sets, so the argument applies at the initial time as well. -/
theorem contDiffOn_pressure_of_joint_contDiff_gradient {T : ℝ} {p : Pressure} {g : Velocity}
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Ico 0 T ×ˢ (univ : Set Vec3)))
    (hP : ∀ t ∈ Ico 0 T, ∀ x, HasGradientAt (p t) (g t x) x)
    (hMean : ∀ t ∈ Ico 0 T, (∫ x in centeredCell, p t x) = 0) :
    ContDiffOn ℝ ∞ (Function.uncurry p) (Ico 0 T ×ˢ (univ : Set Vec3)) := by
  let F : (ℝ × Vec3) × ℝ → ℝ := fun z => ⟪g z.1.1 (z.2 • z.1.2), z.1.2⟫_ℝ
  let q (t : ℝ) (x : Vec3) := ∫ r in Icc (0 : ℝ) 1, F ((t, x), r)
  let V := (volume : Measure Vec3).real centeredCell
  have hV : V ≠ 0 := by
    have hcell : centeredCell ∈ 𝓝 (0 : Vec3) := by
      apply mem_of_superset (Metric.ball_mem_nhds (0 : Vec3) (show 0 < 1 / 2 by norm_num))
      intro x hx i
      have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
    exact (ENNReal.toReal_pos (Measure.measure_pos_of_mem_nhds volume hcell).ne'
      isCompact_centeredCell.measure_ne_top).ne'
  have hq (t : ℝ) (ht : t ∈ Ico 0 T) (x : Vec3) : q t x = p t x - p t 0 := by
    have hgt : Continuous (g t) := by
      rw [← continuousOn_univ]
      exact hg.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun y _ => mem_prod.mpr ⟨ht, mem_univ y⟩)
    have hline := pressure_sub_at_zero_eq_lineIntegral (hP t ht) hgt x
    rw [intervalIntegral.integral_of_le zero_le_one, ← integral_Icc_eq_integral_Ioc] at hline
    exact hline.symm
  have hFormula (t : ℝ) (ht : t ∈ Ico 0 T) (x : Vec3) :
      p t x = q t x - (∫ y in centeredCell, q t y) / V := by
    have hpCont : Continuous (p t) := continuous_iff_continuousAt.mpr
      (fun y => (hP t ht y).differentiableAt.continuousAt)
    have hpInt : IntegrableOn (p t) centeredCell :=
      ContinuousOn.integrableOn_compact isCompact_centeredCell hpCont.continuousOn
    have hconst : IntegrableOn (fun _ : Vec3 => p t 0) centeredCell :=
      integrableOn_const isCompact_centeredCell.measure_ne_top
    have hqMean : (∫ y in centeredCell, q t y) = -(V * p t 0) := by
      rw [setIntegral_congr_fun isCompact_centeredCell.measurableSet (fun y _ => hq t ht y),
        integral_sub hpInt hconst, hMean t ht, setIntegral_const, smul_eq_mul, zero_sub]
    rw [hq t ht x, hqMean, neg_div, mul_comm V _, mul_div_cancel_right₀ _ hV]
    abel
  have hPrefix (S : ℝ) (hS : 0 < S) (hST : S < T) :
      ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 S ×ˢ (univ : Set Vec3)) := by
    let B := Icc (0 : ℝ) S ×ˢ (univ : Set Vec3)
    have hTime : Icc 0 S ⊆ Ico 0 T := fun t ht => ⟨ht.1, ht.2.trans_lt hST⟩
    have hF : ContDiffOn ℝ ∞ F (B ×ˢ univ) := by
      have hmap : ContDiff ℝ ∞ (fun z : (ℝ × Vec3) × ℝ => (z.1.1, z.2 • z.1.2)) := by fun_prop
      have hG : ContDiffOn ℝ ∞ (fun z : (ℝ × Vec3) × ℝ => g z.1.1 (z.2 • z.1.2))
          (B ×ˢ univ) :=
        hg.comp hmap.contDiffOn (fun z hz => mem_prod.mpr ⟨hTime hz.1.1, mem_univ _⟩)
      exact hG.inner ℝ (by fun_prop)
    have hqDiff : ContDiffOn ℝ ∞ (Function.uncurry q) B := contDiffOn_infty.mpr fun m =>
      contDiffOn_setIntegral_compact (μ := volume) m
        ((convex_Icc 0 S).prod (show Convex ℝ (univ : Set Vec3) from convex_univ))
        (isClosed_Icc.prod isClosed_univ) ((uniqueDiffOn_Icc hS).prod uniqueDiffOn_univ)
        isCompact_Icc hF
    have hmDiff : ContDiffOn ℝ ∞ (fun t => ∫ y in centeredCell, q t y) (Icc 0 S) :=
      contDiffOn_infty.mpr fun m =>
        contDiffOn_setIntegral_compact (μ := volume) m (convex_Icc 0 S) isClosed_Icc
          (uniqueDiffOn_Icc hS) isCompact_centeredCell hqDiff
    have hcDiff : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (∫ y in centeredCell, q z.1 y) / V) B := by
      have hm : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => ∫ y in centeredCell, q z.1 y) B :=
        hmDiff.comp contDiff_fst.contDiffOn (fun z hz => hz.1)
      exact hm.div_const V
    exact (hqDiff.sub hcDiff).congr (fun z hz => hFormula z.1 (hTime hz.1) z.2)
  intro z hz
  obtain ⟨S, hzS, hST⟩ := exists_between hz.1.2
  have hlt : (fun w : ℝ × Vec3 => w.1) ⁻¹' Iio S ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hzS)
  have hnbh : Icc 0 S ×ˢ (univ : Set Vec3) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set Vec3)] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlt] with w hw hws
    exact ⟨⟨hw.1.1, (show w.1 < S from hws).le⟩, hw.2⟩
  exact (hPrefix S (hz.1.1.trans_lt hzS) hST z ⟨⟨hz.1.1, hzS.le⟩, hz.2⟩)
    |>.mono_of_mem_nhdsWithin hnbh

/-- Once the limit velocity is jointly smooth, the checked momentum limit identifies a
smooth pressure gradient. Uniform convergence of periodic pressure gradients then gives
an actual jointly smooth, mean-zero pressure for the Euler solution. -/
theorem exists_isEulerSolution_of_prefix_gradient_limits {T : ℝ} {u g : Velocity}
    {U : ℕ → Velocity} {P : ℕ → Pressure} (hT : 0 < T)
    (hu : ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)))
    (hPer : ∀ j t, t ∈ Ico 0 T → SpatiallyPeriodic (U j t))
    (hOdd : ∀ j t, t ∈ Ico 0 T → Function.Odd (U j t))
    (hDiv : ∀ j t, t ∈ Ico 0 T → ∀ x, divergence (U j t) x = 0)
    (hPd : ∀ j t, t ∈ Ico 0 T → Differentiable ℝ (P j t))
    (hPPer : ∀ j t, t ∈ Ico 0 T → SpatiallyPeriodic (P j t))
    (hU : ∀ S < T, TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hDU : ∀ S < T, TendstoUniformlyOn (fun j z => fderiv ℝ (U j z.1) z.2)
      (fun z => fderiv ℝ (u z.1) z.2) atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hG : ∀ S < T, TendstoUniformlyOn (fun j z => gradient (P j z.1) z.2) (Function.uncurry g)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hdynamics : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x)
        (-(fderiv ℝ (u t) x (u t x) + g t x)) (Icc 0 S) t) :
    ∃ p : Pressure, IsEulerSolution T u p ∧ (∀ t ∈ Ico 0 T, Function.Odd (u t)) ∧
      ∀ t ∈ Ico 0 T, ∀ x, HasGradientAt (p t) (g t x) x := by
  let I := Ico (0 : ℝ) T
  have hSlices (t : ℝ) : ∃ p : Vec3 → ℝ, t ∈ I →
      SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧ ∀ x, HasGradientAt p (g t x) x := by
    by_cases ht : t ∈ I
    · have hslice : TendstoUniformly (fun j => gradient (P j t)) (g t) atTop := by
        rw [← tendstoUniformlyOn_univ]
        exact ((hG t ht.2).comp (fun x : Vec3 => (t, x))).mono
          (fun x _ => mem_prod.mpr ⟨⟨ht.1, le_rfl⟩, mem_univ x⟩)
      obtain ⟨p, hp⟩ := exists_periodic_meanZero_pressure_of_uniform_gradient
        (fun j => hPd j t ht) (fun j => hPPer j t ht) hslice
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun h => (ht h).elim⟩
  choose p hp using hSlices
  have htime := timeDerivative_eq_of_prefix_dynamics hdynamics
  have hSpatial : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (u z.1) z.2) (I ×ˢ univ) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Ico 0 T) (by simpa using hu)
  have hTimeDiff : ContDiffOn ℝ ∞ (Function.uncurry (timeDerivative T u)) (I ×ˢ univ) :=
    contDiffOn_timeDerivative_of_joint_contDiff (by simpa using hu)
  have hGDiff : ContDiffOn ℝ ∞ (Function.uncurry g) (I ×ˢ univ) := by
    apply ((hTimeDiff.add (hSpatial.clm_apply hu)).neg).congr
    rintro ⟨t, x⟩ hx
    change g t x = -(timeDerivative T u t x + fderiv ℝ (u t) x (u t x))
    rw [htime t hx.1 x]
    abel
  have hpDiff := contDiffOn_pressure_of_joint_contDiff_gradient hGDiff
    (fun t ht => (hp t ht).2.2) (fun t ht => (hp t ht).2.1)
  have hd : ∀ S < T, ∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x)
        (-(fderiv ℝ (u t) x (u t x) + gradient (p t) x)) (Icc 0 S) t := by
    intro S hST t ht x
    have ht' : t ∈ I := ⟨ht.1, ht.2.trans_lt hST⟩
    rw [((hp t ht').2.2 x).gradient]
    exact hdynamics S hST t ht x
  obtain ⟨hEuler, huOdd⟩ := isEulerSolution_of_prefix_limits hT hu hpDiff
    (fun t ht => (hp t ht).1) (fun t ht => (hp t ht).2.1) hPer hOdd hDiv hU hDU hd
  exact ⟨p, hEuler, huOdd, fun t ht => (hp t ht).2.2⟩

end TorusEuler

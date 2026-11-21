import TorusEuler.PeriodicLift
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Topology.UniformSpace.UniformApproximation

/-! Advection convergence and periodic pressure reconstruction for §8.1. -/

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler

section Advection

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The product estimate for the action of a velocity gradient on a velocity. -/
theorem norm_clm_apply_sub_le (A B : E →L[ℝ] F) (v w : E) :
    ‖A v - B w‖ ≤ ‖A - B‖ * ‖v‖ + ‖B‖ * ‖v - w‖ := by
  have h : A v - B w = (A - B) v + B (v - w) := by
    simp only [sub_apply, map_sub]
    abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add ((A - B).le_opNorm v) (B.le_opNorm (v - w)))

/-- Uniform limits of spatial gradients and velocities pass through their pointwise
application when both limiting fields are bounded on the set. -/
theorem tendstoUniformlyOn_clm_apply_of_bounded {ι α : Type*} {L : Filter ι} {s : Set α}
    {A : ι → α → E →L[ℝ] F} {B : α → E →L[ℝ] F} {v : ι → α → E} {w : α → E}
    (hA : TendstoUniformlyOn A B L s) (hv : TendstoUniformlyOn v w L s)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hB : ∀ x ∈ s, ‖B x‖ ≤ C) (hw : ∀ x ∈ s, ‖w x‖ ≤ M) :
    TendstoUniformlyOn (fun n x => A n x (v n x)) (fun x => B x (w x)) L s := by
  rw [Metric.tendstoUniformlyOn_iff] at hA hv ⊢
  intro ε hε
  have hpos : 0 < M + 1 + C := by linarith
  let δ := min 1 (ε / (M + 1 + C))
  have hδ : 0 < δ := lt_min zero_lt_one (div_pos hε hpos)
  have hδ₁ : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (M + 1 + C) ≤ ε := (le_div_iff₀ hpos).mp (min_le_right _ _)
  filter_upwards [hA δ hδ, hv δ hδ] with n hnA hnv x hx
  have hdA : ‖A n x - B x‖ < δ := by simpa [dist_comm, dist_eq_norm] using hnA x hx
  have hdv : ‖v n x - w x‖ < δ := by simpa [dist_comm, dist_eq_norm] using hnv x hx
  have hnv' : ‖v n x‖ ≤ M + 1 := by
    calc
      ‖v n x‖ ≤ ‖v n x - w x‖ + ‖w x‖ := norm_le_norm_sub_add _ _
      _ ≤ 1 + M := add_le_add (hdv.le.trans hδ₁) (hw x hx)
      _ = M + 1 := add_comm _ _
  rw [dist_comm, dist_eq_norm]
  calc
    ‖A n x (v n x) - B x (w x)‖
        ≤ ‖A n x - B x‖ * ‖v n x‖ + ‖B x‖ * ‖v n x - w x‖ :=
      norm_clm_apply_sub_le _ _ _ _
    _ ≤ ‖A n x - B x‖ * (M + 1) + C * δ :=
      add_le_add (mul_le_mul_of_nonneg_left hnv' (norm_nonneg _))
        (mul_le_mul (hB x hx) hdv.le (norm_nonneg _) hC)
    _ < δ * (M + 1) + C * δ := add_lt_add_left
      (mul_lt_mul_of_pos_right hdA (add_pos_of_nonneg_of_pos hM zero_lt_one)) _
    _ = δ * (M + 1 + C) := by rw [mul_comm C δ, ← mul_add]
    _ ≤ ε := hδε

/-- On a compact space-time set the (C^1) spatial convergence used in §8.1 gives
uniform convergence of the Eulerian advection. -/
theorem tendstoUniformlyOn_eulerAdvection {ι : Type*} {L : Filter ι} {K : Set (ℝ × Vec3)}
    {U : ι → Velocity} {u : Velocity} (hK : IsCompact K)
    (hU : TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u) L K)
    (hDU : TendstoUniformlyOn (fun j z => fderiv ℝ (U j z.1) z.2)
      (fun z => fderiv ℝ (u z.1) z.2) L K)
    (hu : ContinuousOn (Function.uncurry u) K)
    (hDu : ContinuousOn (fun z => fderiv ℝ (u z.1) z.2) K) :
    TendstoUniformlyOn (fun j z => fderiv ℝ (U j z.1) z.2 (U j z.1 z.2))
      (fun z => fderiv ℝ (u z.1) z.2 (u z.1 z.2)) L K := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hDu
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hu
  exact tendstoUniformlyOn_clm_apply_of_bounded hDU hU (le_max_right C 0) (le_max_right M 0)
    (fun z hz => (hC z hz).trans (le_max_left _ _))
    (fun z hz => (hM z hz).trans (le_max_left _ _))

end Advection

/-- Differentiation preserves the lattice periods of a differentiable lift. -/
theorem SpatiallyPeriodic.fderiv {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Vec3 → F} (hper : SpatiallyPeriodic f) (hf : Differentiable ℝ f) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n x
  let a := latticeVector n
  have h := (hf (x + a)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const a)
  have heq : (fun z => f (z + a)) = f := funext (hper n)
  change HasFDerivAt (fun z => f (z + a)) _ x at h
  rw [heq, ContinuousLinearMap.comp_id] at h
  exact h.fderiv.symm

theorem SpatiallyPeriodic.gradient {p : Vec3 → ℝ} (hper : SpatiallyPeriodic p)
    (hp : Differentiable ℝ p) : SpatiallyPeriodic (gradient p) :=
  fun n x => congrArg (InnerProductSpace.toDual ℝ Vec3).symm (hper.fderiv hp n x)

/-- Uniform convergence on the centered cell gives uniform convergence on the lift
for periodic fields. -/
theorem tendstoUniformly_of_spatiallyPeriodic {ι F : Type*} [PseudoMetricSpace F]
    {L : Filter ι} {f : ι → Vec3 → F} {g : Vec3 → F}
    (hf : ∀ j, SpatiallyPeriodic (f j)) (hg : SpatiallyPeriodic g)
    (h : TendstoUniformlyOn f g L centeredCell) : TendstoUniformly f g L := by
  rw [← tendstoUniformlyOn_univ, Metric.tendstoUniformlyOn_iff] at *
  intro ε hε
  filter_upwards [h ε hε] with j hj x _
  obtain ⟨k, hk⟩ := exists_sub_latticeVector_mem_centeredCell x
  have hf' : f j x = f j (x - latticeVector k) := by
    simpa only [sub_add_cancel] using hf j k (x - latticeVector k)
  have hg' : g x = g (x - latticeVector k) := by
    simpa only [sub_add_cancel] using hg k (x - latticeVector k)
  rw [hf', hg']
  exact hj _ hk

private theorem centeredCell_volume_real_pos : 0 < (volume : Measure Vec3).real centeredCell := by
  have hball : Metric.ball (0 : Vec3) (1 / 2) ⊆ centeredCell := by
    intro x hx i
    have hnorm : ‖x‖ < (1 : ℝ) / 2 := by simpa only [Metric.mem_ball, dist_zero_right] using hx
    exact abs_le.mp ((PiLp.norm_apply_le x i).trans hnorm.le)
  have hInterior : (interior centeredCell).Nonempty :=
    ⟨0, interior_maximal hball Metric.isOpen_ball (Metric.mem_ball_self (by norm_num))⟩
  exact ENNReal.toReal_pos (Measure.measure_pos_of_nonempty_interior volume hInterior).ne'
    isCompact_centeredCell.measure_ne_top

/-- A uniform limit of gradients of differentiable periodic pressures is the gradient of a
periodic mean-zero pressure. The values of the approximating pressures need not be prescribed. -/
theorem exists_periodic_meanZero_pressure_of_uniform_gradient {P : ℕ → Vec3 → ℝ} {g : Vec3 → Vec3}
    (hP : ∀ j, Differentiable ℝ (P j)) (hPer : ∀ j, SpatiallyPeriodic (P j))
    (hg : TendstoUniformly (fun j => gradient (P j)) g atTop) :
    ∃ p : Vec3 → ℝ, SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧
      ∀ x, HasGradientAt p (g x) x := by
  let Q (j : ℕ) (x : Vec3) := P j x - P j 0
  let dual := InnerProductSpace.toDual ℝ Vec3
  have hg' : TendstoUniformly (fun j x => dual (gradient (P j) x)) (fun x => dual (g x)) atTop :=
    dual.isometry.uniformContinuous.comp_tendstoUniformly hg
  have hQ (j : ℕ) (x : Vec3) : HasFDerivAt (Q j) (dual (gradient (P j) x)) x :=
    ((hP j x).hasGradientAt.hasFDerivAt).sub_const _
  have hzero : Cauchy (map (fun j => Q j 0) atTop) := by
    simpa only [Q, sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).cauchy_map
  have hqExists (x : Vec3) : ∃ y : ℝ, Tendsto (fun j => Q j x) atTop (𝓝 y) :=
    cauchySeq_tendsto_of_complete (cauchy_map_of_uniformCauchySeqOn_fderiv isOpen_univ
      isPreconnected_univ (hg'.tendstoUniformlyOn (s := univ)).uniformCauchySeqOn
      (fun j y _ => hQ j y) (mem_univ 0) (mem_univ x) hzero)
  choose q hq using hqExists
  have hqGrad (x : Vec3) : HasGradientAt q (g x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    exact hasFDerivAt_of_tendstoUniformly hg' hQ hq x
  have hqPer : SpatiallyPeriodic q := by
    intro k x
    exact tendsto_nhds_unique_of_eventuallyEq (hq (x + latticeVector k)) (hq x)
      (Eventually.of_forall fun j => by simp only [Q, hPer j k x])
  let c := (∫ x in centeredCell, q x) / (volume : Measure Vec3).real centeredCell
  refine ⟨fun x => q x - c, fun k x => congrArg (· - c) (hqPer k x), ?_, ?_⟩
  · have hqCont : Continuous q := continuous_iff_continuousAt.mpr
      (fun x => (hqGrad x).differentiableAt.continuousAt)
    have hqInt : IntegrableOn q centeredCell :=
      ContinuousOn.integrableOn_compact isCompact_centeredCell hqCont.continuousOn
    have hcInt : IntegrableOn (fun _ : Vec3 => c) centeredCell :=
      integrableOn_const isCompact_centeredCell.measure_ne_top
    rw [integral_sub hqInt hcInt, setIntegral_const, smul_eq_mul, mul_comm]
    have hc : c * (volume : Measure Vec3).real centeredCell = ∫ x in centeredCell, q x :=
      div_mul_cancel₀ _ centeredCell_volume_real_pos.ne'
    rw [hc, sub_self]
  · intro x
    rw [hasGradientAt_iff_hasFDerivAt]
    exact (hqGrad x).hasFDerivAt.sub_const c

/-- The reconstruction can be applied at every time using uniform convergence on
the space-time slab over the centered cell and the periods of the limiting gradient. -/
theorem exists_periodic_meanZero_pressure_family {I : Set ℝ} {P : ℕ → Pressure} {g : Velocity}
    (hP : ∀ j t, t ∈ I → Differentiable ℝ (P j t))
    (hPer : ∀ j t, t ∈ I → SpatiallyPeriodic (P j t))
    (hgPer : ∀ t ∈ I, SpatiallyPeriodic (g t))
    (hg : TendstoUniformlyOn (fun j z => gradient (P j z.1) z.2) (Function.uncurry g)
      atTop (I ×ˢ centeredCell)) :
    ∃ p : Pressure, ∀ t ∈ I, SpatiallyPeriodic (p t) ∧ (∫ x in centeredCell, p t x) = 0 ∧
      ∀ x, HasGradientAt (p t) (g t x) x := by
  have hslices (t : ℝ) : ∃ p : Vec3 → ℝ, t ∈ I →
      SpatiallyPeriodic p ∧ (∫ x in centeredCell, p x) = 0 ∧ ∀ x, HasGradientAt p (g t x) x := by
    by_cases ht : t ∈ I
    · have hslice : TendstoUniformlyOn (fun j => gradient (P j t)) (g t) atTop centeredCell := by
        rw [Metric.tendstoUniformlyOn_iff] at hg ⊢
        intro ε hε
        filter_upwards [hg ε hε] with j hj x hx
        exact hj (t, x) ⟨ht, hx⟩
      obtain ⟨p, hp⟩ := exists_periodic_meanZero_pressure_of_uniform_gradient
        (fun j => hP j t ht) (fun j => hPer j t ht)
        (tendstoUniformly_of_spatiallyPeriodic
          (fun j => (hPer j t ht).gradient (hP j t ht)) (hgPer t ht) hslice)
      exact ⟨p, fun _ => hp⟩
    · exact ⟨fun _ => 0, fun h => (ht h).elim⟩
  choose p hp using hslices
  exact ⟨p, hp⟩

/-- A pressure with a smooth gradient is smooth in space. -/
theorem contDiff_pressure_of_contDiff_gradient {p : Vec3 → ℝ} {g : Vec3 → Vec3}
    (hD : ∀ x, HasGradientAt p (g x) x) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ p := by
  let dual := (InnerProductSpace.toDual ℝ Vec3).toLinearIsometry.toContinuousLinearMap
  have hd : fderiv ℝ p = fun x => dual (g x) :=
    funext fun x => (hD x).hasFDerivAt.fderiv
  exact contDiff_infty_iff_fderiv.mpr ⟨fun x => (hD x).differentiableAt,
    hd ▸ dual.contDiff.comp hg⟩

end TorusEuler

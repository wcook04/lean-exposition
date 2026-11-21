import Breakdown.FracCell.AxisLiftSlope
import Breakdown.FracCell.AxisLiftEnergy

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert Internal.SpectralBlocksMode

namespace Internal.AxisLiftDeriv

theorem null_cyl {P Q : Set ℝ} (hP : P.Finite) (hQ : Q.Finite) :
    ∀ᵐ y : Space ∂volume, radialCoord y ∉ P ∧ y 2 ∉ Q := by
  set B : Set Space := {y | radialCoord y ∈ P ∨ y 2 ∈ Q} with hBdef
  have hBm : MeasurableSet B := by
    have h1 : Measurable radialCoord := Internal.AxisLiftSlope.rad_slope.continuous.measurable
    have h2 : Measurable (fun y : Space => y 2) := (Internal.AxisLiftSlope.coord_slope 2).continuous.measurable
    exact (h1 hP.measurableSet).union (h2 hQ.measurableSet)
  have hnull2 : volume {q : ℝ × ℝ | q.1 ∈ P ∨ q.2 ∈ Q} = 0 := by
    have e : {q : ℝ × ℝ | q.1 ∈ P ∨ q.2 ∈ Q} = P ×ˢ (Set.univ : Set ℝ) ∪ (Set.univ : Set ℝ) ×ˢ Q := by
      ext q
      simp
    rw [e, Measure.volume_eq_prod]
    refine measure_union_null ?_ ?_
    · rw [Measure.prod_prod, hP.measure_zero, zero_mul]
    · rw [Measure.prod_prod, hQ.measure_zero, mul_zero]
  have hn : ∀ n : ℕ, volume (B ∩ Metric.closedBall (0 : Space) n) = 0 := by
    intro n
    have hm : MeasurableSet (B ∩ Metric.closedBall (0 : Space) n) := hBm.inter Metric.isClosed_closedBall.measurableSet
    have hfin : volume (B ∩ Metric.closedBall (0 : Space) n) ≠ ⊤ :=
      (measure_mono Set.inter_subset_right).trans_lt (isCompact_closedBall _ _).measure_lt_top |>.ne
    have hI : Integrable ((B ∩ Metric.closedBall (0 : Space) n).indicator (1 : Space → ℝ)) :=
      (integrable_indicator_iff hm).2 (integrableOn_const hfin)
    have h0 := cylIntegral _ hI
    have hz : ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), q.1 * ∫ θ in (-π)..π,
        (B ∩ Metric.closedBall (0 : Space) n).indicator (1 : Space → ℝ) (cylPoint q.1 θ q.2) = 0 := by
      refine integral_eq_zero_of_ae ?_
      have hc : ∀ᵐ q : ℝ × ℝ ∂volume, ¬ (q.1 ∈ P ∨ q.2 ∈ Q) := by
        rw [ae_iff]
        simp only [not_not]
        exact hnull2
      filter_upwards [ae_restrict_of_ae hc, ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with q hq hqS
      have hr : 0 < q.1 := hqS.1
      have e : ∀ θ, (B ∩ Metric.closedBall (0 : Space) n).indicator (1 : Space → ℝ) (cylPoint q.1 θ q.2) = 0 := by
        intro θ
        refine Set.indicator_of_notMem (fun hm' => hq ?_) _
        have := hm'.1
        simp only [hBdef, Set.mem_ofPred_eq, radial_cyl hr, cyl2] at this
        exact this
      simp [e]
    rw [hz, integral_indicator_one hm] at h0
    exact (measureReal_eq_zero_iff hfin).1 h0
  have hU : B = ⋃ n : ℕ, B ∩ Metric.closedBall (0 : Space) n := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hy
      obtain ⟨n, hn⟩ := exists_nat_ge ‖y‖
      exact ⟨n, hy, hn⟩
    · rintro ⟨n, hy, -⟩
      exact hy
  have hB0 : volume B = 0 := by
    rw [hU]
    exact measure_iUnion_null hn
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) hB0
  simp only [Set.mem_ofPred_eq, not_and_or, not_not] at hy
  exact hy

theorem decomp (θ : ℝ) (v : Space) : v = ∑ d : Fin 3, inner ℝ (frameAt d θ) v • frameAt d θ := by
  ext i
  fin_cases i <;> simp [Fin.sum_univ_three, frameAt, unitVector, inner_add_left, EuclideanSpace.inner_single_left] <;>
    first | ring1 | linear_combination (-(v 0)) * cos_sq_add_sin_sq θ | linear_combination (-(v 1)) * cos_sq_add_sin_sq θ

theorem clm_eq (θ : ℝ) {F M : Space →L[ℝ] Space} (h : ∀ d, F (frameAt d θ) = M (frameAt d θ)) : F = M := by
  ext1 v
  rw [decomp θ v, map_sum, map_sum]
  simp only [map_smul, h]

theorem form_apply (A : Fin 3 → Fin 3 → ℝ) (θ : ℝ) (d' : Fin 3) :
    (∑ c : Fin 3, ∑ d : Fin 3, A c d • (innerSL ℝ (frameAt d θ)).smulRight (frameAt c θ)) (frameAt d' θ)
      = ∑ c : Fin 3, A c d' • frameAt c θ := by
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, frame_inner, smul_smul]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [mul_ite, ite_smul, Finset.sum_ite_eq']

theorem frame_coef (a : Fin 3 → ℝ) (θ : ℝ) (c' : Fin 3) :
    inner ℝ (∑ c : Fin 3, a c • frameAt c θ) (frameAt c' θ) = a c' := by
  simp only [sum_inner, real_inner_smul_left, frame_inner]
  simp

theorem cos_angle {r : ℝ} (hr : 0 < r) (φ z : ℝ) : Real.cos (angleCoord (cylPoint r φ z)) = Real.cos φ := by
  have h : r * Real.cos (angleCoord (cylPoint r φ z)) = r * Real.cos φ := by
    have h0 := Complex.norm_mul_cos_arg (⟨(cylPoint r φ z) 0, (cylPoint r φ z) 1⟩ : ℂ)
    rw [← Internal.AxisLiftSlope.rad_cx, radial_cyl hr] at h0
    rw [angleCoord, h0]
    exact cyl0 r φ z
  exact mul_left_cancel₀ hr.ne' h

theorem sin_angle {r : ℝ} (hr : 0 < r) (φ z : ℝ) : Real.sin (angleCoord (cylPoint r φ z)) = Real.sin φ := by
  have h : r * Real.sin (angleCoord (cylPoint r φ z)) = r * Real.sin φ := by
    have h0 := Complex.norm_mul_sin_arg (⟨(cylPoint r φ z) 0, (cylPoint r φ z) 1⟩ : ℂ)
    rw [← Internal.AxisLiftSlope.rad_cx, radial_cyl hr] at h0
    rw [angleCoord, h0]
    exact cyl1 r φ z
  exact mul_left_cancel₀ hr.ne' h

theorem frame_any {r : ℝ} (hr : 0 < r) (c : Fin 3) (φ z : ℝ) : frameVector c (cylPoint r φ z) = frameAt c φ := by
  rw [frame_eq]
  fin_cases c <;> simp [frameAt, cos_angle hr, sin_angle hr]

theorem cyl_self (y : Space) : cylPoint (radialCoord y) (angleCoord y) (y 2) = y := by
  have hcs : radialCoord y * Real.cos (angleCoord y) = y 0 := by
    rw [Internal.AxisLiftSlope.rad_cx, angleCoord]
    exact Complex.norm_mul_cos_arg _
  have hsn : radialCoord y * Real.sin (angleCoord y) = y 1 := by
    rw [Internal.AxisLiftSlope.rad_cx, angleCoord]
    exact Complex.norm_mul_sin_arg _
  ext i
  fin_cases i <;> simp [cylPoint, hcs, hsn]

theorem psi_cyl (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (ψ : Space → Space)
    (hψ : ∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y)
    {r : ℝ} (hr : 0 < r) (φ z : ℝ) :
    ψ (cylPoint r φ z) = ∑ c : Fin 3,
      (∑ s : Fin 2, Internal.OnAxisNorm.cellInd g s r z * liftVal g χ (u s c) r z) • frameAt c φ := by
  classical
  rw [hψ]
  simp only [Set.indicator_apply, solid_iff g _ hr φ z, frame_any hr, radial_cyl hr, cyl2,
    Internal.OnAxisNorm.cellInd]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  split_ifs <;> simp only [liftVal, one_mul, zero_mul, add_zero, zero_add, add_smul, zero_smul] <;> abel

theorem cyl_lin (r φ z : ℝ) : cylPoint r φ z
    = (r * Real.cos φ) • unitVector 0 + (r * Real.sin φ) • unitVector 1 + z • unitVector 2 := by
  ext i
  fin_cases i <;> simp [cylPoint, unitVector]

theorem solid_closed (g : CellBlock) (hin : g.innerRadius = 0) (s : Fin 2) : IsClosed (cellSolid g s) := by
  have e : cellSolid g s = {y : Space | radialCoord y ≤ g.outerRadius ∧ Internal.OnAxisNorm.zLow g s ≤ y 2 ∧
      y 2 ≤ Internal.OnAxisNorm.zHigh g s} := by
    ext y
    exact Internal.AxisLiftSlope.mem_iff g hin s y
  rw [e]
  have h1 := Internal.AxisLiftSlope.rad_slope.continuous
  have h2 := (Internal.AxisLiftSlope.coord_slope 2).continuous
  exact (isClosed_le h1 continuous_const).inter ((isClosed_le continuous_const h2).inter (isClosed_le h2 continuous_const))

open Internal.OnAxisNorm in
theorem sel (g : CellBlock) (hin : g.innerRadius = 0) (hlow : 0 ≤ g.lowerHeight) (s : Fin 2) {r' z' : ℝ}
    (h1 : 0 < r') (h2 : r' ≤ g.outerRadius) (h3 : zLow g s < z') (h4 : z' < zHigh g s) (b : Fin 2 → ℝ) :
    ∑ s' : Fin 2, cellInd g s' r' z' * b s' = b s := by
  have e1 : cellInd g s r' z' = 1 := by
    unfold cellInd
    rw [if_pos ((mem_cell g hin s h1 z').2 ⟨h2, h3.le, h4.le⟩)]
  have e2 : ∀ s', s' ≠ s → cellInd g s' r' z' = 0 := by
    intro s' hs'
    unfold cellInd
    rw [if_neg]
    intro hm
    obtain ⟨-, h5, h6⟩ := (mem_cell g hin s' h1 z').1 hm
    fin_cases s <;> fin_cases s' <;> simp_all [zLow, zHigh] <;> linarith
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  rcases hs with rfl | rfl
  · rw [Fin.sum_univ_two, e1, e2 1 (by decide)]
    simp
  · rw [Fin.sum_univ_two, e1, e2 0 (by decide)]
    simp

theorem dir_z {ψ : Space → Space} {F : Space →L[ℝ] Space} {r θ z zl zh R : ℝ} (hF : HasFDerivAt ψ F (cylPoint r θ z))
    (hr : 0 < r) (hrR : r ≤ R) (hl : zl < z) (hh : z < zh) (V : Fin 3 → ℝ → ℝ → ℝ)
    (hloc : ∀ r' φ z', 0 < r' → r' ≤ R → zl < z' → z' < zh → ψ (cylPoint r' φ z') = ∑ c : Fin 3, V c r' z' • frameAt c φ)
    (W : Fin 3 → ℝ) (hV : ∀ c, HasDerivAt (fun t => V c r (z + t)) (W c) 0) :
    F (frameAt 2 θ) = ∑ c : Fin 3, W c • frameAt c θ := by
  have eγ : ∀ t : ℝ, cylPoint r θ (z + t) = cylPoint r θ z + t • unitVector 2 := by
    intro t
    ext i
    fin_cases i <;> simp [cylPoint, unitVector]
  have hγ : HasDerivAt (fun t : ℝ => cylPoint r θ z + t • unitVector 2) (unitVector 2) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVector 2)).const_add (cylPoint r θ z)
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have h2 : HasDerivAt (fun t => ∑ c : Fin 3, V c r (z + t) • frameAt c θ) (∑ c : Fin 3, W c • frameAt c θ) 0 := by
    have h := HasDerivAt.sum (u := Finset.univ) (fun c _ => (hV c).smul_const (frameAt c θ))
    have e : (∑ c ∈ Finset.univ, fun t => V c r (z + t) • frameAt c θ)
        = fun t => ∑ c : Fin 3, V c r (z + t) • frameAt c θ := by
      funext t
      simp [Finset.sum_apply]
    rw [e] at h
    exact h
  have ht : Filter.Tendsto (fun t : ℝ => z + t) (nhds 0) (nhds z) := by
    simpa using (tendsto_const_nhds (x := z)).add (Filter.tendsto_id (x := nhds (0 : ℝ)))
  have hev := ht.eventually (Ioo_mem_nhds hl hh)
  have heq : (fun t : ℝ => ψ (cylPoint r θ z + t • unitVector 2)) =ᶠ[nhds 0]
      (fun t => ∑ c : Fin 3, V c r (z + t) • frameAt c θ) := by
    filter_upwards [hev] with t ht'
    rw [← eγ t, hloc r θ (z + t) hr hrR ht'.1 ht'.2]
  exact h1.unique (h2.congr_of_eventuallyEq heq)

theorem dir_r {ψ : Space → Space} {F : Space →L[ℝ] Space} {r θ z zl zh R : ℝ} (hF : HasFDerivAt ψ F (cylPoint r θ z))
    (hr : 0 < r) (hrR : r < R) (hl : zl < z) (hh : z < zh) (V : Fin 3 → ℝ → ℝ → ℝ)
    (hloc : ∀ r' φ z', 0 < r' → r' ≤ R → zl < z' → z' < zh → ψ (cylPoint r' φ z') = ∑ c : Fin 3, V c r' z' • frameAt c φ)
    (c : Fin 3) : HasDerivAt (fun t => V c t z) (inner ℝ (F (frameAt 0 θ)) (frameAt c θ)) r := by
  have eγ : ∀ t : ℝ, cylPoint (r + t) θ z = cylPoint r θ z + t • frameAt 0 θ := by
    intro t
    ext i
    fin_cases i <;> simp [cylPoint, frameAt] <;> ring
  have hγ : HasDerivAt (fun t : ℝ => cylPoint r θ z + t • frameAt 0 θ) (frameAt 0 θ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (frameAt 0 θ)).const_add (cylPoint r θ z)
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have h2 := h1.inner ℝ (hasDerivAt_const (0 : ℝ) (frameAt c θ))
  simp only [inner_zero_right, zero_add] at h2
  have ht : Filter.Tendsto (fun t : ℝ => r + t) (nhds 0) (nhds r) := by
    simpa using (tendsto_const_nhds (x := r)).add (Filter.tendsto_id (x := nhds (0 : ℝ)))
  have hev := ht.eventually (Ioo_mem_nhds hr hrR)
  have heq : (fun t : ℝ => V c (r + t) z) =ᶠ[nhds 0]
      (fun t => inner ℝ ((ψ ∘ fun t : ℝ => cylPoint r θ z + t • frameAt 0 θ) t) (frameAt c θ)) := by
    filter_upwards [hev] with t ht'
    simp only [Function.comp_apply]
    rw [← eγ t, hloc (r + t) θ z ht'.1 ht'.2.le hl hh, frame_coef]
  have h3 := h2.congr_of_eventuallyEq heq
  have h4 : HasDerivAt (fun t : ℝ => V c (r + t) z) (inner ℝ (F (frameAt 0 θ)) (frameAt c θ)) (r - r) := by
    rw [sub_self]
    exact h3
  have h5 := h4.comp (h := fun x : ℝ => x - r) r ((hasDerivAt_id' r).sub_const r)
  simp only [mul_one] at h5
  have e : ((fun t => V c (r + t) z) ∘ fun x : ℝ => x - r) = fun t => V c t z := by
    funext t
    simp
  rw [e] at h5
  exact h5

theorem dir_t {ψ : Space → Space} {F : Space →L[ℝ] Space} {r θ z zl zh R : ℝ} (hF : HasFDerivAt ψ F (cylPoint r θ z))
    (hr : 0 < r) (hrR : r ≤ R) (hl : zl < z) (hh : z < zh) (V : Fin 3 → ℝ → ℝ → ℝ)
    (hloc : ∀ r' φ z', 0 < r' → r' ≤ R → zl < z' → z' < zh → ψ (cylPoint r' φ z') = ∑ c : Fin 3, V c r' z' • frameAt c φ) :
    F (frameAt 1 θ) = (-(V 1 r z) / r) • frameAt 0 θ + (V 0 r z / r) • frameAt 1 θ := by
  have hc : HasDerivAt (fun t => Real.cos (θ + t)) (-Real.sin θ) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add θ).cos
  have hs : HasDerivAt (fun t => Real.sin (θ + t)) (Real.cos θ) 0 := by
    simpa using ((hasDerivAt_id' (0 : ℝ)).const_add θ).sin
  have hγ0 : HasDerivAt (fun t => (r * Real.cos (θ + t)) • unitVector 0 + (r * Real.sin (θ + t)) • unitVector 1
      + z • unitVector 2) ((r * -Real.sin θ) • unitVector 0 + (r * Real.cos θ) • unitVector 1 + (0 : Space)) 0 :=
    (((hc.const_mul r).smul_const (unitVector 0)).add ((hs.const_mul r).smul_const (unitVector 1))).add
      (hasDerivAt_const (0 : ℝ) (z • unitVector 2))
  have hγ : HasDerivAt (fun t => cylPoint r (θ + t) z) (r • frameAt 1 θ) 0 := by
    have e1 : (fun t => cylPoint r (θ + t) z) = (fun t => (r * Real.cos (θ + t)) • unitVector 0
        + (r * Real.sin (θ + t)) • unitVector 1 + z • unitVector 2) := by
      funext t
      exact cyl_lin r (θ + t) z
    have e2 : r • frameAt 1 θ = (r * -Real.sin θ) • unitVector 0 + (r * Real.cos θ) • unitVector 1 + (0 : Space) := by
      ext i
      fin_cases i <;> simp [frameAt, unitVector]
    rw [e1, e2]
    exact hγ0
  have h1 := hF.comp_hasDerivAt_of_eq (0 : ℝ) hγ (by simp)
  have e3 : ∀ t, ψ (cylPoint r (θ + t) z) = (V 0 r z * Real.cos (θ + t) - V 1 r z * Real.sin (θ + t)) • unitVector 0
      + (V 0 r z * Real.sin (θ + t) + V 1 r z * Real.cos (θ + t)) • unitVector 1 + V 2 r z • unitVector 2 := by
    intro t
    rw [hloc r (θ + t) z hr hrR hl hh]
    ext i
    fin_cases i <;> simp [Fin.sum_univ_three, frameAt, unitVector] <;> ring
  have h2 : HasDerivAt (fun t => (V 0 r z * Real.cos (θ + t) - V 1 r z * Real.sin (θ + t)) • unitVector 0
      + (V 0 r z * Real.sin (θ + t) + V 1 r z * Real.cos (θ + t)) • unitVector 1 + V 2 r z • unitVector 2)
      ((V 0 r z * -Real.sin θ - V 1 r z * Real.cos θ) • unitVector 0
        + (V 0 r z * Real.cos θ + V 1 r z * -Real.sin θ) • unitVector 1 + (0 : Space)) 0 :=
    ((((hc.const_mul _).sub (hs.const_mul _)).smul_const (unitVector 0)).add
      (((hs.const_mul _).add (hc.const_mul _)).smul_const (unitVector 1))).add
      (hasDerivAt_const (0 : ℝ) (V 2 r z • unitVector 2))
  have h3 := h1.unique (h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => e3 t))
  rw [map_smul] at h3
  have hr0 : r ≠ 0 := hr.ne'
  have h4 : F (frameAt 1 θ) = r⁻¹ • ((V 0 r z * -Real.sin θ - V 1 r z * Real.cos θ) • unitVector 0
        + (V 0 r z * Real.cos θ + V 1 r z * -Real.sin θ) • unitVector 1 + (0 : Space)) := by
    rw [← h3, smul_smul, inv_mul_cancel₀ hr0, one_smul]
  rw [h4]
  ext i
  fin_cases i <;> simp [frameAt, unitVector] <;> field_simp <;> ring

theorem hz_aux (v : ℕ → ℝ → ℝ) (hv : ∀ j, ContDiff ℝ 1 (v j)) (n : ℕ) (r z k : ℝ) :
    HasDerivAt (fun t => k * ∑ j ∈ Finset.range n, r ^ j * v j (z + t))
      (k * ∑ j ∈ Finset.range n, r ^ j * deriv (v j) z) 0 := by
  have hj : ∀ j, HasDerivAt (fun t => r ^ j * v j (z + t)) (r ^ j * deriv (v j) z) 0 := by
    intro j
    have h0 : HasDerivAt (v j) (deriv (v j) z) (z + 0) := by
      rw [add_zero]
      exact ((hv j).differentiable one_ne_zero z).hasDerivAt
    have h1 := h0.comp (h := fun t : ℝ => z + t) (0 : ℝ) ((hasDerivAt_id' (0 : ℝ)).const_add z)
    simp only [mul_one] at h1
    exact h1.const_mul (r ^ j)
  have h := HasDerivAt.sum (u := Finset.range n) (fun j _ => hj j)
  have e : (∑ j ∈ Finset.range n, fun t => r ^ j * v j (z + t))
      = fun t => ∑ j ∈ Finset.range n, r ^ j * v j (z + t) := by
    funext t
    simp [Finset.sum_apply]
  rw [e] at h
  exact h.const_mul k

end Internal.AxisLiftDeriv

open Internal.OnAxisNorm Internal.AxisLift Internal.AxisLiftDeriv in
theorem point_deriv (g : CellBlock) (hin : g.innerRadius = 0) (hmode : g.mode = 0)
    (hlow : 0 ≤ g.lowerHeight) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ)
    (hu : ∀ s c j, ContDiff ℝ 1 (u s c j)) (ψ : Space → Space)
    (hψ : ∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y)
    {y : Space} (hr : 0 < radialCoord y) (hrR : radialCoord y ≠ g.outerRadius)
    (hzl : ∀ s, y 2 ≠ zLow g s) (hzh : ∀ s, y 2 ≠ zHigh g s) (hd : DifferentiableAt ℝ ψ y) :
    fderiv ℝ ψ y = liftGrad g χ u y := by
  have hy := cyl_self y
  have hθ : angleCoord y ∈ Set.Ioc (-π) π := ⟨Complex.neg_pi_lt_arg _, Complex.arg_le_pi _⟩
  by_cases hc : ∃ s, cylPoint (radialCoord y) 0 (y 2) ∈ cellSolid g s
  · obtain ⟨s, hs⟩ := hc
    obtain ⟨h1, h2, h3⟩ := (mem_cell g hin s hr (y 2)).1 hs
    have h1' : radialCoord y < g.outerRadius := lt_of_le_of_ne h1 hrR
    have h2' : zLow g s < y 2 := lt_of_le_of_ne h2 (hzl s).symm
    have h3' : y 2 < zHigh g s := lt_of_le_of_ne h3 (hzh s)
    set V : Fin 3 → ℝ → ℝ → ℝ := fun c r' z' => liftVal g χ (u s c) r' z' with hVdef
    have hloc : ∀ r' φ z', 0 < r' → r' ≤ g.outerRadius → zLow g s < z' → z' < zHigh g s →
        ψ (cylPoint r' φ z') = ∑ c : Fin 3, V c r' z' • frameAt c φ := by
      intro r' φ z' a1 a2 a3 a4
      rw [psi_cyl g χ u ψ hψ a1 φ z']
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [sel g hin hlow s a1 a2 a3 a4 (fun s' => liftVal g χ (u s' c) r' z')]
    have hF : HasFDerivAt ψ (fderiv ℝ ψ y) (cylPoint (radialCoord y) (angleCoord y) (y 2)) := by
      rw [hy]
      exact hd.hasFDerivAt
    have hG : liftGrad g χ u y = liftGrad g χ u (cylPoint (radialCoord y) (angleCoord y) (y 2)) := by rw [hy]
    have hA : ∀ c d, ∑ s' : Fin 2, cellInd g s' (radialCoord y) (y 2) * liftCoef g χ u s' c d 0 (radialCoord y) (y 2)
        = liftCoef g χ u s c d 0 (radialCoord y) (y 2) := fun c d =>
      sel g hin hlow s hr h1 h2' h3' (fun s' => liftCoef g χ u s' c d 0 (radialCoord y) (y 2))
    rw [hG, grad_cyl g hmode χ u hr hθ (y 2)]
    simp only [hA]
    refine clm_eq (angleCoord y) fun d => ?_
    rw [form_apply]
    have hd3 : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
    rcases hd3 with rfl | rfl | rfl
    · rw [decomp (angleCoord y) (fderiv ℝ ψ y (frameAt 0 (angleCoord y)))]
      refine Finset.sum_congr rfl fun c _ => ?_
      have h0 := (dir_r hF hr h1' h2' h3' V hloc c).deriv
      rw [real_inner_comm, ← h0]
      simp [liftCoef, hVdef, liftRad, liftVal]
    · rw [dir_t hF hr h1 h2' h3' V hloc]
      simp [Fin.sum_univ_three, liftCoef, hVdef, neg_div]
    · rw [dir_z hF hr h1 h2' h3' V hloc (fun c => liftHgt g χ (u s c) (radialCoord y) (y 2))
        (fun c => hz_aux (u s c) (hu s c) (g.degree + 1) (radialCoord y) (y 2) _)]
      simp [liftCoef]
  · have hnot : ∀ s, y ∉ cellSolid g s := fun s hm =>
      hc ⟨s, by rw [← solid_iff g s hr (angleCoord y) (y 2), hy]; exact hm⟩
    have hO : ∀ s, ∀ᶠ y' in nhds y, y' ∉ cellSolid g s := fun s =>
      (solid_closed g hin s).isOpen_compl.mem_nhds (hnot s)
    have hev : ψ =ᶠ[nhds y] fun _ => (0 : Space) := by
      filter_upwards [hO 0, hO 1] with y' a0 a1
      rw [hψ y', Fin.sum_univ_two, Set.indicator_of_notMem a0, Set.indicator_of_notMem a1, add_zero]
    rw [hev.fderiv_eq, fderiv_const_apply]
    unfold liftGrad
    rw [Fin.sum_univ_two, Set.indicator_of_notMem (hnot 0), Set.indicator_of_notMem (hnot 1), add_zero]

open Internal.OnAxisNorm Internal.AxisLiftDeriv in
theorem liftDeriv_holds : LiftDerivStatement := by
  intro g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  filter_upwards [null_cyl (P := {0, g.outerRadius})
    (Q := {g.lowerHeight, g.upperHeight, -g.lowerHeight, -g.upperHeight}) (Set.toFinite _) (Set.toFinite _)]
    with y hy hd
  obtain ⟨hP, hQ⟩ := hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hP hQ
  refine point_deriv g hin hmode hlow χ u hu ψ hψ (lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm hP.1)) hP.2
    (fun s => ?_) (fun s => ?_) hd
  · rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
    · simpa [zLow] using hQ.1
    · simpa [zLow] using hQ.2.2.2
  · rcases (show s = 0 ∨ s = 1 by fin_cases s <;> simp) with rfl | rfl
    · simpa [zHigh] using hQ.2.1
    · simpa [zHigh] using hQ.2.2.1


end Spectral

end CellCert

end Breakdown

import TorusEuler.TruncatedParentResidual
import TorusEuler.EndpointConcreteProjection
import TorusEuler.EndpointSpatialRegularity
import Mathlib.Analysis.Calculus.MeanValue

/-! The periodic Leray estimate in the spatial lift norms of Proposition 5.11. -/

open Filter Set UnitAddTorus
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

private abbrev HolderLabels := UnitAddTorus (Fin 3)

private theorem holderBridge_toUnitTorus_sub (x y : Vec3) :
    toUnitTorus (x - y) = toUnitTorus x - toUnitTorus y := by
  funext i
  exact AddCircle.coe_sub 1 (x i) (y i)

private theorem holderBridge_dist_le_lift (x y : Vec3) :
    dist (toUnitTorus x) (toUnitTorus y) ≤ ‖x - y‖ := by
  rw [dist_eq_norm, ← holderBridge_toUnitTorus_sub]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mpr
  intro i
  change ‖(((x - y) i : ℝ) : UnitAddCircle)‖ ≤ ‖x - y‖
  exact QuotientAddGroup.norm_mk_le_norm.trans (PiLp.norm_apply_le (x - y) i)

theorem holderBridge_exists_close_lifts (z w : HolderLabels) :
    ∃ x y : Vec3, toUnitTorus x = z ∧ toUnitTorus y = w ∧ ‖x - y‖ ≤ 2 * dist z w := by
  obtain ⟨x, hx⟩ := toUnitTorus_surjective z
  obtain ⟨a, ha⟩ := toUnitTorus_surjective (z - w)
  obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell a
  let b := a - latticeVector n
  have hb : toUnitTorus b = z - w := by
    rw [← ha]
    apply (toUnitTorus_eq_iff b a).mpr
    refine ⟨-n, ?_⟩
    apply PiLp.ext
    intro i
    change a i - (n i : ℝ) = a i + ((-n) i : ℝ)
    simp [sub_eq_add_neg]
  have hy : toUnitTorus (x - b) = w := by
    rw [holderBridge_toUnitTorus_sub, hx, hb, sub_sub_cancel]
  refine ⟨x, x - b, hx, hy, ?_⟩
  rw [sub_sub_cancel]
  have hcoord (i : Fin 3) : |b i| ≤ dist z w := by
    have hhalf : |b i| ≤ |(1 : ℝ)| / 2 := by simpa [b] using abs_le.mpr (hn i)
    rw [← (AddCircle.norm_coe_eq_abs_iff 1 (by norm_num)).mpr hhalf]
    change ‖toUnitTorus b i‖ ≤ dist z w
    rw [hb, dist_eq_norm]
    exact norm_le_pi_norm _ i
  apply (sq_le_sq₀ (norm_nonneg b) (by positivity)).mp
  rw [EuclideanSpace.real_norm_sq_eq]
  calc
    _ ≤ ∑ _i : Fin 3, (dist z w) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact (sq_abs (b i)).symm.trans_le (pow_le_pow_left₀ (abs_nonneg _) (hcoord i) 2)
    _ ≤ _ := by
      simp
      linarith [sq_nonneg (dist z w)]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem quotient_iteratedFDeriv_zero (f : Vec3 → E) :
    spatialHolderHalfQuotient (iteratedFDeriv ℝ 0 f) = spatialHolderHalfQuotient f := by
  funext p
  rw [iteratedFDeriv_zero_eq_comp]
  let e := (continuousMultilinearCurryFin0 ℝ Vec3 E).symm
  change ‖e (f (p.1 + p.2)) - e (f p.1)‖ / Real.sqrt ‖p.2‖ = _
  rw [← e.map_sub, e.norm_map]
  rfl

/-- The lift's order-zero half-Hölder norm is the sum of the supremum and seminorm. -/
theorem spatialHolderHalfNorm_zero_eq (f : Vec3 → E) :
    spatialHolderHalfNorm 0 f = spatialSupNorm f + spatialHolderHalfSeminorm f := by
  simp only [spatialHolderHalfNorm, Nat.zero_add, Finset.sum_range_one, spatialSupNorm,
    norm_iteratedFDeriv_zero, spatialHolderHalfSeminorm, quotient_iteratedFDeriv_zero]

/-- Bounds on the field and its increments are equivalent to membership in lift order zero. -/
theorem spatialHolderHalf_zero_iff (f : Vec3 → E) :
    SpatialHolderHalf 0 f ↔ Continuous f ∧ BddAbove (range (fun x => ‖f x‖)) ∧
      BddAbove (range (spatialHolderHalfQuotient f)) := by
  unfold SpatialHolderHalf
  rw [show (↑(0 : ℕ) : ℕ∞ω) = 0 from rfl, contDiff_zero]
  constructor
  · rintro ⟨hc, hb⟩
    refine ⟨hc, ?_⟩
    simpa only [norm_iteratedFDeriv_zero, quotient_iteratedFDeriv_zero] using (hb 0 le_rfl)
  · rintro ⟨hc, hb⟩
    refine ⟨hc, fun j hj => ?_⟩
    obtain rfl := Nat.eq_zero_of_le_zero hj
    simpa only [norm_iteratedFDeriv_zero, quotient_iteratedFDeriv_zero] using hb

/-- Pullback to the Euclidean lift is bounded by twice the quotient half-Hölder norm. -/
theorem spatialHolderHalf_zero_of_halfHolder (u : HalfHolder HolderLabels E) :
    let f := fun x => HalfHolder.eval (toUnitTorus x) u
    SpatialHolderHalf 0 f ∧ spatialHolderHalfNorm 0 f ≤ 2 * ‖u‖ := by
  let f := fun x => HalfHolder.eval (toUnitTorus x) u
  have hL : LipschitzWith 1 toUnitTorus := LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using holderBridge_dist_le_lift x y
  have hu := (HalfHolder.norm_le_iff (norm_nonneg u)).mp le_rfl
  have hval (x : Vec3) : ‖f x‖ ≤ ‖u‖ := hu.1 (toUnitTorus x)
  have hquot (p : Vec3 × Vec3) : spatialHolderHalfQuotient f p ≤ ‖u‖ := by
    rcases p with ⟨x, v⟩
    by_cases hv : v = 0
    · simp [spatialHolderHalfQuotient, hv]
    · apply (div_le_iff₀ (Real.sqrt_pos_of_pos (norm_pos_iff.mpr hv))).2
      refine (hu.2 (toUnitTorus (x + v)) (toUnitTorus x)).trans ?_
      apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (norm_nonneg u)
      simpa only [add_sub_cancel_left] using holderBridge_dist_le_lift (x + v) x
  refine ⟨(spatialHolderHalf_zero_iff f).2 ⟨u.val.1.continuous.comp hL.continuous,
    ⟨‖u‖, forall_mem_range.mpr hval⟩, ⟨‖u‖, forall_mem_range.mpr hquot⟩⟩, ?_⟩
  rw [spatialHolderHalfNorm_zero_eq, two_mul]
  exact add_le_add (ciSup_le hval) (ciSup_le hquot)

/-- A periodic order-zero half-Hölder field descends with a bound in the quotient norm. -/
theorem exists_halfHolder_of_spatialHolderHalf_zero {f : Vec3 → E} (hper : SpatiallyPeriodic f)
    (hf : SpatialHolderHalf 0 f) :
    ∃ u : HalfHolder HolderLabels E, (∀ x, HalfHolder.eval (toUnitTorus x) u = f x) ∧
      ‖u‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm 0 f := by
  obtain ⟨hc, hs, hh⟩ := (spatialHolderHalf_zero_iff f).1 hf
  obtain ⟨g, hg⟩ := hper.exists_continuousTorusFunction hc
  let S := spatialSupNorm f
  let H := spatialHolderHalfSeminorm f
  have hS : 0 ≤ S := (norm_nonneg _).trans (norm_le_spatialSupNorm hs 0)
  have hH : 0 ≤ H := by
    have h := le_ciSup hh ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient f (0, 0) = 0 by simp [spatialHolderHalfQuotient]] at h
    exact h
  have hsqrt : 1 ≤ Real.sqrt 2 := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  let M := Real.sqrt 2 * (S + H)
  have hM : 0 ≤ M := by positivity
  have hSM : S ≤ M := by
    calc
      S ≤ Real.sqrt 2 * S := le_mul_of_one_le_left hS hsqrt
      _ ≤ M := mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hH) (Real.sqrt_nonneg _)
  have hHM : H * Real.sqrt 2 ≤ M := by
    rw [mul_comm H]
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hS) (Real.sqrt_nonneg _)
  have hv (z : HolderLabels) : ‖g z‖ ≤ M := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [hg]
    exact (norm_le_spatialSupNorm hs x).trans hSM
  have hD (z w : HolderLabels) : ‖g z - g w‖ ≤ M * Real.sqrt (dist z w) := by
    obtain ⟨x, y, hx, hy, hdist⟩ := holderBridge_exists_close_lifts z w
    have hvalx : g z = f x := by rw [← hx, hg]
    have hvaly : g w = f y := by rw [← hy, hg]
    rw [hvalx, hvaly]
    have hinn := norm_increment_le_spatialHolderHalfSeminorm hh y (x - y)
    rw [add_sub_cancel] at hinn
    calc
      _ ≤ H * Real.sqrt ‖x - y‖ := hinn
      _ ≤ H * Real.sqrt (2 * dist z w) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist) hH
      _ = (H * Real.sqrt 2) * Real.sqrt (dist z w) := by
        rw [Real.sqrt_mul (by norm_num), mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_right hHM (Real.sqrt_nonneg _)
  let u := HalfHolder.ofBound g hv hD
  refine ⟨u, fun x => ?_, ?_⟩
  · exact hg x
  · rw [spatialHolderHalfNorm_zero_eq]
    exact (HalfHolder.norm_le_iff hM).2 ⟨hv, hD⟩


private theorem iteratedFDeriv_one_eq_curry (f : Vec3 → E) (x : Vec3) :
    iteratedFDeriv ℝ 1 f x = (continuousMultilinearCurryFin1 ℝ Vec3 E).symm (fderiv ℝ f x) := by
  ext v
  rw [iteratedFDeriv_one_apply, continuousMultilinearCurryFin1_symm_apply]

private theorem quotient_iteratedFDeriv_one (f : Vec3 → E) :
    spatialHolderHalfQuotient (iteratedFDeriv ℝ 1 f) = spatialHolderHalfQuotient (fderiv ℝ f) := by
  funext p
  unfold spatialHolderHalfQuotient
  rw [iteratedFDeriv_one_eq_curry, iteratedFDeriv_one_eq_curry]
  let e := (continuousMultilinearCurryFin1 ℝ Vec3 E).symm
  change ‖e (fderiv ℝ f (p.1 + p.2)) - e (fderiv ℝ f p.1)‖ / Real.sqrt ‖p.2‖ = _
  rw [← e.map_sub, e.norm_map]

/-- The first-order lift norm is the sum of the order-zero norms of the field and derivative. -/
theorem spatialHolderHalfNorm_one_eq (f : Vec3 → E) :
    spatialHolderHalfNorm 1 f = spatialHolderHalfNorm 0 f + spatialHolderHalfNorm 0 (fderiv ℝ f) := by
  rw [spatialHolderHalfNorm_zero_eq, spatialHolderHalfNorm_zero_eq]
  simp only [spatialHolderHalfNorm, Nat.reduceAdd, Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add,
    spatialSupNorm, spatialHolderHalfSeminorm, norm_iteratedFDeriv_zero, norm_iteratedFDeriv_one,
    quotient_iteratedFDeriv_zero, quotient_iteratedFDeriv_one]

/-- A continuously differentiable lift has first-order half-Hölder regularity when both its
value and spatial derivative have order-zero half-Hölder regularity. -/
theorem spatialHolderHalf_one_iff (f : Vec3 → E) :
    SpatialHolderHalf 1 f ↔ ContDiff ℝ 1 f ∧ SpatialHolderHalf 0 f ∧ SpatialHolderHalf 0 (fderiv ℝ f) := by
  rw [spatialHolderHalf_zero_iff, spatialHolderHalf_zero_iff]
  constructor
  · rintro ⟨hc, h⟩
    refine ⟨hc, ⟨hc.continuous, ?_⟩, ⟨hc.continuous_fderiv one_ne_zero, ?_⟩⟩
    · simpa only [norm_iteratedFDeriv_zero, quotient_iteratedFDeriv_zero] using h 0 (by decide)
    · simpa only [norm_iteratedFDeriv_one, quotient_iteratedFDeriv_one] using h 1 le_rfl
  · rintro ⟨hc, ⟨_, hv⟩, ⟨_, hd⟩⟩
    refine ⟨hc, fun j hj => ?_⟩
    have hj' : j = 0 ∨ j = 1 := by omega
    rcases hj' with rfl | rfl
    · simpa only [norm_iteratedFDeriv_zero, quotient_iteratedFDeriv_zero] using hv
    · simpa only [norm_iteratedFDeriv_one, quotient_iteratedFDeriv_one] using hd


/-- A continuous linear field giving all line derivatives is the Fréchet derivative. -/
theorem hasFDerivAt_of_continuous_lineDerivatives {f : Vec3 → E}
    {D : Vec3 → Vec3 →L[ℝ] E} (hD : Continuous D)
    (hline : ∀ (x v : Vec3) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (x + s • v)) (D (x + t • v) v) t) (x : Vec3) :
    HasFDerivAt f (D x) x := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hnear : ∀ᶠ y in 𝓝 x, ‖D y - D x‖ < ε := by
    filter_upwards [(Metric.tendsto_nhds.mp (hD.continuousAt (x := x))) ε hε] with y hy
    simpa only [dist_eq_norm] using hy
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  refine Metric.mem_nhds_iff.mpr ⟨δ, hδ, fun v hv => ?_⟩
  have hvδ : ‖v‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hv
  let g (t : ℝ) := f (x + t • v) - t • D x v
  have hg (t : ℝ) (_ : t ∈ Icc (0 : ℝ) 1) :
      HasDerivWithinAt g ((D (x + t • v) - D x) v) (Icc 0 1) t := by
    have h := (hline x v t).sub ((hasDerivAt_id t).smul_const (D x v))
    have hfun : ((fun s : ℝ => f (x + s • v)) - (fun s : ℝ => s • D x v)) = g := rfl
    simp only [id_eq] at h
    rw [hfun] at h
    simpa only [one_smul, sub_apply] using h.hasDerivWithinAt (s := Icc 0 1)
  have hb (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) : ‖(D (x + t • v) - D x) v‖ ≤ ε * ‖v‖ := by
    have hsmall : x + t • v ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_of_le_one_left (norm_nonneg v) ht.2.le).trans_lt hvδ
    exact ((D (x + t • v) - D x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hball hsmall).le (norm_nonneg v))
  have h := norm_image_sub_le_of_norm_deriv_le_segment_01' hg hb
  change ‖f (x + v) - f x - D x v‖ ≤ ε * ‖v‖
  simpa only [g, one_smul, zero_smul, add_zero, sub_zero, sub_right_comm] using h


/-- A continuous linear input derivative evaluated in a spatial direction. -/
def torusHalfHolderDirection (v : Vec3) (H : HalfHolder HolderLabels (Vec3 →L[ℝ] E)) :
    HalfHolder HolderLabels E := HalfHolder.map (ContinuousLinearMap.apply ℝ E v) H

@[simp]
theorem eval_torusHalfHolderDirection (v : Vec3) (H : HalfHolder HolderLabels (Vec3 →L[ℝ] E))
    (a : HolderLabels) : HalfHolder.eval a (torusHalfHolderDirection v H) = (HalfHolder.eval a H) v := rfl

/-- Apply a scalar-domain spatial operator to the columns of a derivative field. -/
def torusHalfHolderProjectedDerivative (P : HalfHolder HolderLabels E →L[ℝ] HalfHolder HolderLabels E)
    (H : HalfHolder HolderLabels (Vec3 →L[ℝ] E)) : HalfHolder HolderLabels (Vec3 →L[ℝ] E) :=
  ∑ i : Fin 3, HalfHolder.map (ContinuousLinearMap.smulRightL ℝ Vec3 E (EuclideanSpace.proj i))
    (P (torusHalfHolderDirection (EuclideanSpace.single i 1) H))

/-- Projecting the columns agrees with projecting any directional derivative. -/
theorem eval_torusHalfHolderProjectedDerivative
    (P : HalfHolder HolderLabels E →L[ℝ] HalfHolder HolderLabels E)
    (H : HalfHolder HolderLabels (Vec3 →L[ℝ] E)) (a : HolderLabels) (v : Vec3) :
    HalfHolder.eval a (torusHalfHolderProjectedDerivative P H) v =
      HalfHolder.eval a (P (torusHalfHolderDirection v H)) := by
  have hbasis : (∑ i : Fin 3, v i • EuclideanSpace.single i (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
  have hd : torusHalfHolderDirection v H =
      ∑ i : Fin 3, v i • torusHalfHolderDirection (EuclideanSpace.single i 1) H := by
    apply HalfHolder.ext
    intro b
    simp only [eval_torusHalfHolderDirection, map_sum, map_smul]
    conv_lhs => rw [← hbasis, map_sum]
    simp only [map_smul]
  rw [hd]
  simp only [torusHalfHolderProjectedDerivative, map_sum, map_smul, HalfHolder.eval_map,
    ContinuousLinearMap.smulRightL_apply_apply, ContinuousLinearMap.smulRight_apply, sum_apply]
  rfl

/-- Projecting all directional derivatives costs at most the operator norm of the projection. -/
theorem norm_torusHalfHolderProjectedDerivative_le
    (P : HalfHolder HolderLabels E →L[ℝ] HalfHolder HolderLabels E)
    (H : HalfHolder HolderLabels (Vec3 →L[ℝ] E)) :
    ‖torusHalfHolderProjectedDerivative P H‖ ≤ ‖P‖ * ‖H‖ := by
  let G := torusHalfHolderProjectedDerivative P H
  let M := ‖P‖ * ‖H‖
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hb (v : Vec3) : ‖P (torusHalfHolderDirection v H)‖ ≤ M * ‖v‖ := by
    have heval : ‖(ContinuousLinearMap.apply ℝ E v : (Vec3 →L[ℝ] E) →L[ℝ] E)‖ ≤ ‖v‖ :=
      ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) fun L => by
        simpa only [ContinuousLinearMap.apply_apply, mul_comm ‖v‖ ‖L‖] using L.le_opNorm v
    have hmap := (HalfHolder.map (X := HolderLabels) (ContinuousLinearMap.apply ℝ E v)).le_opNorm H
    have hnorm := HalfHolder.norm_map_le (X := HolderLabels) (ContinuousLinearMap.apply ℝ E v)
    have hdir : ‖torusHalfHolderDirection v H‖ ≤ ‖v‖ * ‖H‖ :=
      hmap.trans (mul_le_mul_of_nonneg_right (hnorm.trans heval) (norm_nonneg H))
    exact ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left hdir (norm_nonneg P))).trans_eq (by
      dsimp only [M]; ring)
  apply (HalfHolder.norm_le_iff hM).2
  constructor
  · intro a
    change ‖HalfHolder.eval a G‖ ≤ M
    apply ContinuousLinearMap.opNorm_le_bound _ hM
    intro v
    rw [eval_torusHalfHolderProjectedDerivative]
    exact (((HalfHolder.norm_le_iff (norm_nonneg (P (torusHalfHolderDirection v H)))).1 le_rfl).1 a).trans (hb v)
  · intro a b
    change ‖HalfHolder.eval a G - HalfHolder.eval b G‖ ≤ M * Real.sqrt (dist a b)
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hM (Real.sqrt_nonneg _))
    intro v
    rw [sub_apply, eval_torusHalfHolderProjectedDerivative, eval_torusHalfHolderProjectedDerivative]
    have h := ((HalfHolder.norm_le_iff (norm_nonneg (P (torusHalfHolderDirection v H)))).1 le_rfl).2 a b
    exact (h.trans (mul_le_mul_of_nonneg_right (hb v) (Real.sqrt_nonneg _))).trans_eq (by ring)


/-- Apply a torus operator to the descent of a periodic half-Hölder lift. -/
def halfHolderProjectionLift (P : HalfHolder HolderLabels E →L[ℝ] HalfHolder HolderLabels E)
    (f : Vec3 → E) : Vec3 → E := by
  classical
  exact if hf : SpatiallyPeriodic f ∧ SpatialHolderHalf 0 f then
    fun x => HalfHolder.eval (toUnitTorus x)
      (P (exists_halfHolder_of_spatialHolderHalf_zero hf.1 hf.2).choose)
  else fun _ => 0

private theorem holderBridge_toUnitTorus_add (x y : Vec3) :
    toUnitTorus (x + y) = toUnitTorus x + toUnitTorus y := by
  funext i
  exact AddCircle.coe_add 1 (x i) (y i)

/-- An order-zero torus operator commuting with line differentiation is bounded
on periodic first-order half-Hölder lifts. -/
theorem spatialHolderHalf_one_halfHolderProjectionLift
    (P : HalfHolder HolderLabels E →L[ℝ] HalfHolder HolderLabels E)
    (hP : ∀ (v : Vec3) (u du : HalfHolder HolderLabels E),
      (∀ (a : HolderLabels) (t : ℝ), HasDerivAt
        (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) u)
        (HalfHolder.eval (a + toUnitTorus (t • v)) du) t) →
      ∀ (a : HolderLabels) (t : ℝ), HasDerivAt
        (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) (P u))
        (HalfHolder.eval (a + toUnitTorus (t • v)) (P du)) t)
    {f : Vec3 → E} (hfper : SpatiallyPeriodic f) (hf : SpatialHolderHalf 1 f) :
    SpatialHolderHalf 1 (halfHolderProjectionLift P f) ∧
      spatialHolderHalfNorm 1 (halfHolderProjectionLift P f) ≤
        (2 * Real.sqrt 2 * ‖P‖) * spatialHolderHalfNorm 1 f := by
  classical
  obtain ⟨hfDiff, hf0, hfD0⟩ := (spatialHolderHalf_one_iff f).mp hf
  have hfDper : SpatiallyPeriodic (fderiv ℝ f) := by
    intro n x
    rw [← fderiv_comp_add_right]
    exact congrArg (fun g : Vec3 → E => fderiv ℝ g x) (funext (hfper n))
  let u := (exists_halfHolder_of_spatialHolderHalf_zero hfper hf0).choose
  let du := (exists_halfHolder_of_spatialHolderHalf_zero hfDper hfD0).choose
  have hu : (∀ x, HalfHolder.eval (toUnitTorus x) u = f x) ∧
      ‖u‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm 0 f :=
    (exists_halfHolder_of_spatialHolderHalf_zero hfper hf0).choose_spec
  have hdu : (∀ x, HalfHolder.eval (toUnitTorus x) du = fderiv ℝ f x) ∧
      ‖du‖ ≤ Real.sqrt 2 * spatialHolderHalfNorm 0 (fderiv ℝ f) :=
    (exists_halfHolder_of_spatialHolderHalf_zero hfDper hfD0).choose_spec
  let g := fun x => HalfHolder.eval (toUnitTorus x) (P u)
  let D := fun x => HalfHolder.eval (toUnitTorus x) (torusHalfHolderProjectedDerivative P du)
  have hgProj : halfHolderProjectionLift P f = g := by
    unfold halfHolderProjectionLift
    rw [dite_eq_left (show SpatiallyPeriodic f ∧ SpatialHolderHalf 0 f from ⟨hfper, hf0⟩)]
  rw [hgProj]
  have hg0 := spatialHolderHalf_zero_of_halfHolder (P u)
  have hD0 := spatialHolderHalf_zero_of_halfHolder (torusHalfHolderProjectedDerivative P du)
  have hline (x v : Vec3) (t : ℝ) :
      HasDerivAt (fun s : ℝ => g (x + s • v)) (D (x + t • v) v) t := by
    have hin (a : HolderLabels) (r : ℝ) : HasDerivAt
        (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) u)
        (HalfHolder.eval (a + toUnitTorus (r • v)) (torusHalfHolderDirection v du)) r := by
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective a
      simp only [← holderBridge_toUnitTorus_add, hu.1, eval_torusHalfHolderDirection, hdu.1]
      have hw : HasDerivAt (fun s : ℝ => y + s • v) v r := by
        simpa only [id_eq, one_smul] using ((hasDerivAt_id r).smul_const v).const_add y
      exact ((hfDiff.differentiable one_ne_zero (y + r • v)).hasFDerivAt).comp_hasDerivAt r hw
    have hout := hP v u (torusHalfHolderDirection v du) hin (toUnitTorus x) t
    simpa only [g, D, holderBridge_toUnitTorus_add, eval_torusHalfHolderProjectedDerivative] using hout
  have hDiff (x : Vec3) : HasFDerivAt g (D x) x :=
    hasFDerivAt_of_continuous_lineDerivatives ((spatialHolderHalf_zero_iff D).1 hD0.1).1 hline x
  have hDeq : fderiv ℝ g = D := funext fun x => (hDiff x).fderiv
  have hCg : ContDiff ℝ 1 g := contDiff_one_iff_fderiv.mpr
    ⟨fun x => (hDiff x).differentiableAt, by rw [hDeq]; exact ((spatialHolderHalf_zero_iff D).1 hD0.1).1⟩
  constructor
  · apply (spatialHolderHalf_one_iff g).2
    exact ⟨hCg, hg0.1, hDeq.symm ▸ hD0.1⟩
  · rw [spatialHolderHalfNorm_one_eq, spatialHolderHalfNorm_one_eq, hDeq, mul_add]
    apply add_le_add
    · calc
        _ ≤ 2 * ‖P u‖ := hg0.2
        _ ≤ 2 * (‖P‖ * (Real.sqrt 2 * spatialHolderHalfNorm 0 f)) :=
          mul_le_mul_of_nonneg_left ((P.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left hu.2 (norm_nonneg P))) (by norm_num)
        _ = _ := by ring
    · calc
        _ ≤ 2 * ‖torusHalfHolderProjectedDerivative P du‖ := hD0.2
        _ ≤ 2 * (‖P‖ * (Real.sqrt 2 * spatialHolderHalfNorm 0 (fderiv ℝ f))) :=
          mul_le_mul_of_nonneg_left ((norm_torusHalfHolderProjectedDerivative_le P du).trans
            (mul_le_mul_of_nonneg_left hdu.2 (norm_nonneg P))) (by norm_num)
        _ = _ := by ring

end

end TorusEuler

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The actual periodic Leray projection commutes with translations by its Fourier law. -/
private theorem periodicLeray_translate (b : Labels) (f : HalfHolder Labels Vec3) :
    endpointStrongSpatialLeray (HalfHolder.torusTranslate b f) =
      HalfHolder.torusTranslate b (endpointStrongSpatialLeray f) :=
  halfHolder_torusTranslate_commutes_of_complexFourierCoefficient endpointSpatialComplexification
    endpointStrongSpatialLeray
    (fun k => endpointSpatialComplexification.extendOperator (angularLeray (latticeVector k)))
    endpointStrongSpatialLeray_complexCoefficient b f

/-- The actual periodic Leray projection commutes with differentiation along torus lines. -/
theorem endpointStrongSpatialLeray_preserves_torusDirectionalDerivative
    (v : Vec3) (f df : HalfHolder Labels Vec3)
    (hf : ∀ (a : Labels) (t : ℝ), HasDerivAt
      (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) f)
      (HalfHolder.eval (a + toUnitTorus (t • v)) df) t) :
    ∀ (a : Labels) (t : ℝ), HasDerivAt
      (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) (endpointStrongSpatialLeray f))
      (HalfHolder.eval (a + toUnitTorus (t • v)) (endpointStrongSpatialLeray df)) t :=
  freezingProjection_preserves_torusDirectionalDerivative endpointStrongSpatialLeray periodicRealLeray
    endpointStrongSpatialLeray_agrees_L2 v
    (fun h f => periodicLeray_translate (toUnitTorus (h • v)) f) f df hf

/-- The actual half-Hölder Leray projection, expressed as a map on periodic Euclidean lifts. -/
def periodicLerayHolderLift : (Vec3 → Vec3) → (Vec3 → Vec3) :=
  halfHolderProjectionLift endpointStrongSpatialLeray

/-- On the lift of a torus half-Hölder field, the projection is its actual torus Leray projection. -/
theorem periodicLerayHolderLift_pullback (u : HalfHolder Labels Vec3) :
    periodicLerayHolderLift (fun x => HalfHolder.eval (toUnitTorus x) u) =
      fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray u) := by
  classical
  let f := fun x => HalfHolder.eval (toUnitTorus x) u
  have hf : SpatiallyPeriodic f := by
    intro n _
    exact congrArg (fun a => HalfHolder.eval a u) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hf0 := (spatialHolderHalf_zero_of_halfHolder u).1
  let h := exists_halfHolder_of_spatialHolderHalf_zero hf hf0
  have hs : h.choose = u := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact h.choose_spec.1 x
  unfold periodicLerayHolderLift halfHolderProjectionLift
  rw [dite_eq_left (show SpatiallyPeriodic f ∧ SpatialHolderHalf 0 f from ⟨hf, hf0⟩)]
  exact congrArg (fun w => fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray w)) hs

/-- The actual periodic Leray lift is additive on its spatial half-Hölder domain. -/
theorem periodicLerayHolderLift_add {f g : Vec3 → Vec3}
    (hfper : SpatiallyPeriodic f) (hgper : SpatiallyPeriodic g)
    (hf : SpatialHolderHalf 0 f) (hg : SpatialHolderHalf 0 g) :
    periodicLerayHolderLift (f + g) = periodicLerayHolderLift f + periodicLerayHolderLift g := by
  obtain ⟨u, hu, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hfper hf
  obtain ⟨v, hv, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hgper hg
  have huv (x : Vec3) : HalfHolder.eval (toUnitTorus x) (u + v) = (f + g) x := by rw [map_add, hu, hv]; rfl
  rw [← funext huv, ← funext hu, ← funext hv, periodicLerayHolderLift_pullback,
    periodicLerayHolderLift_pullback, periodicLerayHolderLift_pullback, map_add]
  funext x
  exact (HalfHolder.eval (toUnitTorus x)).map_add _ _

/-- The periodic Leray Hölder bound used in the estimate of (5.58). -/
theorem periodicLerayHolderLift_holder_one (f : Vec3 → Vec3) (hfper : SpatiallyPeriodic f)
    (hf : SpatialHolderHalf 1 f) : SpatialHolderHalf 1 (periodicLerayHolderLift f) ∧
      spatialHolderHalfNorm 1 (periodicLerayHolderLift f) ≤
        (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) * spatialHolderHalfNorm 1 f :=
  spatialHolderHalf_one_halfHolderProjectionLift endpointStrongSpatialLeray
    endpointStrongSpatialLeray_preserves_torusDirectionalDerivative hfper hf

/-- The estimates for the velocity tail and the actual projected residual, in the time-uniform
spatial norms of Proposition 5.11. The residual coefficient is independent of depth. -/
theorem truncatedEulerLerayProjectedResidual_time_bound {ι : Type*} [Nonempty ι]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hs : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) :
    ∃ Cr : ℝ, 0 ≤ Cr ∧ ∀ (P : ℕ), 2 ≤ P →
      ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ (Λ : ℝ), 1 ≤ Λ →
        ∀ gV gRV : ι → C(Labels, Vec3),
        let V := fun t x => gV t (toUnitTorus x)
        let RV := fun t x => gRV t (toUnitTorus x)
        (∀ t, SpatialHolderHalf P (V t)) →
        (∀ t, SpatialHolderHalf 1 (RV t)) →
        BddAbove (range fun t => spatialHolderHalfNorm P (V t)) →
        BddAbove (range fun t => spatialHolderHalfNorm 1 (RV t)) →
        let v := fun t => (fun x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)) - V t
        let res := fun t => truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t)
        let ε := Λ ^ ((2 : ℤ) - P) * (1 + (⨆ t, spatialHolderHalfNorm P (V t)))^2
        (⨆ t, spatialHolderHalfNorm 2 (v t)) ≤ Ct * ε ∧
        (⨆ t, spatialHolderHalfNorm 1 (res t)) ≤ Cr * (⨆ t, spatialHolderHalfNorm 1 (RV t)) + Ct * ε := by
  let Cproj := 2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖
  let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) *
    (1 + cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1))
  have hCproj : 0 ≤ Cproj := by dsimp only [Cproj]; positivity
  have hC : 0 ≤ cutoffHolderTailUniformConstant (cutoffSchwartzKernel hψ hs) 1 := by
    unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
    positivity
  refine ⟨Cr, ?_, fun P hP => ?_⟩
  · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (by linarith))
  · exact truncatedEulerProjectedResidual_time_bound periodicLerayHolderLift hCproj
      periodicLerayHolderLift_holder_one hψ hs hunit P hP

end

end TorusEuler

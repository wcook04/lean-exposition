import TorusEuler.PeriodicLerayHolderLift

/-! Iterating the directional derivative estimate for the periodic half-Hölder Leray lift. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

private abbrev JetLabels := UnitAddTorus (Fin 3)

universe u

/-- A torus operator projects a derivative field by acting on its spatial directions. -/
def torusHalfHolderDerivativeOperator {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) :
    HalfHolder JetLabels (Vec3 →L[ℝ] E) →L[ℝ] HalfHolder JetLabels (Vec3 →L[ℝ] E) :=
  ∑ i : Fin 3, (HalfHolder.map (X := JetLabels)
    (ContinuousLinearMap.smulRightL ℝ Vec3 E (EuclideanSpace.proj i))).comp
    (P.comp (HalfHolder.map (ContinuousLinearMap.apply ℝ E (EuclideanSpace.single i 1))))

@[simp]
theorem torusHalfHolderDerivativeOperator_apply {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E)
    (H : HalfHolder JetLabels (Vec3 →L[ℝ] E)) :
    torusHalfHolderDerivativeOperator P H = torusHalfHolderProjectedDerivative P H := by
  simp [torusHalfHolderDerivativeOperator, torusHalfHolderProjectedDerivative, torusHalfHolderDirection]

/-- Directionwise extension costs no additional operator-norm constant. -/
theorem norm_torusHalfHolderDerivativeOperator_le {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) :
    ‖torusHalfHolderDerivativeOperator P‖ ≤ ‖P‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.opNorm_nonneg
  intro H
  rw [torusHalfHolderDerivativeOperator_apply]
  exact norm_torusHalfHolderProjectedDerivative_le P H

/-- The directional differentiation property on actual torus lines. -/
def CommutesTorusLineDerivatives {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) : Prop :=
  ∀ (v : Vec3) (f df : HalfHolder JetLabels E),
    (∀ (a : JetLabels) (t : ℝ), HasDerivAt
      (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) f)
      (HalfHolder.eval (a + toUnitTorus (t • v)) df) t) →
    ∀ (a : JetLabels) (t : ℝ), HasDerivAt
      (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) (P f))
      (HalfHolder.eval (a + toUnitTorus (t • v)) (P df)) t

/-- The directionwise extension still commutes with actual differentiation along torus lines. -/
theorem CommutesTorusLineDerivatives.derivativeOperator {E : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E}
    (hP : CommutesTorusLineDerivatives P) :
    CommutesTorusLineDerivatives (torusHalfHolderDerivativeOperator P) := by
  intro v f df hline a t
  let e (i : Fin 3) := EuclideanSpace.single i (1 : ℝ)
  let L (i : Fin 3) := ContinuousLinearMap.smulRightL ℝ Vec3 E (EuclideanSpace.proj i)
  have hin (i : Fin 3) (b : JetLabels) (r : ℝ) : HasDerivAt
      (fun s : ℝ => HalfHolder.eval (b + toUnitTorus (s • v)) (torusHalfHolderDirection (e i) f))
      (HalfHolder.eval (b + toUnitTorus (r • v)) (torusHalfHolderDirection (e i) df)) r := by
    exact ((ContinuousLinearMap.apply ℝ E (e i)).hasFDerivAt).comp_hasDerivAt r (hline b r)
  have hterm (i : Fin 3) : HasDerivAt
      (fun s : ℝ => L i (HalfHolder.eval (a + toUnitTorus (s • v))
        (P (torusHalfHolderDirection (e i) f))))
      (L i (HalfHolder.eval (a + toUnitTorus (t • v))
        (P (torusHalfHolderDirection (e i) df)))) t :=
    (L i).hasFDerivAt.comp_hasDerivAt t
      (hP v (torusHalfHolderDirection (e i) f) (torusHalfHolderDirection (e i) df) (hin i) a t)
  simpa only [torusHalfHolderDerivativeOperator_apply, torusHalfHolderProjectedDerivative, map_sum,
    HalfHolder.eval_map, e, L] using
    (HasDerivAt.fun_sum (u := Finset.univ) (fun i _ => hterm i))

private theorem projectionJets_toUnitTorus_add (x y : Vec3) :
    toUnitTorus (x + y) = toUnitTorus x + toUnitTorus y := by
  funext i
  exact AddCircle.coe_add 1 (x i) (y i)

private theorem projectionJets_fderiv_periodic {E : Type u} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : Vec3 → E} (h : SpatiallyPeriodic f) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n x
  rw [← fderiv_comp_add_right]
  exact congrArg (fun g : Vec3 → E => fderiv ℝ g x) (funext (h n))

/-- The lifted order-zero projection determines the same torus representative pointwise. -/
theorem halfHolderProjectionLift_eq_of_descent {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) {f : Vec3 → E}
    (hper : SpatiallyPeriodic f) (hf : SpatialHolderHalf 0 f)
    (w : HalfHolder JetLabels E) (hw : ∀ x, HalfHolder.eval (toUnitTorus x) w = f x) :
    halfHolderProjectionLift P f = fun x => HalfHolder.eval (toUnitTorus x) (P w) := by
  classical
  let h := exists_halfHolder_of_spatialHolderHalf_zero hper hf
  have heq : h.choose = w := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact (h.choose_spec.1 x).trans (hw x).symm
  unfold halfHolderProjectionLift
  rw [dite_eq_left (show SpatiallyPeriodic f ∧ SpatialHolderHalf 0 f from ⟨hper, hf⟩)]
  exact congrArg (fun z => fun x => HalfHolder.eval (toUnitTorus x) (P z)) heq

/-- Differentiating the lift commutes with projecting its actual derivative field. -/
theorem fderiv_halfHolderProjectionLift {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) (hP : CommutesTorusLineDerivatives P)
    {f : Vec3 → E} (hper : SpatiallyPeriodic f) (hf : SpatialHolderHalf 1 f) :
    fderiv ℝ (halfHolderProjectionLift P f) =
      halfHolderProjectionLift (torusHalfHolderDerivativeOperator P) (fderiv ℝ f) := by
  obtain ⟨hfDiff, hf0, hfD0⟩ := (spatialHolderHalf_one_iff f).mp hf
  have hperD := projectionJets_fderiv_periodic hper
  obtain ⟨q, hq, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper hf0
  obtain ⟨dq, hdq, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hperD hfD0
  rw [halfHolderProjectionLift_eq_of_descent P hper hf0 q hq,
    halfHolderProjectionLift_eq_of_descent (torusHalfHolderDerivativeOperator P) hperD hfD0 dq hdq]
  let g := fun x => HalfHolder.eval (toUnitTorus x) (P q)
  let D := fun x => HalfHolder.eval (toUnitTorus x) (torusHalfHolderDerivativeOperator P dq)
  have hD0 := spatialHolderHalf_zero_of_halfHolder (torusHalfHolderDerivativeOperator P dq)
  have hline (x v : Vec3) (t : ℝ) :
      HasDerivAt (fun s : ℝ => g (x + s • v)) (D (x + t • v) v) t := by
    have hin (a : JetLabels) (r : ℝ) : HasDerivAt
        (fun s : ℝ => HalfHolder.eval (a + toUnitTorus (s • v)) q)
        (HalfHolder.eval (a + toUnitTorus (r • v)) (torusHalfHolderDirection v dq)) r := by
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective a
      simp only [← projectionJets_toUnitTorus_add, hq, eval_torusHalfHolderDirection, hdq]
      have hw : HasDerivAt (fun s : ℝ => y + s • v) v r := by
        simpa only [id_eq, one_smul] using ((hasDerivAt_id r).smul_const v).const_add y
      exact ((hfDiff.differentiable one_ne_zero (y + r • v)).hasFDerivAt).comp_hasDerivAt r hw
    have hout := hP v q (torusHalfHolderDirection v dq) hin (toUnitTorus x) t
    simpa only [g, D, projectionJets_toUnitTorus_add, torusHalfHolderDerivativeOperator_apply,
      eval_torusHalfHolderProjectedDerivative] using hout
  funext x
  exact (hasFDerivAt_of_continuous_lineDerivatives
    ((spatialHolderHalf_zero_iff D).1 hD0.1).1 hline x).fderiv


section Order

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem holderJet_succ_sup_eq (f : Vec3 → E) (j : ℕ) :
    (fun x => ‖iteratedFDeriv ℝ j (fderiv ℝ f) x‖) =
      fun x => ‖iteratedFDeriv ℝ (j + 1) f x‖ :=
  funext fun _ => norm_iteratedFDeriv_fderiv

private theorem holderJet_succ_quotient_eq (f : Vec3 → E) (j : ℕ) :
    spatialHolderHalfQuotient (iteratedFDeriv ℝ j (fderiv ℝ f)) =
      spatialHolderHalfQuotient (iteratedFDeriv ℝ (j + 1) f) := by
  funext p
  unfold spatialHolderHalfQuotient
  let c := (continuousMultilinearCurryRightEquiv' ℝ j Vec3 E).symm
  rw [iteratedFDeriv_succ_eq_comp_right, iteratedFDeriv_succ_eq_comp_right]
  change _ = ‖c (iteratedFDeriv ℝ j (fderiv ℝ f) (p.1 + p.2)) -
    c (iteratedFDeriv ℝ j (fderiv ℝ f) p.1)‖ / Real.sqrt ‖p.2‖
  rw [← c.map_sub, c.norm_map]

/-- Higher-order lift regularity splits into order zero and one fewer derivative of the gradient. -/
theorem spatialHolderHalf_succ_iff (m : ℕ) (f : Vec3 → E) :
    SpatialHolderHalf (m + 1) f ↔ Differentiable ℝ f ∧
      SpatialHolderHalf 0 f ∧ SpatialHolderHalf m (fderiv ℝ f) := by
  have hc : ContDiff ℝ (↑(m + 1 : ℕ)) f ↔
      Differentiable ℝ f ∧ ContDiff ℝ m (fderiv ℝ f) := by
    rw [Nat.cast_add, Nat.cast_one, contDiff_succ_iff_fderiv]
    simp
  rw [SpatialHolderHalf, hc]
  constructor
  · rintro ⟨⟨h, hD⟩, hj⟩
    refine ⟨h, ⟨contDiff_zero.mpr h.continuous, fun j hk => ?_⟩, ⟨hD, fun j hk => ?_⟩⟩
    · exact hj j (hk.trans (Nat.zero_le _))
    · rw [holderJet_succ_sup_eq, holderJet_succ_quotient_eq]
      exact hj (j + 1) (Nat.succ_le_succ hk)
  · rintro ⟨h, h0, hD⟩
    refine ⟨⟨h, hD.1⟩, fun j hj => ?_⟩
    cases j with
    | zero => exact h0.2 0 le_rfl
    | succ j =>
      rw [← holderJet_succ_sup_eq, ← holderJet_succ_quotient_eq]
      exact hD.2 j (Nat.le_of_succ_le_succ hj)

/-- The higher-order norm splits into the order-zero norm and the norm of the derivative. -/
theorem spatialHolderHalfNorm_succ_eq (m : ℕ) (f : Vec3 → E) :
    spatialHolderHalfNorm (m + 1) f = spatialHolderHalfNorm 0 f + spatialHolderHalfNorm m (fderiv ℝ f) := by
  unfold spatialHolderHalfNorm
  rw [Finset.sum_range_succ', add_comm]
  simp only [Nat.zero_add, Finset.sum_range_one]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  unfold spatialSupNorm spatialHolderHalfSeminorm
  rw [holderJet_succ_sup_eq, holderJet_succ_quotient_eq]

/-- The lift of an order-zero torus operator is periodic. -/
theorem spatiallyPeriodic_halfHolderProjectionLift
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) (f : Vec3 → E) :
    SpatiallyPeriodic (halfHolderProjectionLift P f) := by
  classical
  unfold halfHolderProjectionLift
  split
  · intro n x
    exact congrArg _ ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  · exact fun _ _ => rfl

private theorem halfHolderProjectionLift_orderZero
    (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E) {f : Vec3 → E}
    (hper : SpatiallyPeriodic f) (hf : SpatialHolderHalf 0 f) :
    SpatialHolderHalf 0 (halfHolderProjectionLift P f) ∧
      spatialHolderHalfNorm 0 (halfHolderProjectionLift P f) ≤
        (2 * Real.sqrt 2 * ‖P‖) * spatialHolderHalfNorm 0 f := by
  obtain ⟨u, hu, hNu⟩ := exists_halfHolder_of_spatialHolderHalf_zero hper hf
  rw [halfHolderProjectionLift_eq_of_descent P hper hf u hu]
  have h := spatialHolderHalf_zero_of_halfHolder (P u)
  refine ⟨h.1, h.2.trans ?_⟩
  calc
    _ ≤ 2 * (‖P‖ * (Real.sqrt 2 * spatialHolderHalfNorm 0 f)) :=
      mul_le_mul_of_nonneg_left ((P.le_opNorm u).trans (mul_le_mul_of_nonneg_left hNu (norm_nonneg P)))
        (by norm_num)
    _ = _ := by ring

/-- The finite spatial half-Hölder norm is nonnegative on its domain. -/
theorem nonneg_spatialHolderHalfNorm (m : ℕ) (f : Vec3 → E) (hf : SpatialHolderHalf m f) :
    0 ≤ spatialHolderHalfNorm m f := by
  unfold spatialHolderHalfNorm
  apply Finset.sum_nonneg
  intro j hj
  have h := hf.2 j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
  refine add_nonneg ((norm_nonneg _).trans (norm_le_spatialSupNorm h.1 0)) ?_
  have hp := le_ciSup h.2 ((0 : Vec3), (0 : Vec3))
  rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) (0, 0) = 0 by
    simp [spatialHolderHalfQuotient]] at hp
  exact hp

end Order

/-- Every Hölder jet is bounded by the same operator-norm coefficient. -/
theorem spatialHolderHalf_halfHolderProjectionLift (m : ℕ) :
    ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E],
    ∀ (P : HalfHolder JetLabels E →L[ℝ] HalfHolder JetLabels E)
      (_ : CommutesTorusLineDerivatives P) {f : Vec3 → E}
      (_ : SpatiallyPeriodic f) (_ : SpatialHolderHalf m f),
      SpatialHolderHalf m (halfHolderProjectionLift P f) ∧
        spatialHolderHalfNorm m (halfHolderProjectionLift P f) ≤
          (2 * Real.sqrt 2 * ‖P‖) * spatialHolderHalfNorm m f := by
  induction m with
  | zero =>
    intro E _ _ P _ _ hfper hf
    exact halfHolderProjectionLift_orderZero P hfper hf
  | succ m ih =>
    intro E _ _ P hP f hfper hf
    obtain ⟨_, hf0, hfD⟩ := (spatialHolderHalf_succ_iff m f).mp hf
    have hf1 : SpatialHolderHalf 1 f := by
      refine ⟨hf.1.of_le ?_, fun j hj => hf.2 j (hj.trans (Nat.succ_le_succ (Nat.zero_le _)))⟩
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    have hG0 := halfHolderProjectionLift_orderZero P hfper hf0
    have hG1 := spatialHolderHalf_one_halfHolderProjectionLift P hP hfper hf1
    have hDer := fderiv_halfHolderProjectionLift P hP hfper hf1
    have hD := ih (torusHalfHolderDerivativeOperator P) hP.derivativeOperator
      (projectionJets_fderiv_periodic hfper) hfD
    constructor
    · exact (spatialHolderHalf_succ_iff m _).mpr
        ⟨hG1.1.1.differentiable one_ne_zero, hG0.1, hDer.symm ▸ hD.1⟩
    · rw [spatialHolderHalfNorm_succ_eq, spatialHolderHalfNorm_succ_eq, hDer, mul_add]
      apply add_le_add hG0.2
      exact hD.2.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (norm_torusHalfHolderDerivativeOperator_le P) (by positivity))
        (nonneg_spatialHolderHalfNorm m (fderiv ℝ f) hfD))


/-- The actual periodic Leray projection preserves every spatial half-Hölder order. -/
theorem spatialHolderHalf_periodicLerayHolderLift {m : ℕ} {f : Vec3 → Vec3}
    (hfper : SpatiallyPeriodic f) (hf : SpatialHolderHalf m f) :
    SpatialHolderHalf m (periodicLerayHolderLift f) ∧
      spatialHolderHalfNorm m (periodicLerayHolderLift f) ≤
        (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) * spatialHolderHalfNorm m f :=
  spatialHolderHalf_halfHolderProjectionLift m endpointStrongSpatialLeray
    endpointStrongSpatialLeray_preserves_torusDirectionalDerivative hfper hf

/-- The actual Leray lift is spatially periodic. -/
theorem spatiallyPeriodic_periodicLerayHolderLift (f : Vec3 → Vec3) :
    SpatiallyPeriodic (periodicLerayHolderLift f) :=
  spatiallyPeriodic_halfHolderProjectionLift endpointStrongSpatialLeray f

/-- The actual Leray lift commutes with projecting the Fréchet derivative columnwise. -/
theorem fderiv_periodicLerayHolderLift {f : Vec3 → Vec3} (hfper : SpatiallyPeriodic f)
    (hf : SpatialHolderHalf 1 f) :
    fderiv ℝ (periodicLerayHolderLift f) =
      halfHolderProjectionLift (torusHalfHolderDerivativeOperator endpointStrongSpatialLeray) (fderiv ℝ f) :=
  fderiv_halfHolderProjectionLift endpointStrongSpatialLeray
    endpointStrongSpatialLeray_preserves_torusDirectionalDerivative hfper hf

end

end TorusEuler

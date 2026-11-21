import TorusEuler.EndpointPhysicalJetData

/-! Strong spatial differentiation commutes with closed-slab time jets. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem continuous_segmentEval (f : HalfHolder A E) (a : A) (u : Vec3) (h : ℝ) :
    Continuous (fun s : ℝ => HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f) :=
  f.val.1.continuous.comp
    (continuous_const.add (lipschitzWith_toUnitTorus.continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)))

private def segmentEvalAverage (a : A) (u : Vec3) (h : ℝ) : HalfHolder A E →L[ℝ] E := by
  let avg : HalfHolder A E →ₗ[ℝ] E :=
    { toFun := fun f => ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f
      map_add' := by
        intro f g
        simp only [map_add]
        exact intervalIntegral.integral_add ((continuous_segmentEval f a u h).intervalIntegrable 0 1)
          ((continuous_segmentEval g a u h).intervalIntegrable 0 1)
      map_smul' := by
        intro c f
        simp only [map_smul, RingHom.id_apply, intervalIntegral.integral_smul] }
  refine avg.mkContinuous 1 fun f => ?_
  change ‖∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f‖ ≤ 1 * ‖f‖
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun s => HalfHolder.eval (a + toUnitTorus ((s * h) • u)) f)
    (fun s _ => ((HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl).1 (a + toUnitTorus ((s * h) • u)))
  simpa only [one_mul, sub_zero, abs_one, mul_one] using hb

private theorem norm_segmentEvalAverage_sub_le (z : HalfHolder A E) (a : A) (u : Vec3) (h : ℝ) :
    ‖segmentEvalAverage a u h z - HalfHolder.eval a z‖ ≤ ‖z‖ * Real.sqrt (|h| * ‖u‖) := by
  change ‖(∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z) -
        HalfHolder.eval a z‖ ≤ _
  have hZ := (continuous_segmentEval z a u h).intervalIntegrable (μ := MeasureTheory.volume) (0 : ℝ) 1
  have heval : (∫ _s in (0 : ℝ)..1, HalfHolder.eval a z) = HalfHolder.eval a z := by simp
  nth_rw 1 [← heval]
  rw [← intervalIntegral.integral_sub hZ intervalIntegrable_const]
  have hbound (s : ℝ) (hs : s ∈ Set.uIoc (0 : ℝ) 1) :
      ‖HalfHolder.eval (a + toUnitTorus ((s * h) • u)) z - HalfHolder.eval a z‖ ≤
        ‖z‖ * Real.sqrt (|h| * ‖u‖) := by
    rw [uIoc_of_le zero_le_one] at hs
    have hstep : ‖(s * h) • u‖ ≤ |h| * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1.le]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 (abs_nonneg h)) (norm_nonneg u)
    exact (HalfHolder.norm_eval_torusTranslate_lift_sub_le z ((s * h) • u) a).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (norm_nonneg z))
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hbound

/-- A closed-slab time derivative preserves the strong spatial derivative
relation for coefficients as well as for vector-valued fields. -/
theorem terminalSpatialDerivative_of_hasDerivWithinAt {T t : ℝ} (hT : 0 < T)
    (ht : t ∈ Icc 0 T) (u : Vec3) {f df : ℝ → HalfHolder A E} {ft dft : HalfHolder A E}
    (hSpatial : ∀ r ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f r) (df r))
    (hF : HasDerivWithinAt f ft (Icc 0 T) t) (hDF : HasDerivWithinAt df dft (Icc 0 T) t) :
    endpointTorusHasSpatialDerivative u ft dft := by
  apply endpointTorusHasSpatialDerivative_of_sqrtRemainder u ft dft ‖dft‖
  intro a h hh
  let D : HalfHolder A E →L[ℝ] E :=
    h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) - HalfHolder.eval a)
  let J : HalfHolder A E →L[ℝ] E := segmentEvalAverage a u h
  have heq (r : ℝ) (hr : r ∈ Icc 0 T) : D (f r) = J (df r) := by
    change h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) (f r) - HalfHolder.eval a (f r)) =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) (df r)
    rw [← eval_halfHolderTorusDifference, HalfHolder.eval_torusDifference_eq_integral (f r)
      (df r) u (hSpatial r hr) hh a]
  have hFDer := D.hasFDerivAt.comp_hasDerivWithinAt t hF
  have hDFDer := (J.hasFDerivAt.comp_hasDerivWithinAt t hDF).congr_of_mem heq ht
  have hunique := uniqueDiffOn_Icc hT t ht
  have hDiff : D ft = J dft :=
    (hFDer.derivWithin hunique).symm.trans (hDFDer.derivWithin hunique)
  rw [map_sub, eval_halfHolderTorusDifference]
  change ‖D ft - HalfHolder.eval a dft‖ ≤ _
  rw [hDiff]
  exact norm_segmentEvalAverage_sub_le dft a u h

/-- Closed-slab time jets of strongly differentiable half-Hölder fields
retain their exact spatial derivatives, at every available order. -/
theorem terminalSpatialDerivative_iteratedDerivWithin {T : ℝ} (hT : 0 < T)
    {n : ℕ} (u : Vec3) {f df : ℝ → HalfHolder A E}
    (hf : ContDiffOn ℝ n f (Icc 0 T)) (hdf : ContDiffOn ℝ n df (Icc 0 T))
    (hSpatial : ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f t) (df t)) :
    ∀ m ≤ n, ∀ t ∈ Icc 0 T, endpointTorusHasSpatialDerivative u
      (iteratedDerivWithin m f (Icc 0 T) t) (iteratedDerivWithin m df (Icc 0 T) t) := by
  have hdiffF := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hT)).mp hf).2
  have hdiffDF := ((contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (uniqueDiffOn_Icc hT)).mp hdf).2
  intro m
  induction m with
  | zero =>
    intro _ t ht
    simpa only [iteratedDerivWithin_zero] using hSpatial t ht
  | succ m ih =>
    intro hm t ht
    rw [iteratedDerivWithin_succ, iteratedDerivWithin_succ]
    exact terminalSpatialDerivative_of_hasDerivWithinAt hT ht u (ih (Nat.le_of_succ_le hm))
      ((hdiffF m (Nat.lt_of_succ_le hm) t ht).hasDerivWithinAt)
      ((hdiffDF m (Nat.lt_of_succ_le hm) t ht).hasDerivWithinAt)

end

end TorusEuler

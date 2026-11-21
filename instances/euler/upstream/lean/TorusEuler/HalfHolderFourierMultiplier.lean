import TorusEuler.DyadicHolder
import TorusEuler.DyadicMultiplierKernel
import TorusEuler.HalfHolderSpace
import TorusEuler.FourierCutoffBounds
import TorusEuler.PeriodicLift
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-! Hölder summation of the dyadic torus multiplier in Appendix A.2. -/

open ContinuousLinearMap MeasureTheory Set
open scoped ContDiff FourierTransform RealInnerProductSpace SchwartzMap

namespace TorusEuler

section DyadicSum

variable {X E F : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F]

/-- Output blocks with the two scale-dependent bounds used for summation. -/
structure HalfHolderDyadicBlocks (X E F : Type*) [MetricSpace X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] where
  block : ℕ → HalfHolder X E →ₗ[ℝ] C(X, F)
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  sup_bound (j : ℕ) (f : HalfHolder X E) :
    ∀ x, ‖block j f x‖ ≤ bound * ‖f‖ * ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ)
  lip_bound (j : ℕ) (f : HalfHolder X E) :
    ∀ x y, ‖block j f x - block j f y‖ ≤
      bound * ‖f‖ * ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) * dist x y

namespace HalfHolderDyadicBlocks

private theorem summable_scale : Summable (fun j : ℕ => ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ)) := by
  have heq (j : ℕ) : ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ) = (((2 : ℝ) ^ (-1 / 2 : ℝ)) ^ j) := by
    simp only [← Real.rpow_natCast]
    rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), mul_comm (j : ℝ),
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp_rw [heq]
  exact summable_geometric_of_lt_one (by positivity)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num))

theorem summable_blocks (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) :
    Summable (fun j => D.block j f) := by
  apply Summable.of_norm
  apply (summable_scale.mul_left (D.bound * ‖f‖)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro j
  rw [ContinuousMap.norm_le_of_nonempty]
  exact D.sup_bound j f

private theorem eval_tsum (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) (x : X) :
    (∑' j, D.block j f) x = ∑' j, D.block j f x :=
  (ContinuousMap.evalCLM (R := ℝ) x).map_tsum (D.summable_blocks f)

private noncomputable def sumField (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) :
    HalfHolder X F := by
  have h := dyadicSeries_halfHolder (fun j x => D.block j f x)
    (mul_nonneg D.bound_nonneg (norm_nonneg f)) (fun j => D.sup_bound j f) (fun j => D.lip_bound j f)
  refine HalfHolder.ofBound (∑' j, D.block j f) (M := (14 * D.bound) * ‖f‖) ?_ ?_
  · intro x
    rw [D.eval_tsum]
    exact (h.2.1 x).trans (by nlinarith only [mul_nonneg D.bound_nonneg (norm_nonneg f)])
  · intro x y
    rw [D.eval_tsum, D.eval_tsum]
    simpa only [mul_assoc] using h.2.2 x y

private theorem eval_sumField (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) (x : X) :
    HalfHolder.eval x (D.sumField f) = (∑' j, D.block j f) x := rfl

private theorem norm_sumField_le (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) :
    ‖D.sumField f‖ ≤ (14 * D.bound) * ‖f‖ := by
  have h := dyadicSeries_halfHolder (fun j x => D.block j f x)
    (mul_nonneg D.bound_nonneg (norm_nonneg f)) (fun j => D.sup_bound j f) (fun j => D.lip_bound j f)
  refine (HalfHolder.norm_le_iff (mul_nonneg (mul_nonneg (by norm_num) D.bound_nonneg)
    (norm_nonneg f))).mpr ?_
  change (∀ x, ‖HalfHolder.eval x (D.sumField f)‖ ≤ _) ∧
    ∀ x y, ‖HalfHolder.eval x (D.sumField f) - HalfHolder.eval y (D.sumField f)‖ ≤ _
  simp only [eval_sumField, eval_tsum]
  exact ⟨fun x => (h.2.1 x).trans (by nlinarith only [mul_nonneg D.bound_nonneg (norm_nonneg f)]),
    fun x y => by simpa only [mul_assoc] using h.2.2 x y⟩

/-- The dyadic series gives a bounded operator on the half-Hölder Banach space. -/
noncomputable def toMultiplier (D : HalfHolderDyadicBlocks X E F) :
    HalfHolder X E →L[ℝ] HalfHolder X F :=
  let L : HalfHolder X E →ₗ[ℝ] HalfHolder X F :=
    { toFun := D.sumField
      map_add' := fun f g => by
        apply HalfHolder.ext
        intro x
        rw [map_add, eval_sumField, eval_sumField, eval_sumField]
        simp only [map_add]
        rw [(D.summable_blocks f).tsum_add (D.summable_blocks g)]
        rfl
      map_smul' := fun c f => by
        apply HalfHolder.ext
        intro x
        rw [map_smul, RingHom.id_apply, eval_sumField, eval_sumField]
        simp only [map_smul]
        rw [((D.summable_blocks f).hasSum.const_smul c).tsum_eq]
        rfl }
  L.mkContinuous (14 * D.bound) D.norm_sumField_le

theorem norm_toMultiplier_le (D : HalfHolderDyadicBlocks X E F) :
    ‖D.toMultiplier‖ ≤ 14 * D.bound := by
  apply opNorm_le_bound _ (mul_nonneg (by norm_num) D.bound_nonneg)
  exact D.norm_sumField_le

theorem eval_toMultiplier (D : HalfHolderDyadicBlocks X E F) (f : HalfHolder X E) (x : X) :
    HalfHolder.eval x (D.toMultiplier f) = (∑' j, D.block j f) x :=
  D.eval_sumField f x

end HalfHolderDyadicBlocks
end DyadicSum

section Torus

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Frequency" => (Fin 3 → ℤ)

/-- A fixed smooth cutoff for the annular partition and Bernstein estimates. -/
def dyadicMultiplierCutoff : ContDiffBump (0 : Vec3) :=
  ⟨1, 2, zero_lt_one, one_lt_two⟩

theorem dyadicMultiplierCutoff_smooth : ContDiff ℝ ∞ (⇑dyadicMultiplierCutoff) :=
  dyadicMultiplierCutoff.contDiff

theorem dyadicMultiplierCutoff_unit (ξ : Vec3) (h : ‖ξ‖ ≤ 1) :
    dyadicMultiplierCutoff ξ = 1 :=
  dyadicMultiplierCutoff.one_of_mem_closedBall (by
    change dist ξ 0 ≤ 1
    simpa only [dist_zero_right] using h)

theorem dyadicMultiplierCutoff_zero (ξ : Vec3) (h : 2 ≤ ‖ξ‖) :
    dyadicMultiplierCutoff ξ = 0 :=
  dyadicMultiplierCutoff.zero_of_le_dist (by
    change 2 ≤ dist ξ 0
    simpa only [dist_zero_right] using h)

noncomputable local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : (volume : Measure UnitAddCircle).IsAddHaarMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

open UnitAddTorus

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

private theorem torusQuotient_continuous : Continuous toUnitTorus :=
  continuous_pi fun i => (AddCircle.continuous_mk' (1 : ℝ)).comp
    (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i)

private theorem torusQuotient_sub (x y : Vec3) :
    toUnitTorus (x - y) = toUnitTorus x - toUnitTorus y := by
  funext i
  exact AddCircle.coe_sub 1 (x i) (y i)

private theorem torusQuotient_neg (x : Vec3) : toUnitTorus (-x) = -toUnitTorus x := by
  funext i
  exact AddCircle.coe_neg 1

private theorem norm_fourierValue (k : Frequency) (z : Labels) : ‖mFourier k z‖ = 1 := by
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
  exact norm_fourierMode k x

private theorem torusCharacter_add (k : Frequency) (z w : Labels) :
    mFourier k (z + w) = mFourier k z * mFourier k w := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

/-- Operator-valued convolution against one Euclidean kernel, acting on torus functions. -/
noncomputable def operatorTorusConvolution (K : Vec3 → E →L[ℂ] F) (hK : Integrable K)
    (f : C(Labels, E)) : C(Labels, F) where
  toFun z := ∫ y, K y (f (z - toUnitTorus y))
  continuous_toFun := by
    refine continuous_of_dominated (bound := fun y => ‖K y‖ * ‖f‖) ?_ ?_ (hK.norm.mul_const _) ?_
    · exact fun z => (ContinuousLinearMap.apply ℂ F).aestronglyMeasurable_comp₂
        (f.continuous.comp (continuous_const.sub torusQuotient_continuous)).aestronglyMeasurable
        hK.aestronglyMeasurable
    · exact fun z => Filter.Eventually.of_forall fun y => (K y).le_opNorm_of_le (f.norm_coe_le_norm _)
    · exact Filter.Eventually.of_forall fun y =>
        (K y).continuous.comp (f.continuous.comp (continuous_id.sub continuous_const))

omit [CompleteSpace F] in
theorem operatorTorusConvolution_toUnitTorus (K : Vec3 → E →L[ℂ] F) (hK : Integrable K)
    (f : C(Labels, E)) (x : Vec3) :
    operatorTorusConvolution K hK f (toUnitTorus x) =
      operatorLiftConvolution K (fun z => f (toUnitTorus z)) x := by
  simp only [operatorTorusConvolution, ContinuousMap.coe_mk, operatorLiftConvolution,
    torusQuotient_sub]

private theorem integrable_character_smul (f : C(Labels, E)) (k : Frequency) :
    Integrable (fun z => mFourier k z • f z) :=
  ((mFourier k).continuous.smul f.continuous).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [CompleteSpace F] in
private theorem norm_mFourierCoeff_le (k : Frequency) (g : C(Labels, F)) :
    ‖mFourierCoeff g k‖ ≤ ‖g‖ := by
  rw [mFourierCoeff]
  refine (norm_integral_le_integral_norm _).trans ?_
  have h := integral_mono_of_nonneg (μ := (volume : Measure Labels))
    (Filter.Eventually.of_forall fun z => norm_nonneg (mFourier (-k) z • g z))
    (integrable_const ‖g‖) (Filter.Eventually.of_forall fun z => ?_)
  · simpa using h
  · change ‖mFourier (-k) z • g z‖ ≤ ‖g‖
    rw [norm_smul, norm_fourierValue, one_mul]
    exact g.norm_coe_le_norm z

/-- Taking a Fourier coefficient is continuous in the spatial supremum norm. -/
noncomputable def continuousFourierCoefficient (k : Frequency) : C(Labels, F) →L[ℝ] F := by
  let L : C(Labels, F) →ₗ[ℝ] F :=
    { toFun := fun g => mFourierCoeff g k
      map_add' := by
        intro g h
        simp only [mFourierCoeff, ContinuousMap.add_apply, smul_add]
        exact integral_add (integrable_character_smul g (-k)) (integrable_character_smul h (-k))
      map_smul' := by
        intro c g
        simp only [mFourierCoeff, ContinuousMap.smul_apply, RingHom.id_apply]
        simp_rw [smul_comm (mFourier (-k) _ ) c]
        exact integral_smul c _ }
  refine L.mkContinuous 1 fun g => ?_
  change ‖mFourierCoeff g k‖ ≤ 1 * ‖g‖
  simpa only [one_mul] using norm_mFourierCoeff_le k g

omit [CompleteSpace F] in
@[simp] theorem continuousFourierCoefficient_apply (k : Frequency) (g : C(Labels, F)) :
    continuousFourierCoefficient k g = mFourierCoeff g k := rfl

omit [CompleteSpace F] in
theorem norm_continuousFourierCoefficient_le (k : Frequency) :
    ‖(continuousFourierCoefficient k : C(Labels, F) →L[ℝ] F)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro g
  simpa only [continuousFourierCoefficient_apply, one_mul] using norm_mFourierCoeff_le k g

/-- The coefficient of operator convolution equals the sampled operator symbol
applied to the input coefficient. -/
theorem mFourierCoeff_operatorTorusConvolution [CompleteSpace E] (K : Vec3 → E →L[ℂ] F)
    (hK : Integrable K) (hKc : Continuous K) (f : C(Labels, E)) (k : Frequency) :
    mFourierCoeff (operatorTorusConvolution K hK f) k =
      ((𝓕 K) (latticeVector k)) (mFourierCoeff f k) := by
  let H (z : Labels) (y : Vec3) := mFourier (-k) z • K y (f (z - toUnitTorus y))
  have hcont : Continuous (Function.uncurry H) :=
    ((mFourier (-k)).continuous.comp continuous_fst).smul
      ((hKc.comp continuous_snd).clm_apply
        (f.continuous.comp (continuous_fst.sub (torusQuotient_continuous.comp continuous_snd))))
  have hint : Integrable (Function.uncurry H) (volume.prod volume) := by
    refine ((hK.norm.comp_snd (volume : Measure Labels)).mul_const ‖f‖).mono'
      hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    change ‖mFourier (-k) p.1 • K p.2 (f (p.1 - toUnitTorus p.2))‖ ≤ ‖K p.2‖ * ‖f‖
    rw [norm_smul, norm_fourierValue, one_mul]
    exact (K p.2).le_opNorm_of_le (f.norm_coe_le_norm _)
  have hleft : mFourierCoeff (operatorTorusConvolution K hK f) k = ∫ z, ∫ y, H z y := by
    unfold mFourierCoeff
    apply integral_congr_ae
    filter_upwards with z
    exact (integral_smul (mFourier (-k) z) (fun y => K y (f (z - toUnitTorus y)))).symm
  have hright (y : Vec3) : (∫ z, H z y) =
      mFourier (-k) (toUnitTorus y) • K y (mFourierCoeff f k) := by
    rw [← integral_add_right_eq_self (H · y) (toUnitTorus y)]
    simp only [H, add_sub_cancel_right, torusCharacter_add]
    unfold mFourierCoeff
    rw [← (K y).integral_comp_comm (integrable_character_smul f (-k)), ← integral_smul]
    apply integral_congr_ae
    filter_upwards with z
    rw [map_smul, smul_smul, mul_comm]
  let a := mFourierCoeff f k
  have hmode := operatorLiftConvolution_fourierMode_smul hK k a 0
  have hzero : fourierMode k 0 = 1 := by simp [fourierMode_eq_exp]
  rw [operatorLiftConvolution, hzero, one_smul] at hmode
  rw [hleft, integral_integral_swap hint, ← hmode]
  apply integral_congr_ae
  filter_upwards with y
  rw [hright, zero_sub, fourierMode, torusQuotient_neg, mFourier_neg_arg, map_smul]

private theorem torusDist_le_lift (x y : Vec3) : dist (toUnitTorus x) (toUnitTorus y) ≤ ‖x - y‖ := by
  rw [dist_eq_norm, ← torusQuotient_sub]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mpr
  intro i
  change ‖(((x - y) i : ℝ) : UnitAddCircle)‖ ≤ ‖x - y‖
  exact QuotientAddGroup.norm_mk_le_norm.trans (PiLp.norm_apply_le (x - y) i)

/-- Representatives on the Euclidean lift can be chosen with distance at most
twice the distance on the product torus. -/
theorem exists_close_lifts (z w : Labels) :
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
  have hy : toUnitTorus (x - b) = w := by rw [torusQuotient_sub, hx, hb, sub_sub_cancel]
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

/-- The underlying continuous torus field of a half-Hölder field. -/
noncomputable def continuousHalfHolder (f : HalfHolder Labels E) : C(Labels, E) :=
  f.val.1.toContinuousMap

/-- The Fourier coefficients determine a half-Hölder field. -/
theorem eq_halfHolder_of_mFourierCoeff_eq (f g : HalfHolder Labels F)
    (h : ∀ k : Frequency, mFourierCoeff (continuousHalfHolder f) k =
      mFourierCoeff (continuousHalfHolder g) k) : f = g := by
  have heq := eq_of_mFourierCoeff_eq (continuousHalfHolder f) (continuousHalfHolder g) h
  apply HalfHolder.ext
  intro x
  exact congrArg (fun u : C(Labels, F) => u x) heq

private theorem norm_continuousHalfHolder_le (f : HalfHolder Labels E) : ‖continuousHalfHolder f‖ ≤ ‖f‖ := by
  rw [ContinuousMap.norm_le_of_nonempty]
  exact ((HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl).1

/-- Fourier analysis commutes with summation of the dyadic blocks in the supremum norm. -/
theorem mFourierCoeff_halfHolderDyadicMultiplier (D : HalfHolderDyadicBlocks Labels E F)
    (f : HalfHolder Labels E) (k : Frequency) :
    mFourierCoeff (continuousHalfHolder (D.toMultiplier f)) k =
      ∑' j, mFourierCoeff (D.block j f) k := by
  have hfield : continuousHalfHolder (D.toMultiplier f) = ∑' j, D.block j f :=
    ContinuousMap.ext (D.eval_toMultiplier f)
  rw [hfield]
  exact (continuousFourierCoefficient k).map_tsum (D.summable_blocks f)

private theorem norm_halfHolder_lift_increment (f : HalfHolder Labels E) (x y : Vec3) :
    ‖continuousHalfHolder f (toUnitTorus x) - continuousHalfHolder f (toUnitTorus y)‖ ≤
      ‖f‖ * Real.sqrt ‖x - y‖ :=
  (((HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl).2 _ _).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (torusDist_le_lift x y)) (norm_nonneg f))

private noncomputable def operatorConvolutionBlock (K : Vec3 → E →L[ℂ] F) (hK : Integrable K) :
    HalfHolder Labels E →ₗ[ℝ] C(Labels, F) where
  toFun f := operatorTorusConvolution K hK (continuousHalfHolder f)
  map_add' := by
    intro f g
    ext z
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    change operatorTorusConvolution K hK (continuousHalfHolder (f + g)) (toUnitTorus x) =
      operatorTorusConvolution K hK (continuousHalfHolder f) (toUnitTorus x) +
        operatorTorusConvolution K hK (continuousHalfHolder g) (toUnitTorus x)
    simp only [operatorTorusConvolution_toUnitTorus, operatorLiftConvolution]
    change (∫ y, K y (continuousHalfHolder f (toUnitTorus (x - y)) +
        continuousHalfHolder g (toUnitTorus (x - y)))) = _
    simp only [map_add]
    exact integral_add
      (integrable_operatorLiftConvolution hK (f.val.1.continuous.comp torusQuotient_continuous)
        (fun y => (continuousHalfHolder f).norm_coe_le_norm _) x)
      (integrable_operatorLiftConvolution hK (g.val.1.continuous.comp torusQuotient_continuous)
        (fun y => (continuousHalfHolder g).norm_coe_le_norm _) x)
  map_smul' := by
    intro c f
    ext z
    change (∫ y, K y (c • continuousHalfHolder f (z - toUnitTorus y))) = c • ∫ y,
      K y (continuousHalfHolder f (z - toUnitTorus y))
    simp only [map_smul_of_tower, integral_smul]

private theorem torusLip_of_fourierBand
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hψsmooth : ContDiff ℝ ∞ ψ)
    (hψunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {Λ : ℝ} (hΛ : 0 < Λ)
    (g : C(Labels, F)) (hband : ∀ k, 4 * Λ < ‖latticeVector k‖ → mFourierCoeff g k = 0)
    (z w : Labels) :
    ‖g z - g w‖ ≤ (8 * Λ) * (∫ y, ‖iteratedFDeriv ℝ 1
      (cutoffSchwartzKernel hψ hψsmooth : Vec3 → ℂ) y‖) * ‖g‖ * dist z w := by
  let K := cutoffSchwartzKernel hψ hψsmooth
  let B : ℝ := ∫ y, ‖iteratedFDeriv ℝ 1 (K : Vec3 → ℂ) y‖
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  have hK (v : Vec3) : (∫ y, ‖iteratedFDeriv ℝ 1 (K : Vec3 → ℂ) y (fun _ => v)‖) ≤ B * ‖v‖ := by
    rw [← integral_mul_const]
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    · apply Integrable.mul_const
      simpa only [pow_zero, one_mul] using K.integrable_pow_mul_iteratedFDeriv volume 0 1
    · refine Filter.Eventually.of_forall fun y => ?_
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, pow_one] using
        (iteratedFDeriv ℝ 1 (K : Vec3 → ℂ) y).le_opNorm (fun _ => v)
  have hdiff : ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) := by
    rw [← finiteFourierSum_mFourierCoeff_eq_of_band g (4 * Λ) hband]
    exact contDiff_lift_finiteFourierSum _ _
  have hder (x : Vec3) : ‖fderiv ℝ (fun y => g (toUnitTorus y)) x‖ ≤ (4 * Λ) * B * ‖g‖ := by
    refine opNorm_le_bound _ (by positivity) fun v => ?_
    have h := bernstein_lift_of_band hψ hψsmooth hψunit hΛ g hband
      (j := 1) (fun _ => v) x
    rw [iteratedFDeriv_one_apply, pow_one] at h
    calc
      _ ≤ (4 * Λ) * (∫ y, ‖iteratedFDeriv ℝ 1 (K : Vec3 → ℂ) y (fun _ => v)‖) * ‖g‖ := h
      _ ≤ (4 * Λ) * (B * ‖v‖) * ‖g‖ := by gcongr; exact hK v
      _ = _ := by ring
  obtain ⟨x, y, hx, hy, hdist⟩ := exists_close_lifts z w
  rw [← hx, ← hy]
  have hLip := (convex_univ : Convex ℝ (univ : Set Vec3)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => hdiff.differentiable (by simp) x) (fun x _ => hder x) (mem_univ y) (mem_univ x)
  calc
    _ ≤ (4 * Λ) * B * ‖g‖ * ‖x - y‖ := hLip
    _ ≤ (4 * Λ) * B * ‖g‖ * (2 * dist z w) := mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = _ := by rw [hx, hy]; ring

private noncomputable def compactDyadicBlock {σ : Vec3 → E →L[ℂ] F}
    (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ) (j : ℕ) :
    HalfHolder Labels E →ₗ[ℝ] C(Labels, F) :=
  operatorConvolutionBlock (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs))
    (integrable_scaledMultiplierKernel (by positivity) (compactMultiplierKernel hc hs).integrable)

private theorem mFourierCoeff_compactDyadicBlock [CompleteSpace E] {σ : Vec3 → E →L[ℂ] F}
    (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ) (j : ℕ) (f : HalfHolder Labels E) (k : Frequency) :
    mFourierCoeff (compactDyadicBlock hc hs j f) k =
      σ (((2 : ℝ) ^ j)⁻¹ • latticeVector k) (mFourierCoeff (continuousHalfHolder f) k) := by
  have hΛ : 0 < (2 : ℝ) ^ j := by positivity
  let K := compactMultiplierKernel hc hs
  have hkc : Continuous (scaledMultiplierKernel ((2 : ℝ) ^ j) K) :=
    (K.continuous.comp (continuous_id.const_smul ((2 : ℝ) ^ j))).const_smul _
  have hK : Integrable (scaledMultiplierKernel ((2 : ℝ) ^ j) K) :=
    integrable_scaledMultiplierKernel hΛ K.integrable
  change mFourierCoeff (operatorTorusConvolution _ hK (continuousHalfHolder f)) k = _
  rw [mFourierCoeff_operatorTorusConvolution _ _ hkc,
    fourier_scaledMultiplierKernel hΛ, fourier_compactMultiplierKernel]

private theorem norm_compactDyadicBlock_le {σ : Vec3 → E →L[ℂ] F}
    (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ) (hzero : σ 0 = 0)
    (j : ℕ) (f : HalfHolder Labels E) :
    ‖compactDyadicBlock hc hs j f‖ ≤
      (∫ y, ‖compactMultiplierKernel hc hs y‖ * Real.sqrt ‖y‖) *
        ‖f‖ * ((2 : ℝ) ^ j) ^ (-1 / 2 : ℝ) := by
  rw [ContinuousMap.norm_le_of_nonempty]
  intro z
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
  have hK : Integrable (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs)) :=
    integrable_scaledMultiplierKernel (by positivity) (compactMultiplierKernel hc hs).integrable
  change ‖operatorTorusConvolution _ hK (continuousHalfHolder f) (toUnitTorus x)‖ ≤ _
  rw [operatorTorusConvolution_toUnitTorus]
  have h := norm_operatorLiftConvolution_dyadic_le_halfHolder hc hs hzero
    (Λ := (2 : ℝ) ^ j) (by positivity)
    ((continuousHalfHolder f).continuous.comp torusQuotient_continuous)
    (fun _ => (continuousHalfHolder f).norm_coe_le_norm _) (norm_halfHolder_lift_increment f) x
  refine h.trans_eq ?_
  rw [Real.sqrt_eq_rpow, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
  ring_nf

/-- The half-moment appearing in the block bound is controlled by the first
five symbol derivative masses and a fixed finite radial integral. -/
theorem compactMultiplierKernel_halfMoment_le {σ : Vec3 → E →L[ℂ] F}
    (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ) :
    (∫ y, ‖compactMultiplierKernel hc hs y‖ * Real.sqrt ‖y‖) ≤
      (32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass σ)) *
        ∫ y : Vec3, (1 + ‖y‖) ^ (-(4 : ℝ)) := by
  let K := compactMultiplierKernel hc hs
  let C := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 * multiplierDerivativeMass σ)
  have htail : Integrable (fun y : Vec3 => (1 + ‖y‖) ^ (-(4 : ℝ))) := by
    apply integrable_one_add_norm
    norm_num [finrank_euclideanSpace_fin]
  change (∫ y, ‖K y‖ * Real.sqrt ‖y‖) ≤ C * ∫ y : Vec3, (1 + ‖y‖) ^ (-(4 : ℝ))
  rw [← integral_const_mul]
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => by positivity)
    (htail.const_mul C)
  refine Filter.Eventually.of_forall fun y => ?_
  have hdecay := inverseMultiplierKernel_decay (hc.toSchwartzMap hs) (d := 0) (by norm_num) y
  rw [norm_iteratedFDeriv_zero] at hdecay
  change (1 + ‖y‖) ^ 5 * ‖K y‖ ≤ C at hdecay
  have hroot : Real.sqrt ‖y‖ ≤ 1 + ‖y‖ := by
    nlinarith [Real.sq_sqrt (norm_nonneg y), sq_nonneg (Real.sqrt ‖y‖ - 1)]
  calc
    _ ≤ ‖K y‖ * (1 + ‖y‖) := mul_le_mul_of_nonneg_left hroot (norm_nonneg _)
    _ ≤ _ := by
      change ‖K y‖ * (1 + ‖y‖) ≤ C * (1 + ‖y‖) ^ (-(4 : ℝ))
      rw [Real.rpow_neg (by positivity), Real.rpow_ofNat, ← div_eq_mul_inv,
        le_div_iff₀ (by positivity)]
      rw [mul_assoc, ← pow_succ', mul_comm]
      exact hdecay

/-- A fixed smooth cancelled annular symbol and its dyadic dilations give
output blocks with the summable Hölder bounds. -/
noncomputable def compactSymbolDyadicBlocks [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hψsmooth : ContDiff ℝ ∞ ψ)
    (hψunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    {σ : Vec3 → E →L[ℂ] F} (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ)
    (hzero : σ 0 = 0) (hσband : ∀ ξ, 4 < ‖ξ‖ → σ ξ = 0) :
    HalfHolderDyadicBlocks Labels E F := by
  let M := ∫ y, ‖compactMultiplierKernel hc hs y‖ * Real.sqrt ‖y‖
  let B := ∫ y, ‖iteratedFDeriv ℝ 1 (cutoffSchwartzKernel hψ hψsmooth : Vec3 → ℂ) y‖
  have hM : 0 ≤ M := integral_nonneg fun _ => by positivity
  have hB : 0 ≤ B := integral_nonneg fun _ => norm_nonneg _
  let C := max 1 (8 * B) * M
  have hC : 0 ≤ C := mul_nonneg (zero_le_one.trans (le_max_left _ _)) hM
  refine ⟨compactDyadicBlock hc hs, C, hC, ?_, ?_⟩
  · intro j f z
    refine ((compactDyadicBlock hc hs j f).norm_coe_le_norm z).trans
      ((norm_compactDyadicBlock_le hc hs hzero j f).trans ?_)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg f)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 (8 * B)) hM
  · intro j f z w
    let Λ := (2 : ℝ) ^ j
    have hΛ : 0 < Λ := by positivity
    let g := compactDyadicBlock hc hs j f
    have hG (k : Frequency) (hk : 4 * Λ < ‖latticeVector k‖) : mFourierCoeff g k = 0 := by
      have hscaled : 4 < ‖Λ⁻¹ • latticeVector k‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hΛ.le), ← div_eq_inv_mul, lt_div_iff₀ hΛ]
        exact hk
      rw [show g = compactDyadicBlock hc hs j f by rfl, mFourierCoeff_compactDyadicBlock,
        hσband _ hscaled, zero_apply]
    have hpow : Λ * Λ ^ (-1 / 2 : ℝ) = Λ ^ (1 / 2 : ℝ) := by
      calc
        _ = Λ ^ (1 : ℝ) * Λ ^ (-1 / 2 : ℝ) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hΛ]; norm_num
    calc
      ‖g z - g w‖ ≤ (8 * Λ) * B * ‖g‖ * dist z w :=
        torusLip_of_fourierBand hψ hψsmooth hψunit hΛ g hG z w
      _ ≤ (8 * Λ) * B * (M * ‖f‖ * Λ ^ (-1 / 2 : ℝ)) * dist z w := by
        gcongr
        exact norm_compactDyadicBlock_le hc hs hzero j f
      _ = (8 * B * M) * ‖f‖ * Λ ^ (1 / 2 : ℝ) * dist z w := by rw [← hpow]; ring
      _ ≤ C * ‖f‖ * Λ ^ (1 / 2 : ℝ) * dist z w := by
        gcongr
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) hM

/-- The dyadic output block carries the sampled coefficient of the annular symbol. -/
theorem mFourierCoeff_compactSymbolDyadicBlocks [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hψsmooth : ContDiff ℝ ∞ ψ)
    (hψunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    {σ : Vec3 → E →L[ℂ] F} (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ)
    (hzero : σ 0 = 0) (hσband : ∀ ξ, 4 < ‖ξ‖ → σ ξ = 0)
    (j : ℕ) (f : HalfHolder Labels E) (k : Frequency) :
    mFourierCoeff ((compactSymbolDyadicBlocks hψ hψsmooth hψunit hc hs hzero hσband).block j f) k =
      σ (((2 : ℝ) ^ j)⁻¹ • latticeVector k) (mFourierCoeff (continuousHalfHolder f) k) :=
  mFourierCoeff_compactDyadicBlock hc hs j f k

theorem tendsto_operatorLiftConvolution_compactSymbolDyadicBlocks [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hψsmooth : ContDiff ℝ ∞ ψ)
    (hψunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    {σ : Vec3 → E →L[ℂ] F} (hc : HasCompactSupport σ) (hs : ContDiff ℝ ∞ σ)
    (hzero : σ 0 = 0) (hσband : ∀ ξ, 4 < ‖ξ‖ → σ ξ = 0)
    (f : HalfHolder Labels E) (x : Vec3) :
    let D := compactSymbolDyadicBlocks hψ hψsmooth hψunit hc hs hzero hσband
    Filter.Tendsto (fun N => ∑ j ∈ Finset.range N,
      operatorLiftConvolution (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs))
        (fun z => continuousHalfHolder f (toUnitTorus z)) x) Filter.atTop
      (nhds (HalfHolder.eval (toUnitTorus x) (D.toMultiplier f))) := by
  intro D
  have heval (j : ℕ) : D.block j f (toUnitTorus x) =
      operatorLiftConvolution (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs))
        (fun z => continuousHalfHolder f (toUnitTorus z)) x := by
    have hK : Integrable (scaledMultiplierKernel ((2 : ℝ) ^ j) (compactMultiplierKernel hc hs)) :=
      integrable_scaledMultiplierKernel (by positivity) (compactMultiplierKernel hc hs).integrable
    exact operatorTorusConvolution_toUnitTorus _ hK (continuousHalfHolder f) x
  rw [D.eval_toMultiplier]
  let ev := ContinuousMap.evalCLM (R := ℝ) (toUnitTorus x) (M := F)
  have h := ev.continuous.continuousAt.tendsto.comp (D.summable_blocks f).hasSum.tendsto_sum_nat
  change Filter.Tendsto (fun N => ev (∑ j ∈ Finset.range N, D.block j f)) Filter.atTop
    (nhds ((∑' j, D.block j f) (toUnitTorus x))) at h
  simpa only [map_sum, ev, ContinuousMap.evalCLM_apply, heval] using h

/-- Cancel the low frequencies and restrict to an annulus before Fourier inversion. -/
noncomputable def annularLocalize (ψ : Vec3 → ℝ) (A : Vec3 → E →L[ℂ] F)
    (ξ : Vec3) : E →L[ℂ] F :=
  (ψ ξ - ψ ((2 : ℝ) • ξ)) • A ξ

omit [CompleteSpace F] in
theorem annularLocalize_zero_of_large {ψ : Vec3 → ℝ}
    (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) (A : Vec3 → E →L[ℂ] F) (ξ : Vec3)
    (hξ : 2 ≤ ‖ξ‖) : annularLocalize ψ A ξ = 0 := by
  have hx : 2 ≤ ‖(2 : ℝ) • ξ‖ := by
    rw [norm_smul, Real.norm_ofNat]
    linarith
  simp only [annularLocalize, hout ξ hξ, hout _ hx, sub_self, zero_smul]

omit [CompleteSpace F] in
theorem annularLocalize_compact {ψ : Vec3 → ℝ}
    (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) (A : Vec3 → E →L[ℂ] F) :
    HasCompactSupport (annularLocalize ψ A) := by
  apply (isCompact_closedBall (0 : Vec3) 2).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  rw [Metric.mem_closedBall, dist_zero_right]
  exact le_of_not_gt fun h => hξ (annularLocalize_zero_of_large hout A ξ h.le)

omit [CompleteSpace F] in
theorem annularLocalize_zero_of_small {ψ : Vec3 → ℝ}
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (A : Vec3 → E →L[ℂ] F) (ξ : Vec3)
    (hξ : ‖ξ‖ ≤ 1 / 2) : annularLocalize ψ A ξ = 0 := by
  have hx : ‖(2 : ℝ) • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_ofNat]
    linarith
  simp only [annularLocalize, hunit ξ (hξ.trans (by norm_num)), hunit _ hx, sub_self, zero_smul]

omit [CompleteSpace F] in
theorem annularLocalize_smooth {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) {A : Vec3 → E →L[ℂ] F}
    (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) : ContDiff ℝ ∞ (annularLocalize ψ A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    refine (contDiffAt_const (c := (0 : E →L[ℂ] F))).congr_of_eventuallyEq ?_
    filter_upwards [Metric.ball_mem_nhds (0 : Vec3) (by norm_num : (0 : ℝ) < 1 / 2)] with y hy
    exact annularLocalize_zero_of_small hunit A y (by
      exact (show ‖y‖ < 1 / 2 by simpa [Metric.mem_ball, dist_zero_right] using hy).le)
  · have hlocal : ContDiffAt ℝ ∞ A ξ :=
      hA.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hξ))
    have hcut : ContDiff ℝ ∞ (fun x : Vec3 => ψ x - ψ ((2 : ℝ) • x)) :=
      hψ.sub (hψ.comp (contDiff_id.const_smul (2 : ℝ)))
    exact hcut.contDiffAt.smul hlocal

omit [CompleteSpace F] in
/-- Uniform bounds on the first five jets on the annulus control the weighted
derivative mass after localization. The constant depends only on the cutoff. -/
theorem exists_annularLocalize_mass_le {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Vec3 → E →L[ℂ] F}, ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3) →
        ∀ {M : ℝ}, 0 ≤ M →
          (∀ n ≤ 5, ∀ ξ : Vec3, 1 / 2 ≤ ‖ξ‖ → ‖ξ‖ ≤ 2 →
            ‖iteratedFDeriv ℝ n A ξ‖ ≤ M) →
          multiplierDerivativeMass (annularLocalize ψ A) ≤ C * M := by
  let χ := fun ξ : Vec3 => ψ ξ - ψ ((2 : ℝ) • ξ)
  have hχ : ContDiff ℝ ∞ χ := hψ.sub (hψ.comp (contDiff_id.const_smul (2 : ℝ)))
  let ball := Metric.closedBall (0 : Vec3) 2
  have hχjet (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ ξ ∈ ball, ‖iteratedFDeriv ℝ n χ ξ‖ ≤ C := by
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Vec3) 2).bddAbove_image
      (hχ.continuous_iteratedFDeriv (m := n) (by simp)).norm.continuousOn
    exact ⟨max 0 C, le_max_left _ _, fun ξ hξ =>
      (hC ⟨ξ, hξ, rfl⟩).trans (le_max_right _ _)⟩
  choose cutoffJet hcutoffJet hχbound using hχjet
  let K := ∑ n ∈ Finset.range 6, cutoffJet n
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => hcutoffJet i
  have hKbound (n : ℕ) (hn : n ≤ 5) (ξ : Vec3) (hξ : ξ ∈ ball) :
      ‖iteratedFDeriv ℝ n χ ξ‖ ≤ K :=
    (hχbound n ξ hξ).trans (Finset.single_le_sum (fun i _ => hcutoffJet i)
      (Finset.mem_range.mpr (by omega)))
  let C : ℝ := 12 * max 1 2 * (2 ^ (5 : ℕ) * K) * volume.real ball
  refine ⟨C, by unfold C; positivity, ?_⟩
  intro A hA M hM hjet
  let σ := annularLocalize ψ A
  let annulus : Set Vec3 := (fun ξ : Vec3 => ‖ξ‖) ⁻¹' Icc (1 / 2 : ℝ) 2
  have hsupp : tsupport σ ⊆ annulus := by
    apply closure_minimal _ (isClosed_Icc.preimage continuous_norm)
    intro ξ hξ
    refine ⟨le_of_not_gt ?_, le_of_not_gt ?_⟩
    · intro h
      exact hξ (annularLocalize_zero_of_small hunit A ξ h.le)
    · intro h
      exact hξ (annularLocalize_zero_of_large hout A ξ h.le)
  have hball : tsupport σ ⊆ ball := fun ξ hξ => by
    simpa only [ball, Metric.mem_closedBall, dist_zero_right] using (hsupp hξ).2
  have hderiv (n : ℕ) (hn : n ≤ 5) (ξ : Vec3) :
      ‖iteratedFDeriv ℝ n σ ξ‖ ≤ (2 ^ (5 : ℕ) * K) * M := by
    by_cases hξ : ξ ∈ annulus
    · have hmin : (1 / 2 : ℝ) ≤ ‖ξ‖ := hξ.1
      have hmax : ‖ξ‖ ≤ 2 := hξ.2
      have hξb : ξ ∈ ball := by simpa only [ball, Metric.mem_closedBall, dist_zero_right]
      let s : Set Vec3 := {0}ᶜ
      have hs : IsOpen s := isOpen_compl_singleton
      have hξs : ξ ∈ s := by
        change ξ ∉ ({0} : Set Vec3)
        simp only [mem_singleton_iff]
        exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) hmin))
      have hAs : ContDiffOn ℝ ∞ A s := hA
      have h := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn hAs hs.uniqueDiffOn hξs
        (n := n) (by simp)
      rw [iteratedFDerivWithin_of_isOpen n hs hξs] at h
      have hχwithin (i : ℕ) : iteratedFDerivWithin ℝ i χ s ξ = iteratedFDeriv ℝ i χ ξ :=
        iteratedFDerivWithin_of_isOpen i hs hξs
      have hAwithin (i : ℕ) : iteratedFDerivWithin ℝ i A s ξ = iteratedFDeriv ℝ i A ξ :=
        iteratedFDerivWithin_of_isOpen i hs hξs
      simp only [hχwithin, hAwithin] at h
      refine h.trans ?_
      calc
        _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K * M := by
          apply Finset.sum_le_sum
          intro i hi
          have hin := Finset.mem_range.mp hi
          gcongr
          · exact hKbound i (by omega) ξ hξb
          · exact hjet (n - i) ((Nat.sub_le _ _).trans hn) ξ hmin hmax
        _ = ((2 : ℝ) ^ n * K) * M := by
          have hchoose : (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ)) = (2 : ℝ) ^ n := by
            exact_mod_cast Nat.sum_range_choose n
          rw [← Finset.sum_mul, ← Finset.sum_mul, hchoose]
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hK) hM
    · rw [Function.notMem_support.mp (fun h => hξ (hsupp (support_iteratedFDeriv_subset n h))),
        norm_zero]
      positivity
  refine (multiplierDerivativeMass_le_of_support hball hderiv).trans_eq ?_
  unfold C
  ring

private theorem latticeVector_norm_ge_one {k : Frequency} (hk : k ≠ 0) :
    1 ≤ ‖latticeVector k‖ := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hk
  have h : (1 : ℝ) ≤ |(k i : ℝ)| := by
    exact_mod_cast Int.one_le_abs (show k i ≠ 0 from hi)
  exact h.trans (by simpa [Real.norm_eq_abs, latticeVector] using PiLp.norm_apply_le (latticeVector k) i)

private theorem hasSum_annularPartition {ψ : Vec3 → ℝ}
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {ξ : Vec3} (hξ : 1 ≤ ‖ξ‖) :
    HasSum (fun j : ℕ => ψ (((2 : ℝ) ^ j)⁻¹ • ξ) -
      ψ ((2 : ℝ) • (((2 : ℝ) ^ j)⁻¹ • ξ))) (1 : ℝ) := by
  let b (n : ℕ) := ψ ((2 * ((2 : ℝ) ^ n)⁻¹) • ξ)
  have hstart : b 0 = 0 := by
    apply hout
    rw [pow_zero, inv_one, mul_one, norm_smul, Real.norm_ofNat]
    linarith
  have hstep (j : ℕ) :
      ψ (((2 : ℝ) ^ j)⁻¹ • ξ) - ψ ((2 : ℝ) • (((2 : ℝ) ^ j)⁻¹ • ξ)) = b (j + 1) - b j := by
    have hscale : 2 * ((2 : ℝ) ^ (j + 1))⁻¹ = ((2 : ℝ) ^ j)⁻¹ := by
      rw [pow_succ]
      field_simp
    simp only [b, hscale, smul_smul]
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    ((tendsto_pow_atTop_atTop_of_one_lt (show (1 : ℝ) < 2 by norm_num)).eventually_ge_atTop (2 * ‖ξ‖))
  have hstop (n : ℕ) (hn : N ≤ n) : b n = 1 := by
    apply hunit
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    calc
      _ = (2 * ‖ξ‖) / ((2 : ℝ) ^ n) := by ring
      _ ≤ _ := (div_le_one (by positivity)).mpr (hN n hn)
  have hsum : HasSum (fun j : ℕ => b (j + 1) - b j)
      (∑ j ∈ Finset.range N, (b (j + 1) - b j)) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hjN : N ≤ j := Nat.le_of_not_gt (fun hj' => hj (Finset.mem_range.mpr hj'))
    rw [hstop j hjN, hstop (j + 1) (by omega), sub_self]
  simpa only [hstep, Finset.sum_range_sub, hstart, hstop N le_rfl, sub_zero] using hsum

private noncomputable def continuousHalfHolderEmbedding : HalfHolder Labels E →L[ℝ] C(Labels, E) :=
  let L : HalfHolder Labels E →ₗ[ℝ] C(Labels, E) :=
    { toFun := continuousHalfHolder, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  L.mkContinuous 1 (fun f => by
    change ‖continuousHalfHolder f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_continuousHalfHolder_le f)

private noncomputable def halfHolderConstant : F →L[ℝ] HalfHolder Labels F :=
  let C (a : F) := HalfHolder.ofBound (ContinuousMap.const Labels a) (M := ‖a‖)
    (fun _ => le_rfl) (fun _ _ => by simp [mul_nonneg (norm_nonneg a) (Real.sqrt_nonneg _)])
  let L : F →ₗ[ℝ] HalfHolder Labels F :=
    { toFun := C
      map_add' := fun a b => HalfHolder.ext fun x => by
        rw [map_add]
        rfl
      map_smul' := fun c a => HalfHolder.ext fun x => by
        rw [map_smul]
        rfl }
  L.mkContinuous 1 (fun a => by
    rw [one_mul]
    exact (HalfHolder.norm_le_iff (norm_nonneg a)).mpr
      ⟨fun _ => le_rfl, fun _ _ => by
        change ‖a - a‖ ≤ _
        exact (by simpa only [sub_self, norm_zero] using
          mul_nonneg (norm_nonneg a) (Real.sqrt_nonneg _))⟩)

omit [CompleteSpace F] in
private theorem norm_halfHolderConstant_le : ‖(halfHolderConstant : F →L[ℝ] _)‖ ≤ 1 := by
  apply opNorm_le_bound _ zero_le_one
  intro a
  rw [one_mul]
  exact (HalfHolder.norm_le_iff (norm_nonneg a)).mpr
    ⟨fun _ => le_rfl, fun _ _ => by
      change ‖a - a‖ ≤ _
      simpa only [sub_self, norm_zero] using mul_nonneg (norm_nonneg a) (Real.sqrt_nonneg _)⟩

private theorem mFourierCoeff_halfHolderConstant (a : F) (k : Frequency) :
    mFourierCoeff (continuousHalfHolder (halfHolderConstant a)) k = if k = 0 then a else 0 := by
  classical
  have hfield : ⇑(continuousHalfHolder (halfHolderConstant a)) =
      finiteFourierSum {0} (fun _ => a) := by
    funext z
    change a = _
    simp [finiteFourierSum, mFourier]
  rw [hfield, mFourierCoeff_finiteFourierSum]
  simp

/-- The high-frequency blocks of a symbol, separated from its zero mode. -/
noncomputable def homogeneousDyadicBlocks [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) :
    HalfHolderDyadicBlocks Labels E F :=
  compactSymbolDyadicBlocks (fun ξ h => hout ξ h.le) hψ hunit (annularLocalize_compact hout A)
    (annularLocalize_smooth hψ hunit hA) (annularLocalize_zero_of_small hunit A 0 (by norm_num))
    (fun ξ h => annularLocalize_zero_of_large hout A ξ (by linarith))

/-- The bounded half-Hölder multiplier of a degree-zero symbol is defined by its
cancelled dyadic blocks and the separate action on the zero Fourier mode. -/
noncomputable def homogeneousHalfHolderMultiplier [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) :
    HalfHolder Labels E →L[ℝ] HalfHolder Labels F :=
  (homogeneousDyadicBlocks hψ hunit hout hA).toMultiplier +
    halfHolderConstant.comp (((A 0).restrictScalars ℝ).comp
      ((continuousFourierCoefficient 0).comp continuousHalfHolderEmbedding))

/-- The operator norm is bounded by the dyadic block bound and the norm of the zero mode. -/
theorem norm_homogeneousHalfHolderMultiplier_le [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)) :
    ‖homogeneousHalfHolderMultiplier hψ hunit hout hA‖ ≤
      14 * (homogeneousDyadicBlocks hψ hunit hout hA).bound + ‖A 0‖ := by
  let D := homogeneousDyadicBlocks hψ hunit hout hA
  let M : HalfHolder Labels E →L[ℝ] E := (continuousFourierCoefficient 0).comp continuousHalfHolderEmbedding
  have h1 : ‖(continuousHalfHolderEmbedding : HalfHolder Labels E →L[ℝ] C(Labels, E))‖ ≤ 1 := by
    apply opNorm_le_bound _ zero_le_one
    intro f
    rw [one_mul]
    exact norm_continuousHalfHolder_le f
  have hM : ‖M‖ ≤ 1 := (opNorm_comp_le _ _).trans <|
    (mul_le_mul (norm_continuousFourierCoefficient_le (F := E) 0) h1
      (norm_nonneg (continuousHalfHolderEmbedding : HalfHolder Labels E →L[ℝ] C(Labels, E)))
      zero_le_one).trans_eq
      (one_mul 1)
  have hZ : ‖((A 0).restrictScalars ℝ).comp M‖ ≤ ‖A 0‖ := by
    refine (opNorm_comp_le _ _).trans ?_
    rw [norm_restrictScalars]
    exact mul_le_of_le_one_right (norm_nonneg _) hM
  let Z : HalfHolder Labels E →L[ℝ] HalfHolder Labels F :=
    halfHolderConstant.comp (((A 0).restrictScalars ℝ).comp M)
  have hconst : ‖Z‖ ≤ ‖A 0‖ :=
    (opNorm_comp_le _ _).trans <|
      (mul_le_of_le_one_left (norm_nonneg _) norm_halfHolderConstant_le).trans hZ
  change ‖D.toMultiplier + Z‖ ≤ 14 * D.bound + ‖A 0‖
  calc
    _ ≤ ‖D.toMultiplier‖ + ‖Z‖ := norm_add_le D.toMultiplier Z
    _ ≤ _ := add_le_add D.norm_toMultiplier_le hconst

/-- The multiplier's zero mode is constant in space and cancels in increments. -/
theorem eval_sub_homogeneousHalfHolderMultiplier_eq_dyadic [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3))
    (f : HalfHolder Labels E) (x y : Labels) :
    let D := homogeneousDyadicBlocks hψ hunit hout hA
    let M := homogeneousHalfHolderMultiplier hψ hunit hout hA
    HalfHolder.eval x (M f) - HalfHolder.eval y (M f) =
      HalfHolder.eval x (D.toMultiplier f) - HalfHolder.eval y (D.toMultiplier f) := by
  intro D M
  let c := A 0 (mFourierCoeff (continuousHalfHolder f) 0)
  change HalfHolder.eval x (D.toMultiplier f + halfHolderConstant c) -
    HalfHolder.eval y (D.toMultiplier f + halfHolderConstant c) = _
  simp only [map_add]
  change (HalfHolder.eval x (D.toMultiplier f) + c) -
    (HalfHolder.eval y (D.toMultiplier f) + c) = _
  abel

/-- A cutoff-dependent constant controls the homogeneous multiplier by its
annular derivative mass and the zero-mode bound. -/
theorem exists_norm_homogeneousHalfHolderMultiplier_le_mass [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1)
    (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3)),
        ‖homogeneousHalfHolderMultiplier hψ hunit hout hA‖ ≤
          C * multiplierDerivativeMass (annularLocalize ψ A) + ‖A 0‖ := by
  let B := ∫ y, ‖iteratedFDeriv ℝ 1
    (cutoffSchwartzKernel (fun ξ h => hout ξ h.le) hψ : Vec3 → ℂ) y‖
  let J := ∫ y : Vec3, (1 + ‖y‖) ^ (-(4 : ℝ))
  let C₀ : ℝ := 32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5)
  let C : ℝ := 14 * max 1 (8 * B) * C₀ * J
  have hJ : 0 ≤ J := integral_nonneg fun _ => by positivity
  have hmax : 0 ≤ max 1 (8 * B) := zero_le_one.trans (le_max_left _ _)
  refine ⟨C, by unfold C C₀; positivity, ?_⟩
  intro A hA
  apply (norm_homogeneousHalfHolderMultiplier_le hψ hunit hout hA).trans
  apply add_le_add_left
  let σ := annularLocalize ψ A
  let hc := annularLocalize_compact hout A
  let hs := annularLocalize_smooth hψ hunit hA
  have hmoment := compactMultiplierKernel_halfMoment_le hc hs
  change 14 * (max 1 (8 * B) * ∫ y, ‖compactMultiplierKernel hc hs y‖ * Real.sqrt ‖y‖) ≤
    C * multiplierDerivativeMass σ
  calc
    _ ≤ 14 * (max 1 (8 * B) * ((32 * ((1 + 2 * Real.pi) * (4 : ℝ) ^ 5 *
        multiplierDerivativeMass σ)) * J)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmoment hmax) (by norm_num)
    _ = _ := by dsimp only [C, C₀]; ring

/-- The bounded operator has precisely the prescribed mode action, including
at zero frequency. -/
theorem mFourierCoeff_homogeneousHalfHolderMultiplier [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3))
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ : Vec3, ξ ≠ 0 → A (c • ξ) = A ξ)
    (f : HalfHolder Labels E) (k : Frequency) :
    mFourierCoeff (continuousHalfHolder (homogeneousHalfHolderMultiplier hψ hunit hout hA f)) k =
      A (latticeVector k) (mFourierCoeff (continuousHalfHolder f) k) := by
  let D := homogeneousDyadicBlocks hψ hunit hout hA
  let z := A 0 (mFourierCoeff (continuousHalfHolder f) 0)
  change (continuousFourierCoefficient k)
    (continuousHalfHolder (D.toMultiplier f) + continuousHalfHolder (halfHolderConstant z)) = _
  simp only [map_add, continuousFourierCoefficient_apply, mFourierCoeff_halfHolderDyadicMultiplier,
    mFourierCoeff_halfHolderConstant]
  have hblock (j : ℕ) : mFourierCoeff (D.block j f) k =
      annularLocalize ψ A (((2 : ℝ) ^ j)⁻¹ • latticeVector k)
        (mFourierCoeff (continuousHalfHolder f) k) :=
    mFourierCoeff_compactDyadicBlock _ _ j f k
  simp_rw [hblock]
  by_cases hk : k = 0
  · subst k
    have hlat : latticeVector (0 : Frequency) = 0 := by
      apply PiLp.ext
      intro i
      exact Int.cast_zero
    simp [hlat, annularLocalize, z]
  · rw [ite_eq_right hk, add_zero]
    have hnorm := latticeVector_norm_ge_one hk
    have hlat : latticeVector k ≠ 0 := by
      intro h
      exact (by norm_num : ¬(1 : ℝ) ≤ 0) (by simpa [h] using hnorm)
    have hsum := (hasSum_annularPartition hunit hout hnorm).smul_const
      (A (latticeVector k) (mFourierCoeff (continuousHalfHolder f) k))
    have heq (j : ℕ) : A (((2 : ℝ) ^ j)⁻¹ • latticeVector k) = A (latticeVector k) :=
      hhom _ (by positivity) _ hlat
    simp_rw [annularLocalize, _root_.smul_apply, heq]
    simpa only [one_smul] using hsum.tsum_eq

section L2Agreement

open scoped ENNReal

private theorem integrable_L2Character {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G]
    (u : Lp G 2 unitTorusMeasure) (k : Frequency) :
    Integrable (fun z => mFourier k z • u z) unitTorusMeasure :=
  ((Lp.memLp u).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).bdd_smul 1
    (mFourier k).continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => (norm_fourierValue k z).le)

private theorem eq_zero_L2_of_all_mFourierCoeff_zero (u : Lp F 2 unitTorusMeasure)
    (hu : ∀ k : Frequency, mFourierCoeff u k = 0) : u = 0 := by
  obtain ⟨s, hs, hmem⟩ := (Lp.aestronglyMeasurable u).isSeparable_ae_range
  have hsep : (u : Labels → F) =ᵐ[unitTorusMeasure] 0 := by
    refine ae_eq_zero_of_forall_dual_of_isSeparable ℂ hs (fun L => ?_) hmem
    let v : Lp ℂ 2 unitTorusMeasure := L.compLpL 2 unitTorusMeasure u
    have hv (k : Frequency) : mFourierCoeff v k = 0 := by
      calc
        _ = ∫ z, mFourier (-k) z • L (u z) ∂unitTorusMeasure := by
          unfold mFourierCoeff
          apply integral_congr_ae
          filter_upwards [L.coeFn_compLpL u] with z hz
          exact congrArg (fun a : ℂ => mFourier (-k) z • a) hz
        _ = L (mFourierCoeff u k) := by
          change (∫ z, mFourier (-k) z • L (u z) ∂unitTorusMeasure) =
            L (∫ z, mFourier (-k) z • u z ∂unitTorusMeasure)
          rw [← L.integral_comp_comm (integrable_L2Character u (-k))]
          simp only [map_smul]
        _ = 0 := by rw [hu, map_zero]
    have hv0 : v = 0 := by
      apply mFourierBasis.repr.injective
      apply lp.ext
      funext k
      calc
        _ = mFourierCoeff v k := mFourierBasis_repr v k
        _ = 0 := hv k
        _ = _ := (congrArg (fun w : lp (fun _ : Frequency => ℂ) 2 => w k)
          (map_zero (mFourierBasis (d := Fin 3)).repr)).symm
    filter_upwards [L.coeFn_compLpL u, Lp.coeFn_zero ℂ 2 unitTorusMeasure] with z hz h0
    change v z = L (u z) at hz
    rw [hv0, h0] at hz
    exact hz.symm
  exact Lp.ext (hsep.trans (Lp.coeFn_zero F 2 unitTorusMeasure).symm)

/-- Fourier coefficients uniquely determine Banach-valued torus (L^2) functions.
Scalar Fourier uniqueness applies to every continuous linear functional, and a
strongly measurable representative has essentially separable range. -/
theorem eq_L2_of_mFourierCoeff_eq (u v : Lp F 2 unitTorusMeasure)
    (h : ∀ k : Frequency, mFourierCoeff u k = mFourierCoeff v k) : u = v := by
  apply sub_eq_zero.mp
  apply eq_zero_L2_of_all_mFourierCoeff_zero
  intro k
  unfold mFourierCoeff at h ⊢
  have hsub : (fun z => mFourier (-k) z • (u - v) z) =ᵐ[unitTorusMeasure] fun z =>
      mFourier (-k) z • u z - mFourier (-k) z • v z := by
    filter_upwards [Lp.coeFn_sub u v] with z hz
    simp only [hz, Pi.sub_apply, smul_sub]
  change (∫ z, mFourier (-k) z • (u - v) z ∂unitTorusMeasure) = 0
  rw [integral_congr_ae hsub, integral_sub (integrable_L2Character u (-k))
    (integrable_L2Character v (-k))]
  exact sub_eq_zero.mpr (h k)

/-- Embed a half-Hölder torus field in spatial Haar (L^2). -/
noncomputable def halfHolderTorusL2 : HalfHolder Labels E →L[ℝ] Lp E 2 unitTorusMeasure :=
  (ContinuousMap.toLp 2 unitTorusMeasure ℝ).comp continuousHalfHolderEmbedding

private theorem mFourierCoeff_halfHolderTorusL2 (f : HalfHolder Labels E) (k : Frequency) :
    mFourierCoeff (halfHolderTorusL2 f) k = mFourierCoeff (continuousHalfHolder f) k := by
  unfold mFourierCoeff
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure (continuousHalfHolder f)]
    with z hz
  exact congrArg (fun a : E => mFourier (-k) z • a) hz

/-- On half-Hölder data the bounded multiplier agrees with any spatial (L^2)
operator carrying the same Fourier multipliers. -/
theorem homogeneousHalfHolderMultiplier_agrees_L2 [CompleteSpace E]
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hunit : ∀ ξ, ‖ξ‖ ≤ 1 → ψ ξ = 1) (hout : ∀ ξ, 2 ≤ ‖ξ‖ → ψ ξ = 0)
    {A : Vec3 → E →L[ℂ] F} (hA : ContDiffOn ℝ ∞ A ({0}ᶜ : Set Vec3))
    (hhom : ∀ c : ℝ, 0 < c → ∀ ξ : Vec3, ξ ≠ 0 → A (c • ξ) = A ξ)
    (B : Lp E 2 unitTorusMeasure →L[ℝ] Lp F 2 unitTorusMeasure)
    (hB : ∀ u k, mFourierCoeff (B u) k = A (latticeVector k) (mFourierCoeff u k))
    (f : HalfHolder Labels E) :
    halfHolderTorusL2 (homogeneousHalfHolderMultiplier hψ hunit hout hA f) =
      B (halfHolderTorusL2 f) := by
  apply eq_L2_of_mFourierCoeff_eq
  intro k
  rw [mFourierCoeff_halfHolderTorusL2,
    mFourierCoeff_homogeneousHalfHolderMultiplier hψ hunit hout hA hhom,
    hB, mFourierCoeff_halfHolderTorusL2]

end L2Agreement
end Torus
end TorusEuler

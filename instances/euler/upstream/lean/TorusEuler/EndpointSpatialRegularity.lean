import TorusEuler.FreezingSolvability
import TorusEuler.EndpointRealFourierTransfer
import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-! Spatial differentiation of the compressed equation of Lemma A.2. -/

open BoundedContinuousFunction Filter MeasureTheory Set
open scoped ENNReal InnerProductSpace Topology

namespace TorusEuler

noncomputable section

section TorusTranslation

local notation "A" => UnitAddTorus (Fin 3)

theorem toUnitTorus_add (x y : Vec3) :
    toUnitTorus (x + y) = toUnitTorus x + toUnitTorus y := by
  funext i
  exact AddCircle.coe_add 1 (x i) (y i)

@[simp] theorem toUnitTorus_zero : toUnitTorus 0 = 0 := by
  funext i
  simp [toUnitTorus]

/-- The quotient map is nonexpanding for the Euclidean norm on the lift and
the product norm on the unit torus. -/
theorem norm_toUnitTorus_sub_le (x y : Vec3) :
    ‖toUnitTorus x - toUnitTorus y‖ ≤ ‖x - y‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x - y))).mpr
  intro i
  change ‖(x i : UnitAddCircle) - (y i : UnitAddCircle)‖ ≤ ‖x - y‖
  rw [← AddCircle.coe_sub]
  change ‖((x - y) i : UnitAddCircle)‖ ≤ ‖x - y‖
  exact QuotientAddGroup.norm_mk_le_norm.trans (PiLp.norm_apply_le (x - y) i)

theorem lipschitzWith_toUnitTorus : LipschitzWith 1 toUnitTorus :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, dist_eq_norm] using norm_toUnitTorus_sub_le x y

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private noncomputable def torusTranslateField (b : A) (f : HalfHolder A E) : HalfHolder A E := by
  have hf := (HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl
  exact HalfHolder.ofBound
    ⟨fun a => HalfHolder.eval (a + b) f, f.val.1.continuous.comp (continuous_id.add continuous_const)⟩
    (fun a => hf.1 (a + b))
    (fun a c => by
      simpa only [ContinuousMap.coe_mk, HalfHolder.eval_apply, dist_add_right]
        using hf.2 (a + b) (c + b))

@[simp] private theorem eval_torusTranslateField (b : A) (f : HalfHolder A E) (a : A) :
    HalfHolder.eval a (torusTranslateField b f) = HalfHolder.eval (a + b) f := rfl

private theorem norm_torusTranslateField_le (b : A) (f : HalfHolder A E) :
    ‖torusTranslateField b f‖ ≤ ‖f‖ := by
  have hf := (HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl
  apply (HalfHolder.norm_le_iff (norm_nonneg f)).mpr
  change (∀ a, ‖HalfHolder.eval a (torusTranslateField b f)‖ ≤ ‖f‖) ∧
    ∀ a c, ‖HalfHolder.eval a (torusTranslateField b f) - HalfHolder.eval c (torusTranslateField b f)‖ ≤ _
  simp only [eval_torusTranslateField]
  exact ⟨fun a => hf.1 (a + b), fun a c => by
    simpa only [HalfHolder.eval_apply, dist_add_right] using hf.2 (a + b) (c + b)⟩

/-- Translation on the unit torus acts on the spatial half-Hölder Banach space. -/
noncomputable def HalfHolder.torusTranslate (b : A) : HalfHolder A E →L[ℝ] HalfHolder A E := by
  let L : HalfHolder A E →ₗ[ℝ] HalfHolder A E :=
    { toFun := torusTranslateField b
      map_add' := fun f g => HalfHolder.ext fun a => by simp only [eval_torusTranslateField, map_add]
      map_smul' := fun c f => HalfHolder.ext fun a => by
        simp only [eval_torusTranslateField, map_smul, RingHom.id_apply] }
  have hL (f : HalfHolder A E) : ‖L f‖ ≤ 1 * ‖f‖ := by
    change ‖torusTranslateField b f‖ ≤ 1 * ‖f‖
    simpa only [one_mul] using norm_torusTranslateField_le b f
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := HalfHolder A E)
    (F := HalfHolder A E) (σ := RingHom.id ℝ) L 1 hL

@[simp] theorem HalfHolder.eval_torusTranslate (b : A) (f : HalfHolder A E) (a : A) :
    HalfHolder.eval a (HalfHolder.torusTranslate b f) = HalfHolder.eval (a + b) f := rfl

theorem HalfHolder.norm_torusTranslate_apply_le (b : A) (f : HalfHolder A E) :
    ‖HalfHolder.torusTranslate b f‖ ≤ ‖f‖ :=
  norm_torusTranslateField_le b f

theorem HalfHolder.norm_torusTranslate_le (b : A) :
    ‖HalfHolder.torusTranslate (E := E) b‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => by
    simpa only [one_mul] using HalfHolder.norm_torusTranslate_apply_le b f

@[simp] theorem HalfHolder.torusTranslate_zero_apply (f : HalfHolder A E) :
    HalfHolder.torusTranslate 0 f = f :=
  HalfHolder.ext fun a => by simp only [HalfHolder.eval_torusTranslate, add_zero]

theorem HalfHolder.torusTranslate_add_apply (b c : A) (f : HalfHolder A E) :
    HalfHolder.torusTranslate (b + c) f = HalfHolder.torusTranslate b (HalfHolder.torusTranslate c f) :=
  HalfHolder.ext fun a => by simp only [HalfHolder.eval_torusTranslate, add_assoc]

theorem HalfHolder.norm_torusTranslate_apply (b : A) (f : HalfHolder A E) :
    ‖HalfHolder.torusTranslate b f‖ = ‖f‖ := by
  apply le_antisymm (HalfHolder.norm_torusTranslate_apply_le b f)
  simpa only [← HalfHolder.torusTranslate_add_apply, neg_add_cancel, HalfHolder.torusTranslate_zero_apply]
    using HalfHolder.norm_torusTranslate_apply_le (-b) (HalfHolder.torusTranslate b f)

/-- Euclidean translations give a half-power pointwise increment, uniformly in the label. -/
theorem HalfHolder.norm_eval_torusTranslate_lift_sub_le (f : HalfHolder A E) (x : Vec3) (a : A) :
    ‖HalfHolder.eval a (HalfHolder.torusTranslate (toUnitTorus x) f) - HalfHolder.eval a f‖ ≤
      ‖f‖ * Real.sqrt ‖x‖ := by
  have hf := (HalfHolder.norm_le_iff (norm_nonneg f)).mp le_rfl
  rw [HalfHolder.eval_torusTranslate]
  have hdist : dist (a + toUnitTorus x) a ≤ ‖x‖ := by
    calc
      dist (a + toUnitTorus x) a = ‖toUnitTorus x‖ := by simp [dist_eq_norm]
      _ ≤ ‖x‖ := by simpa only [sub_zero, toUnitTorus_zero] using norm_toUnitTorus_sub_le x 0
  exact (hf.2 (a + toUnitTorus x) a).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist) (norm_nonneg f))

end

end TorusTranslation

section DifferenceEquation

variable {A H : Type*} [MetricSpace A] [NormedAddCommGroup H] [NormedSpace ℝ H]

local notation "W" => HalfHolder A H
local notation "M" => HalfHolder A (H →L[ℝ] H)

/-- The scaled difference of a field and its translate. -/
def halfHolderTranslateDifference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (τ : HalfHolder A E →L[ℝ] HalfHolder A E) (h : ℝ) (v : HalfHolder A E) : HalfHolder A E :=
  h⁻¹ • (τ v - v)

/-- Exact finite-difference version of the commutator identity for
the projected coefficient equation in Lemma A.2. -/
theorem endpointSpatialDifference_equation
    (P τ : W →L[ℝ] W) (τB : M →L[ℝ] M) (shift : A → A)
    (hτ : ∀ a z, HalfHolder.eval a (τ z) = HalfHolder.eval (shift a) z)
    (hτB : ∀ a C, HalfHolder.eval a (τB C) = HalfHolder.eval (shift a) C)
    (hComm : ∀ z, P (τ z) = τ (P z))
    (B : M) (v f : W) (hEq : P (B.coefficientMul v) = f) (h : ℝ) :
    P (B.coefficientMul (halfHolderTranslateDifference τ h v)) =
      halfHolderTranslateDifference τ h f -
        P ((halfHolderTranslateDifference τB h B).coefficientMul (τ v)) := by
  have htranslate : τ (B.coefficientMul v) = (τB B).coefficientMul (τ v) := by
    apply HalfHolder.ext
    intro a
    simp only [hτ, hτB, HalfHolder.eval_coefficientMul]
  have hdiff : B.coefficientMul (τ v - v) =
      (τB B).coefficientMul (τ v) - B.coefficientMul v - (τB B - B).coefficientMul (τ v) := by
    rw [map_sub, HalfHolder.coefficientMul_sub, _root_.sub_apply]
    abel
  have hcoeff (c : ℝ) (C : M) (z : W) :
      (c • C).coefficientMul z = c • C.coefficientMul z := by
    apply HalfHolder.ext
    intro a
    simp only [map_smul, HalfHolder.eval_coefficientMul, _root_.smul_apply]
  unfold halfHolderTranslateDifference
  rw [map_smul, hdiff, map_smul, map_sub, map_sub, ← htranslate, hComm, hEq, hcoeff, map_smul, smul_sub]

/-- A translation difference of a projected field is itself projected. -/
theorem endpointSpatialDifference_fixed (P τ : W →L[ℝ] W)
    (hComm : ∀ z, P (τ z) = τ (P z)) {v : W} (hv : P v = v) (h : ℝ) :
    P (halfHolderTranslateDifference τ h v) = halfHolderTranslateDifference τ h v := by
  simp only [halfHolderTranslateDifference, map_smul, map_sub, hComm, hv]

/-- The tame estimate for solving the differentiated projected equation.
The coefficient derivative only multiplies the undifferentiated velocity. -/
theorem endpointSpatialDerivative_candidate
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z) (B dB : M) (v df : W)
    (hdf : P df = df) (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) := by
  let rhs := df - P (dB.coefficientMul v)
  have hfix : P rhs = rhs := by
    simp only [rhs, map_sub, hdf, hP]
  let r : freezingFixedSpace P := ⟨rhs, (mem_freezingFixedSpace P rhs).mpr hfix⟩
  let w := S.symm r
  refine ⟨w.val, (mem_freezingFixedSpace P _).mp w.property, ?_, ?_⟩
  · have hw : freezingCompression P B.coefficientMul hP w = r := by
      rw [← hS]
      exact S.apply_symm_apply r
    exact congrArg Subtype.val hw
  · change ‖S.symm r‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ * _
    refine ((S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).le_opNorm r).trans ?_
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    change ‖rhs‖ ≤ _
    calc
      ‖rhs‖ ≤ ‖df‖ + ‖P (dB.coefficientMul v)‖ := norm_sub_le _ _
      _ ≤ ‖df‖ + ‖P‖ * ((2 * ‖dB‖) * ‖v‖) := by
        exact add_le_add le_rfl ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
          (dB.coefficientMul.le_of_opNorm_le (HalfHolder.norm_coefficientMul_le dB) v)
          (norm_nonneg _)))
      _ = _ := by ring

end DifferenceEquation

section WeakNorm

local notation "A" => UnitAddTorus (Fin 3)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "W" => HalfHolder A H
local notation "M" => HalfHolder A (H →L[ℝ] H)
local notation "W₂" => Lp H 2 unitTorusMeasure

theorem norm_freezingHaarEmbedding_le_sup (v : W) :
    ‖freezingHaarEmbedding v‖ ≤ ‖v.val.1‖ := by
  let J : (A →ᵇ H) →L[ℝ] W₂ := BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ
  have hJ : ‖J‖ ≤ 1 := by
    have h := BoundedContinuousFunction.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := H) unitTorusMeasure
    simpa only [measureUnivNNReal, measure_univ,
      ENNReal.toNNReal_one, NNReal.coe_one, Real.one_rpow] using h
  change ‖J v.val.1‖ ≤ ‖v.val.1‖
  simpa only [one_mul] using J.le_of_opNorm_le hJ v.val.1

/-- The same coercivity as in the zeroth-order solve controls a projected
error by the weak norm of the projected residual. -/
theorem endpointSpatialWeakErrorEstimate
    (P : W →L[ℝ] W) (B : M)
    (hpair : ∀ w (v : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P w), freezingHaarEmbedding v.val⟫_ℝ =
        ⟪freezingHaarEmbedding w, freezingHaarEmbedding v.val⟫_ℝ)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (v : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a v.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a v.val), HalfHolder.eval a v.val⟫_ℝ)
    (u : W) (hu : P u = u) :
    ‖freezingHaarEmbedding u‖ ≤ (min 1 μ)⁻¹ *
      ‖freezingHaarEmbedding (P (B.coefficientMul u))‖ := by
  let v : freezingFixedSpace P := ⟨u, (mem_freezingFixedSpace P u).mpr hu⟩
  let U := freezingHaarEmbedding u
  let b := freezingHaarEmbedding (P (B.coefficientMul u))
  have hν : 0 < min 1 μ := lt_min zero_lt_one hμ
  have hC := freezingHaarEmbedding_line_coercive B u
    (right_mem_Icc.mpr zero_le_one) (hcoercive v)
  have hline : (freezingCoefficientLine B 1).coefficientMul u = B.coefficientMul u := by
    rw [freezingCoefficientLine_mul]
    simp [freezingContinuationLine]
  rw [hline] at hC
  have h : min 1 μ * ‖U‖ ^ 2 ≤ ⟪b, U⟫_ℝ := by
    rw [show ⟪b, U⟫_ℝ = _ from hpair (B.coefficientMul u) v]
    exact hC
  change ‖U‖ ≤ (min 1 μ)⁻¹ * ‖b‖
  by_cases hz : ‖U‖ = 0
  · rw [hz]
    positivity
  have hu₀ : 0 < ‖U‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
  have h' := h.trans (real_inner_le_norm b U)
  rw [pow_two, ← mul_assoc] at h'
  have hh := le_of_mul_le_mul_right h' hu₀
  rw [mul_comm (min 1 μ) ‖U‖] at hh
  simpa only [div_eq_mul_inv, mul_comm] using (le_div_iff₀ hν).mpr hh

theorem freezingProjection_haar_norm_le_of_compatible
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z)) (z : W) :
    ‖freezingHaarEmbedding (P z)‖ ≤ ‖Q‖ * ‖freezingHaarEmbedding z‖ := by
  rw [hPQ]
  exact Q.le_opNorm _

end WeakNorm

/-- A uniform bound in the half-Hölder norm and convergence to zero in spatial
L² imply convergence to zero in the torus supremum norm. -/
theorem tendsto_sup_norm_zero_of_tendsto_freezingHaarEmbedding_norm {H ι : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {l : Filter ι} {f : ι → HalfHolder (UnitAddTorus (Fin 3)) H} {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᶠ i in l, ‖f i‖ ≤ C)
    (hL2 : Tendsto (fun i => ‖freezingHaarEmbedding (f i)‖) l (𝓝 (0 : ℝ))) :
    Tendsto (fun i => ‖(f i).val.1‖) l (𝓝 (0 : ℝ)) := by
  refine Metric.tendsto_nhds.mpr fun ε hε => ?_
  let ρ := min 1 ((ε / 2) / (C + 1))
  have hρ : 0 < ρ := lt_min zero_lt_one (div_pos (half_pos hε) (by positivity))
  have hρ1 : ρ ≤ 1 := min_le_left _ _
  have hρC : ρ * C ≤ ε / 2 := by
    calc
      _ ≤ ((ε / 2) / (C + 1)) * C := mul_le_mul_of_nonneg_right (min_le_right _ _) hC
      _ ≤ (ε / 2) / (C + 1) * (C + 1) :=
        mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (by positivity)
      _ = _ := div_mul_cancel₀ _ (by positivity)
  have hd : 0 < ρ⁻¹ ^ 3 := pow_pos (inv_pos.2 hρ) _
  let δ := (ε / 2) / (ρ⁻¹ ^ 3)
  have hδ : 0 < δ := div_pos (half_pos hε) hd
  filter_upwards [hbound, (Metric.tendsto_nhds.mp hL2) δ hδ] with i hi hsmall
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at hsmall ⊢
  let V : C(UnitAddTorus (Fin 3), H) := (f i).val.1.toContinuousMap
  have hV := unitTorus_sup_le_holderHalf_add_l2 V hρ hρ1 hC
    ((HalfHolder.norm_le_iff hC).mp hi).2
  change ‖(f i).val.1.toContinuousMap‖ ≤ ρ * C +
    ρ⁻¹ ^ 3 * Real.sqrt (∫ a, ‖HalfHolder.eval a (f i)‖ ^ 2 ∂unitTorusMeasure) at hV
  rw [BoundedContinuousFunction.norm_toContinuousMap_eq, ← norm_freezingHaarEmbedding_eq] at hV
  refine hV.trans_lt ((add_lt_add_of_le_of_lt hρC (mul_lt_mul_of_pos_left hsmall hd)).trans_le ?_)
  dsimp [δ]
  rw [mul_comm (ρ⁻¹ ^ 3), div_mul_cancel₀ _ hd.ne', add_halves]

section TorusDifference

local notation "A" => UnitAddTorus (Fin 3)

/-- The difference quotient of the lift in direction `u`, represented on the torus. -/
def halfHolderTorusDifference {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Vec3) (h : ℝ) (f : HalfHolder A E) : HalfHolder A E :=
  halfHolderTranslateDifference (HalfHolder.torusTranslate (toUnitTorus (h • u))) h f

@[simp] theorem eval_halfHolderTorusDifference {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : Vec3) (h : ℝ) (f : HalfHolder A E) (a : A) :
    HalfHolder.eval a (halfHolderTorusDifference u h f) =
      h⁻¹ • (HalfHolder.eval (a + toUnitTorus (h • u)) f - HalfHolder.eval a f) := by
  simp only [halfHolderTorusDifference, halfHolderTranslateDifference, map_smul, map_sub,
    HalfHolder.eval_torusTranslate]

/-- A translated half-Hölder field converges uniformly along each Euclidean direction. -/
theorem tendsto_halfHolder_torusTranslate_sub_sup {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (v : HalfHolder A E) (u : Vec3) :
    Tendsto (fun h : ℝ => ‖(HalfHolder.torusTranslate (toUnitTorus (h • u)) v - v).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero (g := fun h : ℝ => ‖v‖ * Real.sqrt (‖h • u‖))
    (fun _ => norm_nonneg _) (fun h => ?_) ?_
  · apply (BoundedContinuousFunction.norm_le
      (show 0 ≤ ‖v‖ * Real.sqrt (‖h • u‖) by positivity)).mpr
    intro a
    exact HalfHolder.norm_eval_torusTranslate_lift_sub_le v (h • u) a
  · have hc : Continuous (fun h : ℝ => ‖v‖ * Real.sqrt (‖h • u‖)) :=
      continuous_const.mul (Real.continuous_sqrt.comp ((continuous_id.smul continuous_const).norm))
    simpa only [zero_smul, norm_zero, Real.sqrt_zero, mul_zero] using
      (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

local notation "W" => HalfHolder A H
local notation "W₂" => Lp H 2 unitTorusMeasure
local notation "M" => HalfHolder A (H →L[ℝ] H)
/-- Uniform product bound distinguishing the coefficient error and the
velocity error. This uses the half-Hölder norm only for the bounded factors. -/
theorem norm_coefficientMul_sub_sup_le (C D : M) (w v : W) :
    ‖(C.coefficientMul w - D.coefficientMul v).val.1‖ ≤
      ‖C‖ * ‖(w - v).val.1‖ + ‖(C - D).val.1‖ * ‖v‖ := by
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro a
  have hC : ‖HalfHolder.eval a C‖ ≤ ‖C‖ :=
    ((HalfHolder.norm_le_iff (norm_nonneg C)).mp le_rfl).1 a
  have hv : ‖HalfHolder.eval a v‖ ≤ ‖v‖ :=
    ((HalfHolder.norm_le_iff (norm_nonneg v)).mp le_rfl).1 a
  change ‖HalfHolder.eval a (C.coefficientMul w - D.coefficientMul v)‖ ≤ _
  rw [map_sub, HalfHolder.eval_coefficientMul, HalfHolder.eval_coefficientMul]
  have heq : HalfHolder.eval a C (HalfHolder.eval a w) -
      HalfHolder.eval a D (HalfHolder.eval a v) =
      HalfHolder.eval a C (HalfHolder.eval a (w - v)) +
        HalfHolder.eval a (C - D) (HalfHolder.eval a v) := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (((HalfHolder.eval a C).le_opNorm _).trans
      (mul_le_mul hC ((w - v).val.1.norm_coe_le_norm a) (norm_nonneg _) (norm_nonneg _)))
    (((HalfHolder.eval a (C - D)).le_opNorm _).trans
      (mul_le_mul ((C - D).val.1.norm_coe_le_norm a) hv (norm_nonneg _) (norm_nonneg _))))

/-- The coefficient commutator in the translation equation has the expected
uniform limit when the coefficient difference converges uniformly. -/
theorem tendsto_torusDifference_coefficientMul_sub_sup (B dB : M) (v : W) (u : Vec3)
    (hbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h B‖ ≤ ‖dB‖)
    (hlim : Tendsto (fun h => ‖(halfHolderTorusDifference u h B - dB).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    Tendsto (fun h => ‖((halfHolderTorusDifference u h B).coefficientMul
      (HalfHolder.torusTranslate (toUnitTorus (h • u)) v) - dB.coefficientMul v).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  refine squeeze_zero' (g := fun h : ℝ =>
    ‖dB‖ * ‖(HalfHolder.torusTranslate (toUnitTorus (h • u)) v - v).val.1‖ +
      ‖(halfHolderTorusDifference u h B - dB).val.1‖ * ‖v‖)
    (Eventually.of_forall fun _ => norm_nonneg _) ?_ ?_
  · filter_upwards [hbound] with h hh
    refine (norm_coefficientMul_sub_sup_le _ _ _ _).trans (add_le_add ?_ le_rfl)
    exact mul_le_mul_of_nonneg_right hh (norm_nonneg _)
  · have ht := tendsto_halfHolder_torusTranslate_sub_sup v u
    simpa only [mul_zero, zero_mul, add_zero] using
      (tendsto_const_nhds (x := ‖dB‖)).mul ht |>.add
        (hlim.mul (tendsto_const_nhds (x := ‖v‖)))

set_option maxHeartbeats 800000 in
/-- Identify the inverse of the differentiated equation with the actual
directional derivative, using uniform convergence of the difference quotients
on the periodic lift. -/
theorem endpointSpatialDerivative_of_differenceLimits_of_haar_bound
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (hpair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (B dB : M) (v f df : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hv : P v = v) (heq : P (B.coefficientMul v) = f) (hdf : P df = df)
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hDf : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h f‖ ≤ ‖df‖)
    (hDB : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h B‖ ≤ ‖dB‖)
    (hDfSup : Tendsto (fun h => ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hProdSup : Tendsto (fun h =>
      ‖((halfHolderTorusDifference u h B).coefficientMul
        (HalfHolder.torusTranslate (toUnitTorus (h • u)) v) - dB.coefficientMul v).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) ∧
      ∀ x : Vec3, HasLineDerivAt ℝ (fun y : Vec3 => HalfHolder.eval (toUnitTorus y) v)
        (HalfHolder.eval (toUnitTorus x) w) x u := by
  obtain ⟨w, hw, hweq, hwbound⟩ :=
    endpointSpatialDerivative_candidate P hP B dB v df hdf S hS
  let τ (h : ℝ) := HalfHolder.torusTranslate (E := H) (toUnitTorus (h • u))
  let Δ (h : ℝ) := halfHolderTorusDifference u h v
  let rB (h : ℝ) := (halfHolderTorusDifference u h B).coefficientMul (τ h v)
  let U (h : ℝ) := Δ h - w
  have hfix (h : ℝ) : P (Δ h) = Δ h :=
    endpointSpatialDifference_fixed P (τ h) (hcomm h) hv h
  have hΔ (h : ℝ) : P (B.coefficientMul (Δ h)) =
      halfHolderTorusDifference u h f - P (rB h) :=
    endpointSpatialDifference_equation P (τ h) (HalfHolder.torusTranslate (toUnitTorus (h • u)))
      (fun a => a + toUnitTorus (h • u))
      (fun a z => HalfHolder.eval_torusTranslate _ z a)
      (fun a z => HalfHolder.eval_torusTranslate _ z a)
      (hcomm h) B v f heq h
  have hUfix (h : ℝ) : P (U h) = U h := by
    change P (Δ h - w) = Δ h - w
    rw [map_sub, hfix, hw]
  have hUeq (h : ℝ) : P (B.coefficientMul (U h)) =
      (halfHolderTorusDifference u h f - df) - P (rB h - dB.coefficientMul v) := by
    change P (B.coefficientMul (Δ h - w)) = _
    rw [map_sub, map_sub, hΔ, hweq, map_sub]
    abel
  let C := ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
    (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖)
  have hC : 0 ≤ C := mul_nonneg
    (S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).opNorm_nonneg
    (add_nonneg (norm_nonneg df) (mul_nonneg
      (mul_nonneg (mul_nonneg zero_le_two P.opNorm_nonneg) (norm_nonneg dB)) (norm_nonneg v)))
  have hUbound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖U h‖ ≤ C + ‖w‖ := by
    filter_upwards [hDf, hDB] with h hhf hhB
    let a : freezingFixedSpace P := ⟨Δ h, (mem_freezingFixedSpace P _).mpr (hfix h)⟩
    have hnorm : ‖Δ h‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        ‖halfHolderTorusDifference u h f - P (rB h)‖ := by
      have hSa : (S a).val = halfHolderTorusDifference u h f - P (rB h) := by
        rw [show S a = freezingCompression P B.coefficientMul hP a from
          DFunLike.congr_fun hS a, freezingCompression_val]
        exact hΔ h
      have ha := (S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).le_opNorm (S a)
      rw [ContinuousLinearEquiv.coe_coe, S.symm_apply_apply, Submodule.coe_norm a,
        Submodule.coe_norm (S a), hSa] at ha
      exact ha
    have hr (h' : ℝ) : ‖rB h'‖ ≤ (2 * ‖halfHolderTorusDifference u h' B‖) * ‖v‖ := by
      unfold rB
      refine ((halfHolderTorusDifference u h' B).coefficientMul.le_of_opNorm_le
        (HalfHolder.norm_coefficientMul_le _) _).trans ?_
      rw [HalfHolder.norm_torusTranslate_apply]
    refine (norm_sub_le _ _).trans (add_le_add (hnorm.trans ?_) le_rfl)
    apply mul_le_mul_of_nonneg_left _
      (S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P).opNorm_nonneg
    calc
      ‖halfHolderTorusDifference u h f - P (rB h)‖ ≤
          ‖halfHolderTorusDifference u h f‖ + ‖P (rB h)‖ := norm_sub_le _ _
      _ ≤ ‖df‖ + ‖P‖ * ((2 * ‖halfHolderTorusDifference u h B‖) * ‖v‖) :=
        add_le_add hhf ((P.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hr h) P.opNorm_nonneg))
      _ ≤ ‖df‖ + ‖P‖ * ((2 * ‖dB‖) * ‖v‖) := add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hhB zero_le_two) (norm_nonneg v)) P.opNorm_nonneg)
      _ = _ := by ring
  have hUp : Tendsto (fun h => ‖freezingHaarEmbedding (P (B.coefficientMul (U h)))‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero (g := fun h : ℝ =>
      ‖(halfHolderTorusDifference u h f - df).val.1‖ +
        C₂ * ‖(rB h - dB.coefficientMul v).val.1‖)
      (fun _ => norm_nonneg _) (fun h => ?_) ?_
    · rw [hUeq, map_sub]
      exact (norm_sub_le _ _).trans (add_le_add
        (norm_freezingHaarEmbedding_le_sup _)
        ((hWeak _).trans (mul_le_mul_of_nonneg_left
          (norm_freezingHaarEmbedding_le_sup _) hC₂)))
    · simpa only [mul_zero, add_zero] using hDfSup.add (tendsto_const_nhds.mul hProdSup)
  have hU₂ : Tendsto (fun h => ‖freezingHaarEmbedding (U h)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine squeeze_zero (fun _ => norm_nonneg _)
      (fun h => endpointSpatialWeakErrorEstimate P B hpair hμ hcoercive (U h) (hUfix h)) ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := (min 1 μ)⁻¹)).mul hUp
  have hUsup := tendsto_sup_norm_zero_of_tendsto_freezingHaarEmbedding_norm
    (add_nonneg hC (norm_nonneg w)) hUbound hU₂
  refine ⟨w, hw, hweq, hwbound, fun x => hasLineDerivAt_iff_tendsto_slope_zero.mpr ?_⟩
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hUsup) ε hε] with h hh
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at hh
  rw [dist_eq_norm, toUnitTorus_add, ← eval_halfHolderTorusDifference, ← map_sub]
  exact ((U h).val.1.norm_coe_le_norm (toUnitTorus x)).trans_lt hh

theorem endpointSpatialDerivative_of_differenceLimits
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z))
    (hpair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (B dB : M) (v f df : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hv : P v = v) (heq : P (B.coefficientMul v) = f) (hdf : P df = df)
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hDf : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h f‖ ≤ ‖df‖)
    (hDB : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h B‖ ≤ ‖dB‖)
    (hDfSup : Tendsto (fun h => ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0))
    (hProdSup : Tendsto (fun h =>
      ‖((halfHolderTorusDifference u h B).coefficientMul
        (HalfHolder.torusTranslate (toUnitTorus (h • u)) v) - dB.coefficientMul v).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) ∧
      ∀ x : Vec3, HasLineDerivAt ℝ (fun y : Vec3 => HalfHolder.eval (toUnitTorus y) v)
        (HalfHolder.eval (toUnitTorus x) w) x u :=
  endpointSpatialDerivative_of_differenceLimits_of_haar_bound P hP ‖Q‖ Q.opNorm_nonneg
    (freezingProjection_haar_norm_le_of_compatible P Q hPQ) hpair B dB v f df u hcomm
    hv heq hdf S hS hμ hcoercive hDf hDB hDfSup hProdSup

end TorusDifference

section TorusDerivativeData

local notation "A" => UnitAddTorus (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem continuous_torusDirection (df : HalfHolder A E) (u : Vec3) (h : ℝ) (a : A) :
    Continuous (fun s : ℝ => HalfHolder.eval (a + toUnitTorus ((s * h) • u)) df) :=
  df.val.1.continuous.comp
    (continuous_const.add (lipschitzWith_toUnitTorus.continuous.comp
      ((continuous_id.mul continuous_const).smul continuous_const)))

omit [CompleteSpace E] in
/-- A line derivative on every lift point is equivalent to a derivative along
every translated torus line, at every value of its parameter. -/
theorem HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt (f df : HalfHolder A E) (u : Vec3) :
    (∀ x : Vec3, HasLineDerivAt ℝ
      (fun y : Vec3 => HalfHolder.eval (toUnitTorus y) f)
      (HalfHolder.eval (toUnitTorus x) df) x u) ↔
    ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s := by
  constructor
  · intro h a s
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    have hd : HasDerivAt
        (fun r : ℝ => HalfHolder.eval (toUnitTorus ((x + s • u) + r • u)) f)
        (HalfHolder.eval (toUnitTorus (x + s • u)) df) 0 := h (x + s • u)
    have hs : HasDerivAt (fun r : ℝ => r - s) 1 s := (hasDerivAt_id s).sub_const s
    have hD := hd.scomp_of_eq s hs (sub_self s).symm
    have hg (r : ℝ) : (x + s • u) + (r - s) • u = x + r • u := by
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    have heq :
        (fun r : ℝ => HalfHolder.eval (toUnitTorus ((x + s • u) + r • u)) f) ∘
          (fun r : ℝ => r - s) =
        (fun r : ℝ => HalfHolder.eval (toUnitTorus x + toUnitTorus (r • u)) f) := by
      funext r
      change HalfHolder.eval (toUnitTorus ((x + s • u) + (r - s) • u)) f = _
      rw [hg, toUnitTorus_add]
    rw [heq] at hD
    simpa only [one_smul, toUnitTorus_add] using hD
  · intro h x
    change HasDerivAt (fun s : ℝ => HalfHolder.eval (toUnitTorus (x + s • u)) f)
      (HalfHolder.eval (toUnitTorus x) df) 0
    simpa only [toUnitTorus_add, zero_smul, toUnitTorus_zero, add_zero] using h (toUnitTorus x) 0

/-- The average of the actual directional derivative along the translation
segment gives its nonzero finite difference quotient, for either sign of the step. -/
theorem HalfHolder.eval_torusDifference_eq_integral (f df : HalfHolder A E) (u : Vec3)
    (hline : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s)
    {h : ℝ} (hh : h ≠ 0) (a : A) :
    HalfHolder.eval a
      (halfHolderTorusDifference u h f) =
      ∫ s in (0 : ℝ)..1, HalfHolder.eval (a + toUnitTorus ((s * h) • u)) df := by
  have hd (s : ℝ) : HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus ((r * h) • u)) f)
      (h • HalfHolder.eval (a + toUnitTorus ((s * h) • u)) df) s := by
    simpa only [Function.comp_def, id_eq, one_mul] using
      (hline a (s * h)).scomp s ((hasDerivAt_id s).mul_const h)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s)
    (((continuous_torusDirection df u h a).const_smul h).intervalIntegrable (0 : ℝ) 1)
  rw [intervalIntegral.integral_smul] at hFTC
  simp only [one_mul, zero_mul, zero_smul, toUnitTorus_zero, add_zero] at hFTC
  rw [eval_halfHolderTorusDifference,
    ← hFTC, smul_smul, inv_mul_cancel₀ hh, one_smul]

omit [CompleteSpace E] in
private theorem norm_torusDirection_integral_le {g : ℝ → E} {C : ℝ}
    (hC : ∀ s ∈ Ioc (0 : ℝ) 1, ‖g s‖ ≤ C) :
    ‖∫ s in (0 : ℝ)..1, g s‖ ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (f := g)
    (fun s hs => hC s (by simpa only [uIoc_of_le zero_le_one] using hs))
  simpa only [sub_zero, abs_one, mul_one] using h

/-- For actual directional derivatives in the half-Hölder space, the quotient
is bounded in that norm and approaches the derivative in the supremum norm. -/
theorem HalfHolder.torusDifference_bounds_of_hasDerivAt (f df : HalfHolder A E) (u : Vec3)
    (hline : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s)
    {h : ℝ} (hh : h ≠ 0) :
    let δ := halfHolderTorusDifference u h f
    ‖δ‖ ≤ ‖df‖ ∧ ‖(δ - df).val.1‖ ≤ ‖df‖ * Real.sqrt (|h| * ‖u‖) := by
  intro δ
  let D (a : A) (s : ℝ) := HalfHolder.eval (a + toUnitTorus ((s * h) • u)) df
  have hD (a : A) : Continuous (D a) := continuous_torusDirection df u h a
  have hhD (a : A) : HalfHolder.eval a δ = ∫ s in (0 : ℝ)..1, D a s :=
    HalfHolder.eval_torusDifference_eq_integral f df u hline hh a
  have hdf := (HalfHolder.norm_le_iff (norm_nonneg df)).mp le_rfl
  constructor
  · apply (HalfHolder.norm_le_iff (norm_nonneg df)).mpr
    constructor
    · intro a
      change ‖HalfHolder.eval a δ‖ ≤ ‖df‖
      rw [hhD]
      exact norm_torusDirection_integral_le fun s _ => hdf.1 (a + toUnitTorus ((s * h) • u))
    · intro a b
      change ‖HalfHolder.eval a δ - HalfHolder.eval b δ‖ ≤ _
      rw [hhD, hhD, ← intervalIntegral.integral_sub ((hD a).intervalIntegrable _ _)
        ((hD b).intervalIntegrable _ _)]
      apply norm_torusDirection_integral_le
      intro s _
      simpa only [D, HalfHolder.eval_apply, dist_add_right] using
        hdf.2 (a + toUnitTorus ((s * h) • u)) (b + toUnitTorus ((s * h) • u))
  · apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
    intro a
    change ‖HalfHolder.eval a (δ - df)‖ ≤ _
    rw [map_sub, hhD]
    have hconst : (∫ _s in (0 : ℝ)..1, HalfHolder.eval a df) = HalfHolder.eval a df := by simp
    nth_rw 1 [← hconst]
    rw [← intervalIntegral.integral_sub ((hD a).intervalIntegrable _ _) intervalIntegrable_const]
    apply norm_torusDirection_integral_le
    intro s hs
    have hstep : ‖(s * h) • u‖ ≤ |h| * ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hs.1.le]
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hs.2 (abs_nonneg h))
        (norm_nonneg u)
    exact (HalfHolder.norm_eval_torusTranslate_lift_sub_le df ((s * h) • u) a).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hstep) (norm_nonneg df))

/-- The preceding quantitative remainder gives convergence of the quotients
in the supremum norm along the punctured time filter at zero. -/
theorem HalfHolder.tendsto_torusDifference_sub_sup_of_hasDerivAt
    (f df : HalfHolder A E) (u : Vec3)
    (hline : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s) :
    Tendsto (fun h => ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
  let R (h : ℝ) := ‖df‖ * Real.sqrt (|h| * ‖u‖)
  have hR : Continuous R :=
    continuous_const.mul (Real.continuous_sqrt.comp (continuous_abs.mul continuous_const))
  have hR0 : R 0 = 0 := by simp [R]
  have hlim : Tendsto R (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    have h : Tendsto R (𝓝[≠] (0 : ℝ)) (𝓝 (R 0)) :=
      (hR.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
    simpa only [hR0] using h
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact (HalfHolder.torusDifference_bounds_of_hasDerivAt f df u hline hh).2

end TorusDerivativeData

section SpatialDerivative

local notation "A" => UnitAddTorus (Fin 3)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "W" => HalfHolder A H
local notation "W₂" => Lp H 2 unitTorusMeasure
local notation "M" => HalfHolder A (H →L[ℝ] H)
omit [CompleteSpace H] in
theorem freezingProjection_fixed_of_torusDifference_limit_of_haar_bound
    (P : W →L[ℝ] W)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (f df : W) (hfix : P f = f)
    (hDf : Tendsto (fun h => ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    P df = df := by
  let δ (h : ℝ) := halfHolderTorusDifference u h f
  have hδ (h : ℝ) : P (δ h) = δ h :=
    endpointSpatialDifference_fixed P _ (hcomm h) hfix h
  have hIdentity (h : ℝ) : df - P df = P (δ h - df) - (δ h - df) := by
    rw [map_sub, hδ]
    abel
  have hBound (h : ℝ) : ‖freezingHaarEmbedding (df - P df)‖ ≤
      (C₂ + 1) * ‖(δ h - df).val.1‖ := by
    rw [hIdentity h, map_sub]
    calc
      _ ≤ ‖freezingHaarEmbedding (P (δ h - df))‖ + ‖freezingHaarEmbedding (δ h - df)‖ :=
        norm_sub_le _ _
      _ ≤ C₂ * ‖(δ h - df).val.1‖ + ‖(δ h - df).val.1‖ := add_le_add
        ((hWeak _).trans (mul_le_mul_of_nonneg_left (norm_freezingHaarEmbedding_le_sup _) hC₂))
        (norm_freezingHaarEmbedding_le_sup _)
      _ = _ := by rw [add_mul, one_mul]
  have hLimit : Tendsto (fun _ : ℝ => ‖freezingHaarEmbedding (df - P df)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    refine squeeze_zero (fun _ => norm_nonneg _) hBound ?_
    simpa only [mul_zero] using (tendsto_const_nhds (x := C₂ + 1)).mul hDf
  have hZero : ‖freezingHaarEmbedding (df - P df)‖ = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hLimit
  have hDiff : df - P df = 0 := freezingHaarEmbedding_injective (by
    rw [map_zero]
    exact norm_eq_zero.mp hZero)
  exact (sub_eq_zero.mp hDiff).symm

/-- First spatial derivative of the projected solution with the differentiated
equation and its tame bound. The data hypotheses concern actual derivatives
along each translated line through a torus label. -/
theorem endpointSpatialDerivative_of_haar_bound
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (hpair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (B dB : M) (v f df : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hv : P v = v) (heq : P (B.coefficientMul v) = f)
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hf : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s)
    (hB : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) B)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dB) s) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) ∧
      ∀ x : Vec3, HasLineDerivAt ℝ (fun y : Vec3 => HalfHolder.eval (toUnitTorus y) v)
        (HalfHolder.eval (toUnitTorus x) w) x u := by
  have hfBound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h f‖ ≤ ‖df‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (HalfHolder.torusDifference_bounds_of_hasDerivAt f df u hf hh).1
  have hBBound : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖halfHolderTorusDifference u h B‖ ≤ ‖dB‖ := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (HalfHolder.torusDifference_bounds_of_hasDerivAt B dB u hB hh).1
  have hfLim := HalfHolder.tendsto_torusDifference_sub_sup_of_hasDerivAt f df u hf
  have hBLim := HalfHolder.tendsto_torusDifference_sub_sup_of_hasDerivAt B dB u hB
  have hdf := freezingProjection_fixed_of_torusDifference_limit_of_haar_bound P C₂ hC₂ hWeak u hcomm f df
    (by rw [← heq, hP]) hfLim
  exact endpointSpatialDerivative_of_differenceLimits_of_haar_bound P hP C₂ hC₂ hWeak hpair
    B dB v f df u hcomm hv heq hdf S hS hμ hcoercive hfBound hBBound hfLim
    (tendsto_torusDifference_coefficientMul_sub_sup B dB v u hBBound hBLim)

omit [CompleteSpace H] in
theorem freezingProjection_fixed_of_torusDifference_limit
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z))
    (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (f df : W) (hfix : P f = f)
    (hDf : Tendsto (fun h => ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0)) :
    P df = df :=
  freezingProjection_fixed_of_torusDifference_limit_of_haar_bound P ‖Q‖ Q.opNorm_nonneg
    (freezingProjection_haar_norm_le_of_compatible P Q hPQ) u hcomm f df hfix hDf

theorem endpointSpatialDerivative
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z))
    (hself : ∀ z w, ⟪Q z, w⟫_ℝ = ⟪z, Q w⟫_ℝ)
    (B dB : M) (v f df : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hv : P v = v) (heq : P (B.coefficientMul v) = f)
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hf : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s)
    (hB : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) B)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dB) s) :
    ∃ w : W, P w = w ∧
      P (B.coefficientMul w) = df - P (dB.coefficientMul v) ∧
      ‖w‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖df‖ + 2 * ‖P‖ * ‖dB‖ * ‖v‖) ∧
      ∀ x : Vec3, HasLineDerivAt ℝ (fun y : Vec3 => HalfHolder.eval (toUnitTorus y) v)
        (HalfHolder.eval (toUnitTorus x) w) x u :=
  endpointSpatialDerivative_of_haar_bound P hP ‖Q‖ Q.opNorm_nonneg
    (freezingProjection_haar_norm_le_of_compatible P Q hPQ)
    (freezingHaarEmbedding_projected_pairing P Q hPQ hself) B dB v f df u hcomm
    hv heq S hS hμ hcoercive hf hB

end SpatialDerivative

section ProjectionDirectional

local notation "A" => UnitAddTorus (Fin 3)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "W" => HalfHolder A H
local notation "W₂" => Lp H 2 unitTorusMeasure
/-- A bounded projection commuting with torus translations and bounded
in the spatial L² norm commutes with actual line differentiation. -/
theorem freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound
    (P : W →L[ℝ] W)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (f df : W)
    (hf : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s) :
    ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) (P f))
      (HalfHolder.eval (a + toUnitTorus (s • u)) (P df)) s := by
  let U (h : ℝ) := halfHolderTorusDifference u h (P f) - P df
  have hU (h : ℝ) : U h = P (halfHolderTorusDifference u h f - df) := by
    simp only [U, halfHolderTorusDifference, halfHolderTranslateDifference,
      map_sub, map_smul, hcomm]
  let C := ‖P‖ * (‖df‖ + ‖df‖)
  have hC : 0 ≤ C := mul_nonneg P.opNorm_nonneg (add_nonneg (norm_nonneg df) (norm_nonneg df))
  have hB : ∀ᶠ h in 𝓝[≠] (0 : ℝ), ‖U h‖ ≤ C := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hd := (HalfHolder.torusDifference_bounds_of_hasDerivAt f df u hf hh).1
    rw [hU]
    exact (P.le_opNorm _).trans (mul_le_mul_of_nonneg_left
      ((norm_sub_le _ _).trans (add_le_add hd le_rfl)) P.opNorm_nonneg)
  have hF : Tendsto (fun h => ‖freezingHaarEmbedding (U h)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    have hS := HalfHolder.tendsto_torusDifference_sub_sup_of_hasDerivAt f df u hf
    refine squeeze_zero (g := fun h =>
      C₂ * ‖(halfHolderTorusDifference u h f - df).val.1‖)
      (fun _ => norm_nonneg _) (fun h => ?_) ?_
    · rw [hU]
      exact (hWeak _).trans
        (mul_le_mul_of_nonneg_left (norm_freezingHaarEmbedding_le_sup _) hC₂)
    · simpa only [mul_zero] using (tendsto_const_nhds (x := C₂)).mul hS
  have hSup := tendsto_sup_norm_zero_of_tendsto_freezingHaarEmbedding_norm hC hB hF
  apply (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt (P f) (P df) u).mp
  intro x
  apply hasLineDerivAt_iff_tendsto_slope_zero.mpr
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hSup) ε hε] with h hh
  rw [dist_zero_right, Real.norm_of_nonneg (norm_nonneg _)] at hh
  rw [dist_eq_norm, toUnitTorus_add, ← eval_halfHolderTorusDifference, ← map_sub]
  exact ((U h).val.1.norm_coe_le_norm (toUnitTorus x)).trans_lt hh

theorem freezingProjection_preserves_torusDirectionalDerivative
    (P : W →L[ℝ] W) (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z))
    (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (f df : W)
    (hf : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) f)
      (HalfHolder.eval (a + toUnitTorus (s • u)) df) s) :
    ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) (P f))
      (HalfHolder.eval (a + toUnitTorus (s • u)) (P df)) s :=
  freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound P ‖Q‖ Q.opNorm_nonneg
    (freezingProjection_haar_norm_le_of_compatible P Q hPQ) u hcomm f df hf

end ProjectionDirectional

section SecondMixedDerivative

local notation "A" => UnitAddTorus (Fin 3)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "W" => HalfHolder A H
local notation "M" => HalfHolder A (H →L[ℝ] H)
local notation "W₂" => MeasureTheory.Lp H 2 unitTorusMeasure

/-- Differentiating the first projected equation gives an actual second mixed
derivative. Here `w₁` is the first derivative being differentiated, and `w₂`
is the derivative of the original velocity in the new direction. -/
theorem endpointSpatialSecondMixedDerivative_of_haar_bound
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hWeak : ∀ z, ‖freezingHaarEmbedding (P z)‖ ≤ C₂ * ‖freezingHaarEmbedding z‖)
    (hpair : ∀ z (w : freezingFixedSpace P),
      ⟪freezingHaarEmbedding (P z), freezingHaarEmbedding w.val⟫_ℝ =
        ⟪freezingHaarEmbedding z, freezingHaarEmbedding w.val⟫_ℝ)
    (B dB₁ dB₂ ddB : M) (v w₁ w₂ df₁ ddf : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hw₁ : P w₁ = w₁)
    (hEq : P (B.coefficientMul w₁) = df₁ - P (dB₁.coefficientMul v))
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hdf₁ : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) df₁)
      (HalfHolder.eval (a + toUnitTorus (s • u)) ddf) s)
    (hB : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) B)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dB₂) s)
    (hdB₁ : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) dB₁)
      (HalfHolder.eval (a + toUnitTorus (s • u)) ddB) s)
    (hv : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) v)
      (HalfHolder.eval (a + toUnitTorus (s • u)) w₂) s) :
    let dg := ddf - P (ddB.coefficientMul v + dB₁.coefficientMul w₂)
    ∃ w₁₂ : W, P w₁₂ = w₁₂ ∧
      P (B.coefficientMul w₁₂) = dg - P (dB₂.coefficientMul w₁) ∧
      ‖w₁₂‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖dg‖ + 2 * ‖P‖ * ‖dB₂‖ * ‖w₁‖) ∧
      ∀ (a : A) (s : ℝ), HasDerivAt
        (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) w₁)
        (HalfHolder.eval (a + toUnitTorus (s • u)) w₁₂) s := by
  intro dg
  let g := df₁ - P (dB₁.coefficientMul v)
  let c := dB₁.coefficientMul v
  let dc := ddB.coefficientMul v + dB₁.coefficientMul w₂
  have hc (a : A) (s : ℝ) : HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) c)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dc) s := by
    simpa only [c, dc, map_add, HalfHolder.eval_coefficientMul] using
      (hdB₁ a s).clm_apply (hv a s)
  have hPc := freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound P C₂ hC₂ hWeak u hcomm c dc hc
  have hg (a : A) (s : ℝ) : HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) g)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dg) s := by
    have h := (hdf₁ a s).sub (hPc a s)
    change HasDerivAt (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) df₁ -
      HalfHolder.eval (a + toUnitTorus (r • u)) (P c)) _ s at h
    simpa only [g, dg, c, dc, map_sub] using h
  obtain ⟨w, hfix, heq, hbound, hw⟩ := endpointSpatialDerivative_of_haar_bound P hP C₂ hC₂ hWeak hpair
    B dB₂ w₁ g dg u hcomm hw₁ hEq S hS hμ hcoercive hg hB
  exact ⟨w, hfix, heq, hbound,
    (HalfHolder.hasLineDerivAt_lift_iff_torusLine_hasDerivAt w₁ w u).mp hw⟩

theorem endpointSpatialSecondMixedDerivative
    (P : W →L[ℝ] W) (hP : ∀ z, P (P z) = P z)
    (Q : W₂ →L[ℝ] W₂)
    (hPQ : ∀ z, freezingHaarEmbedding (P z) = Q (freezingHaarEmbedding z))
    (hself : ∀ z w, ⟪Q z, w⟫_ℝ = ⟪z, Q w⟫_ℝ)
    (B dB₁ dB₂ ddB : M) (v w₁ w₂ df₁ ddf : W) (u : Vec3)
    (hcomm : ∀ (h : ℝ) z, P (HalfHolder.torusTranslate (toUnitTorus (h • u)) z) =
      HalfHolder.torusTranslate (toUnitTorus (h • u)) (P z))
    (hw₁ : P w₁ = w₁)
    (hEq : P (B.coefficientMul w₁) = df₁ - P (dB₁.coefficientMul v))
    (S : freezingFixedSpace P ≃L[ℝ] freezingFixedSpace P)
    (hS : (S : freezingFixedSpace P →L[ℝ] freezingFixedSpace P) =
      freezingCompression P B.coefficientMul hP)
    {μ : ℝ} (hμ : 0 < μ)
    (hcoercive : ∀ (z : freezingFixedSpace P) a, μ * ‖HalfHolder.eval a z.val‖ ^ 2 ≤
      ⟪HalfHolder.eval a B (HalfHolder.eval a z.val), HalfHolder.eval a z.val⟫_ℝ)
    (hdf₁ : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) df₁)
      (HalfHolder.eval (a + toUnitTorus (s • u)) ddf) s)
    (hB : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) B)
      (HalfHolder.eval (a + toUnitTorus (s • u)) dB₂) s)
    (hdB₁ : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) dB₁)
      (HalfHolder.eval (a + toUnitTorus (s • u)) ddB) s)
    (hv : ∀ (a : A) (s : ℝ), HasDerivAt
      (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) v)
      (HalfHolder.eval (a + toUnitTorus (s • u)) w₂) s) :
    let dg := ddf - P (ddB.coefficientMul v + dB₁.coefficientMul w₂)
    ∃ w₁₂ : W, P w₁₂ = w₁₂ ∧
      P (B.coefficientMul w₁₂) = dg - P (dB₂.coefficientMul w₁) ∧
      ‖w₁₂‖ ≤ ‖(S.symm : freezingFixedSpace P →L[ℝ] freezingFixedSpace P)‖ *
        (‖dg‖ + 2 * ‖P‖ * ‖dB₂‖ * ‖w₁‖) ∧
      ∀ (a : A) (s : ℝ), HasDerivAt
        (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) w₁)
        (HalfHolder.eval (a + toUnitTorus (s • u)) w₁₂) s :=
  endpointSpatialSecondMixedDerivative_of_haar_bound P hP ‖Q‖ Q.opNorm_nonneg
    (freezingProjection_haar_norm_le_of_compatible P Q hPQ)
    (freezingHaarEmbedding_projected_pairing P Q hPQ hself) B dB₁ dB₂ ddB v w₁ w₂ df₁ ddf
    u hcomm hw₁ hEq S hS hμ hcoercive hdf₁ hB hdB₁ hv

end SecondMixedDerivative

section FourierTranslation

open UnitAddTorus

local notation "A" => UnitAddTorus (Fin 3)
local notation "Frequency" => (Fin 3 → ℤ)

local instance spatialTranslationHaar : Measure.IsAddHaarMeasure unitTorusMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure
    (Measure.pi (fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle))))

variable {H HC : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup HC] [NormedSpace ℂ HC] [CompleteSpace HC]

private theorem spatialFourierCharacter_add (k : Frequency) (z w : A) :
    mFourier k (z + w) = mFourier k z * mFourier k w := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.add_apply, fourier_apply, zsmul_add,
    AddCircle.toCircle_add, Circle.coe_mul, Finset.prod_mul_distrib]

omit [CompleteSpace H] [CompleteSpace HC] in
/-- Translating the periodic lift rotates a complex Fourier coefficient by the character. -/
theorem complexifiedHalfHolderFourierCoeff_torusTranslate
    (X : EndpointComplexification H HC) (f : HalfHolder A H) (b : A) (k : Frequency) :
    complexifiedHalfHolderFourierCoeff X (HalfHolder.torusTranslate b f) k =
      mFourier k b • complexifiedHalfHolderFourierCoeff X f k := by
  let g := fun a : A => (mFourier (-k) (-b) * mFourier (-k) a) • X.ofReal (HalfHolder.eval a f)
  have hphase : mFourier (-k) (-b) = mFourier k b := by rw [mFourier_neg_arg, neg_neg]
  rw [← hphase]
  change (∫ a, mFourier (-k) a • HalfHolder.eval a (HalfHolder.map X.ofReal
    (HalfHolder.torusTranslate b f)) ∂unitTorusMeasure) =
    mFourier (-k) (-b) • ∫ a, mFourier (-k) a • HalfHolder.eval a (HalfHolder.map X.ofReal f)
      ∂unitTorusMeasure
  rw [← integral_smul]
  simp only [HalfHolder.eval_map, ← mul_smul]
  change _ = (∫ a, g a ∂unitTorusMeasure)
  rw [← integral_add_right_eq_self g b]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  change mFourier (-k) a • X.ofReal (HalfHolder.eval a (HalfHolder.torusTranslate b f)) =
    (mFourier (-k) (-b) * mFourier (-k) (a + b)) • X.ofReal (HalfHolder.eval (a + b) f)
  rw [HalfHolder.eval_torusTranslate, ← spatialFourierCharacter_add, ← add_assoc,
    add_comm (-b) a, add_assoc, neg_add_cancel, add_zero]

omit [CompleteSpace H] in
/-- A frequency-by-frequency complex Fourier law makes a real half-Hölder
operator commute with actual torus translation. -/
theorem halfHolder_torusTranslate_commutes_of_complexFourierCoefficient
    (X : EndpointComplexification H HC)
    (P : HalfHolder A H →L[ℝ] HalfHolder A H) (σ : Frequency → HC →L[ℂ] HC)
    (hP : ∀ f k, complexifiedHalfHolderFourierCoeff X (P f) k =
      σ k (complexifiedHalfHolderFourierCoeff X f k))
    (b : A) (f : HalfHolder A H) :
    P (HalfHolder.torusTranslate b f) = HalfHolder.torusTranslate b (P f) := by
  have hEq : HalfHolder.map X.ofReal (P (HalfHolder.torusTranslate b f)) =
      HalfHolder.map X.ofReal (HalfHolder.torusTranslate b (P f)) := by
    apply eq_halfHolder_of_mFourierCoeff_eq
    intro k
    change complexifiedHalfHolderFourierCoeff X (P (HalfHolder.torusTranslate b f)) k =
      complexifiedHalfHolderFourierCoeff X (HalfHolder.torusTranslate b (P f)) k
    rw [hP, complexifiedHalfHolderFourierCoeff_torusTranslate,
      complexifiedHalfHolderFourierCoeff_torusTranslate, hP, map_smul]
  apply HalfHolder.ext
  intro a
  have h := congrArg (fun w => X.re (HalfHolder.eval a w)) hEq
  simpa only [HalfHolder.eval_map, X.re_ofReal] using h

/-- The corresponding real character law also gives translation commutation. -/
theorem halfHolder_torusTranslate_commutes_of_realFourierCoefficient
    (X : EndpointComplexification H HC)
    (P : HalfHolder A H →L[ℝ] HalfHolder A H) (S : Vec3 → H →L[ℝ] H)
    (hP : ∀ (f : HalfHolder A H) (k : Frequency) (c : ℂ),
      (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a (P f) ∂unitTorusMeasure) =
        S (latticeVector k)
          (∫ a, endpointRealFourierCharacter k c a • HalfHolder.eval a f ∂unitTorusMeasure))
    (b : A) (f : HalfHolder A H) :
    P (HalfHolder.torusTranslate b f) = HalfHolder.torusTranslate b (P f) :=
  halfHolder_torusTranslate_commutes_of_complexFourierCoefficient X P
    (fun k => X.extendOperator (S (latticeVector k)))
    (complexifiedHalfHolderFourierCoeff_multiplier_of_realCharacterMoments X P S hP) b f

end FourierTranslation

end

end TorusEuler

import TorusEuler.EndpointStrongWeakAgreement
import TorusEuler.EndpointTorusCoercivity
import TorusEuler.EndpointPrimitiveAdjoint
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Ring

/-! The labelwise kinetic and vorticity path operator of Appendix A.2. -/

open ContinuousLinearMap MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

noncomputable section

set_option maxHeartbeats 1000000

local notation "A" => UnitAddTorus (Fin 3)
local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "PathOperator(" T ")" => (Path(T) →L[ℝ] Path(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (PathOperator(T))
local notation "Coefficient" => (Vec3 →L[ℝ] Vec3)
local notation "Slab(" T ")" => (Set.prod (Icc (0 : ℝ) T) (univ : Set A))

/-- The labelwise coefficient (K-JOmega) acting on time paths. -/
def endpointMixedPathCoefficient {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) : MixedCoefficient(T) :=
  Kmix - HalfHolder.map ((ContinuousLinearMap.mul ℝ (PathOperator(T))) (endpointPrimitiveLp hT)) Ωmix

@[simp]
theorem endpointMixedPathCoefficient_eval {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) (a : A) :
    HalfHolder.eval a (endpointMixedPathCoefficient hT Kmix Ωmix) =
      HalfHolder.eval a Kmix - (endpointPrimitiveLp hT).comp (HalfHolder.eval a Ωmix) := by
  rw [endpointMixedPathCoefficient, map_sub, HalfHolder.eval_map]
  rfl

/-- Multiplication by the labelwise path coefficient gives the actual mixed operator. -/
theorem endpointMixedPathCoefficient_coefficientMul {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) :
    (endpointMixedPathCoefficient hT Kmix Ωmix).coefficientMul =
      endpointMixedProductOperator hT Kmix Ωmix := by
  ext1 v
  apply HalfHolder.ext
  intro a
  simp only [endpointMixedProductOperator, _root_.sub_apply, ContinuousLinearMap.comp_apply, map_sub,
    HalfHolder.eval_coefficientMul, endpointMixedPathCoefficient_eval, endpointMixedIntegration,
    HalfHolder.eval_map]

/-- A uniform Lipschitz estimate of the time-slice operators passes to their
labelwise realization as operators on temporal L². -/
theorem norm_endpointMixedCoefficient_sub_le_of_lipschitz {T M L : ℝ}
    (K : ℝ × A → Coefficient)
    (hKt : ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (TimeMeasure(T)))
    (hKsup : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖K (t, a)‖ ≤ M)
    (hKdif : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ M * Real.sqrt (dist a b))
    (hM : 0 ≤ M) (hL : 0 ≤ L)
    (hKlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ L * dist a b)
    (a b : A) :
    let Kmix := endpointMixedCoefficient K hKt hKsup hKdif hM
    ‖HalfHolder.eval a Kmix - HalfHolder.eval b Kmix‖ ≤ L * dist a b := by
  intro Kmix
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hL dist_nonneg)
  intro v
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [endpointMixedCoefficient_apply_ae K hKt hKsup hKdif hM a v,
    endpointMixedCoefficient_apply_ae K hKt hKsup hKdif hM b v,
    ae_restrict_mem (μ := volume) measurableSet_Ioc,
    Lp.coeFn_sub (HalfHolder.eval a Kmix v) (HalfHolder.eval b Kmix v)]
    with t hat hbt ht hsub
  change HalfHolder.eval a Kmix v t = K (t, a) (v t) at hat
  change HalfHolder.eval b Kmix v t = K (t, b) (v t) at hbt
  rw [_root_.sub_apply, hsub, Pi.sub_apply, hat, hbt, ← _root_.sub_apply]
  exact ((K (t, a) - K (t, b)).le_opNorm _).trans
    (mul_le_mul_of_nonneg_right (hKlip t (Ioc_subset_Icc_self ht) a b) (norm_nonneg _))

/-- The uniform norm of the primitive controls the contribution of the vorticity coefficient. -/
theorem norm_endpointMixedPathCoefficient_sup_le {T CK CΩ : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) (hCK : 0 ≤ CK) (hCΩ : 0 ≤ CΩ)
    (bK : ∀ a, ‖HalfHolder.eval a Kmix‖ ≤ CK) (bΩ : ∀ a, ‖HalfHolder.eval a Ωmix‖ ≤ CΩ) :
    ‖(endpointMixedPathCoefficient hT Kmix Ωmix).val.1‖ ≤ CK + T * CΩ := by
  refine (BoundedContinuousFunction.norm_le (by positivity)).mpr (fun a => ?_)
  change ‖HalfHolder.eval a (endpointMixedPathCoefficient hT Kmix Ωmix)‖ ≤ _
  rw [endpointMixedPathCoefficient_eval]
  have hJΩ :
      ‖(endpointPrimitiveLp hT).comp (HalfHolder.eval a Ωmix)‖ ≤ T * CΩ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (norm_endpointPrimitiveLp_le (E := Vec3) hT) (bΩ a) (norm_nonneg _) hT)
  exact (norm_sub_le _ _).trans (add_le_add (bK a) hJΩ)

/-- The Lipschitz constant of the path coefficient is bounded by the sum of
the kinetic constant and the vorticity constant times the interval length. -/
theorem norm_endpointMixedPathCoefficient_sub_le {T LK LΩ : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T))
    (dK : ∀ a b, ‖HalfHolder.eval a Kmix - HalfHolder.eval b Kmix‖ ≤ LK * dist a b)
    (dΩ : ∀ a b, ‖HalfHolder.eval a Ωmix - HalfHolder.eval b Ωmix‖ ≤ LΩ * dist a b)
    (a b : A) :
    ‖HalfHolder.eval a (endpointMixedPathCoefficient hT Kmix Ωmix) -
      HalfHolder.eval b (endpointMixedPathCoefficient hT Kmix Ωmix)‖ ≤ (LK + T * LΩ) * dist a b := by
  simp only [endpointMixedPathCoefficient_eval]
  let J : PathOperator(T) := endpointPrimitiveLp hT
  let Kₐ := HalfHolder.eval a Kmix
  let Kᵦ := HalfHolder.eval b Kmix
  let Ωₐ := HalfHolder.eval a Ωmix
  let Ωᵦ := HalfHolder.eval b Ωmix
  change ‖(Kₐ - J * Ωₐ) - (Kᵦ - J * Ωᵦ)‖ ≤ _
  rw [show (Kₐ - J * Ωₐ) - (Kᵦ - J * Ωᵦ) =
      (Kₐ - Kᵦ) - J * (Ωₐ - Ωᵦ) by rw [mul_sub]; abel]
  have hJΩ : ‖J * (HalfHolder.eval a Ωmix - HalfHolder.eval b Ωmix)‖ ≤ T * (LΩ * dist a b) :=
    (norm_mul_le _ _).trans
      (mul_le_mul (norm_endpointPrimitiveLp_le (E := Vec3) hT) (dΩ a b) (norm_nonneg _) hT)
  exact ((norm_sub_le _ _).trans (add_le_add (dK a b) hJΩ)).trans_eq (by ring)

set_option maxHeartbeats 800000 in
/-- For a zero-time-mean path, the pairing with the physical path coefficient
is the label energy. The sign follows from time integration by parts. -/
theorem endpointMixedPathCoefficient_inner_eq_energy {T : ℝ} (hT : 0 ≤ T)
    (Kmix Ωmix : MixedCoefficient(T)) (a : A) (F M : ℝ → Coefficient)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    (v : Path(T)) (hv : endpointIntegral T v = 0)
    (hK : (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
      fun t => kineticForm (F t) (v t))
    (hΩ : (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TimeMeasure(T)]
      fun t => vorticityForm (F t) (M t) (v t)) :
    ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT Kmix Ωmix) v, v⟫_ℝ =
      endpointL2Energy hT F M cF cM v := by
  have hkin : ⟪HalfHolder.eval a Kmix v, v⟫_ℝ = ‖endpointTimeMultiplier F cF v‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hK, endpointTimeMultiplier_apply_ae F cF v] with t ht hf
    change ⟪HalfHolder.eval a Kmix v t, v t⟫_ℝ = ⟪endpointTimeMultiplier F cF v t,
      endpointTimeMultiplier F cF v t⟫_ℝ
    rw [ht, show endpointTimeMultiplier F cF v t = F t (v t) from hf,
      inner_kineticForm_self, real_inner_self_eq_norm_sq]
  have hskew : HalfHolder.eval a Ωmix v =
      endpointTimeMultiplier (fun t => endpointSkew (F t) (M t)) (continuousOn_endpointSkew cF cM) v :=
    Lp.ext (hΩ.trans (endpointTimeMultiplier_apply_ae _ _ _).symm)
  rw [endpointMixedPathCoefficient_eval, _root_.sub_apply, ContinuousLinearMap.comp_apply, inner_sub_left,
    endpointPrimitiveLp_inner_eq_neg_inner hT _ _ hv, sub_neg_eq_add, hkin, hskew]
  rfl

/-- The physical coefficient has the checked label energy lower bound on every
zero-time-mean path, including the spatial zero mode. -/
theorem endpointMixedPathCoefficient_coercive {T D L : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (Kmix Ωmix : MixedCoefficient(T)) (a : A) (F G M Mt : ℝ → Coefficient)
    (cF : ContinuousOn F (Icc 0 T)) (cM : ContinuousOn M (Icc 0 T))
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T))
    (hGF : ∀ t ∈ Icc 0 T, (G t).comp (F t) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ t ∈ Icc 0 T, ‖G t‖ ≤ D) (hMbound : ∀ t ∈ Icc 0 T, ‖M t‖ ≤ L)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : Vec3, ⟪endpointHessian (M t) (Mt t) x, x⟫_ℝ ≤ ‖x‖ ^ 2)
    (v : Path(T)) (hv : endpointIntegral T v = 0)
    (hK : (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
      fun t => kineticForm (F t) (v t))
    (hΩ : (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TimeMeasure(T)]
      fun t => vorticityForm (F t) (M t) (v t)) :
    (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖v‖ ^ 2 ≤
      ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT.le Kmix Ωmix) v, v⟫_ℝ := by
  rw [endpointMixedPathCoefficient_inner_eq_energy hT.le Kmix Ωmix a F M cF cM v hv hK hΩ]
  exact endpointL2Energy_coercive hT hT₁ hD hL cF cM hF hM hMt hGF hGbound hMbound hupper v hv

section SpatialBounds

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
private theorem norm_operator_mul_sub_mul_le (U B C D : E →L[ℝ] E) :
    ‖U * B - C * D‖ ≤ ‖U - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  have h : U * B - C * D = (U - C) * B + C * (B - D) := by
    rw [sub_mul, mul_sub]
    abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))

private theorem norm_adjoint_sub_self_le (M : E →L[ℝ] E) :
    ‖M.adjoint - M‖ ≤ 2 * ‖M‖ := by
  simpa only [LinearIsometryEquiv.norm_map, two_mul] using norm_sub_le M.adjoint M

private theorem norm_adjoint_sub_self_difference_le (M N : E →L[ℝ] E) :
    ‖(M.adjoint - M) - (N.adjoint - N)‖ ≤ 2 * ‖M - N‖ := by
  have h : (M.adjoint - M) - (N.adjoint - N) = (M - N).adjoint - (M - N) := by
    simp only [map_sub]
    abel
  rw [h]
  exact norm_adjoint_sub_self_le (M - N)

/-- Uniform deformation norm bound for the kinetic coefficient. -/
theorem norm_kineticForm_le {F : E →L[ℝ] E} {F₀ : ℝ} (hF : ‖F‖ ≤ F₀) :
    ‖kineticForm F‖ ≤ F₀ ^ 2 := by
  rw [norm_kineticForm]
  exact pow_le_pow_left₀ (norm_nonneg _) hF 2

/-- A bound on the difference of two deformations transfers to their kinetic coefficients. -/
theorem norm_kineticForm_sub_le {F G : E →L[ℝ] E} {F₀ F₁ d : ℝ}
    (hF : ‖F‖ ≤ F₀) (hG : ‖G‖ ≤ F₀) (hFG : ‖F - G‖ ≤ F₁ * d) :
    ‖kineticForm F - kineticForm G‖ ≤ (2 * F₀ * F₁) * d := by
  have hF₀ : 0 ≤ F₀ := (norm_nonneg _).trans hF
  have hF₁d : 0 ≤ F₁ * d := (norm_nonneg _).trans hFG
  have hAdj : ‖F.adjoint - G.adjoint‖ = ‖F - G‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  calc
    _ ≤ ‖F.adjoint - G.adjoint‖ * ‖F‖ + ‖G.adjoint‖ * ‖F - G‖ :=
      norm_operator_mul_sub_mul_le F.adjoint F G.adjoint G
    _ ≤ (F₁ * d) * F₀ + F₀ * (F₁ * d) := by
      rw [hAdj, LinearIsometryEquiv.norm_map]
      gcongr
    _ = _ := by ring

/-- Pointwise bound on the pulled-back skew coefficient. -/
theorem norm_vorticityForm_le {F M : E →L[ℝ] E} {F₀ M₀ : ℝ}
    (hF : ‖F‖ ≤ F₀) (hM : ‖M‖ ≤ M₀) :
    ‖vorticityForm F M‖ ≤ 2 * F₀ ^ 2 * M₀ := by
  change ‖F.adjoint * ((M.adjoint - M) * F)‖ ≤ _
  have hS := (norm_adjoint_sub_self_le M).trans (mul_le_mul_of_nonneg_left hM (by norm_num : (0 : ℝ) ≤ 2))
  have hF₀ : 0 ≤ F₀ := (norm_nonneg _).trans hF
  have hS₀ : 0 ≤ 2 * M₀ := (norm_nonneg _).trans hS
  calc
    _ ≤ ‖F.adjoint‖ * (‖M.adjoint - M‖ * ‖F‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ F₀ * ((2 * M₀) * F₀) := by
      rw [LinearIsometryEquiv.norm_map]
      gcongr
    _ = _ := by ring

/-- Bounds on differences of deformation and strain transfer to the pulled-back skew coefficient. -/
theorem norm_vorticityForm_sub_le {F G M N : E →L[ℝ] E} {F₀ F₁ M₀ M₁ d : ℝ}
    (hF : ‖F‖ ≤ F₀) (hG : ‖G‖ ≤ F₀) (hM : ‖M‖ ≤ M₀) (hN : ‖N‖ ≤ M₀)
    (hFG : ‖F - G‖ ≤ F₁ * d) (hMN : ‖M - N‖ ≤ M₁ * d) :
    ‖vorticityForm F M - vorticityForm G N‖ ≤
      (4 * F₀ * F₁ * M₀ + 2 * F₀ ^ 2 * M₁) * d := by
  let S := M.adjoint - M
  let R := N.adjoint - N
  have hS : ‖S‖ ≤ 2 * M₀ :=
    (norm_adjoint_sub_self_le M).trans (mul_le_mul_of_nonneg_left hM (by norm_num))
  have hR : ‖R‖ ≤ 2 * M₀ :=
    (norm_adjoint_sub_self_le N).trans (mul_le_mul_of_nonneg_left hN (by norm_num))
  have hSR : ‖S - R‖ ≤ 2 * (M₁ * d) :=
    (norm_adjoint_sub_self_difference_le M N).trans (mul_le_mul_of_nonneg_left hMN (by norm_num))
  have hF₀ : 0 ≤ F₀ := (norm_nonneg _).trans hF
  have hF₁d : 0 ≤ F₁ * d := (norm_nonneg _).trans hFG
  have hS₀ : 0 ≤ 2 * M₀ := (norm_nonneg _).trans hS
  have hSR₀ : 0 ≤ 2 * (M₁ * d) := (norm_nonneg _).trans hSR
  have hAdj : ‖F.adjoint - G.adjoint‖ = ‖F - G‖ := by
    rw [← map_sub, LinearIsometryEquiv.norm_map]
  have hSF : ‖S * F‖ ≤ (2 * M₀) * F₀ := (norm_mul_le _ _).trans (by gcongr)
  have hinner : ‖S * F - R * G‖ ≤ (2 * (M₁ * d)) * F₀ + (2 * M₀) * (F₁ * d) :=
    (norm_operator_mul_sub_mul_le S F R G).trans (by gcongr)
  change ‖F.adjoint * (S * F) - G.adjoint * (R * G)‖ ≤ _
  calc
    _ ≤ ‖F.adjoint - G.adjoint‖ * ‖S * F‖ + ‖G.adjoint‖ * ‖S * F - R * G‖ :=
      norm_operator_mul_sub_mul_le F.adjoint (S * F) G.adjoint (R * G)
    _ ≤ (F₁ * d) * ((2 * M₀) * F₀) + F₀ * ((2 * (M₁ * d)) * F₀ + (2 * M₀) * (F₁ * d)) := by
      rw [hAdj, LinearIsometryEquiv.norm_map]
      gcongr
    _ = _ := by ring

end SpatialBounds

/-- The physical mixed and weak flow operators carry the same representatives
in joint space-time when their two coefficients agree on the time slices. -/
theorem endpointMixedToJoint_productOperator_eq_torusFlowOperator {T : ℝ} (hT : 0 ≤ T)
    (F M : ℝ × A → Coefficient)
    (cF : ContinuousOn F (Slab(T))) (cM : ContinuousOn M (Slab(T)))
    (Kmix Ωmix : MixedCoefficient(T))
    (hKm : ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T), (fun t => HalfHolder.eval a Kmix f t)
      =ᵐ[TimeMeasure(T)] fun t => kineticForm (F (t, a)) (f t))
    (hΩm : ∀ᵐ a ∂unitTorusMeasure, ∀ f : Path(T), (fun t => HalfHolder.eval a Ωmix f t)
      =ᵐ[TimeMeasure(T)] fun t => vorticityForm (F (t, a)) (M (t, a)) (f t))
    (w : HalfHolder A (Path(T))) :
    endpointMixedToJoint T (endpointMixedProductOperator hT Kmix Ωmix w) =
      endpointTorusFlowOperator hT F M cF cM (endpointMixedToJoint T w) := by
  let K (q : ℝ × A) := kineticForm (F q)
  let Ω (q : ℝ × A) := vorticityForm (F q) (M q)
  have cAdj : Continuous (fun S : Coefficient => S.adjoint) :=
    ContinuousLinearMap.adjoint.continuous
  have cK : ContinuousOn K (Slab(T)) := (cAdj.comp_continuousOn cF).clm_comp cF
  have cΩ : ContinuousOn Ω (Slab(T)) := (cAdj.comp_continuousOn cF).clm_comp
    (((cAdj.comp_continuousOn cM).sub cM).clm_comp cF)
  have hC : IsCompact (Slab(T)) := isCompact_Icc.prod isCompact_univ
  have htime : ∀ᵐ q ∂endpointTorusMeasure T, q.1 ∈ Ioc (0 : ℝ) T :=
    (Measure.quasiMeasurePreserving_fst (μ := TimeMeasure(T)) (ν := unitTorusMeasure)).ae
      (ae_restrict_mem measurableSet_Ioc)
  have hslab : ∀ᵐ q ∂endpointTorusMeasure T, q ∈ Slab(T) :=
    htime.mono fun q hq => ⟨Ioc_subset_Icc_self hq, mem_univ q.2⟩
  have coeffData {C : ℝ × A → Coefficient} (cC : ContinuousOn C (Slab(T))) :
      AEStronglyMeasurable C (endpointTorusMeasure T) ∧
        ∃ B : ℝ, ∀ᵐ q ∂endpointTorusMeasure T, ‖C q‖ ≤ B := by
    constructor
    · have hmeas := cC.aestronglyMeasurable_of_isCompact (μ := endpointTorusMeasure T)
        hC (measurableSet_Icc.prod MeasurableSet.univ)
      rwa [Measure.restrict_eq_self_of_ae_mem hslab] at hmeas
    · obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn cC
      exact ⟨B, hslab.mono hB⟩
  obtain ⟨hK, CK, bK⟩ := coeffData cK
  obtain ⟨hΩ, CΩ, bΩ⟩ := coeffData cΩ
  rw [endpointMixedToJoint_productOperator hT K Ω hK hΩ bK bΩ Kmix Ωmix hKm hΩm]
  apply Lp.ext
  exact (endpointProductOperator_apply_ae unitTorusMeasure hT K Ω hK hΩ bK bΩ _).trans
    (endpointTorusFlowOperator_apply_ae hT F M cF cM _).symm


private theorem dist_endpointLabels_le_one (a b : A) : dist a b ≤ 1 := by
  apply (dist_pi_le_iff zero_le_one).mpr
  intro i
  rw [dist_eq_norm]
  exact (AddCircle.norm_le_half_period (1 : ℝ) (x := a i - b i) (by norm_num : (1 : ℝ) ≠ 0)).trans
    (by norm_num)

private theorem endpointMixedCoefficient_eval_norm_le {T M C : ℝ}
    (K : ℝ × A → Coefficient)
    (hKt : ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (TimeMeasure(T)))
    (hKsup : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖K (t, a)‖ ≤ M)
    (hKdif : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ M * Real.sqrt (dist a b))
    (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hKbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ a, ‖K (t, a)‖ ≤ C) (a : A) :
    ‖HalfHolder.eval a (endpointMixedCoefficient K hKt hKsup hKdif hM)‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [endpointMixedCoefficient_apply_ae K hKt hKsup hKdif hM a v,
    ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht htI
  change HalfHolder.eval a (endpointMixedCoefficient K hKt hKsup hKdif hM) v t =
    K (t, a) (v t) at ht
  rw [ht]
  exact (K (t, a)).le_of_opNorm_le (hKbound t (Ioc_subset_Icc_self htI) a) _

private theorem endpointSlab_slice_continuous {T : ℝ} {K : ℝ × A → Coefficient}
    (hK : ContinuousOn K Slab(T)) (a : A) : ContinuousOn (fun t => K (t, a)) (Icc 0 T) :=
  hK.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ ht => ⟨ht, mem_univ a⟩)

private theorem endpointMixedCoefficient_slice_aeStronglyMeasurable {T : ℝ}
    {K : ℝ × A → Coefficient} (hK : ∀ a : A, ContinuousOn (fun t => K (t, a)) (Icc 0 T)) :
    ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (TimeMeasure(T)) :=
  fun a => (hK a).aestronglyMeasurable_of_subset_isCompact isCompact_Icc measurableSet_Ioc
    Ioc_subset_Icc_self

private theorem endpointCoefficient_sqrt_bound {T L : ℝ} (K : ℝ × A → Coefficient) (hL : 0 ≤ L)
    (hK : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖K (t, a) - K (t, b)‖ ≤ L * dist a b)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) (a b : A) :
    ‖K (t, a) - K (t, b)‖ ≤ L * Real.sqrt (dist a b) := by
  simpa only [mul_one] using endpointCoefficient_halfHolder_of_lipschitz K hL
    (R := 1) zero_le_one (by simpa only [one_pow] using dist_endpointLabels_le_one) hK t ht a b

set_option maxHeartbeats 1000000 in
/-- The physical kinetic and vorticity coefficients give the half-Hölder
path operator with an explicit spatial Lipschitz bound and the labelwise
coercivity constant from Theorem 4.2. -/
theorem exists_endpointMixedPhysicalCoefficients {T D L S F₁ M₁ : ℝ}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hL : 0 ≤ L)
    (hS : 0 ≤ S) (hF₁ : 0 ≤ F₁) (hM₁ : 0 ≤ M₁)
    (F G M Mt : ℝ × A → Coefficient)
    (cF : ContinuousOn F Slab(T)) (cM : ContinuousOn M Slab(T))
    (hF : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => F (r, a))
      ((M (t, a)).comp (F (t, a))) (Icc 0 T) t)
    (hM : ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) (Icc 0 T) t)
    (hMt : ∀ a, ContinuousOn (fun t => Mt (t, a)) (Icc 0 T))
    (hGF : ∀ q ∈ Slab(T), (G q).comp (F q) = ContinuousLinearMap.id ℝ Vec3)
    (hGbound : ∀ q ∈ Slab(T), ‖G q‖ ≤ D)
    (hFbound : ∀ q ∈ Slab(T), ‖F q‖ ≤ S)
    (hMbound : ∀ q ∈ Slab(T), ‖M q‖ ≤ L)
    (hFlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖F (t, a) - F (t, b)‖ ≤ F₁ * dist a b)
    (hMlip : ∀ t ∈ Icc (0 : ℝ) T, ∀ a b, ‖M (t, a) - M (t, b)‖ ≤ M₁ * dist a b)
    (hupper : ∀ q ∈ Slab(T), ∀ x : Vec3, ⟪endpointHessian (M q) (Mt q) x, x⟫_ℝ ≤ ‖x‖ ^ 2) :
    ∃ Kmix Ωmix : MixedCoefficient(T),
      (∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
        fun t => kineticForm (F (t, a)) (v t)) ∧
      (∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TimeMeasure(T)]
        fun t => vorticityForm (F (t, a)) (M (t, a)) (v t)) ∧
      let B := endpointMixedPathCoefficient hT.le Kmix Ωmix
      ‖B.val.1‖ ≤ S ^ 2 + T * (2 * S ^ 2 * L) ∧
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤
        (2 * S * F₁ + T * (4 * S * F₁ * L + 2 * S ^ 2 * M₁)) * dist a b) ∧
      (∀ (a : A) (v : Path(T)), endpointIntegral T v = 0 →
        (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ) := by
  let K (q : ℝ × A) := kineticForm (F q)
  let Ω (q : ℝ × A) := vorticityForm (F q) (M q)
  let CK := S ^ 2
  let CΩ := 2 * S ^ 2 * L
  let LK := 2 * S * F₁
  let LΩ := 4 * S * F₁ * L + 2 * S ^ 2 * M₁
  have hCK : 0 ≤ CK := sq_nonneg S
  have hCΩ : 0 ≤ CΩ := by dsimp [CΩ]; positivity
  have hLK : 0 ≤ LK := by dsimp [LK]; positivity
  have hLΩ : 0 ≤ LΩ := by dsimp [LΩ]; positivity
  have hKt : ∀ a, AEStronglyMeasurable (fun t => K (t, a)) (TimeMeasure(T)) := by
    apply endpointMixedCoefficient_slice_aeStronglyMeasurable
    intro a
    have hc := endpointSlab_slice_continuous cF a
    exact (ContinuousLinearMap.adjoint.continuous.comp_continuousOn hc).clm_comp hc
  have hΩt : ∀ a, AEStronglyMeasurable (fun t => Ω (t, a)) (TimeMeasure(T)) :=
    endpointMixedCoefficient_slice_aeStronglyMeasurable fun a =>
      continuousOn_endpointSkew (endpointSlab_slice_continuous cF a) (endpointSlab_slice_continuous cM a)
  have bK (t : ℝ) (ht : t ∈ Icc 0 T) (a : A) : ‖K (t, a)‖ ≤ CK :=
    norm_kineticForm_le (hFbound _ ⟨ht, mem_univ a⟩)
  have bΩ (t : ℝ) (ht : t ∈ Icc 0 T) (a : A) : ‖Ω (t, a)‖ ≤ CΩ :=
    norm_vorticityForm_le (hFbound _ ⟨ht, mem_univ a⟩) (hMbound _ ⟨ht, mem_univ a⟩)
  have dK (t : ℝ) (ht : t ∈ Icc 0 T) (a b : A) : ‖K (t, a) - K (t, b)‖ ≤ LK * dist a b :=
    norm_kineticForm_sub_le (hFbound _ ⟨ht, mem_univ a⟩) (hFbound _ ⟨ht, mem_univ b⟩) (hFlip t ht a b)
  have dΩ (t : ℝ) (ht : t ∈ Icc 0 T) (a b : A) : ‖Ω (t, a) - Ω (t, b)‖ ≤ LΩ * dist a b :=
    norm_vorticityForm_sub_le (hFbound _ ⟨ht, mem_univ a⟩) (hFbound _ ⟨ht, mem_univ b⟩)
      (hMbound _ ⟨ht, mem_univ a⟩) (hMbound _ ⟨ht, mem_univ b⟩) (hFlip t ht a b) (hMlip t ht a b)
  let K₀ := max CK LK
  let Ω₀ := max CΩ LΩ
  have hK₀ : 0 ≤ K₀ := hCK.trans (le_max_left _ _)
  have hΩ₀ : 0 ≤ Ω₀ := hCΩ.trans (le_max_left _ _)
  have bK₀ (t : ℝ) (ht : t ∈ Icc 0 T) (a : A) : ‖K (t, a)‖ ≤ K₀ :=
    (bK t ht a).trans (le_max_left _ _)
  have bΩ₀ (t : ℝ) (ht : t ∈ Icc 0 T) (a : A) : ‖Ω (t, a)‖ ≤ Ω₀ :=
    (bΩ t ht a).trans (le_max_left _ _)
  have dK₀ (t : ℝ) (ht : t ∈ Icc 0 T) (a b : A) :
      ‖K (t, a) - K (t, b)‖ ≤ K₀ * Real.sqrt (dist a b) :=
    (endpointCoefficient_sqrt_bound K hLK dK t ht a b).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  have dΩ₀ (t : ℝ) (ht : t ∈ Icc 0 T) (a b : A) :
      ‖Ω (t, a) - Ω (t, b)‖ ≤ Ω₀ * Real.sqrt (dist a b) :=
    (endpointCoefficient_sqrt_bound Ω hLΩ dΩ t ht a b).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
  let Kmix := endpointMixedCoefficient K hKt bK₀ dK₀ hK₀
  let Ωmix := endpointMixedCoefficient Ω hΩt bΩ₀ dΩ₀ hΩ₀
  have hKrep (a : A) (v : Path(T)) : (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
      fun t => kineticForm (F (t, a)) (v t) :=
    endpointMixedCoefficient_apply_ae K hKt bK₀ dK₀ hK₀ a v
  have hΩrep (a : A) (v : Path(T)) : (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TimeMeasure(T)]
      fun t => vorticityForm (F (t, a)) (M (t, a)) (v t) :=
    endpointMixedCoefficient_apply_ae Ω hΩt bΩ₀ dΩ₀ hΩ₀ a v
  refine ⟨Kmix, Ωmix, hKrep, hΩrep, ?_, ?_, ?_⟩
  · exact norm_endpointMixedPathCoefficient_sup_le hT.le Kmix Ωmix hCK hCΩ
      (endpointMixedCoefficient_eval_norm_le K hKt bK₀ dK₀ hK₀ hCK bK)
      (endpointMixedCoefficient_eval_norm_le Ω hΩt bΩ₀ dΩ₀ hΩ₀ hCΩ bΩ)
  · exact norm_endpointMixedPathCoefficient_sub_le hT.le Kmix Ωmix
      (norm_endpointMixedCoefficient_sub_le_of_lipschitz K hKt bK₀ dK₀ hK₀ hLK dK)
      (norm_endpointMixedCoefficient_sub_le_of_lipschitz Ω hΩt bΩ₀ dΩ₀ hΩ₀ hLΩ dΩ)
  · intro a v hv
    exact endpointMixedPathCoefficient_coercive hT hT₁ hD hL Kmix Ωmix a
      (fun t => F (t, a)) (fun t => G (t, a)) (fun t => M (t, a)) (fun t => Mt (t, a))
      (endpointSlab_slice_continuous cF a) (endpointSlab_slice_continuous cM a)
      (hF a) (hM a) (hMt a)
      (fun t ht => hGF (t, a) ⟨ht, mem_univ a⟩) (fun t ht => hGbound (t, a) ⟨ht, mem_univ a⟩)
      (fun t ht => hMbound (t, a) ⟨ht, mem_univ a⟩) (fun t ht => hupper (t, a) ⟨ht, mem_univ a⟩)
      v hv (hKrep a v) (hΩrep a v)

end

end TorusEuler

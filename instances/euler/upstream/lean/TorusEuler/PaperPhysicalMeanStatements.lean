import TorusEuler.PaperMeanStatements
import TorusEuler.LocalizedSeedRegularity

/-! The frozen physical endpoint inverse and the finite-order mean estimate. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "P" => endpointStrongSpatialProjection
local notation "J(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => Set.prod (J(T)) (univ : Set Vec3)
local notation "Coframe" => (Vec3 →L[ℝ] Vec3)
local notation "TimeMeasure(" T ")" => volume.restrict (Ioc (0 : ℝ) T)
local notation "Path(" T ")" => Lp Vec3 2 (TimeMeasure(T))
local notation "MixedCoefficient(" T ")" => HalfHolder A (Path(T) →L[ℝ] Path(T))

local instance paperPhysicalMeanSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance paperPhysicalMeanSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- The physical coefficient assumptions of §4, in label coordinates.
The coframe identities and the Hessian upper bound are evaluated at fixed
label. The kinetic and vorticity bounds below use the undifferentiated
supremum and the first spatial derivative of their periodic lifts. -/
structure PaperMeanParent (T D L : ℝ) where
  F : ℝ × A → Coframe
  G : ℝ × A → Coframe
  M : ℝ × A → Coframe
  Mt : ℝ × A → Coframe
  deformation_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) LiftSlab(T)
  gradient_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => M (z.1, toUnitTorus z.2)) LiftSlab(T)
  deformation_ode : ∀ a t, t ∈ J(T) →
    HasDerivWithinAt (fun r => F (r, a)) ((M (t, a)).comp (F (t, a))) J(T) t
  gradient_derivative : ∀ a t, t ∈ J(T) →
    HasDerivWithinAt (fun r => M (r, a)) (Mt (t, a)) J(T) t
  gradient_derivative_continuous : ∀ a, ContinuousOn (fun r => Mt (r, a)) J(T)
  left_inverse : ∀ a t, t ∈ J(T) → (G (t, a)).comp (F (t, a)) = ContinuousLinearMap.id ℝ Vec3
  right_inverse : ∀ a t, t ∈ J(T) → (F (t, a)).comp (G (t, a)) = ContinuousLinearMap.id ℝ Vec3
  inverse_bound : ∀ a t, t ∈ J(T) → ‖G (t, a)‖ ≤ D
  gradient_bound : ∀ a t, t ∈ J(T) → ‖M (t, a)‖ ≤ L
  hessian_upper : ∀ a t, t ∈ J(T) → ∀ x : Vec3,
    ⟪endpointHessian (M (t, a)) (Mt (t, a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2

/-- The kinetic coefficient in physical label coordinates. -/
def PaperMeanParent.kinetic {T D L : ℝ} (p : PaperMeanParent T D L) (t : ℝ) (a : Vec3) :
    Coframe :=
  kineticForm (p.F (t, toUnitTorus a))

/-- The vorticity coefficient in physical label coordinates. -/
def PaperMeanParent.vorticity {T D L : ℝ} (p : PaperMeanParent T D L) (t : ℝ) (a : Vec3) :
    Coframe :=
  vorticityForm (p.F (t, toUnitTorus a)) (p.M (t, toUnitTorus a))

private theorem physicalMean_labels_periodic {E : Type*} (f : ℝ × A → E) (t : ℝ) :
    SpatiallyPeriodic (fun x => f (t, toUnitTorus x)) :=
  fun n x => congrArg (fun a => f (t, a)) ((toUnitTorus_eq_iff (x + latticeVector n) x).mpr ⟨n, rfl⟩)

/-- The time coefficients of the physical inverse are represented on the
spatial Hölder and mixed Hilbert path spaces by the exact label formulas. -/
structure PaperMeanPhysicalCoefficients {T D L : ℝ} (hT : 0 < T) (p : PaperMeanParent T D L) where
  K : ℝ → K½
  Ω : ℝ → K½
  Kmix : MixedCoefficient(T)
  Ωmix : MixedCoefficient(T)
  K_smooth : ContDiffOn ℝ ∞ K J(T)
  Ω_smooth : ContDiffOn ℝ ∞ Ω J(T)
  K_eval : ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (K t) = p.kinetic t x
  Ω_eval : ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (Ω t) = p.vorticity t x
  K_action : ∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Kmix v t) =ᵐ[TimeMeasure(T)]
    fun t => HalfHolder.eval a (K t) (v t)
  Ω_action : ∀ (a : A) (v : Path(T)), (fun t => HalfHolder.eval a Ωmix v t) =ᵐ[TimeMeasure(T)]
    fun t => HalfHolder.eval a (Ω t) (v t)
  K_coercive : ∀ t ∈ J(T), ∀ a z,
    (D ^ 2)⁻¹ * ‖z‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) z, z⟫_ℝ
  mixed_coercive : ∀ a (v : Path(T)), endpointIntegral T v = 0 →
    (1 / (2 * D ^ 2 * (1 + L) ^ 2)) * ‖v‖ ^ 2 ≤
      ⟪HalfHolder.eval a (endpointMixedPathCoefficient hT.le Kmix Ωmix) v, v⟫_ℝ

/-- Build both representations from the physical coefficient assumptions.
The coercivity uses the displacement and its two trace conditions. -/
theorem PaperMeanParent.exists_coefficients {T D L : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hD : 1 ≤ D) (hL : 0 ≤ L) (p : PaperMeanParent T D L) :
    Nonempty (PaperMeanPhysicalCoefficients hT p) := by
  obtain ⟨j⟩ := exists_endpointPhysicalJetData hT (fun i : Fin 3 => EuclideanSpace.single i 1)
    (fun z => p.F (z.1, toUnitTorus z.2)) (fun z => p.M (z.1, toUnitTorus z.2))
    (fun _ => (0 : Vec3)) p.deformation_smooth p.gradient_smooth contDiffOn_const
    (fun t _ => physicalMean_labels_periodic p.F t) (fun t _ => physicalMean_labels_periodic p.M t) (fun _ _ _ _ => rfl)
  have hK (t : ℝ) (ht : t ∈ J(T)) (a : A) :
      HalfHolder.eval a (j.kinetic.curve [] t) = kineticForm (p.F (t, a)) := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact j.kinetic.eval_lift [] t ht x
  have hΩ (t : ℝ) (ht : t ∈ J(T)) (a : A) :
      HalfHolder.eval a (j.vorticity.curve [] t) = vorticityForm (p.F (t, a)) (p.M (t, a)) := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact j.vorticity.eval_lift [] t ht x
  refine ⟨⟨j.kinetic.curve [], j.vorticity.curve [], j.kineticMixed [], j.vorticityMixed [],
    j.kinetic.smooth [], j.vorticity.smooth [], fun t ht x => hK t ht (toUnitTorus x),
    fun t ht x => hΩ t ht (toUnitTorus x), j.kinetic_action [], j.vorticity_action [], ?_, ?_⟩⟩
  · intro t ht a z
    rw [hK t ht a]
    exact kineticForm_elliptic (zero_lt_one.trans_le hD) (p.left_inverse a t ht) (p.inverse_bound a t ht) z
  · intro a v hv
    have cF : ContinuousOn (fun t => p.F (t, a)) J(T) :=
      fun t ht => (p.deformation_ode a t ht).continuousWithinAt
    have cM : ContinuousOn (fun t => p.M (t, a)) J(T) :=
      fun t ht => (p.gradient_derivative a t ht).continuousWithinAt
    have ha := ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := 0) (b := T))
    have hKA : (fun t => HalfHolder.eval a (j.kineticMixed []) v t) =ᵐ[TimeMeasure(T)]
        fun t => kineticForm (p.F (t, a)) (v t) :=
      (j.kinetic_action [] a v).trans (ha.mono fun t ht =>
        congrArg (fun K : Coframe => K (v t)) (hK t (Ioc_subset_Icc_self ht) a))
    have hΩA : (fun t => HalfHolder.eval a (j.vorticityMixed []) v t) =ᵐ[TimeMeasure(T)]
        fun t => vorticityForm (p.F (t, a)) (p.M (t, a)) (v t) :=
      (j.vorticity_action [] a v).trans (ha.mono fun t ht =>
        congrArg (fun Ω : Coframe => Ω (v t)) (hΩ t (Ioc_subset_Icc_self ht) a))
    exact endpointMixedPathCoefficient_coercive hT hT₁ hD hL (j.kineticMixed []) (j.vorticityMixed []) a
      (fun t => p.F (t, a)) (fun t => p.G (t, a)) (fun t => p.M (t, a)) (fun t => p.Mt (t, a))
      cF cM (p.deformation_ode a) (p.gradient_derivative a) (p.gradient_derivative_continuous a)
      (p.left_inverse a) (p.inverse_bound a) (p.gradient_bound a) (p.hessian_upper a) v hv hKA hΩA

set_option maxHeartbeats 4200000 in
/-- Theorem 4.2 for arbitrary continuous Hölder sources. The fixed-time
inverse and the displacement velocity have a common polynomial bound
in the physical controls of (4.10). The integrated pressure is the
normalized potential recovered from the same solution. -/
theorem paper_mean_inverse :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T D L K₀ K₁ Ω₀ Ω₁ : ℝ} (hT : 0 < T), T ≤ 1 → 1 ≤ D → 0 ≤ L →
      ∀ (p : PaperMeanParent T D L), 0 ≤ K₀ → 0 ≤ K₁ → 0 ≤ Ω₀ → 0 ≤ Ω₁ →
      (∀ t ∈ J(T), ∀ x, ‖p.kinetic t x‖ ≤ K₀) →
      (∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (p.kinetic t) x‖ ≤ K₁) →
      (∀ t ∈ J(T), ∀ x, ‖p.vorticity t x‖ ≤ Ω₀) →
      (∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (p.vorticity t) x‖ ≤ Ω₁) →
      let cap := C * (D + L + K₀ + K₁ + Ω₀ + Ω₁) ^ (4 * 291 : ℕ)
      ∃ k : PaperMeanPhysicalCoefficients hT p,
        (∃ e : ℝ → S ≃L[ℝ] S,
          (∀ t ∈ J(T), ∀ v : S, e t v = P ((k.K t).coefficientMul v.val)) ∧
          ∀ t ∈ J(T), ‖((e t).symm : S →L[ℝ] S).comp P‖ ≤ cap) ∧
        ∀ src : ℝ → C½, ContinuousOn src J(T) →
        ∃ (s : PaperMeanIntegratedSolution T k.K k.Ω src) (φ : Pressure) (Gφ : ℝ → C½),
          ContDiffOn ℝ 1 (endpointPrimitive s.velocity) J(T) ∧
          endpointPrimitive s.velocity 0 = 0 ∧
          (∀ t ∈ J(T), HasDerivWithinAt (endpointPrimitive s.velocity) (s.velocity t) J(T) t) ∧
          endpointClosedTimeNorm T s.velocity ≤ cap * endpointClosedTimeNorm T src ∧
          ContinuousOn Gφ J(T) ∧
          (∀ t ∈ J(T), SpatiallyPeriodic (φ t) ∧ (∫ x in centeredCell, φ t x) = 0 ∧
            (∀ x, HasGradientAt (φ t) (HalfHolder.eval (toUnitTorus x) (Gφ t)) x) ∧
            paperMeanIntegratedMomentum k.K k.Ω src s.velocity t = (s.constant : C½) + Gφ t) ∧
          ∀ u : PaperMeanIntegratedSolution T k.K k.Ω src,
            EqOn u.velocity s.velocity J(T) ∧ u.constant = s.constant := by
  obtain ⟨C, hC, estimate⟩ := paperMeanIntegratedInverse_of_coercivity
  refine ⟨C * (4096 : ℝ) ^ (291 : ℕ), by positivity, ?_⟩
  intro T D L K₀ K₁ Ω₀ Ω₁ hT hT₁ hD hL p hK₀ hK₁ hΩ₀ hΩ₁ hKv hKg hΩv hΩg cap
  obtain ⟨k⟩ := p.exists_coefficients hT hT₁ hD hL
  let Fℓ := fun t x => p.F (t, toUnitTorus x)
  let M := fun t x => p.M (t, toUnitTorus x)
  have hA (t : ℝ) (ht : t ∈ J(T)) : ContDiff ℝ ∞ (Fℓ t) :=
    contDiffOn_univ.mp (p.deformation_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hM (t : ℝ) (ht : t ∈ J(T)) : ContDiff ℝ ∞ (M t) :=
    contDiffOn_univ.mp (p.gradient_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hAdj : ContDiff ℝ ∞ (fun Q : Coframe => Q.adjoint) :=
    (ContinuousLinearMap.adjoint : Coframe ≃ₗᵢ[ℝ] Coframe).contDiff
  have hks (t : ℝ) (ht : t ∈ J(T)) : ContDiff ℝ ∞ (p.kinetic t) :=
    (hAdj.comp (hA t ht)).clm_comp (hA t ht)
  have hΩs (t : ℝ) (ht : t ∈ J(T)) : ContDiff ℝ ∞ (p.vorticity t) :=
    (hAdj.comp (hA t ht)).clm_comp
      (((hAdj.comp (hM t ht)).sub (hM t ht)).clm_comp (hA t ht))
  obtain ⟨hKn, hKl⟩ := endpointHalfHolderCaps_of_lift_gradient hK₀ hK₁ k.K p.kinetic k.K_eval
    (fun t ht => (hks t ht).differentiable (by simp)) hKv hKg
  obtain ⟨hΩn, hΩl⟩ := endpointHalfHolderCaps_of_lift_gradient hΩ₀ hΩ₁ k.Ω p.vorticity k.Ω_eval
    (fun t ht => (hΩs t ht).differentiable (by simp)) hΩv hΩg
  let μ : ℝ := (D ^ 2)⁻¹
  let μmix : ℝ := 1 / (2 * D ^ 2 * (1 + L) ^ 2)
  have hμ : 0 < μ := by dsimp [μ]; positivity
  have hμmix : 0 < μmix := by dsimp [μmix]; positivity
  let CK := K₀ + 2 * K₁
  let CΩ := Ω₀ + 2 * Ω₁
  let LK := 2 * K₁
  let LΩ := 2 * Ω₁
  have hCK : 0 ≤ CK := by dsimp [CK]; positivity
  have hCΩ : 0 ≤ CΩ := by dsimp [CΩ]; positivity
  have hLK : 0 ≤ LK := by dsimp [LK]; positivity
  have hLΩ : 0 ≤ LΩ := by dsimp [LΩ]; positivity
  obtain ⟨⟨e, he, hb⟩, solve⟩ := estimate hT hT₁ hμ hμmix hCK hCΩ hLK hLΩ k.K k.Ω k.Kmix k.Ωmix
    k.K_smooth.continuousOn k.Ω_smooth.continuousOn hKn hΩn hKl hΩl
    k.K_action k.Ω_action k.K_coercive k.mixed_coercive
  let Aold := D + L + K₀ + K₁ + Ω₀ + Ω₁
  have hBase : 1 ≤ paperMeanBaseScale D L CK CΩ LK LΩ := by
    dsimp [paperMeanBaseScale]; linarith
  have hCapScale : paperMeanBaseScale D L CK CΩ LK LΩ ≤ 4 * Aold := by
    dsimp [paperMeanBaseScale, CK, CΩ, LK, LΩ, Aold]
    linarith
  have hQ : 4 + μ⁻¹ + μmix⁻¹ + CK + CΩ + LK + LΩ ≤ 4096 * Aold ^ 4 := by
    have h := (paperMean_inverse_scale hD hL hCK hCΩ hLK hLΩ).2
    have h₂ : 16 * paperMeanBaseScale D L CK CΩ LK LΩ ^ 4 ≤ 4096 * Aold ^ 4 := by
      calc
        _ ≤ 16 * (4 * Aold) ^ 4 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (zero_le_one.trans hBase) hCapScale _) (by norm_num)
        _ = _ := by ring
    exact (by simpa only [μ, μmix, one_div, inv_inv] using h.trans h₂)
  have hCap : C * (4 + μ⁻¹ + μmix⁻¹ + CK + CΩ + LK + LΩ) ^ (291 : ℕ) ≤ cap := by
    refine (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hQ _) hC).trans_eq ?_
    change C * (4096 * Aold ^ 4) ^ (291 : ℕ) = (C * 4096 ^ (291 : ℕ)) * Aold ^ (4 * 291 : ℕ)
    rw [mul_pow, pow_mul, mul_assoc]
  refine ⟨k, ⟨e, he, fun t ht => (hb t ht).trans hCap⟩, ?_⟩
  intro src hsrc
  obtain ⟨s, hSmooth, hStart, hDeriv, hNorm, hUnique⟩ := solve src hsrc
  obtain ⟨φ, Gφ, hGc, hG⟩ := s.exists_potential k.K_smooth.continuousOn
    k.Ω_smooth.continuousOn hsrc
  exact ⟨s, φ, Gφ, hSmooth, hStart, hDeriv,
    hNorm.trans (mul_le_mul_of_nonneg_right hCap (endpointClosedTimeNorm_nonneg hT.le src)), hGc, hG, hUnique⟩


/-- A smooth solution of the mean equation in physical label coordinates,
including the two displacement conditions. -/
structure PaperSmoothMeanSolution {T D L : ℝ} (p : PaperMeanParent T D L) (force : Velocity) where
  velocity : Velocity
  displacement : Velocity
  mean : Velocity
  pressure : Pressure
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry velocity) LiftSlab(T)
  displacement_smooth : ContDiffOn ℝ ∞ (Function.uncurry displacement) LiftSlab(T)
  mean_smooth : ContDiffOn ℝ ∞ (Function.uncurry mean) LiftSlab(T)
  pressure_smooth : ContDiffOn ℝ ∞ (Function.uncurry pressure) LiftSlab(T)
  periodic : ∀ t ∈ J(T), SpatiallyPeriodic (velocity t) ∧ SpatiallyPeriodic (displacement t) ∧
    SpatiallyPeriodic (mean t) ∧ SpatiallyPeriodic (pressure t)
  initial : displacement 0 = 0
  terminal : displacement T = 0
  mean_eq : ∀ t ∈ J(T), ∀ x, mean t x = p.F (t, toUnitTorus x) (velocity t x)
  displacement_derivative : ∀ t ∈ J(T), ∀ x,
    HasDerivWithinAt (fun r => displacement r x) (velocity t x) J(T) t
  divergence_eq : ∀ t ∈ J(T), ∀ x, divergence (velocity t) x = 0
  momentum : ∀ t ∈ J(T), ∀ x,
    derivWithin (fun r => mean r x) J(T) t + p.M (t, toUnitTorus x) (mean t x) +
      (p.G (t, toUnitTorus x)).adjoint (gradient (pressure t) x) = force t x

private theorem paperMean_slice_spatial {T : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) {t : ℝ} (ht : t ∈ J(T)) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

private theorem paperMean_slice_time {T : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (x : Vec3) :
    ContDiffOn ℝ ∞ (fun t => f t x) J(T) :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ x⟩)

/-- The smooth forced part of Theorem 4.2. In the label form of the
linearized equation the divergence condition is `div(v) = 0` and the
physical pressure gradient is the inverse adjoint applied to the
label gradient. -/
theorem paper_mean_inverse_smooth_force {T D L : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hD : 1 ≤ D) (hL : 0 ≤ L) (p : PaperMeanParent T D L) (force : Velocity)
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hper : ∀ t ∈ J(T), SpatiallyPeriodic (force t)) :
    ∃ s : PaperSmoothMeanSolution p force, ∀ t ∈ J(T),
      (∫ x in centeredCell, s.pressure t x) = 0 := by
  obtain ⟨v, z, B, q, hv, hz, hB, hq, hP, h0, hTend, hmom, _⟩ :=
    exists_endpointPhysicalForcedMean_withRecovery hT hT₁ hD hL p.F p.G p.M p.Mt force
      p.deformation_smooth p.gradient_smooth hforce hper p.deformation_ode p.gradient_derivative
      p.gradient_derivative_continuous p.left_inverse p.right_inverse p.inverse_bound p.gradient_bound
      p.hessian_upper
  exact ⟨⟨v, z, B, q, hv, hz, hB, hq, (fun t ht => ⟨(hP t ht).1, (hP t ht).2.1,
    (hP t ht).2.2.1, (hP t ht).2.2.2.1⟩), h0, hTend,
    (fun t ht x => (hmom t ht x).1), (fun t ht x => (hmom t ht x).2.1),
    (fun t ht x => (hmom t ht x).2.2.1), (fun t ht x => (hmom t ht x).2.2.2)⟩,
    fun t ht => (hP t ht).2.2.2.2⟩

/-- The integrated source of a smooth force is an actual spatial Hölder
curve, with the prescribed physical force primitive on its lift. -/
theorem PaperMeanParent.exists_integratedForce {T D L : ℝ} (hT : 0 < T)
    (p : PaperMeanParent T D L) (force : Velocity)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hp : ∀ t ∈ J(T), SpatiallyPeriodic (force t)) :
    ∃ src : ℝ → C½, ContDiffOn ℝ ∞ src J(T) ∧
      ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (src t) = endpointPhysicalForcePrimitive p.F force (t, x) := by
  let g (t : ℝ) (x : Vec3) := (p.F (t, toUnitTorus x)).adjoint (force t x)
  have cAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (p.F (z.1, toUnitTorus z.2)).adjoint) LiftSlab(T) :=
    (ContinuousLinearMap.adjoint : Coframe ≃ₗᵢ[ℝ] Coframe).contDiff.comp_contDiffOn p.deformation_smooth
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) LiftSlab(T) := cAdj.clm_apply hf
  have hSrc : ContDiffOn ℝ ∞ (endpointPhysicalForcePrimitive p.F force) LiftSlab(T) :=
    (contDiffOn_endpointPhysicalJointPrimitive hT hg).neg
  have hPer (t : ℝ) (ht : t ∈ J(T)) :
      SpatiallyPeriodic (fun x => endpointPhysicalForcePrimitive p.F force (t, x)) := by
    intro n x
    dsimp only [endpointPhysicalForcePrimitive, endpointPrimitive]
    refine congrArg Neg.neg (intervalIntegral.integral_congr ?_)
    rw [uIcc_of_le ht.1]
    intro r hr
    dsimp only []
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩, hp r (Icc_subset_Icc_right ht.2 hr) n x]
  obtain ⟨j⟩ := exists_endpointSlabHalfHolderJets hT (fun i : Fin 3 => EuclideanSpace.single i 1)
    (endpointPhysicalForcePrimitive p.F force) hSrc hPer
  exact ⟨j.curve [], j.smooth [], fun t ht x => j.eval_lift [] t ht x⟩

private theorem PaperSmoothMeanSolution.kinetic_derivative {T D L : ℝ}
    {p : PaperMeanParent T D L} {force : Velocity}
    (s : PaperSmoothMeanSolution p force) {t : ℝ} (ht : t ∈ J(T)) (x : Vec3) :
    let g := (p.F (t, toUnitTorus x)).adjoint (force t x)
    HasDerivWithinAt (fun r => p.kinetic r x (s.velocity r x))
      (p.vorticity t x (s.velocity t x) + g - gradient (s.pressure t) x) J(T) t := by
  let a := toUnitTorus x
  let B := fun r => s.mean r x
  let F := fun r => p.F (r, a)
  let M := p.M (t, a)
  let G := p.G (t, a)
  let q := gradient (s.pressure t) x
  let dB := force t x - M (B t) - G.adjoint q
  have hB : HasDerivWithinAt B dB J(T) t := by
    have hdiff := (paperMean_slice_time s.mean_smooth x).differentiableOn (by simp) t ht
    have hValue : derivWithin B J(T) t = dB := by
      have hmom := s.momentum t ht x
      change derivWithin B J(T) t + M (B t) + G.adjoint q = force t x at hmom
      dsimp only [dB]
      rw [← hmom]
      abel
    exact hValue ▸ hdiff.hasDerivWithinAt
  let Adj : Coframe ≃ₗᵢ[ℝ] Coframe := ContinuousLinearMap.adjoint
  have hF : HasDerivWithinAt (fun r => (F r).adjoint) ((M.comp (F t)).adjoint) J(T) t :=
    Adj.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivWithinAt t
      (p.deformation_ode a t ht)
  have hProd := hF.clm_apply hB
  have hInv : (F t).adjoint (G.adjoint q) = q := by
    change ((F t).adjoint.comp G.adjoint) q = q
    rw [← ContinuousLinearMap.adjoint_comp, p.left_inverse a t ht, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_apply]
  have hValue : (M.comp (F t)).adjoint (B t) + (F t).adjoint dB =
      p.vorticity t x (s.velocity t x) + (F t).adjoint (force t x) - q := by
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_apply]
    dsimp only [dB]
    rw [map_sub, map_sub, hInv]
    change _ = (F t).adjoint ((M.adjoint - M) (F t (s.velocity t x))) + _ - _
    rw [← s.mean_eq t ht x, sub_apply, map_sub]
    abel
  rw [hValue] at hProd
  refine hProd.congr_of_mem ?_ ht
  intro r hr
  rw [show B r = F r (s.velocity r x) from s.mean_eq r hr x]
  rfl

set_option maxHeartbeats 4500000 in
/-- Every smooth mean solution solves the corresponding integrated endpoint
problem in the same Hölder space. In particular the unique inverse
selects its label velocity. -/
theorem PaperSmoothMeanSolution.exists_integratedSolution {T D L : ℝ}
    (hT : 0 < T) {p : PaperMeanParent T D L} {force : Velocity}
    (s : PaperSmoothMeanSolution p force) (k : PaperMeanPhysicalCoefficients hT p)
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (src : ℝ → C½) (hsrc : ContDiffOn ℝ ∞ src J(T))
    (hSource : ∀ t ∈ J(T), ∀ x,
      HalfHolder.eval (toUnitTorus x) (src t) = endpointPhysicalForcePrimitive p.F force (t, x)) :
    ∃ u : PaperMeanIntegratedSolution T k.K k.Ω src,
      ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (u.velocity t).val = s.velocity t x := by
  classical
  obtain ⟨j⟩ := exists_endpointSlabHalfHolderJets hT (fun i : Fin 3 => EuclideanSpace.single i 1)
    (Function.uncurry s.velocity) s.velocity_smooth (fun t ht => (s.periodic t ht).1)
  let V := j.curve []
  have hV := j.smooth []
  have hEval (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (V t) = s.velocity t x := j.eval_lift [] t ht x
  have hMem (t : ℝ) (ht : t ∈ J(T)) : V t ∈ S :=
    (mem_endpointHalfHolderSolenoidal (V t)).mpr
      ((endpointTorusGradientPairing_iff_divergence_free
        (paperMean_slice_spatial s.velocity_smooth ht) (hEval t ht)).mpr (s.divergence_eq t ht))
  let v (t : ℝ) : S := if ht : t ∈ J(T) then ⟨V t, hMem t ht⟩ else 0
  have hVeq (t : ℝ) (ht : t ∈ J(T)) : (v t).val = V t := by
    simp only [v, dite_eq_left ht]
  have hvc : ContinuousOn v J(T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    apply Continuous.subtype_mk
    exact (continuousOn_iff_continuous_domRestrict.mp hV.continuousOn).congr
      (fun t => (hVeq t t.property).symm)
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  have hEnd : endpointPrimitive v T = 0 := by
    apply Subtype.ext
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    let ev := (HalfHolder.eval (toUnitTorus x)).comp endpointHalfHolderSolenoidal.subtypeL
    have hi : IntervalIntegrable v volume 0 T := hvc.intervalIntegrable_of_Icc hT.le
    change ev (∫ r in (0 : ℝ)..T, v r) = 0
    rw [← ev.intervalIntegral_comp_comm hi]
    have hEv (r : ℝ) (hr : r ∈ J(T)) : ev (v r) = s.velocity r x := by
      change HalfHolder.eval (toUnitTorus x) (v r).val = _
      rw [hVeq r hr, hEval r hr]
    have hVelocity : IntervalIntegrable (fun r => s.velocity r x) volume 0 T :=
      (paperMean_slice_time s.velocity_smooth x).continuousOn.intervalIntegrable_of_Icc hT.le
    calc
      _ = ∫ r in (0 : ℝ)..T, s.velocity r x :=
        intervalIntegral.integral_congr (by rwa [uIcc_of_le hT.le])
      _ = s.displacement T x - s.displacement 0 x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
          (paperMean_slice_time s.displacement_smooth x).continuousOn
          (fun r hr => (s.displacement_derivative r (Ioo_subset_Icc_self hr) x).hasDerivAt
            (mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Icc_self)) hVelocity
      _ = 0 := by rw [s.initial, s.terminal]; simp
  let ΩV (t : ℝ) := (k.Ω t).coefficientMul (V t)
  let R (t : ℝ) : C½ := (k.K t).coefficientMul (V t) - endpointPrimitive ΩV t + src t
  have hΩV : ContDiffOn ℝ ∞ ΩV J(T) := (HalfHolder.contDiffOn_coefficientMul k.Ω_smooth).clm_apply hV
  have hKc := (HalfHolder.contDiffOn_coefficientMul k.K_smooth).clm_apply hV
  have hJ := contDiffOn_endpointPrimitive_succ (n := 0) hT (hΩV.of_le (by simp))
  have hRc : ContDiffOn ℝ 1 R J(T) := (hKc.of_le (by simp)).sub hJ |>.add (hsrc.of_le (by simp))
  have hRlift (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (R t) =
        p.kinetic t x (s.velocity t x) -
        endpointPrimitive (fun r => p.vorticity r x (s.velocity r x)) t +
        endpointPhysicalForcePrimitive p.F force (t, x) := by
    let ev : C½ →L[ℝ] Vec3 := HalfHolder.eval (toUnitTorus x)
    unfold R
    rw [map_add, map_sub, HalfHolder.eval_coefficientMul, k.K_eval t ht x, hEval t ht x,
      hSource t ht x]
    have hi := (hΩV.continuousOn.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc
      (μ := volume) ht.1
    change _ - ev (∫ r in (0 : ℝ)..t, ΩV r) + _ = _
    rw [← ev.intervalIntegral_comp_comm hi]
    have hIntegral : (∫ r in (0 : ℝ)..t, ev (ΩV r)) =
        ∫ r in (0 : ℝ)..t, p.vorticity r x (s.velocity r x) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro r hr
      have hr' := Icc_subset_Icc_right ht.2 hr
      change HalfHolder.eval (toUnitTorus x) ((k.Ω r).coefficientMul (V r)) = _
      rw [HalfHolder.eval_coefficientMul, k.Ω_eval r hr' x, hEval r hr' x]
    simpa only [endpointPrimitive] using congrArg
      (fun u => p.kinetic t x (s.velocity t x) - u + endpointPhysicalForcePrimitive p.F force (t, x)) hIntegral
  let Q (a : A) : C½ →L[ℝ] Vec3 :=
    (HalfHolder.eval a).comp (endpointHalfHolderSolenoidal.subtypeL.comp P)
  have hProjR (a : A) (t : ℝ) (ht : t ∈ J(T)) :
      HasDerivWithinAt (fun r => Q a (R r)) 0 J(T) t := by
    let d := derivWithin R J(T) t
    have hder : HasDerivWithinAt R d J(T) t :=
      (hRc.differentiableOn (by simp) t ht).hasDerivWithinAt
    have hq (x : Vec3) : HalfHolder.eval (toUnitTorus x) d = -gradient (s.pressure t) x := by
      let ev : C½ →L[ℝ] Vec3 := HalfHolder.eval (toUnitTorus x)
      let g (r : ℝ) := (p.F (r, toUnitTorus x)).adjoint (force r x)
      let Ωv (r : ℝ) := p.vorticity r x (s.velocity r x)
      have hΩv : ContinuousOn Ωv J(T) := by
        have hb := (ev.continuous.comp_continuousOn hΩV.continuousOn)
        refine hb.congr (fun r hr => ?_)
        change Ωv r = ev ((k.Ω r).coefficientMul (V r))
        rw [HalfHolder.eval_coefficientMul, k.Ω_eval r hr x, hEval r hr x]
      have hg : ContinuousOn g J(T) :=
        ((ContinuousLinearMap.adjoint : Coframe ≃ₗᵢ[ℝ] Coframe).continuous.comp_continuousOn
          (fun r hr => (p.deformation_ode (toUnitTorus x) r hr).continuousWithinAt)).clm_apply
          (paperMean_slice_time hforce x).continuousOn
      have hK := s.kinetic_derivative ht x
      dsimp only at hK
      have hrv := (hK.sub (hasDerivWithinAt_endpointPrimitive_of_continuousOn hΩv ht)).add
        (hasDerivWithinAt_endpointPrimitive_of_continuousOn hg ht).neg
      have hrv' : HasDerivWithinAt (fun r => ev (R r)) (-gradient (s.pressure t) x) J(T) t := by
        have hEqR (r : ℝ) (hr : r ∈ J(T)) : ev (R r) =
            p.kinetic r x (s.velocity r x) - endpointPrimitive Ωv r + -endpointPrimitive g r :=
          hRlift r hr x
        have hc := hrv.congr_of_mem hEqR ht
        have hval : (Ωv t + g t - gradient (s.pressure t) x) - Ωv t + -g t =
            -gradient (s.pressure t) x := by abel
        exact hval ▸ hc
      exact ((ev.hasFDerivAt.comp_hasDerivWithinAt t hder).derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
        (hrv'.derivWithin (uniqueDiffOn_Icc hT t ht))
    let q : EndpointSmoothPotential := ⟨-(s.pressure t),
      (paperMean_slice_spatial s.pressure_smooth ht).neg, fun n x => congrArg Neg.neg ((s.periodic t ht).2.2.2 n x)⟩
    have hGrad (x : Vec3) : gradient q.lift x = -gradient (s.pressure t) x := by
      change (InnerProductSpace.toDual ℝ Vec3).symm (fderiv ℝ (-(s.pressure t)) x) = _
      rw [fderiv_neg, map_neg]
      rfl
    have hp := paperMean_projection_gradient_zero d q (fun x => (hq x).trans (hGrad x).symm)
    have hZero : Q a d = 0 := by
      change HalfHolder.eval a (endpointHalfHolderSolenoidal.subtypeL (P d)) = 0
      rw [hp, map_zero, map_zero]
    have hD := (Q a).hasFDerivAt.comp_hasDerivWithinAt t hder
    rw [hZero] at hD
    exact hD
  have hConst (t : ℝ) (ht : t ∈ J(T)) : P (R t) = P (R 0) := by
    apply Subtype.ext
    apply HalfHolder.ext
    intro a
    change Q a (R t) = Q a (R 0)
    have hc : ContinuousOn (fun r => Q a (R r)) (Icc 0 t) :=
      (Q a).continuous.comp_continuousOn
        (hRc.continuousOn.mono (Icc_subset_Icc_right ht.2))
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 hc
      (fun r hr => (hProjR a r (Icc_subset_Icc_right ht.2 (Ioo_subset_Icc_self hr))).hasDerivAt
        (mem_of_superset (isOpen_Ioo.mem_nhds hr) (Ioo_subset_Icc_self.trans (Icc_subset_Icc_right ht.2))))
      (intervalIntegrable_const (c := (0 : Vec3)) (a := 0) (b := t))
    apply sub_eq_zero.mp
    rw [← h, intervalIntegral.integral_zero]
  have hEq (t : ℝ) (ht : t ∈ J(T)) :
      P (paperMeanIntegratedMomentum k.K k.Ω src v t) = P (R 0) := by
    unfold paperMeanIntegratedMomentum
    rw [hVeq t ht]
    have hI : endpointPrimitive (fun r => (k.Ω r).coefficientMul (v r).val) t = endpointPrimitive ΩV t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro r hr
      change (k.Ω r).coefficientMul (v r).val = (k.Ω r).coefficientMul (V r)
      rw [hVeq r (Icc_subset_Icc_right ht.2 hr)]
    rw [hI]
    exact hConst t ht
  exact ⟨⟨v, P (R 0), hvc, hEnd, hEq⟩, fun t ht x => by
    rw [hVeq t ht, hEval t ht]⟩


private theorem PaperMeanParent.exists_coefficient_caps {T D L : ℝ} (hT : 0 < T)
    (p : PaperMeanParent T D L) :
    ∃ K₀ K₁ Ω₀ Ω₁ : ℝ,
      0 ≤ K₀ ∧ 0 ≤ K₁ ∧ 0 ≤ Ω₀ ∧ 0 ≤ Ω₁ ∧
      (∀ t ∈ J(T), ∀ x, ‖p.kinetic t x‖ ≤ K₀) ∧
      (∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (p.kinetic t) x‖ ≤ K₁) ∧
      (∀ t ∈ J(T), ∀ x, ‖p.vorticity t x‖ ≤ Ω₀) ∧
      (∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (p.vorticity t) x‖ ≤ Ω₁) := by
  let Adj : Coframe ≃ₗᵢ[ℝ] Coframe := ContinuousLinearMap.adjoint
  let Fℓ := fun z : ℝ × Vec3 => p.F (z.1, toUnitTorus z.2)
  let Mℓ := fun z : ℝ × Vec3 => p.M (z.1, toUnitTorus z.2)
  have hFadj : ContDiffOn ℝ ∞ (fun z => (Fℓ z).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn p.deformation_smooth
  have hMadj : ContDiffOn ℝ ∞ (fun z => (Mℓ z).adjoint) LiftSlab(T) :=
    Adj.contDiff.comp_contDiffOn p.gradient_smooth
  have hk : ContDiffOn ℝ ∞ (Function.uncurry p.kinetic) LiftSlab(T) :=
    hFadj.clm_comp p.deformation_smooth
  have hΩ : ContDiffOn ℝ ∞ (Function.uncurry p.vorticity) LiftSlab(T) :=
    hFadj.clm_comp ((hMadj.sub p.gradient_smooth).clm_comp p.deformation_smooth)
  have hKper (t : ℝ) (_ht : t ∈ J(T)) : SpatiallyPeriodic (p.kinetic t) :=
    fun n x => congrArg kineticForm (physicalMean_labels_periodic p.F t n x)
  have hΩper (t : ℝ) (_ht : t ∈ J(T)) : SpatiallyPeriodic (p.vorticity t) :=
    fun n x => congrArg₂ vorticityForm (physicalMean_labels_periodic p.F t n x)
      (physicalMean_labels_periodic p.M t n x)
  obtain ⟨K₀, hK₀⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hk hKper 0
  obtain ⟨K₁, hK₁⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hk hKper 1
  obtain ⟨Ω₀, hΩ₀⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hΩ hΩper 0
  obtain ⟨Ω₁, hΩ₁⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT hΩ hΩper 1
  let h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  refine ⟨K₀, K₁, Ω₀, Ω₁, (norm_nonneg _).trans (hK₀ 0 h0 0), (norm_nonneg _).trans (hK₁ 0 h0 0),
    (norm_nonneg _).trans (hΩ₀ 0 h0 0), (norm_nonneg _).trans (hΩ₁ 0 h0 0), ?_, ?_, ?_, ?_⟩
  · simpa only [norm_iteratedFDeriv_zero] using hK₀
  · simpa only [norm_iteratedFDeriv_one] using hK₁
  · simpa only [norm_iteratedFDeriv_zero] using hΩ₀
  · simpa only [norm_iteratedFDeriv_one] using hΩ₁

/-- The endpoint conditions determine the entire mean velocity, hence also
its initial value, among all smooth solutions of the forced equation. -/
theorem PaperSmoothMeanSolution.mean_eq_of_endpoints {T D L : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hD : 1 ≤ D) (hL : 0 ≤ L) {p : PaperMeanParent T D L} {force : Velocity}
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (hper : ∀ t ∈ J(T), SpatiallyPeriodic (force t))
    (a b : PaperSmoothMeanSolution p force) : EqOn a.mean b.mean J(T) := by
  obtain ⟨_, _, inv⟩ := paper_mean_inverse
  obtain ⟨K₀, K₁, Ω₀, Ω₁, hK₀, hK₁, hΩ₀, hΩ₁, hk0, hk1, hΩ0, hΩ1⟩ := p.exists_coefficient_caps hT
  obtain ⟨k, _, solve⟩ := inv hT hT₁ hD hL p hK₀ hK₁ hΩ₀ hΩ₁ hk0 hk1 hΩ0 hΩ1
  obtain ⟨src, hsrc, hsEval⟩ := p.exists_integratedForce hT force hforce hper
  obtain ⟨s, _, _, _, _, _, _, _, _, hu⟩ := solve src hsrc.continuousOn
  obtain ⟨u, hEvalA⟩ := a.exists_integratedSolution hT k hforce src hsrc hsEval
  obtain ⟨v, hEvalB⟩ := b.exists_integratedSolution hT k hforce src hsrc hsEval
  intro t ht
  funext x
  rw [a.mean_eq t ht x, b.mean_eq t ht x, ← hEvalA t ht x, ← hEvalB t ht x,
    (hu u).1 ht, (hu v).1 ht]

set_option maxHeartbeats 2200000 in
/-- Proposition 5.2. Every smooth forced mean on the actual parent slab
satisfies the one-derivative estimate in the unweighted label norm. Once
the envelope exponent is fixed, the power of the old parent scale is
independent of the measured order. -/
theorem paper_mean_columns (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (b s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {T D L : ℝ} {U : Velocity} {X : ℝ → Velocity}
        (_hT : 0 < T), T ≤ 1 → 2 ≤ D → 0 ≤ L → L ≤ D →
      IsLabelFlowOn U X J(T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T) →
      (∀ t ∈ J(T), SpatiallyPeriodic (U t)) →
      (∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ J(T), ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (p : PaperMeanParent T D L),
      (∀ t ∈ J(T), ∀ a, p.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a) →
      (∀ t ∈ J(T), ∀ a, p.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a)) →
      ∀ (force : Velocity), ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T) →
      (∀ t ∈ J(T), SpatiallyPeriodic (force t)) →
      ∀ (sol : PaperSmoothMeanSolution p force) (s : ℕ), s₀ ≤ s → ∀ n : ℕ,
        let ℓ := (D ^ s)⁻¹
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n (fun t : J(T) => sol.mean t) ≤
          C n * D ^ (b + 2 + 2 * s) *
            hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1) (fun t : J(T) => force t) := by
  obtain ⟨b, s₀, C, hC, hEst⟩ := exists_endpointPhysicalForcedMean_withUniformEstimate R hR
  refine ⟨b, s₀, C, hC, ?_⟩
  intro T D L U X hT hT₁ hD hL hLD hX hU hUP hF₀ hG₀ hJets p hF hM force hf hper sol s hs n
  obtain ⟨v, z, B, q, hv, hz, hB, hq, hperAll, hStart, hEnd, hmom, hEstimate⟩ :=
    hEst hT hT₁ hD hL hLD hX hU hUP hF₀ hG₀ hJets p.F p.G p.M p.Mt force
      p.deformation_smooth p.gradient_smooth hF hM hf hper p.deformation_ode p.gradient_derivative
      p.gradient_derivative_continuous p.left_inverse p.right_inverse p.inverse_bound p.gradient_bound
      p.hessian_upper
  let w : PaperSmoothMeanSolution p force :=
    ⟨v, z, B, q, hv, hz, hB, hq, (fun t ht => ⟨(hperAll t ht).1, (hperAll t ht).2.1,
      (hperAll t ht).2.2.1, (hperAll t ht).2.2.2.1⟩), hStart, hEnd,
      (fun t ht x => (hmom t ht x).1), (fun t ht x => (hmom t ht x).2.1),
      (fun t ht x => (hmom t ht x).2.2.1), (fun t ht x => (hmom t ht x).2.2.2)⟩
  have heq := sol.mean_eq_of_endpoints hT hT₁ (one_le_two.trans hD) hL hf hper w
  have hSame : (fun t : J(T) => sol.mean t) = fun t : J(T) => B t :=
    funext fun t => heq t.property
  rw [hSame]
  exact hEstimate s hs n


/-- The strong label pressure equation (4.11). -/
theorem PaperSmoothMeanSolution.strong_label_equation {T D L : ℝ} (hT : 0 < T)
    {p : PaperMeanParent T D L} {force : Velocity} (s : PaperSmoothMeanSolution p force)
    {t : ℝ} (ht : t ∈ J(T)) (x : Vec3) :
    let a := toUnitTorus x
    let F := p.F (t, a)
    p.kinetic t x (derivWithin (fun r => s.velocity r x) J(T) t) + gradient (s.pressure t) x =
      F.adjoint (force t x) - (2 : ℝ) • F.adjoint (p.M (t, a) (F (s.velocity t x))) := by
  intro a F
  have hK := hasDerivWithinAt_kineticForm (p.deformation_ode a t ht)
  have hv := ((paperMean_slice_time s.velocity_smooth x).differentiableOn (by simp) t ht).hasDerivWithinAt
  have hKinetic := (s.kinetic_derivative ht x).derivWithin (uniqueDiffOn_Icc hT t ht)
  have h := (hK.clm_apply hv).derivWithin (uniqueDiffOn_Icc hT t ht)
  change derivWithin (fun r => p.kinetic r x (s.velocity r x)) J(T) t =
    p.vorticity t x (s.velocity t x) +
      (2 : ℝ) • F.adjoint (p.M (t, a) (F (s.velocity t x))) +
      p.kinetic t x (derivWithin (fun r => s.velocity r x) J(T) t) at h
  rw [hKinetic] at h
  calc
    _ = (p.vorticity t x (s.velocity t x) +
        (2 : ℝ) • F.adjoint (p.M (t, a) (F (s.velocity t x))) +
        p.kinetic t x (derivWithin (fun r => s.velocity r x) J(T) t)) -
        p.vorticity t x (s.velocity t x) -
        (2 : ℝ) • F.adjoint (p.M (t, a) (F (s.velocity t x))) + gradient (s.pressure t) x := by abel
    _ = _ := by rw [← h]; abel

set_option maxHeartbeats 4200000 in
/-- The Eulerian form (4.12) of the smooth solution. The material
derivative is the joint derivative evaluated in direction `(1, U)`. -/
theorem PaperSmoothMeanSolution.eulerian_equation {T D L : ℝ} (hT : 0 < T)
    {p : PaperMeanParent T D L} {force U : Velocity} {X : ℝ → Velocity}
    (s : PaperSmoothMeanSolution p force)
    (hX : IsLabelFlowOn U X J(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ J(T), SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ J(T), ∀ x, divergence (U t) x = 0)
    (hF : ∀ t ∈ J(T), ∀ a, p.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a)
    (hM : ∀ t ∈ J(T), ∀ a, p.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a)) :
    let b (t : ℝ) (x : Vec3) := s.mean t (X t 0 x)
    let q (t : ℝ) (x : Vec3) := s.pressure t (X t 0 x)
    ContDiffOn ℝ ∞ (Function.uncurry b) LiftSlab(T) ∧
    ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
    (∀ t ∈ J(T), SpatiallyPeriodic (b t) ∧ SpatiallyPeriodic (q t)) ∧
    ∀ t ∈ J(T), ∀ x, divergence (b t) x = 0 ∧
      fderivWithin ℝ (Function.uncurry b) LiftSlab(T) (t, x) (1, U t x) +
        fderiv ℝ (U t) x (b t x) + gradient (q t) x = force t (X t 0 x) := by
  intro b q
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) LiftSlab(T) := hU.of_le (by simp)
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  let Inv : ℝ × Vec3 → ℝ × Vec3 := fun z => (z.1, X z.1 0 z.2)
  have hInv : ContDiffOn ℝ ∞ Inv LiftSlab(T) :=
    contDiffOn_fst.prodMk (hX.contDiffOn_inverseLabelFlow hT hU hper)
  have hMap : MapsTo Inv LiftSlab(T) LiftSlab(T) := fun z hz => ⟨hz.1, mem_univ _⟩
  have hb : ContDiffOn ℝ ∞ (Function.uncurry b) LiftSlab(T) := s.mean_smooth.comp hInv hMap
  have hq : ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) := s.pressure_smooth.comp hInv hMap
  refine ⟨hb, hq, ?_, ?_⟩
  · intro t ht
    constructor
    · intro n x
      change s.mean t (X t 0 (x + latticeVector n)) = s.mean t (X t 0 x)
      rw [hX.add_latticeVector hLip hper ht h0 n x, (s.periodic t ht).2.2.1 n]
    · intro n x
      change s.pressure t (X t 0 (x + latticeVector n)) = s.pressure t (X t 0 x)
      rw [hX.add_latticeVector hLip hper ht h0 n x, (s.periodic t ht).2.2.2 n]
  · intro t ht x
    let a := X t 0 x
    have hx : X 0 t a = x := (hX.inverse hLip h0 ht).2 x
    have hGtrue : (fderiv ℝ (X t 0) x).comp (fderiv ℝ (X 0 t) a) =
        ContinuousLinearMap.id ℝ Vec3 := by
      rw [← hx]
      exact (hX.labelDerivative_inverse hT hU₂ hper h0 ht a).1
    have hG : p.G (t, toUnitTorus a) = fderiv ℝ (X t 0) x := by
      let F := fderiv ℝ (X 0 t) a
      let G := fderiv ℝ (X t 0) x
      let Gp := p.G (t, toUnitTorus a)
      have hFGp : F.comp Gp = ContinuousLinearMap.id ℝ Vec3 := by
        change (fderiv ℝ (X 0 t) a).comp Gp = _
        rw [← hF t ht a]
        exact p.right_inverse (toUnitTorus a) t ht
      have hGF : G.comp F = ContinuousLinearMap.id ℝ Vec3 := hGtrue
      calc
        Gp = (G.comp F).comp Gp := by rw [hGF, ContinuousLinearMap.id_comp]
        _ = G.comp (F.comp Gp) := rfl
        _ = G := by rw [hFGp, ContinuousLinearMap.comp_id]
    have hDinv := (hX.differentiableAt_transition hT hU₂ hper ht h0 x).hasFDerivAt
    constructor
    · have hDB := ((paperMean_slice_spatial s.mean_smooth ht).differentiable (by simp) a).hasFDerivAt
      have hDb := (hDB.comp x hDinv).fderiv
      have hFlow := hX.contDiffOn_forwardLabelFlow hT hU hper
      have hDet : ∀ᶠ z in 𝓝 a, LinearMap.det (p.F (t, toUnitTorus z)).toLinearMap = 1 :=
        Eventually.of_forall (fun z => by rw [hF t ht z]; exact hX.det_labelDerivative hT hU₂ hper hdiv h0 ht z)
      have hPiola := trace_endpointPhysicalMean_eq_zero_of_volumePreserving
        (X := X 0 t) (((paperMean_slice_spatial hFlow ht).of_le (by simp : (2 : ℕ∞ω) ≤ ∞)).contDiffAt)
        (hF t ht) (p.left_inverse (toUnitTorus a) t ht) hDet
        ((paperMean_slice_spatial s.velocity_smooth ht).differentiable (by simp) a)
        (s.divergence_eq t ht a) (s.mean_eq t ht)
      change divergence (s.mean t ∘ X t 0) x = 0
      rw [divergence_eq_trace_fderiv, hDb, ← hG]
      exact hPiola
    · have hChain (r : ℝ) (hr : r ∈ J(T)) : b r (X 0 r a) = s.mean r a :=
        congrArg (s.mean r) ((hX.inverse hLip h0 hr).1 a)
      have htCurve : HasDerivWithinAt (fun r => (r, X 0 r a)) (1, U t x) J(T) t := by
        have H := (hasDerivAt_id t).hasDerivWithinAt.prodMk (hX.trajectory 0 h0 a t ht)
        rwa [hx] at H
      have hxb : (t, x) ∈ LiftSlab(T) := ⟨ht, mem_univ x⟩
      have hbD := (hb.differentiableOn (by simp) (t, x) hxb).hasFDerivWithinAt
      have hxy : (t, x) = (fun r => (r, X 0 r a)) t := congrArg (fun y => (t,y)) hx.symm
      have hMap' : MapsTo (fun r => (r, X 0 r a)) J(T) LiftSlab(T) :=
        fun r hr => ⟨hr, mem_univ (X 0 r a)⟩
      have hd := hbD.comp_hasDerivWithinAt_of_eq t htCurve hMap' hxy
      have hMaterial := ((hd.congr_of_mem (fun r hr => (hChain r hr).symm) ht).derivWithin
        (uniqueDiffOn_Icc hT t ht)).symm
      have hgrad := hasGradientAt_endpointPressurePullback hDinv
        ((paperMean_slice_spatial s.pressure_smooth ht).differentiable (by simp) a).hasGradientAt
      have hGrad : gradient (q t) x = (p.G (t, toUnitTorus a)).adjoint (gradient (s.pressure t) a) := by
        rw [hG]
        exact hgrad.gradient
      have hM' : p.M (t, toUnitTorus a) = fderiv ℝ (U t) x :=
        (hM t ht a).trans (congrArg (fderiv ℝ (U t)) hx)
      rw [hMaterial, hGrad, ← hM']
      simpa only [b, a] using s.momentum t ht a

end

end TorusEuler

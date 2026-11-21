import TorusEuler.EndpointPhysicalMeanEstimate
import TorusEuler.EndpointPhysicalMeanParity
import TorusEuler.HierarchyTwistedCompletion
import TorusEuler.HierarchyTwistedSolves

/-! The ordered expansion with the physical mean, transverse and curl solves. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k₀ : Vec3}

local notation "VP" => HierarchyTwistedProfile T k₀ Vec3
local notation "MP" => HierarchyTwistedProfile T k₀ (Vec3 →L[ℝ] Vec3)
local notation "LC" => ℝ × UnitAddTorus (Fin 3) → (Vec3 →L[ℝ] Vec3)
local notation "J" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- The label deformation and parent strain in the endpoint equation. -/
structure MeanCoefficients (G M : MP) where
  deformation : LC
  inverse : LC
  strain : LC
  strain_time : LC
  deformation_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Vec3 => deformation (z.1, toUnitTorus z.2)) J
  strain_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => strain (z.1, toUnitTorus z.2)) J
  inverse_value : ∀ x ∈ hierarchyProfileSlab T, G.val.val.val x = inverse (x.1, toUnitTorus x.2.1)
  strain_value : ∀ x ∈ hierarchyProfileSlab T, M.val.val.val x = strain (x.1, toUnitTorus x.2.1)
  deformation_equation : ∀ a t, t ∈ Icc 0 T →
    HasDerivWithinAt (fun r => deformation (r,a)) ((strain (t,a)).comp (deformation (t,a)))
      (Icc 0 T) t
  strain_equation : ∀ a t, t ∈ Icc 0 T →
    HasDerivWithinAt (fun r => strain (r,a)) (strain_time (t,a)) (Icc 0 T) t
  strain_time_continuous : ∀ a, ContinuousOn (fun r => strain_time (r,a)) (Icc 0 T)
  inverse_left : ∀ a t, t ∈ Icc 0 T → (inverse (t,a)).comp (deformation (t,a)) =
    ContinuousLinearMap.id ℝ Vec3
  inverse_right : ∀ a t, t ∈ Icc 0 T → (deformation (t,a)).comp (inverse (t,a)) =
    ContinuousLinearMap.id ℝ Vec3
  inverse_bound : ℝ
  strain_bound : ℝ
  inverse_bound_ge_one : 1 ≤ inverse_bound
  strain_bound_nonneg : 0 ≤ strain_bound
  norm_inverse_le : ∀ a t, t ∈ Icc 0 T → ‖inverse (t,a)‖ ≤ inverse_bound
  norm_strain_le : ∀ a t, t ∈ Icc 0 T → ‖strain (t,a)‖ ≤ strain_bound
  coercivity : ∀ a t, t ∈ Icc 0 T → ∀ x : Vec3,
    ⟪endpointHessian (strain (t,a)) (strain_time (t,a)) x, x⟫_ℝ ≤ ‖x‖ ^ 2

/-- The deformation, inverse coframe and strain of an odd parent are
all even functions of the starting label. -/
def MeanCoefficients.Even {G M : MP} (d : MeanCoefficients G M) : Prop :=
  (∀ t ∈ Icc 0 T, Function.Even (fun a => d.deformation (t, toUnitTorus a))) ∧
  (∀ t ∈ Icc 0 T, Function.Even (fun a => d.inverse (t, toUnitTorus a))) ∧
  (∀ t ∈ Icc 0 T, Function.Even (fun a => d.strain (t, toUnitTorus a)))

theorem MeanCoefficients.inverse_independent {G M : MP} (d : MeanCoefficients G M) :
    HierarchyPeriodicProfile.PhaseIndependent G.val.val := by
  intro x hx s
  exact (d.inverse_value (x.1,x.2.1,s) ⟨hx.1, mem_univ _⟩).trans (d.inverse_value x hx).symm

theorem TransverseCoefficients.covector_ne_zero {M : MP} {κ : VP} (d : TransverseCoefficients M κ)
    (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) : κ.val.val.val (t,a,0) ≠ 0 := by
  have hc : ContinuousOn (fun r => d.strain r a) (Icc 0 T) :=
    d.strain_smooth.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun _ hr => ⟨hr, mem_univ a⟩)
  have hAdj : ContinuousOn (fun r => -(d.strain r a).adjoint) (Icc 0 T) :=
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ)).continuous.comp_continuousOn hc).neg
  rw [d.covector_value (t,a,0) ⟨ht, mem_univ _⟩]
  exact linearODE_ne_zero_of_mem ordConnected_Icc ⟨le_rfl, ht.1.trans ht.2⟩ hAdj
    (fun r hr => by simpa only [neg_apply] using d.covector_equation a r hr)
    (d.initial_nonzero a) t ht

/-- The physical mean solve includes the solenoidal label velocity and its
primitive with two fixed endpoints. Its Eulerian pullback is the mean profile. -/
structure MeanResult (hT : 0 < T) (G M : MP) (κ S : VP) (d : MeanCoefficients G M) where
  output : HierarchyMeanOutput (twistedHierarchyOperators hT G M κ)
  momentum : (twistedHierarchyOperators hT G M κ).material output.B +
    (twistedHierarchyOperators hT G M κ).labelGrad output.q = S
  velocity : Velocity
  displacement : Velocity
  velocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry velocity) J
  displacement_smooth : ContDiffOn ℝ ∞ (Function.uncurry displacement) J
  velocity_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (velocity t)
  displacement_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (displacement t)
  displacement_initial : displacement 0 = 0
  displacement_final : displacement T = 0
  displacement_equation : ∀ t ∈ Icc 0 T, ∀ a,
    HasDerivWithinAt (fun r => displacement r a) (velocity t a) (Icc 0 T) t
  velocity_divergence : ∀ t ∈ Icc 0 T, ∀ a, divergence (velocity t) a = 0
  mean_velocity : ∀ t ∈ Icc 0 T, ∀ a s,
    output.B.val.val.val (t,a,s) = d.deformation (t, toUnitTorus a) (velocity t a)
  pressure_normalized : ∀ t ∈ Icc 0 T, (∫ a in centeredCell, output.q.val.val.val (t,a,0)) = 0
  reflection : d.Even → (∀ t ∈ Icc 0 T, Function.Odd (fun a => S.val.val.val (t,a,0))) →
    ∀ t ∈ Icc 0 T, ∀ a s, output.B.val.val.val (t,-a,-s) = -output.B.val.val.val (t,a,s) ∧
      output.q.val.val.val (t,-a,-s) = output.q.val.val.val (t,a,s)
  rawVelocity : Velocity
  rawMean : Velocity
  rawVelocity_smooth : ContDiffOn ℝ ∞ (Function.uncurry rawVelocity) J
  rawMean_smooth : ContDiffOn ℝ ∞ (Function.uncurry rawMean) J
  rawMean_periodic : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (rawMean t)
  rawMean_value : ∀ t ∈ Icc 0 T, ∀ a,
    rawMean t a = d.deformation (t, toUnitTorus a) (rawVelocity t a)
  meanSelection :
    (∀ t ∈ Icc 0 T, ∀ a, output.B.val.val.val (t,a,0) = rawMean t a) ∨
    (∀ t ∈ Icc 0 T, ∀ a, output.B.val.val.val (t,a,0) = endpointTimeParityPart (-1) rawMean t a)
  recovery : EndpointPhysicalMeanRecovery hT d.inverse_bound d.strain_bound d.deformation d.strain
    (fun t a => S.val.val.val (t,a,0)) rawVelocity
  labelNorm_le_raw : ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ n : ℕ,
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
      (fun (t : Icc (0 : ℝ) T) a => output.B.val.val.val (t,a,0)) ≤
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
      (fun (t : Icc (0 : ℝ) T) => rawMean t)

set_option maxHeartbeats 3000000 in
/-- Solve the mean equation for the actual phase average on the label torus. -/
theorem exists_meanResult (hT : 0 < T) (hT₁ : T ≤ 1) (G M : MP) (κ : VP)
    (d : MeanCoefficients G M) (S : VP)
    (hS : (twistedHierarchyOperators hT G M κ).average S = S) :
    Nonempty (MeanResult hT G M κ S d) := by
  let force (t : ℝ) (a : Vec3) := S.val.val.val (t,a,0)
  obtain ⟨hforce, hforcePer, hSval⟩ := meanSource_properties hT G M κ S hS
  obtain ⟨v, Z, B, q, hv, hZ, hB, hq, hper, hZ0, hZT, hEq, ⟨rec⟩⟩ :=
    exists_endpointPhysicalForcedMean_withRecovery hT hT₁ d.inverse_bound_ge_one d.strain_bound_nonneg
      d.deformation d.inverse d.strain d.strain_time force d.deformation_smooth d.strain_smooth
      hforce hforcePer d.deformation_equation d.strain_equation d.strain_time_continuous
      d.inverse_left d.inverse_right d.norm_inverse_le d.norm_strain_le d.coercivity
  have package (v' Z' B' : Velocity) (q' : Pressure)
      (hv' : ContDiffOn ℝ ∞ (Function.uncurry v') J) (hZ' : ContDiffOn ℝ ∞ (Function.uncurry Z') J)
      (hB' : ContDiffOn ℝ ∞ (Function.uncurry B') J) (hq' : ContDiffOn ℝ ∞ (Function.uncurry q') J)
      (hper' : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (v' t) ∧ SpatiallyPeriodic (Z' t) ∧
        SpatiallyPeriodic (B' t) ∧ SpatiallyPeriodic (q' t) ∧ (∫ x in centeredCell, q' t x) = 0)
      (hZ0' : Z' 0 = 0) (hZT' : Z' T = 0)
      (hEq' : ∀ t ∈ Icc 0 T, ∀ x,
        B' t x = d.deformation (t,toUnitTorus x) (v' t x) ∧
        HasDerivWithinAt (fun r => Z' r x) (v' t x) (Icc 0 T) t ∧
        divergence (v' t) x = 0 ∧
        derivWithin (fun r => B' r x) (Icc 0 T) t + d.strain (t,toUnitTorus x) (B' t x) +
          (d.inverse (t,toUnitTorus x)).adjoint (gradient (q' t) x) = force t x)
      (hpar : d.Even → (∀ t ∈ Icc 0 T, Function.Odd (force t)) → ∀ t ∈ Icc 0 T,
        Function.Odd (B' t) ∧ Function.Even (q' t))
      (selected : B' = B ∨ B' = endpointTimeParityPart (-1) B)
      (hNorm : ∀ ℓ : ℝ, 0 ≤ ℓ → ∀ n : ℕ,
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
          (fun (t : Icc (0 : ℝ) T) => B' t) ≤
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
          (fun (t : Icc (0 : ℝ) T) => B t)) : Nonempty (MeanResult hT G M κ S d) := by
    obtain ⟨out, hm, hval⟩ := exists_meanOutput_of_solution hT G M κ S B' q' hB' hq'
      (fun t ht => (hper' t ht).2.2.1) (fun t ht => (hper' t ht).2.2.2.1) (by
        intro t a s ht
        rw [d.strain_value (t,a,s) ⟨ht, mem_univ _⟩, d.inverse_value (t,a,s) ⟨ht, mem_univ _⟩,
          hSval t ht a s]
        exact (hEq' t ht a).2.2.2)
    refine ⟨⟨out, hm, v', Z', hv', hZ', fun t ht => (hper' t ht).1, fun t ht => (hper' t ht).2.1,
      hZ0', hZT', fun t ht a => (hEq' t ht a).2.1, fun t ht a => (hEq' t ht a).2.2.1,
      fun t ht a s => (hval t ht a s).1.trans (hEq' t ht a).1, ?_, ?_,
      v, B, hv, hB, (fun t ht => (hper t ht).2.2.1), (fun t ht a => (hEq t ht a).1), ?_, rec, ?_⟩⟩
    · intro t ht
      simpa only [(hval t ht _ 0).2] using (hper' t ht).2.2.2.2
    · intro he ho t ht a s
      obtain ⟨hBo, hqe⟩ := hpar he ho t ht
      simpa only [(hval t ht (-a) (-s)).1, (hval t ht (-a) (-s)).2, (hval t ht a s).1,
        (hval t ht a s).2] using And.intro (hBo a) (hqe a)
    · rcases selected with selected | selected
      · exact Or.inl (fun t ht a => (hval t ht a 0).1.trans (congrFun (congrFun selected t) a))
      · exact Or.inr (fun t ht a => (hval t ht a 0).1.trans (congrFun (congrFun selected t) a))
    · intro ℓ hℓ n
      have hSlice : (fun (t : Icc (0 : ℝ) T) a => out.B.val.val.val (t,a,0)) =
          (fun (t : Icc (0 : ℝ) T) => B' t) :=
        funext fun t => funext fun a => (hval t t.property a 0).1
      rw [hSlice]
      exact hNorm ℓ hℓ n
  classical
  by_cases h : d.Even ∧ (∀ t ∈ Icc 0 T, Function.Odd (force t))
  · obtain ⟨hv', hZ', hB', hq', hp', hZ0', hZT', hEq', hpar⟩ :=
      endpointPhysicalMean_reflectionSelection hT
        (fun t a => d.deformation (t,toUnitTorus a)) (fun t a => d.inverse (t,toUnitTorus a))
        (fun t a => d.strain (t,toUnitTorus a)) force v Z B q h.1.1 h.1.2.1 h.1.2.2 h.2
        hv hZ hB hq hper hZ0 hZT hEq
    refine package _ _ _ _ hv' hZ' hB' hq' hp' hZ0' hZT' hEq'
      (fun _ _ t _ => ⟨(hpar t).2.2.1, (hpar t).2.2.2⟩)
      (Or.inr rfl)
      ?_
    intro ℓ hℓ n
    exact hierarchyFiniteLabelNorm_endpointParityPart_le
      (f := fun (t : Icc (0 : ℝ) T) => B t)
      (fun t => contDiffOn_univ.mp (hB.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun x _ => ⟨t.property, mem_univ x⟩)))
      False ℓ n (sign := -1) (by norm_num)
      (fun w _ => (bddAbove_endpointLabelWord_of_smooth_periodic hT hℓ hB
        (fun t ht => (hper t ht).2.2.1) w).1)
  · exact package v Z B q hv hZ hB hq hper hZ0 hZT hEq (fun he ho => (h ⟨he,ho⟩).elim)
      (Or.inl rfl)
      (fun _ _ _ => le_rfl)

/-- The physical mean solve selected at a finite correction level. -/
def solveMean (hT : 0 < T) (hT₁ : T ≤ 1) (G M : MP) (κ : VP) (d : MeanCoefficients G M)
    (S : VP) (hS : (twistedHierarchyOperators hT G M κ).average S = S) :
    MeanResult hT G M κ S d := Classical.choice (exists_meanResult hT hT₁ G M κ d S hS)

set_option maxHeartbeats 2300000 in
/-- The physical mean selected by the hierarchy has the uniform label norm
estimate after the optional odd projection. -/
theorem exists_solveMean_labelNormBound (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ (p s₀ : ℕ) (C : ℕ → ℝ), (∀ n, 0 ≤ C n) ∧
      ∀ {T D : ℝ} {κ₀ : Vec3} {U : Velocity} {X : ℝ → Velocity}
        (hT : 0 < T) (hT₁ : T ≤ 1), 2 ≤ D →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
      (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
      ∀ (G M : HierarchyTwistedProfile T κ₀ (Vec3 →L[ℝ] Vec3))
        (κ : HierarchyTwistedProfile T κ₀ Vec3) (d : MeanCoefficients G M),
      d.inverse_bound ≤ D → d.strain_bound ≤ D →
      (∀ t ∈ Icc 0 T, ∀ a, d.deformation (t, toUnitTorus a) = fderiv ℝ (X 0 t) a) →
      (∀ t ∈ Icc 0 T, ∀ a, d.strain (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a)) →
      ∀ (S : HierarchyTwistedProfile T κ₀ Vec3)
        (hS : (twistedHierarchyOperators hT G M κ).average S = S),
      ∀ s : ℕ, s₀ ≤ s → ∀ n : ℕ,
        let ℓ := (D ^ s)⁻¹
        hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
          (fun (t : Icc (0 : ℝ) T) a => (solveMean hT hT₁ G M κ d S hS).output.B.val.val.val (t,a,0)) ≤
          C n * D ^ (p + 2 + 2 * s) *
            hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1)
              (fun (t : Icc (0 : ℝ) T) a => S.val.val.val (t,a,0)) := by
  obtain ⟨p, s₀, C, hC, hEstimate⟩ := exists_endpointPhysicalRecoveredMean_parentBound R hR
  refine ⟨p, s₀, C, hC, ?_⟩
  intro T D κ₀ U X hT hT₁ hD hX hU hUper hF₀ hG₀ hUjets G M κ d hD₀ hLD hF hM S hS s hs n
  let out := solveMean hT hT₁ G M κ d S hS
  let force (t : ℝ) (a : Vec3) := S.val.val.val (t,a,0)
  have hForce := meanSource_properties hT G M κ S hS
  have hD₀pos : 0 < d.inverse_bound := zero_lt_one.trans_le d.inverse_bound_ge_one
  have hℓ : 0 ≤ (D ^ s)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith only [hD]) s)
  exact (out.labelNorm_le_raw _ hℓ n).trans
    (hEstimate hT hT₁ hD d.strain_bound_nonneg hLD hX hU hUper hF₀ hG₀ hUjets
      d.deformation d.strain force out.rawVelocity out.rawMean d.deformation_smooth d.strain_smooth
      hF hM hForce.1 hForce.2.1 out.rawVelocity_smooth out.rawMean_value
      (out.recovery.weakenInverseBound hD₀pos hD₀ d.strain_bound_nonneg) s hs n)

/-- Concrete solvers for the finite expansion over one parent. -/
def physicalSolvers (hT : 0 < T) (hT₁ : T ≤ 1) (G M : MP) (κ : VP)
    (mean : MeanCoefficients G M) (osc : TransverseCoefficients M κ) :
    FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ) where
  average_idempotent := average_idempotent hT G M κ
  average_meanPhaseAdv := fun B hB Y => average_meanPhaseAdv hT G M κ B Y osc.covector_independent hB
  solveMean := fun S hS =>
    let meanResult := solveMean hT hT₁ G M κ mean S hS
    ⟨meanResult.output, meanResult.momentum⟩
  solveTransverse := fun S hS =>
    let oscResult := solveTransverse hT G M κ osc S hS
    ⟨oscResult.output, oscResult.momentum⟩
  complete := complete hT G κ osc.covector_independent osc.covector_ne_zero
  average_complete := fun V _ =>
    average_complete hT G M κ mean.inverse_independent osc.covector_independent osc.covector_ne_zero V

end

end TorusEuler.HierarchyTwistedProfile

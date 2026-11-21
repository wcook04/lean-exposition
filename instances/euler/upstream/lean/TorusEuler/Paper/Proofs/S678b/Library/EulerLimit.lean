import TorusEuler.PeriodicEulerLimit
import TorusEuler.PeriodicEulerUniqueness
import TorusEuler.Paper.S5.Statements

/-! # Proposition 8.1: the projected Euler limit with the product estimate (5.59) as a hypothesis

Copies (package S678b, Proposition 8.1's own content and its glue) of the library chain
`exists_inductive_periodicEulerSolution` → `exists_inductive_periodicEulerProjectedLimit` →
`periodicProjectedEuler_of_stage_limits` → the bounded bilinear momentum map on periodic jets
(`periodicProjectedMomentumJets`), from `TorusEuler/PeriodicEulerMomentumJets.lean` and
`TorusEuler/PeriodicEulerLimit.lean`. The only mathematical change: the library proves the
product estimate for `momentumTensor` with `spatialHolderHalf_bilinear` (the content of the
display (5.59)); here the estimate is taken from a hypothesis `h : Statement.Text.eq_5_59`, so
every declaration of the chain that uses the momentum map takes `h` as an argument, and the
bound of the momentum map is `periodicMomentumJetBound h59 m` with the constant `C_{m+1}` of
(5.59) in place of the library constant `3(m+2)2^{m+1}`. This is where the TeX proof of
Proposition 8.1 uses (5.59) (sections/09_limit.tex:39-44: "the product estimate (5.59) and
boundedness of `ℙ` on `C^{0,1/2}` give uniform convergence of the projected nonlinear term ...
The right-hand side is continuous in every spatial Hölder norm, so differentiating the equation
gives joint smoothness").

Declarations of the library that are public and do not reach (5.59) are used as they are
(`smoothPeriodicVelocity`, `smoothPeriodicVelocityJets`, `PeriodicVelocityJetSpace`,
`periodicVelocityJets`, `periodicProjectedMomentum`,
`continuousOn_periodicVelocityJets_of_joint_spatialJets`, ...); private helpers of the two
library files are copied unchanged. -/

open BoundedContinuousFunction ContinuousLinearMap Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S678b

noncomputable section

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def extendAlongLinearIsometry
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E →ₗᵢ[ℝ] H) (he : DenseRange e) :
    (E →L[ℝ] F) →L[ℝ] (H →L[ℝ] F) := by
  have he' : DenseRange e.toContinuousLinearMap := he
  have hU : IsUniformInducing e.toContinuousLinearMap := e.isometry.isUniformInducing
  exact LinearMap.mkContinuous
    { toFun := fun f => f.extend e.toContinuousLinearMap
      map_add' := fun f g => by
        apply ContinuousLinearMap.ext
        intro z
        refine he'.induction_on z ?_ ?_
        · exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
        · intro x
          simp only [_root_.add_apply,
            ContinuousLinearMap.extend_eq _ he' hU]
      map_smul' := fun c f => by
        apply ContinuousLinearMap.ext
        intro z
        refine he'.induction_on z ?_ ?_
        · exact isClosed_eq (ContinuousLinearMap.continuous _) (ContinuousLinearMap.continuous _)
        · intro x
          simp only [_root_.smul_apply, RingHom.id_apply,
            ContinuousLinearMap.extend_eq _ he' hU] } 1
    (fun f => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, NNReal.coe_one, one_mul] using
        f.opNorm_extend_le (N := 1) (e := e.toContinuousLinearMap) he
          (fun x => by simp))

/-- A bounded bilinear map has a bounded extension to the closure of its domain. -/
private def extendJetBilinear
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E →ₗᵢ[ℝ] H) (he : DenseRange e) (B : E →L[ℝ] E →L[ℝ] F) :
    H →L[ℝ] H →L[ℝ] F :=
  (extendAlongLinearIsometry e he).comp (B.extend e.toContinuousLinearMap)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem extendJetBilinear_apply
    {E H F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F] (e : E →ₗᵢ[ℝ] H) (he : DenseRange e) (B : E →L[ℝ] E →L[ℝ] F)
    (x y : E) : extendJetBilinear e he B (e x) (e y) = B x y := by
  unfold extendJetBilinear
  let i := e.toContinuousLinearMap
  have hi : DenseRange i := he
  have hU : IsUniformInducing i := e.isometry.isUniformInducing
  change ((B.extend i (i x)).extend i) (i y) = B x y
  calc
    _ = B.extend i (i x) y := ContinuousLinearMap.extend_eq _ hi hU y
    _ = B x y := congrArg (fun L : E →L[ℝ] F => L y)
      (ContinuousLinearMap.extend_eq B hi hU x)

/-- Time bootstrapping can take place in the completions of the spaces of compatible
periodic spatial jets, with a finite derivative loss in each projected momentum bound. -/
private theorem contDiffOn_jetTower_of_integrated
    {X : ℕ → Type*} [∀ m, NormedAddCommGroup (X m)] [∀ m, NormedSpace ℝ (X m)]
    [∀ m, CompleteSpace (X m)] {S : ℝ} (hS : 0 < S)
    (J : ∀ m, ℝ → X m) (r : ℕ → ℕ)
    (B : ∀ m, X (r m) →L[ℝ] X (r m) →L[ℝ] X m)
    (hcont : ∀ m, ContinuousOn (J m) (Icc 0 S))
    (hEq : ∀ m t, t ∈ Icc 0 S →
      J m t = J m 0 + endpointPrimitive (fun s => B m (J (r m) s) (J (r m) s)) t) :
    ∀ m, ContDiffOn ℝ ∞ (J m) (Icc 0 S) := by
  have h (n : ℕ) : ∀ m, ContDiffOn ℝ n (J m) (Icc 0 S) := by
    induction n with
    | zero => exact fun m => contDiffOn_zero.mpr (hcont m)
    | succ n hn =>
      intro m
      have hb := ((B m).contDiff.comp_contDiffOn (hn (r m))).clm_apply (hn (r m))
      rw [Nat.cast_succ]
      exact (contDiffOn_const.add (contDiffOn_endpointPrimitive_succ hS hb)).congr (hEq m)
  exact fun m => contDiffOn_infty.mpr fun n => h n m


/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem spatiallyPeriodic_iteratedFDeriv {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : Vec3 → F} (hper : SpatiallyPeriodic f) (m : ℕ) :
    SpatiallyPeriodic (iteratedFDeriv ℝ m f) := by
  intro n x
  rw [← iteratedFDeriv_comp_add_right]
  exact congrArg (fun g : Vec3 → F => iteratedFDeriv ℝ m g x) (funext (hper n))

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem exists_uniformBound_of_periodic {F : Type*} [NormedAddCommGroup F]
    {f : Vec3 → F} (hper : SpatiallyPeriodic f) (hf : Continuous f) :
    ∃ C : ℝ, ∀ x, ‖f x‖ ≤ C := by
  obtain ⟨g, hg, _⟩ := hper.existsUnique_torusFunction
  have hg' : Continuous g := isOpenQuotientMap_toUnitTorus.isQuotientMap.continuous_iff.mpr <| by
    simpa only [show g ∘ toUnitTorus = f from funext hg] using hf
  obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn hg'.continuousOn
  exact ⟨C, fun x => by rw [← hg x]; exact hC _ (mem_univ _)⟩

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem smoothPeriodicVelocity_smooth (v : smoothPeriodicVelocity) :
    ContDiff ℝ ∞ (v : Vec3 → Vec3) :=
  v.property.1

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem smoothPeriodicVelocity_periodic (v : smoothPeriodicVelocity) :
    SpatiallyPeriodic (v : Vec3 → Vec3) :=
  v.property.2

/-- Copy of the library's local instance (PeriodicEulerMomentumJets.lean:125): the sup norm on
bounded spatial jets of order `m`. -/
local instance (m : ℕ) : NormedAddCommGroup (BoundedSpatialJet Vec3 Vec3 m) :=
  inferInstanceAs (NormedAddCommGroup
    (Vec3 →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) Vec3))
/-- Copy of the library's local instance (PeriodicEulerMomentumJets.lean:128): the real normed
space structure on bounded spatial jets of order `m`. -/
local instance (m : ℕ) : NormedSpace ℝ (BoundedSpatialJet Vec3 Vec3 m) :=
  inferInstanceAs (NormedSpace ℝ
    (Vec3 →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) Vec3))
/-- Copy of the library's local instance (PeriodicEulerMomentumJets.lean:131): the product (sup)
norm on jet tuples of orders `0, …, m`. -/
local instance (m : ℕ) : NormedAddCommGroup (SpatialJetTuple Vec3 Vec3 m) :=
  inferInstanceAs (NormedAddCommGroup (∀ i : Fin (m + 1), BoundedSpatialJet Vec3 Vec3 i))
/-- Copy of the library's local instance (PeriodicEulerMomentumJets.lean:133): the real normed
space structure on jet tuples of orders `0, …, m`. -/
local instance (m : ℕ) : NormedSpace ℝ (SpatialJetTuple Vec3 Vec3 m) :=
  inferInstanceAs (NormedSpace ℝ (∀ i : Fin (m + 1), BoundedSpatialJet Vec3 Vec3 i))
/-- Copy of the library's local instance (PeriodicEulerMomentumJets.lean:135): jet tuples of
orders `0, …, m` form a complete space. -/
local instance (m : ℕ) : CompleteSpace (SpatialJetTuple Vec3 Vec3 m) :=
  inferInstanceAs (CompleteSpace (∀ i : Fin (m + 1),
    Vec3 →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin (i : ℕ) => Vec3) Vec3))

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def smoothPeriodicVelocityJet (m : ℕ) (v : smoothPeriodicVelocity) :
    BoundedSpatialJet Vec3 Vec3 m := by
  let f := iteratedFDeriv ℝ m (v : Vec3 → Vec3)
  have hcont : Continuous f := (smoothPeriodicVelocity_smooth v).continuous_iteratedFDeriv (by simp)
  let h := exists_uniformBound_of_periodic
    (spatiallyPeriodic_iteratedFDeriv (smoothPeriodicVelocity_periodic v) m) hcont
  exact BoundedContinuousFunction.mkOfBound ⟨f, hcont⟩ (h.choose + h.choose)
    (fun x y => dist_le_norm_add_norm _ _ |>.trans (add_le_add (h.choose_spec x) (h.choose_spec y)))

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
@[simp] private theorem smoothPeriodicVelocityJet_apply (m : ℕ) (v : smoothPeriodicVelocity)
    (x : Vec3) :
    smoothPeriodicVelocityJet m v x = iteratedFDeriv ℝ m (v : Vec3 → Vec3) x :=
  rfl

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem smoothPeriodicVelocityJets_injective (m : ℕ) :
    Function.Injective (smoothPeriodicVelocityJets m) := by
  intro v w h
  apply Subtype.ext
  funext x
  have hx := congrArg (fun U : SpatialJetTuple Vec3 Vec3 m =>
    continuousMultilinearCurryFin0 ℝ Vec3 Vec3 (U 0 x)) h
  let C := continuousMultilinearCurryFin0 ℝ Vec3 Vec3
  change C (smoothPeriodicVelocityJet 0 v x) = C (smoothPeriodicVelocityJet 0 w x) at hx
  simpa only [smoothPeriodicVelocityJet_apply, iteratedFDeriv_zero_eq_comp,
    Function.comp_apply, LinearIsometryEquiv.apply_symm_apply, C] using hx

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicVelocityJetInclusion (m : ℕ) :
    LinearMap.range (smoothPeriodicVelocityJets m) →ₗᵢ[ℝ] PeriodicVelocityJetSpace m where
  toLinearMap := Submodule.inclusion (LinearMap.range (smoothPeriodicVelocityJets m)).le_topologicalClosure
  norm_map' _ := rfl

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem denseRange_periodicVelocityJetInclusion (m : ℕ) :
    DenseRange (periodicVelocityJetInclusion m) :=
  (denseRange_inclusion_iff subset_closure).2 subset_rfl

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def smoothPeriodicVelocityJetRangeEquiv (m : ℕ) :=
  LinearEquiv.ofInjective (smoothPeriodicVelocityJets m) (smoothPeriodicVelocityJets_injective m)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicVelocityJetsLinear (m : ℕ) : smoothPeriodicVelocity →ₗ[ℝ] PeriodicVelocityJetSpace m :=
  (periodicVelocityJetInclusion m).toLinearMap.comp (smoothPeriodicVelocityJetRangeEquiv m).toLinearMap

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicVelocityJetComponent (m : ℕ) (i : Fin (m + 1)) :
    PeriodicVelocityJetSpace m →L[ℝ] BoundedSpatialJet Vec3 Vec3 i :=
  (ContinuousLinearMap.proj i).comp (PeriodicVelocityJetSpace m).subtypeL

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem norm_periodicVelocityJet_le (m : ℕ) (u : smoothPeriodicVelocity)
    (i : Fin (m + 1)) (x : Vec3) :
    ‖iteratedFDeriv ℝ (i : ℕ) (u : Vec3 → Vec3) x‖ ≤ ‖periodicVelocityJets m u‖ :=
  ((smoothPeriodicVelocityJet i u).norm_coe_le_norm x).trans <|
    norm_le_pi_norm (smoothPeriodicVelocityJets m u) i

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem periodicMomentumTensor_smooth (u v : smoothPeriodicVelocity) :
    ContDiff ℝ ∞ (fun x : Vec3 => momentumTensor ((u : Vec3 → Vec3) x) ((v : Vec3 → Vec3) x)) :=
  (momentumTensor.contDiff.comp (smoothPeriodicVelocity_smooth u)).clm_apply
    (smoothPeriodicVelocity_smooth v)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicMomentumDivergence (u v : smoothPeriodicVelocity) : smoothPeriodicVelocity := by
  let q := fun x : Vec3 => momentumTensor ((u : Vec3 → Vec3) x) ((v : Vec3 → Vec3) x)
  have hper : SpatiallyPeriodic q := by
    intro n x
    dsimp only [q]
    rw [smoothPeriodicVelocity_periodic u n x, smoothPeriodicVelocity_periodic v n x]
  refine ⟨momentumTensorDivergence ∘ fderiv ℝ q, ?_, ?_⟩
  · exact momentumTensorDivergence.contDiff.comp
      ((periodicMomentumTensor_smooth u v).fderiv_right (by simp))
  · intro n x
    have hD : fderiv ℝ q (x + latticeVector n) = fderiv ℝ q x := by
      rw [← fderiv_comp_add_right]
      exact congrArg (fun f : Vec3 → MomentumTensor => fderiv ℝ f x) (funext (hper n))
    exact congrArg momentumTensorDivergence hD

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem periodicMomentumDivergence_apply (u v : smoothPeriodicVelocity) (x : Vec3) :
    (periodicMomentumDivergence u v : Vec3 → Vec3) x =
      momentumTensorDivergence (fderiv ℝ (fun y => momentumTensor
        ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) x) :=
  rfl

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicMomentumDivergenceBilinear :
    smoothPeriodicVelocity →ₗ[ℝ] smoothPeriodicVelocity →ₗ[ℝ] smoothPeriodicVelocity :=
  LinearMap.mk₂ ℝ periodicMomentumDivergence
    (fun u v w => by
      apply Subtype.ext
      funext x
      simp only [periodicMomentumDivergence_apply, Submodule.coe_add, Pi.add_apply, map_add, _root_.add_apply]
      rw [show (fun y : Vec3 => momentumTensor ((u : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y) +
          momentumTensor ((v : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y)) =
          ((fun y => momentumTensor ((u : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y)) +
          (fun y => momentumTensor ((v : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y))) from rfl,
        fderiv_add ((periodicMomentumTensor_smooth u w).differentiable (by simp) x)
          ((periodicMomentumTensor_smooth v w).differentiable (by simp) x), map_add])
    (fun c u v => by
      apply Subtype.ext
      funext x
      simp only [periodicMomentumDivergence_apply, Submodule.coe_smul, Pi.smul_apply, map_smul, _root_.smul_apply]
      rw [show (fun y : Vec3 => c • momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) =
          c • (fun y => momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) from rfl,
        fderiv_const_smul ((periodicMomentumTensor_smooth u v).differentiable (by simp) x),
        map_smul])
    (fun u v w => by
      apply Subtype.ext
      funext x
      simp only [periodicMomentumDivergence_apply, Submodule.coe_add, Pi.add_apply, map_add]
      rw [show (fun y : Vec3 => momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y) +
          momentumTensor ((u : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y)) =
          ((fun y => momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) +
          (fun y => momentumTensor ((u : Vec3 → Vec3) y) ((w : Vec3 → Vec3) y))) from rfl,
        fderiv_add ((periodicMomentumTensor_smooth u v).differentiable (by simp) x)
          ((periodicMomentumTensor_smooth u w).differentiable (by simp) x), map_add])
    (fun c u v => by
      apply Subtype.ext
      funext x
      simp only [periodicMomentumDivergence_apply, Submodule.coe_smul, Pi.smul_apply, map_smul]
      rw [show (fun y : Vec3 => c • momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) =
          c • (fun y => momentumTensor ((u : Vec3 → Vec3) y) ((v : Vec3 → Vec3) y)) from rfl,
        fderiv_const_smul ((periodicMomentumTensor_smooth u v).differentiable (by simp) x),
        map_smul])

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem periodicLerayHolderLift_smul_smooth (c : ℝ) (f : smoothPeriodicVelocity) :
    periodicLerayHolderLift (c • (f : Vec3 → Vec3)) = c • periodicLerayHolderLift f := by
  have hf := spatialHolderHalf_of_contDiff_periodic (smoothPeriodicVelocity_smooth f)
    (smoothPeriodicVelocity_periodic f) 0
  obtain ⟨u, hu, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero (smoothPeriodicVelocity_periodic f) hf
  have huv (x : Vec3) : HalfHolder.eval (toUnitTorus x) (c • u) = (c • (f : Vec3 → Vec3)) x := by
    rw [map_smul, hu]
    rfl
  rw [← funext huv, ← funext hu, periodicLerayHolderLift_pullback, periodicLerayHolderLift_pullback, map_smul]
  funext x
  exact (HalfHolder.eval (toUnitTorus x)).map_smul _ _

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def signedPeriodicLeray : smoothPeriodicVelocity →ₗ[ℝ] smoothPeriodicVelocity where
  toFun f := ⟨-periodicLerayHolderLift f,
    contDiff_infty.mpr fun m =>
      ((spatialHolderHalf_periodicLerayHolderLift (smoothPeriodicVelocity_periodic f)
        (spatialHolderHalf_of_contDiff_periodic (smoothPeriodicVelocity_smooth f)
          (smoothPeriodicVelocity_periodic f) m)).1.1).neg,
    fun n x => by simp only [Pi.neg_apply, spatiallyPeriodic_periodicLerayHolderLift _ n x]⟩
  map_add' f g := by
    apply Subtype.ext
    change -periodicLerayHolderLift ((f : Vec3 → Vec3) + g) =
      -periodicLerayHolderLift f + -periodicLerayHolderLift g
    rw [periodicLerayHolderLift_add (smoothPeriodicVelocity_periodic f) (smoothPeriodicVelocity_periodic g)
      (spatialHolderHalf_of_contDiff_periodic (smoothPeriodicVelocity_smooth f)
        (smoothPeriodicVelocity_periodic f) 0)
      (spatialHolderHalf_of_contDiff_periodic (smoothPeriodicVelocity_smooth g)
        (smoothPeriodicVelocity_periodic g) 0), neg_add]
  map_smul' c f := by
    apply Subtype.ext
    change -periodicLerayHolderLift (c • (f : Vec3 → Vec3)) = c • -periodicLerayHolderLift f
    rw [periodicLerayHolderLift_smul_smooth, smul_neg]

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def periodicProjectedMomentumBilinear :
    smoothPeriodicVelocity →ₗ[ℝ] smoothPeriodicVelocity →ₗ[ℝ] smoothPeriodicVelocity :=
  periodicMomentumDivergenceBilinear.compr₂ signedPeriodicLeray

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem periodicProjectedMomentumBilinear_coe (u v : smoothPeriodicVelocity) :
    (periodicProjectedMomentumBilinear u v : Vec3 → Vec3) = periodicProjectedMomentum u v :=
  rfl

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem norm_iteratedFDeriv_le_holderNorm
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Vec3 → F} {m : ℕ}
    (hf : SpatialHolderHalf m f) {j : ℕ} (hj : j ≤ m) (x : Vec3) :
    ‖iteratedFDeriv ℝ j f x‖ ≤ spatialHolderHalfNorm m f := by
  have hsemi (k : ℕ) (hk : k ≤ m) :
      0 ≤ spatialHolderHalfSeminorm (iteratedFDeriv ℝ k f) := by
    have h := le_ciSup (hf.2 k hk).2 ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ k f) (0, 0) = 0 by
      simp [spatialHolderHalfQuotient]] at h
    exact h
  have hsup (k : ℕ) (hk : k ≤ m) : 0 ≤ spatialSupNorm (iteratedFDeriv ℝ k f) :=
    (norm_nonneg _).trans (norm_le_spatialSupNorm (hf.2 k hk).1 0)
  refine (norm_le_spatialSupNorm (hf.2 j hj).1 x).trans <|
    (le_add_of_nonneg_right (hsemi j hj)).trans ?_
  unfold spatialHolderHalfNorm
  exact Finset.single_le_sum (s := Finset.range (m + 1))
    (fun k hk => add_nonneg (hsup k (Finset.mem_range_succ_iff.mp hk))
      (hsemi k (Finset.mem_range_succ_iff.mp hk)))
    (Finset.mem_range_succ_iff.mpr hj)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem periodicVelocityHolderNorm_le (m : ℕ) (u : smoothPeriodicVelocity) :
    SpatialHolderHalf m (u : Vec3 → Vec3) ∧
      spatialHolderHalfNorm m (u : Vec3 → Vec3) ≤
        (3 * (m + 1) : ℝ) * ‖periodicVelocityJets (m + 1) u‖ := by
  let R := ‖periodicVelocityJets (m + 1) u‖
  have h := spatialHolderHalf_of_bounded_jets (m := m) (smoothPeriodicVelocity_smooth u)
    (fun _ => R) (fun j hj x => norm_periodicVelocityJet_le (m + 1) u
      ⟨j, Nat.lt_succ_of_le hj⟩ x)
  refine ⟨h.1, h.2.trans ?_⟩
  have hsqrt : Real.sqrt (2 * R * R) ≤ 2 * R := Real.sqrt_le_iff.2
    ⟨by dsimp only [R]; positivity, by nlinarith [sq_nonneg R]⟩
  calc
    _ ≤ ∑ _ ∈ Finset.range (m + 1), (3 * R) :=
      Finset.sum_le_sum fun _ _ => by linarith
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one, R]
      ring
/-- The bound of the projected momentum map from order `m + 2` jets to order `m` jets, with the
constant `C_{m+1}` of the product estimate (5.59) taken from the hypothesis `h` (copy of the
library's private `periodicMomentumJetBound`, whose constant `3(m+2)2^{m+1}` came from
`spatialHolderHalf_bilinear`). -/
def periodicMomentumJetBound (h59 : Statement.Text.eq_5_59) (m : ℕ) : ℝ :=
  (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) *
    ‖momentumTensorDivergence‖ *
    ((h59 (m + 1)).choose * ‖momentumTensor‖) *
    (3 * (m + 2)) ^ 2

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
theorem nonneg_periodicMomentumJetBound (h59 : Statement.Text.eq_5_59) (m : ℕ) :
    0 ≤ periodicMomentumJetBound h59 m := by
  have hK := (h59 (m + 1)).choose_spec.1
  unfold periodicMomentumJetBound
  positivity

/-- The momentum bound on smooth periodic velocities (copy of the library's private
`norm_periodicProjectedMomentumJets_le`): the product estimate (5.59) for
`u ⊗ v = momentumTensor u v` at order `m + 1` is the hypothesis `h`, followed by the
divergence and the boundedness of the periodic Leray projection on `C^{m,1/2}`. -/
theorem norm_periodicProjectedMomentumJets_le (h59 : Statement.Text.eq_5_59) (m : ℕ)
    (u v : smoothPeriodicVelocity) :
    ‖periodicVelocityJets m (periodicProjectedMomentumBilinear u v)‖ ≤
      periodicMomentumJetBound h59 m *
      ‖periodicVelocityJets (m + 2) u‖ * ‖periodicVelocityJets (m + 2) v‖ := by
  let p := periodicMomentumDivergence u v
  let q := periodicLerayHolderLift (p : Vec3 → Vec3)
  have hu := periodicVelocityHolderNorm_le (m + 1) u
  have hv := periodicVelocityHolderNorm_le (m + 1) v
  have hK := (h59 (m + 1)).choose_spec.1
  have hq := (h59 (m + 1)).choose_spec.2 momentumTensor _ _ hu.1 hv.1
  have hD := spatialHolderHalf_contraction_fderiv momentumTensorDivergence hq.1
  have hP := spatialHolderHalf_periodicLerayHolderLift (smoothPeriodicVelocity_periodic p) hD.1
  have hu₀ : 0 ≤ spatialHolderHalfNorm (m + 1) (u : Vec3 → Vec3) := by
    exact (norm_nonneg _).trans (norm_iteratedFDeriv_le_holderNorm hu.1 (Nat.zero_le _) 0)
  have hv₀ : 0 ≤ spatialHolderHalfNorm (m + 1) (v : Vec3 → Vec3) := by
    exact (norm_nonneg _).trans (norm_iteratedFDeriv_le_holderNorm hv.1 (Nat.zero_le _) 0)
  have hbound : spatialHolderHalfNorm m q ≤ periodicMomentumJetBound h59 m *
      ‖periodicVelocityJets (m + 2) u‖ * ‖periodicVelocityJets (m + 2) v‖ := by
    have hC : 0 ≤ 2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖ := by positivity
    calc
      spatialHolderHalfNorm m q ≤ (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) *
          spatialHolderHalfNorm m (p : Vec3 → Vec3) := hP.2
      _ ≤ (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) *
          (‖momentumTensorDivergence‖ * spatialHolderHalfNorm (m + 1)
            (fun x => momentumTensor ((u : Vec3 → Vec3) x) ((v : Vec3 → Vec3) x))) := by
        gcongr
        exact hD.2
      _ ≤ (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) *
          (‖momentumTensorDivergence‖ * ((h59 (m + 1)).choose * ‖momentumTensor‖ *
            spatialHolderHalfNorm (m + 1) (u : Vec3 → Vec3) *
            spatialHolderHalfNorm (m + 1) (v : Vec3 → Vec3))) := by
        gcongr
        exact hq.2
      _ ≤ (2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖) *
          (‖momentumTensorDivergence‖ * ((h59 (m + 1)).choose * ‖momentumTensor‖ *
            ((3 * ((m + 1 : ℕ) + 1) : ℝ) * ‖periodicVelocityJets (m + 2) u‖) *
            ((3 * ((m + 1 : ℕ) + 1) : ℝ) * ‖periodicVelocityJets (m + 2) v‖))) := by
        gcongr
        · simpa only [Nat.cast_add, Nat.cast_one] using hu.2
        · simpa only [Nat.cast_add, Nat.cast_one] using hv.2
      _ = _ := by
        simp only [periodicMomentumJetBound, Nat.cast_add, Nat.cast_one]
        ring
  change ‖smoothPeriodicVelocityJets m (periodicProjectedMomentumBilinear u v)‖ ≤ _
  have hnonneg : 0 ≤ periodicMomentumJetBound h59 m * ‖periodicVelocityJets (m + 2) u‖ *
      ‖periodicVelocityJets (m + 2) v‖ :=
    mul_nonneg (mul_nonneg (nonneg_periodicMomentumJetBound h59 m) (norm_nonneg _)) (norm_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hnonneg).2
  intro i
  apply BoundedContinuousFunction.norm_le hnonneg |>.2
  intro x
  change ‖smoothPeriodicVelocityJet i (periodicProjectedMomentumBilinear u v) x‖ ≤ _
  rw [smoothPeriodicVelocityJet_apply, periodicProjectedMomentumBilinear_coe,
    show periodicProjectedMomentum u v = -q from rfl, iteratedFDeriv_neg, Pi.neg_apply, norm_neg]
  exact (norm_iteratedFDeriv_le_holderNorm hP.1 (Nat.le_of_lt_succ i.isLt) x).trans hbound

set_option maxHeartbeats 650000 in
/-- The bounded bilinear momentum map on smooth jets (copy of the library's private
`boundedPeriodicMomentumOnSmoothJets`, with the bound of `h`). -/
def boundedPeriodicMomentumOnSmoothJets (h59 : Statement.Text.eq_5_59) (m : ℕ) :
    LinearMap.range (smoothPeriodicVelocityJets (m + 2)) →L[ℝ]
      LinearMap.range (smoothPeriodicVelocityJets (m + 2)) →L[ℝ] PeriodicVelocityJetSpace m := by
  let e := smoothPeriodicVelocityJetRangeEquiv (m + 2)
  let j := periodicVelocityJetsLinear m
  let B := ((periodicProjectedMomentumBilinear.compr₂ j).compl₂ e.symm.toLinearMap).comp
    e.symm.toLinearMap
  refine B.mkContinuous₂ (periodicMomentumJetBound h59 m) ?_
  intro a b
  obtain ⟨u, rfl⟩ := e.surjective a
  obtain ⟨v, rfl⟩ := e.surjective b
  change ‖j (periodicProjectedMomentumBilinear (e.symm (e u)) (e.symm (e v)))‖ ≤ _
  rw [e.symm_apply_apply, e.symm_apply_apply]
  exact norm_periodicProjectedMomentumJets_le h59 m u v

/-- The signed periodic Euler momentum as a bounded bilinear map from order `m+2` compatible
velocity jets to order `m` jets (copy of the library's `periodicProjectedMomentumJets`, with
the product estimate (5.59) from `h`). -/
def periodicProjectedMomentumJets (h59 : Statement.Text.eq_5_59) (m : ℕ) :
    PeriodicVelocityJetSpace (m + 2) →L[ℝ]
      PeriodicVelocityJetSpace (m + 2) →L[ℝ] PeriodicVelocityJetSpace m :=
  extendJetBilinear (periodicVelocityJetInclusion (m + 2))
    (denseRange_periodicVelocityJetInclusion (m + 2)) (boundedPeriodicMomentumOnSmoothJets h59 m)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
theorem periodicProjectedMomentumJets_smooth (h59 : Statement.Text.eq_5_59) (m : ℕ)
    (u v : smoothPeriodicVelocity) :
    periodicProjectedMomentumJets h59 m (periodicVelocityJets (m + 2) u)
        (periodicVelocityJets (m + 2) v) =
      periodicVelocityJets m (periodicProjectedMomentumBilinear u v) := by
  change extendJetBilinear _ _ (boundedPeriodicMomentumOnSmoothJets h59 m)
    (periodicVelocityJetInclusion (m + 2) (smoothPeriodicVelocityJetRangeEquiv (m + 2) u))
    (periodicVelocityJetInclusion (m + 2) (smoothPeriodicVelocityJetRangeEquiv (m + 2) v)) = _
  rw [extendJetBilinear_apply]
  simp only [boundedPeriodicMomentumOnSmoothJets, LinearMap.mkContinuous₂_apply,
    LinearMap.comp_apply, LinearMap.compl₂_apply, LinearMap.compr₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  rfl

/-- On smooth periodic inputs, the bounded momentum map returns the actual spatial derivatives
of the signed projected tensor divergence. -/
theorem periodicProjectedMomentumJets_apply (h59 : Statement.Text.eq_5_59) (m : ℕ)
    (u v : smoothPeriodicVelocity) (i : Fin (m + 1)) (x : Vec3) :
    (periodicProjectedMomentumJets h59 m (periodicVelocityJets (m + 2) u)
      (periodicVelocityJets (m + 2) v) : SpatialJetTuple Vec3 Vec3 m) i x =
      iteratedFDeriv ℝ (i : ℕ) (periodicProjectedMomentum u v) x := by
  rw [periodicProjectedMomentumJets_smooth, periodicVelocityJets_apply,
    periodicProjectedMomentumBilinear_coe]

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem smoothPeriodicVelocityJet_hasFDerivAt (u : smoothPeriodicVelocity) (m : ℕ) (x : Vec3) :
    HasFDerivAt (fun y => smoothPeriodicVelocityJet m u y)
      ((smoothPeriodicVelocityJet (m + 1) u x).curryLeft) x := by
  simp only [smoothPeriodicVelocityJet_apply]
  have h := (smoothPeriodicVelocity_smooth u).contDiffOn.ftaylorSeriesWithin (s := univ) uniqueDiffOn_univ
  have hm : (m : ℕ∞ω) < ∞ := by exact_mod_cast (ENat.natCast_lt_top m)
  simpa only [ftaylorSeriesWithin, iteratedFDerivWithin_univ] using
    (h.fderivWithin m hm x (mem_univ x)).hasFDerivAt (univ_mem : univ ∈ 𝓝 x)

/-- Joint smoothness up to the initial face follows from spatial jet continuity
and the integrated evolution with the actual signed periodic Leray momentum. -/
theorem contDiffOn_periodicEulerVelocity_of_integrated_momentum (h59 : Statement.Text.eq_5_59)
    {S : ℝ} (hS : 0 < S) (u : ℝ → smoothPeriodicVelocity)
    (hcont : ∀ m, ContinuousOn (fun t => periodicVelocityJets m (u t)) (Icc 0 S))
    (hEq : ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Vec3,
      (u t : Vec3 → Vec3) x = (u 0 : Vec3 → Vec3) x +
        endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => (u p.1 : Vec3 → Vec3) p.2) (Icc 0 S ×ˢ univ) := by
  let V m t := periodicVelocityJets m (u t)
  let W m t := periodicProjectedMomentumJets h59 m (V (m + 2) t) (V (m + 2) t)
  let J (m : ℕ) (t : ℝ) := smoothPeriodicVelocityJet m (u t)
  let U (m : ℕ) (t : ℝ) := smoothPeriodicVelocityJet m (periodicProjectedMomentumBilinear (u t) (u t))
  have hWV (m : ℕ) (t : ℝ) :
      W m t = periodicVelocityJets m (periodicProjectedMomentumBilinear (u t) (u t)) :=
    periodicProjectedMomentumJets_smooth h59 m (u t) (u t)
  have hcompV (m : ℕ) (i : Fin (m + 1)) (t : ℝ) :
      periodicVelocityJetComponent m i (V m t) = J i t := rfl
  have hcompW (m : ℕ) (i : Fin (m + 1)) (t : ℝ) :
      periodicVelocityJetComponent m i (W m t) = U i t := by
    rw [hWV]
    rfl
  have hW (m : ℕ) : ContinuousOn (W m) (Icc 0 S) :=
    (((periodicProjectedMomentumJets h59 m).continuous.comp_continuousOn (hcont (m + 2))).clm_apply
      (hcont (m + 2)))
  have hU (m : ℕ) : ContinuousOn (U m) (Icc 0 S) := by
    let i : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    exact ((periodicVelocityJetComponent m i).continuous.comp_continuousOn (hW m)).congr
      (fun t _ => (hcompW m i t).symm)
  let C := continuousMultilinearCurryFin0 ℝ Vec3 Vec3
  have hC (f : Vec3 → Vec3) (x : Vec3) : C (iteratedFDeriv ℝ 0 f x) = f x := by
    rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, C.apply_symm_apply]
  have hEq0 (t : ℝ) (ht : t ∈ Icc 0 S) : J 0 t = J 0 0 + endpointPrimitive (U 0) t := by
    apply BoundedContinuousFunction.ext
    intro x
    apply C.injective
    change C (J 0 t x) = C (J 0 0 x + endpointPrimitive (U 0) t x)
    have hInt := ((hU 0).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hComm : endpointPrimitive (fun s => C (U 0 s x)) t = C (endpointPrimitive (U 0) t x) :=
      (C.toContinuousLinearEquiv.toContinuousLinearMap.comp (evalCLM ℝ x)).intervalIntegral_comp_comm hInt
    have hRhs (s : ℝ) : C (U 0 s x) = periodicProjectedMomentum (u s) (u s) x := by
      change C (smoothPeriodicVelocityJet 0 (periodicProjectedMomentumBilinear (u s) (u s)) x) = _
      rw [smoothPeriodicVelocityJet_apply, hC, periodicProjectedMomentumBilinear_coe]
    rw [map_add, ← hComm, show (fun s : ℝ => C (U 0 s x)) =
      (fun s : ℝ => periodicProjectedMomentum (u s) (u s) x) from funext hRhs]
    simpa only [J, smoothPeriodicVelocityJet_apply, hC] using hEq t ht x
  have hEqs := integrated_spatialJets_of_zeroth hS.le J U
    (fun t _ => smoothPeriodicVelocityJet_hasFDerivAt (u t))
    (fun t _ => smoothPeriodicVelocityJet_hasFDerivAt (periodicProjectedMomentumBilinear (u t) (u t)))
    hU hEq0
  have hEqV (m : ℕ) (t : ℝ) (ht : t ∈ Icc 0 S) :
      V m t = V m 0 + endpointPrimitive (W m) t := by
    apply Subtype.ext
    funext i
    let L := periodicVelocityJetComponent m i
    change L (V m t) = L (V m 0 + endpointPrimitive (W m) t)
    have hInt := ((hW m).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hComm : endpointPrimitive (fun s => L (W m s)) t = L (endpointPrimitive (W m) t) :=
      L.intervalIntegral_comp_comm hInt
    rw [map_add, ← hComm, show (fun s => L (W m s)) = U i from funext (hcompW m i)]
    simpa only [L, hcompV] using hEqs i t ht
  have hV := contDiffOn_jetTower_of_integrated hS V (fun m => m + 2)
    (periodicProjectedMomentumJets h59) hcont hEqV
  have hJ (m : ℕ) : ContDiffOn ℝ ∞ (J m) (Icc 0 S) := by
    let i : Fin (m + 1) := ⟨m, Nat.lt_succ_self m⟩
    exact ((periodicVelocityJetComponent m i).contDiff.comp_contDiffOn (hV m)).congr
      (fun t _ => (hcompV m i t).symm)
  have hjoint := contDiffOn_joint_of_spatialJets_time hS J hJ
    (fun t _ => smoothPeriodicVelocityJet_hasFDerivAt (u t)) 0
  refine (C.toContinuousLinearEquiv.toContinuousLinearMap.contDiff.comp_contDiffOn hjoint).congr ?_
  intro p _
  change (u p.1 : Vec3 → Vec3) p.2 = C (smoothPeriodicVelocityJet 0 (u p.1) p.2)
  rw [smoothPeriodicVelocityJet_apply, hC]


/-- Closed-prefix joint smoothness from the actual integrated projected momentum,
periodicity, and jointly continuous spatial derivatives of every finite order. -/
theorem contDiffOn_periodicEulerVelocity_of_integrated_projected_momentum
    (h59 : Statement.Text.eq_5_59) {S : ℝ} (hS : 0 < S) {u : Velocity}
    (hsmooth : ∀ t ∈ Icc (0 : ℝ) S, ContDiff ℝ ∞ (u t))
    (hperiodic : ∀ t ∈ Icc (0 : ℝ) S, SpatiallyPeriodic (u t))
    (hjets : ∀ m, ContinuousOn (fun p : ℝ × Vec3 =>
      iteratedFDeriv ℝ m (u p.1) p.2) (Icc 0 S ×ˢ univ))
    (hEq : ∀ t ∈ Icc (0 : ℝ) S, ∀ x : Vec3, u t x = u 0 x +
      endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ univ) := by
  classical
  let v (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ Icc 0 S then ⟨u t, hsmooth t ht, hperiodic t ht⟩ else 0
  have hV (t : ℝ) (ht : t ∈ Icc 0 S) : (v t : Vec3 → Vec3) = u t := by simp only [v, dite_eq_left ht]
  have hC := continuousOn_periodicVelocityJets_of_joint_spatialJets v (fun m =>
    (hjets m).congr fun p hp => by rw [hV p.1 hp.1])
  have hR (t : ℝ) (ht : t ∈ Icc 0 S) (x : Vec3) :
      (v t : Vec3 → Vec3) x = (v 0 : Vec3 → Vec3) x +
        endpointPrimitive (fun s => periodicProjectedMomentum (v s) (v s) x) t := by
    rw [hV t ht, hV 0 ⟨le_rfl, hS.le⟩]
    refine (hEq t ht x).trans (congrArg (u 0 x + ·) ?_)
    apply endpointPrimitive_congr_ae _ ht
    filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := S))]
      with s hs
    rw [hV s (Ioc_subset_Icc_self hs)]
  exact (contDiffOn_periodicEulerVelocity_of_integrated_momentum h59 hS v hC hR).congr <|
    fun p hp => (congrFun (hV p.1 hp.1) p.2).symm

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private def evalPeriodicMomentumJetZero (x : Vec3) : PeriodicVelocityJetSpace 0 →L[ℝ] Vec3 :=
  (continuousMultilinearCurryFin0 ℝ Vec3 Vec3).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((evalCLM ℝ x).comp ((ContinuousLinearMap.proj (0 : Fin 1)).comp
      (PeriodicVelocityJetSpace 0).subtypeL))

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem evalPeriodicMomentumJetZero_apply (h59 : Statement.Text.eq_5_59) (u v : smoothPeriodicVelocity)
    (x : Vec3) :
    evalPeriodicMomentumJetZero x (periodicProjectedMomentumJets h59 0 (periodicVelocityJets 2 u)
      (periodicVelocityJets 2 v)) = periodicProjectedMomentum u v x := by
  let C := continuousMultilinearCurryFin0 ℝ Vec3 Vec3
  let V := periodicProjectedMomentumJets h59 0 (periodicVelocityJets 2 u) (periodicVelocityJets 2 v)
  change C ((V : SpatialJetTuple Vec3 Vec3 0) 0 x) = _
  rw [periodicProjectedMomentumJets_apply h59]
  change C (iteratedFDeriv ℝ 0 (periodicProjectedMomentum u v) x) = _
  rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, C.apply_symm_apply]

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem continuousOn_periodicProjectedMomentum (h59 : Statement.Text.eq_5_59) {S : ℝ}
    (u : ℝ → smoothPeriodicVelocity)
    (h : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S)) (x : Vec3) :
    ContinuousOn (fun t => periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) := by
  have hW := ((periodicProjectedMomentumJets h59 0).continuous.comp_continuousOn h).clm_apply h
  exact ((evalPeriodicMomentumJetZero x).continuous.comp_continuousOn hW).congr
    (fun t _ => (evalPeriodicMomentumJetZero_apply h59 (u t) (u t) x).symm)

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem tendstoUniformlyOn_bilinear_diagonal
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ}
    (B : E →L[ℝ] E →L[ℝ] F) {U : ℕ → ℝ → E} {u : ℝ → E}
    (h : TendstoUniformlyOn U u atTop (Icc 0 S)) (hc : ContinuousOn u (Icc 0 S)) :
    TendstoUniformlyOn (fun j t => B (U j t) (U j t)) (fun t => B (u t) (u t))
      atTop (Icc 0 S) := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBA := B.uniformContinuous.comp_tendstoUniformlyOn h
  have hbound (t : ℝ) (ht : t ∈ Icc 0 S) : ‖B (u t)‖ ≤ ‖B‖ * max M 0 :=
    (B.le_opNorm _).trans
      (mul_le_mul_of_nonneg_left ((hM t ht).trans (le_max_left _ _)) (norm_nonneg _))
  have hM' (t : ℝ) (ht : t ∈ Icc 0 S) : ‖u t‖ ≤ max M 0 := (hM t ht).trans (le_max_left _ _)
  exact tendstoUniformlyOn_clm_apply_of_bounded hBA h (C := ‖B‖ * max M 0) (M := max M 0)
    (mul_nonneg (norm_nonneg B) (le_max_right M 0)) (le_max_right M 0) hbound hM'

set_option synthInstance.maxHeartbeats 125000 in
/-- Uniform convergence in two compatible spatial jet orders passes through the
actual signed projected quadratic momentum, at each fixed spatial point. -/
theorem tendstoUniformlyOn_periodicProjectedMomentum_of_jetTuples (h59 : Statement.Text.eq_5_59) {S : ℝ}
    {U : ℕ → ℝ → smoothPeriodicVelocity} {u : ℝ → smoothPeriodicVelocity}
    (h : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (U j t))
      (fun t => periodicVelocityJets 2 (u t)) atTop (Icc 0 S))
    (hc : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S)) (x : Vec3) :
    TendstoUniformlyOn (fun j t => periodicProjectedMomentum (U j t) (U j t) x)
      (fun t => periodicProjectedMomentum (u t) (u t) x) atTop (Icc 0 S) := by
  have hN := tendstoUniformlyOn_bilinear_diagonal (periodicProjectedMomentumJets h59 0) h hc
  simpa only [Function.comp_def, evalPeriodicMomentumJetZero_apply h59] using
    (evalPeriodicMomentumJetZero x).uniformContinuous.comp_tendstoUniformlyOn hN

/-- Copy, unchanged except for the argument `h59` where it is threaded, of the library declaration of the same name (TorusEuler/PeriodicEulerMomentumJets.lean or TorusEuler/PeriodicEulerLimit.lean). -/
private theorem integrated_periodicProjectedMomentum_of_uniformLimits (h59 : Statement.Text.eq_5_59)
    {S : ℝ} (hS : 0 < S) {U : ℕ → ℝ → smoothPeriodicVelocity} {u : ℝ → smoothPeriodicVelocity}
    {R : ℕ → Velocity} (x : Vec3)
    (hU : TendstoUniformlyOn (fun j t => (U j t : Vec3 → Vec3) x)
      (fun t => (u t : Vec3 → Vec3) x) atTop (Icc 0 S))
    (hJ : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (U j t))
      (fun t => periodicVelocityJets 2 (u t)) atTop (Icc 0 S))
    (hUc : ∀ j, ContinuousOn (fun t => (U j t : Vec3 → Vec3) x) (Icc 0 S))
    (hJc : ∀ j, ContinuousOn (fun t => periodicVelocityJets 2 (U j t)) (Icc 0 S))
    (huc : ContinuousOn (fun t => periodicVelocityJets 2 (u t)) (Icc 0 S))
    (hR : TendstoUniformlyOn (fun j t => R j t x) (fun _ => 0) atTop (Icc 0 S))
    (hRc : ∀ j, ContinuousOn (fun t => R j t x) (Icc 0 S))
    (hStage : ∀ j t, t ∈ Icc 0 S → HasDerivWithinAt (fun r => (U j r : Vec3 → Vec3) x)
      (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t) :
    (∀ t ∈ Icc 0 S, (u t : Vec3 → Vec3) x = (u 0 : Vec3 → Vec3) x +
      endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
    (∀ t ∈ Icc 0 S, HasDerivWithinAt (fun r => (u r : Vec3 → Vec3) x)
      (periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) t) := by
  let N j t := periodicProjectedMomentum (U j t) (U j t) x
  let n t := periodicProjectedMomentum (u t) (u t) x
  have hN : TendstoUniformlyOn N n atTop (Icc 0 S) :=
    tendstoUniformlyOn_periodicProjectedMomentum_of_jetTuples h59 hJ huc x
  have hNc (j : ℕ) : ContinuousOn (N j) (Icc 0 S) :=
    continuousOn_periodicProjectedMomentum h59 (U j) (hJc j) x
  have hInt (j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 S) :
      (U j t : Vec3 → Vec3) x = (U j 0 : Vec3 → Vec3) x -
        (∫ s in (0 : ℝ)..t, -N j s) + ∫ s in (0 : ℝ)..t, R j s x := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc_right ht.2
    have hNint := ((hNc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hRint := ((hRc j).mono hsub).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 ((hUc j).mono hsub)
      (fun r hr => (hStage j r ⟨hr.1.le, hr.2.le.trans ht.2⟩).hasDerivAt
        (mem_of_superset (Ioo_mem_nhds hr.1 (hr.2.trans_le ht.2)) Ioo_subset_Icc_self))
      (hNint.add hRint)
    change (∫ r in (0 : ℝ)..t, N j r + R j r x) =
      (U j t : Vec3 → Vec3) x - (U j 0 : Vec3 → Vec3) x at hFTC
    rw [intervalIntegral.integral_add hNint hRint] at hFTC
    rw [intervalIntegral.integral_neg, sub_neg_eq_add, add_assoc, hFTC]
    abel
  have hLim := integratedLimit_of_uniformConvergence hS.le hU hN.neg hR
    (fun j => (hNc j).neg) hRc hInt
  refine ⟨fun t ht => ?_, fun t ht => ?_⟩
  · change (u t : Vec3 → Vec3) x = (u 0 : Vec3 → Vec3) x + ∫ s in (0 : ℝ)..t, n s
    simpa only [Pi.neg_apply, intervalIntegral.integral_neg, sub_neg_eq_add] using hLim.1 t ht
  · simpa only [Pi.neg_apply, neg_neg] using hLim.2 t ht


/-- On a compact prefix, the periodic stage equations with a uniformly vanishing
residual give both the actual limiting projected equation and joint smoothness. -/
theorem periodicProjectedEuler_of_stage_limits (h59 : Statement.Text.eq_5_59) {S : ℝ} (hS : 0 < S)
    {U R : ℕ → Velocity} {u : Velocity}
    (hStageSmooth : ∀ j, ContDiffOn ℝ ∞ (Function.uncurry (U j))
      (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hStagePeriodic : ∀ j t, t ∈ Icc 0 S → SpatiallyPeriodic (U j t))
    (huSmooth : ∀ t ∈ Icc 0 S, ContDiff ℝ ∞ (u t))
    (hU : TendstoUniformlyOn (fun j => Function.uncurry (U j)) (Function.uncurry u)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hJets : ∀ m, TendstoUniformlyOn
      (fun j (p : ℝ × Vec3) => iteratedFDeriv ℝ m (U j p.1) p.2)
      (fun p : ℝ × Vec3 => iteratedFDeriv ℝ m (u p.1) p.2) atTop (Icc 0 S ×ˢ univ))
    (hR : TendstoUniformlyOn (fun j => Function.uncurry (R j)) (fun _ => 0)
      atTop (Icc 0 S ×ˢ (univ : Set Vec3)))
    (hStage : ∀ j t, t ∈ Icc 0 S → ∀ x,
      HasDerivWithinAt (fun r => U j r x)
        (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t) :
    (∀ t ∈ Icc 0 S, ∀ x,
      u t x = u 0 x + endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
    (∀ t ∈ Icc 0 S, ∀ x,
      HasDerivWithinAt (fun r => u r x) (periodicProjectedMomentum (u t) (u t) x) (Icc 0 S) t) ∧
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  classical
  let I := Icc (0 : ℝ) S
  have hStageJets (j : ℕ) := stage_spatial_jets_of_joint_smoothness hS (hStageSmooth j)
  have hPeriodic (t : ℝ) (ht : t ∈ I) : SpatiallyPeriodic (u t) := by
    intro n x
    have h₁ := hU.tendsto_at (x := (t, x + latticeVector n)) ⟨ht, mem_univ _⟩
    have h₂ := hU.tendsto_at (x := (t, x)) ⟨ht, mem_univ _⟩
    exact tendsto_nhds_unique_of_eventuallyEq h₁ h₂
      (Eventually.of_forall fun j => hStagePeriodic j t ht n x)
  have hJetCont (m : ℕ) := (hJets m).continuousOn
    (Frequently.of_forall fun j => (hStageJets j).2 m)
  let Uₛ (j : ℕ) (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ I then ⟨U j t, (hStageJets j).1 t ht, hStagePeriodic j t ht⟩ else 0
  let uₛ (t : ℝ) : smoothPeriodicVelocity :=
    if ht : t ∈ I then ⟨u t, huSmooth t ht, hPeriodic t ht⟩ else 0
  have hUs (j : ℕ) (t : ℝ) (ht : t ∈ I) : (Uₛ j t : Vec3 → Vec3) = U j t := by
    simp only [Uₛ, dite_eq_left ht]
  have hus (t : ℝ) (ht : t ∈ I) : (uₛ t : Vec3 → Vec3) = u t := by
    simp only [uₛ, dite_eq_left ht]
  have hJetLimit : TendstoUniformlyOn (fun j t => periodicVelocityJets 2 (Uₛ j t))
      (fun t => periodicVelocityJets 2 (uₛ t)) atTop I := by
    apply tendstoUniformlyOn_periodicVelocityJets_of_iteratedFDeriv
    intro m _
    exact ((hJets m).congr (Eventually.of_forall fun j p hp => by rw [hUs j p.1 hp.1])).congr_right
      (fun p hp => by rw [hus p.1 hp.1])
  have hCStage (j : ℕ) := continuousOn_periodicVelocityJets_of_joint_spatialJets (Uₛ j)
    (fun m => ((hStageJets j).2 m).congr fun p hp => by rw [hUs j p.1 hp.1]) 2
  have hCu := continuousOn_periodicVelocityJets_of_joint_spatialJets uₛ
    (fun m => (hJetCont m).congr fun p hp => by rw [hus p.1 hp.1]) 2
  have hDynamics (x : Vec3) :
      (∀ t ∈ I, u t x = u 0 x + endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t) ∧
      (∀ t ∈ I, HasDerivWithinAt (fun r => u r x) (periodicProjectedMomentum (u t) (u t) x) I t) := by
    have hmaps : I ⊆ (fun r => (r, x)) ⁻¹' (I ×ˢ (univ : Set Vec3)) :=
      fun r hr => ⟨hr, mem_univ x⟩
    have hU' := (((hU.comp (fun t => (t, x))).mono hmaps).congr
      (Eventually.of_forall fun j t ht => congrFun (hUs j t ht).symm x)).congr_right
      (fun t ht => congrFun (hus t ht).symm x)
    have hUc (j : ℕ) : ContinuousOn (fun t => (Uₛ j t : Vec3 → Vec3) x) I :=
      (((hStageSmooth j).continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn) hmaps).congr
        (fun t ht => congrFun (hUs j t ht) x)
    have hRc (j : ℕ) : ContinuousOn (fun t => R j t x) I := by
      have hTime : ContinuousOn (fun t => derivWithin (fun r => U j r x) I t) I :=
        (contDiffOn_sliceTimeDerivWithin_Icc hS (hStageSmooth j)).continuousOn.comp
          (continuous_id.prodMk continuous_const).continuousOn hmaps
      have hMom : ContinuousOn (fun t => periodicProjectedMomentum (U j t) (U j t) x) I :=
        (continuousOn_periodicProjectedMomentum h59 (Uₛ j) (hCStage j) x).congr
          (fun t ht => by
            change periodicProjectedMomentum (U j t) (U j t) x =
              periodicProjectedMomentum (Uₛ j t) (Uₛ j t) x
            rw [hUs j t ht])
      refine (hTime.sub hMom).congr fun t ht => ?_
      change R j t x = derivWithin (fun r => U j r x) (Icc 0 S) t -
        periodicProjectedMomentum (U j t) (U j t) x
      rw [(hStage j t ht x).derivWithin (uniqueDiffOn_Icc hS t ht)]
      abel
    have hStage' (j : ℕ) (t : ℝ) (ht : t ∈ I) :
        HasDerivWithinAt (fun r => (Uₛ j r : Vec3 → Vec3) x)
          (periodicProjectedMomentum (Uₛ j t) (Uₛ j t) x + R j t x) I t := by
      rw [hUs j t ht]
      exact (hStage j t ht x).congr_of_mem (fun r hr => congrFun (hUs j r hr) x) ht
    have hL := integrated_periodicProjectedMomentum_of_uniformLimits h59 hS x hU' hJetLimit
      hUc hCStage hCu ((hR.comp (fun t => (t, x))).mono hmaps) hRc hStage'
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · have hintegral : endpointPrimitive (fun s => periodicProjectedMomentum (uₛ s) (uₛ s) x) t =
          endpointPrimitive (fun s => periodicProjectedMomentum (u s) (u s) x) t := by
        apply endpointPrimitive_congr_ae _ ht
        filter_upwards [ae_restrict_mem (μ := volume) (measurableSet_Ioc (a := (0 : ℝ)) (b := S))]
          with s hs
        rw [hus s (Ioc_subset_Icc_self hs)]
      simpa only [hus t ht, hus 0 ⟨le_rfl, hS.le⟩, hintegral] using hL.1 t ht
    · have hd := hL.2 t ht
      rw [hus t ht] at hd
      exact hd.congr_of_mem (fun r hr => congrFun (hus r hr).symm x) ht
  have hEq (t : ℝ) (ht : t ∈ I) (x : Vec3) := (hDynamics x).1 t ht
  exact ⟨hEq, fun t ht x => (hDynamics x).2 t ht,
    contDiffOn_periodicEulerVelocity_of_integrated_projected_momentum h59 hS huSmooth hPeriodic
      hJetCont hEq⟩






/-- Proposition 8.1's projected evolution and joint preterminal velocity
regularity, from the inductive velocity bounds and actual projected residuals. -/
theorem exists_inductive_periodicEulerProjectedLimit (h59 : Statement.Text.eq_5_59)
    {T : ℝ} {slab freq activation : ℕ → ℝ} {q : ℕ → ℕ} {U O R : ℕ → Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hactivation : Tendsto activation atTop (𝓝 T))
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hper : ∀ n t, t ∈ Icc 0 (slab n) → SpatiallyPeriodic (U n t))
    (hodd : ∀ n t, t ∈ Icc 0 (slab n) → Function.Odd (U n t))
    (hdiv : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, divergence (U n t) x = 0)
    (hOvanish : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), O n t = 0)
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹)
    (hProj : ∀ n t, t ∈ Icc 0 (slab n) → closedSlabLerayMomentum 0 (slab n) (U n) t = R n t)
    (hResidual : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, ‖R n t x‖ ≤ ((freq (n + 1))⁻¹)^3) :
    ∃ u : Velocity,
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry u)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set Vec3)) ∧
      (∀ t ∈ Ico 0 T, SpatiallyPeriodic (u t) ∧ Function.Odd (u t) ∧
        (∀ x, divergence (u t) x = 0) ∧
        ∀ x, timeDerivative T u t x = periodicProjectedMomentum (u t) (u t) x) ∧
      ∀ S, 0 < S → S < T → ∀ m, TendstoUniformlyOn
        (fun n (p : ℝ × Vec3) => iteratedFDeriv ℝ m (U n p.1) p.2)
        (fun p : ℝ × Vec3 => iteratedFDeriv ℝ m (u p.1) p.2)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
  obtain ⟨u, hu, hU, hLocal⟩ := exists_inductive_velocity_limit_and_spatial_jets hT hslab
    hinit hfreq hq hUstage hO hB
  have hPrefix (S : ℝ) (hST : S < T) :=
    hLocal (Icc 0 S) univ (Icc_subset_Icc_right hST.le) isOpen_univ
      (inductive_oscillations_eventually_zero_on_prefix hactivation hST hOvanish)
  have hDecay : Tendsto (fun n => ((freq (n + 1))⁻¹)^3) atTop (𝓝 0) := by
    simpa only [Nat.add_comm, zero_pow (by decide : 3 ≠ 0)] using
      (reciprocal_inductive_frequency_tail hinit hfreq 1).1.tendsto_atTop_zero.pow 3
  have hDynamics (S : ℝ) (hS : 0 < S) (hST : S < T) := by
    have hsub (n : ℕ) : Icc 0 S ⊆ Icc 0 (slab n) :=
      Icc_subset_Icc_right (hST.le.trans (hslab n))
    have hRlim : TendstoUniformlyOn (fun j => Function.uncurry (R j)) (fun _ => 0)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      filter_upwards [hDecay.eventually (Iio_mem_nhds hε)] with j hj p hp
      rw [dist_comm, dist_zero_right]
      exact (hResidual j p.1 (hsub j hp.1) p.2).trans_lt hj
    have hStage (j t) (ht : t ∈ Icc 0 S) (x : Vec3) :
        HasDerivWithinAt (fun r => U j r x)
          (periodicProjectedMomentum (U j t) (U j t) x + R j t x) (Icc 0 S) t := by
      have h := (hasDerivWithinAt_of_closedSlabLerayMomentum (hT.trans_le (hslab j))
        (hUstage j) (hper j) (hdiv j) (hProj j) (hsub j ht) x).mono (hsub j)
      simpa only [periodicProjectedMomentum, Pi.neg_apply, sub_eq_add_neg, add_comm] using h
    exact periodicProjectedEuler_of_stage_limits h59 hS
      (fun j => (hUstage j).mono (prod_mono_left (hsub j)))
      (fun j t ht => hper j t (hsub j ht))
      (fun t ht => contDiffOn_univ.mp ((hPrefix S hST).1 t ht))
      (hU.mono (prod_mono_left (Icc_subset_Icc_right hST.le)))
      (fun m => ((hPrefix S hST).2 m).1) hRlim hStage
  have hdt : ∀ t ∈ Ico 0 T, ∀ x,
      timeDerivative T u t x = periodicProjectedMomentum (u t) (u t) x := by
    apply timeDerivative_eq_of_prefix_dynamics
    intro S hST t ht x
    obtain ⟨s, hs, hsT⟩ := exists_between (max_lt hST hT)
    have hs₀ : 0 < s := (le_max_right S 0).trans_lt hs
    have hSs : S ≤ s := (le_max_left S 0).trans hs.le
    exact (((hDynamics s hs₀ hsT).2.1 t ⟨ht.1, ht.2.trans hSs⟩ x).mono
      (Icc_subset_Icc_right hSs))
  refine ⟨u, hu, hU, contDiffOn_halfOpen_of_closedPrefixes (fun S hS hST =>
    (hDynamics S hS hST).2.2), ?_, fun S _ hST m => ((hPrefix S hST).2 m).1⟩
  intro t ht
  obtain ⟨S, htS, hST⟩ := exists_between ht.2
  have hmem : t ∈ Icc 0 S := ⟨ht.1, htS.le⟩
  have hmemT : t ∈ Icc 0 T := Ico_subset_Icc_self ht
  have hmemStage (j : ℕ) : t ∈ Icc 0 (slab j) :=
    Icc_subset_Icc_right (hslab j) hmemT
  obtain ⟨huper, huodd⟩ := periodic_odd_of_pointwise_limit
    (fun x => hU.tendsto_at (x := (t, x)) ⟨hmemT, mem_univ _⟩)
    (fun j => hper j t (hmemStage j)) (fun j => hodd j t (hmemStage j))
  refine ⟨huper, huodd, ?_, hdt t ht⟩
  intro x
  exact divergence_eq_zero_of_tendsto_fderiv
    ((tendstoUniformlyOn_spatial_fderiv_of_first_jet ((hPrefix S hST).2 1).1).tendsto_at
      (x := (t, x)) ⟨hmem, mem_univ _⟩)
    (fun j => hdiv j t (hmemStage j) x)



/-- The inductive tower produces an actual preterminal Euler solution with
normalized pressure, together with the continuous terminal velocity and
convergence of all spatial jets on strict prefixes. -/
theorem exists_inductive_periodicEulerSolution (h59 : Statement.Text.eq_5_59)
    {T : ℝ} {slab freq activation : ℕ → ℝ} {q : ℕ → ℕ} {U O R : ℕ → Velocity}
    (hT : 0 < T) (hslab : ∀ n, T ≤ slab n) (hinit : 2 ≤ freq 0)
    (hfreq : ∀ n, freq n ^ 2 ≤ freq (n + 1)) (hq : Tendsto q atTop atTop)
    (hactivation : Tendsto activation atTop (𝓝 T))
    (hUstage : ∀ n, ContDiffOn ℝ ∞ (Function.uncurry (U n))
      (Icc 0 (slab n) ×ˢ (univ : Set Vec3)))
    (hper : ∀ n t, t ∈ Icc 0 (slab n) → SpatiallyPeriodic (U n t))
    (hodd : ∀ n t, t ∈ Icc 0 (slab n) → Function.Odd (U n t))
    (hdiv : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, divergence (U n t) x = 0)
    (hOvanish : ∀ n ≥ 2, ∀ t ∈ Icc 0 (activation n), O n t = 0)
    (hO : ∀ n t, t ∈ Icc 0 (slab (n + 1)) → ∀ x,
      ‖O (n + 1) t x‖ ≤ (freq (n + 1))⁻¹)
    (hB : ∀ n m, m ≤ q (n + 1) → ∀ t ∈ Icc 0 (slab (n + 1)), ∀ x,
      ‖iteratedFDeriv ℝ m (U (n + 1) t - U n t - O (n + 1) t) x‖ ≤ (freq (n + 1))⁻¹)
    (hProj : ∀ n t, t ∈ Icc 0 (slab n) → closedSlabLerayMomentum 0 (slab n) (U n) t = R n t)
    (hResidual : ∀ n t, t ∈ Icc 0 (slab n) → ∀ x, ‖R n t x‖ ≤ ((freq (n + 1))⁻¹)^3) :
    ∃ (u : Velocity) (p : Pressure),
      IsEulerSolution T u p ∧ (∀ t ∈ Ico 0 T, Function.Odd (u t)) ∧
      ContinuousOn (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (U n)) (Function.uncurry u)
        atTop (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ S, 0 < S → S < T → ∀ m, TendstoUniformlyOn
        (fun n (x : ℝ × Vec3) => iteratedFDeriv ℝ m (U n x.1) x.2)
        (fun x : ℝ × Vec3 => iteratedFDeriv ℝ m (u x.1) x.2)
        atTop (Icc 0 S ×ˢ (univ : Set Vec3)) ∧
        TendstoUniformlyOn (fun n t => spatialHolderHalfNorm m (U n t - u t))
          (fun _ => 0) atTop (Icc 0 S) := by
  obtain ⟨u, hucont, hU, husmooth, hkin, hjets⟩ := exists_inductive_periodicEulerProjectedLimit h59
    hT hslab hinit hfreq hq hactivation hUstage hper hodd hdiv hOvanish hO hB hProj hResidual
  obtain ⟨p, hp, _⟩ := exists_isEulerSolution_of_periodicProjectedMomentum hT husmooth
    (fun t ht => (hkin t ht).1) (fun t ht => (hkin t ht).2.2.1) (fun t ht => (hkin t ht).2.2.2)
  refine ⟨u, p, hp, fun t ht => (hkin t ht).2.1, hucont, hU, fun S hS hST m => ⟨hjets S hS hST m, ?_⟩⟩
  exact tendstoUniformlyOn_spatialHolderHalfNorm_sub_of_iteratedFDeriv m
    (fun n t ht => (stage_spatial_jets_of_joint_smoothness (hT.trans_le (hslab n)) (hUstage n)).1 t
      (Icc_subset_Icc_right (hST.le.trans (hslab n)) ht))
    (fun t ht => hp.contDiff_velocity_slice ⟨ht.1, ht.2.trans_lt hST⟩)
    (fun k _ => hjets S hS hST k)

end

end TorusEuler.Paper.Lib.S678b

import TorusEuler.Paper.S678.Statements
import TorusEuler.PaperSequenceStatements
import TorusEuler.Paper.Proofs.S678b.Library.Comparison
import TorusEuler.InductiveParentGeometry
import TorusEuler.LaterPhysicalAmplification
import TorusEuler.Paper.Proofs.S5Bridge.Parent

/-! # The parent of a stage (package S678a)

Copies of `InductiveEulerStage.exists_onSlab_threshold` (InductiveParentGeometry.lean:107) and of
`exists_parent_projectedMomentum_bounds` (LaterPhysicalAmplification.lean:545) in which the
Bernstein and derived-low-bound inputs (content of 5.1) come from `hB_1`
(`Lib.S678b.bernstein_jets`, `Lib.S678b.parent_derived_low_bounds`). -/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S678a

/-- Copy of `exists_parent_projectedMomentum_bounds`; `ContDiff ∞` of the residual slices is a
hypothesis (it holds for a stage) and the Bernstein step is `hB_1`. -/
theorem projectedMomentum_bounds_of_hB1 (hB_1 : Statement.lemma_B_1) :
    ∃ (N K : ℝ), 1 ≤ N ∧ 0 ≤ K ∧
      ∀ {T old μ : ℝ}, 0 < T → N ≤ old → 1 ≤ μ →
        ∀ (U : ℝ → C(UnitAddTorus (Fin 3), Vec3)) (R : Velocity),
          (∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (R t)) →
          let u : Velocity := fun t x => U t (toUnitTorus x)
          ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 T ×ˢ (univ : Set Vec3)) →
          (∀ t ∈ Icc 0 T, ‖U t‖ ≤ old ∧ RealTorusFourierBand (2 * old ^ 5) (U t)) →
          (∀ t ∈ Icc 0 T, ∀ x, divergence (u t) x = 0) →
          (∀ t ∈ Icc 0 T, closedSlabLerayMomentum 0 T u t = R t) →
          (∀ t ∈ Icc 0 T, ∀ x, ‖R t x‖ ≤ (μ⁻¹) ^ (3 : ℕ)) →
          ∃ (A : ℝ → HalfHolder (UnitAddTorus (Fin 3)) Vec3)
            (Rtor : ℝ → C(UnitAddTorus (Fin 3), Vec3)),
            (∀ t ∈ Icc 0 T, ∀ x,
              HalfHolder.eval (toUnitTorus x) (A t) = fderiv ℝ (u t) x (u t x)) ∧
            (∀ t ∈ Icc 0 T, ∀ x, Rtor t (toUnitTorus x) = R t x) ∧
            (∀ t ∈ Icc 0 T, ‖Rtor t‖ ≤ μ ^ (-3 : ℝ)) ∧
            (∀ t ∈ Icc 0 T, ∀ x,
              HasDerivWithinAt (fun s => u s x)
                (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
                  Rtor t (toUnitTorus x)) (Icc 0 T) t) ∧
            (∀ t ∈ Icc 0 T, RealTorusFourierBand (4 * old ^ 5) (Rtor t) ∧
              ContDiff ℝ ∞ (R t)) ∧
            (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (u t) x‖ ≤ old ^ 9 ∧
              ‖derivWithin (fun s => fderiv ℝ (u s) x) (Icc 0 T) t‖ ≤ old ^ 18 ∧
              ‖fderiv ℝ (R t) x‖ ≤ K * old ^ 5 * μ ^ (-3 : ℝ)) := by
  classical
  obtain ⟨N, hN, hLow⟩ := Lib.S678b.parent_derived_low_bounds hB_1
  obtain ⟨K₁, K₂, hK₁, -, hBernstein⟩ := Lib.S678b.bernstein_jets hB_1
  refine ⟨N, K₁, hN, hK₁, ?_⟩
  intro T old μ hT hOld hμ₁ U R hRs u hSmooth hU hDiv hMom hR
  let I := Icc (0 : ℝ) T
  let Labels := UnitAddTorus (Fin 3)
  let W : Velocity := fun t x => derivWithin (fun s => u s x) I t
  have hPer (t : ℝ) (_ht : t ∈ I) : SpatiallyPeriodic (u t) := fun n x =>
    congrArg (U t) ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
  have hSlice {f : Velocity} (h : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ (univ : Set Vec3)))
      (t : ℝ) (ht : t ∈ I) : ContDiff ℝ ∞ (f t) := by
    let e : Vec3 → ℝ × Vec3 := fun x => (t, x)
    exact h.comp_contDiff (f := e) (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨ht, mem_univ x⟩)
  have hWt : ContDiffOn ℝ ∞ (Function.uncurry W) (I ×ˢ (univ : Set Vec3)) :=
    contDiffOn_sliceTimeDerivWithin_Icc hT hSmooth
  let adv : Velocity := fun t x => fderiv ℝ (u t) x (u t x)
  have hExistsA (t : ℝ) : ∃ a : HalfHolder Labels Vec3,
      t ∈ I → ∀ x, HalfHolder.eval (toUnitTorus x) a = adv t x := by
    by_cases ht : t ∈ I
    · have hUs := hSlice hSmooth t ht
      have hA : ContDiff ℝ ∞ (adv t) := (hUs.fderiv_right (m := ∞) (by simp)).clm_apply hUs
      have hAPer : SpatiallyPeriodic (adv t) := by
        intro n x
        change fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
          fderiv ℝ (u t) x (u t x)
        rw [(hPer t ht).fderiv (hUs.differentiable (by simp)) n x, hPer t ht n x]
      obtain ⟨a, ha, _⟩ := exists_halfHolder_of_spatialHolderHalf_zero hAPer
        (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic (hA.of_le (by simp)) hAPer)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose A hA using hExistsA
  let S : Velocity := fun t x =>
    HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t))
  have hEq (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x) (R t x - S t x) I t := by
    have hU_s := hSlice hSmooth t ht
    have hX := hasDerivWithinAt_of_closedSlabLerayMomentum hT hSmooth hPer hDiv hMom ht x
    have hAdv : momentumTensorDivergence ∘ fderiv ℝ (fun y => momentumTensor (u t y) (u t y)) =
        adv t := momentumTensorDivergence_self_eq_advection (hU_s.differentiable (by simp)) (hDiv t ht)
    have hTor : periodicLerayHolderLift (adv t) = S t := by
      rw [← funext (hA t ht), periodicLerayHolderLift_pullback]
    rwa [hAdv, hTor] at hX
  have hExistsR (t : ℝ) : ∃ z : C(Labels, Vec3), t ∈ I →
      (∀ x, z (toUnitTorus x) = R t x) ∧ ‖z‖ ≤ μ ^ (-3 : ℝ) := by
    by_cases ht : t ∈ I
    · have hWc : Continuous (W t) := (hSlice hWt t ht).continuous
      have hWper : SpatiallyPeriodic (W t) := fun n x =>
        derivWithin_congr (fun s hs => hPer s hs n x) (hPer t ht n x)
      have hSc : Continuous (S t) :=
        (endpointStrongSpatialLeray (A t)).val.1.continuous.comp
          isOpenQuotientMap_toUnitTorus.continuous
      have hSper : SpatiallyPeriodic (S t) := fun n x =>
        congrArg (fun y => HalfHolder.eval y (endpointStrongSpatialLeray (A t)))
          ((toUnitTorus_eq_iff _ _).2 ⟨n, rfl⟩)
      have hRep : R t = W t + S t := by
        funext x
        exact (sub_eq_iff_eq_add.mp ((hEq t ht x).derivWithin
          (uniqueDiffOn_Icc hT t ht)).symm)
      have hSumPer : SpatiallyPeriodic (W t + S t) := by
        intro n x
        change W t (x + latticeVector n) + S t (x + latticeVector n) = W t x + S t x
        rw [hWper n x, hSper n x]
      obtain ⟨z, hz⟩ := hSumPer.exists_continuousTorusFunction (hWc.add hSc)
      have hzR : ∀ x, z (toUnitTorus x) = R t x := fun x =>
        (hz x).trans (congrFun hRep x).symm
      have hPow : (μ⁻¹) ^ (3 : ℕ) = μ ^ (-3 : ℝ) := by
        rw [inv_pow, Real.rpow_neg (zero_le_one.trans hμ₁), Real.rpow_ofNat]
      have hzBound : ‖z‖ ≤ μ ^ (-3 : ℝ) := by
        apply (ContinuousMap.norm_le z (Real.rpow_nonneg (zero_le_one.trans hμ₁) _)).2
        intro a
        obtain ⟨x, rfl⟩ := isOpenQuotientMap_toUnitTorus.surjective a
        rw [hzR, ← hPow]
        exact hR t ht x
      exact ⟨z, fun _ => ⟨hzR, hzBound⟩⟩
    · exact ⟨0, fun h => (ht h).elim⟩
  choose Rtor hRtor using hExistsR
  have hMomentum (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HasDerivWithinAt (fun s => u s x)
        (-HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray (A t)) +
          Rtor t (toUnitTorus x)) I t := by
    rw [(hRtor t ht).1 x]
    exact (hEq t ht x).congr_deriv (sub_eq_neg_add _ _)
  have hD : 0 < old ^ 5 := pow_pos (zero_lt_one.trans_le (hN.trans hOld)) _
  have hRband (t : ℝ) (ht : t ∈ I) : RealTorusFourierBand (4 * old ^ 5) (Rtor t) :=
    parentResidualFourierBand_of_projectedMomentum hT hD.le ht U (Rtor t) (A t)
      hSmooth (fun s hs => (hU s hs).2) (hA t ht) (hMomentum t ht)
  have hRjet (t : ℝ) (ht : t ∈ I) :
      ContDiff ℝ ∞ (R t) ∧
        ∀ x, ‖fderiv ℝ (R t) x‖ ≤ K₁ * old ^ 5 * μ ^ (-3 : ℝ) := by
    have hRep : (fun x => Rtor t (toUnitTorus x)) = R t := funext (hRtor t ht).1
    have hRsm : ContDiff ℝ 2 (fun x => Rtor t (toUnitTorus x)) := by
      rw [hRep]; exact (hRs t ht).of_le (by simp)
    have hJet := hBernstein (Rtor t) hD (hRtor t ht).2 (hRband t ht) hRsm
    rw [hRep] at hJet
    exact ⟨hRs t ht, fun x => by simpa only [mul_right_comm] using (hJet x).1⟩
  refine ⟨A, Rtor, hA, fun t ht => (hRtor t ht).1, fun t ht => (hRtor t ht).2, hMomentum,
    fun t ht => ⟨hRband t ht, (hRjet t ht).1⟩, ?_⟩
  intro t ht x
  obtain ⟨hGrad, hTimeGrad⟩ := hLow hT hOld hμ₁ U Rtor A hSmooth hU
    (fun s hs => (hRtor s hs).2) hA hMomentum t ht x
  exact ⟨hGrad, hTimeGrad, (hRjet t ht).2 x⟩

end TorusEuler.Paper.Lib.S678a

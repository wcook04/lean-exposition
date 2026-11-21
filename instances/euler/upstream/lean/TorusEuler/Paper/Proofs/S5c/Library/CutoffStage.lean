import TorusEuler.PaperPhysicalCutoff

/-!
# Library copies for Proposition 5.11: the truncated child stage from Lemma B.1

The library construction of the truncation of §5.7 (`nonempty_truncatedChildStage`,
`TruncatedChildStage.lean:435`) obtains the properties of the real Fourier cutoff
`S_Λ = realVectorFourierCutoff ψ Λ` from library lemmas that are listed as content of
Lemma B.1 (`odd_lift_realVectorFourierCutoff`, `divergence_free_lift_realVectorFourierCutoff`,
`mFourierCoeff_realVectorFourierCutoff_of_even`, `hasDerivWithinAt_realVectorFourierCutoff_time`,
`fderiv_lift_realVectorFourierCutoff_single`). In the proof of Proposition 5.11 these
properties are cited from Lemma B.1 (`sections/08_exact_wave.tex:403-421`: "By
Lemma B.1, `u` and `v_Λ` are odd and divergence free and `u` is supported on frequencies
at most `2Λ`"; "Applying `S_Λ` and then `ℙ` to (5.46)" uses the commutation of `S_Λ` with
the time and space derivatives). The copies below take each of these properties of the
cutoff, at one frequency `Λ`, as a hypothesis whose statement is the corresponding clause of
`Paper.Statement.lemma_B_1` (the predicates `CutParity`, `CutDivergence`, `CutBand`,
`CutSpaceDeriv`, `CutTimeDeriv`), and are otherwise the library proofs.

| original | copy | change |
|---|---|---|
| `toUnitTorus_neg_cutoff` (private, `TruncatedParentAdmissibility.lean:72`) | `toUnitTorus_neg` | none |
| `spatiallyPeriodic_pullback` (private, `TruncationFourierCommutation.lean:15`) | `spatiallyPeriodic_pullback` | none |
| `fderiv_left_comp_CLM` (private, `:42`) | `fderiv_left_comp_CLM` | none |
| `fderiv_tensorColumn` (private, `:178`) | `fderiv_tensorColumn` | none |
| `exists_torusVectorCoordinateDerivative` (private, `:194`) | `exists_torusVectorCoordinateDerivative` | none |
| `realVectorFourierCutoff_tensorDivergence` (`:204`) | `realVectorFourierCutoff_tensorDivergence` | hypothesis `CutSpaceDeriv ψ Λ` replaces `fderiv_lift_realVectorFourierCutoff_single` |
| `momentum_realFourierCutoff_eq_residual_input` (`:292`) | `momentum_realFourierCutoff_eq_residual_input` | hypothesis `CutSpaceDeriv ψ Λ` |
| `projectedMomentum_realFourierCutoff_eq_residual` (`:346`) | `projectedMomentum_realFourierCutoff_eq_residual` | hypothesis `CutSpaceDeriv ψ Λ` |
| `contDiff_slice_of_contDiffOn_Icc`, `periodic_sliceTimeDerivWithin_Icc`, `exists_closedSlab_torusSlices` (private, `TruncatedParentProjectedMomentum.lean:37,44,276`) | same names | none |
| `closedSlabLerayMomentum_realFourierCutoff` (`:292`) | `closedSlabLerayMomentum_realFourierCutoff` | hypotheses `CutTimeDeriv`, `CutSpaceDeriv`, `CutDivergence` replace the B.1 lemmas; `Function.Even ψ` dropped |
| `exists_realFourierCutoffPoissonPressure` (`TruncatedParentPoissonPressure.lean:338`) | `exists_realFourierCutoffPoissonPressure` | hypotheses `CutBand`, `CutDivergence`, `CutTimeDeriv`, `CutSpaceDeriv`; `Function.Even ψ` dropped |
| `nonempty_truncatedChildStage` (`TruncatedChildStage.lean:435`) | `nonempty_truncatedChildStage` | hypotheses `CutParity`, `CutDivergence`, `CutBand`, `CutTimeDeriv`, `CutSpaceDeriv`; the slice cutoff of `exists_truncatedParent_T1` (`TruncatedParentAdmissibility.lean:426`) is inlined with oddness, divergence and band from the hypotheses |
-/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-! ## The properties of the real cutoff of Lemma B.1 at one frequency -/

/-- Lemma B.1, real block, parity clause at the frequency `Λ`: `S_Λ` preserves
`g(-z) = c g(z)`. -/
def CutParity (ψ : Vec3 → ℝ) (Λ : ℝ) : Prop :=
  ∀ (g : C(Labels, Vec3)) (c : ℝ), (∀ z, g (-z) = c • g z) →
    ∀ z, realVectorFourierCutoff ψ Λ g (-z) = c • realVectorFourierCutoff ψ Λ g z

/-- Lemma B.1, real block, divergence clause at the frequency `Λ`. -/
def CutDivergence (ψ : Vec3 → ℝ) (Λ : ℝ) : Prop :=
  ∀ g : C(Labels, Vec3), ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) →
    (∀ x, divergence (fun y => g (toUnitTorus y)) x = 0) →
    ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x = 0

/-- Lemma B.1, real block, band clause at the frequency `Λ`: `S_Λ g` has frequencies at
most `2Λ`. -/
def CutBand (ψ : Vec3 → ℝ) (Λ : ℝ) : Prop :=
  ∀ (g : C(Labels, Vec3)) (k : Fin 3 → ℤ), 2 * Λ < ‖latticeVector k‖ →
    mFourierCoeff (fun z => periodicComplexifyVector (realVectorFourierCutoff ψ Λ g z)) k = 0

/-- Lemma B.1, real block, commutation with the first-order coordinate derivatives. -/
def CutSpaceDeriv (ψ : Vec3 → ℝ) (Λ : ℝ) : Prop :=
  ∀ (g d : C(Labels, Vec3)) (i : Fin 3), ContDiff ℝ 1 (fun x => g (toUnitTorus x)) →
    (∀ x, d (toUnitTorus x) =
      fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) →
    ∀ x, fderiv ℝ (fun y => realVectorFourierCutoff ψ Λ g (toUnitTorus y)) x
      (EuclideanSpace.single i 1) = realVectorFourierCutoff ψ Λ d (toUnitTorus x)

/-- Lemma B.1, real block, commutation with the time derivative on a closed slab. -/
def CutTimeDeriv (ψ : Vec3 → ℝ) (Λ : ℝ) : Prop :=
  ∀ (a b : ℝ), a < b → ∀ V : Velocity,
    ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)) →
    ∀ g gt : ℝ → C(Labels, Vec3),
    (∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x) →
    (∀ t ∈ Icc a b, ∀ x, gt t (toUnitTorus x) = derivWithin (fun r => V r x) (Icc a b) t) →
    ∀ t ∈ Icc a b, ∀ x,
      HasDerivWithinAt (fun r => realVectorFourierCutoff ψ Λ (g r) (toUnitTorus x))
        (realVectorFourierCutoff ψ Λ (gt t) (toUnitTorus x)) (Icc a b) t

/-! ## Copied glue -/

/-- Copy of the private `toUnitTorus_neg_cutoff`. -/
theorem toUnitTorus_neg (x : Vec3) : toUnitTorus (-x) = -toUnitTorus x := by
  funext i
  change ((-(x i) : ℝ) : UnitAddCircle) = -(x i : UnitAddCircle)
  exact AddCircle.coe_neg (p := (1 : ℝ)) (x := x i)

/-- The parity clause of Lemma B.1 makes the cutoff of an odd lifted field odd (this
replaces `odd_lift_realVectorFourierCutoff`). -/
theorem odd_lift_of_cutParity {ψ : Vec3 → ℝ} {Λ : ℝ} (hpar : CutParity ψ Λ)
    (g : C(Labels, Vec3)) (hg : Function.Odd (fun x => g (toUnitTorus x))) :
    Function.Odd (fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  have hOdd (z : Labels) : g (-z) = (-1 : ℝ) • g z := by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    rw [← toUnitTorus_neg, neg_one_smul]
    exact hg x
  intro x
  change realVectorFourierCutoff ψ Λ g (toUnitTorus (-x)) =
    -realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  rw [toUnitTorus_neg, hpar g (-1) hOdd, neg_one_smul]

/-- Copy of the private `spatiallyPeriodic_pullback`. -/
theorem spatiallyPeriodic_pullback {E : Type*} (g : Labels → E) :
    SpatiallyPeriodic (fun x => g (toUnitTorus x)) :=
  fun n _ => congrArg g ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

/-- Copy of the private `fderiv_left_comp_CLM`. -/
theorem fderiv_left_comp_CLM {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {f : Vec3 → E}
    {x : Vec3} (hf : DifferentiableAt ℝ f x) :
    fderiv ℝ (fun y => L (f y)) x = L.comp (fderiv ℝ f x) :=
  (L.hasFDerivAt.comp x hf.hasFDerivAt).fderiv

/-- Copy of the private `fderiv_tensorColumn`. -/
theorem fderiv_tensorColumn {f : Vec3 → MomentumTensor} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    fderiv ℝ (fun y => f y i) x (EuclideanSpace.single i 1) =
      fderiv ℝ f x (EuclideanSpace.single i 1) i :=
  congrArg (fun D : Vec3 →L[ℝ] Vec3 => D (EuclideanSpace.single i 1))
    (fderiv_left_comp_CLM (ContinuousLinearMap.proj i) hf)

/-- Copy of the private `exists_torusVectorCoordinateDerivative`. -/
theorem exists_torusVectorCoordinateDerivative (g : C(Labels, Vec3))
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x))) (i : Fin 3) :
    ∃ d : C(Labels, Vec3), ∀ x,
      d (toUnitTorus x) = fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1) := by
  have hper := (spatiallyPeriodic_pullback g).fderiv (hg.differentiable (by simp))
  have hD : SpatiallyPeriodic
      (fun x => fderiv ℝ (fun y => g (toUnitTorus y)) x (EuclideanSpace.single i 1)) :=
    fun n x => congrArg (fun A : Vec3 →L[ℝ] Vec3 => A (EuclideanSpace.single i 1)) (hper n x)
  exact hD.exists_continuousTorusFunction ((hg.continuous_fderiv (by simp)).clm_apply continuous_const)

/-- Copy of `realVectorFourierCutoff_tensorDivergence`: the cutoff commutes with the
tensor divergence of (5.58). The commutation of the real cutoff with the coordinate
derivatives is the hypothesis `hspace` (Lemma B.1). -/
theorem realVectorFourierCutoff_tensorDivergence
    {ψ : Vec3 → ℝ} {Λ : ℝ} (hspace : CutSpaceDeriv ψ Λ)
    (g : C(Labels, MomentumTensor)) (d : C(Labels, Vec3))
    (hg : ContDiff ℝ 1 (fun x => g (toUnitTorus x)))
    (hd : ∀ x, d (toUnitTorus x) =
      momentumTensorDivergence (fderiv ℝ (fun y => g (toUnitTorus y)) x)) :
    (fun x => realVectorFourierCutoff ψ Λ d (toUnitTorus x)) =
      momentumTensorDivergence ∘
        fderiv ℝ (fun x => momentumTensorFourierCutoff ψ Λ g (toUnitTorus x)) := by
  let T := fun x => momentumTensorFourierCutoff ψ Λ g (toUnitTorus x)
  have hT : ContDiff ℝ ∞ T := contDiff_lift_momentumTensorFourierCutoff ψ Λ g
  have hf (i : Fin 3) : ContDiff ℝ 1 (fun x => momentumTensorColumn g i (toUnitTorus x)) := by
    let L : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj i
    exact L.contDiff.comp hg
  choose dc hdc using fun i =>
    exists_torusVectorCoordinateDerivative (momentumTensorColumn g i) (hf i) i
  have hsum : d = ∑ j : Fin 3, dc j := by
    ext a : 1
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hd, momentumTensorDivergence_apply]
    simp only [ContinuousMap.sum_apply, hdc]
    exact Finset.sum_congr rfl fun j _ =>
      (fderiv_tensorColumn (hg.differentiable (by simp) x) j).symm
  funext x
  change realVectorFourierCutoff ψ Λ d (toUnitTorus x) = momentumTensorDivergence (fderiv ℝ T x)
  rw [hsum, realVectorFourierCutoff_sum, momentumTensorDivergence_apply]
  apply Finset.sum_congr rfl
  intro j _
  have hpoint : (fun y => T y j) =
      fun y => realVectorFourierCutoff ψ Λ (momentumTensorColumn g j) (toUnitTorus y) :=
    funext fun y => momentumTensorFourierCutoff_apply ψ Λ g (toUnitTorus y) j
  rw [← fderiv_tensorColumn (hT.differentiable (by simp) x) j, hpoint]
  exact (hspace (momentumTensorColumn g j) (dc j) j (hf j) (hdc j) x).symm

/-- Copy of `momentum_realFourierCutoff_eq_residual_input` (the unprojected momentum
identity behind (5.58)), with the commutation hypothesis `hspace` of Lemma B.1. -/
theorem momentum_realFourierCutoff_eq_residual_input
    {ψ : Vec3 → ℝ} {Λ : ℝ} (hspace : CutSpaceDeriv ψ Λ)
    (gV gVt gD gPG gRV : C(Labels, Vec3)) (u_t : Vec3 → Vec3)
    (hV : ContDiff ℝ 1 (fun x => gV (toUnitTorus x)))
    (ht : u_t = fun x => realVectorFourierCutoff ψ Λ gVt (toUnitTorus x))
    (hVeq : gVt + gD + gPG = gRV)
    (hD : ∀ x, gD (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV (toUnitTorus y)) (gV (toUnitTorus y))) x))
    (hu : ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ gV (toUnitTorus y)) x = 0) :
    let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
    u_t + (fun x => fderiv ℝ u x (u x)) +
        (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)) =
      truncatedEulerProjectedResidual id ψ Λ gV gRV := by
  let V := fun x => gV (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
  let v := u - V
  let gVV : C(Labels, MomentumTensor) := ⟨fun z => momentumTensor (gV z) (gV z),
    (momentumTensor.continuous.comp gV.continuous).clm_apply gV.continuous⟩
  let VV := fun x => gVV (toUnitTorus x)
  let cutVV := fun x => momentumTensorFourierCutoff ψ Λ gVV (toUnitTorus x)
  let uu := fun x => momentumTensor (u x) (u x)
  let E := (fun x => momentumTensor (v x) (u x)) + (fun x => momentumTensor (V x) (v x)) +
    (VV - cutVV)
  let cutD := fun x => realVectorFourierCutoff ψ Λ gD (toUnitTorus x)
  let cutPG := fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)
  let cutRV := fun x => realVectorFourierCutoff ψ Λ gRV (toUnitTorus x)
  let divT := fun g : Vec3 → MomentumTensor => momentumTensorDivergence ∘ fderiv ℝ g
  let adv := fun x => fderiv ℝ u x (u x)
  have hVV : ContDiff ℝ 1 VV := (momentumTensor.contDiff.comp hV).clm_apply hV
  have hcD : cutD = divT cutVV := realVectorFourierCutoff_tensorDivergence hspace gVV gD hVV hD
  have hcRV : cutRV = u_t + cutD + cutPG := by
    funext x
    change realVectorFourierCutoff ψ Λ gRV (toUnitTorus x) = (u_t + cutD + cutPG) x
    rw [← hVeq, realVectorFourierCutoff_add, realVectorFourierCutoff_add, ht]
    rfl
  have hu' : ContDiff ℝ ∞ u := contDiff_lift_realVectorFourierCutoff ψ Λ gV
  have hcutVV : ContDiff ℝ ∞ cutVV := contDiff_lift_momentumTensorFourierCutoff ψ Λ gVV
  have huu : ContDiff ℝ ∞ uu := (momentumTensor.contDiff.comp hu').clm_apply hu'
  have hE : E = uu - cutVV := by
    funext x
    change momentumTensor (u x - V x) (u x) + momentumTensor (V x) (u x - V x) +
      (momentumTensor (V x) (V x) - cutVV x) = momentumTensor (u x) (u x) - cutVV x
    simp only [map_sub, _root_.sub_apply]
    abel
  have hdivE : divT E = divT uu - divT cutVV := by
    funext x
    change momentumTensorDivergence (fderiv ℝ E x) =
       momentumTensorDivergence (fderiv ℝ uu x) - momentumTensorDivergence (fderiv ℝ cutVV x)
    rw [hE, fderiv_sub (huu.differentiable (by simp) x) (hcutVV.differentiable (by simp) x),
      map_sub]
  have hA : divT uu = adv :=
    momentumTensorDivergence_self_eq_advection (hu'.differentiable (by simp)) hu
  change u_t + adv + cutPG = cutRV + divT E
  rw [← hA, hdivE, hcRV, hcD]
  abel

/-- Copy of `projectedMomentum_realFourierCutoff_eq_residual` with the commutation
hypothesis `hspace` of Lemma B.1. -/
theorem projectedMomentum_realFourierCutoff_eq_residual
    {ψ : Vec3 → ℝ} {Λ : ℝ} (hspace : CutSpaceDeriv ψ Λ)
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3))
    (gV gVt gD gPG gRV : C(Labels, Vec3)) (u_t : Vec3 → Vec3)
    (hV : ContDiff ℝ 1 (fun x => gV (toUnitTorus x)))
    (ht : u_t = fun x => realVectorFourierCutoff ψ Λ gVt (toUnitTorus x))
    (hVeq : gVt + gD + gPG = gRV)
    (hD : ∀ x, gD (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV (toUnitTorus y)) (gV (toUnitTorus y))) x))
    (hu : ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ gV (toUnitTorus y)) x = 0) :
    let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
    let mom := u_t + fun x => fderiv ℝ u x (u x)
    proj (mom + (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x))) = proj mom →
    proj mom = truncatedEulerProjectedResidual proj ψ Λ gV gRV := by
  intro u mom hP
  rw [← hP, show mom + (fun x => realVectorFourierCutoff ψ Λ gPG (toUnitTorus x)) =
    truncatedEulerProjectedResidual id ψ Λ gV gRV from
    momentum_realFourierCutoff_eq_residual_input hspace gV gVt gD gPG gRV u_t hV ht hVeq hD hu]
  rfl

/-- Copy of the private `contDiff_slice_of_contDiffOn_Icc`. -/
theorem contDiff_slice_of_contDiffOn_Icc {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) {t : ℝ}
    (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (f t) := by
  have hp : ContDiff ℝ ∞ (fun x : Vec3 => (t, x)) := contDiff_const.prodMk contDiff_id
  exact contDiffOn_univ.1 (hf.comp hp.contDiffOn fun x _ => ⟨ht, mem_univ x⟩)

/-- Copy of the private `periodic_sliceTimeDerivWithin_Icc`. -/
theorem periodic_sliceTimeDerivWithin_Icc {a b : ℝ} {f : Velocity}
    (hf : ∀ t ∈ Icc a b, SpatiallyPeriodic (f t)) {t : ℝ} (ht : t ∈ Icc a b) :
    SpatiallyPeriodic (fun x => derivWithin (fun r => f r x) (Icc a b) t) := by
  intro n x
  exact derivWithin_congr (fun r hr => hf r hr n x) (hf t ht n x)

/-- Copy of the private `exists_closedSlab_torusSlices`. -/
theorem exists_closedSlab_torusSlices {a b : ℝ} {V : Velocity}
    (hc : ∀ t ∈ Icc a b, Continuous (V t)) (hp : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t)) :
    ∃ g : ℝ → C(Labels, Vec3), ∀ t ∈ Icc a b, ∀ x, g t (toUnitTorus x) = V t x := by
  classical
  have h (t : ℝ) (ht : t ∈ Icc a b) := (hp t ht).exists_continuousTorusFunction (hc t ht)
  refine ⟨fun t => if ht : t ∈ Icc a b then (h t ht).choose else 0, ?_⟩
  intro t ht x
  simp only [dite_eq_left ht]
  exact (h t ht).choose_spec x

/-- Copy of `closedSlabLerayMomentum_realFourierCutoff`: applying the real cutoff and the
periodic Leray projection to the approximate momentum equation gives (5.58). The
commutation of `S_Λ` with the time and space derivatives and the preservation of
divergence freeness are the hypotheses `htime`, `hspace`, `hdivc` (Lemma B.1). -/
theorem closedSlabLerayMomentum_realFourierCutoff
    {ψ : Vec3 → ℝ} {Λ : ℝ} (htime : CutTimeDeriv ψ Λ) (hspace : CutSpaceDeriv ψ Λ)
    (hdivc : CutDivergence ψ Λ)
    {a b : ℝ} (hab : a < b) {V RV : Velocity} (pressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc a b ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc a b, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc a b, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc a b, ∀ x, derivWithin (fun r => V r x) (Icc a b) t +
      fderiv ℝ (V t) x (V t x) + gradient (pressure t).lift x = RV t x)
    (gV gRV : ℝ → C(Labels, Vec3))
    (hgV : ∀ t ∈ Icc a b, ∀ x, gV t (toUnitTorus x) = V t x)
    (hgRV : ∀ t ∈ Icc a b, ∀ x, gRV t (toUnitTorus x) = RV t x) :
    let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)
    ∀ t ∈ Icc a b, closedSlabLerayMomentum a b u t =
      truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t) := by
  intro u
  let Vt : Velocity := fun t x => derivWithin (fun r => V r x) (Icc a b) t
  let A : Velocity := fun t x => fderiv ℝ (V t) x (V t x)
  have hVs (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (V t) :=
    contDiff_slice_of_contDiffOn_Icc hV ht
  have hVts (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ ∞ (Vt t) :=
    contDiff_slice_of_contDiffOn_Icc (f := Vt) (contDiffOn_sliceTimeDerivWithin_Icc hab hV) ht
  obtain ⟨gVt, hgVt⟩ := exists_closedSlab_torusSlices (fun t ht => (hVts t ht).continuous)
    (fun _ ht => periodic_sliceTimeDerivWithin_Icc hVper ht)
  have hAc (t : ℝ) (ht : t ∈ Icc a b) : Continuous (A t) :=
    ((hVs t ht).continuous_fderiv (by simp)).clm_apply (hVs t ht).continuous
  have hAper (t : ℝ) (ht : t ∈ Icc a b) : SpatiallyPeriodic (A t) := by
    intro n x
    change fderiv ℝ (V t) (x + latticeVector n) (V t (x + latticeVector n)) =
      fderiv ℝ (V t) x (V t x)
    rw [(hVper t ht).fderiv ((hVs t ht).differentiable (by simp)) n x, hVper t ht n x]
  obtain ⟨gA, hgA⟩ := exists_closedSlab_torusSlices hAc hAper
  intro t ht
  let ut := fun x => derivWithin (fun r => u r x) (Icc a b) t
  let mom := ut + fun x => fderiv ℝ (u t) x (u t x)
  have hut : ut = fun x => realVectorFourierCutoff ψ Λ (gVt t) (toUnitTorus x) := by
    funext x
    exact (htime a b hab V hV gV gVt hgV hgVt t ht x).derivWithin (uniqueDiffOn_Icc hab t ht)
  have hEq : gVt t + gA t + endpointPotentialGradient (pressure t) = gRV t := by
    ext z : 1
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
    simp only [ContinuousMap.add_apply, hgVt t ht, hgA t ht, endpointPotentialGradient_toUnitTorus,
      hgRV t ht]
    exact hMom t ht x
  have hVG : (fun x => gV t (toUnitTorus x)) = V t := funext (hgV t ht)
  have hV₁ : ContDiff ℝ 1 (fun x => gV t (toUnitTorus x)) := by
    rw [hVG]
    exact (hVs t ht).of_le (by simp)
  have hD (x : Vec3) : gA t (toUnitTorus x) = momentumTensorDivergence
      (fderiv ℝ (fun y => momentumTensor (gV t (toUnitTorus y)) (gV t (toUnitTorus y))) x) := by
    rw [hgA t ht]
    have hA := congrFun (momentumTensorDivergence_self_eq_advection
      ((hVs t ht).differentiable (by simp)) (hVdiv t ht)) x
    change A t x = _
    simpa only [hgV t ht, Function.comp_apply, A] using hA.symm
  have huDiv : ∀ x, divergence (u t) x = 0 := by
    apply hdivc (gV t)
    · rw [hVG]; exact hVs t ht
    · rw [hVG]; exact hVdiv t ht
  have hu : ContDiff ℝ ∞ (u t) := contDiff_lift_realVectorFourierCutoff ψ Λ (gV t)
  have huper : SpatiallyPeriodic (u t) := spatiallyPeriodic_lift_realVectorFourierCutoff ψ Λ (gV t)
  have hm : ContDiff ℝ 1 mom := by
    have htime' : ContDiff ℝ ∞ ut := by
      rw [hut]
      exact contDiff_lift_realVectorFourierCutoff ψ Λ (gVt t)
    exact (htime'.of_le (by simp : (1 : ℕ∞ω) ≤ ∞)).add
      ((hu.fderiv_right (m := 1) (by simp)).clm_apply (hu.of_le (by simp)))
  have hmper : SpatiallyPeriodic mom := by
    have htper : SpatiallyPeriodic ut := by
      rw [hut]
      exact spatiallyPeriodic_lift_realVectorFourierCutoff ψ Λ (gVt t)
    intro n x
    change ut (x + latticeVector n) +
        fderiv ℝ (u t) (x + latticeVector n) (u t (x + latticeVector n)) =
      ut x + fderiv ℝ (u t) x (u t x)
    rw [htper n x, huper.fderiv (hu.differentiable (by simp)) n x, huper n x]
  change periodicLerayHolderLift mom = _
  exact projectedMomentum_realFourierCutoff_eq_residual hspace periodicLerayHolderLift
    (gV t) (gVt t) (gA t) (endpointPotentialGradient (pressure t)) (gRV t) ut hV₁ hut hEq hD huDiv
    (periodicLerayHolderLift_add_cutoff_pressure_gradient ψ Λ (pressure t) mom hmper
      (spatialHolderHalf_zero_of_contDiff_spatiallyPeriodic hm hmper))

/-- Copy of `exists_realFourierCutoffPoissonPressure`: the zero-mean Poisson pressure of
the cutoff velocity, whose residual is (5.58). The band and divergence properties of the
cutoff are the hypotheses `hband`, `hdivc` (Lemma B.1). -/
theorem exists_realFourierCutoffPoissonPressure
    {ψ : Vec3 → ℝ} {Λ : ℝ} (hband : CutBand ψ Λ) (hdivc : CutDivergence ψ Λ)
    (htime : CutTimeDeriv ψ Λ) (hspace : CutSpaceDeriv ψ Λ)
    {T : ℝ} (hT : 0 < T)
    {V RV : Velocity} (pressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
      fderiv ℝ (V t) x (V t x) + gradient (pressure t).lift x = RV t x)
    (gV gRV : ℝ → C(Labels, Vec3))
    (hgV : ∀ t ∈ Icc 0 T, ∀ x, gV t (toUnitTorus x) = V t x)
    (hgRV : ∀ t ∈ Icc 0 T, ∀ x, gRV t (toUnitTorus x) = RV t x) :
    let u : Velocity := fun t x => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus x)
    ∃ p : Pressure, ContDiffOn ℝ ∞ (Function.uncurry p) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (p t) ∧ (∫ x in centeredCell, p t x) = 0 ∧
        (∀ x, divergence (gradient (p t)) x =
          -LinearMap.trace ℝ Vec3 ((fderiv ℝ (u t) x).comp (fderiv ℝ (u t) x)).toLinearMap) ∧
        momentumResidual (Icc 0 T) u p t =
          truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ (gV t) (gRV t) := by
  intro u
  let U (t : ℝ) : C(Labels, Vec3) := by
    refine ⟨realVectorFourierCutoff ψ Λ (gV t), periodicRealPartVector.continuous.comp ?_⟩
    unfold smoothFourierCutoff finiteFourierSum
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  have hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => U z.1 (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_lift_realVectorFourierCutoff_of_coefficients ψ Λ gV fun k _ =>
      contDiffOn_mFourierCoeff_of_truncatedParentLift hT hV (fun t z => gV t z) hgV k
  have hB (t : ℝ) (_ : t ∈ Icc 0 T) : RealTorusFourierBand (2 * Λ) (U t) :=
    fun k hk => hband (gV t) k hk
  have hD (t : ℝ) (ht : t ∈ Icc 0 T) :
      ∀ x, divergence (fun y => U t (toUnitTorus y)) x = 0 := by
    change ∀ x, divergence (fun y => realVectorFourierCutoff ψ Λ (gV t) (toUnitTorus y)) x = 0
    have hrep : (fun y => gV t (toUnitTorus y)) = V t := funext (hgV t ht)
    apply hdivc (gV t)
    · rw [hrep]; exact contDiff_slice_of_contDiffOn_Icc hV ht
    · rw [hrep]; exact hVdiv t ht
  obtain ⟨p, hp, hSlice⟩ := exists_truncatedParentPoissonPressure hT U hU hB hD
  refine ⟨p, hp, fun t ht => ?_⟩
  obtain ⟨hper, hmean, hPois, hRes⟩ := hSlice t ht
  have hProj := closedSlabLerayMomentum_realFourierCutoff htime hspace hdivc hT pressure hV hVper
    hVdiv hMom gV gRV hgV hgRV t ht
  exact ⟨hper, hmean, hPois, hRes.trans hProj⟩

/-- Copy of `nonempty_truncatedChildStage`: the truncation of §5.7 exists as a library
child stage. The slice cutoff (`exists_truncatedParent_T1`) is inlined; oddness,
divergence freeness and the band `2Λ` of the cutoff velocity come from the hypotheses
`hpar`, `hdivc`, `hband` (Lemma B.1), and the Poisson pressure from the copy
`exists_realFourierCutoffPoissonPressure`. -/
theorem nonempty_truncatedChildStage
    {ψ : Vec3 → ℝ} {Λ : ℝ} (hpar : CutParity ψ Λ) (hdivc : CutDivergence ψ Λ)
    (hband : CutBand ψ Λ) (htime : CutTimeDeriv ψ Λ) (hspace : CutSpaceDeriv ψ Λ)
    {T : ℝ} (hT : 0 < T)
    {V RV : Velocity} (approximatePressure : ℝ → EndpointSmoothPotential)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hRV : ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hRVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (RV t))
    (hVodd : ∀ t ∈ Icc 0 T, Function.Odd (V t))
    (hVdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0)
    (hMom : ∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
      fderiv ℝ (V t) x (V t x) + gradient (approximatePressure t).lift x = RV t x) :
    Nonempty (TruncatedChildStage T Λ ψ V RV) := by
  classical
  obtain ⟨gV, hgV⟩ := exists_closedSlab_torusSlices
    (fun t ht => (contDiff_slice_of_contDiffOn_Icc hV ht).continuous) hVper
  have hrep (t : ℝ) (ht : t ∈ Icc 0 T) : (fun x => gV t (toUnitTorus x)) = V t :=
    funext (hgV t ht)
  have hs : ContDiffOn ℝ ∞
      (fun z : ℝ × Vec3 => realVectorFourierCutoff ψ Λ (gV z.1) (toUnitTorus z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_lift_realVectorFourierCutoff_of_coefficients ψ Λ gV fun k _ =>
      contDiffOn_mFourierCoeff_of_truncatedParentLift hT hV (fun t z => gV t z) hgV k
  obtain ⟨gRV, hgRV⟩ := exists_closedSlab_torusSlices
    (fun t ht => (contDiff_slice_of_contDiffOn_Icc hRV ht).continuous) hRVper
  obtain ⟨p, hp, hP⟩ := exists_realFourierCutoffPoissonPressure hband hdivc htime hspace hT
    approximatePressure hV hVper hVdiv hMom gV gRV hgV hgRV
  let U (t : ℝ) : C(Labels, Vec3) := by
    refine ⟨realVectorFourierCutoff ψ Λ (gV t), periodicRealPartVector.continuous.comp ?_⟩
    unfold smoothFourierCutoff finiteFourierSum
    exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const
  refine ⟨{
    approximateTorus := gV
    approximateResidualTorus := gRV
    torusVelocity := U
    pressure := p
    approximate_rep := hgV
    approximateResidual_rep := hgRV
    cutoff := fun _ _ => rfl
    smooth_velocity := hs
    odd_velocity := fun t ht => odd_lift_of_cutParity hpar (gV t) (by rw [hrep t ht]; exact hVodd t ht)
    divergence_free := fun t ht => hdivc (gV t)
      (by rw [hrep t ht]; exact contDiff_slice_of_contDiffOn_Icc hV ht)
      (by rw [hrep t ht]; exact hVdiv t ht)
    velocity_band := fun t _ k hk => hband (gV t) k hk
    smooth_pressure := hp
    periodic_pressure := fun t ht => (hP t ht).1
    mean_zero_pressure := fun t ht => (hP t ht).2.1
    poisson := fun t ht => (hP t ht).2.2.1
    projected_eq := ?_
    residual_cutoff := fun t ht => (hP t ht).2.2.2
  }⟩
  intro t ht
  exact (hP t ht).2.2.2.trans
    (closedSlabLerayMomentum_realFourierCutoff htime hspace hdivc hT approximatePressure hV hVper
      hVdiv hMom gV gRV hgV hgRV t ht).symm

end

end TorusEuler.Paper.Lib.S5c

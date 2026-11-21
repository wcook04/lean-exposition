import TorusEuler.HierarchyPhysicalApproximation
import TorusEuler.HierarchyHigherPressure
import TorusEuler.HierarchyPrimaryPressureCenter
import TorusEuler.MeanPressureHessian

/-! The exact mean-pressure equation and total physical Hessian of frozen Lemma 5.9. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

noncomputable section

local notation "TimeSlab(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => (Set.prod (TimeSlab(T)) (univ : Set Vec3))

private theorem pressureGraph_spaceSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (ht : t ∈ TimeSlab(T)) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

private theorem pressureGraph_timeSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    DifferentiableWithinAt ℝ (fun r => f r x) TimeSlab(T) t :=
  ((hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    (fun r hr => show (r, x) ∈ LiftSlab(T) from ⟨hr, mem_univ x⟩)).differentiableOn (by simp)) t ht

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "MP" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)

private def pressureGraphEval {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Velocity) (k : Vec3) (t : ℝ) (x : Vec3) : HierarchySmoothProfile T E →ₗ[ℝ] E where
  toFun f := graphRead A k f t x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

set_option maxHeartbeats 1000000 in
/-- The linearized material momentum is the graph of the material and
pressure operators. Polarization of the exact nonlinear graph equation
removes the quadratic perturbation advection. -/
theorem linearizedMomentum_graphRead_parent
    {U : Velocity} {X : ℝ → Velocity} (hT : 0 < T) (hX : IsLabelFlowOn U X TimeSlab(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (G M : MP) (κ W : VP) (q : SP) (k : Vec3) {t : ℝ} (ht : t ∈ TimeSlab(T)) (x : Vec3)
    (hG : ∀ a s, G.val (t,a,s) = fderiv ℝ (X t 0) (X 0 t a))
    (hM : ∀ a s, M.val (t,a,s) = fderiv ℝ (U t) (X 0 t a))
    (hκ : ∀ a s, κ.val (t,a,s) = labelWaveVector X 0 a k t) :
    let A : Velocity := fun r => X r 0
    let O := hierarchyConcreteOperators hT G M κ
    let V := graphRead A k W
    let Q := graphRead A k q
    derivWithin (fun r => V r x) TimeSlab(T) t + fderiv ℝ (V t) x (U t x) +
      fderiv ℝ (U t) x (V t x) + gradient (Q t) x =
      graphRead A k (O.material W + O.labelGrad q + O.phaseGrad q) t x := by
  intro A O V Q
  let ev : VP →ₗ[ℝ] Vec3 := pressureGraphEval A k t x
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) LiftSlab(T) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hV : ContDiffOn ℝ ∞ (Function.uncurry V) LiftSlab(T) := contDiffOn_graphRead k W hA
  have hu := pressureGraph_timeSlice hU ht x
  have hv := pressureGraph_timeSlice hV ht x
  have hu' := (pressureGraph_spaceSlice hU ht).differentiable (by simp) x
  have hv' := (pressureGraph_spaceSlice hV ht).differentiable (by simp) x
  have hp : DifferentiableAt ℝ ((0 : Pressure) t) x := differentiableAt_const 0
  have hplus := momentumResidual_graphRead_parent (p := 0) hT hX hU hper hA
    G M κ W q k ht x hp hG hM hκ
  have hminus := momentumResidual_graphRead_parent (p := 0) hT hX hU hper hA
    G M κ (-W) (-q) k ht x hp hG hM hκ
  change momentumResidual TimeSlab(T) (U + V) (0 + Q) t x =
    ev (O.material W + O.labelAdv W W + O.phaseAdv W W + O.labelGrad q + O.phaseGrad q) +
      momentumResidual TimeSlab(T) U 0 t x at hplus
  change momentumResidual TimeSlab(T) (U + -V) (0 + -Q) t x =
    ev (O.material (-W) + O.labelAdv (-W) (-W) + O.phaseAdv (-W) (-W) +
      O.labelGrad (-q) + O.phaseGrad (-q)) + momentumResidual TimeSlab(T) U 0 t x at hminus
  rw [zero_add] at hplus
  rw [zero_add, ← sub_eq_add_neg] at hminus
  have hgrad : gradient (-(Q t)) x = -gradient (Q t) x := by
    rw [gradient, fderiv_neg, map_neg]
    rfl
  have hplusL : momentumResidual TimeSlab(T) (U + V) Q t x =
      derivWithin (fun r => U r x) TimeSlab(T) t + derivWithin (fun r => V r x) TimeSlab(T) t +
      (fderiv ℝ (U t) x + fderiv ℝ (V t) x) (U t x + V t x) + gradient (Q t) x := by
    simp only [momentumResidual, materialAcceleration, Pi.add_apply]
    rw [derivWithin_fun_add hu hv, fderiv_add hu' hv']
  have hminusL : momentumResidual TimeSlab(T) (U - V) (-Q) t x =
      derivWithin (fun r => U r x) TimeSlab(T) t - derivWithin (fun r => V r x) TimeSlab(T) t +
      (fderiv ℝ (U t) x - fderiv ℝ (V t) x) (U t x - V t x) - gradient (Q t) x := by
    simp only [momentumResidual, materialAcceleration, Pi.sub_apply, Pi.neg_apply, hgrad]
    rw [derivWithin_fun_sub hu hv, fderiv_sub hu' hv']
    simp only [sub_eq_add_neg]
  rw [hplusL] at hplus
  rw [hminusL] at hminus
  have H := congrArg₂ (· - ·) hplus hminus
  have hleft :
      (derivWithin (fun r => U r x) TimeSlab(T) t + derivWithin (fun r => V r x) TimeSlab(T) t +
        (fderiv ℝ (U t) x + fderiv ℝ (V t) x) (U t x + V t x) + gradient (Q t) x) -
      (derivWithin (fun r => U r x) TimeSlab(T) t - derivWithin (fun r => V r x) TimeSlab(T) t +
        (fderiv ℝ (U t) x - fderiv ℝ (V t) x) (U t x - V t x) - gradient (Q t) x) =
      (2 : ℝ) • (derivWithin (fun r => V r x) TimeSlab(T) t + fderiv ℝ (V t) x (U t x) +
        fderiv ℝ (U t) x (V t x) + gradient (Q t) x) := by
    simp only [_root_.add_apply, _root_.sub_apply, map_add, map_sub]
    module
  have hright :
      (ev (O.material W + O.labelAdv W W + O.phaseAdv W W + O.labelGrad q + O.phaseGrad q) +
        momentumResidual TimeSlab(T) U 0 t x) -
      (ev (O.material (-W) + O.labelAdv (-W) (-W) + O.phaseAdv (-W) (-W) +
        O.labelGrad (-q) + O.phaseGrad (-q)) + momentumResidual TimeSlab(T) U 0 t x) =
      (2 : ℝ) • ev (O.material W + O.labelGrad q + O.phaseGrad q) := by
    simp only [map_add, map_neg, LinearMap.neg_apply, neg_neg]
    module
  rw [hleft, hright] at H
  exact smul_right_injective Vec3 (by norm_num : (2 : ℝ) ≠ 0) H

end HierarchySmoothProfile

namespace HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

/-- The physical readout of a phase-independent profile keeps the order-two
label budget when estimated in the spatial half-Hölder norm of order one. -/
theorem spatialHolderHalf_graphRead_independent_le_unweighted
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Velocity} {B : Vec3 → Vec3 →L[ℝ] Vec3} {t ell h C Q : ℝ}
    (hT : 0 < T) (ht : t ∈ Icc 0 T) (hell : 0 < ell)
    (hC : 0 ≤ C) (hQ : 1 ≤ Q) (hcost : ell⁻¹ * C ≤ Q)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x)
    (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ j ≤ 2, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j B a‖ ≤ C)
    (f : HierarchyTwistedProfile T k E)
    (hi : HierarchyPeriodicProfile.PhaseIndependent f.val.val) :
    SpatialHolderHalf 1 (graphRead A f t) ∧
      spatialHolderHalfNorm 1 (graphRead A f t) ≤
        13824 * Q ^ 2 * unweightedSeminorm False ell h 2 hT f := by
  let I := Icc (0 : ℝ) T
  let sf (r : I) (a : Vec3) (s : ℝ) := f.val.val.val (r,a,s)
  let mean (a : Vec3) := f.val.val.val (t,a,0)
  let N := unweightedSeminorm False ell h 2 hT f
  have hN : 0 ≤ N := apply_nonneg _ _
  have htimes := (show I ⊆ Icc 0 T from Subset.rfl)
  have hbdd (w : List (Fin 4)) (_ : w ∈ hierarchyAdmissibleWords (Fin 4) 2) :
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ell h) w
        (fun r : I => ((1 : ℝ)⁻¹ • Function.uncurry (sf r)))) := by
    exact hierarchyTwistedMixedWord_bddAbove_weighted hT ell h False w f htimes
      (fun _ => (1 : ℝ)⁻¹) (B := 1) (by simp)
  have hs := HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht
  have hj := scaledPhaseProfile_jetBound_of_actual_weightedWordNorm
    (f := sf) (gamma := fun _ => 1) hbdd ⟨t, ht⟩ zero_lt_one hs
  have hsEq :
      scaledPhaseProfile ell h (sf ⟨t,ht⟩) = scaledPhaseProfile ell 1 (fun a _ => mean a) := by
    funext z
    change f.val.val.val (t,ell • z.1,h * z.2) = f.val.val.val (t,ell • z.1,0)
    exact hi (t,ell • z.1,0) ⟨ht, mem_univ _⟩ (h * z.2)
  have hweight : (fun r : I => (1 : ℝ)⁻¹ • Function.uncurry (sf r)) =
      weightedSlices I (fun _ => 1) f := by
    funext r z
    simp only [inv_one]
    rfl
  rw [hsEq, hweight, one_mul] at hj
  change PhaseJetBound 2 ((4 : ℝ) ^ 2 * N) (scaledPhaseProfile ell 1 (fun a _ => mean a)) at hj
  have hmean : ContDiff ℝ ∞ mean := hs.comp (contDiff_id.prodMk contDiff_const)
  have hgraph : graphRead A f t = mean ∘ A t := by
    funext x
    change f.val.val.val (t,A t x,_) = f.val.val.val (t,A t x,0)
    exact hi (t,A t x,0) ⟨ht, mem_univ _⟩ _
  have hjet := transportedHierarchyMean_jetBound hell hC
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4 ^ 2) hN)
    hQ hcost hA hB hBreg hmean hcoeff hj
  rw [hgraph]
  obtain ⟨hh, hj'⟩ := spatialHolderHalfNorm_le_of_uniformJets (m := 1) (hmean.comp hA)
    (by positivity) hjet
  refine ⟨hh, hj'.trans_eq ?_⟩
  change _ = 13824 * Q^2 * N
  ring

private theorem meanBudget_seminorm_sum_le {ι E : Type*} [AddCommGroup E] [Module ℝ E]
    (N : Seminorm ℝ E) (S : Finset ι) (g : ι → E) :
    N (∑ i ∈ S, g i) ≤ ∑ i ∈ S, N (g i) := by
  let := N.toAddGroupSeminorm.toSeminormedAddCommGroup
  exact norm_sum_le S g

/-- The actual sum of the order-two label means and of their exact sources
both satisfy the decay rate in Lemma 5.9 on the full slab. -/
theorem meanProfileSums_orderTwo_le_of_actualLevels
    {P : ℕ} {ell h freq loss C : ℝ} (hT : 0 < T)
    (hfreq : 1 ≤ freq) (hL : 1 ≤ loss) (hC : 0 ≤ C)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (A : HierarchyOperators (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ))
    (completionSwitch parentResidual : HierarchyTwistedProfile T k Vec3)
    (hlevels : ∀ i ∈ Finset.Icc 2 P, HierarchyLevelBound
      (actualMeasuredLevels A u P completionSwitch parentResidual freq
        (zero_le_one.trans hfreq) ell h hT ht₀ htT γ hγ hpos) freq loss C 2 i) :
    let s := Finset.Icc 2 P
    let f := fun i => -A.average (A.sourceBeforeMean u P completionSwitch i) -
      (if i = 2 then parentResidual else 0)
    let N := unweightedSeminorm False ell h 2 hT
    let M := (s.card : ℝ) * (C * loss ^ 6 * freq ^ (-5 / 2 : ℝ))
    N (∑ i ∈ s, u.B i) ≤ M ∧ N (∑ i ∈ s, f i) ≤ M := by
  intro s f N M
  have hL₀ := zero_le_one.trans hL
  have hL56 : loss ^ 5 ≤ loss ^ 6 := pow_le_pow_right₀ hL (by decide)
  have hmono (i : ℕ) (hi : i ∈ s) : hierarchyMeanExponent i ≤ (-5 / 2 : ℝ) := by
    have hc : (2 : ℝ) ≤ i := by exact_mod_cast (Finset.mem_Icc.mp hi).1
    unfold hierarchyMeanExponent
    linarith
  have hterm (g : ℕ → HierarchyTwistedProfile T k Vec3)
      (hg : ∀ i ∈ s, N (g i) ≤ C * loss^6 * freq ^ hierarchyMeanExponent i) :
      N (∑ i ∈ s, g i) ≤ M := by
    refine (meanBudget_seminorm_sum_le N s g).trans ?_
    calc
      _ ≤ ∑ _i ∈ s, (C * loss ^ 6 * freq ^ (-5 / 2 : ℝ)) := by
        apply Finset.sum_le_sum
        intro i hi
        exact (hg i hi).trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le hfreq (hmono i hi)) (by positivity))
      _ = M := by rw [Finset.sum_const, nsmul_eq_mul]
  refine ⟨hterm u.B (fun i hi => (hlevels i hi).meanStrong), hterm f ?_⟩
  intro i hi
  have hi1 : i ≠ 1 := by have := (Finset.mem_Icc.mp hi).1; omega
  have hh := (hlevels i hi).meanSource
  change (if i = 1 then 0 else N (f i)) ≤ _ at hh
  rw [ite_eq_right hi1] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL56 hC) (by positivity))

/-- The common mean budget costs a fixed parent power when the recurrence
loss does. The coefficient records the number of retained correction levels. -/
theorem meanOrderTwoBudget_le_parentPower
    {P r : ℕ} {D freq C loss K : ℝ} (hfreq : 0 ≤ freq)
    (hC : 0 ≤ C) (hloss : 0 ≤ loss) (hK : loss ≤ K * D ^ r) :
    ((Finset.Icc 2 P).card : ℝ) * (C * loss ^ 6 * freq ^ (-5 / 2 : ℝ)) ≤
      (((Finset.Icc 2 P).card : ℝ) * C * K ^ 6) * D ^ (6 * r) * freq ^ (-5 / 2 : ℝ) := by
  have hpow := pow_le_pow_left₀ hloss hK 6
  calc
    _ ≤ ((Finset.Icc 2 P).card : ℝ) * (C * (K * D ^ r) ^ 6 * freq ^ (-5 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hC) (Real.rpow_nonneg hfreq _)) (Nat.cast_nonneg _)
    _ = _ := by rw [mul_pow, ← pow_mul, mul_comm r 6]; ring

/-- The pressure of the physical mean keeps the rate `freq^(-5/2)` on the
whole slab. The two order-two bounds are on the actual, unweighted profiles. -/
theorem norm_graphRead_meanHessian_le_of_orderTwo
    {U A : Velocity} {B : ℝ → Vec3 → Vec3 →L[ℝ] Vec3}
    {D freq ell h C Cparent Cmean : ℝ} {a b : ℕ}
    (hT : 0 < T) (hD : 1 ≤ D) (hfreq : 0 < freq) (hell : 0 < ell)
    (hC : 0 ≤ C) (hCparent : 0 ≤ Cparent) (hCmean : 0 ≤ Cmean)
    (hcost : ell⁻¹ * C ≤ D ^ a)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hAper : ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) x,
      A t (x + latticeVector n) = A t x + latticeVector n)
    (hB : ∀ t ∈ Icc 0 T, ∀ x, B t (A t x) = fderiv ℝ (A t) x)
    (hBreg : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (B t))
    (hcoeff : ∀ t ∈ Icc 0 T, ∀ j ≤ 2, ∀ a, ell ^ j * ‖iteratedFDeriv ℝ j (B t) a‖ ≤ C)
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hUper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hUdiv : ∀ t ∈ Icc 0 T, ∀ x, divergence (U t) x = 0)
    (hUsize : ∀ t ∈ Icc 0 T, SpatialHolderHalf 0 (fderiv ℝ (U t)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (U t)) ≤ Cparent * D ^ 2)
    (v f : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ)
    (hvi : HierarchyPeriodicProfile.PhaseIndependent v.val.val)
    (hfi : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    (hv : unweightedSeminorm False ell h 2 hT v ≤ Cmean * D ^ b * freq ^ (-5 / 2 : ℝ))
    (hf : unweightedSeminorm False ell h 2 hT f ≤ Cmean * D ^ b * freq ^ (-5 / 2 : ℝ)) :
    let V := graphRead A v
    let F := graphRead A f
    let Q := graphRead A q
    (∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0) →
    (∀ t ∈ Icc 0 T, ∀ x,
      derivWithin (fun r => V r x) (Icc 0 T) t + fderiv ℝ (V t) x (U t x) +
        fderiv ℝ (U t) x (V t x) + gradient (Q t) x = F t x) →
    ∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (gradient (Q t)) x‖ ≤
      (48 * ‖pressureHessianMultiplier‖ * (13824 * Cmean) * (1 + Cparent)) *
        D ^ (b + 2 * a + 2) * freq ^ (-5 / 2 : ℝ) := by
  intro V F Q hVdiv hMom
  let M := (13824 * Cmean) * D ^ (b + 2 * a) * freq ^ (-5 / 2 : ℝ)
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hQpow : 1 ≤ D ^ a := one_le_pow₀ hD
  have hsA (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (A t) :=
    contDiffOn_univ.mp (hA.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hVs : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    HierarchySmoothProfile.contDiffOn_graphRead k v.val.val hA
  have hQs : ContDiffOn ℝ ∞ (Function.uncurry Q) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    HierarchySmoothProfile.contDiffOn_graphRead k q.val.val hA
  have hsQ (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (Q t) :=
    contDiffOn_univ.mp (hQs.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hVp (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (V t) :=
    spatiallyPeriodic_graphRead A v t (hAper t ht)
  have hFp (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (F t) :=
    spatiallyPeriodic_graphRead A f t (hAper t ht)
  have hQp (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (Q t) :=
    spatiallyPeriodic_graphRead A q t (hAper t ht)
  have hnorm (g : HierarchyTwistedProfile T k Vec3)
      (hi : HierarchyPeriodicProfile.PhaseIndependent g.val.val)
      (hg : unweightedSeminorm False ell h 2 hT g ≤ Cmean * D ^ b * freq ^ (-5 / 2 : ℝ))
      (t : ℝ) (ht : t ∈ Icc 0 T) : SpatialHolderHalf 1 (graphRead A g t) ∧
        spatialHolderHalfNorm 1 (graphRead A g t) ≤ M := by
    obtain ⟨H, Hsize⟩ := spatialHolderHalf_graphRead_independent_le_unweighted hT ht hell hC hQpow
      hcost (hsA t ht) (hB t ht) (hBreg t ht) (hcoeff t ht) g hi
    refine ⟨H, Hsize.trans ((mul_le_mul_of_nonneg_left hg (by positivity)).trans_eq ?_)⟩
    dsimp only [M]
    rw [← pow_mul, pow_add, mul_comm 2 a]
    ring
  have hH := meanPressureHessian_closedSlab_bound hT hU (hVs.of_le (by simp)) hsQ hQp
    hUper hVp hFp hUdiv hVdiv hMom hUsize (hnorm v hvi hv) (hnorm f hfi hf)
  have hR := meanPressureHessian_rate_absorption (b := b + 2 * a) hD hfreq hCparent
    (mul_nonneg (by norm_num) hCmean) hM le_rfl (le_refl M) (le_refl M)
  intro t ht x
  let H := fderiv ℝ (gradient (Q t))
  obtain ⟨hbounded, hnormH⟩ := hH.1 t ht
  obtain ⟨_, hs, hh⟩ := (spatialHolderHalf_zero_iff H).mp hbounded
  have hnonneg : 0 ≤ spatialHolderHalfSeminorm H := by
    have h := le_ciSup hh ((0 : Vec3), (0 : Vec3))
    have hz : spatialHolderHalfQuotient H (0, 0) = 0 := by simp [spatialHolderHalfQuotient]
    rw [hz] at h
    exact h
  have hpoint : ‖H x‖ ≤ spatialHolderHalfNorm 0 H := by
    rw [spatialHolderHalfNorm_zero_eq]
    exact (norm_le_spatialSupNorm hs x).trans (le_add_of_nonneg_right hnonneg)
  exact hpoint.trans (hnormH.trans hR)

end

end HierarchyTwistedProfile


namespace HierarchyTwistedProfile

/-- Finite profile sums commute with the Eulerian readout. -/
theorem graphRead_finset_sum {T : ℝ} {k : Vec3}
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : Velocity) (s : Finset ι) (f : ι → HierarchyTwistedProfile T k E) :
    graphRead A (∑ i ∈ s, f i) = fun t x => ∑ i ∈ s, graphRead A (f i) t x := by
  funext t x
  let eval : HierarchyTwistedProfile T k E →+ E :=
    { toFun := fun y => y.val.val.val (hierarchyGraphPoint A k t x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  exact map_sum eval f s

/-- The exact correction to the parent pressure, decomposed by the selected
leading, higher oscillatory, and mean profiles. -/
theorem PhysicalApproximationData.pressure_sub_parent_eq_graph_components
    {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
    {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
    (b : PhysicalApproximationData d p P) (hP : 1 ≤ P) (t : ℝ) :
    b.pressure t - p t =
      graphRead (fun r => X r 0) b.leading.output.p t +
      (fun x => ∑ i ∈ Finset.Icc 2 P, graphRead (fun r => X r 0) (b.profiles.p i) t x) +
      (fun x => ∑ i ∈ Finset.Icc 2 P, graphRead (fun r => X r 0) (b.profiles.q i) t x) := by
  classical
  have hLeading := b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
    b.parentResidual_average b.leading.output
  have hOsc : b.profiles.p 1 = b.leading.output.p := hLeading.2.1
  have hMean : b.profiles.q 1 = 0 := hLeading.2.2.2
  have hsum : b.profiles.pressure P = b.leading.output.p +
      (∑ i ∈ Finset.Icc 2 P, b.profiles.p i) + (∑ i ∈ Finset.Icc 2 P, b.profiles.q i) := by
    unfold HierarchyProfiles.pressure
    rw [← Finset.insert_Icc_add_one_left_eq_Icc hP, Finset.sum_insert (by simp), hOsc, hMean,
      add_zero, Finset.sum_add_distrib, add_assoc]
    rfl
  funext x
  let eval : HierarchyTwistedProfile T k ℝ →+ ℝ :=
    { toFun := fun f => f.val.val.val (hierarchyGraphPoint (fun r => X r 0) k t x)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change p t x + eval (b.profiles.pressure P) - p t x = eval b.leading.output.p +
    (∑ i ∈ Finset.Icc 2 P, eval (b.profiles.p i)) + (∑ i ∈ Finset.Icc 2 P, eval (b.profiles.q i))
  rw [hsum, map_add, map_add, map_sum, map_sum]
  abel

end HierarchyTwistedProfile

private theorem gradient_add_for_pressure {p q : Vec3 → ℝ}
    (hp : Differentiable ℝ p) (hq : Differentiable ℝ q) :
    gradient (p + q) = gradient p + gradient q := by
  funext x
  unfold gradient
  rw [fderiv_add (hp x) (hq x), map_add]
  rfl

/-- The graph pressure Hessian is the sum of the three physical Hessians. -/
theorem fderiv_gradient_add_three_pressures {p q r : Vec3 → ℝ}
    (hp : ContDiff ℝ 2 p) (hq : ContDiff ℝ 2 q) (hr : ContDiff ℝ 2 r) (x : Vec3) :
    fderiv ℝ (gradient (p + q + r)) x =
      fderiv ℝ (gradient p) x + fderiv ℝ (gradient q) x + fderiv ℝ (gradient r) x := by
  have hreg (u : Vec3 → ℝ) (hu : ContDiff ℝ 2 u) : Differentiable ℝ (gradient u) := by
    let S := (InnerProductSpace.toDual ℝ Vec3).symm.toContinuousLinearEquiv
    exact S.differentiable.comp ((hu.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num))
  have hp' := hp.differentiable (by norm_num)
  have hq' := hq.differentiable (by norm_num)
  rw [gradient_add_for_pressure (hp'.add hq') (hr.differentiable (by norm_num)),
    gradient_add_for_pressure hp' hq', fderiv_add ((hreg p hp).add (hreg q hq) x) (hreg r hr x),
    fderiv_add (hreg p hp x) (hreg q hq x)]

/-- The three correction norms decay faster than the leading one-sided term.
Their fixed constants add without any change in the leading frequency rate. -/
theorem pressureHessian_quadratic_upper_at_step_scale {freq A B C D : ℝ}
    {H L G O M : Vec3 →L[ℝ] Vec3}
    (hf : 1 ≤ freq) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hH : H = L + G + O + M)
    (hL : ∀ v, ⟪v, L v⟫_ℝ ≤ (A * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hG : ‖G‖ ≤ B * freq ^ (-3 / 4 : ℝ))
    (hO : ‖O‖ ≤ C * freq ^ (-5 / 12 : ℝ))
    (hM : ‖M‖ ≤ D * freq ^ (-5 / 2 : ℝ)) (v : Vec3) :
    ⟪v, H v⟫_ℝ ≤ ((A + B + C + D) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  have hge : freq ^ (-3 / 4 : ℝ) ≤ freq ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have hoe : freq ^ (-5 / 12 : ℝ) ≤ freq ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have hme : freq ^ (-5 / 2 : ℝ) ≤ freq ^ (-1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hf (by norm_num)
  have h := wavePressure_hessian_quadratic_upper hH hL
    (hG.trans (mul_le_mul_of_nonneg_left hge hB))
    (hO.trans (mul_le_mul_of_nonneg_left hoe hC))
    (hM.trans (mul_le_mul_of_nonneg_left hme hD)) v
  rw [← add_mul, ← add_mul, ← add_mul] at h
  exact h


namespace HierarchyTwistedProfile.PhysicalApproximationData

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {p : Pressure}
  {hT : 0 < T} {d : ParentGeometry hT U X k} {P : ℕ}
  (b : PhysicalApproximationData d p P)

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ

/-- The actual source of the selected mean at level `i`. At level two this
also cancels the physical parent residual. -/
def meanForceAt (i : ℕ) : VP :=
  let H := b.operators.sourceBeforeMean b.profiles P b.leading.completionSwitch i
  (-(b.operators.average H)) - (if i = 2 then b.parentResidual else 0)

/-- The finite sum of the physical mean sources, on the inverse-label graph. -/
def meanForce : Velocity :=
  graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 2 P, b.meanForceAt i)

/-- The finite sum of the actual selected mean pressures. -/
def meanPressure : Pressure :=
  graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 2 P, b.profiles.q i)

/-- The leading correction has zero mean, so the mean velocity starts at level two. -/
theorem meanCorrection_eq_correctionGraphSum (hP : 1 ≤ P) :
    b.meanCorrection = graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 2 P, b.profiles.B i) := by
  have hB : b.profiles.B 1 = 0 :=
    (b.solvers.construct_leading P b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).2.2.1
  rw [b.meanCorrection_eq_graph_sum, ← Finset.insert_Icc_add_one_left_eq_Icc hP,
    Finset.sum_insert (by simp), hB, zero_add]
  rfl

/-- The actual mean source is fixed by phase averaging. -/
theorem average_meanForceAt (i : ℕ) (hi : i ∈ Finset.Icc 2 P) :
    b.operators.average (b.meanForceAt i) = b.meanForceAt i := by
  obtain ⟨hf, _, _⟩ := b.solvers.construct_mean_selected hi b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output
  exact hf

set_option maxHeartbeats 850000 in
/-- The exact sum of the selected mean equations, including vanishing of the
phase gradient of every selected mean pressure. -/
theorem summedMeanProfile_momentum :
    b.operators.material (∑ i ∈ Finset.Icc 2 P, b.profiles.B i) +
      b.operators.labelGrad (∑ i ∈ Finset.Icc 2 P, b.profiles.q i) +
      b.operators.phaseGrad (∑ i ∈ Finset.Icc 2 P, b.profiles.q i) =
      ∑ i ∈ Finset.Icc 2 P, b.meanForceAt i := by
  rw [map_sum, map_sum, map_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hm : b.operators.material (b.profiles.B i) + b.operators.labelGrad (b.profiles.q i) =
      b.meanForceAt i :=
    (b.solvers.construct_equations hi b.leading.completionSwitch b.parentResidual
      b.parentResidual_average b.leading.output).1
  obtain ⟨hf, _, hq⟩ := b.solvers.construct_mean_selected hi b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output
  have hphase : b.operators.phaseGrad (b.profiles.q i) = 0 :=
    (congrArg b.operators.phaseGrad hq).trans (b.solvers.solveMean (b.meanForceAt i) hf).val.phaseGrad_q
  rw [hm, hphase, add_zero]

/-- The sum of the actual selected means satisfies physical linearized
Euler momentum with the exact summed force from those same levels. -/
theorem meanCorrection_linearizedMomentum (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    {t : ℝ} (ht : t ∈ TimeSlab(T)) (x : Vec3) :
    derivWithin (fun r => b.meanCorrection r x) TimeSlab(T) t +
      fderiv ℝ (b.meanCorrection t) x (U t x) +
      fderiv ℝ (U t) x (b.meanCorrection t x) + gradient (b.meanPressure t) x =
      b.meanForce t x := by
  let W : VP := ∑ i ∈ Finset.Icc 2 P, b.profiles.B i
  let Q : SP := ∑ i ∈ Finset.Icc 2 P, b.profiles.q i
  have hGraph := HierarchySmoothProfile.linearizedMomentum_graphRead_parent hT hX hU hper
    d.inverse.val.val d.strain.val.val d.covector.val.val W.val.val Q.val.val k ht x
    (fun a s => d.inverse_value (t,a,s) ⟨ht, mem_univ _⟩)
    (fun a s => d.strain_value (t,a,s) ⟨ht, mem_univ _⟩)
    (fun a s => d.covector_value (t,a,s) ⟨ht, mem_univ _⟩)
  have hEq : b.operators.material W + b.operators.labelGrad Q + b.operators.phaseGrad Q =
      ∑ i ∈ Finset.Icc 2 P, b.meanForceAt i := b.summedMeanProfile_momentum
  rw [b.meanCorrection_eq_correctionGraphSum hP]
  exact hGraph.trans (congrArg (fun f : VP => graphRead (fun r => X r 0) f t x) hEq)

set_option maxHeartbeats 1600000 in
/-- The summed mean correction is solenoidal by the Piola identities of the
same selected mean levels. -/
theorem meanCorrection_divergence_eq_zero (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ TimeSlab(T), ∀ x, divergence (U t) x = 0) :
    ∀ t ∈ TimeSlab(T), ∀ x, divergence (b.meanCorrection t) x = 0 := by
  intro t ht x
  let W : VP := ∑ i ∈ Finset.Icc 2 P, b.profiles.B i
  let forget : VP →ₗ[ℝ] HierarchySmoothProfile T Vec3 :=
    (hierarchyPeriodicProfileSubmodule T Vec3).subtype.comp (hierarchyTwistedProfileSubmodule T k Vec3).subtype
  let D := (HierarchySmoothProfile.profileTotalDivergence hT d.inverse.val.val d.covector.val.val).comp forget
  have hW : D W = 0 := by
    unfold W
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    obtain ⟨hf, hB, _⟩ := b.solvers.construct_mean_selected hi b.leading.completionSwitch
      b.parentResidual b.parentResidual_average b.leading.output
    change b.profiles.B i = (b.solvers.solveMean (b.meanForceAt i) hf).val.B at hB
    rw [hB]
    exact d.physicalSolvers_mean_divergence_eq_zero hX hU hper hdiv b.time_le_one _ hf
  have hcoeff := (d.inverseGraph_values hX hU hper).2 t ht x ⟪k, X t 0 x⟫_ℝ
  have hAreg : ContDiffOn ℝ ∞ (Function.uncurry (fun r => X r 0)) LiftSlab(T) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hA := (pressureGraph_spaceSlice hAreg ht).differentiable (by simp) x
  rw [b.meanCorrection_eq_correctionGraphSum hP]
  exact HierarchySmoothProfile.divergence_transportedSmoothProfile_eq_zero
    (A := fun r => X r 0) (k := k) (x := x) (Ax := fderiv ℝ (X t 0) x)
    hT d.inverse.val.val d.covector.val.val W.val.val ht hA.hasFDerivAt hcoeff.1 hcoeff.2 hW

/-- Poisson's equation for the sum of the physical mean pressures on the
closed slab. Its force is the graph of the actual selected mean sources. -/
theorem meanPressure_poisson (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ TimeSlab(T), ∀ x, divergence (U t) x = 0) :
    ∀ t ∈ TimeSlab(T), ∀ x,
      divergence (gradient (b.meanPressure t)) x = divergence (b.meanForce t) x -
        2 * LinearMap.trace ℝ Vec3 ((fderiv ℝ (U t) x).comp
          (fderiv ℝ (b.meanCorrection t) x)).toLinearMap := by
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hV : ContDiffOn ℝ ∞ (Function.uncurry b.meanCorrection) LiftSlab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  have hq : ContDiffOn ℝ ∞ (Function.uncurry b.meanPressure) LiftSlab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  exact meanPressure_poisson_closedSlab hT (hU.of_le (by simp)) (hV.of_le (by simp))
    (fun t ht => (pressureGraph_spaceSlice hq ht).of_le (by simp)) hdiv
    (b.meanCorrection_divergence_eq_zero hP hX hU hper hdiv)
    (fun _ ht x => b.meanCorrection_linearizedMomentum hP hX hU hper ht x)

private theorem phaseIndependent_sum_of_average (f : ℕ → VP)
    (hf : ∀ i ∈ Finset.Icc 2 P, b.operators.average (f i) = f i) :
    HierarchyPeriodicProfile.PhaseIndependent (∑ i ∈ Finset.Icc 2 P, f i).val.val := by
  have heq : b.operators.average (∑ i ∈ Finset.Icc 2 P, f i) = ∑ i ∈ Finset.Icc 2 P, f i := by
    rw [map_sum]
    exact Finset.sum_congr rfl hf
  exact HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT _
    (congrArg Subtype.val heq)

/-- From the measured hierarchy levels, the exact mean and mean force have
one common order-two profile budget with the mean frequency rate. -/
theorem meanProfileSums_le_of_actualLevels
    {ell h freq loss C : ℝ} (hfreq : 1 ≤ freq) (hLoss : 1 ≤ loss) (hC : 0 ≤ C)
    {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hLevels : ∀ i ∈ Finset.Icc 2 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual freq
        (zero_le_one.trans hfreq) ell h hT ht₀ htT γ hγ hpos) freq loss C 2 i) :
    let N : Seminorm ℝ VP := unweightedSeminorm False ell h 2 hT
    let M := (Finset.Icc 2 P).card * (C * loss ^ 6 * freq ^ (-5 / 2 : ℝ))
    N (∑ i ∈ Finset.Icc 2 P, b.profiles.B i) ≤ M ∧
      N (∑ i ∈ Finset.Icc 2 P, b.meanForceAt i) ≤ M :=
  meanProfileSums_orderTwo_le_of_actualLevels hT hfreq hLoss hC ht₀ htT γ hγ hpos
    b.operators b.profiles b.leading.completionSwitch b.parentResidual hLevels

/-- The exact selected mean pressure obeys the `freq^(-5/2)` Hessian bound
from the order-two label norms of its mean velocity and force. -/
theorem norm_meanPressure_hessian_le_of_orderTwo (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ TimeSlab(T), ∀ x, divergence (U t) x = 0)
    {D freq ell h C Cparent Cmean : ℝ} {a e : ℕ}
    (hD : 1 ≤ D) (hfreq : 0 < freq) (hell : 0 < ell)
    (hC : 0 ≤ C) (hCparent : 0 ≤ Cparent) (hCmean : 0 ≤ Cmean)
    (hcost : ell⁻¹ * C ≤ D ^ a)
    (hcoeff : ∀ t ∈ TimeSlab(T), ∀ j ≤ 2, ∀ z,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => d.inverse.val.val.val (t,y,0)) z‖ ≤ C)
    (hUsize : ∀ t ∈ TimeSlab(T), SpatialHolderHalf 0 (fderiv ℝ (U t)) ∧
      spatialHolderHalfNorm 0 (fderiv ℝ (U t)) ≤ Cparent * D ^ 2)
    (hV : unweightedSeminorm False ell h 2 hT (∑ i ∈ Finset.Icc 2 P, b.profiles.B i) ≤
      Cmean * D ^ e * freq ^ (-5 / 2 : ℝ))
    (hF : unweightedSeminorm False ell h 2 hT (∑ i ∈ Finset.Icc 2 P, b.meanForceAt i) ≤
      Cmean * D ^ e * freq ^ (-5 / 2 : ℝ)) :
    ∀ t ∈ TimeSlab(T), ∀ x, ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤
      (48 * ‖pressureHessianMultiplier‖ * (13824 * Cmean) * (1 + Cparent)) *
        D ^ (e + 2 * a + 2) * freq ^ (-5 / 2 : ℝ) := by
  let A : Velocity := fun t => X t 0
  let W : VP := ∑ i ∈ Finset.Icc 2 P, b.profiles.B i
  let F : VP := ∑ i ∈ Finset.Icc 2 P, b.meanForceAt i
  let Q : SP := ∑ i ∈ Finset.Icc 2 P, b.profiles.q i
  let B (t : ℝ) (y : Vec3) := d.inverse.val.val.val (t,y,0)
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) LiftSlab(T) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hAper : ∀ t ∈ TimeSlab(T), ∀ (n : Fin 3 → ℤ) x,
      A t (x + latticeVector n) = A t x + latticeVector n := by
    intro t ht
    exact hX.add_latticeVector hK hper ht (left_mem_Icc.mpr hT.le)
  have hB : ∀ t ∈ TimeSlab(T), ∀ x, B t (A t x) = fderiv ℝ (A t) x :=
    fun t ht x => ((d.inverseGraph_values hX hU hper).2 t ht x 0).1
  have hBreg : ∀ t ∈ TimeSlab(T), ContDiff ℝ ∞ (B t) := by
    intro t ht
    exact (HierarchySmoothProfile.contDiff_labelPhase_slice d.inverse.val.val ht).comp
      (contDiff_id.prodMk contDiff_const)
  have hWi : HierarchyPeriodicProfile.PhaseIndependent W.val.val :=
    b.phaseIndependent_sum_of_average _ (fun i _ => b.solvers.construct_average_B P
      b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output i)
  have hFi : HierarchyPeriodicProfile.PhaseIndependent F.val.val :=
    b.phaseIndependent_sum_of_average _ b.average_meanForceAt
  have hEq : b.meanCorrection = graphRead A W := b.meanCorrection_eq_correctionGraphSum hP
  have hVdiv : ∀ t ∈ TimeSlab(T), ∀ x, divergence (graphRead A W t) x = 0 := by
    rw [← hEq]
    exact b.meanCorrection_divergence_eq_zero hP hX hU hper hdiv
  have hMom : ∀ t ∈ TimeSlab(T), ∀ x,
      derivWithin (fun r => graphRead A W r x) TimeSlab(T) t +
        fderiv ℝ (graphRead A W t) x (U t x) + fderiv ℝ (U t) x (graphRead A W t x) +
        gradient (graphRead A Q t) x = graphRead A F t x := by
    rw [← hEq]
    exact fun _ ht x => b.meanCorrection_linearizedMomentum hP hX hU hper ht x
  exact norm_graphRead_meanHessian_le_of_orderTwo hT hD hfreq hell hC hCparent hCmean hcost
    hA hAper hB hBreg hcoeff (hU.of_le (by simp)) hper hdiv hUsize W F Q hWi hFi hV hF hVdiv hMom


/-- The exact leading pressure of the supplied hierarchy, read on the physical graph. -/
def leadingPressure : Pressure := graphRead (fun t => X t 0) b.leading.output.p

/-- The higher oscillatory pressure uses the selected corrections only. -/
def higherOscillatoryPressure : Pressure :=
  graphRead (fun t => X t 0) (∑ i ∈ Finset.Icc 2 P, b.profiles.p i)

/-- The pressure in the physical approximation separates into the parent and
its three exact corrections. -/
theorem pressure_sub_parent_eq_components (hP : 1 ≤ P) (t : ℝ) :
    b.pressure t - p t = b.leadingPressure t + b.higherOscillatoryPressure t + b.meanPressure t := by
  rw [b.pressure_sub_parent_eq_graph_components hP t, leadingPressure, higherOscillatoryPressure,
    meanPressure, graphRead_finset_sum, graphRead_finset_sum]

/-- The constant in the `freq^(-5/12)` estimate of the selected higher pressures. -/
def higherOscillatoryHessianPrefactor (P : ℕ) (C loss Cjet Aell Kwave : ℝ) : ℝ :=
  (6 * ((Aell + Kwave) * Cjet)) * ((Finset.Icc 2 P).card *
    (C * (8 * Cjet + (32 * Cjet ^ 2 + 32 * Cjet * Aell) * loss)))

set_option maxHeartbeats 1400000 in
/-- The canonical higher-pressure estimate (5.52) over the full parent slab.
The actual inactive-set propagation handles times before activation. -/
theorem norm_higherOscillatoryPressure_hessian_le_of_actualLevels (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    {freq ell h t₀ C loss Cjet Aell Kwave : ℝ} {S : Set Vec3}
    (hS : IsClosed S) (hInactive : b.leading.Inactive t₀ S)
    (hfreq : 1 ≤ freq) (hell : 0 < ell) (hhw : h = freq ^ (-1 / 2 : ℝ))
    (hellInv : ell⁻¹ ≤ Aell) (hk : ‖k‖ ≤ Kwave * freq)
    (hC : 0 ≤ C) (hLoss : 0 ≤ loss) (hCjet : 0 ≤ Cjet)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) (γ : ℝ → ℝ)
    (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ₁ : ∀ t ∈ Icc t₀ T, γ t ≤ 1)
    (hGJet : ∀ t ∈ TimeSlab(T), ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => d.inverse.val.val.val (t,y,0)) a‖ ≤ Cjet)
    (hGadjJet : ∀ t ∈ TimeSlab(T), ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => (d.inverse.val.val.val (t,y,0)).adjoint) a‖ ≤ Cjet)
    (hMJet : ∀ t ∈ TimeSlab(T), ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun y => d.strain.val.val.val (t,y,0)) a‖ ≤ Cjet)
    (hProjectionJet : ∀ t ∈ TimeSlab(T), ∀ j ≤ 1, ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j
        (fun y => hierarchyLongitudinalProjection (d.covector.val.val.val (t,y,0))) a‖ ≤ Cjet)
    (hLevels : ∀ n ∈ Finset.Icc 1 2, ∀ i ∈ Finset.Icc 2 P, HierarchyLevelBound
      (actualMeasuredLevels b.operators b.profiles P b.leading.completionSwitch b.parentResidual freq
        (zero_le_one.trans hfreq) ell h hT ht₀ htT γ hγ hpos) freq loss C n i) :
    ∀ t ∈ TimeSlab(T), ∀ x, ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤
      higherOscillatoryHessianPrefactor P C loss Cjet Aell Kwave * freq ^ (-5 / 12 : ℝ) := by
  let A : Velocity := fun r => X r 0
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) LiftSlab(T) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hAe : 0 ≤ Aell := (inv_nonneg.mpr hell.le).trans hellInv
  have hKw : 0 ≤ Kwave := nonneg_of_mul_nonneg_left ((norm_nonneg _).trans hk)
    (zero_lt_one.trans_le hfreq)
  have hB : 0 ≤ higherOscillatoryHessianPrefactor P C loss Cjet Aell Kwave * freq ^ (-5 / 12 : ℝ) := by
    unfold higherOscillatoryHessianPrefactor
    positivity
  have hSupport := (physicalConstruct_support_and_tail_on_inactive hT b.time_le_one hS
    d.inverse d.strain d.covector d.mean d.oscillation hP b.leading.completionSwitch
    b.parentResidual b.parentResidual_average b.leading.output hInactive.velocity
    hInactive.pressure hInactive.completionSwitch).1
  have hActive (t : ℝ) (ht : t ∈ Icc t₀ T) :
      ∀ x, ‖fderiv ℝ (gradient (fun y => ∑ i ∈ Finset.Icc 2 P,
        transportedProfile A k (fun _ a s => (b.profiles.p i).val.val.val (t,a,s)) t y)) x‖ ≤
        higherOscillatoryHessianPrefactor P C loss Cjet Aell Kwave * freq ^ (-5 / 12 : ℝ) := by
    have ht' : t ∈ TimeSlab(T) := Icc_subset_Icc_left ht₀ ht
    have hK (a : Vec3) : d.covector.val.val.val (t,a,0) = (d.inverse.val.val.val (t,a,0)).adjoint k := by
      rw [d.inverse_value _ ⟨ht', mem_univ _⟩, d.covector_value _ ⟨ht', mem_univ _⟩]
      rfl
    exact norm_higherPressureSum_hessian_of_actualLevels b.solvers
      (physicalSolvers_selectsTransverseResult b.time_le_one d.mean d.oscillation)
      P b.leading.completionSwitch b.parentResidual b.parentResidual_average b.leading.output
      (A := A) hfreq hell hhw hellInv hk hC hLoss hCjet ht₀ htT γ hγ hpos ht (hγ₁ t ht)
      (pressureGraph_spaceSlice hA ht') (fun x => ((d.inverseGraph_values hX hU hper).2 t ht' x 0).1)
      hK (d.oscillation.covector_ne_zero t ht') (hGJet t ht') (hGadjJet t ht')
      (hMJet t ht') (hProjectionJet t ht') (hLevels 1 (by decide)) (hLevels 2 (by decide))
  have H := norm_higherPressureSum_hessian_le_on_slab_of_support (A := A) b.profiles.p hB
    (fun i _ => (hSupport i).2.2) hActive
  intro t ht x
  rw [higherOscillatoryPressure, graphRead_finset_sum]
  exact H t ht x

/-- The total correction pressure satisfies the one-sided bound (5.49).
The three inputs refer to the exact leading, selected higher, and selected
mean pressures, all read on the same physical graph. -/
theorem pressureCorrection_hessian_upper_at_stepScale (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    {freq leading higher mean : ℝ} (hfreq : 1 ≤ freq) (hHigher₀ : 0 ≤ higher) (hMean₀ : 0 ≤ mean)
    (hLead : ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
        (leading * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hHigher : ∀ t ∈ TimeSlab(T), ∀ x,
      ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤ higher * freq ^ (-5 / 12 : ℝ))
    (hMean : ∀ t ∈ TimeSlab(T), ∀ x,
      ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤ mean * freq ^ (-5 / 2 : ℝ)) :
    ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.pressure t - p t)) x v⟫_ℝ ≤
        ((leading + higher + mean) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  let A : Velocity := fun r => X r 0
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) LiftSlab(T) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  have hLreg : ContDiffOn ℝ ∞ (Function.uncurry b.leadingPressure) LiftSlab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  have hOreg : ContDiffOn ℝ ∞ (Function.uncurry b.higherOscillatoryPressure) LiftSlab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  have hMreg : ContDiffOn ℝ ∞ (Function.uncurry b.meanPressure) LiftSlab(T) :=
    HierarchySmoothProfile.contDiffOn_graphRead k _ hA
  intro t ht x v
  have hH := fderiv_gradient_add_three_pressures
    ((pressureGraph_spaceSlice hLreg ht).of_le (by simp))
    ((pressureGraph_spaceSlice hOreg ht).of_le (by simp))
    ((pressureGraph_spaceSlice hMreg ht).of_le (by simp)) x
  rw [b.pressure_sub_parent_eq_components hP t]
  have hQ := pressureHessian_quadratic_upper_at_step_scale (G := 0) (B := 0)
    hfreq le_rfl hHigher₀ hMean₀ (by simpa only [add_zero] using hH)
    (hLead t ht x) (by simp) (hHigher t ht x) (hMean t ht x) v
  simpa only [add_zero] using hQ

/-- The one-sided correction bound gives the required estimate for the
exact slice potential, including the original pressure Hessian. -/
theorem potential_hessian_upper_of_pressureCorrection
    (props : PhysicalApproximationProperties b)
    (hp : ∀ t ∈ TimeSlab(T), ContDiff ℝ 2 (p t)) {stepBound : ℝ}
    (hCorr : ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.pressure t - p t)) x v⟫_ℝ ≤ stepBound * ‖v‖ ^ 2) :
    ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.potential props t).lift) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (p t)) x v⟫_ℝ + stepBound * ‖v‖ ^ 2 := by
  intro t ht x v
  let correction := b.pressure t - p t
  have hQ : ContDiff ℝ 2 correction :=
    ((pressureGraph_spaceSlice props.pressure_smooth ht).of_le (by simp)).sub (hp t ht)
  have hZ : ContDiff ℝ 2 (0 : Vec3 → ℝ) := contDiff_const
  have hzgrad : gradient (0 : Vec3 → ℝ) = 0 := gradient_fun_const' (0 : ℝ)
  have hH := fderiv_gradient_add_three_pressures (hp t ht) hQ hZ x
  rw [hzgrad, fderiv_zero, Pi.zero_apply, add_zero, add_zero] at hH
  have hsum : b.pressure t = p t + correction := by dsimp only [correction]; abel
  rw [b.potential_eq props ht, hsum, hH, _root_.add_apply, inner_add_right]
  exact add_le_add le_rfl (hCorr t ht x v)

/-- The pressure condition used by the exact Fourier cutoff stage. -/
theorem potential_hessian_upper_at_stepScale (hP : 1 ≤ P)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (props : PhysicalApproximationProperties b) (hp : ∀ t ∈ TimeSlab(T), ContDiff ℝ 2 (p t))
    {freq leading higher mean Cstep : ℝ} (hfreq : 1 ≤ freq) (hHigher₀ : 0 ≤ higher) (hMean₀ : 0 ≤ mean)
    (hStep : leading + higher + mean ≤ Cstep)
    (hLead : ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
        (leading * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2)
    (hHigher : ∀ t ∈ TimeSlab(T), ∀ x,
      ‖fderiv ℝ (gradient (b.higherOscillatoryPressure t)) x‖ ≤ higher * freq ^ (-5 / 12 : ℝ))
    (hMean : ∀ t ∈ TimeSlab(T), ∀ x,
      ‖fderiv ℝ (gradient (b.meanPressure t)) x‖ ≤ mean * freq ^ (-5 / 2 : ℝ)) :
    ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.potential props t).lift) x v⟫_ℝ ≤
        ⟪v, fderiv ℝ (gradient (p t)) x v⟫_ℝ +
          (Cstep * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  intro t ht x v
  have h := b.potential_hessian_upper_of_pressureCorrection props hp
    (b.pressureCorrection_hessian_upper_at_stepScale hP hX hU hper hfreq hHigher₀ hMean₀
      hLead hHigher hMean) t ht x v
  have hfreq₀ : 0 ≤ freq := zero_le_one.trans hfreq
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hStep (Real.rpow_nonneg hfreq₀ _)) (sq_nonneg _)))

set_option maxHeartbeats 1000000 in
/-- Specialize the leading estimate to the exact pressure of a later wave
stored by the physical approximation. -/
theorem leadingPressure_hessian_upper_of_seed
    {center : ℝ → Vec3} {t₀ ell D C r h freq B K : ℝ}
    (seed : LocalizedAmplitude.SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C)
    (reg : seed.HierarchyRegularity r h)
    (hSeed : b.leading.output.p = seed.twistedPressure reg k)
    (hX : IsLabelFlowOn U X TimeSlab(T)) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ TimeSlab(T), SpatiallyPeriodic (U t))
    (hBud : ∀ t ∈ TimeSlab(T), seed.PrimaryPressureBudget (fun u => X u 0) k r h t freq B K) :
    ∀ t ∈ TimeSlab(T), ∀ x v,
      ⟪v, fderiv ℝ (gradient (b.leadingPressure t)) x v⟫_ℝ ≤
        ((2 * B ^ 3 + (3 * B ^ 4 + B ^ 2) * K) * freq ^ (-1 / 4 : ℝ)) * ‖v‖ ^ 2 := by
  intro t ht x v
  have hEval : b.leadingPressure t = graphRead (fun u => X u 0) (seed.twistedPressure reg k) t :=
    congrArg (fun f : SP => graphRead (fun u => X u 0) f t) hSeed
  rw [hEval]
  exact LocalizedAmplitude.SeedOn.twistedPressure_parentGraph_hessian_upper
    (U := U) (X := X) (k := k) (seed := seed) reg hX hU hper ht (hBud t ht) x v

end HierarchyTwistedProfile.PhysicalApproximationData

end

end TorusEuler

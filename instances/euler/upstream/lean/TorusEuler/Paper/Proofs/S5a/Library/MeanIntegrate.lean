import TorusEuler.PaperPhysicalMeanStatements

/-!
# S5a library: a smooth mean solution solves the integrated endpoint system

Copy, for the glue passage "(4.9) is the linearized momentum equation (4.11) integrated once in
time" (`sections/06b_mean_inverse.tex:136-139`; ledger decision D5, glue), of the library
`PaperSmoothMeanSolution.exists_integratedSolution` (`PaperPhysicalMeanStatements.lean:357`) and
its private helper `PaperSmoothMeanSolution.kinetic_derivative` (:308). Change: the coefficient
package `k : PaperMeanPhysicalCoefficients hT p` (whose construction needs `T ≤ 1` and the mixed
coercivity) is replaced by the four properties of its curves that the proof uses
(`K`, `Ω` smooth curves in `C^{0,1/2}` with lifts `p.kinetic`, `p.vorticity`); the proofs are
otherwise the same.
-/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S5a

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

local instance meanIntegrateSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance meanIntegrateSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- A jointly smooth field on the slab is smooth in the label at each time of `[0,T]`
(copy of the private `paperMean_slice_spatial`). -/
theorem meanInt_slice_spatial {T : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) {t : ℝ} (ht : t ∈ J(T)) :
    ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- A jointly smooth field on the slab is smooth in time at each label (copy of the private
`paperMean_slice_time`). -/
theorem meanInt_slice_time {T : ℝ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T)) (x : Vec3) :
    ContDiffOn ℝ ∞ (fun t => f t x) J(T) :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ x⟩)

/-- Copy of the private `PaperSmoothMeanSolution.kinetic_derivative`: the time derivative of
`K v` along a smooth mean solution. -/
theorem kinetic_derivative_of_smooth {T D L : ℝ}
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
    have hdiff := (meanInt_slice_time s.mean_smooth x).differentiableOn (by simp) t ht
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
/-- **A smooth mean solution solves the integrated endpoint problem** (the glue passage
"(4.9) is (4.11) integrated once in time", `sections/06b_mean_inverse.tex:136-139`): for the
curves `K`, `Ω` of (4.1) in `C^{0,1/2}` (smooth in time, with lifts `p.kinetic`, `p.vorticity`) and
the integrated source `src` of a smooth force, the label velocity of a smooth solution of the
mean equation is the velocity of a `PaperMeanIntegratedSolution`. Copy of
`PaperSmoothMeanSolution.exists_integratedSolution` with `k` replaced by its four used
fields. -/
theorem integratedSolution_of_smooth {T D L : ℝ}
    (hT : 0 < T) {p : PaperMeanParent T D L} {force : Velocity}
    (s : PaperSmoothMeanSolution p force) (K Ω : ℝ → K½)
    (hKs : ContDiffOn ℝ ∞ K J(T)) (hΩs : ContDiffOn ℝ ∞ Ω J(T))
    (hKe : ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (K t) = p.kinetic t x)
    (hΩe : ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (Ω t) = p.vorticity t x)
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T))
    (src : ℝ → C½) (hsrc : ContDiffOn ℝ ∞ src J(T))
    (hSource : ∀ t ∈ J(T), ∀ x,
      HalfHolder.eval (toUnitTorus x) (src t) = endpointPhysicalForcePrimitive p.F force (t, x)) :
    ∃ u : PaperMeanIntegratedSolution T K Ω src,
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
        (meanInt_slice_spatial s.velocity_smooth ht) (hEval t ht)).mpr (s.divergence_eq t ht))
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
      (meanInt_slice_time s.velocity_smooth x).continuousOn.intervalIntegrable_of_Icc hT.le
    calc
      _ = ∫ r in (0 : ℝ)..T, s.velocity r x :=
        intervalIntegral.integral_congr (by rwa [uIcc_of_le hT.le])
      _ = s.displacement T x - s.displacement 0 x :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT.le
          (meanInt_slice_time s.displacement_smooth x).continuousOn
          (fun r hr => (s.displacement_derivative r (Ioo_subset_Icc_self hr) x).hasDerivAt
            (mem_of_superset (isOpen_Ioo.mem_nhds hr) Ioo_subset_Icc_self)) hVelocity
      _ = 0 := by rw [s.initial, s.terminal]; simp
  let ΩV (t : ℝ) := (Ω t).coefficientMul (V t)
  let R (t : ℝ) : C½ := (K t).coefficientMul (V t) - endpointPrimitive ΩV t + src t
  have hΩV : ContDiffOn ℝ ∞ ΩV J(T) := (HalfHolder.contDiffOn_coefficientMul hΩs).clm_apply hV
  have hKc := (HalfHolder.contDiffOn_coefficientMul hKs).clm_apply hV
  have hJ := contDiffOn_endpointPrimitive_succ (n := 0) hT (hΩV.of_le (by simp))
  have hRc : ContDiffOn ℝ 1 R J(T) := (hKc.of_le (by simp)).sub hJ |>.add (hsrc.of_le (by simp))
  have hRlift (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (R t) =
        p.kinetic t x (s.velocity t x) -
        endpointPrimitive (fun r => p.vorticity r x (s.velocity r x)) t +
        endpointPhysicalForcePrimitive p.F force (t, x) := by
    let ev : C½ →L[ℝ] Vec3 := HalfHolder.eval (toUnitTorus x)
    unfold R
    rw [map_add, map_sub, HalfHolder.eval_coefficientMul, hKe t ht x, hEval t ht x,
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
      change HalfHolder.eval (toUnitTorus x) ((Ω r).coefficientMul (V r)) = _
      rw [HalfHolder.eval_coefficientMul, hΩe r hr' x, hEval r hr' x]
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
        change Ωv r = ev ((Ω r).coefficientMul (V r))
        rw [HalfHolder.eval_coefficientMul, hΩe r hr x, hEval r hr x]
      have hg : ContinuousOn g J(T) :=
        ((ContinuousLinearMap.adjoint : Coframe ≃ₗᵢ[ℝ] Coframe).continuous.comp_continuousOn
          (fun r hr => (p.deformation_ode (toUnitTorus x) r hr).continuousWithinAt)).clm_apply
          (meanInt_slice_time hforce x).continuousOn
      have hK := kinetic_derivative_of_smooth s ht x
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
      (meanInt_slice_spatial s.pressure_smooth ht).neg, fun n x => congrArg Neg.neg ((s.periodic t ht).2.2.2 n x)⟩
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
      P (paperMeanIntegratedMomentum K Ω src v t) = P (R 0) := by
    unfold paperMeanIntegratedMomentum
    rw [hVeq t ht]
    have hI : endpointPrimitive (fun r => (Ω r).coefficientMul (v r).val) t = endpointPrimitive ΩV t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro r hr
      change (Ω r).coefficientMul (v r).val = (Ω r).coefficientMul (V r)
      rw [hVeq r (Icc_subset_Icc_right ht.2 hr)]
    rw [hI]
    exact hConst t ht
  exact ⟨⟨v, P (R 0), hvc, hEnd, hEq⟩, fun t ht x => by
    rw [hVeq t ht, hEval t ht]⟩

end

end TorusEuler.Paper.Lib.S5a

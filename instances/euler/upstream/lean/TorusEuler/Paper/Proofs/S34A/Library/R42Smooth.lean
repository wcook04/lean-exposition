import TorusEuler.Paper.Proofs.S34A.Library.R42Scale
import TorusEuler.EndpointPhysicalMeanSolve

/-! Glue for the proof of **Theorem 4.2** (package S34A): smoothness of curves in
`C^{0,1/2}` from joint smoothness of their periodic lifts, and the time derivative of a
jointly smooth displacement. No numbered result is used. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance r42SmoothSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance r42SmoothSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- A curve whose periodic lift is a jointly smooth function on the closed slab is a
smooth curve in `C^{0,1/2}` (through `exists_endpointSlabHalfHolderJets`). -/
theorem contDiffOn_curve_of_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {T : ℝ} (hT : 0 < T) (K : ℝ → HalfHolder A E) (f : ℝ × Vec3 → E)
    (hf : ContDiffOn ℝ ∞ f Slab(T))
    (hper : ∀ t ∈ Icc (0 : ℝ) T, SpatiallyPeriodic fun x => f (t, x))
    (hK : ∀ t ∈ Icc (0 : ℝ) T, ∀ x, HalfHolder.eval (toUnitTorus x) (K t) = f (t, x)) :
    ContDiffOn ℝ ∞ K (Icc 0 T) := by
  obtain ⟨J⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection f hf hper
  refine (J.smooth []).congr fun t ht => ?_
  apply HalfHolder.ext
  intro a
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
  rw [hK t ht x]
  exact (J.eval_lift [] t ht x).symm

/-- The periodic lift of a curve in `C^{0,1/2}` is periodic. -/
theorem spatiallyPeriodic_lift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HalfHolder A E) : SpatiallyPeriodic fun x : Vec3 => HalfHolder.eval (toUnitTorus x) f := by
  intro n x
  change HalfHolder.eval (toUnitTorus (x + latticeVector n)) f = _
  rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]

/-- A solenoidal curve whose lift is jointly smooth is smooth as a curve in the
divergence-free subspace (the strong Leray projection fixes the subspace). -/
theorem contDiffOn_solenoidal_of_lift {T : ℝ} (hT : 0 < T) (g : ℝ → S)
    (hg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (g z.1 : C½))
      Slab(T)) :
    ContDiffOn ℝ ∞ g (Icc 0 T) := by
  have hc : ContDiffOn ℝ ∞ (fun t => (g t : C½)) (Icc 0 T) :=
    contDiffOn_curve_of_lift hT (fun t => (g t : C½)) _ hg
      (fun t _ => spatiallyPeriodic_lift (g t : C½)) (fun _ _ _ => rfl)
  refine (endpointStrongSpatialProjection.contDiff.comp_contDiffOn hc).congr fun t _ => ?_
  exact (Subtype.ext ((endpointStrongSpatialLeray_fixed_iff _).mpr (g t).property)).symm

/-- The time slice derivative of a jointly smooth field (copy of the private
`hasDerivWithinAt_time_slice_of_joint`, EndpointPhysicalMeanSolve.lean:58; glue). -/
theorem hasDerivWithinAt_timeSlice {T t : ℝ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : ℝ → Vec3 → E}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) Slab(T)) (ht : t ∈ Icc (0 : ℝ) T) (x : Vec3) :
    HasDerivWithinAt (fun r => v r x)
      (fderivWithin ℝ (Function.uncurry v) Slab(T) (t, x) (1, 0)) (Icc 0 T) t := by
  have hline : HasDerivWithinAt (fun r : ℝ => (r, x)) (1, 0) (Icc 0 T) t :=
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t x)).hasDerivWithinAt
  have htx : (t, x) ∈ Slab(T) := ⟨ht, mem_univ x⟩
  have h := (hv.differentiableOn (by simp) (t, x) htx).hasFDerivWithinAt
  have hmap : MapsTo (fun r : ℝ => (r, x)) (Icc 0 T) Slab(T) := fun _ hr => ⟨hr, mem_univ x⟩
  exact h.comp_hasDerivWithinAt t hline hmap

/-- The time derivative of a jointly smooth field is jointly smooth (copy of the private
`contDiffOn_jointTimeDerivative`, EndpointPhysicalMeanSolve.lean:70; glue). -/
theorem contDiffOn_timeDerivative {T : ℝ} (hT : 0 < T) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {v : ℝ → Vec3 → E}
    (hv : ContDiffOn ℝ ∞ (Function.uncurry v) Slab(T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 =>
      fderivWithin ℝ (Function.uncurry v) Slab(T) z (1, 0)) Slab(T) :=
  (hv.fderivWithin ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) (by simp)).clm_apply
    contDiffOn_const

/-- If a solenoidal displacement `z` with `z_t = v` has a jointly smooth lift, so does `v`. -/
theorem contDiffOn_lift_velocity {T : ℝ} (hT : 0 < T) {z v : ℝ → S}
    (hz : ∀ t ∈ Icc (0 : ℝ) T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (hzs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
      Slab(T)) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (v q.1 : C½))
      Slab(T) := by
  let Z : ℝ → Vec3 → Vec3 := fun t x => HalfHolder.eval (toUnitTorus x) (z t : C½)
  have hZ : ContDiffOn ℝ ∞ (Function.uncurry Z) Slab(T) := hzs
  refine (contDiffOn_timeDerivative hT hZ).congr fun q hq => ?_
  let ev := (HalfHolder.eval (toUnitTorus q.2)).comp endpointHalfHolderSolenoidal.subtypeL
  have h1 : HasDerivWithinAt (fun r => Z r q.2) (ev (v q.1)) (Icc 0 T) q.1 :=
    ev.hasFDerivAt.comp_hasDerivWithinAt q.1 (hz q.1 hq.1)
  have h2 := hasDerivWithinAt_timeSlice hZ hq.1 q.2
  exact (h1.derivWithin (uniqueDiffOn_Icc hT q.1 hq.1)).symm.trans
    (h2.derivWithin (uniqueDiffOn_Icc hT q.1 hq.1))

/-- The derivative of an integrated source (copy of the private
`eval_endpointSourceDerivative`, EndpointPhysicalMeanSolve.lean:608; glue). -/
theorem eval_sourceDerivative {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc (0 : ℝ) T)
    (a : A) (src : ℝ → C½) (f : ℝ → Vec3)
    (hs : ContDiffOn ℝ 1 src (Icc 0 T)) (hf : ContinuousOn f (Icc 0 T))
    (hEval : ∀ r ∈ Icc (0 : ℝ) T, HalfHolder.eval a (src r) = -endpointPrimitive f r) :
    HalfHolder.eval a (derivWithin src (Icc 0 T) t) = -f t := by
  have hd : HasDerivWithinAt (fun r => HalfHolder.eval a (src r))
      (HalfHolder.eval a (derivWithin src (Icc 0 T) t)) (Icc 0 T) t :=
    (HalfHolder.eval a).hasFDerivAt.comp_hasDerivWithinAt t
      ((hs.differentiableOn_one t ht).hasDerivWithinAt)
  have hd' := hd.congr (fun r hr => (hEval r hr).symm) (hEval t ht).symm
  have hInt := (hasDerivWithinAt_endpointPrimitive_of_continuousOn hf ht).neg
  exact (hd'.derivWithin (uniqueDiffOn_Icc hT t ht)).symm.trans
    (hInt.derivWithin (uniqueDiffOn_Icc hT t ht))

end

end TorusEuler.Paper.Lib.S34A

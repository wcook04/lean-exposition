import TorusEuler.Paper.Proofs.S5a.Library.MeanUnique

/-!
# The mean equation (5.11) in Eulerian coordinates (4.12), from Theorem 4.2

`sections/08_exact_wave.tex:233-240`: "In Eulerian coordinates the sum is the linearized Euler
equation (4.12) for `W̄^♮` over `U`, with the pressure `∑q̄_p^♮` and the source
`(∑f̄_p)^♮`". `exists_mean_eulerian` is a copy of the glue `Lib.S5a.meanSolvable_of_theorem42`
(solvability of (5.11) from the smooth-force item of `h4_2`) that keeps the conjunct of that item
that the original discards: `div b = 0` and (4.12) for `b = B∘X⁻¹`, `q = q̄∘X⁻¹`;
`meanSolution_sum` is linearity of (5.11), and `fderivWithin_slab_direction` rewrites the
material derivative of (4.12), `∂_{(1,u)}` on the slab, as `∂_t b + (Db)u`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open HierarchyTwistedProfile Lib.S5a

noncomputable section

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)

local instance meanEulerSolenoidalNormedGroup : NormedAddCommGroup endpointHalfHolderSolenoidal :=
  inferInstance

local instance meanEulerSolenoidalNormedSpace : NormedSpace ℝ endpointHalfHolderSolenoidal :=
  inferInstance

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure}
  {D lam : ℝ}

/-- The Eulerian form of a solution `(B, q̄)` of (5.11) with source `f̄`: `b = B∘X⁻¹`,
`q = q̄∘X⁻¹`, `f = f̄∘X⁻¹` are smooth and periodic, `div b = 0`, and the linearized Euler
equation (4.12) holds, with the material derivative `∂_{(1,U)}` taken on the closed slab. -/
def EulerMean (U : Velocity) (X : ℝ → Velocity) (f B : HierarchyTwistedProfile T k Vec3)
    (q : HierarchyTwistedProfile T k ℝ) : Prop :=
  ContDiffOn ℝ ∞ (Function.uncurry fun t x => B.val.val.val (t, X t 0 x, 0))
      (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ContDiffOn ℝ ∞ (Function.uncurry fun t x => q.val.val.val (t, X t 0 x, 0))
      (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    (∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => B.val.val.val (t, X t 0 x, 0)) ∧
      SpatiallyPeriodic (fun x => q.val.val.val (t, X t 0 x, 0))) ∧
    ∀ t ∈ Icc 0 T, ∀ x, divergence (fun y => B.val.val.val (t, X t 0 y, 0)) x = 0 ∧
      fderivWithin ℝ (Function.uncurry fun t x => B.val.val.val (t, X t 0 x, 0))
          (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) (1, U t x) +
        fderiv ℝ (U t) x (B.val.val.val (t, X t 0 x, 0)) +
        gradient (fun y => q.val.val.val (t, X t 0 y, 0)) x = f.val.val.val (t, X t 0 x, 0)

set_option maxHeartbeats 6400000 in
/-- **The mean equation (5.11) is solvable, with the Eulerian form (4.12)** (copy of
`Lib.S5a.meanSolvable_of_theorem42`, `06d_mean_estimates.tex:3-14`, keeping the conjunct of the
smooth-force item of Theorem 4.2 that the copy discarded): for a phase-independent source `f̄`
there is a normalized solution `(B, q̄)` of (5.11) for which `b = B∘X⁻¹`, `q = q̄∘X⁻¹` and
`f = f̄∘X⁻¹` satisfy `div b = 0` and the linearized Euler equation (4.12), the latter two being
the conclusions of `h4_2` for the solution of (4.9) that gives `(B, q̄)`. -/
theorem exists_mean_eulerian (h4_2 : Statement.theorem_4_2) (d : ParentGeometry hT U X k)
    (hP : S5.Parent T U X pU D lam) {f : HierarchyTwistedProfile T k Vec3}
    (hf : (S5.ops d).average f = f) :
    ∃ (B : HierarchyTwistedProfile T k Vec3) (q : HierarchyTwistedProfile T k ℝ),
      S5.MeanSolution d f B q ∧ (∀ t ∈ Icc 0 T, (∫ a in centeredCell, q.val.val.val (t, a, 0)) = 0) ∧
      EulerMean U X f B q := by
  have h0 : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.velocity_smooth.of_le (by simp)
  have hD1 : 1 ≤ D := Bridge.Parent.scale_ge_one hP
  obtain ⟨C, p, -, h42⟩ := h4_2
  obtain ⟨hKper, hΩper, K₀, K₁, Ω₀, Ω₁, hK₀, hK₁, hΩ₀, hΩ₁⟩ := exists_meanCoefficient_bounds hT hP
  obtain ⟨Kc, hKc⟩ := exists_halfHolder_curve hT (meanKinetic X) (meanKinetic_smooth hT hP) hKper
  obtain ⟨Ωc, hΩc⟩ := exists_halfHolder_curve hT (meanVorticity U X) (meanVorticity_smooth hT hP)
    hΩper
  have H := h42 T U X (meanParentFlow_of_parent hT hP) (meanHsharp_le_of_parent hT hP) D D K₀ K₁
    Ω₀ Ω₁ hD1 (fun t ht a => hP.inverse_deformation_le t ht a)
    (fun t ht a => hP.gradient_le t ht _) hK₀ hK₁ hΩ₀ hΩ₁ Kc Ωc hKc hΩc
  dsimp only at H
  obtain ⟨-, hsmooth, -⟩ := H
  -- the phase-independent source on the label cell, and its Eulerian form `f = f̄∘X⁻¹`
  have hfs : ContDiffOn ℝ ∞ f.val.val.val (hierarchyProfileSlab T) :=
    HierarchySmoothProfile.smooth f.val.val
  have hfind : ∀ t ∈ Icc 0 T, ∀ a s, f.val.val.val (t, a, s) = f.val.val.val (t, a, 0) :=
    fun t ht a s => Bridge.phaseIndependent_of_average_eq d hf (t, a, 0) ⟨ht, mem_univ _⟩ s
  have hfper : ∀ t ∈ Icc 0 T, ∀ (n : Fin 3 → ℤ) a,
      f.val.val.val (t, a + latticeVector n, 0) = f.val.val.val (t, a, 0) :=
    fun t ht n a => meanProfile_periodic d hf ht 0 0 n a
  have hinvX := hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  have hfwdX := hP.flow.contDiffOn_forwardLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  have hFsm := hP.flow.contDiffOn_forwardLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  have hGsm := hP.flow.contDiffOn_inverseLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  let fE : Velocity := fun t x => f.val.val.val (t, X t 0 x, 0)
  have hfE : ContDiffOn ℝ ∞ (Function.uncurry fE) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hfs.comp (contDiffOn_fst.prodMk (hinvX.prodMk contDiffOn_const))
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hfEper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fE t) := by
    intro t ht n x
    change f.val.val.val (t, X t 0 (x + latticeVector n), 0) = f.val.val.val (t, X t 0 x, 0)
    rw [parent_flow_lattice hT hP ht h0 n x, hfper t ht n]
  -- the source `L = -∫_0^t (D_aX)^T f̄` of (4.9) as a curve in `C^{0,1/2}`
  let w : ℝ → Vec3 → Vec3 := fun r x => (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0))
  have hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    have adj : ContDiff ℝ ∞ (fun F : Vec3 →L[ℝ] Vec3 => F.adjoint) :=
      (ContinuousLinearMap.adjoint : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ⋆[ℝ] (Vec3 →L[ℝ] Vec3)).contDiff
    have hf0 : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => f.val.val.val (z.1, z.2, 0))
        (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      hfs.comp (contDiffOn_fst.prodMk (contDiffOn_snd.prodMk contDiffOn_const))
        (fun z hz => ⟨hz.1, mem_univ _⟩)
    exact (adj.comp_contDiffOn hFsm).clm_apply hf0
  let g : ℝ → Vec3 → Vec3 := fun t x => -endpointPrimitive (fun r => w r x) t
  have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (contDiffOn_endpointPhysicalJointPrimitive hT hw).neg
  have hgper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (g t) := by
    intro t ht n x
    change -endpointPrimitive (fun r => w r (x + latticeVector n)) t =
      -endpointPrimitive (fun r => w r x) t
    unfold endpointPrimitive
    refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
    rw [uIcc_of_le ht.1] at hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    change (fderiv ℝ (X 0 r) (x + latticeVector n)).adjoint
        (f.val.val.val (r, x + latticeVector n, 0)) =
      (fderiv ℝ (X 0 r) x).adjoint (f.val.val.val (r, x, 0))
    have h1 : fderiv ℝ (X 0 r) (x + latticeVector n) = fderiv ℝ (X 0 r) x :=
      parent_deformation_periodic hT hP hr' n x
    rw [h1, hfper r hr' n x]
  obtain ⟨src, hsrcv⟩ := exists_halfHolder_curve hT g hg hgper
  have hsrc : ∀ t ∈ Icc 0 T, ∀ a, HalfHolder.eval (toUnitTorus a) (src t) =
      -∫ s in (0 : ℝ)..t, (meanDeformation X s a).adjoint (fE s (X 0 s a)) := by
    intro t ht a
    rw [hsrcv t ht a]
    change -endpointPrimitive (fun r => w r a) t = _
    unfold endpointPrimitive
    refine congrArg Neg.neg (intervalIntegral.integral_congr fun r hr => ?_)
    rw [uIcc_of_le ht.1] at hr
    have hr' : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans ht.2⟩
    change (fderiv ℝ (X 0 r) a).adjoint (f.val.val.val (r, a, 0)) =
      (fderiv ℝ (X 0 r) a).adjoint (f.val.val.val (r, X r 0 (X 0 r a), 0))
    rw [parent_flow_left_inverse hT hP hr' a]
  -- Theorem 4.2: a solution of (4.9), its smoothness and (4.11)
  obtain ⟨⟨z, v, c, φ, G, hsol⟩, hall⟩ := hsmooth fE hfE hfEper src hsrc
  have hprop := hall z v c φ G hsol
  obtain ⟨hz, -, qL, hqL, hqLper, hmom, hb, hq4, hper4, heq4⟩ := hprop
  let vl : Velocity := fun t a => HalfHolder.eval (toUnitTorus a) (v t : C½)
  let B : Velocity := fun t a =>
    meanDeformation X t (X t 0 (X 0 t a)) (vl t (X t 0 (X 0 t a)))
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hb.comp (contDiffOn_fst.prodMk hfwdX) (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hBval : ∀ t ∈ Icc 0 T, ∀ a, B t a = fderiv ℝ (X 0 t) a (vl t a) := by
    intro t ht a
    change meanDeformation X t (X t 0 (X 0 t a)) (vl t (X t 0 (X 0 t a))) = _
    rw [parent_flow_left_inverse hT hP ht a]
    rfl
  have hBper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (B t) := by
    intro t ht n a
    rw [hBval t ht, hBval t ht]
    have h1 : fderiv ℝ (X 0 t) (a + latticeVector n) = fderiv ℝ (X 0 t) a :=
      parent_deformation_periodic hT hP ht n a
    rw [h1]
    exact congrArg _ (halfHolder_lift_periodic (v t : C½) n a)
  have hinv : ∀ t ∈ Icc 0 T, ∀ a,
      (fderiv ℝ (X t 0) (X 0 t a)).comp (fderiv ℝ (X 0 t) a) = .id ℝ Vec3 ∧
        (fderiv ℝ (X 0 t) a).comp (fderiv ℝ (X t 0) (X 0 t a)) = .id ℝ Vec3 :=
    fun t ht a => hP.flow.labelDerivative_inverse hT hU2 hP.velocity_periodic h0 ht a
  have hvl : ContDiffOn ℝ ∞ (Function.uncurry vl) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
    refine (hGsm.clm_apply hB).congr fun z hz => ?_
    change vl z.1 z.2 = fderiv ℝ (X z.1 0) (X 0 z.1 z.2) (B z.1 z.2)
    rw [hBval z.1 hz.1 z.2, ← ContinuousLinearMap.comp_apply, (hinv z.1 hz.1 z.2).1]
    rfl
  let Bp : HierarchyTwistedProfile T k Vec3 := ofLabelField k B hB hBper
  let qp : HierarchyTwistedProfile T k ℝ :=
    ofLabelField k qL hqL (fun t ht => (hqLper t ht).1)
  have hBp : ∀ t ∈ Icc 0 T, ∀ a s, Bp.val.val.val (t, a, s) = B t a := fun t ht a s =>
    ofLabelField_eval k B hB hBper (x := (t, a, s)) ⟨ht, mem_univ _⟩
  have hqp : ∀ t ∈ Icc 0 T, ∀ a s, qp.val.val.val (t, a, s) = qL t a := fun t ht a s =>
    ofLabelField_eval k qL hqL (fun t ht => (hqLper t ht).1) (x := (t, a, s)) ⟨ht, mem_univ _⟩
  refine ⟨Bp, qp, ⟨?_, ?_, ?_, ?_⟩, fun t ht => ?_, ?_⟩
  · -- (5.11): `B_t + MB + 𝐝q̄ = f̄` from (4.11)
    refine HierarchyTwistedProfile.ext fun x hx => ?_
    obtain ⟨t, a, s⟩ := x
    have ht : t ∈ Icc 0 T := hx.1
    let F := fderiv ℝ (X 0 t) a
    let Gi := fderiv ℝ (X t 0) (X 0 t a)
    let M := fderiv ℝ (U t) (X 0 t a)
    have hFd : HasDerivWithinAt (fun r => fderiv ℝ (X 0 r) a) (M.comp F) (Icc 0 T) t :=
      (hP.flow.labelDerivative_evolves hT hU2 hP.velocity_periodic h0 a).2 t ht
    have hvd : HasDerivWithinAt (fun r => vl r a) (derivWithin (fun r => vl r a) (Icc 0 T) t)
        (Icc 0 T) t :=
      ((meanTimeSlice_contDiffOn hvl a).differentiableOn (by simp) t ht).hasDerivWithinAt
    have hBd : HasDerivWithinAt (fun r => Bp.val.val.val (r, a, s))
        ((M.comp F) (vl t a) + F (derivWithin (fun r => vl r a) (Icc 0 T) t)) (Icc 0 T) t := by
      refine (hFd.clm_apply hvd).congr (fun r hr => ?_) ?_
      · rw [hBp r hr a s, hBval r hr a]
      · rw [hBp t ht a s, hBval t ht a]
    have hlab : ((S5.ops d).labelGrad qp).val.val.val (t, a, s) = Gi.adjoint (gradient (qL t) a) := by
      change (HierarchySmoothProfile.labelGradient hT d.inverse.val.val qp.val.val).val (t, a, s) = _
      rw [HierarchySmoothProfile.labelGradient_eq_adjoint_gradient hT d.inverse.val.val qp.val.val ht
        a s, d.inverse_value (t, a, s) hx]
      have hq' : (fun y => qp.val.val.val (t, y, s)) = qL t := funext fun y => hqp t ht y s
      change Gi.adjoint (gradient (fun y => qp.val.val.val (t, y, s)) a) = _
      rw [hq']
    have hm := hmom t ht a
    have hFd' : HasDerivWithinAt (fun r => meanDeformation X r a) (M.comp F) (Icc 0 T) t := hFd
    rw [hFd'.derivWithin (uniqueDiffOn_Icc hT t ht)] at hm
    change kineticForm F (derivWithin (fun r => vl r a) (Icc 0 T) t) + gradient (qL t) a =
      F.adjoint (fE t (X 0 t a)) - (2 : ℝ) • F.adjoint ((M.comp F) (vl t a)) at hm
    have hGF : ∀ y : Vec3, Gi.adjoint (F.adjoint y) = y := by
      intro y
      rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.adjoint_comp, (hinv t ht a).2,
        ContinuousLinearMap.adjoint_id]
      rfl
    have hfE0 : fE t (X 0 t a) = f.val.val.val (t, a, s) := by
      change f.val.val.val (t, X t 0 (X 0 t a), 0) = _
      rw [parent_flow_left_inverse hT hP ht a, ← hfind t ht a s]
    have hm' := congrArg Gi.adjoint hm
    rw [map_add, map_sub, map_smul, kineticForm, ContinuousLinearMap.comp_apply, hGF, hGF, hGF,
      hfE0] at hm'
    change ((S5.ops d).material Bp).val.val.val (t, a, s) +
      ((S5.ops d).labelGrad qp).val.val.val (t, a, s) = f.val.val.val (t, a, s)
    rw [Bridge.ops_material_eval d Bp hx, hlab, hBd.derivWithin (uniqueDiffOn_Icc hT t ht)]
    change (M.comp F) (vl t a) + F (derivWithin (fun r => vl r a) (Icc 0 T) t) +
        M (Bp.val.val.val (t, a, s)) + Gi.adjoint (gradient (qL t) a) = _
    rw [hBp t ht a s, hBval t ht a]
    rw [eq_sub_iff_add_eq] at hm'
    change (M.comp F) (vl t a) + F (derivWithin (fun r => vl r a) (Icc 0 T) t) +
        M (F (vl t a)) + Gi.adjoint (gradient (qL t) a) = _
    rw [← hm', ContinuousLinearMap.comp_apply, two_smul]
    abel
  · -- `B` is independent of the phase
    refine HierarchyTwistedProfile.ext fun x hx => ?_
    rw [Bridge.ops_average_eval d Bp hx]
    have hc : (fun z => Bp.val.val.val (x.1, x.2.1, z)) = fun _ => B x.1 x.2.1 :=
      funext fun z => hBp x.1 hx.1 x.2.1 z
    rw [hc, phaseMean_const, ← hBp x.1 hx.1 x.2.1 x.2.2]
  · -- `q̄` is independent of the phase
    refine HierarchyTwistedProfile.ext fun x hx => ?_
    rw [Bridge.ops_phaseGrad_eval d qp hx]
    have hc : (fun z => qp.val.val.val (x.1, x.2.1, z)) = fun _ => qL x.1 x.2.1 :=
      funext fun z => hqp x.1 hx.1 x.2.1 z
    rw [hc, deriv_const, zero_smul]
    rfl
  · -- the endpoint data `B = D_aX v`, `v = z_t`, `div_a v = 0`, `z(0) = z(T) = 0`
    let zl : Velocity := fun t a => HalfHolder.eval (toUnitTorus a) (z t : C½)
    refine ⟨vl, zl, hvl, hz, fun t _ => ⟨halfHolder_lift_periodic _, halfHolder_lift_periodic _⟩,
      ?_, ?_, fun t ht a => ?_, fun t ht a => ?_, fun t ht a s => ?_⟩
    · funext a
      change HalfHolder.eval (toUnitTorus a) (z 0 : C½) = 0
      rw [hsol.initial]
      exact map_zero _
    · funext a
      change HalfHolder.eval (toUnitTorus a) (z T : C½) = 0
      rw [hsol.terminal]
      exact map_zero _
    · let L := (HalfHolder.eval (toUnitTorus a)).comp endpointHalfHolderSolenoidal.subtypeL
      exact L.hasFDerivAt.comp_hasDerivWithinAt t (hsol.displacement_deriv t ht)
    · have hvl' : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity v))
          (Icc 0 T ×ˢ (univ : Set Vec3)) := hvl
      exact divergence_endpointPhysicalLabelVelocity v hvl' ht a
    · rw [hBp t ht a s, hBval t ht a]
  · -- the normalization of `𝗊`
    rw [← (hqLper t ht).2]
    congr 1
    funext a
    exact hqp t ht a 0
  · -- the Eulerian form (4.12) of the solution
    let b4 : Velocity := fun t x => meanDeformation X t (X t 0 x) (vl t (X t 0 x))
    let q4 : Pressure := fun t x => qL t (X t 0 x)
    have hbE : ∀ t ∈ Icc 0 T, ∀ x, Bp.val.val.val (t, X t 0 x, 0) = b4 t x := by
      intro t ht x
      rw [hBp t ht _ 0, hBval t ht]
      rfl
    have hqE : ∀ t ∈ Icc 0 T, ∀ x, qp.val.val.val (t, X t 0 x, 0) = q4 t x :=
      fun t ht x => hqp t ht _ 0
    have hb4 : ContDiffOn ℝ ∞ (Function.uncurry b4) (Icc 0 T ×ˢ (univ : Set Vec3)) := hb
    have hq4' : ContDiffOn ℝ ∞ (Function.uncurry q4) (Icc 0 T ×ˢ (univ : Set Vec3)) := hq4
    refine ⟨?_, ?_, ?_, ?_⟩
    · refine hb4.congr fun z hz => ?_
      obtain ⟨t, x⟩ := z
      exact hbE t hz.1 x
    · refine hq4'.congr fun z hz => ?_
      obtain ⟨t, x⟩ := z
      exact hqE t hz.1 x
    · intro t ht
      have e1 : (fun x => Bp.val.val.val (t, X t 0 x, 0)) = b4 t := funext (hbE t ht)
      have e2 : (fun x => qp.val.val.val (t, X t 0 x, 0)) = q4 t := funext (hqE t ht)
      rw [e1, e2]
      exact hper4 t ht
    · intro t ht x
      obtain ⟨hdiv, heq⟩ := heq4 t ht x
      have e1 : (fun x => Bp.val.val.val (t, X t 0 x, 0)) = b4 t := funext (hbE t ht)
      have e2 : (fun x => qp.val.val.val (t, X t 0 x, 0)) = q4 t := funext (hqE t ht)
      have e3 : fderivWithin ℝ (Function.uncurry fun t x => Bp.val.val.val (t, X t 0 x, 0))
          (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) =
          fderivWithin ℝ (Function.uncurry b4) (Icc 0 T ×ˢ (univ : Set Vec3)) (t, x) :=
        fderivWithin_congr (fun z hz => by
          obtain ⟨t', x'⟩ := z
          exact hbE t' hz.1 x') (hbE t ht x)
      rw [e1, e2, e3, hbE t ht x]
      exact ⟨hdiv, heq⟩

end

end TorusEuler.Paper.Lib.S5c

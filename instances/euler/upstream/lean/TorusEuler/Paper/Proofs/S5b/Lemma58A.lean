import TorusEuler.Paper.Proofs.S5b.Lemma57
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.HierarchyPhysicalGraph

/-!
# Lemma 5.8, first part: smoothness, periodicity, divergence and the equation (5.46)

Glue for the proof of Lemma 5.8 (`sections/08_exact_wave.tex:108-117`): for twisted
profiles `W`, `𝖯` over a parent, the Eulerian fields `V = U + W^♮`, `Π = p_U + 𝖯^♮` are
smooth and periodic (`approx_smooth`), `V` is divergence free when `𝐝̃·W = 0`
(`approx_divergence`), and the chain rule (3.1) turns an operator identity
`W_t + MW + (W·𝐝̃)W + 𝐝̃𝖯 + R_U∘X = F` into `V_t + V·∇V + ∇Π = F^♮`
(`approx_residual`), "because `(R_U∘X)^♮ = R_U`". The operator identity is (5.29) of
Proposition 5.4, supplied by the caller from `h5_4`; the library lemmas used here are the
generic graph identities `HierarchySmoothProfile.momentumResidual_graphRead_parent`,
`HierarchySmoothProfile.divergence_transportedSmoothProfile_eq_zero` and
`HierarchySmoothProfile.contDiffOn_graphRead`.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3} {D lam : ℝ}

/-- The Eulerian fields `V = U + W^♮` and `Π = p_U + 𝖯^♮` are smooth on `[0,T] × ℝ³` and
spatially periodic (`08_exact_wave.tex:118-121`: the oscillatory terms extend smoothly and
periodically, and the profiles are jointly smooth). -/
theorem approx_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam)
    (W : HierarchyTwistedProfile T k Vec3) (Pr : HierarchyTwistedProfile T k ℝ) :
    let Y : Velocity := fun t => X t 0
    (ContDiffOn ℝ ∞ (Function.uncurry (U + graphRead Y W)) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic ((U + graphRead Y W) t)) ∧
    (ContDiffOn ℝ ∞ (Function.uncurry (pU + graphRead Y Pr)) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic ((pU + graphRead Y Pr) t)) := by
  intro Y
  have hA : ContDiffOn ℝ ∞ (Function.uncurry Y) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  refine ⟨⟨hP.velocity_smooth.add (HierarchySmoothProfile.contDiffOn_graphRead k W.val.val hA),
    fun t ht n x => ?_⟩, ⟨hP.pressure_smooth.add
      (HierarchySmoothProfile.contDiffOn_graphRead k Pr.val.val hA), fun t ht n x => ?_⟩⟩
  · change U t (x + latticeVector n) + graphRead Y W t (x + latticeVector n) =
      U t x + graphRead Y W t x
    rw [hP.velocity_periodic t ht n x,
      spatiallyPeriodic_inverseParentGraphRead hT hP.flow hP.velocity_smooth hP.velocity_periodic
        W ht n x]
  · change pU t (x + latticeVector n) + graphRead Y Pr t (x + latticeVector n) =
      pU t x + graphRead Y Pr t x
    rw [hP.pressure_periodic t ht n x,
      spatiallyPeriodic_inverseParentGraphRead hT hP.flow hP.velocity_smooth hP.velocity_periodic
        Pr ht n x]

/-- The divergence is additive on differentiable fields (copy of the private
`divergence_add`, `TorusEuler/HierarchyPhysicalApproximation.lean:241`). -/
theorem divergence_add' {f g : Vec3 → Vec3} {x : Vec3}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    divergence (f + g) x = divergence f x + divergence g x := by
  change divergence (fun y => f y + g y) x = _
  simp only [divergence, fderiv_fun_add hf hg, _root_.add_apply, PiLp.add_apply,
    Finset.sum_add_distrib]

/-- `V = U + W^♮` is divergence free when `𝐝̃·W = 0` (`08_exact_wave.tex:117`). -/
theorem approx_divergence (hT : 0 < T) (d : ParentGeometry hT U X k)
    (hP : S5.Parent T U X pU D lam) (W : HierarchyTwistedProfile T k Vec3)
    (hW : S5.totalDivergence d W = 0) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    divergence ((U + graphRead (fun r => X r 0) W) t) x = 0 := by
  have hA : ContDiffOn ℝ ∞ (Function.uncurry (fun r => X r 0)) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  have hAt : ContDiff ℝ ∞ (X t 0) := slice_contDiff hA ht
  have hUt : ContDiff ℝ ∞ (U t) := slice_contDiff hP.velocity_smooth ht
  obtain ⟨_, hChart⟩ := d.inverseGraph_values hP.flow hP.velocity_smooth hP.velocity_periodic
  have hDiv : divergence (graphRead (fun r => X r 0) W t) x = 0 :=
    HierarchySmoothProfile.divergence_transportedSmoothProfile_eq_zero hT
      d.inverse.val.val d.covector.val.val W.val.val (A := fun r => X r 0) (k := k) (x := x) ht
      ((hAt.differentiable (by simp) x).hasFDerivAt)
      (hChart t ht x _).1 (hChart t ht x _).2 hW
  have hgraph : ContDiff ℝ ∞ (graphRead (fun r => X r 0) W t) :=
    slice_contDiff (HierarchySmoothProfile.contDiffOn_graphRead k W.val.val hA) ht
  change divergence (U t + graphRead (fun r => X r 0) W t) x = 0
  rw [divergence_add' (hUt.differentiable (by simp) x) (hgraph.differentiable (by simp) x),
    hP.divergence_free t ht x, hDiv, add_zero]

set_option maxHeartbeats 800000 in
/-- **The approximate equation (5.46)** from an operator identity: if
`W_t + MW + (W·𝐝)W + (W·κ)∂_sW + 𝐝𝖯 + κ∂_s𝖯 + R = F` with `R = R_U∘X` on the slab, then
`V_t + V·∇V + ∇Π = F^♮` for `V = U + W^♮`, `Π = p_U + 𝖯^♮` (`08_exact_wave.tex:109-116`:
the chain rule (3.1) and `(R_U∘X)^♮ = R_U`). -/
theorem approx_residual (hT : 0 < T) (d : ParentGeometry hT U X k)
    (hP : S5.Parent T U X pU D lam) (W R F : HierarchyTwistedProfile T k Vec3)
    (Pr : HierarchyTwistedProfile T k ℝ)
    (hmom : (S5.ops d).material W + (S5.ops d).labelAdv W W + (S5.ops d).phaseAdv W W +
      (S5.ops d).labelGrad Pr + (S5.ops d).phaseGrad Pr + R = F)
    (hR : ∀ z ∈ hierarchyProfileSlab T,
      R.val.val.val z = momentumResidual (Icc 0 T) U pU z.1 (X 0 z.1 z.2.1))
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    momentumResidual (Icc 0 T) (U + graphRead (fun r => X r 0) W)
      (pU + graphRead (fun r => X r 0) Pr) t x = graphRead (fun r => X r 0) F t x := by
  let A : Velocity := fun r => X r 0
  let O₀ := HierarchySmoothProfile.hierarchyConcreteOperators hT d.inverse.val.val
    d.strain.val.val d.covector.val.val
  have hAreg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.flow.contDiffOn_inverseLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  have hp : DifferentiableAt ℝ (pU t) x :=
    (slice_contDiff hP.pressure_smooth ht).differentiable (by simp) x
  obtain ⟨K, hLip⟩ := Bridge.Parent.exists_lipschitz hT hP
  have hInv : X 0 t (A t x) = x := (hP.flow.inverse hLip (left_mem_Icc.mpr hT.le) ht).2 x
  have hRz : R.val.val.val (hierarchyGraphPoint A k t x) = momentumResidual (Icc 0 T) U pU t x := by
    change R.val.val.val (t, A t x, ⟪k, A t x⟫_ℝ) = _
    rw [hR _ ⟨ht, mem_univ _⟩]
    change momentumResidual (Icc 0 T) U pU t (X 0 t (A t x)) = _
    rw [hInv]
  have hEq := congrArg (fun G : HierarchyTwistedProfile T k Vec3 => G.val.val) hmom
  change O₀.material W.val.val + O₀.labelAdv W.val.val W.val.val + O₀.phaseAdv W.val.val W.val.val +
    O₀.labelGrad Pr.val.val + O₀.phaseGrad Pr.val.val + R.val.val = F.val.val at hEq
  change momentumResidual (Icc 0 T) (U + HierarchySmoothProfile.graphRead A k W.val.val)
    (pU + HierarchySmoothProfile.graphRead A k Pr.val.val) t x =
      HierarchySmoothProfile.graphRead A k F.val.val t x
  rw [HierarchySmoothProfile.momentumResidual_graphRead_parent hT hP.flow hP.velocity_smooth
    hP.velocity_periodic hAreg d.inverse.val.val d.strain.val.val d.covector.val.val W.val.val
    Pr.val.val k ht x hp (fun a s => d.inverse_value (t, a, s) ⟨ht, mem_univ _⟩)
    (fun a s => d.strain_value (t, a, s) ⟨ht, mem_univ _⟩)
    (fun a s => d.covector_value (t, a, s) ⟨ht, mem_univ _⟩), ← hRz]
  change (O₀.material W.val.val + O₀.labelAdv W.val.val W.val.val + O₀.phaseAdv W.val.val W.val.val +
    O₀.labelGrad Pr.val.val + O₀.phaseGrad Pr.val.val + R.val.val).val (hierarchyGraphPoint A k t x) =
      F.val.val.val (hierarchyGraphPoint A k t x)
  rw [hEq]

end

end TorusEuler.Paper.S5b

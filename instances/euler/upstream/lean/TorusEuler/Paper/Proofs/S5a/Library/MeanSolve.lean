import TorusEuler.Paper.Proofs.S5a.Library.MeanSetting
import TorusEuler.Paper.Proofs.S5Bridge.Hierarchy
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.EndpointPhysicalMeanSolve
import TorusEuler.SmoothPeriodicHolder
import TorusEuler.HierarchyConcreteMean

/-!
# S5a library: the mean equation (5.11) has normalized smooth solutions (from Theorem 4.2)

`sections/06d_mean_estimates.tex:3-14` defines the mean equation (5.11) through Theorem 4.2:
"For a smooth phase-independent source `f̄(t,a)`, Theorem 4.2 over `U` gives `(B, q̄)` with
`B_t + MB + 𝐝q̄ = f̄`, `𝐝·B = 0`, `z(0) = z(T) = 0`, `B = D_aX z_t`. In the notation of that
theorem, `f̄ = f∘X`, `g = (D_aX)^T f̄`, `v = z_t`, and `q̄` is the pressure `𝗊` of (4.11)."
The proof of Proposition 5.4 uses exactly this ("the mean equation has smooth solutions by
Theorem 4.2", `06c_finite_hierarchy.tex:372`).

`meanSolvable_of_theorem42 h4_2 d hP : Bridge.MeanSolvable d` carries this out for the parent of
§5.1:

* the parent is a parent of Theorem 4.2 (`meanParentFlow_of_parent`, `meanHsharp_le_of_parent`),
  with `D_- = 𝖣` and `‖M‖_∞ ≤ 𝖣` by (5.1), any finite bounds `K₀, K₁, Ω₀, Ω₁` for `K`, `Ω` and
  their first label derivatives (compactness of `[0,T] × [0,1]³` and periodicity), and the curves
  `K, Ω` in `C^{0,1/2}` realizing (4.1);
* the Eulerian force is `f = f̄∘X⁻¹`, so that `f∘X = f̄`, and the source `L = -∫_0^t g` of (4.9)
  is realized as a curve in `C^{0,1/2}`;
* the smooth-force item of `h4_2` gives a solution of (4.9) and, for it, smoothness of `z`,
  (4.11) `K v_t + ∇_a 𝗊 = g - 2(D_aX)^T ∂_t D_aX v` with a smooth zero-mean label pressure `𝗊`,
  and smoothness of `b = B∘X⁻¹`;
* `B = D_aX v` (`= b∘X`) and `q̄ = 𝗊` as phase-independent twisted profiles; multiplying (4.11)
  by `(D_aX)^{-T}` and using `∂_t D_aX = M D_aX` gives `B_t + MB + 𝐝q̄ = f̄`; `div_a v = 0` because
  `v(t)` lies in the divergence-free subspace; `z(0) = z(T) = 0`, `z_t = v` are the fields of the
  solution of (4.9).

No content lemma of a ledger row is used: the parent data come from `S5.Parent`, the Hölder
curves from the generic `exists_endpointSlabHalfHolderJets`, and the solution and its properties
from `h4_2` only.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile

local notation "C½" => HalfHolder (UnitAddTorus (Fin 3)) Vec3
local notation "K½" => HalfHolder (UnitAddTorus (Fin 3)) (Vec3 →L[ℝ] Vec3)

/-- Normed group structure on the divergence-free subspace (local shortcut for instance
search, as in the library files on the endpoint system). -/
local instance meanSolveSolenoidalNormedGroup : NormedAddCommGroup endpointHalfHolderSolenoidal :=
  inferInstance

/-- Real normed space structure on the divergence-free subspace (local shortcut). -/
local instance meanSolveSolenoidalNormedSpace : NormedSpace ℝ endpointHalfHolderSolenoidal :=
  inferInstance

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A jointly smooth field on the slab is smooth in the label at each time of `[0,T]`. -/
theorem meanSlice_contDiff {T t : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- A jointly smooth field on the slab is smooth in time on `[0,T]` at each label. -/
theorem meanTimeSlice_contDiffOn {T : ℝ} {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3))) (a : Vec3) :
    ContDiffOn ℝ ∞ (fun t => f t a) (Icc 0 T) :=
  hf.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ a⟩)

/-- A smooth periodic field on the slab is realized, at each time of `[0,T]`, by an element of
`C^{0,1/2}(𝕋³; E)` (the empty word of the generic slab jets). -/
theorem exists_halfHolder_curve [CompleteSpace E] {T : ℝ} (hT : 0 < T) (f : ℝ → Vec3 → E)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (f t)) :
    ∃ c : ℝ → HalfHolder (UnitAddTorus (Fin 3)) E,
      ∀ t ∈ Icc 0 T, ∀ a, HalfHolder.eval (toUnitTorus a) (c t) = f t a := by
  obtain ⟨j⟩ := exists_endpointSlabHalfHolderJets hT (fun i : Fin 3 => EuclideanSpace.single i 1)
    (Function.uncurry f) hf hper
  exact ⟨j.curve [], fun t ht a => j.eval_lift [] t ht a⟩

/-- The lift of an element of a space of torus fields is periodic. -/
theorem halfHolder_lift_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (w : HalfHolder (UnitAddTorus (Fin 3)) F) :
    SpatiallyPeriodic (fun a : Vec3 => HalfHolder.eval (toUnitTorus a) w) := by
  intro n a
  change HalfHolder.eval (toUnitTorus (a + latticeVector n)) w = HalfHolder.eval (toUnitTorus a) w
  rw [(toUnitTorus_eq_iff (a + latticeVector n) a).mpr ⟨n, rfl⟩]

end Helpers

section Parent

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {D lam : ℝ}

/-- The flow of the parent of §5.1 commutes with the lattice translations. -/
theorem parent_flow_lattice (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {s t : ℝ}
    (hs : s ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (n : Fin 3 → ℤ) (a : Vec3) :
    X s t (a + latticeVector n) = X s t a + latticeVector n := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (hP.velocity_smooth.of_le (by simp)) hP.velocity_periodic
  exact hP.flow.add_latticeVector hK hP.velocity_periodic hs ht n a

/-- `X(t,·)⁻¹ ∘ X(t,·) = id` for the parent of §5.1. -/
theorem parent_flow_left_inverse (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) (a : Vec3) : X t 0 (X 0 t a) = a := by
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT
    (hP.velocity_smooth.of_le (by simp)) hP.velocity_periodic
  exact (hP.flow.inverse hK (left_mem_Icc.mpr hT.le) ht).1 a

/-- The deformation `D_aX(t,·)` of the parent of §5.1 is periodic in the label. -/
theorem parent_deformation_periodic (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (fun a => fderiv ℝ (X 0 t) a) := by
  intro n a
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q a)
    (funext (parent_flow_lattice hT hP (left_mem_Icc.mpr hT.le) ht n))
  simpa only [fderiv_comp_add_right, fderiv_add_const] using h

/-- The velocity gradient along the flow `M(t,·)` of the parent is periodic in the label. -/
theorem parent_strain_periodic (hT : 0 < T) (hP : S5.Parent T U X pU D lam) {t : ℝ}
    (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (fun a => fderiv ℝ (U t) (X 0 t a)) := by
  intro n a
  change fderiv ℝ (U t) (X 0 t (a + latticeVector n)) = fderiv ℝ (U t) (X 0 t a)
  rw [parent_flow_lattice hT hP (left_mem_Icc.mpr hT.le) ht n a]
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q (X 0 t a))
    (funext (hP.velocity_periodic t ht n))
  simpa only [fderiv_comp_add_right] using h

/-- Joint smoothness of the kinetic coefficient `K = (D_aX)^T D_aX` of (4.1). -/
theorem meanKinetic_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ContDiffOn ℝ ∞ (Function.uncurry (meanKinetic X)) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  have hF := hP.flow.contDiffOn_forwardLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  have cAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (fderiv ℝ (X 0 z.1) z.2).adjoint)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (ContinuousLinearMap.adjoint : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ⋆[ℝ] (Vec3 →L[ℝ] Vec3)).contDiff.comp_contDiffOn hF
  exact cAdj.clm_comp hF

/-- Joint smoothness of the vorticity coefficient `Ω = (D_aX)^T (M^T - M) D_aX` of (4.1). -/
theorem meanVorticity_smooth (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    ContDiffOn ℝ ∞ (Function.uncurry (meanVorticity U X)) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  have hF := hP.flow.contDiffOn_forwardLabelDerivative hT hP.velocity_smooth hP.velocity_periodic
  have hM := hP.flow.contDiffOn_materialGradient hT hP.velocity_smooth hP.velocity_periodic
  have adj : ContDiff ℝ ∞ (fun F : Vec3 →L[ℝ] Vec3 => F.adjoint) :=
    (ContinuousLinearMap.adjoint : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ⋆[ℝ] (Vec3 →L[ℝ] Vec3)).contDiff
  have cAdjF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (fderiv ℝ (X 0 z.1) z.2).adjoint)
      (Icc 0 T ×ˢ (univ : Set Vec3)) := adj.comp_contDiffOn hF
  have cAdjM : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (fderiv ℝ (U z.1) (X 0 z.1 z.2)).adjoint)
      (Icc 0 T ×ˢ (univ : Set Vec3)) := adj.comp_contDiffOn hM
  exact cAdjF.clm_comp ((cAdjM.sub hM).clm_comp hF)

/-- Finite bounds for `K`, `Ω` of (4.1) and their first label derivatives on `[0,T] × ℝ³`
(continuity on the compact `[0,T] × [-1/2,1/2]³` and periodicity). Their values do not enter:
Theorem 4.2 is used here only for existence. -/
theorem exists_meanCoefficient_bounds (hT : 0 < T) (hP : S5.Parent T U X pU D lam) :
    (∀ t ∈ Icc 0 T, SpatiallyPeriodic (meanKinetic X t)) ∧
    (∀ t ∈ Icc 0 T, SpatiallyPeriodic (meanVorticity U X t)) ∧
    ∃ K₀ K₁ Ω₀ Ω₁ : ℝ,
      (∀ t ∈ Icc 0 T, ∀ a, ‖meanKinetic X t a‖ ≤ K₀) ∧
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (meanKinetic X t) a‖ ≤ K₁) ∧
      (∀ t ∈ Icc 0 T, ∀ a, ‖meanVorticity U X t a‖ ≤ Ω₀) ∧
      (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (meanVorticity U X t) a‖ ≤ Ω₁) := by
  have hKper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (meanKinetic X t) := fun t ht n a =>
    congrArg kineticForm (parent_deformation_periodic hT hP ht n a)
  have hΩper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (meanVorticity U X t) := fun t ht n a => by
    change vorticityForm (fderiv ℝ (X 0 t) (a + latticeVector n))
        (fderiv ℝ (U t) (X 0 t (a + latticeVector n))) =
      vorticityForm (fderiv ℝ (X 0 t) a) (fderiv ℝ (U t) (X 0 t a))
    have h1 : fderiv ℝ (X 0 t) (a + latticeVector n) = fderiv ℝ (X 0 t) a :=
      parent_deformation_periodic hT hP ht n a
    have h2 : fderiv ℝ (U t) (X 0 t (a + latticeVector n)) = fderiv ℝ (U t) (X 0 t a) :=
      parent_strain_periodic hT hP ht n a
    rw [h1, h2]
  have hone {F : ℝ → Vec3 → (Vec3 →L[ℝ] Vec3)} (t : ℝ) (a : Vec3) :
      ‖fderiv ℝ (F t) a‖ = ‖iteratedFDeriv ℝ 1 (F t) a‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_zero]
  obtain ⟨K₀, hK₀⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT (meanKinetic_smooth hT hP)
    hKper 0
  obtain ⟨K₁, hK₁⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT (meanKinetic_smooth hT hP)
    hKper 1
  obtain ⟨Ω₀, hΩ₀⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT
    (meanVorticity_smooth hT hP) hΩper 0
  obtain ⟨Ω₁, hΩ₁⟩ := exists_bound_spatial_jet_of_contDiffOn_periodic hT
    (meanVorticity_smooth hT hP) hΩper 1
  refine ⟨hKper, hΩper, K₀, K₁, Ω₀, Ω₁, fun t ht a => ?_, fun t ht a => ?_, fun t ht a => ?_,
    fun t ht a => ?_⟩
  · simpa only [norm_iteratedFDeriv_zero] using hK₀ t ht a
  · rw [hone]
    exact hK₁ t ht a
  · simpa only [norm_iteratedFDeriv_zero] using hΩ₀ t ht a
  · rw [hone]
    exact hΩ₁ t ht a

end Parent

section Solve

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {pU : Pressure}
  {D lam : ℝ}

/-- A phase-independent twisted profile is periodic in the label at fixed phase. -/
theorem meanProfile_periodic (d : ParentGeometry hT U X k) {f : HierarchyTwistedProfile T k Vec3}
    (hf : (S5.ops d).average f = f) {t : ℝ} (ht : t ∈ Icc 0 T) (s s' : ℝ) (n : Fin 3 → ℤ)
    (a : Vec3) : f.val.val.val (t, a + latticeVector n, s) = f.val.val.val (t, a, s') := by
  have hind := Bridge.phaseIndependent_of_average_eq d hf
  have h1 : f.val.val.val (t, a + latticeVector n, s) =
      f.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) :=
    (hind (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) ⟨ht, mem_univ _⟩ s)
  rw [h1, twistedSlice f t a s n]
  exact (hind (t, a, s') ⟨ht, mem_univ _⟩ s).trans rfl

set_option maxHeartbeats 1600000 in
/-- **The mean equation (5.11) is solvable** (`06d_mean_estimates.tex:3-14`): for the parent
of §5.1, every phase-independent source `f̄` has a solution `(B, q̄)` of (5.11) whose pressure has
zero mean over the label cell. `h4_2` enters through its smooth-force item: it gives the
solution of (4.9) with source `L = -∫_0^t (D_aX)^T f̄`, smoothness of `z` and of
`b = B∘X⁻¹`, and (4.11) with the normalized label pressure `𝗊 = q̄`; (5.11) is (4.11) multiplied
by `(D_aX)^{-T}`, with `B = D_aX v` and `∂_t D_aX = M D_aX`. -/
theorem meanSolvable_of_theorem42 (h4_2 : Statement.theorem_4_2) (d : ParentGeometry hT U X k)
    (hP : S5.Parent T U X pU D lam) : Bridge.MeanSolvable d := by
  intro f hf
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
  obtain ⟨hz, -, qL, hqL, hqLper, hmom, hb, -, -, -⟩ := hprop
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
  refine ⟨Bp, qp, ⟨?_, ?_, ?_, ?_⟩, fun t ht => ?_⟩
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

end Solve

end

end TorusEuler.Paper.Lib.S5a

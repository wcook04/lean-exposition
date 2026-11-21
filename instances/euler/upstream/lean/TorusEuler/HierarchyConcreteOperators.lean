import TorusEuler.HierarchySmoothProfiles

/-! Actual material derivatives, coframe derivatives and phase means for the hierarchy. -/

open ContinuousLinearMap MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)
local notation "Directions" => HierarchySmoothProfile T HierarchyProfilePoint

private def labelInclusion : Vec3 →L[ℝ] HierarchyProfilePoint :=
  (inr ℝ ℝ (Vec3 × ℝ)).comp (inl ℝ Vec3 ℝ)

private def phaseInclusion : ℝ →L[ℝ] HierarchyProfilePoint :=
  (inr ℝ ℝ (Vec3 × ℝ)).comp (inr ℝ Vec3 ℝ)

/-- The coframe sends an Eulerian direction into the label component
of a profile derivative. -/
def labelDirections (G : VPmap) : VP →ₗ[ℝ] Directions :=
  (map labelInclusion).comp (applyField G)

theorem labelDirections_apply (G : VPmap) (u : VP) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) :
    (labelDirections G u).val x = (0, G.val x (u.val x), 0) := by
  simp only [labelDirections, LinearMap.comp_apply, map_apply _ _ hx, applyField_eval _ _ hx]
  rfl

/-- The fast direction is the contraction of the advecting field with
the transported covector. -/
def phaseDirections (κ : VP) : VP →ₗ[ℝ] Directions :=
  (map phaseInclusion).comp (applyField (map (innerSL ℝ) κ))

theorem phaseDirections_apply (κ u : VP) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) :
    (phaseDirections κ u).val x = (0, 0, ⟪κ.val x, u.val x⟫_ℝ) := by
  simp only [phaseDirections, LinearMap.comp_apply, map_apply _ _ hx, applyField_eval _ _ hx]
  rfl

private def euclideanBasisVector (i : Fin 3) : Vec3 := EuclideanSpace.single i 1

/-- The three scalar coframe derivatives form the Eulerian label gradient. -/
def labelGradient (hT : 0 < T) (G : VPmap) : SP →ₗ[ℝ] VP :=
  ∑ i : Fin 3, (map (toSpanSingleton ℝ (euclideanBasisVector i))).comp
    (derivativeAlong hT (labelDirections G (constant (euclideanBasisVector i))))

theorem labelGradient_apply (hT : 0 < T) (G : VPmap) (q : SP)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (labelGradient hT G q).val x = ∑ i : Fin 3,
      fderivWithin ℝ q.val (hierarchyProfileSlab T) x (0, G.val x (euclideanBasisVector i), 0) •
        euclideanBasisVector i := by
  simp only [labelGradient, LinearMap.sum_apply]
  change (∑ i : Fin 3, (map (toSpanSingleton ℝ (euclideanBasisVector i))
    (derivativeAlong hT (labelDirections G (constant (euclideanBasisVector i))) q)).val) x = _
  simp only [Finset.sum_apply, map_apply _ _ hx, derivativeAlong_apply _ _ _ hx,
    labelDirections_apply _ _ hx, constant_apply _ hx, toSpanSingleton_apply]

/-- The fast scalar derivative of the pressure multiplies the transported covector. -/
def phaseGradient (hT : 0 < T) (κ : VP) : SP →ₗ[ℝ] VP :=
  (applyField (map (smulRightL ℝ ℝ Vec3 (ContinuousLinearMap.id ℝ ℝ)) κ)).comp
    (derivativeAlong hT (constant (0, 0, 1)))

theorem phaseGradient_apply (hT : 0 < T) (κ : VP) (q : SP)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (phaseGradient hT κ q).val x =
      fderivWithin ℝ q.val (hierarchyProfileSlab T) x (0, 0, 1) • κ.val x := by
  simp only [phaseGradient, LinearMap.comp_apply, applyField_eval _ _ hx, map_apply _ _ hx,
    derivativeAlong_apply _ _ _ hx, constant_apply _ hx]
  rfl

private theorem contDiffOn_profilePhaseAverage (hT : 0 < T) (f : VP) :
    ContDiffOn ℝ ∞ (fun x : HierarchyProfilePoint => phaseMean (fun s => f.val (x.1, x.2.1, s)))
      (hierarchyProfileSlab T) := by
  let S : Set (ℝ × Vec3) := Icc 0 T ×ˢ univ
  let F (p : ℝ × Vec3) (s : ℝ) := f.val (p.1, p.2, s)
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (S ×ˢ (univ : Set ℝ)) :=
    (smooth f).comp (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd))
      (fun z hz => ⟨hz.1.1, mem_univ _⟩)
  exact (contDiffOn_phaseMean ((convex_Icc 0 T).prod convex_univ)
    ((uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ) hF).comp
      (contDiffOn_fst.prodMk contDiffOn_snd.fst) (fun z hz => ⟨hz.1, mem_univ _⟩)

private theorem continuous_profilePhase (f : VP) {t : ℝ} {a : Vec3} (ht : t ∈ Icc 0 T) :
    Continuous (fun s => f.val (t, a, s)) :=
  (smooth f).continuousOn.comp_continuous
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    (fun _ => ⟨ht, mem_univ _⟩)

/-- Averaging the actual unit-period phase yields a smooth phase-independent profile. -/
def profilePhaseAverage (hT : 0 < T) : VP →ₗ[ℝ] VP where
  toFun f := ofSmooth _ (contDiffOn_profilePhaseAverage hT f)
  map_add' f g := by
    apply ext
    intro x hx
    simp only [ofSmooth_apply _ hx, Submodule.coe_add, Pi.add_apply]
    exact phaseMean_add (continuous_profilePhase f hx.1) (continuous_profilePhase g hx.1)
  map_smul' c f := by
    apply ext
    intro x hx
    simp only [ofSmooth_apply _ hx, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    exact phaseMean_const_smul _ _

theorem profilePhaseAverage_apply (hT : 0 < T) (f : VP) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) :
    (profilePhaseAverage hT f).val x = phaseMean (fun s => f.val (x.1, x.2.1, s)) :=
  ofSmooth_apply (contDiffOn_profilePhaseAverage hT f) hx

theorem profilePhaseAverage_eq_self_of_independent (hT : 0 < T) (f : VP)
    (h : ∀ x ∈ hierarchyProfileSlab T, ∀ s : ℝ, f.val (x.1, x.2.1, s) = f.val x) :
    profilePhaseAverage hT f = f := by
  apply ext
  intro x hx
  rw [profilePhaseAverage_apply hT f hx, show (fun s => f.val (x.1, x.2.1, s)) =
    (fun _ : ℝ => f.val x) from funext (h x hx), phaseMean_const]

/-- The actual profile operators in (5.20) and (5.25) on a closed time slab. -/
def hierarchyConcreteOperators (hT : 0 < T) (G M : VPmap) (κ : VP) :
    HierarchyOperators VP SP where
  material := derivativeAlong hT (constant (1, 0, 0)) + applyField M
  labelGrad := labelGradient hT G
  phaseGrad := phaseGradient hT κ
  labelAdv := advect hT (labelDirections G)
  phaseAdv := advect hT (phaseDirections κ)
  average := profilePhaseAverage hT

theorem hierarchyConcreteOperators_material_apply (hT : 0 < T) (G M : VPmap) (κ u : VP)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    ((hierarchyConcreteOperators hT G M κ).material u).val x =
      fderivWithin ℝ u.val (hierarchyProfileSlab T) x (1, 0, 0) + M.val x (u.val x) := by
  simp only [hierarchyConcreteOperators, LinearMap.add_apply, Submodule.coe_add, Pi.add_apply,
    derivativeAlong_apply _ _ _ hx, constant_apply _ hx, applyField_eval _ _ hx]

end HierarchySmoothProfile

end

end TorusEuler

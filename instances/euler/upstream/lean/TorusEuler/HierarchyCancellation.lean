import TorusEuler.HierarchyExponents

/-!
The momentum identity in `cc:uf:hier:prop:identity` from the supplied
mean and transverse equations. The differential operations are represented
by their linear and bilinear actions on profiles.
-/

namespace TorusEuler

private theorem sum_Icc_previous {E : Type*} [AddCommMonoid E]
    (P : ℕ) (f : ℕ → E) :
    (∑ p ∈ Finset.Icc 2 (P + 1), f (p - 1)) = ∑ p ∈ Finset.Icc 1 P, f p := by
  refine Finset.sum_bij' (fun p _ => p - 1) (fun p _ => p + 1)
    (fun p hp => ?_) (fun p hp => ?_) (fun p hp => ?_) (fun p _ => by omega) (fun _ _ => rfl)
  · rw [Finset.mem_Icc] at hp ⊢
    omega
  · rw [Finset.mem_Icc] at hp ⊢
    omega
  · rw [Finset.mem_Icc] at hp
    omega

private theorem sum_Icc_split_first {E : Type*} [AddCommMonoid E]
    {P : ℕ} (hP : 1 ≤ P) (f : ℕ → E) :
    (∑ p ∈ Finset.Icc 1 P, f p) = f 1 + ∑ p ∈ Finset.Icc 2 P, f p := by
  rw [Finset.Icc_eq_cons_Ioc hP, Finset.sum_cons]
  rfl

private theorem bilinear_advection_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (adv : E →ₗ[ℝ] E →ₗ[ℝ] E) (s t : Finset ℕ) (f g : ℕ → E) :
    adv (∑ i ∈ s, f i) (∑ j ∈ t, g j) =
      ∑ ij ∈ s.product t, adv (f ij.1) (g ij.2) := by
  rw [map_sum adv, LinearMap.sum_apply]
  simp only [map_sum]
  exact (Finset.sum_product s t (fun ij => adv (f ij.1) (g ij.2))).symm

/-- The profiles, divergence completions and two parts of the pressure at
each level of the finite expansion. -/
structure HierarchyProfiles (E F : Type*) where
  V : ℕ → E
  C : ℕ → E
  B : ℕ → E
  p : ℕ → F
  q : ℕ → F

/-- The actions of `∂t+M`, the two gradient and advection terms, and the
phase average on profiles. -/
structure HierarchyOperators (E F : Type*) [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] where
  material : E →ₗ[ℝ] E
  labelGrad : F →ₗ[ℝ] E
  phaseGrad : F →ₗ[ℝ] E
  labelAdv : E →ₗ[ℝ] E →ₗ[ℝ] E
  phaseAdv : E →ₗ[ℝ] E →ₗ[ℝ] E
  average : E →ₗ[ℝ] E

namespace HierarchyProfiles

variable {E F : Type*}

def Y [Add E] (u : HierarchyProfiles E F) (p : ℕ) : E := u.V p + u.C (p - 1)

def Z [Add E] (u : HierarchyProfiles E F) (p : ℕ) : E := u.Y p + u.B p

def velocity [AddCommMonoid E] (u : HierarchyProfiles E F) (P : ℕ) : E :=
  ∑ p ∈ Finset.Icc 1 P, (u.V p + u.C p + u.B p)

def pressure [AddCommMonoid F] (u : HierarchyProfiles E F) (P : ℕ) : F :=
  ∑ p ∈ Finset.Icc 1 P, (u.p p + u.q p)

/-- The two groupings of the velocity in `cc:uf:hier:prop:identity`. -/
theorem velocity_eq_sum_Z_add_completion [AddCommGroup E] (u : HierarchyProfiles E F)
    {P : ℕ} (hP : 1 ≤ P) (hC₀ : u.C 0 = 0) :
    u.velocity P = (∑ i ∈ Finset.Icc 1 P, u.Z i) + u.C P := by
  have hC : (∑ i ∈ Finset.Icc 1 P, u.C (i - 1)) + u.C P = ∑ i ∈ Finset.Icc 1 P, u.C i := by
    have h := sum_Icc_previous P u.C
    rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ P + 1)] at h
    have hsplit := sum_Icc_split_first hP (fun i => u.C (i - 1))
    simp only [Nat.add_sub_cancel, Nat.sub_self, hC₀, zero_add] at h hsplit
    rw [hsplit]
    exact h
  simp only [velocity, Z, Y, Finset.sum_add_distrib]
  rw [← hC]
  abel

/-- The last index in the quadratic expansion is the last divergence correction. -/
theorem velocity_eq_sum_Z [AddCommGroup E] (u : HierarchyProfiles E F)
    {P : ℕ} (hP : 1 ≤ P) (hC₀ : u.C 0 = 0)
    (hVlast : u.V (P + 1) = 0) (hBlast : u.B (P + 1) = 0) :
    u.velocity P = ∑ i ∈ Finset.Icc 1 (P + 1), u.Z i := by
  rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ P + 1), u.velocity_eq_sum_Z_add_completion hP hC₀]
  simp only [Z, Y, hVlast, hBlast, Nat.add_sub_cancel, zero_add, add_zero]

/-- If each completed oscillation and each mean is divergence free, their
finite velocity is divergence free. -/
theorem divergence_velocity_eq_zero {G : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup G] [Module ℝ G]
    (u : HierarchyProfiles E F) (P : ℕ) (divergence : E →ₗ[ℝ] G)
    (hC : ∀ i ∈ Finset.Icc 1 P, divergence (u.V i + u.C i) = 0)
    (hB : ∀ i ∈ Finset.Icc 1 P, divergence (u.B i) = 0) :
    divergence (u.velocity P) = 0 := by
  unfold velocity
  rw [map_sum]
  exact Finset.sum_eq_zero fun i hi => by rw [map_add, hC i hi, hB i hi, add_zero]

/-- The oscillatory part of the total velocity is the sum of the
completed oscillations. -/
theorem velocity_sub_average [AddCommGroup E] [Module ℝ E]
    (u : HierarchyProfiles E F) (P : ℕ) (average : E →ₗ[ℝ] E)
    (hV : ∀ p, average (u.V p) = 0) (hC : ∀ p, average (u.C p) = 0)
    (hB : ∀ p, average (u.B p) = u.B p) :
    u.velocity P - average (u.velocity P) =
      ∑ p ∈ Finset.Icc 1 P, (u.V p + u.C p) := by
  simp only [velocity, map_sum, map_add, hV, hC, hB, zero_add]
  rw [Finset.sum_add_distrib, add_sub_cancel_right]

end HierarchyProfiles

/-- The level-`p` contribution of a quadratic term. -/
def hierarchyAdvectionAtLevel {E : Type*} [AddCommMonoid E]
    (P shift p : ℕ) (f : ℕ × ℕ → E) : E :=
  ∑ ij ∈ hierarchyAdvectionPairs P shift with hierarchyAdvectionLevel shift ij = p, f ij

namespace HierarchyOperators

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

def labelProduct (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (ij : ℕ × ℕ) : E :=
  A.labelAdv (u.Z ij.1) (u.Z ij.2)

def completionPhaseProduct (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    (ij : ℕ × ℕ) : E :=
  A.phaseAdv (u.C (ij.1 - 1)) (u.Y ij.2)

def meanPhaseProduct (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    (ij : ℕ × ℕ) : E :=
  A.phaseAdv (u.B ij.1) (u.Y ij.2)

private theorem phase_advection_expand
    (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    {P : ℕ} (hP : 1 ≤ P) (hC₀ : u.C 0 = 0) (hB₁ : u.B 1 = 0)
    (hVlast : u.V (P + 1) = 0) (hBlast : u.B (P + 1) = 0)
    (htransverse : ∀ i v, A.phaseAdv (u.V i) v = 0)
    (hmean : ∀ j v, A.phaseAdv v (u.B j) = 0) :
    A.phaseAdv (u.velocity P) (u.velocity P) =
      ∑ ij ∈ hierarchyAdvectionPairs P 1, (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij) := by
  rw [u.velocity_eq_sum_Z hP hC₀ hVlast hBlast, bilinear_advection_sum]
  change (∑ ij ∈ hierarchyAdvectionPairs P 0, A.phaseAdv (u.Z ij.1) (u.Z ij.2)) = _
  have hsubset : hierarchyAdvectionPairs P 1 ⊆ hierarchyAdvectionPairs P 0 := by
    intro ij hij
    have h := (Finset.mem_product
      (s := Finset.Icc 2 (P + 1)) (t := Finset.Icc 1 (P + 1))).mp hij
    apply (Finset.mem_product
      (s := Finset.Icc 1 (P + 1)) (t := Finset.Icc 1 (P + 1))).mpr
    rw [Finset.mem_Icc] at h
    exact ⟨Finset.mem_Icc.mpr ⟨by omega, h.1.2⟩, h.2⟩
  rw [← Finset.sum_subset hsubset]
  · refine Finset.sum_congr rfl fun ij _ => ?_
    rw [show u.Z ij.2 = u.Y ij.2 + u.B ij.2 from rfl]
    simp only [map_add, hmean, add_zero, completionPhaseProduct, meanPhaseProduct]
    rw [show u.Z ij.1 = u.V ij.1 + u.C (ij.1 - 1) + u.B ij.1 from rfl]
    simp only [map_add, LinearMap.add_apply, htransverse, zero_add]
  · intro ij hij hnot
    have h := (Finset.mem_product
      (s := Finset.Icc 1 (P + 1)) (t := Finset.Icc 1 (P + 1))).mp hij
    have hfirst : ij.1 = 1 := by
      by_contra hne
      apply hnot
      apply (Finset.mem_product
        (s := Finset.Icc 2 (P + 1)) (t := Finset.Icc 1 (P + 1))).mpr
      rw [Finset.mem_Icc] at h
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, h.1.2⟩, h.2⟩
    simp only [HierarchyProfiles.Z, HierarchyProfiles.Y, hfirst, Nat.sub_self, hC₀, hB₁,
      add_zero, htransverse]

/-- `H_p` before the mean's phase advection is added. At level two the
linear part is the switched linear term with the activation derivative
removed, as in `cc:uf:hier:eq:H2`. -/
def sourceBeforeMean (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    (P : ℕ) (completionSwitch : E) (p : ℕ) : E :=
  A.material (u.C (p - 1)) + A.labelGrad (u.p (p - 1)) -
    (if p = 2 then completionSwitch else 0) +
    hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) +
    hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u)

/-- The two linear terms at level `P+1` and the quadratic interactions
above depth `P`, as in `cc:uf:hier:eq:tail`. -/
def remainder (A : HierarchyOperators E F) (u : HierarchyProfiles E F) (P : ℕ) : E :=
  A.material (u.C P) + A.labelGrad (u.p P) +
    (∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij) +
    (∑ ij ∈ hierarchyTailPairs P 1, (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij))

/-- The residual identity `cc:uf:hier:eq:residual` follows from the leading
wave equation, the mean and transverse equations at every retained level,
and the phase-advection compatibility of the profiles. -/
theorem momentum_eq_remainder_add_switch
    (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    {P : ℕ} (hP : 2 ≤ P) (leadingSwitch completionSwitch parentResidual : E)
    (hC₀ : u.C 0 = 0) (hB₁ : u.B 1 = 0) (hq₁ : u.q 1 = 0)
    (hVlast : u.V (P + 1) = 0) (hBlast : u.B (P + 1) = 0)
    (htransverse : ∀ i v, A.phaseAdv (u.V i) v = 0)
    (hphaseMean : ∀ j v, A.phaseAdv v (u.B j) = 0)
    (hphasePressure : ∀ j, A.phaseGrad (u.q j) = 0)
    (hleading : A.material (u.V 1) + A.phaseGrad (u.p 1) = leadingSwitch)
    (hmean : ∀ p ∈ Finset.Icc 2 P,
      A.material (u.B p) + A.labelGrad (u.q p) =
        -A.average (A.sourceBeforeMean u P completionSwitch p) -
          (if p = 2 then parentResidual else 0))
    (hosc : ∀ p ∈ Finset.Icc 2 P,
      A.material (u.V p) + A.phaseGrad (u.p p) =
        -(A.sourceBeforeMean u P completionSwitch p -
          A.average (A.sourceBeforeMean u P completionSwitch p)) -
          hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)) :
    A.material (u.velocity P) + A.labelAdv (u.velocity P) (u.velocity P) +
      A.phaseAdv (u.velocity P) (u.velocity P) +
      A.labelGrad (u.pressure P) + A.phaseGrad (u.pressure P) + parentResidual =
      A.remainder u P + (leadingSwitch + completionSwitch) := by
  let trans := fun p => A.material (u.V p) + A.phaseGrad (u.p p)
  let mean := fun p => A.material (u.B p) + A.labelGrad (u.q p)
  let completionLinear := fun p => A.material (u.C p) + A.labelGrad (u.p p)
  let slow := fun p => hierarchyAdvectionAtLevel P 0 p (A.labelProduct u)
  let fastC := fun p => hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u)
  let fastB := fun p => hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)
  let levels := Finset.Icc 2 P
  have hP₁ : 1 ≤ P := by omega
  have hslow : A.labelAdv (u.velocity P) (u.velocity P) =
      (∑ p ∈ levels, slow p) + ∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij := by
    rw [u.velocity_eq_sum_Z hP₁ hC₀ hVlast hBlast, bilinear_advection_sum]
    exact hierarchy_advection_filtration P 0 (A.labelProduct u)
  have hfast : A.phaseAdv (u.velocity P) (u.velocity P) =
      ((∑ p ∈ levels, fastC p) + (∑ p ∈ levels, fastB p)) +
        ∑ ij ∈ hierarchyTailPairs P 1, (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij) := by
    rw [A.phase_advection_expand u hP₁ hC₀ hB₁ hVlast hBlast htransverse hphaseMean,
      hierarchy_advection_filtration P 1]
    simp only [levels, fastC, fastB, hierarchyAdvectionAtLevel, Finset.sum_add_distrib]
  have hlin : A.material (u.velocity P) + A.labelGrad (u.pressure P) + A.phaseGrad (u.pressure P) =
      (∑ p ∈ Finset.Icc 1 P, trans p) + (∑ p ∈ Finset.Icc 1 P, mean p) +
        ∑ p ∈ Finset.Icc 1 P, completionLinear p := by
    simp only [HierarchyProfiles.velocity, HierarchyProfiles.pressure, trans, mean, completionLinear,
      map_sum, map_add, Finset.sum_add_distrib, hphasePressure, Finset.sum_const_zero, add_zero]
    abel
  have htransSum : (∑ p ∈ Finset.Icc 1 P, trans p) = leadingSwitch + ∑ p ∈ levels, trans p := by
    rw [sum_Icc_split_first hP₁]
    exact congrArg (· + ∑ p ∈ levels, trans p) hleading
  have hmeanSum : (∑ p ∈ Finset.Icc 1 P, mean p) = ∑ p ∈ levels, mean p := by
    rw [sum_Icc_split_first hP₁]
    simp only [levels, mean, hB₁, hq₁, map_zero, zero_add]
  have hcompletionSum : (∑ p ∈ Finset.Icc 1 P, completionLinear p) =
      (∑ p ∈ levels, completionLinear (p - 1)) + completionLinear P := by
    rw [← sum_Icc_previous P completionLinear, Finset.sum_Icc_succ_top (by omega : 2 ≤ P + 1)]
    simp only [levels, Nat.add_sub_cancel]
  have hlevel (p : ℕ) (hp : p ∈ levels) :
      trans p + mean p + completionLinear (p - 1) + slow p + fastC p + fastB p =
        (if p = 2 then completionSwitch else 0) - (if p = 2 then parentResidual else 0) := by
    have ht := hosc p hp
    have hm := hmean p hp
    change trans p = _ at ht
    change mean p = _ at hm
    rw [ht, hm]
    simp only [sourceBeforeMean, completionLinear, slow, fastC, fastB]
    abel
  have hcancel :
      (∑ p ∈ levels, trans p) + (∑ p ∈ levels, mean p) +
        (∑ p ∈ levels, completionLinear (p - 1)) + (∑ p ∈ levels, slow p) +
        (∑ p ∈ levels, fastC p) + (∑ p ∈ levels, fastB p) =
          completionSwitch - parentResidual := by
    have htwo : 2 ∈ levels := Finset.mem_Icc.mpr ⟨le_rfl, hP⟩
    simp only [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl hlevel, Finset.sum_sub_distrib]
    simp only [Finset.sum_ite_eq', htwo, ite_true]
  calc
    _ = (A.material (u.velocity P) + A.labelGrad (u.pressure P) + A.phaseGrad (u.pressure P)) +
        A.labelAdv (u.velocity P) (u.velocity P) +
        A.phaseAdv (u.velocity P) (u.velocity P) + parentResidual := by abel
    _ = A.remainder u P + leadingSwitch +
        ((∑ p ∈ levels, trans p) + (∑ p ∈ levels, mean p) +
          (∑ p ∈ levels, completionLinear (p - 1)) + (∑ p ∈ levels, slow p) +
          (∑ p ∈ levels, fastC p) + (∑ p ∈ levels, fastB p)) + parentResidual := by
      rw [hlin, htransSum, hmeanSum, hcompletionSum, hslow, hfast]
      change _ = (completionLinear P + _ + _) + _ + _ + _
      abel
    _ = _ := by rw [hcancel]; abel

end HierarchyOperators

end TorusEuler

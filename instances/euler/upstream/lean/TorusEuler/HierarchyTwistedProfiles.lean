import TorusEuler.HierarchyPeriodicProfiles

/-! Twisted lattice periodicity and label reflection for the concrete hierarchy. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Pointwise

namespace TorusEuler

noncomputable section

/-- A shift of the label lattice changes the phase by the carrier pairing. -/
def hierarchyLatticeShift (k : Vec3) (n : Fin 3 → ℤ) : HierarchyProfilePoint :=
  (0, latticeVector n, ⟪k, latticeVector n⟫_ℝ)

@[simp] theorem add_hierarchyLatticeShift (x : HierarchyProfilePoint)
    (k : Vec3) (n : Fin 3 → ℤ) :
    x + hierarchyLatticeShift k n =
      (x.1, x.2.1 + latticeVector n, x.2.2 + ⟪k, latticeVector n⟫_ℝ) := by
  rcases x with ⟨t, a, s⟩
  simp [hierarchyLatticeShift]

@[simp] theorem add_hierarchyLatticeShift_mem_slab {T : ℝ} {x : HierarchyProfilePoint}
    {k : Vec3} {n : Fin 3 → ℤ} :
    x + hierarchyLatticeShift k n ∈ hierarchyProfileSlab T ↔ x ∈ hierarchyProfileSlab T := by
  simp [hierarchyProfileSlab]

theorem hierarchyLatticeShift_vadd_slab (T : ℝ) (k : Vec3) (n : Fin 3 → ℤ) :
    hierarchyLatticeShift k n +ᵥ hierarchyProfileSlab T = hierarchyProfileSlab T := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  simp [hierarchyProfileSlab, hierarchyLatticeShift]

section ProfileSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The actual phase-periodic profiles compatible with the label lattice. -/
def hierarchyTwistedProfileSubmodule (T : ℝ) (k : Vec3) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Submodule ℝ (HierarchyPeriodicProfile T E) where
  carrier := {f | ∀ n : Fin 3 → ℤ, Function.Periodic f.val.val (hierarchyLatticeShift k n)}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro f g hf hg n x
    change f.val.val (x + hierarchyLatticeShift k n) + g.val.val (x + hierarchyLatticeShift k n) =
      f.val.val x + g.val.val x
    exact congrArg₂ (· + ·) (hf n x) (hg n x)
  smul_mem' := by
    intro c f hf n x
    change c • f.val.val (x + hierarchyLatticeShift k n) = c • f.val.val x
    exact congrArg (c • ·) (hf n x)

abbrev HierarchyTwistedProfile (T : ℝ) (k : Vec3) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] := hierarchyTwistedProfileSubmodule T k E

instance instAddCommGroupHierarchyTwistedProfile {T : ℝ} {k : Vec3} :
    AddCommGroup (HierarchyTwistedProfile T k E) :=
  @Submodule.addCommGroup ℝ (HierarchyPeriodicProfile T E) _
    (@Submodule.addCommGroup ℝ (HierarchySmoothProfile T E) _ _ _
      (hierarchyPeriodicProfileSubmodule T E)) _
    (hierarchyTwistedProfileSubmodule T k E)

instance instModuleHierarchyTwistedProfile {T : ℝ} {k : Vec3} :
    Module ℝ (HierarchyTwistedProfile T k E) :=
  @Submodule.module ℝ (HierarchyPeriodicProfile T E) _ _ _
    (hierarchyTwistedProfileSubmodule T k E)

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

/-- Genuine label periodicity, measured at phase zero on the slab. -/
def LabelPeriodic (f : HierarchySmoothProfile T E) : Prop :=
  ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun a => f.val (t, a, 0))

theorem twistedPeriodic (f : HierarchyTwistedProfile T k E) (n : Fin 3 → ℤ) :
    Function.Periodic f.val.val.val (hierarchyLatticeShift k n) := f.property n

theorem twistedSlice (f : HierarchyTwistedProfile T k E) (t : ℝ) (a : Vec3) (s : ℝ)
    (n : Fin 3 → ℤ) :
    f.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
      f.val.val.val (t, a, s) := by
  simpa only [add_hierarchyLatticeShift] using (twistedPeriodic f n (t, a, s))

theorem ext {f g : HierarchyTwistedProfile T k E}
    (h : ∀ x ∈ hierarchyProfileSlab T, f.val.val.val x = g.val.val.val x) : f = g :=
  Subtype.ext (HierarchyPeriodicProfile.ext h)

private theorem twisted_of_onSlab (f : HierarchyPeriodicProfile T E)
    (h : ∀ (n : Fin 3 → ℤ) x, x ∈ hierarchyProfileSlab T →
      f.val.val (x + hierarchyLatticeShift k n) = f.val.val x) :
    ∀ n : Fin 3 → ℤ, Function.Periodic f.val.val (hierarchyLatticeShift k n) := by
  intro n x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact h n x hx
  · rw [HierarchySmoothProfile.eq_zero_outside f.val
      (fun h => hx (add_hierarchyLatticeShift_mem_slab.mp h)),
      HierarchySmoothProfile.eq_zero_outside f.val hx]

/-- An actual twisted-periodic solution on each time slice belongs to the
twisted submodule with its original underlying profile. -/
def ofTwistedSlices (f : HierarchyPeriodicProfile T E)
    (h : ∀ t ∈ Icc 0 T, ∀ (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ),
      f.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = f.val.val (t, a, s)) :
    HierarchyTwistedProfile T k E :=
  ⟨f, twisted_of_onSlab f fun n x hx => by
    rw [add_hierarchyLatticeShift]
    exact h x.1 hx.1 x.2.1 x.2.2 n⟩

@[simp] theorem ofTwistedSlices_val (f : HierarchyPeriodicProfile T E)
    (h : ∀ t ∈ Icc 0 T, ∀ (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ),
      f.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = f.val.val (t, a, s)) :
    (ofTwistedSlices f h).val = f := rfl

/-- A smooth function that is both phase-periodic and twisted-periodic
defines a twisted profile when restricted to the time slab. -/
def ofSmooth (f : HierarchyProfilePoint → E) (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T))
    (hphase : Function.Periodic f hierarchyPhasePeriod)
    (htwist : ∀ n : Fin 3 → ℤ, Function.Periodic f (hierarchyLatticeShift k n)) :
    HierarchyTwistedProfile T k E :=
  ⟨HierarchyPeriodicProfile.ofSmooth f hf hphase, twisted_of_onSlab _ fun n x hx => by
    rw [HierarchyPeriodicProfile.ofSmooth_apply hf hphase (add_hierarchyLatticeShift_mem_slab.mpr hx),
      HierarchyPeriodicProfile.ofSmooth_apply hf hphase hx, htwist n x]⟩

theorem ofSmooth_eval {f : HierarchyProfilePoint → E} (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T))
    (hphase : Function.Periodic f hierarchyPhasePeriod)
    (htwist : ∀ n : Fin 3 → ℤ, Function.Periodic f (hierarchyLatticeShift k n))
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    (ofSmooth f hf hphase htwist).val.val.val x = f x :=
  HierarchyPeriodicProfile.ofSmooth_apply hf hphase hx

/-- Periodic phase-independent coefficients belong to every twisted space. -/
def ofPhaseIndependent (f : HierarchySmoothProfile T E)
    (hf : HierarchyPeriodicProfile.PhaseIndependent f) (hper : LabelPeriodic f) :
    HierarchyTwistedProfile T k E :=
  ofTwistedSlices (HierarchyPeriodicProfile.ofPhaseIndependent f hf) fun t ht a s n => by
    have h₁ : (t, a + latticeVector n, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    have h₂ : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    change f.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) = f.val (t, a, s)
    rw [hf _ h₁ _, hf _ h₂ _]
    exact hper t ht n a

@[simp] theorem ofPhaseIndependent_val (f : HierarchySmoothProfile T E)
    (hf : HierarchyPeriodicProfile.PhaseIndependent f) (hper : LabelPeriodic f) :
    (ofPhaseIndependent (k := k) f hf hper).val =
      HierarchyPeriodicProfile.ofPhaseIndependent f hf := rfl

/-- Restriction of an actual periodic linear operator to twisted profiles. -/
def restrict (L : HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F)
    (hL : ∀ (f : HierarchyTwistedProfile T k E) n,
      Function.Periodic (L f.val).val.val (hierarchyLatticeShift k n)) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k F :=
  L.restrict fun f hf => hL ⟨f, hf⟩

@[simp] theorem restrict_val (L : HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F)
    (hL : ∀ (f : HierarchyTwistedProfile T k E) n,
      Function.Periodic (L f.val).val.val (hierarchyLatticeShift k n))
    (f : HierarchyTwistedProfile T k E) : (restrict L hL f).val = L f.val := rfl

/-- Restriction of an actual periodic bilinear operator in both arguments. -/
def restrictBilinear
    (L : HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F →ₗ[ℝ] HierarchyPeriodicProfile T G)
    (hL : ∀ (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) n,
      Function.Periodic (L f.val g.val).val.val (hierarchyLatticeShift k n)) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k F →ₗ[ℝ] HierarchyTwistedProfile T k G where
  toFun f := restrict (L f.val) (hL f)
  map_add' f g := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    change L (f.val + g.val) h.val = L f.val h.val + L g.val h.val
    rw [L.map_add, LinearMap.add_apply]
  map_smul' c f := by
    apply LinearMap.ext
    intro h
    apply Subtype.ext
    change L (c • f.val) h.val = c • L f.val h.val
    rw [L.map_smul, LinearMap.smul_apply]

@[simp] theorem restrictBilinear_val
    (L : HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F →ₗ[ℝ] HierarchyPeriodicProfile T G)
    (hL : ∀ (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) n,
      Function.Periodic (L f.val g.val).val.val (hierarchyLatticeShift k n))
    (f : HierarchyTwistedProfile T k E) (g : HierarchyTwistedProfile T k F) :
    (restrictBilinear L hL f g).val = L f.val g.val := rfl

/-- The full within-slab derivative commutes with each twisted lattice shift. -/
theorem fderivWithin_twistedPeriodic (f : HierarchyTwistedProfile T k E) (n : Fin 3 → ℤ) :
    Function.Periodic (fderivWithin ℝ f.val.val.val (hierarchyProfileSlab T)) (hierarchyLatticeShift k n) := by
  intro x
  have heq : (fun y => f.val.val.val (y + hierarchyLatticeShift k n)) = f.val.val.val :=
    funext (twistedPeriodic f n)
  have hd := fderivWithin_comp_add_right (𝕜 := ℝ) (f := f.val.val.val)
    (s := hierarchyProfileSlab T) (x := x) (hierarchyLatticeShift k n)
  rw [heq, hierarchyLatticeShift_vadd_slab] at hd
  exact hd.symm

/-- The actual slab derivative as a linear map of twisted profiles. -/
def derivative (hT : 0 < T) :
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k (HierarchyProfilePoint →L[ℝ] E) :=
  restrict (HierarchyPeriodicProfile.derivative hT) fun f => twisted_of_onSlab _ fun n x hx => by
    rw [HierarchyPeriodicProfile.derivative_val,
      HierarchySmoothProfile.derivative_apply hT f.val.val (add_hierarchyLatticeShift_mem_slab.mpr hx),
      HierarchySmoothProfile.derivative_apply hT f.val.val hx, fderivWithin_twistedPeriodic f n x]

@[simp] theorem derivative_val (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    (derivative hT f).val = HierarchyPeriodicProfile.derivative hT f.val := rfl

/-- Bounded linear postcomposition preserves twisted periodicity. -/
def map (L : E →L[ℝ] F) : HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k F :=
  restrict (HierarchyPeriodicProfile.map L) fun f => twisted_of_onSlab _ fun n x hx => by
    rw [HierarchyPeriodicProfile.map_val,
      HierarchySmoothProfile.map_apply L f.val.val (add_hierarchyLatticeShift_mem_slab.mpr hx),
      HierarchySmoothProfile.map_apply L f.val.val hx, twistedPeriodic f n x]

@[simp] theorem map_val (L : E →L[ℝ] F) (f : HierarchyTwistedProfile T k E) :
    (map L f).val = HierarchyPeriodicProfile.map L f.val := rfl

/-- Pointwise application preserves twisted periodicity in both arguments. -/
def applyField : HierarchyTwistedProfile T k (E →L[ℝ] F) →ₗ[ℝ]
    HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k F :=
  restrictBilinear HierarchyPeriodicProfile.applyField fun L f =>
    twisted_of_onSlab _ fun n x hx => by
      rw [HierarchyPeriodicProfile.applyField_val,
        HierarchySmoothProfile.applyField_eval L.val.val f.val.val (add_hierarchyLatticeShift_mem_slab.mpr hx),
        HierarchySmoothProfile.applyField_eval L.val.val f.val.val hx,
        twistedPeriodic L n x, twistedPeriodic f n x]

@[simp] theorem applyField_val (L : HierarchyTwistedProfile T k (E →L[ℝ] F))
    (f : HierarchyTwistedProfile T k E) :
    (applyField L f).val = HierarchyPeriodicProfile.applyField L.val f.val := rfl

end HierarchyTwistedProfile

end ProfileSpace

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

private theorem phaseMean_translate {f : ℝ → Vec3} (hper : Function.Periodic f 1) (b : ℝ) :
    phaseMean (fun s => f (s + b)) = phaseMean f := by
  unfold phaseMean
  rw [intervalIntegral.integral_comp_add_right]
  simpa only [zero_add, add_comm (1 : ℝ) b] using hper.intervalIntegral_add_eq b 0

/-- Integrating over a full phase removes the twist and gives a genuinely
label-periodic field for the torus mean solver. -/
theorem average_labelPeriodic (hT : 0 < T) (f : VP) :
    LabelPeriodic (HierarchySmoothProfile.profilePhaseAverage hT f.val.val) := by
  intro t ht n a
  have h₁ : (t, a + latticeVector n, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have h₂ : (t, a, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  change (HierarchySmoothProfile.profilePhaseAverage hT f.val.val).val (t, a + latticeVector n, 0) =
    (HierarchySmoothProfile.profilePhaseAverage hT f.val.val).val (t, a, 0)
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val h₁,
    HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val h₂]
  calc
    _ = phaseMean (fun s => f.val.val.val
        (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ)) :=
      (phaseMean_translate (HierarchyPeriodicProfile.phasePeriodic f.val t (a + latticeVector n))
        ⟪k, latticeVector n⟫_ℝ).symm
    _ = _ := congrArg phaseMean (funext fun s => twistedSlice f t a s n)

/-- The concrete phase average closes the twisted space. -/
def profilePhaseAverage (hT : 0 < T) : VP →ₗ[ℝ] VP :=
  restrict (HierarchyPeriodicProfile.profilePhaseAverage hT) fun f =>
    (ofPhaseIndependent (k := k) _
      (HierarchyPeriodicProfile.profilePhaseAverage_independent hT f.val.val)
      (average_labelPeriodic hT f)).property

@[simp] theorem profilePhaseAverage_val (hT : 0 < T) (f : VP) :
    (profilePhaseAverage hT f).val = HierarchyPeriodicProfile.profilePhaseAverage hT f.val := rfl

private theorem material_twisted (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    ∀ n : Fin 3 → ℤ, Function.Periodic
      ((HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).material f.val).val.val
      (hierarchyLatticeShift k n) := by
  apply twisted_of_onSlab
  intro n x hx
  have hx' := (add_hierarchyLatticeShift_mem_slab (k := k) (n := n)).mpr hx
  rw [HierarchyPeriodicProfile.periodicHierarchyOperators_material_val,
    HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val.val M.val.val κ.val.val
      f.val.val hx',
    HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val.val M.val.val κ.val.val
      f.val.val hx,
    fderivWithin_twistedPeriodic f n x, twistedPeriodic M n x, twistedPeriodic f n x]

private theorem labelGradient_twisted (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) :
    ∀ n : Fin 3 → ℤ, Function.Periodic
      ((HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).labelGrad p.val).val.val
      (hierarchyLatticeShift k n) := by
  apply twisted_of_onSlab
  intro n x hx
  have hx' := (add_hierarchyLatticeShift_mem_slab (k := k) (n := n)).mpr hx
  rw [HierarchyPeriodicProfile.periodicHierarchyOperators_labelGrad_val]
  change (HierarchySmoothProfile.labelGradient hT G.val.val p.val.val).val
    (x + hierarchyLatticeShift k n) =
      (HierarchySmoothProfile.labelGradient hT G.val.val p.val.val).val x
  rw [HierarchySmoothProfile.labelGradient_apply hT G.val.val p.val.val hx',
    HierarchySmoothProfile.labelGradient_apply hT G.val.val p.val.val hx]
  simp only [fderivWithin_twistedPeriodic p n x, twistedPeriodic G n x]

private theorem phaseGradient_twisted (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) :
    ∀ n : Fin 3 → ℤ, Function.Periodic
      ((HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).phaseGrad p.val).val.val
      (hierarchyLatticeShift k n) := by
  apply twisted_of_onSlab
  intro n x hx
  have hx' := (add_hierarchyLatticeShift_mem_slab (k := k) (n := n)).mpr hx
  rw [HierarchyPeriodicProfile.periodicHierarchyOperators_phaseGrad_val]
  change (HierarchySmoothProfile.phaseGradient hT κ.val.val p.val.val).val
    (x + hierarchyLatticeShift k n) =
      (HierarchySmoothProfile.phaseGradient hT κ.val.val p.val.val).val x
  rw [HierarchySmoothProfile.phaseGradient_apply hT κ.val.val p.val.val hx',
    HierarchySmoothProfile.phaseGradient_apply hT κ.val.val p.val.val hx,
    fderivWithin_twistedPeriodic p n x, twistedPeriodic κ n x]

private theorem labelAdvection_twisted (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ∀ n : Fin 3 → ℤ, Function.Periodic
      ((HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).labelAdv f.val g.val).val.val
      (hierarchyLatticeShift k n) := by
  apply twisted_of_onSlab
  intro n x hx
  have hx' := (add_hierarchyLatticeShift_mem_slab (k := k) (n := n)).mpr hx
  rw [HierarchyPeriodicProfile.periodicHierarchyOperators_labelAdv_val]
  let D := HierarchySmoothProfile.labelDirections G.val.val
  change (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val
    (x + hierarchyLatticeShift k n) = (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val x
  rw [HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx',
    HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx]
  dsimp only [D]
  rw [HierarchySmoothProfile.labelDirections_apply G.val.val f.val.val hx',
    HierarchySmoothProfile.labelDirections_apply G.val.val f.val.val hx,
    fderivWithin_twistedPeriodic g n x, twistedPeriodic G n x, twistedPeriodic f n x]

private theorem phaseAdvection_twisted (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ∀ n : Fin 3 → ℤ, Function.Periodic
      ((HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).phaseAdv f.val g.val).val.val
      (hierarchyLatticeShift k n) := by
  apply twisted_of_onSlab
  intro n x hx
  have hx' := (add_hierarchyLatticeShift_mem_slab (k := k) (n := n)).mpr hx
  rw [HierarchyPeriodicProfile.periodicHierarchyOperators_phaseAdv_val]
  let D := HierarchySmoothProfile.phaseDirections κ.val.val
  change (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val
    (x + hierarchyLatticeShift k n) = (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val x
  rw [HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx',
    HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx]
  dsimp only [D]
  rw [HierarchySmoothProfile.phaseDirections_apply κ.val.val f.val.val hx',
    HierarchySmoothProfile.phaseDirections_apply κ.val.val f.val.val hx,
    fderivWithin_twistedPeriodic g n x, twistedPeriodic κ n x, twistedPeriodic f n x]

/-- The actual material, pressure-gradient and advection maps act on
twisted profiles. The coframe, material matrix and wave vector can enter
from `ofPhaseIndependent` when they are periodic in the labels. -/
def twistedHierarchyOperators (hT : 0 < T) (G M : VPmap) (κ : VP) : HierarchyOperators VP SP :=
  let A := HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val
  { material := restrict A.material (material_twisted hT G M κ)
    labelGrad := restrict A.labelGrad (labelGradient_twisted hT G M κ)
    phaseGrad := restrict A.phaseGrad (phaseGradient_twisted hT G M κ)
    labelAdv := restrictBilinear A.labelAdv (labelAdvection_twisted hT G M κ)
    phaseAdv := restrictBilinear A.phaseAdv (phaseAdvection_twisted hT G M κ)
    average := profilePhaseAverage hT }

@[simp] theorem twistedHierarchyOperators_material_val (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    ((twistedHierarchyOperators hT G M κ).material f).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).material f.val := rfl

@[simp] theorem twistedHierarchyOperators_labelGrad_val (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) :
    ((twistedHierarchyOperators hT G M κ).labelGrad p).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).labelGrad p.val := rfl

@[simp] theorem twistedHierarchyOperators_phaseGrad_val (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) :
    ((twistedHierarchyOperators hT G M κ).phaseGrad p).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).phaseGrad p.val := rfl

@[simp] theorem twistedHierarchyOperators_labelAdv_val (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ((twistedHierarchyOperators hT G M κ).labelAdv f g).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).labelAdv f.val g.val := rfl

@[simp] theorem twistedHierarchyOperators_phaseAdv_val (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ((twistedHierarchyOperators hT G M κ).phaseAdv f g).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).phaseAdv f.val g.val := rfl

@[simp] theorem twistedHierarchyOperators_average_val (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    ((twistedHierarchyOperators hT G M κ).average f).val =
      (HierarchyPeriodicProfile.periodicHierarchyOperators hT G.val M.val κ.val).average f.val := rfl

/-- A hierarchy average is a phase-independent, label-periodic mean profile. -/
theorem average_is_mean (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    let mean := ((twistedHierarchyOperators hT G M κ).average f).val.val
    HierarchyPeriodicProfile.PhaseIndependent mean ∧ LabelPeriodic mean :=
  ⟨HierarchyPeriodicProfile.profilePhaseAverage_independent hT f.val.val,
    average_labelPeriodic hT f⟩

theorem phaseGrad_eq_zero_of_independent (hT : 0 < T) (G M : VPmap) (κ : VP)
    (p : SP) (hp : HierarchyPeriodicProfile.PhaseIndependent p.val.val) :
    (twistedHierarchyOperators hT G M κ).phaseGrad p = 0 :=
  Subtype.ext (HierarchyPeriodicProfile.phaseGrad_eq_zero_of_independent hT G.val M.val κ.val p.val hp)

theorem phaseAdv_eq_zero_of_independent (hT : 0 < T) (G M : VPmap) (κ u v : VP)
    (hv : HierarchyPeriodicProfile.PhaseIndependent v.val.val) :
    (twistedHierarchyOperators hT G M κ).phaseAdv u v = 0 :=
  Subtype.ext
    (HierarchyPeriodicProfile.phaseAdv_eq_zero_of_independent hT G.val M.val κ.val u.val v.val hv)

theorem phaseAdv_eq_zero_of_transverse (hT : 0 < T) (G M : VPmap) (κ u v : VP)
    (hu : ∀ x ∈ hierarchyProfileSlab T, ⟪κ.val.val.val x, u.val.val.val x⟫_ℝ = 0) :
    (twistedHierarchyOperators hT G M κ).phaseAdv u v = 0 :=
  Subtype.ext
    (HierarchyPeriodicProfile.phaseAdv_eq_zero_of_transverse hT G.val M.val κ.val u.val v.val hu)

theorem average_idempotent (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    let A := twistedHierarchyOperators hT G M κ
    A.average (A.average f) = A.average f :=
  Subtype.ext (HierarchyPeriodicProfile.average_idempotent hT G.val M.val κ.val f.val)

theorem average_meanPhaseAdv (hT : 0 < T) (G M : VPmap) (κ B Y : VP)
    (hκ : HierarchyPeriodicProfile.PhaseIndependent κ.val.val)
    (hB : (twistedHierarchyOperators hT G M κ).average B = B) :
    let A := twistedHierarchyOperators hT G M κ
    A.average (A.phaseAdv B Y) = 0 :=
  Subtype.ext (HierarchyPeriodicProfile.average_meanPhaseAdv hT G.val M.val κ.val hκ B.val Y.val
    (congrArg Subtype.val hB))

end HierarchyTwistedProfile

/-- The joint reflection fixes time and reverses both label and phase. -/
def hierarchyProfileReflection : HierarchyProfilePoint →L[ℝ] HierarchyProfilePoint :=
  (ContinuousLinearMap.id ℝ ℝ).prodMap (-(ContinuousLinearMap.id ℝ (Vec3 × ℝ)))

@[simp] theorem hierarchyProfileReflection_apply (x : HierarchyProfilePoint) :
    hierarchyProfileReflection x = (x.1, -x.2.1, -x.2.2) := rfl

@[simp] theorem hierarchyProfileReflection_mem_slab {T : ℝ} {x : HierarchyProfilePoint} :
    hierarchyProfileReflection x ∈ hierarchyProfileSlab T ↔ x ∈ hierarchyProfileSlab T := by
  simp [hierarchyProfileSlab]

/-- The reflected profile has sign -1 for velocity and sign +1
for pressure and even label coefficients. -/
def HierarchyProfileReflectionParity {E : Type*} [SMul ℝ E]
    (sign : ℝ) (f : HierarchyProfilePoint → E) : Prop :=
  ∀ x, f (hierarchyProfileReflection x) = sign • f x

private theorem periodic_comp_hierarchyProfileReflection {E : Type*}
    {f : HierarchyProfilePoint → E} {d : HierarchyProfilePoint}
    (hD : hierarchyProfileReflection d = -d) (hf : Function.Periodic f d) :
    Function.Periodic (fun x => f (hierarchyProfileReflection x)) d := by
  intro x
  change f (hierarchyProfileReflection (x + d)) = f (hierarchyProfileReflection x)
  rw [map_add, hD, ← sub_eq_add_neg]
  exact hf.sub_eq _

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Reflection is an actual linear self-map on the twisted profile space. -/
def reflection : HierarchyTwistedProfile T k E →ₗ[ℝ] HierarchyTwistedProfile T k E where
  toFun f := by
    let fR (x : HierarchyProfilePoint) := f.val.val.val (hierarchyProfileReflection x)
    have hreg : ContDiffOn ℝ ∞ fR (hierarchyProfileSlab T) :=
      (HierarchySmoothProfile.smooth f.val.val).comp hierarchyProfileReflection.contDiff.contDiffOn
        (fun _ hx => hierarchyProfileReflection_mem_slab.mpr hx)
    have hout : ∀ x ∉ hierarchyProfileSlab T, fR x = 0 := fun x hx =>
      HierarchySmoothProfile.eq_zero_outside f.val.val
        (fun hx' => hx (hierarchyProfileReflection_mem_slab.mp hx'))
    let fSmooth : HierarchySmoothProfile T E := ⟨fR, hreg, hout⟩
    let fPeriodic : HierarchyPeriodicProfile T E := ⟨fSmooth,
      periodic_comp_hierarchyProfileReflection (by simp [hierarchyPhasePeriod])
        (HierarchyPeriodicProfile.periodic f.val)⟩
    exact ⟨fPeriodic, fun n =>
      periodic_comp_hierarchyProfileReflection (by simp [hierarchyLatticeShift]) (twistedPeriodic f n)⟩
  map_add' f g := by
    apply HierarchyTwistedProfile.ext
    intro x _
    rfl
  map_smul' c f := by
    apply HierarchyTwistedProfile.ext
    intro x _
    rfl

@[simp] theorem reflection_eval (f : HierarchyTwistedProfile T k E) (x : HierarchyProfilePoint) :
    (reflection f).val.val.val x = f.val.val.val (hierarchyProfileReflection x) := rfl

theorem reflection_involutive (f : HierarchyTwistedProfile T k E) :
    reflection (reflection f) = f := by
  apply HierarchyTwistedProfile.ext
  intro x _
  simp only [reflection_eval, hierarchyProfileReflection_apply, neg_neg, Prod.mk.eta]

theorem reflection_eq_smul_iff (sign : ℝ) (f : HierarchyTwistedProfile T k E) :
    reflection f = sign • f ↔ HierarchyProfileReflectionParity sign f.val.val.val := by
  constructor
  · intro h x
    exact congrArg (fun u : HierarchyTwistedProfile T k E => u.val.val.val x) h
  · intro h
    exact HierarchyTwistedProfile.ext fun x _ => h x

end HierarchyTwistedProfile

/-- Differentiating reflection on the closed slab preserves the time
direction and reverses every slow label and fast phase direction. -/
theorem fderivWithin_hierarchyProfileReflection {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T sign : ℝ} (hT : 0 < T)
    (f : HierarchySmoothProfile T E) (hf : HierarchyProfileReflectionParity sign f.val)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) (d : HierarchyProfilePoint) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) (hierarchyProfileReflection x)
        (hierarchyProfileReflection d) =
      sign • fderivWithin ℝ f.val (hierarchyProfileSlab T) x d := by
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  have hd := (HierarchySmoothProfile.smooth f).differentiableOn (by simp)
  have hUnique := uniqueDiffOn_hierarchyProfileSlab hT x hx
  have h := ((hd _ hxR).hasFDerivWithinAt.comp x hierarchyProfileReflection.hasFDerivAt.hasFDerivWithinAt
    (fun _ hy => hierarchyProfileReflection_mem_slab.mpr hy)).fderivWithin hUnique
  change fderivWithin ℝ (fun y => f.val (hierarchyProfileReflection y)) (hierarchyProfileSlab T) x =
    (fderivWithin ℝ f.val (hierarchyProfileSlab T) (hierarchyProfileReflection x)).comp
      hierarchyProfileReflection at h
  rw [funext hf] at h
  change fderivWithin ℝ (sign • f.val) (hierarchyProfileSlab T) x = _ at h
  rw [fderivWithin_const_smul hUnique (hd x hx) sign] at h
  exact (congrArg (fun A : HierarchyProfilePoint →L[ℝ] E => A d) h).symm

/-- The unreflected direction of a spatial derivative reverses the
profile sign at the reflected point. -/
theorem fderivWithin_hierarchyProfileReflection_of_reversed {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {T sign : ℝ} (hT : 0 < T)
    (f : HierarchySmoothProfile T E) (hf : HierarchyProfileReflectionParity sign f.val)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T)
    {d : HierarchyProfilePoint} (hd : hierarchyProfileReflection d = -d) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) (hierarchyProfileReflection x) d =
      (-sign) • fderivWithin ℝ f.val (hierarchyProfileSlab T) x d := by
  have h := fderivWithin_hierarchyProfileReflection hT f hf hx d
  rw [hd, map_neg] at h
  simpa only [neg_neg, neg_smul] using congrArg Neg.neg h

private theorem reflectionParity_of_onSlab {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T sign : ℝ} (f : HierarchySmoothProfile T E)
    (h : ∀ x ∈ hierarchyProfileSlab T,
      f.val (hierarchyProfileReflection x) = sign • f.val x) :
    HierarchyProfileReflectionParity sign f.val := by
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact h x hx
  · rw [HierarchySmoothProfile.eq_zero_outside f
      (fun hr => hx (hierarchyProfileReflection_mem_slab.mp hr)),
      HierarchySmoothProfile.eq_zero_outside f hx, smul_zero]

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- The material derivative preserves the reflection sign with an even
material matrix. -/
theorem material_reflectionParity (hT : 0 < T) (G M : VPmap) (κ f : VP) (sign : ℝ)
    (hM : HierarchyProfileReflectionParity 1 M.val.val.val)
    (hf : HierarchyProfileReflectionParity sign f.val.val.val) :
    HierarchyProfileReflectionParity sign
      ((twistedHierarchyOperators hT G M κ).material f).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  have htime := fderivWithin_hierarchyProfileReflection hT f.val.val hf hx (1, 0, 0)
  have hdir : hierarchyProfileReflection ((1, 0, 0) : HierarchyProfilePoint) = (1, 0, 0) := by simp
  rw [hdir] at htime
  rw [twistedHierarchyOperators_material_val, HierarchyPeriodicProfile.periodicHierarchyOperators_material_val,
    HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val.val M.val.val κ.val.val
      f.val.val hxR,
    HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val.val M.val.val κ.val.val
      f.val.val hx,
    htime, hM x, one_smul, hf x, map_smul, smul_add]

/-- The label pressure gradient reverses the reflection sign with an even coframe. -/
theorem labelGrad_reflectionParity (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) (sign : ℝ)
    (hG : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hp : HierarchyProfileReflectionParity sign p.val.val.val) :
    HierarchyProfileReflectionParity (-sign)
      ((twistedHierarchyOperators hT G M κ).labelGrad p).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  rw [twistedHierarchyOperators_labelGrad_val,
    HierarchyPeriodicProfile.periodicHierarchyOperators_labelGrad_val]
  change (HierarchySmoothProfile.labelGradient hT G.val.val p.val.val).val (hierarchyProfileReflection x) =
    (-sign) • (HierarchySmoothProfile.labelGradient hT G.val.val p.val.val).val x
  rw [HierarchySmoothProfile.labelGradient_apply hT G.val.val p.val.val hxR,
    HierarchySmoothProfile.labelGradient_apply hT G.val.val p.val.val hx, hG x, one_smul,
    Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [fderivWithin_hierarchyProfileReflection_of_reversed hT p.val.val hp hx (by simp)]
  exact smul_assoc _ _ _

/-- The fast pressure gradient reverses the reflection sign with an
even transported wave vector. -/
theorem phaseGrad_reflectionParity (hT : 0 < T) (G M : VPmap) (κ : VP) (p : SP) (sign : ℝ)
    (hκ : HierarchyProfileReflectionParity 1 κ.val.val.val)
    (hp : HierarchyProfileReflectionParity sign p.val.val.val) :
    HierarchyProfileReflectionParity (-sign)
      ((twistedHierarchyOperators hT G M κ).phaseGrad p).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  rw [twistedHierarchyOperators_phaseGrad_val,
    HierarchyPeriodicProfile.periodicHierarchyOperators_phaseGrad_val]
  change (HierarchySmoothProfile.phaseGradient hT κ.val.val p.val.val).val (hierarchyProfileReflection x) =
    (-sign) • (HierarchySmoothProfile.phaseGradient hT κ.val.val p.val.val).val x
  rw [HierarchySmoothProfile.phaseGradient_apply hT κ.val.val p.val.val hxR,
    HierarchySmoothProfile.phaseGradient_apply hT κ.val.val p.val.val hx, hκ x, one_smul,
    fderivWithin_hierarchyProfileReflection_of_reversed hT p.val.val hp hx (by simp)]
  exact smul_assoc _ _ _

/-- Label advection has sign minus the product of the two profile signs. -/
theorem labelAdv_reflectionParity (hT : 0 < T) (G M : VPmap) (κ f g : VP) (signF signG : ℝ)
    (hG : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hf : HierarchyProfileReflectionParity signF f.val.val.val)
    (hg : HierarchyProfileReflectionParity signG g.val.val.val) :
    HierarchyProfileReflectionParity (-(signF * signG))
      ((twistedHierarchyOperators hT G M κ).labelAdv f g).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  rw [twistedHierarchyOperators_labelAdv_val, HierarchyPeriodicProfile.periodicHierarchyOperators_labelAdv_val]
  let D := HierarchySmoothProfile.labelDirections G.val.val
  change (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val (hierarchyProfileReflection x) =
    (-(signF * signG)) • (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val x
  rw [HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hxR,
    HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx]
  dsimp only [D]
  rw [HierarchySmoothProfile.labelDirections_apply G.val.val f.val.val hxR,
    HierarchySmoothProfile.labelDirections_apply G.val.val f.val.val hx,
    hG x, one_smul, hf x, map_smul]
  let a := G.val.val.val x (f.val.val.val x)
  have hdir : ((0, signF • a, 0) : HierarchyProfilePoint) =
      signF • ((0, a, 0) : HierarchyProfilePoint) := by simp
  change fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) (hierarchyProfileReflection x)
      (0, signF • a, 0) =
    (-(signF * signG)) • fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) x (0, a, 0)
  rw [hdir, map_smul,
    fderivWithin_hierarchyProfileReflection_of_reversed hT g.val.val hg hx (by simp),
    smul_smul, mul_neg]

/-- Fast phase advection has sign minus the product of the profile signs. -/
theorem phaseAdv_reflectionParity (hT : 0 < T) (G M : VPmap) (κ f g : VP) (signF signG : ℝ)
    (hκ : HierarchyProfileReflectionParity 1 κ.val.val.val)
    (hf : HierarchyProfileReflectionParity signF f.val.val.val)
    (hg : HierarchyProfileReflectionParity signG g.val.val.val) :
    HierarchyProfileReflectionParity (-(signF * signG))
      ((twistedHierarchyOperators hT G M κ).phaseAdv f g).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  rw [twistedHierarchyOperators_phaseAdv_val, HierarchyPeriodicProfile.periodicHierarchyOperators_phaseAdv_val]
  let D := HierarchySmoothProfile.phaseDirections κ.val.val
  change (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val (hierarchyProfileReflection x) =
    (-(signF * signG)) • (HierarchySmoothProfile.advect hT D f.val.val g.val.val).val x
  rw [HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hxR,
    HierarchySmoothProfile.advect_apply hT D f.val.val g.val.val hx]
  dsimp only [D]
  rw [HierarchySmoothProfile.phaseDirections_apply κ.val.val f.val.val hxR,
    HierarchySmoothProfile.phaseDirections_apply κ.val.val f.val.val hx,
    hκ x, one_smul, hf x, real_inner_smul_right]
  let c := ⟪κ.val.val.val x, f.val.val.val x⟫_ℝ
  have hdir : ((0, 0, signF * c) : HierarchyProfilePoint) =
      signF • ((0, 0, c) : HierarchyProfilePoint) := by simp
  change fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) (hierarchyProfileReflection x)
      (0, 0, signF * c) =
    (-(signF * signG)) • fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) x (0, 0, c)
  rw [hdir, map_smul,
    fderivWithin_hierarchyProfileReflection_of_reversed hT g.val.val hg hx (by simp),
    smul_smul, mul_neg]

private theorem phaseMean_reflect {f : ℝ → Vec3} (hf : Function.Periodic f 1) :
    phaseMean (fun s => f (-s)) = phaseMean f := by
  unfold phaseMean
  rw [intervalIntegral.integral_comp_neg, neg_zero]
  simpa only [neg_add_cancel, zero_add] using hf.intervalIntegral_add_eq (-1) 0

/-- The full-period phase average preserves reflection parity. -/
theorem average_reflectionParity (hT : 0 < T) (f : VP) (sign : ℝ)
    (hf : HierarchyProfileReflectionParity sign f.val.val.val) :
    HierarchyProfileReflectionParity sign (profilePhaseAverage hT f).val.val.val := by
  apply reflectionParity_of_onSlab
  intro x hx
  have hxR := hierarchyProfileReflection_mem_slab.mpr hx
  change (HierarchySmoothProfile.profilePhaseAverage hT f.val.val).val (hierarchyProfileReflection x) =
    sign • (HierarchySmoothProfile.profilePhaseAverage hT f.val.val).val x
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val hxR,
    HierarchySmoothProfile.profilePhaseAverage_apply hT f.val.val hx]
  simp only [hierarchyProfileReflection_apply]
  have herr (s : ℝ) :
      f.val.val.val (x.1, -x.2.1, s) = sign • f.val.val.val (x.1, x.2.1, -s) := by
    simpa only [hierarchyProfileReflection_apply, neg_neg] using hf (x.1, x.2.1, -s)
  rw [funext herr, phaseMean_const_smul,
    phaseMean_reflect (HierarchyPeriodicProfile.phasePeriodic f.val x.1 x.2.1)]

end HierarchyTwistedProfile

end

end TorusEuler

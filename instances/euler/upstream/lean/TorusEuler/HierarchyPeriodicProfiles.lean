import TorusEuler.HierarchyConcreteOperators

/-! Actual unit-period phase profiles for the concrete finite hierarchy. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace Pointwise

namespace TorusEuler

noncomputable section

/-- One period in the phase direction of the joint profile domain. -/
def hierarchyPhasePeriod : HierarchyProfilePoint := (0, 0, 1)

@[simp] theorem add_hierarchyPhasePeriod (x : HierarchyProfilePoint) :
    x + hierarchyPhasePeriod = (x.1, x.2.1, x.2.2 + 1) := by
  rcases x with ⟨t, a, s⟩
  simp [hierarchyPhasePeriod]

@[simp] theorem add_hierarchyPhasePeriod_mem_slab {T : ℝ} {x : HierarchyProfilePoint} :
    x + hierarchyPhasePeriod ∈ hierarchyProfileSlab T ↔ x ∈ hierarchyProfileSlab T := by
  simp [hierarchyProfileSlab]

theorem hierarchyPhasePeriod_vadd_slab (T : ℝ) :
    hierarchyPhasePeriod +ᵥ hierarchyProfileSlab T = hierarchyProfileSlab T := by
  ext x
  rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add]
  simp [hierarchyProfileSlab, hierarchyPhasePeriod]

section ProfileSpace

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The smooth slab profiles that are periodic under one phase translation. -/
def hierarchyPeriodicProfileSubmodule (T : ℝ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] : Submodule ℝ (HierarchySmoothProfile T E) where
  carrier := {f | Function.Periodic f.val hierarchyPhasePeriod}
  zero_mem' := fun _ => rfl
  add_mem' := by
    intro f g hf hg x
    change f.val (x + hierarchyPhasePeriod) + g.val (x + hierarchyPhasePeriod) =
      f.val x + g.val x
    exact congrArg₂ (· + ·) (hf x) (hg x)
  smul_mem' := by
    intro c f hf x
    change c • f.val (x + hierarchyPhasePeriod) = c • f.val x
    exact congrArg (c • ·) (hf x)

abbrev HierarchyPeriodicProfile (T : ℝ) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] := hierarchyPeriodicProfileSubmodule T E

namespace HierarchyPeriodicProfile

variable {T : ℝ}

/-- Phase independence only concerns values on the time slab. -/
def PhaseIndependent (f : HierarchySmoothProfile T E) : Prop :=
  ∀ x ∈ hierarchyProfileSlab T, ∀ s : ℝ, f.val (x.1, x.2.1, s) = f.val x

theorem periodic (f : HierarchyPeriodicProfile T E) :
    Function.Periodic f.val.val hierarchyPhasePeriod := f.property

theorem phasePeriodic (f : HierarchyPeriodicProfile T E) (t : ℝ) (a : Vec3) :
    Function.Periodic (fun s : ℝ => f.val.val (t, a, s)) 1 := by
  intro s
  simpa only [add_hierarchyPhasePeriod] using (periodic f (t, a, s))

theorem ext {f g : HierarchyPeriodicProfile T E}
    (h : ∀ x ∈ hierarchyProfileSlab T, f.val.val x = g.val.val x) : f = g :=
  Subtype.ext (HierarchySmoothProfile.ext h)

private theorem periodic_of_onSlab (f : HierarchySmoothProfile T E)
    (h : ∀ x ∈ hierarchyProfileSlab T, f.val (x + hierarchyPhasePeriod) = f.val x) :
    Function.Periodic f.val hierarchyPhasePeriod := by
  intro x
  by_cases hx : x ∈ hierarchyProfileSlab T
  · exact h x hx
  · rw [HierarchySmoothProfile.eq_zero_outside f (fun h => hx (add_hierarchyPhasePeriod_mem_slab.mp h)),
      HierarchySmoothProfile.eq_zero_outside f hx]

/-- A smooth phase-periodic function gives a periodic profile after taking
its zero extension outside the time slab. -/
def ofSmooth (f : HierarchyProfilePoint → E)
    (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T))
    (hper : Function.Periodic f hierarchyPhasePeriod) : HierarchyPeriodicProfile T E :=
  ⟨HierarchySmoothProfile.ofSmooth f hf, periodic_of_onSlab _ fun x hx => by
    rw [HierarchySmoothProfile.ofSmooth_apply hf (add_hierarchyPhasePeriod_mem_slab.mpr hx),
      HierarchySmoothProfile.ofSmooth_apply hf hx, hper x]⟩

theorem ofSmooth_apply {f : HierarchyProfilePoint → E}
    (hf : ContDiffOn ℝ ∞ f (hierarchyProfileSlab T))
    (hper : Function.Periodic f hierarchyPhasePeriod) {x : HierarchyProfilePoint}
    (hx : x ∈ hierarchyProfileSlab T) : (ofSmooth f hf hper).val.val x = f x :=
  HierarchySmoothProfile.ofSmooth_apply hf hx

/-- Phase-independent coefficients such as the coframe and the
transported wave vector belong to the periodic space. -/
def ofPhaseIndependent (f : HierarchySmoothProfile T E)
    (hf : PhaseIndependent f) : HierarchyPeriodicProfile T E :=
  ⟨f, periodic_of_onSlab f fun x hx => by
    rw [add_hierarchyPhasePeriod]
    exact hf x hx _⟩

@[simp] theorem ofPhaseIndependent_val (f : HierarchySmoothProfile T E)
    (h : PhaseIndependent f) : (ofPhaseIndependent f h).val = f := rfl

/-- A solver returning phase-periodic slices on the slab gives an
element of the periodic submodule without changing the underlying profile. -/
def ofPeriodicSlices (f : HierarchySmoothProfile T E)
    (h : ∀ t ∈ Icc 0 T, ∀ a : Vec3,
      Function.Periodic (fun s : ℝ => f.val (t, a, s)) 1) : HierarchyPeriodicProfile T E :=
  ⟨f, periodic_of_onSlab f fun x hx => by
    rw [add_hierarchyPhasePeriod]
    exact h x.1 hx.1 x.2.1 x.2.2⟩

@[simp] theorem ofPeriodicSlices_val (f : HierarchySmoothProfile T E)
    (h : ∀ t ∈ Icc 0 T, ∀ a : Vec3,
      Function.Periodic (fun s : ℝ => f.val (t, a, s)) 1) :
    (ofPeriodicSlices f h).val = f := rfl

/-- Restrict a concrete linear map using its phase-periodicity proof. -/
def restrict (L : HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F)
    (hL : ∀ f : HierarchyPeriodicProfile T E, Function.Periodic (L f.val).val hierarchyPhasePeriod) :
    HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F :=
  L.restrict fun f hf => hL ⟨f, hf⟩

@[simp] theorem restrict_val (L : HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F)
    (hL : ∀ f : HierarchyPeriodicProfile T E, Function.Periodic (L f.val).val hierarchyPhasePeriod)
    (f : HierarchyPeriodicProfile T E) : (restrict L hL f).val = L f.val := rfl

/-- Restrict a concrete bilinear map in both arguments and its result. -/
def restrictBilinear
    (L : HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F →ₗ[ℝ] HierarchySmoothProfile T G)
    (hL : ∀ (f : HierarchyPeriodicProfile T E) (g : HierarchyPeriodicProfile T F),
      Function.Periodic (L f.val g.val).val hierarchyPhasePeriod) :
    HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F →ₗ[ℝ] HierarchyPeriodicProfile T G where
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
    (L : HierarchySmoothProfile T E →ₗ[ℝ] HierarchySmoothProfile T F →ₗ[ℝ] HierarchySmoothProfile T G)
    (hL : ∀ (f : HierarchyPeriodicProfile T E) (g : HierarchyPeriodicProfile T F),
      Function.Periodic (L f.val g.val).val hierarchyPhasePeriod)
    (f : HierarchyPeriodicProfile T E) (g : HierarchyPeriodicProfile T F) :
    (restrictBilinear L hL f g).val = L f.val g.val := rfl

/-- The slab derivative, including at either time endpoint, commutes
with phase translations. -/
theorem fderivWithin_periodic (f : HierarchyPeriodicProfile T E) :
    Function.Periodic (fderivWithin ℝ f.val.val (hierarchyProfileSlab T)) hierarchyPhasePeriod := by
  intro x
  have heq : (fun y => f.val.val (y + hierarchyPhasePeriod)) = f.val.val := funext (periodic f)
  have hd := fderivWithin_comp_add_right (𝕜 := ℝ) (f := f.val.val)
    (s := hierarchyProfileSlab T) (x := x) hierarchyPhasePeriod
  rw [heq, hierarchyPhasePeriod_vadd_slab] at hd
  exact hd.symm

/-- The actual slab derivative restricted to the periodic profiles. -/
def derivative (hT : 0 < T) :
    HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T (HierarchyProfilePoint →L[ℝ] E) :=
  restrict (HierarchySmoothProfile.derivative hT) fun f => periodic_of_onSlab _ fun x hx => by
    rw [HierarchySmoothProfile.derivative_apply hT f.val (add_hierarchyPhasePeriod_mem_slab.mpr hx),
      HierarchySmoothProfile.derivative_apply hT f.val hx]
    exact fderivWithin_periodic f x

@[simp] theorem derivative_val (hT : 0 < T) (f : HierarchyPeriodicProfile T E) :
    (derivative hT f).val = HierarchySmoothProfile.derivative hT f.val := rfl

/-- Bounded linear postcomposition preserves phase periodicity. -/
def map (L : E →L[ℝ] F) : HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F :=
  restrict (HierarchySmoothProfile.map L) fun f => periodic_of_onSlab _ fun x hx => by
    rw [HierarchySmoothProfile.map_apply L f.val (add_hierarchyPhasePeriod_mem_slab.mpr hx),
      HierarchySmoothProfile.map_apply L f.val hx, periodic f x]

@[simp] theorem map_val (L : E →L[ℝ] F) (f : HierarchyPeriodicProfile T E) :
    (map L f).val = HierarchySmoothProfile.map L f.val := rfl

/-- Pointwise multiplication by phase-periodic operator profiles. -/
def applyField : HierarchyPeriodicProfile T (E →L[ℝ] F) →ₗ[ℝ]
    HierarchyPeriodicProfile T E →ₗ[ℝ] HierarchyPeriodicProfile T F :=
  restrictBilinear HierarchySmoothProfile.applyField fun L f =>
    periodic_of_onSlab _ fun x hx => by
      rw [HierarchySmoothProfile.applyField_eval L.val f.val (add_hierarchyPhasePeriod_mem_slab.mpr hx),
        HierarchySmoothProfile.applyField_eval L.val f.val hx, periodic L x, periodic f x]

@[simp] theorem applyField_val (L : HierarchyPeriodicProfile T (E →L[ℝ] F))
    (f : HierarchyPeriodicProfile T E) :
    (applyField L f).val = HierarchySmoothProfile.applyField L.val f.val := rfl

end HierarchyPeriodicProfile

end ProfileSpace

namespace HierarchyPeriodicProfile

variable {T : ℝ}

local notation "VP" => HierarchyPeriodicProfile T Vec3
local notation "SP" => HierarchyPeriodicProfile T ℝ
local notation "VPmap" => HierarchyPeriodicProfile T (Vec3 →L[ℝ] Vec3)

/-- The smooth concrete phase average is independent of the phase. -/
theorem profilePhaseAverage_independent (hT : 0 < T) (f : HierarchySmoothProfile T Vec3) :
    PhaseIndependent (HierarchySmoothProfile.profilePhaseAverage hT f) := by
  intro x hx s
  have hs : (x.1, x.2.1, s) ∈ hierarchyProfileSlab T := ⟨hx.1, mem_univ _⟩
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT f hs,
    HierarchySmoothProfile.profilePhaseAverage_apply hT f hx]

/-- The concrete phase average acts on the periodic submodule. -/
def profilePhaseAverage (hT : 0 < T) : VP →ₗ[ℝ] VP :=
  restrict (HierarchySmoothProfile.profilePhaseAverage hT) fun f =>
    periodic (ofPhaseIndependent _ (profilePhaseAverage_independent hT f.val))

@[simp] theorem profilePhaseAverage_val (hT : 0 < T) (f : VP) :
    (profilePhaseAverage hT f).val = HierarchySmoothProfile.profilePhaseAverage hT f.val := rfl

theorem profilePhaseAverage_eq_self_of_independent (hT : 0 < T) (f : VP)
    (h : PhaseIndependent f.val) : profilePhaseAverage hT f = f :=
  Subtype.ext (HierarchySmoothProfile.profilePhaseAverage_eq_self_of_independent hT f.val h)

theorem phaseIndependent_of_profilePhaseAverage_eq_self (hT : 0 < T) (f : VP)
    (h : profilePhaseAverage hT f = f) : PhaseIndependent f.val := by
  rw [← h, profilePhaseAverage_val]
  exact profilePhaseAverage_independent hT f.val

theorem profilePhaseAverage_idempotent (hT : 0 < T) (f : VP) :
    profilePhaseAverage hT (profilePhaseAverage hT f) = profilePhaseAverage hT f :=
  profilePhaseAverage_eq_self_of_independent hT _
    (profilePhaseAverage_independent hT f.val)

private theorem concrete_material_periodic (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    Function.Periodic
      ((HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).material f.val).val
      hierarchyPhasePeriod := by
  apply periodic_of_onSlab
  intro x hx
  rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val M.val κ.val f.val
    (add_hierarchyPhasePeriod_mem_slab.mpr hx),
    HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val M.val κ.val f.val hx,
    fderivWithin_periodic f x, periodic M x, periodic f x]

private theorem concrete_labelGradient_periodic (hT : 0 < T) (G : VPmap) (f : SP) :
    Function.Periodic (HierarchySmoothProfile.labelGradient hT G.val f.val).val hierarchyPhasePeriod := by
  apply periodic_of_onSlab
  intro x hx
  rw [HierarchySmoothProfile.labelGradient_apply hT G.val f.val (add_hierarchyPhasePeriod_mem_slab.mpr hx),
    HierarchySmoothProfile.labelGradient_apply hT G.val f.val hx]
  simp only [fderivWithin_periodic f x, periodic G x]

private theorem concrete_phaseGradient_periodic (hT : 0 < T) (κ : VP) (f : SP) :
    Function.Periodic (HierarchySmoothProfile.phaseGradient hT κ.val f.val).val hierarchyPhasePeriod := by
  apply periodic_of_onSlab
  intro x hx
  rw [HierarchySmoothProfile.phaseGradient_apply hT κ.val f.val (add_hierarchyPhasePeriod_mem_slab.mpr hx),
    HierarchySmoothProfile.phaseGradient_apply hT κ.val f.val hx, fderivWithin_periodic f x, periodic κ x]

private theorem concrete_labelAdvection_periodic (hT : 0 < T) (G : VPmap) (f g : VP) :
    Function.Periodic
      (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val) f.val g.val).val
      hierarchyPhasePeriod := by
  apply periodic_of_onSlab
  intro x hx
  have hx' := add_hierarchyPhasePeriod_mem_slab.mpr hx
  rw [HierarchySmoothProfile.advect_apply hT _ f.val g.val hx',
    HierarchySmoothProfile.advect_apply hT _ f.val g.val hx,
    HierarchySmoothProfile.labelDirections_apply G.val f.val hx',
    HierarchySmoothProfile.labelDirections_apply G.val f.val hx,
    fderivWithin_periodic g x, periodic G x, periodic f x]

private theorem concrete_phaseAdvection_periodic (hT : 0 < T) (κ f g : VP) :
    Function.Periodic
      (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val) f.val g.val).val
      hierarchyPhasePeriod := by
  apply periodic_of_onSlab
  intro x hx
  have hx' := add_hierarchyPhasePeriod_mem_slab.mpr hx
  rw [HierarchySmoothProfile.advect_apply hT _ f.val g.val hx',
    HierarchySmoothProfile.advect_apply hT _ f.val g.val hx,
    HierarchySmoothProfile.phaseDirections_apply κ.val f.val hx',
    HierarchySmoothProfile.phaseDirections_apply κ.val f.val hx,
    fderivWithin_periodic g x, periodic κ x, periodic f x]

/-- The same concrete hierarchy operators on the actual periodic profile space. -/
def periodicHierarchyOperators (hT : 0 < T) (G M : VPmap) (κ : VP) : HierarchyOperators VP SP where
  material := restrict (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).material
    (concrete_material_periodic hT G M κ)
  labelGrad := restrict (HierarchySmoothProfile.labelGradient hT G.val)
    (concrete_labelGradient_periodic hT G)
  phaseGrad := restrict (HierarchySmoothProfile.phaseGradient hT κ.val)
    (concrete_phaseGradient_periodic hT κ)
  labelAdv := restrictBilinear (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val))
    (concrete_labelAdvection_periodic hT G)
  phaseAdv := restrictBilinear (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val))
    (concrete_phaseAdvection_periodic hT κ)
  average := profilePhaseAverage hT

@[simp] theorem periodicHierarchyOperators_material_val (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    ((periodicHierarchyOperators hT G M κ).material f).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).material f.val := rfl

@[simp] theorem periodicHierarchyOperators_labelGrad_val (hT : 0 < T) (G M : VPmap) (κ : VP) (f : SP) :
    ((periodicHierarchyOperators hT G M κ).labelGrad f).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).labelGrad f.val := rfl

@[simp] theorem periodicHierarchyOperators_phaseGrad_val (hT : 0 < T) (G M : VPmap) (κ : VP) (f : SP) :
    ((periodicHierarchyOperators hT G M κ).phaseGrad f).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).phaseGrad f.val := rfl

@[simp] theorem periodicHierarchyOperators_labelAdv_val (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ((periodicHierarchyOperators hT G M κ).labelAdv f g).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).labelAdv f.val g.val := rfl

@[simp] theorem periodicHierarchyOperators_phaseAdv_val (hT : 0 < T) (G M : VPmap) (κ f g : VP) :
    ((periodicHierarchyOperators hT G M κ).phaseAdv f g).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).phaseAdv f.val g.val := rfl

@[simp] theorem periodicHierarchyOperators_average_val (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    ((periodicHierarchyOperators hT G M κ).average f).val =
      (HierarchySmoothProfile.hierarchyConcreteOperators hT G.val M.val κ.val).average f.val := rfl

theorem average_idempotent (hT : 0 < T) (G M : VPmap) (κ f : VP) :
    let A := periodicHierarchyOperators hT G M κ
    A.average (A.average f) = A.average f :=
  profilePhaseAverage_idempotent hT f

private theorem hasDerivAt_phaseSlice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    HasDerivAt (fun r => f.val (t, a, r))
      (fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) hierarchyPhasePeriod) s := by
  have hF := ((HierarchySmoothProfile.smooth f).differentiableOn (by simp) (t, a, s) ⟨ht, mem_univ _⟩).hasFDerivWithinAt
  have hd : HasDerivAt (fun r : ℝ => (t, a, r)) hierarchyPhasePeriod s :=
    (hasDerivAt_const (c := t) s).prodMk
      ((hasDerivAt_const (c := a) s).prodMk (hasDerivAt_id s))
  have hInside (r : ℝ) : (t, a, r) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  exact hF.comp_hasDerivAt s hd (Filter.Eventually.of_forall hInside)

private theorem continuous_phaseSliceDerivative (hT : 0 < T)
    (f : HierarchySmoothProfile T Vec3) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun s => fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s)
      hierarchyPhasePeriod) := by
  have h := (HierarchySmoothProfile.smooth f).continuousOn_fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT) (by simp)
  have hline : Continuous (fun s : ℝ => (t, a, s)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  exact (h.comp_continuous hline (fun _ => ⟨ht, mem_univ _⟩)).clm_apply continuous_const

private theorem phaseDirection_eq_smul_period (c : ℝ) :
    ((0, 0, c) : HierarchyProfilePoint) = c • hierarchyPhasePeriod := by
  simp [hierarchyPhasePeriod]

/-- A phase-independent profile has zero phase derivative at each slab point. -/
theorem phaseDerivative_eq_zero_of_independent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) (hf : PhaseIndependent f)
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyProfileSlab T) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) x hierarchyPhasePeriod = 0 := by
  have hD := hasDerivAt_phaseSlice f hx.1 x.2.1 x.2.2
  rw [show (fun r => f.val (x.1, x.2.1, r)) = fun _ : ℝ => f.val x from funext (hf x hx)] at hD
  exact hD.unique (hasDerivAt_const x.2.2 (f.val x))

/-- Phase-independent mean pressures have zero fast gradient. -/
theorem phaseGrad_eq_zero_of_independent (hT : 0 < T) (G M : VPmap) (κ : VP)
    (p : SP) (hp : PhaseIndependent p.val) :
    (periodicHierarchyOperators hT G M κ).phaseGrad p = 0 := by
  apply HierarchyPeriodicProfile.ext
  intro x hx
  change (HierarchySmoothProfile.phaseGradient hT κ.val p.val).val x = 0
  rw [HierarchySmoothProfile.phaseGradient_apply hT κ.val p.val hx]
  change fderivWithin ℝ p.val.val (hierarchyProfileSlab T) x hierarchyPhasePeriod • κ.val.val x = 0
  rw [phaseDerivative_eq_zero_of_independent p.val hp hx, zero_smul]

/-- Fast advection vanishes when the advected profile is a mean field. -/
theorem phaseAdv_eq_zero_of_independent (hT : 0 < T) (G M : VPmap) (κ f g : VP)
    (hg : PhaseIndependent g.val) :
    (periodicHierarchyOperators hT G M κ).phaseAdv f g = 0 := by
  apply HierarchyPeriodicProfile.ext
  intro x hx
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val)
    f.val g.val).val x = 0
  rw [HierarchySmoothProfile.advect_apply hT _ f.val g.val hx,
    HierarchySmoothProfile.phaseDirections_apply κ.val f.val hx,
    phaseDirection_eq_smul_period, map_smul,
    phaseDerivative_eq_zero_of_independent g.val hg hx, smul_zero]

/-- A transverse advecting profile gives zero fast advection. -/
theorem phaseAdv_eq_zero_of_transverse (hT : 0 < T) (G M : VPmap) (κ f g : VP)
    (hf : ∀ x ∈ hierarchyProfileSlab T, ⟪κ.val.val x, f.val.val x⟫_ℝ = 0) :
    (periodicHierarchyOperators hT G M κ).phaseAdv f g = 0 := by
  apply HierarchyPeriodicProfile.ext
  intro x hx
  change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val)
    f.val g.val).val x = 0
  rw [HierarchySmoothProfile.advect_apply hT _ f.val g.val hx,
    HierarchySmoothProfile.phaseDirections_apply κ.val f.val hx, hf x hx,
    phaseDirection_eq_smul_period, zero_smul, map_zero]

/-- Fast advection by a mean field has zero average when the covector is
phase-independent. This is the mean-source cancellation used at every grade. -/
theorem average_meanPhaseAdv (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hκ : PhaseIndependent κ.val) (B Y : VP)
    (hB : (periodicHierarchyOperators hT G M κ).average B = B) :
    let A := periodicHierarchyOperators hT G M κ
    A.average (A.phaseAdv B Y) = 0 := by
  let A := periodicHierarchyOperators hT G M κ
  have hB' : PhaseIndependent B.val := phaseIndependent_of_profilePhaseAverage_eq_self hT B hB
  apply HierarchyPeriodicProfile.ext
  intro x hx
  let d (s : ℝ) := fderivWithin ℝ Y.val.val (hierarchyProfileSlab T) (x.1, x.2.1, s)
    hierarchyPhasePeriod
  have hEval (s : ℝ) :
      (A.phaseAdv B Y).val.val (x.1, x.2.1, s) =
        ⟪κ.val.val x, B.val.val x⟫_ℝ • d s := by
    have hs : (x.1, x.2.1, s) ∈ hierarchyProfileSlab T := ⟨hx.1, mem_univ _⟩
    change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val) B.val Y.val).val
      (x.1, x.2.1, s) = _
    rw [HierarchySmoothProfile.advect_apply hT _ B.val Y.val hs,
      HierarchySmoothProfile.phaseDirections_apply κ.val B.val hs, hκ x hx s, hB' x hx s]
    rw [phaseDirection_eq_smul_period, map_smul]
  change (HierarchySmoothProfile.profilePhaseAverage hT (A.phaseAdv B Y).val).val x = 0
  rw [HierarchySmoothProfile.profilePhaseAverage_apply hT (A.phaseAdv B Y).val hx, funext hEval]
  rw [phaseMean_const_smul, phaseMean_deriv (fun s => hasDerivAt_phaseSlice Y.val hx.1 x.2.1 s)
    (continuous_phaseSliceDerivative hT Y.val hx.1 x.2.1) (phasePeriodic Y x.1 x.2.1), smul_zero]

end HierarchyPeriodicProfile

end

end TorusEuler

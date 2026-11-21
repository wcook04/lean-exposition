import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.HierarchyTwistedProfiles

/-!
Reflection parity through the selected finite hierarchy in frozen section 5.5.
The odd velocity and even pressure spaces enter the algebraic recursion as
submodules. Parity of the chosen analytic solves is a separate input.
-/

open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

section Algebra

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

namespace HierarchyOperators

/-- Closure of the six hierarchy operations on the velocity and pressure subspaces. -/
structure PreservesSubmodules (A : HierarchyOperators E F) (velocity : Submodule ℝ E)
    (pressure : Submodule ℝ F) : Prop where
  material_mem : ∀ v ∈ velocity, A.material v ∈ velocity
  labelGrad_mem : ∀ p ∈ pressure, A.labelGrad p ∈ velocity
  phaseGrad_mem : ∀ p ∈ pressure, A.phaseGrad p ∈ velocity
  labelAdv_mem : ∀ v ∈ velocity, ∀ w ∈ velocity, A.labelAdv v w ∈ velocity
  phaseAdv_mem : ∀ v ∈ velocity, ∀ w ∈ velocity, A.phaseAdv v w ∈ velocity
  average_mem : ∀ v ∈ velocity, A.average v ∈ velocity

end HierarchyOperators

namespace HierarchyProfiles

/-- The three velocity components and two pressures at one level have
the prescribed submodule memberships. -/
structure LevelMem (u : HierarchyProfiles E F) (velocity : Submodule ℝ E)
    (pressure : Submodule ℝ F) (p : ℕ) : Prop where
  V_mem : u.V p ∈ velocity
  C_mem : u.C p ∈ velocity
  B_mem : u.B p ∈ velocity
  p_mem : u.p p ∈ pressure
  q_mem : u.q p ∈ pressure

variable {u : HierarchyProfiles E F} {velocity : Submodule ℝ E} {pressure : Submodule ℝ F}
  {p : ℕ}

theorem LevelMem.Y_mem (h : u.LevelMem velocity pressure p)
    (hPrev : u.LevelMem velocity pressure (p - 1)) : u.Y p ∈ velocity :=
  velocity.add_mem h.V_mem hPrev.C_mem

theorem LevelMem.Z_mem (h : u.LevelMem velocity pressure p)
    (hPrev : u.LevelMem velocity pressure (p - 1)) : u.Z p ∈ velocity :=
  velocity.add_mem (h.Y_mem hPrev) h.B_mem

theorem velocity_mem_of_levelMem (h : ∀ i, u.LevelMem velocity pressure i) (P : ℕ) :
    u.velocity P ∈ velocity :=
  velocity.sum_mem fun i _ => velocity.add_mem
    (velocity.add_mem (h i).V_mem (h i).C_mem) (h i).B_mem

theorem pressure_mem_of_levelMem (h : ∀ i, u.LevelMem velocity pressure i) (P : ℕ) :
    u.pressure P ∈ pressure :=
  pressure.sum_mem fun i _ => pressure.add_mem (h i).p_mem (h i).q_mem

end HierarchyProfiles

namespace HierarchyOperators

variable {A : HierarchyOperators E F} {velocity : Submodule ℝ E} {pressure : Submodule ℝ F}

private theorem indices_of_mem_hierarchyAdvectionAtLevel {P shift p : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ (hierarchyAdvectionPairs P shift).filter
      (fun ij => hierarchyAdvectionLevel shift ij = p)) :
    shift + 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1 + ij.2 = p + shift := by
  obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
  rw [Finset.mem_Icc] at hi hj
  unfold hierarchyAdvectionLevel at hlevel
  exact ⟨hi.1, hj.1, by omega⟩

/-- The preliminary source needs parity only at lower levels. Its
level-two switch contribution has the same parity as the completion. -/
theorem sourceBeforeMean_mem_of_mem_before
    (hA : A.PreservesSubmodules velocity pressure) {u : HierarchyProfiles E F}
    {P p : ℕ} (hp : 2 ≤ p) (hprev : ∀ i < p, u.LevelMem velocity pressure i)
    {completionSwitch : E} (hSwitch : completionSwitch ∈ velocity) :
    A.sourceBeforeMean u P completionSwitch p ∈ velocity := by
  have hlabel : hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) ∈ velocity := by
    apply velocity.sum_mem
    intro ij hij
    obtain ⟨hi, hj, hsum⟩ := indices_of_mem_hierarchyAdvectionAtLevel hij
    obtain ⟨hi', hj'⟩ := hierarchy_label_inputs_previous hi hj (by simpa using hsum)
    exact hA.labelAdv_mem _ ((hprev _ hi').Z_mem (hprev _ (by omega)))
      _ ((hprev _ hj').Z_mem (hprev _ (by omega)))
  have hfast : hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u) ∈ velocity := by
    apply velocity.sum_mem
    intro ij hij
    obtain ⟨hi, hj, hsum⟩ := indices_of_mem_hierarchyAdvectionAtLevel hij
    obtain ⟨hi', hj', _, _⟩ := hierarchy_phase_inputs_previous hi hj hsum
    exact hA.phaseAdv_mem _ (hprev _ hi').C_mem _ ((hprev _ hj').Y_mem (hprev _ (by omega)))
  have hswitch : (if p = 2 then completionSwitch else 0) ∈ velocity := by
    split_ifs
    · exact hSwitch
    · exact velocity.zero_mem
  have hPrev := hprev (p - 1) (by omega)
  exact velocity.add_mem (velocity.add_mem (velocity.sub_mem
    (velocity.add_mem (hA.material_mem _ hPrev.C_mem) (hA.labelGrad_mem _ hPrev.p_mem))
    hswitch) hlabel) hfast

/-- The supplementary source uses the new mean but only older
oscillations and completions. -/
theorem meanPhaseAdvectionAtLevel_mem_of_mem_before
    (hA : A.PreservesSubmodules velocity pressure) {u : HierarchyProfiles E F}
    {P p : ℕ} (hp : p ≤ P) (hprev : ∀ i < p, u.LevelMem velocity pressure i)
    (hB : u.B p ∈ velocity) :
    hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u) ∈ velocity := by
  rw [A.meanPhaseAdvectionAtLevel_eq_sum u hp]
  apply velocity.sum_mem
  intro i hi
  obtain ⟨hi₂, hip⟩ := Finset.mem_Icc.mp hi
  have hmean : u.B i ∈ velocity := by
    rcases lt_or_eq_of_le hip with hlt | heq
    · exact (hprev i hlt).B_mem
    · rwa [heq]
  exact hA.phaseAdv_mem _ hmean _
    ((hprev _ (by omega)).Y_mem (hprev _ (by omega)))

/-- Every retained term and interaction above the retained depth has
the velocity parity of the exact hierarchy. -/
theorem remainder_mem_of_levelMem (hA : A.PreservesSubmodules velocity pressure)
    {u : HierarchyProfiles E F} (h : ∀ i, u.LevelMem velocity pressure i) (P : ℕ) :
    A.remainder u P ∈ velocity := by
  have hslow : (∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij) ∈ velocity :=
    velocity.sum_mem fun ij _ => hA.labelAdv_mem _
      ((h ij.1).Z_mem (h _)) _ ((h ij.2).Z_mem (h _))
  have hfast : (∑ ij ∈ hierarchyTailPairs P 1,
      (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij)) ∈ velocity := by
    apply velocity.sum_mem
    intro ij _
    have hY := (h ij.2).Y_mem (h _)
    exact velocity.add_mem (hA.phaseAdv_mem _ (h (ij.1 - 1)).C_mem _ hY)
      (hA.phaseAdv_mem _ (h ij.1).B_mem _ hY)
  exact velocity.add_mem
    (velocity.add_mem (velocity.add_mem (hA.material_mem _ (h P).C_mem)
      (hA.labelGrad_mem _ (h P).p_mem)) hslow) hfast

end HierarchyOperators

namespace FiniteHierarchySolvers

variable {A : HierarchyOperators E F} {velocity : Submodule ℝ E} {pressure : Submodule ℝ F}

/-- The actual selected recursion keeps its velocity and pressure
submodules when each selected solver has the corresponding closure. -/
theorem construct_levelMem (S : FiniteHierarchySolvers A)
    (hA : A.PreservesSubmodules velocity pressure) {P : ℕ} (hP : 1 ≤ P)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A)
    (hSwitch : completionSwitch ∈ velocity) (hResidual : parentResidual ∈ velocity)
    (hLeadingV : leading.V ∈ velocity) (hLeadingP : leading.p ∈ pressure)
    (hMean : ∀ (f : E) (hf : A.average f = f), f ∈ velocity →
      (S.solveMean f hf).val.B ∈ velocity ∧ (S.solveMean f hf).val.q ∈ pressure)
    (hTransverse : ∀ (f : E) (hf : A.average f = 0), f ∈ velocity →
      (S.solveTransverse f hf).val.V ∈ velocity ∧ (S.solveTransverse f hf).val.p ∈ pressure)
    (hCompletion : ∀ o : HierarchyTransverseOutput A, o.V ∈ velocity → S.complete o.V ∈ velocity) :
    ∀ p, (S.construct P completionSwitch parentResidual hR leading).LevelMem velocity pressure p := by
  let u := S.construct P completionSwitch parentResidual hR leading
  change ∀ p, u.LevelMem velocity pressure p
  intro p
  induction p using Nat.strongRecOn with
  | ind p hprev =>
    by_cases hzero : p = 0 ∨ P < p
    · obtain ⟨hV, hC, hB, hpress, hq⟩ :=
        S.construct_eq_zero_of_index hP hzero completionSwitch parentResidual hR leading
      exact ⟨hV.symm ▸ velocity.zero_mem, hC.symm ▸ velocity.zero_mem,
        hB.symm ▸ velocity.zero_mem, hpress.symm ▸ pressure.zero_mem,
        hq.symm ▸ pressure.zero_mem⟩
    · have hpP : p ≤ P := by omega
      have hretained : p ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, hpP⟩
      have hC := S.construct_completion hretained completionSwitch parentResidual hR leading
      by_cases hfirst : p = 1
      · subst p
        obtain ⟨hV, hpress, hB, hq⟩ := S.construct_leading P completionSwitch parentResidual hR leading
        have hComp : u.C 1 ∈ velocity := by
          rw [hC, hV]
          exact hCompletion leading hLeadingV
        exact ⟨hV.symm ▸ hLeadingV, hComp, hB.symm ▸ velocity.zero_mem,
          hpress.symm ▸ hLeadingP, hq.symm ▸ pressure.zero_mem⟩
      · have hp₂ : 2 ≤ p := by omega
        have hcorrection : p ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨hp₂, hpP⟩
        let H := A.sourceBeforeMean u P completionSwitch p
        have hH : H ∈ velocity := HierarchyOperators.sourceBeforeMean_mem_of_mem_before hA hp₂ hprev hSwitch
        let meanForce := -A.average H - (if p = 2 then parentResidual else 0)
        have hparent : (if p = 2 then parentResidual else 0) ∈ velocity := by
          split_ifs
          · exact hResidual
          · exact velocity.zero_mem
        have hmeanForce : meanForce ∈ velocity :=
          velocity.sub_mem (velocity.neg_mem (hA.average_mem _ hH)) hparent
        obtain ⟨hm, hB, hq⟩ :=
          S.construct_mean_selected hcorrection completionSwitch parentResidual hR leading
        obtain ⟨hMeanB, hMeanQ⟩ := hMean meanForce hm hmeanForce
        have hBmem : u.B p ∈ velocity := hB.symm ▸ hMeanB
        have hfast := HierarchyOperators.meanPhaseAdvectionAtLevel_mem_of_mem_before hA hpP hprev hBmem
        let oscForce := -(H - A.average H) -
          hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)
        have hoscForce : oscForce ∈ velocity := velocity.sub_mem
          (velocity.neg_mem (velocity.sub_mem hH (hA.average_mem _ hH))) hfast
        obtain ⟨ho, hV, hpress⟩ :=
          S.construct_transverse_selected hcorrection completionSwitch parentResidual hR leading
        obtain ⟨hOscV, hOscP⟩ := hTransverse oscForce ho hoscForce
        have hComp : u.C p ∈ velocity := by
          rw [hC, hV]
          exact hCompletion (S.solveTransverse oscForce ho).val hOscV
        exact ⟨hV.symm ▸ hOscV, hComp, hBmem, hpress.symm ▸ hOscP, hq.symm ▸ hMeanQ⟩

end FiniteHierarchySolvers

end Algebra

namespace HierarchyTwistedProfile

variable {T : ℝ} {k : Vec3}

/-- Profiles of a fixed reflection sign form a submodule of the twisted
profile space. -/
def reflectionSubmodule (sign : ℝ) (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    Submodule ℝ (HierarchyTwistedProfile T k E) where
  carrier := {f | HierarchyProfileReflectionParity sign f.val.val.val}
  zero_mem' := by intro x; exact (smul_zero sign).symm
  add_mem' := by
    intro f g hf hg x
    change f.val.val.val (hierarchyProfileReflection x) + g.val.val.val (hierarchyProfileReflection x) =
      sign • (f.val.val.val x + g.val.val.val x)
    rw [hf x, hg x, smul_add]
  smul_mem' := by
    intro c f hf x
    change c • f.val.val.val (hierarchyProfileReflection x) = sign • (c • f.val.val.val x)
    rw [hf x, smul_comm]

theorem mem_reflectionSubmodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (sign : ℝ) (f : HierarchyTwistedProfile T k E) :
    f ∈ reflectionSubmodule sign E ↔ HierarchyProfileReflectionParity sign f.val.val.val := Iff.rfl

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "VPmap" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- Even coframe, material matrix, and covector give closure on odd
velocities and even pressures. -/
theorem concrete_preservesReflectionSubmodules (hT : 0 < T) (G M : VPmap) (κ : VP)
    (hG : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hM : HierarchyProfileReflectionParity 1 M.val.val.val)
    (hκ : HierarchyProfileReflectionParity 1 κ.val.val.val) :
    (twistedHierarchyOperators hT G M κ).PreservesSubmodules
      (reflectionSubmodule (-1) Vec3) (reflectionSubmodule 1 ℝ) := by
  constructor
  · intro f hf
    exact material_reflectionParity hT G M κ f (-1) hM hf
  · intro p hp
    exact labelGrad_reflectionParity hT G M κ p 1 hG hp
  · intro p hp
    exact phaseGrad_reflectionParity hT G M κ p 1 hκ hp
  · intro f hf g hg
    have h := labelAdv_reflectionParity hT G M κ f g (-1) (-1) hG hf hg
    exact (by norm_num at h; exact h)
  · intro f hf g hg
    have h := phaseAdv_reflectionParity hT G M κ f g (-1) (-1) hκ hf hg
    exact (by norm_num at h; exact h)
  · intro f hf
    exact average_reflectionParity hT f (-1) hf

/-- Odd leading velocities and parent and switch sources, even leading
pressure and coefficients, and parity-preserving selected solves give
the exact constructed hierarchy its reflection parity through all levels. -/
theorem construct_reflectionParity (hT : 0 < T) (G M : VPmap) (κ : VP)
    (S : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    {P : ℕ} (hP : 1 ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hG : HierarchyProfileReflectionParity 1 G.val.val.val)
    (hM : HierarchyProfileReflectionParity 1 M.val.val.val)
    (hκ : HierarchyProfileReflectionParity 1 κ.val.val.val)
    (hSwitch : HierarchyProfileReflectionParity (-1) completionSwitch.val.val.val)
    (hResidual : HierarchyProfileReflectionParity (-1) parentResidual.val.val.val)
    (hLeadingV : HierarchyProfileReflectionParity (-1) leading.V.val.val.val)
    (hLeadingP : HierarchyProfileReflectionParity 1 leading.p.val.val.val)
    (hMean : ∀ (f : VP) (hf : (twistedHierarchyOperators hT G M κ).average f = f),
      HierarchyProfileReflectionParity (-1) f.val.val.val →
      HierarchyProfileReflectionParity (-1) (S.solveMean f hf).val.B.val.val.val ∧
        HierarchyProfileReflectionParity 1 (S.solveMean f hf).val.q.val.val.val)
    (hTransverse : ∀ (f : VP) (hf : (twistedHierarchyOperators hT G M κ).average f = 0),
      HierarchyProfileReflectionParity (-1) f.val.val.val →
      HierarchyProfileReflectionParity (-1) (S.solveTransverse f hf).val.V.val.val.val ∧
        HierarchyProfileReflectionParity 1 (S.solveTransverse f hf).val.p.val.val.val)
    (hCompletion : ∀ o : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ),
      HierarchyProfileReflectionParity (-1) o.V.val.val.val →
      HierarchyProfileReflectionParity (-1) (S.complete o.V).val.val.val) :
    let u := S.construct P completionSwitch parentResidual hR leading
    (∀ i, HierarchyProfileReflectionParity (-1) (u.V i).val.val.val ∧
      HierarchyProfileReflectionParity (-1) (u.C i).val.val.val ∧
      HierarchyProfileReflectionParity (-1) (u.B i).val.val.val ∧
      HierarchyProfileReflectionParity 1 (u.p i).val.val.val ∧
      HierarchyProfileReflectionParity 1 (u.q i).val.val.val) ∧
    HierarchyProfileReflectionParity (-1) (u.velocity P).val.val.val ∧
    HierarchyProfileReflectionParity 1 (u.pressure P).val.val.val ∧
    HierarchyProfileReflectionParity (-1)
      ((twistedHierarchyOperators hT G M κ).remainder u P).val.val.val := by
  let u := S.construct P completionSwitch parentResidual hR leading
  let oddVel : Submodule ℝ VP := reflectionSubmodule (-1) Vec3
  let evenPressure : Submodule ℝ SP := reflectionSubmodule 1 ℝ
  have hA : (twistedHierarchyOperators hT G M κ).PreservesSubmodules oddVel evenPressure :=
    concrete_preservesReflectionSubmodules hT G M κ hG hM hκ
  have hLevels : ∀ i, u.LevelMem oddVel evenPressure i :=
    S.construct_levelMem hA hP completionSwitch parentResidual hR leading
      hSwitch hResidual hLeadingV hLeadingP hMean hTransverse hCompletion
  refine ⟨fun i => ?_, u.velocity_mem_of_levelMem hLevels P,
    u.pressure_mem_of_levelMem hLevels P, HierarchyOperators.remainder_mem_of_levelMem hA hLevels P⟩
  obtain ⟨hV, hC, hB, hpress, hq⟩ := hLevels i
  exact ⟨hV, hC, hB, hpress, hq⟩

/-- The leading switch term has odd parity by the leading momentum
equation. Adding it and the completion switch preserves the odd residual. -/
theorem remainder_add_switch_reflectionParity (hT : 0 < T) (G M : VPmap) (κ : VP)
    (u : HierarchyProfiles VP SP) (P : ℕ) (leading : HierarchyTransverseOutput
      (twistedHierarchyOperators hT G M κ)) (leadingSwitch completionSwitch : VP)
    (hM : HierarchyProfileReflectionParity 1 M.val.val.val)
    (hκ : HierarchyProfileReflectionParity 1 κ.val.val.val)
    (hV : HierarchyProfileReflectionParity (-1) leading.V.val.val.val)
    (hP : HierarchyProfileReflectionParity 1 leading.p.val.val.val)
    (hLead : (twistedHierarchyOperators hT G M κ).material leading.V +
      (twistedHierarchyOperators hT G M κ).phaseGrad leading.p = leadingSwitch)
    (hC : HierarchyProfileReflectionParity (-1) completionSwitch.val.val.val)
    (hR : HierarchyProfileReflectionParity (-1)
      ((twistedHierarchyOperators hT G M κ).remainder u P).val.val.val) :
    HierarchyProfileReflectionParity (-1)
      (((twistedHierarchyOperators hT G M κ).remainder u P) +
        (leadingSwitch + completionSwitch)).val.val.val := by
  rw [← hLead]
  let oddVel : Submodule ℝ VP := reflectionSubmodule (-1) Vec3
  exact oddVel.add_mem hR (oddVel.add_mem
    (oddVel.add_mem (material_reflectionParity hT G M κ leading.V (-1) hM hV)
      (phaseGrad_reflectionParity hT G M κ leading.p 1 hκ hP)) hC)

end HierarchyTwistedProfile

/-- A time-dependent scalar, including the derivative of the switch,
preserves the reflection sign. -/
theorem hierarchyProfileReflectionParity_time_smul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : HierarchyProfilePoint → E} {sign : ℝ}
    (hf : HierarchyProfileReflectionParity sign f) (c : ℝ → ℝ) :
    HierarchyProfileReflectionParity sign (fun x => c x.1 • f x) := by
  intro x
  change c (hierarchyProfileReflection x).1 • f (hierarchyProfileReflection x) =
    sign • (c x.1 • f x)
  rw [hf x]
  change c x.1 • (sign • f x) = sign • (c x.1 • f x)
  exact smul_comm _ _ _

end

end TorusEuler

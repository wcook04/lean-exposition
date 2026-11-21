import TorusEuler.HierarchyCancellation

/-! The ordered finite expansion in §5.5, conditional on the mean and
transverse solves of §§5.3 and 5.4 and the divergence completion of §3.
The recursion exposes only earlier levels to the preliminary source.
For the supplementary source it additionally exposes the current mean.
Analytic solvability, support, and derivative estimates are separate. -/

namespace TorusEuler

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

private theorem hierarchy_indices_of_mem_level {P shift p : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ (hierarchyAdvectionPairs P shift).filter
      (fun ij => hierarchyAdvectionLevel shift ij = p)) :
    shift + 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1 + ij.2 = p + shift := by
  obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
  rw [Finset.mem_Icc] at hi hj
  unfold hierarchyAdvectionLevel at hlevel
  exact ⟨hi.1, hj.1, by omega⟩

namespace HierarchyProfiles

/-- All source inputs from levels strictly below `p` agree. -/
def AgreesBefore (u v : HierarchyProfiles E F) (p : ℕ) : Prop :=
  ∀ i, i < p → u.V i = v.V i ∧ u.C i = v.C i ∧ u.B i = v.B i ∧ u.p i = v.p i

omit [Module ℝ E] [AddCommGroup F] [Module ℝ F] in
private theorem AgreesBefore.Y_eq {u v : HierarchyProfiles E F} {p i : ℕ}
    (h : u.AgreesBefore v p) (hi : i < p) : u.Y i = v.Y i := by
  rw [Y, Y, (h i hi).1, (h (i - 1) (by omega)).2.1]

omit [Module ℝ E] [AddCommGroup F] [Module ℝ F] in
private theorem AgreesBefore.Z_eq {u v : HierarchyProfiles E F} {p i : ℕ}
    (h : u.AgreesBefore v p) (hi : i < p) : u.Z i = v.Z i := by
  rw [Z, Z, h.Y_eq hi, (h i hi).2.2.1]

end HierarchyProfiles

namespace HierarchyOperators

/-- The preliminary source of level `p` depends only on lower levels. -/
theorem sourceBeforeMean_congr (A : HierarchyOperators E F)
    {u v : HierarchyProfiles E F} {P p : ℕ} (hp : 2 ≤ p)
    (h : u.AgreesBefore v p) (completionSwitch : E) :
    A.sourceBeforeMean u P completionSwitch p = A.sourceBeforeMean v P completionSwitch p := by
  have hlabel : hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) =
      hierarchyAdvectionAtLevel P 0 p (A.labelProduct v) := by
    apply Finset.sum_congr rfl
    intro ij hij
    obtain ⟨hi, hj, hpij⟩ := hierarchy_indices_of_mem_level hij
    have hprev := hierarchy_label_inputs_previous hi hj (by simpa only [Nat.add_zero] using hpij)
    rw [labelProduct, labelProduct, h.Z_eq hprev.1, h.Z_eq hprev.2]
  have hfast : hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u) =
      hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct v) := by
    apply Finset.sum_congr rfl
    intro ij hij
    obtain ⟨hi, hj, hpij⟩ := hierarchy_indices_of_mem_level hij
    have hprev := hierarchy_phase_inputs_previous hi hj hpij
    rw [completionPhaseProduct, completionPhaseProduct,
      (h _ hprev.1).2.1, h.Y_eq hprev.2.1]
  rw [sourceBeforeMean, sourceBeforeMean, hlabel, hfast,
    (h (p - 1) (by omega)).2.1, (h (p - 1) (by omega)).2.2.2]

/-- The supplementary source reaches the current level only in its mean
factor, paired with the leading oscillation. -/
theorem meanPhaseAdvectionAtLevel_congr (A : HierarchyOperators E F)
    {u v : HierarchyProfiles E F} {P p : ℕ} (h : u.AgreesBefore v p)
    (hmean : u.B p = v.B p) :
    hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u) =
      hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct v) := by
  apply Finset.sum_congr rfl
  intro ij hij
  obtain ⟨hi, hj, hpij⟩ := hierarchy_indices_of_mem_level hij
  have hprev := hierarchy_phase_inputs_previous hi hj hpij
  have hB : u.B ij.1 = v.B ij.1 := by
    rcases lt_or_eq_of_le hprev.2.2.1 with hlt | heq
    · exact (h _ hlt).2.2.1
    · simpa only [heq] using hmean
  rw [meanPhaseProduct, meanPhaseProduct, hB, h.Y_eq hprev.2.1]

/-- The filtered phase-advection sum is the single-index sum in (5.28)
with the sign removed. At a correction level its last term uses (B_p) and (Y_1). -/
theorem meanPhaseAdvectionAtLevel_eq_sum (A : HierarchyOperators E F)
    (u : HierarchyProfiles E F) {P p : ℕ} (hp : p ≤ P) :
    hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u) =
      ∑ i ∈ Finset.Icc 2 p, A.phaseAdv (u.B i) (u.Y (p + 1 - i)) := by
  unfold hierarchyAdvectionAtLevel
  refine Finset.sum_bij' (fun ij _ => ij.1) (fun i _ => (i, p + 1 - i))
    (fun ij hij => ?_) (fun i hi => ?_) (fun ij hij => ?_) (fun _ _ => rfl) (fun ij hij => ?_)
  · obtain ⟨hi, hj, hsum⟩ := hierarchy_indices_of_mem_level hij
    exact Finset.mem_Icc.mpr ⟨hi, by omega⟩
  · obtain ⟨hi₂, hip⟩ := Finset.mem_Icc.mp hi
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
    · exact Finset.mem_Icc.mpr ⟨hi₂, by omega⟩
    · exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · unfold hierarchyAdvectionLevel
      simp only
      omega
  · obtain ⟨_, _, hsum⟩ := hierarchy_indices_of_mem_level hij
    exact Prod.ext rfl (by omega)
  · obtain ⟨_, _, hsum⟩ := hierarchy_indices_of_mem_level hij
    have hsecond : ij.2 = p + 1 - ij.1 := by omega
    rw [meanPhaseProduct, hsecond]

end HierarchyOperators

/-- Phase-independent output of the mean equation. -/
structure HierarchyMeanOutput (A : HierarchyOperators E F) where
  B : E
  q : F
  average_B : A.average B = B
  phaseAdv_B : ∀ v, A.phaseAdv v B = 0
  phaseGrad_q : A.phaseGrad q = 0

/-- Transverse oscillatory output, including its pressure. -/
structure HierarchyTransverseOutput (A : HierarchyOperators E F) where
  V : E
  p : F
  average_V : A.average V = 0
  phaseAdv_V : ∀ v, A.phaseAdv V v = 0

/-- The analytic inputs used in the ordered expansion. The two solves
receive admissible sources. The completion returns (C[V]). -/
structure FiniteHierarchySolvers (A : HierarchyOperators E F) where
  average_idempotent : ∀ f, A.average (A.average f) = A.average f
  average_meanPhaseAdv : ∀ B, A.average B = B → ∀ Y, A.average (A.phaseAdv B Y) = 0
  solveMean : (f : E) → A.average f = f →
    {m : HierarchyMeanOutput A // A.material m.B + A.labelGrad m.q = f}
  solveTransverse : (f : E) → A.average f = 0 →
    {o : HierarchyTransverseOutput A // A.material o.V + A.phaseGrad o.p = f}
  complete : E → E
  average_complete : ∀ v, A.average v = 0 → A.average (complete v) = 0

namespace FiniteHierarchySolvers

variable {A : HierarchyOperators E F}

private structure Level (A : HierarchyOperators E F) where
  oscillation : HierarchyTransverseOutput A
  C : E
  average_C : A.average C = 0
  mean : HierarchyMeanOutput A

private def zeroMean (A : HierarchyOperators E F) : HierarchyMeanOutput A :=
  ⟨0, 0, by simp, by simp, by simp⟩

private def zeroLevel (A : HierarchyOperators E F) : Level A :=
  ⟨⟨0, 0, by simp, by simp⟩, 0, by simp, zeroMean A⟩

private def profiles (L : ℕ → Level A) : HierarchyProfiles E F :=
  ⟨fun i => (L i).oscillation.V, fun i => (L i).C, fun i => (L i).mean.B,
    fun i => (L i).oscillation.p, fun i => (L i).mean.q⟩

private def earlierLevels {p : ℕ} (prior : (i : ℕ) → i < p → Level A) : ℕ → Level A :=
  fun i => if hi : i < p then prior i hi else zeroLevel A

private def setMean (u : HierarchyProfiles E F) (p : ℕ) (B : E) : HierarchyProfiles E F :=
  { u with B := Function.update u.B p B }

private def meanSource (A : HierarchyOperators E F) (H parentResidual : E) (p : ℕ) : E :=
  -A.average H - (if p = 2 then parentResidual else 0)

private def transverseSource (A : HierarchyOperators E F) (u : HierarchyProfiles E F)
    (P p : ℕ) (H : E) : E :=
  -(H - A.average H) - hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)

private theorem average_meanSource (S : FiniteHierarchySolvers A)
    {parentResidual : E} (hR : A.average parentResidual = parentResidual) (H : E) (p : ℕ) :
    A.average (meanSource A H parentResidual p) = meanSource A H parentResidual p := by
  by_cases hp : p = 2 <;> simp [meanSource, hp, S.average_idempotent, hR]

private theorem average_transverseSource (S : FiniteHierarchySolvers A)
    (u : HierarchyProfiles E F) (hB : ∀ i, A.average (u.B i) = u.B i) (P p : ℕ) (H : E) :
    A.average (transverseSource A u P p H) = 0 := by
  simp [transverseSource, map_sum, hierarchyAdvectionAtLevel, HierarchyOperators.meanPhaseProduct,
    S.average_idempotent, S.average_meanPhaseAdv _ (hB _)]

private def solveLevel (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    {p : ℕ} (prior : (i : ℕ) → i < p → Level A) :
    let u := profiles (earlierLevels prior)
    let H := A.sourceBeforeMean u P completionSwitch p
    {l : Level A // A.material l.mean.B + A.labelGrad l.mean.q =
      meanSource A H parentResidual p ∧
      A.material l.oscillation.V + A.phaseGrad l.oscillation.p =
        transverseSource A (setMean u p l.mean.B) P p H} := by
  let u := profiles (earlierLevels prior)
  let H := A.sourceBeforeMean u P completionSwitch p
  let m := S.solveMean (meanSource A H parentResidual p) (S.average_meanSource hR H p)
  let u' := setMean u p m.val.B
  have hB (i : ℕ) : A.average (u'.B i) = u'.B i := by
    by_cases h : i = p
    · subst i
      simpa [u', setMean] using m.val.average_B
    · simpa [u', setMean, Function.update_of_ne h, u, profiles] using
        ((earlierLevels prior i).mean.average_B)
  let o := S.solveTransverse (transverseSource A u' P p H)
    (S.average_transverseSource u' hB P p H)
  exact ⟨⟨o.val, S.complete o.val.V, S.average_complete _ o.val.average_V, m.val⟩,
    m.property, o.property⟩

private noncomputable def level (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) (p : ℕ) : Level A :=
  p.strongRecOn fun i prior =>
    if i = 1 then
      ⟨leading, S.complete leading.V, S.average_complete _ leading.average_V, zeroMean A⟩
    else if 2 ≤ i ∧ i ≤ P then
      (S.solveLevel P completionSwitch parentResidual hR prior).val
    else zeroLevel A

private theorem level_one (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    S.level P completionSwitch parentResidual hR leading 1 =
      ⟨leading, S.complete leading.V, S.average_complete _ leading.average_V, zeroMean A⟩ := by
  rw [level, Nat.strongRecOn_eq]
  simp only [ite_true]

private theorem level_solve (S : FiniteHierarchySolvers A) {P p : ℕ}
    (hp₂ : 2 ≤ p) (hpP : p ≤ P)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    S.level P completionSwitch parentResidual hR leading p =
      (S.solveLevel P completionSwitch parentResidual hR (p := p)
        (fun i _ => S.level P completionSwitch parentResidual hR leading i)).val := by
  conv_lhs => rw [level, Nat.strongRecOn_eq]
  have h1 : p ≠ 1 := by omega
  simp only [ite_eq_right h1, ite_eq_left (And.intro hp₂ hpP)]
  rfl

private theorem level_zero_or_past (S : FiniteHierarchySolvers A)
    {P p : ℕ} (hP : 1 ≤ P) (hp : p = 0 ∨ P < p)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    S.level P completionSwitch parentResidual hR leading p = zeroLevel A := by
  rw [level, Nat.strongRecOn_eq]
  have h1 : p ≠ 1 := by omega
  have h2 : ¬ (2 ≤ p ∧ p ≤ P) := by omega
  simp only [ite_eq_right h1, ite_eq_right h2]

/-- The finite profiles produced by the ordered solves. At positive depth
the profiles are zero at level zero and above the retained depth. -/
noncomputable def construct (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) : HierarchyProfiles E F :=
  profiles (S.level P completionSwitch parentResidual hR leading)

private theorem prefix_agrees_before {p : ℕ} (L : ℕ → Level A) :
    (profiles (earlierLevels (p := p) (fun i _ => L i))).AgreesBefore (profiles L) p := by
  intro i hi
  simp [profiles, earlierLevels, hi]

/-- The leading profiles of the construction are the prescribed ones. -/
theorem construct_leading (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    u.V 1 = leading.V ∧ u.p 1 = leading.p ∧ u.B 1 = 0 ∧ u.q 1 = 0 := by
  let L := S.level P completionSwitch parentResidual hR leading
  change (L 1).oscillation.V = leading.V ∧ (L 1).oscillation.p = leading.p ∧
    (L 1).mean.B = 0 ∧ (L 1).mean.q = 0
  rw [show L 1 = _ from S.level_one P completionSwitch parentResidual hR leading]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- At positive depth all five profiles vanish at index zero and beyond
the retained hierarchy. -/
theorem construct_eq_zero_of_index (S : FiniteHierarchySolvers A)
    {P p : ℕ} (hP : 1 ≤ P) (hp : p = 0 ∨ P < p)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    u.V p = 0 ∧ u.C p = 0 ∧ u.B p = 0 ∧ u.p p = 0 ∧ u.q p = 0 := by
  let L := S.level P completionSwitch parentResidual hR leading
  change (L p).oscillation.V = 0 ∧ (L p).C = 0 ∧ (L p).mean.B = 0 ∧
    (L p).oscillation.p = 0 ∧ (L p).mean.q = 0
  rw [show L p = zeroLevel A from
    S.level_zero_or_past hP hp completionSwitch parentResidual hR leading]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The selected oscillations and completions have zero phase mean, and
the selected transverse velocity contributes no phase advection. -/
theorem construct_oscillatory_phase_data (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    ∀ i, A.average (u.V i) = 0 ∧ A.average (u.C i) = 0 ∧ ∀ v, A.phaseAdv (u.V i) v = 0 := by
  let L := S.level P completionSwitch parentResidual hR leading
  exact fun i => ⟨(L i).oscillation.average_V, (L i).average_C, (L i).oscillation.phaseAdv_V⟩

/-- Every selected mean is fixed by the phase average. -/
theorem construct_average_B (S : FiniteHierarchySolvers A) (P : ℕ)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A) (p : ℕ) :
    A.average ((S.construct P completionSwitch parentResidual hR leading).B p) =
      (S.construct P completionSwitch parentResidual hR leading).B p :=
  (S.level P completionSwitch parentResidual hR leading p).mean.average_B

set_option maxHeartbeats 400000 in
/-- The velocity and pressure at each correction level are the selected
transverse solve of the exact source expressed in the constructed profiles. -/
theorem construct_transverse_selected (S : FiniteHierarchySolvers A) {P p : ℕ}
    (hp : p ∈ Finset.Icc 2 P) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    let H := A.sourceBeforeMean u P completionSwitch p
    let f := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)
    ∃ hf : A.average f = 0,
      u.V p = (S.solveTransverse f hf).val.V ∧ u.p p = (S.solveTransverse f hf).val.p := by
  obtain ⟨hp₂, hpP⟩ := Finset.mem_Icc.mp hp
  let L := S.level P completionSwitch parentResidual hR leading
  let u := profiles L
  let u₀ := profiles (earlierLevels (p := p) (fun i _ => L i))
  let H₀ := A.sourceBeforeMean u₀ P completionSwitch p
  let m := S.solveMean (meanSource A H₀ parentResidual p) (S.average_meanSource hR H₀ p)
  let u₁ := setMean u₀ p m.val.B
  let f₀ := transverseSource A u₁ P p H₀
  let f := transverseSource A u P p (A.sourceBeforeMean u P completionSwitch p)
  have hlevel : L p = (S.solveLevel P completionSwitch parentResidual hR
      (p := p) (fun i _ => L i)).val :=
    S.level_solve hp₂ hpP completionSwitch parentResidual hR leading
  have hmean : ∀ i, A.average (u₁.B i) = u₁.B i := by
    intro i
    by_cases hi : i = p
    · subst i
      simpa [u₁, setMean] using m.val.average_B
    · simpa [u₁, setMean, Function.update_of_ne hi, u₀, profiles] using
        ((earlierLevels (p := p) (fun j _ => L j) i).mean.average_B)
  have hf₀ : A.average f₀ = 0 := S.average_transverseSource u₁ hmean P p H₀
  have hselected : (L p).oscillation = (S.solveTransverse f₀ hf₀).val := by
    rw [hlevel]
    rfl
  have hprev : u₀.AgreesBefore u p := prefix_agrees_before L
  have hprev' : u₁.AgreesBefore u p := by
    intro i hi
    obtain ⟨hv, hc, hb, hq⟩ := hprev i hi
    exact ⟨hv, hc, by simpa [u₁, setMean, Function.update_of_ne (ne_of_lt hi)] using hb, hq⟩
  have hB : u₁.B p = u.B p := by
    have hm : m.val.B = (L p).mean.B := by rw [hlevel]; rfl
    simpa [u₁, setMean, u, profiles] using hm
  have hH : H₀ = A.sourceBeforeMean u P completionSwitch p :=
    A.sourceBeforeMean_congr (P := P) hp₂ hprev completionSwitch
  have hfast := A.meanPhaseAdvectionAtLevel_congr (P := P) hprev' hB
  have hF : f₀ = f := by
    change -(H₀ - A.average H₀) - hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u₁) = _
    rw [hH, hfast]
    rfl
  change ∃ hf : A.average f = 0,
    (L p).oscillation.V = (S.solveTransverse f hf).val.V ∧
    (L p).oscillation.p = (S.solveTransverse f hf).val.p
  rw [← hF]
  exact ⟨hf₀, congrArg HierarchyTransverseOutput.V hselected,
    congrArg HierarchyTransverseOutput.p hselected⟩

/-- The mean and its pressure at each correction level are the selected
mean solve of the exact phase-averaged preliminary source. -/
theorem construct_mean_selected (S : FiniteHierarchySolvers A) {P p : ℕ}
    (hp : p ∈ Finset.Icc 2 P) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    let H := A.sourceBeforeMean u P completionSwitch p
    let f := -A.average H - (if p = 2 then parentResidual else 0)
    ∃ hf : A.average f = f,
      u.B p = (S.solveMean f hf).val.B ∧ u.q p = (S.solveMean f hf).val.q := by
  obtain ⟨hp₂, hpP⟩ := Finset.mem_Icc.mp hp
  let L := S.level P completionSwitch parentResidual hR leading
  let u := profiles L
  let u₀ := profiles (earlierLevels (p := p) (fun i _ => L i))
  let H₀ := A.sourceBeforeMean u₀ P completionSwitch p
  let f₀ := meanSource A H₀ parentResidual p
  let f := meanSource A (A.sourceBeforeMean u P completionSwitch p) parentResidual p
  have hf₀ : A.average f₀ = f₀ := S.average_meanSource hR H₀ p
  have hselected : (L p).mean = (S.solveMean f₀ hf₀).val := by
    rw [show L p = _ from S.level_solve hp₂ hpP completionSwitch parentResidual hR leading]
    rfl
  have hF : f₀ = f :=
    congrArg (fun H => meanSource A H parentResidual p)
      (A.sourceBeforeMean_congr (P := P) hp₂ (prefix_agrees_before L) completionSwitch)
  change ∃ hf : A.average f = f,
    (L p).mean.B = (S.solveMean f hf).val.B ∧ (L p).mean.q = (S.solveMean f hf).val.q
  rw [← hF]
  exact ⟨hf₀, congrArg HierarchyMeanOutput.B hselected, congrArg HierarchyMeanOutput.q hselected⟩

/-- At every retained correction level, the profiles solve the exact mean
and transverse equations of the expansion. -/
theorem construct_equations (S : FiniteHierarchySolvers A) {P p : ℕ}
    (hp : p ∈ Finset.Icc 2 P) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    let H := A.sourceBeforeMean u P completionSwitch p
    (A.material (u.B p) + A.labelGrad (u.q p) =
      -A.average H - (if p = 2 then parentResidual else 0)) ∧
    (A.material (u.V p) + A.phaseGrad (u.p p) =
      -(H - A.average H) - hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)) := by
  obtain ⟨hp₂, hpP⟩ := Finset.mem_Icc.mp hp
  let L := S.level P completionSwitch parentResidual hR leading
  let u := profiles L
  let u₀ := profiles (earlierLevels (p := p) (fun i _ => L i))
  let l := S.solveLevel P completionSwitch parentResidual hR (p := p) (fun i _ => L i)
  have hlevel : L p = l.val := S.level_solve hp₂ hpP completionSwitch parentResidual hR leading
  have hprev : u₀.AgreesBefore u p := prefix_agrees_before L
  have hsup : (setMean u₀ p l.val.mean.B).AgreesBefore u p := by
    intro i hi
    obtain ⟨hv, hc, hb, hpress⟩ := hprev i hi
    exact ⟨hv, hc, by
      simpa [setMean, Function.update_of_ne (ne_of_lt hi)] using hb, hpress⟩
  have hnew : (setMean u₀ p l.val.mean.B).B p = u.B p := by
    simp [setMean, u, profiles, hlevel]
  have hsource := A.sourceBeforeMean_congr (P := P) hp₂ hprev completionSwitch
  have hsupp := A.meanPhaseAdvectionAtLevel_congr (P := P) hsup hnew
  change (A.material (L p).mean.B + A.labelGrad (L p).mean.q = _) ∧
    (A.material (L p).oscillation.V + A.phaseGrad (L p).oscillation.p = _)
  rw [hlevel]
  have hm := l.property.1
  have ho := l.property.2
  change _ = meanSource A (A.sourceBeforeMean u₀ P completionSwitch p) parentResidual p at hm
  change _ = transverseSource A (setMean u₀ p l.val.mean.B) P p
    (A.sourceBeforeMean u₀ P completionSwitch p) at ho
  refine ⟨hm.trans (congrArg (fun H => meanSource A H parentResidual p) hsource), ho.trans ?_⟩
  refine (congrArg (transverseSource A (setMean u₀ p l.val.mean.B) P p) hsource).trans ?_
  exact congrArg (fun f => -(A.sourceBeforeMean u P completionSwitch p -
    A.average (A.sourceBeforeMean u P completionSwitch p)) - f) hsupp

/-- Every retained oscillation, including the leading wave, is completed
at its own level. -/
theorem construct_completion (S : FiniteHierarchySolvers A) {P p : ℕ}
    (hp : p ∈ Finset.Icc 1 P) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    u.C p = S.complete (u.V p) := by
  obtain ⟨hp₁, hpP⟩ := Finset.mem_Icc.mp hp
  change (S.level P completionSwitch parentResidual hR leading p).C =
    S.complete (S.level P completionSwitch parentResidual hR leading p).oscillation.V
  by_cases h1 : p = 1
  · subst p
    rw [S.level_one]
  · rw [S.level_solve (by omega) hpP]
    rfl

/-- The full velocity is divergence free whenever the two solvers have the
divergence properties of (5.11) and the completed oscillation. -/
theorem construct_divergence_eq_zero {G : Type*} [AddCommGroup G] [Module ℝ G]
    (S : FiniteHierarchySolvers A) (P : ℕ) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A)
    (divergence : E →ₗ[ℝ] G)
    (hC : ∀ o : HierarchyTransverseOutput A, divergence (o.V + S.complete o.V) = 0)
    (hB : ∀ f hf, divergence (S.solveMean f hf).val.B = 0) :
    divergence ((S.construct P completionSwitch parentResidual hR leading).velocity P) = 0 := by
  let u := S.construct P completionSwitch parentResidual hR leading
  refine u.divergence_velocity_eq_zero P divergence ?_ ?_
  · intro p hp
    rw [S.construct_completion hp completionSwitch parentResidual hR leading]
    exact hC (S.level P completionSwitch parentResidual hR leading p).oscillation
  · intro p hp
    obtain ⟨hp₁, hpP⟩ := Finset.mem_Icc.mp hp
    change divergence (S.level P completionSwitch parentResidual hR leading p).mean.B = 0
    by_cases h1 : p = 1
    · subst p
      rw [S.level_one]
      exact divergence.map_zero
    · rw [S.level_solve (by omega) hpP]
      exact hB _ _

/-- Phase subtraction returns exactly the sum of the completed oscillations. -/
theorem construct_velocity_sub_average (S : FiniteHierarchySolvers A)
    (P : ℕ) (completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A) :
    let u := S.construct P completionSwitch parentResidual hR leading
    u.velocity P - A.average (u.velocity P) =
      ∑ p ∈ Finset.Icc 1 P, (u.V p + u.C p) := by
  let L := S.level P completionSwitch parentResidual hR leading
  exact (profiles L).velocity_sub_average P A.average (fun i => (L i).oscillation.average_V)
    (fun i => (L i).average_C) (fun i => (L i).mean.average_B)

/-- The constructed expansion has the residual and switching terms stated
in the algebraic part of Proposition 5.4. -/
theorem construct_momentum (S : FiniteHierarchySolvers A) {P : ℕ} (hP : 2 ≤ P)
    (leadingSwitch completionSwitch parentResidual : E)
    (hR : A.average parentResidual = parentResidual) (leading : HierarchyTransverseOutput A)
    (hL : A.material leading.V + A.phaseGrad leading.p = leadingSwitch) :
    let u := S.construct P completionSwitch parentResidual hR leading
    A.material (u.velocity P) + A.labelAdv (u.velocity P) (u.velocity P) +
      A.phaseAdv (u.velocity P) (u.velocity P) + A.labelGrad (u.pressure P) +
      A.phaseGrad (u.pressure P) + parentResidual =
        A.remainder u P + (leadingSwitch + completionSwitch) := by
  let L := S.level P completionSwitch parentResidual hR leading
  let u := profiles L
  have h₀ : L 0 = zeroLevel A :=
    S.level_zero_or_past (by omega) (.inl rfl) completionSwitch parentResidual hR leading
  have h₁ := S.level_one P completionSwitch parentResidual hR leading
  have hlast : L (P + 1) = zeroLevel A :=
    S.level_zero_or_past (by omega) (.inr (by omega)) completionSwitch parentResidual hR leading
  change A.material (u.velocity P) + A.labelAdv (u.velocity P) (u.velocity P) +
    A.phaseAdv (u.velocity P) (u.velocity P) + A.labelGrad (u.pressure P) +
    A.phaseGrad (u.pressure P) + parentResidual = A.remainder u P + (leadingSwitch + completionSwitch)
  refine A.momentum_eq_remainder_add_switch u hP leadingSwitch completionSwitch parentResidual
    ?_ ?_ ?_ ?_ ?_ (fun i v => (L i).oscillation.phaseAdv_V v)
    (fun i v => (L i).mean.phaseAdv_B v) (fun i => (L i).mean.phaseGrad_q) ?_ ?_ ?_
  · simp [u, profiles, h₀, zeroLevel]
  · simp [u, profiles, L, h₁, zeroMean]
  · simp [u, profiles, L, h₁, zeroMean]
  · simp [u, profiles, hlast, zeroLevel]
  · simp [u, profiles, hlast, zeroLevel, zeroMean]
  · simpa [u, profiles, L, h₁] using hL
  · exact fun p hp => (S.construct_equations hp completionSwitch parentResidual hR leading).1
  · exact fun p hp => (S.construct_equations hp completionSwitch parentResidual hR leading).2

end FiniteHierarchySolvers

end TorusEuler

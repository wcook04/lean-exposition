import TorusEuler.FiniteHierarchyConstruction
import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchyTwistedProfiles

/-! Support propagation through the selected oscillatory solves and the tail. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff Topology

namespace TorusEuler

section OrderedSupport

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

/-- Local operations preserve vanishing on the inactive region. Slow
advection of two means is again fixed by the phase average. -/
structure HierarchySupportLaws (A : HierarchyOperators E F)
    (E₀ : Submodule ℝ E) (F₀ : Submodule ℝ F) : Prop where
  material : ∀ {u}, u ∈ E₀ → A.material u ∈ E₀
  labelGrad : ∀ {q}, q ∈ F₀ → A.labelGrad q ∈ E₀
  labelAdv_left : ∀ {u}, u ∈ E₀ → ∀ v, A.labelAdv u v ∈ E₀
  labelAdv_right : ∀ u {v}, v ∈ E₀ → A.labelAdv u v ∈ E₀
  phaseAdv_right : ∀ u {v}, v ∈ E₀ → A.phaseAdv u v ∈ E₀
  average : ∀ {u}, u ∈ E₀ → A.average u ∈ E₀
  labelAdv_mean : ∀ {u v}, A.average u = u → A.average v = v →
    A.average (A.labelAdv u v) = A.labelAdv u v

namespace HierarchySupportLaws

variable {A : HierarchyOperators E F} {E₀ : Submodule ℝ E} {F₀ : Submodule ℝ F}

private theorem labelProduct_sub_mean_mem (L : HierarchySupportLaws A E₀ F₀)
    (u : HierarchyProfiles E F) (ij : ℕ × ℕ) (hi : u.Y ij.1 ∈ E₀) (hj : u.Y ij.2 ∈ E₀) :
    A.labelProduct u ij - A.labelAdv (u.B ij.1) (u.B ij.2) ∈ E₀ := by
  have h : A.labelProduct u ij - A.labelAdv (u.B ij.1) (u.B ij.2) =
      A.labelAdv (u.Y ij.1) (u.Z ij.2) + A.labelAdv (u.B ij.1) (u.Y ij.2) := by
    unfold HierarchyOperators.labelProduct
    simp only [HierarchyProfiles.Z, map_add, LinearMap.add_apply]
    abel
  rw [h]
  exact E₀.add_mem (L.labelAdv_left hi _) (L.labelAdv_right _ hj)

private theorem partialSource_pairs {P shift p : ℕ} {ij : ℕ × ℕ}
    (hij : ij ∈ (hierarchyAdvectionPairs P shift).filter
      (fun ij => hierarchyAdvectionLevel shift ij = p)) :
    shift + 1 ≤ ij.1 ∧ 1 ≤ ij.2 ∧ ij.1 + ij.2 = p + shift := by
  obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
  obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
  rw [Finset.mem_Icc] at hi hj
  unfold hierarchyAdvectionLevel at hlevel
  exact ⟨hi.1, hj.1, by omega⟩

/-- On the inactive region the preliminary source is a sum of mean products.
Centering removes that sum, and every supplementary term has an inactive
oscillation in its second argument. -/
theorem transverseSource_mem (L : HierarchySupportLaws A E₀ F₀)
    (u : HierarchyProfiles E F) {P p : ℕ} (hp : 2 ≤ p)
    {completionSwitch : E} (hSwitch : completionSwitch ∈ E₀)
    (hB : ∀ i, A.average (u.B i) = u.B i)
    (hprev : ∀ i < p, u.V i ∈ E₀ ∧ u.C i ∈ E₀ ∧ u.p i ∈ F₀) :
    let H := A.sourceBeforeMean u P completionSwitch p
    (-(H - A.average H) - hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u)) ∈ E₀ := by
  let H := A.sourceBeforeMean u P completionSwitch p
  let meanLabel (ij : ℕ × ℕ) := A.labelAdv (u.B ij.1) (u.B ij.2)
  let D := hierarchyAdvectionAtLevel P 0 p meanLabel
  have hY (i : ℕ) (hi : i < p) : u.Y i ∈ E₀ :=
    E₀.add_mem (hprev i hi).1 (hprev (i - 1) (by omega)).2.1
  have hslow : hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) - D ∈ E₀ := by
    unfold D hierarchyAdvectionAtLevel
    rw [← Finset.sum_sub_distrib]
    refine Submodule.sum_mem E₀ fun ij hij => ?_
    obtain ⟨hi, hj, hsum⟩ := partialSource_pairs hij
    exact L.labelProduct_sub_mean_mem u ij (hY ij.1 (by omega)) (hY ij.2 (by omega))
  have hfast (w : ℕ × ℕ → E)
      (hw : ∀ ij, u.Y ij.2 ∈ E₀ → w ij ∈ E₀) :
      hierarchyAdvectionAtLevel P 1 p w ∈ E₀ := by
    unfold hierarchyAdvectionAtLevel
    refine Submodule.sum_mem E₀ fun ij hij => ?_
    obtain ⟨hi, hj, hsum⟩ := partialSource_pairs hij
    exact hw ij (hY ij.2 (by omega))
  have hC := hfast (A.completionPhaseProduct u) fun ij hYj => L.phaseAdv_right _ hYj
  have hBfast := hfast (A.meanPhaseProduct u) fun ij hYj => L.phaseAdv_right _ hYj
  have hlin : A.material (u.C (p - 1)) + A.labelGrad (u.p (p - 1)) -
      (if p = 2 then completionSwitch else 0) ∈ E₀ := by
    have hi : p - 1 < p := by omega
    refine E₀.sub_mem (E₀.add_mem (L.material (hprev _ hi).2.1) (L.labelGrad (hprev _ hi).2.2)) ?_
    by_cases hp' : p = 2 <;> simp [hp', hSwitch]
  have hH : H - D ∈ E₀ := by
    have heq : H - D =
        (A.material (u.C (p - 1)) + A.labelGrad (u.p (p - 1)) -
          (if p = 2 then completionSwitch else 0)) +
        (hierarchyAdvectionAtLevel P 0 p (A.labelProduct u) - D) +
        hierarchyAdvectionAtLevel P 1 p (A.completionPhaseProduct u) := by
      dsimp only [H, HierarchyOperators.sourceBeforeMean]
      abel
    rw [heq]
    exact E₀.add_mem (E₀.add_mem hlin hslow) hC
  have hD : A.average D = D := by
    unfold D hierarchyAdvectionAtLevel
    rw [map_sum]
    exact Finset.sum_congr rfl fun ij _ => L.labelAdv_mean (hB ij.1) (hB ij.2)
  have hcenter : H - A.average H ∈ E₀ := by
    have heq : H - A.average H = (H - D) - A.average (H - D) := by
      rw [map_sub, hD]
      abel
    rw [heq]
    exact E₀.sub_mem hH (L.average hH)
  exact E₀.sub_mem (E₀.neg_mem hcenter) hBfast

/-- The ordered selection of the means and transverse solves preserves
the inactive-region support of every oscillatory component. -/
theorem construct_mem (L : HierarchySupportLaws A E₀ F₀)
    (solvers : FiniteHierarchySolvers A) {P : ℕ} (hP : 1 ≤ P)
    (completionSwitch parentResidual : E) (hR : A.average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput A)
    (hLeadingV : leading.V ∈ E₀) (hLeadingp : leading.p ∈ F₀) (hSwitch : completionSwitch ∈ E₀)
    (hSolve : ∀ f (hf : A.average f = 0), f ∈ E₀ →
      (solvers.solveTransverse f hf).val.V ∈ E₀ ∧ (solvers.solveTransverse f hf).val.p ∈ F₀)
    (hComplete : ∀ v ∈ E₀, A.average v = 0 → solvers.complete v ∈ E₀) :
    let u := solvers.construct P completionSwitch parentResidual hR leading
    (∀ i, u.V i ∈ E₀ ∧ u.C i ∈ E₀ ∧ u.p i ∈ F₀) ∧
    (∀ i ∈ Finset.Icc 2 P,
      let H := A.sourceBeforeMean u P completionSwitch i
      (-(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)) ∈ E₀) := by
  let u := solvers.construct P completionSwitch parentResidual hR leading
  have hB (i : ℕ) : A.average (u.B i) = u.B i :=
    solvers.construct_average_B P completionSwitch parentResidual hR leading i
  have hall (i : ℕ) : u.V i ∈ E₀ ∧ u.C i ∈ E₀ ∧ u.p i ∈ F₀ := by
    induction i using Nat.strongRecOn with
    | ind i ih =>
      by_cases hi : i = 0 ∨ P < i
      · obtain ⟨hv, hc, _, hp, _⟩ :=
          solvers.construct_eq_zero_of_index hP hi completionSwitch parentResidual hR leading
        rw [hv, hc, hp]
        exact ⟨E₀.zero_mem, E₀.zero_mem, F₀.zero_mem⟩
      have hiP : i ∈ Finset.Icc 1 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      have hc := solvers.construct_completion hiP completionSwitch parentResidual hR leading
      have hvp : u.V i ∈ E₀ ∧ u.p i ∈ F₀ ∧ A.average (u.V i) = 0 := by
        by_cases h1 : i = 1
        · subst i
          obtain ⟨hv, hp, _, _⟩ := solvers.construct_leading P completionSwitch parentResidual hR leading
          change u.V 1 = leading.V at hv
          change u.p 1 = leading.p at hp
          rw [hv, hp]
          exact ⟨hLeadingV, hLeadingp, leading.average_V⟩
        · have hiP' : i ∈ Finset.Icc 2 P := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
          obtain ⟨hf, hv, hp⟩ :=
            solvers.construct_transverse_selected hiP' completionSwitch parentResidual hR leading
          rw [hv, hp]
          obtain ⟨hV, hP⟩ := hSolve _ hf
            (L.transverseSource_mem u (P := P) (by omega) hSwitch hB ih)
          exact ⟨hV, hP, (solvers.solveTransverse _ hf).val.average_V⟩
      refine ⟨hvp.1, ?_, hvp.2.1⟩
      change u.C i = solvers.complete (u.V i) at hc
      rw [hc]
      exact hComplete _ hvp.1 hvp.2.2
  refine ⟨hall, fun i hi => ?_⟩
  exact L.transverseSource_mem u (Finset.mem_Icc.mp hi).1 hSwitch hB (fun j _ => hall j)

/-- Outside the support of the completed oscillations, exactly the slow
products of two means remain in the hierarchy tail. -/
theorem remainder_sub_mean_mem (L : HierarchySupportLaws A E₀ F₀)
    (u : HierarchyProfiles E F) (P : ℕ)
    (h : ∀ i, u.V i ∈ E₀ ∧ u.C i ∈ E₀ ∧ u.p i ∈ F₀) :
    A.remainder u P -
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)) ∈ E₀ := by
  have hY (i : ℕ) : u.Y i ∈ E₀ := E₀.add_mem (h i).1 (h (i - 1)).2.1
  have hslow : (∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij) -
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)) ∈ E₀ := by
    rw [← Finset.sum_sub_distrib]
    exact Submodule.sum_mem E₀ fun ij _ => L.labelProduct_sub_mean_mem u ij (hY _) (hY _)
  have hfast : (∑ ij ∈ hierarchyTailPairs P 1,
      (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij)) ∈ E₀ :=
    Submodule.sum_mem E₀ fun ij _ => E₀.add_mem (L.phaseAdv_right _ (hY ij.2))
      (L.phaseAdv_right _ (hY ij.2))
  have heq : A.remainder u P - (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)) =
      (A.material (u.C P) + A.labelGrad (u.p P)) +
      ((∑ ij ∈ hierarchyTailPairs P 0, A.labelProduct u ij) -
        (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2))) +
      (∑ ij ∈ hierarchyTailPairs P 1, (A.completionPhaseProduct u ij + A.meanPhaseProduct u ij)) := by
    unfold HierarchyOperators.remainder
    abel
  rw [heq]
  exact E₀.add_mem (E₀.add_mem (E₀.add_mem (L.material (h P).2.1) (L.labelGrad (h P).2.2)) hslow) hfast

end HierarchySupportLaws

end OrderedSupport

/-- Inactive points consist of preactivation time slices and labels
outside the common envelope, with all phases at each such point. -/
def hierarchyInactiveRegion (T τ : ℝ) (S : Set Vec3) : Set HierarchyProfilePoint :=
  {x | x ∈ hierarchyProfileSlab T ∧ (x.1 < τ ∨ x.2.1 ∉ S)}

namespace HierarchySmoothProfile

variable {T τ : ℝ} {S : Set Vec3}

section Locality

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full slab derivative vanishes on the relatively open inactive region. -/
theorem fderivWithin_eq_zero_on_inactive (hT : 0 < T) (hS : IsClosed S)
    (f : HierarchySmoothProfile T E)
    (hf : EqOn f.val 0 (hierarchyInactiveRegion T τ S))
    {x : HierarchyProfilePoint} (hx : x ∈ hierarchyInactiveRegion T τ S) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) x = 0 := by
  let U : Set HierarchyProfilePoint := {y | y.1 < τ ∨ y.2.1 ∉ S}
  have hU : IsOpen U :=
    (isOpen_lt continuous_fst continuous_const).union
      (hS.isOpen_compl.preimage continuous_snd.fst)
  have hN : ∀ᶠ y in 𝓝[hierarchyProfileSlab T] x, y ∈ U :=
    nhdsWithin_le_nhds (hU.mem_nhds hx.2)
  have heq : f.val =ᶠ[𝓝[hierarchyProfileSlab T] x] (fun _ => (0 : E)) := by
    filter_upwards [hN, self_mem_nhdsWithin (s := hierarchyProfileSlab T)] with y hy hs
    exact hf ⟨hs, hy⟩
  have hd := heq.fderivWithin_eq_of_mem (𝕜 := ℝ) hx.1
  exact hd.trans ((hasFDerivWithinAt_const (0 : E) x (hierarchyProfileSlab T)).fderivWithin
    (uniqueDiffOn_hierarchyProfileSlab hT x hx.1))

private theorem fderiv_labelSlice_apply (f : HierarchySmoothProfile T E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a d : Vec3) (s : ℝ) :
    fderiv ℝ (fun b => f.val (t, b, s)) a d =
      fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, a, s) (0, d, 0) := by
  let L := (inr ℝ ℝ (Vec3 × ℝ)).comp (inl ℝ Vec3 ℝ)
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hF := ((smooth f).differentiableOn (by simp) (t, a, s) hx).hasFDerivWithinAt
  have hI : HasFDerivAt (fun b : Vec3 => (t, b, s)) L a :=
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (a, s)).comp a
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)
  have hmem : ∀ᶠ b : Vec3 in 𝓝 a, (t, b, s) ∈ hierarchyProfileSlab T :=
    Eventually.of_forall fun _ => ⟨ht, mem_univ _⟩
  exact DFunLike.congr_fun (hF.comp_hasFDerivAt a hI hmem).fderiv d

/-- A strictly vanishing prefix includes the positive activation time
by continuity on the closed time slab. -/
theorem eq_zero_at_activation (f : HierarchySmoothProfile T E)
    (hτ : 0 < τ) (hτT : τ ≤ T)
    (hf : EqOn f.val 0 (hierarchyInactiveRegion T τ S)) (a : Vec3) (s : ℝ) :
    f.val (τ, a, s) = 0 := by
  have hc : Continuous (fun t : ℝ => (t, a, s)) := continuous_id.prodMk continuous_const
  have hfc : ContinuousOn (fun t => f.val (t, a, s)) (Icc 0 T) :=
    (smooth f).continuousOn.comp hc.continuousOn (fun _ ht => ⟨ht, mem_univ _⟩)
  have hsmall : Ico 0 τ ⊆ Icc 0 T := fun _ hy => ⟨hy.1, hy.2.le.trans hτT⟩
  have hcl : τ ∈ closure (Ico 0 τ) := by
    rw [closure_Ico hτ.ne]
    exact ⟨hτ.le, le_rfl⟩
  exact ((hfc τ ⟨hτ.le, hτT⟩).mono hsmall).eq_const_of_mem_closure hcl
    (fun y hy => hf ⟨⟨hsmall hy, mem_univ _⟩, Or.inl hy.2⟩)

end Locality

/-- The concrete normalized potential and its slow curl preserve the
support of the input transverse velocity. -/
theorem profileCompletion_eq_zero_on_inactive (hT : 0 < T) (hS : IsClosed S)
    (G : HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)) (κ V : HierarchySmoothProfile T Vec3)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val (t, a, 0) ≠ 0)
    (hV : EqOn V.val 0 (hierarchyInactiveRegion T τ S)) :
    EqOn (profileCompletion hT G κ hκ V).val 0 (hierarchyInactiveRegion T τ S) := by
  let Q := profileWavePotential hT κ hκ V
  have hQ : EqOn Q.val 0 (hierarchyInactiveRegion T τ S) := by
    rintro ⟨t, a, s⟩ hx
    change Q.val (t, a, s) = 0
    have hv (σ : ℝ) : V.val (t, a, σ) = 0 :=
      hV (x := (t, a, σ)) ⟨⟨hx.1.1, mem_univ _⟩, hx.2⟩
    rw [show Q.val (t, a, s) =
      wavePotential (κ.val (t, a, 0)) (fun σ => V.val (t, a, σ)) s from
      profileWavePotential_apply hT κ hκ V hx.1.1 a s]
    exact wavePotential_zero_of_profile_zero hv s
  rintro ⟨t, a, s⟩ hx
  have hD := fderivWithin_eq_zero_on_inactive hT hS Q hQ hx
  have hlabel : fderiv ℝ (fun b => Q.val (t, b, s)) a = 0 := by
    apply ContinuousLinearMap.ext
    intro d
    rw [fderiv_labelSlice_apply Q hx.1.1 a d s, hD]
    rfl
  change (profileSlowCurl hT G Q).val (t, a, s) = 0
  rw [profileSlowCurl_apply hT G Q hx.1.1, hlabel, zero_comp]
  exact curlOfDerivativeCLM.map_zero

/-- Slow advection of two phase-independent profiles stays phase independent
when the coframe is phase independent. -/
theorem labelAdv_independent (hT : 0 < T)
    (G : HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)) (u v : HierarchySmoothProfile T Vec3)
    (hG : HierarchyPeriodicProfile.PhaseIndependent G)
    (hu : HierarchyPeriodicProfile.PhaseIndependent u)
    (hv : HierarchyPeriodicProfile.PhaseIndependent v) :
    HierarchyPeriodicProfile.PhaseIndependent (advect hT (labelDirections G) u v) := by
  rintro ⟨t, a, s⟩ hx σ
  have hσ : (t, a, σ) ∈ hierarchyProfileSlab T := ⟨hx.1, mem_univ _⟩
  rw [advect_apply hT _ u v hσ, advect_apply hT _ u v hx,
    labelDirections_apply G u hσ, labelDirections_apply G u hx, hG _ hx σ, hu _ hx σ,
    ← fderiv_labelSlice_apply v hx.1 a _ σ, ← fderiv_labelSlice_apply v hx.1 a _ s]
  have heq : (fun b => v.val (t, b, σ)) = fun b => v.val (t, b, s) :=
    funext fun b => hv (t, b, s) ⟨hx.1, mem_univ _⟩ σ
  rw [heq]

end HierarchySmoothProfile

/-- Inactive points together with the activation slice. -/
def hierarchyInactiveThroughActivation (T τ : ℝ) (S : Set Vec3) : Set HierarchyProfilePoint :=
  {x | x ∈ hierarchyProfileSlab T ∧ (x.1 ≤ τ ∨ x.2.1 ∉ S)}

namespace HierarchyTwistedProfile

variable {T τ : ℝ} {k : Vec3} {S : Set Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "SP" => HierarchyTwistedProfile T k ℝ
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

/-- Twisted profiles vanishing at each inactive point form a submodule. -/
def inactiveSubmodule (T : ℝ) (k : Vec3) (E : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (τ : ℝ) (S : Set Vec3) :
    Submodule ℝ (HierarchyTwistedProfile T k E) where
  carrier := {f | EqOn f.val.val.val 0 (hierarchyInactiveRegion T τ S)}
  zero_mem' := fun _ _ => rfl
  add_mem' := by
    intro f g hf hg x hx
    change f.val.val.val x + g.val.val.val x = 0
    rw [hf hx, hg hx]
    exact zero_add 0
  smul_mem' := by
    intro c f hf x hx
    change c • f.val.val.val x = 0
    rw [hf hx]
    exact smul_zero c

theorem mem_inactiveSubmodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} :
    f ∈ inactiveSubmodule T k E τ S ↔ EqOn f.val.val.val 0 (hierarchyInactiveRegion T τ S) :=
  Iff.rfl

private theorem eq_zero_through_activation {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} (hτ : 0 < τ)
    (hf : f ∈ inactiveSubmodule T k E τ S) :
    EqOn f.val.val.val 0 (hierarchyInactiveThroughActivation T τ S) := by
  rintro ⟨t, a, s⟩ hx
  rcases hx.2 with ht | ha
  · rcases lt_or_eq_of_le ht with hlt | rfl
    · exact hf ⟨hx.1, Or.inl hlt⟩
    · exact HierarchySmoothProfile.eq_zero_at_activation f.val.val hτ hx.1.1.2 hf a s
  · exact hf ⟨hx.1, Or.inr ha⟩

/-- The differential operators for the actual twisted hierarchy satisfy the
inactive-region laws used by the ordered recursion. -/
theorem inactiveLaws (hT : 0 < T) (hS : IsClosed S) (G M : MP) (κ : VP)
    (hG : HierarchyPeriodicProfile.PhaseIndependent G.val.val) :
    HierarchySupportLaws (twistedHierarchyOperators hT G M κ)
      (inactiveSubmodule T k Vec3 τ S) (inactiveSubmodule T k ℝ τ S) := by
  let A := twistedHierarchyOperators hT G M κ
  let A₀ := HierarchySmoothProfile.hierarchyConcreteOperators hT G.val.val M.val.val κ.val.val
  constructor
  · intro u hu x hx
    change (A₀.material u.val.val).val x = 0
    rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT G.val.val M.val.val
      κ.val.val u.val.val hx.1, HierarchySmoothProfile.fderivWithin_eq_zero_on_inactive hT hS
      u.val.val hu hx, show u.val.val.val x = 0 from hu hx]
    simp
  · intro q hq x hx
    change (HierarchySmoothProfile.labelGradient hT G.val.val q.val.val).val x = 0
    rw [HierarchySmoothProfile.labelGradient_apply hT G.val.val q.val.val hx.1,
      HierarchySmoothProfile.fderivWithin_eq_zero_on_inactive hT hS q.val.val hq hx]
    simp
  · intro u hu v x hx
    change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val.val)
      u.val.val v.val.val).val x = 0
    rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx.1,
      HierarchySmoothProfile.labelDirections_apply G.val.val u.val.val hx.1,
      show u.val.val.val x = 0 from hu hx, map_zero]
    exact map_zero _
  · intro u v hv x hx
    change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.labelDirections G.val.val)
      u.val.val v.val.val).val x = 0
    rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx.1,
      HierarchySmoothProfile.fderivWithin_eq_zero_on_inactive hT hS v.val.val hv hx]
    rfl
  · intro u v hv x hx
    change (HierarchySmoothProfile.advect hT (HierarchySmoothProfile.phaseDirections κ.val.val)
      u.val.val v.val.val).val x = 0
    rw [HierarchySmoothProfile.advect_apply hT _ _ _ hx.1,
      HierarchySmoothProfile.fderivWithin_eq_zero_on_inactive hT hS v.val.val hv hx]
    rfl
  · intro u hu x hx
    change (HierarchySmoothProfile.profilePhaseAverage hT u.val.val).val x = 0
    rw [HierarchySmoothProfile.profilePhaseAverage_apply hT u.val.val hx.1]
    rw [show (fun s => u.val.val.val (x.1, x.2.1, s)) = fun _ => 0 from
      funext fun s => hu ⟨⟨hx.1.1, mem_univ _⟩, hx.2⟩]
    exact phaseMean_const 0
  · intro u v hu hv
    have hu' : HierarchyPeriodicProfile.profilePhaseAverage hT u.val = u.val :=
      congrArg Subtype.val hu
    have hv' : HierarchyPeriodicProfile.profilePhaseAverage hT v.val = v.val :=
      congrArg Subtype.val hv
    have hU := HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT u.val hu'
    have hV := HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT v.val hv'
    have hL := HierarchySmoothProfile.labelAdv_independent hT G.val.val u.val.val v.val.val hG hU hV
    apply Subtype.ext
    exact HierarchyPeriodicProfile.profilePhaseAverage_eq_self_of_independent hT (A.labelAdv u v).val hL

set_option maxHeartbeats 1000000 in
/-- The selected twisted hierarchy vanishes in its oscillatory components on the inactive region.
The tail there consists exactly of the retained slow mean products. -/
theorem construct_support_and_tail_on_inactive
    (hT : 0 < T) (hS : IsClosed S) (G M : MP) (κ : VP)
    (hG : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (solvers : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    {P : ℕ} (hP : 1 ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeadingV : EqOn leading.V.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hLeadingp : EqOn leading.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSwitch : EqOn completionSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSolve : ∀ f (hf : (twistedHierarchyOperators hT G M κ).average f = 0),
      EqOn f.val.val.val 0 (hierarchyInactiveRegion T τ S) →
      EqOn (solvers.solveTransverse f hf).val.V.val.val.val 0 (hierarchyInactiveRegion T τ S) ∧
      EqOn (solvers.solveTransverse f hf).val.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hComplete : ∀ v, (twistedHierarchyOperators hT G M κ).average v = 0 →
      (solvers.complete v).val.val =
        HierarchySmoothProfile.profileCompletion hT G.val.val κ.val.val hκ v.val.val) :
    let A := twistedHierarchyOperators hT G M κ
    let u := solvers.construct P completionSwitch parentResidual hR leading
    let U := hierarchyInactiveRegion T τ S
    (∀ i, EqOn (u.V i).val.val.val 0 U ∧ EqOn (u.C i).val.val.val 0 U ∧ EqOn (u.p i).val.val.val 0 U) ∧
    (∀ i ∈ Finset.Icc 2 P,
      let H := A.sourceBeforeMean u P completionSwitch i
      let f := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)
      EqOn f.val.val.val 0 U) ∧
    EqOn (A.remainder u P).val.val.val
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)).val.val.val U := by
  let A := twistedHierarchyOperators hT G M κ
  let u := solvers.construct P completionSwitch parentResidual hR leading
  let E₀ := inactiveSubmodule T k Vec3 τ S
  let F₀ := inactiveSubmodule T k ℝ τ S
  let Mtail : VP := ∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)
  have hL : HierarchySupportLaws A E₀ F₀ := inactiveLaws hT hS G M κ hG
  have hc (v : VP) (hv : v ∈ E₀) (hvmean : A.average v = 0) : solvers.complete v ∈ E₀ := by
    change EqOn (solvers.complete v).val.val.val 0 (hierarchyInactiveRegion T τ S)
    rw [hComplete v hvmean]
    exact HierarchySmoothProfile.profileCompletion_eq_zero_on_inactive hT hS G.val.val κ.val.val
      v.val.val hκ hv
  obtain ⟨hLevels, hSources⟩ := hL.construct_mem solvers hP completionSwitch parentResidual
    hR leading hLeadingV hLeadingp hSwitch hSolve hc
  refine ⟨hLevels, hSources, fun x hx => ?_⟩
  have htail : A.remainder u P - Mtail ∈ E₀ := hL.remainder_sub_mean_mem u P hLevels
  exact sub_eq_zero.mp (htail hx)

set_option maxHeartbeats 1000000 in
/-- The selected twisted hierarchy retains the common envelope and is zero
in its oscillatory components through the positive activation time.
Its tail on this region is exactly the retained slow sum of mean products. -/
theorem construct_support_and_tail
    (hT : 0 < T) (hτ : 0 < τ) (hS : IsClosed S) (G M : MP) (κ : VP)
    (hG : HierarchyPeriodicProfile.PhaseIndependent G.val.val)
    (hκ : ∀ t ∈ Icc 0 T, ∀ a, κ.val.val.val (t, a, 0) ≠ 0)
    (solvers : FiniteHierarchySolvers (twistedHierarchyOperators hT G M κ))
    {P : ℕ} (hP : 1 ≤ P) (completionSwitch parentResidual : VP)
    (hR : (twistedHierarchyOperators hT G M κ).average parentResidual = parentResidual)
    (leading : HierarchyTransverseOutput (twistedHierarchyOperators hT G M κ))
    (hLeadingV : EqOn leading.V.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hLeadingp : EqOn leading.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSwitch : EqOn completionSwitch.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hSolve : ∀ f (hf : (twistedHierarchyOperators hT G M κ).average f = 0),
      EqOn f.val.val.val 0 (hierarchyInactiveRegion T τ S) →
      EqOn (solvers.solveTransverse f hf).val.V.val.val.val 0 (hierarchyInactiveRegion T τ S) ∧
      EqOn (solvers.solveTransverse f hf).val.p.val.val.val 0 (hierarchyInactiveRegion T τ S))
    (hComplete : ∀ v, (twistedHierarchyOperators hT G M κ).average v = 0 →
      (solvers.complete v).val.val =
        HierarchySmoothProfile.profileCompletion hT G.val.val κ.val.val hκ v.val.val) :
    let A := twistedHierarchyOperators hT G M κ
    let u := solvers.construct P completionSwitch parentResidual hR leading
    let U := hierarchyInactiveThroughActivation T τ S
    (∀ i, EqOn (u.V i).val.val.val 0 U ∧ EqOn (u.C i).val.val.val 0 U ∧ EqOn (u.p i).val.val.val 0 U) ∧
    (∀ i ∈ Finset.Icc 2 P,
      let H := A.sourceBeforeMean u P completionSwitch i
      let f := -(H - A.average H) - hierarchyAdvectionAtLevel P 1 i (A.meanPhaseProduct u)
      EqOn f.val.val.val 0 U) ∧
    EqOn (A.remainder u P).val.val.val
      (∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)).val.val.val U := by
  let A := twistedHierarchyOperators hT G M κ
  let u := solvers.construct P completionSwitch parentResidual hR leading
  let Mtail : VP := ∑ ij ∈ hierarchyTailPairs P 0, A.labelAdv (u.B ij.1) (u.B ij.2)
  obtain ⟨hLevels, hSources, hTail⟩ := construct_support_and_tail_on_inactive hT hS G M κ hG hκ
    solvers hP completionSwitch parentResidual hR leading hLeadingV hLeadingp hSwitch hSolve hComplete
  refine ⟨?_, ?_, ?_⟩
  · intro i
    obtain ⟨hv, hc, hp⟩ := hLevels i
    exact ⟨eq_zero_through_activation hτ hv, eq_zero_through_activation hτ hc,
      eq_zero_through_activation hτ hp⟩
  · intro i hi
    exact eq_zero_through_activation hτ (hSources i hi)
  · have hz : A.remainder u P - Mtail ∈ inactiveSubmodule T k Vec3 τ S := by
      intro x hx
      exact sub_eq_zero.mpr (hTail hx)
    have h := eq_zero_through_activation hτ hz
    exact fun x hx => sub_eq_zero.mp (h hx)

end HierarchyTwistedProfile

end TorusEuler

import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchySourceBounds

/-! The mixed and label norms agree on phase-independent hierarchy profiles. -/

open ContinuousLinearMap Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {Time E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Pulling back a label field along the first projection just projects the
constant directions at each position in a derivative word. -/
private theorem phaseOperatorWord_fst_of_constant {ι : Type*} (d : ι → Vec3 × ℝ)
    {f : Vec3 → E} (hf : ContDiff ℝ ∞ f) (w : List ι) :
    phaseOperatorWord (fun i _ => d i) w (f ∘ Prod.fst) =
      phaseOperatorWord (fun i _ => (d i).1) w f ∘ Prod.fst := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (phaseOperatorWord (fun j _ => d j) w (f ∘ Prod.fst)) x (d i) =
      fderiv ℝ (phaseOperatorWord (fun j _ => (d j).1) w f) x.1 (d i).1
    rw [ih]
    have hW := (contDiff_phaseOperatorWord (D := fun j _ => (d j).1)
      (fun _ => contDiff_const) hf w).differentiable (by simp) x.1
    exact (ContinuousLinearMap.ext_iff.mp
      ((hW.hasFDerivAt.comp x (fst ℝ Vec3 ℝ).hasFDerivAt).fderiv)) (d i)

private theorem phaseOperatorWord_map_letters {I J U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] (D : J → U → U) (e : I → J)
    (w : List I) (f : U → E) :
    phaseOperatorWord D (w.map e) f = phaseOperatorWord (fun i => D (e i)) w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, phaseOperatorWord, ih]

private theorem phaseOperatorWord_eq_zero_of_zero_letter {I : Type*}
    (D : I → Vec3 → Vec3) (f : Vec3 → E) (i : I) (hi : D i = 0)
    {w : List I} (hw : i ∈ w) : phaseOperatorWord D w f = 0 := by
  induction w with
  | nil => simp at hw
  | cons j w ih =>
    rcases List.mem_cons.mp hw with h | h
    · subst j
      funext x
      simp [phaseOperatorWord, phaseDirectionalDerivative, hi]
    · funext x
      simp [phaseOperatorWord, phaseDirectionalDerivative, ih h]

private theorem list_eq_castSucc_map_of_not_mem_last {w : List (Fin 4)}
    (hw : Fin.last 3 ∉ w) : ∃ v : List (Fin 3), v.map Fin.castSucc = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons i w ih =>
    have hi : i ≠ Fin.last 3 := fun h => hw (List.mem_cons.mpr (Or.inl h.symm))
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    obtain ⟨u, hu⟩ := ih (fun h => hw (List.mem_cons.mpr (Or.inr h)))
    exact ⟨j :: u, by simp [hu]⟩

/-- In the uniform hierarchy seminorm, every word containing a phase
letter vanishes on a phase-independent profile. The other sorted mixed
words are exactly the sorted label words and carry the same suprema. -/
theorem hierarchyFiniteMixedWordNorm_phaseIndependent_eq_label
    (ell h : ℝ) (n : ℕ) {f : Time → Vec3 → E} (hf : ∀ t, ContDiff ℝ ∞ (f t)) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ell h) n (fun t x => f t x.1) =
      hierarchyFiniteWordNorm False (hierarchyLabelDirection ell) n f := by
  classical
  let d (i : Fin 4) := hierarchyMixedDirection ell h i ((0 : Vec3), (0 : ℝ))
  let e : List (Fin 3) ↪ List (Fin 4) :=
    ⟨List.map Fin.castSucc, fun _ _ h => (List.map_inj_right (fun _ _ hv => Fin.castSucc_injective 3 hv)).mp h⟩
  let A := hierarchyAdmissibleWords (Fin 3) n
  let B := hierarchyAdmissibleWords (Fin 4) n
  have hm (w : List (Fin 3)) : e w ∈ B ↔ w ∈ A := by
    simp only [B, A, mem_hierarchyAdmissibleWords]
    change ((w.map Fin.castSucc).length ≤ n ∧ (w.map Fin.castSucc).Pairwise (· ≤ ·)) ↔ _
    simp only [List.length_map, List.pairwise_map, Fin.castSucc_le_castSucc_iff]
  have hsub : A.map e ⊆ B := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
    exact (hm v).mpr hv
  have hzero (w : List (Fin 4)) (hw : Fin.last 3 ∈ w) :
      hierarchyJetValues False (hierarchyMixedDirection ell h) w (fun t x => f t x.1) = {0} := by
    have hz (t : Time) : phaseOperatorWord (hierarchyMixedDirection ell h) w (fun x => f t x.1) = 0 := by
      change phaseOperatorWord (fun i _ => d i) w (f t ∘ Prod.fst) = 0
      rw [phaseOperatorWord_fst_of_constant d (hf t)]
      rw [phaseOperatorWord_eq_zero_of_zero_letter (fun i _ => (d i).1) (f t) _ ?_ hw]
      · rfl
      · funext a
        unfold d hierarchyMixedDirection
        rw [Fin.lastCases_last]
        simp [phaseCoordinateDirection]
    ext y
    simp only [hierarchyJetValues, Set.mem_ofPred_eq, false_and, or_false, mem_singleton_iff, hz, Pi.zero_apply,
      norm_zero]
    constructor
    · rintro (hy | ⟨_, _, hy⟩)
      · exact hy
      · exact hy.symm
    · exact Or.inl
  have he (w : List (Fin 3)) :
      hierarchyJetValues False (hierarchyMixedDirection ell h) (e w) (fun t x => f t x.1) =
        hierarchyJetValues False (hierarchyLabelDirection ell) w f := by
    have hv (t : Time) : phaseOperatorWord (hierarchyMixedDirection ell h) (e w) (fun x => f t x.1) =
        phaseOperatorWord (hierarchyLabelDirection ell) w (f t) ∘ Prod.fst := by
      change phaseOperatorWord (fun i _ => d i) (w.map Fin.castSucc) (f t ∘ Prod.fst) = _
      rw [phaseOperatorWord_fst_of_constant d (hf t), phaseOperatorWord_map_letters]
      have hD : (fun (i : Fin 3) (_ : Vec3) => (d i.castSucc).1) =
          hierarchyLabelDirection ell := by
        funext i a
        simp [d, hierarchyMixedDirection, hierarchyLabelDirection, phaseCoordinateDirection]
      rw [hD]
    ext y
    simp only [hierarchyJetValues, Set.mem_ofPred_eq, false_and, or_false, hv, Function.comp_apply]
    constructor
    · rintro (rfl | ⟨t, x, hx⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨t, x.1, hx⟩
    · rintro (rfl | ⟨t, a, ha⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨t, (a, 0), ha⟩
  let J (w : List (Fin 4)) :=
    sSup (hierarchyJetValues False (hierarchyMixedDirection ell h) w (fun t x => f t x.1))
  change (∑ w ∈ B, J w) = _
  calc
    _ = ∑ w ∈ A.map e, J w := by
      symm
      refine Finset.sum_subset hsub (fun w hw hwo => ?_)
      have hl : Fin.last 3 ∈ w := by
        by_contra hnl
        obtain ⟨v, hv⟩ := list_eq_castSucc_map_of_not_mem_last hnl
        have hv' : e v = w := hv
        exact hwo (Finset.mem_map.mpr ⟨v, (hm v).mp (hv' ▸ hw), hv'⟩)
      simp [J, hzero w hl]
    _ = ∑ w ∈ A, sSup (hierarchyJetValues False (hierarchyLabelDirection ell) w f) := by
      rw [Finset.sum_map]
      exact Finset.sum_congr rfl (fun w _ => congrArg sSup (he w))
    _ = _ := rfl

namespace HierarchyTwistedProfile

/-- Exact equality between the mixed unweighted seminorm of a phase-independent
profile and the label norm used in the quantitative mean solve. -/
theorem unweightedSeminorm_false_eq_labelWordNorm_of_phaseIndependent
    {T : ℝ} {k : Vec3} (hT : 0 < T) (ell h : ℝ) (n : ℕ)
    (f : HierarchyTwistedProfile T k E)
    (hPhase : HierarchyPeriodicProfile.PhaseIndependent f.val.val) :
    unweightedSeminorm False ell h n hT f =
      hierarchyFiniteWordNorm False (hierarchyLabelDirection ell) n
        (fun (t : Icc (0 : ℝ) T) a => f.val.val.val (t,a,0)) := by
  let F (t : Icc (0 : ℝ) T) (a : Vec3) := f.val.val.val (t,a,0)
  have hF (t : Icc (0 : ℝ) T) : ContDiff ℝ ∞ (F t) :=
    (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val t.property).comp
      (contDiff_id.prodMk contDiff_const)
  change hierarchyFiniteWordNorm False (hierarchyMixedDirection ell h) n
    (weightedSlices (Icc (0 : ℝ) T) (fun _ => 1) f) = _
  have he : weightedSlices (Icc (0 : ℝ) T) (fun _ => 1) f = fun t x => F t x.1 := by
    funext t x
    change (1 : ℝ) • f.val.val.val (t,x) = F t x.1
    rw [one_smul]
    exact hPhase (t, x) ⟨t.property, mem_univ _⟩ 0 |>.symm
  rw [he]
  exact hierarchyFiniteMixedWordNorm_phaseIndependent_eq_label ell h n hF

/-- Phase-averaged inputs and outputs have exactly the quantitative solver's
label norm, so the same mean estimate applies to the mixed norm recurrence. -/
theorem unweightedSeminorm_false_eq_labelWordNorm_of_average
    {T : ℝ} {k : Vec3} (hT : 0 < T) (ell h : ℝ) (n : ℕ)
    {G M : HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)}
    {κ : HierarchyTwistedProfile T k Vec3} (f : HierarchyTwistedProfile T k Vec3)
    (hf : (twistedHierarchyOperators hT G M κ).average f = f) :
    unweightedSeminorm False ell h n hT f =
      hierarchyFiniteWordNorm False (hierarchyLabelDirection ell) n
        (fun (t : Icc (0 : ℝ) T) a => f.val.val.val (t,a,0)) := by
  have hAvg : HierarchyPeriodicProfile.profilePhaseAverage hT f.val = f.val :=
    congrArg Subtype.val hf
  exact unweightedSeminorm_false_eq_labelWordNorm_of_phaseIndependent hT ell h n f
    (HierarchyPeriodicProfile.phaseIndependent_of_profilePhaseAverage_eq_self hT f.val hAvg)

end HierarchyTwistedProfile

end

end TorusEuler

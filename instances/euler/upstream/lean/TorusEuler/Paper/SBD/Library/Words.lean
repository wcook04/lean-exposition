import TorusEuler.HierarchyPhaseIndependentNorm

/-! # Derivative words of phase-independent fields (package SBD)

Public copies, under new names in `TorusEuler.Paper.Lib.SBD`, of four private
helpers of `TorusEuler/HierarchyPhaseIndependentNorm.lean`:

- `word_fst_of_constant` is `phaseOperatorWord_fst_of_constant` (line 18);
- `word_map_letters` is `phaseOperatorWord_map_letters` (line 34);
- `word_eq_zero_of_zero_letter` is `phaseOperatorWord_eq_zero_of_zero_letter` (line 42);
- `list_eq_castSucc_map_of_not_mem_last` is the lemma of the same name (line 55).

They are calculus glue (a field of the label pulled back along the projection
`(a, s) ↦ a`, and words with a vanishing letter), not the content of a numbered
result. They are used by the vocabulary lemmas of `TorusEuler/Paper/SBD/Vocabulary.lean`
that identify the norm (D.1) of a phase-independent field. -/

open scoped ContDiff

namespace TorusEuler.Paper.Lib.SBD

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A label field pulled back along the first projection: a word of constant
directions acts through the label components of the directions. -/
theorem word_fst_of_constant {ι : Type*} (d : ι → Vec3 × ℝ)
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
      ((hW.hasFDerivAt.comp x (ContinuousLinearMap.fst ℝ Vec3 ℝ).hasFDerivAt).fderiv)) (d i)

/-- Renaming the letters of a word. -/
theorem word_map_letters {I J U : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] (D : J → U → U) (e : I → J)
    (w : List I) (f : U → E) :
    phaseOperatorWord D (w.map e) f = phaseOperatorWord (fun i => D (e i)) w f := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [List.map_cons, phaseOperatorWord, ih]

/-- A word containing a letter with zero direction vanishes. -/
theorem word_eq_zero_of_zero_letter {I : Type*}
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

/-- A word in the four mixed letters without the phase letter is a word in the
three label letters. -/
theorem list_eq_castSucc_map_of_not_mem_last {w : List (Fin 4)}
    (hw : Fin.last 3 ∉ w) : ∃ v : List (Fin 3), v.map Fin.castSucc = w := by
  induction w with
  | nil => exact ⟨[], rfl⟩
  | cons i w ih =>
    have hi : i ≠ Fin.last 3 := fun h => hw (List.mem_cons.mpr (Or.inl h.symm))
    obtain ⟨j, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    obtain ⟨u, hu⟩ := ih (fun h => hw (List.mem_cons.mpr (Or.inr h)))
    exact ⟨j :: u, by simp [hu]⟩

end TorusEuler.Paper.Lib.SBD

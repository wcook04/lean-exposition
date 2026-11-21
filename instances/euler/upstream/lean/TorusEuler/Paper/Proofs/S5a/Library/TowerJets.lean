import TorusEuler.Paper.Proofs.S5a.Library.TowerDer
import TorusEuler.Paper.Proofs.S5a.Library.Jets

/-!
# S5a library: symmetric derivative towers of a smooth periodic field

`SymTower T f`: the words of label derivatives of a jointly smooth periodic field `f` on the slab, as
curves in `C^{0,1/2}`, indexed by *all* words, exactly invariant under permutations of the word (jets of
the sorted word), smooth in time, forming a derivative tower (`IsDer`), with the lifts
`∂^w f(t, ·)`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a.Tower

noncomputable section

/-- The sorted word. -/
def srt (w : Wd) : Wd := w.mergeSort (· ≤ ·)

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `srt_perm`. -/
theorem srt_perm (w : Wd) : (srt w).Perm w := List.mergeSort_perm _ _

/-- Auxiliary declaration of the tower argument for (5.14) (`sections/06d_mean_estimates.tex:46-58`): `srt_eq_of_perm`. -/
theorem srt_eq_of_perm {p q : Wd} (h : p.Perm q) : srt p = srt q :=
  List.Perm.eq_of_pairwise' (List.pairwise_mergeSort' _ _) (List.pairwise_mergeSort' _ _)
    ((srt_perm p).trans (h.trans (srt_perm q).symm))

/-- Symmetric derivative towers of a smooth periodic field. -/
structure SymTower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ)
    (f : ℝ × Vec3 → E) where
  Y : Wd → ℝ → HalfHolder (UnitAddTorus (Fin 3)) E
  sym : Sym Y
  smooth : ∀ w, ContDiffOn ℝ ∞ (Y w) (Icc 0 T)
  der : IsDer T Y
  lift : ∀ w, ∀ t ∈ Icc 0 T, ∀ x,
    HalfHolder.eval (toUnitTorus x) (Y w t) = spatialDerivativeWord w (fun y => f (t, y)) x

/-- A jointly smooth periodic field on the slab has a symmetric derivative tower (jets of the sorted word, `sections/06d_mean_estimates.tex:46-48`: "label derivatives preserve the constraints"). -/
theorem exists_symTower {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {T : ℝ} (hT : 0 < T) (f : ℝ × Vec3 → E) (hf : ContDiffOn ℝ ∞ f (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (fun x => f (t, x))) : Nonempty (SymTower T f) := by
  obtain ⟨j⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection f hf hper
  have hslice (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (fun y => f (t, y)) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hlift (w : Wd) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (j.curve w t) = spatialDerivativeWord w (fun y => f (t, y)) x :=
    (j.eval_lift w t ht x).trans (endpointSlabSpatialWord_eq_spatialDerivativeWord hT hf w t ht x)
  have hperm (p q : Wd) (h : p.Perm q) (t : ℝ) (ht : t ∈ Icc 0 T) : j.curve p t = j.curve q t := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hlift p t ht x, hlift q t ht x]
    exact congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection (hslice t ht) h) x
  refine ⟨⟨fun w => j.curve (srt w), ?_, fun w => j.smooth _, ?_, ?_⟩⟩
  · intro p q h
    simp only [srt_eq_of_perm h]
  · intro i w t ht
    have h := j.spatialDerivative i (srt w) t ht
    have e : j.curve (i :: srt w) t = j.curve (srt (i :: w)) t :=
      hperm _ _ (((srt_perm w).cons i).trans (srt_perm (i :: w)).symm) t ht
    rw [e] at h
    exact h
  · intro w t ht x
    rw [hlift (srt w) t ht x]
    exact congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection (hslice t ht)
      (srt_perm w)) x

end

end TorusEuler.Paper.Lib.S5a.Tower

import TorusEuler.HierarchyActualNorms

/-! Finite word samples of smooth twisted profiles on the active time slab. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

/-- Phase and label periodicity bound all fixed-order jet samples of a smooth
profile defined on the active slab, including a singleton launch slice. -/
theorem paperHierarchyActiveWord_bddAbove {t₀ T ℓ h : ℝ} {k : Vec3}
    {f : ℝ → Vec3 × ℝ → Vec3} (htT : t₀ < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc t₀ T ×ˢ univ))
    (hphase : ∀ t ∈ Icc t₀ T, ∀ (a : Vec3) (s : ℝ), f t (a, s + 1) = f t (a, s))
    (htwist : ∀ t ∈ Icc t₀ T, ∀ (a : Vec3) (s : ℝ) (j : Fin 3 → ℤ),
      f t (a + latticeVector j, s + ⟪k, latticeVector j⟫_ℝ) = f t (a, s))
    {A : Set ℝ} (hA : A ⊆ Icc t₀ T) (τ : ℝ → ℝ) {B : ℝ}
    (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) (w : List (Fin 4)) :
    BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
      (fun (t : A) x => τ t • f t x)) := by
  classical
  let S := hierarchyProfileSlab (T - t₀)
  let shift (x : HierarchyProfilePoint) : HierarchyProfilePoint := (t₀ + x.1, x.2)
  have hShift : MapsTo shift S (Icc t₀ T ×ˢ univ) := by
    rintro ⟨u, x⟩ ⟨hu, _⟩
    exact ⟨⟨by change t₀ ≤ t₀ + u; linarith [hu.1],
      by change t₀ + u ≤ T; linarith [hu.2]⟩, mem_univ x⟩
  let F (x : HierarchyProfilePoint) := if x ∈ S then f (t₀ + x.1) x.2 else 0
  have hFc : ContDiffOn ℝ ∞ F S := by
    have hsc : ContDiff ℝ ∞ shift :=
      (contDiff_const.add contDiff_fst).prodMk contDiff_snd
    refine (hf.comp hsc.contDiffOn hShift).congr ?_
    intro x hx
    exact ite_eq_left hx
  have hFp : Function.Periodic F hierarchyPhasePeriod := by
    rintro ⟨u, a, s⟩
    change F ((u, a, s) + hierarchyPhasePeriod) = F (u, a, s)
    rw [add_hierarchyPhasePeriod]
    by_cases hu : u ∈ Icc 0 (T - t₀)
    · have ht := (hShift (show (u, a, s) ∈ S from ⟨hu, mem_univ _⟩)).1
      rw [show F (u, a, s + 1) = f (t₀ + u) (a, s + 1) from ite_eq_left ⟨hu, mem_univ _⟩,
        show F (u, a, s) = f (t₀ + u) (a, s) from ite_eq_left ⟨hu, mem_univ _⟩]
      exact hphase (t₀ + u) ht a s
    · have hn : ¬ (0 ≤ u ∧ u ≤ T - t₀) := hu
      simp [F, S, hierarchyProfileSlab, hn]
  have hFt (j : Fin 3 → ℤ) : Function.Periodic F (hierarchyLatticeShift k j) := by
    rintro ⟨u, a, s⟩
    change F ((u, a, s) + hierarchyLatticeShift k j) = F (u, a, s)
    rw [add_hierarchyLatticeShift]
    by_cases hu : u ∈ Icc 0 (T - t₀)
    · have ht := (hShift (show (u, a, s) ∈ S from ⟨hu, mem_univ _⟩)).1
      rw [show F (u, a + latticeVector j, s + ⟪k, latticeVector j⟫_ℝ) =
        f (t₀ + u) (a + latticeVector j, s + ⟪k, latticeVector j⟫_ℝ) from ite_eq_left ⟨hu, mem_univ _⟩,
        show F (u, a, s) = f (t₀ + u) (a, s) from ite_eq_left ⟨hu, mem_univ _⟩]
      exact htwist (t₀ + u) ht a s j
    · have hn : ¬ (0 ≤ u ∧ u ≤ T - t₀) := hu
      simp [F, S, hierarchyProfileSlab, hn]
  let g := HierarchyTwistedProfile.ofSmooth F hFc hFp hFt
  let A' := (fun u : ℝ => t₀ + u) ⁻¹' A
  have hA' : A' ⊆ Icc 0 (T - t₀) := by
    intro u hu
    have ht : t₀ + u ∈ Icc t₀ T := hA hu
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hBound := hierarchyTwistedMixedWord_bddAbove_weighted (sub_pos.mpr htT) ℓ h False w g
    hA' (fun u => τ (t₀ + u)) (fun u hu => hτ (t₀ + u) hu)
  have hTime (t : A) : t₀ + ((t : ℝ) - t₀) = t := by ring
  let idx (t : A) : A' := ⟨(t : ℝ) - t₀, by
    change t₀ + ((t : ℝ) - t₀) ∈ A
    rw [hTime t]
    exact t.property⟩
  have hSample (t : A) :
      (fun x => τ (t₀ + (idx t : ℝ)) • g.val.val.val ((idx t : ℝ), x)) =
        fun x => τ t • f t x := by
    funext x
    have hIdx : ((idx t : A') : ℝ) ∈ Icc 0 (T - t₀) := hA' (idx t).property
    rw [show g.val.val.val ((idx t : ℝ), x) = F ((idx t : ℝ), x) from
      HierarchyTwistedProfile.ofSmooth_eval hFc hFp hFt ⟨hIdx, mem_univ x⟩]
    rw [show F ((idx t : ℝ), x) = f (t₀ + (idx t : ℝ)) x from ite_eq_left ⟨hIdx, mem_univ x⟩]
    simp only [idx, hTime t]
  refine hBound.mono ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hFalse, _⟩)
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨idx t, x,
      congrArg (fun q => ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w q x‖) (hSample t)⟩)
  · exact hFalse.elim

end TorusEuler

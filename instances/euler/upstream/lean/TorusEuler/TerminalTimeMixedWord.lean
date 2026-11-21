import TorusEuler.TerminalTimeJetNorms

/-! Time derivatives of the actual mixed label and phase words. -/

open ContinuousLinearMap Set

namespace TorusEuler

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace HierarchyTwistedProfile

private theorem hierarchyTwistedMixedWord_cons_eq (hT : 0 < T) (ℓ h : ℝ) (i : Fin 4)
    (w : List (Fin 4)) (f : HierarchyTwistedProfile T k E) :
    hierarchyTwistedMixedWord hT ℓ h (i :: w) f =
      directionDerivative hT (0, hierarchyMixedDirection ℓ h i 0)
        (hierarchyTwistedMixedWord hT ℓ h w f) := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  rw [directionDerivative_apply hT _ _ hx]
  simp only [hierarchyTwistedMixedWord, LinearMap.comp_apply, map_val,
    HierarchyPeriodicProfile.map_val, HierarchySmoothProfile.map_apply _ _ hx,
    hierarchyTwistedSliceDerivative, derivative_val, HierarchyPeriodicProfile.derivative_val,
    HierarchySmoothProfile.derivative_apply _ _ hx]
  rfl

/-- Applying a fixed spatial word commutes with each time jet on the closed slab. -/
theorem timeJet_mixedWord (hT : 0 < T) (j : ℕ) (ℓ h : ℝ) (w : List (Fin 4))
    (f : HierarchyTwistedProfile T k E) :
    timeJet hT j (hierarchyTwistedMixedWord hT ℓ h w f) =
      hierarchyTwistedMixedWord hT ℓ h w (timeJet hT j f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    rw [hierarchyTwistedMixedWord_cons_eq, hierarchyTwistedMixedWord_cons_eq,
      timeJet_directionDerivative, ih]

/-- The derivatives in the time-jet norm and in each spatial word are
the ordinary derivatives with the other coordinates fixed. -/
theorem iteratedDerivWithin_mixedWord (hT : 0 < T) (j : ℕ) (ℓ h : ℝ)
    (w : List (Fin 4)) (f : HierarchyTwistedProfile T k E)
    {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3 × ℝ) :
    iteratedDerivWithin j
        (fun u => phaseOperatorWord (hierarchyMixedDirection ℓ h) w
          (fun z => f.val.val.val (u, z)) x) (Icc 0 T) t =
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w
        (fun z => (timeJet hT j f).val.val.val (t, z)) x := by
  rw [← hierarchyTwistedMixedWord_apply hT ℓ h w _ ht x, ← timeJet_mixedWord,
    timeJet_apply hT j _ ht x]
  exact iteratedDerivWithin_congr
    (fun _ hu => (hierarchyTwistedMixedWord_apply hT ℓ h w f hu x).symm) ht

end HierarchyTwistedProfile

end

end TorusEuler

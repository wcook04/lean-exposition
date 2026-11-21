import TorusEuler.Paper.SBD.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Norms

/-!
# Norm facts for the proof of Proposition 5.2

Generic facts on the norms of Appendix D used to pass between phase-independent fields and their
lifts `(t, a, s) ↦ c(t, a)`: finiteness of a lift gives finiteness of the coefficient
(converse of `AppendixD.CoefficientNormFinite.fieldNormFinite`), and nonnegativity of the norms.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a

open AppendixD

noncomputable section

section Generic

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Converse of `CoefficientNormFinite.fieldNormFinite`: if the lift `(t, a, s) ↦ c(t, a)` has
finite norm (D.1) for some `ℓ > 0` and `h`, the coefficient `c` has a finite norm. -/
theorem coefficientNormFinite_of_lift {ℓ h : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {c : I → Vec3 → X}
    (hf : FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => c t x.1)) :
    CoefficientNormFinite n c := by
  classical
  have hc : ∀ t, ContDiff ℝ ∞ (c t) := fun t =>
    (hf.1 t).comp (contDiff_id.prodMk (contDiff_const (c := (0 : ℝ))))
  refine ⟨hc, fun w hw => ?_⟩
  let d (i : Fin 4) := hierarchyMixedDirection ℓ h i ((0 : Vec3), (0 : ℝ))
  have hlift (u : List (Fin 4)) (t : I) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) u (fun x : Vec3 × ℝ => c t x.1) =
        phaseOperatorWord (fun i (_ : Vec3) => (d i).1) u (c t) ∘ Prod.fst :=
    Lib.SBD.word_fst_of_constant d (hc t) u
  have hw4 : w.map Fin.castSucc ∈ hierarchyAdmissibleWords (Fin 4) n := by
    obtain ⟨hlen, hs⟩ := mem_hierarchyAdmissibleWords.mp hw
    refine mem_hierarchyAdmissibleWords.mpr ⟨by simpa only [List.length_map] using hlen, ?_⟩
    simpa only [List.pairwise_map, Fin.castSucc_le_castSucc_iff] using hs
  have hD : (fun (i : Fin 3) (_ : Vec3) => (d i.castSucc).1) = hierarchyLabelDirection ℓ := by
    funext i a
    simp [d, hierarchyMixedDirection, hierarchyLabelDirection, phaseCoordinateDirection]
  have hword (t : I) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) (w.map Fin.castSucc)
          (fun x : Vec3 × ℝ => c t x.1) =
        phaseOperatorWord (hierarchyLabelDirection ℓ) w (c t) ∘ Prod.fst := by
    rw [hlift, Lib.SBD.word_map_letters, hD]
  have hsub : hierarchyJetValues False (hierarchyLabelDirection ℓ) w c ⊆
      hierarchyJetValues False (hierarchyMixedDirection ℓ h) (w.map Fin.castSucc)
        (fun t (x : Vec3 × ℝ) => c t x.1) := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨t, (x, 0), by simp only [hword, Function.comp_apply]⟩)
    · exact hH.elim
  obtain ⟨M, hM⟩ := (hf.2 _ hw4).mono hsub
  rw [jetValues_labelDirection False ℓ w hc] at hM
  have hpos : 0 < ‖ℓ ^ w.length‖ := by
    rw [Real.norm_of_nonneg (pow_nonneg hℓ.le _)]; positivity
  refine ⟨M / ‖ℓ ^ w.length‖, fun r hr => ?_⟩
  rw [le_div_iff₀ hpos, mul_comm]
  exact hM (Set.smul_mem_smul_set hr)

end Generic

section Nonneg

variable {ι T U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The values in a jet-value set are nonnegative. -/
theorem jetValues_nonneg (holder : Prop) (D : ι → U → U) (w : List ι) (f : T → U → E) :
    ∀ r ∈ hierarchyJetValues holder D w f, 0 ≤ r := by
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨_, t, x, y, rfl⟩)
  · exact le_rfl
  · exact norm_nonneg _
  · exact div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)

end Nonneg

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Nonnegativity of the Hölder field norm. -/
theorem holderFieldNorm_nonneg (ℓ : ℝ) (n : ℕ) (c : I → Vec3 → X) : 0 ≤ holderFieldNorm ℓ n c :=
  Finset.sum_nonneg fun _ _ => Real.sSup_nonneg (jetValues_nonneg _ _ _ _)

/-- Nonnegativity of the coefficient norm for `ℓ ≥ 0`. -/
theorem coefficientNorm_nonneg {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (n : ℕ) (c : I → Vec3 → X) :
    0 ≤ coefficientNorm ℓ n c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (pow_nonneg hℓ _)
    (Finset.sum_nonneg fun _ _ => Real.sSup_nonneg (jetValues_nonneg _ _ _ _))

end

end TorusEuler.Paper.Lib.S5a

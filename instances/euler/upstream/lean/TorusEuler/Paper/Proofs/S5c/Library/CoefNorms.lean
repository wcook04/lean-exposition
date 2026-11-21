import TorusEuler.Paper.SBD.Vocabulary
import TorusEuler.PhysicalHierarchyProfileBounds
import TorusEuler.HierarchyActualNorms
import TorusEuler.ParentResidualEstimates

/-!
# Glue for (5.52) of Lemma 5.9: sums of fields and phase-independent coefficients

Copies of glue of package S5b (`Proofs/S5b/Library/Fields.lean`, `Words57.lean`, written for
the proof of Lemma 5.7), in the language of Lemma D.1 (fields `f : I → Vec3 × ℝ → E`):
derivative words are additive (`word_add`, `word_zero`); the norms (D.1) are nonnegative and
subadditive and finite norms are closed under finite sums (`fieldNorm_nonneg`,
`fieldNormFinite_add`, `fieldNorm_add_le`, `fieldNormFinite_sum`, `fieldNorm_sum_le`,
`weighted_add`, `weighted_sum`); a weighted label word of a phase-independent field is at most
`r^{|w|}` times its Fréchet jet (`norm_labelWord_le`); and the norm of a phase-independent
coefficient `L(G(t,a))` is bounded by its scaled Fréchet jets (`coef_bounds`, generalized from a
scalar functional `L` to a continuous linear map `L` with values in any normed space). None of
these is the content of a numbered result: they are the triangle inequality and the definition of
the norms.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

open AppendixD

noncomputable section

section Words

variable {ι U E : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Derivative words are additive on smooth functions. -/
theorem word_add {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i)) {f g : U → E}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List ι) :
    phaseOperatorWord D w (f + g) = phaseOperatorWord D w f + phaseOperatorWord D w g := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (phaseOperatorWord D w (f + g)) x (D i x) =
      fderiv ℝ (phaseOperatorWord D w f) x (D i x) + fderiv ℝ (phaseOperatorWord D w g) x (D i x)
    rw [ih, fderiv_add ((contDiff_phaseOperatorWord hD hf w).differentiable (by simp) x)
      ((contDiff_phaseOperatorWord hD hg w).differentiable (by simp) x)]
    rfl

/-- Derivative words vanish on the zero function. -/
theorem word_zero (D : ι → U → U) (w : List ι) : phaseOperatorWord D w (0 : U → E) = 0 := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    funext x
    change fderiv ℝ (phaseOperatorWord D w (0 : U → E)) x (D i x) = 0
    rw [ih]
    simp

end Words

section FieldNorms

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {ℓ h : ℝ} {n : ℕ}

/-- The weighted directions of (D.1) are constant, hence smooth. -/
theorem mixedDirection_smooth (ℓ h : ℝ) (i : Fin 4) : ContDiff ℝ ∞ (hierarchyMixedDirection ℓ h i) :=
  contDiff_const

/-- A finite norm (D.1) is nonnegative. -/
theorem fieldNorm_nonneg {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h n f) :
    0 ≤ fieldNorm ℓ h n f :=
  Finset.sum_nonneg fun w hw => le_csSup (hf.2 w hw) (Or.inl rfl)

/-- The zero field has finite norms. -/
theorem fieldNormFinite_zero : FieldNormFinite ℓ h n (0 : I → Vec3 × ℝ → E) := by
  refine ⟨fun _ => contDiff_const, fun w _ => ⟨0, ?_⟩⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
  · exact le_rfl
  · change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (0 : Vec3 × ℝ → E) x‖ ≤ 0
    rw [word_zero]
    simp
  · exact hH.elim

/-- The zero field has norm zero. -/
theorem fieldNorm_zero : fieldNorm ℓ h n (0 : I → Vec3 × ℝ → E) = 0 := by
  refine le_antisymm ?_ (fieldNorm_nonneg fieldNormFinite_zero)
  refine (hierarchyFiniteWordNorm_sup_le le_rfl fun w _ t x => ?_).trans_eq (mul_zero _)
  change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (0 : Vec3 × ℝ → E) x‖ ≤ 0
  rw [word_zero]
  simp

/-- Finite norms (D.1) are closed under addition. -/
theorem fieldNormFinite_add {f g : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h n f)
    (hg : FieldNormFinite ℓ h n g) : FieldNormFinite ℓ h n (f + g) := by
  refine ⟨fun t => (hf.1 t).add (hg.1 t), fun w hw => ?_⟩
  obtain ⟨A, hA⟩ := hf.2 w hw
  obtain ⟨B, hB⟩ := hg.2 w hw
  refine ⟨A + B, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
  · exact add_nonneg (hA (Or.inl rfl)) (hB (Or.inl rfl))
  · change ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (f t + g t) x‖ ≤ A + B
    rw [word_add (mixedDirection_smooth ℓ h) (hf.1 t) (hg.1 t)]
    exact (norm_add_le _ _).trans (add_le_add (hA (Or.inr (Or.inl ⟨t, x, rfl⟩)))
      (hB (Or.inr (Or.inl ⟨t, x, rfl⟩))))
  · exact hH.elim

/-- The norm (D.1) is subadditive on fields with finite norms. -/
theorem fieldNorm_add_le {f g : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h n f)
    (hg : FieldNormFinite ℓ h n g) : fieldNorm ℓ h n (f + g) ≤ fieldNorm ℓ h n f + fieldNorm ℓ h n g := by
  unfold fieldNorm hierarchyFiniteWordNorm
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun w hw => actualJetValues_add_le False (mixedDirection_smooth ℓ h) w
    hf.1 hg.1 (hf.2 w hw) (hg.2 w hw)

/-- Finite norms (D.1) are closed under finite sums. -/
theorem fieldNormFinite_sum {ι : Type*} (s : Finset ι) {f : ι → I → Vec3 × ℝ → E}
    (hf : ∀ i ∈ s, FieldNormFinite ℓ h n (f i)) : FieldNormFinite ℓ h n (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using fieldNormFinite_zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact fieldNormFinite_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

/-- The norm (D.1) of a finite sum of fields with finite norms is at most the sum of
the norms. -/
theorem fieldNorm_sum_le {ι : Type*} (s : Finset ι) {f : ι → I → Vec3 × ℝ → E}
    (hf : ∀ i ∈ s, FieldNormFinite ℓ h n (f i)) :
    fieldNorm ℓ h n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, fieldNorm ℓ h n (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, fieldNorm_zero, le_refl]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : ∀ j ∈ s, FieldNormFinite ℓ h n (f j) := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    exact (fieldNorm_add_le (hf i (Finset.mem_insert_self i s)) (fieldNormFinite_sum s hs)).trans
      (add_le_add le_rfl (ih hs))

/-- The time weight distributes over sums of fields. -/
theorem weighted_add (γ : I → ℝ) (f g : I → Vec3 × ℝ → E) :
    weighted γ (f + g) = weighted γ f + weighted γ g := by
  funext t x
  simp only [weighted, Pi.add_apply, smul_add]

/-- The time weight distributes over finite sums of fields. -/
theorem weighted_sum {ι : Type*} (γ : I → ℝ) (s : Finset ι) (f : ι → I → Vec3 × ℝ → E) :
    weighted γ (∑ i ∈ s, f i) = ∑ i ∈ s, weighted γ (f i) := by
  funext t x
  simp only [weighted, Finset.sum_apply, Finset.smul_sum]

end FieldNorms

section Coefficients

variable {I : Type*}

/-- A weighted label word of a smooth phase-independent field is at most `r^{|w|}` times
the Fréchet jet of the same order. -/
theorem norm_labelWord_le {G' : Type*} [NormedAddCommGroup G'] [NormedSpace ℝ G']
    {r : ℝ} (hr : 0 ≤ r) {g : Vec3 → G'} (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) (x : Vec3) :
    ‖phaseOperatorWord (hierarchyLabelDirection r) w g x‖ ≤
      r ^ w.length * ‖iteratedFDeriv ℝ w.length g x‖ := by
  rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul r hg w x, norm_smul,
    Real.norm_of_nonneg (pow_nonneg hr _), spatialDerivativeWord_eq_iteratedFDeriv hg]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr _)
  have h1 (i : Fin w.length) : ‖coordinateDirection (w.get i)‖ = 1 := by
    simp [coordinateDirection]
  simpa only [h1, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ w.length g x).le_opNorm (fun i => coordinateDirection (w.get i))

/-- **Norms of a phase-independent coefficient** (copy of the S5b glue `coef_bounds`, with a
vector-valued `L`). For a smooth `G` with uniformly bounded jets and `ℓ^m |∇^m G(t,a)| ≤ B` for
`m ≤ n`, the field `(t,a,s) ↦ L(G(t,a))` has a finite norm (D.1) of order `n`, at most
`#W_n ‖L‖ B`. -/
theorem coef_bounds {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} (L : (Vec3 →L[ℝ] Vec3) →L[ℝ] E')
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t, ContDiff ℝ ∞ (G t))
    (hunif : ∀ m, ∃ b, ∀ t a, ‖iteratedFDeriv ℝ m (G t) a‖ ≤ b)
    (hjet : ∀ m ≤ n, ∀ t a, ℓ ^ m * ‖iteratedFDeriv ℝ m (G t) a‖ ≤ B) :
    FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => L (G t x.1)) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => L (G t x.1)) ≤
        (hierarchyAdmissibleWords (Fin 3) n).card * (‖L‖ * B) := by
  let c : I → Vec3 → E' := fun t a => L (G t a)
  have hc : ∀ t, ContDiff ℝ ∞ (c t) := fun t => L.contDiff.comp (hG t)
  have hcD (m : ℕ) (t : I) (a : Vec3) :
      ‖iteratedFDeriv ℝ m (c t) a‖ ≤ ‖L‖ * ‖iteratedFDeriv ℝ m (G t) a‖ :=
    L.norm_iteratedFDeriv_comp_left (hG t).contDiffAt (by exact_mod_cast le_top)
  have hcoef : CoefficientNormFinite n c := by
    refine ⟨hc, fun w _ => ?_⟩
    obtain ⟨b, hb⟩ := hunif w.length
    refine ⟨‖L‖ * max b 0, ?_⟩
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact mul_nonneg L.opNorm_nonneg (le_max_right _ _)
    · refine (norm_labelWord_le zero_le_one (hc t) w x).trans ?_
      rw [one_pow, one_mul]
      exact (hcD _ t x).trans (mul_le_mul_of_nonneg_left ((hb t x).trans (le_max_left _ _))
        L.opNorm_nonneg)
    · exact hH.elim
  refine ⟨CoefficientNormFinite.fieldNormFinite hcoef ℓ h, ?_⟩
  change fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => c t x.1) ≤ _
  rw [fieldNorm_phaseIndependent hℓ h n hc, coefficientNorm_eq_labelWordNorm hℓ n hc]
  refine hierarchyFiniteWordNorm_sup_le (mul_nonneg L.opNorm_nonneg hB) fun w hw t x => ?_
  have hlen := (mem_hierarchyAdmissibleWords.mp hw).1
  refine (norm_labelWord_le hℓ (hc t) w x).trans ?_
  calc ℓ ^ w.length * ‖iteratedFDeriv ℝ w.length (c t) x‖ ≤
        ℓ ^ w.length * (‖L‖ * ‖iteratedFDeriv ℝ w.length (G t) x‖) :=
        mul_le_mul_of_nonneg_left (hcD _ t x) (pow_nonneg hℓ _)
    _ = ‖L‖ * (ℓ ^ w.length * ‖iteratedFDeriv ℝ w.length (G t) x‖) := by ring
    _ ≤ ‖L‖ * B := mul_le_mul_of_nonneg_left (hjet _ hlen t x) L.opNorm_nonneg

end Coefficients

end

end TorusEuler.Paper.Lib.S5c

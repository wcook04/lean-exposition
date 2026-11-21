import TorusEuler.Paper.SBD.Vocabulary
import TorusEuler.PhysicalHierarchyProfileBounds
import TorusEuler.HierarchyActualNorms
import TorusEuler.ParentResidualEstimates

/-!
# Glue for Lemma 5.7: fields, the operators `d̃_i`, and the graph chain rule

Generic glue for the proof of Lemma 5.7 (`sections/08_exact_wave.tex:51-74`), in the
language of the statement of Lemma D.1 (fields `f : I → Vec3 × ℝ → E` with the norms
`AppendixD.fieldNorm`, `AppendixD.weightedFieldNorm`):

* the norms (D.1) are subadditive on fields with finite norms, and finite norms are
  closed under finite sums;
* the operator `d̃_i = ∑_j G_{ji} (∂_{a_j} + k_j ∂_s)` of `08_exact_wave.tex:56`
  (`tildeWord … [i]`), for a coframe `G = (D_aX)⁻¹`, is a sum of four products of a
  phase-independent coefficient with a label or phase derivative (`tildeWord_cons_eq`),
  which is the form in which (D.3) and (D.4) of Lemma D.1 apply;
* the spatial chain rule (3.1): the Eulerian derivative words of the graph of a field
  are the graphs of the `d̃`-words (`spatialDerivativeWord_graph`);
* an abstract iteration of a one-step estimate over all derivative words
  (`iterate_words`);
* the operator norm of a multilinear map is at most the sum of its values on the
  coordinate words (`norm_le_sum_coordinate`, adapted from the private library lemma
  `norm_multilinear_le_of_coordinate_bounds` of `TorusEuler/PhaseJetBounds.lean:322`).

None of these is the content of a numbered result: they are algebraic identities,
the triangle inequality and the chain rule.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD

noncomputable section

/-! ## Derivative words are linear -/

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

/-! ## The norms (D.1) on sums of fields -/

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

/-- The time weight of the zero field is zero. -/
theorem weighted_zero (γ : I → ℝ) : weighted γ (0 : I → Vec3 × ℝ → E) = 0 := by
  funext t x
  simp only [weighted, Pi.zero_apply, smul_zero]

/-- The supremum of a field at a fixed time is at most the weight times its weighted
norm of order zero: `sup |f(t)| ≤ γ(t) ‖f‖_{[0],γ}` (`08_exact_wave.tex:66-67`). -/
theorem norm_le_weight_mul_weightedFieldNorm {γ : I → ℝ} (hγ : ∀ t, 0 < γ t)
    {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h n (weighted γ f)) (t : I) (x : Vec3 × ℝ) :
    ‖f t x‖ ≤ γ t * weightedFieldNorm ℓ h γ n f := by
  have hw : ([] : List (Fin 4)) ∈ hierarchyAdmissibleWords (Fin 4) n :=
    mem_hierarchyAdmissibleWords.mpr ⟨Nat.zero_le _, List.Pairwise.nil⟩
  have h0 := norm_word_le_hierarchyFiniteWordNorm False hf.2 hw t x
  change ‖(γ t)⁻¹ • f t x‖ ≤ weightedFieldNorm ℓ h γ n f at h0
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hγ t).le)] at h0
  have hγt := hγ t
  calc ‖f t x‖ = γ t * ((γ t)⁻¹ * ‖f t x‖) := by field_simp
    _ ≤ γ t * weightedFieldNorm ℓ h γ n f := mul_le_mul_of_nonneg_left h0 hγt.le

end FieldNorms

/-! ## Phase-independent fields -/

section PhaseIndependent

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A field is independent of the phase. -/
def PhaseIndep (f : I → Vec3 × ℝ → E) : Prop := ∀ t a s, f t (a, s) = f t (a, 0)

/-- The projection `(a, s) ↦ (a, 0)`. -/
def phaseDrop : (Vec3 × ℝ) →L[ℝ] (Vec3 × ℝ) :=
  (ContinuousLinearMap.inl ℝ Vec3 ℝ).comp (ContinuousLinearMap.fst ℝ Vec3 ℝ)

/-- Evaluation of the phase-dropping map. -/
theorem phaseDrop_apply (x : Vec3 × ℝ) : phaseDrop x = (x.1, 0) := rfl

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A phase-independent field is its own composition with `(a, s) ↦ (a, 0)`. -/
theorem PhaseIndep.eq_comp {f : I → Vec3 × ℝ → E} (hf : PhaseIndep f) (t : I) :
    f t = f t ∘ phaseDrop := by
  funext x
  exact hf t x.1 x.2

/-- The derivative of a phase-independent smooth field only sees the label
component of the increment. -/
theorem PhaseIndep.fderiv_eq {f : I → Vec3 × ℝ → E} (hf : PhaseIndep f)
    (hs : ∀ t, ContDiff ℝ ∞ (f t)) (t : I) (x v : Vec3 × ℝ) :
    fderiv ℝ (f t) x v = fderiv ℝ (f t) (x.1, 0) (v.1, 0) := by
  have hd : DifferentiableAt ℝ (f t) (phaseDrop x) := (hs t).differentiable (by simp) _
  have hc := hd.hasFDerivAt.comp x phaseDrop.hasFDerivAt
  rw [← hf.eq_comp t] at hc
  rw [hc.fderiv]
  rfl

/-- The phase derivative of a phase-independent smooth field vanishes. -/
theorem PhaseIndep.phasePartial_eq_zero {f : I → Vec3 × ℝ → E} (hf : PhaseIndep f)
    (hs : ∀ t, ContDiff ℝ ∞ (f t)) : phasePartial f = 0 := by
  funext t x
  change fderiv ℝ (f t) x (phaseCoordinateDirection (.inr ())) = 0
  rw [hf.fderiv_eq hs t]
  simp only [phaseCoordinateDirection]
  rw [Prod.mk_zero_zero, map_zero]

/-- Label derivatives of a phase-independent smooth field are phase independent. -/
theorem PhaseIndep.labelPartial {f : I → Vec3 × ℝ → E} (hf : PhaseIndep f)
    (hs : ∀ t, ContDiff ℝ ∞ (f t)) (j : Fin 3) : PhaseIndep (labelPartial j f) := by
  intro t a s
  change fderiv ℝ (f t) (a, s) (phaseCoordinateDirection (.inl j)) =
    fderiv ℝ (f t) (a, 0) (phaseCoordinateDirection (.inl j))
  rw [hf.fderiv_eq hs t (a, s) (phaseCoordinateDirection (.inl j)),
    hf.fderiv_eq hs t (a, 0) (phaseCoordinateDirection (.inl j))]

end PhaseIndependent

/-! ## The operators `d̃_i` -/

section Tilde

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The direction field of `d̃_i = ∑_j G_{ji}(∂_{a_j} + k_j ∂_s)` at a fixed time:
`(a, s) ↦ (G(a) e_i, k · G(a) e_i)`. For `G = (D_aX)⁻¹` this is
`d̃ = (D_aX)^{-T}(∇_a + k_*∂_s)` of `08_exact_wave.tex:56`. -/
def tildeDirection (G : Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (i : Fin 3) (x : Vec3 × ℝ) :
    Vec3 × ℝ :=
  (G x.1 (coordinateDirection i), ⟪k, G x.1 (coordinateDirection i)⟫_ℝ)

/-- The direction fields of `d̃` are smooth for a smooth coframe. -/
theorem tildeDirection_smooth {G : Vec3 → Vec3 →L[ℝ] Vec3} (hG : ContDiff ℝ ∞ G) (k : Vec3)
    (i : Fin 3) : ContDiff ℝ ∞ (tildeDirection G k i) := by
  have hv : ContDiff ℝ ∞ fun x : Vec3 × ℝ => G x.1 (coordinateDirection i) :=
    (hG.comp contDiff_fst).clm_apply contDiff_const
  exact hv.prodMk ((innerSL ℝ k).contDiff.comp hv)

/-- The `d̃`-word `d̃_{w₁} ⋯ d̃_{w_m} f` of a field, time by time (the first letter is the
outermost derivative). -/
def tildeWord (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (w : List (Fin 3))
    (f : I → Vec3 × ℝ → E) : I → Vec3 × ℝ → E :=
  fun t => phaseOperatorWord (tildeDirection (G t) k) w (f t)

/-- The coefficient `G_{ji} = (G e_i)_j` of `∂_{a_j}` in `d̃_i`. -/
def labelCoef (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (i j : Fin 3) : I → Vec3 → ℝ :=
  fun t a => (G t a (coordinateDirection i)) j

/-- The coefficient `∑_j G_{ji} k_j = k · G e_i` of `∂_s` in `d̃_i`. -/
def phaseCoef (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (i : Fin 3) : I → Vec3 → ℝ :=
  fun t a => ⟪k, G t a (coordinateDirection i)⟫_ℝ

/-- A vector is the sum of its coordinates times the coordinate directions. -/
theorem sum_coordinate (v : Vec3) : (∑ j : Fin 3, v j • coordinateDirection j) = v := by
  apply PiLp.ext
  intro j
  let eval : Vec3 →L[ℝ] ℝ := EuclideanSpace.proj j
  change eval (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [eval, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- A label-phase increment in the coordinate directions of Appendix D. -/
theorem labelPhase_decomp (v : Vec3) (r : ℝ) :
    ((v, r) : Vec3 × ℝ) = (∑ j : Fin 3, v j • phaseCoordinateDirection (.inl j)) +
      r • phaseCoordinateDirection (.inr ()) := by
  apply Prod.ext
  · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst, phaseCoordinateDirection, smul_zero,
      add_zero]
    exact (sum_coordinate v).symm
  · simp [phaseCoordinateDirection, Prod.snd_sum]

/-- `d̃_i g = ∑_j G_{ji} ∂_{a_j} g + (k·G e_i) ∂_s g`: one letter of a `d̃`-word is a sum of
products of phase-independent coefficients with the label and phase derivatives of
Lemma D.1. -/
theorem tildeWord_cons_eq (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (i : Fin 3)
    (w : List (Fin 3)) (f : I → Vec3 × ℝ → E) :
    tildeWord G k (i :: w) f =
      (∑ j : Fin 3, fun t x => labelCoef G i j t x.1 • labelPartial j (tildeWord G k w f) t x) +
        fun t x => phaseCoef G k i t x.1 • phasePartial (tildeWord G k w f) t x := by
  funext t x
  change fderiv ℝ (phaseOperatorWord (tildeDirection (G t) k) w (f t)) x
      (tildeDirection (G t) k i x) = _
  rw [show tildeDirection (G t) k i x = _ from labelPhase_decomp _ _, map_add, map_sum]
  simp only [map_smul, Pi.add_apply, Finset.sum_apply]
  rfl

/-- One letter of a `d̃`-word applied to a word is the word with one more letter. -/
theorem tildeWord_cons (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (i : Fin 3)
    (w : List (Fin 3)) (f : I → Vec3 × ℝ → E) :
    tildeWord G k (i :: w) f = tildeWord G k [i] (tildeWord G k w f) := rfl

end Tilde

/-! ## The spatial chain rule (3.1) -/

section Graph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The graph point `x ↦ (A(x), k·A(x))` at a fixed time, with `A = X(t,·)⁻¹`. -/
def graphPoint (A : Vec3 → Vec3) (k : Vec3) (x : Vec3) : Vec3 × ℝ := (A x, ⟪k, A x⟫_ℝ)

/-- The graph point is smooth for a smooth inverse map. -/
theorem graphPoint_smooth {A : Vec3 → Vec3} (hA : ContDiff ℝ ∞ A) (k : Vec3) :
    ContDiff ℝ ∞ (graphPoint A k) :=
  hA.prodMk ((innerSL ℝ k).contDiff.comp hA)

/-- The spatial chain rule (3.1), iterated: with `A = X(t,·)⁻¹` and the coframe `G` with
`G(A(x)) = D A(x)`, every Eulerian derivative word of the graph `g ∘ (A, k·A)` is the
graph of the `d̃`-word of `g` (`08_exact_wave.tex:55-56`). -/
theorem spatialDerivativeWord_graph {A : Vec3 → Vec3} (hA : ContDiff ℝ ∞ A)
    {G : Vec3 → Vec3 →L[ℝ] Vec3} (hG : ContDiff ℝ ∞ G) (hGA : ∀ x, G (A x) = fderiv ℝ A x)
    (k : Vec3) {g : Vec3 × ℝ → E} (hg : ContDiff ℝ ∞ g) (w : List (Fin 3)) :
    spatialDerivativeWord w (g ∘ graphPoint A k) =
      phaseOperatorWord (tildeDirection G k) w g ∘ graphPoint A k := by
  refine spatialDerivativeWord_comp ((graphPoint_smooth hA k).differentiable (by simp))
    (tildeDirection_smooth hG k) hg (fun i x => ?_) w
  have hd : HasFDerivAt (graphPoint A k)
      ((fderiv ℝ A x).prod ((innerSL ℝ k).comp (fderiv ℝ A x))) x :=
    (hA.differentiable (by simp) x).hasFDerivAt.prodMk
      ((innerSL ℝ k).hasFDerivAt.comp x (hA.differentiable (by simp) x).hasFDerivAt)
  rw [hd.fderiv]
  simp only [tildeDirection, graphPoint, hGA, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.comp_apply, innerSL_apply_apply]

end Graph

/-! ## Iterating a one-step estimate over derivative words -/

section Iterate

variable {F : Type*}

/-- The word `d_{w₁} ⋯ d_{w_m} f` of a family of operators (first letter outermost). -/
def opWord (d : Fin 3 → F → F) (w : List (Fin 3)) (f : F) : F := w.foldr (fun i g => d i g) f

/-- Unfolding an ordered derivative word with one more leading letter. -/
theorem opWord_cons (d : Fin 3 → F → F) (i : Fin 3) (w : List (Fin 3)) (f : F) :
    opWord d (i :: w) f = d i (opWord d w f) := rfl

/-- The `d̃`-words are the operator words of the one-letter `d̃`. -/
theorem tildeWord_eq_opWord {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (w : List (Fin 3)) (f : I → Vec3 × ℝ → E) :
    tildeWord G k w f = opWord (fun i g => tildeWord G k [i] g) w f := by
  induction w with
  | nil => rfl
  | cons i w ih => rw [tildeWord_cons, ih]; rfl

/-- Iteration of a one-step estimate `∑_i N_n(d_i f) ≤ κ_n N_{n+1}(f)` over all words of
length `m` (`08_exact_wave.tex:66`, "iterate the displayed bound"): the words keep an
invariant `Q` and finite norms, and
`∑_{|w| = m} N_n(d_w f) ≤ (∏_{j<m} κ_{n+j}) N_{n+m}(f)`. -/
theorem iterate_words (d : Fin 3 → F → F) (Fin' : ℕ → F → Prop) (N : ℕ → F → ℝ) (Q : F → Prop)
    (κ : ℕ → ℝ) (hκ : ∀ n, 0 ≤ κ n)
    (hstep : ∀ n f, Q f → Fin' (n + 1) f →
      (∀ i, Q (d i f) ∧ Fin' n (d i f)) ∧ ∑ i, N n (d i f) ≤ κ n * N (n + 1) f) :
    ∀ m n f, Q f → Fin' (n + m) f →
      (∀ w : Fin m → Fin 3, Q (opWord d (List.ofFn w) f) ∧ Fin' n (opWord d (List.ofFn w) f)) ∧
        ∑ w : Fin m → Fin 3, N n (opWord d (List.ofFn w) f) ≤
          (∏ j ∈ Finset.range m, κ (n + j)) * N (n + m) f := by
  intro m
  induction m with
  | zero =>
    intro n f hQ hF
    refine ⟨fun w => ⟨hQ, hF⟩, ?_⟩
    simp [opWord]
  | succ m ih =>
    intro n f hQ hF
    obtain ⟨hw, hsum⟩ := ih (n + 1) f hQ (by simpa [Nat.add_assoc, Nat.add_comm 1 m] using hF)
    have hcons (w : Fin (m + 1) → Fin 3) :
        opWord d (List.ofFn w) f = d (w 0) (opWord d (List.ofFn (Fin.tail w)) f) := by
      rw [List.ofFn_succ]
      rfl
    have hstepw (v : Fin m → Fin 3) :=
      hstep n (opWord d (List.ofFn v) f) (hw v).1 (hw v).2
    refine ⟨fun w => ?_, ?_⟩
    · rw [hcons]
      exact (hstepw (Fin.tail w)).1 (w 0)
    · have hsplit : (∑ w : Fin (m + 1) → Fin 3, N n (opWord d (List.ofFn w) f)) =
          ∑ v : Fin m → Fin 3, ∑ i : Fin 3, N n (d i (opWord d (List.ofFn v) f)) := by
        rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 3)).sum_comp, Fintype.sum_prod_type,
          Finset.sum_comm]
        refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun i _ => ?_
        rw [hcons]
        simp [Fin.consEquiv]
      rw [hsplit]
      calc
        _ ≤ ∑ v : Fin m → Fin 3, κ n * N (n + 1) (opWord d (List.ofFn v) f) :=
          Finset.sum_le_sum fun v _ => (hstepw v).2
        _ = κ n * ∑ v : Fin m → Fin 3, N (n + 1) (opWord d (List.ofFn v) f) := by
          rw [Finset.mul_sum]
        _ ≤ κ n * ((∏ j ∈ Finset.range m, κ (n + 1 + j)) * N (n + 1 + m) f) :=
          mul_le_mul_of_nonneg_left hsum (hκ n)
        _ = (∏ j ∈ Finset.range (m + 1), κ (n + j)) * N (n + (m + 1)) f := by
          rw [Finset.prod_range_succ', show n + 1 + m = n + (m + 1) by omega]
          simp only [add_zero, Nat.add_assoc, Nat.add_comm 1]
          ring

end Iterate

/-! ## Operator norms from coordinate values -/

section Multilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The operator norm of a multilinear map on `ℝ³` is at most the sum of the norms of
its values on the coordinate words. Adapted from the private library lemma
`norm_multilinear_le_of_coordinate_bounds` (`TorusEuler/PhaseJetBounds.lean:322`),
with a sum in place of a uniform bound. -/
theorem norm_le_sum_coordinate {m : ℕ}
    (L : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) E) :
    ‖L‖ ≤ ∑ r : Fin m → Fin 3, ‖L (fun j => coordinateDirection (r j))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have hsum := L.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsub : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => sum_coordinate (p j)
  rw [hsub] at hsum
  change L p = ∑ r : Fin m → Fin 3, L (fun j => p j (r j) • coordinateDirection (r j)) at hsum
  rw [hsum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  rw [show L (fun j => p j (r j) • coordinateDirection (r j)) =
      (∏ j, p j (r j)) • L (fun j => coordinateDirection (r j)) from
    L.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun j _ => PiLp.norm_apply_le (p j) (r j)))
    (norm_nonneg _)

/-- The Fréchet jet of order `m` of a smooth field on `ℝ³` is at most the sum of its
ordered coordinate derivative words. -/
theorem norm_iteratedFDeriv_le_sum_words {g : Vec3 → E} (hg : ContDiff ℝ ∞ g) (m : ℕ)
    (x : Vec3) :
    ‖iteratedFDeriv ℝ m g x‖ ≤
      ∑ r : Fin m → Fin 3, ‖spatialDerivativeWord (List.ofFn r) g x‖ := by
  refine (norm_le_sum_coordinate _).trans_eq (Finset.sum_congr rfl fun r _ => ?_)
  rw [spatialDerivativeWord_eq_iteratedFDeriv hg]
  simp only [List.get_ofFn]
  have hcast {l : ℕ} (hl : l = m) :
      ‖iteratedFDeriv ℝ l g x (fun j => coordinateDirection (r (Fin.cast hl j)))‖ =
        ‖iteratedFDeriv ℝ m g x (fun j => coordinateDirection (r j))‖ := by
    subst l
    rfl
  exact (hcast List.length_ofFn).symm

end Multilinear

end

end TorusEuler.Paper.S5b

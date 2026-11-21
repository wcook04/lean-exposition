import TorusEuler.Paper.Proofs.S5b.Library.Tilde

/-!
# Glue for Lemma 5.7: the word estimates and the coefficient norms

* `words_general`, `words_phaseIndep`: the iteration over words of the one-step bounds
  `tilde_step_general`, `tilde_step_phaseIndep` (`sections/08_exact_wave.tex:66`, "iterate
  the displayed bound"). Both use the statement of Lemma D.1 (hypothesis `hD_1`).
* `coef_bounds`: the norms (D.1) of a phase-independent coefficient `L(G(t,a))` with a
  continuous linear functional `L`, from pointwise bounds `ℓ^m |∇^m G| ≤ B` (the bounds that
  the proof of Lemma 5.7 reads from (5.8) of Proposition 5.1 for `G = (D_aX)⁻¹`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD

noncomputable section

section WordEstimates

variable {I : Type} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The word estimate for a general field**: iterating `tilde_step_general`,
`∑_{|w|=m} ‖d̃_w f‖_{[0],γ} ≤ (∏_{j<m} κ_j) ‖f‖_{[m],γ}` with
`κ_j = c_j (9 Nc_j ℓ⁻¹ + 3 Nk_j h⁻¹)`. Uses `hD_1` (Lemma D.1) at every step. -/
theorem words_general (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {Nc Nk : ℕ → ℝ}
    (hcL : ∀ n i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc n)
    (hcP : ∀ n i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk n)
    {f : I → Vec3 × ℝ → E} (hfin : ∀ n, FieldNormFinite ℓ h n (weighted γ f)) (m : ℕ) :
    (∀ w : Fin m → Fin 3, FieldNormFinite ℓ h 0 (weighted γ (tildeWord G k (List.ofFn w) f))) ∧
      ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) ≤
        (∏ j ∈ Finset.range m, productConst j * (9 * Nc j * ℓ⁻¹ + 3 * Nk j * h⁻¹)) *
          weightedFieldNorm ℓ h γ m f := by
  have hNc (n : ℕ) : 0 ≤ Nc n := (fieldNorm_nonneg (hcL n 0 0).1).trans (hcL n 0 0).2
  have hNk (n : ℕ) : 0 ≤ Nk n := (fieldNorm_nonneg (hcP n 0).1).trans (hcP n 0).2
  have hit := iterate_words (fun i g => tildeWord G k [i] g)
    (fun n g => FieldNormFinite ℓ h n (weighted γ g)) (fun n g => weightedFieldNorm ℓ h γ n g)
    (fun _ => True) (fun j => productConst j * (9 * Nc j * ℓ⁻¹ + 3 * Nk j * h⁻¹))
    (fun j => mul_nonneg (productConst_nonneg j) (add_nonneg
      (mul_nonneg (mul_nonneg (by norm_num) (hNc j)) (inv_nonneg.mpr hℓ.le))
      (mul_nonneg (mul_nonneg (by norm_num) (hNk j)) (inv_nonneg.mpr hh.le))))
    (fun n g _ hg => by
      obtain ⟨h1, h2⟩ := tilde_step_general hD_1 hℓ hh hγ n (hcL n) (hcP n) hg
      exact ⟨fun i => ⟨trivial, h1 i⟩, h2⟩)
    m 0 f trivial (by simpa only [zero_add] using hfin m)
  simp only [zero_add] at hit
  have heq (w : Fin m → Fin 3) : tildeWord G k (List.ofFn w) f =
      opWord (fun i g => tildeWord G k [i] g) (List.ofFn w) f := tildeWord_eq_opWord G k _ f
  refine ⟨fun w => heq w ▸ (hit.1 w).2, ?_⟩
  calc _ = ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0
        (opWord (fun i g => tildeWord G k [i] g) (List.ofFn w) f) :=
        Finset.sum_congr rfl fun w _ => by rw [heq w]
    _ ≤ _ := hit.2

/-- **The word estimate for a phase-independent field**: iterating
`tilde_step_phaseIndep`, `∑_{|w|=m} ‖d̃_w f‖_{[0],γ} ≤ (∏_{j<m} 9 c_j Nc_j ℓ⁻¹) ‖f‖_{[m],γ}`.
Uses `hD_1` (Lemma D.1) at every step. -/
theorem words_phaseIndep (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {Nc Nk : ℕ → ℝ}
    (hcL : ∀ n i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc n)
    (hcP : ∀ n i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk n)
    {f : I → Vec3 × ℝ → E} (hpi : PhaseIndep f)
    (hfin : ∀ n, FieldNormFinite ℓ h n (weighted γ f)) (m : ℕ) :
    (∀ w : Fin m → Fin 3, FieldNormFinite ℓ h 0 (weighted γ (tildeWord G k (List.ofFn w) f))) ∧
      ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) ≤
        (∏ j ∈ Finset.range m, productConst j * (9 * Nc j * ℓ⁻¹)) *
          weightedFieldNorm ℓ h γ m f := by
  have hNc (n : ℕ) : 0 ≤ Nc n := (fieldNorm_nonneg (hcL n 0 0).1).trans (hcL n 0 0).2
  have hit := iterate_words (fun i g => tildeWord G k [i] g)
    (fun n g => FieldNormFinite ℓ h n (weighted γ g)) (fun n g => weightedFieldNorm ℓ h γ n g)
    PhaseIndep (fun j => productConst j * (9 * Nc j * ℓ⁻¹))
    (fun j => mul_nonneg (productConst_nonneg j)
      (mul_nonneg (mul_nonneg (by norm_num) (hNc j)) (inv_nonneg.mpr hℓ.le)))
    (fun n g hq hg => tilde_step_phaseIndep hD_1 hℓ hh hγ n (hcL n) (hcP n) hq hg)
    m 0 f hpi (by simpa only [zero_add] using hfin m)
  simp only [zero_add] at hit
  have heq (w : Fin m → Fin 3) : tildeWord G k (List.ofFn w) f =
      opWord (fun i g => tildeWord G k [i] g) (List.ofFn w) f := tildeWord_eq_opWord G k _ f
  refine ⟨fun w => heq w ▸ (hit.1 w).2, ?_⟩
  calc _ = ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0
        (opWord (fun i g => tildeWord G k [i] g) (List.ofFn w) f) :=
        Finset.sum_congr rfl fun w _ => by rw [heq w]
    _ ≤ _ := hit.2

end WordEstimates

/-! ## Norms of phase-independent coefficients -/

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

/-- **Norms of a phase-independent coefficient.** For a smooth coframe `G` with uniformly
bounded jets and `ℓ^m |∇^m G(t,a)| ≤ B` for `m ≤ n`, and a continuous linear functional
`L`, the field `(t,a,s) ↦ L(G(t,a))` has a finite norm (D.1) of order `n`, at most
`#W_n ‖L‖ B`. -/
theorem coef_bounds {G : I → Vec3 → Vec3 →L[ℝ] Vec3} (L : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ)
    {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hG : ∀ t, ContDiff ℝ ∞ (G t))
    (hunif : ∀ m, ∃ b, ∀ t a, ‖iteratedFDeriv ℝ m (G t) a‖ ≤ b)
    (hjet : ∀ m ≤ n, ∀ t a, ℓ ^ m * ‖iteratedFDeriv ℝ m (G t) a‖ ≤ B) :
    FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => L (G t x.1)) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => L (G t x.1)) ≤
        (hierarchyAdmissibleWords (Fin 3) n).card * (‖L‖ * B) := by
  let c : I → Vec3 → ℝ := fun t a => L (G t a)
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

/-- The functional `A ↦ (A e_i)_j`, so that `labelCoef G i j t a = (G t a e_i)_j`. -/
def labelFunctional (i j : Fin 3) : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
  (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i))

/-- The functional `A ↦ k · A e_i`, so that `phaseCoef G k i t a = k · G t a e_i`. -/
def phaseFunctional (k : Vec3) (i : Fin 3) : (Vec3 →L[ℝ] Vec3) →L[ℝ] ℝ :=
  (innerSL ℝ k).comp (ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i))

/-- The coordinate functional has norm at most one. -/
theorem norm_apply_coordinate_le (i : Fin 3) :
    ‖ContinuousLinearMap.apply ℝ Vec3 (coordinateDirection i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun A => ?_
  have h1 : ‖coordinateDirection i‖ = 1 := by simp [coordinateDirection]
  simpa [h1] using A.le_opNorm (coordinateDirection i)

/-- The label functional has norm at most one. -/
theorem norm_labelFunctional_le (i j : Fin 3) : ‖labelFunctional i j‖ ≤ 1 := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  have hp : ‖(EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using PiLp.norm_apply_le v j
  simpa using mul_le_mul hp (norm_apply_coordinate_le i) (norm_nonneg _) zero_le_one

/-- The phase functional has norm at most the norm of the wavevector. -/
theorem norm_phaseFunctional_le (k : Vec3) (i : Fin 3) : ‖phaseFunctional k i‖ ≤ ‖k‖ := by
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [innerSL_apply_norm]
  simpa using mul_le_mul_of_nonneg_left (norm_apply_coordinate_le i) (norm_nonneg k)

/-- Label coefficient as the evaluation of the label functional. -/
theorem labelCoef_eq (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (i j : Fin 3) (t : I) (a : Vec3) :
    labelCoef G i j t a = labelFunctional i j (G t a) := rfl

/-- Phase coefficient as the evaluation of the phase functional. -/
theorem phaseCoef_eq (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (k : Vec3) (i : Fin 3) (t : I) (a : Vec3) :
    phaseCoef G k i t a = phaseFunctional k i (G t a) := rfl

end Coefficients

end

end TorusEuler.Paper.S5b

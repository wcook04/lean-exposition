import TorusEuler.HierarchyActualNorms
import TorusEuler.HierarchyConcreteCompletion
import TorusEuler.HierarchyLinearRelayBounds
import TorusEuler.HierarchySourceBounds
import TorusEuler.OscillatorySolveSymmetries

/-! Coordinate derivatives, products and phase operations in Lemma D.1. -/

open MeasureTheory Set
open scoped ContDiff

namespace TorusEuler

section FiniteFieldNorm

variable {ι I U E : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem finiteWordNorm_const_smul (holder : Prop) {D : ι → U → U}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (n : ℕ) {f : I → U → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (c : ℝ) :
    hierarchyFiniteWordNorm holder D n (c • f) = ‖c‖ * hierarchyFiniteWordNorm holder D n f := by
  unfold hierarchyFiniteWordNorm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [actualJetValues_smul holder hD w hf c, Real.sSup_smul_of_nonneg (norm_nonneg c)]
  rfl

/-- An unscaled constant coordinate derivative costs the reciprocal of
the positive weight of its letter. -/
theorem paperFiniteNorm_directionalDerivative_le (holder : Prop) (d : ι → U)
    (r : ι → ℝ) (i : ι) (hr : 0 < r i) (n : ℕ) {f : I → U → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι (n + 1),
      BddAbove (hierarchyJetValues holder (fun j _ => r j • d j) w f)) :
    hierarchyFiniteWordNorm holder (fun j _ => r j • d j) n
      (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)) ≤
      (r i)⁻¹ * hierarchyFiniteWordNorm holder (fun j _ => r j • d j) (n + 1) f := by
  let g (t : I) := phaseDirectionalDerivative (fun _ => r i • d i) (f t)
  have hg (t : I) : ContDiff ℝ ∞ (g t) :=
    ((hf t).fderiv_right (by simp)).clm_apply contDiff_const
  have hEq : (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)) = (r i)⁻¹ • g := by
    funext t x
    change fderiv ℝ (f t) x (d i) = (r i)⁻¹ • fderiv ℝ (f t) x (r i • d i)
    rw [map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  rw [hEq, finiteWordNorm_const_smul holder (fun _ => contDiff_const) n hg,
    Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hr.le)]
  exact mul_le_mul_of_nonneg_left
    (hierarchyFiniteWordNorm_constDerivative_le holder (fun j => r j • d j) hf i n hb).2
    (inv_nonneg.mpr hr.le)

end FiniteFieldNorm

/-- Spatial half-Hölder control costs one label derivative and one
inverse square root of the label scale. -/
theorem paperAppendixD_holderComparison {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hℓ₁ : ℓ ≤ 1) (n : ℕ) {f : I → Vec3 → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 3) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f))
    (hbh : ∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
      BddAbove (hierarchyJetValues True (hierarchyLabelDirection ℓ) w f)) :
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n f ≤
      hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) n f ∧
    hierarchyFiniteWordNorm True (hierarchyLabelDirection ℓ) n f ≤
      4 * hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) (n + 1) f / Real.sqrt ℓ := by
  refine ⟨?_, hierarchyFiniteWordNorm_holder_le ℓ hℓ hℓ₁ n hf hb⟩
  unfold hierarchyFiniteWordNorm
  apply Finset.sum_le_sum
  intro w hw
  refine csSup_le_csSup (hbh w hw) ⟨0, Or.inl rfl⟩ ?_
  rintro r (h | h | ⟨h, _⟩)
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact h.elim

section MixedFields

variable {I E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

local notation "Q" => Vec3 × ℝ

/-- Both derivative losses in (D.2) for the exact coordinate word norm. -/
theorem paperLemmaD1_derivatives (ell h : ℝ) (hell : 0 < ell) (hh : 0 < h) (n : ℕ)
    {f : I → Q → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ell h) w f)) :
    let N (m : ℕ) := hierarchyFiniteWordNorm False (hierarchyMixedDirection ell h) m (E := E) (T := I)
    (∑ i : Fin 3, N n (fun t => phaseDirectionalDerivative (fun _ => phaseCoordinateDirection (.inl i))
      (f t))) ≤ 3 * ell⁻¹ * N (n + 1) f ∧
    N n (fun t => phaseDirectionalDerivative (fun _ => phaseCoordinateDirection (.inr ())) (f t)) ≤
      h⁻¹ * N (n + 1) f := by
  let q (i : Fin 4) : Q := Fin.lastCases (phaseCoordinateDirection (.inr ()))
    (fun j => phaseCoordinateDirection (.inl j)) i
  let s (i : Fin 4) : ℝ := Fin.lastCases h (fun _ : Fin 3 => ell) i
  have hEq : (fun j (_ : Q) => s j • q j) = hierarchyMixedDirection ell h := by
    funext j x
    refine Fin.lastCases (motive := fun i => s i • q i = hierarchyMixedDirection ell h i x)
      ?_ (fun i => ?_) j
    · simp only [q, s, hierarchyMixedDirection, Fin.lastCases_last]
    · simp only [q, s, hierarchyMixedDirection, Fin.lastCases_castSucc]
  have hb' := hEq.symm ▸ hb
  have hDer (i : Fin 4) (hi : 0 < s i) :=
    paperFiniteNorm_directionalDerivative_le False q s i hi n hf hb'
  simp only
  constructor
  · calc
      _ ≤ ∑ _i : Fin 3, ell⁻¹ * hierarchyFiniteWordNorm False (hierarchyMixedDirection ell h) (n + 1) f := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [hEq, s, q, Fin.lastCases_castSucc] using hDer i.castSucc
          (by simp [s, hell])
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring
  · simpa only [hEq, s, q, Fin.lastCases_last] using hDer (Fin.last 3)
      (by simpa only [s, Fin.lastCases_last] using hh)

/-- The product estimate (D.3) applies to a time-normalized second
factor. Choosing the label directions and unweighted time slices gives
the half-Hölder version for phase-independent fields as well. -/
theorem paperLemmaD1_product {J V : Type*} [Fintype J] [LinearOrder J]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (B : E →L[ℝ] F →L[ℝ] G) (holder : Prop) {D : J → V → V}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) (n : ℕ) {f : I → V → E} {g : I → V → F}
    (γ : I → ℝ) (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfb : ∀ w ∈ hierarchyAdmissibleWords J n, BddAbove (hierarchyJetValues holder D w f))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords J n,
      BddAbove (hierarchyJetValues holder D w (fun t x => (γ t)⁻¹ • g t x))) :
    hierarchyFiniteWordNorm holder D n (fun t x => (γ t)⁻¹ • B (f t x) (g t x)) ≤
      ((hierarchyAdmissibleWords J n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) *
        hierarchyFiniteWordNorm holder D n f *
        hierarchyFiniteWordNorm holder D n (fun t x => (γ t)⁻¹ • g t x) := by
  simp_rw [← map_smul]
  have h := hierarchyFiniteWordNorm_bilinear_le B holder hD n hf
    (fun t => (hg t).const_smul ((γ t)⁻¹)) hfb hgb
  refine h.trans_eq ?_
  ring

variable [CompleteSpace E]

private noncomputable def appendixPhaseMeanTranslations (f : Q → E) (x : Q) : E :=
  phaseMean (fun r => f (x + (0, r)))

private theorem appendixPhaseMeanTranslations_smooth {f : Q → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (appendixPhaseMeanTranslations f) := by
  let F (x : Q) (r : ℝ) := f (x + (0, r))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hf.comp (contDiff_fst.add (contDiff_const.prodMk contDiff_snd))
  exact (contDiff_and_iteratedFDeriv_phaseInterval hF 0 1).1

private theorem appendixPhaseMeanTranslations_derivative
    {f : Q → E} (hf : ContDiff ℝ ∞ f) (d : Q) :
    phaseDirectionalDerivative (fun _ => d) (appendixPhaseMeanTranslations f) =
      appendixPhaseMeanTranslations (phaseDirectionalDerivative (fun _ => d) f) := by
  let F (x : Q) (r : ℝ) := f (x + (0, r))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hf.comp (contDiff_fst.add (contDiff_const.prodMk contDiff_snd))
  funext x
  have hD : fderiv ℝ (appendixPhaseMeanTranslations f) x =
      phaseMean (fun r => fderiv ℝ f (x + (0, r))) := by
    change fderiv ℝ (fun y => phaseMean (F y)) x = _
    rw [fderiv_phaseMean_eq_phaseMean_fderiv hF]
    simp only [F, fderiv_comp_add_right]
  let L : (Q →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E d
  have hc : Continuous (fun r : ℝ => fderiv ℝ f (x + (0, r))) :=
    (hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_const.prodMk continuous_id))
  change fderiv ℝ (appendixPhaseMeanTranslations f) x d =
    phaseMean (fun r => fderiv ℝ f (x + (0, r)) d)
  rw [hD]
  exact (L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)).symm

private theorem appendixPhaseMeanTranslations_word {J : Type*} (d : J → Q) (w : List J)
    {f : Q → E} (hf : ContDiff ℝ ∞ f) :
    phaseOperatorWord (fun i _ => d i) w (appendixPhaseMeanTranslations f) =
      appendixPhaseMeanTranslations (phaseOperatorWord (fun i _ => d i) w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [phaseOperatorWord, ih]
    exact appendixPhaseMeanTranslations_derivative
      (contDiff_phaseOperatorWord (fun _ => contDiff_const) hf w) (d i)

omit [CompleteSpace E] in
private theorem appendixPhaseMeanTranslations_eq {f : Q → E}
    (hper : ∀ a, Function.Periodic (fun s => f (a, s)) 1) (x : Q) :
    appendixPhaseMeanTranslations f x = phaseMean (fun s => f (x.1, s)) := by
  rcases x with ⟨a, s⟩
  change phaseMean (fun r => f (a + 0, s + r)) = _
  simp only [add_zero]
  simpa only [add_comm s] using (phaseMean_translate_periodic (hper a) s)

open scoped Pointwise in
/-- Phase averaging is contractive and subtraction of the mean costs
at most two, in the same time-weighted finite norm. -/
theorem paperLemmaD1_phaseAverage {J : Type*} [Fintype J] [LinearOrder J]
    (d : J → Q) (n : ℕ) {f : I → Q → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a, s)) 1)
    (hb : ∀ w ∈ hierarchyAdmissibleWords J n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w f)) :
    let avg (t : I) (x : Q) := phaseMean (fun s => f t (x.1, s))
    let N := hierarchyFiniteWordNorm False (fun i _ => d i) n (E := E) (T := I)
    N avg ≤ N f ∧ N (f - avg) ≤ 2 * N f := by
  let avg (t : I) (x : Q) := phaseMean (fun s => f t (x.1, s))
  let D (i : J) (_ : Q) := d i
  let N := hierarchyFiniteWordNorm False D n (E := E) (T := I)
  have hEq (t : I) : avg t = appendixPhaseMeanTranslations (f t) :=
    funext fun x => (appendixPhaseMeanTranslations_eq (hper t) x).symm
  have hSmooth (t : I) : ContDiff ℝ ∞ (avg t) := hEq t ▸ appendixPhaseMeanTranslations_smooth (hf t)
  have hPoint (w : List J) (hw : w ∈ hierarchyAdmissibleWords J n) :
      sSup (hierarchyJetValues False D w f) ∈ upperBounds (hierarchyJetValues False D w avg) := by
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨h, _⟩)
    · exact le_csSup (hb w hw) (Or.inl rfl)
    · rw [hEq t, appendixPhaseMeanTranslations_word d w (hf t)]
      exact norm_phaseMean_le fun s _ =>
        le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x + (0, s), rfl⟩))
    · exact h.elim
  have ha (w : List J) (hw : w ∈ hierarchyAdmissibleWords J n) :
      sSup (hierarchyJetValues False D w avg) ≤ sSup (hierarchyJetValues False D w f) :=
    csSup_le ⟨0, Or.inl rfl⟩ (hPoint w hw)
  refine ⟨Finset.sum_le_sum ha, ?_⟩
  have hNneg (w : List J) :
      hierarchyJetValues False D w (-avg) = hierarchyJetValues False D w avg := by
    rw [show -avg = (-1 : ℝ) • avg from (neg_one_smul ℝ avg).symm,
      actualJetValues_smul False (fun _ => contDiff_const) w hSmooth, norm_neg, norm_one, one_smul]
  change N (f - avg) ≤ 2 * N f
  rw [sub_eq_add_neg, two_mul]
  unfold N hierarchyFiniteWordNorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun w hw => ?_
  have h := actualJetValues_add_le False (fun _ => contDiff_const) w hf
    (g := -avg) (fun t => (hSmooth t).neg) (hb w hw)
    (show BddAbove (hierarchyJetValues False D w (-avg)) by
      rw [hNneg]
      exact ⟨_, hPoint w hw⟩)
  rw [hNneg] at h
  exact h.trans (add_le_add le_rfl (ha w hw))

/-- The primitive in (D.4) acts on phase-periodic zero-mean fields. -/
theorem paperLemmaD1_phasePrimitive {J : Type*} [Fintype J] [LinearOrder J]
    (d : J → Q) (n : ℕ) {f : I → Q → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a, s)) 1)
    (hzero : ∀ t a, phaseMean (fun s => f t (a, s)) = 0)
    (hb : ∀ w ∈ hierarchyAdmissibleWords J n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w f)) :
    hierarchyFiniteWordNorm False (fun i _ => d i) n
      (fun t x => phasePrimitive (fun s => f t (x.1, s)) x.2) ≤
      2 * hierarchyFiniteWordNorm False (fun i _ => d i) n f :=
  (hierarchyFiniteWordNorm_phasePrimitive_le d n hf hper hzero hb).2

end MixedFields

end TorusEuler

import TorusEuler.Paper.SBD.Vocabulary

/-! # Glue for the proof of Lemma D.1: finiteness of the finite norms

The inequalities of Lemma D.1 come from the library lemmas `paperLemmaD1_*`
(own content of D.1). The statement also asserts that each left side has a
finite norm; this file provides the finiteness glue (namespace
`TorusEuler.Paper.Lib.SBD`). Public copies of private glue lemmas (verbatim
except for names and visibility):

* `actualWord_add` (HierarchyActualNorms.lean:34) → `phaseOperatorWord_add'`;
* `hierarchy_admissible_jet_bounds` (HierarchySourceBounds.lean:149) →
  `admissible_jet_bounds'` (the `let F := …` of the conclusion is unfolded);
* `hierarchyJetValues_bdd_bilinear` (HierarchySourceBounds.lean:169) →
  `hierarchyJetValues_bdd_bilinear'` (calls the copy above; nonnegativity of
  the norms by `Finset.sum_nonneg` in place of `hierarchyFiniteWordNorm_nonneg`);
* `appendixPhaseMeanTranslations`, `_smooth`, `_derivative`, `_word`, `_eq`
  (PaperAppendixDFields.lean:144-194) → `phaseMeanTranslations'`, `_smooth`,
  `_derivative`, `_word`, `_eq`.

Adapted from proofs of library lemmas of Lemma D.1 (own content of the row D.1):

* `jetValues_bdd_dirDeriv` (finiteness of the norm of a derivative): the
  rescaling `g`, `hg`, `hEq` is copied from the proof of
  `paperFiniteNorm_directionalDerivative_le` (PaperAppendixDFields.lean:40-46,
  which calls `hierarchyFiniteWordNorm_constDerivative_le`, content of D.1), and
  the bound is read off the first part of
  `hierarchyFiniteWordNorm_constDerivative_le`;
* `phaseAverage_jetValues_bdd`: the steps `hEq`, `hSmooth`, `hPoint` are
  copied from the proof of `paperLemmaD1_phaseAverage`
  (PaperAppendixDFields.lean:211-221, content of D.1), with the private
  `appendixPhaseMeanTranslations*` replaced by the copies above.

New glue: `jetValues_bdd_add`, `jetValues_bdd_smul`. -/

open MeasureTheory Set
open scoped ContDiff Pointwise

namespace TorusEuler.Paper.Lib.SBD

section Words

variable {ι T U E F G : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

omit [Fintype ι] [LinearOrder ι] in
/-- A derivative word of a sum of smooth fields is the sum of the words. Copy
of the private `actualWord_add` (HierarchyActualNorms.lean:34). -/
theorem phaseOperatorWord_add' {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f g : U → E} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : List ι) (x : U) :
    phaseOperatorWord D w (f + g) x = phaseOperatorWord D w f x + phaseOperatorWord D w g x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord D w (f + g)) x (D i x) = _
    rw [show phaseOperatorWord D w (f + g) =
      phaseOperatorWord D w f + phaseOperatorWord D w g from funext ih,
      fderiv_add ((contDiff_phaseOperatorWord hD hf w).differentiable (by simp) x)
        ((contDiff_phaseOperatorWord hD hg w).differentiable (by simp) x)]
    rfl

omit [Fintype ι] [LinearOrder ι] in
/-- The sum of two fields with bounded jets of a word has bounded jets of that
word (supremum quantities). -/
theorem jetValues_bdd_add {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i)) (w : List ι)
    {f g : T → U → E} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hbf : BddAbove (hierarchyJetValues False D w f))
    (hbg : BddAbove (hierarchyJetValues False D w g)) :
    BddAbove (hierarchyJetValues False D w (f + g)) := by
  refine ⟨sSup (hierarchyJetValues False D w f) + sSup (hierarchyJetValues False D w g), ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
  · exact add_nonneg (le_csSup hbf (Or.inl rfl)) (le_csSup hbg (Or.inl rfl))
  · change ‖phaseOperatorWord D w (f t + g t) x‖ ≤ _
    rw [phaseOperatorWord_add' hD (hf t) (hg t)]
    exact (norm_add_le _ _).trans (add_le_add
      (le_csSup hbf (Or.inr (Or.inl ⟨t, x, rfl⟩)))
      (le_csSup hbg (Or.inr (Or.inl ⟨t, x, rfl⟩))))
  · exact hH.elim

omit [Fintype ι] [LinearOrder ι] in
/-- A scalar multiple of a field with bounded jets of a word has bounded jets. -/
theorem jetValues_bdd_smul (holder : Prop) {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (w : List ι) {f : T → U → E} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (c : ℝ)
    (hb : BddAbove (hierarchyJetValues holder D w f)) :
    BddAbove (hierarchyJetValues holder D w (c • f)) := by
  rw [actualJetValues_smul holder hD w hf c]
  exact hb.smul_of_nonneg (norm_nonneg c)

/-- Pointwise bounds of an admissible word by the finite norm. Copy of the
private `hierarchy_admissible_jet_bounds` (HierarchySourceBounds.lean:149). -/
theorem admissible_jet_bounds' {holder : Prop} {D : ι → U → U}
    {n : ℕ} {f : T → U → E}
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    {w : List ι} (hw : w ∈ hierarchyAdmissibleWords ι n) (t : T) :
    (∀ x, ‖phaseOperatorWord D w (f t) x‖ ≤ hierarchyFiniteWordNorm holder D n f) ∧
      (holder → ∀ x y, ‖phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y‖ ≤
        hierarchyFiniteWordNorm holder D n f * Real.sqrt (dist x y)) := by
  have h : sSup (hierarchyJetValues holder D w f) ≤ hierarchyFiniteWordNorm holder D n f := by
    apply Finset.single_le_sum _ hw
    intro v hv
    exact le_csSup (hb v hv) (Or.inl rfl)
  refine ⟨fun x => (le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans h, ?_⟩
  intro hh x y
  by_cases hxy : x = y
  · subst y
    simp
  · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).mp
    exact (le_csSup (hb w hw) (Or.inr (Or.inr ⟨hh, t, x, y, rfl⟩))).trans h

/-- A bilinear product of two fields with finite norms has bounded jets of
every admissible word. Copy of the private `hierarchyJetValues_bdd_bilinear`
(HierarchySourceBounds.lean:169). -/
theorem hierarchyJetValues_bdd_bilinear' (B : E →L[ℝ] F →L[ℝ] G)
    (holder : Prop) {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (n : ℕ) {f : T → U → E} {g : T → U → F}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w g))
    (w : List ι) (hw : w ∈ hierarchyAdmissibleWords ι n) :
    BddAbove (hierarchyJetValues holder D w (fun t x => B (f t x) (g t x))) := by
  let fN := hierarchyFiniteWordNorm holder D n f
  let gN := hierarchyFiniteWordNorm holder D n g
  have hf₀ : 0 ≤ fN := Finset.sum_nonneg fun w hw => le_csSup (hfb w hw) (Or.inl rfl)
  have hg₀ : 0 ≤ gN := Finset.sum_nonneg fun w hw => le_csSup (hgb w hw) (Or.inl rfl)
  obtain ⟨hord, hsort⟩ := mem_hierarchyAdmissibleWords.mp hw
  have hsub (v : List ι) (hv : List.Sublist v w) : v ∈ hierarchyAdmissibleWords ι n :=
    mem_hierarchyAdmissibleWords.mpr ⟨hv.length_le.trans hord, hsort.sublist hv⟩
  have bound (t : T) := phaseOperatorWord_bilinear_bounds B hD (hf t) (hg t)
    w hf₀ (fun v hv => (admissible_jet_bounds' hfb (hsub v hv) t).1)
    (fun v hv => (admissible_jet_bounds' hgb (hsub v hv) t).1)
  let C := (2 : ℝ) ^ w.length * (2 * ‖B‖ * fN * gN)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, ?_⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hh, t, x, y, rfl⟩)
  · exact hC
  · exact ((bound t).1 x).trans (by dsimp [C, fN, gN] at *; nlinarith)
  · by_cases hxy : x = y
    · subst y
      simpa only [sub_self, norm_zero, zero_div] using hC
    · exact (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).2
        ((bound t).2 (fun v hv => (admissible_jet_bounds' hfb (hsub v hv) t).2 hh)
          (fun v hv => (admissible_jet_bounds' hgb (hsub v hv) t).2 hh) x y)

/-- Finiteness of the norm of order `n` of a derivative in one weighted
constant direction, from finiteness of the norm of order `n + 1`: the first
part of `hierarchyFiniteWordNorm_constDerivative_le` (own content of D.1),
rescaled from the weighted direction `r_i d_i` to the unit direction `d_i`.
The rescaling (`g`, `hg`, `hEq`) is copied from the proof of
`paperFiniteNorm_directionalDerivative_le` (PaperAppendixDFields.lean:40-46),
Lemma D.1 glue that calls the same content lemma. -/
theorem jetValues_bdd_dirDeriv (holder : Prop) (d : ι → U) (r : ι → ℝ) (i : ι)
    (hr : 0 < r i) (n : ℕ) {f : T → U → E} (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hb : ∀ w ∈ hierarchyAdmissibleWords ι (n + 1),
      BddAbove (hierarchyJetValues holder (fun j _ => r j • d j) w f)) :
    (∀ t, ContDiff ℝ ∞ (phaseDirectionalDerivative (fun _ => d i) (f t))) ∧
    ∀ w ∈ hierarchyAdmissibleWords ι n,
      BddAbove (hierarchyJetValues holder (fun j _ => r j • d j) w
        (fun t => phaseDirectionalDerivative (fun _ => d i) (f t))) := by
  let g (t : T) := phaseDirectionalDerivative (fun _ => r i • d i) (f t)
  have hg (t : T) : ContDiff ℝ ∞ (g t) :=
    ((hf t).fderiv_right (by simp)).clm_apply contDiff_const
  have hEq : (fun t => phaseDirectionalDerivative (fun _ => d i) (f t)) = (r i)⁻¹ • g := by
    funext t x
    change fderiv ℝ (f t) x (d i) = (r i)⁻¹ • fderiv ℝ (f t) x (r i • d i)
    rw [map_smul, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  refine ⟨fun t => ((hf t).fderiv_right (by simp)).clm_apply contDiff_const, fun w hw => ?_⟩
  rw [hEq]
  exact jetValues_bdd_smul holder (fun _ => contDiff_const) w hg _
    ((hierarchyFiniteWordNorm_constDerivative_le holder (fun j => r j • d j) hf i n hb).1 w hw)

end Words

section PhaseMean

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

local notation "Q" => Vec3 × ℝ

/-- Phase mean of the phase translates of a field. Copy of the private
`appendixPhaseMeanTranslations` (PaperAppendixDFields.lean:144). -/
noncomputable def phaseMeanTranslations' (f : Q → E) (x : Q) : E :=
  phaseMean (fun r => f (x + (0, r)))

/-- Copy of the private `appendixPhaseMeanTranslations_smooth`
(PaperAppendixDFields.lean:147). -/
theorem phaseMeanTranslations'_smooth {f : Q → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (phaseMeanTranslations' f) := by
  let F (x : Q) (r : ℝ) := f (x + (0, r))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hf.comp (contDiff_fst.add (contDiff_const.prodMk contDiff_snd))
  exact (contDiff_and_iteratedFDeriv_phaseInterval hF 0 1).1

/-- Copy of the private `appendixPhaseMeanTranslations_derivative`
(PaperAppendixDFields.lean:154): constant-direction derivatives commute with
the phase mean of the translates. -/
theorem phaseMeanTranslations'_derivative {f : Q → E} (hf : ContDiff ℝ ∞ f) (d : Q) :
    phaseDirectionalDerivative (fun _ => d) (phaseMeanTranslations' f) =
      phaseMeanTranslations' (phaseDirectionalDerivative (fun _ => d) f) := by
  let F (x : Q) (r : ℝ) := f (x + (0, r))
  have hF : ContDiff ℝ ∞ (Function.uncurry F) :=
    hf.comp (contDiff_fst.add (contDiff_const.prodMk contDiff_snd))
  funext x
  have hD : fderiv ℝ (phaseMeanTranslations' f) x =
      phaseMean (fun r => fderiv ℝ f (x + (0, r))) := by
    change fderiv ℝ (fun y => phaseMean (F y)) x = _
    rw [fderiv_phaseMean_eq_phaseMean_fderiv hF]
    simp only [F, fderiv_comp_add_right]
  let L : (Q →L[ℝ] E) →L[ℝ] E := ContinuousLinearMap.apply ℝ E d
  have hc : Continuous (fun r : ℝ => fderiv ℝ f (x + (0, r))) :=
    (hf.continuous_fderiv (by simp)).comp
      (continuous_const.add (continuous_const.prodMk continuous_id))
  change fderiv ℝ (phaseMeanTranslations' f) x d =
    phaseMean (fun r => fderiv ℝ f (x + (0, r)) d)
  rw [hD]
  exact (L.intervalIntegral_comp_comm (hc.intervalIntegrable 0 1)).symm

/-- Copy of the private `appendixPhaseMeanTranslations_word`
(PaperAppendixDFields.lean:176). -/
theorem phaseMeanTranslations'_word {J : Type*} (d : J → Q) (w : List J)
    {f : Q → E} (hf : ContDiff ℝ ∞ f) :
    phaseOperatorWord (fun i _ => d i) w (phaseMeanTranslations' f) =
      phaseMeanTranslations' (phaseOperatorWord (fun i _ => d i) w f) := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [phaseOperatorWord, ih]
    exact phaseMeanTranslations'_derivative
      (contDiff_phaseOperatorWord (fun _ => contDiff_const) hf w) (d i)

omit [CompleteSpace E] in
/-- Copy of the private `appendixPhaseMeanTranslations_eq`
(PaperAppendixDFields.lean:188): for periodic fields, the mean of the
translates is the phase average. -/
theorem phaseMeanTranslations'_eq {f : Q → E}
    (hper : ∀ a, Function.Periodic (fun s => f (a, s)) 1) (x : Q) :
    phaseMeanTranslations' f x = phaseMean (fun s => f (x.1, s)) := by
  rcases x with ⟨a, s⟩
  change phaseMean (fun r => f (a + 0, s + r)) = _
  simp only [add_zero]
  simpa only [add_comm s] using (phaseMean_translate_periodic (hper a) s)

/-- The phase average of a periodic field with bounded jets is smooth and has
bounded jets: each word of the average is the average of the word, bounded by
the supremum of the word. Adapted from the boundedness part (`hEq`, `hSmooth`,
`hPoint`) of the proof of `paperLemmaD1_phaseAverage`
(PaperAppendixDFields.lean:211-221), own content of D.1, with
`appendixPhaseMeanTranslations*` renamed to `phaseMeanTranslations'*`. -/
theorem phaseAverage_jetValues_bdd {J : Type*} [Fintype J] [LinearOrder J]
    (d : J → Q) (n : ℕ) {f : I → Q → E}
    (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a, s)) 1)
    (hb : ∀ w ∈ hierarchyAdmissibleWords J n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w f)) :
    (∀ t, ContDiff ℝ ∞ (fun x : Q => phaseMean (fun s => f t (x.1, s)))) ∧
    ∀ w ∈ hierarchyAdmissibleWords J n,
      BddAbove (hierarchyJetValues False (fun i _ => d i) w
        (fun t (x : Q) => phaseMean (fun s => f t (x.1, s)))) := by
  have hEq (t : I) : (fun x : Q => phaseMean (fun s => f t (x.1, s))) =
      phaseMeanTranslations' (f t) :=
    funext fun x => (phaseMeanTranslations'_eq (hper t) x).symm
  refine ⟨fun t => hEq t ▸ phaseMeanTranslations'_smooth (hf t), fun w hw =>
    ⟨sSup (hierarchyJetValues False (fun i _ => d i) w f), ?_⟩⟩
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨h, _⟩)
  · exact le_csSup (hb w hw) (Or.inl rfl)
  · change ‖phaseOperatorWord (fun i _ => d i) w
      (fun x : Q => phaseMean (fun s => f t (x.1, s))) x‖ ≤ _
    rw [hEq t, phaseMeanTranslations'_word d w (hf t)]
    exact norm_phaseMean_le fun s _ =>
      le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x + (0, s), rfl⟩))
  · exact h.elim

end PhaseMean

end TorusEuler.Paper.Lib.SBD

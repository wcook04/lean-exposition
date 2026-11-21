import TorusEuler.Paper.Proofs.S5b.T56Prod
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.HierarchyTwistedSourceCancellation

/-!
# Theorem 5.6, glue: the operators of §5.5 as fields, and comparisons of norms

* The time slices of `(f·𝐝)g`, `(f·κ)∂_s g`, `(𝐝·V)Y` and `⟨f⟩` for the operators `S5.ops d` of a
  parent are the fields `slowAdv`, `fastAdv`, `divProd`, `phaseAverage` of `T56Prod` with the
  coefficients `(D_aX)⁻¹(t,a) = D(X(t,·)⁻¹)(X(t,a))` and `κ(t,a)` (`slices_labelAdv`,
  `slices_phaseAdv`, `slices_divProduct`, `slices_average`).
* Comparisons of the norms (D.1) on the two time domains: the unweighted norm on `[t₀,T]` is at
  most the weighted one when `γ ≤ 1` (`plain_le_wNorm`) and at most the unweighted norm on `[0,T]`
  (`plain_le_uNorm`); for a field vanishing before `t₀` the unweighted norm on `[0,T]` is the one
  on `[t₀,T]` (`uNorm_le_plain`), hence at most the weighted norm (`uNorm_le_wNorm`). These are
  the comparisons "the weighted norm dominates the unweighted one because `γ ≤ 1`"
  (`sections/06c_finite_hierarchy.tex:654-657`).
* `coefField_bounds`: the norm (D.1) of a phase-independent coefficient from bounds on its
  Fréchet jets.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

/-! ## Comparison of word norms -/

section Compare

variable {ι U E : Type*} [Fintype ι] [LinearOrder ι] [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {T₁ T₂ : Type*}

/-- A word norm is at most another one when every value of the first is dominated by a value
of the second. -/
theorem wordNorm_le_of_values {D : ι → U → U} {n : ℕ} {f₁ : T₁ → U → E} {f₂ : T₂ → U → E}
    (hbdd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues False D w f₂))
    (hle : ∀ w ∈ hierarchyAdmissibleWords ι n, ∀ t x, ∃ t' x',
      ‖phaseOperatorWord D w (f₁ t) x‖ ≤ ‖phaseOperatorWord D w (f₂ t') x'‖) :
    hierarchyFiniteWordNorm False D n f₁ ≤ hierarchyFiniteWordNorm False D n f₂ := by
  refine Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ ?_
  rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
  · exact le_csSup (hbdd w hw) (Or.inl rfl)
  · obtain ⟨t', x', h⟩ := hle w hw t x
    exact h.trans (le_csSup (hbdd w hw) (Or.inr (Or.inl ⟨t', x', rfl⟩)))
  · exact hH.elim

end Compare

/-- A derivative word of a constant multiple. -/
theorem word_smul_const {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D : ι → Vec3 × ℝ → Vec3 × ℝ} (c : ℝ) {F : Vec3 × ℝ → E} (w : List ι) :
    phaseOperatorWord D w (fun x => c • F x) = c • phaseOperatorWord D w F := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change phaseDirectionalDerivative (D i) (phaseOperatorWord D w (fun x => c • F x)) =
      c • phaseDirectionalDerivative (D i) (phaseOperatorWord D w F)
    rw [ih]
    funext x
    change fderiv ℝ (c • phaseOperatorWord D w F) x (D i x) =
      c • fderiv ℝ (phaseOperatorWord D w F) x (D i x)
    rw [fderiv_const_smul_field]
    rfl

variable {T : ℝ} {k : Vec3} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The unweighted norm on `[t₀,T]` is at most the weighted norm when `0 < γ ≤ 1`. -/
theorem plain_le_wNorm (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {ℓ h : ℝ}
    {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ1 : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (n : ℕ) (f : HierarchyTwistedProfile T k E) :
    fieldNorm ℓ h n (Bridge.slices (Icc t₀ T) f) ≤ S5.wNorm ℓ h t₀ γ n f := by
  have hfin := Bridge.fieldNormFinite_weighted hT ℓ h n ht₀ htT hγc hγ f
  refine wordNorm_le_of_values hfin.2 fun w _ t x => ⟨t, x, ?_⟩
  change ‖phaseOperatorWord _ w (fun y => f.val.val.val ((t : ℝ), y)) x‖ ≤
    ‖phaseOperatorWord _ w (fun y => (γ t)⁻¹ • f.val.val.val ((t : ℝ), y)) x‖
  rw [word_smul_const, Pi.smul_apply, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hγ t t.2).le)]
  exact le_mul_of_one_le_left (norm_nonneg _) (one_le_inv₀ (hγ t t.2) |>.mpr (hγ1 t t.2))

/-- The unweighted norm on a smaller time set is smaller. -/
theorem slices_mono (hT : 0 < T) {A B : Set ℝ} (hAB : A ⊆ B) (hB : B ⊆ Icc 0 T) {ℓ h : ℝ}
    (n : ℕ) (f : HierarchyTwistedProfile T k E) :
    fieldNorm ℓ h n (Bridge.slices A f) ≤ fieldNorm ℓ h n (Bridge.slices B f) :=
  wordNorm_le_of_values (Bridge.fieldNormFinite_slices hT ℓ h n hB f).2
    fun _ _ t x => ⟨⟨t, hAB t.2⟩, x, le_rfl⟩

/-- The unweighted norm on `[t₀,T]` is at most the one on `[0,T]`. -/
theorem plain_le_uNorm (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) {ℓ h : ℝ} (n : ℕ)
    (f : HierarchyTwistedProfile T k E) :
    fieldNorm ℓ h n (Bridge.slices (Icc t₀ T) f) ≤ S5.uNorm ℓ h n f := by
  rw [Bridge.uNorm_eq_fieldNorm]
  exact slices_mono hT (Icc_subset_Icc_left ht₀) subset_rfl n f

/-- For a field vanishing before `t₀`, the unweighted norm on `[0,T]` is the one on `[t₀,T]`. -/
theorem uNorm_le_plain (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {ℓ h : ℝ} (n : ℕ)
    {f : HierarchyTwistedProfile T k E}
    (hf : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, f.val.val.val (t, x, s) = 0) :
    S5.uNorm ℓ h n f ≤ fieldNorm ℓ h n (Bridge.slices (Icc t₀ T) f) := by
  rw [Bridge.uNorm_eq_fieldNorm]
  have ht₀mem : t₀ ∈ Icc t₀ T := ⟨le_rfl, htT⟩
  refine wordNorm_le_of_values (Bridge.fieldNormFinite_slices hT ℓ h n
    (Icc_subset_Icc_left ht₀) f).2 fun w _ t x => ?_
  by_cases htt : (t : ℝ) < t₀
  · have h0 : Bridge.slices (Icc 0 T) f t = 0 := funext fun y => hf t t.2 htt y.1 y.2
    refine ⟨⟨t₀, ht₀mem⟩, x, ?_⟩
    rw [h0, word_zero, Pi.zero_apply, norm_zero]
    exact norm_nonneg _
  · exact ⟨⟨t, ⟨not_lt.mp htt, t.2.2⟩⟩, x, le_rfl⟩

/-- For a field vanishing before `t₀`, `‖f‖_{[n]} ≤ ‖f‖_{[n],γ}` when `γ ≤ 1`. -/
theorem uNorm_le_wNorm (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {ℓ h : ℝ}
    {γ : ℝ → ℝ} (hγc : ContinuousOn γ (Icc t₀ T)) (hγ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγ1 : ∀ t ∈ Icc t₀ T, γ t ≤ 1) (n : ℕ) {f : HierarchyTwistedProfile T k E}
    (hf : ∀ t ∈ Icc 0 T, t < t₀ → ∀ x s, f.val.val.val (t, x, s) = 0) :
    S5.uNorm ℓ h n f ≤ S5.wNorm ℓ h t₀ γ n f :=
  (uNorm_le_plain hT ht₀ htT n hf).trans (plain_le_wNorm hT ht₀ htT hγc hγ hγ1 n f)

/-! ## Coefficients -/

/-- **Norms of a phase-independent coefficient** from bounds on its Fréchet jets
(`ℓ^m |∇^m c(t,a)| ≤ B` for `m ≤ n`, uniformly bounded jets): the field `(t,a,s) ↦ c(t,a)` has
a finite norm (D.1) of order `n`, at most `#W_n B` (the argument of `coef_bounds` without a
functional). -/
theorem coefField_bounds {A X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : A → Vec3 → X} {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hunif : ∀ m, ∃ b, ∀ t a, ‖iteratedFDeriv ℝ m (c t) a‖ ≤ b)
    (hjet : ∀ m ≤ n, ∀ t a, ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) a‖ ≤ B) :
    FieldNormFinite ℓ h n (coefField c) ∧
      fieldNorm ℓ h n (coefField c) ≤ (hierarchyAdmissibleWords (Fin 3) n).card * B := by
  have hcoef : CoefficientNormFinite n c := by
    refine ⟨hc, fun w _ => ?_⟩
    obtain ⟨b, hb⟩ := hunif w.length
    refine ⟨max b 0, ?_⟩
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact le_max_right _ _
    · refine (norm_labelWord_le zero_le_one (hc t) w x).trans ?_
      rw [one_pow, one_mul]
      exact (hb t x).trans (le_max_left _ _)
    · exact hH.elim
  refine ⟨CoefficientNormFinite.fieldNormFinite hcoef ℓ h, ?_⟩
  change fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => c t x.1) ≤ _
  rw [fieldNorm_phaseIndependent hℓ h n hc, coefficientNorm_eq_labelWordNorm hℓ n hc]
  refine hierarchyFiniteWordNorm_sup_le hB fun w hw t x => ?_
  have hlen := (mem_hierarchyAdmissibleWords.mp hw).1
  exact (norm_labelWord_le hℓ (hc t) w x).trans (hjet _ hlen t x)

/-! ## The operators as fields -/

/-- The derivative of a slice in a label direction. -/
theorem slice_fderiv_label {F : Vec3 × ℝ → E} (hF : ContDiff ℝ ∞ F) (a : Vec3) (s : ℝ)
    (v : Vec3) : fderiv ℝ F (a, s) (v, 0) = fderiv ℝ (fun b => F (b, s)) a v := by
  have hi : HasFDerivAt (fun b : Vec3 => (b, s)) (ContinuousLinearMap.inl ℝ Vec3 ℝ) a :=
    hasFDerivAt_prodMk_left a s
  have h := ((hF.differentiable (by simp)) (a, s)).hasFDerivAt.comp a hi
  exact (congrArg (fun L : Vec3 →L[ℝ] E => L v) h.fderiv).symm

/-- The derivative within the slab in a direction without time component is the derivative of
the time slice. -/
theorem slab_fderiv_slice (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T)
    (x v : Vec3 × ℝ) :
    fderivWithin ℝ f.val (hierarchyProfileSlab T) (t, x) (0, v) =
      fderiv ℝ (fun y => f.val (t, y)) x v := by
  have hx : (t, x) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hf := ((HierarchySmoothProfile.smooth f).differentiableOn (by simp) _ hx).hasFDerivWithinAt
  have hi : HasFDerivAt (fun y : Vec3 × ℝ => (t, y)) (ContinuousLinearMap.inr ℝ ℝ (Vec3 × ℝ)) x :=
    hasFDerivAt_prodMk_right t x
  have h := hf.comp_hasFDerivAt x hi
    (Eventually.of_forall fun y => (⟨ht, mem_univ _⟩ : (t, y) ∈ hierarchyProfileSlab T))
  exact (congrArg (fun L : (Vec3 × ℝ) →L[ℝ] E => L v) h.fderiv).symm

/-- The label partial of the slices of a profile. -/
theorem labelPartial_slices {A : Set ℝ} (hA : A ⊆ Icc 0 T) (g : HierarchyTwistedProfile T k E)
    (j : Fin 3) (t : A) (a : Vec3) (s : ℝ) :
    labelPartial j (Bridge.slices A g) t (a, s) =
      fderiv ℝ (fun b => g.val.val.val ((t : ℝ), b, s)) a (coordinateDirection j) :=
  slice_fderiv_label (HierarchySmoothProfile.contDiff_labelPhase_slice g.val.val (hA t.2)) a s _

/-- The phase partial of the slices of a profile. -/
theorem phasePartial_slices {A : Set ℝ} (hA : A ⊆ Icc 0 T) (g : HierarchyTwistedProfile T k E)
    (t : A) (x : Vec3 × ℝ) :
    phasePartial (Bridge.slices A g) t x =
      fderivWithin ℝ g.val.val.val (hierarchyProfileSlab T) ((t : ℝ), x) (0, 0, 1) :=
  (slab_fderiv_slice g.val.val (hA t.2) x (0, 1)).symm

section Slices

variable {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} (d : ParentGeometry hT U X k)

/-- The coframe `(D_aX)⁻¹(t,a) = D(X(t,·)⁻¹)(X(t,a))` on a time set. -/
def coframeC (X : ℝ → Velocity) (A : Set ℝ) : A → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => fderiv ℝ (X t 0) (X 0 t a)

/-- The wave vector `κ(t,a)` on a time set. -/
def waveC (X : ℝ → Velocity) (k : Vec3) (A : Set ℝ) : A → Vec3 → Vec3 :=
  fun t a => S5.waveVector X k t a

/-- **The label advection as a field**: `(f·𝐝)g = ∑_j ((D_aX)⁻¹ f)_j ∂_{a_j} g`. -/
theorem slices_labelAdv {A : Set ℝ} (hA : A ⊆ Icc 0 T) (f g : HierarchyTwistedProfile T k Vec3) :
    Bridge.slices A ((S5.ops d).labelAdv f g) =
      slowAdv (coframeC X A) (Bridge.slices A f) (Bridge.slices A g) := by
  funext t x
  obtain ⟨a, s⟩ := x
  have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
  rw [Bridge.slices_apply, labelAdv_apply_label_fderiv hT d.inverse d.strain d.covector f g ht a s,
    d.inverse_value _ ⟨ht, mem_univ _⟩]
  simp only [slowAdv, coframeC, Bridge.slices_apply, labelPartial_slices hA]
  conv_lhs => rw [← sum_coordinate (fderiv ℝ (X (t : ℝ) 0) (X 0 t a) (f.val.val.val ((t : ℝ), a, s)))]
  rw [map_sum]
  simp only [map_smul]

/-- **The phase advection as a field**: `(f·κ)∂_s g`. -/
theorem slices_phaseAdv {A : Set ℝ} (hA : A ⊆ Icc 0 T) (f g : HierarchyTwistedProfile T k Vec3) :
    Bridge.slices A ((S5.ops d).phaseAdv f g) =
      fastAdv (waveC X k A) (Bridge.slices A f) (Bridge.slices A g) := by
  funext t x
  obtain ⟨a, s⟩ := x
  have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
  rw [Bridge.slices_apply, phaseAdv_apply_phase_fderiv hT d.inverse d.strain d.covector f g ht a s,
    d.covector_value _ ⟨ht, mem_univ _⟩]
  simp only [fastAdv, waveC, Bridge.slices_apply, phasePartial_slices hA]
  rfl

/-- **The divergence product as a field**: `(𝐝·V)Y`. -/
theorem slices_divProduct {A : Set ℝ} (hA : A ⊆ Icc 0 T) (V Y : HierarchyTwistedProfile T k Vec3) :
    Bridge.slices A (slowLabelDivergenceProduct hT d.inverse V Y) =
      divProd (coframeC X A) (Bridge.slices A V) (Bridge.slices A Y) := by
  funext t x
  obtain ⟨a, s⟩ := x
  have ht : (t : ℝ) ∈ Icc 0 T := hA t.2
  have hx : ((t : ℝ), a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [Bridge.slices_apply, slowLabelDivergenceProduct_apply hT d.inverse V Y hx]
  have hdiv : (HierarchySmoothProfile.profileLabelDivergence hT d.inverse.val.val V.val.val).val
      ((t : ℝ), a, s) = ∑ i : Fin 3, (d.inverse.val.val.val ((t : ℝ), a, s)
        (fderiv ℝ (fun b => V.val.val.val ((t : ℝ), b, s)) a (EuclideanSpace.single i 1))) i :=
    slowLabelDivergence_apply_labelRows hT d.inverse V ht a s
  rw [hdiv, d.inverse_value _ hx]
  simp only [divProd, slowDiv, coframeC, Bridge.slices_apply, labelPartial_slices hA]
  rfl

/-- **The phase average as a field.** -/
theorem slices_average {A : Set ℝ} (hA : A ⊆ Icc 0 T) (f : HierarchyTwistedProfile T k Vec3) :
    Bridge.slices A ((S5.ops d).average f) = phaseAverage (Bridge.slices A f) := by
  funext t x
  rw [Bridge.slices_apply, Bridge.ops_average_eval d f ⟨hA t.2, mem_univ _⟩]
  rfl

end Slices

end

end TorusEuler.Paper.S5b

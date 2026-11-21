import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.SBD.Vocabulary

/-!
# S5 bridge: the finite norms (D.1) and the cutoff symbol

Glue between the norms of the Section 5 statements (`S5.fieldNorm`, `S5.wNorm`,
`S5.uNorm`, `S5.launchNorm`), the library seminorms on twisted profiles
(`amplitudeSeminorm`, `unweightedSeminorm`, `boundedWeightSeminorm`,
`hierarchyLaunchSeminorm`) and the norms of the statements of Lemmas D.1–D.3
(`AppendixD.fieldNorm`, `AppendixD.weightedFieldNorm`, `AppendixD.FieldNormFinite`).
All identities are definitional unfoldings or the boundedness of the jets of a
smooth twisted profile on the compact slab; none of them is the content of a
numbered result. The last section converts the cutoff symbol of §5.7
(`S5.CutoffSymbol`) into the hypotheses of Appendix B (`AppendixB.CutoffSymbol`).
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ} {k : Vec3}

/-! ## Time slices of a profile -/

/-- The slices `t ↦ f(t, ·, ·)` of a profile, on a time set `A`, as a field on
`A × (ℝ³ × ℝ)`, in the form taken by the statements of Appendix D. -/
def slices (A : Set ℝ) (f : HierarchyTwistedProfile T k E) : A → Vec3 × ℝ → E :=
  fun t x => f.val.val.val ((t : ℝ), x)

/-- The value of `slices A f` at `(t, x)` is `f(t, x)`. -/
@[simp] theorem slices_apply (A : Set ℝ) (f : HierarchyTwistedProfile T k E) (t : A)
    (x : Vec3 × ℝ) : slices A f t x = f.val.val.val ((t : ℝ), x) := rfl

/-- The time restriction of a weight `γ` to a time set `A`. -/
def restrictWeight (A : Set ℝ) (γ : ℝ → ℝ) : A → ℝ := fun t => γ t

/-! ## `S5` norms as library seminorms -/

/-- `‖f‖_{[n],γ}` (`S5.wNorm`) is the library `amplitudeSeminorm`. -/
theorem wNorm_eq_amplitudeSeminorm (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (htT : t₀ ≤ T) (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T))
    (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t) (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n f = amplitudeSeminorm False ℓ h n hT ht₀ htT γ hγ hpos f := rfl

/-- `‖f‖_{[n],γ}` (`S5.wNorm`) is the library `boundedWeightSeminorm` with the time
multiplier `γ⁻¹` on `[t₀,T]`, for any bound `B` of `γ⁻¹`. -/
theorem wNorm_eq_boundedWeightSeminorm (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (γ : ℝ → ℝ) {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n f =
      boundedWeightSeminorm False ℓ h n hT (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹) hB f := rfl

/-- `‖f‖_{[n]}` on `[0,T]` (`S5.uNorm`) is the library `unweightedSeminorm`. -/
theorem uNorm_eq_unweightedSeminorm (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (f : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n f = unweightedSeminorm False ℓ h n hT f := rfl

/-- `‖f(t₀)‖_{[n]}` (`S5.launchNorm`) is the library `hierarchyLaunchSeminorm`. -/
theorem launchNorm_eq_hierarchyLaunchSeminorm (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) (f : HierarchyTwistedProfile T k Vec3) :
    S5.launchNorm ℓ h t₀ n f = hierarchyLaunchSeminorm hT ht₀ ℓ h n f := rfl

/-! ## `S5` norms as the norms (D.1) of Appendix D -/

/-- `S5.fieldNorm` is `AppendixD.fieldNorm` of the field multiplied by the time
multiplier, on the time set as index type. -/
theorem fieldNorm_eq_appendixD (ℓ h : ℝ) (A : Set ℝ) (τ : ℝ → ℝ) (n : ℕ)
    (f : ℝ → Vec3 × ℝ → E) :
    S5.fieldNorm ℓ h A τ n f = AppendixD.fieldNorm ℓ h n (fun (t : A) x => τ t • f t x) := rfl

/-- `S5.fieldNorm` with the multiplier `γ⁻¹` is `AppendixD.weightedFieldNorm` with
weight `γ`. -/
theorem fieldNorm_inv_eq_weightedFieldNorm (ℓ h : ℝ) (A : Set ℝ) (γ : ℝ → ℝ) (n : ℕ)
    (f : ℝ → Vec3 × ℝ → E) :
    S5.fieldNorm ℓ h A (fun t => (γ t)⁻¹) n f =
      AppendixD.weightedFieldNorm ℓ h (restrictWeight A γ) n (fun (t : A) x => f t x) := rfl

/-- `‖f‖_{[n],γ}` (`S5.wNorm`) is `‖f‖_{[n],γ}` of Appendix D on `[t₀,T]`. -/
theorem wNorm_eq_weightedFieldNorm (ℓ h t₀ : ℝ) (γ : ℝ → ℝ) (n : ℕ)
    (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n f =
      AppendixD.weightedFieldNorm ℓ h (restrictWeight (Icc t₀ T) γ) n (slices (Icc t₀ T) f) := rfl

/-- `‖f‖_{[n]}` (`S5.uNorm`) is the norm (D.1) of Appendix D on `[0,T]`. -/
theorem uNorm_eq_fieldNorm (ℓ h : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n f = AppendixD.fieldNorm ℓ h n (slices (Icc 0 T) f) := by
  unfold S5.uNorm S5.fieldNorm AppendixD.fieldNorm
  simp only [one_smul]
  rfl

/-- `‖f‖_{[n]}` (`S5.uNorm`) is the weighted norm of Appendix D with weight one. -/
theorem uNorm_eq_weightedFieldNorm_one (ℓ h : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n f =
      AppendixD.weightedFieldNorm ℓ h (fun _ : Icc 0 T => (1 : ℝ)) n (slices (Icc 0 T) f) := by
  unfold S5.uNorm S5.fieldNorm AppendixD.weightedFieldNorm AppendixD.fieldNorm AppendixD.weighted
  simp only [inv_one, one_smul]
  rfl

/-- The launch norm is the norm (D.1) of Appendix D on the one-point time set `{t₀}`. -/
theorem launchNorm_eq_fieldNorm (ℓ h t₀ : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k E) :
    S5.launchNorm ℓ h t₀ n f = AppendixD.fieldNorm ℓ h n (slices {t₀} f) := by
  unfold S5.launchNorm S5.fieldNorm AppendixD.fieldNorm
  simp only [one_smul]
  rfl

/-! ## Finiteness of the norms of a profile -/

/-- Every smooth twisted profile has bounded weighted jets on any time set `A ⊆ [0,T]`
with a bounded time multiplier `τ`: the field `τ f` has finite norms (D.1) of every
order (`AppendixD.FieldNormFinite`). -/
theorem fieldNormFinite_profile (hT : 0 < T) (ℓ h : ℝ) (n : ℕ) {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    (τ : ℝ → ℝ) {B : ℝ} (hτ : ∀ t ∈ A, ‖τ t‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    AppendixD.FieldNormFinite ℓ h n (fun (t : A) x => τ t • f.val.val.val ((t : ℝ), x)) :=
  ⟨fun t => weightedSlices_smooth hA τ f t,
    fun w _ => hierarchyTwistedMixedWord_bddAbove_weighted hT ℓ h False w f hA τ hτ⟩

/-- The field `f/γ` of a profile on `[t₀,T]` has finite norms (D.1) of every order when
`γ` is continuous and positive on `[t₀,T]`. -/
theorem fieldNormFinite_weighted (hT : 0 < T) (ℓ h : ℝ) (n : ℕ) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (htT : t₀ ≤ T) {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (f : HierarchyTwistedProfile T k E) :
    AppendixD.FieldNormFinite ℓ h n
      (AppendixD.weighted (restrictWeight (Icc t₀ T) γ) (slices (Icc t₀ T) f)) := by
  obtain ⟨B, hB⟩ := inverse_amplitude_has_bound isCompact_Icc (nonempty_Icc.mpr htT) hγ hpos
  exact fieldNormFinite_profile hT ℓ h n (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹) hB f

/-- The slices of a profile on `[0,T]` have finite norms (D.1) of every order. -/
theorem fieldNormFinite_slices (hT : 0 < T) (ℓ h : ℝ) (n : ℕ) {A : Set ℝ} (hA : A ⊆ Icc 0 T)
    (f : HierarchyTwistedProfile T k E) :
    AppendixD.FieldNormFinite ℓ h n (slices A f) := by
  have h := fieldNormFinite_profile hT ℓ h n hA (fun _ => 1) (B := 1) (by simp) f
  simp only [one_smul] at h
  exact h

/-- The weighted field `f/1` of a profile on `[0,T]` has finite norms (D.1). -/
theorem fieldNormFinite_weighted_one (hT : 0 < T) (ℓ h : ℝ) (n : ℕ) {A : Set ℝ}
    (hA : A ⊆ Icc 0 T) (f : HierarchyTwistedProfile T k E) :
    AppendixD.FieldNormFinite ℓ h n (AppendixD.weighted (fun _ : A => (1 : ℝ)) (slices A f)) := by
  have h := fieldNormFinite_slices hT ℓ h n hA f
  unfold AppendixD.weighted
  simpa only [inv_one, one_smul] using h

/-! ## Seminorm properties of the `S5` norms -/

/-- `S5.wNorm` is nonnegative (for a weight whose inverse is bounded on `[t₀,T]`). -/
theorem wNorm_nonneg (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (γ : ℝ → ℝ)
    {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    0 ≤ S5.wNorm ℓ h t₀ γ n f := by
  rw [wNorm_eq_boundedWeightSeminorm ℓ h n hT ht₀ γ hB]
  exact apply_nonneg _ _

/-- Triangle inequality for `S5.wNorm`. -/
theorem wNorm_add_le (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (γ : ℝ → ℝ)
    {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (f g : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n (f + g) ≤ S5.wNorm ℓ h t₀ γ n f + S5.wNorm ℓ h t₀ γ n g := by
  simp only [wNorm_eq_boundedWeightSeminorm ℓ h n hT ht₀ γ hB]
  exact map_add_le_add _ _ _

/-- `S5.wNorm` of a scalar multiple. -/
theorem wNorm_smul (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (γ : ℝ → ℝ)
    {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (c : ℝ) (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n (c • f) = ‖c‖ * S5.wNorm ℓ h t₀ γ n f := by
  simp only [wNorm_eq_boundedWeightSeminorm ℓ h n hT ht₀ γ hB]
  exact map_smul_eq_mul _ _ _

/-- `S5.wNorm` of a negative. -/
theorem wNorm_neg (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (γ : ℝ → ℝ)
    {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n (-f) = S5.wNorm ℓ h t₀ γ n f := by
  simp only [wNorm_eq_boundedWeightSeminorm ℓ h n hT ht₀ γ hB]
  exact map_neg_eq_map _ _

/-- `S5.wNorm` of a finite sum. -/
theorem wNorm_sum_le {ι : Type*} (s : Finset ι) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) {t₀ : ℝ}
    (ht₀ : 0 ≤ t₀) (γ : ℝ → ℝ) {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B)
    (f : ι → HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, S5.wNorm ℓ h t₀ γ n (f i) := by
  simp only [wNorm_eq_boundedWeightSeminorm ℓ h n hT ht₀ γ hB]
  exact Finset.le_sum_of_subadditive
    (⇑(boundedWeightSeminorm False ℓ h n hT (Icc_subset_Icc_left ht₀) (fun t => (γ t)⁻¹) hB))
    (map_zero _).le (map_add_le_add _) s f

/-- `S5.wNorm` is monotone in the order. -/
theorem wNorm_mono_order (ℓ h : ℝ) {n m : ℕ} (hnm : n ≤ m) (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (γ : ℝ → ℝ) {B : ℝ} (hB : ∀ t ∈ Icc t₀ T, ‖(γ t)⁻¹‖ ≤ B) (f : HierarchyTwistedProfile T k E) :
    S5.wNorm ℓ h t₀ γ n f ≤ S5.wNorm ℓ h t₀ γ m f := by
  simp only [wNorm_eq_boundedWeightSeminorm _ _ _ hT ht₀ γ hB]
  exact boundedWeightSeminorm_mono_order False ℓ h hnm hT _ _ hB f

/-- `S5.uNorm` is nonnegative. -/
theorem uNorm_nonneg (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    0 ≤ S5.uNorm ℓ h n f := by
  rw [uNorm_eq_unweightedSeminorm ℓ h n hT]
  exact apply_nonneg _ _

/-- Triangle inequality for `S5.uNorm`. -/
theorem uNorm_add_le (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) (f g : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n (f + g) ≤ S5.uNorm ℓ h n f + S5.uNorm ℓ h n g := by
  simp only [uNorm_eq_unweightedSeminorm ℓ h n hT]
  exact map_add_le_add _ _ _

/-- `S5.uNorm` of a scalar multiple. -/
theorem uNorm_smul (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) (c : ℝ) (f : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n (c • f) = ‖c‖ * S5.uNorm ℓ h n f := by
  simp only [uNorm_eq_unweightedSeminorm ℓ h n hT]
  exact map_smul_eq_mul _ _ _

/-- `S5.uNorm` of a negative. -/
theorem uNorm_neg (ℓ h : ℝ) (n : ℕ) (hT : 0 < T) (f : HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n (-f) = S5.uNorm ℓ h n f := by
  simp only [uNorm_eq_unweightedSeminorm ℓ h n hT]
  exact map_neg_eq_map _ _

/-- `S5.uNorm` of a finite sum. -/
theorem uNorm_sum_le {ι : Type*} (s : Finset ι) (ℓ h : ℝ) (n : ℕ) (hT : 0 < T)
    (f : ι → HierarchyTwistedProfile T k E) :
    S5.uNorm ℓ h n (∑ i ∈ s, f i) ≤ ∑ i ∈ s, S5.uNorm ℓ h n (f i) := by
  simp only [uNorm_eq_unweightedSeminorm ℓ h n hT]
  exact Finset.le_sum_of_subadditive (⇑(unweightedSeminorm (E := E) (k := k) False ℓ h n hT))
    (map_zero _).le (map_add_le_add _) s f

/-- `S5.uNorm` is monotone in the order. -/
theorem uNorm_mono_order (ℓ h : ℝ) {n m : ℕ} (hnm : n ≤ m) (hT : 0 < T)
    (f : HierarchyTwistedProfile T k E) : S5.uNorm ℓ h n f ≤ S5.uNorm ℓ h m f := by
  simp only [uNorm_eq_unweightedSeminorm _ _ _ hT]
  exact unweightedSeminorm_mono_order False ℓ h hnm hT f

/-- `S5.wNorm` only sees the values on the slab times `[t₀,T]`: profiles with equal values
on `[t₀,T]` have equal weighted norms. -/
theorem wNorm_congr (ℓ h t₀ : ℝ) (γ : ℝ → ℝ) (n : ℕ) {f g : HierarchyTwistedProfile T k E}
    (hfg : ∀ t ∈ Icc t₀ T, ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = g.val.val.val (t, x)) :
    S5.wNorm ℓ h t₀ γ n f = S5.wNorm ℓ h t₀ γ n g := by
  unfold S5.wNorm S5.fieldNorm
  congr 1
  funext t x
  simp only [hfg t t.property x]

/-- `S5.uNorm` only sees the values on the slab times `[0,T]`: profiles with equal values
on `[0,T]` have equal unweighted norms. -/
theorem uNorm_congr (ℓ h : ℝ) (n : ℕ) {f g : HierarchyTwistedProfile T k E}
    (hfg : ∀ t ∈ Icc 0 T, ∀ x : Vec3 × ℝ, f.val.val.val (t, x) = g.val.val.val (t, x)) :
    S5.uNorm ℓ h n f = S5.uNorm ℓ h n g := by
  unfold S5.uNorm S5.fieldNorm
  congr 1
  funext t x
  simp only [hfg t t.property x]

/-! ## Phase-independent profiles -/

/-- For a profile independent of the phase on `[0,T]` (a mean profile), the norm (D.1)
`‖B‖_{[n]}` on `[0,T]` is the coefficient norm `∑_{m≤n} ℓ_*^m |B|_m` of its phase-zero
slice (only the terms without phase derivatives occur, `appD_finite_norms.tex:22-23`). -/
theorem uNorm_eq_coefficientNorm {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ)
    {B : HierarchyTwistedProfile T k E}
    (hB : ∀ t ∈ Icc 0 T, ∀ a s, B.val.val.val (t, a, s) = B.val.val.val (t, a, 0)) :
    S5.uNorm ℓ h n B =
      AppendixD.coefficientNorm ℓ n (fun (t : Icc 0 T) a => B.val.val.val ((t : ℝ), a, 0)) := by
  rw [uNorm_eq_fieldNorm]
  have hs : slices (Icc 0 T) B = fun (t : Icc 0 T) (x : Vec3 × ℝ) =>
      (fun (t : Icc 0 T) a => B.val.val.val ((t : ℝ), a, 0)) t x.1 := by
    funext t x
    exact hB t t.property x.1 x.2
  rw [hs]
  exact AppendixD.fieldNorm_phaseIndependent hℓ h n fun t =>
    (HierarchySmoothProfile.contDiff_labelPhase_slice B.val.val t.property).comp
      (contDiff_id.prodMk contDiff_const)

/-- The same norm as the library label word norm of the phase-zero slice. -/
theorem uNorm_eq_labelWordNorm {ℓ : ℝ} (hℓ : 0 ≤ ℓ) (h : ℝ) (n : ℕ)
    {B : HierarchyTwistedProfile T k E}
    (hB : ∀ t ∈ Icc 0 T, ∀ a s, B.val.val.val (t, a, s) = B.val.val.val (t, a, 0)) :
    S5.uNorm ℓ h n B = hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n
      (fun (t : Icc 0 T) a => B.val.val.val ((t : ℝ), a, 0)) := by
  rw [uNorm_eq_coefficientNorm hℓ h n hB]
  exact AppendixD.coefficientNorm_eq_labelWordNorm hℓ n fun t =>
    (HierarchySmoothProfile.contDiff_labelPhase_slice B.val.val t.property).comp
      (contDiff_id.prodMk contDiff_const)

/-! ## The cutoff symbol -/

/-- The symbol of §5.7 (`S5.CutoffSymbol`: radial, smooth, `0 ≤ ψ ≤ 1`, `ψ = 1` on
`|ζ| ≤ 1`, `ψ = 0` for `|ζ| > 2`) satisfies the hypotheses of Appendix B
(`AppendixB.CutoffSymbol`). -/
theorem cutoffSymbol_appendixB {ψ : Vec3 → ℝ} (hψ : S5.CutoffSymbol ψ) :
    AppendixB.CutoffSymbol ψ :=
  AppendixB.CutoffSymbol.of_radial hψ.smooth hψ.radial (fun ξ => (hψ.range ξ).1)
    (fun ξ => (hψ.range ξ).2) hψ.unit hψ.support

/-- A radial symbol is even. -/
theorem CutoffSymbol.even {ψ : Vec3 → ℝ} (hψ : S5.CutoffSymbol ψ) : Function.Even ψ :=
  (cutoffSymbol_appendixB hψ).even

end

end TorusEuler.Paper.Bridge

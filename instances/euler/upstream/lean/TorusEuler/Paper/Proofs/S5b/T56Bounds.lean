import TorusEuler.Paper.Proofs.S5b.T56Ops

/-!
# Theorem 5.6, glue: the advection bounds (5.39) for profiles

The bounds (5.39) (`cc:uf:hier:eq:advection`, `sections/06c_finite_hierarchy.tex:500-512`) for
the operators `S5.ops d`, in the norms `S5.wNorm` (weighted, on `[t₀,T]`), `S5.uNorm`
(unweighted, on `[0,T]`) and the unweighted norm on `[t₀,T]` (`plain`), "with the weight on
either factor of a product or on neither", from (D.3)–(D.5) of **Lemma D.1** (`hD_1`) and
coefficient bounds `CoefBounds` for `(D_aX)⁻¹` and `κ` (supplied by Proposition 5.1 in the
proof of Theorem 5.6).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

/-- The standing data of the norms: `T, ℓ, h > 0`, `0 ≤ t₀ ≤ T`, and the weight `γ`
continuous, positive and at most one on `[t₀,T]`. -/
structure NormSetting (T ℓ h t₀ : ℝ) (γ : ℝ → ℝ) : Prop where
  hT : 0 < T
  hℓ : 0 < ℓ
  hh : 0 < h
  ht₀ : 0 ≤ t₀
  htT : t₀ ≤ T
  hγc : ContinuousOn γ (Icc t₀ T)
  hγ : ∀ t ∈ Icc t₀ T, 0 < γ t
  hγ1 : ∀ t ∈ Icc t₀ T, γ t ≤ 1

/-- Bounds `NG n`, `Nk n` for the norms (D.1) of the coefficients `(D_aX)⁻¹` and `κ` on every
time set in `[0,T]`. -/
def CoefBounds (T ℓ h : ℝ) (X : ℝ → Velocity) (k : Vec3) (NG Nk : ℕ → ℝ) : Prop :=
  ∀ A : Set ℝ, A ⊆ Icc 0 T → ∀ n : ℕ,
    (FieldNormFinite ℓ h n (coefField (coframeC X A)) ∧
      fieldNorm ℓ h n (coefField (coframeC X A)) ≤ NG n) ∧
    (FieldNormFinite ℓ h n (coefField (waveC X k A)) ∧
      fieldNorm ℓ h n (coefField (waveC X k A)) ≤ Nk n)

variable {T : ℝ} {hT' : 0 < T} {U : Velocity} {X : ℝ → Velocity} {k : Vec3}
  {ℓ h t₀ : ℝ} {γ : ℝ → ℝ}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- The unweighted norm on `[t₀,T]`. -/
abbrev plain (ℓ h t₀ : ℝ) (n : ℕ) (f : HierarchyTwistedProfile T k Vec3) : ℝ :=
  fieldNorm ℓ h n (Bridge.slices (Icc t₀ T) f)

/-- The active interval lies in `[0, T]`. -/
theorem NormSetting.active (st : NormSetting T ℓ h t₀ γ) : Icc t₀ T ⊆ Icc 0 T :=
  Icc_subset_Icc_left st.ht₀

/-- The weight of a norm setting is positive. -/
theorem NormSetting.weight_pos (st : NormSetting T ℓ h t₀ γ) :
    ∀ t : Icc t₀ T, 0 < Bridge.restrictWeight (Icc t₀ T) γ t := fun t => st.hγ t t.2

/-- Finiteness of the `W` seminorm. -/
theorem NormSetting.finW (st : NormSetting T ℓ h t₀ γ) (n : ℕ) (f : VP) :
    FieldNormFinite ℓ h n (weighted (Bridge.restrictWeight (Icc t₀ T) γ) (Bridge.slices (Icc t₀ T) f)) :=
  Bridge.fieldNormFinite_weighted st.hT ℓ h n st.ht₀ st.htT st.hγc st.hγ f

/-- Finiteness of the plain `P` seminorm. -/
theorem NormSetting.finP (st : NormSetting T ℓ h t₀ γ) (n : ℕ) (f : VP) :
    FieldNormFinite ℓ h n (Bridge.slices (Icc t₀ T) f) :=
  Bridge.fieldNormFinite_slices st.hT ℓ h n st.active f

/-- Finiteness of the `U` seminorm. -/
theorem NormSetting.finU (st : NormSetting T ℓ h t₀ γ) (n : ℕ) (f : VP) :
    FieldNormFinite ℓ h n (Bridge.slices (Icc 0 T) f) :=
  Bridge.fieldNormFinite_slices st.hT ℓ h n subset_rfl f

/-! ## Label advection -/

/-- `‖(f·𝐝)g‖_{[n],γ} ≤ c_n (c_n N_G ‖f‖_{[n]}) (3ℓ⁻¹ ‖g‖_{[n+1],γ})`, (5.39) with the weight on
the advected field. -/
theorem wNorm_labelAdv_right (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (f g : VP) :
    S5.wNorm ℓ h t₀ γ n ((S5.ops d).labelAdv f g) ≤
      productConst n * (productConst n * NG n * plain ℓ h t₀ n f) *
        (3 * ℓ⁻¹ * S5.wNorm ℓ h t₀ γ (n + 1) g) := by
  have h1 := slowAdv_right hD_1 st.hℓ st.hh st.weight_pos n (hc _ st.active n).1.1
    (hc _ st.active n).1.2 (st.finP n f) (st.finW (n + 1) g)
  rw [Bridge.wNorm_eq_weightedFieldNorm, slices_labelAdv d st.active]
  exact h1.2

/-- (5.39) for the label advection with the weight on the advecting field. -/
theorem wNorm_labelAdv_left (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (f g : VP) :
    S5.wNorm ℓ h t₀ γ n ((S5.ops d).labelAdv f g) ≤
      productConst n * (3 * ℓ⁻¹ * plain ℓ h t₀ (n + 1) g) *
        (productConst n * NG n * S5.wNorm ℓ h t₀ γ n f) := by
  have h1 := slowAdv_left hD_1 st.hℓ st.hh st.weight_pos n (hc _ st.active n).1.1
    (hc _ st.active n).1.2 (st.finW n f) (st.finP (n + 1) g)
  rw [Bridge.wNorm_eq_weightedFieldNorm, slices_labelAdv d st.active]
  exact h1.2

/-- (5.39) for the label advection without weight, on `[0,T]`. -/
theorem uNorm_labelAdv (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (f g : VP) :
    S5.uNorm ℓ h n ((S5.ops d).labelAdv f g) ≤
      productConst n * (productConst n * NG n * S5.uNorm ℓ h n f) *
        (3 * ℓ⁻¹ * S5.uNorm ℓ h (n + 1) g) := by
  have hg : FieldNormFinite ℓ h (n + 1)
      (weighted (fun _ : Icc 0 T => (1 : ℝ)) (Bridge.slices (Icc 0 T) g)) := by
    rw [weighted_one]; exact st.finU (n + 1) g
  have h1 := slowAdv_right hD_1 st.hℓ st.hh (γ := fun _ : Icc 0 T => (1 : ℝ)) (fun _ => one_pos)
    n (hc _ subset_rfl n).1.1 (hc _ subset_rfl n).1.2 (st.finU n f) hg
  simp only [weightedFieldNorm, weighted_one] at h1
  rw [Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm,
    slices_labelAdv d subset_rfl]
  exact h1.2

/-! ## Phase advection -/

/-- `‖(f·κ)∂_s g‖_{[n],γ} ≤ c_n (c_n N_κ ‖f‖_{[n]}) (h⁻¹ ‖g‖_{[n+1],γ})`, (5.39), second line. -/
theorem wNorm_phaseAdv_right (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (f g : VP) :
    S5.wNorm ℓ h t₀ γ n ((S5.ops d).phaseAdv f g) ≤
      productConst n * (productConst n * Nk n * plain ℓ h t₀ n f) *
        (h⁻¹ * S5.wNorm ℓ h t₀ γ (n + 1) g) := by
  have h1 := fastAdv_right hD_1 st.hℓ st.hh st.weight_pos n (hc _ st.active n).2.1
    (hc _ st.active n).2.2 (st.finP n f) (st.finW (n + 1) g)
  rw [Bridge.wNorm_eq_weightedFieldNorm, slices_phaseAdv d st.active]
  exact h1.2

/-- (5.39), second line, with the weight on the advecting field. -/
theorem wNorm_phaseAdv_left (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (f g : VP) :
    S5.wNorm ℓ h t₀ γ n ((S5.ops d).phaseAdv f g) ≤
      productConst n * (h⁻¹ * plain ℓ h t₀ (n + 1) g) *
        (productConst n * Nk n * S5.wNorm ℓ h t₀ γ n f) := by
  have h1 := fastAdv_left hD_1 st.hℓ st.hh st.weight_pos n (hc _ st.active n).2.1
    (hc _ st.active n).2.2 (st.finW n f) (st.finP (n + 1) g)
  rw [Bridge.wNorm_eq_weightedFieldNorm, slices_phaseAdv d st.active]
  exact h1.2

/-! ## The divergence product -/

/-- `‖(𝐝·V)Y‖_{[n]} ≤ c_n (c_n N_G 3ℓ⁻¹ ‖V‖_{[n+1]}) ‖Y‖_{[n]}` on `[0,T]`. -/
theorem uNorm_divProduct (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) {NG Nk : ℕ → ℝ} (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ)
    (V Y : VP) :
    S5.uNorm ℓ h n (slowLabelDivergenceProduct hT' d.inverse V Y) ≤
      productConst n * (productConst n * NG n * (3 * ℓ⁻¹ * S5.uNorm ℓ h (n + 1) V)) *
        S5.uNorm ℓ h n Y := by
  have hdiv := slowDiv_le_one hD_1 st.hℓ st.hh n (hc _ subset_rfl n).1.1 (hc _ subset_rfl n).1.2
    (st.finU (n + 1) V)
  have hp := prod_le_one hD_1 st.hℓ st.hh n smulCLM norm_smulCLM_le hdiv.1 (st.finU n Y)
  rw [Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm,
    slices_divProduct d subset_rfl]
  have heq : divProd (coframeC X (Icc 0 T)) (Bridge.slices (Icc 0 T) V) (Bridge.slices (Icc 0 T) Y) =
      fun t x => smulCLM (slowDiv (coframeC X (Icc 0 T)) (Bridge.slices (Icc 0 T) V) t x)
        (Bridge.slices (Icc 0 T) Y t x) := rfl
  rw [heq]
  exact hp.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdiv.2
    (productConst_nonneg n)) (fieldNorm_nonneg (st.finU n Y)))

/-! ## Phase averages -/

/-- The slices of a profile are `1`-periodic in the phase. -/
theorem slices_phasePeriodic {A : Set ℝ} (f : VP) (t : A) (a : Vec3) :
    Function.Periodic (fun s => Bridge.slices A f t (a, s)) 1 :=
  HierarchyPeriodicProfile.phasePeriodic f.val t a

/-- (D.5): `‖f - ⟨f⟩‖_{[n],γ} ≤ 2 ‖f‖_{[n],γ}`. -/
theorem wNorm_center (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (n : ℕ) (f : VP) :
    S5.wNorm ℓ h t₀ γ n (f - (S5.ops d).average f) ≤ 2 * S5.wNorm ℓ h t₀ γ n f := by
  have h1 := (average_le hD_1 st.hℓ st.hh st.weight_pos n (st.finW n f)
    (slices_phasePeriodic f)).2
  rw [Bridge.wNorm_eq_weightedFieldNorm, Bridge.wNorm_eq_weightedFieldNorm]
  have heq : Bridge.slices (Icc t₀ T) (f - (S5.ops d).average f) =
      Bridge.slices (Icc t₀ T) f - phaseAverage (Bridge.slices (Icc t₀ T) f) := by
    rw [← slices_average d st.active]
    rfl
  rw [heq]
  exact h1

/-- (D.5): `‖⟨f⟩‖_{[n]} ≤ ‖f‖_{[n]}` on `[0,T]`. -/
theorem uNorm_average (hD_1 : Statement.lemma_D_1) (st : NormSetting T ℓ h t₀ γ)
    (d : ParentGeometry hT' U X k) (n : ℕ) (f : VP) :
    S5.uNorm ℓ h n ((S5.ops d).average f) ≤ S5.uNorm ℓ h n f := by
  have hf : FieldNormFinite ℓ h n (weighted (fun _ : Icc 0 T => (1 : ℝ)) (Bridge.slices (Icc 0 T) f)) := by
    rw [weighted_one]; exact st.finU n f
  have h1 := (average_le hD_1 st.hℓ st.hh (γ := fun _ : Icc 0 T => (1 : ℝ)) (fun _ => one_pos) n hf
    (slices_phasePeriodic f)).1
  simp only [weightedFieldNorm, weighted_one] at h1
  rw [Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm, slices_average d subset_rfl]
  exact h1

end

end TorusEuler.Paper.S5b

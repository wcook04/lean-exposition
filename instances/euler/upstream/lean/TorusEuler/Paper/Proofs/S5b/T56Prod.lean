import TorusEuler.Paper.Proofs.S5b.Library.Words57

/-!
# Theorem 5.6, glue: the advection bounds (5.39) from Lemma D.1

The products of the expansion of §5.5, written as fields `f : I → Vec3 × ℝ → E` of the
statement of Lemma D.1 (`AppendixD`):

* `slowAdv G f g = ∑_j (G f)_j ∂_{a_j} g` (the label advection `(f·𝐝)g` with the coframe `G`),
* `fastAdv κ f g = (κ·f) ∂_s g` (the phase advection `(f·κ)∂_s g`),
* `slowDiv G V = ∑_i (G ∂_{a_i} V)_i` (the label divergence `𝐝·V`).

Their norms (D.1) are bounded by (D.3) and (D.4) of **Lemma D.1** (hypothesis
`hD_1 : Statement.lemma_D_1`), with the weight on either factor or on neither:
this is (5.39) (`cc:uf:hier:eq:advection`, `sections/06c_finite_hierarchy.tex:500-512`) before
the coefficient bounds of Proposition 5.1 are inserted.
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD

noncomputable section

section Prod

variable {I : Type}

/-- The weight one does nothing. -/
theorem weighted_one {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : I → Vec3 × ℝ → E) : weighted (fun _ : I => (1 : ℝ)) f = f := by
  funext t x
  simp only [weighted, inv_one, one_smul]

/-- **(D.4) of Lemma D.1** for a bilinear map of norm at most one, with the weight on the
second factor. -/
theorem prod_le (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {E F G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1) {f : I → Vec3 × ℝ → E}
    {g : I → Vec3 × ℝ → F} (hf : FieldNormFinite ℓ h n f)
    (hg : FieldNormFinite ℓ h n (weighted γ g)) :
    FieldNormFinite ℓ h n (weighted γ (fun t x => B (f t x) (g t x))) ∧
      weightedFieldNorm ℓ h γ n (fun t x => B (f t x) (g t x)) ≤
        productConst n * fieldNorm ℓ h n f * weightedFieldNorm ℓ h γ n g := by
  obtain ⟨-, hD4, -, -⟩ := hD_1 I ℓ h hℓ hh γ hγ n
  obtain ⟨hfin, hle⟩ := hD4 E F G B f g hf hg
  refine ⟨hfin, hle.trans ?_⟩
  have hc : ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) ≤
      productConst n := by
    unfold productConst
    have : 0 ≤ ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * (2 : ℝ) ^ n := by positivity
    nlinarith [norm_nonneg B]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (fieldNorm_nonneg hf))
    (fieldNorm_nonneg hg)

/-- **(D.4) of Lemma D.1** without weight (`γ ≡ 1`). -/
theorem prod_le_one (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    (n : ℕ) {E F G : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (B : E →L[ℝ] F →L[ℝ] G) (hB : ‖B‖ ≤ 1) {f : I → Vec3 × ℝ → E}
    {g : I → Vec3 × ℝ → F} (hf : FieldNormFinite ℓ h n f) (hg : FieldNormFinite ℓ h n g) :
    FieldNormFinite ℓ h n (fun t x => B (f t x) (g t x)) ∧
      fieldNorm ℓ h n (fun t x => B (f t x) (g t x)) ≤
        productConst n * fieldNorm ℓ h n f * fieldNorm ℓ h n g := by
  have hg' : FieldNormFinite ℓ h n (weighted (fun _ : I => (1 : ℝ)) g) := by rwa [weighted_one]
  have h1 := prod_le hD_1 hℓ hh (γ := fun _ : I => (1 : ℝ)) (fun _ => one_pos) n B hB hf hg'
  simp only [weightedFieldNorm, weighted_one] at h1
  exact h1

/-- **(D.3) of Lemma D.1** (label and phase derivatives). -/
theorem deriv_le (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h (n + 1) (weighted γ f)) :
    (∀ i, FieldNormFinite ℓ h n (weighted γ (labelPartial i f))) ∧
      FieldNormFinite ℓ h n (weighted γ (phasePartial f)) ∧
      (∑ i : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial i f)) ≤
        3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f ∧
      weightedFieldNorm ℓ h γ n (phasePartial f) ≤ h⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f :=
  (hD_1 I ℓ h hℓ hh γ hγ n).1 E f hf

/-- **(D.3) of Lemma D.1** without weight. -/
theorem deriv_le_one (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    (n : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h (n + 1) f) :
    (∀ i, FieldNormFinite ℓ h n (labelPartial i f)) ∧
      FieldNormFinite ℓ h n (phasePartial f) ∧
      (∑ i : Fin 3, fieldNorm ℓ h n (labelPartial i f)) ≤ 3 * ℓ⁻¹ * fieldNorm ℓ h (n + 1) f ∧
      fieldNorm ℓ h n (phasePartial f) ≤ h⁻¹ * fieldNorm ℓ h (n + 1) f := by
  have hf' : FieldNormFinite ℓ h (n + 1) (weighted (fun _ : I => (1 : ℝ)) f) := by
    rwa [weighted_one]
  have h1 := deriv_le hD_1 hℓ hh (γ := fun _ : I => (1 : ℝ)) (fun _ => one_pos) n hf'
  simp only [weightedFieldNorm, weighted_one] at h1
  exact h1

/-- **(D.5) of Lemma D.1** (the phase average and the centered part). -/
theorem average_le (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : I → Vec3 × ℝ → E}
    (hf : FieldNormFinite ℓ h n (weighted γ f))
    (hper : ∀ t a, Function.Periodic (fun s => f t (a, s)) 1) :
    weightedFieldNorm ℓ h γ n (phaseAverage f) ≤ weightedFieldNorm ℓ h γ n f ∧
      weightedFieldNorm ℓ h γ n (f - phaseAverage f) ≤ 2 * weightedFieldNorm ℓ h γ n f := by
  obtain ⟨-, -, h1, h2, -⟩ := (hD_1 I ℓ h hℓ hh γ hγ n).2.2.1 E f hf hper
  exact ⟨h1, h2⟩

/-! ## The bilinear maps -/

/-- `(M, v) ↦ (M v)_j`. -/
def rowCLM (j : Fin 3) : (Vec3 →L[ℝ] Vec3) →L[ℝ] Vec3 →L[ℝ] ℝ :=
  ContinuousLinearMap.compL ℝ Vec3 Vec3 ℝ (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)

/-- Action of the row functional on a vector. -/
@[simp] theorem rowCLM_apply (j : Fin 3) (M : Vec3 →L[ℝ] Vec3) (v : Vec3) :
    rowCLM j M v = (M v) j := rfl

/-- The row functional has norm at most one. -/
theorem norm_rowCLM_le (j : Fin 3) : ‖rowCLM j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun M => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [rowCLM_apply, one_mul]
  exact (PiLp.norm_apply_le (M v) j).trans (M.le_opNorm v)

/-- `(r, v) ↦ r v`. -/
abbrev smulCLM : ℝ →L[ℝ] Vec3 →L[ℝ] Vec3 := ContinuousLinearMap.lsmul ℝ ℝ

/-- The scalar multiplication map has norm at most one. -/
theorem norm_smulCLM_le : ‖smulCLM‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le

/-- The flipped scalar multiplication map has norm at most one. -/
theorem norm_smulCLM_flip_le : ‖smulCLM.flip‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_flip]
  exact norm_smulCLM_le

/-- `(u, v) ↦ u · v`. -/
abbrev innerCLM : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ

/-- The inner product map has norm at most one. -/
theorem norm_innerCLM_le : ‖innerCLM‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => ?_
  rw [innerSL_apply_norm, one_mul]

/-! ## The advection fields -/

/-- `(f·𝐝)g = ∑_j (G f)_j ∂_{a_j} g` for the coframe `G`. -/
def slowAdv (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (f g : I → Vec3 × ℝ → Vec3) :
    I → Vec3 × ℝ → Vec3 :=
  fun t x => ∑ j : Fin 3, (G t x.1 (f t x)) j • labelPartial j g t x

/-- `(f·κ)∂_s g`. -/
def fastAdv (κ : I → Vec3 → Vec3) (f g : I → Vec3 × ℝ → Vec3) : I → Vec3 × ℝ → Vec3 :=
  fun t x => ⟪κ t x.1, f t x⟫_ℝ • phasePartial g t x

/-- `𝐝·V = ∑_i (G ∂_{a_i} V)_i`. -/
def slowDiv (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (V : I → Vec3 × ℝ → Vec3) : I → Vec3 × ℝ → ℝ :=
  fun t x => ∑ i : Fin 3, (G t x.1 (labelPartial i V t x)) i

/-- `(𝐝·V) Y`. -/
def divProd (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (V Y : I → Vec3 × ℝ → Vec3) :
    I → Vec3 × ℝ → Vec3 :=
  fun t x => slowDiv G V t x • Y t x

/-- The coefficient field `(t,a,s) ↦ c(t,a)`. -/
def coefField {X : Type} (c : I → Vec3 → X) : I → Vec3 × ℝ → X := fun t x => c t x.1

section Bounds


/-- The slow advection term as a product of the given factors. -/
theorem slowAdv_eq (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (f g : I → Vec3 × ℝ → Vec3) :
    slowAdv G f g = ∑ j : Fin 3, fun t x =>
      smulCLM (rowCLM j (coefField G t x) (f t x)) (labelPartial j g t x) := by
  funext t x
  simp only [slowAdv, Finset.sum_apply, ContinuousLinearMap.lsmul_apply, rowCLM_apply, coefField]

/-- The slow advection term with the factors flipped. -/
theorem slowAdv_eq_flip (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (f g : I → Vec3 × ℝ → Vec3) :
    slowAdv G f g = ∑ j : Fin 3, fun t x =>
      smulCLM.flip (labelPartial j g t x) (rowCLM j (coefField G t x) (f t x)) := by
  funext t x
  simp only [slowAdv, Finset.sum_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lsmul_apply, rowCLM_apply, coefField]

/-- **Label advection, weight on the advected field** ((5.39), first line):
`‖(f·𝐝)g‖_{[n],γ} ≤ c_n (c_n N_G ‖f‖_{[n]}) (3ℓ⁻¹ ‖g‖_{[n+1],γ})`, by (D.4) for the coefficient
`(G f)_j` and for its product with `∂_{a_j} g`, and (D.3) for `∑_j ‖∂_{a_j} g‖`. -/
theorem slowAdv_right (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {NG : ℝ}
    (hG : FieldNormFinite ℓ h n (coefField G)) (hNG : fieldNorm ℓ h n (coefField G) ≤ NG)
    {f g : I → Vec3 × ℝ → Vec3} (hf : FieldNormFinite ℓ h n f)
    (hg : FieldNormFinite ℓ h (n + 1) (weighted γ g)) :
    FieldNormFinite ℓ h n (weighted γ (slowAdv G f g)) ∧
      weightedFieldNorm ℓ h γ n (slowAdv G f g) ≤
        productConst n * (productConst n * NG * fieldNorm ℓ h n f) *
          (3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) g) := by
  obtain ⟨hLfin, -, hLsum, -⟩ := deriv_le hD_1 hℓ hh hγ n hg
  have hc (j : Fin 3) := prod_le_one hD_1 hℓ hh n (rowCLM j) (norm_rowCLM_le j) hG hf
  have hp (j : Fin 3) := prod_le hD_1 hℓ hh hγ n smulCLM norm_smulCLM_le (hc j).1 (hLfin j)
  have hw : weighted γ (slowAdv G f g) = ∑ j : Fin 3, weighted γ (fun t x =>
      smulCLM (rowCLM j (coefField G t x) (f t x)) (labelPartial j g t x)) := by
    rw [slowAdv_eq, weighted_sum]
  have hfin : FieldNormFinite ℓ h n (weighted γ (slowAdv G f g)) := by
    rw [hw]
    exact fieldNormFinite_sum _ fun j _ => (hp j).1
  refine ⟨hfin, ?_⟩
  have hNG0 : 0 ≤ NG := (fieldNorm_nonneg hG).trans hNG
  have hf0 := fieldNorm_nonneg hf
  have hpc := productConst_nonneg n
  have hterm (j : Fin 3) : weightedFieldNorm ℓ h γ n (fun t x =>
      smulCLM (rowCLM j (coefField G t x) (f t x)) (labelPartial j g t x)) ≤
        productConst n * (productConst n * NG * fieldNorm ℓ h n f) *
          weightedFieldNorm ℓ h γ n (labelPartial j g) := by
    refine (hp j).2.trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hpc)
      (fieldNorm_nonneg (hLfin j))
    exact (hc j).2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNG hpc) hf0)
  calc weightedFieldNorm ℓ h γ n (slowAdv G f g)
      ≤ ∑ j : Fin 3, weightedFieldNorm ℓ h γ n (fun t x =>
          smulCLM (rowCLM j (coefField G t x) (f t x)) (labelPartial j g t x)) := by
        change fieldNorm ℓ h n (weighted γ (slowAdv G f g)) ≤ _
        rw [hw]
        exact fieldNorm_sum_le _ fun j _ => (hp j).1
    _ ≤ ∑ j : Fin 3, productConst n * (productConst n * NG * fieldNorm ℓ h n f) *
          weightedFieldNorm ℓ h γ n (labelPartial j g) := Finset.sum_le_sum fun j _ => hterm j
    _ = productConst n * (productConst n * NG * fieldNorm ℓ h n f) *
          ∑ j : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial j g) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hLsum (by positivity)

/-- **Label advection, weight on the advecting field** ((5.39), first line, weight on `Z`). -/
theorem slowAdv_left (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {NG : ℝ}
    (hG : FieldNormFinite ℓ h n (coefField G)) (hNG : fieldNorm ℓ h n (coefField G) ≤ NG)
    {f g : I → Vec3 × ℝ → Vec3} (hf : FieldNormFinite ℓ h n (weighted γ f))
    (hg : FieldNormFinite ℓ h (n + 1) g) :
    FieldNormFinite ℓ h n (weighted γ (slowAdv G f g)) ∧
      weightedFieldNorm ℓ h γ n (slowAdv G f g) ≤
        productConst n * (3 * ℓ⁻¹ * fieldNorm ℓ h (n + 1) g) *
          (productConst n * NG * weightedFieldNorm ℓ h γ n f) := by
  obtain ⟨hLfin, -, hLsum, -⟩ := deriv_le_one hD_1 hℓ hh n hg
  have hc (j : Fin 3) := prod_le hD_1 hℓ hh hγ n (rowCLM j) (norm_rowCLM_le j) hG hf
  have hp (j : Fin 3) := prod_le hD_1 hℓ hh hγ n smulCLM.flip norm_smulCLM_flip_le (hLfin j)
    (hc j).1
  have hw : weighted γ (slowAdv G f g) = ∑ j : Fin 3, weighted γ (fun t x =>
      smulCLM.flip (labelPartial j g t x) (rowCLM j (coefField G t x) (f t x))) := by
    rw [slowAdv_eq_flip, weighted_sum]
  have hfin : FieldNormFinite ℓ h n (weighted γ (slowAdv G f g)) := by
    rw [hw]
    exact fieldNormFinite_sum _ fun j _ => (hp j).1
  refine ⟨hfin, ?_⟩
  have hNG0 : 0 ≤ NG := (fieldNorm_nonneg hG).trans hNG
  have hf0 : 0 ≤ weightedFieldNorm ℓ h γ n f := fieldNorm_nonneg hf
  have hpc := productConst_nonneg n
  have hterm (j : Fin 3) : weightedFieldNorm ℓ h γ n (fun t x =>
      smulCLM.flip (labelPartial j g t x) (rowCLM j (coefField G t x) (f t x))) ≤
        productConst n * fieldNorm ℓ h n (labelPartial j g) *
          (productConst n * NG * weightedFieldNorm ℓ h γ n f) := by
    refine (hp j).2.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hpc (fieldNorm_nonneg (hLfin j)))
    exact (hc j).2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNG hpc) hf0)
  calc weightedFieldNorm ℓ h γ n (slowAdv G f g)
      ≤ ∑ j : Fin 3, weightedFieldNorm ℓ h γ n (fun t x =>
          smulCLM.flip (labelPartial j g t x) (rowCLM j (coefField G t x) (f t x))) := by
        change fieldNorm ℓ h n (weighted γ (slowAdv G f g)) ≤ _
        rw [hw]
        exact fieldNorm_sum_le _ fun j _ => (hp j).1
    _ ≤ ∑ j : Fin 3, productConst n * fieldNorm ℓ h n (labelPartial j g) *
          (productConst n * NG * weightedFieldNorm ℓ h γ n f) := Finset.sum_le_sum fun j _ => hterm j
    _ = productConst n * (∑ j : Fin 3, fieldNorm ℓ h n (labelPartial j g)) *
          (productConst n * NG * weightedFieldNorm ℓ h γ n f) := by
        rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLsum hpc) (by positivity)

/-- The fast advection term as a product of the given factors. -/
theorem fastAdv_eq (κ : I → Vec3 → Vec3) (f g : I → Vec3 × ℝ → Vec3) :
    fastAdv κ f g = fun t x => smulCLM (innerCLM (coefField κ t x) (f t x)) (phasePartial g t x) := by
  funext t x
  simp only [fastAdv, ContinuousLinearMap.lsmul_apply, coefField]
  rfl

/-- The fast advection term with the factors flipped. -/
theorem fastAdv_eq_flip (κ : I → Vec3 → Vec3) (f g : I → Vec3 × ℝ → Vec3) :
    fastAdv κ f g =
      fun t x => smulCLM.flip (phasePartial g t x) (innerCLM (coefField κ t x) (f t x)) := by
  funext t x
  simp only [fastAdv, ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, coefField]
  rfl

/-- **Phase advection, weight on the advected field** ((5.39), second line):
`‖(f·κ)∂_s g‖_{[n],γ} ≤ c_n (c_n N_κ ‖f‖_{[n]}) (h⁻¹ ‖g‖_{[n+1],γ})`. -/
theorem fastAdv_right (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {κ : I → Vec3 → Vec3} {Nk : ℝ}
    (hk : FieldNormFinite ℓ h n (coefField κ)) (hNk : fieldNorm ℓ h n (coefField κ) ≤ Nk)
    {f g : I → Vec3 × ℝ → Vec3} (hf : FieldNormFinite ℓ h n f)
    (hg : FieldNormFinite ℓ h (n + 1) (weighted γ g)) :
    FieldNormFinite ℓ h n (weighted γ (fastAdv κ f g)) ∧
      weightedFieldNorm ℓ h γ n (fastAdv κ f g) ≤
        productConst n * (productConst n * Nk * fieldNorm ℓ h n f) *
          (h⁻¹ * weightedFieldNorm ℓ h γ (n + 1) g) := by
  obtain ⟨-, hPfin, -, hPle⟩ := deriv_le hD_1 hℓ hh hγ n hg
  have hc := prod_le_one hD_1 hℓ hh n innerCLM norm_innerCLM_le hk hf
  have hp := prod_le hD_1 hℓ hh hγ n smulCLM norm_smulCLM_le hc.1 hPfin
  rw [fastAdv_eq]
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hpc := productConst_nonneg n
  have hNk0 : 0 ≤ Nk := (fieldNorm_nonneg hk).trans hNk
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hc.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hNk hpc) (fieldNorm_nonneg hf))) hpc) hPle (fieldNorm_nonneg hPfin)
    (by have := fieldNorm_nonneg hf; positivity)

/-- **Phase advection, weight on the advecting field.** -/
theorem fastAdv_left (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {κ : I → Vec3 → Vec3} {Nk : ℝ}
    (hk : FieldNormFinite ℓ h n (coefField κ)) (hNk : fieldNorm ℓ h n (coefField κ) ≤ Nk)
    {f g : I → Vec3 × ℝ → Vec3} (hf : FieldNormFinite ℓ h n (weighted γ f))
    (hg : FieldNormFinite ℓ h (n + 1) g) :
    FieldNormFinite ℓ h n (weighted γ (fastAdv κ f g)) ∧
      weightedFieldNorm ℓ h γ n (fastAdv κ f g) ≤
        productConst n * (h⁻¹ * fieldNorm ℓ h (n + 1) g) *
          (productConst n * Nk * weightedFieldNorm ℓ h γ n f) := by
  obtain ⟨-, hPfin, -, hPle⟩ := deriv_le_one hD_1 hℓ hh n hg
  have hc := prod_le hD_1 hℓ hh hγ n innerCLM norm_innerCLM_le hk hf
  have hp := prod_le hD_1 hℓ hh hγ n smulCLM.flip norm_smulCLM_flip_le hPfin hc.1
  rw [fastAdv_eq_flip]
  refine ⟨hp.1, hp.2.trans ?_⟩
  have hpc := productConst_nonneg n
  have hNk0 : 0 ≤ Nk := (fieldNorm_nonneg hk).trans hNk
  have hf0 : 0 ≤ weightedFieldNorm ℓ h γ n f := fieldNorm_nonneg hf
  exact mul_le_mul (mul_le_mul_of_nonneg_left hPle hpc) (hc.2.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hNk hpc) hf0)) (fieldNorm_nonneg hc.1)
    (mul_nonneg hpc (by have := fieldNorm_nonneg hg; positivity))

/-- The slow divergence term as a product of the given factors. -/
theorem slowDiv_eq (G : I → Vec3 → Vec3 →L[ℝ] Vec3) (V : I → Vec3 × ℝ → Vec3) :
    slowDiv G V = ∑ i : Fin 3, fun t x => rowCLM i (coefField G t x) (labelPartial i V t x) := by
  funext t x
  simp only [slowDiv, Finset.sum_apply, rowCLM_apply, coefField]

/-- **The label divergence**: `‖𝐝·V‖_{[n],γ} ≤ c_n N_G 3ℓ⁻¹ ‖V‖_{[n+1],γ}`. -/
theorem slowDiv_le (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ) {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {NG : ℝ}
    (hG : FieldNormFinite ℓ h n (coefField G)) (hNG : fieldNorm ℓ h n (coefField G) ≤ NG)
    {V : I → Vec3 × ℝ → Vec3} (hV : FieldNormFinite ℓ h (n + 1) (weighted γ V)) :
    FieldNormFinite ℓ h n (weighted γ (slowDiv G V)) ∧
      weightedFieldNorm ℓ h γ n (slowDiv G V) ≤
        productConst n * NG * (3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) V) := by
  obtain ⟨hLfin, -, hLsum, -⟩ := deriv_le hD_1 hℓ hh hγ n hV
  have hp (i : Fin 3) := prod_le hD_1 hℓ hh hγ n (rowCLM i) (norm_rowCLM_le i) hG (hLfin i)
  have hw : weighted γ (slowDiv G V) = ∑ i : Fin 3,
      weighted γ (fun t x => rowCLM i (coefField G t x) (labelPartial i V t x)) := by
    rw [slowDiv_eq, weighted_sum]
  have hfin : FieldNormFinite ℓ h n (weighted γ (slowDiv G V)) := by
    rw [hw]
    exact fieldNormFinite_sum _ fun i _ => (hp i).1
  refine ⟨hfin, ?_⟩
  have hpc := productConst_nonneg n
  have hNG0 : 0 ≤ NG := (fieldNorm_nonneg hG).trans hNG
  calc weightedFieldNorm ℓ h γ n (slowDiv G V)
      ≤ ∑ i : Fin 3, weightedFieldNorm ℓ h γ n
          (fun t x => rowCLM i (coefField G t x) (labelPartial i V t x)) := by
        change fieldNorm ℓ h n (weighted γ (slowDiv G V)) ≤ _
        rw [hw]
        exact fieldNorm_sum_le _ fun i _ => (hp i).1
    _ ≤ ∑ i : Fin 3, productConst n * NG * weightedFieldNorm ℓ h γ n (labelPartial i V) :=
        Finset.sum_le_sum fun i _ => (hp i).2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hNG hpc) (fieldNorm_nonneg (hLfin i)))
    _ = productConst n * NG * ∑ i : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial i V) := by
        rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hLsum (mul_nonneg hpc hNG0)

/-- **The label divergence without weight.** -/
theorem slowDiv_le_one (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h) (n : ℕ) {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {NG : ℝ}
    (hG : FieldNormFinite ℓ h n (coefField G)) (hNG : fieldNorm ℓ h n (coefField G) ≤ NG)
    {V : I → Vec3 × ℝ → Vec3} (hV : FieldNormFinite ℓ h (n + 1) V) :
    FieldNormFinite ℓ h n (slowDiv G V) ∧
      fieldNorm ℓ h n (slowDiv G V) ≤ productConst n * NG * (3 * ℓ⁻¹ * fieldNorm ℓ h (n + 1) V) := by
  have hV' : FieldNormFinite ℓ h (n + 1) (weighted (fun _ : I => (1 : ℝ)) V) := by
    rwa [weighted_one]
  have h1 := slowDiv_le hD_1 hℓ hh (γ := fun _ : I => (1 : ℝ)) (fun _ => one_pos) n hG hNG hV'
  simp only [weightedFieldNorm, weighted_one] at h1
  exact h1

end Bounds

end Prod

end

end TorusEuler.Paper.S5b

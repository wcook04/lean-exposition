import TorusEuler.Paper.Proofs.S5b.Library.Fields
import TorusEuler.Paper.SBD.Statements

/-!
# Glue for Lemma 5.7: the one-step estimate for `d̃` and the graph readout

The displayed one-step bound of the proof of Lemma 5.7 (`sections/08_exact_wave.tex:57-65`),
`∑_i ‖d̃_i g‖_{[n],γ} ≤ C_n 𝖣^C λ^{3/2} ‖g‖_{[n+1],γ}`, in the form
`∑_i ‖d̃_i g‖_{[n],γ} ≤ c_n (3 N_c 3ℓ⁻¹ ‖g‖_{[n+1],γ} + 3 N_k ‖∂_s g‖_{[n],γ})`, where `N_c`,
`N_k` bound the norms of the coefficients `G_{ji}`, `k·G e_i` of `d̃_i`. It is proved from the
statement of **Lemma D.1** (a hypothesis `hD_1 : Statement.lemma_D_1`): (D.4) bounds each
product of a coefficient with a derivative, (D.3) bounds the label and phase derivatives.

The iteration over words and the readout on the graph (`graph_from_words`) then give the
two bounds (5.44), (5.45) at a fixed time from the word estimate, with the bound
`sup |f(t)| ≤ γ(t) ‖f‖_{[0],γ}` (`08_exact_wave.tex:66-71`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open AppendixD

noncomputable section

/-- The constant of (D.4) for a bilinear map of norm at most one,
`#W_n · 2^n · 2` (`Statement.lemma_D_1`, (D.4)). -/
def productConst (n : ℕ) : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * 2

/-- The product constant is nonnegative. -/
theorem productConst_nonneg (n : ℕ) : 0 ≤ productConst n := by
  unfold productConst; positivity

/-- A field whose weighted field is smooth is smooth (the weight is a nonzero constant at
each time). -/
theorem smooth_of_weighted {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) {f : I → Vec3 × ℝ → E}
    (hf : ∀ t, ContDiff ℝ ∞ (weighted γ f t)) (t : I) : ContDiff ℝ ∞ (f t) := by
  have h := (hf t).const_smul (γ t)
  have he : (fun x => γ t • weighted γ f t x) = f t := by
    funext x
    simp only [weighted, smul_smul, mul_inv_cancel₀ (hγ t).ne', one_smul]
  rwa [he] at h

section Step

variable {I : Type} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **One letter of `d̃`, by Lemma D.1.** For a coframe `G` and a carrier `k`, whose
coefficients `G_{ji}` and `k·G e_i` (fields independent of the phase) have finite norms (D.1)
bounded by `Nc` and `Nk`, and a field `f` with `‖f‖_{[n+1],γ}` finite:
`d̃_i f` has a finite weighted norm and
`∑_i ‖d̃_i f‖_{[n],γ} ≤ c_n (3 Nc (3ℓ⁻¹ ‖f‖_{[n+1],γ}) + 3 Nk ‖∂_s f‖_{[n],γ})`.
Uses `hD_1` (Lemma D.1): (D.4) for each of the four products of `d̃_i f`
(`tildeWord_cons_eq`) and (D.3) for `∑_j ‖∂_{a_j} f‖_{[n],γ} ≤ 3ℓ⁻¹‖f‖_{[n+1],γ}`
(`sections/08_exact_wave.tex:57-63`). -/
theorem tilde_step (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {Nc Nk : ℝ}
    (hcL : ∀ i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc)
    (hcP : ∀ i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk)
    {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h (n + 1) (weighted γ f)) :
    (∀ i, FieldNormFinite ℓ h n (weighted γ (tildeWord G k [i] f))) ∧
      ∑ i, weightedFieldNorm ℓ h γ n (tildeWord G k [i] f) ≤
        productConst n * (3 * Nc * (3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f) +
          3 * Nk * weightedFieldNorm ℓ h γ n (phasePartial f)) := by
  obtain ⟨hD3, hD4, -, -⟩ := hD_1 I ℓ h hℓ hh γ hγ n
  obtain ⟨hLfin, hPfin, hLsum, -⟩ := hD3 E f hf
  let B : ℝ →L[ℝ] E →L[ℝ] E := ContinuousLinearMap.lsmul ℝ ℝ
  have hB : ‖B‖ ≤ 1 := ContinuousLinearMap.opNorm_lsmul_le
  let cL (i j : Fin 3) : I → Vec3 × ℝ → ℝ := fun t x => labelCoef G i j t x.1
  let cP (i : Fin 3) : I → Vec3 × ℝ → ℝ := fun t x => phaseCoef G k i t x.1
  let PL (i j : Fin 3) : I → Vec3 × ℝ → E := fun t x => B (cL i j t x) (labelPartial j f t x)
  let PP (i : Fin 3) : I → Vec3 × ℝ → E := fun t x => B (cP i t x) (phasePartial f t x)
  have hprodL (i j : Fin 3) := hD4 ℝ E E B (cL i j) (labelPartial j f) (hcL i j).1 (hLfin j)
  have hprodP (i : Fin 3) := hD4 ℝ E E B (cP i) (phasePartial f) (hcP i).1 hPfin
  have hdecomp (i : Fin 3) : tildeWord G k [i] f = (∑ j : Fin 3, PL i j) + PP i := by
    rw [tildeWord_cons_eq]
    rfl
  have hw (i : Fin 3) :
      weighted γ (tildeWord G k [i] f) = (∑ j : Fin 3, weighted γ (PL i j)) + weighted γ (PP i) := by
    rw [hdecomp, weighted_add, weighted_sum]
  have hfin (i : Fin 3) : FieldNormFinite ℓ h n (weighted γ (tildeWord G k [i] f)) := by
    rw [hw]
    exact fieldNormFinite_add (fieldNormFinite_sum _ fun j _ => (hprodL i j).1) (hprodP i).1
  refine ⟨hfin, ?_⟩
  have hc4 : ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) ≤
      productConst n := by
    unfold productConst
    have : 0 ≤ ((hierarchyAdmissibleWords (Fin 4) n).card : ℝ) * (2 : ℝ) ^ n := by positivity
    nlinarith
  have hc4' : 0 ≤ ((hierarchyAdmissibleWords (Fin 4) n).card * (2 : ℝ) ^ n * (2 * ‖B‖)) := by
    positivity
  have hNL (j : Fin 3) : 0 ≤ weightedFieldNorm ℓ h γ n (labelPartial j f) := fieldNorm_nonneg (hLfin j)
  have hNP : 0 ≤ weightedFieldNorm ℓ h γ n (phasePartial f) := fieldNorm_nonneg hPfin
  have hNc : 0 ≤ Nc := (fieldNorm_nonneg (hcL 0 0).1).trans (hcL 0 0).2
  have hNk : 0 ≤ Nk := (fieldNorm_nonneg (hcP 0).1).trans (hcP 0).2
  have hterm (i : Fin 3) : weightedFieldNorm ℓ h γ n (tildeWord G k [i] f) ≤
      productConst n * (Nc * ∑ j : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial j f) +
        Nk * weightedFieldNorm ℓ h γ n (phasePartial f)) := by
    change fieldNorm ℓ h n (weighted γ (tildeWord G k [i] f)) ≤ _
    rw [hw]
    refine (fieldNorm_add_le (fieldNormFinite_sum _ fun j _ => (hprodL i j).1) (hprodP i).1).trans ?_
    refine (add_le_add (fieldNorm_sum_le _ fun j _ => (hprodL i j).1) le_rfl).trans ?_
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun j _ => ?_) ?_
    · refine (hprodL i j).2.trans ?_
      calc _ ≤ productConst n * fieldNorm ℓ h n (cL i j) *
            weightedFieldNorm ℓ h γ n (labelPartial j f) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc4
              (fieldNorm_nonneg (hcL i j).1)) (hNL j)
        _ ≤ productConst n * Nc * weightedFieldNorm ℓ h γ n (labelPartial j f) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcL i j).2
              (productConst_nonneg n)) (hNL j)
        _ = _ := by ring
    · refine (hprodP i).2.trans ?_
      calc _ ≤ productConst n * fieldNorm ℓ h n (cP i) *
            weightedFieldNorm ℓ h γ n (phasePartial f) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc4
              (fieldNorm_nonneg (hcP i).1)) hNP
        _ ≤ productConst n * Nk * weightedFieldNorm ℓ h γ n (phasePartial f) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hcP i).2
              (productConst_nonneg n)) hNP
        _ = _ := by ring
  calc _ ≤ ∑ _i : Fin 3, productConst n * (Nc * ∑ j : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial j f) +
        Nk * weightedFieldNorm ℓ h γ n (phasePartial f)) := Finset.sum_le_sum fun i _ => hterm i
    _ = productConst n * (3 * Nc * (∑ j : Fin 3, weightedFieldNorm ℓ h γ n (labelPartial j f)) +
        3 * Nk * weightedFieldNorm ℓ h γ n (phasePartial f)) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hLsum
        (by positivity)) le_rfl) (productConst_nonneg n)

/-- **The one-step estimate for a general field** (`08_exact_wave.tex:57-65`):
`∑_i ‖d̃_i f‖_{[n],γ} ≤ c_n (9 Nc ℓ⁻¹ + 3 Nk h⁻¹) ‖f‖_{[n+1],γ}`. Uses `hD_1` through
`tilde_step` and the phase bound `‖∂_s f‖_{[n],γ} ≤ h⁻¹‖f‖_{[n+1],γ}` of (D.3). -/
theorem tilde_step_general (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {Nc Nk : ℝ}
    (hcL : ∀ i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc)
    (hcP : ∀ i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk)
    {f : I → Vec3 × ℝ → E} (hf : FieldNormFinite ℓ h (n + 1) (weighted γ f)) :
    (∀ i, FieldNormFinite ℓ h n (weighted γ (tildeWord G k [i] f))) ∧
      ∑ i, weightedFieldNorm ℓ h γ n (tildeWord G k [i] f) ≤
        productConst n * (9 * Nc * ℓ⁻¹ + 3 * Nk * h⁻¹) * weightedFieldNorm ℓ h γ (n + 1) f := by
  obtain ⟨hfin, hsum⟩ := tilde_step hD_1 hℓ hh hγ n hcL hcP hf
  obtain ⟨hD3, -, -, -⟩ := hD_1 I ℓ h hℓ hh γ hγ n
  obtain ⟨-, -, -, hphase⟩ := hD3 E f hf
  have hNk : 0 ≤ Nk := (fieldNorm_nonneg (hcP 0).1).trans (hcP 0).2
  refine ⟨hfin, hsum.trans ?_⟩
  have h3 : 3 * Nk * weightedFieldNorm ℓ h γ n (phasePartial f) ≤
      3 * Nk * (h⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f) :=
    mul_le_mul_of_nonneg_left hphase (by positivity)
  calc _ ≤ productConst n * (3 * Nc * (3 * ℓ⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f) +
        3 * Nk * (h⁻¹ * weightedFieldNorm ℓ h γ (n + 1) f)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl h3) (productConst_nonneg n)
    _ = _ := by ring

/-- **The one-step estimate for a phase-independent field**: `d̃_i f` is again phase
independent, and `∑_i ‖d̃_i f‖_{[n],γ} ≤ 9 c_n Nc ℓ⁻¹ ‖f‖_{[n+1],γ}`, since `∂_s f = 0`
(`08_exact_wave.tex:72-73`: a phase-independent field has `d̃ g₀ = d g₀`). Uses `hD_1`
through `tilde_step`. -/
theorem tilde_step_phaseIndep (hD_1 : Statement.lemma_D_1) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hh : 0 < h)
    {γ : I → ℝ} (hγ : ∀ t, 0 < γ t) (n : ℕ)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {Nc Nk : ℝ}
    (hcL : ∀ i j, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => labelCoef G i j t x.1) ≤ Nc)
    (hcP : ∀ i, FieldNormFinite ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ∧
      fieldNorm ℓ h n (fun t (x : Vec3 × ℝ) => phaseCoef G k i t x.1) ≤ Nk)
    {f : I → Vec3 × ℝ → E} (hpi : PhaseIndep f) (hf : FieldNormFinite ℓ h (n + 1) (weighted γ f)) :
    (∀ i, PhaseIndep (tildeWord G k [i] f) ∧ FieldNormFinite ℓ h n (weighted γ (tildeWord G k [i] f))) ∧
      ∑ i, weightedFieldNorm ℓ h γ n (tildeWord G k [i] f) ≤
        productConst n * (9 * Nc * ℓ⁻¹) * weightedFieldNorm ℓ h γ (n + 1) f := by
  obtain ⟨hfin, hsum⟩ := tilde_step hD_1 hℓ hh hγ n hcL hcP hf
  have hs : ∀ t, ContDiff ℝ ∞ (f t) := smooth_of_weighted hγ hf.1
  have hzero : phasePartial f = 0 := hpi.phasePartial_eq_zero hs
  have hN0 : weightedFieldNorm ℓ h γ n (phasePartial f) = 0 := by
    rw [hzero]
    change fieldNorm ℓ h n (weighted γ 0) = 0
    rw [weighted_zero, fieldNorm_zero]
  refine ⟨fun i => ⟨?_, hfin i⟩, ?_⟩
  · intro t a s
    rw [tildeWord_cons_eq]
    simp only [Pi.add_apply, Finset.sum_apply]
    have hL (j : Fin 3) := hpi.labelPartial hs j t a s
    change (∑ j : Fin 3, labelCoef G i j t a • labelPartial j f t (a, s)) +
        phaseCoef G k i t a • phasePartial f t (a, s) =
      (∑ j : Fin 3, labelCoef G i j t a • labelPartial j f t (a, 0)) +
        phaseCoef G k i t a • phasePartial f t (a, 0)
    simp only [hL, hzero, Pi.zero_apply, smul_zero]
  · refine hsum.trans (le_of_eq ?_)
    rw [hN0]
    ring

end Step

/-! ## Readout on the graph -/

section Readout

variable {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **(5.44), (5.45) at a fixed time from the word estimate.** Let `A = X(t,·)⁻¹` be smooth
with `G(A(x)) = D A(x)` for the coframe `G` at time `t`, and suppose the `d̃`-words of `f`
satisfy `∑_{|w|=m} ‖d̃_w f‖_{[0],γ} ≤ P_m ‖f‖_{[m],γ}` with finite norms. Then the graph
`F = f(t) ∘ (A, k·A)` satisfies
`∑_{|w|=m} sup |∂_w F| ≤ γ(t) P_m ‖f‖_{[m],γ}` and
`‖F‖_{C^{m,1/2}} ≤ 3(m+1) γ(t) (∑_{j≤m+1} P_j) ‖f‖_{[m+1],γ}`
(`08_exact_wave.tex:55-71`: the chain rule (3.1), `sup |g(t)| ≤ γ(t)‖g‖_{[0],γ}`, and the
Hölder bound by one more derivative). -/
theorem graph_from_words {ℓ h : ℝ} {γ : I → ℝ} (hγ : ∀ t, 0 < γ t)
    {G : I → Vec3 → Vec3 →L[ℝ] Vec3} {k : Vec3} {f : I → Vec3 × ℝ → E}
    (hfin : ∀ n, FieldNormFinite ℓ h n (weighted γ f)) {P : ℕ → ℝ} (hP : ∀ m, 0 ≤ P m)
    (hW : ∀ m, (∀ w : Fin m → Fin 3, FieldNormFinite ℓ h 0 (weighted γ (tildeWord G k (List.ofFn w) f))) ∧
      ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) ≤
        P m * weightedFieldNorm ℓ h γ m f)
    (t : I) {A : Vec3 → Vec3} (hA : ContDiff ℝ ∞ A) (hG : ContDiff ℝ ∞ (G t))
    (hGA : ∀ x, G t (A x) = fderiv ℝ A x) (m : ℕ) :
    let F := f t ∘ graphPoint A k
    (∑ w : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn w) F)) ≤
        γ t * P m * weightedFieldNorm ℓ h γ m f ∧
      SpatialHolderHalf m F ∧
      spatialHolderHalfNorm m F ≤
        (3 * (m + 1) : ℝ) * (γ t * (∑ j ∈ Finset.range (m + 2), P j) *
          weightedFieldNorm ℓ h γ (m + 1) f) := by
  intro F
  have hs : ∀ t, ContDiff ℝ ∞ (f t) := smooth_of_weighted hγ (hfin 0).1
  have hF : ContDiff ℝ ∞ F := (hs t).comp (graphPoint_smooth hA k)
  have hγt := (hγ t).le
  have hNn (n : ℕ) : 0 ≤ weightedFieldNorm ℓ h γ n f := fieldNorm_nonneg (hfin n)
  -- the pointwise value of a word of `F` at `x`
  have hword (j : ℕ) (w : Fin j → Fin 3) (x : Vec3) :
      ‖spatialDerivativeWord (List.ofFn w) F x‖ ≤
        γ t * weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) := by
    have hg := spatialDerivativeWord_graph hA hG hGA k (hs t) (List.ofFn w)
    rw [show spatialDerivativeWord (List.ofFn w) F x =
      (phaseOperatorWord (tildeDirection (G t) k) (List.ofFn w) (f t) ∘ graphPoint A k) x from
        congrFun hg x]
    exact norm_le_weight_mul_weightedFieldNorm hγ ((hW j).1 w) t _
  -- the word sums
  have hsum (j : ℕ) (x : Vec3) :
      (∑ w : Fin j → Fin 3, ‖spatialDerivativeWord (List.ofFn w) F x‖) ≤
        γ t * P j * weightedFieldNorm ℓ h γ j f := by
    calc _ ≤ ∑ w : Fin j → Fin 3, γ t * weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) :=
          Finset.sum_le_sum fun w _ => hword j w x
      _ = γ t * ∑ w : Fin j → Fin 3, weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) := by
          rw [Finset.mul_sum]
      _ ≤ γ t * (P j * weightedFieldNorm ℓ h γ j f) := mul_le_mul_of_nonneg_left (hW j).2 hγt
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · calc _ ≤ ∑ w : Fin m → Fin 3, γ t * weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) :=
          Finset.sum_le_sum fun w _ => ciSup_le fun x => hword m w x
      _ = γ t * ∑ w : Fin m → Fin 3, weightedFieldNorm ℓ h γ 0 (tildeWord G k (List.ofFn w) f) := by
          rw [Finset.mul_sum]
      _ ≤ γ t * (P m * weightedFieldNorm ℓ h γ m f) := mul_le_mul_of_nonneg_left (hW m).2 hγt
      _ = _ := by ring
  · have hB : 0 ≤ γ t * (∑ j ∈ Finset.range (m + 2), P j) * weightedFieldNorm ℓ h γ (m + 1) f :=
      mul_nonneg (mul_nonneg hγt (Finset.sum_nonneg fun j _ => hP j)) (hNn _)
    refine spatialHolderHalfNorm_le_of_uniformJets hF hB fun j hj x => ?_
    refine (norm_iteratedFDeriv_le_sum_words hF j x).trans ((hsum j x).trans ?_)
    have hPj : P j ≤ ∑ i ∈ Finset.range (m + 2), P i :=
      Finset.single_le_sum (fun i _ => hP i) (Finset.mem_range.mpr (by omega))
    have hmono : weightedFieldNorm ℓ h γ j f ≤ weightedFieldNorm ℓ h γ (m + 1) f :=
      hierarchyFiniteWordNorm_mono_order False hj (hfin (m + 1)).2
    exact mul_le_mul (mul_le_mul_of_nonneg_left hPj hγt) hmono (hNn j)
      (mul_nonneg hγt (Finset.sum_nonneg fun i _ => hP i))

end Readout

end

end TorusEuler.Paper.S5b

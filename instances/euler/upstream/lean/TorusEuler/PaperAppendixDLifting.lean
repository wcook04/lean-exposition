import TorusEuler.HierarchyProductEstimates
import TorusEuler.MeanDerivativeLifting
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! The abstract weighted derivative lifting of Lemma D.3. -/

namespace TorusEuler

section WordDerivatives

variable {I E : Type*} [AddCommGroup E] [Module ℝ E]

/-- Apply coordinate derivative maps in word order, with the outermost
derivative first. The maps can already include coordinate weights. -/
def appendixDerivativeWord (D : I → E →ₗ[ℝ] E) : List I → E →ₗ[ℝ] E
  | [] => LinearMap.id
  | i :: w => (D i).comp (appendixDerivativeWord D w)

@[simp] theorem appendixDerivativeWord_nil (D : I → E →ₗ[ℝ] E) (u : E) :
    appendixDerivativeWord D [] u = u := rfl

@[simp] theorem appendixDerivativeWord_cons (D : I → E →ₗ[ℝ] E) (i : I) (w : List I) (u : E) :
    appendixDerivativeWord D (i :: w) u = D i (appendixDerivativeWord D w u) := rfl

/-- Multiplying each coordinate derivative by its weight multiplies the
whole derivative by the product of its letter weights. -/
theorem appendixDerivativeWord_scaled (D : I → E →ₗ[ℝ] E) (r : I → ℝ) (w : List I) (u : E) :
    appendixDerivativeWord (fun i => r i • D i) w u = (w.map r).prod • appendixDerivativeWord D w u := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simp only [appendixDerivativeWord_cons, LinearMap.smul_apply, ih, map_smul, List.map_cons,
      List.prod_cons, mul_smul]
    simp only [smul_smul, mul_comm]

/-- Commuting coordinate derivatives can be put into sorted word order. -/
theorem appendixDerivativeWord_perm (D : I → E →ₗ[ℝ] E)
    (hc : ∀ i j u, D i (D j u) = D j (D i u))
    {w w' : List I} (h : w.Perm w') (u : E) :
    appendixDerivativeWord D w u = appendixDerivativeWord D w' u := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp only [appendixDerivativeWord_cons, ih]
  | swap i j w => simp only [appendixDerivativeWord_cons, hc j i]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The exact finite norm consists of one word for each mixed multi-index.
The zeroth-order seminorm can be the weighted sup norm or the Hölder norm. -/
noncomputable def appendixFiniteDerivativeNorm [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (n : ℕ) (u : E) : ℝ :=
  ∑ w ∈ hierarchyAdmissibleWords I n, p (appendixDerivativeWord D w u)

/-- The weighted word norm is the corresponding sum of unweighted jets
multiplied by their coordinate weights, as in (D.1). -/
theorem appendixFiniteDerivativeNorm_scaled [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (r : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (n : ℕ) (u : E) :
    appendixFiniteDerivativeNorm p (fun i => r i • D i) n u =
      ∑ w ∈ hierarchyAdmissibleWords I n, (w.map r).prod * p (appendixDerivativeWord D w u) := by
  have h (l : List I) : 0 ≤ (l.map r).prod := by
    induction l with
    | nil => simp
    | cons i l ih => exact mul_nonneg (hr i) ih
  unfold appendixFiniteDerivativeNorm
  apply Finset.sum_congr rfl
  intro w _
  rw [appendixDerivativeWord_scaled, map_smul_eq_mul, Real.norm_of_nonneg (h w)]

private theorem nonneg_appendixFiniteDerivativeNorm [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (n : ℕ) (u : E) :
    0 ≤ appendixFiniteDerivativeNorm p D n u :=
  Finset.sum_nonneg fun _ _ => apply_nonneg p _

private theorem seminorm_word_le_appendixFiniteDerivativeNorm [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (hc : ∀ i j u, D i (D j u) = D j (D i u))
    (n : ℕ) (u : E) (w : List I) (hw : w.length ≤ n) :
    p (appendixDerivativeWord D w u) ≤ appendixFiniteDerivativeNorm p D n u := by
  let z := w.mergeSort (fun i j => decide (i ≤ j))
  have hperm : z.Perm w := List.mergeSort_perm _ _
  have hmem : z ∈ hierarchyAdmissibleWords I n :=
    mem_hierarchyAdmissibleWords.mpr
      ⟨hperm.length_eq.trans_le hw, List.pairwise_mergeSort' _ _⟩
  rw [← appendixDerivativeWord_perm D hc hperm u]
  exact Finset.single_le_sum (f := fun w => p (appendixDerivativeWord D w u))
    (fun _ _ => apply_nonneg p _) hmem

/-- The coefficient size at one order sums its distinct coordinate
derivatives of that order. The derivative maps carry the scale factors. -/
noncomputable def appendixExactOrderDerivativeNorm [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (m : ℕ) (u : E) : ℝ :=
  ∑ w ∈ (hierarchyAdmissibleWords I m).filter (fun w => w.length = m), p (appendixDerivativeWord D w u)

theorem seminorm_word_le_appendixExactOrderDerivativeNorm [Fintype I] [LinearOrder I]
    (p : Seminorm ℝ E) (D : I → E →ₗ[ℝ] E) (hc : ∀ i j u, D i (D j u) = D j (D i u))
    (u : E) (w : List I) :
    p (appendixDerivativeWord D w u) ≤ appendixExactOrderDerivativeNorm p D w.length u := by
  let z := w.mergeSort (fun i j => decide (i ≤ j))
  have hperm : z.Perm w := List.mergeSort_perm _ _
  have hmem : z ∈ (hierarchyAdmissibleWords I w.length).filter (fun w' => w'.length = w.length) :=
    Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
      ⟨hperm.length_eq.le, List.pairwise_mergeSort' _ _⟩, hperm.length_eq⟩
  conv_lhs => rw [← appendixDerivativeWord_perm D hc hperm u]
  exact Finset.single_le_sum (f := fun w => p (appendixDerivativeWord D w u))
    (fun _ _ => apply_nonneg p _) hmem

end WordDerivatives

section DerivativeLifting

variable {I J A E F : Type*}
  [AddCommGroup A] [Module ℝ A] [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

variable (DA : I → A →ₗ[ℝ] A) (DE : I → E →ₗ[ℝ] E) (DF : I → F →ₗ[ℝ] F)

private theorem appendixDerivativeWord_linear_commute (L₀ : E →ₗ[ℝ] F)
    (hComm : ∀ i v, DF i (L₀ v) = L₀ (DE i v)) (w : List I) (v : E) :
    appendixDerivativeWord DF w (L₀ v) = L₀ (appendixDerivativeWord DE w v) := by
  induction w with
  | nil => rfl
  | cons i w ih => simp only [appendixDerivativeWord_cons, ih, hComm]

/-- Differentiate the coefficient action. All Leibniz terms apart from
the original coefficient action have a positive coefficient order. -/
theorem appendixDerivativeWord_coefficientAction (B : A →ₗ[ℝ] E →ₗ[ℝ] F)
    (hProduct : ∀ i a v, DF i (B a v) = B (DA i a) v + B a (DE i v))
    (w : List I) (a : A) (v : E) :
    appendixDerivativeWord DF w (B a v) =
      B a (appendixDerivativeWord DE w v) +
        ((endpointMixedCorrectionPairs w).map fun p =>
          B (appendixDerivativeWord DA p.1 a) (appendixDerivativeWord DE p.2 v)).sum := by
  induction w with
  | nil => simp [endpointMixedCorrectionPairs]
  | cons i w ih =>
    simp only [appendixDerivativeWord_cons, ih, map_add, hProduct]
    rw [endpointMixedCorrectionPairs_sum_cons]
    let corr (p : List I × List I) :=
      B (appendixDerivativeWord DA p.1 a) (appendixDerivativeWord DE p.2 v)
    have hMap : DF i ((endpointMixedCorrectionPairs w).map corr).sum =
        ((endpointMixedCorrectionPairs w).map fun p => corr (i :: p.1, p.2) + corr (p.1, i :: p.2)).sum := by
      rw [map_list_sum, List.map_map]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      exact hProduct i _ _
    rw [hMap]
    simp only [appendixDerivativeWord_cons, appendixDerivativeWord_nil, corr]
    abel

omit [Module ℝ F] in
private theorem appendix_sum_list_sum [Fintype J] (l : List (List I × List I))
    (f : J → List I × List I → F) :
    (∑ j, (l.map (f j)).sum) = (l.map fun p => ∑ j, f j p).sum := by
  induction l with
  | nil => simp
  | cons p l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]

/-- The differentiated equation underlying Lemma D.3. Coefficient
actions already include the operators applied after multiplication. -/
theorem appendixDerivativeWord_equation [Fintype J]
    (L₀ : E →ₗ[ℝ] F) (B : J → A →ₗ[ℝ] E →ₗ[ℝ] F) (c : J → A) {v : E} {f : F}
    (hComm : ∀ i u, DF i (L₀ u) = L₀ (DE i u))
    (hProduct : ∀ j i a u, DF i (B j a u) = B j (DA i a) u + B j a (DE i u))
    (hEq : L₀ v + ∑ j, B j (c j) v = f) (w : List I) :
    L₀ (appendixDerivativeWord DE w v) + ∑ j, B j (c j) (appendixDerivativeWord DE w v) =
      appendixDerivativeWord DF w f - ((endpointMixedCorrectionPairs w).map fun p =>
        ∑ j, B j (appendixDerivativeWord DA p.1 (c j)) (appendixDerivativeWord DE p.2 v)).sum := by
  apply eq_sub_of_add_eq
  rw [← appendix_sum_list_sum, add_assoc, ← Finset.sum_add_distrib]
  simp_rw [← appendixDerivativeWord_coefficientAction DA DE DF _ (hProduct _)]
  rw [← appendixDerivativeWord_linear_commute DE DF L₀ hComm w v,
    ← map_sum, ← map_add, hEq]

private theorem seminorm_listSum_le (p : Seminorm ℝ F) {α : Type*} (l : List α) (g : α → F) :
    p (l.map g).sum ≤ (l.map fun x => p (g x)).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simpa only [List.map_cons, List.sum_cons] using
      (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

private theorem seminorm_finsetSum_le (p : Seminorm ℝ F) {α : Type*} (s : Finset α) (g : α → F) :
    p (∑ x ∈ s, g x) ≤ ∑ x ∈ s, p (g x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    simp only [Finset.sum_insert hx]
    exact (map_add_le_add p _ _).trans (add_le_add le_rfl ih)

variable [Fintype I] [LinearOrder I] [Fintype J]

/-- The slow-coefficient bound for the whole order implies the bound for
each word required in the derivative recursion. -/
theorem appendixSlowCoefficient_word_le (pA : Seminorm ℝ A)
    (hComm : ∀ i j a, DA i (DA j a) = DA j (DA i a))
    (c : J → A) (b : J → ℝ) (hb : ∀ j, 0 ≤ b j)
    {low S : ℝ} (hLow : 0 ≤ low) (w : List I)
    (hSlow : low * (∑ j, b j * appendixExactOrderDerivativeNorm pA DA w.length (c j)) ≤ S) :
    low * (∑ j, b j * pA (appendixDerivativeWord DA w (c j))) ≤ S := by
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) hLow).trans hSlow
  exact mul_le_mul_of_nonneg_left (seminorm_word_le_appendixExactOrderDerivativeNorm pA DA hComm (c j) w)
    (hb j)

/-- Lemma D.3. The solution space can impose the invariant linear
constraints, and the forcing space can combine the quotient equation
with differentiated data. The derivative maps include the label and
phase weights. For a phase-independent coefficient the positive-order
phase words vanish, so the slow-coefficient hypothesis asks only for
the weighted label derivatives. -/
theorem paperLemmaD3_lifting (n : ℕ)
    (pA : Seminorm ℝ A) (pE : Seminorm ℝ E) (pF : Seminorm ℝ F)
    (L₀ : E →ₗ[ℝ] F) (B : J → A →ₗ[ℝ] E →ₗ[ℝ] F) (c : J → A)
    (hComm : ∀ i u, DF i (L₀ u) = L₀ (DE i u))
    (hProduct : ∀ j i a u, DF i (B j a u) = B j (DA i a) u + B j a (DE i u))
    (hForcingCommutes : ∀ i j g, DF i (DF j g) = DF j (DF i g))
    (b : J → ℝ) (hB : ∀ j a u, pF (B j a u) ≤ b j * pA a * pE u)
    {low : ℝ} (hLow : 0 ≤ low)
    (hInverse : ∀ u, pE u ≤ low * pF (L₀ u + ∑ j, B j (c j) u))
    (slow : ℕ → ℝ) (hSlow : ∀ m, 0 ≤ slow m)
    (hCoefficient : ∀ w : List I, 1 ≤ w.length → w.length ≤ n →
      low * (∑ j, b j * pA (appendixDerivativeWord DA w (c j))) ≤ slow w.length)
    {v : E} {f : F} (hEq : L₀ v + ∑ j, B j (c j) v = f) :
    let C := ∑ i ∈ Finset.range (n + 1), slow i
    let G := 1 + (2 : ℝ) ^ n * C
    appendixFiniteDerivativeNorm pE DE n v ≤
      ((hierarchyAdmissibleWords I n).card * G ^ n) * low * appendixFiniteDerivativeNorm pF DF n f := by
  let C := ∑ i ∈ Finset.range (n + 1), slow i
  let G := 1 + (2 : ℝ) ^ n * C
  let M := appendixFiniteDerivativeNorm pF DF n f
  let V := fun w => pE (appendixDerivativeWord DE w v)
  let Fsize := fun w => pF (appendixDerivativeWord DF w f)
  let Bsize := fun w => ∑ j, b j * pA (appendixDerivativeWord DA w (c j))
  have hC : 0 ≤ C := Finset.sum_nonneg fun i _ => hSlow i
  have hG : 1 ≤ G := le_add_of_nonneg_right (mul_nonneg (by positivity) hC)
  have hM : 0 ≤ M := nonneg_appendixFiniteDerivativeNorm pF DF n f
  have hRec (w : List I) :
      V w ≤ low * (Fsize w + ((endpointMixedCorrectionPairs w).map
        fun p => Bsize p.1 * V p.2).sum) := by
    let correction (p : List I × List I) :=
      ∑ j, B j (appendixDerivativeWord DA p.1 (c j)) (appendixDerivativeWord DE p.2 v)
    have hTerm (p : List I × List I) : pF (correction p) ≤ Bsize p.1 * V p.2 := by
      apply (seminorm_finsetSum_le pF Finset.univ _).trans
      unfold Bsize V
      rw [Finset.sum_mul]
      exact Finset.sum_le_sum fun j _ => hB j _ _
    have hNorm :
        pF ((endpointMixedCorrectionPairs w).map correction).sum ≤
          ((endpointMixedCorrectionPairs w).map fun p => Bsize p.1 * V p.2).sum :=
      (seminorm_listSum_le pF _ correction).trans
        (List.sum_le_sum fun p _ => hTerm p)
    apply (hInverse (appendixDerivativeWord DE w v)).trans
    rw [appendixDerivativeWord_equation DA DE DF L₀ B c hComm hProduct hEq w]
    apply mul_le_mul_of_nonneg_left _ hLow
    exact (map_sub_le_add pF _ _).trans (add_le_add le_rfl hNorm)
  have hWord (w : List I) (hw : w.length ≤ n) :
      V w ≤ low * M * G ^ w.length := by
    have h := meanDerivativeLifting n V Fsize Bsize (ℓ := 1) (A := low) (C := C) (M := M)
      zero_le_one hLow hM hC (fun _ => apply_nonneg pE _)
      (fun s hs => by
        simpa only [one_pow, one_mul] using
          seminorm_word_le_appendixFiniteDerivativeNorm pF DF hForcingCommutes n f s hs)
      (fun s hs hs' => by
        simpa only [one_pow, one_mul] using (hCoefficient s hs hs').trans
          (Finset.single_le_sum (f := slow) (fun i _ => hSlow i)
            (Finset.mem_range.mpr (Nat.lt_succ_of_le hs'))))
      (fun s _ => hRec s) w hw
    simpa only [one_pow, one_mul, G] using h
  change (∑ w ∈ hierarchyAdmissibleWords I n, V w) ≤
    ((hierarchyAdmissibleWords I n).card * G ^ n) * low * M
  calc
    _ ≤ ∑ _ ∈ hierarchyAdmissibleWords I n, low * M * G ^ n := by
      apply Finset.sum_le_sum
      intro w hw
      have hlen := (mem_hierarchyAdmissibleWords.mp hw).1
      exact (hWord w hlen).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ hG hlen) (mul_nonneg hLow hM))
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]; ring

end DerivativeLifting

end TorusEuler

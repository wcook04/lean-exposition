import TorusEuler.PhaseJetBounds
import TorusEuler.HalfHolderSpace

/-! Leibniz's rule at finite weighted order for (D.4) and the strict
order decrease used in the differentiated equations of Lemma D.3. -/

open scoped ContDiff

namespace TorusEuler

/-- Assign each derivative in an ordered word to one of the two factors.
The list retains multiplicity when equal coordinate directions recur. -/
def hierarchyLeibnizSplits {ι : Type*} : List ι → List (List ι × List ι)
  | [] => [([], [])]
  | i :: w =>
    (hierarchyLeibnizSplits w).map (fun p => (i :: p.1, p.2)) ++
    (hierarchyLeibnizSplits w).map (fun p => (p.1, i :: p.2))

theorem hierarchyLeibnizSplits_spec {ι : Type*} {w : List ι} {p : List ι × List ι}
    (hp : p ∈ hierarchyLeibnizSplits w) :
    List.Sublist p.1 w ∧ List.Sublist p.2 w ∧ p.1.length + p.2.length = w.length := by
  induction w generalizing p with
  | nil =>
    simp only [hierarchyLeibnizSplits, List.mem_singleton] at hp
    subst p
    exact ⟨.refl _, .refl _, rfl⟩
  | cons i w ih =>
    simp only [hierarchyLeibnizSplits, List.mem_append, List.mem_map] at hp
    rcases hp with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · obtain ⟨h₁, h₂, hlen⟩ := ih hq
      exact ⟨h₁.cons_cons i, h₂.cons i, by simp only [List.length_cons]; omega⟩
    · obtain ⟨h₁, h₂, hlen⟩ := ih hq
      exact ⟨h₁.cons i, h₂.cons_cons i, by simp only [List.length_cons]; omega⟩

/-- A term with a derivative on the coefficient leaves a strictly lower
order derivative of the other factor, within the specified order budget. -/
theorem hierarchyLeibnizSplits_order_lt {ι : Type*} {w : List ι} {p : List ι × List ι}
    (hp : p ∈ hierarchyLeibnizSplits w) (hn : p.1 ≠ []) :
    p.2.length < w.length := by
  have hlen := (hierarchyLeibnizSplits_spec hp).2.2
  have hpos := List.length_pos_iff.mpr hn
  omega

@[simp] theorem length_hierarchyLeibnizSplits {ι : Type*} (w : List ι) :
    (hierarchyLeibnizSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons i w ih => simp [hierarchyLeibnizSplits, ih, pow_succ, Nat.mul_two]

private theorem hierarchyLeibnizSplits_append_undifferentiated {ι : Type*} (w : List ι) :
    hierarchyLeibnizSplits w =
      (hierarchyLeibnizSplits w).filter (fun p => !p.1.isEmpty) ++ [([], w)] := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    let s := hierarchyLeibnizSplits w
    let left (p : List ι × List ι) := (i :: p.1, p.2)
    let right (p : List ι × List ι) := (p.1, i :: p.2)
    let keep (p : List ι × List ι) := !p.1.isEmpty
    simp only [hierarchyLeibnizSplits, List.filter_append, List.filter_map]
    change s.map left ++ s.map right =
      (s.filter (fun _ => true)).map left ++ (s.filter keep).map right ++ [([], i :: w)]
    rw [List.filter_true, show s.map right = ((s.filter keep) ++ [([], w)]).map right from
      congrArg (List.map right) ih, List.map_append, List.append_assoc]
    rfl

section ProductRule

variable {ι U E F G : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem contDiff_listSum {α : Type*} (l : List α) (f : α → U → G)
    (hf : ∀ i, ContDiff ℝ ∞ (f i)) :
    ContDiff ℝ ∞ (fun x => (l.map fun i => f i x).sum) := by
  induction l with
  | nil => exact contDiff_const
  | cons i l ih => exact (hf i).add ih

private theorem directionalDerivative_listSum {α : Type*} (d : U → U) (l : List α)
    (f : α → U → G) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (x : U) :
    phaseDirectionalDerivative d (fun y => (l.map fun i => f i y).sum) x =
      (l.map fun i => phaseDirectionalDerivative d (f i) x).sum := by
  induction l with
  | nil => simp [phaseDirectionalDerivative]
  | cons i l ih =>
    change fderiv ℝ (f i + fun y => (l.map fun j => f j y).sum) x (d x) = _
    rw [fderiv_add ((hf i).differentiable (by simp) x)
      ((contDiff_listSum l f hf).differentiable (by simp) x)]
    exact congrArg ((phaseDirectionalDerivative d (f i) x) + ·) ih

private theorem directionalDerivative_bilinear (B : E →L[ℝ] F →L[ℝ] G)
    {f : U → E} {g : U → F} {x : U} (hf : DifferentiableAt ℝ f x)
    (hg : DifferentiableAt ℝ g x)
    (d : U → U) :
    phaseDirectionalDerivative d (fun y => B (f y) (g y)) x =
      B (phaseDirectionalDerivative d f x) (g x) +
        B (f x) (phaseDirectionalDerivative d g x) := by
  have h := (B.hasFDerivAt.comp x hf.hasFDerivAt).clm_apply hg.hasFDerivAt
  change HasFDerivAt (fun y => B (f y) (g y)) _ x at h
  unfold phaseDirectionalDerivative
  rw [h.fderiv]
  exact add_comm _ _

/-- Exact ordered Leibniz formula for a real continuous bilinear operator,
including application of an operator-valued coefficient to a vector field. -/
theorem phaseOperatorWord_bilinear (B : E →L[ℝ] F →L[ℝ] G)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} {g : U → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (x : U) :
    phaseOperatorWord D w (fun y => B (f y) (g y)) x =
      ((hierarchyLeibnizSplits w).map fun p =>
        B (phaseOperatorWord D p.1 f x) (phaseOperatorWord D p.2 g x)).sum := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord, hierarchyLeibnizSplits]
  | cons i w ih =>
    change phaseDirectionalDerivative (D i) (phaseOperatorWord D w (fun y => B (f y) (g y))) x = _
    rw [funext ih, directionalDerivative_listSum]
    · simp only [hierarchyLeibnizSplits, List.map_append, List.sum_append, List.map_map,
        Function.comp_apply, phaseOperatorWord, ← List.sum_map_add]
      apply congrArg List.sum
      apply List.map_congr_left
      intro p _
      exact directionalDerivative_bilinear B
        ((contDiff_phaseOperatorWord hD hf p.1).differentiable (by simp) x)
        ((contDiff_phaseOperatorWord hD hg p.2).differentiable (by simp) x) (D i)
    · intro p
      exact (B.contDiff.comp (contDiff_phaseOperatorWord hD hf p.1)).clm_apply
        (contDiff_phaseOperatorWord hD hg p.2)

/-- Scaling the directions multiplies a word derivative by the product of
its coordinate weights. This supplies the weights `ℓ^m * h^j` of (D.1). -/
theorem phaseOperatorWord_scaled_directions (r : ι → ℝ)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} (hf : ContDiff ℝ ∞ f) (w : List ι) (x : U) :
    phaseOperatorWord (fun i y => r i • D i y) w f x =
      (w.map r).prod • phaseOperatorWord D w f x := by
  induction w generalizing x with
  | nil => simp [phaseOperatorWord]
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord (fun i y => r i • D i y) w f) x (r i • D i x) =
      (r i * (w.map r).prod) • fderiv ℝ (phaseOperatorWord D w f) x (D i x)
    rw [funext ih, fderiv_fun_const_smul ((contDiff_phaseOperatorWord hD hf w).differentiable
      (by simp) x)]
    simp [smul_smul]

/-- A time weight may be applied to the field before taking any label or
phase derivative at fixed time. -/
theorem phaseOperatorWord_const_smul {D : ι → U → U}
    (hD : ∀ i, ContDiff ℝ ∞ (D i)) {f : U → E} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (w : List ι) (x : U) :
    phaseOperatorWord D w (fun y => r • f y) x = r • phaseOperatorWord D w f x := by
  induction w generalizing x with
  | nil => rfl
  | cons i w ih =>
    change fderiv ℝ (phaseOperatorWord D w (fun y => r • f y)) x (D i x) =
      r • fderiv ℝ (phaseOperatorWord D w f) x (D i x)
    rw [funext ih, fderiv_fun_const_smul ((contDiff_phaseOperatorWord hD hf w).differentiable
      (by simp) x)]
    rfl

private theorem norm_bilinear_apply_le (B : E →L[ℝ] F →L[ℝ] G) (a : E) (b : F) :
    ‖B a b‖ ≤ ‖B‖ * ‖a‖ * ‖b‖ :=
  ((B a).le_opNorm b).trans (mul_le_mul_of_nonneg_right (B.le_opNorm a) (norm_nonneg _))

omit [NormedSpace ℝ G] in
private theorem norm_listSum_le {α : Type*} (l : List α) (f : α → G) :
    ‖(l.map f).sum‖ ≤ (l.map fun a => ‖f a‖).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    exact (norm_add_le _ _).trans (add_le_add le_rfl ih)

/-- The word Leibniz formula bounds each derivative by the convolution of
the norms of lower-order derivatives. The directions may already carry
their weights. -/
theorem norm_phaseOperatorWord_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} {g : U → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (x : U) :
    ‖phaseOperatorWord D w (fun y => B (f y) (g y)) x‖ ≤
      ((hierarchyLeibnizSplits w).map fun p =>
        ‖B‖ * ‖phaseOperatorWord D p.1 f x‖ * ‖phaseOperatorWord D p.2 g x‖).sum := by
  rw [phaseOperatorWord_bilinear B hD hf hg]
  exact (norm_listSum_le _ _).trans <|
    List.sum_le_sum fun p _ => norm_bilinear_apply_le B _ _

/-- The differentiated product with its same-level term removed. Every
remaining term uses a strictly lower order derivative of the second factor. -/
theorem phaseOperatorWord_bilinear_commutator (B : E →L[ℝ] F →L[ℝ] G)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} {g : U → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (x : U) :
    phaseOperatorWord D w (fun y => B (f y) (g y)) x - B (f x) (phaseOperatorWord D w g x) =
      (((hierarchyLeibnizSplits w).filter fun p => !p.1.isEmpty).map fun p =>
        B (phaseOperatorWord D p.1 f x) (phaseOperatorWord D p.2 g x)).sum := by
  rw [phaseOperatorWord_bilinear B hD hf hg]
  nth_rewrite 1 [hierarchyLeibnizSplits_append_undifferentiated w]
  simp [phaseOperatorWord]

omit [NormedSpace ℝ G] in
private theorem listSum_sub {α : Type*} (l : List α) (f g : α → G) :
    (l.map f).sum - (l.map g).sum = (l.map fun j => f j - g j).sum := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, ← ih]
    abel

private theorem norm_bilinear_sub_le (B : E →L[ℝ] F →L[ℝ] G)
    (a a' : E) (b b' : F) :
    ‖B a b - B a' b'‖ ≤
      ‖B‖ * ‖a - a'‖ * ‖b‖ + ‖B‖ * ‖a'‖ * ‖b - b'‖ := by
  have h : B a b - B a' b' = B (a - a') b + B a' (b - b') := by
    simp only [map_sub, _root_.sub_apply]
    abel
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (norm_bilinear_apply_le B _ _) (norm_bilinear_apply_le B _ _))

/-- The corresponding convolution bound for differences of the derivatives.
This supplies the numerator of the half-Hölder seminorm. -/
theorem norm_phaseOperatorWord_bilinear_sub_le (B : E →L[ℝ] F →L[ℝ] G)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} {g : U → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) (x y : U) :
    ‖phaseOperatorWord D w (fun z => B (f z) (g z)) x -
      phaseOperatorWord D w (fun z => B (f z) (g z)) y‖ ≤
      ((hierarchyLeibnizSplits w).map fun p =>
        ‖B‖ * ‖phaseOperatorWord D p.1 f x - phaseOperatorWord D p.1 f y‖ *
          ‖phaseOperatorWord D p.2 g x‖ +
        ‖B‖ * ‖phaseOperatorWord D p.1 f y‖ *
          ‖phaseOperatorWord D p.2 g x - phaseOperatorWord D p.2 g y‖).sum := by
  rw [phaseOperatorWord_bilinear B hD hf hg, phaseOperatorWord_bilinear B hD hf hg, listSum_sub]
  exact (norm_listSum_le _ _).trans <|
    List.sum_le_sum fun p _ => norm_bilinear_sub_le B _ _ _ _

private theorem listSum_le_card_mul {α : Type*} (l : List α) (f : α → ℝ)
    {M : ℝ} (h : ∀ a ∈ l, f a ≤ M) : (l.map f).sum ≤ (l.length : ℝ) * M := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul,
      one_mul]
    exact (add_le_add (h i (by simp)) (ih fun j hj => h j (by simp [hj]))).trans_eq (add_comm _ _)

/-- Finite-order sup and difference bounds for a product. The hypotheses
need only hold for subwords of the specified derivative. -/
theorem phaseOperatorWord_bilinear_bounds (B : E →L[ℝ] F →L[ℝ] G)
    {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    {f : U → E} {g : U → F} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (w : List ι) {Cf Cg : ℝ} (hCf : 0 ≤ Cf)
    (hF : ∀ v, List.Sublist v w → ∀ x, ‖phaseOperatorWord D v f x‖ ≤ Cf)
    (hG : ∀ v, List.Sublist v w → ∀ x, ‖phaseOperatorWord D v g x‖ ≤ Cg) :
    (∀ x, ‖phaseOperatorWord D w (fun y => B (f y) (g y)) x‖ ≤
      (2 : ℝ) ^ w.length * ‖B‖ * Cf * Cg) ∧
    ((∀ v, List.Sublist v w → ∀ x y,
        ‖phaseOperatorWord D v f x - phaseOperatorWord D v f y‖ ≤ Cf * Real.sqrt (dist x y)) →
      (∀ v, List.Sublist v w → ∀ x y,
        ‖phaseOperatorWord D v g x - phaseOperatorWord D v g y‖ ≤ Cg * Real.sqrt (dist x y)) →
      ∀ x y, ‖phaseOperatorWord D w (fun z => B (f z) (g z)) x -
        phaseOperatorWord D w (fun z => B (f z) (g z)) y‖ ≤
        (2 : ℝ) ^ w.length * (2 * ‖B‖ * Cf * Cg) * Real.sqrt (dist x y)) := by
  have hlen : ((hierarchyLeibnizSplits w).length : ℝ) = (2 : ℝ) ^ w.length := by
    simp
  constructor
  · intro x
    refine (norm_phaseOperatorWord_bilinear_le B hD hf hg w x).trans ?_
    refine (listSum_le_card_mul _ _ (M := ‖B‖ * Cf * Cg) (fun p hp => ?_)).trans_eq ?_
    · obtain ⟨h₁, h₂, _⟩ := hierarchyLeibnizSplits_spec hp
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hF p.1 h₁ x) (norm_nonneg B))
        (hG p.2 h₂ x) (norm_nonneg _) (mul_nonneg (norm_nonneg B) hCf)
    · rw [hlen]
      ring
  · intro hFd hGd x y
    refine (norm_phaseOperatorWord_bilinear_sub_le B hD hf hg w x y).trans ?_
    refine (listSum_le_card_mul _ _ (M := 2 * ‖B‖ * Cf * Cg * Real.sqrt (dist x y))
      (fun p hp => ?_)).trans_eq ?_
    · obtain ⟨h₁, h₂, _⟩ := hierarchyLeibnizSplits_spec hp
      have ha := mul_le_mul
        (mul_le_mul_of_nonneg_left (hFd p.1 h₁ x y) (norm_nonneg B))
        (hG p.2 h₂ x) (norm_nonneg _) (mul_nonneg (norm_nonneg B) (mul_nonneg hCf (Real.sqrt_nonneg _)))
      have hb := mul_le_mul
        (mul_le_mul_of_nonneg_left (hF p.1 h₁ y) (norm_nonneg B))
        (hGd p.2 h₂ x y) (norm_nonneg _) (mul_nonneg (norm_nonneg B) hCf)
      refine (add_le_add ha hb).trans_eq ?_
      ring
    · rw [hlen]
      ring

end ProductRule

section FiniteNorm

variable {ι T U E F G : Type*} [Fintype ι] [LinearOrder ι]
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The canonical sorted derivative words of total order at most `n`.
For `Fin 4`, the first three letters specify the label multi-index
and the last specifies the phase order in (D.1). -/
def hierarchyAdmissibleWords (ι : Type*) [Fintype ι] [LinearOrder ι] (n : ℕ) : Finset (List ι) :=
  (Finset.range (n + 1)).biUnion fun k =>
    ((Finset.univ : Finset (Fin k → ι)).image List.ofFn).filter (List.Pairwise (· ≤ ·))

theorem mem_hierarchyAdmissibleWords {n : ℕ} {w : List ι} :
    w ∈ hierarchyAdmissibleWords ι n ↔ w.length ≤ n ∧ w.Pairwise (· ≤ ·) := by
  constructor
  · intro hw
    obtain ⟨k, hk, h⟩ := Finset.mem_biUnion.mp hw
    obtain ⟨hout, hsorted⟩ := Finset.mem_filter.mp h
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hout
    exact ⟨by simpa using Finset.mem_range.mp hk, hsorted⟩
  · rintro ⟨hn, hs⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨w.length, Finset.mem_range.mpr (Nat.lt_succ_of_le hn), Finset.mem_filter.mpr ⟨?_, hs⟩⟩
    exact Finset.mem_image.mpr ⟨w.get, Finset.mem_univ _, List.ofFn_get _⟩

/-- Quantities measured by the supremum at each word. The half-Hölder
choice also includes all half-power difference quotients at fixed time,
with the max convention of `HalfHolder`. -/
def hierarchyJetValues (holder : Prop) (D : ι → U → U)
    (w : List ι) (f : T → U → E) : Set ℝ :=
  {r | r = 0 ∨ (∃ t x, ‖phaseOperatorWord D w (f t) x‖ = r) ∨
    (holder ∧ ∃ t x y, ‖phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y‖ /
      Real.sqrt (dist x y) = r)}

/-- The finite weighted norm, when the directional fields already include
their weights and the profile already includes any fixed-time normalization. -/
noncomputable def hierarchyFiniteWordNorm (holder : Prop) (D : ι → U → U)
    (n : ℕ) (f : T → U → E) : ℝ :=
  ∑ w ∈ hierarchyAdmissibleWords ι n, sSup (hierarchyJetValues holder D w f)

omit [Fintype ι] [LinearOrder ι] in
private theorem hierarchyJetValues_nonempty (holder : Prop) (D : ι → U → U)
    (w : List ι) (f : T → U → E) :
    (hierarchyJetValues holder D w f).Nonempty :=
  ⟨0, Or.inl rfl⟩

private theorem hierarchyJetValues_sup_le_finiteNorm {holder : Prop} {D : ι → U → U}
    {n : ℕ} {f : T → U → E}
    (hbdd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    {w : List ι} (hw : w ∈ hierarchyAdmissibleWords ι n) :
    sSup (hierarchyJetValues holder D w f) ≤ hierarchyFiniteWordNorm holder D n f := by
  apply Finset.single_le_sum _ hw
  intro v hv
  exact le_csSup (hbdd v hv) (Or.inl rfl)

private theorem wordNorm_bounds_of_bdd {holder : Prop} {D : ι → U → U}
    {n : ℕ} {f : T → U → E}
    (hbdd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    {w : List ι} (hw : w ∈ hierarchyAdmissibleWords ι n) (t : T) :
    let M := hierarchyFiniteWordNorm holder D n f
    (∀ x, ‖phaseOperatorWord D w (f t) x‖ ≤ M) ∧
    (holder → ∀ x y, ‖phaseOperatorWord D w (f t) x - phaseOperatorWord D w (f t) y‖ ≤
      M * Real.sqrt (dist x y)) := by
  have hM := hierarchyJetValues_sup_le_finiteNorm hbdd hw
  refine ⟨fun x => (le_csSup (hbdd w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans hM,
    fun hH x y => ?_⟩
  by_cases hxy : x = y
  · subst y
    simp
  · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).mp
    exact (le_csSup (hbdd w hw) (Or.inr (Or.inr ⟨hH, t, x, y, rfl⟩))).trans hM

/-- The product estimate (D.4) for all admissible derivative orders,
with the sup norm or the half-Hölder norm according to `holder`. Apply
it in the weighted coordinate directions to `f` and the time-normalized
second factor. The constant depends only on the order and the index set. -/
theorem hierarchyFiniteWordNorm_bilinear_le (B : E →L[ℝ] F →L[ℝ] G)
    (holder : Prop) {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (n : ℕ) {f : T → U → E} {g : T → U → F}
    (hf : ∀ t, ContDiff ℝ ∞ (f t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hfbd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w f))
    (hgbd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w g)) :
    hierarchyFiniteWordNorm holder D n (fun t x => B (f t x) (g t x)) ≤
      (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n *
        (2 * ‖B‖ * hierarchyFiniteWordNorm holder D n f * hierarchyFiniteWordNorm holder D n g) := by
  let K := hierarchyAdmissibleWords ι n
  let Mf := hierarchyFiniteWordNorm holder D n f
  let Mg := hierarchyFiniteWordNorm holder D n g
  have hnF : 0 ≤ Mf := Finset.sum_nonneg fun w hw => le_csSup (hfbd w hw) (Or.inl rfl)
  have hnG : 0 ≤ Mg := Finset.sum_nonneg fun w hw => le_csSup (hgbd w hw) (Or.inl rfl)
  let C := (2 : ℝ) ^ n * (2 * ‖B‖ * Mf * Mg)
  have hpos : 0 ≤ C := by dsimp only [C]; positivity
  have hterm (w : List ι) (hw : w ∈ K) :
      sSup (hierarchyJetValues holder D w (fun t x => B (f t x) (g t x))) ≤ C := by
    obtain ⟨horder, hsorted⟩ := mem_hierarchyAdmissibleWords.mp hw
    have hsub (v : List ι) (hv : List.Sublist v w) : v ∈ K :=
      mem_hierarchyAdmissibleWords.mpr ⟨hv.length_le.trans horder, hsorted.sublist hv⟩
    have hpow : (2 : ℝ) ^ w.length ≤ 2 ^ n := pow_le_pow_right₀ (by norm_num) horder
    have hbounds (t : T) := phaseOperatorWord_bilinear_bounds B hD (hf t) (hg t)
      w hnF (fun v hv => (wordNorm_bounds_of_bdd hfbd (hsub v hv) t).1)
      (fun v hv => (wordNorm_bounds_of_bdd hgbd (hsub v hv) t).1)
    apply csSup_le (hierarchyJetValues_nonempty _ _ _ _)
    rintro r (rfl | ⟨t, x, rfl⟩ | ⟨hH, t, x, y, rfl⟩)
    · exact hpos
    · refine ((hbounds t).1 x).trans ?_
      dsimp only [C]
      calc
        _ ≤ (2 : ℝ) ^ n * ‖B‖ * Mf * Mg := by gcongr
        _ ≤ _ := by nlinarith [show 0 ≤ (2 : ℝ) ^ n * ‖B‖ * Mf * Mg by positivity]
    · by_cases hxy : x = y
      · subst y
        simpa only [sub_self, norm_zero, zero_div] using hpos
      · apply (div_le_iff₀ (Real.sqrt_pos.2 (dist_pos.mpr hxy))).mpr
        refine ((hbounds t).2
          (fun v hv => (wordNorm_bounds_of_bdd hfbd (hsub v hv) t).2 hH)
          (fun v hv => (wordNorm_bounds_of_bdd hgbd (hsub v hv) t).2 hH) x y).trans ?_
        dsimp only [C]
        gcongr
  change (∑ w ∈ K, sSup (hierarchyJetValues holder D w (fun t x => B (f t x) (g t x)))) ≤ _
  calc
    _ ≤ ∑ _ ∈ K, C := Finset.sum_le_sum hterm
    _ = _ := by simp [K, C, Mf, Mg, mul_assoc]

/-- The real operator-valued coefficient version of (D.4). A time weight
on the second factor remains a time weight on the product by linearity. -/
theorem hierarchyFiniteWordNorm_clm_apply_le
    (holder : Prop) {D : ι → U → U} (hD : ∀ i, ContDiff ℝ ∞ (D i))
    (n : ℕ) {c : T → U → F →L[ℝ] G} {g : T → U → F}
    (hc : ∀ t, ContDiff ℝ ∞ (c t)) (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hcbd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w c))
    (hgbd : ∀ w ∈ hierarchyAdmissibleWords ι n, BddAbove (hierarchyJetValues holder D w g)) :
    hierarchyFiniteWordNorm holder D n (fun t x => c t x (g t x)) ≤
      (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n *
        (2 * hierarchyFiniteWordNorm holder D n c * hierarchyFiniteWordNorm holder D n g) := by
  let B : (F →L[ℝ] G) →L[ℝ] F →L[ℝ] G :=
    ContinuousLinearMap.flip (ContinuousLinearMap.apply ℝ G)
  have hB : ‖B‖ ≤ 1 := by
    simp only [B, ContinuousLinearMap.opNorm_flip, ContinuousLinearMap.apply]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    simp only [ContinuousLinearMap.coe_id', id, one_mul]
    rfl
  have hnF : 0 ≤ hierarchyFiniteWordNorm holder D n c :=
    Finset.sum_nonneg fun w hw => le_csSup (hcbd w hw) (Or.inl rfl)
  have hnG : 0 ≤ hierarchyFiniteWordNorm holder D n g :=
    Finset.sum_nonneg fun w hw => le_csSup (hgbd w hw) (Or.inl rfl)
  refine (hierarchyFiniteWordNorm_bilinear_le B holder hD n hc hg hcbd hgbd).trans ?_
  calc
    _ ≤ (hierarchyAdmissibleWords ι n).card * (2 : ℝ) ^ n *
        (2 * 1 * hierarchyFiniteWordNorm holder D n c * hierarchyFiniteWordNorm holder D n g) := by
      gcongr
    _ = _ := by rw [mul_one]

end FiniteNorm

/-- The weighted label and phase directions in (D.1), indexed so that
their sorted words represent exactly one word per mixed multi-index. -/
noncomputable def hierarchyMixedDirection (ℓ h : ℝ) (i : Fin 4) : (Vec3 × ℝ) → Vec3 × ℝ :=
  fun _ => Fin.lastCases (h • phaseCoordinateDirection (.inr ()))
    (fun j => ℓ • phaseCoordinateDirection (.inl j)) i

/-- Under the scale choice of Lemma D.2(c), a positive-order coefficient
bound of the form (D.6) leaves one factor of the envelope radius. -/
theorem hierarchy_weighted_coefficient_le {D ℓ C bound : ℝ} {k m : ℕ}
    (hD : 1 ≤ D) (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C) (hscale : ℓ * D ^ k ≤ 1)
    (hm : 1 ≤ m) (hbound : bound ≤ C * D ^ (k * (m + 1))) :
    ℓ ^ m * bound ≤ C * D ^ (2 * k) * ℓ := by
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  calc
    ℓ ^ m * bound ≤ ℓ ^ m * (C * D ^ (k * (m + 1))) :=
      mul_le_mul_of_nonneg_left hbound (pow_nonneg hℓ _)
    _ = C * D ^ k * (ℓ * D ^ k) ^ m := by
      rw [Nat.mul_succ, pow_add, pow_mul, mul_pow]
      ring
    _ ≤ C * D ^ k * (ℓ * D ^ k) :=
      mul_le_mul_of_nonneg_left (pow_le_of_le_one (mul_nonneg hℓ (pow_nonneg hD₀ _))
        hscale (by omega)) (mul_nonneg hC (pow_nonneg hD₀ _))
    _ = _ := by rw [pow_mul]; ring

end TorusEuler

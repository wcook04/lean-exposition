module

public import QuarticQuery.Model.Quantum
public import QuarticQuery.Bridge.Deferred
public import Complexity.Computability.QueryComplexity.Quantum.Adversary
import Complexity.Foundations.Quantum.Measurement.Overlap

/-!
# Appendix A: arbitrary adversary matrices and the final-overlap argument

Compiled as part of the `QuarticQuery` library target.

The definitions below use the paper's complex-valued progress sum. The library's
private `progress` instead sums absolute overlaps on sensitive edges. In particular,
the library's spectral-sensitivity theorem is not the arbitrary-matrix Lemma A.2.

`appendixA_adversary_of_perron` is explicitly conditional on a Perron witness.
The arbitrary-matrix per-query estimate is supplied by `appendixAProgress_query_le`.
Existence of the Perron witness is handled separately.


The final-overlap theorem is proved for arbitrary nonnegative matrices supported
on opposite-output pairs. Its specialization to the library's fixed query model
uses the public theorem `Cslib.Quantum.norm_inner_run_le`.
-/

@[expose] public section

namespace QuarticQuery.Paper

open Finset
open scoped BigOperators

variable {n : ℕ} {W : Type*} [Fintype W]

/-- Ledger: def-Gamma-i. The input-indexed real matrices of Appendix A. -/
abbrev AppendixAMatrix (n : ℕ) :=
  Matrix (BitInput (Fin n)) (BitInput (Fin n)) ℝ

/-- Ledger: def-Gamma-i. Euclidean operator norm, avoiding the default matrix norm. -/
noncomputable def appendixAMatrixNorm (Γ : AppendixAMatrix n) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℝ) Γ‖

/-- Ledger: def-Gamma-i. The coordinate mask `(Γᵢ)ₓᵧ = Γₓᵧ 1[xᵢ ≠ yᵢ]`. -/
def appendixAGammaCoord (Γ : AppendixAMatrix n) (i : Fin n) : AppendixAMatrix n :=
  fun x y => if x i ≠ y i then Γ x y else 0

/-- Ledger: def-Gamma-i. The mask agrees exactly with the displayed definition. -/
theorem appendixAGammaCoord_apply (Γ : AppendixAMatrix n) (i : Fin n)
    (x y : BitInput (Fin n)) :
    appendixAGammaCoord Γ i x y = if x i ≠ y i then Γ x y else 0 := rfl

/-- Ledger: def-Gamma-i. Coordinate masking preserves nonnegativity. -/
theorem appendixAGammaCoord_nonneg {Γ : AppendixAMatrix n}
    (hΓ : ∀ x y, 0 ≤ Γ x y) (i : Fin n) (x y : BitInput (Fin n)) :
    0 ≤ appendixAGammaCoord Γ i x y := by
  unfold appendixAGammaCoord
  split_ifs
  · exact hΓ x y
  · exact le_rfl

/-- Ledger: claim-per-query. The arbitrary-input controlled-phase oracle identity.
This extends the library's neighboring-input identity to all pairs of inputs. -/
theorem appendixA_inner_phaseOracle (x y : BitInput (Fin n))
    (ψ φ : Cslib.Quantum.State n W) :
    inner ℂ (Cslib.Quantum.phaseOracle x ψ) (Cslib.Quantum.phaseOracle y φ) =
      inner ℂ ψ φ - 2 * ∑ i : Fin n,
        if x i ≠ y i then
          inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) else 0 := by
  classical
  have hproj (i : Fin n) :
      inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) =
        ∑ p : Fin n × Bool × W,
          if p.1 = i ∧ p.2.1 = true then star (ψ.ofLp p) * φ.ofLp p else 0 := by
    simp only [PiLp.inner_apply, RCLike.inner_apply']
    apply sum_congr rfl
    intro p hp
    obtain ⟨j, b, w⟩ := p
    by_cases hi : j = i <;> cases b <;>
      simp [Cslib.Quantum.ctrlProj, hi]
  have hmask (i : Fin n) :
      (if x i ≠ y i then
        inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) else 0) =
      ∑ p : Fin n × Bool × W,
        if p.1 = i ∧ p.2.1 = true ∧ x i ≠ y i then
          star (ψ.ofLp p) * φ.ofLp p else 0 := by
    by_cases hxy : x i = y i
    · simp [hxy]
    · simp [hxy, hproj]
  have hsum :
      (∑ i : Fin n, if x i ≠ y i then
        inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) else 0) =
      ∑ p : Fin n × Bool × W,
        if p.2.1 = true ∧ x p.1 ≠ y p.1 then
          star (ψ.ofLp p) * φ.ofLp p else 0 := by
    simp only [hmask]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_eq_single p.1]
    · simp
    · intro i hi hne
      simp [Ne.symm hne]
    · simp
  rw [hsum]
  simp only [PiLp.inner_apply, RCLike.inner_apply', mul_sum, ← sum_sub_distrib]
  apply sum_congr rfl
  intro p hp
  obtain ⟨i, b, w⟩ := p
  cases hx : x i <;> cases hy : y i <;> cases b <;>
    simp [Cslib.Quantum.phaseOracle_apply, hx, hy] <;> ring

/-- Ledger: claim-per-query. Each pairwise overlap changes by at most the sum of
the query magnitudes on coordinates where the inputs differ. -/
theorem appendixA_norm_inner_phaseOracle_sub (x y : BitInput (Fin n))
    (ψ φ : Cslib.Quantum.State n W) :
    ‖inner ℂ (Cslib.Quantum.phaseOracle x ψ) (Cslib.Quantum.phaseOracle y φ) -
      inner ℂ ψ φ‖ ≤
      2 * ∑ i : Fin n, if x i ≠ y i then
        ‖Cslib.Quantum.ctrlProj i ψ‖ * ‖Cslib.Quantum.ctrlProj i φ‖ else 0 := by
  rw [appendixA_inner_phaseOracle]
  have hid (a b : ℂ) : (a - 2 * b) - a = -(2 * b) := by ring
  rw [hid, norm_neg, norm_mul, RCLike.norm_ofNat]
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ‖∑ i : Fin n, if x i ≠ y i then
        inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) else 0‖
        ≤ ∑ i : Fin n, ‖if x i ≠ y i then
          inner ℂ (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ) else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin n, if x i ≠ y i then
        ‖Cslib.Quantum.ctrlProj i ψ‖ * ‖Cslib.Quantum.ctrlProj i φ‖ else 0 := by
      apply sum_le_sum
      intro i hi
      by_cases hxy : x i = y i
      · simp [hxy]
      · rw [if_pos hxy, if_pos hxy]
        exact norm_inner_le_norm (𝕜 := ℂ)
          (Cslib.Quantum.ctrlProj i ψ) (Cslib.Quantum.ctrlProj i φ)

/-- Ledger: claim-perron. The precise witness required by the paper.
This is a predicate, not a proof that a witness exists. -/
def AppendixAPerronWitness (Γ : AppendixAMatrix n) (v : BitInput (Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ v x) ∧ (∑ x, v x ^ 2 = 1) ∧
    ∀ x, ∑ y, Γ x y * v y = appendixAMatrixNorm Γ * v x

/-- Ledger: claim-perron. The existence assertion that remains to be formalised.
It is stated as a proposition-valued definition, without an axiom or `sorry`. -/
def AppendixAPerronObligation (Γ : AppendixAMatrix n) : Prop :=
  (∀ x y, Γ x y = Γ y x) → (∀ x y, 0 ≤ Γ x y) → Γ ≠ 0 →
    ∃ v, AppendixAPerronWitness Γ v

/-- Ledger: def-adv-progress. The paper's complex progress measure on an arbitrary
family of pure states. The coefficient is cast from ℝ to ℂ. -/
noncomputable def appendixAProgress (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W) : ℂ :=
  ∑ x, ∑ y, ((v x * v y * Γ x y : ℝ) : ℂ) * inner ℂ (Ψ x) (Ψ y)

/-- Ledger: claim-per-query. A quadratic form is bounded by the Euclidean operator
norm, with no symmetry or nonnegativity hypothesis. -/
theorem appendixA_quadratic_le_norm (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ) :
    ∑ x, ∑ y, v x * v y * Γ x y ≤ appendixAMatrixNorm Γ * ∑ x, v x ^ 2 := by
  let A := Matrix.toEuclideanCLM (𝕜 := ℝ) Γ
  let w : EuclideanSpace ℝ (BitInput (Fin n)) := WithLp.toLp 2 v
  have hnorm : ‖w‖ ^ 2 = ∑ x, v x ^ 2 := by
    exact EuclideanSpace.real_norm_sq_eq w
  have hform : inner ℝ w (A w) = ∑ x, ∑ y, v x * v y * Γ x y := by
    change inner ℝ (WithLp.toLp 2 v)
      (Matrix.toEuclideanCLM (𝕜 := ℝ) Γ (WithLp.toLp 2 v)) = _
    rw [Matrix.inner_toEuclideanCLM]
    simp only [dotProduct, Matrix.mulVec, PiLp.toLp_apply, mul_sum]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    ring
  have hinner := real_inner_le_norm w (A w)
  have hop := A.le_opNorm w
  have hw := norm_nonneg w
  change _ ≤ ‖A‖ * ∑ x, v x ^ 2
  rw [← hnorm, ← hform]
  nlinarith

/-- Ledger: claim-per-query. The total squared control-query weight is at most
one. A control bit equal to zero contributes no query weight. -/
theorem appendixA_query_weights_le_one (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W)
    (hv : ∑ x, v x ^ 2 = 1) (hΨ : ∀ x, ‖Ψ x‖ = 1) :
    ∑ i : Fin n, ∑ x, (v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖) ^ 2 ≤ 1 := by
  rw [sum_comm]
  calc
    ∑ x, ∑ i : Fin n, (v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖) ^ 2
        ≤ ∑ x, v x ^ 2 := by
      apply sum_le_sum
      intro x hx
      have hi : ∑ i : Fin n, ‖Cslib.Quantum.ctrlProj i (Ψ x)‖ ^ 2 ≤ 1 := by
        calc
          ∑ i : Fin n, ‖Cslib.Quantum.ctrlProj i (Ψ x)‖ ^ 2
              ≤ ∑ i : Fin n, Cslib.Quantum.regProb (Ψ x) i :=
            sum_le_sum fun i _ => Cslib.Quantum.norm_sq_ctrlProj_le i (Ψ x)
          _ = 1 := by rw [Cslib.Quantum.sum_regProb, hΨ x, one_pow]
      simp only [mul_pow, ← mul_sum]
      nlinarith [sq_nonneg (v x)]
    _ = 1 := hv

/-- Ledger: claim-per-query. The first inequality in the displayed per-query
estimate, for the paper's exact complex progress. -/
theorem appendixAProgress_query_quadratic
    (Γ : AppendixAMatrix n) (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W)
    (hΓ : ∀ x y, 0 ≤ Γ x y) (hv : ∀ x, 0 ≤ v x) :
    ‖appendixAProgress Γ v (fun x => Cslib.Quantum.phaseOracle x (Ψ x)) -
      appendixAProgress Γ v Ψ‖ ≤
      2 * ∑ i : Fin n, ∑ x, ∑ y,
        (v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖) *
        (v y * ‖Cslib.Quantum.ctrlProj i (Ψ y)‖) * appendixAGammaCoord Γ i x y := by
  classical
  let a (i : Fin n) (x : BitInput (Fin n)) := ‖Cslib.Quantum.ctrlProj i (Ψ x)‖
  have hid : appendixAProgress Γ v (fun x => Cslib.Quantum.phaseOracle x (Ψ x)) -
      appendixAProgress Γ v Ψ =
      ∑ x, ∑ y, ((v x * v y * Γ x y : ℝ) : ℂ) *
        (inner ℂ (Cslib.Quantum.phaseOracle x (Ψ x)) (Cslib.Quantum.phaseOracle y (Ψ y)) -
          inner ℂ (Ψ x) (Ψ y)) := by
    simp only [appendixAProgress, ← sum_sub_distrib]
    apply sum_congr rfl
    intro x hx
    apply sum_congr rfl
    intro y hy
    ring
  rw [hid]
  calc
    ‖∑ x, ∑ y, ((v x * v y * Γ x y : ℝ) : ℂ) *
        (inner ℂ (Cslib.Quantum.phaseOracle x (Ψ x)) (Cslib.Quantum.phaseOracle y (Ψ y)) -
          inner ℂ (Ψ x) (Ψ y))‖
        ≤ ∑ x, ∑ y, ‖((v x * v y * Γ x y : ℝ) : ℂ) *
          (inner ℂ (Cslib.Quantum.phaseOracle x (Ψ x)) (Cslib.Quantum.phaseOracle y (Ψ y)) -
            inner ℂ (Ψ x) (Ψ y))‖ :=
      (norm_sum_le _ _).trans (sum_le_sum fun x _ => norm_sum_le _ _)
    _ ≤ ∑ x, ∑ y, (v x * v y * Γ x y) *
        (2 * ∑ i : Fin n, if x i ≠ y i then a i x * a i y else 0) := by
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro y hy
      have hw : 0 ≤ v x * v y * Γ x y := mul_nonneg (mul_nonneg (hv x) (hv y)) (hΓ x y)
      have hpair := appendixA_norm_inner_phaseOracle_sub x y (Ψ x) (Ψ y)
      have hm := mul_le_mul_of_nonneg_left hpair hw
      simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hv x), abs_of_nonneg (hv y), abs_of_nonneg (hΓ x y), a] using hm
    _ = ∑ x, ∑ y, ∑ i : Fin n,
        2 * ((v x * a i x) * (v y * a i y) * appendixAGammaCoord Γ i x y) := by
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      simp only [mul_sum]
      apply sum_congr rfl
      intro i hi
      by_cases hxy : x i = y i <;> simp [appendixAGammaCoord, hxy] <;> ring
    _ = ∑ x, ∑ i : Fin n, ∑ y,
        2 * ((v x * a i x) * (v y * a i y) * appendixAGammaCoord Γ i x y) := by
      apply sum_congr rfl
      intro x hx
      exact sum_comm
    _ = ∑ i : Fin n, ∑ x, ∑ y,
        2 * ((v x * a i x) * (v y * a i y) * appendixAGammaCoord Γ i x y) := sum_comm
    _ = _ := by simp only [mul_sum, a]

/-- Ledger: claim-per-query. The full arbitrary-matrix per-query estimate.
`M` bounds every Euclidean coordinate-mask norm. -/
theorem appendixAProgress_query_le
    (Γ : AppendixAMatrix n) (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W)
    (hΓ : ∀ x y, 0 ≤ Γ x y) (hv : ∀ x, 0 ≤ v x)
    (hv1 : ∑ x, v x ^ 2 = 1) (hΨ : ∀ x, ‖Ψ x‖ = 1)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    ‖appendixAProgress Γ v (fun x => Cslib.Quantum.phaseOracle x (Ψ x)) -
      appendixAProgress Γ v Ψ‖ ≤ 2 * M := by
  have hquad := appendixAProgress_query_quadratic Γ v Ψ hΓ hv
  have hweight := appendixA_query_weights_le_one v Ψ hv1 hΨ
  have hform :
      (∑ i : Fin n, ∑ x, ∑ y,
        (v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖) *
        (v y * ‖Cslib.Quantum.ctrlProj i (Ψ y)‖) * appendixAGammaCoord Γ i x y)
      ≤ M * (∑ i : Fin n, ∑ x, (v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖) ^ 2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    exact (appendixA_quadratic_le_norm (appendixAGammaCoord Γ i)
      (fun x => v x * ‖Cslib.Quantum.ctrlProj i (Ψ x)‖)).trans
      (mul_le_mul_of_nonneg_right (hcoord i) (sum_nonneg fun _ _ => sq_nonneg _))
  have hsum := mul_le_mul_of_nonneg_left hweight hM
  nlinarith

/-- Ledger: def-adv-progress. Input-independent isometries preserve progress. -/
theorem appendixAProgress_isometry (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W)
    (U : Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W) :
    appendixAProgress Γ v (fun x => U (Ψ x)) = appendixAProgress Γ v Ψ := by
  simp only [appendixAProgress, LinearIsometry.inner_map_map]

/-- Ledger: claim-perron. A Perron witness gives the required quadratic form.
The eigenvector's existence is a separate obligation. -/
theorem appendixA_perron_form {Γ : AppendixAMatrix n}
    {v : BitInput (Fin n) → ℝ} (hv : AppendixAPerronWitness Γ v) :
    ∑ x, ∑ y, v x * v y * Γ x y = appendixAMatrixNorm Γ := by
  rcases hv with ⟨hv0, hv1, hve⟩
  calc
    ∑ x, ∑ y, v x * v y * Γ x y = ∑ x, v x * (∑ y, Γ x y * v y) := by
      simp only [mul_sum]
      apply sum_congr rfl
      intro x hx
      apply sum_congr rfl
      intro y hy
      ring
    _ = ∑ x, v x * (appendixAMatrixNorm Γ * v x) := by simp only [hve]
    _ = appendixAMatrixNorm Γ * ∑ x, v x ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro x hx
      ring
    _ = appendixAMatrixNorm Γ := by rw [hv1, mul_one]

/-- Ledger: def-adv-progress. Equal unit initial states give the quadratic form. -/
theorem appendixAProgress_initial (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ) (ψ : Cslib.Quantum.State n W) (hψ : ‖ψ‖ = 1) :
    appendixAProgress Γ v (fun _ => ψ) =
      ((∑ x, ∑ y, v x * v y * Γ x y : ℝ) : ℂ) := by
  have hi : inner ℂ ψ ψ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hψ]
    norm_num
  simp only [appendixAProgress, hi, mul_one, Complex.ofReal_sum]

/-- Ledger: claim-final-overlap. Triangle inequality for the exact complex progress
sum. This applies to arbitrary nonnegative Γ, with no symmetry assumption. -/
theorem appendixAProgress_final_of_overlap
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (Ψ : BitInput (Fin n) → Cslib.Quantum.State n W)
    (hΓ : ∀ x y, 0 ≤ Γ x y) (hv : ∀ x, 0 ≤ v x)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    {r : ℝ} (hoverlap : ∀ x y, f x ≠ f y → ‖inner ℂ (Ψ x) (Ψ y)‖ ≤ r) :
    ‖appendixAProgress Γ v Ψ‖ ≤ r * (∑ x, ∑ y, v x * v y * Γ x y) := by
  unfold appendixAProgress
  calc
    ‖∑ x, ∑ y, ((v x * v y * Γ x y : ℝ) : ℂ) * inner ℂ (Ψ x) (Ψ y)‖
        ≤ ∑ x, ‖∑ y, ((v x * v y * Γ x y : ℝ) : ℂ) * inner ℂ (Ψ x) (Ψ y)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ x, ∑ y, ‖((v x * v y * Γ x y : ℝ) : ℂ) * inner ℂ (Ψ x) (Ψ y)‖ :=
      sum_le_sum fun x _ => norm_sum_le _ _
    _ ≤ ∑ x, ∑ y, r * (v x * v y * Γ x y) := by
      apply sum_le_sum
      intro x hx
      apply sum_le_sum
      intro y hy
      by_cases hxy : f x = f y
      · simp [hzero x y hxy]
      · have hw : 0 ≤ v x * v y * Γ x y := mul_nonneg (mul_nonneg (hv x) (hv y)) (hΓ x y)
        have h := mul_le_mul_of_nonneg_left (hoverlap x y hxy) hw
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hv x), abs_of_nonneg (hv y), abs_of_nonneg (hΓ x y),
          mul_comm r] using h
    _ = r * (∑ x, ∑ y, v x * v y * Γ x y) := by simp only [mul_sum]

/-- Ledger: claim-final-overlap. The paper's standalone two-state statement:
opposite acceptance probabilities force overlap at most `2 sqrt(2) / 3`.
This statement does not require the states to come from an algorithm. -/
theorem appendixA_unit_states_final_overlap
    {ι : Type*} [Fintype ι] (ψ φ : EuclideanSpace ℂ ι)
    (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (S : Finset ι)
    (hp : Cslib.Quantum.measureProb ψ S ≤ 1 / 3)
    (hq : 2 / 3 ≤ Cslib.Quantum.measureProb φ S) :
    ‖inner ℂ ψ φ‖ ≤ 2 * Real.sqrt 2 / 3 := by
  have hov := Cslib.Quantum.norm_inner_sq_add_sq_measureProb_sub_le_one hψ hφ S
  have hsqrt := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hgap : (1 / 3 : ℝ) ≤
      Cslib.Quantum.measureProb φ S - Cslib.Quantum.measureProb ψ S := by linarith
  have hgapSq := sq_nonneg
    (Cslib.Quantum.measureProb φ S - Cslib.Quantum.measureProb ψ S - (1 / 3 : ℝ))
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
  nlinarith

/-- Ledger: claim-final-overlap. The library's exact algorithm-level overlap bound.
At error 1/3 the constant is `2 * sqrt (2/9) = 2 * sqrt 2 / 3`. -/
theorem appendixA_final_overlap
    {f : TotalBool (Fin n)} {ε : ℝ}
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    {ψ₀ : Cslib.Quantum.State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin n × Bool × W))
    (h : ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ₀ x T) S -
      Cslib.BitString.bitVal ℝ (f x)| ≤ ε)
    (hε : 2 * ε ≤ 1) {x y : BitInput (Fin n)} (hxy : f x ≠ f y) :
    ‖inner ℂ (Cslib.Quantum.run U ψ₀ x T) (Cslib.Quantum.run U ψ₀ y T)‖ ≤
      2 * Real.sqrt (ε * (1 - ε)) :=
  Cslib.Quantum.norm_inner_run_le U hψ₀ T S h hε hxy

/-- Ledger: claim-final-overlap. Weighted final overlap for the paper's Γ and v. -/
theorem appendixAProgress_final
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    {ψ₀ : Cslib.Quantum.State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin n × Bool × W))
    (h : ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ₀ x T) S -
      Cslib.BitString.bitVal ℝ (f x)| ≤ 1 / 3)
    (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    (hv : AppendixAPerronWitness Γ v) :
    ‖appendixAProgress Γ v (fun x => Cslib.Quantum.run U ψ₀ x T)‖ ≤
      (2 * Real.sqrt ((1 / 3 : ℝ) * (1 - 1 / 3))) * appendixAMatrixNorm Γ := by
  rw [← appendixA_perron_form hv]
  apply appendixAProgress_final_of_overlap f Γ v _ hΓ hv.1 hzero
  intro x y hxy
  exact appendixA_final_overlap U hψ₀ T S h (by norm_num) hxy

/-- Ledger: claim-per-query. The per-query estimate as a reusable predicate.
It is proved from matrix bounds in `appendixA_perQuery_of_bounds`. -/
def AppendixAPerQueryObligation (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    (ψ₀ : Cslib.Quantum.State n W) (M : ℝ) : Prop :=
  ∀ t : ℕ,
    ‖appendixAProgress Γ v (fun x => Cslib.Quantum.run U ψ₀ x (t + 1)) -
      appendixAProgress Γ v (fun x => Cslib.Quantum.run U ψ₀ x t)‖ ≤ 2 * M

/-- Ledger: claim-per-query. Fixed-sequence execution satisfies the arbitrary-matrix
per-query estimate. The post-query gate disappears by isometry invariance. -/
theorem appendixA_perQuery_of_bounds
    (Γ : AppendixAMatrix n) (v : BitInput (Fin n) → ℝ)
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    (ψ₀ : Cslib.Quantum.State n W) (hψ₀ : ‖ψ₀‖ = 1)
    (hΓ : ∀ x y, 0 ≤ Γ x y) (hv : ∀ x, 0 ≤ v x)
    (hv1 : ∑ x, v x ^ 2 = 1) {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    AppendixAPerQueryObligation Γ v U ψ₀ M := by
  intro t
  change ‖appendixAProgress Γ v (fun x =>
      U (t + 1) (Cslib.Quantum.phaseOracle x (Cslib.Quantum.run U ψ₀ x t))) -
    appendixAProgress Γ v (fun x => Cslib.Quantum.run U ψ₀ x t)‖ ≤ 2 * M
  rw [appendixAProgress_isometry]
  exact appendixAProgress_query_le Γ v (fun x => Cslib.Quantum.run U ψ₀ x t)
    hΓ hv hv1 (fun x => by rw [Cslib.Quantum.norm_run, hψ₀]) hM hcoord

/-- Ledger: claim-per-query. The exact complex progress telescopes. -/
theorem appendixA_progress_telescope (P : ℕ → ℂ) {B : ℝ}
    (hstep : ∀ t, ‖P (t + 1) - P t‖ ≤ B) (T : ℕ) :
    ‖P T - P 0‖ ≤ (T : ℝ) * B := by
  induction T with
  | zero => simp
  | succ T ih =>
    have hid : P (T + 1) - P 0 = (P (T + 1) - P T) + (P T - P 0) := by ring
    rw [hid]
    have ht := norm_add_le (P (T + 1) - P T) (P T - P 0)
    have hs := hstep T
    push_cast
    linarith

/-- Ledger: lem-A.2. Numerical end of the adversary proof, conditional on initial,
final and per-query progress estimates. This is not the missing arbitrary-matrix
adversary theorem: the assumptions expose precisely what remains to be proved. -/
theorem appendixA_conditional_adversary (P : ℕ → ℂ) (T : ℕ) (G M r : ℝ)
    (hzero : ‖P 0‖ = G) (hfinal : ‖P T‖ ≤ r * G)
    (hstep : ∀ t, ‖P (t + 1) - P t‖ ≤ 2 * M) :
    (1 - r) * G ≤ 2 * (T : ℝ) * M := by
  have htel := appendixA_progress_telescope P hstep T
  have hid : P 0 = (P 0 - P T) + P T := by ring
  have hb : ‖P 0‖ ≤ ‖P 0 - P T‖ + ‖P T‖ := by
    conv_lhs => rw [hid]
    exact norm_add_le _ _
  rw [norm_sub_rev] at hb
  rw [hzero] at hb
  nlinarith

/-- Ledger: lem-A.2. The full arbitrary-matrix adversary estimate from a Perron
witness. The query normalization and constant are explicit. -/
theorem appendixA_adversary_of_perron
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    {ψ₀ : Cslib.Quantum.State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin n × Bool × W))
    (h : ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ₀ x T) S -
      Cslib.BitString.bitVal ℝ (f x)| ≤ 1 / 3)
    (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    (hv : AppendixAPerronWitness Γ v)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    (1 - 2 * Real.sqrt ((1 / 3 : ℝ) * (1 - 1 / 3))) * appendixAMatrixNorm Γ ≤
      2 * (T : ℝ) * M := by
  let P (t : ℕ) := appendixAProgress Γ v (fun x => Cslib.Quantum.run U ψ₀ x t)
  have hPzero : ‖P 0‖ = appendixAMatrixNorm Γ := by
    change ‖appendixAProgress Γ v (fun _ => U 0 ψ₀)‖ = _
    rw [appendixAProgress_initial Γ v (U 0 ψ₀) (by rw [(U 0).norm_map, hψ₀]),
      appendixA_perron_form hv]
    exact Complex.norm_of_nonneg (norm_nonneg _)
  have hPfinal := appendixAProgress_final f Γ v U hψ₀ T S h hΓ hzero hv
  have hPstep := appendixA_perQuery_of_bounds Γ v U ψ₀ hψ₀ hΓ hv.1 hv.2.1 hM hcoord
  exact appendixA_conditional_adversary P T (appendixAMatrixNorm Γ) M
    (2 * Real.sqrt ((1 / 3 : ℝ) * (1 - 1 / 3))) hPzero hPfinal hPstep

/-- Ledger: lem-A.2. Rational-constant form of the arbitrary-matrix estimate,
still explicitly conditional on the Perron witness. -/
theorem appendixA_adversary_thirty_five_of_perron
    (f : TotalBool (Fin n)) (Γ : AppendixAMatrix n)
    (v : BitInput (Fin n) → ℝ)
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    {ψ₀ : Cslib.Quantum.State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin n × Bool × W))
    (h : ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ₀ x T) S -
      Cslib.BitString.bitVal ℝ (f x)| ≤ 1 / 3)
    (hΓ : ∀ x y, 0 ≤ Γ x y)
    (hzero : ∀ x y, f x = f y → Γ x y = 0)
    (hv : AppendixAPerronWitness Γ v)
    {M : ℝ} (hM : 0 ≤ M)
    (hcoord : ∀ i, appendixAMatrixNorm (appendixAGammaCoord Γ i) ≤ M) :
    appendixAMatrixNorm Γ ≤ 35 * (T : ℝ) * M := by
  have hmain := appendixA_adversary_of_perron f Γ v U hψ₀ T S h hΓ hzero hv hM hcoord
  have hsqrt : Real.sqrt ((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 33 / 70 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hnorm : 0 ≤ appendixAMatrixNorm Γ := norm_nonneg _
  nlinarith

/-- Ledger: lem-A.3.lambda. A sharper rational constant in the library's existing
sensitivity-graph adversary proof. This does not prove Lemma A.2 for arbitrary Γ. -/
theorem appendixA_spectralSensitivity_le_thirty_five_mul {f : TotalBool (Fin n)}
    (U : ℕ → Cslib.Quantum.State n W →ₗᵢ[ℂ] Cslib.Quantum.State n W)
    {ψ₀ : Cslib.Quantum.State n W} (hψ₀ : ‖ψ₀‖ = 1) (T : ℕ)
    (S : Finset (Fin n × Bool × W))
    (h : ∀ x, |Cslib.Quantum.measureProb (Cslib.Quantum.run U ψ₀ x T) S -
      Cslib.BitString.bitVal ℝ (f x)| ≤ 1 / 3) :
    Cslib.BitString.spectralSensitivity f ≤ 35 * (T : ℝ) := by
  have hmain := Cslib.Quantum.one_sub_mul_spectralSensitivity_le U hψ₀ T S h (by norm_num)
  have hsqrt : Real.sqrt ((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 33 / 70 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  have hlam := Cslib.BitString.spectralSensitivity_nonneg f
  nlinarith

end QuarticQuery.Paper

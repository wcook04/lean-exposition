import TorusEuler.AmplitudeDenominatorBounds
import TorusEuler.AmplitudeScaledStrainBounds
import TorusEuler.AmplitudeStrainError
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial control of the scaled coordinate changes in Lemma 2.3. -/

namespace TorusEuler.MovingAmplitude

open MvPolynomial

/-- A fixed polynomial has polynomially bounded size and sensitivity on boxes
of radius at least one. The coefficient and exponent depend only on the
polynomial. In the amplitude rows, reciprocal quantities such as the
reciprocal wave-vector norm are treated as coordinates with separate bounds. -/
theorem polynomial_eval_bound {ι : Type*} (p : MvPolynomial ι ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ,
      ∀ {M d : ℝ}, 1 ≤ M → 0 ≤ d → ∀ {x y : ι → ℝ},
        (∀ i, |x i| ≤ M) → (∀ i, |y i| ≤ M) → (∀ i, |x i - y i| ≤ d) →
        |eval x p| ≤ C * M ^ n ∧ |eval x p - eval y p| ≤ C * M ^ n * d := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine ⟨|a|, abs_nonneg _, 0, ?_⟩
    intro M d hM hd x y hx hy hxy
    constructor
    · simp
    · simpa using mul_nonneg (abs_nonneg a) hd
  | add p q hp hq =>
    obtain ⟨C₁, hC₁, n₁, hp⟩ := hp
    obtain ⟨C₂, hC₂, n₂, hq⟩ := hq
    refine ⟨C₁ + C₂, add_nonneg hC₁ hC₂, n₁ + n₂, ?_⟩
    intro M d hM hd x y hx hy hxy
    obtain ⟨hpx, hpδ⟩ := hp hM hd hx hy hxy
    obtain ⟨hqx, hqδ⟩ := hq hM hd hx hy hxy
    have hpM := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_right n₁ n₂)) hC₁
    have hqM := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hM (Nat.le_add_left n₂ n₁)) hC₂
    simp only [map_add]
    constructor
    · calc
        |eval x p + eval x q| ≤ |eval x p| + |eval x q| := abs_add_le _ _
        _ ≤ C₁ * M ^ n₁ + C₂ * M ^ n₂ := add_le_add hpx hqx
        _ ≤ C₁ * M ^ (n₁ + n₂) + C₂ * M ^ (n₁ + n₂) := add_le_add hpM hqM
        _ = _ := by ring
    · rw [show eval x p + eval x q - (eval y p + eval y q) =
          (eval x p - eval y p) + (eval x q - eval y q) by ring]
      calc
        |(eval x p - eval y p) + (eval x q - eval y q)| ≤
            |eval x p - eval y p| + |eval x q - eval y q| := abs_add_le _ _
        _ ≤ C₁ * M ^ n₁ * d + C₂ * M ^ n₂ * d := add_le_add hpδ hqδ
        _ ≤ (C₁ * M ^ (n₁ + n₂)) * d + (C₂ * M ^ (n₁ + n₂)) * d :=
          add_le_add (mul_le_mul_of_nonneg_right hpM hd) (mul_le_mul_of_nonneg_right hqM hd)
        _ = _ := by ring
  | mul_X p i hp =>
    obtain ⟨C, hC, n, hp⟩ := hp
    refine ⟨2 * C, by positivity, n + 1, ?_⟩
    intro M d hM hd x y hx hy hxy
    obtain ⟨hpx, hpδ⟩ := hp hM hd hx hy hxy
    have hpy := (hp hM hd hy hx (fun j => by rw [abs_sub_comm]; exact hxy j)).1
    have hM₀ : 0 ≤ M := zero_le_one.trans hM
    have hCM : 0 ≤ C * M ^ n := by positivity
    simp only [map_mul, eval_X]
    constructor
    · rw [abs_mul, pow_succ]
      calc
        |eval x p| * |x i| ≤ C * M ^ n * M :=
          mul_le_mul hpx (hx i) (abs_nonneg _) hCM
        _ ≤ (2 * C) * (M ^ n * M) := by nlinarith [mul_nonneg hCM hM₀]
    · rw [show eval x p * x i - eval y p * y i =
          (eval x p - eval y p) * x i + eval y p * (x i - y i) by ring]
      calc
        |(eval x p - eval y p) * x i + eval y p * (x i - y i)| ≤
            |eval x p - eval y p| * |x i| + |eval y p| * |x i - y i| := by
          simpa only [abs_mul] using abs_add_le ((eval x p - eval y p) * x i)
            (eval y p * (x i - y i))
        _ ≤ C * M ^ n * d * M + C * M ^ n * d :=
          add_le_add
            (mul_le_mul hpδ (hx i) (abs_nonneg _) (mul_nonneg hCM hd))
            (mul_le_mul hpy (hxy i) (abs_nonneg _) hCM)
        _ ≤ (2 * C) * M ^ (n + 1) * d := by
          rw [pow_succ]
          nlinarith [mul_nonneg (mul_nonneg hCM hd) (sub_nonneg.mpr hM)]

/-- The entries of the two scaled strains and the six scalar inputs to the
amplitude matrix. The scalar entries are $X,Q,Z,1/S,1/Z,1/m$ in that order. -/
abbrev ScaledAmplitudeIndex := (Fin 3 × Fin 3) ⊕ ((Fin 3 × Fin 3) ⊕ Fin 6)

def scaledAmplitudeInputs (b A : Entries) (X Q Z invS invZ invM : ℝ) :
    ScaledAmplitudeIndex → ℝ :=
  Sum.elim (fun p => b p.1 p.2) (Sum.elim (fun p => A p.1 p.2) ![X, Q, Z, invS, invZ, invM])

private def matrixFromCoordinates {R : Type*} [CommRing R]
    (χ : ScaledAmplitudeIndex → R) : Matrix (Fin 2) (Fin 2) R :=
  scaledMatrix
    (fun i j => χ (.inl (i, j))) (fun i j => χ (.inr (.inl (i, j))))
    (χ (.inr (.inr 0))) (χ (.inr (.inr 1))) (χ (.inr (.inr 2)))
    (χ (.inr (.inr 3))) (χ (.inr (.inr 4))) (χ (.inr (.inr 5)))

private theorem matrixFromCoordinates_eq (b A : Entries) (X Q Z invS invZ invM : ℝ) :
    matrixFromCoordinates (scaledAmplitudeInputs b A X Q Z invS invZ invM) =
      scaledMatrix b A X Q Z invS invZ invM := rfl

private theorem eval_matrixFromCoordinates (χ : ScaledAmplitudeIndex → ℝ) (i j : Fin 2) :
    eval χ (matrixFromCoordinates X i j) = matrixFromCoordinates χ i j := by
  fin_cases i <;> fin_cases j <;>
    simp [matrixFromCoordinates, scaledMatrix, scaledPressureU, scaledPressureV, Fin.zero_eta,
      Fin.mk_one]

private theorem matrixFromCoordinates_sub_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ,
      ∀ {M d : ℝ}, 1 ≤ M → 0 ≤ d → ∀ {x y : ScaledAmplitudeIndex → ℝ},
        (∀ k, |x k| ≤ M) → (∀ k, |y k| ≤ M) → (∀ k, |x k - y k| ≤ d) →
        ∀ i j, |matrixFromCoordinates x i j - matrixFromCoordinates y i j| ≤ C * M ^ n * d := by
  classical
  choose C hC n hbound using fun p : Fin 2 × Fin 2 =>
    polynomial_eval_bound (matrixFromCoordinates X p.1 p.2)
  let C₀ : ℝ := ∑ p, C p
  let n₀ : ℕ := Finset.univ.sup n
  refine ⟨C₀, Finset.sum_nonneg (fun p _ => hC p), n₀, ?_⟩
  intro M d hM hd x y hx hy hxy i j
  have h := (hbound (i, j) hM hd hx hy hxy).2
  simp only [eval_matrixFromCoordinates] at h
  have hC' : C (i, j) ≤ C₀ :=
    Finset.single_le_sum (f := C) (fun p _ => hC p) (Finset.mem_univ (i, j))
  have hn : n (i, j) ≤ n₀ := Finset.le_sup (f := n) (Finset.mem_univ (i, j))
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hd)
  exact mul_le_mul hC' (pow_le_pow_right₀ hM hn) (by positivity) (by
    exact Finset.sum_nonneg (fun p _ => hC p))

/-- The raw error in Lemma 2.3 has polynomial sensitivity to changes in the
scaled inputs. To obtain the manuscript's bound, supply the uniform size and
comparison bounds for the wave coordinates, reciprocals and scaled entries. -/
theorem errorOperator_le_of_scaled_input_bounds :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ,
      ∀ {ε τ X Q Z S M d : ℝ} {b A : Entries}, S ≠ 0 → Z ≠ 0 → 1 ≤ M → 0 ≤ d →
        let x := scaledAmplitudeInputs (scaledEntries b S) (scaledEntries A S)
          X Q Z S⁻¹ Z⁻¹ (normFactor X Q Z S)⁻¹
        let y := scaledAmplitudeInputs (referenceScaledOlderEntries ε) (referenceScaledStrainEntries ε)
          (ReferenceRiccati.x ε τ) (-ε * τ) 1 0 1 (ReferenceRiccati.s ε τ ^ 2)
        (∀ k, |x k| ≤ M) → (∀ k, |y k| ≤ M) → (∀ k, |x k - y k| ≤ d) →
        ‖errorOperator ε τ b A X Q Z S‖ ≤ C * M ^ n * d := by
  obtain ⟨C, hC, n, hbound⟩ := matrixFromCoordinates_sub_le
  refine ⟨2 * C, by positivity, n, ?_⟩
  intro ε τ X Q Z S M d b A hS hZ hM hd x y hx hy hxy
  have herr := norm_pairOperator_le (N := rawMatrix b A X Q Z S - referenceMatrix ε τ)
    (d := C * M ^ n * d) (by positivity) (fun i j => by
      have h := hbound hM hd hx hy hxy i j
      simpa only [x, y, matrixFromCoordinates_eq, scaledMatrix_eq _ _ _ _ _ _ hS hZ,
        scaledMatrix_reference, Matrix.sub_apply] using h)
  unfold errorOperator
  convert herr using 1
  ring

open MovingWaveVector

/-- On the normalized time window of Lemma 2.3, the wave-coordinate bounds
and the small strain and relative coupling errors imply a polynomial bound
on the full amplitude error, with constants uniform in all wave data. -/
theorem errorOperator_le_on_normalized_window :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ n : ℕ,
      ∀ {e : Fin 3 → Space}, Orthonormal ℝ e → ∀ (B E : Space →L[ℝ] Space)
        {ε τ X Q Z S T δ σratio : ℝ},
        2 ≤ T → 0 ≤ τ → τ ≤ T → 0 ≤ ε → ε ≤ 1 →
        1 ≤ S → S⁻¹ ≤ 2 * δ → 0 ≤ δ → 120 * δ * T ^ 6 ≤ 1 / 2 →
        |X - ReferenceRiccati.x ε τ| + |Q + ε * τ| + |Z - 1| ≤ 120 * δ * T ^ 6 →
        ‖B‖ ≤ δ → ‖E‖ ≤ δ / S →
        |2 * S * entry e B 0 1 - 1| ≤ δ → |2 * S * entry e B 2 1 - ε| ≤ δ →
        |σratio - 1| ≤ 2 * T * δ →
        ‖errorOperator ε τ (entry e B) (entry e (strain e B E S σratio)) X Q Z S‖ ≤
          C * T ^ n * δ := by
  obtain ⟨C, hC, n, hbound⟩ := errorOperator_le_of_scaled_input_bounds
  refine ⟨C * 4 ^ n * 1448 + 6, by positivity, 2 * n + 8, ?_⟩
  intro e he B E ε τ X Q Z S T δ σratio hT hτ₀ hτT hε₀ hε₁ hS hSinv hδ hsmall
    hclose hB hE h12 h32 hσ
  let b := entry e B
  let A := entry e (strain e B 0 S σratio)
  let M := 4 * T ^ 2
  let d := 1448 * T ^ 8 * δ
  let R := errorOperator ε τ b (entry e (strain e B E S σratio)) X Q Z S
  let R₀ := errorOperator ε τ b A X Q Z S
  have hT₁ : 1 ≤ T := by linarith
  have hS₀ : 0 < S := by linarith
  have hT6 : T ≤ T ^ 6 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT₁ (show 1 ≤ (6 : ℕ) by decide)
  have hT8 : T ≤ T ^ 8 := by
    simpa only [pow_one] using pow_le_pow_right₀ hT₁ (show 1 ≤ (8 : ℕ) by decide)
  have hTδ : δ ≤ T * δ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hT₁ hδ
  have hsmall' : 3 * T * δ ≤ 1 := by
    nlinarith only [hsmall, mul_le_mul_of_nonneg_right hT6 hδ]
  have hdiff : 3 * T * δ ≤ d := by
    dsimp only [d]
    nlinarith only [mul_le_mul_of_nonneg_right hT8 hδ, show 0 ≤ T ^ 8 * δ by positivity]
  have hM : 2 ≤ M := by dsimp only [M]; nlinarith [sq_nonneg (T - 1)]
  have hMS : M ≤ S := by
    have h := mul_le_mul_of_nonneg_left hSinv (show 0 ≤ M by positivity)
    have hT26 : T ^ 2 ≤ T ^ 6 := pow_le_pow_right₀ hT₁ (by decide)
    have h' : M * S⁻¹ ≤ 1 := h.trans (by
      dsimp only [M]
      nlinarith only [hsmall, mul_le_mul_of_nonneg_right hT26 hδ])
    simpa only [← div_eq_mul_inv, div_le_iff₀ hS₀, one_mul] using h'
  obtain ⟨hZ, hw, hwref, hwdiff⟩ :=
    amplitude_wave_scalar_box hT hτ₀ hτT hε₀ hε₁ hS hSinv hδ hsmall hclose
  have hstrainBox := scaledEntries_abs_le_two he B hε₀ hε₁ hδ hT₁ hS hB h12 h32 hσ hsmall'
  have hrefBox := referenceScaledEntries_abs_le_one hε₀ hε₁
  have hbold := scaledOlderStrainEntries_sub_ref_le he B hδ hS hB h12 h32
  have hA := scaledStrainEntries_sub_ref_le he B hδ hT₁ hS hB h12 h32 hσ
  have hbare : ‖R₀‖ ≤ C * M ^ n * d := by
    apply hbound hS₀.ne' (by linarith) (by linarith) (by positivity)
    · rintro (⟨i, j⟩ | (⟨i, j⟩ | k))
      · exact (hstrainBox i j).1.trans hM
      · exact (hstrainBox i j).2.trans hM
      · exact hw k
    · rintro (⟨i, j⟩ | (⟨i, j⟩ | k))
      · exact (hrefBox i j).1.trans (by linarith)
      · exact (hrefBox i j).2.trans (by linarith)
      · exact hwref k
    · rintro (⟨i, j⟩ | (⟨i, j⟩ | k))
      · exact (hbold i j).trans ((show δ ≤ 3 * T * δ by linarith).trans hdiff)
      · exact (hA i j).trans hdiff
      · exact hwdiff k
  have hEpart : ‖R - R₀‖ ≤ 6 * δ := by
    calc
      _ ≤ 6 * S * ‖E‖ := norm_errorOperator_sub_strain_le he B E hS
        ((hw 0).trans hMS) ((hw 1).trans hMS) hZ
      _ ≤ 6 * S * (δ / S) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = 6 * δ := by field_simp
  calc
    ‖R‖ = ‖(R - R₀) + R₀‖ := by rw [sub_add_cancel]
    _ ≤ ‖R - R₀‖ + ‖R₀‖ := norm_add_le _ _
    _ ≤ 6 * δ + C * M ^ n * d := add_le_add hEpart hbare
    _ = 6 * δ + (C * 4 ^ n * 1448) * T ^ (2 * n + 8) * δ := by
      dsimp only [M, d]
      rw [mul_pow, pow_add, pow_mul]
      ring
    _ ≤ (C * 4 ^ n * 1448 + 6) * T ^ (2 * n + 8) * δ := by
      nlinarith only [mul_le_mul_of_nonneg_right (one_le_pow₀ hT₁ (n := 2 * n + 8)) hδ]

end TorusEuler.MovingAmplitude

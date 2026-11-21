import Breakdown.Held.Statements

noncomputable section

namespace Breakdown.Held

private lemma abs_sum_mul_le_sqrt_mul_sqrt {k : ℕ} (f g : Fin k → ℝ) :
    |∑ j, f j * g j| ≤ Real.sqrt (∑ j, f j ^ 2) * Real.sqrt (∑ j, g j ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun j _ => sq_nonneg (f j))]
  exact Real.abs_le_sqrt (Finset.sum_mul_sq_le_sq_mul_sq _ _ _)

theorem adjointEnclosure : AdjointEnclosureStatement := by
  intro Y V _ _ _ _ k E L Q b pin ζ c u₀ δ l μ r hE hμ hδ hl hL u κ R hQ heq hr
  have hR : inner ℝ R ζ =
      -(inner ℝ (L u) ζ + ∑ j, κ j * inner ℝ (b j) ζ + inner ℝ (Q u) ζ) := by
    have h1 : R = -(L u + ∑ j, κ j • b j + Q u) := by rw [heq, neg_neg]
    rw [h1, inner_neg_left, inner_add_left, inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  set e : Fin k → ℝ := fun j => inner ℝ (b j) ζ - u₀ j with he
  have hsplit : ∑ j, u₀ j * κ j + inner ℝ R ζ + ∑ j, c j * pin u j =
      -(inner ℝ (L u) ζ - ∑ j, c j * pin u j) - ∑ j, κ j * e j - inner ℝ (Q u) ζ := by
    rw [hR]
    simp only [he, mul_sub, Finset.sum_sub_distrib]
    have hc : ∑ j, u₀ j * κ j = ∑ j, κ j * u₀ j :=
      Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [hc]
    ring
  set S := ∑ j, κ j ^ 2 with hSdef
  set T := ∑ j, e j ^ 2 with hTdef
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hEu := hE u
  set X := E u + μ ^ 2 * S with hXdef
  have hX : 0 ≤ X := by positivity
  have hr0 : 0 ≤ r := (Real.sqrt_nonneg X).trans hr
  have hXr : X ≤ r ^ 2 := (Real.sqrt_le_left hr0).1 hr
  have hEr : E u ≤ r ^ 2 := by
    have : 0 ≤ μ ^ 2 * S := by positivity
    linarith
  have hA2 : Real.sqrt (E u) ^ 2 = E u := Real.sq_sqrt hEu
  have hB2 : Real.sqrt S ^ 2 = S := Real.sq_sqrt hS
  have hC2 : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT
  have hA : 0 ≤ Real.sqrt (E u) := Real.sqrt_nonneg _
  have hB : 0 ≤ Real.sqrt S := Real.sqrt_nonneg _
  have hC : 0 ≤ Real.sqrt T := Real.sqrt_nonneg _
  have hμ2 : 0 < μ ^ 2 := by positivity
  have hW : 0 ≤ δ ^ 2 + T / μ ^ 2 := by positivity
  have hD2 : Real.sqrt (δ ^ 2 + T / μ ^ 2) ^ 2 = δ ^ 2 + T / μ ^ 2 := Real.sq_sqrt hW
  have hD : 0 ≤ Real.sqrt (δ ^ 2 + T / μ ^ 2) := Real.sqrt_nonneg _
  have h1 := hL u
  have h2 : |∑ j, κ j * e j| ≤ Real.sqrt S * Real.sqrt T := abs_sum_mul_le_sqrt_mul_sqrt κ e
  have h3 : δ * Real.sqrt (E u) + Real.sqrt S * Real.sqrt T ≤
      r * Real.sqrt (δ ^ 2 + T / μ ^ 2) := by
    have hCst : μ ^ 2 * (δ * Real.sqrt (E u) + Real.sqrt S * Real.sqrt T) ^ 2 +
        (δ * μ ^ 2 * Real.sqrt S - Real.sqrt T * Real.sqrt (E u)) ^ 2 =
        (μ ^ 2 * δ ^ 2 + Real.sqrt T ^ 2) * (Real.sqrt (E u) ^ 2 + μ ^ 2 * Real.sqrt S ^ 2) := by
      ring
    rw [hA2, hB2, hC2] at hCst
    have hmain : μ ^ 2 * (δ * Real.sqrt (E u) + Real.sqrt S * Real.sqrt T) ^ 2 ≤
        (μ ^ 2 * δ ^ 2 + T) * r ^ 2 := by
      have hq := sq_nonneg (δ * μ ^ 2 * Real.sqrt S - Real.sqrt T * Real.sqrt (E u))
      have hm : (μ ^ 2 * δ ^ 2 + T) * X ≤ (μ ^ 2 * δ ^ 2 + T) * r ^ 2 :=
        mul_le_mul_of_nonneg_left hXr (by positivity)
      linarith
    have key : (δ * Real.sqrt (E u) + Real.sqrt S * Real.sqrt T) ^ 2 ≤
        (r * Real.sqrt (δ ^ 2 + T / μ ^ 2)) ^ 2 := by
      rw [mul_pow, hD2]
      have hid : r ^ 2 * (δ ^ 2 + T / μ ^ 2) = (μ ^ 2 * δ ^ 2 + T) * r ^ 2 / μ ^ 2 := by
        field_simp
      rw [hid, le_div_iff₀ hμ2]
      linarith
    have hsq := Real.sqrt_le_sqrt key
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (by positivity)] at hsq
  have h4 : l * E u ≤ l * r ^ 2 := mul_le_mul_of_nonneg_left hEr hl
  rw [hsplit]
  have a1 := abs_le.1 h1
  have a2 := abs_le.1 h2
  have a3 := abs_le.1 hQ
  rw [abs_le]
  constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]

end Breakdown.Held

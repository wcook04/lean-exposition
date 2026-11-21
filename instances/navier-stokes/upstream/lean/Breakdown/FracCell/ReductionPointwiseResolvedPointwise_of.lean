import Breakdown.FracCell.ReductionPointwiseDefs

namespace Breakdown.CellCert.Reduction

open SteadyCert Assembly CellAnalysis

private theorem sesq_scalar (a : ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    sesqValue (strainScalarMatrix a) (pairVec s v) = a * sumSq s := by
  have h1 : ∀ U : Fin 12 → ℂ, sesqValue (strainScalarMatrix a) U =
      ∑ i : Fin 12, ((starRingEnd ℂ) (U i) * ((if i.val < 9 then (a : ℂ) else 0)) * U i).re := by
    intro U
    unfold sesqValue strainScalarMatrix
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i]
    · simp [Matrix.diagonal_apply_eq]
    · intro j _ hj
      simp [Matrix.diagonal_apply_ne _ (Ne.symm hj)]
    · simp
  rw [h1]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, sumSq, pairVec]
  simp
  simp only [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem sumSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s := by
  unfold sumSq
  positivity

private theorem curlSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by
  unfold curlSq
  positivity

private theorem vecSq_nonneg (v : Fin 3 → ℂ) : 0 ≤ vecSq v := by
  unfold vecSq
  positivity

private theorem lin_le {lo hi r : ℝ} (x : ℝ) (h1 : lo ≤ r) (h2 : r ≤ hi) :
    r * x ≤ max (lo * x) (hi * x) := by
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (mul_le_mul_of_nonneg_right h2 hx)
  · exact le_max_of_le_left (mul_le_mul_of_nonpos_right h1 hx)

private theorem two_mul_le (a b l : ℝ) (hl : 0 < l) : 2 * a * b ≤ l * a ^ 2 + b ^ 2 / l := by
  have h : l * a ^ 2 + b ^ 2 / l - 2 * a * b = (l * a - b) ^ 2 / l := by
    field_simp
    ring
  nlinarith [div_nonneg (sq_nonneg (l * a - b)) hl.le]

private theorem hbase {r lo hi aS C Sq V lam lamMax T g₀ g' k₀ k' l l₀ rc rs rv : ℝ}
    (hlo : 0 ≤ lo) (h1 : lo ≤ r) (h2 : r ≤ hi) (hC : 0 ≤ C) (hS : 0 ≤ Sq) (hV : 0 ≤ V)
    (hlam : lam ≤ lamMax) (hg₀ : T * g₀ ≤ 2 * k₀) (hg' : T * g' ≤ 2 * k') (hk₀ : 0 ≤ k₀) (hk' : 0 ≤ k')
    (hl : 0 < l) (hl₀ : 0 < l₀)
    (hrc : max (lo * lamMax) (hi * lamMax) ≤ rc)
    (hrs : max (lo * (k' * l + k₀ * l₀ - aS)) (hi * (k' * l + k₀ * l₀ - aS)) ≤ rs)
    (hrv : hi * (k' / l + k₀ / l₀) ≤ rv) :
    0 ≤ r * (aS * Sq - (lam * C + T * g₀ * Real.sqrt Sq * Real.sqrt V
        + (1 / 2) * T * g' * (l * Sq + V / l))) + rc * C + rs * Sq + rv * V := by
  have hr0 : 0 ≤ r := hlo.trans h1
  have hsS := Real.sqrt_nonneg Sq
  have hsV := Real.sqrt_nonneg V
  have am : 2 * Real.sqrt Sq * Real.sqrt V ≤ l₀ * Sq + V / l₀ := by
    have := two_mul_le (Real.sqrt Sq) (Real.sqrt V) l₀ hl₀
    rwa [Real.sq_sqrt hS, Real.sq_sqrt hV] at this
  have hA : lam * C ≤ lamMax * C := mul_le_mul_of_nonneg_right hlam hC
  have hB : T * g₀ * Real.sqrt Sq * Real.sqrt V ≤ k₀ * (l₀ * Sq + V / l₀) := by
    have e1 : T * g₀ * Real.sqrt Sq * Real.sqrt V = (T * g₀) * (Real.sqrt Sq * Real.sqrt V) := by ring
    have e2 : (T * g₀) * (Real.sqrt Sq * Real.sqrt V) ≤ (2 * k₀) * (Real.sqrt Sq * Real.sqrt V) :=
      mul_le_mul_of_nonneg_right hg₀ (mul_nonneg hsS hsV)
    have e3 : (2 * k₀) * (Real.sqrt Sq * Real.sqrt V) ≤ k₀ * (l₀ * Sq + V / l₀) := by
      have := mul_le_mul_of_nonneg_left am hk₀
      linarith
    linarith
  have hW : 0 ≤ l * Sq + V / l := by positivity
  have hD : (1 / 2) * T * g' * (l * Sq + V / l) ≤ k' * (l * Sq + V / l) := by
    have e1 : (1 / 2) * T * g' * (l * Sq + V / l) = (1 / 2) * (T * g') * (l * Sq + V / l) := by ring
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ hW
    linarith
  have hL : lam * C + T * g₀ * Real.sqrt Sq * Real.sqrt V + (1 / 2) * T * g' * (l * Sq + V / l) ≤
      lamMax * C + k₀ * (l₀ * Sq + V / l₀) + k' * (l * Sq + V / l) := by linarith
  have hM := mul_le_mul_of_nonneg_left hL hr0
  have c1 : r * lamMax ≤ rc := (lin_le lamMax h1 h2).trans hrc
  have c2 : r * (k' * l + k₀ * l₀ - aS) ≤ rs := (lin_le _ h1 h2).trans hrs
  have c3 : r * (k' / l + k₀ / l₀) ≤ rv := by
    have : 0 ≤ k' / l + k₀ / l₀ := by positivity
    exact (mul_le_mul_of_nonneg_right h2 this).trans hrv
  have key : r * (aS * Sq - (lamMax * C + k₀ * (l₀ * Sq + V / l₀) + k' * (l * Sq + V / l)))
      + rc * C + rs * Sq + rv * V = (rc - r * lamMax) * C + (rs - r * (k' * l + k₀ * l₀ - aS)) * Sq
      + (rv - r * (k' / l + k₀ / l₀)) * V := by ring
  have p1 := mul_nonneg (sub_nonneg.2 c1) hC
  have p2 := mul_nonneg (sub_nonneg.2 c2) hS
  have p3 := mul_nonneg (sub_nonneg.2 c3) hV
  nlinarith

theorem resolvedPointwise_of : ResolvedPointwiseStatement := by
  intro α k N c K S W aS lowConst _ hF hT hR
  refine ⟨?_, ?_⟩
  · intro n hn p hp s v
    rw [hR.local_form n hn p, sesq_scalar]
    unfold CellScalars.densityForm
    have hS := sumSq_nonneg s
    have hC := curlSq_nonneg s
    have hw := hT.weight_le p hp
    have hc := hT.consts_nonneg.2.2
    have h1 : aS ≤ c.curlWeight - c.coercivity * CellScalars.sampleWeight c p := by
      have := mul_le_mul_of_nonneg_left hw hc
      linarith [hR.strain_scalar_le]
    nlinarith [mul_nonneg hR.curl_coef_nonneg hC, mul_le_mul_of_nonneg_right h1 hS]
  · intro n hn p hp hp1 s v _
    unfold CellScalars.pairLoss supremumLoss
    rw [hR.local_form n hn p, sesq_scalar]
    simp only [hF.curl_form n, hF.strain_form n, hF.velocity_form n, if_pos hn]
    obtain ⟨hr1, hr2⟩ := hT.range_spec p hp hp1
    exact hbase hT.range_pos hr1 hr2 (curlSq_nonneg s) (sumSq_nonneg s) (vecSq_nonneg v)
      (hT.lam_le p hp) (hT.mean_le p hp) (hT.wave_le p hp) hT.consts_nonneg.1 hT.consts_nonneg.2.1
      hT.splitLength_pos hR.lowConst_pos hR.resolved_curl_ge hR.resolved_strain_ge hR.resolved_velocity_ge

end Breakdown.CellCert.Reduction

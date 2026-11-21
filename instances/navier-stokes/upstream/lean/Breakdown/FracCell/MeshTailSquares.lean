import Breakdown.FracCell.MeshTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailSquares

theorem proj_sq_sum_le {α : Type*} [MeasurableSpace α] {μ : Measure α} (s : Finset ℕ) (ρ : α → ℝ) (e : ℕ → α → ℝ)
    (g : α → ℂ) (hρ : ∀ᵐ x ∂μ, 0 ≤ ρ x)
    (hgg : Integrable (fun x => ρ x * ‖g x‖ ^ 2) μ)
    (hge : ∀ k ∈ s, Integrable (fun x => (ρ x : ℂ) * g x * (e k x : ℂ)) μ)
    (hee : ∀ k ∈ s, ∀ k' ∈ s, Integrable (fun x => ρ x * e k x * e k' x) μ)
    (horth : ∀ k ∈ s, ∀ k' ∈ s, ∫ x, ρ x * e k x * e k' x ∂μ = if k = k' then 1 else 0) :
    ∑ k ∈ s, ‖∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ‖ ^ 2 ≤ ∫ x, ρ x * ‖g x‖ ^ 2 ∂μ := by
  set a : ℕ → ℂ := fun k => ∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ with ha
  have hpt : ∀ x, ((ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 : ℝ) : ℂ)
      = ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))
        - ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))
        + ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x * e k x * e k' x : ℝ) : ℂ) := by
    intro x
    have hS' : (starRingEnd ℂ) (∑ k ∈ s, a k * (e k x : ℂ)) = ∑ k ∈ s, (starRingEnd ℂ) (a k) * (e k x : ℂ) := by
      rw [map_sum]; simp only [map_mul, Complex.conj_ofReal]
    have h1 : (ρ x : ℂ) * (g x * ∑ k ∈ s, (starRingEnd ℂ) (a k) * (e k x : ℂ))
        = ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
    have h2 : (ρ x : ℂ) * ((∑ k ∈ s, a k * (e k x : ℂ)) * (starRingEnd ℂ) (g x))
        = ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ)) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by simp only [map_mul, Complex.conj_ofReal]; ring
    have h3 : (ρ x : ℂ) * ((∑ k ∈ s, a k * (e k x : ℂ)) * ∑ k' ∈ s, (starRingEnd ℂ) (a k') * (e k' x : ℂ))
        = ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x * e k x * e k' x : ℝ) : ℂ) := by
      rw [Finset.sum_mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      push_cast; ring
    have h4 : ((ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 : ℝ) : ℂ)
        = (ρ x : ℂ) * ((g x - ∑ k ∈ s, a k * (e k x : ℂ)) * (starRingEnd ℂ) (g x - ∑ k ∈ s, a k * (e k x : ℂ))) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj']
    have h5 : ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ) = (ρ x : ℂ) * (g x * (starRingEnd ℂ) (g x)) := by
      rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.mul_conj']
    rw [h4, h5, map_sub, hS', ← h1, ← h2, ← h3]
    ring
  have hI1 : Integrable (fun x => ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)) μ := hgg.ofReal
  have hI2 : Integrable (fun x => ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))) μ :=
    integrable_finsetSum _ fun k hk => (hge k hk).const_mul _
  have hconj : ∀ k ∈ s, Integrable (fun x => (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := by
    intro k hk
    exact (Complex.conjCLE.toContinuousLinearMap).integrable_comp (hge k hk)
  have hI3 : Integrable (fun x => ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))) μ :=
    integrable_finsetSum _ fun k hk => (hconj k hk).const_mul _
  have hI4 : Integrable (fun x => ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) *
      ((ρ x * e k x * e k' x : ℝ) : ℂ)) μ :=
    integrable_finsetSum _ fun k hk => integrable_finsetSum _ fun k' hk' => ((hee k hk k' hk').ofReal).const_mul _
  have hint : (((∫ x, ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 ∂μ) : ℝ) : ℂ)
      = ((∫ x, ρ x * ‖g x‖ ^ 2 ∂μ : ℝ) : ℂ) - ((∑ k ∈ s, ‖a k‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    have hI12 : Integrable (fun x => ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := hI1.sub hI2
    have hI123 : Integrable (fun x => ((ρ x * ‖g x‖ ^ 2 : ℝ) : ℂ)
        - ∑ k ∈ s, (starRingEnd ℂ) (a k) * ((ρ x : ℂ) * g x * (e k x : ℂ))
        - ∑ k ∈ s, a k * (starRingEnd ℂ) ((ρ x : ℂ) * g x * (e k x : ℂ))) μ := hI12.sub hI3
    rw [integral_add hI123 hI4, integral_sub hI12 hI3, integral_sub hI1 hI2,
      integral_complex_ofReal, integral_finsetSum _ fun k hk => (hge k hk).const_mul _,
      integral_finsetSum _ fun k hk => (hconj k hk).const_mul _,
      integral_finsetSum _ fun k hk => integrable_finsetSum _ fun k' hk' => ((hee k hk k' hk').ofReal).const_mul _]
    simp only [integral_const_mul, integral_conj]
    have e4 : ∀ k ∈ s, ∫ x, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x * e k x * e k' x : ℝ) : ℂ) ∂μ
        = a k * (starRingEnd ℂ) (a k) := by
      intro k hk
      rw [integral_finsetSum _ fun k' hk' => ((hee k hk k' hk').ofReal).const_mul _]
      simp only [integral_const_mul, integral_complex_ofReal]
      rw [Finset.sum_congr rfl fun k' hk' => by rw [horth k hk k' hk']]
      rw [Finset.sum_eq_single_of_mem k hk (fun k' _ hne => by rw [if_neg (Ne.symm hne)]; simp)]
      simp
    rw [Finset.sum_congr rfl e4]
    have hak : ∀ k, (∫ x, (ρ x : ℂ) * g x * (e k x : ℂ) ∂μ) = a k := fun k => rfl
    simp only [hak]
    have e5 : ∀ k, (starRingEnd ℂ) (a k) * a k = ((‖a k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [mul_comm, Complex.mul_conj']; push_cast; ring
    have e6 : ∀ k, a k * (starRingEnd ℂ) (a k) = ((‖a k‖ ^ 2 : ℝ) : ℂ) := fun k => by
      rw [Complex.mul_conj']; push_cast; ring
    simp only [e5, e6]
    push_cast
    ring
  have hnn : 0 ≤ ∫ x, ρ x * ‖g x - ∑ k ∈ s, a k * (e k x : ℂ)‖ ^ 2 ∂μ :=
    integral_nonneg_of_ae (hρ.mono fun x hx => mul_nonneg hx (by positivity))
  have hre := congrArg Complex.re hint
  simp only [Complex.ofReal_re, Complex.sub_re] at hre
  linarith

theorem sum_mul_le_sqrt_mul {ι : Type*} (t : Finset ι) (f g : ι → ℝ) :
    ∑ i ∈ t, f i * g i ≤ Real.sqrt (∑ i ∈ t, f i ^ 2) * Real.sqrt (∑ i ∈ t, g i ^ 2) := by
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg (f i))]
  exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq t f g)

theorem swap4 {A B C : Type*} (sa : Finset A) (sb : Finset B) (sc : Finset C) (F : A → B → C → C → ℝ) :
    ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ c' ∈ sc, F a b c c' = ∑ c ∈ sc, ∑ c' ∈ sc, ∑ a ∈ sa, ∑ b ∈ sb, F a b c c' := by
  calc ∑ a ∈ sa, ∑ b ∈ sb, ∑ c ∈ sc, ∑ c' ∈ sc, F a b c c'
      = ∑ a ∈ sa, ∑ c ∈ sc, ∑ b ∈ sb, ∑ c' ∈ sc, F a b c c' :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ sc, ∑ a ∈ sa, ∑ b ∈ sb, ∑ c' ∈ sc, F a b c c' := Finset.sum_comm
    _ = ∑ c ∈ sc, ∑ a ∈ sa, ∑ c' ∈ sc, ∑ b ∈ sb, F a b c c' :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ c ∈ sc, ∑ c' ∈ sc, ∑ a ∈ sa, ∑ b ∈ sb, F a b c c' :=
        Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem weighted_sum_sq_le {O κ J : Type*} [Fintype O] (ks : Finset κ) (js : Finset J) (ω : O → ℝ) (hω : ∀ o, 0 ≤ ω o)
    (v : O → κ → J → ℂ) (δ U : κ → ℝ) (hδ : ∀ k, 0 ≤ δ k) (hU : ∀ k, 0 ≤ U k)
    (h : ∀ k ∈ ks, ∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ ^ 2 ≤ δ k ^ 2 * U k) :
    ∑ o, ω o * ∑ j ∈ js, ‖∑ k ∈ ks, v o k j‖ ^ 2 ≤ (∑ k ∈ ks, δ k) * ∑ k ∈ ks, δ k * U k := by
  set N : κ → ℝ := fun k => Real.sqrt (∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ ^ 2) with hN
  have hpair : ∀ k k', ∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ * ‖v o k' j‖ ≤ N k * N k' := by
    intro k k'
    have e : ∀ k'' : κ, ∑ o, ω o * ∑ j ∈ js, ‖v o k'' j‖ ^ 2
        = ∑ q ∈ (Finset.univ : Finset O) ×ˢ js, (Real.sqrt (ω q.1) * ‖v q.1 k'' q.2‖) ^ 2 := by
      intro k''
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (hω o)]
    have e2 : ∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ * ‖v o k' j‖
        = ∑ q ∈ (Finset.univ : Finset O) ×ˢ js,
            (Real.sqrt (ω q.1) * ‖v q.1 k q.2‖) * (Real.sqrt (ω q.1) * ‖v q.1 k' q.2‖) := by
      rw [Finset.sum_product]
      refine Finset.sum_congr rfl fun o _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have := Real.mul_self_sqrt (hω o)
      calc ω o * (‖v o k j‖ * ‖v o k' j‖)
          = (Real.sqrt (ω o) * Real.sqrt (ω o)) * (‖v o k j‖ * ‖v o k' j‖) := by rw [this]
        _ = _ := by ring
    rw [e2, hN]
    dsimp only
    rw [e k, e k']
    exact sum_mul_le_sqrt_mul _ _ _
  have hNle : ∀ k ∈ ks, N k ≤ δ k * Real.sqrt (U k) := by
    intro k hk
    rw [hN]; dsimp only
    calc Real.sqrt (∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ ^ 2) ≤ Real.sqrt (δ k ^ 2 * U k) := Real.sqrt_le_sqrt (h k hk)
      _ = δ k * Real.sqrt (U k) := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (hδ k)]
  calc ∑ o, ω o * ∑ j ∈ js, ‖∑ k ∈ ks, v o k j‖ ^ 2
      ≤ ∑ o, ω o * ∑ j ∈ js, (∑ k ∈ ks, ‖v o k j‖) ^ 2 := by
        refine Finset.sum_le_sum fun o _ => mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) (hω o)
        exact pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ = ∑ k ∈ ks, ∑ k' ∈ ks, ∑ o, ω o * ∑ j ∈ js, ‖v o k j‖ * ‖v o k' j‖ := by
        have hsq : ∀ o j, (∑ k ∈ ks, ‖v o k j‖) ^ 2 = ∑ k ∈ ks, ∑ k' ∈ ks, ‖v o k j‖ * ‖v o k' j‖ :=
          fun o j => by rw [sq, Finset.sum_mul_sum]
        simp only [hsq, Finset.mul_sum]
        exact swap4 Finset.univ js ks (fun o j k k' => ω o * (‖v o k j‖ * ‖v o k' j‖))
    _ ≤ ∑ k ∈ ks, ∑ k' ∈ ks, N k * N k' :=
        Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun k' _ => hpair k k'
    _ = (∑ k ∈ ks, N k) ^ 2 := by rw [sq, Finset.sum_mul_sum]
    _ ≤ (∑ k ∈ ks, δ k * Real.sqrt (U k)) ^ 2 :=
        pow_le_pow_left₀ (Finset.sum_nonneg fun k _ => Real.sqrt_nonneg _) (Finset.sum_le_sum hNle) 2
    _ = (∑ k ∈ ks, Real.sqrt (δ k) * (Real.sqrt (δ k) * Real.sqrt (U k))) ^ 2 := by
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← mul_assoc, Real.mul_self_sqrt (hδ k)]
    _ ≤ (∑ k ∈ ks, Real.sqrt (δ k) ^ 2) * ∑ k ∈ ks, (Real.sqrt (δ k) * Real.sqrt (U k)) ^ 2 :=
        Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ k ∈ ks, δ k) * ∑ k ∈ ks, δ k * U k := by
        congr 1
        · exact Finset.sum_congr rfl fun k _ => Real.sq_sqrt (hδ k)
        · exact Finset.sum_congr rfl fun k _ => by rw [mul_pow, Real.sq_sqrt (hδ k), Real.sq_sqrt (hU k)]

end MeshTailSquares

end CellAnalysis

end CellCert

end Breakdown

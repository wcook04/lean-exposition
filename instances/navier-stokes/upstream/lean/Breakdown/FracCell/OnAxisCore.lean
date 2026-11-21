import Breakdown.FracCell.OnAxisNorm

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.OnAxisCore

theorem cut_continuous (χ : ℝ → ℝ) (hχ : Continuous χ) (R : ℝ) (q : ℕ) (u : ℕ → ℝ → ℝ)
    (hu : ∀ j, Continuous (u j)) :
    Continuous (fun p : ℝ × ℝ => χ (p.1 / R) * ∑ j ∈ Finset.range (q + 1), p.1 ^ j * u j p.2) := by
  refine (hχ.comp (continuous_fst.div_const R)).mul (continuous_finsetSum _ fun j _ => ?_)
  exact (continuous_fst.pow j).mul ((hu j).comp continuous_snd)

theorem poly_continuous (P : ℝ[X][X]) : Continuous (fun p : ℝ × ℝ => twoVarEval P p.1 p.2) := by
  have h : (fun p : ℝ × ℝ => twoVarEval P p.1 p.2) = fun p : ℝ × ℝ =>
      ∑ i ∈ Finset.range (P.natDegree + 1), (P.coeff i).eval p.2 * p.1 ^ i := by
    funext p
    simp only [twoVarEval, Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
    rfl
  rw [h]
  refine continuous_finsetSum _ fun i _ => ?_
  exact ((P.coeff i).continuous.comp continuous_snd).mul (continuous_fst.pow i)

theorem smoothing_congr {g : CellBlock} {lam bound : ℝ} {φ φ₀ : Space → Space}
    (h : BlockSmoothing g lam bound φ₀) (he : φ =ᵐ[volume] φ₀) : BlockSmoothing g lam bound φ := by
  obtain ⟨ψ, Dψ, k1, k2, k3, k4, k5, ⟨f, hf, hF⟩, k7⟩ := h
  have hz : (0 : Space → Space) =ᵐ[volume] fun y => φ y - φ₀ y := he.mono fun y hy => by simp [hy]
  refine ⟨fun y => ψ y + (φ y - φ₀ y), Dψ, k1.add (MemLp.zero.ae_eq hz), k2, k3, fun T hT j => ?_, k5,
    ⟨f, hf, fun y => ?_⟩, ?_⟩
  · rw [← k4 T hT j]
    refine integral_congr_ae (he.mono fun y hy => ?_)
    simp [hy]
  · refine Eq.trans ?_ (hF y)
    show φ y - (ψ y + (φ y - φ₀ y)) = φ₀ y - ψ y
    abel
  · have e1 : (fun y => ‖φ y - (ψ y + (φ y - φ₀ y))‖ ^ 2) = fun y => ‖φ₀ y - ψ y‖ ^ 2 := by
      funext y
      congr 2
      abel
    have e2 : ∫ y, ‖φ y‖ ^ 2 = ∫ y, ‖φ₀ y‖ ^ 2 := integral_congr_ae (he.mono fun y hy => by simp [hy])
    rw [e1, e2]
    exact k7

theorem smoothing_of_everywhere {g : CellBlock} {lam bound : ℝ}
    (H : ∀ φ : Space → Space, (∃ A : Fin 2 → Fin 3 → Fin 2 → ℝ[X][X],
      (∀ s c t, (A s c t).natDegree ≤ g.degree ∧ ∀ j, ((A s c t).coeff j).natDegree ≤ g.degree) ∧
      (g.onAxis = true → ∀ s t, X ∣ A s 0 t ∧ X ∣ A s 1 t) ∧
      ∀ y, φ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
          * twoVarEval (A s c t) (radialCoord w) (w 2)) • frameVector c w) y) →
      MemLp φ 2 volume → BlockSmoothing g lam bound φ)
    (φ : Space → Space) (hφ : IsBlockField g φ) (hL : MemLp φ 2 volume) : BlockSmoothing g lam bound φ := by
  obtain ⟨A, h1, h2, h3⟩ := hφ
  exact smoothing_congr (H _ ⟨A, h1, h2, fun y => rfl⟩ (hL.ae_eq h3)) h3

end Internal.OnAxisCore

open Internal.OnAxisCore in
theorem onAxisCore_of_parts (h : RectAxisStatement) (hN : AxisNormStatement) (hL : AxisLiftStatement) :
    OnAxisCoreStatement := by
  intro g lam ν va vz χ hlam hax hin hmode hR hz hlow hν hA hI
  refine smoothing_of_everywhere fun φ hφ hφ2 => ?_
  obtain ⟨A, hdeg, hdiv, hφeq⟩ := hφ
  have hR0 : 0 < g.outerRadius := by rw [hin] at hR; exact hR
  have hνR : ν ≤ lam * g.outerRadius ^ 2 := by rw [hin, sub_zero] at hν; exact hν
  have hrect : ∀ s : Fin 2, ∀ c : Fin 3, ∃ u : ℕ → ℝ → ℝ, (∀ j, ContDiff ℝ 1 (u j)) ∧
      (∀ j, u j (if s = 0 then g.lowerHeight else -g.upperHeight) = 0 ∧
        u j (if s = 0 then g.upperHeight else -g.lowerHeight) = 0) ∧
      ((if c = 2 then 0 else 1 : ℕ) = 1 → u 0 = 0) ∧
      (∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
          ((twoVarEval (A s c 0) r z - χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * u j z) ^ 2
            + lam⁻¹ * (deriv (fun t => χ (t / g.outerRadius)
                * ∑ j ∈ Finset.range (g.degree + 1), t ^ j * u j z) r ^ 2
              + (χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * deriv (u j) z) ^ 2
              + ((if c = 2 then 0 else 1 : ℕ) : ℝ) ^ 2
                * (χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * u j z) ^ 2 / r ^ 2)) * r)
        ≤ (va + vz) * ∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
            twoVarEval (A s c 0) r z ^ 2 * r := by
    intro s c
    have hzs : (if s = 0 then g.lowerHeight else -g.upperHeight)
        < (if s = 0 then g.upperHeight else -g.lowerHeight) := by
      split_ifs <;> linarith
    have hIs : IntervalCertificate g.degree (lam * ((if s = 0 then g.upperHeight else -g.lowerHeight)
        - (if s = 0 then g.lowerHeight else -g.upperHeight)) ^ 2 / 4) vz := by
      have e : (if s = 0 then g.upperHeight else -g.lowerHeight)
          - (if s = 0 then g.lowerHeight else -g.upperHeight) = g.upperHeight - g.lowerHeight := by
        split_ifs <;> ring
      rw [e]
      exact hI
    refine h g.degree (if c = 2 then 0 else 1) g.outerRadius _ _ lam ν va vz χ hlam hR0 hzs
      (by split_ifs <;> norm_num) hνR hA hIs (A s c 0) (hdeg s c 0).1 (hdeg s c 0).2 ?_
    intro hi
    have hc : c ≠ 2 := by
      intro hc
      simp [hc] at hi
    fin_cases c
    · exact (hdiv hax s 0).1
    · exact (hdiv hax s 0).2
    · exact absurd rfl hc
  choose u hu1 hu2 hu3 hu4 using hrect
  obtain ⟨K, hK⟩ := hA.2.2.1
  have hχc : Continuous χ := hK.continuous
  obtain ⟨D, hψ2, hDm, hDi, hDw, hDmode, hbound⟩ := hL g χ u
    (fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y)
    hin hmode hR0 hz hlow hA.2.1 ⟨K, hK⟩ hu1 hu2 (fun s c hc => hu3 s c (by simp [hc])) (fun y => rfl)
  have hφf : ∀ y, φ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, twoVarEval (A s c 0) (radialCoord w) (w 2) • frameVector c w) y := by
    intro y
    rw [hφeq y, hmode]
    refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    funext w
    refine Finset.sum_congr rfl fun c _ => ?_
    congr 1
    simp [trigMode]
  have hPc : ∀ s c, Continuous (Function.uncurry (fun r z => twoVarEval (A s c 0) r z)) :=
    fun s c => poly_continuous (A s c 0)
  refine ⟨_, D, hψ2, hDm, hDi, hDw, hDmode, ?_, ?_⟩
  · refine ⟨fun s c t r z => if t = 0 then twoVarEval (A s c 0) r z
      - χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * u s c j z else 0, ?_, ?_⟩
    · intro s c t
      by_cases ht : t = 0
      · subst ht
        refine Continuous.measurable ?_
        exact (poly_continuous (A s c 0)).sub
          (cut_continuous χ hχc g.outerRadius g.degree (u s c) fun j => (hu1 s c j).continuous)
      · simp only [ht, if_false]
        exact measurable_const
    · intro y
      beta_reduce
      rw [hφf y, hmode, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      by_cases hy : y ∈ cellSolid g s
      · simp only [Set.indicator_of_mem hy]
        rw [← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [← sub_smul]
        congr 1
        simp [trigMode]
      · simp [Set.indicator_of_notMem hy]
  · have hφ2' : MemLp (fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
        (fun w => ∑ c : Fin 3, twoVarEval (A s c 0) (radialCoord w) (w 2) • frameVector c w) y) 2 volume := by
      have e : φ = fun y => ∑ s : Fin 2, Set.indicator (cellSolid g s)
          (fun w => ∑ c : Fin 3, twoVarEval (A s c 0) (radialCoord w) (w 2) • frameVector c w) y := funext hφf
      rw [← e]
      exact hφ2
    have hb := hbound lam (fun s c r z => twoVarEval (A s c 0) r z) hlam hPc hφ2'
    have hn := hN g (fun s c r z => twoVarEval (A s c 0) r z) hin hR0 hz hlow hPc hφ2'
    simp only [] at hb hn
    simp only [hφf]
    rw [hn]
    refine hb.trans ?_
    have hsum : ∑ s : Fin 2, ∑ c : Fin 3, (va + vz) * ∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
            twoVarEval (A s c 0) r z ^ 2 * r
        = (va + vz) * ∑ s : Fin 2, ∑ c : Fin 3, ∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
            twoVarEval (A s c 0) r z ^ 2 * r := by
      simp only [Finset.mul_sum]
    have hle := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) =>
      Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hu4 s c
    rw [hsum] at hle
    have h2π : (0 : ℝ) ≤ 2 * Real.pi := by positivity
    calc _ ≤ 2 * Real.pi * ((va + vz) * ∑ s : Fin 2, ∑ c : Fin 3, ∫ r in (0 : ℝ)..g.outerRadius,
          ∫ z in (if s = 0 then g.lowerHeight else -g.upperHeight)..(if s = 0 then g.upperHeight else -g.lowerHeight),
            twoVarEval (A s c 0) r z ^ 2 * r) := mul_le_mul_of_nonneg_left hle h2π
      _ = _ := by ring

theorem onAxisCore_of_rect (h : RectAxisStatement) (hL : AxisLiftStatement) : OnAxisCoreStatement :=
  onAxisCore_of_parts h axisNorm_holds hL

end Spectral

end CellCert

end Breakdown

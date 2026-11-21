import Breakdown.Uniqueness.RegUniqueAux3

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

theorem varConst_unique {F G : ℝ → Space → CSpace} {a b : ℝ} (hF : IsHsCurve 3 F a b)
    (hG : IsHsCurve 3 G a b) (hFd : IsVarConstSymbol F a b) (hGd : IsVarConstSymbol G a b)
    (hFs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) (hGs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (G t))
    (h : F a = G a) : ∀ t ∈ Icc a b, F t = G t := by
  have hm : ∀ H : ℝ → Space → CSpace, IsHsCurve 3 H a b → ∀ t ∈ Icc a b,
      AEStronglyMeasurable (H t) volume := fun H hH t ht => (hH.1 t ht).1
  have hfin : ∀ H : ℝ → Space → CSpace, IsHsCurve 3 H a b → ∀ t ∈ Icc a b,
      hsNormSq 3 (H t) < ⊤ := fun H hH t ht => (hH.1 t ht).2
  obtain ⟨CF, hCF, hFb⟩ := hsCurve_bound hF
  obtain ⟨CG, hCG, hGb⟩ := hsCurve_bound hG
  set C := max CF CG with hCdef
  have hC : C ≠ ⊤ := (max_lt hCF.lt_top hCG.lt_top).ne
  have hFC : ∀ t ∈ Icc a b, hsNormSq 3 (F t) ≤ C := fun t ht => (hFb t ht).trans (le_max_left _ _)
  have hGC : ∀ t ∈ Icc a b, hsNormSq 3 (G t) ≤ C := fun t ht => (hGb t ht).trans (le_max_right _ _)
  obtain ⟨C1, hC1⟩ := weightedFreqL1_le 1
  set Kₑ : ℝ≥0∞ := ENNReal.ofReal C1 * C ^ (1 / 2 : ℝ) with hKdef
  have hKt : Kₑ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC)
  set K := Kₑ.toReal with hKr
  have hK0 : 0 ≤ K := ENNReal.toReal_nonneg
  have hKK : ENNReal.ofReal K = Kₑ := ENNReal.ofReal_toReal hKt
  have hwt : ∀ H : ℝ → Space → CSpace, (∀ t ∈ Icc a b, hsNormSq 3 (H t) ≤ C) → ∀ t ∈ Icc a b,
      ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ 1) * ‖H t ξ‖ₑ ≤ ENNReal.ofReal K := by
    intro H hH t ht
    rw [hKK]
    refine (hC1 (H t)).trans ?_
    rw [hKdef]
    gcongr
    exact hH t ht
  have hFg : ∀ t ∈ Icc a b, gradFreqL1Norm (F t) ≤ ENNReal.ofReal K :=
    fun t ht => (gradFreqL1Norm_le_weighted _).trans (hwt F hFC t ht)
  have hGw : ∀ t ∈ Icc a b, freqL1Norm (G t) ≤ ENNReal.ofReal K :=
    fun t ht => (freqL1Norm_le_weighted _).trans (hwt G hGC t ht)
  have hcont : ∀ ξ, ContinuousOn (fun s => nonlinSymbol (F s) ξ - nonlinSymbol (G s) ξ) (Icc a b) :=
    fun ξ => (continuousOn_nonlinSymbol hF ξ).sub (continuousOn_nonlinSymbol hG ξ)
  set Q : ℝ≥0∞ := ENNReal.ofReal (36 * π) * ((2 * (C + C)) ^ (1 / 2 : ℝ) * C ^ (1 / 2 : ℝ) +
    C ^ (1 / 2 : ℝ) * (2 * (C + C)) ^ (1 / 2 : ℝ)) with hQdef
  have hQt : Q ≠ ⊤ := by
    have h2 : (2 * (C + C)) ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (by simp) (ENNReal.add_ne_top.2 ⟨hC, hC⟩))
    have h1 : C ^ (1 / 2 : ℝ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) hC
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top h2 h1, ENNReal.mul_ne_top h1 h2⟩)
  have hN0 : ∀ r ∈ Icc a b, ∀ ξ, ‖nonlinSymbol (F r) ξ - nonlinSymbol (G r) ξ‖ ≤ Q.toReal := by
    intro r hr ξ
    have := ENNReal.toReal_mono hQt
      (enorm_nonlinSymbol_sub_le_const (hm F hF r hr) (hm G hG r hr) hC (hFC r hr) (hGC r hr) ξ)
    simpa using this
  have hglob : ∀ t ∈ Icc a b, ∀ ξ, (1 + ‖ξ‖) * ‖F t ξ - G t ξ‖ ≤
      Q.toReal * ((b - a) + Real.sqrt (b - a)) := by
    intro t ht ξ
    rw [varConst_sub_eq hF hG hFd hGd h ht ξ]
    refine (heat_varConst_bound (M := Q.toReal) ξ (hcont ξ) le_rfl ht.1 ht.2 ?_ ?_).trans ?_
    · intro r hr
      rw [le_antisymm hr.2 hr.1, h, sub_self]
    · intro r hr
      exact hN0 r ⟨hr.1, hr.2.trans ht.2⟩ ξ
    · have htb := ht.2
      have hsq : Real.sqrt (t - a) ≤ Real.sqrt (b - a) := Real.sqrt_le_sqrt (by linarith)
      exact mul_le_mul_of_nonneg_left (add_le_add (by linarith) hsq) ENNReal.toReal_nonneg
  set δ : ℝ := 1 / (288 * π * K + 1) with hδdef
  have hpk : 0 ≤ π * K := mul_nonneg Real.pi_pos.le hK0
  have hden : 0 < 288 * π * K + 1 := by nlinarith
  have hδpos : 0 < δ := by positivity
  have hδmul : δ * (288 * π * K + 1) = 1 := by
    rw [hδdef]
    field_simp
  have hδ1 : δ ≤ 1 := by nlinarith
  set hh : ℝ := δ ^ 2 with hhdef
  have hhpos : 0 < hh := by positivity
  have hsq : Real.sqrt hh = δ := Real.sqrt_sq hδpos.le
  have hhδ : hh ≤ δ := by nlinarith
  have hq : 72 * π * K * (hh + Real.sqrt hh) ≤ 1 / 2 := by
    rw [hsq]
    nlinarith
  have hstep : ∀ n : ℕ, (∀ t ∈ Icc a b, t ≤ a + n * hh → F t = G t) →
      ∀ t ∈ Icc a b, t ≤ a + n * hh + hh → F t = G t := by
    intro n hn
    set T := a + n * hh with hT
    have haT : a ≤ T := by
      have : (0 : ℝ) ≤ n * hh := by positivity
      linarith
    have hk : ∀ k : ℕ, ∀ t ∈ Icc a b, t ≤ T + hh → ∀ ξ, (1 + ‖ξ‖) * ‖F t ξ - G t ξ‖ ≤
        Q.toReal * ((b - a) + Real.sqrt (b - a)) * (1 / 2) ^ k := by
      intro k
      induction k with
      | zero =>
        intro t ht _ ξ
        simpa using hglob t ht ξ
      | succ k ih =>
        intro t ht htT ξ
        have hba : 0 ≤ (b - a) + Real.sqrt (b - a) := by
          have := ht.1.trans ht.2
          have := Real.sqrt_nonneg (b - a)
          linarith
        set B := Q.toReal * ((b - a) + Real.sqrt (b - a)) * (1 / 2) ^ k with hB
        have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hba) (by positivity)
        by_cases htT' : t ≤ T
        · rw [hn t ht htT', sub_self, norm_zero, mul_zero]
          exact mul_nonneg (mul_nonneg ENNReal.toReal_nonneg hba) (by positivity)
        · rw [not_le] at htT'
          rw [varConst_sub_eq hF hG hFd hGd h ht ξ]
          refine (heat_varConst_bound (M := 72 * π * K * B) ξ (hcont ξ) haT htT'.le ht.2 ?_ ?_).trans ?_
          · intro r hr
            have hrab : r ∈ Icc a b := ⟨hr.1, hr.2.trans (htT'.le.trans ht.2)⟩
            rw [hn r hrab hr.2, sub_self]
          · intro r hr
            have hrab : r ∈ Icc a b := ⟨haT.trans hr.1, hr.2.trans ht.2⟩
            exact norm_nonlinSymbol_sub_le_of_bound (hm F hF r hrab) (hm G hG r hrab)
              (hfin F hF r hrab) (hfin G hG r hrab) hK0 hB0 (hFg r hrab) (hGw r hrab)
              (fun η => ih r hrab (hr.2.trans htT) η) ξ
          · have htd : t - T ≤ hh := by linarith
            have hc0 : 0 ≤ 72 * π * K * B := by
              have := Real.pi_pos
              exact mul_nonneg (by positivity) hB0
            calc 72 * π * K * B * ((t - T) + Real.sqrt (t - T))
                ≤ 72 * π * K * B * (hh + Real.sqrt hh) :=
                  mul_le_mul_of_nonneg_left (add_le_add htd (Real.sqrt_le_sqrt htd)) hc0
              _ = B * (72 * π * K * (hh + Real.sqrt hh)) := by ring
              _ ≤ B * (1 / 2) := mul_le_mul_of_nonneg_left hq hB0
              _ = Q.toReal * ((b - a) + Real.sqrt (b - a)) * (1 / 2) ^ (k + 1) := by
                  rw [hB, pow_succ]
                  ring
    intro t ht htT
    funext ξ
    have hx : ∀ k : ℕ, (1 + ‖ξ‖) * ‖F t ξ - G t ξ‖ ≤
        Q.toReal * ((b - a) + Real.sqrt (b - a)) * (1 / 2) ^ k := fun k => hk k t ht htT ξ
    have hlim : Tendsto (fun k : ℕ => Q.toReal * ((b - a) + Real.sqrt (b - a)) * (1 / 2 : ℝ) ^ k)
        atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul (Q.toReal * ((b - a) + Real.sqrt (b - a)))
    have hle : (1 + ‖ξ‖) * ‖F t ξ - G t ξ‖ ≤ 0 := ge_of_tendsto' hlim hx
    have hn0 : ‖F t ξ - G t ξ‖ ≤ 0 := by
      nlinarith [norm_nonneg ξ, norm_nonneg (F t ξ - G t ξ)]
    exact sub_eq_zero.1 (norm_le_zero_iff.1 hn0)
  have hall : ∀ n : ℕ, ∀ t ∈ Icc a b, t ≤ a + n * hh → F t = G t := by
    intro n
    induction n with
    | zero =>
      intro t ht ht0
      have : t = a := le_antisymm (by simpa using ht0) ht.1
      rw [this]
      exact h
    | succ n ih =>
      intro t ht htn
      exact hstep n ih t ht (by push_cast at htn; linarith)
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge ((t - a) / hh)
  refine hall n t ht ?_
  rw [div_le_iff₀ hhpos] at hn
  linarith

end Breakdown.SmoothFlow

import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegLocalAuxSymm
import Breakdown.Uniqueness.RegLocalAuxLimit
import Breakdown.Uniqueness.RegLocalAuxHs

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

private def iter (α a : ℝ) (F₀ : Space → CSpace) : ℕ → ℝ → Space → CSpace
  | 0 => fun _ => F₀
  | n + 1 => powerMildMap α a F₀ (iter α a F₀ n)

private theorem hsNormSq_neg (m : ℕ) (f : Space → CSpace) : hsNormSq m (-f) = hsNormSq m f := by
  simp [hsNormSq]

private theorem hsNormSq_sub_comm (m : ℕ) (f g : Space → CSpace) :
    hsNormSq m (f - g) = hsNormSq m (g - f) := by
  rw [← neg_sub, hsNormSq_neg]

private theorem two_mul_ofReal (x : ℝ) :
    (2 : ℝ≥0∞) * ENNReal.ofReal x = ENNReal.ofReal (2 * x) := by
  rw [ENNReal.ofReal_mul (by norm_num)]
  simp

end PowerInternal

open PowerInternal in
theorem powerFixedPoint_of (α : ℝ) (hα : 1 < α) (h1 : PowerMildMapBasicStatement α)
    (h2 : PowerMildMapEstStatement α) (h3 : PowerMildMapCurveStatement α) :
    PowerFixedPointStatement α := by
  intro m hm R
  obtain ⟨C1, hC1, hbd⟩ := h2.1 m hm
  obtain ⟨C2, hC2, hctr⟩ := h2.2 m hm
  set R' := max R 1 with hR'
  set B := 4 * R' with hB
  set C := max C1 C2 with hC
  have hR'1 : 1 ≤ R' := le_max_right _ _
  have hR'0 : 0 < R' := by linarith
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hCpos : 0 < C := lt_of_lt_of_le hC1 (le_max_left _ _)
  set δ := min 1 (1 / (16 * C * R')) with hδdef
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδC : δ * (16 * C * R') ≤ 1 := by
    have h := min_le_right 1 (1 / (16 * C * R'))
    rw [← hδdef, le_div_iff₀ (by positivity)] at h
    exact h
  have hCδB : C * δ * B ≤ 1 / 4 := by
    have : C * δ * B = δ * (16 * C * R') / 4 := by rw [hB]; ring
    rw [this]
    linarith
  have hC2δB : C2 * δ * B ≤ 1 / 4 :=
    le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le) hB0)
      hCδB
  have hC1δB : C1 * δ * B ^ 2 ≤ R' := by
    have h1' : C1 * δ * B ≤ 1 / 4 :=
      le_trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le) hB0)
        hCδB
    have : C1 * δ * B ^ 2 = (C1 * δ * B) * B := by ring
    rw [this]
    nlinarith
  refine ⟨δ, hδ, fun a F₀ hmeas hsol hR => ?_⟩
  have hF₀R' : hsNormSq m F₀ ≤ ENNReal.ofReal R' :=
    hR.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hF₀B : hsNormSq m F₀ ≤ ENNReal.ofReal B :=
    hF₀R'.trans (ENNReal.ofReal_le_ofReal (by rw [hB]; linarith))
  have hfin : hsNormSq m F₀ < ⊤ := lt_of_le_of_lt hR ENNReal.ofReal_lt_top
  have hsub : ∀ t ∈ Icc a (a + δ), ∀ s ∈ uIcc a t, s ∈ Icc a (a + δ) := by
    intro t ht s hs
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  set G := iter α a F₀ with hGdef
  have hG0 : G 0 = fun _ => F₀ := rfl
  have hGs : ∀ n, G (n + 1) = powerMildMap α a F₀ (G n) := fun n => rfl
  have hP : ∀ n, IsHsCurve m (G n) a (a + δ) ∧
      (∀ t ∈ Icc a (a + δ), hsNormSq m (G n t) ≤ ENNReal.ofReal B) ∧
      (∀ t ∈ Icc a (a + δ), ∀ᵐ ξ ∂volume, G n t (-ξ) = conjVec (G n t ξ)) := by
    intro n
    induction n with
    | zero =>
      rw [hG0]
      refine ⟨⟨fun t _ => ⟨hmeas, hfin⟩, fun t₀ _ => ?_⟩, fun t _ => hF₀B,
        fun t _ => Eventually.of_forall fun ξ => (hsol ξ).2⟩
      simp only [sub_self]
      have h0 : hsNormSq m (0 : Space → CSpace) = 0 := by simp [hsNormSq]
      rw [h0]
      exact tendsto_const_nhds
    | succ n ih =>
      obtain ⟨hc, hb, hj⟩ := ih
      rw [hGs]
      refine ⟨h3 m hm a δ F₀ (G n) hδ hmeas hfin hc, fun t ht => ?_,
        fun t ht => Eventually.of_forall fun ξ =>
          (h1.2 a F₀ (G n) t hsol (fun s hs => hj s (hsub t ht s hs)) ξ).2⟩
      refine (hbd a δ B F₀ (G n) hδ hδ1 hmeas hc hb t ht).trans ?_
      calc 2 * hsNormSq m F₀ + ENNReal.ofReal (C1 * δ * B ^ 2)
          ≤ 2 * ENNReal.ofReal R' + ENNReal.ofReal R' := by
            gcongr
        _ = ENNReal.ofReal (2 * R' + R') := by
            rw [two_mul_ofReal R', ENNReal.ofReal_add (by linarith) hR'0.le]
        _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal (by rw [hB]; linarith)
  set K := 4 * B with hK
  have hK0 : 0 ≤ K := by rw [hK]; linarith
  have hstep : ∀ n, ∀ t ∈ Icc a (a + δ),
      hsNormSq m (G (n + 1) t - G n t) ≤ ENNReal.ofReal (K * (1 / 4) ^ n) := by
    intro n
    induction n with
    | zero =>
      intro t ht
      have hm1 := ((hP 1).1.1 t ht).1
      rw [sub_eq_add_neg]
      refine (hsNormSq_add_le m hm1 ((hP 0).1.1 t ht).1.neg).trans ?_
      rw [hsNormSq_neg]
      calc 2 * hsNormSq m (G 1 t) + 2 * hsNormSq m (G 0 t)
          ≤ 2 * ENNReal.ofReal B + 2 * ENNReal.ofReal B := by
            gcongr
            · exact (hP 1).2.1 t ht
            · exact (hP 0).2.1 t ht
        _ = ENNReal.ofReal (K * (1 / 4) ^ 0) := by
            rw [two_mul_ofReal B, ← ENNReal.ofReal_add (by linarith) (by linarith), hK]
            congr 1
            ring
    | succ n ih =>
      intro t ht
      rw [hGs (n + 1), hGs n]
      refine (hctr a δ B F₀ (G (n + 1)) (G n) hδ hδ1 hmeas hfin (hP (n + 1)).1 (hP n).1
        (hP (n + 1)).2.1 (hP n).2.1 t ht).trans ?_
      have hsup : ⨆ s ∈ Icc a (a + δ), hsNormSq m (G (n + 1) s - G n s) ≤
          ENNReal.ofReal (K * (1 / 4) ^ n) := iSup₂_le fun s hs => ih s hs
      calc ENNReal.ofReal (C2 * δ * B) * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G (n + 1) s - G n s)
          ≤ ENNReal.ofReal (1 / 4) * ENNReal.ofReal (K * (1 / 4) ^ n) := by
            gcongr
        _ = ENNReal.ofReal (K * (1 / 4) ^ (n + 1)) := by
            rw [← ENNReal.ofReal_mul (by norm_num)]
            congr 1
            ring
  obtain ⟨L, hLc, hLB, hLconj, hLt⟩ :=
    hsCurve_limit m a (a + δ) B K G (fun n => (hP n).1) (fun n => (hP n).2.1)
      (fun n => (hP n).2.2) hstep
  refine ⟨L, hLc, fun t ht => ?_, hLconj⟩
  have hD := h3 m hm a δ F₀ L hδ hmeas hfin hLc
  set c := C2 * δ * B with hc
  have hbound : ∀ n, hsNormSq m (powerMildMap α a F₀ L t - L t) ≤
      2 * (ENNReal.ofReal c * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G n s - L s)) +
        2 * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G (n + 1) s - L s) := by
    intro n
    have hdec : powerMildMap α a F₀ L t - L t =
        (powerMildMap α a F₀ L t - G (n + 1) t) + (G (n + 1) t - L t) := by abel
    rw [hdec]
    refine (hsNormSq_add_le m (((hD.1 t ht).1).sub ((hP (n + 1)).1.1 t ht).1)
      ((((hP (n + 1)).1.1 t ht).1).sub (hLc.1 t ht).1)).trans ?_
    gcongr
    · rw [hGs n]
      refine (hctr a δ B F₀ L (G n) hδ hδ1 hmeas hfin hLc (hP n).1 hLB (hP n).2.1 t ht).trans ?_
      gcongr with s hs
      rw [hsNormSq_sub_comm]
    · exact le_iSup₂ (f := fun s _ => hsNormSq m (G (n + 1) s - L s)) t ht
  have hlim : Tendsto (fun n => 2 * (ENNReal.ofReal c * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G n s - L s)) +
      2 * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G (n + 1) s - L s)) atTop (𝓝 0) := by
    have e1 : Tendsto (fun n => ENNReal.ofReal c * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G n s - L s))
        atTop (𝓝 (ENNReal.ofReal c * 0)) :=
      ENNReal.Tendsto.const_mul hLt (Or.inr ENNReal.ofReal_ne_top)
    have e2 : Tendsto (fun n => 2 * (ENNReal.ofReal c * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G n s - L s)))
        atTop (𝓝 (2 * (ENNReal.ofReal c * 0))) :=
      ENNReal.Tendsto.const_mul e1 (Or.inr (by norm_num))
    have e3 : Tendsto (fun n => 2 * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G (n + 1) s - L s))
        atTop (𝓝 (2 * 0)) :=
      ENNReal.Tendsto.const_mul (hLt.comp (tendsto_add_atTop_nat 1)) (Or.inr (by norm_num))
    simpa using e2.add e3
  have hzero : hsNormSq m (powerMildMap α a F₀ L t - L t) = 0 :=
    le_antisymm (ge_of_tendsto' hlim hbound) bot_le
  have hae := ae_eq_zero_of_hsNormSq_eq_zero m (((hD.1 t ht).1).sub (hLc.1 t ht).1) hzero
  filter_upwards [hae] with ξ hξ
  have := sub_eq_zero.mp hξ
  exact this.symm

theorem powerLocal_of (α : ℝ) (hα : 1 < α) (h1 : PowerFixedPointStatement α)
    (h2 : PowerMildMapBasicStatement α) : PowerLocalStatement α := by
  intro m hm R
  obtain ⟨δ, hδ, hfix⟩ := h1 m hm R
  refine ⟨δ, hδ, fun a F₀ hmeas hsol hR => ?_⟩
  obtain ⟨G, hGc, hGfix, hGconj⟩ := hfix a F₀ hmeas hsol hR
  have hFG : ∀ t ∈ Icc a (a + δ), powerMildMap α a F₀ G t =ᵐ[volume] G t :=
    fun t ht => (hGfix t ht).symm
  have hsub : ∀ t ∈ Icc a (a + δ), ∀ s ∈ uIcc a t, s ∈ Icc a (a + δ) := by
    intro t ht s hs
    rw [uIcc_of_le ht.1] at hs
    exact ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨powerMildMap α a F₀ G, h2.1 a F₀ G, isHsCurve_congr hGc hFG, ?_, ?_⟩
  · intro t ht ξ
    rw [h2.1 a F₀ G]
    conv_lhs => rw [powerMildMap]
    congr 1
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [nonlinSymbol_congr_ae (hFG s (hsub t ht s hs))]
  · intro t ht
    exact h2.2 a F₀ G t hsol fun s hs => hGconj s (hsub t ht s hs)

end Breakdown.SmoothFlow

import Breakdown.Uniqueness.RegPersistAuxGain

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private theorem hsNormSq_add_le_two (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  rw [← fracNormSq_natCast, ← fracNormSq_natCast, ← fracNormSq_natCast]
  exact fracNormSq_add_le _ hf hg

private theorem hsNormSq_sub_le_two (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f - g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  rw [← fracNormSq_natCast, ← fracNormSq_natCast, ← fracNormSq_natCast]
  exact fracNormSq_sub_le _ hf hg

private theorem tendsto_zero_of_le_two {l : Filter ℝ} {u v w : ℝ → ℝ≥0∞}
    (hu : Tendsto u l (𝓝 0)) (hv : Tendsto v l (𝓝 0)) (h : ∀ᶠ t in l, w t ≤ 2 * u t + 2 * v t) :
    Tendsto w l (𝓝 0) := by
  have h2 : Tendsto (fun t => 2 * u t + 2 * v t) l (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hu (Or.inr (by norm_num))).add
      (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hv (Or.inr (by norm_num)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2 (Eventually.of_forall fun _ => zero_le) h

private theorem persist_bound {m : ℕ} (hm : 3 ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (hd : IsVarConstSymbol F a b)
    (hs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) (h0 : hsNormSq m (F a) < ⊤) :
    ∀ n : ℕ, n ≤ 2 * (m - 3) →
      ∃ B : ℝ, ∀ t ∈ Icc a b, fracNormSq (3 + (n : ℝ) / 2) (F t) ≤ ENNReal.ofReal B := by
  intro n
  induction n with
  | zero =>
    intro _
    obtain ⟨B, hB⟩ := hsNormSq_bdd_of_curve h3
    refine ⟨B, fun t ht => ?_⟩
    have h := fracNormSq_natCast 3 (F t)
    have e : (3 + ((0 : ℕ) : ℝ) / 2) = ((3 : ℕ) : ℝ) := by norm_num
    rw [e, h]
    exact hB t ht
  | succ n ih =>
    intro hn
    obtain ⟨B, hB⟩ := ih (by omega)
    obtain ⟨B', hB'⟩ := fracNormSq_varConst_gain h3 hd hs (r := 3 + (n : ℝ) / 2) (by positivity) hB
    have hn' : n + 1 + 6 ≤ 2 * m := by omega
    have hnr : ((n + 1 + 6 : ℕ) : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hn'
    push_cast at hnr
    have heq : (3 + ((n + 1 : ℕ) : ℝ) / 2) = 3 + (n : ℝ) / 2 + 1 / 2 := by push_cast; ring
    have hle : 3 + (n : ℝ) / 2 + 1 / 2 ≤ (m : ℝ) := by linarith
    have hfin : 2 * hsNormSq m (F a) + 2 * ENNReal.ofReal B' ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) h0.ne,
        ENNReal.mul_ne_top (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) ENNReal.ofReal_ne_top⟩
    refine ⟨(2 * hsNormSq m (F a) + 2 * ENNReal.ofReal B').toReal, fun t ht => ?_⟩
    rw [ENNReal.ofReal_toReal hfin, heq]
    have hFa : AEStronglyMeasurable (F a) volume := (h3.1 a ⟨le_rfl, ht.1.trans ht.2⟩).1
    have hsplit : F t = heatPart a (F a) t + (F t - heatPart a (F a) t) := (add_sub_cancel _ _).symm
    calc fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F t)
        = fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (heatPart a (F a) t + (F t - heatPart a (F a) t)) := by
          rw [← hsplit]
      _ ≤ 2 * fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (heatPart a (F a) t) +
          2 * fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F t - heatPart a (F a) t) :=
            fracNormSq_add_le _ (aestronglyMeasurable_heatPart hFa _ _)
              ((h3.1 t ht).1.sub (aestronglyMeasurable_heatPart hFa _ _))
      _ ≤ 2 * hsNormSq m (F a) + 2 * ENNReal.ofReal B' := by
          gcongr
          · calc fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (heatPart a (F a) t)
                ≤ fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F a) := fracNormSq_heatPart_le _ ht.1 _
              _ ≤ fracNormSq (m : ℝ) (F a) := fracNormSq_mono hle _
              _ = hsNormSq m (F a) := fracNormSq_natCast m _
          · exact hB' t ht

theorem isHsCurve_of_persist {m : ℕ} (hm : 3 ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (hd : IsVarConstSymbol F a b)
    (hs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) (h0 : hsNormSq m (F a) < ⊤) :
    IsHsCurve m F a b := by
  rcases lt_or_ge b a with hba | hab
  · refine ⟨fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hba), fun t ht => ?_⟩
    exact absurd (ht.1.trans ht.2) (not_le.mpr hba)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨Bm, hBm⟩ := persist_bound hm h3 hd hs h0 (2 * (m - 3)) le_rfl
  have hlev : (3 + ((2 * (m - 3) : ℕ) : ℝ) / 2) = (m : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [hlev] at hBm
  have hBHs : ∀ t ∈ Icc a b, hsNormSq m (F t) ≤ ENNReal.ofReal Bm := fun t ht => by
    rw [← fracNormSq_natCast]
    exact hBm t ht
  refine ⟨fun t ht => ⟨(h3.1 t ht).1, (hBHs t ht).trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  obtain ⟨B', hB'⟩ := fracNormSq_varConst_gain h3 hd hs (r := (m : ℝ)) (by positivity) hBm
  set G : ℝ → Space → CSpace := fun t => F t - heatPart a (F a) t with hGdef
  have hheat : ∀ k : ℕ, hsNormSq k (F a) < ⊤ → ∀ t₀ ∈ Icc a b,
      Tendsto (fun t => hsNormSq k (heatPart a (F a) t - heatPart a (F a) t₀)) (𝓝[Icc a b] t₀) (𝓝 0) :=
    fun k hk t₀ ht₀ => tendsto_hsNormSq_heatPart (h3.1 a ha).1 hk t₀ ht₀
  have hHm : ∀ t, AEStronglyMeasurable (heatPart a (F a) t) volume :=
    fun t => aestronglyMeasurable_heatPart (h3.1 a ha).1 a t
  have hGmeas : ∀ t ∈ Icc a b, AEStronglyMeasurable (G t) volume :=
    fun t ht => (h3.1 t ht).1.sub (hHm t)
  have hG3 : ∀ t₀ ∈ Icc a b, Tendsto (fun t => hsNormSq 3 (G t - G t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
    intro t₀ ht₀
    refine tendsto_zero_of_le_two (h3.2 t₀ ht₀) (hheat 3 (h3.1 a ha).2 t₀ ht₀) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have e : G t - G t₀ = (F t - F t₀) - (heatPart a (F a) t - heatPart a (F a) t₀) := by
      simp only [hGdef]
      exact sub_sub_sub_comm _ _ _ _
    rw [e]
    exact hsNormSq_sub_le_two 3 ((h3.1 t ht).1.sub (h3.1 t₀ ht₀).1) ((hHm t).sub (hHm t₀))
  have hGm := tendsto_hsNormSq_of_frac (m := m) (r := (m : ℝ) + 1 / 2) (by linarith) hGmeas hB' hG3
  intro t₀ ht₀
  refine tendsto_zero_of_le_two (hheat m h0 t₀ ht₀) (hGm t₀ ht₀) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have e : F t - F t₀ = (heatPart a (F a) t - heatPart a (F a) t₀) + (G t - G t₀) := by
    simp only [hGdef]
    abel
  rw [e]
  exact hsNormSq_add_le_two m ((hHm t).sub (hHm t₀)) ((hGmeas t ht).sub (hGmeas t₀ ht₀))

end Breakdown.SmoothFlow

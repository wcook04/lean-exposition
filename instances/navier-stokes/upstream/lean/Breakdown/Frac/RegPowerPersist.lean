import Breakdown.Frac.StSpaceReg
import Breakdown.Uniqueness.RegPersistAux

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

namespace PowerInternal

private theorem persistHs_add_le (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f + g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  rw [← fracNormSq_natCast, ← fracNormSq_natCast, ← fracNormSq_natCast]
  exact fracNormSq_add_le _ hf hg

private theorem persistHs_sub_le (m : ℕ) {f g : Space → CSpace}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume) :
    hsNormSq m (f - g) ≤ 2 * hsNormSq m f + 2 * hsNormSq m g := by
  rw [← fracNormSq_natCast, ← fracNormSq_natCast, ← fracNormSq_natCast]
  exact fracNormSq_sub_le _ hf hg

private theorem persistTendsto_of_le {l : Filter ℝ} {u v w : ℝ → ℝ≥0∞}
    (hu : Tendsto u l (𝓝 0)) (hv : Tendsto v l (𝓝 0)) (h : ∀ᶠ t in l, w t ≤ 2 * u t + 2 * v t) :
    Tendsto w l (𝓝 0) := by
  have h2 : Tendsto (fun t => 2 * u t + 2 * v t) l (𝓝 0) := by
    have := (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hu (Or.inr (by norm_num))).add
      (ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hv (Or.inr (by norm_num)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h2
    (Eventually.of_forall fun _ => zero_le) h

private theorem persistHalfStep_bound {α : ℝ} (h1 : PowerMildGainStatement α)
    (h2 : PowerHeatPartStatement α) {m : ℕ} (hm : 3 ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (hd : IsPowerMildSymbol α F a b)
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
    obtain ⟨B', hB'⟩ := h1 F a b h3 hd hs (3 + (n : ℝ) / 2) (by positivity) B hB
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
    have hsplit : F t = powerHeatPart α a (F a) t + (F t - powerHeatPart α a (F a) t) :=
      (add_sub_cancel _ _).symm
    calc fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F t)
        = fracNormSq (3 + (n : ℝ) / 2 + 1 / 2)
            (powerHeatPart α a (F a) t + (F t - powerHeatPart α a (F a) t)) := by
          rw [← hsplit]
      _ ≤ 2 * fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (powerHeatPart α a (F a) t) +
          2 * fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F t - powerHeatPart α a (F a) t) :=
            fracNormSq_add_le _ (h2.1 _ hFa _ _) ((h3.1 t ht).1.sub (h2.1 _ hFa _ _))
      _ ≤ 2 * hsNormSq m (F a) + 2 * ENNReal.ofReal B' := by
          gcongr
          · calc fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (powerHeatPart α a (F a) t)
                ≤ fracNormSq (3 + (n : ℝ) / 2 + 1 / 2) (F a) := h2.2.1 _ _ _ ht.1 _
              _ ≤ fracNormSq (m : ℝ) (F a) := fracNormSq_mono hle _
              _ = hsNormSq m (F a) := fracNormSq_natCast m _
          · exact hB' t ht

private theorem persistCurve {α : ℝ} (h1 : PowerMildGainStatement α)
    (h2 : PowerHeatPartStatement α) {m : ℕ} (hm : 3 ≤ m) {F : ℝ → Space → CSpace} {a b : ℝ}
    (h3 : IsHsCurve 3 F a b) (hd : IsPowerMildSymbol α F a b)
    (hs : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) (h0 : hsNormSq m (F a) < ⊤) :
    IsHsCurve m F a b := by
  rcases lt_or_ge b a with hba | hab
  · refine ⟨fun t ht => absurd (ht.1.trans ht.2) (not_le.mpr hba), fun t ht => ?_⟩
    exact absurd (ht.1.trans ht.2) (not_le.mpr hba)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  obtain ⟨Bm, hBm⟩ := persistHalfStep_bound h1 h2 hm h3 hd hs h0 (2 * (m - 3)) le_rfl
  have hlev : (3 + ((2 * (m - 3) : ℕ) : ℝ) / 2) = (m : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_sub hm]
    push_cast
    ring
  rw [hlev] at hBm
  have hBHs : ∀ t ∈ Icc a b, hsNormSq m (F t) ≤ ENNReal.ofReal Bm := fun t ht => by
    rw [← fracNormSq_natCast]
    exact hBm t ht
  refine ⟨fun t ht => ⟨(h3.1 t ht).1, (hBHs t ht).trans_lt ENNReal.ofReal_lt_top⟩, ?_⟩
  obtain ⟨B', hB'⟩ := h1 F a b h3 hd hs (m : ℝ) (by positivity) Bm hBm
  set G : ℝ → Space → CSpace := fun t => F t - powerHeatPart α a (F a) t with hGdef
  have hheat : ∀ k : ℕ, hsNormSq k (F a) < ⊤ → ∀ t₀ ∈ Icc a b,
      Tendsto (fun t => hsNormSq k (powerHeatPart α a (F a) t - powerHeatPart α a (F a) t₀))
        (𝓝[Icc a b] t₀) (𝓝 0) :=
    fun k hk t₀ ht₀ => h2.2.2 k (F a) (h3.1 a ha).1 hk a b t₀ ht₀
  have hHm : ∀ t, AEStronglyMeasurable (powerHeatPart α a (F a) t) volume :=
    fun t => h2.1 _ (h3.1 a ha).1 a t
  have hGmeas : ∀ t ∈ Icc a b, AEStronglyMeasurable (G t) volume :=
    fun t ht => (h3.1 t ht).1.sub (hHm t)
  have hG3 : ∀ t₀ ∈ Icc a b, Tendsto (fun t => hsNormSq 3 (G t - G t₀)) (𝓝[Icc a b] t₀) (𝓝 0) := by
    intro t₀ ht₀
    refine persistTendsto_of_le (h3.2 t₀ ht₀) (hheat 3 (h3.1 a ha).2 t₀ ht₀) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have e : G t - G t₀ = (F t - F t₀) -
        (powerHeatPart α a (F a) t - powerHeatPart α a (F a) t₀) := by
      simp only [hGdef]
      exact sub_sub_sub_comm _ _ _ _
    rw [e]
    exact persistHs_sub_le 3 ((h3.1 t ht).1.sub (h3.1 t₀ ht₀).1) ((hHm t).sub (hHm t₀))
  have hGm := tendsto_hsNormSq_of_frac (m := m) (r := (m : ℝ) + 1 / 2) (by linarith) hGmeas hB' hG3
  intro t₀ ht₀
  refine persistTendsto_of_le (hheat m h0 t₀ ht₀) (hGm t₀ ht₀) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have e : F t - F t₀ = (powerHeatPart α a (F a) t - powerHeatPart α a (F a) t₀) + (G t - G t₀) := by
    simp only [hGdef]
    abel
  rw [e]
  exact persistHs_add_le m ((hHm t).sub (hHm t₀)) ((hGmeas t ht).sub (hGmeas t₀ ht₀))

end PowerInternal

theorem powerPersist_of (α : ℝ) (_hα : 1 < α) (h1 : PowerMildGainStatement α)
    (h2 : PowerHeatPartStatement α) : PowerPersistStatement α :=
  fun _ hm _ _ _ h3 hd hs h0 => PowerInternal.persistCurve h1 h2 hm h3 hd hs h0

end Breakdown.SmoothFlow

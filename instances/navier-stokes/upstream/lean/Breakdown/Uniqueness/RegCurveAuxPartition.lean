import Breakdown.FreqTr.Basic

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

private lemma mem_segment_partition_point (t s : ℝ) (N k : ℕ) (hk : k ≤ N + 1) :
    t + ((k : ℝ) / (N + 1)) * (s - t) ∈ segment ℝ t s := by
  have hN : (0 : ℝ) < N + 1 := by positivity
  have h0 : (0 : ℝ) ≤ (k : ℝ) / (N + 1) := by positivity
  have h1 : (k : ℝ) / (N + 1) ≤ 1 := by
    rw [div_le_one hN]; exact_mod_cast hk
  refine ⟨1 - (k : ℝ) / (N + 1), (k : ℝ) / (N + 1), by linarith, h0, by ring, ?_⟩
  simp only [smul_eq_mul]; ring

private lemma partition_sum_tendsto_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : ℝ → E} {t s : ℝ}
    (hder : ∀ σ ∈ segment ℝ t s, HasDerivWithinAt f (g σ) (segment ℝ t s) σ)
    (hg : ContinuousOn g (segment ℝ t s)) :
    Tendsto (fun N : ℕ => ∑ k ∈ Finset.range (N + 1),
      (f (t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t)) - f (t + ((k : ℝ) / (N + 1)) * (s - t))
        - ((s - t) / (N + 1)) • g (t + ((k : ℝ) / (N + 1)) * (s - t)))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  set η : ℝ := ε / (2 * (|s - t| + 1)) with hη
  have hηpos : 0 < η := by positivity
  have huc := (show IsCompact (segment ℝ t s) by rw [segment_eq_uIcc]; exact isCompact_uIcc).uniformContinuousOn_of_continuous hg
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ, hδ, hδc⟩ := huc η hηpos
  obtain ⟨N0, hN0⟩ := exists_nat_gt (|s - t| / δ)
  refine ⟨N0, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N + 1 := by positivity
  have hstep : |s - t| / (N + 1) < δ := by
    rw [div_lt_iff₀ hNpos]
    have : |s - t| / δ < N + 1 := by
      have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hterm : ∀ k ∈ Finset.range (N + 1),
      ‖f (t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t)) - f (t + ((k : ℝ) / (N + 1)) * (s - t))
        - ((s - t) / (N + 1)) • g (t + ((k : ℝ) / (N + 1)) * (s - t))‖ ≤ η * (|s - t| / (N + 1)) := by
    intro k hk
    have hk' : k + 1 ≤ N + 1 := Finset.mem_range.1 hk
    set a := t + ((k : ℝ) / (N + 1)) * (s - t) with ha
    set b := t + (((k + 1 : ℕ) : ℝ) / (N + 1)) * (s - t) with hb
    have haI : a ∈ segment ℝ t s := mem_segment_partition_point t s N k (by omega)
    have hbI : b ∈ segment ℝ t s := mem_segment_partition_point t s N (k + 1) hk'
    have hJ : segment ℝ a b ⊆ segment ℝ t s := (convex_segment t s).segment_subset haI hbI
    have hba : b - a = (s - t) / (N + 1) := by
      rw [ha, hb]; push_cast; field_simp; ring
    have hφ : ∀ τ ∈ segment ℝ a b, HasDerivWithinAt (fun τ => f τ - τ • g a) (g τ - g a)
        (segment ℝ a b) τ := by
      intro τ hτ
      have h1 := (hder τ (hJ hτ)).mono hJ
      have h2 : HasDerivWithinAt (fun τ : ℝ => τ • g a) ((1 : ℝ) • g a) (segment ℝ a b) τ :=
        (hasDerivWithinAt_id τ _).smul_const (g a)
      rw [one_smul] at h2
      exact h1.sub h2
    have hbound : ∀ τ ∈ segment ℝ a b, ‖g τ - g a‖ ≤ η := by
      intro τ hτ
      have hdist : dist τ a < δ := by
        rw [Real.dist_eq]
        rw [segment_eq_uIcc] at hτ
        calc |τ - a| ≤ |b - a| := abs_sub_left_of_mem_uIcc hτ
          _ = |s - t| / (N + 1) := by rw [hba, abs_div, abs_of_pos hNpos]
          _ < δ := hstep
      have := hδc τ (hJ hτ) a haI hdist
      rw [dist_eq_norm] at this
      exact this.le
    have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hφ hbound (convex_segment a b)
      (left_mem_segment ℝ a b) (right_mem_segment ℝ a b)
    have heq : (f b - b • g a) - (f a - a • g a) = f b - f a - ((s - t) / (N + 1)) • g a := by
      rw [← hba, sub_smul]; abel
    rw [heq, hba, Real.norm_eq_abs, abs_div, abs_of_pos hNpos] at hmv
    exact hmv
  rw [dist_zero_right]
  calc _ ≤ ∑ k ∈ Finset.range (N + 1), η * (|s - t| / (N + 1)) := by
        refine (norm_sum_le _ _).trans ?_
        exact Finset.sum_le_sum hterm
    _ = η * |s - t| := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast; field_simp
    _ < ε := by
        rw [hη]
        have h3 : 0 < |s - t| + 1 := by positivity
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg (s - t)]

private lemma lintegral_enorm_increment_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : ℝ → α → E} {t s : ℝ} {C : ℝ≥0∞}
    (hder : ∀ x, ∀ σ ∈ segment ℝ t s, HasDerivWithinAt (fun τ => u τ x) (v σ x)
      (segment ℝ t s) σ)
    (hvc : ∀ x, ContinuousOn (fun σ => v σ x) (segment ℝ t s))
    (hmeas : ∀ σ ∈ segment ℝ t s, AEStronglyMeasurable (v σ) μ)
    (hbd : ∀ σ ∈ segment ℝ t s, ∫⁻ x, ‖v σ x - v t x‖ₑ ∂μ ≤ C) :
    ∫⁻ x, ‖u s x - u t x - (s - t) • v t x‖ₑ ∂μ ≤ ENNReal.ofReal |s - t| * C := by
  set p : ℕ → ℕ → ℝ := fun N k => t + ((k : ℝ) / (N + 1)) * (s - t) with hp
  set B : ℕ → α → E := fun N x => ∑ k ∈ Finset.range (N + 1),
    ((s - t) / (N + 1)) • (v (p N k) x - v t x) with hB
  have hsplit : ∀ N x, B N x = (u s x - u t x - (s - t) • v t x) -
      ∑ k ∈ Finset.range (N + 1), (u (p N (k + 1)) x - u (p N k) x
        - ((s - t) / (N + 1)) • v (p N k) x) := by
    intro N x
    have hNpos : (N : ℝ) + 1 ≠ 0 := by positivity
    have htel : ∑ k ∈ Finset.range (N + 1), (u (p N (k + 1)) x - u (p N k) x) = u s x - u t x := by
      rw [Finset.sum_range_sub (fun k => u (p N k) x)]
      simp only [hp]
      congr 2
      · push_cast; field_simp; ring
      · simp
    have hmul : ((N + 1 : ℕ) : ℝ) * ((s - t) / (N + 1)) = s - t := by push_cast; field_simp
    have hc : (s - t) • v t x = ∑ k ∈ Finset.range (N + 1), ((s - t) / (N + 1)) • v t x := by
      rw [Finset.sum_const, Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, hmul]
    simp only [hB]
    rw [← htel, hc]
    simp only [smul_sub, Finset.sum_sub_distrib]
    abel
  have hlim : ∀ x, Tendsto (fun N => B N x) atTop (𝓝 (u s x - u t x - (s - t) • v t x)) := by
    intro x
    have h0 := partition_sum_tendsto_zero (f := fun τ => u τ x) (g := fun σ => v σ x)
      (hder x) (hvc x)
    have := (tendsto_const_nhds (x := u s x - u t x - (s - t) • v t x)).sub h0
    rw [sub_zero] at this
    refine this.congr ?_
    intro N
    rw [hsplit N x]
  have hptw : ∀ x, ‖u s x - u t x - (s - t) • v t x‖ₑ = liminf (fun N => ‖B N x‖ₑ) atTop :=
    fun x => (((continuous_enorm).tendsto _).comp (hlim x)).liminf_eq.symm
  have hpI : ∀ N k, k ∈ Finset.range (N + 1) → p N k ∈ segment ℝ t s := fun N k hk =>
    mem_segment_partition_point t s N k (by have := Finset.mem_range.1 hk; omega)
  have htI : t ∈ segment ℝ t s := left_mem_segment ℝ t s
  have hBmeas : ∀ N, AEMeasurable (fun x => ‖B N x‖ₑ) μ := by
    intro N
    have : AEStronglyMeasurable (B N) μ := by
      simp only [hB]
      exact Finset.aestronglyMeasurable_fun_sum _ fun k hk =>
        ((hmeas _ (hpI N k hk)).sub (hmeas t htI)).const_smul _
    exact this.enorm
  have hBbd : ∀ N, ∫⁻ x, ‖B N x‖ₑ ∂μ ≤ ENNReal.ofReal |s - t| * C := by
    intro N
    have hNpos : (0 : ℝ) < N + 1 := by positivity
    calc ∫⁻ x, ‖B N x‖ₑ ∂μ
        ≤ ∫⁻ x, ∑ k ∈ Finset.range (N + 1),
            ‖((s - t) / (N + 1)) • (v (p N k) x - v t x)‖ₑ ∂μ :=
          lintegral_mono fun x => enorm_sum_le _ _
      _ = ∑ k ∈ Finset.range (N + 1),
            ∫⁻ x, ‖((s - t) / (N + 1)) • (v (p N k) x - v t x)‖ₑ ∂μ :=
          lintegral_finsetSum' _ fun k hk =>
            (((hmeas _ (hpI N k hk)).sub (hmeas t htI)).const_smul _).enorm
      _ = ∑ k ∈ Finset.range (N + 1),
            ‖(s - t) / (N + 1)‖ₑ * ∫⁻ x, ‖v (p N k) x - v t x‖ₑ ∂μ := by
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [enorm_smul]
          exact lintegral_const_mul' _ _ enorm_ne_top
      _ ≤ ∑ k ∈ Finset.range (N + 1), ‖(s - t) / (N + 1)‖ₑ * C :=
          Finset.sum_le_sum fun k hk => by gcongr; exact hbd _ (hpI N k hk)
      _ = ENNReal.ofReal |s - t| * C := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc]
          congr 1
          rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity), abs_div, abs_of_pos hNpos]
          congr 1
          push_cast; field_simp
  calc ∫⁻ x, ‖u s x - u t x - (s - t) • v t x‖ₑ ∂μ
      = ∫⁻ x, liminf (fun N => ‖B N x‖ₑ) atTop ∂μ := lintegral_congr fun x => hptw x
    _ ≤ liminf (fun N => ∫⁻ x, ‖B N x‖ₑ ∂μ) atTop := lintegral_liminf_le' hBmeas
    _ ≤ ENNReal.ofReal |s - t| * C :=
        liminf_le_of_frequently_le' (Frequently.of_forall hBbd)

theorem hasDerivWithinAt_toLp_of_pointwise {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S : Set ℝ} (hS : Convex ℝ S) {u v : ℝ → α → CSpace} {t : ℝ} (ht : t ∈ S)
    (hu : ∀ s ∈ S, MemLp (u s) 1 μ) (hv : ∀ s ∈ S, MemLp (v s) 1 μ)
    (hder : ∀ x, ∀ s ∈ S, HasDerivWithinAt (fun τ => u τ x) (v s x) S s)
    (hvc : ∀ x, ContinuousOn (fun s => v s x) S)
    (hlim : Tendsto (fun s => ∫⁻ x, ‖v s x - v t x‖ₑ ∂μ) (𝓝[S] t) (𝓝 0))
    {H : ℝ → Lp CSpace 1 μ} (hH : ∀ s (hs : s ∈ S), H s = (hu s hs).toLp (u s)) :
    HasDerivWithinAt H ((hv t ht).toLp (v t)) S t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  have h1 := (ENNReal.tendsto_nhds_zero.1 hlim) _ (ENNReal.ofReal_pos.2 hc)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
  obtain ⟨δ, hδ, h1⟩ := h1
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)]
    with s hs hsb
  have hseg : segment ℝ t s ⊆ S := hS.segment_subset ht hs
  have hball : segment ℝ t s ⊆ Metric.ball t δ :=
    (convex_ball t δ).segment_subset (Metric.mem_ball_self hδ) hsb
  have key := lintegral_enorm_increment_le (μ := μ) (u := u) (v := v) (t := t) (s := s)
    (C := ENNReal.ofReal c)
    (fun x σ hσ => (hder x σ (hseg hσ)).mono hseg) (fun x => (hvc x).mono hseg)
    (fun σ hσ => (hv σ (hseg hσ)).1) (fun σ hσ => h1 (hball hσ) (hseg hσ))
  rw [hH s hs, hH t ht, ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub,
    Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm]
  simp only [Pi.sub_apply, Pi.smul_apply]
  rw [← ENNReal.ofReal_mul (abs_nonneg _), mul_comm] at key
  rw [Real.norm_eq_abs]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) key

end Breakdown.SmoothFlow

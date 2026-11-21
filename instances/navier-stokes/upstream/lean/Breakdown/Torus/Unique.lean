import Breakdown.Torus.Basic
import Breakdown.Torus.StatementsAnalysis

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace Unique.Internal

theorem kernel_sq_sub_sq (τ : ℝ) (x y : V) :
    kernel τ x x - kernel τ y y = kernel τ (x - y) (x + y) := by
  simp only [map_sub, map_add, sub_apply]
  rw [kernel_symm τ x y]
  abel

theorem integral_sub_rpow (t₀ t : ℝ) :
    ∫ s in t₀..t, (t - s) ^ (-(3 / 4 : ℝ)) = 4 * (t - t₀) ^ (1 / 4 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_left (fun x : ℝ => x ^ (-(3 / 4 : ℝ))), sub_self,
    integral_rpow (Or.inl (by norm_num))]
  have e : -(3 / 4 : ℝ) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

theorem intervalIntegrable_sub_rpow (t₀ t : ℝ) :
    IntervalIntegrable (fun s : ℝ => (t - s) ^ (-(3 / 4 : ℝ))) volume t₀ t := by
  have h := (intervalIntegral.intervalIntegrable_rpow' (a := t - t₀) (b := t - t)
    (r := -(3 / 4 : ℝ)) (by norm_num)).comp_sub_left t
  simpa only [sub_sub_cancel] using h

theorem norm_integral_kernel_le {C M S t₀ t : ℝ}
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖kernel τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hC : 0 < C) (hS : 0 ≤ S) (w z : ℝ → V) (ht : t₀ ≤ t) (ht1 : t - t₀ ≤ 1)
    (hw : ∀ s ∈ Icc t₀ t, ‖w s‖ ≤ S) (hz : ∀ s ∈ Icc t₀ t, ‖z s‖ ≤ M) :
    ‖∫ s in t₀..t, kernel (t - s) (w s) (z s)‖ ≤ C * M * S * (4 * (t - t₀) ^ (1 / 4 : ℝ)) := by
  calc ‖∫ s in t₀..t, kernel (t - s) (w s) (z s)‖
      ≤ ∫ s in t₀..t, C * M * S * (t - s) ^ (-(3 / 4 : ℝ)) := by
        refine intervalIntegral.norm_integral_le_of_norm_le ht ?_
          ((intervalIntegrable_sub_rpow t₀ t).const_mul (C * M * S))
        filter_upwards [volume.ae_ne t] with s hst hs
        have hs' : s ∈ Icc t₀ t := Ioc_subset_Icc_self hs
        have hτ : 0 < t - s := sub_pos.2 (lt_of_le_of_ne hs.2 hst)
        have hτ1 : t - s ≤ 1 := by linarith [hs.1]
        have hk := hK (t - s) hτ hτ1
        have hp : 0 ≤ (t - s) ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hτ.le _
        calc ‖kernel (t - s) (w s) (z s)‖ ≤ ‖kernel (t - s)‖ * ‖w s‖ * ‖z s‖ :=
              ContinuousLinearMap.le_opNorm₂ _ _ _
          _ ≤ (C * (t - s) ^ (-(3 / 4 : ℝ))) * S * M := by
              gcongr
              · exact hw s hs'
              · exact hz s hs'
          _ = C * M * S * (t - s) ^ (-(3 / 4 : ℝ)) := by ring
    _ = C * M * S * (4 * (t - t₀) ^ (1 / 4 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul, integral_sub_rpow t₀ t]

theorem rpow_quarter_le {ε x : ℝ} (hε : 0 ≤ ε) (hx : 0 ≤ x) (h : x ≤ ε ^ 4) :
    x ^ (1 / 4 : ℝ) ≤ ε := by
  have e : (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ := by norm_num
  calc x ^ (1 / 4 : ℝ) ≤ (ε ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hx h (by norm_num)
    _ = ε := by rw [e]; exact Real.pow_rpow_inv_natCast hε (by norm_num)

theorem local_contraction {C M S ε a t₀ r : ℝ}
    (hK : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ‖kernel τ‖ ≤ C * τ ^ (-(3 / 4 : ℝ)))
    (hC : 0 < C) (hM : 0 ≤ M) (hS : 0 ≤ S) (hε0 : 0 ≤ ε) (hε : 4 * C * M * ε ≤ 1 / 2)
    (w z : ℝ → V) (hat₀ : a ≤ t₀) (hr : t₀ ≤ r) (hr1 : r - t₀ ≤ 1) (hrε : r - t₀ ≤ ε ^ 4)
    (hint : IntervalIntegrable (fun s => kernel (r - s) (w s) (z s)) volume a r)
    (heq : w r = ∫ s in a..r, kernel (r - s) (w s) (z s))
    (hw0 : ∀ s ∈ Icc a t₀, w s = 0)
    (hw : ∀ s ∈ Icc t₀ r, ‖w s‖ ≤ S) (hz : ∀ s ∈ Icc t₀ r, ‖z s‖ ≤ M) :
    ‖w r‖ ≤ S / 2 := by
  have h1 : IntervalIntegrable (fun s => kernel (r - s) (w s) (z s)) volume a t₀ :=
    hint.mono_set (by
      rw [uIcc_of_le hat₀, uIcc_of_le (hat₀.trans hr)]
      exact Icc_subset_Icc le_rfl hr)
  have h2 : IntervalIntegrable (fun s => kernel (r - s) (w s) (z s)) volume t₀ r :=
    hint.mono_set (by
      rw [uIcc_of_le hr, uIcc_of_le (hat₀.trans hr)]
      exact Icc_subset_Icc hat₀ le_rfl)
  have hzero : ∫ s in a..t₀, kernel (r - s) (w s) (z s) = 0 := by
    have hc : EqOn (fun s => kernel (r - s) (w s) (z s)) (fun _ => (0 : V)) (uIcc a t₀) := by
      intro s hs
      rw [uIcc_of_le hat₀] at hs
      simp only [hw0 s hs, map_zero, zero_apply]
    rw [intervalIntegral.integral_congr hc, intervalIntegral.integral_zero]
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, hzero, zero_add]
  have hb := norm_integral_kernel_le hK hC hS w z hr hr1 hw hz
  have hq : (r - t₀) ^ (1 / 4 : ℝ) ≤ ε := rpow_quarter_le hε0 (sub_nonneg.2 hr) hrε
  refine hb.trans ?_
  have hCMS : 0 ≤ C * M * S := by positivity
  calc C * M * S * (4 * (r - t₀) ^ (1 / 4 : ℝ)) ≤ C * M * S * (4 * ε) := by gcongr
    _ = S * (4 * C * M * ε) := by ring
    _ ≤ S * (1 / 2) := by gcongr
    _ = S / 2 := by ring

theorem zero_on_block {t₀ t₂ : ℝ} (w : ℝ → V) (hcont : ContinuousOn w (Icc t₀ t₂)) (ht : t₀ ≤ t₂)
    (hhalf : ∀ S : ℝ, 0 ≤ S → (∀ s ∈ Icc t₀ t₂, ‖w s‖ ≤ S) → ∀ r ∈ Icc t₀ t₂, ‖w r‖ ≤ S / 2) :
    ∀ r ∈ Icc t₀ t₂, w r = 0 := by
  obtain ⟨m, hm, hmax⟩ := isCompact_Icc.exists_isMaxOn (f := fun s => ‖w s‖)
    (nonempty_Icc.2 ht) hcont.norm
  have hb : ∀ s ∈ Icc t₀ t₂, ‖w s‖ ≤ ‖w m‖ := fun s hs => hmax hs
  have hh := hhalf ‖w m‖ (norm_nonneg _) hb m hm
  have h0 : ‖w m‖ ≤ 0 := by linarith
  intro r hr
  exact norm_le_zero_iff.1 ((hb r hr).trans h0)

theorem zero_of_blocks {a c δ : ℝ} (hδ : 0 < δ) (w : ℝ → V) (h0 : w a = 0)
    (hstep : ∀ t₀ t : ℝ, a ≤ t₀ → t₀ < t → t ≤ c → t ≤ t₀ + δ →
      (∀ s ∈ Icc a t₀, w s = 0) → w t = 0) :
    ∀ t ∈ Icc a c, w t = 0 := by
  have key : ∀ n : ℕ, ∀ t ∈ Icc a c, t ≤ a + n * δ → w t = 0 := by
    intro n
    induction n with
    | zero =>
      intro t ht htn
      simp only [Nat.cast_zero, zero_mul, add_zero] at htn
      rw [le_antisymm htn ht.1, h0]
    | succ n ih =>
      intro t ht htn
      by_cases hle : t ≤ a + n * δ
      · exact ih t ht hle
      rw [not_le] at hle
      have hn : (0 : ℝ) ≤ n * δ := mul_nonneg (Nat.cast_nonneg n) hδ.le
      refine hstep (a + n * δ) t (by linarith) hle ht.2 (by rw [Nat.cast_succ] at htn; linarith) ?_
      intro s hs
      exact ih s ⟨hs.1, hs.2.trans (hle.le.trans ht.2)⟩ hs.2
  intro t ht
  obtain ⟨n, hn⟩ := exists_nat_ge ((t - a) / δ)
  rw [div_le_iff₀ hδ] at hn
  exact key n t ht (by linarith)

theorem mild_difference_eq {u v : ℝ → V} {a b : ℝ} (hu : IsMildOn u a b) (hv : IsMildOnIcc v a b)
    (hav : u a = v a) (t : ℝ) (ht : t ∈ Ico a b) :
    IntervalIntegrable (fun s => kernel (t - s) (u s - v s) (u s + v s)) volume a t ∧
      u t - v t = ∫ s in a..t, kernel (t - s) (u s - v s) (u s + v s) := by
  obtain ⟨hiu, hequ⟩ := hu.2 t ht
  obtain ⟨hiv, heqv⟩ := hv.2 t (Ico_subset_Icc_self ht)
  have hf : (fun s => kernel (t - s) (u s - v s) (u s + v s)) =
      fun s => kernel (t - s) (u s) (u s) - kernel (t - s) (v s) (v s) := by
    funext s
    rw [kernel_sq_sub_sq]
  rw [hf]
  refine ⟨hiu.sub hiv, ?_⟩
  rw [intervalIntegral.integral_sub hiu hiv, hequ, heqv, hav]
  abel

end Unique.Internal

open Unique.Internal in
theorem mildUniqueness (hK : KernelSharpBound) : MildUniqueness := by
  obtain ⟨C, hC, hKC⟩ := hK
  intro u v a b hu hv hav c hc
  have hcb : Icc a c ⊆ Ico a b := Icc_subset_Ico_right hc.2
  have hcont : ContinuousOn (fun s => u s + v s) (Icc a c) :=
    (hu.1.mono hcb).add (hv.1.mono (hcb.trans Ico_subset_Icc_self))
  have hwcont : ContinuousOn (fun s => u s - v s) (Icc a c) :=
    (hu.1.mono hcb).sub (hv.1.mono (hcb.trans Ico_subset_Icc_self))
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = max M₀ 0 := ⟨_, rfl⟩
  have hM : 0 ≤ M := hMdef ▸ le_max_right _ _
  have hMb : ∀ s ∈ Icc a c, ‖u s + v s‖ ≤ M :=
    fun s hs => (hM₀ s hs).trans (hMdef ▸ le_max_left _ _)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = 1 / (8 * C * M + 8) := ⟨_, rfl⟩
  have hCM : 0 ≤ C * M := mul_nonneg hC.le hM
  have hεpos : 0 < ε := by rw [hεdef]; positivity
  have hε : 4 * C * M * ε ≤ 1 / 2 := by
    rw [hεdef, show 4 * C * M * (1 / (8 * C * M + 8)) = 4 * C * M / (8 * C * M + 8) by ring,
      div_le_iff₀ (by positivity)]
    nlinarith
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min 1 (ε ^ 4) := ⟨_, rfl⟩
  have hδpos : 0 < δ := hδdef ▸ lt_min one_pos (pow_pos hεpos 4)
  have hδ1 : δ ≤ 1 := hδdef ▸ min_le_left _ _
  have hδε : δ ≤ ε ^ 4 := hδdef ▸ min_le_right _ _
  have hall : ∀ t ∈ Icc a c, (fun s => u s - v s) t = 0 := by
    refine zero_of_blocks hδpos (fun s => u s - v s) (by simp [hav]) ?_
    intro t₀ t hat₀ ht₀t htc htδ hw0
    have ht₂ : t₀ ≤ min (t₀ + δ) c := le_min (by linarith) (by linarith)
    have hsub : Icc t₀ (min (t₀ + δ) c) ⊆ Icc a c := Icc_subset_Icc hat₀ (min_le_right _ _)
    refine zero_on_block (fun s => u s - v s) (hwcont.mono hsub) ht₂ ?_ t
      ⟨ht₀t.le, le_min htδ htc⟩
    intro S hS hSb r hr
    have hrδ : r - t₀ ≤ δ := by linarith [hr.2.trans (min_le_left _ _)]
    obtain ⟨hint, heq⟩ := mild_difference_eq hu hv hav r (hcb (hsub hr))
    exact local_contraction hKC hC hM hS hεpos.le hε (fun s => u s - v s) (fun s => u s + v s)
      hat₀ hr.1 (hrδ.trans hδ1) (hrδ.trans hδε) hint heq hw0
      (fun s hs => hSb s ⟨hs.1, hs.2.trans hr.2⟩)
      (fun s hs => hMb s (hsub ⟨hs.1, hs.2.trans hr.2⟩))
  exact sub_eq_zero.1 (hall c ⟨hc.1, le_rfl⟩)

end Breakdown.Periodic

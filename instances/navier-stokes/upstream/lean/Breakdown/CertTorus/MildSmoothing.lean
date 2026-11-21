import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace MildSmoothing.Internal

theorem isDerivX_fin_zero (α : Fin 0 → Fin 3) (x : X) : IsDerivX α x x :=
  Filter.Eventually.of_forall fun ξ => by simp [monoSymbol]

theorem symX_sub (x y : X) : symX (x - y) =ᵐ[volume] symX x - symX y := by
  unfold symX
  rw [Submodule.coe_sub]
  exact Lp.coeFn_sub _ _

theorem isDerivX_sub {n : ℕ} {α : Fin n → Fin 3} {x y x' y' : X} (h : IsDerivX α x y)
    (h' : IsDerivX α x' y') : IsDerivX α (x - x') (y - y') := by
  filter_upwards [h, h', symX_sub x x', symX_sub y y'] with ξ h1 h2 h3 h4
  rw [h4, h3, Pi.sub_apply, Pi.sub_apply, h1, h2, smul_sub]

theorem aemeasurable_enorm_symX (x : X) : AEMeasurable (fun ξ => ‖symX x ξ‖ₑ) volume :=
  (Lp.aestronglyMeasurable (x : L2C)).enorm

theorem homSob_zero_eq (v : X) : homSob 0 v = ENNReal.ofReal ‖v‖ ^ (2 : ℝ) := by
  have h1 : ENNReal.ofReal ‖v‖ = eLpNorm (symX v) 2 volume := by
    rw [Submodule.coe_norm, Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)]
    rfl
  rw [h1, eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top,
    ← ENNReal.rpow_mul]
  simp only [ENNReal.toReal_ofNat]
  norm_num
  unfold homSob homNormSq
  refine lintegral_congr fun ξ => ?_
  simp

theorem homSob_le_interp (k : ℕ) (v : X) :
    homSob k v ≤ homSob 0 v ^ (1 / 2 : ℝ) * homSob (2 * k) v ^ (1 / 2 : ℝ) := by
  have hf := aemeasurable_enorm_symX v
  have hw : AEMeasurable (fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * k))) volume :=
    (by fun_prop : Measurable fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ (2 * k))).aemeasurable
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two hf (hw.mul hf)
  have hA : ∫⁻ ξ, ‖symX v ξ‖ₑ ^ (2 : ℝ) = homSob 0 v := by
    unfold homSob homNormSq
    refine lintegral_congr fun ξ => ?_
    simp
  simp only [Pi.mul_apply] at h
  have hB : ∫⁻ ξ, (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX v ξ‖ₑ) ^ (2 : ℝ) = homSob (2 * k) v := by
    unfold homSob homNormSq
    refine lintegral_congr fun ξ => ?_
    rw [ENNReal.rpow_two, mul_pow, ← ENNReal.ofReal_pow (by positivity), ← pow_mul]
    ring_nf
  have hC : ∫⁻ ξ, ‖symX v ξ‖ₑ * (ENNReal.ofReal (‖ξ‖ ^ (2 * k)) * ‖symX v ξ‖ₑ) = homSob k v := by
    unfold homSob homNormSq
    refine lintegral_congr fun ξ => ?_
    ring
  rw [hA, hB, hC] at h
  exact h

theorem deriv_bounds (hLG : LocalGain) (hMR : MildRestrict) (u : ℝ → X) (a b : ℝ)
    (hu : IsMildX u a b) (M : ℝ) (hM : ∀ t ∈ Icc a b, ‖u t‖ ≤ M) :
    ∀ n : ℕ, ∀ c ∈ Ioo a b, ∃ B : ℝ, ∀ t ∈ Icc c b, ∀ m ≤ n, ∀ α : Fin m → Fin 3,
      ∃ y, IsDerivX α (u t) y ∧ ‖y‖ ≤ B := by
  intro n
  induction n with
  | zero =>
    intro c hc
    refine ⟨M, fun t ht m hm α => ?_⟩
    obtain rfl : m = 0 := Nat.le_zero.mp hm
    exact ⟨u t, isDerivX_fin_zero α (u t), hM t ⟨hc.1.le.trans ht.1, ht.2⟩⟩
  | succ n ih =>
    intro c hc
    have hc1 : a < c := hc.1
    obtain ⟨B₀, hB₀⟩ := ih ((a + c) / 2) ⟨by linarith, by linarith [hc.2]⟩
    obtain ⟨δ, B, hδ, -, hG⟩ := hLG n (max M B₀)
    obtain ⟨η, hη0, hηδ, hηc⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ δ / 2 ∧ η ≤ c - (a + c) / 2 :=
      ⟨min (δ / 2) (c - (a + c) / 2), lt_min (by linarith) (by linarith), min_le_left _ _,
        min_le_right _ _⟩
    refine ⟨max B (B * η ^ (-(1 / 2 : ℝ))), fun t ht m hm α => ?_⟩
    have hs1 : (a + c) / 2 ≤ t - η := by linarith [ht.1]
    have has : a ≤ t - η := by linarith
    have hsb : t - η < b := by linarith [ht.2]
    have hmild : IsMildX u (t - η) b := hMR u a (t - η) b hu has hsb.le
    have hbound : ∀ τ ∈ Icc (t - η) b, ‖u τ‖ ≤ max M B₀ :=
      fun τ hτ => (hM τ ⟨has.trans hτ.1, hτ.2⟩).trans (le_max_left _ _)
    have hderiv : ∀ m ≤ n, ∀ α : Fin m → Fin 3,
        ∃ y, IsDerivX α (u (t - η)) y ∧ ‖y‖ ≤ max M B₀ := by
      intro m hm α
      obtain ⟨y, hy, hyB⟩ := hB₀ (t - η) ⟨hs1, hsb.le⟩ m hm α
      exact ⟨y, hy, hyB.trans (le_max_right _ _)⟩
    have ht' : t ∈ Ioc (t - η) (min b (t - η + δ)) :=
      ⟨by linarith, le_min ht.2 (by linarith)⟩
    obtain ⟨hlow, htop⟩ := hG u (t - η) b hsb hmild hbound hderiv t ht'
    rcases Nat.le_succ_iff.mp hm with hm' | rfl
    · obtain ⟨y, hy, hyB⟩ := hlow m hm' α
      exact ⟨y, hy, hyB.trans (le_max_left _ _)⟩
    · obtain ⟨y, hy, hyB⟩ := htop α
      have he : t - (t - η) = η := by ring
      rw [he] at hyB
      exact ⟨y, hy, hyB.trans (le_max_right _ _)⟩

end MildSmoothing.Internal

open MildSmoothing.Internal

theorem mildSmoothingOfLocalGain_holds : MildSmoothingOfLocalGain := by
  intro hLG hMR hDS u a b hab hu a' ha' k
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hu.1
  have hB := deriv_bounds hLG hMR u a b hu M hM
  obtain ⟨Bk, hBk⟩ := hB k a' ha'
  obtain ⟨B2, hB2⟩ := hB (2 * k) a' ha'
  obtain ⟨Ck, hCk⟩ := hDS k
  obtain ⟨C2, hC2⟩ := hDS (2 * k)
  refine ⟨fun t ht => ?_, fun t₀ ht₀ => ?_⟩
  · exact ((hCk (u t)).2 Bk fun α => hBk t ht k le_rfl α).trans_lt ENNReal.ofReal_lt_top
  · have hK : ∀ t ∈ Icc a' b,
        homSob (2 * k) (u t - u t₀) ≤ ENNReal.ofReal (C2 * (2 * B2) ^ 2) := by
      intro t ht
      refine (hC2 (u t - u t₀)).2 (2 * B2) fun α => ?_
      obtain ⟨y, hy, hyB⟩ := hB2 t ht (2 * k) le_rfl α
      obtain ⟨y₀, hy₀, hy₀B⟩ := hB2 t₀ ht₀ (2 * k) le_rfl α
      exact ⟨y - y₀, isDerivX_sub hy hy₀, (norm_sub_le _ _).trans (by linarith)⟩
    have hcont : Tendsto (fun t => ‖u t - u t₀‖) (𝓝[Icc a' b] t₀) (𝓝 0) :=
      tendsto_iff_norm_sub_tendsto_zero.mp
        ((hu.1 t₀ ⟨ha'.1.le.trans ht₀.1, ht₀.2⟩).mono (Icc_subset_Icc_left ha'.1.le))
    have hzero : Tendsto (fun t => homSob 0 (u t - u t₀)) (𝓝[Icc a' b] t₀) (𝓝 0) := by
      simp_rw [homSob_zero_eq]
      have h0 : Tendsto (fun x : ℝ => ENNReal.ofReal x ^ (2 : ℝ)) (𝓝 0)
          (𝓝 (ENNReal.ofReal 0 ^ (2 : ℝ))) :=
        (ENNReal.continuous_rpow_const.comp ENNReal.continuous_ofReal).tendsto 0
      rw [ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos (by norm_num)] at h0
      exact h0.comp hcont
    have hup : Tendsto (fun t => homSob 0 (u t - u t₀) ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (C2 * (2 * B2) ^ 2) ^ (1 / 2 : ℝ)) (𝓝[Icc a' b] t₀) (𝓝 0) := by
      have h1 : Tendsto (fun t => homSob 0 (u t - u t₀) ^ (1 / 2 : ℝ)) (𝓝[Icc a' b] t₀) (𝓝 0) := by
        have h0 := (ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto 0
        rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h0
        exact h0.comp hzero
      simpa using ENNReal.Tendsto.mul_const h1
        (Or.inr (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
      (Eventually.of_forall fun _ => zero_le) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hKt := hK t ht
    refine (homSob_le_interp k _).trans ?_
    gcongr

end Breakdown.FarField

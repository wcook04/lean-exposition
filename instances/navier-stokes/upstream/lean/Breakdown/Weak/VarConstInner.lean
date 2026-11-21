import Breakdown.Weak.StatementsTime
import Breakdown.FreqTr.MildOfWeak

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

namespace Internal.VarConstInner

open Breakdown.Freq.Internal.Phi Breakdown.Freq.Internal.WeakInX Breakdown.Freq.Internal.MildOfWeak

theorem heat_sspHeat {a b : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (ψ : X) :
    heatX a (sspHeatX b ψ) = sspHeatX (a + b) ψ := by
  have h1 := fieldOpRealized_holds
  have h5 := heat_holds
  have hab : 0 < a + b := by linarith
  apply Subtype.ext
  apply Lp.ext
  have e1 : ((heatX a (sspHeatX b ψ) : X) : L2C) =
      fieldOp id (fun ξ => heatFactor a ξ • ContinuousLinearMap.id ℝ CSpace) (sspHeatX b ψ : L2C) :=
    h5.2.2.2.2.2 a _
  have ha' := scalarOp_ae h1 (continuous_heatFactor a) (heatFactor_le a) (sspHeatX b ψ : L2C)
  rw [← e1] at ha'
  have hb' := scalarOp_ae h1 (continuous_sspHeat b) (sspHeat_le hb) (ψ : L2C)
  rw [← sspHeatX_coe h1 hb] at hb'
  have hc' := scalarOp_ae h1 (continuous_sspHeat (a + b)) (sspHeat_le hab) (ψ : L2C)
  rw [← sspHeatX_coe h1 hab] at hc'
  filter_upwards [ha', hb', hc'] with ξ x y z
  rw [x, y, z, smul_smul]
  congr 1
  unfold heatFactor
  rw [max_eq_left ha, max_eq_left hb.le, max_eq_left hab.le,
    show -(4 * π ^ 2 * (a + b) * ‖ξ‖ ^ 2) = -(4 * π ^ 2 * a * ‖ξ‖ ^ 2) + -(4 * π ^ 2 * b * ‖ξ‖ ^ 2) by ring,
    Real.exp_add]
  ring

theorem norm_sspHeatX_le {τ : ℝ} (hτ : 0 < τ) (x : X) : ‖sspHeatX τ x‖ ≤ τ⁻¹ * ‖x‖ := by
  have h := scalarOp_norm_le fieldOpRealized_holds (continuous_sspHeat τ) (sspHeat_le hτ) (x : L2C)
  rw [← sspHeatX_coe fieldOpRealized_holds hτ] at h
  exact h

theorem heat_slope {a : ℝ} (ha : 0 < a) (φ : X) {σ σ' : ℝ} (hσ : a ≤ σ) (hσσ : σ ≤ σ') :
    ‖heatX σ' φ - heatX σ φ‖ ≤ a⁻¹ * ‖φ‖ * (σ' - σ) := by
  refine norm_image_sub_le_of_norm_deriv_le_segment' (f := fun s => heatX s φ)
    (f' := fun s => -(sspHeatX s φ)) (fun s hs => ?_) (fun s hs => ?_) σ' ⟨hσσ, le_rfl⟩
  · exact (heat_hasDerivAt fieldOpRealized_holds heat_holds (by linarith [hs.1]) φ).hasDerivWithinAt
  · have hs0 : 0 < s := by linarith [hs.1]
    rw [norm_neg]
    refine (norm_sspHeatX_le hs0 φ).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact inv_anti₀ ha (hσ.trans hs.1)

theorem chain_const {S : Set ℝ} {a b : ℝ} (hab : a ≤ b) (ha : a ∈ S) (hb : b ∈ S)
    (hS : ∀ u v, a ≤ u → u < v → v ≤ b → ∃ z ∈ S, u < z ∧ z < v) (H : ℝ → ℝ) {C δ : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ)
    (hH : ∀ p ∈ S, ∀ q ∈ S, a ≤ p → p ≤ q → q ≤ b → q - p ≤ δ → |H q - H p| ≤ C * (q - p) ^ 2) :
    H b = H a := by
  rcases hab.eq_or_lt with h | hlt
  · rw [h]
  have key : ∀ N : ℕ, 0 < N → 3 * (b - a) ≤ 2 * δ * N → |H b - H a| ≤ C * (3 / 2 * ((b - a) / N)) * (b - a) := by
    intro N hN hNδ
    have hNr : (0 : ℝ) < N := Nat.cast_pos.2 hN
    set h := (b - a) / N with hh
    have hpos : 0 < h := div_pos (sub_pos.2 hlt) hNr
    have hbN : a + N * h = b := by rw [hh]; field_simp; ring
    have hex : ∀ k : ℕ, ∃ z : ℝ, 1 ≤ k → k ≤ N → z ∈ S ∧ a + k * h - h / 2 < z ∧ z < a + k * h := by
      intro k
      by_cases hk : 1 ≤ k ∧ k ≤ N
      · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1
        have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk.2
        obtain ⟨z, hz, h1, h2⟩ := hS (a + k * h - h / 2) (a + k * h) (by nlinarith) (by linarith)
          (by rw [← hbN]; nlinarith)
        exact ⟨z, fun _ _ => ⟨hz, h1, h2⟩⟩
      · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hk⟩
    choose z hz using hex
    set p : ℕ → ℝ := fun k => if k = 0 then a else if k = N then b else z k with hp
    have hprop : ∀ k, k ≤ N → p k ∈ S ∧ a + k * h - h / 2 ≤ p k ∧ p k ≤ a + k * h ∧ a ≤ p k ∧ p k ≤ b := by
      intro k hk
      by_cases h0 : k = 0
      · subst h0
        simp only [hp, if_true, Nat.cast_zero, zero_mul, add_zero]
        exact ⟨ha, by linarith, le_rfl, le_rfl, hab⟩
      by_cases hN' : k = N
      · subst hN'
        simp only [hp, h0, if_false, if_true]
        exact ⟨hb, by linarith, by linarith, hab, le_rfl⟩
      have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 h0
      have hk1' : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hkN : (k : ℝ) ≤ N := by exact_mod_cast hk
      obtain ⟨hzS, hz1, hz2⟩ := hz k hk1 hk
      simp only [hp, h0, hN', if_false]
      refine ⟨hzS, hz1.le, hz2.le, by nlinarith, ?_⟩
      rw [← hbN]; nlinarith
    have hstep : ∀ k, k < N → |H (p (k + 1)) - H (p k)| ≤ C * (3 / 2 * h) * (p (k + 1) - p k) := by
      intro k hk
      obtain ⟨s1, l1, u1, a1, b1⟩ := hprop k hk.le
      obtain ⟨s2, l2, u2, a2, b2⟩ := hprop (k + 1) hk
      push_cast at l2 u2
      have hle : p k ≤ p (k + 1) := by linarith
      have hgap : p (k + 1) - p k ≤ 3 / 2 * h := by linarith
      refine (hH _ s1 _ s2 a1 hle b2 (hgap.trans ?_)).trans ?_
      · have e : (N : ℝ) * h = b - a := by linarith
        have h3 : 3 * h * N ≤ 2 * δ * N := by nlinarith
        have := le_of_mul_le_mul_right h3 hNr
        linarith
      · rw [sq]
        have h0 : 0 ≤ p (k + 1) - p k := by linarith
        calc C * ((p (k + 1) - p k) * (p (k + 1) - p k)) = C * (p (k + 1) - p k) * (p (k + 1) - p k) := by ring
          _ ≤ C * (3 / 2 * h) * (p (k + 1) - p k) := by
              apply mul_le_mul_of_nonneg_right _ h0
              exact mul_le_mul_of_nonneg_left hgap hC
    have htel : H b - H a = ∑ k ∈ Finset.range N, (H (p (k + 1)) - H (p k)) := by
      rw [Finset.sum_range_sub (fun k => H (p k))]
      have e0 : p 0 = a := by simp [hp]
      have eN : p N = b := by simp [hp, hN.ne']
      rw [e0, eN]
    have htel2 : ∑ k ∈ Finset.range N, (p (k + 1) - p k) = b - a := by
      rw [Finset.sum_range_sub p]
      have e0 : p 0 = a := by simp [hp]
      have eN : p N = b := by simp [hp, hN.ne']
      rw [e0, eN]
    rw [htel]
    calc |∑ k ∈ Finset.range N, (H (p (k + 1)) - H (p k))| ≤ ∑ k ∈ Finset.range N, |H (p (k + 1)) - H (p k)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range N, C * (3 / 2 * h) * (p (k + 1) - p k) :=
          Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.1 hk)
      _ = C * (3 / 2 * h) * (b - a) := by rw [← Finset.mul_sum, htel2]
  by_contra hne
  have hd : 0 < |H b - H a| := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨N, hN⟩ := exists_nat_gt (max (3 * (b - a) / (2 * δ)) ((C * (3 / 2) * (b - a) ^ 2) / |H b - H a|))
  have hN1 : (3 * (b - a) / (2 * δ)) < N := (le_max_left _ _).trans_lt hN
  have hN2 : (C * (3 / 2) * (b - a) ^ 2) / |H b - H a| < N := (le_max_right _ _).trans_lt hN
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN1
  have hk := key N (Nat.cast_pos.1 hN0) (by rw [div_lt_iff₀ (by positivity)] at hN1; linarith)
  rw [div_lt_iff₀ hd] at hN2
  have e : C * (3 / 2 * ((b - a) / N)) * (b - a) = C * (3 / 2) * (b - a) ^ 2 / N := by
    field_simp
  rw [e, le_div_iff₀ hN0] at hk
  linarith


theorem bilin_inner {σ : ℝ} (hσ : 0 < σ) (u ψ : X) :
    inner ℝ (bilinX σ u u) ψ = -trilinear u u (velocity (sspHeatX σ ψ)) := by
  rw [inner_bilinX bilin_holds.1 hσ]
  unfold bilinForm
  rw [tri_congr _ _ (phi_holds.2 _ hσ ψ _ (isSspOf_heat fieldOpRealized_holds heat_holds hσ ψ))]
  ring

theorem inner_curve_intervalIntegrable {y : ℝ → X} {l r M : ℝ} (hM : ∀ t ∈ Ioo l r, ‖y t‖ ≤ M)
    (hy : AEStronglyMeasurable y (volume.restrict (Ioo l r))) {a b : ℝ} (hab : a ≤ b)
    (hsub : Icc a b ⊆ Ioo l r) (c : X) :
    IntervalIntegrable (fun ρ => inner ℝ (y ρ) c) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  have hs : Ioc a b ⊆ Ioo l r := Ioc_subset_Icc_self.trans hsub
  have hm : AEStronglyMeasurable y (volume.restrict (Ioc a b)) :=
    hy.mono_measure (Measure.restrict_mono hs le_rfl)
  refine Integrable.mono' (integrable_const (M * ‖c‖)) (hm.inner aestronglyMeasurable_const) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun ρ hρ => ?_)
  rw [Real.norm_eq_abs]
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right (hM ρ (hs hρ)) (norm_nonneg _))

theorem sspRate_bound {K : ℝ} (hK : ∀ u v χ h : X, IsSspOf χ h →
      |trilinear u v (velocity h)| ≤ K * ‖u‖ * ‖v‖ * (‖χ‖ + ‖h‖)) (hK0 : 0 ≤ K)
    {M P B : ℝ} (hM0 : 0 ≤ M) {u χ h : X} (hl : IsSspOf χ h) (hu : ‖u‖ ≤ M) (hχ : ‖χ‖ ≤ P)
    (hh : ‖h‖ ≤ B) :
    |sspRate u h| ≤ M * B + K * M * M * (P + B) := by
  unfold sspRate
  have h1 : ‖u‖ * ‖h‖ ≤ M * B := mul_le_mul hu hh (norm_nonneg _) hM0
  have h2 : K * ‖u‖ * ‖u‖ ≤ K * M * M := by
    have := mul_le_mul hu hu (norm_nonneg _) hM0
    calc K * ‖u‖ * ‖u‖ = K * (‖u‖ * ‖u‖) := by ring
      _ ≤ K * (M * M) := mul_le_mul_of_nonneg_left this hK0
      _ = K * M * M := by ring
  have h3 : ‖χ‖ + ‖h‖ ≤ P + B := add_le_add hχ hh
  have h4 := mul_le_mul h2 h3 (by positivity) (mul_nonneg (mul_nonneg hK0 hM0) hM0)
  calc |inner ℝ u h + trilinear u u (velocity h)| ≤ |inner ℝ u h| + |trilinear u u (velocity h)| :=
        abs_add_le _ _
    _ ≤ ‖u‖ * ‖h‖ + K * ‖u‖ * ‖u‖ * (‖χ‖ + ‖h‖) :=
        add_le_add (abs_real_inner_le_norm _ _) (hK _ _ _ _ hl)
    _ ≤ M * B + K * M * M * (P + B) := add_le_add h1 h4

end Internal.VarConstInner

set_option maxHeartbeats 4000000 in
open Internal.VarConstInner Breakdown.Freq.Internal.MildOfWeak in
theorem varConstInner_holds : VarConstInner := by
  intro hBI y l r M E hM hy hE t₀ ht₀ t ht htt ε hε ψ
  have h1 := fieldOpRealized_holds
  have h5 := heat_holds
  have h12 := trilinear_holds
  have h13 := velocityInverts_holds
  obtain ⟨K, hK0, hK⟩ := tri_bound h1 h12 h13
  have hl : l < t₀ := (hE.sub ht₀).1
  have hr : t < r := (hE.sub ht).2
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM t₀ (hE.sub ht₀))
  have hsubI : ∀ a b, t₀ ≤ a → b ≤ t → Icc a b ⊆ Ioo l r := fun a b ha hb z hz =>
    ⟨by linarith [hz.1], by linarith [hz.2]⟩
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ : X, φ = sspHeatX (ε / 2) ψ := ⟨_, rfl⟩
  have hLrep : ∀ σ, ε / 2 ≤ σ → sspHeatX σ ψ = heatX (σ - ε / 2) φ₀ := by
    intro σ hσ
    have := heat_sspHeat (sub_nonneg.2 hσ) hε2 ψ
    rw [sub_add_cancel] at this
    rw [hφ₀]
    exact this.symm
  have hLssp : ∀ σ, ε ≤ σ → IsSspOf (sspHeatX σ ψ) (sspHeatX (σ - ε / 2) φ₀) := by
    intro σ hσ
    rw [hLrep σ (by linarith)]
    exact isSspOf_heat h1 h5 (by linarith) φ₀
  have hLnorm : ∀ σ, ε ≤ σ → ‖sspHeatX σ ψ‖ ≤ ‖φ₀‖ := by
    intro σ hσ
    rw [hLrep σ (by linarith)]
    exact ((heatX (σ - ε / 2)).le_opNorm φ₀).trans
      (mul_le_of_le_one_left (norm_nonneg _) (h5.2.2.1 _ (by linarith)))
  have hL'norm : ∀ σ, ε ≤ σ → ‖sspHeatX (σ - ε / 2) φ₀‖ ≤ (ε / 2)⁻¹ * ‖φ₀‖ := by
    intro σ hσ
    refine (norm_sspHeatX_le (by linarith) φ₀).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
    exact inv_anti₀ hε2 (by linarith)
  have hgSlope : ∀ σ σ', ε ≤ σ → σ ≤ σ' →
      ‖heatX σ' ψ - heatX σ ψ‖ ≤ ε⁻¹ * ‖ψ‖ * (σ' - σ) :=
    fun σ σ' hσ hσσ => heat_slope hε ψ hσ hσσ
  have hLSlope : ∀ σ σ', ε ≤ σ → σ ≤ σ' →
      ‖sspHeatX σ' ψ - sspHeatX σ ψ‖ ≤ (ε / 2)⁻¹ * ‖φ₀‖ * (σ' - σ) := by
    intro σ σ' hσ hσσ
    rw [hLrep σ (by linarith), hLrep σ' (by linarith)]
    have := heat_slope hε2 φ₀ (σ := σ - ε / 2) (σ' := σ' - ε / 2) (by linarith) (by linarith)
    rwa [show σ' - ε / 2 - (σ - ε / 2) = σ' - σ by ring] at this
  have hNint : IntervalIntegrable
      (fun ρ => trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ))) volume t₀ t := by
    have hB := hBI y l r M hM hy t₀ t ε hl htt hr hε.le
    have hI : IntervalIntegrable (fun τ => innerSL ℝ ψ (bilinX (t - τ + ε) (y τ) (y τ))) volume t₀ t :=
      ⟨(innerSL ℝ ψ).integrable_comp hB.1, (innerSL ℝ ψ).integrable_comp hB.2⟩
    simp only [innerSL_apply_apply] at hI
    refine hI.neg.congr_ae ?_
    refine (ae_restrict_iff' measurableSet_uIoc).2 (Filter.Eventually.of_forall fun ρ hρ => ?_)
    rw [uIoc_of_le htt] at hρ
    have hσ : 0 < t - ρ + ε := by linarith [hρ.2]
    have e1 := bilin_inner hσ (y ρ) ψ
    have e2 : inner ℝ ψ (bilinX (t - ρ + ε) (y ρ) (y ρ)) = inner ℝ (bilinX (t - ρ + ε) (y ρ) (y ρ)) ψ :=
      real_inner_comm _ _
    show -inner ℝ ψ (bilinX (t - ρ + ε) (y ρ) (y ρ)) = trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ))
    linarith
  have hNsub : ∀ a b, t₀ ≤ a → a ≤ b → b ≤ t → IntervalIntegrable
      (fun ρ => trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ))) volume a b :=
    fun a b ha hab hb => hNint.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le htt]; exact Icc_subset_Icc ha hb)
  have hnull : ∀ᵐ ρ, ρ ∈ Ioo l r → ρ ∈ E := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hE.null] with ρ hρ hρI
    by_contra hc
    exact hρ ⟨hρI, hc⟩
  have hdense : ∀ u v, t₀ ≤ u → u < v → v ≤ t → ∃ z ∈ E, u < z ∧ z < v := by
    intro u v hu huv hv
    by_contra hno
    have hsub : Ioo u v ⊆ Ioo l r \ E := fun z hz =>
      ⟨⟨by linarith [hz.1], by linarith [hz.2]⟩, fun hzE => hno ⟨z, hzE, hz.1, hz.2⟩⟩
    have hle := measure_mono (μ := volume) hsub
    rw [hE.null, Real.volume_Ioo] at hle
    exact (ENNReal.ofReal_pos.2 (sub_pos.2 huv)).ne' (nonpos_iff_eq_zero.1 hle)
  obtain ⟨H, hHdef⟩ : ∃ H : ℝ → ℝ, H = fun s => inner ℝ (y s) (heatX (t - s + ε) ψ) +
      ∫ ρ in t₀..s, trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ)) := ⟨_, rfl⟩
  have hP0 : 0 ≤ ‖φ₀‖ := norm_nonneg _
  have hB0 : 0 ≤ (ε / 2)⁻¹ * ‖φ₀‖ := by positivity
  obtain ⟨C₁, hC₁⟩ : ∃ c : ℝ, c = M * ((ε / 2)⁻¹ * ‖φ₀‖) + K * M * M * (‖φ₀‖ + (ε / 2)⁻¹ * ‖φ₀‖) :=
    ⟨_, rfl⟩
  have hC₁0 : 0 ≤ C₁ := by
    rw [hC₁]
    exact add_nonneg (mul_nonneg hM0 hB0)
      (mul_nonneg (mul_nonneg (mul_nonneg hK0 hM0) hM0) (add_nonneg hP0 hB0))
  obtain ⟨C, hC⟩ : ∃ c : ℝ, c = M * (16 / ε ^ 2 * ‖ψ‖) + C₁ +
      K * M * M * (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) := ⟨_, rfl⟩
  have hH : ∀ p ∈ E, ∀ q ∈ E, t₀ ≤ p → p ≤ q → q ≤ t → q - p ≤ ε / 2 →
      |H q - H p| ≤ max C 0 * (q - p) ^ 2 := by
    intro r₁ hr₁ r₂ hr₂ h₀₁ h₁₂ h₂t hΔ
    refine le_trans ?_ (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
    have hσ₂ : ε ≤ t - r₂ + ε := by linarith
    have hσ₂0 : 0 < t - r₂ + ε := by linarith
    obtain ⟨IL, WL⟩ := hE.weak r₁ hr₁ r₂ hr₂ h₁₂ _ _ (isSspOf_heat h1 h5 hσ₂0 ψ)
    have I1 := inner_curve_intervalIntegrable hM hy h₁₂ (hsubI r₁ r₂ h₀₁ h₂t)
      (sspHeatX (t - r₂ + ε) ψ)
    have I2 : IntervalIntegrable
        (fun ρ => trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - r₂ + ε) ψ))) volume r₁ r₂ := by
      refine (IL.sub I1).congr_ae (Filter.Eventually.of_forall fun ρ => ?_)
      simp only [sspRate]
      ring
    have I3 := hNsub r₁ r₂ h₀₁ h₁₂ h₂t
    have hsplit : ∫ ρ in r₁..r₂, sspRate (y ρ) (sspHeatX (t - r₂ + ε) ψ) =
        (∫ ρ in r₁..r₂, inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ)) +
          ∫ ρ in r₁..r₂, trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - r₂ + ε) ψ)) := by
      rw [← intervalIntegral.integral_add I1 I2]
      rfl
    have hdiff : H r₂ - H r₁ = inner ℝ (y r₂) (heatX (t - r₂ + ε) ψ) -
        inner ℝ (y r₁) (heatX (t - r₁ + ε) ψ) +
        ∫ ρ in r₁..r₂, trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ)) := by
      rw [hHdef]
      simp only
      rw [← intervalIntegral.integral_interval_sub_left (hNsub t₀ r₂ le_rfl (h₀₁.trans h₁₂) h₂t)
        (hNsub t₀ r₁ le_rfl h₀₁ (h₁₂.trans h₂t))]
      ring
    have hT2 : |inner ℝ (y r₁) (heatX (t - r₂ + ε) ψ - heatX (t - r₁ + ε) ψ -
        (r₂ - r₁) • sspHeatX (t - r₂ + ε) ψ)| ≤ M * (16 / ε ^ 2 * ‖ψ‖) * (r₂ - r₁) ^ 2 := by
      have e0 : t - r₁ + ε - (t - r₂ + ε) = r₂ - r₁ := by ring
      have ht2 := heat_expansion_norm h1 h5 hσ₂0 (r := t - r₁ + ε)
        (by rw [e0, abs_of_nonneg (by linarith)]; linarith) ψ
      rw [e0] at ht2
      have e : heatX (t - r₂ + ε) ψ - heatX (t - r₁ + ε) ψ - (r₂ - r₁) • sspHeatX (t - r₂ + ε) ψ =
          -(heatX (t - r₁ + ε) ψ - heatX (t - r₂ + ε) ψ - (r₂ - r₁) • -sspHeatX (t - r₂ + ε) ψ) := by
        rw [smul_neg]; abel
      rw [e, inner_neg_right, abs_neg]
      refine (abs_real_inner_le_norm _ _).trans ?_
      have h16 : 16 / (t - r₂ + ε) ^ 2 * (r₂ - r₁) ^ 2 * ‖ψ‖ ≤ 16 / ε ^ 2 * (r₂ - r₁) ^ 2 * ‖ψ‖ := by
        gcongr
      calc _ ≤ M * (16 / ε ^ 2 * (r₂ - r₁) ^ 2 * ‖ψ‖) :=
            mul_le_mul (hM _ (hE.sub hr₁)) (ht2.trans h16) (norm_nonneg _) hM0
        _ = _ := by ring
    have hT1 : |∫ ρ in r₁..r₂, (inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) -
        inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ))| ≤ C₁ * (r₂ - r₁) * (r₂ - r₁) := by
      rw [← Real.norm_eq_abs]
      have hb := intervalIntegral.norm_integral_le_of_norm_le_const_ae (a := r₁) (b := r₂)
        (C := C₁ * (r₂ - r₁)) (f := fun ρ => inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) -
          inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ)) ?_
      · rwa [abs_of_nonneg (by linarith : (0 : ℝ) ≤ r₂ - r₁)] at hb
      filter_upwards [hnull] with ρ hρE hρ
      rw [uIoc_of_le h₁₂] at hρ
      have hρE' : ρ ∈ E := hρE (hsubI r₁ r₂ h₀₁ h₂t ⟨hρ.1.le, hρ.2⟩)
      obtain ⟨_, W1⟩ := hE.weak r₁ hr₁ ρ hρE' hρ.1.le _ _ (hLssp _ hσ₂)
      rw [Real.norm_eq_abs, abs_sub_comm, W1, abs_neg, ← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := C₁) fun τ hτ => ?_).trans ?_
      · rw [uIoc_of_le hρ.1.le] at hτ
        rw [Real.norm_eq_abs, hC₁]
        exact sspRate_bound hK hK0 hM0 (hLssp _ hσ₂)
          (hM τ (hsubI r₁ r₂ h₀₁ h₂t ⟨hτ.1.le, hτ.2.trans hρ.2⟩)) (hLnorm _ hσ₂) (hL'norm _ hσ₂)
      · rw [abs_of_nonneg (by linarith [hρ.1])]
        exact mul_le_mul_of_nonneg_left (by linarith [hρ.2]) hC₁0
    have hT3 : |∫ ρ in r₁..r₂, (trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ)) -
        trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - r₂ + ε) ψ)))| ≤
        K * M * M * (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (r₂ - r₁) * (r₂ - r₁) := by
      rw [← Real.norm_eq_abs]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const
        (C := K * M * M * (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (r₂ - r₁)) fun ρ hρ => ?_).trans
        (le_of_eq ?_)
      · rw [uIoc_of_le h₁₂] at hρ
        have hσρ : t - r₂ + ε ≤ t - ρ + ε := by linarith [hρ.2]
        have hσρ0 : 0 < t - ρ + ε := by linarith
        have hyρ := hM ρ (hsubI r₁ r₂ h₀₁ h₂t ⟨hρ.1.le, hρ.2⟩)
        rw [← tri_sub_third h1 h12 h13 _ _ (isSspOf_heat h1 h5 hσρ0 ψ) (isSspOf_heat h1 h5 hσ₂0 ψ),
          Real.norm_eq_abs]
        refine (hK _ _ _ _ (isSspOf_sub (isSspOf_heat h1 h5 hσρ0 ψ)
          (isSspOf_heat h1 h5 hσ₂0 ψ))).trans ?_
        have hg := hgSlope _ _ hσ₂ hσρ
        have hL := hLSlope _ _ hσ₂ hσρ
        have hd : t - ρ + ε - (t - r₂ + ε) ≤ r₂ - r₁ := by linarith [hρ.1]
        have hA0 : 0 ≤ ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖ := by positivity
        have hA : ‖heatX (t - ρ + ε) ψ - heatX (t - r₂ + ε) ψ‖ +
            ‖sspHeatX (t - ρ + ε) ψ - sspHeatX (t - r₂ + ε) ψ‖ ≤
            (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (r₂ - r₁) := by
          calc _ ≤ ε⁻¹ * ‖ψ‖ * (t - ρ + ε - (t - r₂ + ε)) +
                (ε / 2)⁻¹ * ‖φ₀‖ * (t - ρ + ε - (t - r₂ + ε)) := add_le_add hg hL
            _ = (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (t - ρ + ε - (t - r₂ + ε)) := by ring
            _ ≤ _ := mul_le_mul_of_nonneg_left hd hA0
        have hKy : K * ‖y ρ‖ * ‖y ρ‖ ≤ K * M * M := by
          have := mul_le_mul hyρ hyρ (norm_nonneg _) hM0
          calc K * ‖y ρ‖ * ‖y ρ‖ = K * (‖y ρ‖ * ‖y ρ‖) := by ring
            _ ≤ K * (M * M) := mul_le_mul_of_nonneg_left this hK0
            _ = K * M * M := by ring
        calc _ ≤ K * M * M * ((ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (r₂ - r₁)) :=
              mul_le_mul hKy hA (by positivity) (mul_nonneg (mul_nonneg hK0 hM0) hM0)
          _ = _ := by ring
      · rw [abs_of_nonneg (by linarith)]
    have hsum : H r₂ - H r₁ = inner ℝ (y r₁) (heatX (t - r₂ + ε) ψ - heatX (t - r₁ + ε) ψ -
        (r₂ - r₁) • sspHeatX (t - r₂ + ε) ψ) +
        (∫ ρ in r₁..r₂, (inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) -
          inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ))) +
        ∫ ρ in r₁..r₂, (trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - ρ + ε) ψ)) -
          trilinear (y ρ) (y ρ) (velocity (sspHeatX (t - r₂ + ε) ψ))) := by
      have s1 : ∫ ρ in r₁..r₂, (inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) -
          inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ)) = (r₂ - r₁) * inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) -
          ∫ ρ in r₁..r₂, inner ℝ (y ρ) (sspHeatX (t - r₂ + ε) ψ) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const I1, intervalIntegral.integral_const,
          smul_eq_mul]
      have s2 := intervalIntegral.integral_sub I3 I2
      have s3 : inner ℝ (y r₁) (heatX (t - r₂ + ε) ψ - heatX (t - r₁ + ε) ψ -
          (r₂ - r₁) • sspHeatX (t - r₂ + ε) ψ) = inner ℝ (y r₁) (heatX (t - r₂ + ε) ψ) -
          inner ℝ (y r₁) (heatX (t - r₁ + ε) ψ) - (r₂ - r₁) * inner ℝ (y r₁) (sspHeatX (t - r₂ + ε) ψ) := by
        rw [inner_sub_right, inner_sub_right, real_inner_smul_right]
      rw [hsplit] at WL
      rw [hdiff, s1, s2, s3]
      linarith
    rw [hsum]
    calc _ ≤ _ := abs_add_three _ _ _
      _ ≤ M * (16 / ε ^ 2 * ‖ψ‖) * (r₂ - r₁) ^ 2 + C₁ * (r₂ - r₁) * (r₂ - r₁) +
          K * M * M * (ε⁻¹ * ‖ψ‖ + (ε / 2)⁻¹ * ‖φ₀‖) * (r₂ - r₁) * (r₂ - r₁) :=
          add_le_add (add_le_add hT2 hT1) hT3
      _ = C * (r₂ - r₁) ^ 2 := by rw [hC]; ring
  have hHeq := chain_const htt ht₀ ht hdense H (le_max_right C 0) hε2 hH
  rw [hHdef] at hHeq
  simp only [sub_self, zero_add, intervalIntegral.integral_same, add_zero] at hHeq
  have hint : ∫ τ in t₀..t, inner ℝ (bilinX (t - τ + ε) (y τ) (y τ)) ψ =
      -∫ τ in t₀..t, trilinear (y τ) (y τ) (velocity (sspHeatX (t - τ + ε) ψ)) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le htt] at hτ
    exact bilin_inner (by linarith [hτ.2]) _ _
  rw [hint]
  linarith

end Breakdown.WeakProfile

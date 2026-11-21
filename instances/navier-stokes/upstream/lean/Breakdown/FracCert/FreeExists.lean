import Breakdown.FracCert.StFreeNice
import Breakdown.Frac.SpaceDecay

open scoped ContDiff ENNReal
open MeasureTheory Real Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeExistsInternal

theorem axialTurn_add (x w : Space) : axialTurn (x + w) = axialTurn x + axialTurn w := by
  ext i; fin_cases i <;> simp [axialTurn] <;> ring

theorem axialTurn_smul (c : ℝ) (x : Space) : axialTurn (c • x) = c • axialTurn x := by
  ext i; fin_cases i <;> simp [axialTurn]

theorem axialTurn_sub (x w : Space) : axialTurn (x - w) = axialTurn x - axialTurn w := by
  ext i; fin_cases i <;> simp [axialTurn] <;> ring

theorem axialTurn_continuous : Continuous axialTurn := by
  let L : Space →ₗ[ℝ] Space := ⟨⟨axialTurn, axialTurn_add⟩, axialTurn_smul⟩
  exact L.continuous_of_finiteDimensional

theorem sum_unit (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem clm_tendsto {K : ℕ → Space →L[ℝ] Space} {K₀ : Space →L[ℝ] Space}
    (h : ∀ i, Tendsto (fun n => K n (unitVector i)) atTop (𝓝 (K₀ (unitVector i)))) (x : Space) :
    Tendsto (fun n => K n x) atTop (𝓝 (K₀ x)) := by
  have e : ∀ L : Space →L[ℝ] Space, L x = ∑ j : Fin 3, x j • L (unitVector j) := by
    intro L
    conv_lhs => rw [sum_unit x]
    simp [map_sum, map_smul]
  rw [show (fun n => K n x) = fun n => ∑ j : Fin 3, x j • K n (unitVector j) from funext fun n => e (K n),
    e K₀]
  exact tendsto_finsetSum _ fun j _ => (h j).const_smul (x j)

theorem l2Norm_eq {f : Space → Space} (hf : MemLp f 2 volume) : l2Norm f = ‖hf.toLp f‖ := by
  rw [Lp.norm_toLp, hf.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top,
    ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [l2Norm, Real.sqrt_eq_rpow, one_div]

theorem l2Norm_sub {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Norm (fun y => f y - g y) = ‖hf.toLp f - hg.toLp g‖ := by
  rw [← MemLp.toLp_sub]
  exact l2Norm_eq (hf.sub hg)

theorem inner_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem power_memLp {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {φ : Space → Space}
    (hφ : IsTestVectorField φ) :
    MemLp (fractionalPowerAt α φ) (ENNReal.ofReal (6 / 5)) volume := by
  obtain ⟨hc, C, hC⟩ := fracCompactDecay α h1 h2 φ hφ.1 hφ.2
  have hr : ((Module.finrank ℝ Space : ℕ) : ℝ) < (3 + 2 * α) * (6 / 5) := by
    rw [finrank_euclideanSpace_fin]; push_cast; nlinarith
  have hint := integrable_one_add_norm (E := Space) (μ := volume) hr
  have hm : AEStronglyMeasurable (fun x : Space => (1 + ‖x‖) ^ (-(3 + 2 * α))) volume :=
    (Continuous.rpow_const (continuous_const.add continuous_norm)
      fun x => Or.inl (by show (1 : ℝ) + ‖x‖ ≠ 0; positivity)).aestronglyMeasurable
  have hdom : MemLp (fun x : Space => (1 + ‖x‖) ^ (-(3 + 2 * α))) (ENNReal.ofReal (6 / 5)) volume := by
    refine (integrable_norm_rpow_iff hm (by simp) ENNReal.ofReal_ne_top).1 ?_
    refine hint.congr (ae_of_all _ fun x => ?_)
    have hx : (0 : ℝ) < 1 + ‖x‖ := by positivity
    show (1 + ‖x‖) ^ (-((3 + 2 * α) * (6 / 5))) = ‖(1 + ‖x‖) ^ (-(3 + 2 * α))‖ ^ (ENNReal.ofReal (6 / 5)).toReal
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _), ENNReal.toReal_ofReal (by norm_num),
      ← Real.rpow_mul hx.le]
    ring_nf
  refine (hdom.const_mul C).of_le hc.aestronglyMeasurable (ae_of_all _ fun x => ?_)
  exact (hC x).trans (le_abs_self _)

theorem conj_six : (6 : ℝ).HolderConjugate (6 / 5) :=
  Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩

theorem six_memLp {w : Space → Space} (hw : MemLp w 6 volume) :
    MemLp (fun y => ‖w y‖) (ENNReal.ofReal 6) volume := by
  have e : ENNReal.ofReal 6 = 6 := by norm_num
  rw [e]; exact hw.norm

theorem pair_integrable {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {φ : Space → Space}
    (hφ : IsTestVectorField φ) {w : Space → Space} (hw : MemLp w 6 volume) :
    Integrable (fun y => inner ℝ (w y) (fractionalPowerAt α φ y)) volume := by
  have := conj_six.ennrealOfReal
  have hg := (power_memLp h1 h2 hφ).norm
  have hi : Integrable (fun y => ‖w y‖ * ‖fractionalPowerAt α φ y‖) volume :=
    (six_memLp hw).integrable_mul hg
  refine hi.mono (hw.1.inner (power_memLp h1 h2 hφ).1) (ae_of_all _ fun y => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg (w y)) (norm_nonneg (fractionalPowerAt α φ y)))]
  exact norm_inner_le_norm _ _

theorem pair_bound {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {φ : Space → Space}
    (hφ : IsTestVectorField φ) {w : Space → Space} (hw : MemLp w 6 volume) :
    |∫ y, inner ℝ (w y) (fractionalPowerAt α φ y)| ≤
      (∫ y, ‖w y‖ ^ 6) ^ (1 / (6 : ℝ)) *
        (∫ y, ‖fractionalPowerAt α φ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)) := by
  have := conj_six.ennrealOfReal
  have hg := (power_memLp h1 h2 hφ).norm
  have hi : Integrable (fun y => ‖w y‖ * ‖fractionalPowerAt α φ y‖) volume :=
    (six_memLp hw).integrable_mul hg
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg conj_six (ae_of_all _ fun y => norm_nonneg (w y))
    (ae_of_all _ fun y => norm_nonneg (fractionalPowerAt α φ y)) (six_memLp hw) hg
  have e6 : ∀ y, ‖w y‖ ^ (6 : ℝ) = ‖w y‖ ^ 6 := fun y => by exact_mod_cast Real.rpow_natCast ‖w y‖ 6
  simp only [e6] at hh
  calc |∫ y, inner ℝ (w y) (fractionalPowerAt α φ y)|
      ≤ ∫ y, ‖inner ℝ (w y) (fractionalPowerAt α φ y)‖ := by
        rw [← Real.norm_eq_abs]; exact norm_integral_le_integral_norm _
    _ ≤ ∫ y, ‖w y‖ * ‖fractionalPowerAt α φ y‖ :=
        integral_mono (pair_integrable h1 h2 hφ hw).norm hi (fun y => norm_inner_le_norm _ _)
    _ ≤ _ := hh

theorem sub_field (h5 : SecondOrderLinearStatement) {m : ℕ} {v u : Space → Space}
    {G K : Space → (Space →L[ℝ] Space)} {H L : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField m v G H) (hu : IsSecondOrderField m u K L) :
    IsSecondOrderField m (fun y => v y - u y) (fun y => G y - K y) (fun y => H y - L y) := by
  have h := h5 m v u G K H L (-1) hv hu
  simp only [neg_one_smul, ← sub_eq_add_neg] at h
  exact h

theorem sub_power {α : ℝ} (h1 : 1 < α) (h2 : α < 3 / 2) {v u P Q : Space → Space}
    (hv : MemLp v 6 volume) (hu : MemLp u 6 volume)
    (hP : IsWeakFractionalPower α v P) (hQ : IsWeakFractionalPower α u Q) :
    IsWeakFractionalPower α (fun y => v y - u y) (fun y => P y - Q y) := by
  refine ⟨hP.1.sub hQ.1, fun φ hφ => ?_⟩
  have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
  simp only [inner_sub_left]
  rw [integral_sub (inner_integrable hP.1 hφ2) (inner_integrable hQ.1 hφ2),
    integral_sub (pair_integrable h1 h2 hφ hv) (pair_integrable h1 h2 hφ hu), hP.2 φ hφ, hQ.2 φ hφ]

theorem drift_sub (α a : ℝ) (v u : Space → Space) (G K : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun y => v y - u y) (fun y => G y - K y) y =
      driftField α a v G y - driftField α a u K y := by
  simp only [driftField, ContinuousLinearMap.sub_apply, axialTurn_sub, smul_sub]
  abel

theorem sq_bound {A B c ε : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (h : Real.sqrt A + Real.sqrt B ≤ c)
    (hc : c < Real.sqrt ε) (hε : 0 < ε) : A + B < ε := by
  have hsA := Real.sq_sqrt hA
  have hsB := Real.sq_sqrt hB
  have hsE := Real.sq_sqrt hε.le
  have hs : Real.sqrt A + Real.sqrt B < Real.sqrt ε := lt_of_le_of_lt h hc
  have := mul_self_lt_mul_self (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg B)) hs
  nlinarith [Real.sqrt_nonneg A, Real.sqrt_nonneg B]

theorem tendsto_of_pow {f : ℕ → ℝ} (hf : ∀ i, 0 ≤ f i) {k : ℕ} (hk : k ≠ 0)
    (h : Tendsto (fun i => f i ^ k) atTop (𝓝 0)) : Tendsto f atTop (𝓝 0) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have := h.rpow_const (p := (k : ℝ)⁻¹) (Or.inr (inv_nonneg.2 hk'.le))
  rw [Real.zero_rpow (inv_ne_zero hk'.ne')] at this
  exact this.congr fun i => Real.pow_rpow_inv_natCast (hf i) hk

theorem closure_core (h3 : FreeBoundsStatement) (h4 : SecondOrderCompleteStatement)
    (h5 : SecondOrderLinearStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ)
    {F : Space → Space} (hF : MemLp F 2 volume) (Fn : ℕ → Space → Space)
    (hFnF : ∀ n : ℕ, ∫ y, ‖F y - Fn n y‖ ^ 2 < 1 / ((n : ℝ) + 1))
    (v : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
    (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : ℕ → Space → Space)
    (hv : ∀ n, IsSecondOrderField m (v n) (G n) (H n)) (hP : ∀ n, IsWeakFractionalPower α (v n) (P n))
    (hD : ∀ n, MemLp (driftField α a (v n) (G n)) 2 volume)
    (hE : ∀ n, ∀ᵐ y ∂volume, driftField α a (v n) (G n) y + P n y = Fn n y) :
    ∃ (v₀ : Space → Space) (G₀ : Space → (Space →L[ℝ] Space))
      (H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P₀ : Space → Space),
      IsSecondOrderField m v₀ G₀ H₀ ∧ IsWeakFractionalPower α v₀ P₀ ∧
      MemLp (driftField α a v₀ G₀) 2 volume ∧ ∀ᵐ y ∂volume, driftField α a v₀ G₀ y + P₀ y = F y := by
  have hα32 : α < 3 / 2 := by linarith
  obtain ⟨C₀, hC₀⟩ := h3 α hα1 hα2
  have hFn2 : ∀ n, MemLp (Fn n) 2 volume := fun n => ((hD n).add (hP n).1).ae_eq (hE n)
  have hB : ∀ n k, _ := fun n k => hC₀ a m _ _ _ _ (fun y => Fn n y - Fn k y)
    (sub_field h5 (hv n) (hv k))
    (sub_power hα1 hα32 (hv n).velocity_six (hv k).velocity_six (hP n) (hP k))
    (((hD n).sub (hD k)).ae_eq (Eventually.of_forall fun y => (drift_sub α a _ _ _ _ y).symm))
    ((hFn2 n).sub (hFn2 k))
    (by
      filter_upwards [hE n, hE k] with y e1 e2
      rw [drift_sub, ← e1, ← e2]
      abel)
  let FL : ℕ → Lp Space 2 volume := fun n => (hFn2 n).toLp (Fn n)
  let PL : ℕ → Lp Space 2 volume := fun n => (hP n).1.toLp (P n)
  have hFL : Tendsto FL atTop (𝓝 (hF.toLp F)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hs := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).sqrt
    rw [Real.sqrt_zero] at hs
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hs
    show ‖(hFn2 n).toLp (Fn n) - hF.toLp F‖ ≤ _
    rw [← l2Norm_sub (hFn2 n) hF]
    refine Real.sqrt_le_sqrt ?_
    calc ∫ y, ‖Fn n y - F y‖ ^ 2 = ∫ y, ‖F y - Fn n y‖ ^ 2 :=
          integral_congr_ae (ae_of_all _ fun y => by simp only [norm_sub_rev (Fn n y)])
      _ ≤ _ := (hFnF n).le
  have hFc := hFL.cauchySeq
  have hPc : CauchySeq PL := by
    rw [Metric.cauchySeq_iff] at hFc ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hFc ε hε
    refine ⟨N, fun n hn k hk => ?_⟩
    have hd := hN n hn k hk
    rw [dist_eq_norm] at hd ⊢
    calc ‖PL n - PL k‖ = l2Norm (fun y => P n y - P k y) := (l2Norm_sub (hP n).1 (hP k).1).symm
      _ ≤ l2Norm (fun y => Fn n y - Fn k y) := (hB n k).1
      _ = ‖FL n - FL k‖ := l2Norm_sub (hFn2 n) (hFn2 k)
      _ < ε := hd
  obtain ⟨P0L, hP0⟩ := cauchySeq_tendsto_of_complete hPc
  have hcE : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ n' ≥ N,
      weightedEnergy (fun _ => (1 : ℝ)) (fun y => G n y - G n' y) (fun y => H n y - H n' y) < ε := by
    intro ε hε
    have hδ : 0 < Real.sqrt ε / (|C₀| + 1) := by positivity
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hFc _ hδ
    refine ⟨N, fun n hn k hk => ?_⟩
    have hd := hN n hn k hk
    rw [dist_eq_norm] at hd
    have hd' : l2Norm (fun y => Fn n y - Fn k y) < Real.sqrt ε / (|C₀| + 1) := by
      rw [l2Norm_sub (hFn2 n) (hFn2 k)]; exact hd
    have hl0 : 0 ≤ l2Norm (fun y => Fn n y - Fn k y) := Real.sqrt_nonneg _
    have hsε := Real.sqrt_pos.2 hε
    have hlt : C₀ * l2Norm (fun y => Fn n y - Fn k y) < Real.sqrt ε := by
      have i1 : C₀ * l2Norm (fun y => Fn n y - Fn k y) ≤ |C₀| * l2Norm (fun y => Fn n y - Fn k y) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) hl0
      have i2 : |C₀| * l2Norm (fun y => Fn n y - Fn k y) ≤ |C₀| * (Real.sqrt ε / (|C₀| + 1)) :=
        mul_le_mul_of_nonneg_left hd'.le (abs_nonneg _)
      have i3 : |C₀| * (Real.sqrt ε / (|C₀| + 1)) < Real.sqrt ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith [abs_nonneg C₀]
      linarith
    simp only [weightedEnergy, one_mul]
    exact sq_bound (integral_nonneg fun _ => by positivity) (integral_nonneg fun _ => by
      simp only [entrySq]; positivity) (hB n k).2.2.2 hlt hε
  obtain ⟨v₀, G₀, H₀, h0, hEn, hv6⟩ := h4 m (fun _ => (1 : ℝ)) 1 one_pos measurable_const
    (fun _ => le_rfl) ⟨1, fun _ => le_rfl⟩ v G H hv hcE
  have hPow0 : IsWeakFractionalPower α v₀ (P0L : Space → Space) := by
    refine ⟨Lp.memLp P0L, fun φ hφ => ?_⟩
    have hφ2 : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2
    have e : ∀ (f : Lp Space 2 volume) (g : Space → Space), (f : Space → Space) =ᵐ[volume] g →
        inner ℝ f (hφ2.toLp φ) = ∫ y, inner ℝ (g y) (φ y) := by
      intro f g hfg
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hfg, hφ2.coeFn_toLp] with y e1 e2
      rw [e1, e2]
    have hl : Tendsto (fun n => ∫ y, inner ℝ (P n y) (φ y)) atTop
        (𝓝 (∫ y, inner ℝ ((P0L : Space → Space) y) (φ y))) := by
      have ht := hP0.inner (𝕜 := ℝ) (tendsto_const_nhds (x := hφ2.toLp φ))
      rw [e P0L P0L (ae_eq_refl _)] at ht
      exact ht.congr fun n => e _ _ (hP n).1.coeFn_toLp
    have hr : Tendsto (fun n => ∫ y, inner ℝ (v n y) (fractionalPowerAt α φ y)) atTop
        (𝓝 (∫ y, inner ℝ (v₀ y) (fractionalPowerAt α φ y))) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      have hlim : Tendsto (fun n => (∫ y, ‖v n y - v₀ y‖ ^ 6) ^ (1 / (6 : ℝ)) *
          (∫ y, ‖fractionalPowerAt α φ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ))) atTop (𝓝 0) := by
        have := (hv6.rpow_const (p := 1 / (6 : ℝ)) (Or.inr (by norm_num))).mul_const
          ((∫ y, ‖fractionalPowerAt α φ y‖ ^ (6 / 5 : ℝ)) ^ (1 / (6 / 5 : ℝ)))
        rwa [Real.zero_rpow (by norm_num), zero_mul] at this
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
      have eq : (∫ y, inner ℝ (v n y) (fractionalPowerAt α φ y)) - ∫ y, inner ℝ (v₀ y) (fractionalPowerAt α φ y)
          = ∫ y, inner ℝ (v n y - v₀ y) (fractionalPowerAt α φ y) := by
        rw [← integral_sub (pair_integrable hα1 hα32 hφ (hv n).velocity_six)
          (pair_integrable hα1 hα32 hφ h0.velocity_six)]
        simp only [inner_sub_left]
      rw [Real.norm_eq_abs, eq]
      exact pair_bound hα1 hα32 hφ ((hv n).velocity_six.sub h0.velocity_six)
    exact tendsto_nhds_unique hl (hr.congr fun n => ((hP n).2 φ hφ).symm)
  have hE0 : MemLp (fun y => F y - (P0L : Space → Space) y) 2 volume := hF.sub (Lp.memLp P0L)
  have hEn2 : ∀ n, MemLp (fun y => Fn n y - P n y) 2 volume := fun n => (hFn2 n).sub (hP n).1
  have hEt : Tendsto (fun n => ∫ y, ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2) atTop (𝓝 0) := by
    have eqn : ∀ n, ∫ y, ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2 =
        ‖(hEn2 n).toLp (fun y => Fn n y - P n y) - hE0.toLp (fun y => F y - (P0L : Space → Space) y)‖ ^ 2 := by
      intro n
      rw [← l2Norm_sub (hEn2 n) hE0, l2Norm, Real.sq_sqrt (integral_nonneg fun _ => by positivity)]
    have hT : Tendsto (fun n => (hEn2 n).toLp (fun y => Fn n y - P n y)) atTop
        (𝓝 (hE0.toLp (fun y => F y - (P0L : Space → Space) y))) := by
      have e1 : ∀ n, (hEn2 n).toLp (fun y => Fn n y - P n y) = FL n - PL n :=
        fun n => MemLp.toLp_sub (hFn2 n) (hP n).1
      have e2 : hE0.toLp (fun y => F y - (P0L : Space → Space) y) = hF.toLp F - P0L := by
        rw [show hE0.toLp (fun y => F y - (P0L : Space → Space) y) = hF.toLp F - (Lp.memLp P0L).toLp P0L
          from MemLp.toLp_sub hF (Lp.memLp P0L), Lp.toLp_coeFn]
      simp only [e1, e2]
      exact hFL.sub hP0
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hT).pow 2
    rw [zero_pow two_ne_zero] at this
    exact this.congr fun n => (eqn n).symm
  have hbE : Tendsto (fun n => ∫ y, entrySq (G n y - G₀ y)) atTop (𝓝 0) := by
    simp only [weightedEnergy, one_mul] at hEn
    refine squeeze_zero (fun n => integral_nonneg fun _ => by simp only [entrySq]; positivity)
      (fun n => ?_) hEn
    have : 0 ≤ ∫ y, ‖secondTrace (H n y - H₀ y)‖ ^ 2 := integral_nonneg fun _ => by positivity
    linarith
  obtain ⟨hh, hhdef⟩ : ∃ hh : ℕ → Space → ℝ, ∀ n y, hh n y = ‖v n y - v₀ y‖ ^ 6 +
      entrySq (G n y - G₀ y) + ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2 :=
    ⟨_, fun _ _ => rfl⟩
  have ia : ∀ n, Integrable (fun y => ‖v n y - v₀ y‖ ^ 6) volume := fun n =>
    ((hv n).velocity_six.sub h0.velocity_six).integrable_norm_pow (p := 6) (by norm_num)
  have ib : ∀ n, Integrable (fun y => entrySq (G n y - G₀ y)) volume := fun n =>
    (sub_field h5 (hv n) h0).gradient_two
  have ic : ∀ n, Integrable (fun y => ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2) volume :=
    fun n => ((hEn2 n).sub hE0).integrable_norm_pow (p := 2) two_ne_zero
  have hint : ∀ n, Integrable (hh n) volume := fun n => by
    have := ((ia n).add (ib n)).add (ic n)
    refine this.congr (ae_of_all _ fun y => ?_)
    simp only [Pi.add_apply, hhdef]
  have hnn : ∀ n y, 0 ≤ hh n y := fun n y => by rw [hhdef]; simp only [entrySq]; positivity
  have hlimI : Tendsto (fun n => ∫ y, hh n y) atTop (𝓝 0) := by
    have e : ∀ n, ∫ y, hh n y = (∫ y, ‖v n y - v₀ y‖ ^ 6) + (∫ y, entrySq (G n y - G₀ y)) +
        ∫ y, ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2 := fun n => by
      have iab : Integrable (fun y => ‖v n y - v₀ y‖ ^ 6 + entrySq (G n y - G₀ y)) volume := (ia n).add (ib n)
      rw [← integral_add (ia n) (ib n), ← integral_add iab (ic n)]
      exact integral_congr_ae (ae_of_all _ fun y => by simp only [Pi.add_apply, hhdef])
    simp only [e]
    have := (hv6.add hbE).add hEt
    simpa using this
  have hmeas : TendstoInMeasure volume hh atTop (fun _ => 0) := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
      (fun n => (hint n).aestronglyMeasurable) aestronglyMeasurable_const ?_
    have e : ∀ n, eLpNorm (hh n - fun _ => (0 : ℝ)) 1 volume = ENNReal.ofReal (∫ y, hh n y) := fun n => by
      have h0' : hh n - (fun _ => (0 : ℝ)) = hh n := by ext y; simp
      rw [h0', eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hint n)]
      congr 1
      exact integral_congr_ae (ae_of_all _ fun y => Real.norm_of_nonneg (hnn n y))
    simp only [e]
    have := ENNReal.tendsto_ofReal hlimI
    rwa [ENNReal.ofReal_zero] at this
  obtain ⟨ψ, -, hae⟩ := hmeas.exists_seq_tendsto_ae
  have hlimit : ∀ᵐ y ∂volume, driftField α a v₀ G₀ y = F y - (P0L : Space → Space) y := by
    filter_upwards [hae, ae_all_iff.2 hE] with y hy hEy
    have part : ∀ f : ℕ → ℝ, (∀ n, 0 ≤ f n) → (∀ n, f n ≤ hh n y) →
        Tendsto (fun i => f (ψ i)) atTop (𝓝 0) := fun f h0f hle =>
      squeeze_zero (fun i => h0f _) (fun i => hle _) hy
    have tv : Tendsto (fun i => v (ψ i) y) atTop (𝓝 (v₀ y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 6) (by norm_num) ?_
      exact part (fun n => ‖v n y - v₀ y‖ ^ 6) (fun n => by positivity) (fun n => by
        rw [hhdef]; have : 0 ≤ entrySq (G n y - G₀ y) := by simp only [entrySq]; positivity
        nlinarith [sq_nonneg ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖])
    have tG : ∀ x, Tendsto (fun i => G (ψ i) y x) atTop (𝓝 (G₀ y x)) := by
      refine clm_tendsto (K := fun i => G (ψ i) y) fun j => ?_
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 2) two_ne_zero ?_
      refine part (fun n => ‖G n y (unitVector j) - G₀ y (unitVector j)‖ ^ 2) (fun n => by positivity)
        (fun n => ?_)
      have hj : ‖G n y (unitVector j) - G₀ y (unitVector j)‖ ^ 2 ≤ entrySq (G n y - G₀ y) := by
        have := Finset.single_le_sum (f := fun i : Fin 3 => ‖(G n y - G₀ y) (unitVector i)‖ ^ 2)
          (fun i _ => sq_nonneg _) (Finset.mem_univ j)
        simpa [entrySq] using this
      rw [hhdef]
      nlinarith [sq_nonneg ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖,
        pow_nonneg (norm_nonneg (v n y - v₀ y)) 6]
    have tE : Tendsto (fun i => Fn (ψ i) y - P (ψ i) y) atTop (𝓝 (F y - (P0L : Space → Space) y)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine tendsto_of_pow (fun i => norm_nonneg _) (k := 2) two_ne_zero ?_
      refine part (fun n => ‖(Fn n y - P n y) - (F y - (P0L : Space → Space) y)‖ ^ 2)
        (fun n => by positivity) (fun n => ?_)
      rw [hhdef]
      have : 0 ≤ entrySq (G n y - G₀ y) := by simp only [entrySq]; positivity
      nlinarith [pow_nonneg (norm_nonneg (v n y - v₀ y)) 6]
    have tD : Tendsto (fun i => driftField α a (v (ψ i)) (G (ψ i)) y) atTop
        (𝓝 (driftField α a v₀ G₀ y)) := by
      simp only [driftField]
      exact ((tv.const_smul _).add ((tG y).const_smul _)).add
        (((tG (axialTurn y)).sub ((axialTurn_continuous.tendsto _).comp tv)).const_smul _)
    refine tendsto_nhds_unique tD (tE.congr fun i => ?_)
    exact (eq_sub_of_add_eq (hEy (ψ i))).symm
  refine ⟨v₀, G₀, H₀, (P0L : Space → Space), h0, hPow0, hE0.ae_eq (hlimit.mono fun y h => h.symm), ?_⟩
  filter_upwards [hlimit] with y h
  rw [h, sub_add_cancel]

end FreeExistsInternal

theorem freeExists_of (h1 : FreeExistsNiceStatement) (h2 : NiceClassDenseStatement)
    (h3 : FreeBoundsStatement) (h4 : SecondOrderCompleteStatement) (h5 : SecondOrderLinearStatement) :
    FreeExistsStatement := by
  intro α hα1 hα2 a m F hF hFc
  have hs : ∀ n : ℕ, ∃ s : Space → Freq.CSpace, Freq.IsNiceSymbol s ∧ IsClassField m (Freq.niceField s) ∧
      ∫ y, ‖F y - Freq.niceField s y‖ ^ 2 < 1 / ((n : ℝ) + 1) :=
    fun n => h2 m F hF hFc _ (by positivity)
  choose s hsn hsc hsF using hs
  have hsol := fun n => h1 α hα1 hα2 a m (s n) (hsn n) (hsc n)
  choose v G H P hv hP hD hE using hsol
  exact FreeExistsInternal.closure_core h3 h4 h5 hα1 hα2 a m hF.1 (fun n => Freq.niceField (s n)) hsF
    v G H P hv hP hD hE

end SteadyCert

end Breakdown

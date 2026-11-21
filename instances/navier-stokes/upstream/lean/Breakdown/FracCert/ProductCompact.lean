import Breakdown.FracCert.StFree
import Breakdown.FreqTr.BilinCompact
import Breakdown.Cert.TranslationCriterion

open scoped ContDiff ENNReal Topology
open MeasureTheory Real Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def BallShiftStatement : Prop :=
  ∀ (u : Space → Space) (K : Space → (Space →L[ℝ] Space)) (R : ℝ), AEStronglyMeasurable u volume →
    IsWeakGradientOf u K → IntegrableOn (fun y => ‖u y‖ ^ 2) (Metric.ball (0 : Space) (R + 2)) →
    Integrable (fun y => entrySq (K y)) → ∀ h : Space, ‖h‖ ≤ 1 →
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖u (y + h) - u y‖ ^ 2) ≤
      ENNReal.ofReal (‖h‖ ^ 2 * ∫ y, entrySq (K y))

def BallCompactStatement : Prop :=
  ∀ (u : ℕ → Space → Space) (K : ℕ → Space → (Space →L[ℝ] Space)) (R A : ℝ),
    (∀ n, AEStronglyMeasurable (u n) volume) → (∀ n, AEStronglyMeasurable (K n) volume) →
    (∀ n, IsWeakGradientOf (u n) (K n)) →
    (∀ n, IntegrableOn (fun y => ‖u n y‖ ^ 2) (Metric.ball (0 : Space) (R + 2))) →
    (∀ n, Integrable (fun y => entrySq (K n y))) →
    (∀ n, (∫ y in Metric.ball (0 : Space) (R + 2), ‖u n y‖ ^ 2) + (∫ y, entrySq (K n y)) ≤ A) →
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, ∫ y in Metric.ball (0 : Space) R, ‖u n y - u k y‖ ^ 2 < ε

def BallNetStatement : Prop :=
  ∀ (m : ℕ) (v : ℕ → Space → Space) (G : ℕ → Space → (Space →L[ℝ] Space))
    (H : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (B : ℝ), (∀ n, IsSecondOrderField m (v n) (G n) (H n)) →
    (∀ n, Integrable (fun y => ‖v n y‖ ^ 2 / ‖y‖ ^ 2)) →
    (∀ n, (∫ y, ‖v n y‖ ^ 2 / ‖y‖ ^ 2) + (∫ y, entrySq (G n y)) + (∫ y, fullSecondSq (H n y)) ≤ B) →
    ∀ R ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S,
      ∫ y in Metric.ball (0 : Space) R, (‖v n y - v k y‖ ^ 2 + entrySq (G n y - G k y)) < ε

namespace ProductCompactInternal

private theorem integral_sq_dist (u w : Freq.L2R) (f g : Space → Space) (hf : f =ᵐ[volume] u) (hg : g =ᵐ[volume] w) :
    ∫ y, ‖f y - g y‖ ^ 2 = ‖u - w‖ ^ 2 := by
  rw [← Freq.Internal.BilinCompact.integral_sq_norm (u - w)]
  apply integral_congr_ae
  filter_upwards [hf, hg, Lp.coeFn_sub u w] with y h1 h2 h3
  rw [h3, Pi.sub_apply, h1, h2]

private theorem subseq_of_net (F : ℕ → Space → Space) (hF : ∀ n, MemLp (F n) 2 volume)
    (hnet : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, ∫ y, ‖F n y - F k y‖ ^ 2 < ε) :
    ∃ (φ : ℕ → ℕ) (L : Space → Space), StrictMono φ ∧ MemLp L 2 volume ∧
      Tendsto (fun n => ∫ y, ‖F (φ n) y - L y‖ ^ 2) atTop (nhds 0) := by
  let x : ℕ → Freq.L2R := fun n => (hF n).toLp (F n)
  have hx : ∀ n, F n =ᵐ[volume] (x n : Space → Space) := fun n => ((hF n).coeFn_toLp).symm
  have htb : TotallyBounded (Set.range x) := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨S, hS⟩ := hnet (ε ^ 2) (by positivity)
    refine ⟨x '' (S : Set ℕ), (S.finite_toSet.image x), ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨k, hk, hlt⟩ := hS n
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    refine ⟨x k, ⟨k, hk, rfl⟩, ?_⟩
    rw [Metric.mem_ball, dist_eq_norm]
    rw [integral_sq_dist (x n) (x k) (F n) (F k) (hx n) (hx k)] at hlt
    exact lt_of_pow_lt_pow_left₀ 2 hε.le hlt
  obtain ⟨a, -, φ, hφ, hlim⟩ := (TotallyBounded.isCompact_of_isClosed (TotallyBounded.closure htb) isClosed_closure).tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩)
  refine ⟨φ, (a : Space → Space), hφ, Lp.memLp a, ?_⟩
  have h1 : ∀ n, ∫ y, ‖F (φ n) y - (a : Space → Space) y‖ ^ 2 = ‖x (φ n) - a‖ ^ 2 := fun n =>
    integral_sq_dist (x (φ n)) a _ _ (hx (φ n)) (Filter.EventuallyEq.refl _ _)
  simp_rw [h1]
  have h2 : Tendsto (fun n => ‖x (φ n) - a‖) atTop (nhds 0) :=
    (tendsto_iff_norm_sub_tendsto_zero.mp hlim)
  simpa using h2.pow 2




private theorem entrySq_nonneg (G : Space →L[ℝ] Space) : 0 ≤ entrySq G :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

private theorem apply_sq_le (G : Space →L[ℝ] Space) (w : Space) : ‖G w‖ ^ 2 ≤ entrySq G * ‖w‖ ^ 2 := by
  have hw : w = ∑ i : Fin 3, w i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
    simp [EuclideanSpace.basisFun_apply, unitVector]
  have h1 : ‖G w‖ ≤ ∑ i : Fin 3, ‖w i‖ * ‖G (unitVector i)‖ := by
    calc ‖G w‖ = ‖∑ i : Fin 3, w i • G (unitVector i)‖ := by
          conv_lhs => rw [hw]
          rw [map_sum]
          simp only [map_smul]
      _ ≤ ∑ i : Fin 3, ‖w i • G (unitVector i)‖ := norm_sum_le _ _
      _ = ∑ i : Fin 3, ‖w i‖ * ‖G (unitVector i)‖ := by simp only [norm_smul]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => ‖w i‖) (fun i => ‖G (unitVector i)‖)
  have h3 : ‖G w‖ ^ 2 ≤ (∑ i : Fin 3, ‖w i‖ * ‖G (unitVector i)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  rw [EuclideanSpace.norm_sq_eq w, entrySq, mul_comm]
  exact h3.trans h2

private theorem sym_sq_le (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (C : ℝ)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖DW y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (y : Space) (hy : y ≠ 0) :
    ‖symProduct W DW v G y‖ ^ 2 ≤ C ^ 2 * ((1 + ‖y‖)⁻¹) ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2) := by
  set t := ‖y‖ with ht
  have htpos : 0 < t := norm_pos_iff.mpr hy
  set s := (1 + t)⁻¹ with hs
  have hspos : 0 < s := by positivity
  have hW : ‖W y‖ ≤ C * s := by
    have := (hb y).1
    rwa [Real.rpow_neg_one] at this
  have hD : ‖DW y‖ ≤ C * s ^ 2 := by
    have := (hb y).2
    rwa [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow] at this
  have hC : 0 ≤ C * s := (norm_nonneg _).trans hW
  have hst : s * t ≤ 1 := by
    rw [hs, inv_mul_le_iff₀ (by positivity)]
    linarith
  set a := G y (W y)
  set b := DW y (v y)
  have ha : ‖a‖ ^ 2 ≤ entrySq (G y) * (C * s) ^ 2 :=
    (apply_sq_le _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hW 2)
      (entrySq_nonneg _))
  have hb1 : ‖b‖ ≤ C * s ^ 2 * ‖v y‖ :=
    ((DW y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hb2 : ‖b‖ ^ 2 ≤ (C * s ^ 2 * ‖v y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb1 2
  have hb3 : (C * s ^ 2 * ‖v y‖) ^ 2 ≤ C ^ 2 * s ^ 2 * (‖v y‖ ^ 2 / t ^ 2) := by
    have e : (C * s ^ 2 * ‖v y‖) ^ 2 = C ^ 2 * s ^ 2 * (‖v y‖ ^ 2 / t ^ 2) * (s * t) ^ 2 := by
      field_simp
    rw [e]
    have h0 : 0 ≤ C ^ 2 * s ^ 2 * (‖v y‖ ^ 2 / t ^ 2) := by positivity
    have h1 : (s * t) ^ 2 ≤ 1 := by
      have := mul_pos hspos htpos
      nlinarith
    nlinarith
  have hF : ‖symProduct W DW v G y‖ ≤ (1 / 2) * (‖a‖ + ‖b‖) := by
    unfold symProduct
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
  have hF2 : ‖symProduct W DW v G y‖ ^ 2 ≤ ((1 / 2) * (‖a‖ + ‖b‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hab : ((1 / 2) * (‖a‖ + ‖b‖)) ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  have e2 : C ^ 2 * s ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / t ^ 2) =
      entrySq (G y) * (C * s) ^ 2 + C ^ 2 * s ^ 2 * (‖v y‖ ^ 2 / t ^ 2) := by ring
  rw [e2]
  linarith

private theorem net_of_split (F : ℕ → Space → Space) (hF : ∀ n, MemLp (F n) 2 volume)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n, ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖F n y‖ ^ 2 < ε)
    (hloc : ∀ R ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S,
      ∫ y in Metric.ball (0 : Space) R, ‖F n y - F k y‖ ^ 2 < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, ∫ y, ‖F n y - F k y‖ ^ 2 < ε := by
  intro ε hε
  obtain ⟨R, hR⟩ := htail (ε / 8) (by positivity)
  obtain ⟨S, hS⟩ := hloc R (ε / 2) (by positivity)
  refine ⟨S, fun n => ?_⟩
  obtain ⟨k, hk, hlt⟩ := hS n
  refine ⟨k, hk, ?_⟩
  have hint : ∀ f : Space → Space, MemLp f 2 volume → Integrable (fun y => ‖f y‖ ^ 2) :=
    fun f hf => (memLp_two_iff_integrable_sq_norm hf.1).mp hf
  have hd : Integrable (fun y => ‖F n y - F k y‖ ^ 2) := hint _ ((hF n).sub (hF k))
  rw [← integral_add_compl (s := Metric.ball (0 : Space) R) measurableSet_ball hd]
  have i1 := (hint _ (hF n)).const_mul 2
  have i2 := (hint _ (hF k)).const_mul 2
  have hc : ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖F n y - F k y‖ ^ 2 ≤
      ∫ y in (Metric.ball (0 : Space) R)ᶜ, (2 * ‖F n y‖ ^ 2 + 2 * ‖F k y‖ ^ 2) := by
    apply setIntegral_mono hd.integrableOn (i1.add i2).integrableOn
    intro y
    show ‖F n y - F k y‖ ^ 2 ≤ 2 * ‖F n y‖ ^ 2 + 2 * ‖F k y‖ ^ 2
    have h1 := norm_sub_le (F n y) (F k y)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [sq_nonneg (‖F n y‖ - ‖F k y‖)]
  rw [integral_add i1.integrableOn i2.integrableOn, integral_const_mul, integral_const_mul] at hc
  have h3 := hR n
  have h4 := hR k
  linarith


private theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp

private theorem field_bounds (h1 : InverseSquareBoundStatement) (W : Space → Space) (C : ℝ) (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hf : IsSecondOrderField m v G H) :
    MemLp (symProduct W (fun z => fderiv ℝ W z) v G) 2 volume ∧
      ∀ R : ℝ, 0 < R → ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2
        ≤ C ^ 2 / R ^ 2 * (5 * ∫ y, entrySq (G y)) := by
  obtain ⟨hi, hle⟩ := h1 v G hf.measurable_velocity hf.velocity_six hf.gradient_two hf.weak_gradient
  have hg := hf.gradient_two
  have hX : Integrable (fun y => entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2) := hg.add hi
  have hWc : Continuous W := hW.continuous
  have hDc : Continuous (fun z => fderiv ℝ W z) := hW.continuous_fderiv (by norm_num)
  have hm : AEStronglyMeasurable (symProduct W (fun z => fderiv ℝ W z) v G) volume := by
    show AEStronglyMeasurable (fun y => (1 / 2 : ℝ) • (G y (W y) + fderiv ℝ W y (v y))) volume
    refine AEStronglyMeasurable.const_smul (AEStronglyMeasurable.add (f := fun y => G y (W y))
      (g := fun y => fderiv ℝ W y (v y)) ?_ ?_) (1 / 2 : ℝ)
    · exact (ContinuousLinearMap.apply ℝ Space).aestronglyMeasurable_comp₂ hWc.aestronglyMeasurable
        hf.measurable_gradient
    · exact (ContinuousLinearMap.apply ℝ Space).aestronglyMeasurable_comp₂ hf.measurable_velocity
        hDc.aestronglyMeasurable
  have hpt := sym_sq_le W (fun z => fderiv ℝ W z) C hb v G
  have hF2 : Integrable (fun y => ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2) := by
    refine (hX.const_mul (C ^ 2)).mono' (hm.norm.pow 2) ?_
    filter_upwards [ae_ne_zero] with y hy
    rw [Real.norm_of_nonneg (by positivity)]
    refine (hpt y hy).trans ?_
    have h0 : 0 ≤ entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2 := by
      have := entrySq_nonneg (G y)
      positivity
    have hs : ((1 + ‖y‖)⁻¹) ^ 2 ≤ 1 := by
      have : (1 + ‖y‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg y])
      have h' : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_right hs h0
    nlinarith [sq_nonneg C]
  refine ⟨(memLp_two_iff_integrable_sq_norm hm).mpr hF2, fun R hR => ?_⟩
  have hXR := hX.const_mul (C ^ 2 / R ^ 2)
  calc ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2
      ≤ ∫ y in (Metric.ball (0 : Space) R)ᶜ, C ^ 2 / R ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2) := by
        refine setIntegral_mono_on hF2.integrableOn hXR.integrableOn measurableSet_ball.compl ?_
        intro y hy
        have hRy : R ≤ ‖y‖ := by
          simpa [Metric.mem_ball, dist_zero_right] using hy
        have hy0 : y ≠ 0 := by
          intro h
          rw [h, norm_zero] at hRy
          linarith
        refine (hpt y hy0).trans ?_
        have h0 : 0 ≤ entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2 := by
          have := entrySq_nonneg (G y)
          positivity
        have hs : ((1 + ‖y‖)⁻¹) ^ 2 ≤ 1 / R ^ 2 := by
          rw [one_div, ← inv_pow]
          have : (1 + ‖y‖)⁻¹ ≤ R⁻¹ := inv_anti₀ hR (by linarith)
          exact pow_le_pow_left₀ (by positivity) this 2
        have := mul_le_mul_of_nonneg_right hs h0
        have e : C ^ 2 / R ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2) =
            C ^ 2 * (1 / R ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2)) := by ring
        rw [e, mul_assoc]
        exact mul_le_mul_of_nonneg_left this (sq_nonneg C)
    _ ≤ ∫ y, C ^ 2 / R ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2) := by
        refine setIntegral_le_integral hXR (ae_of_all _ fun y => ?_)
        have := entrySq_nonneg (G y)
        show 0 ≤ C ^ 2 / R ^ 2 * (entrySq (G y) + ‖v y‖ ^ 2 / ‖y‖ ^ 2)
        positivity
    _ = C ^ 2 / R ^ 2 * ((∫ y, entrySq (G y)) + ∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2) := by
        rw [integral_const_mul, integral_add hg hi]
    _ ≤ C ^ 2 / R ^ 2 * (5 * ∫ y, entrySq (G y)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

private theorem tail_of_bound (F : ℕ → Space → Space) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ R : ℝ, 0 < R → ∀ n, ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖F n y‖ ^ 2 ≤ K / R ^ 2) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ n, ∫ y in (Metric.ball (0 : Space) R)ᶜ, ‖F n y‖ ^ 2 < ε := by
  intro ε hε
  refine ⟨K / ε + 1, fun n => ?_⟩
  have hR1 : 1 ≤ K / ε + 1 := by
    have : 0 ≤ K / ε := by positivity
    linarith
  refine (hb _ (by linarith) n).trans_lt ?_
  have h2 : K / (K / ε + 1) ^ 2 ≤ K / (K / ε + 1) := by
    apply div_le_div_of_nonneg_left hK (by linarith)
    nlinarith
  refine h2.trans_lt ?_
  rw [div_lt_iff₀ (by linarith)]
  have : ε * (K / ε) = K := by field_simp
  nlinarith



private theorem diff_apply (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (v u : Space → Space)
    (G K : Space → (Space →L[ℝ] Space)) (y : Space) :
    symProduct W DW v G y - symProduct W DW u K y =
      symProduct W DW (fun z => v z - u z) (fun z => G z - K z) y := by
  simp only [symProduct, ContinuousLinearMap.sub_apply, map_sub, ← smul_sub]
  congr 1
  abel

private theorem diff_sq_le (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (C : ℝ)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖DW y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (u : Space → Space) (K : Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖symProduct W DW u K y‖ ^ 2 ≤ C ^ 2 * (‖u y‖ ^ 2 + entrySq (K y)) := by
  have hs1 : (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
  have hs2 : (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
  have hp1 : 0 ≤ (1 + ‖y‖) ^ (-(1 : ℝ)) := by positivity
  have hp2 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
  have hC : 0 ≤ C := by
    have h := (norm_nonneg _).trans (hb 0).1
    simpa using h
  have hW : ‖W y‖ ≤ C := (hb y).1.trans (by nlinarith)
  have hD : ‖DW y‖ ≤ C := (hb y).2.trans (by nlinarith)
  set a := K y (W y)
  set b := DW y (u y)
  have ha : ‖a‖ ^ 2 ≤ entrySq (K y) * C ^ 2 :=
    (apply_sq_le _ _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hW 2)
      (entrySq_nonneg _))
  have hb1 : ‖b‖ ≤ C * ‖u y‖ :=
    ((DW y).le_opNorm _).trans (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have hb2 : ‖b‖ ^ 2 ≤ (C * ‖u y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb1 2
  have hF : ‖symProduct W DW u K y‖ ≤ (1 / 2) * (‖a‖ + ‖b‖) := by
    unfold symProduct
    rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
    exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
  have hF2 : ‖symProduct W DW u K y‖ ^ 2 ≤ ((1 / 2) * (‖a‖ + ‖b‖)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hF 2
  have hab : ((1 / 2) * (‖a‖ + ‖b‖)) ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  nlinarith

private theorem entrySq_continuous : Continuous entrySq := by
  unfold entrySq
  fun_prop

private theorem entrySq_sub_le (A K : Space →L[ℝ] Space) : entrySq (A - K) ≤ 2 * entrySq A + 2 * entrySq K := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.sub_apply]
  have h1 := norm_sub_le (A (unitVector i)) (K (unitVector i))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖A (unitVector i)‖ - ‖K (unitVector i)‖)]

private theorem ball_integrable {m : ℕ} {v u : Space → Space} {G K : Space → (Space →L[ℝ] Space)}
    {H H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hf : IsSecondOrderField m v G H) (hg : IsSecondOrderField m u K H') (R : ℝ) :
    IntegrableOn (fun y => ‖v y - u y‖ ^ 2 + entrySq (G y - K y)) (Metric.ball (0 : Space) R) := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) R)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have h6 : MemLp (fun y => v y - u y) 6 (volume.restrict (Metric.ball (0 : Space) R)) :=
    (hf.velocity_six.sub hg.velocity_six).restrict _
  have h2 : MemLp (fun y => v y - u y) 2 (volume.restrict (Metric.ball (0 : Space) R)) :=
    h6.mono_exponent (by norm_num)
  have i1 : IntegrableOn (fun y => ‖v y - u y‖ ^ 2) (Metric.ball (0 : Space) R) :=
    (memLp_two_iff_integrable_sq_norm h2.1).mp h2
  have hm : AEStronglyMeasurable (fun y => entrySq (G y - K y)) volume :=
    entrySq_continuous.comp_aestronglyMeasurable (hf.measurable_gradient.sub hg.measurable_gradient)
  have i2 : Integrable (fun y => entrySq (G y - K y)) := by
    refine ((hf.gradient_two.const_mul 2).add (hg.gradient_two.const_mul 2)).mono' hm
      (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (entrySq_nonneg _)]
    exact entrySq_sub_le _ _
  exact i1.add i2.integrableOn


private theorem net_add (d e : ℕ → ℕ → ℝ) (hd : ∀ n k j, d n k ≤ 2 * d n j + 2 * d j k) (hds : ∀ n k, d n k = d k n)
    (he : ∀ n k j, e n k ≤ 2 * e n j + 2 * e j k) (hes : ∀ n k, e n k = e k n)
    (hnd : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, d n k < ε)
    (hne : ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, e n k < ε) :
    ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S, d n k + e n k < ε := by
  classical
  intro ε hε
  obtain ⟨S₁, h₁⟩ := hnd (ε / 8) (by positivity)
  obtain ⟨S₂, h₂⟩ := hne (ε / 8) (by positivity)
  let P : ℕ × ℕ → Prop := fun p => ∃ n, d n p.1 < ε / 8 ∧ e n p.2 < ε / 8
  let pick : ℕ × ℕ → ℕ := fun p => if h : P p then h.choose else 0
  refine ⟨(S₁ ×ˢ S₂).image pick, fun n => ?_⟩
  obtain ⟨a, ha, hna⟩ := h₁ n
  obtain ⟨b, hb, hnb⟩ := h₂ n
  have hP : P (a, b) := ⟨n, hna, hnb⟩
  refine ⟨pick (a, b), Finset.mem_image_of_mem _ (Finset.mem_product.mpr ⟨ha, hb⟩), ?_⟩
  have hs := hP.choose_spec
  have hpk : pick (a, b) = hP.choose := dif_pos hP
  rw [hpk]
  have t1 := hd n hP.choose a
  have t2 := he n hP.choose b
  rw [hds a hP.choose] at t1
  rw [hes b hP.choose] at t2
  linarith [hs.1, hs.2]

private theorem sq_tri {μ : Measure Space} (f : ℕ → Space → Space) (hf : ∀ n, MemLp (f n) 2 μ) (n k j : ℕ) :
    ∫ y, ‖f n y - f k y‖ ^ 2 ∂μ ≤ 2 * (∫ y, ‖f n y - f j y‖ ^ 2 ∂μ) + 2 * (∫ y, ‖f j y - f k y‖ ^ 2 ∂μ) := by
  have hi : ∀ a b, Integrable (fun y => ‖f a y - f b y‖ ^ 2) μ := fun a b =>
    (memLp_two_iff_integrable_sq_norm ((hf a).sub (hf b)).1).mp ((hf a).sub (hf b))
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi n j).const_mul 2) ((hi j k).const_mul 2)]
  refine integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _)
    (((hi n j).const_mul 2).add ((hi j k).const_mul 2)) (ae_of_all _ fun y => ?_)
  show ‖f n y - f k y‖ ^ 2 ≤ 2 * ‖f n y - f j y‖ ^ 2 + 2 * ‖f j y - f k y‖ ^ 2
  have e : f n y - f k y = (f n y - f j y) + (f j y - f k y) := by abel
  have h1 := norm_add_le (f n y - f j y) (f j y - f k y)
  rw [← e] at h1
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  nlinarith [sq_nonneg (‖f n y - f j y‖ - ‖f j y - f k y‖)]

private theorem sq_symm {μ : Measure Space} (f : ℕ → Space → Space) (n k : ℕ) :
    ∫ y, ‖f n y - f k y‖ ^ 2 ∂μ = ∫ y, ‖f k y - f n y‖ ^ 2 ∂μ := by
  congr 1
  funext y
  rw [norm_sub_rev]

private theorem entry_le (G : Space →L[ℝ] Space) (i : Fin 3) : ‖G (unitVector i)‖ ^ 2 ≤ entrySq G := by
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G (unitVector i)‖ ^ 2) (fun _ _ => sq_nonneg _)
    (Finset.mem_univ i)

private theorem col_entrySq_le (H : Space →L[ℝ] Space →L[ℝ] Space) (i : Fin 3) :
    entrySq (H.flip (unitVector i)) ≤ fullSecondSq H := by
  unfold entrySq fullSecondSq
  simp only [ContinuousLinearMap.flip_apply, Fin.sum_univ_three]
  fin_cases i <;> simp <;> nlinarith [sq_nonneg ‖H (unitVector 0) (unitVector 0)‖, sq_nonneg ‖H (unitVector 0) (unitVector 1)‖,
    sq_nonneg ‖H (unitVector 0) (unitVector 2)‖, sq_nonneg ‖H (unitVector 1) (unitVector 0)‖,
    sq_nonneg ‖H (unitVector 1) (unitVector 1)‖, sq_nonneg ‖H (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖H (unitVector 2) (unitVector 0)‖, sq_nonneg ‖H (unitVector 2) (unitVector 1)‖,
    sq_nonneg ‖H (unitVector 2) (unitVector 2)‖]

private theorem flip_cont (w : Space) : Continuous (fun H : Space →L[ℝ] Space →L[ℝ] Space => H.flip w) :=
  (ContinuousLinearMap.flipₗᵢ ℝ Space Space Space).continuous.clm_apply continuous_const

private theorem apply_cont (w : Space) : Continuous (fun G : Space →L[ℝ] Space => G w) := by
  fun_prop


end ProductCompactInternal

namespace ShiftInternal

private theorem period_const (r : ℝ) (f : Space → ℝ) :
    periodBallLIntegral r (fun _ y => f y) =
      ∫⁻ y in Metric.closedBall (0 : Space) r, ENNReal.ofReal (f y) := by
  unfold periodBallLIntegral
  rw [setLIntegral_const, Real.volume_Icc]
  simp

private theorem separated (d : ℕ → ℕ → ℝ) (ε : ℝ)
    (hbad : ∀ S : Finset ℕ, ∃ n, ∀ k ∈ S, ε ≤ d n k) :
    ∃ s : ℕ → ℕ, ∀ i j, i < j → ε ≤ d (s j) (s i) := by
  classical
  choose f hf using hbad
  let T : ℕ → Finset ℕ := fun j => Nat.rec ∅ (fun _ t => insert (f t) t) j
  have hT : ∀ j, T (j + 1) = insert (f (T j)) (T j) := fun j => rfl
  have hmono : ∀ i j, i ≤ j → T i ⊆ T j := by
    intro i j hij
    induction hij with
    | refl => exact le_rfl
    | step _ ih => exact ih.trans (by rw [hT]; exact Finset.subset_insert _ _)
  refine ⟨fun j => f (T j), fun i j hij => hf (T j) _ ?_⟩
  have : f (T i) ∈ T (i + 1) := by rw [hT]; exact Finset.mem_insert_self _ _
  exact hmono (i + 1) j hij this

end ShiftInternal


open ShiftInternal in
theorem ballCompact_of (hsh : BallShiftStatement) : BallCompactStatement := by
  classical
  intro u K R A hum hKm hw hui hKi hA ε hε
  rcases le_or_gt R 0 with hR | hR
  · refine ⟨{0}, fun n => ⟨0, Finset.mem_singleton_self 0, ?_⟩⟩
    rw [Metric.ball_eq_empty.mpr hR]
    simpa using hε
  have hK0 : ∀ n, 0 ≤ ∫ y, entrySq (K n y) := fun n => integral_nonneg fun y =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hU0 : ∀ n, 0 ≤ ∫ y in Metric.ball (0 : Space) (R + 2), ‖u n y‖ ^ 2 := fun n =>
    setIntegral_nonneg measurableSet_ball fun y _ => sq_nonneg _
  have hA0 : 0 ≤ A := by linarith [hA 0, hK0 0, hU0 0]
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs⟩ := separated (fun n k => ∫ y in Metric.ball (0 : Space) R, ‖u n y - u k y‖ ^ 2) ε hcon
  have hsub : Metric.closedBall (0 : Space) (R + 1) ⊆ Metric.ball (0 : Space) (R + 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub0 : Metric.closedBall (0 : Space) R ⊆ Metric.ball (0 : Space) (R + 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hrate : Tendsto (fun t : ℝ => Real.sqrt A * t) (𝓝[>] 0) (𝓝 0) := by
    have hc : Continuous (fun t : ℝ => Real.sqrt A * t) := continuous_const.mul continuous_id
    have := hc.tendsto 0
    simp only [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  obtain ⟨φ, hφ, hcau⟩ := Cert.translationCriterionHolds_proof (fun m (_ : ℝ) y => u (s m) y) R A
    (fun t => Real.sqrt A * t) hR hrate (fun m => (hum (s m)).comp_snd) (fun m σ y => rfl)
    (fun m => by
      rw [period_const (R + 1) (fun y => ‖u (s m) y‖ ^ 2)]
      calc ∫⁻ y in Metric.closedBall (0 : Space) (R + 1), ENNReal.ofReal (‖u (s m) y‖ ^ 2)
          ≤ ∫⁻ y in Metric.ball (0 : Space) (R + 2), ENNReal.ofReal (‖u (s m) y‖ ^ 2) :=
            lintegral_mono_set hsub
        _ = ENNReal.ofReal (∫ y in Metric.ball (0 : Space) (R + 2), ‖u (s m) y‖ ^ 2) :=
            (ofReal_integral_eq_lintegral_ofReal (hui (s m)) (ae_of_all _ fun y => sq_nonneg _)).symm
        _ ≤ ENNReal.ofReal A := ENNReal.ofReal_le_ofReal (by linarith [hA (s m), hK0 (s m)]))
    (fun m δ hδ => by
      have hz : (fun (σ : ℝ) (y : Space) => ‖u (s m) y - u (s m) y‖ ^ 2) = fun _ _ => 0 := by
        funext σ y
        simp
      show Real.sqrt (periodBallLIntegral R (fun σ y => ‖u (s m) y - u (s m) y‖ ^ 2)).toReal ≤ _
      rw [hz]
      simp only [periodBallLIntegral, ENNReal.ofReal_zero, lintegral_zero, ENNReal.toReal_zero,
        Real.sqrt_zero]
      exact mul_nonneg (Real.sqrt_nonneg _) hδ.1.le)
    (fun m h _ hh => by
      show Real.sqrt (periodBallLIntegral R (fun σ y => ‖u (s m) (y + h) - u (s m) y‖ ^ 2)).toReal ≤ _
      rw [period_const R (fun y => ‖u (s m) (y + h) - u (s m) y‖ ^ 2)]
      have hb := hsh (u (s m)) (K (s m)) R (hum _) (hw _) (hui _) (hKi _) h hh
      have h1 := ENNReal.toReal_le_of_le_ofReal (by have := hK0 (s m); positivity) hb
      have h2 : ‖h‖ ^ 2 * ∫ y, entrySq (K (s m) y) ≤ ‖h‖ ^ 2 * A :=
        mul_le_mul_of_nonneg_left (by linarith [hA (s m), hU0 (s m)]) (sq_nonneg _)
      calc _ ≤ Real.sqrt (‖h‖ ^ 2 * A) := Real.sqrt_le_sqrt (h1.trans h2)
        _ = Real.sqrt A * ‖h‖ := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _), mul_comm])
  obtain ⟨N, hN⟩ := hcau (Real.sqrt ε) (Real.sqrt_pos.mpr hε)
  have h1 := hN (N + 1) (by omega) N le_rfl
  have h2 := hs (φ N) (φ (N + 1)) (hφ (Nat.lt_succ_self N))
  set a := s (φ (N + 1))
  set b := s (φ N)
  change Real.sqrt (periodBallLIntegral R (fun σ y => ‖u a y - u b y‖ ^ 2)).toReal < Real.sqrt ε at h1
  rw [period_const R (fun y => ‖u a y - u b y‖ ^ 2)] at h1
  have hg : IntegrableOn (fun y => ‖u a y - u b y‖ ^ 2) (Metric.ball (0 : Space) (R + 2)) := by
    refine (((hui a).const_mul 2).add ((hui b).const_mul 2)).mono'
      (((hum a).sub (hum b)).norm.pow 2).restrict (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    show ‖u a y - u b y‖ ^ 2 ≤ 2 * ‖u a y‖ ^ 2 + 2 * ‖u b y‖ ^ 2
    have t1 := norm_sub_le (u a y) (u b y)
    have t2 := pow_le_pow_left₀ (norm_nonneg _) t1 2
    nlinarith [sq_nonneg (‖u a y‖ - ‖u b y‖)]
  have hgc : IntegrableOn (fun y => ‖u a y - u b y‖ ^ 2) (Metric.closedBall (0 : Space) R) := hg.mono_set hsub0
  rw [← ofReal_integral_eq_lintegral_ofReal hgc (ae_of_all _ fun y => sq_nonneg _),
    ENNReal.toReal_ofReal (setIntegral_nonneg Metric.isClosed_closedBall.measurableSet fun y _ => sq_nonneg _)] at h1
  have h3 := (Real.sqrt_lt_sqrt_iff (setIntegral_nonneg Metric.isClosed_closedBall.measurableSet
    fun y _ => sq_nonneg _)).mp h1
  have h4 : ∫ y in Metric.ball (0 : Space) R, ‖u a y - u b y‖ ^ 2 ≤
      ∫ y in Metric.closedBall (0 : Space) R, ‖u a y - u b y‖ ^ 2 :=
    setIntegral_mono_set hgc (ae_of_all _ fun y => sq_nonneg _) Metric.ball_subset_closedBall.eventuallyLE
  linarith


open ProductCompactInternal in
theorem ballNet_of (h : BallCompactStatement) : BallNetStatement := by
  intro m v G H B hf hvi hB R ε hε
  have hH0 : ∀ n, 0 ≤ ∫ y, ‖v n y‖ ^ 2 / ‖y‖ ^ 2 := fun n => integral_nonneg fun y => by positivity
  have hG0 : ∀ n, 0 ≤ ∫ y, entrySq (G n y) := fun n => integral_nonneg fun y => entrySq_nonneg _
  have hF0 : ∀ n, 0 ≤ ∫ y, fullSecondSq (H n y) := fun n => integral_nonneg fun y =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have fin : ∀ r : ℝ, IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) r)) := fun r =>
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hv2 : ∀ (r : ℝ) n, MemLp (v n) 2 (volume.restrict (Metric.ball (0 : Space) r)) := fun r n => by
    have := fin r
    exact ((hf n).velocity_six.restrict _).mono_exponent (by norm_num)
  let c : Fin 3 → ℕ → Space → Space := fun i n y => G n y (unitVector i)
  let Kc : Fin 3 → ℕ → Space → (Space →L[ℝ] Space) := fun i n y => (H n y).flip (unitVector i)
  have hcm : ∀ i n, AEStronglyMeasurable (c i n) volume := fun i n =>
    (apply_cont _).comp_aestronglyMeasurable (hf n).measurable_gradient
  have hci : ∀ i n, Integrable (fun y => ‖c i n y‖ ^ 2) := fun i n =>
    (hf n).gradient_two.mono' ((hcm i n).norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact entry_le _ _)
  have hc2 : ∀ i n, MemLp (c i n) 2 volume := fun i n =>
    (memLp_two_iff_integrable_sq_norm (hcm i n)).mpr (hci i n)
  have hKm : ∀ i n, AEStronglyMeasurable (Kc i n) volume := fun i n =>
    (flip_cont _).comp_aestronglyMeasurable (hf n).measurable_second
  have hKi : ∀ i n, Integrable (fun y => entrySq (Kc i n y)) := fun i n =>
    (hf n).second_two.mono' (entrySq_continuous.comp_aestronglyMeasurable (hKm i n)) (ae_of_all _ fun y => by
      rw [Real.norm_of_nonneg (entrySq_nonneg _)]
      exact col_entrySq_le _ _)
  have hKw : ∀ i n, IsWeakGradientOf (c i n) (Kc i n) := fun i n φ hφ j => by
    have := (hf n).weak_second φ hφ i j
    simpa [c, Kc, ContinuousLinearMap.flip_apply] using this
  have hGB : ∀ n, ∫ y, entrySq (G n y) ≤ B := fun n => by linarith [hB n, hH0 n, hF0 n]
  have hHB : ∀ n, ∫ y, ‖v n y‖ ^ 2 / ‖y‖ ^ 2 ≤ B := fun n => by linarith [hB n, hG0 n, hF0 n]
  have hSB : ∀ n, ∫ y, fullSecondSq (H n y) ≤ B := fun n => by linarith [hB n, hG0 n, hH0 n]
  have hvball : ∀ n, ∫ y in Metric.ball (0 : Space) (R + 2), ‖v n y‖ ^ 2 ≤
      (R + 2) ^ 2 * ∫ y, ‖v n y‖ ^ 2 / ‖y‖ ^ 2 := by
    intro n
    have hi : IntegrableOn (fun y => ‖v n y‖ ^ 2) (Metric.ball (0 : Space) (R + 2)) :=
      (memLp_two_iff_integrable_sq_norm (hv2 (R + 2) n).1).mp (hv2 (R + 2) n)
    rw [← integral_const_mul]
    calc ∫ y in Metric.ball (0 : Space) (R + 2), ‖v n y‖ ^ 2
        ≤ ∫ y in Metric.ball (0 : Space) (R + 2), (R + 2) ^ 2 * (‖v n y‖ ^ 2 / ‖y‖ ^ 2) := by
          refine integral_mono_ae hi ((hvi n).const_mul _).integrableOn ?_
          filter_upwards [ae_restrict_of_ae ae_ne_zero, ae_restrict_mem measurableSet_ball] with y hy hyb
          have hyb' : ‖y‖ < R + 2 := by simpa [Metric.mem_ball, dist_zero_right] using hyb
          have hyp : 0 < ‖y‖ := norm_pos_iff.mpr hy
          have hsq : ‖y‖ ^ 2 ≤ (R + 2) ^ 2 := pow_le_pow_left₀ hyp.le hyb'.le 2
          calc ‖v n y‖ ^ 2 = ‖y‖ ^ 2 * (‖v n y‖ ^ 2 / ‖y‖ ^ 2) := by field_simp
            _ ≤ (R + 2) ^ 2 * (‖v n y‖ ^ 2 / ‖y‖ ^ 2) :=
              mul_le_mul_of_nonneg_right hsq (by positivity)
      _ ≤ ∫ y, (R + 2) ^ 2 * (‖v n y‖ ^ 2 / ‖y‖ ^ 2) :=
          setIntegral_le_integral ((hvi n).const_mul _) (ae_of_all _ fun y => by positivity)
  have netv := h v G R (((R + 2) ^ 2 + 1) * B) (fun n => (hf n).measurable_velocity)
    (fun n => (hf n).measurable_gradient) (fun n => (hf n).weak_gradient)
    (fun n => (memLp_two_iff_integrable_sq_norm (hv2 (R + 2) n).1).mp (hv2 (R + 2) n))
    (fun n => (hf n).gradient_two) (fun n => by
      have := hvball n
      have := mul_le_mul_of_nonneg_left (hHB n) (sq_nonneg (R + 2))
      nlinarith [hGB n])
  have netc : ∀ i, ∀ ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S,
      ∫ y in Metric.ball (0 : Space) R, ‖c i n y - c i k y‖ ^ 2 < ε := fun i =>
    h (c i) (Kc i) R (2 * B) (hcm i) (hKm i) (hKw i) (fun n => (hci i n).integrableOn) (hKi i) (fun n => by
      have a1 : ∫ y in Metric.ball (0 : Space) (R + 2), ‖c i n y‖ ^ 2 ≤ ∫ y, ‖c i n y‖ ^ 2 :=
        setIntegral_le_integral (hci i n) (ae_of_all _ fun y => sq_nonneg _)
      have a2 : ∫ y, ‖c i n y‖ ^ 2 ≤ ∫ y, entrySq (G n y) :=
        integral_mono (hci i n) (hf n).gradient_two fun y => entry_le _ _
      have a3 : ∫ y, entrySq (Kc i n y) ≤ ∫ y, fullSecondSq (H n y) :=
        integral_mono (hKi i n) (hf n).second_two fun y => col_entrySq_le _ _
      linarith [hGB n, hSB n])
  have hcb : ∀ i n, MemLp (c i n) 2 (volume.restrict (Metric.ball (0 : Space) R)) := fun i n =>
    (hc2 i n).restrict _
  have tv := sq_tri (μ := volume.restrict (Metric.ball (0 : Space) R)) v (hv2 R)
  have tc := fun i => sq_tri (μ := volume.restrict (Metric.ball (0 : Space) R)) (c i) (hcb i)
  have sv := sq_symm (μ := volume.restrict (Metric.ball (0 : Space) R)) v
  have scs := fun i => sq_symm (μ := volume.restrict (Metric.ball (0 : Space) R)) (c i)
  have N1 := net_add _ _ tv sv (tc 0) (scs 0) netv (netc 0)
  have N2 := net_add _ _ (tc 1) (scs 1) (tc 2) (scs 2) (netc 1) (netc 2)
  have N := net_add _ _ (fun n k j => by linarith [tv n k j, tc 0 n k j])
    (fun n k => by rw [sv n k, scs 0 n k]) (fun n k j => by linarith [tc 1 n k j, tc 2 n k j])
    (fun n k => by rw [scs 1 n k, scs 2 n k]) N1 N2
  obtain ⟨S, hS⟩ := N ε hε
  refine ⟨S, fun n => ?_⟩
  obtain ⟨k, hk, hlt⟩ := hS n
  refine ⟨k, hk, ?_⟩
  have iv : Integrable (fun y => ‖v n y - v k y‖ ^ 2) (volume.restrict (Metric.ball (0 : Space) R)) :=
    (memLp_two_iff_integrable_sq_norm ((hv2 R n).sub (hv2 R k)).1).mp ((hv2 R n).sub (hv2 R k))
  have ic : ∀ i, Integrable (fun y => ‖c i n y - c i k y‖ ^ 2) (volume.restrict (Metric.ball (0 : Space) R)) :=
    fun i => (memLp_two_iff_integrable_sq_norm ((hcb i n).sub (hcb i k)).1).mp ((hcb i n).sub (hcb i k))
  have e : (fun y => ‖v n y - v k y‖ ^ 2 + entrySq (G n y - G k y)) = fun y =>
      ‖v n y - v k y‖ ^ 2 + ‖c 0 n y - c 0 k y‖ ^ 2 + (‖c 1 n y - c 1 k y‖ ^ 2 + ‖c 2 n y - c 2 k y‖ ^ 2) := by
    funext y
    simp only [entrySq, Fin.sum_univ_three, c, ContinuousLinearMap.sub_apply]
    ring
  have i01 : Integrable (fun y => ‖v n y - v k y‖ ^ 2 + ‖c 0 n y - c 0 k y‖ ^ 2)
      (volume.restrict (Metric.ball (0 : Space) R)) := iv.add (ic 0)
  have i12 : Integrable (fun y => ‖c 1 n y - c 1 k y‖ ^ 2 + ‖c 2 n y - c 2 k y‖ ^ 2)
      (volume.restrict (Metric.ball (0 : Space) R)) := (ic 1).add (ic 2)
  rw [e, integral_add i01 i12, integral_add iv (ic 0), integral_add (ic 1) (ic 2)]
  exact hlt

open ProductCompactInternal in
theorem profileProductCompact_of (h1 : InverseSquareBoundStatement) (h2 : SecondSymbolEnergyStatement)
    (h3 : BallShiftStatement) : ProfileProductCompactStatement := by
  intro m W C hW hb v G H B hf hB
  set F : ℕ → Space → Space := fun n => symProduct W (fun z => fderiv ℝ W z) (v n) (G n) with hFdef
  have hG0 : ∀ n, 0 ≤ ∫ y, entrySq (G n y) := fun n => integral_nonneg fun y => entrySq_nonneg _
  have hT0 : ∀ n, 0 ≤ ∫ y, ‖secondTrace (H n y)‖ ^ 2 := fun n => integral_nonneg fun y => sq_nonneg _
  have hB0 : 0 ≤ B := by linarith [hB 0, hG0 0, hT0 0]
  have hGB : ∀ n, ∫ y, entrySq (G n y) ≤ B := fun n => by linarith [hB n, hT0 n]
  have hFm : ∀ n, MemLp (F n) 2 volume := fun n => (field_bounds h1 W C hW hb (hf n)).1
  have htail := tail_of_bound F (C ^ 2 * (5 * B)) (by positivity) (fun R hR n => by
    refine ((field_bounds h1 W C hW hb (hf n)).2 R hR).trans ?_
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ (by positivity)
    exact mul_le_mul_of_nonneg_left (by linarith [hGB n]) (sq_nonneg C))
  have hE : ∀ n, (∫ y, ‖v n y‖ ^ 2 / ‖y‖ ^ 2) + (∫ y, entrySq (G n y)) + (∫ y, fullSecondSq (H n y)) ≤ 5 * B := by
    intro n
    have hh := (h1 (v n) (G n) (hf n).measurable_velocity (hf n).velocity_six (hf n).gradient_two
      (hf n).weak_gradient).2
    have hs := h2 m (v n) (G n) (H n) (hf n)
    rw [hs.2.2.1, ← hs.2.2.2]
    linarith [hB n, hG0 n, hT0 n]
  have hloc : ∀ R ε : ℝ, 0 < ε → ∃ S : Finset ℕ, ∀ n, ∃ k ∈ S,
      ∫ y in Metric.ball (0 : Space) R, ‖F n y - F k y‖ ^ 2 < ε := by
    intro R ε hε
    obtain ⟨S, hS⟩ := ballNet_of (ballCompact_of h3) m v G H (5 * B) hf (fun n => (h1 (v n) (G n) (hf n).measurable_velocity
      (hf n).velocity_six (hf n).gradient_two (hf n).weak_gradient).1) hE R (ε / (C ^ 2 + 1)) (by positivity)
    refine ⟨S, fun n => ?_⟩
    obtain ⟨k, hk, hlt⟩ := hS n
    refine ⟨k, hk, ?_⟩
    have hint := ball_integrable (hf n) (hf k) R
    set x := ∫ y in Metric.ball (0 : Space) R, (‖v n y - v k y‖ ^ 2 + entrySq (G n y - G k y)) with hx
    have hx0 : 0 ≤ x := setIntegral_nonneg measurableSet_ball fun y _ => by
      have := entrySq_nonneg (G n y - G k y)
      positivity
    have hle : ∫ y in Metric.ball (0 : Space) R, ‖F n y - F k y‖ ^ 2 ≤ C ^ 2 * x := by
      rw [hx, ← integral_const_mul]
      refine integral_mono_of_nonneg (ae_of_all _ fun y => sq_nonneg _) (hint.const_mul _)
        (ae_of_all _ fun y => ?_)
      show ‖F n y - F k y‖ ^ 2 ≤ C ^ 2 * (‖v n y - v k y‖ ^ 2 + entrySq (G n y - G k y))
      simp only [hFdef]
      rw [diff_apply]
      exact diff_sq_le W _ C hb _ _ y
    have h4 : x * (C ^ 2 + 1) < ε := (lt_div_iff₀ (by positivity)).mp hlt
    nlinarith
  exact subseq_of_net F hFm (net_of_split F hFm htail hloc)

end SteadyCert

end Breakdown

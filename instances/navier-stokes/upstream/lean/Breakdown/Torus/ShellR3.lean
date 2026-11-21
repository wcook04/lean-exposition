import Breakdown.Torus.StatementsShell
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.EmbedNegSsp

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.ShellR3

theorem cutLp_norm_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (b : ℝ) : ‖cutLp p b‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => ?_)
  rw [one_mul, Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (cutLp_apply p b f)]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _)

theorem restrictR3_apply (b : ℝ) (v : Freq.X) :
    restrictR3 b v = (fun j => cutLp 2 b (Freq.partialX j v), cutLp 6 b (Freq.velocity v)) := rfl

theorem partialX_norm_le (hP : Freq.PartialNormLe) (v : Freq.X) (j : Fin 3) :
    ‖Freq.partialX j v‖ ≤ ‖v‖ := by
  have h1 := hP v
  have h2 : ‖Freq.partialX j v‖ ^ 2 ≤ ∑ i : Fin 3, ‖Freq.partialX i v‖ ^ 2 :=
    Finset.single_le_sum (f := fun i => ‖Freq.partialX i v‖ ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  nlinarith [norm_nonneg (Freq.partialX j v), norm_nonneg v]

theorem toLpOrZero_congr {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f g : Space → F}
    (h : f =ᵐ[volume] g) : Freq.toLpOrZero p f = Freq.toLpOrZero p g := by
  unfold Freq.toLpOrZero
  by_cases hf : MemLp f p volume
  · have hg : MemLp g p volume := (memLp_congr_ae h).1 hf
    rw [dif_pos hf, dif_pos hg]
    exact MemLp.toLp_congr hf hg h
  · have hg : ¬ MemLp g p volume := fun hg => hf ((memLp_congr_ae h).2 hg)
    rw [dif_neg hf, dif_neg hg]

theorem toLpOrZero_norm_le {F : Type*} [NormedAddCommGroup F] (p : ℝ≥0∞) (f : Space → F) :
    ∀ᵐ y ∂volume, ‖(Freq.toLpOrZero p f : Space → F) y‖ ≤ ‖f y‖ := by
  unfold Freq.toLpOrZero
  by_cases hf : MemLp f p volume
  · rw [dif_pos hf]
    filter_upwards [hf.coeFn_toLp] with y hy
    rw [hy]
  · rw [dif_neg hf]
    filter_upwards [Lp.coeFn_zero F p volume] with y hy
    rw [hy]
    simp

theorem advectShell_restrict {φ : Space → Space} (hφ : IsTestField φ) {b : ℝ}
    (hb : tsupport φ ⊆ Metric.closedBall 0 b) (v : Freq.X) :
    advectShell φ hφ b (restrictR3 b v) = Freq.advectTest φ v := by
  show advectShellFun φ b (restrictR3 b v) = _
  unfold advectShellFun Freq.advectTest
  apply toLpOrZero_congr
  have h1 : ∀ᵐ y ∂volume, ∀ j : Fin 3, (cutLp 2 b (Freq.partialX j v) : Space → Space) y =
      (Metric.closedBall (0 : Space) b).indicator (Freq.partialX j v : Space → Space) y := by
    rw [ae_all_iff]
    intro j
    exact cutLp_apply 2 b _
  filter_upwards [h1, cutLp_apply 6 b (Freq.velocity v)] with y hy1 hy2
  rw [restrictR3_apply]
  dsimp only
  by_cases hy : y ∈ Metric.closedBall (0 : Space) b
  · rw [indicator_of_mem hy]
    simp only [hy1, hy2, indicator_of_mem hy]
  · rw [indicator_of_notMem hy]
    have hφy : φ y = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (hb h))
    have hd : fderiv ℝ φ y = 0 :=
      Function.notMem_support.mp (fun h => hy (hb (support_fderiv_subset ℝ h)))
    have hdy : ∀ j, Freq.partialField φ j y = 0 := by
      intro j
      simp [Freq.partialField, hd]
    simp [hφy, hdy]


theorem lpProdTriple_of_real {p q r : ℝ} (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p⁻¹ + q⁻¹ = r⁻¹) :
    ENNReal.HolderTriple (ENNReal.ofReal p) (ENNReal.ofReal q) (ENNReal.ofReal r) :=
  ⟨by rw [← ENNReal.ofReal_inv_of_pos hp, ← ENNReal.ofReal_inv_of_pos hq,
    ← ENNReal.ofReal_inv_of_pos hr, ← ENNReal.ofReal_add (by positivity) (by positivity), h]⟩

theorem lintegral_three_le {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : Space → E} {g : Space → F} {h : Space → G}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ * ‖g y‖ * ‖h y‖) ≤
      eLpNorm f 6 volume * eLpNorm g 2 volume *
        (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ) := by
  have t1 : ENNReal.HolderTriple 2 2 1 := by
    simpa using lpProdTriple_of_real (p := 2) (q := 2) (r := 1) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have t2 : ENNReal.HolderTriple 6 3 2 := by
    simpa using lpProdTriple_of_real (p := 6) (q := 3) (r := 2) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  have t3 : ENNReal.HolderTriple 4 12 3 := by
    simpa using lpProdTriple_of_real (p := 4) (q := 12) (r := 3) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num)
  set s : Space → ℝ := fun y => ‖h y‖ ^ (1 / 2 : ℝ) with hs_def
  have hs : AEStronglyMeasurable s volume :=
    (hh.norm.aemeasurable.pow_const (1 / 2 : ℝ)).aestronglyMeasurable
  have e4 : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 2 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      show (4 : ℝ≥0∞) = 2 * 2 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have e12 : (12 : ℝ≥0∞) * ENNReal.ofReal (1 / 2) = 6 := by
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat,
      show (12 : ℝ≥0∞) = 6 * 2 by norm_num, mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
  have hss : (fun y => ‖h y‖) = fun y => s y * s y := by
    funext y
    rw [hs_def, ← Real.rpow_add' (norm_nonneg _) (by norm_num)]
    norm_num
  have h3 : eLpNorm h 3 volume ≤ (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ) := by
    calc eLpNorm h 3 volume = eLpNorm (fun y => ‖h y‖) 3 volume := (eLpNorm_norm h).symm
      _ = eLpNorm (fun y => s y * s y) 3 volume := by rw [hss]
      _ ≤ (1 : NNReal) * eLpNorm s 4 volume * eLpNorm s 12 volume :=
          eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hs hs (fun a c : ℝ => a * c) 1
            (ae_of_all _ fun y => by simp [norm_mul]) (hpqr := t3)
      _ = (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ) := by
          rw [hs_def, eLpNorm_norm_rpow h (by norm_num), eLpNorm_norm_rpow h (by norm_num), e4, e12,
            ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
          simp
  have hk : AEStronglyMeasurable (fun y => ‖f y‖ * ‖h y‖) volume := hf.norm.mul hh.norm
  have h2 : eLpNorm (fun y => ‖f y‖ * ‖h y‖) 2 volume ≤ (1 : NNReal) * eLpNorm f 6 volume * eLpNorm h 3 volume :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hf hh (fun a c => ‖a‖ * ‖c‖) 1
      (ae_of_all _ fun y => by simp [norm_mul]) (hpqr := t2)
  have h1 : eLpNorm (fun y => ‖g y‖ * (‖f y‖ * ‖h y‖)) 1 volume ≤
      (1 : NNReal) * eLpNorm g 2 volume * eLpNorm (fun y => ‖f y‖ * ‖h y‖) 2 volume :=
    eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm hg hk (fun a c => ‖a‖ * c) 1
      (ae_of_all _ fun y => by simp [norm_mul]) (hpqr := t1)
  have e0 : ∫⁻ y, ENNReal.ofReal (‖f y‖ * ‖g y‖ * ‖h y‖) =
      eLpNorm (fun y => ‖g y‖ * (‖f y‖ * ‖h y‖)) 1 volume := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal (by positivity)]
    congr 1
    ring
  rw [e0]
  calc eLpNorm (fun y => ‖g y‖ * (‖f y‖ * ‖h y‖)) 1 volume
      ≤ (1 : NNReal) * eLpNorm g 2 volume * ((1 : NNReal) * eLpNorm f 6 volume * eLpNorm h 3 volume) :=
        h1.trans (by gcongr)
    _ ≤ (1 : NNReal) * eLpNorm g 2 volume * ((1 : NNReal) * eLpNorm f 6 volume *
          (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ)) := by gcongr
    _ = eLpNorm f 6 volume * eLpNorm g 2 volume *
          (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ) := by
        simp only [ENNReal.coe_one, one_mul]
        ring

theorem lintegral_three_le_real {E F G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedAddCommGroup G] {f : Space → E} {g : Space → F} {h : Space → G}
    (hf : AEStronglyMeasurable f volume) (hg : AEStronglyMeasurable g volume)
    (hh : AEStronglyMeasurable h volume) {a b c d : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hc0 : 0 ≤ c)
    (hd0 : 0 ≤ d) (ha : eLpNorm f 6 volume ≤ ENNReal.ofReal a)
    (hb : eLpNorm g 2 volume ≤ ENNReal.ofReal b) (hc : eLpNorm h 2 volume ≤ ENNReal.ofReal c)
    (hd : eLpNorm h 6 volume ≤ ENNReal.ofReal d) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ * ‖g y‖ * ‖h y‖) ≤ ENNReal.ofReal (a * b * Real.sqrt (c * d)) := by
  refine (lintegral_three_le hf hg hh).trans ?_
  calc eLpNorm f 6 volume * eLpNorm g 2 volume * (eLpNorm h 2 volume * eLpNorm h 6 volume) ^ (1 / 2 : ℝ)
      ≤ ENNReal.ofReal a * ENNReal.ofReal b * (ENNReal.ofReal c * ENNReal.ofReal d) ^ (1 / 2 : ℝ) := by
        gcongr
    _ = ENNReal.ofReal (a * b * Real.sqrt (c * d)) := by
        rw [← ENNReal.ofReal_mul hc0, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
          ← Real.sqrt_eq_rpow, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (by positivity)]

theorem eLpNorm_Lp {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} (u : Lp (α := Space) F p) :
    eLpNorm u p volume = ENNReal.ofReal ‖u‖ := by
  rw [Lp.norm_def, ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top u)]

theorem eLpNorm_Lp_le {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} (u : Lp (α := Space) F p)
    {r : ℝ} (h : ‖u‖ ≤ r) : eLpNorm u p volume ≤ ENNReal.ofReal r := by
  rw [eLpNorm_Lp]
  exact ENNReal.ofReal_le_ofReal h

theorem sqrt_phi_product {K τ s : ℝ} (hK : 0 ≤ K) (hτ : 0 < τ) (hs : 0 ≤ s) :
    Real.sqrt ((K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s)) = K * τ ^ (-(3 / 4 : ℝ)) * s := by
  have e : (τ ^ (-(3 / 4 : ℝ))) ^ 2 = τ ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 : ℝ)) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_natCast, ← Real.rpow_mul hτ.le]
    norm_num
  rw [show (K * τ ^ (-(1 / 2 : ℝ)) * s) * (K * τ ^ (-(1 : ℝ)) * s) = (K * τ ^ (-(3 / 4 : ℝ)) * s) ^ 2 by
    rw [mul_pow, mul_pow, e]; ring]
  exact Real.sqrt_sq (by positivity)

theorem pointwise_inner_le (a u p f : Space) (z₁ q g : Fin 3 → Space) (z₂ : Space) (hp : p = f)
    (hq : ∀ j, q j = g j)
    (ha : ‖a‖ ≤ ‖∑ j : Fin 3, (f j • z₁ j + z₂ j • g j)‖) :
    ENNReal.ofReal ‖inner ℝ a u‖ ≤
      ∑ j : Fin 3, (ENNReal.ofReal (‖p‖ * ‖z₁ j‖ * ‖u‖) + ENNReal.ofReal (‖z₂‖ * ‖q j‖ * ‖u‖)) := by
  subst hp
  have hq' : q = g := funext hq
  subst hq'
  have hreal : ‖inner ℝ a u‖ ≤ ∑ j : Fin 3, (‖p‖ * ‖z₁ j‖ * ‖u‖ + ‖z₂‖ * ‖q j‖ * ‖u‖) := by
    calc ‖inner ℝ a u‖ ≤ ‖a‖ * ‖u‖ := norm_inner_le_norm _ _
      _ ≤ (∑ j : Fin 3, (‖p‖ * ‖z₁ j‖ + ‖z₂‖ * ‖q j‖)) * ‖u‖ := by
          gcongr
          refine ha.trans ((norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
          refine (norm_add_le _ _).trans ?_
          rw [norm_smul, norm_smul]
          gcongr
          · exact PiLp.norm_apply_le _ _
          · exact PiLp.norm_apply_le _ _
      _ = ∑ j : Fin 3, (‖p‖ * ‖z₁ j‖ * ‖u‖ + ‖z₂‖ * ‖q j‖ * ‖u‖) := by
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  calc ENNReal.ofReal ‖inner ℝ a u‖
      ≤ ENNReal.ofReal (∑ j : Fin 3, (‖p‖ * ‖z₁ j‖ * ‖u‖ + ‖z₂‖ * ‖q j‖ * ‖u‖)) :=
        ENNReal.ofReal_le_ofReal hreal
    _ = ∑ j : Fin 3, ENNReal.ofReal (‖p‖ * ‖z₁ j‖ * ‖u‖ + ‖z₂‖ * ‖q j‖ * ‖u‖) :=
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)
    _ = _ := Finset.sum_congr rfl fun j _ => ENNReal.ofReal_add (by positivity) (by positivity)

theorem lintegral_sum_le {a c : Fin 3 → Space → ℝ≥0∞} (ha : ∀ j, AEMeasurable (a j) volume)
    (hc : ∀ j, AEMeasurable (c j) volume) {α γ : ℝ≥0∞} (h₁ : ∀ j, ∫⁻ y, a j y ≤ α)
    (h₂ : ∀ j, ∫⁻ y, c j y ≤ γ) : ∫⁻ y, ∑ j : Fin 3, (a j y + c j y) ≤ 3 * (α + γ) := by
  rw [lintegral_finsetSum' _ (f := fun j y => a j y + c j y) (fun j _ => (ha j).add (hc j))]
  calc ∑ j : Fin 3, ∫⁻ y, (a j y + c j y) ≤ ∑ _j : Fin 3, (α + γ) := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [lintegral_add_left' (ha j)]
        exact add_le_add (h₁ j) (h₂ j)
    _ = 3 * (α + γ) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

theorem integral_bound_of_parts (A w : Freq.L2R) (P z₂ : Freq.L6R) (z₁ Q : Fin 3 → Freq.L2R)
    {α β γ c d : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β) (hγ : 0 ≤ γ) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hP : ‖P‖ ≤ α) (hz₁ : ∀ j, ‖z₁ j‖ ≤ β) (hz₂ : ‖z₂‖ ≤ β) (hQ : ∀ j, ‖Q j‖ ≤ γ)
    (hw2 : eLpNorm (w : Space → Space) 2 volume ≤ ENNReal.ofReal c)
    (hw6 : eLpNorm (w : Space → Space) 6 volume ≤ ENNReal.ofReal d)
    (hpt : ∀ᵐ y ∂volume, ENNReal.ofReal ‖inner ℝ ((A : Space → Space) y) ((w : Space → Space) y)‖ ≤
      ∑ j : Fin 3, (ENNReal.ofReal (‖(P : Space → Space) y‖ * ‖(z₁ j : Space → Space) y‖ *
          ‖(w : Space → Space) y‖) +
        ENNReal.ofReal (‖(z₂ : Space → Space) y‖ * ‖(Q j : Space → Space) y‖ *
          ‖(w : Space → Space) y‖))) :
    ∫ y, inner ℝ ((A : Space → Space) y) ((w : Space → Space) y) ≤
      3 * (α * β * Real.sqrt (c * d) + β * γ * Real.sqrt (c * d)) := by
  have hwm : AEStronglyMeasurable (w : Space → Space) volume := Lp.aestronglyMeasurable w
  have hs : 0 ≤ Real.sqrt (c * d) := Real.sqrt_nonneg _
  have h1 : 0 ≤ α * β * Real.sqrt (c * d) := mul_nonneg (mul_nonneg hα hβ) hs
  have h2 : 0 ≤ β * γ * Real.sqrt (c * d) := mul_nonneg (mul_nonneg hβ hγ) hs
  have hM : 0 ≤ 3 * (α * β * Real.sqrt (c * d) + β * γ * Real.sqrt (c * d)) :=
    mul_nonneg (by norm_num) (add_nonneg h1 h2)
  have hL : ∫⁻ y, ENNReal.ofReal ‖inner ℝ ((A : Space → Space) y) ((w : Space → Space) y)‖ ≤
      ENNReal.ofReal (3 * (α * β * Real.sqrt (c * d) + β * γ * Real.sqrt (c * d))) := by
    refine (lintegral_mono_ae hpt).trans ?_
    refine (lintegral_sum_le
      (a := fun j y => ENNReal.ofReal (‖(P : Space → Space) y‖ * ‖(z₁ j : Space → Space) y‖ *
        ‖(w : Space → Space) y‖))
      (c := fun j y => ENNReal.ofReal (‖(z₂ : Space → Space) y‖ * ‖(Q j : Space → Space) y‖ *
        ‖(w : Space → Space) y‖))
      (fun j => (((Lp.aestronglyMeasurable P).norm.mul
        (Lp.aestronglyMeasurable (z₁ j)).norm).mul hwm.norm).aemeasurable.ennreal_ofReal)
      (fun j => (((Lp.aestronglyMeasurable z₂).norm.mul
        (Lp.aestronglyMeasurable (Q j)).norm).mul hwm.norm).aemeasurable.ennreal_ofReal)
      (fun j => lintegral_three_le_real (Lp.aestronglyMeasurable P) (Lp.aestronglyMeasurable (z₁ j))
        hwm hα hβ hc hd (eLpNorm_Lp_le P hP) (eLpNorm_Lp_le (z₁ j) (hz₁ j)) hw2 hw6)
      (fun j => lintegral_three_le_real (Lp.aestronglyMeasurable z₂) (Lp.aestronglyMeasurable (Q j))
        hwm hβ hγ hc hd (eLpNorm_Lp_le z₂ hz₂) (eLpNorm_Lp_le (Q j) (hQ j)) hw2 hw6)).trans
      (le_of_eq ?_)
    rw [← ENNReal.ofReal_add h1 h2, show (3 : ℝ≥0∞) = ENNReal.ofReal 3 by simp,
      ← ENNReal.ofReal_mul (by norm_num)]
  exact (Real.le_norm_self _).trans ((norm_integral_le_lintegral_norm _).trans
    (ENNReal.toReal_le_of_le_ofReal hM hL))

set_option maxHeartbeats 400000 in
theorem inner_heatDivFree_le (hF : Freq.FieldOpRealized) (hPhi : Freq.PhiBounds)
    (hVs : Freq.VelocityDecay) (hPd : Freq.PartialDecay) (hP : Freq.PartialNormLe) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ), 0 < τ → ∀ ζ : ShellData,
      ∀ ψ : Freq.X, inner ℝ (Freq.heatDivFree τ (advectShell φ hφ b ζ)) ψ ≤
        C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖ * ‖ψ‖ := by
  obtain ⟨C0, hC0⟩ := hPhi
  obtain ⟨K, hK_def⟩ : ∃ K, K = |C0| := ⟨_, rfl⟩
  have hK : 0 ≤ K := hK_def ▸ abs_nonneg C0
  obtain ⟨V, hV_def⟩ : ∃ V, V = ‖(Freq.velocity : Freq.X →L[ℝ] Freq.L6R)‖ := ⟨_, rfl⟩
  have hV : 0 ≤ V := hV_def ▸ norm_nonneg _
  refine ⟨3 * (V + 1) * K, mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hK, ?_⟩
  intro φ hφ b τ hτ ζ ψ
  obtain ⟨hw6, hw2, hw6'⟩ := hC0 τ hτ ψ
  have hD := Freq.Internal.EmbedNegSsp.isDecayField_of_isTestField hφ
  have hAeq : advectShell φ hφ b ζ = advectShellFun φ b ζ := rfl
  rw [hAeq]
  obtain ⟨A, hA_def⟩ : ∃ A, A = advectShellFun φ b ζ := ⟨_, rfl⟩
  rw [← hA_def]
  obtain ⟨e, he_def⟩ : ∃ e, e = Freq.embedX φ := ⟨_, rfl⟩
  rw [← he_def]
  obtain ⟨w, hw_def⟩ : ∃ w, w = Freq.phiX τ ψ := ⟨_, rfl⟩
  rw [← hw_def] at hw6 hw2 hw6'
  obtain ⟨P, hP_def⟩ : ∃ P, P = Freq.velocity e := ⟨_, rfl⟩
  obtain ⟨S, hS_def⟩ : ∃ S, S = K * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖ := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := hS_def ▸ mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hc0 : 0 ≤ K * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖ := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hd0 : 0 ≤ K * τ ^ (-(1 : ℝ)) * ‖ψ‖ := mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hτ.le _)) (norm_nonneg ψ)
  have hVe : 0 ≤ V * ‖e‖ := mul_nonneg hV (norm_nonneg e)
  have hw2' : eLpNorm (w : Space → Space) 2 volume ≤ ENNReal.ofReal (K * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖) := by
    rw [ENNReal.le_ofReal_iff_toReal_le (Lp.memLp w).eLpNorm_ne_top hc0]
    refine hw2.trans ?_
    rw [hK_def]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.rpow_nonneg hτ.le _))
      (norm_nonneg ψ)
  have hw6'' : eLpNorm (w : Space → Space) 6 volume ≤ ENNReal.ofReal (K * τ ^ (-(1 : ℝ)) * ‖ψ‖) := by
    rw [ENNReal.le_ofReal_iff_toReal_le hw6.eLpNorm_ne_top hd0]
    refine hw6'.trans ?_
    rw [hK_def]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self C0) (Real.rpow_nonneg hτ.le _))
      (norm_nonneg ψ)
  have hsq := sqrt_phi_product hK hτ (norm_nonneg ψ)
  have hPφ : (P : Space → Space) =ᵐ[volume] φ := by
    rw [hP_def, he_def]
    exact hVs φ hD
  have hQφ : ∀ᵐ y ∂volume, ∀ j : Fin 3,
      (Freq.partialX j e : Space → Space) y = Freq.partialField φ j y := by
    rw [ae_all_iff, he_def]
    exact fun j => hPd φ hD j
  have hA : ∀ᵐ y ∂volume, ‖(A : Space → Space) y‖ ≤
      ‖(Metric.closedBall (0 : Space) b).indicator
        (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
          (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) y‖ := by
    rw [hA_def]
    exact toLpOrZero_norm_le 2 _
  have hpt : ∀ᵐ y ∂volume, ENNReal.ofReal ‖inner ℝ ((A : Space → Space) y) (w y)‖ ≤
      ∑ j : Fin 3, (ENNReal.ofReal (‖(P : Space → Space) y‖ * ‖(ζ.1 j : Space → Space) y‖ * ‖w y‖) +
        ENNReal.ofReal (‖(ζ.2 : Space → Space) y‖ * ‖(Freq.partialX j e : Space → Space) y‖ *
          ‖w y‖)) := by
    filter_upwards [hPφ, hQφ, hA] with y hy1 hy2 hy3
    exact pointwise_inner_le _ _ _ _ _ _ _ _ hy1 hy2 (hy3.trans (norm_indicator_le_norm_self _ _))
  rw [Freq.Internal.BilinTestFormula.heatDivFree_inner hF hτ, ← hw_def, MeasureTheory.L2.inner_def]
  have hI := integral_bound_of_parts A w P ζ.2 ζ.1 (fun j => Freq.partialX j e) hVe (norm_nonneg ζ)
    (norm_nonneg e) hc0 hd0 (by rw [hP_def, hV_def]; exact Freq.velocity.le_opNorm e)
    (fun j => (norm_le_pi_norm ζ.1 j).trans (norm_fst_le ζ)) (norm_snd_le ζ)
    (fun j => partialX_norm_le hP e j) hw2' hw6'' hpt
  rw [hsq] at hI
  have key : 3 * (V * ‖e‖ * ‖ζ‖ * (K * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖) +
      ‖ζ‖ * ‖e‖ * (K * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖)) =
      3 * (V + 1) * K * τ ^ (-(3 / 4 : ℝ)) * ‖e‖ * ‖ζ‖ * ‖ψ‖ := by ring
  exact hI.trans key.le

end Internal.ShellR3

open Internal.ShellR3 in
theorem restrictR3Bound (_hV : Freq.VelocityExists) (hP : Freq.PartialNormLe) : RestrictR3Bound := by
  have hC : (0 : ℝ) ≤ max 1 ‖Freq.velocity‖ := le_max_of_le_left zero_le_one
  refine ⟨max 1 ‖Freq.velocity‖, hC, fun b => ?_⟩
  refine ContinuousLinearMap.opNorm_le_bound _ hC (fun v => ?_)
  have hv : 0 ≤ max 1 ‖Freq.velocity‖ * ‖v‖ := mul_nonneg hC (norm_nonneg v)
  rw [restrictR3_apply, norm_prod_le_iff]
  constructor
  · refine (pi_norm_le_iff_of_nonneg hv).2 (fun j => ?_)
    calc ‖cutLp 2 b (Freq.partialX j v)‖ ≤ ‖cutLp 2 b‖ * ‖Freq.partialX j v‖ := (cutLp 2 b).le_opNorm _
      _ ≤ 1 * ‖v‖ := by
        gcongr
        · exact cutLp_norm_le 2 b
        · exact partialX_norm_le hP v j
      _ ≤ max 1 ‖Freq.velocity‖ * ‖v‖ := by gcongr; exact le_max_left _ _
  · calc ‖cutLp 6 b (Freq.velocity v)‖ ≤ ‖cutLp 6 b‖ * ‖Freq.velocity v‖ := (cutLp 6 b).le_opNorm _
      _ ≤ 1 * (‖Freq.velocity‖ * ‖v‖) := by
        gcongr
        · exact cutLp_norm_le 6 b
        · exact Freq.velocity.le_opNorm v
      _ ≤ max 1 ‖Freq.velocity‖ * ‖v‖ := by
        rw [one_mul]; gcongr; exact le_max_right _ _

open Internal.ShellR3 in
theorem r3Factor (hB : Freq.BilinTestFormula) (_hVs : Freq.VelocityDecay) (_hPd : Freq.PartialDecay) :
    R3Factor := by
  intro φ hφ b hb τ hτ v
  rw [hB φ hφ τ hτ v, lambdaR3]
  show _ = -(Freq.heatDivFree τ (advectShell φ hφ b (restrictR3 b v)))
  rw [advectShell_restrict hφ hb, smul_smul, show (2 : ℝ) * (-(1 / 2)) = -1 by norm_num, neg_one_smul]

open Internal.ShellR3 in
theorem r3LambdaBound (hF : Freq.FieldOpRealized) (hPhi : Freq.PhiBounds) (hVs : Freq.VelocityDecay)
    (hPd : Freq.PartialDecay) (hP : Freq.PartialNormLe) : R3LambdaBound := by
  obtain ⟨C, hC, hI⟩ := inner_heatDivFree_le hF hPhi hVs hPd hP
  refine ⟨C, hC, fun φ hφ b τ hτ ζ => ?_⟩
  have hx : ‖lambdaR3 φ hφ b τ ζ‖ = ‖Freq.heatDivFree τ (advectShell φ hφ b ζ)‖ := by
    rw [lambdaR3]
    show ‖-(Freq.heatDivFree τ (advectShell φ hφ b ζ))‖ = _
    rw [norm_neg]
  rw [hx]
  have h1 := hI φ hφ b τ hτ ζ (Freq.heatDivFree τ (advectShell φ hφ b ζ))
  rw [real_inner_self_eq_norm_sq] at h1
  have hM : 0 ≤ C * τ ^ (-(3 / 4 : ℝ)) * ‖Freq.embedX φ‖ * ‖ζ‖ := by positivity
  nlinarith [norm_nonneg (Freq.heatDivFree τ (advectShell φ hφ b ζ))]

end Breakdown.Periodic

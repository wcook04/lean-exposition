import Breakdown.Cert.Statement
import Breakdown.Uniqueness.CutoffBounds
import Breakdown.FracCell.AdjointConvectionPairingParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace RepresentationParts

namespace Internal

namespace Slice

theorem linear_expand {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F)
    (w : Space) : L w = ∑ k : Fin 3, w k • L (unitVector k) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w]
  simp [map_sum, map_smul, unitVector]

theorem inner_expand (a b : Space) : inner ℝ a b = ∑ i : Fin 3, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

theorem component_locallyIntegrable {f : Space → Space} (hf : LocallyIntegrable f volume) (i : Fin 3) :
    LocallyIntegrable (fun y => f y i) volume := by
  have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).locallyIntegrableOn_comp
    (locallyIntegrableOn_univ.2 hf)
  exact locallyIntegrableOn_univ.1 h

theorem apply_locallyIntegrable {G : Space → (Space →L[ℝ] Space)} (hG : LocallyIntegrable G volume)
    (w : Space) : LocallyIntegrable (fun y => G y w) volume := by
  have h := (ContinuousLinearMap.apply ℝ Space w).locallyIntegrableOn_comp
    (locallyIntegrableOn_univ.2 hG)
  exact locallyIntegrableOn_univ.1 h

theorem weak_component {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hvG : IsWeakGradient v G) {ψ : Space → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (i k : Fin 3) :
    ∫ y, fderiv ℝ ψ y (unitVector k) * v y i = -∫ y, ψ y * G y (unitVector k) i := by
  have hGk : LocallyIntegrable (fun y => G y (unitVector k)) volume :=
    apply_locallyIntegrable hvG.2.1 (unitVector k)
  have hw : SteadyCert.IsWeakGradientOf v G := by
    intro φ hφ j
    rw [hvG.2.2 φ hφ j, neg_neg]
  have h := FracInternal.ConvectionPairing.weak_of_C1 hvG.1 k hGk hw hψ hψc
  have hd : Continuous fun y => fderiv ℝ ψ y (unitVector k) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ ψ y (unitVector k) • v y) :=
    hvG.1.integrable_smul_left_of_hasCompactSupport hd (hψc.fderiv_apply (𝕜 := ℝ) (unitVector k))
  have i2 : Integrable (fun y => ψ y • G y (unitVector k)) :=
    hGk.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
  have e1 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i1
  have e2 := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i2
  have h' := congrArg (EuclideanSpace.proj i : Space →L[ℝ] ℝ) h
  rw [← e1, map_neg, ← e2] at h'
  simpa [smul_eq_mul] using h'

theorem cutoff_identity {v W ζ : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hvG : IsWeakGradient v G) (hW : ContDiff ℝ 1 W) (hWdiv : ∀ y, divergenceAt W y = 0)
    (hζ : ContDiff ℝ 1 ζ) {χ : Space → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∫ y, χ y * inner ℝ (G y (W y)) (ζ y) =
      -∫ y, (χ y * inner ℝ (v y) (fderiv ℝ ζ y (W y)) + fderiv ℝ χ y (W y) * inner ℝ (ζ y) (v y)) := by
  set T : Fin 3 → Fin 3 → Space → ℝ := fun i k y => χ y * (ζ y i * W y k) with hT
  have hζi : ∀ i, ContDiff ℝ 1 (fun y => ζ y i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hζ
  have hWk : ∀ k, ContDiff ℝ 1 (fun y => W y k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW
  have hTc : ∀ i k, ContDiff ℝ 1 (T i k) := fun i k => hχ.mul ((hζi i).mul (hWk k))
  have hTs : ∀ i k, HasCompactSupport (T i k) := fun i k => HasCompactSupport.mul_right hχc
  have hTd : ∀ i k y, fderiv ℝ (T i k) y (unitVector k) =
      χ y * (ζ y i * fderiv ℝ W y (unitVector k) k + W y k * fderiv ℝ ζ y (unitVector k) i) +
        ζ y i * W y k * fderiv ℝ χ y (unitVector k) := by
    intro i k y
    have h1 : HasFDerivAt χ (fderiv ℝ χ y) y := (hχ.differentiable one_ne_zero y).hasFDerivAt
    have h2 : HasFDerivAt (fun y => ζ y i)
        ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ ζ y)) y :=
      (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y
        ((hζ.differentiable one_ne_zero y).hasFDerivAt)
    have h3 : HasFDerivAt (fun y => W y k)
        ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (fderiv ℝ W y)) y :=
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y
        ((hW.differentiable one_ne_zero y).hasFDerivAt)
    have h4 := (h1.mul (h2.mul h3)).fderiv
    have e : T i k = χ * ((fun y => ζ y i) * fun y => W y k) := rfl
    rw [e, h4]
    simp
    ring
  have S1 : ∀ y, ∑ i : Fin 3, ∑ k : Fin 3, fderiv ℝ (T i k) y (unitVector k) * v y i =
      χ y * inner ℝ (v y) (fderiv ℝ ζ y (W y)) + fderiv ℝ χ y (W y) * inner ℝ (ζ y) (v y) := by
    intro y
    have hd := hWdiv y
    unfold divergenceAt at hd
    simp only [hTd]
    rw [inner_expand, inner_expand, linear_expand (fderiv ℝ ζ y) (W y),
      linear_expand (fderiv ℝ χ y) (W y)]
    simp [Fin.sum_univ_three] at hd ⊢
    linear_combination (χ y * (ζ y 0 * v y 0 + ζ y 1 * v y 1 + ζ y 2 * v y 2)) * hd
  have S2 : ∀ y, ∑ i : Fin 3, ∑ k : Fin 3, T i k y * G y (unitVector k) i =
      χ y * inner ℝ (G y (W y)) (ζ y) := by
    intro y
    rw [inner_expand, linear_expand (G y) (W y)]
    simp [Fin.sum_univ_three, T]
    ring
  have iA : ∀ i k, Integrable (fun y => fderiv ℝ (T i k) y (unitVector k) * v y i) := by
    intro i k
    have hd : Continuous fun y => fderiv ℝ (T i k) y (unitVector k) :=
      ((hTc i k).continuous_fderiv one_ne_zero).clm_apply continuous_const
    simpa only [smul_eq_mul] using (component_locallyIntegrable hvG.1 i).integrable_smul_left_of_hasCompactSupport
      hd ((hTs i k).fderiv_apply (𝕜 := ℝ) (unitVector k))
  have iB : ∀ i k, Integrable (fun y => T i k y * G y (unitVector k) i) := by
    intro i k
    simpa only [smul_eq_mul] using
      (component_locallyIntegrable (apply_locallyIntegrable hvG.2.1 (unitVector k)) i).integrable_smul_left_of_hasCompactSupport
        (hTc i k).continuous (hTs i k)
  have w : ∀ i k, ∫ y, T i k y * G y (unitVector k) i =
      -∫ y, fderiv ℝ (T i k) y (unitVector k) * v y i := by
    intro i k
    rw [weak_component hvG (hTc i k) (hTs i k) i k, neg_neg]
  calc ∫ y, χ y * inner ℝ (G y (W y)) (ζ y)
      = ∫ y, ∑ i : Fin 3, ∑ k : Fin 3, T i k y * G y (unitVector k) i :=
        integral_congr_ae (ae_of_all _ fun y => (S2 y).symm)
    _ = ∑ i : Fin 3, ∑ k : Fin 3, ∫ y, T i k y * G y (unitVector k) i := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => iB i k]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun k _ => iB i k]
    _ = -∑ i : Fin 3, ∑ k : Fin 3, ∫ y, fderiv ℝ (T i k) y (unitVector k) * v y i := by
        simp only [w, Finset.sum_neg_distrib]
    _ = -∫ y, ∑ i : Fin 3, ∑ k : Fin 3, fderiv ℝ (T i k) y (unitVector k) * v y i := by
        rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ => iA i k]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun k _ => iA i k]
    _ = _ := by
        congr 1
        exact integral_congr_ae (ae_of_all _ fun y => S1 y)

theorem mul_le_sixth_add (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a * b ≤ a ^ 6 + b ^ ((6 : ℝ) / 5) := by
  by_cases h : a ≤ b ^ ((1 : ℝ) / 5)
  · have e : b ^ ((6 : ℝ) / 5) = b ^ ((1 : ℝ) / 5) * b := by
      rw [show (6 : ℝ) / 5 = 1 / 5 + 1 by norm_num, Real.rpow_add' hb (by norm_num), Real.rpow_one]
    have h1 : a * b ≤ b ^ ((1 : ℝ) / 5) * b := mul_le_mul_of_nonneg_right h hb
    linarith [pow_nonneg ha 6]
  · replace h := not_le.1 h
    have e : (b ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) = b := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hb]
      norm_num
    have hb5 : b ≤ a ^ 5 := by
      calc b = (b ^ ((1 : ℝ) / 5)) ^ (5 : ℕ) := e.symm
        _ ≤ a ^ 5 := pow_le_pow_left₀ (Real.rpow_nonneg hb _) h.le 5
    have h1 : a * b ≤ a * a ^ 5 := mul_le_mul_of_nonneg_left hb5 ha
    have h6 : a * a ^ 5 = a ^ 6 := by ring
    linarith [Real.rpow_nonneg hb ((6 : ℝ) / 5)]

theorem decay_rpow_integrable {f : Space → ℝ} (hf : Continuous f) (hf0 : ∀ y, 0 ≤ f y) {a p C : ℝ}
    (hp : 0 < p) (hC : 0 ≤ C) (hb : ∀ y, f y ≤ C / (1 + ‖y‖) ^ a) (hap : 3 < a * p) :
    Integrable (fun y => f y ^ p) := by
  have hI : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(a * p))) := by
    refine integrable_one_add_norm ?_
    rw [show Module.finrank ℝ Space = 3 from finrank_euclideanSpace_fin]
    exact_mod_cast hap
  refine (hI.const_mul (C ^ p)).mono' (hf.rpow_const fun _ => Or.inr hp.le).aestronglyMeasurable
    (ae_of_all _ fun y => ?_)
  have h1 : 0 < 1 + ‖y‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hf0 y) p)]
  calc f y ^ p ≤ (C / (1 + ‖y‖) ^ a) ^ p := Real.rpow_le_rpow (hf0 y) (hb y) hp.le
    _ = C ^ p * (1 + ‖y‖) ^ (-(a * p)) := by
      rw [Real.div_rpow hC (Real.rpow_nonneg h1.le a), ← Real.rpow_mul h1.le, Real.rpow_neg h1.le,
        div_eq_mul_inv]

end Slice

end Internal

open Internal.Slice in
set_option maxHeartbeats 1000000 in
theorem slice_convection_pairing {v W ζ : Space → Space} {G : Space → (Space →L[ℝ] Space)} {D C γ : ℝ}
    (hvG : IsWeakGradient v G) (hv6 : ∫⁻ y, ENNReal.ofReal (‖v y‖ ^ 6) < ⊤)
    (hG2 : ∫⁻ y, ENNReal.ofReal (matSq (G y)) < ⊤)
    (hW : ContDiff ℝ 1 W) (hWdiv : ∀ y, divergenceAt W y = 0) (hWb : ∀ y, ‖W y‖ ≤ D)
    (hζ : ContDiff ℝ 1 ζ) (hγ : 5 / 2 < γ)
    (hζd : ∀ y, ‖ζ y‖ ≤ C / (1 + ‖y‖) ^ γ ∧ ‖fderiv ℝ ζ y‖ ≤ C / (1 + ‖y‖) ^ (γ + 1)) :
    ∫ y, inner ℝ (G y (W y)) (ζ y) = -∫ y, inner ℝ (v y) (fderiv ℝ ζ y (W y)) := by
  have hC : 0 ≤ C := by
    have h := (hζd 0).1
    simp at h
    exact (norm_nonneg _).trans h
  have hD : 0 ≤ D := (norm_nonneg _).trans (hWb 0)
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hc0 : 0 ≤ c := by
    have h := hc 1 one_pos 0
    rw [div_one] at h
    exact (norm_nonneg _).trans h
  have hdζ : Continuous fun y => fderiv ℝ ζ y := hζ.continuous_fderiv one_ne_zero
  have iv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    refine ⟨hvG.1.aestronglyMeasurable.norm.pow 6, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 hv6
  have iGk : ∀ k : Fin 3, Integrable (fun y => ‖G y (unitVector k)‖ ^ 2) := by
    intro k
    refine ⟨(apply_locallyIntegrable hvG.2.1 (unitVector k)).aestronglyMeasurable.norm.pow 2, ?_⟩
    refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun y => by positivity)).2 ?_
    refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) hG2
    unfold matSq
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ k)
  have iζ2 : Integrable (fun y => ‖ζ y‖ ^ 2) := by
    have h := decay_rpow_integrable hζ.continuous.norm (fun y => norm_nonneg _) (p := 2) two_pos hC
      (fun y => (hζd y).1) (by linarith)
    simpa [Real.rpow_two] using h
  have iζ6 : Integrable (fun y => ‖ζ y‖ ^ ((6 : ℝ) / 5)) :=
    decay_rpow_integrable hζ.continuous.norm (fun y => norm_nonneg _) (by norm_num) hC
      (fun y => (hζd y).1) (by linarith)
  have idζ6 : Integrable (fun y => ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) :=
    decay_rpow_integrable hdζ.norm (fun y => norm_nonneg _) (by norm_num) hC
      (fun y => (hζd y).2) (by linarith)
  have mG : AEStronglyMeasurable (fun y => G y (W y)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable
      (hvG.2.1.aestronglyMeasurable.prodMk hW.continuous.aestronglyMeasurable)
  have mf : AEStronglyMeasurable (fun y => inner ℝ (G y (W y)) (ζ y)) volume :=
    mG.inner hζ.continuous.aestronglyMeasurable
  have mg : AEStronglyMeasurable (fun y => inner ℝ (v y) (fderiv ℝ ζ y (W y))) volume :=
    hvG.1.aestronglyMeasurable.inner (hdζ.clm_apply hW.continuous).aestronglyMeasurable
  have mh : AEStronglyMeasurable (fun y => inner ℝ (ζ y) (v y)) volume :=
    hζ.continuous.aestronglyMeasurable.inner hvG.1.aestronglyMeasurable
  have bf : ∀ y, |inner ℝ (G y (W y)) (ζ y)| ≤
      D * ∑ k : Fin 3, (‖G y (unitVector k)‖ ^ 2 + ‖ζ y‖ ^ 2) := by
    intro y
    have h1 : ‖G y (W y)‖ ≤ ∑ k : Fin 3, D * ‖G y (unitVector k)‖ := by
      rw [linear_expand (G y) (W y)]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (W y) k).trans (hWb y)) (norm_nonneg _)
    calc |inner ℝ (G y (W y)) (ζ y)| ≤ ‖G y (W y)‖ * ‖ζ y‖ := abs_real_inner_le_norm _ _
      _ ≤ (∑ k : Fin 3, D * ‖G y (unitVector k)‖) * ‖ζ y‖ :=
        mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
      _ ≤ D * ∑ k : Fin 3, (‖G y (unitVector k)‖ ^ 2 + ‖ζ y‖ ^ 2) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_le_sum fun k _ => ?_
        nlinarith [mul_nonneg hD (sq_nonneg (‖G y (unitVector k)‖ - ‖ζ y‖)),
          mul_nonneg hD (sq_nonneg ‖G y (unitVector k)‖), mul_nonneg hD (sq_nonneg ‖ζ y‖)]
  have bg : ∀ y, |inner ℝ (v y) (fderiv ℝ ζ y (W y))| ≤
      D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) := by
    intro y
    have h1 : ‖fderiv ℝ ζ y (W y)‖ ≤ ‖fderiv ℝ ζ y‖ * D :=
      (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_left (hWb y) (norm_nonneg _))
    have h2 := mul_le_sixth_add ‖v y‖ ‖fderiv ℝ ζ y‖ (norm_nonneg _) (norm_nonneg _)
    calc |inner ℝ (v y) (fderiv ℝ ζ y (W y))| ≤ ‖v y‖ * ‖fderiv ℝ ζ y (W y)‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖v y‖ * (‖fderiv ℝ ζ y‖ * D) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = D * (‖v y‖ * ‖fderiv ℝ ζ y‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 hD
  have bh : ∀ y, |inner ℝ (ζ y) (v y)| ≤ ‖v y‖ ^ 6 + ‖ζ y‖ ^ ((6 : ℝ) / 5) := by
    intro y
    have h2 := mul_le_sixth_add ‖v y‖ ‖ζ y‖ (norm_nonneg _) (norm_nonneg _)
    calc |inner ℝ (ζ y) (v y)| ≤ ‖ζ y‖ * ‖v y‖ := abs_real_inner_le_norm _ _
      _ = ‖v y‖ * ‖ζ y‖ := mul_comm _ _
      _ ≤ _ := h2
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have χc : ∀ n : ℕ, ContDiff ℝ 1 (radialCutoff ((n : ℝ) + 1)) := fun n =>
    (contDiff_radialCutoff (hr n)).of_le (by simp)
  have χs : ∀ n : ℕ, HasCompactSupport (radialCutoff ((n : ℝ) + 1)) := fun n =>
    hasCompactSupport_radialCutoff (hr n)
  have ev : ∀ y : Space, ∀ᶠ n : ℕ in Filter.atTop,
      radialCutoff ((n : ℝ) + 1) y = 1 ∧ fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y = 0 := by
    intro y
    refine Filter.eventually_atTop.2 ⟨⌊‖y‖⌋₊, fun n hn => ?_⟩
    have hy : ‖y‖ < (n : ℝ) + 1 := by
      have h1 := Nat.lt_floor_add_one ‖y‖
      have h2 : (⌊‖y‖⌋₊ : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    refine ⟨radialCutoff_eq_one (hr n) hy.le, ?_⟩
    have hloc : radialCutoff ((n : ℝ) + 1) =ᶠ[nhds y] fun _ => (1 : ℝ) :=
      Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hy))
        fun z hz => radialCutoff_eq_one (hr n) (mem_ball_zero_iff.1 hz).le
    rw [hloc.fderiv_eq]
    simp
  have ib1 : Integrable (fun y => D * ∑ k : Fin 3, (‖G y (unitVector k)‖ ^ 2 + ‖ζ y‖ ^ 2)) := by
    refine Integrable.const_mul ?_ D
    refine integrable_finsetSum (f := fun k y => ‖G y (unitVector k)‖ ^ 2 + ‖ζ y‖ ^ 2) _ fun k _ => ?_
    exact (iGk k).add iζ2
  have ib2 : Integrable (fun y => D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) +
      c * D * (‖v y‖ ^ 6 + ‖ζ y‖ ^ ((6 : ℝ) / 5))) := by
    have j1 : Integrable (fun y => D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5))) :=
      Integrable.const_mul (iv6.add idζ6) D
    have j2 : Integrable (fun y => c * D * (‖v y‖ ^ 6 + ‖ζ y‖ ^ ((6 : ℝ) / 5))) :=
      Integrable.const_mul (iv6.add iζ6) (c * D)
    exact j1.add j2
  have lim1 : Filter.Tendsto (fun n : ℕ => ∫ y, radialCutoff ((n : ℝ) + 1) y * inner ℝ (G y (W y)) (ζ y))
      Filter.atTop (nhds (∫ y, inner ℝ (G y (W y)) (ζ y))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => D * ∑ k : Fin 3, (‖G y (unitVector k)‖ ^ 2 + ‖ζ y‖ ^ 2))
      (fun n => (χc n).continuous.aestronglyMeasurable.mul mf)
      ib1
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · rw [Real.norm_eq_abs, abs_mul]
      have h0 := radialCutoff_nonneg ((n : ℝ) + 1) y
      have h1 := radialCutoff_le_one ((n : ℝ) + 1) y
      rw [abs_of_nonneg h0]
      calc radialCutoff ((n : ℝ) + 1) y * |inner ℝ (G y (W y)) (ζ y)|
          ≤ 1 * |inner ℝ (G y (W y)) (ζ y)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact bf y
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev y] with n hn
      rw [hn.1, one_mul]
  have lim2 : Filter.Tendsto (fun n : ℕ => ∫ y, (radialCutoff ((n : ℝ) + 1) y *
      inner ℝ (v y) (fderiv ℝ ζ y (W y)) + fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (W y) *
        inner ℝ (ζ y) (v y)))
      Filter.atTop (nhds (∫ y, inner ℝ (v y) (fderiv ℝ ζ y (W y)))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun y => D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) +
        c * D * (‖v y‖ ^ 6 + ‖ζ y‖ ^ ((6 : ℝ) / 5)))
      (fun n => ((χc n).continuous.aestronglyMeasurable.mul mg).add
        ((((χc n).continuous_fderiv one_ne_zero).clm_apply hW.continuous).aestronglyMeasurable.mul mh))
      ib2
      (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have h0 := radialCutoff_nonneg ((n : ℝ) + 1) y
      have h1 := radialCutoff_le_one ((n : ℝ) + 1) y
      have hd : |fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (W y)| ≤ c * D := by
        rw [← Real.norm_eq_abs]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        have h2 : c / ((n : ℝ) + 1) ≤ c := div_le_self hc0 (by linarith [hr n, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        exact mul_le_mul ((hc _ (hr n) y).trans h2) (hWb y) (norm_nonneg _) hc0
      rw [Real.norm_eq_abs]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg h0]
      have e1 : radialCutoff ((n : ℝ) + 1) y * |inner ℝ (v y) (fderiv ℝ ζ y (W y))| ≤
          D * (‖v y‖ ^ 6 + ‖fderiv ℝ ζ y‖ ^ ((6 : ℝ) / 5)) :=
        (mul_le_of_le_one_left (abs_nonneg _) h1).trans (bg y)
      have e2 : |fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (W y)| * |inner ℝ (ζ y) (v y)| ≤
          c * D * (‖v y‖ ^ 6 + ‖ζ y‖ ^ ((6 : ℝ) / 5)) :=
        mul_le_mul hd (bh y) (abs_nonneg _) (mul_nonneg hc0 hD)
      linarith
    · refine tendsto_const_nhds.congr' ?_
      filter_upwards [ev y] with n hn
      rw [hn.1, hn.2, one_mul]
      simp
  have eq : ∀ n : ℕ, ∫ y, radialCutoff ((n : ℝ) + 1) y * inner ℝ (G y (W y)) (ζ y) =
      -∫ y, (radialCutoff ((n : ℝ) + 1) y * inner ℝ (v y) (fderiv ℝ ζ y (W y)) +
        fderiv ℝ (radialCutoff ((n : ℝ) + 1)) y (W y) * inner ℝ (ζ y) (v y)) := fun n =>
    cutoff_identity hvG hW hWdiv hζ (χc n) (χs n)
  exact tendsto_nhds_unique lim1 (lim2.neg.congr fun n => (eq n).symm)

end RepresentationParts

end Breakdown

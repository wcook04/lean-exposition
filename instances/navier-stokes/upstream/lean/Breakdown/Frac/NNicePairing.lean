import Breakdown.Frac.StRealize
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform LineDeriv

noncomputable section

namespace Breakdown.Freq

namespace Internal.NicePairing

theorem coord_sum_zero {m : Space → CSpace} (hm : IsNiceSymbol m) (y : Space) :
    ∑ i : Fin 3, (𝓕⁻ ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i))
      (hm.2.1.toSchwartzMap hm.1)) y) i = 0 := by
  set Mc : 𝓢(Space, CSpace) := hm.2.1.toSchwartzMap hm.1 with hMc
  have hMf : ⇑Mc = m := rfl
  have hT : ∀ i : Fin 3, (fun x : Space => inner ℝ x (unitVector i)).HasTemperateGrowth :=
    fun i => ((innerSL ℝ).flip (unitVector i)).hasTemperateGrowth
  have hint : ∀ i : Fin 3, Integrable (fun v : Space => 𝐞 (inner ℝ v y) •
      ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc) v) volume := by
    intro i
    have := (Real.fourierIntegral_convergent_iff (-y)).2
      ((((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc)).integrable
        (μ := volume))
    simpa [inner_neg_right] using this
  have hc : ∀ i : Fin 3, (𝓕⁻ ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i))
      Mc) y) i = ∫ v, (𝐞 (inner ℝ v y) •
        ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc) v) i := by
    intro i
    rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
    exact ((EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integral_comp_comm (hint i)).symm
  have hint' : ∀ i : Fin 3, Integrable (fun v : Space => (𝐞 (inner ℝ v y) •
      ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc) v) i) volume :=
    fun i => (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 3) i).integrable_comp (hint i)
  simp_rw [hc]
  rw [← integral_finsetSum _ (fun i _ => hint' i)]
  have hpt : ∀ v : Space, ∑ i : Fin 3, (𝐞 (inner ℝ v y) •
      ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc) v) i = 0 := by
    intro v
    have e : ∀ i : Fin 3, (𝐞 (inner ℝ v y) •
        ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i)) Mc) v) i =
        ((𝐞 (inner ℝ v y) : ℂ) * (2 * π * Complex.I)) * (((v i : ℝ) : ℂ) * m v i) := by
      intro i
      rw [Circle.smul_def, smul_apply, SchwartzMap.smulLeftCLM_apply_apply (hT i), hMf]
      simp [unitVector, EuclideanSpace.inner_single_right, Complex.real_smul]
      ring
    simp_rw [e]
    rw [← Finset.mul_sum, hm.2.2.2.2 v, mul_zero]
  simp_rw [hpt, integral_zero]

theorem rapid_of_symbol {m : Space → CSpace} (hm : IsNiceSymbol m) :
    ∃ G : 𝓢(Space, Space), ⇑G = niceField m ∧
      FourierTransform.fourier (fun x => complexifyVec (G x)) = m ∧ ∀ y, divergenceAt G y = 0 := by
  set Mc : 𝓢(Space, CSpace) := hm.2.1.toSchwartzMap hm.1 with hMc
  have hMf : ⇑Mc = m := rfl
  set H : 𝓢(Space, CSpace) := 𝓕⁻ Mc with hH
  set G : 𝓢(Space, Space) := SchwartzMap.postcompCLM realVec H with hG
  have hGf : ∀ x, G x = realVec (H x) := fun x => SchwartzMap.postcompCLM_apply _ _ _
  have hHf : ⇑H = 𝓕⁻ m := by rw [hH, SchwartzMap.fourierInv_coe, hMf]
  have hcG : (fun x => complexifyVec (G x)) = ⇑H := by
    funext x
    rw [hGf]
    exact Internal.NiceApprox.complexify_realVec_of_conj
      (Internal.NiceApprox.freqTrInv_conj Mc (fun ξ => by rw [hMf]; exact hm.2.2.2.1 ξ) x)
  refine ⟨G, ?_, ?_, ?_⟩
  · funext x
    rw [hGf, hHf]
    rfl
  · rw [hcG, ← SchwartzMap.fourier_coe, hH, FourierTransform.fourier_fourierInv_eq, hMf]
  · intro y
    have e1 : (⇑G) = fun x => realVec (H x) := funext hGf
    have hd : ∀ i : Fin 3, fderiv ℝ (⇑G) y (unitVector i) =
        realVec ((𝓕⁻ ((2 * π * Complex.I) • SchwartzMap.smulLeftCLM CSpace (inner ℝ · (unitVector i))
          Mc)) y) := by
      intro i
      have h := congrFun (Internal.NiceApprox.pd_clm realVec H.differentiable (unitVector i)) y
      rw [← e1] at h
      change fderiv ℝ (⇑G) y (unitVector i) = realVec (fderiv ℝ (⇑H) y (unitVector i)) at h
      rw [h, ← SchwartzMap.lineDerivOp_apply_eq_fderiv, hH, SchwartzMap.lineDerivOp_fourierInv_eq]
    unfold divergenceAt
    simp_rw [hd]
    have hre : ∀ (z : CSpace) (i : Fin 3), (realVec z) i = (z i).re := fun z i => rfl
    simp_rw [hre]
    rw [← Complex.re_sum, coord_sum_zero hm y, Complex.zero_re]

theorem integrable_inner_rapid {a : Space → Space} (ha : Continuous a) {C : ℝ}
    (hC : ∀ x, ‖a x‖ ≤ C) (b : 𝓢(Space, Space)) : Integrable (fun x => inner ℝ (a x) (b x)) := by
  refine ((b.integrable (μ := volume)).norm.const_mul C).mono'
    (ha.inner b.continuous).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs]
  calc |inner ℝ (a x) (b x)| ≤ ‖a x‖ * ‖b x‖ := abs_real_inner_le_norm _ _
    _ ≤ C * ‖b x‖ := mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem decay_bounds {f : Space → Space} (hf : IsDecayField f) :
    ∃ C : ℝ, (∀ x, ‖f x‖ ≤ C) ∧ ∀ x v, ‖fderiv ℝ f x v‖ ≤ C * ‖v‖ := by
  obtain ⟨-, -, C, hC⟩ := hf
  have hC0 : 0 ≤ C := by
    have h := (hC 0).1
    simp only [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have h1 : ∀ x : Space, (1 : ℝ) ≤ 1 + ‖x‖ := fun x => by linarith [norm_nonneg x]
  refine ⟨C, fun x => (hC x).1.trans (div_le_self hC0 (h1 x)), fun x v => ?_⟩
  refine (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right ((hC x).2.trans (div_le_self hC0 (one_le_pow₀ (h1 x)))) (norm_nonneg _))

theorem rapid_of_nice {φ : Space → Space} (hφ : IsNiceField φ) :
    ∃ S : 𝓢(Space, Space), ⇑S = φ := by
  obtain ⟨m, hm, rfl⟩ := hφ
  obtain ⟨G, hG, -⟩ := rapid_of_symbol hm
  exact ⟨G, hG⟩

theorem iteratedFDeriv_two_diag {φ : Space → Space} (hφ : ContDiff ℝ ∞ φ) (x v : Space) :
    iteratedFDeriv ℝ 2 φ x ![v, v] = fderiv ℝ (fun y => fderiv ℝ φ y v) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp) x
  rw [iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const v)]
  simp

theorem dir_eq (S : 𝓢(Space, Space)) (v : Space) :
    (fun y => fderiv ℝ (⇑S) y v) = ⇑((LineDeriv.lineDerivOp v S : 𝓢(Space, Space))) :=
  funext fun y => (SchwartzMap.lineDerivOp_apply_eq_fderiv v S y).symm

theorem dir_dir_eq (S : 𝓢(Space, Space)) (v : Space) :
    (fun x => fderiv ℝ (fun y => fderiv ℝ (⇑S) y v) x v) = ⇑((LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp v S : 𝓢(Space, Space)) : 𝓢(Space, Space))) := by
  rw [dir_eq]
  exact dir_eq _ v

theorem coord_ibp {f : Space → Space} (hf : ContDiff ℝ ∞ f) {C : ℝ} (hC1 : ∀ x, ‖f x‖ ≤ C)
    (hC2 : ∀ x v, ‖fderiv ℝ f x v‖ ≤ C * ‖v‖) (S : 𝓢(Space, Space)) (v : Space) :
    ∫ x, inner ℝ (fderiv ℝ f x v) (fderiv ℝ (⇑S) x v) =
      -∫ x, inner ℝ (f x) (fderiv ℝ (fun y => fderiv ℝ (⇑S) y v) x v) := by
  have hfd : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 := integrable_inner_rapid hfd (fun x => hC2 x v) ((LineDeriv.lineDerivOp v S : 𝓢(Space, Space)))
  have i2 := integrable_inner_rapid hf.continuous hC1 ((LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp v S : 𝓢(Space, Space)) : 𝓢(Space, Space)))
  have i3 := integrable_inner_rapid hf.continuous hC1 ((LineDeriv.lineDerivOp v S : 𝓢(Space, Space)))
  have e2 : (fun x => fderiv ℝ (⇑((LineDeriv.lineDerivOp v S : 𝓢(Space, Space)))) x v) = ⇑((LineDeriv.lineDerivOp v (LineDeriv.lineDerivOp v S : 𝓢(Space, Space)) : 𝓢(Space, Space))) := dir_eq _ v
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable
    (μ := volume) (B := innerSL ℝ) (v := v) (f := f) (g := ⇑((LineDeriv.lineDerivOp v S : 𝓢(Space, Space))))
    i1 (by
      refine i2.congr (ae_of_all _ fun x => ?_)
      simp only [← congrFun e2 x]
      rfl) i3
    (fun x _ => (hf.differentiable (by simp)) x)
    (fun x _ => ((LineDeriv.lineDerivOp v S : 𝓢(Space, Space))).differentiable x)
  change ∫ x, inner ℝ (f x) (fderiv ℝ (⇑((LineDeriv.lineDerivOp v S : 𝓢(Space, Space)))) x v) =
    -∫ x, inner ℝ (fderiv ℝ f x v) (((LineDeriv.lineDerivOp v S : 𝓢(Space, Space))) x) at key
  rw [dir_eq S v, key, neg_neg]
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem sum_coord_inner (L : Space →L[ℝ] Space) (v a : Space) :
    ∑ j : Fin 3, v j * inner ℝ (L (unitVector j)) a = inner ℝ (L v) a := by
  have hv : v = ∑ j : Fin 3, v j • unitVector j := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    simpa [unitVector] using this.symm
  conv_rhs => rw [hv]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, real_inner_smul_left]

end Internal.NicePairing

theorem niceEmbedSymbol : NiceEmbedSymbol := by
  intro m hm
  obtain ⟨G, hG, hF, hdiv⟩ := Internal.NicePairing.rapid_of_symbol hm
  have h := Internal.NiceApprox.embed_rapid fieldOpRealized_holds embedMem_holds G hdiv
  rw [hF, hG] at h
  exact h

open Internal.NicePairing in
theorem nicePairingByParts : NicePairingByParts := by
  intro f φ hf hφ
  obtain ⟨S, rfl⟩ := rapid_of_nice hφ
  obtain ⟨C, hC1, hC2⟩ := decay_bounds hf
  have hfs := hf.1
  have hφs : ContDiff ℝ ∞ (⇑S) := S.smooth ⊤
  have hfd : ∀ v, Continuous (fun x => fderiv ℝ f x v) := fun v =>
    (hfs.continuous_fderiv (by simp)).clm_apply continuous_const
  have I1 : ∀ i : Fin 3, Integrable (fun x => inner ℝ (fderiv ℝ f x (unitVector i))
      (fderiv ℝ (⇑S) x (unitVector i))) := by
    intro i
    have h := integrable_inner_rapid (hfd (unitVector i)) (fun x => hC2 x (unitVector i))
      ((LineDeriv.lineDerivOp (unitVector i) S : 𝓢(Space, Space)))
    simpa only [SchwartzMap.lineDerivOp_apply_eq_fderiv] using h
  have I2 : ∀ i : Fin 3, Integrable (fun x => inner ℝ (f x)
      (fderiv ℝ (fun y => fderiv ℝ (⇑S) y (unitVector i)) x (unitVector i))) := by
    intro i
    have h := integrable_inner_rapid hfs.continuous hC1 ((LineDeriv.lineDerivOp (unitVector i) (LineDeriv.lineDerivOp (unitVector i) S : 𝓢(Space, Space)) : 𝓢(Space, Space)))
    rw [← dir_dir_eq] at h
    exact h
  unfold gradientPairing fieldPairing negSsp sumSecondPartialsAt
  simp_rw [iteratedFDeriv_two_diag hφs, inner_neg_right, inner_sum]
  rw [integral_finsetSum _ (fun i _ => I1 i), integral_neg, integral_finsetSum _ (fun i _ => I2 i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => coord_ibp hfs hC1 hC2 S (unitVector i)

theorem niceAdvectionTrilinear : NiceAdvectionTrilinear := by
  intro f w hf _
  unfold advectionPairing trilinear
  refine integral_congr_ae ?_
  filter_upwards [velocityDecay_holds f hf, ae_all_iff.2 (fun j => partial_holds.1 f hf j)] with x hv hp
  simp only [hv, hp, partialField, advectionAt]
  exact (Internal.NicePairing.sum_coord_inner (fderiv ℝ f x) (f x) (w x)).symm

end Breakdown.Freq

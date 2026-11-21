import TorusEuler.PaperAppendixBLInfinity

/-! The Appendix B cutoff bound on all essentially bounded real velocity fields. -/

open Filter MeasureTheory UnitAddTorus
open scoped ComplexConjugate ContDiff ENNReal SchwartzMap

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- The real vector Fourier cutoff acting on an arbitrary representative of
an essentially bounded torus velocity field. -/
def realVectorFourierCutoffOfFunction (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : Labels → Vec3) (x : Labels) : Vec3 :=
  periodicRealPartVector (smoothFourierCutoff ψ Λ (periodicComplexifyVector ∘ g) x)

@[simp] theorem realVectorFourierCutoffOfFunction_continuous (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : C(Labels, Vec3)) :
    realVectorFourierCutoffOfFunction ψ Λ g = realVectorFourierCutoff ψ Λ g := rfl

/-- The real cutoff depends only on the almost-everywhere class of its input. -/
theorem realVectorFourierCutoffOfFunction_congr_ae (ψ : Vec3 → ℝ) (Λ : ℝ)
    {g h : Labels → Vec3} (hgh : g =ᵐ[unitTorusMeasure] h) :
    realVectorFourierCutoffOfFunction ψ Λ g = realVectorFourierCutoffOfFunction ψ Λ h := by
  have h := paperLemmaB1_cutoff_congr_ae ψ Λ
    (hgh.mono fun z hz => congrArg (fun u : Vec3 => periodicComplexifyVector u) hz)
  exact congrArg (fun f : Labels → ComplexEuclideanVec3 => periodicRealPartVector ∘ f) h

/-- The real output is continuous for every representative, by finite Fourier synthesis. -/
theorem continuous_realVectorFourierCutoffOfFunction (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : Labels → Vec3) : Continuous (realVectorFourierCutoffOfFunction ψ Λ g) := by
  refine periodicRealPartVector.continuous.comp ?_
  unfold smoothFourierCutoff finiteFourierSum
  exact continuous_finsetSum _ fun k _ => (mFourier k).continuous.smul continuous_const

theorem memLp_realVectorFourierCutoffOfFunction (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : Labels → Vec3) : MemLp (realVectorFourierCutoffOfFunction ψ Λ g) ∞ unitTorusMeasure :=
  (continuous_realVectorFourierCutoffOfFunction ψ Λ g).memLp_top_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) _

private theorem norm_realPart_le (x : ComplexEuclideanVec3) :
    ‖periodicRealPartVector x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [periodicRealPartVector_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (x i)) _

private theorem norm_complexify (x : Vec3) : ‖periodicComplexifyVector x‖ = ‖x‖ := by
  simp only [EuclideanSpace.norm_eq, periodicComplexifyVector_apply, Complex.norm_real]

/-- The exact kernel mass bounds the pointwise real cutoff on essentially
bounded, strongly measurable inputs. -/
theorem paperLemmaB1_realCutoff_aeBound {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → Vec3) (hg : Integrable g unitTorusMeasure) {M : ℝ}
    (hM : 0 ≤ M) (hbound : ∀ᵐ z ∂unitTorusMeasure, ‖g z‖ ≤ M) (x : Labels) :
    ‖realVectorFourierCutoffOfFunction ψ Λ g x‖ ≤
      (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) * M := by
  have hComplexBound : ∀ᵐ z ∂unitTorusMeasure, ‖(periodicComplexifyVector ∘ g) z‖ ≤ M := by
    simpa only [Function.comp_apply, norm_complexify] using hbound
  exact (norm_realPart_le _).trans (paperLemmaB1_cutoff_aeBound hsupp hsmooth hΛ
    (periodicComplexifyVector ∘ g) (periodicComplexifyVector.integrable_comp hg) hM hComplexBound x)

/-- Lemma B.1 on the entire real velocity essential-supremum space, with
the same scale-independent constant as for continuous fields. -/
theorem paperLemmaB1_realCutoff_LInfinity {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → Vec3) (hg : MemLp g ∞ unitTorusMeasure) :
    eLpNormEssSup (realVectorFourierCutoffOfFunction ψ Λ g) unitTorusMeasure ≤
      ENNReal.ofReal (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) *
        eLpNormEssSup g unitTorusMeasure := by
  have h := eLpNormEssSup_le_of_ae_bound (ae_of_all unitTorusMeasure
    (paperLemmaB1_realCutoff_aeBound hsupp hsmooth hΛ g (hg.integrable (by simp))
      (lpNorm_nonneg (f := g) (p := ∞) (μ := unitTorusMeasure)) (ae_le_lpNorm_exponent_top hg)))
  simpa only [ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _),
    ofReal_lpNorm hg, eLpNorm_exponent_top] using h

section RealBanach

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem integrable_continuous_smul {𝕜 G : Type*} [RCLike 𝕜]
    [NormedAddCommGroup G] [NormedSpace 𝕜 G] {k : Labels → 𝕜} {f : Labels → G}
    (hk : Continuous k) (hf : Integrable f unitTorusMeasure) :
    Integrable (fun z => k z • f z) unitTorusMeasure := by
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hk.continuousOn
  exact hf.bdd_smul M hk.aestronglyMeasurable (ae_of_all unitTorusMeasure fun z => hM z (Set.mem_univ _))

/-- The torus cutoff on a real Banach space, defined using the real part of
the spectral kernel. For an even symbol this has the prescribed Fourier
multiplier after testing by real continuous linear functionals. -/
def realBanachFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : Labels → V) (x : Labels) : V :=
  ∫ z, (appendixCutoffKernel ψ Λ x z).re • g z ∂unitTorusMeasure

omit [CompleteSpace V] in
/-- The cutoff depends only on the almost-everywhere class of the input. -/
theorem realBanachFourierCutoff_congr_ae (ψ : Vec3 → ℝ) (Λ : ℝ) {g h : Labels → V}
    (hgh : g =ᵐ[unitTorusMeasure] h) :
    realBanachFourierCutoff ψ Λ g = realBanachFourierCutoff ψ Λ h := by
  funext x
  exact integral_congr_ae (hgh.mono fun z hz =>
    congrArg (fun v => (appendixCutoffKernel ψ Λ x z).re • v) hz)

omit [CompleteSpace V] in
/-- The real cutoff of integrable input has a continuous representative. -/
theorem continuous_realBanachFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : Labels → V)
    (hg : Integrable g unitTorusMeasure) : Continuous (realBanachFourierCutoff ψ Λ g) := by
  have hK : Continuous (fun p : Labels × Labels => appendixCutoffKernel ψ Λ p.1 p.2) := by
    unfold appendixCutoffKernel
    exact continuous_finsetSum _ fun k _ =>
      (continuous_const.mul ((mFourier k).continuous.comp continuous_fst)).mul
        ((mFourier (-k)).continuous.comp continuous_snd)
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hK.continuousOn
  have hm (x : Labels) : AEStronglyMeasurable
      (fun z => (appendixCutoffKernel ψ Λ x z).re • g z) unitTorusMeasure :=
    (integrable_continuous_smul (Complex.continuous_re.comp
      (continuous_appendixCutoffKernel ψ Λ x)) hg).aestronglyMeasurable
  unfold realBanachFourierCutoff
  refine continuous_of_dominated hm (fun x => ae_of_all unitTorusMeasure fun z => ?_)
    (hg.norm.const_mul M) (ae_of_all unitTorusMeasure fun z => ?_)
  · rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      ((Complex.abs_re_le_norm _).trans (hM (x, z) (Set.mem_univ _))) (norm_nonneg _)
  · exact (Complex.continuous_re.comp (hK.comp (continuous_id.prodMk continuous_const))).smul
      continuous_const

omit [CompleteSpace V] in
theorem memLp_realBanachFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : Labels → V)
    (hg : MemLp g ∞ unitTorusMeasure) :
    MemLp (realBanachFourierCutoff ψ Λ g) ∞ unitTorusMeasure :=
  (continuous_realBanachFourierCutoff ψ Λ g (hg.integrable (by simp))).memLp_top_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _) _

/-- The real convolution agrees with the existing real velocity construction. -/
theorem realBanachFourierCutoff_vec_eq (ψ : Vec3 → ℝ) (Λ : ℝ) (g : Labels → Vec3)
    (hg : Integrable g unitTorusMeasure) :
    realBanachFourierCutoff ψ Λ g = realVectorFourierCutoffOfFunction ψ Λ g := by
  funext x
  have hgi := periodicComplexifyVector.integrable_comp hg
  have hK := integrable_continuous_smul (continuous_appendixCutoffKernel ψ Λ x) hgi
  change (∫ z, (appendixCutoffKernel ψ Λ x z).re • g z ∂unitTorusMeasure) =
    periodicRealPartVector (smoothFourierCutoff ψ Λ (fun z => periodicComplexifyVector (g z)) x)
  rw [smoothFourierCutoff_eq_integral_appendixKernel ψ Λ _ hgi x,
    ← periodicRealPartVector.integral_comp_comm hK]
  congr 1
  funext z
  apply PiLp.ext
  intro i
  simp [Complex.mul_re, PiLp.smul_apply, smul_eq_mul]

/-- Testing the real operator by a bounded real linear functional gives the
corresponding scalar Fourier multiplier for every even symbol. -/
theorem realBanachFourierCutoff_scalarization {ψ : Vec3 → ℝ} (heven : Function.Even ψ)
    (Λ : ℝ) (g : Labels → V) (hg : Integrable g unitTorusMeasure) (l : V →L[ℝ] ℝ) (x : Labels) :
    (l (realBanachFourierCutoff ψ Λ g x) : ℂ) =
      smoothFourierCutoff ψ Λ (fun z => (l (g z) : ℂ)) x := by
  let K := appendixCutoffKernel ψ Λ x
  let f : Labels → ℂ := fun z => (l (g z) : ℂ)
  have hc := continuous_appendixCutoffKernel ψ Λ x
  have hf : Integrable f unitTorusMeasure := (Complex.ofRealCLM.comp l).integrable_comp hg
  have hReal : Integrable (fun z => (K z).re • g z) unitTorusMeasure :=
    integrable_continuous_smul (Complex.continuous_re.comp hc) hg
  have hComplex := integrable_continuous_smul hc hf
  change _ = smoothFourierCutoff ψ Λ f x
  calc
    _ = ((smoothFourierCutoff ψ Λ f x).re : ℂ) := by
      rw [smoothFourierCutoff_eq_integral_appendixKernel ψ Λ f hf x]
      apply congrArg Complex.ofReal
      change l (∫ z, (K z).re • g z ∂unitTorusMeasure) =
        Complex.reCLM (∫ z, K z • f z ∂unitTorusMeasure)
      rw [← l.integral_comp_comm hReal, ← Complex.reCLM.integral_comp_comm hComplex]
      congr 1
      funext z
      simp [K, f, smul_eq_mul, Complex.mul_re]
    _ = _ := Complex.conj_eq_iff_re.mp
      (conj_smoothFourierCutoff_of_real heven Λ (fun z => Complex.conj_ofReal (l (g z))) x)

omit [CompleteSpace V] in
/-- The real kernel obeys the same pointwise bound for every real Banach space. -/
theorem paperLemmaB1_realBanachCutoff_aeBound {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → V) {M : ℝ} (hM : 0 ≤ M)
    (hbound : ∀ᵐ z ∂unitTorusMeasure, ‖g z‖ ≤ M) (x : Labels) :
    ‖realBanachFourierCutoff ψ Λ g x‖ ≤
      (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) * M := by
  let K := appendixCutoffKernel ψ Λ x
  have hKI : Integrable (fun z => ‖K z‖) unitTorusMeasure :=
    (continuous_appendixCutoffKernel ψ Λ x).norm.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold realBanachFourierCutoff
  calc
    _ ≤ ∫ z, ‖(K z).re • g z‖ ∂unitTorusMeasure := norm_integral_le_integral_norm _
    _ ≤ ∫ z, ‖K z‖ * M ∂unitTorusMeasure := by
      refine integral_mono_of_nonneg (ae_of_all unitTorusMeasure fun _ => norm_nonneg _)
        (hKI.mul_const M) ?_
      filter_upwards [hbound] with z hz
      rw [norm_smul]
      exact mul_le_mul (Complex.abs_re_le_norm _) hz (norm_nonneg _) (norm_nonneg _)
    _ = (∫ z, ‖K z‖ ∂unitTorusMeasure) * M := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (norm_appendixCutoffKernel_integral_le hsupp hsmooth hΛ x) hM

omit [CompleteSpace V] in
/-- The cutoff has a dimension-free bound on real Banach-valued L∞. -/
theorem paperLemmaB1_realBanachCutoff_LInfinity {ψ : Vec3 → ℝ}
    (hsupp : ∀ ξ, 2 < ‖ξ‖ → ψ ξ = 0) (hsmooth : ContDiff ℝ ∞ ψ) {Λ : ℝ}
    (hΛ : 0 < Λ) (g : Labels → V) (hg : MemLp g ∞ unitTorusMeasure) :
    eLpNormEssSup (realBanachFourierCutoff ψ Λ g) unitTorusMeasure ≤
      ENNReal.ofReal (∫ y, ‖(cutoffSchwartzKernel hsupp hsmooth : Vec3 → ℂ) y‖) *
        eLpNormEssSup g unitTorusMeasure := by
  have h := eLpNormEssSup_le_of_ae_bound (ae_of_all unitTorusMeasure
    (paperLemmaB1_realBanachCutoff_aeBound hsupp hsmooth hΛ g
      (lpNorm_nonneg (f := g) (p := ∞) (μ := unitTorusMeasure)) (ae_le_lpNorm_exponent_top hg)))
  simpa only [ENNReal.ofReal_mul (integral_nonneg fun _ => norm_nonneg _),
    ofReal_lpNorm hg, eLpNorm_exponent_top] using h

end RealBanach

end

end TorusEuler

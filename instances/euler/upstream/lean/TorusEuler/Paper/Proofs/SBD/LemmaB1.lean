import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.SBD.Library.Holder
import TorusEuler.TruncatedParentProjectedMomentum

/-! # Proof of Lemma B.1 (the frequency cutoff)

Conditional proof `Paper.Proof.lemma_B_1` of `Paper.Statement.lemma_B_1`
(`cc:uf:trunc:lem:cutoff`, sections/appB_cutoff.tex:12-56 of the latest
manuscript). Lemma B.1 is a leaf of the proof spine: its TeX proof cites no
other numbered result (only the external reference to Tao's Euclidean
Bernstein inequalities, whose content the library proves), so the Lean proof
has no hypotheses. -/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff ENNReal

namespace TorusEuler.Paper

open AppendixB AppendixD

/-- Proof of **Lemma B.1** (`cc:uf:trunc:lem:cutoff`), following
sections/appB_cutoff.tex:29-55. The TeX proof cites no numbered result, so this
leaf has no hypotheses. The constants are those of the convolution kernel
`K = ψ̌` (`cutoffSchwartzKernel`), as in the TeX: `Cop = ‖K‖_{L¹}`,
`C_m = 4^m ∑_{β} ‖∂^β K‖_{L¹}` (sum over nondecreasing words `β` of length `m`),
and `C_M = cutoffHolderTailUniformConstant K M` (built from the moments
`∫ |y|^k |K(y)| dy`); all depend only on the index and on `ψ`.

* appB:30-31 (scalar, even, time-independent symbol): the multiplier identity
  (`mFourierCoeff_smoothFourierCutoff`), parity (`smoothFourierCutoff_neg_arg`,
  `paperLemmaB1_realCutoff_parity`), divergence freeness
  (`divergence_free_lift_realVectorFourierCutoff`) and commutation with
  derivatives. For complex fields the commutation of every coordinate word
  `∂^β` follows from the convolution representation of the derivative
  (`paperLemmaB1_cutoff_commutes_contDiff`) and of `S_Λ d`
  (`liftConvolution_cutoffSchwartzKernel`), by moving the evaluation at the
  directions `e_β` inside the Bochner integral; for real velocities by
  `fderiv_lift_realVectorFourierCutoff_single`, and in time by
  `hasDerivWithinAt_realVectorFourierCutoff_time`.
* appB:32 (support gives the frequency bound): `mFourierCoeff_smoothFourierCutoff_eq_zero`
  and, for real fields, the vanishing of `ψ` outside the ball of radius `2`.
* appB:32-39 (convolution with `K_Λ`, `‖K_Λ‖_{L¹} = ‖K‖_{L¹}`): the
  `L^∞`, uniform and `C^{0,1/2}` operator bounds `paperLemmaB1_cutoff_LInfinity`,
  `paperLemmaB1_cutoff_sup`, `paperLemmaB1_cutoff_holder`,
  `paperLemmaB1_realCutoff_sup`; the real `C^{0,1/2}` bound is the complex one
  composed with the complexification and the real part, both contractions
  (`Lib.SBD.spatialHolderHalf_comp_contraction'`).
* appB:40-43, (B.1) `cc:uf:trunc:eq:lp`: `f = S_{4Λ} f` and
  `‖∂^β K_{4Λ}‖_{L¹} = (4Λ)^{|β|} ‖∂^β K‖_{L¹}`, i.e. the pointwise bound
  `bernstein_lift_of_real_band` for each word, summed over the nondecreasing
  words of length `m`.
* appB:45-55, (B.2) `cc:uf:trunc:eq:tail`: vanishing moments and Taylor's
  formula, `spatialHolderHalfNorm_cutoffTail` (complex) and
  `spatialHolderHalfNorm_realVectorCutoffTail` (real). -/
theorem Proof.lemma_B_1 : Statement.lemma_B_1 := by
  intro ψ hψ
  let K := cutoffSchwartzKernel hψ.eq_zero hψ.smooth
  let Cb : ℕ → ℝ := fun m => (4 : ℝ) ^ m *
    ∑ β ∈ Finset.univ.filter (fun β : Fin m → Fin 3 => Monotone β),
      ∫ y, ‖iteratedFDeriv ℝ m (K : Vec3 → ℂ) y (fun i => EuclideanSpace.single (β i) 1)‖
  refine ⟨∫ y, ‖(K : Vec3 → ℂ) y‖, Cb, fun M => cutoffHolderTailUniformConstant K M,
    integral_nonneg fun _ => norm_nonneg _,
    fun m => mul_nonneg (by positivity)
      (Finset.sum_nonneg fun _ _ => integral_nonneg fun _ => norm_nonneg _),
    fun M => by unfold cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment; positivity,
    ?_⟩
  intro Λ hΛ
  refine ⟨?_, ?_, ?_⟩
  · -- (i) complex-Banach-valued fields
    intro E _ _ _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g k
      exact mFourierCoeff_smoothFourierCutoff hΛ hψ.eq_zero g k
    · intro m β g d hg hd x
      have hrep := paperLemmaB1_cutoff_commutes_contDiff hψ.eq_zero hψ.smooth hΛ g hg
      let F := iteratedFDeriv ℝ m (fun y => g (toUnitTorus y))
      let KΛ := scaledLiftKernel Λ (K : Vec3 → ℂ)
      have hKΛ : Integrable KΛ := integrable_scaledLiftKernel hΛ K.integrable
      have hPer : SpatiallyPeriodic (fun y => g (toUnitTorus y)) := fun n x =>
        congrArg g ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
      have hFc : Continuous F := hg.continuous_iteratedFDeriv (by exact_mod_cast le_rfl)
      obtain ⟨Mb, hMb⟩ : ∃ Mb, ∀ z, ‖F z‖ ≤ Mb := by
        obtain ⟨M, hM⟩ := isCompact_centeredCell.exists_bound_of_continuousOn hFc.continuousOn
        refine ⟨M, fun z => ?_⟩
        obtain ⟨n, hn⟩ := exists_sub_latticeVector_mem_centeredCell z
        have hEq : F z = F (z - latticeVector n) := by
          calc
            F z = iteratedFDeriv ℝ m (fun y => g (toUnitTorus y))
                (z - latticeVector n + latticeVector n) := by rw [sub_add_cancel]
            _ = iteratedFDeriv ℝ m (fun y => g (toUnitTorus (y + latticeVector n)))
                (z - latticeVector n) :=
              (iteratedFDeriv_comp_add_right m (latticeVector n) (z - latticeVector n)).symm
            _ = _ := by rw [funext (hPer n)]
        exact (congrArg norm hEq).le.trans (hM _ hn)
      have hint : Integrable (fun y => KΛ y • F (x - y)) :=
        integrable_liftConvolution hKΛ hFc hMb x
      let L := ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Vec3) E
        (fun i => EuclideanSpace.single (β i) 1)
      rw [hrep, ← liftConvolution_cutoffSchwartzKernel hψ.eq_zero hψ.smooth hΛ d x]
      change L (∫ y, KΛ y • F (x - y)) = ∫ y, KΛ y • d (toUnitTorus (x - y))
      rw [← L.integral_comp_comm hint]
      congr 1
      funext y
      simp [L, F, hd]
    · intro g c hg
      exact smoothFourierCutoff_neg_arg hψ.even Λ c hg
    · intro g k hk
      exact mFourierCoeff_smoothFourierCutoff_eq_zero ψ Λ g hk
    · intro g hg
      exact paperLemmaB1_cutoff_LInfinity hψ.eq_zero hψ.smooth hΛ g hg
    · intro g
      exact paperLemmaB1_cutoff_sup hψ.eq_zero hψ.smooth hΛ g
    · intro g hg
      exact paperLemmaB1_cutoff_holder hψ.eq_zero hψ.smooth hΛ g hg
    · intro M s hs g hg
      exact spatialHolderHalfNorm_cutoffTail hψ.eq_zero hψ.smooth hψ.eq_one hΛ g hs hg
  · -- (ii) real velocity fields
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro g k
      rw [mFourierCoeff_realVectorFourierCutoff_of_even hψ.even]
      split_ifs with hk
      · rfl
      · have hscaled : 2 < ‖Λ⁻¹ • latticeVector k‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), ← div_eq_inv_mul,
            lt_div_iff₀ hΛ]
          simpa using hk
        rw [hψ.eq_zero _ hscaled, zero_smul]
    · intro g d i hg hd x
      exact fderiv_lift_realVectorFourierCutoff_single ψ Λ g d i hg hd x
    · intro a b hab V hV g gt hrep hrept t ht x
      exact hasDerivWithinAt_realVectorFourierCutoff_time hab hV g gt hrep hrept ψ Λ ht x
    · intro g c hg
      exact paperLemmaB1_realCutoff_parity hψ.even Λ c g hg
    · intro g hg hdiv
      exact divergence_free_lift_realVectorFourierCutoff hψ.even Λ g hg hdiv
    · intro g k hk
      have hk' : k ∉ frequencyBand (2 * Λ) := by simpa using hk
      rw [mFourierCoeff_realVectorFourierCutoff_of_even hψ.even]
      simp only [hk', ↓reduceIte]
    · intro g
      exact paperLemmaB1_realCutoff_sup hψ.eq_zero hψ.smooth hΛ g
    · intro g hg
      let gc : C(UnitAddTorus (Fin 3), ComplexEuclideanVec3) :=
        ⟨fun z => periodicComplexifyVector (g z),
          periodicComplexifyVector.continuous.comp g.continuous⟩
      have hcx (a : Vec3) : ‖periodicComplexifyVector a‖ ≤ ‖a‖ := by
        simp only [EuclideanSpace.norm_eq, periodicComplexifyVector_apply, Complex.norm_real,
          le_refl]
      have hre (a : ComplexEuclideanVec3) : ‖periodicRealPartVector a‖ ≤ ‖a‖ := by
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        apply Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
        rw [periodicRealPartVector_apply]
        exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (a i)) _
      have hc := Lib.SBD.spatialHolderHalf_comp_contraction' periodicComplexifyVector hcx hg
      change SpatialHolderHalf 0 (fun x => gc (toUnitTorus x)) ∧
        spatialHolderHalfNorm 0 (fun x => gc (toUnitTorus x)) ≤ _ at hc
      have hS := paperLemmaB1_cutoff_holder hψ.eq_zero hψ.smooth hΛ gc hc.1
      have hr := Lib.SBD.spatialHolderHalf_comp_contraction' periodicRealPartVector hre hS.1
      have heq : (periodicRealPartVector ∘ fun x => smoothFourierCutoff ψ Λ gc (toUnitTorus x)) =
          fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x) := rfl
      rw [heq] at hr
      refine ⟨hr.1, hr.2.trans (hS.2.trans ?_)⟩
      exact mul_le_mul_of_nonneg_left hc.2 (integral_nonneg fun _ => norm_nonneg _)
    · intro M s hs g hg
      exact spatialHolderHalfNorm_realVectorCutoffTail hψ.eq_zero hψ.smooth hψ.eq_one hΛ g hs hg
  · -- (B.1) for fields with values in a real normed space
    intro m V _ _ g hband
    have hpt (β : Fin m → Fin 3) (x : Vec3) :
        ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
            (fun i => EuclideanSpace.single (β i) 1)‖ ≤
          (4 * Λ) ^ m * (∫ y, ‖iteratedFDeriv ℝ m (K : Vec3 → ℂ) y
            (fun i => EuclideanSpace.single (β i) 1)‖) * ‖g‖ :=
      bernstein_lift_of_real_band hψ.eq_zero hψ.smooth hψ.eq_one hΛ g hband _ x
    refine ⟨fun β => ⟨_, forall_mem_range.mpr (hpt β)⟩, ?_⟩
    calc
      _ ≤ ∑ β ∈ Finset.univ.filter (fun β : Fin m → Fin 3 => Monotone β),
          (4 * Λ) ^ m * (∫ y, ‖iteratedFDeriv ℝ m (K : Vec3 → ℂ) y
            (fun i => EuclideanSpace.single (β i) 1)‖) * ‖g‖ :=
        Finset.sum_le_sum fun β _ => ciSup_le (hpt β)
      _ = _ := by
        simp only [Cb]
        rw [← Finset.sum_mul, ← Finset.mul_sum, mul_pow]
        ring

end TorusEuler.Paper

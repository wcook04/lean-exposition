import TorusEuler.CoframeDerivativeBounds
import TorusEuler.FlowHigherVariations
import TorusEuler.HalfHolderFourierMultiplier
import TorusEuler.HierarchyExponents
import TorusEuler.HierarchySourceBounds
import TorusEuler.TruncatedParentAdmissibility

/-! The band-limited parent residual in the weighted label norm of (5.10). -/

open Filter MeasureTheory Set UnitAddTorus
open scoped BigOperators ContDiff SchwartzMap

namespace TorusEuler

noncomputable section

private theorem norm_parentComplexify (v : Vec3) : ‖periodicComplexifyVector v‖ = ‖v‖ := by
  simp only [EuclideanSpace.norm_eq, periodicComplexifyVector_apply, Complex.norm_real]

private theorem norm_parentRealPart_le_one : ‖periodicRealPartVector‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [periodicRealPartVector_apply]
  exact pow_le_pow_left₀ (norm_nonneg _) (Complex.abs_re_le_norm (v i)) _

/-- The Fourier-band Bernstein estimate of Appendix B in Fréchet operator norm. -/
theorem exists_bandBernsteinJetBounds : ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
    ∀ (g : C(UnitAddTorus (Fin 3), Vec3)) {D A : ℝ}, 0 < D → 0 ≤ A → ‖g‖ ≤ A →
      (∀ k, 4 * D < ‖latticeVector k‖ →
        mFourierCoeff (fun z => periodicComplexifyVector (g z)) k = 0) →
      ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) ∧
      ∀ m : ℕ, ∀ x : Vec3,
        ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x‖ ≤ K m * A * D ^ m := by
  let ψ : Vec3 → ℝ := dyadicMultiplierCutoff
  have hout (ξ : Vec3) (h : 2 < ‖ξ‖) : ψ ξ = 0 := dyadicMultiplierCutoff_zero ξ h.le
  let Q := cutoffSchwartzKernel hout dyadicMultiplierCutoff_smooth
  let B (m : ℕ) : ℝ := ∫ y : Vec3, ‖iteratedFDeriv ℝ m (Q : Vec3 → ℂ) y‖
  have hB (m : ℕ) : 0 ≤ B m := integral_nonneg fun _ => norm_nonneg _
  have hInt (m : ℕ) : Integrable
      (fun y : Vec3 => ‖iteratedFDeriv ℝ m (Q : Vec3 → ℂ) y‖) := by
    simpa only [pow_zero, one_mul] using Q.integrable_pow_mul_iteratedFDeriv volume 0 m
  refine ⟨fun m => (4 : ℝ) ^ m * B m,
    fun m => mul_nonneg (by positivity) (hB m), ?_⟩
  intro g D A hD hA hg hband
  let gC : C(UnitAddTorus (Fin 3), ComplexEuclideanVec3) :=
    ⟨fun z => periodicComplexifyVector (g z), periodicComplexifyVector.continuous.comp g.continuous⟩
  have hgC : ‖gC‖ ≤ A := (ContinuousMap.norm_le gC hA).mpr fun z => by
    change ‖periodicComplexifyVector (g z)‖ ≤ A
    rw [norm_parentComplexify]
    exact (g.norm_coe_le_norm z).trans hg
  have hbandC : ∀ k, 4 * D < ‖latticeVector k‖ → mFourierCoeff gC k = 0 := hband
  have hC : ContDiff ℝ ∞ (fun x => gC (toUnitTorus x)) := by
    rw [← finiteFourierSum_mFourierCoeff_eq_of_band gC (4 * D) hbandC]
    exact contDiff_lift_finiteFourierSum _ _
  have hRe : (fun x => g (toUnitTorus x)) =
      periodicRealPartVector ∘ (fun x => gC (toUnitTorus x)) :=
    funext fun x => (periodicRealPartVector_complexifyVector (g (toUnitTorus x))).symm
  refine ⟨?_, ?_⟩
  · rw [hRe]
    exact periodicRealPartVector.contDiff.comp hC
  · intro m x
    have hJet : ‖iteratedFDeriv ℝ m (fun y => gC (toUnitTorus y)) x‖ ≤
        (4 * D) ^ m * B m * A := by
      refine ContinuousMultilinearMap.opNorm_le_bound
        (mul_nonneg (mul_nonneg (by positivity) (hB m)) hA) fun v => ?_
      have hProd : 0 ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
      have hDir : (∫ y : Vec3, ‖iteratedFDeriv ℝ m (Q : Vec3 → ℂ) y v‖) ≤
          B m * ∏ i, ‖v i‖ := by
        change _ ≤ (∫ y : Vec3, ‖iteratedFDeriv ℝ m (Q : Vec3 → ℂ) y‖) * _
        rw [← integral_mul_const]
        exact integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _)
          ((hInt m).mul_const _) (Eventually.of_forall fun y => (iteratedFDeriv ℝ m
            (Q : Vec3 → ℂ) y).le_opNorm v)
      calc
        _ ≤ (4 * D) ^ m * (∫ y : Vec3, ‖iteratedFDeriv ℝ m (Q : Vec3 → ℂ) y v‖) * ‖gC‖ :=
          bernstein_lift_of_band hout dyadicMultiplierCutoff_smooth dyadicMultiplierCutoff_unit
            hD gC hbandC v x
        _ ≤ (4 * D) ^ m * (B m * ∏ i, ‖v i‖) * A := by
          calc
            _ ≤ (4 * D) ^ m * (B m * ∏ i, ‖v i‖) * ‖gC‖ :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hDir (by positivity)) (norm_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left hgC
              (mul_nonneg (by positivity) (mul_nonneg (hB m) hProd))
        _ = _ := by ring
    rw [hRe]
    calc
      _ ≤ ‖periodicRealPartVector‖ * ‖iteratedFDeriv ℝ m (fun y => gC (toUnitTorus y)) x‖ :=
        periodicRealPartVector.norm_iteratedFDeriv_comp_left hC.contDiffAt (by simp)
      _ ≤ (4 * D) ^ m * B m * A := by
        exact (mul_le_mul_of_nonneg_right norm_parentRealPart_le_one
          (norm_nonneg _)).trans (by simpa only [one_mul] using hJet)
      _ = _ := by rw [mul_pow]; ring

/-- The physical parent residual pulled back by the actual forward label flow
is smooth and obeys the pointwise form of (5.7), with the scale factor `D ^ (6 * m)`. -/
theorem exists_parentResidualLabelJetBounds (V : ℕ → ℝ) (hV : ∀ m, 0 ≤ V m) :
    ∃ C : ℕ → ℝ, (∀ m, 0 ≤ C m) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D A : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        0 ≤ A → IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n ≥ 2, ∀ k, 2 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ V n * D ^ k) →
        ∀ R : ℝ → C(UnitAddTorus (Fin 3), Vec3),
          (∀ t ∈ Icc 0 T, ‖R t‖ ≤ A) →
          (∀ t ∈ Icc 0 T, ∀ k, 4 * D < ‖latticeVector k‖ →
            mFourierCoeff (fun z => periodicComplexifyVector (R t z)) k = 0) →
          ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (fun a => R t (toUnitTorus (X 0 t a))) ∧
            ∀ m : ℕ, ∀ a : Vec3,
              ‖iteratedFDeriv ℝ m (fun b => R t (toUnitTorus (X 0 t b))) a‖ ≤
                C m * A * D ^ (6 * m) := by
  obtain ⟨K, hK, hBernstein⟩ := exists_bandBernsteinJetBounds
  obtain ⟨F, hF, hFlow⟩ := exists_forward_flowJetBounds V hV
  let K₀ (m : ℕ) := ∑ i ∈ Finset.range (m + 1), K i
  let F₀ (m : ℕ) := 1 + ∑ i ∈ Finset.range (m + 1), F i
  have hK₀ (m : ℕ) : 0 ≤ K₀ m := Finset.sum_nonneg fun i _ => hK i
  have hF₀ (m : ℕ) : 1 ≤ F₀ m :=
    le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hF i)
  let C (m : ℕ) := (m.factorial : ℝ) * K₀ m * (F₀ m) ^ m
  have hC (m : ℕ) : 0 ≤ C m := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hK₀ m))
    (pow_nonneg (zero_le_one.trans (hF₀ m)) m)
  refine ⟨C, hC, ?_⟩
  intro U X T D A hT hT₁ hD hA hX hU hPer hJac hInv hVel R hR hBand t ht
  have hD₀ : 0 < D := zero_lt_one.trans_le hD
  obtain ⟨hRsmooth, hRjet⟩ := hBernstein (R t) hD₀ hA (hR t ht) (hBand t ht)
  have hXsmooth (m : ℕ) : ContDiff ℝ m (X 0 t) :=
    (hX.labelJets_evolve m hT hU hPer).1 t ht
  have hXinf : ContDiff ℝ ∞ (X 0 t) := contDiff_iff_forall_nat_le.mpr fun m _ => hXsmooth m
  refine ⟨hRsmooth.comp hXinf, fun m a => ?_⟩
  apply norm_iteratedFDeriv_parentComposition_le (hRsmooth.of_le (by simp)) (hXsmooth m)
    a hD (hF₀ m) (hK₀ m) hA
  · intro i hi him
    have hSum : F i ≤ F₀ m := by
      apply le_trans (Finset.single_le_sum (f := F) (fun j _ => hF j)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le him)))
      exact le_add_of_nonneg_left zero_le_one
    calc
      _ ≤ F i * D ^ (5 * i - 4) :=
        hFlow hT hT₁ hD hX hU hPer hJac hInv hVel i hi t ht a
      _ ≤ F₀ m * D ^ (5 * i) := mul_le_mul hSum
        (pow_le_pow_right₀ hD (Nat.sub_le _ _)) (pow_nonneg hD₀.le _) (zero_le_one.trans (hF₀ m))
  · intro i him
    have hSum : K i ≤ K₀ m := Finset.single_le_sum (f := K) (fun j _ => hK j)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le him))
    exact (hRjet i (X 0 t a)).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hSum hA) (pow_nonneg hD₀.le _))

/-- The preceding round's bound (T2) implies the parent-small residual
hypothesis (5.6) at the current frequency. -/
theorem parentResidual_invCube_le_parentSmall {Λ : ℝ} (hΛ : 1 ≤ Λ) :
    Λ ^ (-3 : ℝ) ≤ Λ ^ hierarchyMeanExponent 2 :=
  Real.rpow_le_rpow_of_exponent_le hΛ (by norm_num [hierarchyMeanExponent])

section LabelWord

variable {T G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Each weighted label derivative introduces one factor of the label radius. -/
theorem phaseOperatorWord_hierarchyLabelDirection_eq_smul
    (ell : ℝ) {f : Vec3 → G} (hf : ContDiff ℝ ∞ f) (w : List (Fin 3)) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection ell) w f x =
      ell ^ w.length • spatialDerivativeWord w f x := by
  change phaseOperatorWord (fun i (_ : Vec3) => ell • coordinateDirection i) w f x = _
  simpa only [spatialDerivativeWord, List.map_const', List.prod_replicate] using
    (phaseOperatorWord_scaled_directions (fun _ : Fin 3 => ell)
      (D := fun i (_ : Vec3) => coordinateDirection i) (fun _ => contDiff_const) hf w x)

private theorem norm_coordinateDirection_eq_one (i : Fin 3) : ‖coordinateDirection i‖ = 1 := by
  simp [coordinateDirection]

/-- The small label radius absorbs the factor of the parent scale in each
Fréchet derivative. -/
theorem norm_hierarchyLabelWord_le_of_iteratedFDeriv
    {ell D A C : ℝ} (hell : 0 ≤ ell) (hscale : ell * D ^ 6 ≤ 1)
    (hA : 0 ≤ A) (hC : 0 ≤ C) {f : Vec3 → G} (hf : ContDiff ℝ ∞ f)
    (w : List (Fin 3)) (x : Vec3)
    (hjet : ‖iteratedFDeriv ℝ w.length f x‖ ≤ C * A * D ^ (6 * w.length)) :
    ‖phaseOperatorWord (hierarchyLabelDirection ell) w f x‖ ≤ C * A := by
  have hD : 0 ≤ D ^ 6 := by
    rw [show (6 : ℕ) = 3 * 2 by decide, pow_mul]
    exact sq_nonneg _
  have hnorm : ‖spatialDerivativeWord w f x‖ ≤ ‖iteratedFDeriv ℝ w.length f x‖ := by
    rw [spatialDerivativeWord_eq_iteratedFDeriv hf]
    simpa only [norm_coordinateDirection_eq_one, Finset.prod_const_one, mul_one] using
      (iteratedFDeriv ℝ w.length f x).le_opNorm (fun i => coordinateDirection (w.get i))
  rw [phaseOperatorWord_hierarchyLabelDirection_eq_smul ell hf w x,
    norm_smul, Real.norm_of_nonneg (pow_nonneg hell _)]
  calc
    _ ≤ ell ^ w.length * ‖iteratedFDeriv ℝ w.length f x‖ :=
      mul_le_mul_of_nonneg_left hnorm (pow_nonneg hell _)
    _ ≤ ell ^ w.length * (C * A * D ^ (6 * w.length)) :=
      mul_le_mul_of_nonneg_left hjet (pow_nonneg hell _)
    _ = (ell * D ^ 6) ^ w.length * (C * A) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ _ := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (pow_le_one₀ (mul_nonneg hell hD) hscale) (mul_nonneg hC hA)

/-- The pointwise bounds give bounded jet ranges and the finite pure label
derivative norm of Proposition 5.1. -/
theorem hierarchyFiniteWordNorm_false_label_le_of_iteratedFDeriv
    {ell D A : ℝ} {C : ℕ → ℝ}
    (hell : 0 ≤ ell) (hscale : ell * D ^ 6 ≤ 1) (hA : 0 ≤ A)
    {f : T → Vec3 → G} (hf : ∀ t, ContDiff ℝ ∞ (f t)) (n : ℕ)
    (hC : ∀ m ≤ n, 0 ≤ C m)
    (hjets : ∀ m ≤ n, ∀ t x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ C m * A * D ^ (6 * m)) :
    (∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection ell) w f)) ∧
    hierarchyFiniteWordNorm False (hierarchyLabelDirection ell) n f ≤
      (∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, C w.length) * A := by
  have hterm (w : List (Fin 3)) (hw : w ∈ hierarchyAdmissibleWords (Fin 3) n) :
      ∀ r ∈ hierarchyJetValues False (hierarchyLabelDirection ell) w f, r ≤ C w.length * A := by
    have hn := (mem_hierarchyAdmissibleWords.mp hw).1
    rintro _ (rfl | ⟨t, x, rfl⟩ | ⟨hfalse, _⟩)
    · exact mul_nonneg (hC _ hn) hA
    · exact norm_hierarchyLabelWord_le_of_iteratedFDeriv hell hscale hA (hC _ hn) (hf t) w x
        (hjets w.length hn t x)
    · exact hfalse.elim
  refine ⟨fun w hw => ⟨C w.length * A, hterm w hw⟩, ?_⟩
  unfold hierarchyFiniteWordNorm
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hterm w hw)

end LabelWord

set_option maxHeartbeats 800000 in
/-- Equation (5.10) in the finite label norm used for the hierarchy. Its
constants depend only on the derivative order and the velocity jet constants. -/
theorem exists_parentResidualWeightedBounds (V : ℕ → ℝ) (hV : ∀ m, 0 ≤ V m) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D ℓ Λ : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        0 ≤ ℓ → ℓ * D ^ 6 ≤ 1 → 1 ≤ Λ → IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n ≥ 2, ∀ k, 2 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ V n * D ^ k) →
        ∀ R : ℝ → C(UnitAddTorus (Fin 3), Vec3),
          (∀ t ∈ Icc 0 T, ‖R t‖ ≤ Λ ^ hierarchyMeanExponent 2) →
          (∀ t ∈ Icc 0 T, ∀ k, 4 * D < ‖latticeVector k‖ →
            mFourierCoeff (fun z => periodicComplexifyVector (R t z)) k = 0) →
          ∀ n : ℕ,
            let f (t : Icc (0 : ℝ) T) (a : Vec3) := R t.val (toUnitTorus (X 0 t.val a))
            (∀ w ∈ hierarchyAdmissibleWords (Fin 3) n,
              BddAbove (hierarchyJetValues False (hierarchyLabelDirection ℓ) w f)) ∧
            hierarchyFiniteWordNorm False (hierarchyLabelDirection ℓ) n f ≤
              C n * Λ ^ hierarchyMeanExponent 2 := by
  obtain ⟨J, hJ, hjet⟩ := exists_parentResidualLabelJetBounds V hV
  let C (n : ℕ) := ∑ w ∈ hierarchyAdmissibleWords (Fin 3) n, J w.length
  refine ⟨C, fun n => Finset.sum_nonneg (fun w _ => hJ w.length), ?_⟩
  intro U X T D ℓ Λ hT hT₁ hD hℓ hscale hΛ hX hU hPer hJac hInv hVel R hR hBand n f
  have hA : 0 ≤ Λ ^ hierarchyMeanExponent 2 :=
    Real.rpow_nonneg (zero_le_one.trans hΛ) _
  have h := hjet (U := U) (X := X) hT hT₁ hD hA hX hU hPer hJac hInv hVel R hR hBand
  exact hierarchyFiniteWordNorm_false_label_le_of_iteratedFDeriv hℓ hscale hA
    (f := f) (fun t => (h t.val t.property).1) n (fun m _ => hJ m)
    (fun m _ t a => (h t.val t.property).2 m a)

end

end TorusEuler

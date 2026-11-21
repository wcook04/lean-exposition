import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.SBD.Statements

/-!
# S5a glue: operator-norm jets, coordinate words and Fourier bands

Calculus glue for the proof of Proposition 5.1 (and the other rows of package S5a):

* the operator norm of an iterated derivative on `ℝ³` is bounded by the sum of its
  values on coordinate directions (copy of a private library lemma, generalized to
  any target space), and each such value is the value of one nondecreasing
  coordinate word (symmetry of the derivatives of a smooth function), so that
  `‖D^m c(t,a)‖ ≤ 3^m |c|_m` for the coefficient size `|c|_m` of Appendix D;
* conversely, operator-norm jet bounds `‖D^m c‖ ≤ K_m 𝖣^{a(m+1)}` give the power
  bound (D.6) in the form `AppendixD.CoefficientPower` of the statement of Lemma D.2;
* a real vector field whose complexified Fourier coefficients vanish above a
  frequency has the same band in the sense of the statement of Lemma B.1
  (`RealNormedTorusFourierBand`: every scalar measurement is band limited).

None of these is the content of a numbered result: they translate between the
representations of the same norms and bands used by different statements. -/

open Set UnitAddTorus MeasureTheory
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

section Coordinates

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- A vector of `ℝ³` is the sum of its coordinates times the coordinate directions. -/
theorem sum_coordinateDirection (v : Vec3) : (∑ i, v i • coordinateDirection i) = v := by
  apply PiLp.ext
  intro j
  let ev := (EuclideanSpace.proj j : Vec3 →L[ℝ] ℝ)
  change ev (∑ i, v i • coordinateDirection i) = v j
  rw [map_sum]
  simp [ev, coordinateDirection, EuclideanSpace.single, PiLp.single_apply]

/-- The operator norm of a multilinear map on `ℝ³` is at most the sum of its values on
coordinate directions. Copy of the private `appendixOpNorm_le_coordinateSum`
(`TorusEuler/PaperAppendixDCoordinate.lean:37`), stated for any normed target space
instead of a normed algebra; same proof. -/
theorem opNorm_le_coordinateSum {m : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin m => Vec3) X) :
    ‖D‖ ≤ ∑ β : Fin m → Fin 3, ‖D (fun i => coordinateDirection (β i))‖ := by
  classical
  apply ContinuousMultilinearMap.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  intro p
  have h := D.toMultilinearMap.map_sum (fun j i => p j i • coordinateDirection i)
  have hsum : (fun j => ∑ i, p j i • coordinateDirection i) = p :=
    funext fun j => sum_coordinateDirection (p j)
  rw [hsum] at h
  change D p = ∑ β : Fin m → Fin 3, D (fun j => p j (β j) • coordinateDirection (β j)) at h
  rw [h, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β _ => ?_)
  rw [show D (fun j => p j (β j) • coordinateDirection (β j)) =
    (∏ j, p j (β j)) • D (fun j => coordinateDirection (β j)) from
      D.toMultilinearMap.map_smul_univ _ _, norm_smul, Real.norm_eq_abs, Finset.abs_prod, mul_comm]
  exact mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => abs_nonneg _)
    (fun j _ => PiLp.norm_apply_le (p j) (β j))) (norm_nonneg _)

/-- A linear map on `ℝ³` whose values on the coordinate directions are at most `M` has
operator norm at most `3M`. Copy of the private `norm_linearMap_le_of_coordinateBounds`
(`TorusEuler/ParentVelocityEstimates.lean:165`), for any target space; same proof. -/
theorem norm_linearMap_le_of_coordinateBounds {A : Vec3 →L[ℝ] X} {M : ℝ}
    (hM : 0 ≤ M) (hA : ∀ i, ‖A (coordinateDirection i)‖ ≤ M) : ‖A‖ ≤ 3 * M := by
  refine ContinuousLinearMap.opNorm_le_bound A (mul_nonneg (by norm_num) hM) fun x => ?_
  calc
    ‖A x‖ = ‖∑ i : Fin 3, x i • A (coordinateDirection i)‖ := by
      have heq := congrArg A (sum_coordinateDirection x)
      simp only [map_sum, map_smul] at heq
      exact congrArg norm heq.symm
    _ ≤ ∑ i : Fin 3, ‖x i • A (coordinateDirection i)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 3, M * ‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul, mul_comm]
      exact mul_le_mul (hA i) (PiLp.norm_apply_le x i) (norm_nonneg _) hM
    _ = _ := by simp; ring

/-- The unit label directions of Appendix D are the coordinate directions. -/
theorem labelDirection_one :
    hierarchyLabelDirection 1 = fun j (_ : Vec3) => coordinateDirection j := by
  funext j x
  exact one_smul ℝ (coordinateDirection j)

/-- The value of a coordinate word is the iterated derivative on the coordinate
directions of its letters. -/
theorem labelWord_eq_iteratedFDeriv {f : Vec3 → X} (hf : ContDiff ℝ ∞ f)
    (w : List (Fin 3)) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) w f x =
      iteratedFDeriv ℝ w.length f x (fun i => coordinateDirection (w.get i)) := by
  rw [labelDirection_one, phaseOperatorWord_constant_eq_iteratedFDeriv _ hf]

/-- The word of the letters `β 0, …, β (m-1)` is the iterated derivative on
`e_{β 0}, …, e_{β (m-1)}`. -/
theorem ofFnWord_eq_iteratedFDeriv {f : Vec3 → X} (hf : ContDiff ℝ ∞ f) {m : ℕ}
    (β : Fin m → Fin 3) (x : Vec3) :
    phaseOperatorWord (hierarchyLabelDirection 1) (List.ofFn β) f x =
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by
  rw [labelWord_eq_iteratedFDeriv hf]
  simp only [List.get_ofFn]
  have h (k : ℕ) (hk : k = m) :
      iteratedFDeriv ℝ k f x (fun j => coordinateDirection (β (Fin.cast hk j))) =
        iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) := by subst k; rfl
  exact h _ List.length_ofFn

/-- Symmetry of the derivatives of a smooth function: every coordinate component
`D^m f(x)(e_{β 0}, …, e_{β (m-1)})` is the value of one nondecreasing coordinate word
of length `m` (the sorted word of the letters of `β`). -/
theorem exists_sortedWord {f : Vec3 → X} (hf : ContDiff ℝ ∞ f) {m : ℕ} (β : Fin m → Fin 3) :
    ∃ w ∈ appendixCoefficientOrderWords m, ∀ x,
      iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j)) =
        phaseOperatorWord (hierarchyLabelDirection 1) w f x := by
  let w := (List.ofFn β).mergeSort (· ≤ ·)
  have hperm : w.Perm (List.ofFn β) := List.mergeSort_perm _ _
  have hlen : w.length = m := hperm.length_eq.trans List.length_ofFn
  refine ⟨w, Finset.mem_filter.mpr ⟨mem_hierarchyAdmissibleWords.mpr
    ⟨hlen.le, List.pairwise_mergeSort' (· ≤ ·) _⟩, hlen⟩, fun x => ?_⟩
  have hword := congrFun (phaseOperatorWord_constantDirections_perm coordinateDirection hf hperm) x
  rw [← ofFnWord_eq_iteratedFDeriv hf β x, labelDirection_one, ← hword]

/-- A nondecreasing coordinate word of length `m` is the word of a monotone map
`Fin m → Fin 3`. -/
theorem exists_monotone_of_orderWord {m : ℕ} {w : List (Fin 3)}
    (hw : w ∈ appendixCoefficientOrderWords m) :
    ∃ β : Fin m → Fin 3, Monotone β ∧ List.ofFn β = w := by
  obtain ⟨hadm, hlen⟩ := Finset.mem_filter.mp hw
  have hsorted := (mem_hierarchyAdmissibleWords.mp hadm).2
  refine ⟨fun i => w.get (Fin.cast hlen.symm i), fun i j hij => ?_, ?_⟩
  · exact List.Pairwise.rel_get_of_le hsorted (a := Fin.cast hlen.symm i) (b := Fin.cast hlen.symm j) hij
  · apply List.ext_get
    · simp [hlen]
    · intro n h₁ h₂
      simp

end Coordinates

/-! ## Operator-norm jets and the coefficient sizes `|c|_m` of Appendix D -/

section CoefficientJets

variable {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `‖D^m c(t,x)‖ ≤ 3^m |c|_m`: the operator norm of the `m`-th label derivative is
bounded by the coefficient size `|c|_m = ∑_{|β|=m} sup |∂^β c|` of Appendix D. -/
theorem norm_iteratedFDeriv_le_coefficientOrderNorm {c : I → Vec3 → X}
    (hc : ∀ t, ContDiff ℝ ∞ (c t)) {m : ℕ}
    (hb : ∀ w ∈ appendixCoefficientOrderWords m,
      BddAbove (hierarchyJetValues False (hierarchyLabelDirection 1) w c))
    (t : I) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (c t) x‖ ≤ 3 ^ m * AppendixD.coefficientOrderNorm m c := by
  refine (opNorm_le_coordinateSum _).trans ?_
  have hterm (β : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m (c t) x (fun j => coordinateDirection (β j))‖ ≤
        AppendixD.coefficientOrderNorm m c := by
    obtain ⟨w, hw, hwx⟩ := exists_sortedWord (hc t) β
    rw [hwx x]
    unfold AppendixD.coefficientOrderNorm
    exact (le_csSup (hb w hw) (Or.inr (Or.inl ⟨t, x, rfl⟩))).trans
      (Finset.single_le_sum (fun v hv => le_csSup (hb v hv) (Or.inl rfl)) hw)
  calc
    _ ≤ ∑ _β : Fin m → Fin 3, AppendixD.coefficientOrderNorm m c :=
      Finset.sum_le_sum fun β _ => hterm β
    _ = 3 ^ m * AppendixD.coefficientOrderNorm m c := by
      simp [Finset.card_univ]

/-- The power bound (D.6) in the form of Appendix D gives operator-norm jet bounds
with the same exponent: `‖D^m c(t,x)‖ ≤ 3^m C_m 𝖣^{a(m+1)}`. -/
theorem norm_iteratedFDeriv_le_of_coefficientPower {C : ℕ → ℝ} {D : ℝ} {a : ℕ}
    {c : I → Vec3 → X} (hc : AppendixD.CoefficientPower C D a c) (m : ℕ) (t : I) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (c t) x‖ ≤ 3 ^ m * C m * D ^ (a * (m + 1)) := by
  refine (norm_iteratedFDeriv_le_coefficientOrderNorm hc.1 (hc.2.1 m) t x).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (hc.2.2 m) (by positivity)

/-- Operator-norm jet bounds `‖D^m c(t,x)‖ ≤ K_m 𝖣^{a(m+1)}` of a field smooth in the
label give the power bound (D.6) in the form of Appendix D, with constants
`#{words of order m} · K_m`. -/
theorem coefficientPower_of_jets {c : I → Vec3 → X} {K : ℕ → ℝ} {D : ℝ} {a : ℕ}
    (hD : 0 ≤ D) (hK : ∀ m, 0 ≤ K m) (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hj : ∀ m t x, ‖iteratedFDeriv ℝ m (c t) x‖ ≤ K m * D ^ (a * (m + 1))) :
    AppendixD.CoefficientPower (fun m => (appendixCoefficientOrderWords m).card * K m) D a c := by
  have hval (m : ℕ) (w : List (Fin 3)) (hw : w ∈ appendixCoefficientOrderWords m) :
      K m * D ^ (a * (m + 1)) ∈
        upperBounds (hierarchyJetValues False (hierarchyLabelDirection 1) w c) := by
    have hlen := (Finset.mem_filter.mp hw).2
    rintro y (rfl | ⟨t, x, rfl⟩ | ⟨hH, _⟩)
    · exact mul_nonneg (hK m) (pow_nonneg hD _)
    · rw [labelWord_eq_iteratedFDeriv (hc t)]
      refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
      have hprod : ∏ i, ‖coordinateDirection (w.get i)‖ = 1 := by
        simp [coordinateDirection]
      rw [hprod, mul_one]
      calc
        _ ≤ K w.length * D ^ (a * (w.length + 1)) := hj _ t x
        _ = K m * D ^ (a * (m + 1)) := by rw [hlen]
    · exact hH.elim
  refine ⟨hc, fun m w hw => ⟨_, hval m w hw⟩, fun m => ?_⟩
  unfold AppendixD.coefficientOrderNorm
  calc
    _ ≤ ∑ _w ∈ appendixCoefficientOrderWords m, K m * D ^ (a * (m + 1)) :=
      Finset.sum_le_sum fun w hw => csSup_le ⟨0, Or.inl rfl⟩ (hval m w hw)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]; ring

/-- The power bound (D.6) is monotone in the exponent, since `𝖣 ≥ 1`. -/
theorem CoefficientPower.mono_exponent {C : ℕ → ℝ} {D : ℝ} {a b : ℕ} {c : I → Vec3 → X}
    (hc : AppendixD.CoefficientPower C D a c) (hD : 1 ≤ D) (hab : a ≤ b) :
    AppendixD.CoefficientPower C D b c := by
  refine ⟨hc.1, hc.2.1, fun m => (hc.2.2 m).trans ?_⟩
  have hnorm : 0 ≤ AppendixD.coefficientOrderNorm m c :=
    Finset.sum_nonneg fun w hw => le_csSup (hc.2.1 m w hw) (Or.inl rfl)
  have hC : 0 ≤ C m := by
    have hp : 0 < D ^ (a * (m + 1)) := pow_pos (zero_lt_one.trans_le hD) _
    by_contra hneg
    have : C m * D ^ (a * (m + 1)) < 0 := mul_neg_of_neg_of_pos (lt_of_not_ge hneg) hp
    linarith [hc.2.2 m]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right _ hab)) hC

end CoefficientJets

/-! ## Fourier bands -/

section Bands

/-- Fourier coefficients commute with complex-linear maps. Copy of the private
`mFourierCoeff_comp_complexCLM` (`TorusEuler/TruncationFourierCommutation.lean:19`), for a
map into `ℂ` from the complex Euclidean space; same proof. -/
theorem mFourierCoeff_comp_clm (L : ComplexEuclideanVec3 →L[ℂ] ℂ)
    (g : C(Labels, ComplexEuclideanVec3)) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => L (g z)) k = L (mFourierCoeff g k) := by
  have hcont : Continuous (fun z => mFourier (-k) z • g z) :=
    (mFourier (-k)).continuous.smul g.continuous
  have hint : Integrable (fun z => mFourier (-k) z • g z) unitTorusMeasure := by
    simpa only [integrableOn_univ] using
      hcont.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ
  change (∫ z, mFourier (-k) z • L (g z) ∂unitTorusMeasure) =
    L (∫ z, mFourier (-k) z • g z ∂unitTorusMeasure)
  rw [← L.integral_comp_comm hint]
  simp only [map_smul]

/-- A continuous real vector field on the torus whose complexified Fourier coefficients
vanish at the frequencies `|k| > R` is supported on frequencies at most `R` in the sense
of the statement of Lemma B.1: every real linear measurement of it has vanishing
Fourier coefficients at those frequencies. -/
theorem realNormedTorusFourierBand_of_vector {R : ℝ} {g : C(Labels, Vec3)}
    (hg : ∀ k, R < ‖latticeVector k‖ →
      mFourierCoeff (fun z => periodicComplexifyVector (g z)) k = 0) :
    RealNormedTorusFourierBand R g := by
  intro l k hk
  let L : ComplexEuclideanVec3 →L[ℂ] ℂ :=
    ∑ j, ((l (coordinateDirection j) : ℝ) : ℂ) • (EuclideanSpace.proj j : ComplexEuclideanVec3 →L[ℂ] ℂ)
  have hL (v : Vec3) : ((l v : ℝ) : ℂ) = L (periodicComplexifyVector v) := by
    have hl : l v = ∑ j, v j * l (coordinateDirection j) := by
      conv_lhs => rw [← sum_coordinateDirection v]
      simp only [map_sum, map_smul, smul_eq_mul]
    rw [hl]
    simp [L, mul_comm]
  let gc : C(Labels, ComplexEuclideanVec3) :=
    ⟨fun z => periodicComplexifyVector (g z), periodicComplexifyVector.continuous.comp g.continuous⟩
  have hfun : (⇑(realFourierScalarization l g) : Labels → ℂ) = fun z => L (gc z) :=
    funext fun z => hL (g z)
  rw [hfun, mFourierCoeff_comp_clm L gc k]
  change L (mFourierCoeff (fun z => periodicComplexifyVector (g z)) k) = 0
  rw [hg k hk, map_zero]

end Bands

end

end TorusEuler.Paper.Lib.S5a

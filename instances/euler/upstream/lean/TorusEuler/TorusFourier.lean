import TorusEuler.Statement
import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
Fourier modes and the finite frequency cutoff on the unit three-torus in
Appendix B. The Euclidean lift uses the same centered cell as the Euler
statement.
-/

open MeasureTheory Set UnitAddTorus
open scoped ComplexConjugate ContDiff

namespace TorusEuler

noncomputable section

/-- The quotient of the periodic Euclidean lift by the integer lattice. -/
def toUnitTorus (x : Vec3) : UnitAddTorus (Fin 3) :=
  fun i => (x i : UnitAddCircle)

theorem toUnitTorus_surjective : Function.Surjective toUnitTorus := by
  intro z
  have h i : ∃ t : ℝ, (t : UnitAddCircle) = z i :=
    QuotientAddGroup.mk_surjective (z i)
  choose x hx using h
  exact ⟨WithLp.toLp 2 x, funext hx⟩

theorem toUnitTorus_eq_iff (x y : Vec3) :
    toUnitTorus x = toUnitTorus y ↔ ∃ n : Fin 3 → ℤ, x = y + latticeVector n := by
  constructor
  · intro h
    have hcoord (i : Fin 3) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
      have hz : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
        rw [AddCircle.coe_sub, sub_eq_zero]
        exact congrFun h i
      simpa [zsmul_one] using (AddCircle.coe_eq_zero_iff 1).mp hz
    choose n hn using hcoord
    exact ⟨n, PiLp.ext fun i => by
      change x i = y i + (n i : ℝ)
      rw [hn]
      ring⟩
  · rintro ⟨n, rfl⟩
    funext i
    change ((y i + (n i : ℝ) : ℝ) : UnitAddCircle) = (y i : UnitAddCircle)
    rw [AddCircle.coe_add, add_eq_left]
    exact (AddCircle.coe_eq_zero_iff 1).mpr ⟨n i, by simp⟩

/-- A periodic function on the lift determines a function on the quotient. -/
theorem SpatiallyPeriodic.existsUnique_torusFunction {α : Type*} {f : Vec3 → α}
    (hf : SpatiallyPeriodic f) :
    ∃! g : UnitAddTorus (Fin 3) → α, ∀ x, g (toUnitTorus x) = f x := by
  classical
  let g : UnitAddTorus (Fin 3) → α := fun z => f (toUnitTorus_surjective z).choose
  have hg (x : Vec3) : g (toUnitTorus x) = f x := by
    obtain ⟨n, hn⟩ := (toUnitTorus_eq_iff _ _).mp
      (toUnitTorus_surjective (toUnitTorus x)).choose_spec
    change f (toUnitTorus_surjective (toUnitTorus x)).choose = f x
    rw [hn, hf]
  refine ⟨g, hg, fun g' hg' => ?_⟩
  funext z
  obtain ⟨x, rfl⟩ := toUnitTorus_surjective z
  exact (hg' x).trans (hg x).symm

/-- Product Haar probability measure on the unit three-torus. -/
def unitTorusMeasure : Measure (UnitAddTorus (Fin 3)) :=
  Measure.pi fun _ : Fin 3 => AddCircle.haarAddCircle

/-- The standard torus probability integral is the lift's integral over the
centered unit cube. -/
theorem torusIntegral_eq_centeredCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : UnitAddTorus (Fin 3) → E) :
    ∫ z, g z ∂unitTorusMeasure = ∫ x in centeredCell, g (toUnitTorus x) := by
  let box (s : Set ℝ) : Set (Fin 3 → ℝ) := pi univ (fun _ => s)
  have hcell : IsClosed (box (Icc (-(1 / 2 : ℝ)) (1 / 2))) :=
    isClosed_set_pi fun _ _ => isClosed_Icc
  have hpres := (PiLp.volume_preserving_ofLp (Fin 3)).restrict_preimage hcell.measurableSet
  have hpre : WithLp.ofLp ⁻¹' box (Icc (-(1 / 2 : ℝ)) (1 / 2)) = centeredCell := by
    ext x
    simp only [mem_preimage, box, mem_pi, mem_univ, true_implies, centeredCell, mem_ofPred_eq]
  rw [hpre] at hpres
  calc
    _ = ∫ y in box (Icc (-(1 / 2 : ℝ)) (1 / 2)), g (fun i => (y i : UnitAddCircle)) := by
      rw [show (∫ z, g z ∂unitTorusMeasure) =
        ∫ (y : Fin 3 → ℝ) in {y | ∀ i, y i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)},
          g (fun i => (y i : UnitAddCircle)) from integral_preimage g (fun _ => -(1 / 2 : ℝ))]
      have hbox : {x : Fin 3 → ℝ | ∀ i, x i ∈ Ioc (-(1 / 2 : ℝ)) (-(1 / 2 : ℝ) + 1)} =
          box (Ioc (-(1 / 2 : ℝ)) (1 / 2)) := by
        norm_num [box, Set.pi]
      rw [hbox]
      have hrestrict :
          (volume : Measure (Fin 3 → ℝ)).restrict (box (Ioc (-(1 / 2 : ℝ)) (1 / 2))) =
            volume.restrict (box (Icc (-(1 / 2 : ℝ)) (1 / 2))) := by
        change (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).restrict _ =
          (Measure.pi fun _ : Fin 3 => (volume : Measure ℝ)).restrict _
        dsimp only [box]
        rw [Measure.restrict_pi_pi, Measure.restrict_pi_pi]
        simp only [restrict_Ioc_eq_restrict_Icc]
      rw [hrestrict]
    _ = _ := (hpres.integral_comp
      (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.measurableEmbedding
      (fun y => g (fun i => (y i : UnitAddCircle)))).symm

/-- The Fourier character evaluated on the periodic Euclidean lift. -/
def fourierMode (k : Fin 3 → ℤ) (x : Vec3) : ℂ := mFourier k (toUnitTorus x)

theorem fourierCoeff_eq_centeredCell {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (g : UnitAddTorus (Fin 3) → E) (k : Fin 3 → ℤ) :
    mFourierCoeff g k = ∫ x in centeredCell, fourierMode (-k) x • g (toUnitTorus x) :=
  torusIntegral_eq_centeredCell (fun z => mFourier (-k) z • g z)

theorem spatiallyPeriodic_fourierMode (k : Fin 3 → ℤ) : SpatiallyPeriodic (fourierMode k) := by
  intro n x
  rw [fourierMode, fourierMode, (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]

private def fourierPhase (k : Fin 3 → ℤ) : Vec3 →L[ℝ] ℂ :=
  (2 * (Real.pi : ℂ) * Complex.I) • (Complex.ofRealCLM.comp (innerSL ℝ (latticeVector k)))

private theorem fourierPhase_apply (k : Fin 3 → ℤ) (x : Vec3) :
    fourierPhase k x = 2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ) := by
  simp [fourierPhase, EuclideanSpace.inner_eq_star_dotProduct, dotProduct, latticeVector,
    mul_comm]

theorem fourierMode_eq_exp (k : Fin 3 → ℤ) (x : Vec3) :
    fourierMode k x =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ)) := by
  rw [Finset.mul_sum, Complex.exp_sum]
  simp only [fourierMode, mFourier, ContinuousMap.coe_mk, toUnitTorus, fourier_coe_apply,
    Complex.ofReal_one, div_one, mul_assoc]

private theorem fourierMode_eq_exp_phase (k : Fin 3 → ℤ) (x : Vec3) :
    fourierMode k x = Complex.exp (fourierPhase k x) := by
  rw [fourierMode_eq_exp, fourierPhase_apply]

theorem norm_fourierMode (k : Fin 3 → ℤ) (x : Vec3) : ‖fourierMode k x‖ = 1 := by
  simp only [fourierMode, mFourier, fourier_apply, ContinuousMap.coe_mk, norm_prod,
    Circle.norm_coe, Finset.prod_const_one]

theorem contDiff_fourierMode (k : Fin 3 → ℤ) : ContDiff ℝ ∞ (fourierMode k) := by
  have h : fourierMode k = Complex.exp ∘ fourierPhase k :=
    funext (fourierMode_eq_exp_phase k)
  rw [h]
  exact Complex.contDiff_exp.comp (fourierPhase k).contDiff

private theorem hasFDerivAt_fourierMode (k : Fin 3 → ℤ) (x : Vec3) :
    HasFDerivAt (fourierMode k) (fourierMode k x • fourierPhase k) x := by
  have h : fourierMode k = Complex.exp ∘ fourierPhase k :=
    funext (fourierMode_eq_exp_phase k)
  rw [h]
  have hd := ((Complex.hasDerivAt_exp (fourierPhase k x)).hasFDerivAt.restrictScalars ℝ).comp x
    (fourierPhase k).hasFDerivAt
  refine hd.congr_fderiv ?_
  ext v
  simp [mul_comm]

/-- Differentiation of a mode along a constant vector multiplies it by its
frequency paired with that vector. -/
theorem fderiv_fourierMode (k : Fin 3 → ℤ) (x v : Vec3) :
    fderiv ℝ (fourierMode k) x v =
      (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (v i : ℂ)) * fourierMode k x := by
  rw [(hasFDerivAt_fourierMode k x).fderiv]
  simp only [smul_apply, smul_eq_mul, fourierPhase_apply]
  ac_rfl

/-- The symbol of the (i)-th coordinate derivative on a unit-torus mode. -/
def fourierDerivativeSymbol (k : Fin 3 → ℤ) (i : Fin 3) : ℂ :=
  2 * (Real.pi : ℂ) * Complex.I * (k i : ℂ)

theorem fderiv_fourierMode_single (k : Fin 3 → ℤ) (x : Vec3) (i : Fin 3) :
    fderiv ℝ (fourierMode k) x (EuclideanSpace.single i 1) =
      fourierDerivativeSymbol k i * fourierMode k x := by
  rw [(hasFDerivAt_fourierMode k x).fderiv]
  simp [fourierPhase, fourierDerivativeSymbol, EuclideanSpace.inner_single_right,
    latticeVector, mul_comm]

/-- The integer frequencies in the closed Euclidean ball of radius `R`. -/
def frequencyBand (R : ℝ) : Finset (Fin 3 → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ : Fin 3 => Finset.Icc (-⌈R⌉) ⌈R⌉).filter
    (fun k => ‖latticeVector k‖ ≤ R)

@[simp] theorem mem_frequencyBand (R : ℝ) (k : Fin 3 → ℤ) :
    k ∈ frequencyBand R ↔ ‖latticeVector k‖ ≤ R := by
  classical
  rw [frequencyBand, Finset.mem_filter]
  refine ⟨And.right, fun hk => ⟨Fintype.mem_piFinset.mpr fun i => ?_, hk⟩⟩
  apply Finset.mem_Icc.mpr
  rw [← abs_le]
  apply (Int.cast_le (R := ℝ)).mp
  rw [Int.cast_abs]
  have hc : |(k i : ℝ)| ≤ ‖latticeVector k‖ :=
    PiLp.norm_apply_le (latticeVector k) i
  exact hc.trans (hk.trans (Int.le_ceil R))

private theorem latticeVector_neg (k : Fin 3 → ℤ) : latticeVector (-k) = -latticeVector k :=
  PiLp.ext fun i => Int.cast_neg (k i)

theorem mem_frequencyBand_neg (R : ℝ) (k : Fin 3 → ℤ) :
    -k ∈ frequencyBand R ↔ k ∈ frequencyBand R := by
  simp only [mem_frequencyBand, latticeVector_neg, norm_neg]

theorem mFourier_neg_arg (k : Fin 3 → ℤ) (z : UnitAddTorus (Fin 3)) :
    mFourier k (-z) = mFourier (-k) z := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.neg_apply, fourier_apply, zsmul_neg, neg_zsmul]

private instance : Measure.IsAddHaarMeasure unitTorusMeasure :=
  inferInstanceAs (Measure.IsAddHaarMeasure
    (Measure.pi (fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle))))

private instance : IsProbabilityMeasure unitTorusMeasure :=
  inferInstanceAs (IsProbabilityMeasure
    (Measure.pi (fun _ : Fin 3 => (AddCircle.haarAddCircle : Measure UnitAddCircle))))

/-- The Fourier power basis has Kronecker coefficients for the normalized
product Haar measure. -/
theorem integral_fourier_pair (k j : Fin 3 → ℤ) :
    (∫ z, mFourier (-k) z * mFourier j z ∂unitTorusMeasure) =
      if k = j then 1 else 0 := by
  classical
  have h := (orthonormal_iff_ite.mp (orthonormal_mFourier (d := Fin 3))) k j
  change inner ℂ ((mFourier k).toLp 2 unitTorusMeasure ℂ)
    ((mFourier j).toLp 2 unitTorusMeasure ℂ) = _ at h
  rw [MeasureTheory.ContinuousMap.inner_toLp] at h
  simpa only [← mFourier_neg, mul_comm (mFourier j _)] using h

section ComplexValues

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- Synthesis of a trigonometric polynomial from its finite list of
coefficients. -/
def finiteFourierSum (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E)
    (z : UnitAddTorus (Fin 3)) : E :=
  ∑ k ∈ s, mFourier k z • a k

theorem contDiff_lift_finiteFourierSum (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E) :
    ContDiff ℝ ∞ (fun x => finiteFourierSum s a (toUnitTorus x)) := by
  change ContDiff ℝ ∞ (fun x => ∑ k ∈ s, fourierMode k x • a k)
  exact ContDiff.sum fun k _ => (contDiff_fourierMode k).smul contDiff_const

theorem fderiv_lift_finiteFourierSum_single (s : Finset (Fin 3 → ℤ)) (a : (Fin 3 → ℤ) → E)
    (x : Vec3) (i : Fin 3) :
    fderiv ℝ (fun x => finiteFourierSum s a (toUnitTorus x)) x (EuclideanSpace.single i 1) =
      finiteFourierSum s (fun k => fourierDerivativeSymbol k i • a k) (toUnitTorus x) := by
  change fderiv ℝ (fun x => ∑ k ∈ s, fourierMode k x • a k) x (EuclideanSpace.single i 1) =
    ∑ k ∈ s, fourierMode k x • (fourierDerivativeSymbol k i • a k)
  have hd := HasFDerivAt.fun_sum (u := s)
    (fun k _ => (hasFDerivAt_fourierMode k x).smul_const (a k))
  rw [hd.fderiv, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ContinuousLinearMap.smulRight_apply, ← (hasFDerivAt_fourierMode k x).fderiv,
    fderiv_fourierMode_single, ← smul_smul]
  exact smul_comm _ _ _

/-- A finite band symmetric in frequency transfers parity of coefficients to
parity of the synthesized field. -/
theorem finiteFourierSum_neg_arg (R : ℝ) (a : (Fin 3 → ℤ) → E) (c : ℝ)
    (ha : ∀ k, a (-k) = c • a k) (z : UnitAddTorus (Fin 3)) :
    finiteFourierSum (frequencyBand R) a (-z) =
      c • finiteFourierSum (frequencyBand R) a z := by
  classical
  rw [finiteFourierSum, finiteFourierSum, Finset.smul_sum]
  refine Finset.sum_bij' (fun k _ => -k) (fun k _ => -k) (fun k hk => ?_) (fun k hk => ?_)
    (fun k _ => neg_neg k) (fun k _ => neg_neg k) (fun k _ => ?_)
  · exact (mem_frequencyBand_neg R k).mpr hk
  · exact (mem_frequencyBand_neg R k).mpr hk
  · rw [mFourier_neg_arg, smul_comm c (mFourier (-k) z)]
    exact congrArg ((mFourier (-k) z) • ·) (by simpa only [neg_neg] using ha (-k))

theorem mFourierCoeff_neg_of_parity {g : UnitAddTorus (Fin 3) → E} (c : ℝ)
    (hg : ∀ z, g (-z) = c • g z) (k : Fin 3 → ℤ) :
    mFourierCoeff g (-k) = c • mFourierCoeff g k := by
  let f := fun z : UnitAddTorus (Fin 3) => mFourier k z • g z
  have hneg : MeasurePreserving (fun z : UnitAddTorus (Fin 3) => -z)
      unitTorusMeasure unitTorusMeasure :=
    AddMonoidHom.measurePreserving (f := -AddMonoidHom.id (UnitAddTorus (Fin 3)))
      continuous_neg neg_involutive.surjective rfl
  have h := hneg.integral_comp
    (MeasurableEquiv.neg (UnitAddTorus (Fin 3))).measurableEmbedding f
  change (∫ z, mFourier (-(-k)) z • g z ∂unitTorusMeasure) =
    c • ∫ z, mFourier (-k) z • g z ∂unitTorusMeasure
  rw [neg_neg, ← h, ← integral_smul]
  congr 1
  funext z
  simp only [f, mFourier_neg_arg, hg]
  exact smul_comm (mFourier (-k) z) c (g z)

theorem mFourierCoeff_finiteFourierSum [CompleteSpace E] (s : Finset (Fin 3 → ℤ))
    (a : (Fin 3 → ℤ) → E) (k : Fin 3 → ℤ) :
    mFourierCoeff (finiteFourierSum s a) k = if k ∈ s then a k else 0 := by
  classical
  change (∫ z, mFourier (-k) z • finiteFourierSum s a z ∂unitTorusMeasure) = _
  simp only [finiteFourierSum, Finset.smul_sum, smul_smul]
  rw [integral_finsetSum s]
  · simp_rw [integral_smul_const, integral_fourier_pair, ite_smul, one_smul, zero_smul]
    exact Finset.sum_ite_eq s k a
  · intro j _
    have hc : Continuous (fun z => (mFourier (-k) z * mFourier j z) • a j) :=
      ((mFourier (-k)).continuous.mul (mFourier j).continuous).smul continuous_const
    simpa using (hc.continuousOn.integrableOn_compact (μ := unitTorusMeasure) isCompact_univ)

/-- The finite Fourier synthesis of the Appendix B multiplier. -/
def smoothFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ) (g : UnitAddTorus (Fin 3) → E) :
    UnitAddTorus (Fin 3) → E :=
  finiteFourierSum (frequencyBand (2 * Λ))
    (fun k => ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff g k)

theorem contDiff_lift_smoothFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : UnitAddTorus (Fin 3) → E) :
    ContDiff ℝ ∞ (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) :=
  contDiff_lift_finiteFourierSum _ _

theorem spatiallyPeriodic_lift_smoothFourierCutoff (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : UnitAddTorus (Fin 3) → E) :
    SpatiallyPeriodic (fun x => smoothFourierCutoff ψ Λ g (toUnitTorus x)) := by
  intro n x
  exact congrArg (smoothFourierCutoff ψ Λ g) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)

theorem mFourierCoeff_smoothFourierCutoff [CompleteSpace E] {ψ : Vec3 → ℝ} {Λ : ℝ}
    (hΛ : 0 < Λ) (hψ : ∀ x, 2 < ‖x‖ → ψ x = 0)
    (g : UnitAddTorus (Fin 3) → E) (k : Fin 3 → ℤ) :
    mFourierCoeff (smoothFourierCutoff ψ Λ g) k =
      ψ (Λ⁻¹ • latticeVector k) • mFourierCoeff g k := by
  classical
  rw [smoothFourierCutoff, mFourierCoeff_finiteFourierSum]
  by_cases hk : k ∈ frequencyBand (2 * Λ)
  · simp [hk]
  · have hscaled : 2 < ‖Λ⁻¹ • latticeVector k‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), ← div_eq_inv_mul,
        lt_div_iff₀ hΛ]
      simpa using hk
    simp [hk, hψ _ hscaled]

theorem mFourierCoeff_smoothFourierCutoff_eq_zero [CompleteSpace E] (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g : UnitAddTorus (Fin 3) → E) {k : Fin 3 → ℤ} (hk : 2 * Λ < ‖latticeVector k‖) :
    mFourierCoeff (smoothFourierCutoff ψ Λ g) k = 0 := by
  classical
  rw [smoothFourierCutoff, mFourierCoeff_finiteFourierSum]
  simp [not_le.mpr hk]

theorem smoothFourierCutoff_neg_arg {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ)
    {g : UnitAddTorus (Fin 3) → E} (c : ℝ) (hg : ∀ z, g (-z) = c • g z)
    (z : UnitAddTorus (Fin 3)) :
    smoothFourierCutoff ψ Λ g (-z) = c • smoothFourierCutoff ψ Λ g z := by
  apply finiteFourierSum_neg_arg
  intro k
  rw [latticeVector_neg, smul_neg, hψ, mFourierCoeff_neg_of_parity c hg, smul_comm]

end ComplexValues

theorem mFourierCoeff_conj (g : UnitAddTorus (Fin 3) → ℂ) (k : Fin 3 → ℤ) :
    mFourierCoeff (fun z => conj (g z)) k = conj (mFourierCoeff g (-k)) := by
  change (∫ z, mFourier (-k) z * conj (g z) ∂unitTorusMeasure) =
    conj (∫ z, mFourier (-(-k)) z * g z ∂unitTorusMeasure)
  rw [neg_neg, ← integral_conj]
  simp only [mFourier_neg, map_mul]

/-- Real even symbols commute with complex conjugation. -/
theorem smoothFourierCutoff_conj {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ)
    (g : UnitAddTorus (Fin 3) → ℂ) (z : UnitAddTorus (Fin 3)) :
    smoothFourierCutoff ψ Λ (fun z => conj (g z)) z =
      conj (smoothFourierCutoff ψ Λ g z) := by
  classical
  simp only [smoothFourierCutoff, finiteFourierSum, map_sum]
  refine Finset.sum_bij' (fun k _ => -k) (fun k _ => -k) (fun k hk => ?_) (fun k hk => ?_)
    (fun k _ => neg_neg k) (fun k _ => neg_neg k) (fun k _ => ?_)
  · exact (mem_frequencyBand_neg _ k).mpr hk
  · exact (mem_frequencyBand_neg _ k).mpr hk
  · simp only [latticeVector_neg, smul_neg, mFourierCoeff_conj, smul_eq_mul, Complex.real_smul,
      map_mul, Complex.conj_ofReal, mFourier_neg, starRingEnd_self_apply]
    rw [hψ (Λ⁻¹ • latticeVector k)]

theorem conj_smoothFourierCutoff_of_real {ψ : Vec3 → ℝ} (hψ : Function.Even ψ) (Λ : ℝ)
    {g : UnitAddTorus (Fin 3) → ℂ} (hg : ∀ z, conj (g z) = g z) (z : UnitAddTorus (Fin 3)) :
    conj (smoothFourierCutoff ψ Λ g z) = smoothFourierCutoff ψ Λ g z := by
  rw [← smoothFourierCutoff_conj hψ Λ, show (fun z => conj (g z)) = g from funext hg]

end

end TorusEuler

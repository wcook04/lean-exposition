import Breakdown.CellReduction.PotFluxRadialWeak
import Breakdown.FracCell.GivenToolkit
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeSphericalDivFrame

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace Internal.RadialFlux

open CertCell CertCell.GivenShape
open CellCert.GivenFields (heightRatio cellIndex cellCount weightPoly atFirst)
open CellCert.GivenFields.OpenLeavesInternal (pk pk_continuous pk_bound pk_hasDerivAt cellIndex_le
  cellIndex_right cellIndex_nhds glue_continuous interior_get eval_atFirst height_le height_smul)

def weightedPiece (S : PotScalar) (i j : ℕ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 ^ S.lowOrder * (1 - MvPolynomial.X 0) ^ S.highOrder * S.amp.toSpline.piece i j

def cellValue (S : PotScalar) (t x : ℝ) : ℂ :=
  pk (weightedPiece S (cellIndex S.amp.tAxis.breaks t) (cellIndex S.amp.xAxis.breaks x)) (t, x)

theorem pk_weightedPiece (S : PotScalar) (i j : ℕ) (t x : ℝ) :
    pk (weightedPiece S i j) (t, x) = weightPoly S.lowOrder S.highOrder t * pk (S.amp.toSpline.piece i j) (t, x) := by
  simp [pk, weightedPiece, weightPoly]

theorem cellValue_eq (S : PotScalar) (t x : ℝ) :
    weightPoly S.lowOrder S.highOrder t * S.amp.toSpline.evalHalf t x = cellValue S t x := by
  rw [cellValue, pk_weightedPiece]
  rfl

theorem cellValue_bounds (S : PotScalar) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t' t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ‖pk (weightedPiece S (cellIndex S.amp.tAxis.breaks t') (cellIndex S.amp.xAxis.breaks x)) (t, x)‖ ≤ B ∧
    ‖pk (MvPolynomial.pderiv 0
      (weightedPiece S (cellIndex S.amp.tAxis.breaks t') (cellIndex S.amp.xAxis.breaks x))) (t, x)‖ ≤ B := by
  choose bd hbd0 hbd using fun Q : MvPolynomial (Fin 2) ℂ => pk_bound Q
  let term : ℕ → ℕ → ℝ := fun i j =>
    bd (weightedPiece S i j) + bd (MvPolynomial.pderiv 0 (weightedPiece S i j))
  have hterm0 : ∀ i j, 0 ≤ term i j := fun i j => add_nonneg (hbd0 _) (hbd0 _)
  refine ⟨∑ i ∈ Finset.range (S.amp.tAxis.breaks.length + 1),
      ∑ j ∈ Finset.range (S.amp.xAxis.breaks.length + 1), term i j,
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hterm0 i j, fun t' t x ht hx => ?_⟩
  have hi : cellIndex S.amp.tAxis.breaks t' ∈ Finset.range (S.amp.tAxis.breaks.length + 1) := by
    have := cellIndex_le S.amp.tAxis.breaks t'
    rw [Finset.mem_range]
    omega
  have hj : cellIndex S.amp.xAxis.breaks x ∈ Finset.range (S.amp.xAxis.breaks.length + 1) := by
    have := cellIndex_le S.amp.xAxis.breaks x
    rw [Finset.mem_range]
    omega
  have hle : term (cellIndex S.amp.tAxis.breaks t') (cellIndex S.amp.xAxis.breaks x) ≤
      ∑ i ∈ Finset.range (S.amp.tAxis.breaks.length + 1),
        ∑ j ∈ Finset.range (S.amp.xAxis.breaks.length + 1), term i j :=
    (Finset.single_le_sum (f := fun j => term (cellIndex S.amp.tAxis.breaks t') j)
      (fun j _ => hterm0 _ j) hj).trans
      (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (S.amp.xAxis.breaks.length + 1), term i j)
        (fun i _ => Finset.sum_nonneg fun j _ => hterm0 i j) hi)
  exact ⟨(hbd _ t x ht hx).trans ((le_add_of_nonneg_right (hbd0 _)).trans hle),
    (hbd _ t x ht hx).trans ((le_add_of_nonneg_left (hbd0 _)).trans hle)⟩

theorem piece_join (S : PotScalar) (hS : IsJetAxis S.amp.tAxis 0 1) (k j : ℕ)
    (hk : k + 1 < cellCount S.amp.tAxis.breaks) :
    atFirst ((S.amp.tAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ) (S.amp.toSpline.piece k j) =
      atFirst ((S.amp.tAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ) (S.amp.toSpline.piece (k + 1) j) := by
  rw [GivenShape.Internal.toSpline_piece, GivenShape.Internal.toSpline_piece,
    GivenShape.Internal.atFirst_sum, GivenShape.Internal.atFirst_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [GivenShape.Internal.atFirst_sum, GivenShape.Internal.atFirst_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [GivenShape.Internal.atFirst_term, GivenShape.Internal.atFirst_term]
  have h := GivenShape.Internal.dofPoly_jets_agree
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_left n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalLeft_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_right n p o hab ho)
    (fun n p o _ _ hab ho => iterate_derivative_nodalRight_eval_left n p o hab ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_left n s o a b ho)
    (fun n s o a b ho => iterate_derivative_bubblePoly_eval_right n s o a b ho)
    S.amp.tAxis hS.sorted (k + 1) (by omega) hk 0 hS.depth_pos d
  have h' : Polynomial.eval (((S.amp.tAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ)) (S.amp.tAxis.dofPoly k d) =
      Polynomial.eval (((S.amp.tAxis.breaks.getD (k + 1) 0 : ℝ) : ℂ)) (S.amp.tAxis.dofPoly (k + 1) d) := by
    exact h
  rw [h']

theorem cellValue_continuous (S : PotScalar) (hS : IsJetAxis S.amp.tAxis 0 1) (x : ℝ) :
    Continuous (fun t => cellValue S t x) := by
  have hI : ((S.amp.tAxis.breaks.drop 1).dropLast).Pairwise (· < ·) :=
    hS.sorted.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _))
  have hG := glue_continuous (Z := ℝ) id continuous_id _ hI
    (fun k t => pk (weightedPiece S k (cellIndex S.amp.xAxis.breaks x)) (t, x))
    (fun k _ => (pk_continuous _).comp (continuous_id.prodMk continuous_const)) ?_
  · exact hG
  · intro k hk t ht
    have hk' := hk
    simp only [List.length_dropLast, List.length_drop] at hk'
    have h := congrArg (MvPolynomial.eval ![(0 : ℂ), ((x : ℝ) : ℂ)])
      (piece_join S hS k (cellIndex S.amp.xAxis.breaks x) (by unfold cellCount; omega))
    simp only [eval_atFirst] at h
    rw [id, interior_get _ _ hk] at ht
    have hp : pk (S.amp.toSpline.piece k (cellIndex S.amp.xAxis.breaks x)) (S.amp.tAxis.breaks.getD (k + 1) 0, x) =
        pk (S.amp.toSpline.piece (k + 1) (cellIndex S.amp.xAxis.breaks x)) (S.amp.tAxis.breaks.getD (k + 1) 0, x) := by
      simpa [pk] using h
    show pk _ (t, x) = pk _ (t, x)
    rw [pk_weightedPiece, pk_weightedPiece, ht, hp]

theorem cellValue_right (S : PotScalar) (t₀ x : ℝ) : ∀ᶠ t in 𝓝[≥] t₀,
    cellValue S t x =
      pk (weightedPiece S (cellIndex S.amp.tAxis.breaks t₀) (cellIndex S.amp.xAxis.breaks x)) (t, x) := by
  filter_upwards [cellIndex_right S.amp.tAxis.breaks t₀] with t ht
  rw [cellValue, ht]

def phaseAngle (P : ShapeParams) (κ : FieldKey) (M : ℤ) (σ : ℝ) (y : Space) : ℝ :=
  2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y + (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)

def sideFactor (withSine : Bool) (S : PotScalar) (y : Space) : ℝ :=
  (1 - heightRatio y ^ 2) ^ S.axisPower * (if withSine then polarSine y else 1)

theorem scalarValue_eq (P : ShapeParams) (κ : FieldKey) (M : ℤ) (b : Bool) (S : PotScalar) (σ : ℝ) (y : Space) :
    scalarValue P κ M b S σ y = Complex.exp ((phaseAngle P κ M σ y : ℂ) * Complex.I) * (sideFactor b S y : ℂ) *
      cellValue S (chartCoord P y) (heightRatio y) := by
  rw [scalarValue, ← cellValue_eq, phaseAngle, sideFactor]
  ring

theorem sideFactor_abs_le (b : Bool) (S : PotScalar) (y : Space) : |sideFactor b S y| ≤ 1 := by
  have hh := height_le y
  have hsq : heightRatio y ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact hh
  have h0 : 0 ≤ 1 - heightRatio y ^ 2 := by linarith
  have h1 : 1 - heightRatio y ^ 2 ≤ 1 := by nlinarith
  have hp0 : 0 ≤ (1 - heightRatio y ^ 2) ^ S.axisPower := pow_nonneg h0 _
  have hp1 : (1 - heightRatio y ^ 2) ^ S.axisPower ≤ 1 := pow_le_one₀ h0 h1
  have hs0 : 0 ≤ (if b then polarSine y else 1) := by
    cases b
    · simp
    · simp [polarSine, Real.sqrt_nonneg]
  have hs1 : (if b then polarSine y else 1) ≤ 1 := by
    cases b
    · simp
    · simp only [if_true, polarSine]
      exact Real.sqrt_le_one.mpr h1
  rw [sideFactor, abs_of_nonneg (mul_nonneg hp0 hs0)]
  nlinarith

theorem pointAngle_pos_smul {s : ℝ} (hs : 0 < s) (y : Space) : pointAngle (s • y) = pointAngle y := by
  have e : (((s • y) 0 : ℝ) : ℂ) + (((s • y) 1 : ℝ) : ℂ) * Complex.I =
      (s : ℂ) * (((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I) := by
    simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  unfold pointAngle
  rw [e, Complex.arg_real_mul _ hs]

theorem scalarValue_ray (P : ShapeParams) (κ : FieldKey) (M : ℤ) (b : Bool) (S : PotScalar) (σ : ℝ) (y : Space)
    {s : ℝ} (hs : 0 < s) :
    scalarValue P κ M b S σ (s • y) =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
        (κ.phaseIndex : ℝ) * P.radialPhase ((s * ‖y‖) ^ 2) : ℝ) : ℂ) * Complex.I) * (sideFactor b S y : ℂ) *
        cellValue S (s * ‖y‖ / (s * ‖y‖ + P.chartLength)) (heightRatio y) := by
  rw [scalarValue_eq, phaseAngle, sideFactor, sideFactor, polarSine, polarSine, pointAngle_pos_smul hs,
    height_smul hs, chartCoord, smul_norm_pos hs]

theorem chartCoord_mem (P : ShapeParams) (hP : IsShapeParams P) (y : Space) :
    0 ≤ chartCoord P y ∧ chartCoord P y < 1 := by
  have hL := hP.chartLength_pos
  unfold chartCoord
  refine ⟨by positivity, ?_⟩
  rw [div_lt_one (by positivity)]
  linarith

theorem radialPhase_continuous (P : ShapeParams) (hP : IsShapeParams P) :
    Continuous (fun y : Space => P.radialPhase (‖y‖ ^ 2)) := by
  obtain ⟨δ, hδ, hc⟩ := hP.phase.smooth
  refine hc.continuousOn.comp_continuous (continuous_norm.pow 2) (fun y => ?_)
  simp only [Set.mem_Ioi]
  nlinarith [sq_nonneg ‖y‖]

theorem scalarValue_measurable (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (b : Bool)
    (S : PotScalar) (σ : ℝ) : Measurable (scalarValue P κ M b S σ) := by
  have hpa : Measurable pointAngle := by
    unfold pointAngle
    fun_prop
  have hh : Measurable heightRatio := by
    unfold heightRatio
    fun_prop
  have hc : Measurable (chartCoord P) := by
    unfold chartCoord
    fun_prop
  have hph : Measurable (phaseAngle P κ M σ) := by
    unfold phaseAngle
    exact ((measurable_const.add (measurable_const.mul hpa)).add
      (measurable_const.mul (radialPhase_continuous P hP).measurable))
  have hsd : Measurable (sideFactor b S) := by
    unfold sideFactor polarSine
    cases b
    · simp only [Bool.false_eq_true, if_false]
      exact ((measurable_const.sub (hh.pow_const 2)).pow_const _).mul measurable_const
    · simp only [if_true]
      exact ((measurable_const.sub (hh.pow_const 2)).pow_const _).mul
        (measurable_const.sub (hh.pow_const 2)).sqrt
  have hcv : Measurable (fun y : Space => cellValue S (chartCoord P y) (heightRatio y)) := by
    have e : (fun y : Space => cellValue S (chartCoord P y) (heightRatio y)) =
        fun y => weightPoly S.lowOrder S.highOrder (chartCoord P y) *
          Function.uncurry S.amp.toSpline.evalHalf (chartCoord P y, heightRatio y) := by
      funext y
      rw [← cellValue_eq]
      rfl
    rw [e]
    refine Measurable.mul ?_ ((CellCert.GivenFields.OpenLeavesInternal.evalHalf_measurable _).comp (hc.prodMk hh))
    unfold weightPoly
    exact Complex.measurable_ofReal.comp ((hc.pow_const _).mul ((measurable_const.sub hc).pow_const _))
  have e : scalarValue P κ M b S σ = fun y => Complex.exp ((phaseAngle P κ M σ y : ℂ) * Complex.I) *
      (sideFactor b S y : ℂ) * cellValue S (chartCoord P y) (heightRatio y) :=
    funext fun y => scalarValue_eq P κ M b S σ y
  rw [e]
  exact (((Complex.measurable_ofReal.comp hph).mul_const _).cexp.mul (Complex.measurable_ofReal.comp hsd)).mul hcv

theorem scalarValue_bound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (b : Bool)
    (S : PotScalar) (σ : ℝ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y, ‖scalarValue P κ M b S σ y‖ ≤ B := by
  obtain ⟨B, hB0, hB⟩ := cellValue_bounds S
  refine ⟨B, hB0, fun y => ?_⟩
  have hm := chartCoord_mem P hP y
  rw [scalarValue_eq, norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real, Real.norm_eq_abs]
  have h1 := sideFactor_abs_le b S y
  have h2 : ‖cellValue S (chartCoord P y) (heightRatio y)‖ ≤ B :=
    (hB (chartCoord P y) _ _ (abs_le.2 ⟨by linarith [hm.1], hm.2.le⟩) (height_le y)).1
  calc 1 * |sideFactor b S y| * ‖cellValue S (chartCoord P y) (heightRatio y)‖ ≤ 1 * 1 * B := by gcongr
    _ = B := by ring

theorem chart_hasDerivAt (L r s₀ : ℝ) (hne : s₀ * r + L ≠ 0) :
    HasDerivAt (fun s : ℝ => s * r / (s * r + L)) (r * L / (s₀ * r + L) ^ 2) s₀ := by
  have h : HasDerivAt (fun s : ℝ => s * r / (s * r + L))
      ((1 * r * (s₀ * r + L) - s₀ * r * (1 * r)) / (s₀ * r + L) ^ 2) s₀ :=
    ((hasDerivAt_id' s₀).mul_const r).div (((hasDerivAt_id' s₀).mul_const r).add_const L) hne
  exact h.congr_deriv (by field_simp; ring)

theorem ray_piece_deriv (P : ShapeParams) (hP : IsShapeParams P) (c jr A r x : ℝ) (Q : MvPolynomial (Fin 2) ℂ)
    {s₀ : ℝ} (hs₀ : 0 < s₀) (hr : 0 < r) {Bv Bφ : ℝ} (hBv0 : 0 ≤ Bv) (hA : |A| ≤ 1)
    (hpv : ‖pk Q (s₀ * r / (s₀ * r + P.chartLength), x)‖ ≤ Bv)
    (hpd : ‖pk (MvPolynomial.pderiv 0 Q) (s₀ * r / (s₀ * r + P.chartLength), x)‖ ≤ Bv)
    (hφb : |(s₀ * r) ^ 2 * deriv P.radialPhase ((s₀ * r) ^ 2)| ≤ Bφ) :
    ∃ D : ℂ, HasDerivAt (fun s : ℝ => s ^ 2 • (Complex.exp (((c + jr * P.radialPhase ((s * r) ^ 2) : ℝ) : ℂ) *
      Complex.I) * (A : ℂ) * pk Q (s * r / (s * r + P.chartLength), x))) D s₀ ∧
      ‖D‖ ≤ s₀ * (2 * |jr| * Bφ * Bv + Bv + 2 * Bv) := by
  have hL := hP.chartLength_pos
  have hne : s₀ * r + P.chartLength ≠ 0 := by positivity
  have hτ := chart_hasDerivAt P.chartLength r s₀ hne
  have hpk : HasDerivAt (fun s : ℝ => pk Q (s * r / (s * r + P.chartLength), x))
      ((r * P.chartLength / (s₀ * r + P.chartLength) ^ 2) •
        pk (MvPolynomial.pderiv 0 Q) (s₀ * r / (s₀ * r + P.chartLength), x)) s₀ :=
    (pk_hasDerivAt Q _ x).scomp s₀ hτ
  obtain ⟨δ, hδ, hc⟩ := hP.phase.smooth
  have hmem : (s₀ * r) ^ 2 ∈ Set.Ioi (-δ) := by
    simp only [Set.mem_Ioi]
    nlinarith [sq_nonneg (s₀ * r)]
  have hd : DifferentiableAt ℝ P.radialPhase ((s₀ * r) ^ 2) :=
    (hc.contDiffAt (isOpen_Ioi.mem_nhds hmem)).differentiableAt (by norm_num)
  have hφ : HasDerivAt (fun s : ℝ => P.radialPhase ((s * r) ^ 2))
      (deriv P.radialPhase ((s₀ * r) ^ 2) * (2 * s₀ * r ^ 2)) s₀ := by
    have h : HasDerivAt (fun s : ℝ => P.radialPhase ((s * r) ^ 2))
        (deriv P.radialPhase ((s₀ * r) ^ 2) * (((2 : ℕ) : ℝ) * (s₀ * r) ^ (2 - 1) * (1 * r))) s₀ :=
      hd.hasDerivAt.comp s₀ (((hasDerivAt_id' s₀).mul_const r).pow 2)
    exact h.congr_deriv (by ring)
  have hg : HasDerivAt (fun s : ℝ => ((c + jr * P.radialPhase ((s * r) ^ 2) : ℝ) : ℂ) * Complex.I)
      (((jr * (deriv P.radialPhase ((s₀ * r) ^ 2) * (2 * s₀ * r ^ 2)) : ℝ) : ℂ) * Complex.I) s₀ :=
    ((hφ.const_mul jr).const_add c).ofReal_comp.mul_const Complex.I
  have hall := (hasDerivAt_pow 2 s₀).smul ((hg.cexp.mul_const (A : ℂ)).mul hpk)
  refine ⟨_, hall, ?_⟩
  set E := Complex.exp (((c + jr * P.radialPhase ((s₀ * r) ^ 2) : ℝ) : ℂ) * Complex.I) with hEdef
  set dg := (((jr * (deriv P.radialPhase ((s₀ * r) ^ 2) * (2 * s₀ * r ^ 2)) : ℝ) : ℂ) * Complex.I) with hdg
  set τ' := r * P.chartLength / (s₀ * r + P.chartLength) ^ 2 with hτ'
  set pv := pk Q (s₀ * r / (s₀ * r + P.chartLength), x) with hpvdef
  set pd := pk (MvPolynomial.pderiv 0 Q) (s₀ * r / (s₀ * r + P.chartLength), x) with hpddef
  have hE1 : ‖E‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hA' : ‖(A : ℂ)‖ ≤ 1 := by rw [Complex.norm_real, Real.norm_eq_abs]; exact hA
  have key1 : ‖dg‖ * s₀ ≤ 2 * |jr| * Bφ := by
    rw [hdg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    calc |jr * (deriv P.radialPhase ((s₀ * r) ^ 2) * (2 * s₀ * r ^ 2))| * s₀
        = |jr * (deriv P.radialPhase ((s₀ * r) ^ 2) * (2 * s₀ * r ^ 2)) * s₀| := by
          rw [abs_mul _ s₀, abs_of_pos hs₀]
      _ = |2 * jr * ((s₀ * r) ^ 2 * deriv P.radialPhase ((s₀ * r) ^ 2))| := by congr 1; ring
      _ = 2 * |jr| * |(s₀ * r) ^ 2 * deriv P.radialPhase ((s₀ * r) ^ 2)| := by
          rw [abs_mul, abs_mul, abs_two]
      _ ≤ 2 * |jr| * Bφ := by gcongr
  have key2 : |τ'| * s₀ ≤ 1 := by
    rw [hτ', abs_of_nonneg (by positivity), div_mul_eq_mul_div, div_le_one (by positivity)]
    nlinarith [mul_pos hs₀ hr, hL, mul_pos (mul_pos hs₀ hr) hL]
  have n1 : ‖E * dg * (A : ℂ) * pv‖ ≤ ‖dg‖ * Bv := by
    rw [norm_mul, norm_mul, norm_mul, hE1]
    calc 1 * ‖dg‖ * ‖(A : ℂ)‖ * ‖pv‖ ≤ 1 * ‖dg‖ * 1 * Bv := by gcongr
      _ = ‖dg‖ * Bv := by ring
  have n2 : ‖E * (A : ℂ) * (τ' • pd)‖ ≤ |τ'| * Bv := by
    rw [norm_mul, norm_mul, norm_smul, hE1, Real.norm_eq_abs]
    calc 1 * ‖(A : ℂ)‖ * (|τ'| * ‖pd‖) ≤ 1 * 1 * (|τ'| * Bv) := by gcongr
      _ = |τ'| * Bv := by ring
  have n3 : ‖E * (A : ℂ) * pv‖ ≤ Bv := by
    rw [norm_mul, norm_mul, hE1]
    calc 1 * ‖(A : ℂ)‖ * ‖pv‖ ≤ 1 * 1 * Bv := by gcongr
      _ = Bv := by ring
  have a1 : s₀ ^ 2 * (‖dg‖ * Bv) ≤ s₀ * (2 * |jr| * Bφ * Bv) := by
    calc s₀ ^ 2 * (‖dg‖ * Bv) = s₀ * ((‖dg‖ * s₀) * Bv) := by ring
      _ ≤ s₀ * ((2 * |jr| * Bφ) * Bv) := by gcongr
      _ = s₀ * (2 * |jr| * Bφ * Bv) := by ring
  have a2 : s₀ ^ 2 * (|τ'| * Bv) ≤ s₀ * Bv := by
    calc s₀ ^ 2 * (|τ'| * Bv) = s₀ * ((|τ'| * s₀) * Bv) := by ring
      _ ≤ s₀ * (1 * Bv) := by gcongr
      _ = s₀ * Bv := by ring
  calc ‖s₀ ^ 2 • (E * dg * (A : ℂ) * pv + E * (A : ℂ) * (τ' • pd)) +
        ((2 : ℕ) * s₀ ^ (2 - 1)) • (E * (A : ℂ) * pv)‖
      ≤ s₀ ^ 2 * (‖dg‖ * Bv + |τ'| * Bv) + 2 * s₀ * Bv := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          gcongr
          exact (norm_add_le _ _).trans (add_le_add n1 n2)
        · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
          calc ((2 : ℕ) * s₀ ^ (2 - 1) : ℝ) * ‖E * (A : ℂ) * pv‖ ≤ ((2 : ℕ) * s₀ ^ (2 - 1) : ℝ) * Bv := by
                gcongr
            _ = 2 * s₀ * Bv := by norm_num
    _ ≤ s₀ * (2 * |jr| * Bφ * Bv + Bv + 2 * Bv) := by nlinarith [a1, a2]

theorem chart_continuousAt (L r s₀ : ℝ) (hne : s₀ * r + L ≠ 0) :
    ContinuousAt (fun s : ℝ => s * r / (s * r + L)) s₀ :=
  (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add continuousAt_const) hne

theorem chart_tendsto_right (L r s₀ : ℝ) (hL : 0 < L) (hr : 0 < r) (hs₀ : 0 < s₀) :
    Tendsto (fun s : ℝ => s * r / (s * r + L)) (𝓝[≥] s₀) (𝓝[≥] (s₀ * r / (s₀ * r + L))) := by
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    ((chart_continuousAt L r s₀ (by positivity)).tendsto.mono_left nhdsWithin_le_nhds) ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : s₀ ≤ s := hs
  show s₀ * r / (s₀ * r + L) ≤ s * r / (s * r + L)
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith [mul_nonneg (mul_nonneg hr.le hL.le) (sub_nonneg.2 hs')]

theorem phase_continuous (P : ShapeParams) (hP : IsShapeParams P) (c jr r : ℝ) :
    Continuous (fun s : ℝ => Complex.exp (((c + jr * P.radialPhase ((s * r) ^ 2) : ℝ) : ℂ) * Complex.I)) := by
  obtain ⟨δ, hδ, hc⟩ := hP.phase.smooth
  have hφ : Continuous (fun s : ℝ => P.radialPhase ((s * r) ^ 2)) :=
    hc.continuousOn.comp_continuous ((continuous_id.mul continuous_const).pow 2) (fun s => by
      simp only [Set.mem_Ioi]
      nlinarith [sq_nonneg (s * r)])
  exact Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.add (continuous_const.mul hφ))).mul continuous_const)

theorem scalarValue_raySlopeBound (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ) (b : Bool)
    (S : PotScalar) (σ : ℝ) (hS : IsJetAxis S.amp.tAxis 0 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal C)
      (fun s : ℝ => s ^ 2 • scalarValue P κ M b S σ (s • y)) (Metric.ball 1 (1 / 2)) := by
  obtain ⟨Bv, hBv0, hBv⟩ := cellValue_bounds S
  obtain ⟨Bφ, hBφ⟩ := hP.phase.scaled_bounded
  have hBφ0 : 0 ≤ Bφ := le_trans (abs_nonneg _) (hBφ 0 le_rfl).1
  have hL := hP.chartLength_pos
  set jr : ℝ := (κ.phaseIndex : ℝ) with hjr
  set K : ℝ := 2 * |jr| * Bφ * Bv + Bv + 2 * Bv with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * K, by positivity, fun y hy => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  set r := ‖y‖ with hrdef
  set x := heightRatio y with hx
  set A := sideFactor b S y with hA
  set c := 2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y with hc
  set f := fun s : ℝ => s ^ 2 • scalarValue P κ M b S σ (s • y) with hf
  have hray : ∀ s : ℝ, 0 < s → f s = s ^ 2 • (Complex.exp (((c + jr * P.radialPhase ((s * r) ^ 2) : ℝ) : ℂ) *
      Complex.I) * (A : ℂ) * cellValue S (s * r / (s * r + P.chartLength)) x) := by
    intro s hs
    simp only [hf]
    rw [scalarValue_ray P κ M b S σ y hs]
  have hxa : |x| ≤ 1 := height_le y
  have hex : ∀ s₀ : ℝ, ∃ D : ℂ, 0 < s₀ → HasDerivWithinAt f D (Ici s₀) s₀ ∧ ‖D‖ ≤ s₀ * K := by
    intro s₀
    by_cases hs₀ : 0 < s₀
    · set t₀ := s₀ * r / (s₀ * r + P.chartLength) with ht₀
      have ht0 : 0 ≤ t₀ := by positivity
      have ht1 : t₀ < 1 := by rw [ht₀, div_lt_one (by positivity)]; linarith
      set Q := weightedPiece S (cellIndex S.amp.tAxis.breaks t₀) (cellIndex S.amp.xAxis.breaks x) with hQ
      have hb := hBv t₀ t₀ x (abs_le.2 ⟨by linarith, ht1.le⟩) hxa
      obtain ⟨D, hD, hDb⟩ := ray_piece_deriv P hP c jr A r x Q hs₀ hr hBv0 (sideFactor_abs_le b S y)
        hb.1 hb.2 (hBφ ((s₀ * r) ^ 2) (sq_nonneg _)).1
      refine ⟨D, fun _ => ⟨hD.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_, hDb⟩⟩
      · have hev := (chart_tendsto_right P.chartLength r s₀ hL hr hs₀).eventually (cellValue_right S t₀ x)
        filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
        have hs0 : 0 < s := lt_of_lt_of_le hs₀ hs1
        rw [hray s hs0, hs]
      · rw [hray s₀ hs₀, cellValue, ← ht₀]
    · exact ⟨0, fun h => absurd h hs₀⟩
  choose D hD using hex
  have hco : ContinuousOn f (Ioi 0) := by
    intro s hs
    have hs0 : (0 : ℝ) < s := hs
    have hca : ContinuousAt (fun s : ℝ => s ^ 2 • (Complex.exp (((c + jr * P.radialPhase ((s * r) ^ 2) : ℝ) : ℂ) *
        Complex.I) * (A : ℂ) * cellValue S (s * r / (s * r + P.chartLength)) x)) s :=
      (continuousAt_id.pow 2).smul (((phase_continuous P hP c jr r).continuousAt.mul continuousAt_const).mul
        ((cellValue_continuous S hS x).continuousAt.comp (chart_continuousAt P.chartLength r s (by positivity))))
    refine (hca.congr ?_).continuousWithinAt
    filter_upwards [eventually_gt_nhds hs0] with s' hs'
    exact (hray s' hs').symm
  have key : ∀ u v : ℝ, u ∈ Metric.ball (1 : ℝ) (1 / 2) → v ∈ Metric.ball (1 : ℝ) (1 / 2) → u ≤ v →
      ‖f v - f u‖ ≤ 2 * K * (v - u) := by
    intro u v hu hv huv
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu hv
    refine norm_image_sub_le_of_norm_deriv_right_le_segment (f' := D)
      (hco.mono fun s hs => show (0 : ℝ) < s by linarith [hs.1])
      (fun s hs => (hD s (by linarith [hs.1])).1)
      (fun s hs => ((hD s (by linarith [hs.1])).2).trans ?_) v (right_mem_Icc.2 huv)
    have : s < 2 := by linarith [hs.2]
    nlinarith
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, Real.dist_eq]
  rcases le_total u v with h | h
  · rw [norm_sub_rev, abs_of_nonpos (by linarith)]
    have := key u v hu hv h
    linarith
  · rw [abs_of_nonneg (by linarith)]
    exact key v u hv hu h

theorem pk_differentiable (Q : MvPolynomial (Fin 2) ℂ) : Differentiable ℝ (pk Q) := by
  have hfst : Differentiable ℝ (fun z : ℝ × ℝ => ((z.1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp differentiable_fst
  have hsnd : Differentiable ℝ (fun z : ℝ × ℝ => ((z.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp differentiable_snd
  induction Q using MvPolynomial.induction_on with
  | C a =>
    have e : pk (MvPolynomial.C a) = fun _ => a := funext fun z => by simp [pk]
    rw [e]
    exact differentiable_const a
  | add p q hp hq =>
    have e : pk (p + q) = fun z => pk p z + pk q z := funext fun z => by simp [pk]
    rw [e]
    exact hp.add hq
  | mul_X p i hp =>
    fin_cases i
    · have e : pk (p * MvPolynomial.X 0) = fun z => pk p z * ((z.1 : ℝ) : ℂ) := funext fun z => by simp [pk]
      show Differentiable ℝ (pk (p * MvPolynomial.X 0))
      rw [e]
      exact hp.mul hfst
    · have e : pk (p * MvPolynomial.X 1) = fun z => pk p z * ((z.2 : ℝ) : ℂ) := funext fun z => by simp [pk]
      show Differentiable ℝ (pk (p * MvPolynomial.X 1))
      rw [e]
      exact hp.mul hsnd

theorem ae_chartCoord_ne (P : ShapeParams) (hP : IsShapeParams P) (b' : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), chartCoord P y ≠ b' := by
  have hL := hP.chartLength_pos
  by_cases hb : b' = 1
  · refine Eventually.of_forall fun y => ?_
    rw [hb]
    exact (chartCoord_mem P hP y).2.ne
  · refine ae_iff.2 (measure_mono_null (t := Metric.sphere (0 : Space) (b' * P.chartLength / (1 - b')))
      (fun y hy => ?_) (Measure.addHaar_sphere volume 0 _))
    simp only [Set.mem_ofPred_eq, not_not] at hy
    rw [mem_sphere_zero_iff_norm]
    have h1 : 1 - b' ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
    have hpos : ‖y‖ + P.chartLength ≠ 0 := by positivity
    rw [eq_div_iff h1]
    unfold chartCoord at hy
    rw [div_eq_iff hpos] at hy
    linarith

theorem ae_heightRatio_ne (b' : ℝ) : ∀ᵐ y ∂(volume : Measure Space), heightRatio y ≠ b' := by
  refine ae_iff.2 (measure_mono_null (fun y hy => ?_) (FracInternal.cone_null b'))
  simp only [Set.mem_ofPred_eq, not_not] at hy ⊢
  rcases eq_or_ne y 0 with h | h
  · subst h
    simp
  · have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 h
    unfold heightRatio at hy
    rw [div_eq_iff hn] at hy
    exact hy

theorem heightRatio_sq_lt {y : Space} (hy : y 1 ≠ 0) : heightRatio y ^ 2 < 1 := by
  have hy0 : y ≠ 0 := fun h => hy (by rw [h]; rfl)
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy0
  have hs := SphericalDivInternal.coords_sq y
  unfold heightRatio
  rw [div_pow, div_lt_one (by positivity)]
  have : 0 < y 1 * y 1 := mul_self_pos.2 hy
  nlinarith [mul_self_nonneg (y 0)]

theorem scalarValue_ae_differentiable (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (M : ℤ)
    (b : Bool) (S : PotScalar) (σ : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 ∧ DifferentiableAt ℝ (scalarValue P κ M b S σ) y := by
  have hL := hP.chartLength_pos
  set mt := (S.amp.tAxis.breaks.drop 1).dropLast with hmt
  set mx := (S.amp.xAxis.breaks.drop 1).dropLast with hmx
  filter_upwards [FracInternal.ae_coord_ne_zero 1,
    (eventually_all_finset mt.toFinset).2 (fun b' _ => ae_chartCoord_ne P hP b'),
    (eventually_all_finset mx.toFinset).2 (fun b' _ => ae_heightRatio_ne b')] with y hy1 hyt hyx
  have hy0 : y ≠ 0 := fun h => hy1 (by rw [h]; rfl)
  refine ⟨hy0, ?_⟩
  have hmt' : chartCoord P y ∉ mt := fun h => hyt _ (List.mem_toFinset.2 h) rfl
  have hmx' : heightRatio y ∉ mx := fun h => hyx _ (List.mem_toFinset.2 h) rfl
  obtain ⟨Lc, hLc, -⟩ := SphericalDivInternal.chartCoord_hasFDerivAt P hL hy0
  obtain ⟨Lh, hLh, -⟩ := SphericalDivInternal.heightRatio_hasFDerivAt hy0
  obtain ⟨La, hLa, -⟩ := SphericalDivInternal.pointAngle_hasFDerivAt (Or.inr hy1)
  obtain ⟨Lφ, hLφ, -⟩ := SphericalDivInternal.radialPhase_hasFDerivAt hP.phase y
  set Q := weightedPiece S (cellIndex S.amp.tAxis.breaks (chartCoord P y))
    (cellIndex S.amp.xAxis.breaks (heightRatio y)) with hQ
  have hev : ∀ᶠ z in 𝓝 y, scalarValue P κ M b S σ z = Complex.exp ((phaseAngle P κ M σ z : ℂ) * Complex.I) *
      (sideFactor b S z : ℂ) * pk Q (chartCoord P z, heightRatio z) := by
    filter_upwards [hLc.continuousAt.tendsto.eventually (cellIndex_nhds S.amp.tAxis.breaks hmt'),
      hLh.continuousAt.tendsto.eventually (cellIndex_nhds S.amp.xAxis.breaks hmx')] with z hz1 hz2
    rw [scalarValue_eq, cellValue, hz1, hz2]
  refine DifferentiableAt.congr_of_eventuallyEq ?_ hev
  have hph : DifferentiableAt ℝ (phaseAngle P κ M σ) y := by
    unfold phaseAngle
    exact ((differentiableAt_const _).add (hLa.differentiableAt.const_mul _)).add
      (hLφ.differentiableAt.const_mul _)
  have hph' : DifferentiableAt ℝ (fun z => ((phaseAngle P κ M σ z : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y hph
  have hq : DifferentiableAt ℝ (fun z => 1 - heightRatio z ^ 2) y :=
    (differentiableAt_const _).sub (hLh.differentiableAt.pow 2)
  have hsd : DifferentiableAt ℝ (sideFactor b S) y := by
    unfold sideFactor polarSine
    cases b
    · simp only [Bool.false_eq_true, if_false]
      exact (hq.pow _).mul (differentiableAt_const _)
    · simp only [if_true]
      exact (hq.pow _).mul (hq.sqrt (by linarith [heightRatio_sq_lt hy1]))
  have hsd' : DifferentiableAt ℝ (fun z => ((sideFactor b S z : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y hsd
  exact ((hph'.mul_const Complex.I).cexp.mul hsd').mul
    ((pk_differentiable Q).differentiableAt.comp y (hLc.differentiableAt.prodMk hLh.differentiableAt))

end Internal.RadialFlux

end PotentialShape

end Breakdown

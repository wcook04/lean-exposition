import Breakdown.CellReduction.PotFluxDecayJet
import Breakdown.CertCell.ShapeSphericalDiv
import Breakdown.FracCell.GivenToolkit

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (weightPoly heightRatio radialVec polarVecQ azimVecQ radialScale heightDeriv cellIndex)

namespace FluxDecay.Internal

def angularPart (k : ℕ) (withSine : Bool) (x : ℝ) : ℝ :=
  (1 - x ^ 2) ^ k * (if withSine then Real.sqrt (1 - x ^ 2) else 1)

def scalarAmp (S : PotScalar) (withSine : Bool) (t x : ℝ) : ℂ :=
  weightPoly S.lowOrder S.highOrder t * (angularPart S.axisPower withSine x : ℂ) * S.amp.toSpline.evalHalf t x

def shiftedParams (P : ShapeParams) (M : ℤ) : ShapeParams :=
  { P with azimuthOrder := if M = 0 then P.azimuthOrder else M.natAbs }

def shiftedKey (κ : FieldKey) (M : ℤ) : FieldKey := ⟨(M.sign, 1), κ.phaseIndex⟩

def shiftedTime (κ : FieldKey) (M : ℤ) (σ : ℝ) : ℝ :=
  (labelTime κ.label : ℝ) * σ / (labelTime (M.sign, 1) : ℝ)

def fluxAmps (K : PotKeyData) (c : PotComponent) (t x : ℝ) : Fin 3 → ℂ :=
  ![scalarAmp (K.radialFlux c) c.carriesSine t x, scalarAmp (K.polarFlux c) c.carriesSine t x, 0]

theorem shiftedParams_valid {P : ShapeParams} (hP : IsShapeParams P) (M : ℤ) :
    IsShapeParams (shiftedParams P M) := by
  refine ⟨hP.chartLength_pos, ?_, hP.phase, hP.origin⟩
  show 0 < (if M = 0 then P.azimuthOrder else M.natAbs)
  split_ifs with h
  · exact hP.azimuthOrder_pos
  · exact Int.natAbs_pos.2 h

theorem labelTime_shifted_ne (M : ℤ) : (labelTime (M.sign, 1) : ℝ) ≠ 0 := by
  unfold labelTime
  rcases lt_trichotomy M 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h]; norm_num
  · rw [h]; norm_num
  · rw [Int.sign_eq_one_of_pos h]; norm_num

theorem labelAzimuth_shifted (P : ShapeParams) (M : ℤ) :
    labelAzimuth (shiftedParams P M).azimuthOrder (M.sign, 1) = M := by
  unfold labelAzimuth shiftedParams
  simp only
  split_ifs with h
  · rw [h]; simp
  · exact Int.sign_mul_natAbs M

theorem keyPhase_shifted (P : ShapeParams) (κ : FieldKey) (M : ℤ) (σ : ℝ) (y : Space) :
    keyPhase (shiftedParams P M) (shiftedKey κ M) (shiftedTime κ M σ) y =
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) := by
  unfold keyPhase
  have h1 := labelTime_shifted_ne M
  have h2 := labelAzimuth_shifted P M
  have e : 2 * Real.pi * (labelTime (shiftedKey κ M).label : ℝ) * shiftedTime κ M σ +
      (labelAzimuth (shiftedParams P M).azimuthOrder (shiftedKey κ M).label : ℝ) * pointAngle y +
      ((shiftedKey κ M).phaseIndex : ℝ) * (shiftedParams P M).radialPhase (‖y‖ ^ 2) =
      2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle y +
        (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) := by
    simp only [shiftedKey, shiftedTime]
    rw [h2]
    field_simp
    rfl
  rw [e]

theorem scalarValue_eq (P : ShapeParams) (κ : FieldKey) (M : ℤ) (w : Bool) (S : PotScalar) (σ : ℝ) (y : Space) :
    scalarValue P κ M w S σ y = keyPhase (shiftedParams P M) (shiftedKey κ M) (shiftedTime κ M σ) y *
      scalarAmp S w (chartCoord P y) (heightRatio y) := by
  rw [keyPhase_shifted]
  unfold scalarValue scalarAmp angularPart polarSine
  push_cast
  ring

theorem fluxVector_eq (P : ShapeParams) (κ : FieldKey) (K : PotKeyData) (c : PotComponent) (σ : ℝ) :
    fluxVector P κ K c σ = framedField (shiftedParams P (labelAzimuth P.azimuthOrder κ.label + c.shift))
      (shiftedKey κ (labelAzimuth P.azimuthOrder κ.label + c.shift))
      (shiftedTime κ (labelAzimuth P.azimuthOrder κ.label + c.shift) σ) (fluxAmps K c) := by
  funext y i
  simp only [fluxVector, componentValue, framedField, fluxAmps, scalarValue_eq]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons,
    zero_mul, add_zero]
  have e : chartCoord (shiftedParams P (labelAzimuth P.azimuthOrder κ.label + c.shift)) y = chartCoord P y := rfl
  rw [e]
  ring

theorem keyPhase_norm (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (y : Space) : ‖keyPhase P κ σ y‖ = 1 := by
  unfold keyPhase
  exact Complex.norm_exp_ofReal_mul_I _

theorem angularPart_nonneg (k : ℕ) (w : Bool) {x : ℝ} (hx : |x| ≤ 1) : 0 ≤ angularPart k w x := by
  have hu : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x]
  unfold angularPart
  split_ifs <;> positivity

theorem angularPart_le_one (k : ℕ) (w : Bool) {x : ℝ} (hx : |x| ≤ 1) : angularPart k w x ≤ 1 := by
  have hu : 0 ≤ 1 - x ^ 2 := by nlinarith [abs_le.1 hx, sq_abs x]
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  unfold angularPart
  have hk : (1 - x ^ 2) ^ k ≤ 1 := pow_le_one₀ hu hu1
  have hk0 : 0 ≤ (1 - x ^ 2) ^ k := pow_nonneg hu k
  split_ifs
  · have hs : Real.sqrt (1 - x ^ 2) ≤ 1 := Real.sqrt_le_one.2 hu1
    have hs0 := Real.sqrt_nonneg (1 - x ^ 2)
    nlinarith
  · linarith

theorem weightPoly_norm_le (e0 e1 : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ‖weightPoly e0 e1 t‖ ≤ (1 - t) ^ e1 := by
  unfold weightPoly
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by have h : 0 ≤ 1 - t := (by linarith); positivity)]
  have : t ^ e0 ≤ 1 := pow_le_one₀ h0 h1
  have : 0 ≤ (1 - t) ^ e1 := pow_nonneg (by linarith) e1
  nlinarith

theorem weightDeriv_bound (e0 e1 : ℕ) {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t * (1 - t) * |(e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1) * (-1))| ≤
      (e0 + e1) * (1 - t) ^ e1 := by
  have hu : 0 ≤ 1 - t := by linarith
  have hA : 0 ≤ (e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 := by positivity
  have hB : 0 ≤ t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) := by positivity
  have habs : |(e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1) * (-1))| ≤
      (e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) :=
    abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have ha : t * ((e0 : ℝ) * t ^ (e0 - 1)) = e0 * t ^ e0 := mul_pow_pred_eq t e0
  have hb : (1 - t) * ((e1 : ℝ) * (1 - t) ^ (e1 - 1)) = e1 * (1 - t) ^ e1 := mul_pow_pred_eq (1 - t) e1
  have htp : t ^ e0 ≤ 1 := pow_le_one₀ h0 h1
  have htp0 : 0 ≤ t ^ e0 := pow_nonneg h0 e0
  have hup : 0 ≤ (1 - t) ^ e1 := pow_nonneg hu e1
  have hstep : t * (1 - t) * ((e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1))) =
      ((e0 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * (1 - t)) + ((e1 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * t) := by
    linear_combination ((1 - t) * (1 - t) ^ e1) * ha + (t ^ e0 * t) * hb
  have hp1 : ((e0 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * (1 - t)) ≤ (e0 : ℝ) * (1 - t) ^ e1 :=
    mul_le_of_le_one_right (by positivity) (by nlinarith)
  have hp2 : ((e1 : ℝ) * (1 - t) ^ e1) * (t ^ e0 * t) ≤ (e1 : ℝ) * (1 - t) ^ e1 :=
    mul_le_of_le_one_right (by positivity) (by nlinarith)
  calc _ ≤ t * (1 - t) * ((e0 : ℝ) * t ^ (e0 - 1) * (1 - t) ^ e1 + t ^ e0 * ((e1 : ℝ) * (1 - t) ^ (e1 - 1))) :=
        mul_le_mul_of_nonneg_left habs (by positivity)
    _ ≤ _ := by rw [hstep]; linarith


theorem sq_lt_one_of_abs {x : ℝ} (hx : |x| < 1) : x ^ 2 < 1 := by
  have h := abs_lt.1 hx
  nlinarith

theorem polarAngular_hasDerivAt (k : ℕ) (w : Bool) {x : ℝ} (hx : |x| < 1) :
    ∃ b' : ℝ, HasDerivAt (fun s => (1 - s ^ 2) * angularPart k w s) b' x ∧ |b'| ≤ 2 * k + 3 := by
  have hx2 := sq_lt_one_of_abs hx
  have hu0 : 0 < 1 - x ^ 2 := by linarith
  have hu1 : 1 - x ^ 2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hxa := abs_lt.1 hx
  have hu : HasDerivAt (fun s : ℝ => 1 - s ^ 2) (-((2 : ℕ) * x ^ (2 - 1))) x := (hasDerivAt_pow 2 x).const_sub 1
  cases w with
  | false =>
    refine ⟨((k + 1 : ℕ) : ℝ) * (1 - x ^ 2) ^ (k + 1 - 1) * -((2 : ℕ) * x ^ (2 - 1)), ?_, ?_⟩
    · have e : (fun s => (1 - s ^ 2) * angularPart k false s) = fun s => (1 - s ^ 2) ^ (k + 1) := by
        funext s
        simp only [angularPart, Bool.false_eq_true, if_false, mul_one]
        ring
      rw [e]
      exact hu.pow (k + 1)
    · simp only [Nat.add_sub_cancel, Nat.cast_ofNat]
      have hp0 : 0 ≤ (1 - x ^ 2) ^ k := pow_nonneg hu0.le k
      have hp1 : (1 - x ^ 2) ^ k ≤ 1 := pow_le_one₀ hu0.le hu1
      rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_of_nonneg hp0, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)),
        abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      push_cast
      have hxx : |x| ≤ 1 := hx.le
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : ((k : ℝ) + 1) * (1 - x ^ 2) ^ k ≤ (k : ℝ) + 1 := by nlinarith
      simp only [pow_one]
      have h3 := mul_le_mul h1 hxx (abs_nonneg x) (by positivity)
      nlinarith
  | true =>
    set r := Real.sqrt (1 - x ^ 2) with hr
    have hr0 : 0 < r := Real.sqrt_pos.2 hu0
    have hr1 : r ≤ 1 := Real.sqrt_le_one.2 hu1
    have hs := hu.sqrt hu0.ne'
    refine ⟨((2 * k + 3 : ℕ) : ℝ) * r ^ (2 * k + 3 - 1) * (-((2 : ℕ) * x ^ (2 - 1)) / (2 * r)), ?_, ?_⟩
    · have hev : (fun s => (1 - s ^ 2) * angularPart k true s) =ᶠ[nhds x]
          fun s => Real.sqrt (1 - s ^ 2) ^ (2 * k + 3) := by
        filter_upwards [continuousAt_const.eventually_lt hu.continuousAt hu0] with s hs0
        simp only [angularPart, if_true]
        rw [show 2 * k + 3 = 2 * (k + 1) + 1 by ring, pow_succ (Real.sqrt (1 - s ^ 2)), pow_mul, Real.sq_sqrt hs0.le]
        ring
      exact (hs.pow (2 * k + 3)).congr_of_eventuallyEq hev
    · have e : ((2 * k + 3 : ℕ) : ℝ) * r ^ (2 * k + 3 - 1) * (-((2 : ℕ) * x ^ (2 - 1)) / (2 * r)) =
          -(((2 * k + 3 : ℕ) : ℝ) * x * r ^ (2 * k + 1)) := by
        rw [show 2 * k + 3 - 1 = (2 * k + 1) + 1 by omega, pow_succ]
        field_simp
        push_cast
        ring
      rw [e, abs_neg, abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((2 * k + 3 : ℕ) : ℝ)),
        abs_of_nonneg (pow_nonneg hr0.le _)]
      have hp1 : r ^ (2 * k + 1) ≤ 1 := pow_le_one₀ hr0.le hr1
      have hp0 : 0 ≤ r ^ (2 * k + 1) := pow_nonneg hr0.le _
      have hxx : |x| ≤ 1 := hx.le
      push_cast
      have hk0 : (0 : ℝ) ≤ 2 * k + 3 := by positivity
      have : |x| * r ^ (2 * k + 1) ≤ 1 := by nlinarith [abs_nonneg x]
      nlinarith

theorem scalarAmp_bound (S : PotScalar) (w : Bool) (hs : S.amp.tAxis.breaks.Pairwise (· < ·))
    (h0 : S.amp.tAxis.breaks.head? = some 0) (h1 : S.amp.tAxis.breaks.getLast? = some 1)
    (hend : ∃ z ≤ S.amp.tAxis.depth, 2 ≤ S.highOrder + z ∧ EndVanishOrder S.amp z) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| ≤ 1 →
      ‖scalarAmp S w t x‖ ≤ B * (1 - t) ^ 2 ∧
      (t ∉ (S.amp.tAxis.breaks.drop 1).dropLast → ∃ g : ℂ,
        HasDerivAt (fun s => scalarAmp S w s x) g t ∧ t * (1 - t) * ‖g‖ ≤ B * (1 - t) ^ 2) ∧
      (x ∉ (S.amp.xAxis.breaks.drop 1).dropLast → |x| < 1 → ∃ g : ℂ,
        HasDerivAt (fun s => polarFactor s * scalarAmp S w t s) g x ∧ ‖g‖ ≤ B * (1 - t) ^ 2) := by
  obtain ⟨z, hz, h2, hv⟩ := hend
  obtain ⟨B0, hB0, hb⟩ := jetEnd_bound S.amp z hz hs h0 h1 hv
  refine ⟨(S.lowOrder + S.highOrder + 2 * S.axisPower + 5) * B0, by positivity, fun t x ht0 ht1 hx => ?_⟩
  obtain ⟨hg0, hgt, hgx⟩ := hb t x ht0 ht1 hx
  have hu : 0 ≤ 1 - t := by linarith
  have hpow : (1 - t) ^ S.highOrder * (1 - t) ^ z ≤ (1 - t) ^ 2 := by
    rw [← pow_add]
    exact pow_le_pow_of_le_one hu (by linarith) h2
  have hW := weightPoly_norm_le S.lowOrder S.highOrder ht0 ht1
  have hA0 := angularPart_nonneg S.axisPower w hx
  have hA1 := angularPart_le_one S.axisPower w hx
  have hAn : ‖((angularPart S.axisPower w x : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0]
    exact hA1
  have he1 : 0 ≤ (1 - t) ^ S.highOrder := pow_nonneg hu _
  have hez : 0 ≤ (1 - t) ^ z := pow_nonneg hu _
  have hfin : ∀ c : ℝ, 0 ≤ c → c ≤ S.lowOrder + S.highOrder + 2 * S.axisPower + 5 →
      (1 - t) ^ S.highOrder * (c * (B0 * (1 - t) ^ z)) ≤
        (S.lowOrder + S.highOrder + 2 * S.axisPower + 5) * B0 * (1 - t) ^ 2 := by
    intro c hc0 hc
    calc (1 - t) ^ S.highOrder * (c * (B0 * (1 - t) ^ z)) = (c * B0) * ((1 - t) ^ S.highOrder * (1 - t) ^ z) := by ring
      _ ≤ (c * B0) * (1 - t) ^ 2 := by gcongr
      _ ≤ _ := by gcongr
  refine ⟨?_, ?_, ?_⟩
  · show ‖weightPoly S.lowOrder S.highOrder t * ((angularPart S.axisPower w x : ℝ) : ℂ) *
      S.amp.toSpline.evalHalf t x‖ ≤ _
    rw [norm_mul, norm_mul]
    calc ‖weightPoly S.lowOrder S.highOrder t‖ * ‖((angularPart S.axisPower w x : ℝ) : ℂ)‖ *
          ‖S.amp.toSpline.evalHalf t x‖ ≤ (1 - t) ^ S.highOrder * 1 * (B0 * (1 - t) ^ z) := by gcongr
      _ = (1 - t) ^ S.highOrder * (1 * (B0 * (1 - t) ^ z)) := by ring
      _ ≤ _ := hfin 1 zero_le_one (by norm_cast; omega)
  · intro htn
    obtain ⟨g, hg, hgb⟩ := hgt htn
    have hw : HasDerivAt (fun s : ℝ => s ^ S.lowOrder * (1 - s) ^ S.highOrder)
        ((S.lowOrder : ℝ) * t ^ (S.lowOrder - 1) * (1 - t) ^ S.highOrder +
          t ^ S.lowOrder * ((S.highOrder : ℝ) * (1 - t) ^ (S.highOrder - 1) * (-1))) t :=
      (hasDerivAt_pow S.lowOrder t).mul (((hasDerivAt_id' t).const_sub 1).pow S.highOrder)
    have hfull := (hw.ofReal_comp.mul_const ((angularPart S.axisPower w x : ℝ) : ℂ)).mul hg
    refine ⟨_, hfull, ?_⟩
    have hwd := weightDeriv_bound S.lowOrder S.highOrder ht0 ht1
    set dW : ℝ := (S.lowOrder : ℝ) * t ^ (S.lowOrder - 1) * (1 - t) ^ S.highOrder +
          t ^ S.lowOrder * ((S.highOrder : ℝ) * (1 - t) ^ (S.highOrder - 1) * (-1)) with hdW
    have hgt0 : 0 ≤ t * (1 - t) := by positivity
    have hn1 : ‖(dW : ℂ) * ((angularPart S.axisPower w x : ℝ) : ℂ) * S.amp.toSpline.evalHalf t x‖ ≤
        |dW| * (B0 * (1 - t) ^ z) := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      calc |dW| * ‖((angularPart S.axisPower w x : ℝ) : ℂ)‖ * ‖S.amp.toSpline.evalHalf t x‖ ≤
          |dW| * 1 * (B0 * (1 - t) ^ z) := by gcongr
        _ = _ := by ring
    have hn2 : ‖((t ^ S.lowOrder * (1 - t) ^ S.highOrder : ℝ) : ℂ) * ((angularPart S.axisPower w x : ℝ) : ℂ) * g‖ ≤
        (1 - t) ^ S.highOrder * ‖g‖ := by
      rw [norm_mul, norm_mul]
      have := weightPoly_norm_le S.lowOrder S.highOrder ht0 ht1
      calc ‖((t ^ S.lowOrder * (1 - t) ^ S.highOrder : ℝ) : ℂ)‖ * ‖((angularPart S.axisPower w x : ℝ) : ℂ)‖ * ‖g‖ ≤
          (1 - t) ^ S.highOrder * 1 * ‖g‖ := by gcongr; exact this
        _ = _ := by ring
    calc t * (1 - t) * ‖(dW : ℂ) * ((angularPart S.axisPower w x : ℝ) : ℂ) * S.amp.toSpline.evalHalf t x +
          ((t ^ S.lowOrder * (1 - t) ^ S.highOrder : ℝ) : ℂ) * ((angularPart S.axisPower w x : ℝ) : ℂ) * g‖
        ≤ t * (1 - t) * (|dW| * (B0 * (1 - t) ^ z) + (1 - t) ^ S.highOrder * ‖g‖) := by
          gcongr
          exact (norm_add_le _ _).trans (add_le_add hn1 hn2)
      _ = (t * (1 - t) * |dW|) * (B0 * (1 - t) ^ z) + (1 - t) ^ S.highOrder * (t * ((1 - t) * ‖g‖)) := by ring
      _ ≤ ((S.lowOrder + S.highOrder) * (1 - t) ^ S.highOrder) * (B0 * (1 - t) ^ z) +
          (1 - t) ^ S.highOrder * (1 * (B0 * (1 - t) ^ z)) := by
          refine add_le_add (mul_le_mul_of_nonneg_right hwd (by positivity)) (mul_le_mul_of_nonneg_left ?_ he1)
          calc t * ((1 - t) * ‖g‖) ≤ 1 * ((1 - t) * ‖g‖) := by gcongr
            _ ≤ 1 * (B0 * (1 - t) ^ z) := by gcongr
      _ = (1 - t) ^ S.highOrder * ((S.lowOrder + S.highOrder + 1) * (B0 * (1 - t) ^ z)) := by ring
      _ ≤ _ := hfin _ (by positivity) (by have := (Nat.cast_nonneg (α := ℝ) S.axisPower); linarith)
  · intro hxn hx1
    obtain ⟨g, hg, hgb⟩ := hgx hxn
    obtain ⟨b', hb', hbb⟩ := polarAngular_hasDerivAt S.axisPower w hx1
    have e : (fun s => polarFactor s * scalarAmp S w t s) = fun s => weightPoly S.lowOrder S.highOrder t *
        ((((1 - s ^ 2) * angularPart S.axisPower w s : ℝ) : ℂ) * S.amp.toSpline.evalHalf t s) := by
      funext s
      simp only [polarFactor, scalarAmp]
      push_cast
      ring
    rw [e]
    refine ⟨_, (hb'.ofReal_comp.mul hg).const_mul _, ?_⟩
    have hx2 := sq_lt_one_of_abs hx1
    have hbx0 : 0 ≤ (1 - x ^ 2) * angularPart S.axisPower w x := mul_nonneg (by linarith) hA0
    have hbx1 : (1 - x ^ 2) * angularPart S.axisPower w x ≤ 1 := by
      have : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith
    rw [norm_mul]
    calc ‖weightPoly S.lowOrder S.highOrder t‖ * ‖(b' : ℂ) * S.amp.toSpline.evalHalf t x +
          (((1 - x ^ 2) * angularPart S.axisPower w x : ℝ) : ℂ) * g‖
        ≤ (1 - t) ^ S.highOrder * (|b'| * (B0 * (1 - t) ^ z) + 1 * (B0 * (1 - t) ^ z)) := by
          gcongr
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            gcongr
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hbx0]
            gcongr
      _ = (1 - t) ^ S.highOrder * ((|b'| + 1) * (B0 * (1 - t) ^ z)) := by ring
      _ ≤ _ := hfin _ (by positivity) (by
          have := (Nat.cast_nonneg (α := ℝ) S.lowOrder)
          have := (Nat.cast_nonneg (α := ℝ) S.highOrder)
          linarith)

theorem scalarAmp_differentiableAt (S : PotScalar) (w : Bool) {t x : ℝ}
    (ht : t ∉ (S.amp.tAxis.breaks.drop 1).dropLast) (hx : x ∉ (S.amp.xAxis.breaks.drop 1).dropLast)
    (hx1 : |x| < 1) : DifferentiableAt ℝ (fun z : ℝ × ℝ => scalarAmp S w z.1 z.2) (t, x) := by
  have hu : 0 < 1 - x ^ 2 := by linarith [sq_lt_one_of_abs hx1]
  have h1 : DifferentiableAt ℝ (fun z : ℝ × ℝ => weightPoly S.lowOrder S.highOrder z.1) (t, x) := by
    have : DifferentiableAt ℝ (fun z : ℝ × ℝ => z.1 ^ S.lowOrder * (1 - z.1) ^ S.highOrder) (t, x) := by fun_prop
    exact Complex.ofRealCLM.differentiableAt.comp (t, x) this
  have ha : DifferentiableAt ℝ (fun s : ℝ => angularPart S.axisPower w s) x := by
    unfold angularPart
    cases w with
    | false => simp only [Bool.false_eq_true, if_false]; fun_prop
    | true =>
      simp only [if_true]
      exact (((differentiableAt_id.pow 2).const_sub 1).pow _).mul
        (((differentiableAt_id.pow 2).const_sub 1).sqrt hu.ne')
  have h2a : DifferentiableAt ℝ (fun z : ℝ × ℝ => angularPart S.axisPower w z.2) (t, x) := by
    have hc := DifferentiableAt.comp (x := (t, x)) (g := fun s : ℝ => angularPart S.axisPower w s)
      (f := Prod.snd) ha differentiableAt_snd
    exact hc
  have h2 : DifferentiableAt ℝ (fun z : ℝ × ℝ => ((angularPart S.axisPower w z.2 : ℝ) : ℂ)) (t, x) :=
    Complex.ofRealCLM.differentiableAt.comp (t, x) h2a
  have h3 : DifferentiableAt ℝ (fun z : ℝ × ℝ => S.amp.toSpline.evalHalf z.1 z.2) (t, x) := by
    have hp := ((FracInternal.mvPoly_eval_contDiff (S.amp.toSpline.piece (cellIndex S.amp.tAxis.breaks t)
      (cellIndex S.amp.xAxis.breaks x)) (f := Prod.fst) (g := Prod.snd) contDiff_fst contDiff_snd).differentiable
        (by simp)) (t, x)
    exact hp.congr_of_eventuallyEq (FracInternal.ProfilePowerJumpsPieces.evalHalf_eventuallyEq _ ht hx)
  exact (h1.mul h2).mul h3

def FluxScalarEnd (S : PotScalar) : Prop :=
  S.amp.tAxis.breaks.Pairwise (· < ·) ∧ S.amp.tAxis.breaks.head? = some 0 ∧
    S.amp.tAxis.breaks.getLast? = some 1 ∧
    ∃ z ≤ S.amp.tAxis.depth, 2 ≤ S.highOrder + z ∧ EndVanishOrder S.amp z

theorem phaseSlope_abs_le (P : ShapeParams) {B : ℝ}
    (hB : ∀ s, 0 ≤ s → |s * deriv P.radialPhase s| ≤ B) (t : ℝ) : |phaseSlope P t| ≤ 2 * |B| := by
  unfold phaseSlope
  have h := hB (chartRadius P t ^ 2) (sq_nonneg _)
  rw [show 2 * chartRadius P t ^ 2 * deriv P.radialPhase (chartRadius P t ^ 2) =
    2 * (chartRadius P t ^ 2 * deriv P.radialPhase (chartRadius P t ^ 2)) by ring, abs_mul]
  have := le_abs_self B
  rw [abs_two]
  linarith

theorem framedFormula_bound (P : ShapeParams) (hP : IsShapeParams P) (K : PotKeyData) (c : PotComponent)
    (j m : ℤ) (hr : FluxScalarEnd (K.radialFlux c)) (hp : FluxScalarEnd (K.polarFlux c)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t x : ℝ, 0 ≤ t → t ≤ 1 → |x| < 1 →
      t ∉ ((K.radialFlux c).amp.tAxis.breaks.drop 1).dropLast →
      x ∉ ((K.polarFlux c).amp.xAxis.breaks.drop 1).dropLast →
      ‖shiftedScale P j (fun t x => fluxAmps K c t x 0) t x + 2 * fluxAmps K c t x 0 -
        heightDeriv (fun t x => polarFactor x * fluxAmps K c t x 1) t x +
        Complex.I * (m : ℂ) * fluxAmps K c t x 2‖ ≤ C * (1 - t) ^ 2 := by
  obtain ⟨Bφ, hBφ⟩ := hP.phase.scaled_bounded
  obtain ⟨Br, hBr0, hbr⟩ := scalarAmp_bound (K.radialFlux c) c.carriesSine hr.1 hr.2.1 hr.2.2.1 hr.2.2.2
  obtain ⟨Bp, hBp0, hbp⟩ := scalarAmp_bound (K.polarFlux c) c.carriesSine hp.1 hp.2.1 hp.2.2.1 hp.2.2.2
  refine ⟨Br * (3 + 2 * |(j : ℝ)| * |Bφ|) + Bp, by positivity, fun t x ht0 ht1 hx htn hxn => ?_⟩
  have hxa : |x| ≤ 1 := hx.le
  obtain ⟨hA, hrt, -⟩ := hbr t x ht0 ht1 hxa
  obtain ⟨-, -, hpx⟩ := hbp t x ht0 ht1 hxa
  obtain ⟨g, hg, hgb⟩ := hrt htn
  obtain ⟨h, hh, hhb⟩ := hpx hxn hx
  have hps := phaseSlope_abs_le P (fun s hs => (hBφ s hs).1) t
  have hu : 0 ≤ 1 - t := by linarith
  have hu2 : 0 ≤ (1 - t) ^ 2 := by positivity
  simp only [fluxAmps, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, mul_zero, add_zero]
  unfold shiftedScale radialScale heightDeriv
  rw [hg.deriv, hh.deriv]
  set A := scalarAmp (K.radialFlux c) c.carriesSine t x
  have h1 : ‖((t * (1 - t) : ℝ) : ℂ) * g‖ ≤ Br * (1 - t) ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hgb
  have h2 : ‖Complex.I * (((j : ℝ) * phaseSlope P t : ℝ) : ℂ) * A‖ ≤ (2 * |(j : ℝ)| * |Bφ|) * (Br * (1 - t) ^ 2) := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    have hj0 := abs_nonneg (j : ℝ)
    calc |(j : ℝ)| * |phaseSlope P t| * ‖A‖ ≤ |(j : ℝ)| * (2 * |Bφ|) * (Br * (1 - t) ^ 2) := by gcongr
      _ = _ := by ring
  have h3 : ‖(2 : ℂ) * A‖ ≤ 2 * (Br * (1 - t) ^ 2) := by
    rw [norm_mul, Complex.norm_two]
    gcongr
  calc ‖((t * (1 - t) : ℝ) : ℂ) * g + Complex.I * (((j : ℝ) * phaseSlope P t : ℝ) : ℂ) * A + 2 * A - h‖
      ≤ ‖((t * (1 - t) : ℝ) : ℂ) * g‖ + ‖Complex.I * (((j : ℝ) * phaseSlope P t : ℝ) : ℂ) * A‖ + ‖(2 : ℂ) * A‖ + ‖h‖ := by
        refine (norm_sub_le _ _).trans ?_
        gcongr
        refine (norm_add_le _ _).trans ?_
        gcongr
        exact norm_add_le _ _
    _ ≤ Br * (1 - t) ^ 2 + (2 * |(j : ℝ)| * |Bφ|) * (Br * (1 - t) ^ 2) + 2 * (Br * (1 - t) ^ 2) + Bp * (1 - t) ^ 2 := by
        gcongr
    _ = _ := by ring

end FluxDecay.Internal

end PotentialShape

end Breakdown

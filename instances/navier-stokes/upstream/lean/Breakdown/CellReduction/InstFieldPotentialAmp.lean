import Breakdown.CellReduction.InstFieldPotentialParts
import Breakdown.CellReduction.InstPressureRegular
import Breakdown.CellReduction.PotScalarOff

open scoped ContDiff NNReal Topology
open Set Metric Filter

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape
open CellCert.GivenFields (weightPoly heightRatio)

namespace Internal

namespace AmpField

def coordLift : Space →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i : Space →L[ℝ] ℝ)

theorem coordLift_norm_le (w : Space) : ‖coordLift w‖ ≤ ‖w‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg w)).2 fun i => ?_
  simp only [coordLift, ContinuousLinearMap.pi_apply, ContinuousLinearMap.coe_comp, Function.comp_apply,
    Complex.ofRealCLM_apply, Complex.norm_real]
  exact PiLp.norm_apply_le w i

theorem coordLift_opNorm : ‖coordLift‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by rw [one_mul]; exact coordLift_norm_le w

def ampScalar (P : ShapeParams) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ) (y : Space) : ℂ :=
  Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      weightPoly 1 e (chartCoord P y) * f (chartCoord P y, heightRatio y)

theorem field_eq (P : ShapeParams) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ) (V : Space →L[ℝ] Space) :
    radialAmpField P j e f V = fun y => ampScalar P j e f y • (coordLift.comp V) y := by
  funext y
  rfl

theorem comp_real_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {l : ℝ → F} {l' : F}
    {u : Space → ℝ} {U : Space →L[ℝ] ℝ} {y : Space} (hl : HasDerivAt l l' (u y)) (hu : HasFDerivAt u U y) :
    ∃ D : Space →L[ℝ] F, HasFDerivAt (fun z => l (u z)) D y ∧ ‖D‖ ≤ ‖l'‖ * ‖U‖ := by
  refine ⟨_, hl.hasFDerivAt.comp y hu, ?_⟩
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun s => ?_
  simp [norm_smul, mul_comm]

theorem mul_bound {a b : Space → ℂ} {A B : Space →L[ℝ] ℂ} {y : Space} (ha : HasFDerivAt a A y)
    (hb : HasFDerivAt b B y) :
    ∃ D : Space →L[ℝ] ℂ, HasFDerivAt (fun z => a z * b z) D y ∧ ‖D‖ ≤ ‖a y‖ * ‖B‖ + ‖b y‖ * ‖A‖ := by
  refine ⟨_, ha.mul hb, ?_⟩
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_smul_le _ _)
    (ContinuousLinearMap.opNorm_smul_le _ _))

theorem smul_bound {g : Space → ℂ} {G : Space →L[ℝ] ℂ} {y : Space} (hg : HasFDerivAt g G y)
    (W : Space →L[ℝ] (Fin 3 → ℂ)) :
    ∃ D : Space →L[ℝ] (Fin 3 → ℂ), HasFDerivAt (fun z => g z • W z) D y ∧
      ‖D‖ ≤ ‖g y‖ * ‖W‖ + ‖G‖ * ‖W y‖ := by
  refine ⟨_, hg.smul W.hasFDerivAt, ?_⟩
  refine (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_smul_le _ _) ?_)
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun w => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul]
  calc ‖G w‖ * ‖W y‖ ≤ ‖G‖ * ‖w‖ * ‖W y‖ := mul_le_mul_of_nonneg_right (G.le_opNorm w) (norm_nonneg _)
    _ = ‖G‖ * ‖W y‖ * ‖w‖ := by ring

theorem pair_bound {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ 1 f) {u v : Space → ℝ} {T X : Space →L[ℝ] ℝ} {y : Space}
    (hT : HasFDerivAt u T y) (hX : HasFDerivAt v X y) :
    ∃ D : Space →L[ℝ] ℂ, HasFDerivAt (fun z => f (u z, v z)) D y ∧
      ‖D‖ ≤ ‖fderiv ℝ f (u y, v y)‖ * (‖T‖ + ‖X‖) := by
  refine ⟨_, ((hf.differentiable (by norm_num)) _).hasFDerivAt.comp y (hT.prodMk hX), ?_⟩
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (norm_nonneg _))
  rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  exact max_le_add_of_nonneg (norm_nonneg _) (norm_nonneg _)

theorem norm_deriv_bound {y : Space} (hy : y ≠ 0) :
    ∃ N : Space →L[ℝ] ℝ, HasFDerivAt (fun z : Space => ‖z‖) N y ∧ ‖N‖ ≤ 1 := by
  have h := ((contDiffAt_norm ℝ hy : ContDiffAt ℝ 1 (fun z : Space => ‖z‖) y).differentiableAt
    (by norm_num)).hasFDerivAt
  refine ⟨_, h, h.le_of_lip' zero_le_one (Eventually.of_forall fun z => ?_)⟩
  rw [one_mul, Real.norm_eq_abs]
  exact abs_norm_sub_norm_le z y

theorem chart_deriv_bound (P : ShapeParams) (hL : 0 < P.chartLength) {y : Space} (hy : y ≠ 0) :
    ∃ T : Space →L[ℝ] ℝ, HasFDerivAt (chartCoord P) T y ∧
      ‖T‖ * ‖y‖ ≤ chartCoord P y * (1 - chartCoord P y) := by
  obtain ⟨N, hN, hN1⟩ := norm_deriv_bound hy
  set L := P.chartLength with hLdef
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hpos : 0 < ‖y‖ + L := by positivity
  have hl : HasDerivAt (fun s : ℝ => s / (s + L)) ((1 * (‖y‖ + L) - ‖y‖ * 1) / (‖y‖ + L) ^ 2) ‖y‖ :=
    (hasDerivAt_id' ‖y‖).div ((hasDerivAt_id' ‖y‖).add_const L) hpos.ne'
  obtain ⟨D, hD, hDn⟩ := comp_real_bound (u := fun z : Space => ‖z‖) hl hN
  refine ⟨D, hD, ?_⟩
  have e : (1 * (‖y‖ + L) - ‖y‖ * 1) / (‖y‖ + L) ^ 2 = L / (‖y‖ + L) ^ 2 := by ring
  rw [e, Real.norm_eq_abs, abs_of_pos (by positivity)] at hDn
  calc ‖D‖ * ‖y‖ ≤ (L / (‖y‖ + L) ^ 2 * 1) * ‖y‖ :=
        mul_le_mul_of_nonneg_right (hDn.trans (mul_le_mul_of_nonneg_left hN1 (by positivity))) hr.le
    _ = chartCoord P y * (1 - chartCoord P y) := by
        unfold chartCoord
        rw [← hLdef]
        field_simp
        ring

theorem height_deriv_bound {y : Space} (hy : y ≠ 0) :
    ∃ X : Space →L[ℝ] ℝ, HasFDerivAt heightRatio X y ∧ ‖X‖ * ‖y‖ ≤ 2 := by
  obtain ⟨N, hN, hN1⟩ := norm_deriv_bound hy
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hinv : HasFDerivAt (fun z : Space => ‖z‖⁻¹) ((-(‖y‖ ^ 2)⁻¹) • N) y :=
    (hasDerivAt_inv hr.ne').comp_hasFDerivAt y hN
  have hc : HasFDerivAt (fun z : Space => z 2) (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt
  have e : heightRatio = fun z : Space => z 2 * ‖z‖⁻¹ := by
    funext z
    simp [heightRatio, div_eq_mul_inv]
  have hp : ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
      rw [one_mul]
      simpa using PiLp.norm_apply_le w 2
  have k1 : ‖(-(‖y‖ ^ 2)⁻¹) • N‖ ≤ (‖y‖ ^ 2)⁻¹ := by
    rw [norm_smul, norm_neg, norm_inv, norm_pow, norm_norm]
    exact mul_le_of_le_one_right (by positivity) hN1
  have h2 : ‖y 2‖ ≤ ‖y‖ := PiLp.norm_apply_le y 2
  have hm := hc.mul hinv
  refine ⟨_, (by rw [e]; exact hm), ?_⟩
  calc _ ≤ (‖y 2‖ * ‖(-(‖y‖ ^ 2)⁻¹) • N‖ + ‖‖y‖⁻¹‖ * ‖(EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)‖) *
        ‖y‖ := by
        gcongr
        exact (norm_add_le _ _).trans (add_le_add (norm_smul_le _ _) (norm_smul_le _ _))
    _ ≤ (‖y‖ * (‖y‖ ^ 2)⁻¹ + ‖y‖⁻¹ * 1) * ‖y‖ := by
        rw [norm_inv, norm_norm]
        gcongr
    _ = 2 := by
        field_simp
        ring

theorem weight_deriv_bound (e : ℕ) (he : 1 ≤ e) (s : ℝ) :
    ∃ w' : ℝ, HasDerivAt (fun s : ℝ => weightPoly 1 e s) (w' : ℂ) s ∧
      (0 ≤ s → s ≤ 1 → |w'| ≤ (1 + e) * (1 - s) ^ (e - 1)) := by
  have h : HasDerivAt (fun s : ℝ => s * (1 - s) ^ e)
      (1 * (1 - s) ^ e + s * ((e : ℝ) * (1 - s) ^ (e - 1) * (-1))) s :=
    (hasDerivAt_id' s).mul (((hasDerivAt_id' s).const_sub 1).pow e)
  have ew : (fun s : ℝ => weightPoly 1 e s) = fun s : ℝ => ((s * (1 - s) ^ e : ℝ) : ℂ) := by
    funext s
    simp [weightPoly]
  refine ⟨_, ew ▸ h.ofReal_comp, fun h0 h1 => ?_⟩
  have hs : 0 ≤ 1 - s := by linarith
  have hp : (1 - s) ^ e = (1 - s) * (1 - s) ^ (e - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hq : 0 ≤ (1 - s) ^ (e - 1) := pow_nonneg hs _
  rw [hp]
  calc |1 * ((1 - s) * (1 - s) ^ (e - 1)) + s * ((e : ℝ) * (1 - s) ^ (e - 1) * (-1))|
      ≤ |1 * ((1 - s) * (1 - s) ^ (e - 1))| + |s * ((e : ℝ) * (1 - s) ^ (e - 1) * (-1))| := abs_add_le _ _
    _ = (1 - s) * (1 - s) ^ (e - 1) + s * ((e : ℝ) * (1 - s) ^ (e - 1)) := by
        rw [one_mul, abs_of_nonneg (mul_nonneg hs hq), abs_mul, abs_mul, abs_mul, abs_neg, abs_one, mul_one,
          abs_of_nonneg h0, abs_of_nonneg (Nat.cast_nonneg e), abs_of_nonneg hq]
    _ ≤ 1 * (1 - s) ^ (e - 1) + 1 * ((e : ℝ) * (1 - s) ^ (e - 1)) := by
        gcongr
        linarith
    _ = (1 + e) * (1 - s) ^ (e - 1) := by ring

theorem phase_deriv_bound (Φ : ℝ → ℝ) (hΦ : IsRadialPhase Φ) (j : ℤ) (y : Space) :
    ∃ D : Space →L[ℝ] ℂ,
      HasFDerivAt (fun z : Space => Complex.exp ((((j : ℝ) * Φ (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I)) D y ∧
      ‖D‖ ≤ |(j : ℝ)| * |deriv Φ (‖y‖ ^ 2)| * (2 * ‖y‖) := by
  obtain ⟨δ, hδ, hs⟩ := hΦ.smooth
  have hmem : ‖y‖ ^ 2 ∈ Ioi (-δ) := by
    simp only [mem_Ioi]
    nlinarith [sq_nonneg ‖y‖]
  have hd : HasDerivAt Φ (deriv Φ (‖y‖ ^ 2)) (‖y‖ ^ 2) :=
    ((hs.contDiffAt (isOpen_Ioi.mem_nhds hmem)).differentiableAt (by norm_num)).hasDerivAt
  have hl := (((hd.const_mul (j : ℝ)).ofReal_comp).mul_const Complex.I).cexp
  obtain ⟨D, hD, hDn⟩ := comp_real_bound (u := fun z : Space => ‖z‖ ^ 2) hl
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  refine ⟨D, hD, hDn.trans ?_⟩
  have k : ‖(2 • innerSL ℝ y : Space →L[ℝ] ℝ)‖ ≤ 2 * ‖y‖ := by
    refine norm_nsmul_le.trans ?_
    rw [innerSL_apply_norm]
    norm_num
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_mul, Complex.norm_I, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_left k (by positivity)


theorem box_mem (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    (chartCoord P y, heightRatio y) ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1 :=
  ⟨⟨chartCoord_nonneg P hL y, chartCoord_le_one P hL y⟩, abs_le.mp (abs_heightRatio_le_one y)⟩

theorem weight_norm (P : ShapeParams) (hL : 0 < P.chartLength) (e : ℕ) (y : Space) :
    ‖weightPoly 1 e (chartCoord P y)‖ = chartCoord P y * (1 - chartCoord P y) ^ e := by
  have h0 := chartCoord_nonneg P hL y
  have h1 : 0 ≤ 1 - chartCoord P y := by linarith [chartCoord_le_one P hL y]
  simp only [weightPoly, pow_one, Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (by positivity)

theorem amp_norm_le (P : ShapeParams) (hL : 0 < P.chartLength) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ) {B : ℝ}
    (hB : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖f z‖ ≤ B) (y : Space) :
    ‖ampScalar P j e f y‖ ≤ chartCoord P y * (1 - chartCoord P y) ^ e * B := by
  unfold ampScalar
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, weight_norm P hL]
  have h0 := chartCoord_nonneg P hL y
  have h1 : 0 ≤ 1 - chartCoord P y := by linarith [chartCoord_le_one P hL y]
  exact mul_le_mul_of_nonneg_left (hB _ (box_mem P hL y)) (by positivity)

theorem amp_deriv_off (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) (e : ℕ) (he : 1 ≤ e)
    (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (W : Space →L[ℝ] (Fin 3 → ℂ)) (hW : ‖W‖ ≤ 1)
    {B B' Bφ : ℝ} (hB0 : 0 ≤ B) (hB'0 : 0 ≤ B')
    (hB : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖f z‖ ≤ B)
    (hB' : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖fderiv ℝ f z‖ ≤ B')
    (hφ : ∀ s, 0 ≤ s → |s * deriv P.radialPhase s| ≤ Bφ) {y : Space} (hy : y ≠ 0) :
    ∃ D : Space →L[ℝ] (Fin 3 → ℂ), HasFDerivAt (fun z => ampScalar P j e f z • W z) D y ∧
      ‖D‖ ≤ (B + 3 * B' + (1 + e) * B + 2 * |(j : ℝ)| * Bφ * B) *
        (chartCoord P y * (1 - chartCoord P y) ^ e) := by
  have hL := hP.chartLength_pos
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  set t := chartCoord P y with htdef
  have ht0 : 0 ≤ t := chartCoord_nonneg P hL y
  have ht1 : t ≤ 1 := chartCoord_le_one P hL y
  have hs : 0 ≤ 1 - t := by linarith
  set a := t * (1 - t) ^ e with hadef
  have ha : 0 ≤ a := by positivity
  obtain ⟨T, hT, hTn⟩ := chart_deriv_bound P hL hy
  obtain ⟨X, hX, hXn⟩ := height_deriv_bound hy
  obtain ⟨w', hw, hw'⟩ := weight_deriv_bound e he t
  have hw'b := hw' ht0 ht1
  obtain ⟨Dp, hDp, hDpn⟩ := comp_real_bound (u := chartCoord P) hw hT
  obtain ⟨DF, hDF, hDFn⟩ := pair_bound hf hT hX
  obtain ⟨Dq, hDq, hDqn⟩ := mul_bound hDp hDF
  obtain ⟨DE, hDE, hDEn⟩ := phase_deriv_bound P.radialPhase hP.phase j y
  obtain ⟨Dg, hDg, hDgn⟩ := mul_bound hDE hDq
  obtain ⟨D, hD, hDn⟩ := smul_bound hDg W
  have eq : (fun z => ampScalar P j e f z • W z) = fun z =>
      (Complex.exp ((((j : ℝ) * P.radialPhase (‖z‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        (weightPoly 1 e (chartCoord P z) * f (chartCoord P z, heightRatio z))) • W z := by
    funext z
    rw [ampScalar, mul_assoc]
  refine ⟨D, eq ▸ hD, ?_⟩
  have hFy : ‖f (t, heightRatio y)‖ ≤ B := hB _ (box_mem P hL y)
  have hF'y : ‖fderiv ℝ f (t, heightRatio y)‖ ≤ B' := hB' _ (box_mem P hL y)
  have hpy : ‖weightPoly 1 e t‖ = a := weight_norm P hL e y
  have hEy : ‖Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)‖ = 1 :=
    Complex.norm_exp_ofReal_mul_I _
  have hWy : ‖W y‖ ≤ ‖y‖ := (W.le_opNorm y).trans (by nlinarith [norm_nonneg y])
  have htt : t * (1 - t) ≤ 1 := by nlinarith
  have hpow : (1 - t) ^ (e - 1) * (t * (1 - t)) = a := by
    rw [hadef]
    have : (1 - t) ^ e = (1 - t) * (1 - t) ^ (e - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [this]
    ring
  have k1 : ‖y‖ * ‖DF‖ ≤ 3 * B' := by
    calc ‖y‖ * ‖DF‖ ≤ ‖y‖ * (B' * (‖T‖ + ‖X‖)) :=
          mul_le_mul_of_nonneg_left (hDFn.trans (mul_le_mul_of_nonneg_right hF'y (by positivity))) hr.le
      _ = B' * (‖T‖ * ‖y‖ + ‖X‖ * ‖y‖) := by ring
      _ ≤ B' * (1 + 2) := mul_le_mul_of_nonneg_left (add_le_add (hTn.trans htt) hXn) hB'0
      _ = 3 * B' := by ring
  have k2 : ‖y‖ * ‖Dp‖ ≤ (1 + e) * a := by
    have hw0 : ‖(w' : ℂ)‖ = |w'| := by rw [Complex.norm_real, Real.norm_eq_abs]
    calc ‖y‖ * ‖Dp‖ ≤ ‖y‖ * (|w'| * ‖T‖) := mul_le_mul_of_nonneg_left (hw0 ▸ hDpn) hr.le
      _ = |w'| * (‖T‖ * ‖y‖) := by ring
      _ ≤ ((1 + e) * (1 - t) ^ (e - 1)) * (t * (1 - t)) :=
          mul_le_mul hw'b hTn (by positivity) (by positivity)
      _ = (1 + e) * a := by rw [← hpow]; ring
  have k3 : ‖y‖ * ‖Dq‖ ≤ (3 * B' + (1 + e) * B) * a := by
    calc ‖y‖ * ‖Dq‖ ≤ ‖y‖ * (a * ‖DF‖ + ‖f (t, heightRatio y)‖ * ‖Dp‖) :=
          mul_le_mul_of_nonneg_left (hpy ▸ hDqn) hr.le
      _ = a * (‖y‖ * ‖DF‖) + ‖f (t, heightRatio y)‖ * (‖y‖ * ‖Dp‖) := by ring
      _ ≤ a * (3 * B') + B * ((1 + e) * a) :=
          add_le_add (mul_le_mul_of_nonneg_left k1 ha) (mul_le_mul hFy k2 (by positivity) hB0)
      _ = (3 * B' + (1 + e) * B) * a := by ring
  have k4 : ‖y‖ * ‖DE‖ ≤ 2 * |(j : ℝ)| * Bφ := by
    have hb := hφ (‖y‖ ^ 2) (by positivity)
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖y‖ ^ 2)] at hb
    calc ‖y‖ * ‖DE‖ ≤ ‖y‖ * (|(j : ℝ)| * |deriv P.radialPhase (‖y‖ ^ 2)| * (2 * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hDEn hr.le
      _ = 2 * |(j : ℝ)| * (‖y‖ ^ 2 * |deriv P.radialPhase (‖y‖ ^ 2)|) := by ring
      _ ≤ 2 * |(j : ℝ)| * Bφ := mul_le_mul_of_nonneg_left hb (by positivity)
  have hqy : ‖weightPoly 1 e t * f (t, heightRatio y)‖ ≤ a * B := by
    rw [norm_mul, hpy]
    exact mul_le_mul_of_nonneg_left hFy ha
  have k5 : ‖y‖ * ‖Dg‖ ≤ (3 * B' + (1 + e) * B + 2 * |(j : ℝ)| * Bφ * B) * a := by
    calc ‖y‖ * ‖Dg‖ ≤ ‖y‖ * (1 * ‖Dq‖ + ‖weightPoly 1 e t * f (t, heightRatio y)‖ * ‖DE‖) :=
          mul_le_mul_of_nonneg_left (hEy ▸ hDgn) hr.le
      _ = ‖y‖ * ‖Dq‖ + ‖weightPoly 1 e t * f (t, heightRatio y)‖ * (‖y‖ * ‖DE‖) := by ring
      _ ≤ (3 * B' + (1 + e) * B) * a + (a * B) * (2 * |(j : ℝ)| * Bφ) :=
          add_le_add k3 (mul_le_mul hqy k4 (by positivity) (by positivity))
      _ = _ := by ring
  have hgy : ‖Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      (weightPoly 1 e t * f (t, heightRatio y))‖ ≤ a * B := by
    rw [norm_mul, hEy, one_mul]
    exact hqy
  calc ‖D‖ ≤ _ := hDn
    _ ≤ a * B * 1 + ‖Dg‖ * ‖y‖ :=
        add_le_add (mul_le_mul hgy hW (norm_nonneg _) (by positivity))
          (mul_le_mul_of_nonneg_left hWy (norm_nonneg _))
    _ = a * B + ‖y‖ * ‖Dg‖ := by ring
    _ ≤ a * B + (3 * B' + (1 + e) * B + 2 * |(j : ℝ)| * Bφ * B) * a := add_le_add le_rfl k5
    _ = _ := by ring


theorem field_smooth_off (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) (e : ℕ) (f : ℝ × ℝ → ℂ)
    (hf : ContDiff ℝ 1 f) (W : Space →L[ℝ] (Fin 3 → ℂ)) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (fun z => ampScalar P j e f z • W z) y := by
  have hL := hP.chartLength_pos
  have hE : ContDiff ℝ 1 (radFactor P.radialPhase j) := radFactor_contDiff _ hP.phase j
  have ht : ContDiffAt ℝ 1 (chartCoord P) y := (PotentialShape.Internal.AwayFromOrigin.chartCoord_contDiffAt P hL hy).of_le (by norm_num)
  have hx : ContDiffAt ℝ 1 heightRatio y := (PotentialShape.Internal.AwayFromOrigin.heightRatio_contDiffAt hy).of_le (by norm_num)
  have hw : ContDiff ℝ 1 (fun s : ℝ => weightPoly 1 e s) := by
    have h : ContDiff ℝ 1 (fun s : ℝ => s ^ 1 * (1 - s) ^ e) := by fun_prop
    exact Complex.ofRealCLM.contDiff.comp h
  exact ((hE.contDiffAt.mul (hw.contDiffAt.comp y ht)).mul
    (hf.contDiffAt.comp y (ht.prodMk hx))).smul W.contDiff.contDiffAt

theorem field_regular (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) (e : ℕ) (he : 3 ≤ e)
    (f : ℝ × ℝ → ℂ) (hf : ContDiff ℝ 1 f) (W : Space →L[ℝ] (Fin 3 → ℂ)) (hW : ‖W‖ ≤ 1) :
    ContDiff ℝ 1 (fun y => ampScalar P j e f y • W y) ∧ ∃ C : ℝ, ∀ y,
      ‖ampScalar P j e f y • W y‖ ≤ C / (1 + ‖y‖) ^ 2 ∧
      ‖fderiv ℝ (fun y => ampScalar P j e f y • W y) y‖ ≤ C / (1 + ‖y‖) ^ 3 := by
  have hL := hP.chartLength_pos
  set L := P.chartLength with hLdef
  set b := fun y => ampScalar P j e f y • W y with hbdef
  have hKc : IsCompact (Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  obtain ⟨B₀, hB₀⟩ := hKc.exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨B₁, hB₁⟩ := hKc.exists_bound_of_continuousOn (hf.continuous_fderiv (by norm_num)).continuousOn
  obtain ⟨Bφ, hφ⟩ := hP.phase.scaled_bounded
  set B := max B₀ 0 with hBdef
  set B' := max B₁ 0 with hB'def
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hB : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖f z‖ ≤ B := fun z hz => (hB₀ z hz).trans (le_max_left _ _)
  have hB' : ∀ z ∈ Icc (0 : ℝ) 1 ×ˢ Icc (-1 : ℝ) 1, ‖fderiv ℝ f z‖ ≤ B' :=
    fun z hz => (hB₁ z hz).trans (le_max_left _ _)
  have hφ' : ∀ s, 0 ≤ s → |s * deriv P.radialPhase s| ≤ Bφ := fun s hs => (hφ s hs).1
  have hBφ0 : 0 ≤ Bφ := by simpa using hφ' 0 le_rfl
  set K := B + 3 * B' + (1 + e) * B + 2 * |(j : ℝ)| * Bφ * B with hKdef
  have hK0 : 0 ≤ K := by positivity
  have hrng : ∀ y, 0 ≤ chartCoord P y ∧ chartCoord P y ≤ 1 :=
    fun y => ⟨chartCoord_nonneg P hL y, chartCoord_le_one P hL y⟩
  have ha0 : ∀ y, 0 ≤ chartCoord P y * (1 - chartCoord P y) ^ e := fun y => by
    have := hrng y
    have : 0 ≤ 1 - chartCoord P y := by linarith
    exact mul_nonneg (hrng y).1 (pow_nonneg this _)
  have hale : ∀ y, chartCoord P y * (1 - chartCoord P y) ^ e ≤ ‖y‖ / L := fun y => by
    have h := hrng y
    have hs : 0 ≤ 1 - chartCoord P y := by linarith
    calc chartCoord P y * (1 - chartCoord P y) ^ e ≤ chartCoord P y * 1 :=
          mul_le_mul_of_nonneg_left (pow_le_one₀ hs (by linarith)) h.1
      _ ≤ ‖y‖ / L := by rw [mul_one]; exact chartCoord_le_norm P hL y
  have hval : ∀ y, ‖b y‖ ≤ B * (chartCoord P y * (1 - chartCoord P y) ^ e) * ‖y‖ := fun y => by
    simp only [hbdef]
    rw [norm_smul]
    have hWy : ‖W y‖ ≤ ‖y‖ := (W.le_opNorm y).trans (by nlinarith [norm_nonneg y])
    calc ‖ampScalar P j e f y‖ * ‖W y‖ ≤ (chartCoord P y * (1 - chartCoord P y) ^ e * B) * ‖y‖ :=
          mul_le_mul (amp_norm_le P hL j e f hB y) hWy (norm_nonneg _) (mul_nonneg (ha0 y) hB0)
      _ = _ := by ring
  have hoff : ∀ y, y ≠ 0 → ∃ D : Space →L[ℝ] (Fin 3 → ℂ), HasFDerivAt b D y ∧
      ‖D‖ ≤ K * (chartCoord P y * (1 - chartCoord P y) ^ e) := fun y hy =>
    amp_deriv_off P hP j e (by omega) f hf W hW hB0 hB'0 hB hB' hφ' hy
  have hb0 : b 0 = 0 := by
    have h := hval 0
    rw [norm_zero, mul_zero] at h
    exact norm_le_zero_iff.mp h
  have h0 : HasFDerivAt b (0 : Space →L[ℝ] (Fin 3 → ℂ)) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have e1 : (fun h : Space => b (0 + h) - b 0 - (0 : Space →L[ℝ] (Fin 3 → ℂ)) h) = b := by
      funext h
      simp [hb0]
    rw [e1]
    refine Asymptotics.IsBigO.trans_isLittleO ?_ (Asymptotics.isLittleO_norm_pow_id (n := 2) (by norm_num))
    refine Asymptotics.IsBigO.of_bound (B / L) (Eventually.of_forall fun z => ?_)
    rw [norm_pow, norm_norm]
    calc ‖b z‖ ≤ B * (chartCoord P z * (1 - chartCoord P z) ^ e) * ‖z‖ := hval z
      _ ≤ B * (‖z‖ / L) * ‖z‖ := by gcongr; exact hale z
      _ = B / L * ‖z‖ ^ 2 := by ring
  have hfd : ∀ y, ‖fderiv ℝ b y‖ ≤ K * (chartCoord P y * (1 - chartCoord P y) ^ e) := fun y => by
    by_cases hy : y = 0
    · subst hy
      rw [h0.fderiv, norm_zero]
      exact mul_nonneg hK0 (ha0 0)
    · obtain ⟨D, hD, hDn⟩ := hoff y hy
      rw [hD.fderiv]
      exact hDn
  have hdiff : Differentiable ℝ b := fun y => by
    by_cases hy : y = 0
    · subst hy
      exact h0.differentiableAt
    · obtain ⟨D, hD, -⟩ := hoff y hy
      exact hD.differentiableAt
  refine ⟨?_, ?_⟩
  · rw [contDiff_one_iff_fderiv]
    refine ⟨hdiff, continuous_iff_continuousAt.2 fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy
      rw [ContinuousAt, h0.fderiv]
      refine squeeze_zero_norm (fun z => (hfd z).trans (mul_le_mul_of_nonneg_left (hale z) hK0)) ?_
      have hc : Continuous (fun z : Space => K * (‖z‖ / L)) := by fun_prop
      simpa using hc.tendsto 0
    · exact (field_smooth_off P hP j e f hf W hy).continuousAt_fderiv (by norm_num)
  · refine ⟨max (B * L * (L + 1) ^ 2) (K * (L + 1) ^ 3), fun y => ?_⟩
    have h := hrng y
    set t := chartCoord P y with htdef
    set r := ‖y‖ with hrdef
    have hr0 : 0 ≤ r := norm_nonneg y
    have hs0 : 0 ≤ 1 - t := by linarith
    have hgap : 1 - t = L / (r + L) := by
      rw [htdef, hrdef]
      unfold chartCoord
      rw [← hLdef]
      field_simp
      ring
    have hgap2 : 1 - t ≤ (L + 1) / (1 + r) := by
      rw [hgap, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    have hrs : r * (1 - t) ≤ L := by
      rw [hgap, ← mul_div_assoc, div_le_iff₀ (by positivity)]
      nlinarith
    have hcube : t * (1 - t) ^ e ≤ (1 - t) ^ 3 :=
      (mul_le_mul h.2 (pow_le_pow_of_le_one hs0 (by linarith) he) (pow_nonneg hs0 _) zero_le_one).trans
        (by rw [one_mul])
    have hq : 0 ≤ (L + 1) / (1 + r) := by positivity
    constructor
    · calc ‖b y‖ ≤ B * (t * (1 - t) ^ e) * r := hval y
        _ ≤ B * ((1 - t) ^ 3) * r := by gcongr
        _ = B * ((1 - t) ^ 2 * (r * (1 - t))) := by ring
        _ ≤ B * (((L + 1) / (1 + r)) ^ 2 * L) := by gcongr
        _ = B * L * (L + 1) ^ 2 / (1 + r) ^ 2 := by rw [div_pow]; ring
        _ ≤ _ := by gcongr; exact le_max_left _ _
    · calc ‖fderiv ℝ b y‖ ≤ K * (t * (1 - t) ^ e) := hfd y
        _ ≤ K * (1 - t) ^ 3 := by gcongr
        _ ≤ K * ((L + 1) / (1 + r)) ^ 3 := by gcongr
        _ = K * (L + 1) ^ 3 / (1 + r) ^ 3 := by rw [div_pow]; ring
        _ ≤ _ := by gcongr; exact le_max_right _ _

end AmpField

end Internal

theorem radialAmpField_regular : RadialAmpFieldRegular := by
  intro P j e f V hP he hf hV
  rw [Internal.AmpField.field_eq]
  refine Internal.AmpField.field_regular P hP j e he f hf (Internal.AmpField.coordLift.comp V) ?_
  calc ‖Internal.AmpField.coordLift.comp V‖ ≤ ‖Internal.AmpField.coordLift‖ * ‖V‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * 1 := mul_le_mul Internal.AmpField.coordLift_opNorm hV (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

end Instantiation

end CellReduction

end Breakdown

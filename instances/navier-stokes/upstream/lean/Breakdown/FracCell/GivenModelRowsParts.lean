import Breakdown.FracCell.GivenModelDefs
import Breakdown.FracCell.CylIntegral

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

namespace RowsInternal

open SteadyCert CellAnalysis Spectral.Internal.CylIntegral

private theorem coord_cont (i : Fin 3) : Continuous fun y : Space => y i :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous

private theorem cylRadius_cont : Continuous cylRadius := by
  unfold cylRadius
  exact (((coord_cont 0).pow 2).add ((coord_cont 1).pow 2)).sqrt

private theorem absHeight_cont : Continuous fun y => |cylHeight y| := by
  unfold cylHeight; exact (coord_cont 2).abs

theorem solid_measurableSet (K : CellBox) : MeasurableSet K.solid :=
  (measurableSet_le measurable_const cylRadius_cont.measurable).inter
    ((measurableSet_le cylRadius_cont.measurable measurable_const).inter
    ((measurableSet_le measurable_const absHeight_cont.measurable).inter
      (measurableSet_le absHeight_cont.measurable measurable_const)))

private theorem cylAngle_meas : Measurable cylAngle := by
  unfold cylAngle
  exact Complex.measurable_arg.comp (by fun_prop)

private theorem single_eq (i : Fin 3) (x : ℝ) :
    EuclideanSpace.single i x = x • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]

private theorem single_cont (i : Fin 3) : Continuous fun x : ℝ => EuclideanSpace.single i x := by
  have h : (fun x : ℝ => EuclideanSpace.single i x) = fun x => x • EuclideanSpace.single i (1 : ℝ) :=
    funext (single_eq i)
  rw [h]
  exact continuous_id.smul continuous_const

private theorem frameUnit_meas (a : Fin 3) : Measurable fun θ : ℝ => frameUnit θ a := by
  fin_cases a
  · show Measurable fun θ : ℝ => radialUnit θ
    unfold radialUnit
    exact (((single_cont 0).comp Real.continuous_cos).add ((single_cont 1).comp Real.continuous_sin)).measurable
  · show Measurable fun θ : ℝ => angularUnit θ
    unfold angularUnit
    exact (((single_cont 0).comp Real.continuous_sin.neg).add ((single_cont 1).comp Real.continuous_cos)).measurable
  · exact measurable_const

private theorem vectorSign_meas (c : Fin 3) : Measurable fun y => vectorSign y c := by
  unfold vectorSign
  refine Measurable.ite ?_ measurable_const measurable_const
  by_cases hc : c = 2
  · simp only [hc, and_true]
    exact measurableSet_lt (coord_cont 2).measurable measurable_const
  · simp only [hc, and_false, Set.ofPred_false, MeasurableSet.empty]

private theorem frameUnit_norm_le (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ ≤ 2 := by
  fin_cases a
  · show ‖radialUnit θ‖ ≤ 2
    unfold radialUnit
    refine (norm_add_le _ _).trans ?_
    rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · show ‖angularUnit θ‖ ≤ 2
    unfold angularUnit
    refine (norm_add_le _ _).trans ?_
    rw [PiLp.norm_single, PiLp.norm_single, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
    linarith [Real.abs_cos_le_one θ, Real.abs_sin_le_one θ]
  · show ‖axialUnit‖ ≤ 2
    unfold axialUnit
    rw [PiLp.norm_single]; norm_num

private theorem evalPoly_norm_le {d : ℕ} (P : CellPoly d) {r h R Z : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) (hh : 0 ≤ h)
    (hhZ : h ≤ Z) : ‖evalPoly P r h‖ ≤ ∑ j, ∑ l, ‖P j l‖ * R ^ (j : ℕ) * Z ^ (l : ℕ) := by
  unfold evalPoly
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_))
  rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg hr, abs_of_nonneg hh]
  have hR0 : 0 ≤ R := hr.trans hrR
  exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrR _) (norm_nonneg _))
    (pow_le_pow_left₀ hh hhZ _) (by positivity) (mul_nonneg (norm_nonneg _) (pow_nonneg hR0 _))

theorem testField_memLp {M : CellMesh} {N : ℕ} (R : RowData M N) (hM : IsCellMesh M) (m : ℕ) (a : Fin N) :
    MemLp (R.testField m a) 2 volume := by
  set K := M.box (R.cell a)
  have hK := hM.boxes (R.cell a)
  have hs := solid_measurableSet K
  unfold RowData.testField
  rw [memLp_indicator_iff_restrict hs]
  have hbdd : Bornology.IsBounded K.solid := by
    refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := K.r₂ + K.z₂)).subset fun y hy => ?_
    rw [Metric.mem_closedBall, dist_zero_right]
    obtain ⟨h1, h2, h3, h4⟩ := hy
    have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
    have hrr : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hz : |cylHeight y| ^ 2 = y 2 ^ 2 := by rw [sq_abs]; rfl
    have hz0 : 0 ≤ |cylHeight y| := abs_nonneg _
    have hsum : ∑ i : Fin 3, ‖y i‖ ^ 2 ≤ (K.r₂ + K.z₂) ^ 2 := by
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
      nlinarith
    rw [EuclideanSpace.norm_eq]
    calc Real.sqrt (∑ i : Fin 3, ‖y i‖ ^ 2) ≤ Real.sqrt ((K.r₂ + K.z₂) ^ 2) := Real.sqrt_le_sqrt hsum
      _ = K.r₂ + K.z₂ := Real.sqrt_sq (by linarith)
  have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.2 hbdd.measure_lt_top.ne
  set B : ℝ := ∑ c : Fin 3, 2 * ∑ j, ∑ l, ‖R.profile a c j l‖ * K.r₂ ^ (j : ℕ) * K.z₂ ^ (l : ℕ)
  refine MemLp.of_bound ?_ B ((ae_restrict_iff' hs).2 (Filter.Eventually.of_forall fun y hy => ?_))
  · refine Measurable.aestronglyMeasurable ?_
    unfold cartOfFrame
    refine Finset.measurable_sum _ fun c _ => ?_
    have h2 : Measurable fun z => frameUnit (cylAngle z) c := (frameUnit_meas c).comp cylAngle_meas
    have h1 : Measurable fun z : Space => vectorSign z c * (evalPoly (R.profile a c) (cylRadius z) |cylHeight z| *
        Complex.exp ((azimuth m (R.harmonic a : ℤ) * cylAngle z : ℝ) * Complex.I)).re := by
      refine (vectorSign_meas c).mul (Complex.measurable_re.comp (Measurable.mul ?_ ?_))
      · unfold evalPoly
        refine Finset.measurable_sum _ fun j _ => Finset.measurable_sum _ fun l _ => ?_
        refine (measurable_const.mul ((Complex.measurable_ofReal.comp cylRadius_cont.measurable).pow_const _)).mul
          ((Complex.measurable_ofReal.comp absHeight_cont.measurable).pow_const _)
      · exact Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp (measurable_const.mul cylAngle_meas)).mul_const _)
    exact h1.smul h2
  · obtain ⟨h1, h2, h3, h4⟩ := hy
    have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
    unfold cartOfFrame
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_smul]
    have hw : ‖vectorSign y c * (evalPoly (R.profile a c) (cylRadius y) |cylHeight y| *
        Complex.exp ((azimuth m (R.harmonic a : ℤ) * cylAngle y : ℝ) * Complex.I)).re‖ ≤
        ∑ j, ∑ l, ‖R.profile a c j l‖ * K.r₂ ^ (j : ℕ) * K.z₂ ^ (l : ℕ) := by
      have hv : |vectorSign y c| = 1 := by unfold vectorSign; split_ifs <;> simp
      rw [norm_mul, Real.norm_eq_abs, hv, one_mul, Real.norm_eq_abs]
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
      exact evalPoly_norm_le _ hr0 h2 (abs_nonneg _) h4
    calc _ ≤ (∑ j, ∑ l, ‖R.profile a c j l‖ * K.r₂ ^ (j : ℕ) * K.z₂ ^ (l : ℕ)) * 2 :=
          mul_le_mul hw (frameUnit_norm_le _ c) (norm_nonneg _) (le_trans (norm_nonneg _) hw)
      _ = _ := by ring

private theorem level_finite_null (t : ℝ) : volume {b : ℝ | b ^ 2 = t} = 0 := by
  refine measure_mono_null (t := {Real.sqrt t, -Real.sqrt t}) (fun b hb => ?_) ((Set.toFinite _).measure_zero _)
  have hb' : b ^ 2 = t := hb
  have habs : |b| = Real.sqrt t := by rw [← hb', Real.sqrt_sq_eq_abs]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  exact (abs_eq (Real.sqrt_nonneg t)).1 habs

private theorem radius_level_null (c : ℝ) : volume {y : Space | cylRadius y = c} = 0 := by
  rw [← toSpace_mp.measure_preimage_equiv]
  set S : Set (ℝ × ℝ) := {p | p.1 ^ 2 + p.2 ^ 2 = c ^ 2} with hSdef
  have hS : volume S = 0 := by
    have hSm : MeasurableSet S := measurableSet_eq_fun (by fun_prop) measurable_const
    rw [Measure.volume_eq_prod, Measure.measure_prod_null hSm]
    refine Filter.Eventually.of_forall fun a => ?_
    show volume (Prod.mk a ⁻¹' S) = 0
    refine measure_mono_null (fun b hb => ?_) (level_finite_null (c ^ 2 - a ^ 2))
    have hb' : a ^ 2 + b ^ 2 = c ^ 2 := hb
    show b ^ 2 = c ^ 2 - a ^ 2
    linarith
  refine measure_mono_null (t := S ×ˢ Set.univ) ?_ ?_
  · rintro ⟨⟨a, b⟩, z⟩ hw
    refine ⟨?_, Set.mem_univ _⟩
    have h : Real.sqrt (a ^ 2 + b ^ 2) = c := hw
    show a ^ 2 + b ^ 2 = c ^ 2
    rw [← h, Real.sq_sqrt (by positivity)]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, hS, zero_mul]

private theorem height_level_null (c : ℝ) : volume {y : Space | |cylHeight y| = c} = 0 := by
  rw [← toSpace_mp.measure_preimage_equiv]
  refine measure_mono_null (t := Set.univ ×ˢ {z : ℝ | z ^ 2 = c ^ 2}) ?_ ?_
  · rintro ⟨⟨a, b⟩, z⟩ hw
    refine ⟨Set.mem_univ _, ?_⟩
    have h : |z| = c := hw
    show z ^ 2 = c ^ 2
    rw [← h, sq_abs]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, level_finite_null, mul_zero]

theorem solid_inter_null {M : CellMesh} (hM : IsCellMesh M) {K K' : Fin M.cellCount} (h : K ≠ K') :
    volume ((M.box K).solid ∩ (M.box K').solid) = 0 := by
  rcases hM.interiors_disjoint K K' h with h1 | h1 | h1 | h1
  · exact measure_mono_null (fun y hy => le_antisymm hy.1.2.1 (h1.trans hy.2.1)) (radius_level_null (M.box K).r₂)
  · exact measure_mono_null (fun y hy => le_antisymm hy.2.2.1 (h1.trans hy.1.1)) (radius_level_null (M.box K').r₂)
  · exact measure_mono_null (fun y hy => le_antisymm hy.1.2.2.2 (h1.trans hy.2.2.2.1))
      (height_level_null (M.box K).z₂)
  · exact measure_mono_null (fun y hy => le_antisymm hy.2.2.2.2 (h1.trans hy.1.2.2.1))
      (height_level_null (M.box K').z₂)

private theorem turnStep_coords (m : ℕ) (y : Space) :
    turnStep m y 0 = Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 ∧
    turnStep m y 1 = Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 ∧
    turnStep m y 2 = y 2 := by
  simp [turnStep]

private theorem mirror_coords (y : Space) : mirror y 0 = y 0 ∧ mirror y 1 = y 1 ∧ mirror y 2 = -y 2 := by
  simp [mirror]

private theorem cylRadius_turn (m : ℕ) (y : Space) : cylRadius (turnStep m y) = cylRadius y := by
  unfold cylRadius
  obtain ⟨h0, h1, -⟩ := turnStep_coords m y
  rw [h0, h1]
  congr 1
  have := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * this

private theorem cylHeight_turn (m : ℕ) (y : Space) : cylHeight (turnStep m y) = cylHeight y :=
  (turnStep_coords m y).2.2

private theorem cylRadius_mirror (y : Space) : cylRadius (mirror y) = cylRadius y := by
  unfold cylRadius
  rw [(mirror_coords y).1, (mirror_coords y).2.1]

private theorem absHeight_mirror (y : Space) : |cylHeight (mirror y)| = |cylHeight y| := by
  unfold cylHeight
  rw [(mirror_coords y).2.2, abs_neg]

private theorem cylAngle_mirror (y : Space) : cylAngle (mirror y) = cylAngle y := by
  unfold cylAngle
  rw [(mirror_coords y).1, (mirror_coords y).2.1]

private theorem vectorSign_turn (m : ℕ) (y : Space) (c : Fin 3) : vectorSign (turnStep m y) c = vectorSign y c := by
  unfold vectorSign
  rw [cylHeight_turn]

private theorem solid_turn (K : CellBox) (m : ℕ) (y : Space) : turnStep m y ∈ K.solid ↔ y ∈ K.solid := by
  unfold CellBox.solid
  simp only [Set.mem_setOf_eq, cylRadius_turn, cylHeight_turn]

private theorem solid_mirror (K : CellBox) (y : Space) : mirror y ∈ K.solid ↔ y ∈ K.solid := by
  unfold CellBox.solid
  simp only [Set.mem_setOf_eq, cylRadius_mirror, absHeight_mirror]

private theorem frame_mirror (θ : ℝ) (w : Fin 3 → ℝ) :
    mirror (cartOfFrame θ w) = cartOfFrame θ (fun c => if c = 2 then -w c else w c) := by
  ext i
  fin_cases i <;>
    simp [mirror, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit]

private theorem frame_turn (m : ℕ) (θ : ℝ) (n : ℤ) (w : Fin 3 → ℝ) :
    cartOfFrame (θ + 2 * Real.pi / m + 2 * Real.pi * n) w = turnStep m (cartOfFrame θ w) := by
  have hc : Real.cos (θ + 2 * Real.pi / m + 2 * Real.pi * n) = Real.cos (θ + 2 * Real.pi / m) := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  have hs : Real.sin (θ + 2 * Real.pi / m + 2 * Real.pi * n) = Real.sin (θ + 2 * Real.pi / m) := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
  ext i
  fin_cases i <;>
    simp [turnStep, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, hc, hs,
      Real.cos_add, Real.sin_add] <;> ring

private theorem cylAngle_turn (m : ℕ) (y : Space) (hy : cylRadius y ≠ 0) :
    ∃ n : ℤ, cylAngle (turnStep m y) = cylAngle y + 2 * Real.pi / m + 2 * Real.pi * n := by
  obtain ⟨h0, h1, -⟩ := turnStep_coords m y
  set x : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I with hx
  set u : ℂ := Complex.exp (((2 * Real.pi / m : ℝ) : ℂ) * Complex.I) with hu
  have hx0 : x ≠ 0 := by
    intro h0
    apply hy
    have h0r := congrArg Complex.re h0
    have h0i := congrArg Complex.im h0
    simp [hx] at h0r h0i
    unfold cylRadius
    rw [h0r, h0i]
    simp
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hcu : u = ((Real.cos (2 * Real.pi / m) : ℝ) : ℂ) + ((Real.sin (2 * Real.pi / m) : ℝ) : ℂ) * Complex.I := by
    rw [hu, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hxu : (turnStep m y 0 : ℂ) + (turnStep m y 1 : ℂ) * Complex.I = x * u := by
    rw [hcu, h0, h1]
    apply Complex.ext <;> simp [hx] <;> ring
  have hang : (Complex.arg (x * u) : Real.Angle) = ((Complex.arg x + 2 * Real.pi / m : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hx0 hu0, Real.Angle.coe_add, hu, Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  refine ⟨k, ?_⟩
  unfold cylAngle
  rw [hxu]
  linarith

private theorem exp_turn (m : ℕ) (hm : 0 < m) (h : ℕ) (θ : ℝ) (n : ℤ) :
    Complex.exp ((azimuth m (h : ℤ) * (θ + 2 * Real.pi / m + 2 * Real.pi * n) : ℝ) * Complex.I) =
      Complex.exp ((azimuth m (h : ℤ) * θ : ℝ) * Complex.I) := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hr : azimuth m (h : ℤ) * (θ + 2 * Real.pi / m + 2 * Real.pi * n) =
      azimuth m (h : ℤ) * θ + (((h : ℤ) + (h : ℤ) * m * n : ℤ) : ℝ) * (2 * Real.pi) := by
    unfold azimuth
    push_cast
    field_simp
    ring
  have hk : ((((h : ℤ) + (h : ℤ) * m * n : ℤ) : ℝ) * (2 * Real.pi) : ℝ) * Complex.I =
      (((h : ℤ) + (h : ℤ) * m * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [hr, Complex.ofReal_add, add_mul, Complex.exp_add, hk, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem testField_class {M : CellMesh} {N : ℕ} (R : RowData M N) {m : ℕ} (hm : 0 < m) (a : Fin N) :
    IsClassField m (R.testField m a) := by
  have hax : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | cylRadius y = 0} :=
    (measure_eq_zero_iff_ae_notMem).1 (radius_level_null 0)
  have hpl : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | |cylHeight y| = 0} :=
    (measure_eq_zero_iff_ae_notMem).1 (height_level_null 0)
  refine ⟨?_, ?_⟩
  · filter_upwards [hax] with y hy
    obtain ⟨n, hn⟩ := cylAngle_turn m y hy
    unfold RowData.testField
    by_cases hs : y ∈ (M.box (R.cell a)).solid
    · rw [Set.indicator_of_mem ((solid_turn _ m y).2 hs), Set.indicator_of_mem hs, hn,
        ← frame_turn m (cylAngle y) n]
      congr 1
      funext c
      rw [vectorSign_turn, cylRadius_turn, cylHeight_turn, exp_turn m hm]
    · rw [Set.indicator_of_notMem (mt (solid_turn _ m y).1 hs), Set.indicator_of_notMem hs]
      ext i
      fin_cases i <;> simp [turnStep]
  · filter_upwards [hpl] with y hy
    have hy' : cylHeight y ≠ 0 := fun h => hy (by simp [h])
    unfold RowData.testField
    by_cases hs : y ∈ (M.box (R.cell a)).solid
    · rw [Set.indicator_of_mem ((solid_mirror _ y).2 hs), Set.indicator_of_mem hs, frame_mirror, cylAngle_mirror]
      congr 1
      funext c
      rw [cylRadius_mirror, absHeight_mirror]
      have h2 : cylHeight (mirror y) = -cylHeight y := (mirror_coords y).2.2
      unfold vectorSign
      rw [h2]
      rcases lt_or_gt_of_ne hy' with h | h <;> by_cases hc : c = 2 <;>
        simp only [hc, and_true, and_false, if_true, if_false] <;> split_ifs <;>
        first | (exfalso; linarith) | ring
    · rw [Set.indicator_of_notMem (mt (solid_mirror _ y).1 hs), Set.indicator_of_notMem hs]
      ext i
      fin_cases i <;> simp [mirror]

private theorem exists_normalizer {ι : Type*} [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ C : Matrix ι ι ℝ, C * G * C.transpose = 1 := by
  set U : Matrix ι ι ℝ := (hG.1.eigenvectorUnitary : Matrix ι ι ℝ) with hUdef
  have hD : star U * G * U = Matrix.diagonal (fun i => hG.1.eigenvalues i) := by
    have h := hG.1.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_apply] at h
    simpa [hUdef] using h
  refine ⟨Matrix.diagonal (fun i => (Real.sqrt (hG.1.eigenvalues i))⁻¹) * star U, ?_⟩
  have hst : (star U).transpose = U := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose]
  rw [Matrix.transpose_mul, hst, Matrix.diagonal_transpose]
  calc Matrix.diagonal (fun i => (Real.sqrt (hG.1.eigenvalues i))⁻¹) * star U * G *
        (U * Matrix.diagonal (fun i => (Real.sqrt (hG.1.eigenvalues i))⁻¹)) =
      Matrix.diagonal (fun i => (Real.sqrt (hG.1.eigenvalues i))⁻¹) * (star U * G * U) *
        Matrix.diagonal (fun i => (Real.sqrt (hG.1.eigenvalues i))⁻¹) := by
        simp only [Matrix.mul_assoc]
    _ = 1 := by
      rw [hD, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      have hl := hG.eigenvalues_pos i
      have hs : 0 < Real.sqrt (hG.1.eigenvalues i) := Real.sqrt_pos.2 hl
      have hss := Real.mul_self_sqrt hl.le
      field_simp
      linarith

theorem exists_block_normalizer {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (k : ι → κ) (G : Matrix ι ι ℝ) (hG : G.PosDef) (hblk : ∀ a b, k a ≠ k b → G a b = 0) :
    ∃ C : Matrix ι ι ℝ, C * G * C.transpose = 1 ∧ ∀ a b, C a b ≠ 0 → k a = k b := by
  set e := Equiv.sigmaFiberEquiv k
  set Gb : ∀ v : κ, Matrix {a // k a = v} {a // k a = v} ℝ := fun v => G.submatrix Subtype.val Subtype.val
  have hGb : ∀ v, (Gb v).PosDef := fun v => hG.submatrix Subtype.val_injective
  choose Cb hCb using fun v => exists_normalizer (Gb v) (hGb v)
  have hG' : G.submatrix e e = Matrix.blockDiagonal' Gb := by
    ext ⟨v, a⟩ ⟨w, b⟩
    rw [Matrix.blockDiagonal'_apply']
    split_ifs with h
    · subst h
      rfl
    · simp only [Matrix.submatrix_apply]
      apply hblk
      change k a.1 ≠ k b.1
      rw [a.2, b.2]
      exact h
  refine ⟨(Matrix.blockDiagonal' Cb).submatrix e.symm e.symm, ?_, ?_⟩
  · have hGe : G = (G.submatrix e e).submatrix e.symm e.symm := by
      simp [Matrix.submatrix_submatrix]
    rw [hGe, hG', Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      Matrix.blockDiagonal'_transpose, ← Matrix.blockDiagonal'_mul, ← Matrix.blockDiagonal'_mul]
    simp only [hCb]
    rw [show (Matrix.blockDiagonal' fun v => (1 : Matrix {a // k a = v} {a // k a = v} ℝ)) = 1 from
      Matrix.blockDiagonal'_one]
    exact Matrix.submatrix_one_equiv e.symm
  · intro a b hab
    by_contra h
    apply hab
    exact Matrix.blockDiagonal'_apply_ne Cb _ _ h

theorem mix_spec {M : CellMesh} {N : ℕ} (R : RowData M N) (hG : R.testPairing.PosDef) :
    R.mix * R.testPairing * R.mix.transpose = 1 ∧
      ∀ a b, R.mix a b ≠ 0 → R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b := by
  classical
  have hH := hG.1
  have hmix : R.mix = cfc (fun x : ℝ => Real.sqrt x⁻¹) R.testPairing := by
    unfold RowData.mix
    rw [dif_pos hH, Matrix.IsHermitian.cfc_eq hH]
  have hsa : IsSelfAdjoint R.mix := by
    rw [hmix]; exact cfc_predicate _ _
  have htr : R.mix.transpose = R.mix := by
    have h := hsa.star_eq
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h
  refine ⟨?_, ?_⟩
  · rw [htr, hmix]
    have hsG : IsSelfAdjoint R.testPairing := hH
    have hspec : ∀ x ∈ spectrum ℝ R.testPairing, 0 < x := by
      intro x hx
      obtain ⟨i, rfl⟩ := hH.spectrum_real_eq_range_eigenvalues ▸ hx
      exact hG.eigenvalues_pos i
    have hfin : (spectrum ℝ R.testPairing).Finite := Matrix.finite_real_spectrum
    have h1 : cfc (fun x : ℝ => Real.sqrt x⁻¹) R.testPairing * R.testPairing =
        cfc (fun x : ℝ => Real.sqrt x⁻¹ * x) R.testPairing := by
      conv_lhs => arg 2; rw [← cfc_id' ℝ R.testPairing]
      exact (cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)).symm
    rw [h1, ← cfc_mul _ _ _ (hfin.continuousOn _) (hfin.continuousOn _)]
    rw [cfc_congr (g := fun _ => (1 : ℝ))]
    · exact cfc_const_one ℝ R.testPairing
    · intro x hx
      have h0 := hspec x hx
      have hs : 0 < Real.sqrt x⁻¹ := Real.sqrt_pos.2 (inv_pos.2 h0)
      have hss := Real.mul_self_sqrt (inv_pos.2 h0).le
      show Real.sqrt x⁻¹ * x * Real.sqrt x⁻¹ = 1
      rw [show Real.sqrt x⁻¹ * x * Real.sqrt x⁻¹ = (Real.sqrt x⁻¹ * Real.sqrt x⁻¹) * x by ring, hss]
      exact inv_mul_cancel₀ h0.ne'
  · intro a b hab
    by_contra hne
    apply hab
    let P : Matrix (Fin N) (Fin N) ℝ :=
      Matrix.diagonal (fun i => if R.cell i = R.cell a ∧ R.harmonic i = R.harmonic a then 1 else 0)
    have hGP : Commute R.testPairing P := by
      ext i j
      simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul]
      by_cases hij : R.cell i = R.cell j ∧ R.harmonic i = R.harmonic j
      · rw [hij.1, hij.2]; ring
      · have : R.testPairing i j = 0 := by
          unfold RowData.testPairing; rw [if_neg hij]
        rw [this]; ring
    have hc : Commute R.mix P := by
      rw [hmix]; exact hGP.cfc_real _
    have h := congrFun (congrFun hc.eq a) b
    simp only [P, Matrix.mul_diagonal, Matrix.diagonal_mul, and_self, if_true] at h
    have hb : ¬ (R.cell b = R.cell a ∧ R.harmonic b = R.harmonic a) := fun h' => hne ⟨h'.1.symm, h'.2.symm⟩
    rw [if_neg hb] at h
    linarith

private noncomputable def freqExp (n : ℤ) (θ : ℝ) : ℂ := Complex.exp (((n : ℝ) * θ : ℝ) * Complex.I)

private theorem freqExp_mul (n n' : ℤ) (θ : ℝ) : freqExp n θ * freqExp n' θ = freqExp (n + n') θ := by
  unfold freqExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem freqExp_conj (n : ℤ) (θ : ℝ) : (starRingEnd ℂ) (freqExp n θ) = freqExp (-n) θ := by
  unfold freqExp
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem freqExp_cont (n : ℤ) : Continuous (freqExp n) := by
  unfold freqExp
  fun_prop

private theorem freqExp_integral (n : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, freqExp n θ = if n = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp [freqExp]
    ring
  · have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hn) Complex.I_ne_zero
    have hf : freqExp n = fun θ : ℝ => Complex.exp ((n : ℂ) * Complex.I * θ) := by
      funext θ
      unfold freqExp
      push_cast
      ring_nf
    rw [hf, integral_exp_mul_complex hc]
    have h2 : Complex.exp ((n : ℂ) * Complex.I * (Real.pi : ℝ)) = Complex.exp ((n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ)) := by
      rw [show (n : ℂ) * Complex.I * (Real.pi : ℝ) = (n : ℂ) * Complex.I * ((-Real.pi : ℝ) : ℂ) + n * (2 * Real.pi * Complex.I) by
        push_cast; ring, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [h2, sub_self, zero_div]

private theorem re_mode (A : ℂ) (n : ℤ) (θ : ℝ) :
    (((A * freqExp n θ).re : ℝ) : ℂ) = (A * freqExp n θ + (starRingEnd ℂ) A * freqExp (-n) θ) / 2 := by
  rw [Complex.re_eq_add_conj, map_mul, freqExp_conj]

private theorem mode_angular_int (A B : ℂ) (n₁ n₂ : ℤ) (hp1 : 0 ≤ n₁) (hp2 : 0 ≤ n₂) :
    ∫ θ in (-Real.pi)..Real.pi, (A * freqExp n₁ θ).re * (B * freqExp n₂ θ).re =
    if n₁ = n₂ then (if n₁ = 0 then 2 * Real.pi * (A.re * B.re) else Real.pi * (A * (starRingEnd ℂ) B).re)
    else 0 := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have hpt : (fun θ : ℝ => (((A * freqExp n₁ θ).re * (B * freqExp n₂ θ).re : ℝ) : ℂ)) = fun θ =>
      (A * B / 4) * freqExp (n₁ + n₂) θ + (A * (starRingEnd ℂ) B / 4) * freqExp (n₁ + -n₂) θ +
        ((starRingEnd ℂ) A * B / 4) * freqExp (-n₁ + n₂) θ +
        ((starRingEnd ℂ) A * (starRingEnd ℂ) B / 4) * freqExp (-n₁ + -n₂) θ := by
    funext θ
    rw [Complex.ofReal_mul, re_mode, re_mode, ← freqExp_mul, ← freqExp_mul, ← freqExp_mul, ← freqExp_mul]
    ring
  have hi : ∀ (c : ℂ) (n : ℤ), IntervalIntegrable (fun θ => c * freqExp n θ) volume (-Real.pi) Real.pi :=
    fun c n => (continuous_const.mul (freqExp_cont n)).intervalIntegrable _ _
  rw [hpt, intervalIntegral.integral_add (((hi _ _).add (hi _ _)).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add ((hi _ _).add (hi _ _)) (hi _ _),
    intervalIntegral.integral_add (hi _ _) (hi _ _)]
  simp only [intervalIntegral.integral_const_mul, freqExp_integral]
  by_cases h12 : n₁ = n₂
  · subst h12
    by_cases h0 : n₁ = 0
    · subst h0
      simp only [add_zero, neg_zero, if_true]
      apply Complex.ext <;> simp <;> ring
    · rw [if_neg (by omega : n₁ + n₁ ≠ 0), if_pos (by omega : n₁ + -n₁ = 0), if_pos (by omega : -n₁ + n₁ = 0),
        if_neg (by omega : -n₁ + -n₁ ≠ 0), if_pos rfl, if_neg h0]
      apply Complex.ext <;> simp <;> ring
  · rw [if_neg (by omega : n₁ + n₂ ≠ 0), if_neg (by omega : n₁ + -n₂ ≠ 0), if_neg (by omega : -n₁ + n₂ ≠ 0),
      if_neg (by omega : -n₁ + -n₂ ≠ 0), if_neg h12]
    simp

theorem mode_angular (A B : ℂ) (m : ℕ) (hm : 0 < m) (h₁ h₂ : ℕ) :
    ∫ θ in (-Real.pi)..Real.pi, (A * Complex.exp ((azimuth m (h₁ : ℤ) * θ : ℝ) * Complex.I)).re *
      (B * Complex.exp ((azimuth m (h₂ : ℤ) * θ : ℝ) * Complex.I)).re =
    if h₁ = h₂ then (if h₁ = 0 then 2 * Real.pi * (A.re * B.re) else Real.pi * (A * (starRingEnd ℂ) B).re)
    else 0 := by
  have he : ∀ (h : ℕ) (θ : ℝ), Complex.exp ((azimuth m (h : ℤ) * θ : ℝ) * Complex.I) =
      freqExp ((h : ℤ) * m) θ := by
    intro h θ
    unfold freqExp azimuth
    push_cast
    ring_nf
  simp only [he]
  rw [mode_angular_int A B _ _ (by positivity) (by positivity)]
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have hiff : ((h₁ : ℤ) * m = (h₂ : ℤ) * m) ↔ h₁ = h₂ := by
    constructor
    · intro h; exact_mod_cast mul_right_cancel₀ hm' h
    · intro h; rw [h]
  have hz : ((h₁ : ℤ) * m = 0) ↔ h₁ = 0 := by
    constructor
    · intro h
      rcases mul_eq_zero.1 h with h | h
      · exact_mod_cast h
      · exact absurd h hm'
    · intro h; rw [h]; simp
  simp only [hiff, hz]

private theorem cylPoint_coords (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ ∧ cylPoint r θ z 1 = r * Real.sin θ ∧
    cylPoint r θ z 2 = z := by
  simp [cylPoint]

private theorem cylAngle_cylPoint {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (z : ℝ) :
    cylAngle (cylPoint r θ z) = θ := by
  unfold cylAngle
  obtain ⟨h0, h1, -⟩ := cylPoint_coords r θ z
  rw [h0, h1]
  have : ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    push_cast; ring
  rw [this, Complex.arg_real_mul _ hr, Complex.arg_cos_add_sin_mul_I hθ]

private theorem cylRadius_cylPoint {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  unfold cylRadius
  obtain ⟨h0, h1, -⟩ := cylPoint_coords r θ z
  rw [h0, h1, show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    linear_combination r ^ 2 * Real.cos_sq_add_sin_sq θ, Real.sqrt_sq hr]

private theorem frame_inner (θ : ℝ) (w w' : Fin 3 → ℝ) :
    inner ℝ (cartOfFrame θ w) (cartOfFrame θ w') = ∑ c, w c * w' c := by
  have h := Real.sin_sq_add_cos_sq θ
  simp [cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, PiLp.inner_apply]
  linear_combination (w 0 * w' 0 + w 1 * w' 1) * h

theorem testField_inner_cyl {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (a b : Fin N)
    (hc : R.cell a = R.cell b) {r : ℝ} (hr : 0 < r) {θ : ℝ} (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (z : ℝ) :
    inner ℝ (R.testField m a (cylPoint r θ z)) (R.testField m b (cylPoint r θ z)) =
      (M.box (R.cell a)).rect.indicator (fun p => ∑ c,
        (evalPoly (R.profile a c) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re *
          (evalPoly (R.profile b c) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re)
        (r, |z|) := by
  have hmem : cylPoint r θ z ∈ (M.box (R.cell a)).solid ↔ (r, |z|) ∈ (M.box (R.cell a)).rect := by
    unfold CellBox.solid CellBox.rect
    have hh : cylHeight (cylPoint r θ z) = z := (cylPoint_coords r θ z).2.2
    simp only [Set.mem_setOf_eq, cylRadius_cylPoint hr.le, hh, Set.mem_prod, Set.mem_Icc]
    tauto
  unfold RowData.testField
  rw [← hc]
  by_cases h : (r, |z|) ∈ (M.box (R.cell a)).rect
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem (hmem.2 h), frame_inner,
      cylAngle_cylPoint hr hθ, cylRadius_cylPoint hr.le, show cylHeight (cylPoint r θ z) = z from (cylPoint_coords r θ z).2.2]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hv : vectorSign (cylPoint r θ z) c * vectorSign (cylPoint r θ z) c = 1 := by
      unfold vectorSign; split_ifs <;> norm_num
    linear_combination (evalPoly (R.profile a c) r |z| * Complex.exp ((azimuth m (R.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re *
          (evalPoly (R.profile b c) r |z| * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re * hv
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hmem.1 h), inner_zero_left]

private theorem line_null_fst (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.1 = c} = 0 := by
  have : {p : ℝ × ℝ | p.1 = c} = {c} ×ˢ Set.univ := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

private theorem line_null_snd (c : ℝ) : (volume : Measure (ℝ × ℝ)) {p | p.2 = c} = 0 := by
  have : {p : ℝ × ℝ | p.2 = c} = Set.univ ×ˢ {c} := by ext p; simp
  rw [this, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem doubling (K : CellBox) (hK : IsCellBox K) (g : ℝ × ℝ → ℝ) (hg : Continuous g) :
    ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), K.rect.indicator g (q.1, |q.2|) =
      2 * ∫ p in K.rect, g p := by
  have hrc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  set φ : ℝ × ℝ → ℝ := K.rect.indicator g with hφ
  have hφi : Integrable φ := (integrable_indicator_iff hrm).2 (hg.continuousOn.integrableOn_compact hrc)
  obtain ⟨C, hC⟩ := hrc.exists_bound_of_continuousOn hg.continuousOn
  set B : Set (ℝ × ℝ) := Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc (-K.z₂) K.z₂
  have hBm : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hBf : volume B < ⊤ := (isCompact_Icc.prod isCompact_Icc).measure_lt_top
  have hFi : Integrable (fun q : ℝ × ℝ => φ (q.1, |q.2|)) := by
    have hmeas : Measurable (fun q : ℝ × ℝ => φ (q.1, |q.2|)) :=
      (hg.measurable.indicator hrm).comp (measurable_fst.prodMk measurable_snd.abs)
    refine Integrable.mono' ((integrable_indicator_iff hBm).2 (integrableOn_const (C := C) hBf.ne)) hmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => ?_)
    by_cases h : (q.1, |q.2|) ∈ K.rect
    · have hq : q ∈ B := ⟨h.1, abs_le.1 h.2.2⟩
      rw [hφ, Set.indicator_of_mem h, Set.indicator_of_mem hq]
      exact hC _ h
    · rw [hφ, Set.indicator_of_notMem h, norm_zero]
      have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (K.r₁, K.z₁)
        ⟨⟨le_rfl, hK.r_order.2.le⟩, ⟨le_rfl, hK.z_order.2.le⟩⟩)
      exact Set.indicator_nonneg (fun _ _ => hC0) _
  have hnull : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∉ Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) → φ p = 0 := by
    have h1 := (measure_eq_zero_iff_ae_notMem).1 (line_null_fst 0)
    have h2 := (measure_eq_zero_iff_ae_notMem).1 (line_null_snd 0)
    filter_upwards [h1, h2] with p hp1 hp2 hp
    rw [hφ]
    refine Set.indicator_of_notMem (fun hr => hp ⟨?_, ?_⟩) _
    · exact lt_of_le_of_ne (hK.r_order.1.trans hr.1.1) (fun h => hp1 h.symm)
    · exact lt_of_le_of_ne (hK.z_order.1.trans hr.2.1) (fun h => hp2 h.symm)
  rw [Measure.volume_eq_prod, setIntegral_prod _ (hFi.integrableOn.mono_measure (by rw [Measure.volume_eq_prod]))]
  simp only [Measure.restrict_univ]
  have hB : ∀ r : ℝ, ∫ z, φ (r, |z|) = 2 * ∫ z in Set.Ioi (0 : ℝ), φ (r, z) := fun r =>
    integral_comp_abs (f := fun t => φ (r, t))
  simp only [hB]
  rw [integral_const_mul, ← setIntegral_prod _ (hφi.integrableOn.mono_measure (by rw [Measure.volume_eq_prod])),
    ← Measure.volume_eq_prod, setIntegral_eq_integral_of_ae_compl_eq_zero hnull, hφ, integral_indicator hrm]

private theorem inner_int {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    Integrable (fun y => inner ℝ (F y) (E y)) := by
  have h := hF.norm.integrable_mul hE.norm
  refine h.mono (hF.aestronglyMeasurable.inner hE.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul, abs_norm]
  exact abs_real_inner_le_norm _ _

theorem pairing_same_cell {M : CellMesh} {N : ℕ} (R : RowData M N) (hM : IsCellMesh M) {m : ℕ} (hm : 0 < m)
    (a b : Fin N) (hc : R.cell a = R.cell b) :
    l2Pair (R.testField m a) (R.testField m b) = R.testPairing a b := by
  have hK : IsCellBox (M.box (R.cell a)) := hM.boxes _
  obtain ⟨E, hE⟩ : ∃ E : ℝ × ℝ → ℝ, E = fun p => if R.harmonic a = R.harmonic b then
      2 * Real.pi * RowData.modePairDensity (R.harmonic a = 0) (fun c => evalPoly (R.profile a c) p.1 p.2)
        (fun c => evalPoly (R.profile b c) p.1 p.2) else 0 := ⟨_, rfl⟩
  have hang : ∀ r z : ℝ, ∫ θ in (-Real.pi)..Real.pi, ∑ c,
      (evalPoly (R.profile a c) r z * Complex.exp ((azimuth m (R.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re *
        (evalPoly (R.profile b c) r z * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re =
      E (r, z) := by
    intro r z
    rw [intervalIntegral.integral_finset_sum (fun c _ => by
      apply Continuous.intervalIntegrable
      fun_prop)]
    simp only [mode_angular _ _ m hm]
    rw [hE]
    by_cases h12 : R.harmonic a = R.harmonic b
    · by_cases h0 : R.harmonic a = 0
      · simp only [if_pos h12, if_pos h0, RowData.modePairDensity]
        rw [Finset.mul_sum]
      · simp only [if_pos h12, if_neg h0, RowData.modePairDensity]
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    · simp only [if_neg h12, Finset.sum_const_zero]
  have hf := inner_int (testField_memLp R hM m a) (testField_memLp R hM m b)
  unfold l2Pair
  rw [Spectral.cylIntegral _ hf]
  have hcp : ∀ r θ z : ℝ, Spectral.cylPoint r θ z = cylPoint r θ z := fun _ _ _ => rfl
  simp only [hcp]
  have hq : ∀ q ∈ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ),
      q.1 * ∫ θ in (-Real.pi)..Real.pi, inner ℝ (R.testField m a (cylPoint q.1 θ q.2))
        (R.testField m b (cylPoint q.1 θ q.2)) =
      (M.box (R.cell a)).rect.indicator (fun p => p.1 * E p) (q.1, |q.2|) := by
    intro q hq
    have hr : 0 < q.1 := hq.1
    have hcongr : ∫ θ in (-Real.pi)..Real.pi, inner ℝ (R.testField m a (cylPoint q.1 θ q.2))
        (R.testField m b (cylPoint q.1 θ q.2)) =
        ∫ θ in (-Real.pi)..Real.pi, (M.box (R.cell a)).rect.indicator (fun p => ∑ c,
          (evalPoly (R.profile a c) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re *
            (evalPoly (R.profile b c) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re)
          (q.1, |q.2|) := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
      rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
      exact testField_inner_cyl R m a b hc hr hθ q.2
    rw [hcongr]
    by_cases hin : (q.1, |q.2|) ∈ (M.box (R.cell a)).rect
    · rw [Set.indicator_of_mem hin]
      simp only [Set.indicator_of_mem hin]
      rw [hang q.1 |q.2|]
    · simp only [Set.indicator_of_notMem hin, intervalIntegral.integral_zero, mul_zero]
  have hEc : Continuous fun p : ℝ × ℝ => p.1 * E p := by
    refine continuous_fst.mul ?_
    rw [hE]
    split_ifs
    · unfold RowData.modePairDensity evalPoly
      split_ifs <;> fun_prop
    · exact continuous_const
  refine (setIntegral_congr_fun ((measurableSet_Ioi (a := (0 : ℝ))).prod (MeasurableSet.univ (α := ℝ)))
    (fun q hq' => hq q hq')).trans ?_
  rw [doubling _ hK _ hEc]
  unfold RowData.testPairing
  by_cases h12 : R.harmonic a = R.harmonic b
  · rw [if_pos ⟨hc, h12⟩, mul_assoc]
    refine congrArg (2 * ·) ?_
    rw [← integral_const_mul]
    refine setIntegral_congr_fun
      (show MeasurableSet (M.box (R.cell a)).rect from measurableSet_Icc.prod measurableSet_Icc) fun p _ => ?_
    rw [hE]
    simp only [if_pos h12]
    ring
  · rw [if_neg (fun h => h12 h.2), hE]
    simp [h12]


theorem testField_pairing {M : CellMesh} {N : ℕ} (R : RowData M N) (hM : IsCellMesh M) {m : ℕ} (hm : 0 < m)
    (a b : Fin N) :
    l2Pair (R.testField m a) (R.testField m b) = R.testPairing a b := by
  by_cases hc : R.cell a = R.cell b
  · exact pairing_same_cell R hM hm a b hc
  · unfold RowData.testPairing
    rw [if_neg (fun h => hc h.1)]
    unfold l2Pair
    refine integral_eq_zero_of_ae ?_
    have hae := (measure_eq_zero_iff_ae_notMem).1 (solid_inter_null hM hc)
    filter_upwards [hae] with y hy
    unfold RowData.testField
    by_cases h1 : y ∈ (M.box (R.cell a)).solid
    · by_cases h2 : y ∈ (M.box (R.cell b)).solid
      · exact absurd ⟨h1, h2⟩ hy
      · rw [Set.indicator_of_notMem h2, inner_zero_right]; rfl
    · rw [Set.indicator_of_notMem h1, inner_zero_left]; rfl

end RowsInternal

end GivenModel

end CellCert

end Breakdown

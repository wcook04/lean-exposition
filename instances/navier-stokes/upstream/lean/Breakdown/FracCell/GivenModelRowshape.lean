import Breakdown.FracCell.GivenModelDefs
import Breakdown.FracCell.GivenModelMixClauses

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

private theorem rs_mix_support {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (rowMax : ℝ)
    (hR : IsRowData R m rowMax) (a b : Fin N) (h : R.mix a b ≠ 0) :
    R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b :=
  (mix_clauses R m rowMax hR).2.1 a b h

private theorem rs_mirror_coord (u : Space) (i : Fin 3) : mirror u i = (if i = 2 then -1 else 1) * u i := by
  fin_cases i <;> simp [mirror]

private theorem rs_mirror_sum {ι : Type*} (s : Finset ι) (f : ι → Space) :
    mirror (∑ j ∈ s, f j) = ∑ j ∈ s, mirror (f j) := by
  ext i
  simp [rs_mirror_coord, Finset.mul_sum]

private theorem rs_mirror_smul (t : ℝ) (u : Space) : mirror (t • u) = t • mirror u := by
  ext i
  simp [rs_mirror_coord]

private theorem rs_mirror_zero : mirror (0 : Space) = 0 := by
  ext i
  simp [rs_mirror_coord]

private theorem rs_cart_sign (θ : ℝ) (w : Fin 3 → ℝ) :
    cartOfFrame θ (fun c => (if c = 2 then -1 else 1) * w c) = mirror (cartOfFrame θ w) := by
  ext i
  fin_cases i <;> simp [cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, mirror]

private theorem rs_radius_mirror (y : Space) : cylRadius (mirror y) = cylRadius y := by
  simp [cylRadius, mirror]

private theorem rs_height_mirror (y : Space) : cylHeight (mirror y) = -cylHeight y := by
  simp [cylHeight, mirror]

private theorem rs_angle_mirror (y : Space) : cylAngle (mirror y) = cylAngle y := by
  simp [cylAngle, mirror]

private theorem rs_testField_mirror {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N) (y : Space)
    (hy : cylHeight y < 0) : R.testField m b y = mirror (R.testField m b (mirror y)) := by
  have hz : |cylHeight (mirror y)| = |cylHeight y| := by rw [rs_height_mirror, abs_neg]
  have hmem : mirror y ∈ (M.box (R.cell b)).solid ↔ y ∈ (M.box (R.cell b)).solid := by
    simp only [CellBox.solid, Set.mem_setOf_eq, rs_radius_mirror, hz]
  unfold RowData.testField
  by_cases h : y ∈ (M.box (R.cell b)).solid
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hmem.2 h)]
    simp only [rs_radius_mirror, hz, rs_angle_mirror]
    rw [← rs_cart_sign]
    congr 1
    funext c
    have h2 : ¬ cylHeight (mirror y) < 0 := by rw [rs_height_mirror]; linarith
    by_cases hc : c = 2 <;> simp [vectorSign, hy, h2, hc]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (mt hmem.1 h), rs_mirror_zero]

theorem rowsInCell_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) :
    ∀ a ∈ R.rowSet, ∀ y ∉ (M.box K₀).solid, c.row a y = 0 := by
  intro a ha y hy
  rw [hI.row_eq]
  unfold RowData.rowField
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hab : RD.mix a b = 0
  · simp [hab]
  · have h1 := (rs_mix_support RD c.order c.rowMax hR a b hab).1
    have hK : RD.cell a = K₀ := (hI.rowSet_eq a).1 ha
    have hy' : y ∉ (M.box (RD.cell b)).solid := by rw [← h1, hK]; exact hy
    simp [RowData.testField, Set.indicator_of_notMem hy']

theorem solidInRegion_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hI : IsRowsInstance c M RD K₀ R) :
    (M.box K₀).solid ⊆ c.cellRegion := by
  intro y hy
  rw [hI.region_eq]
  exact Set.mem_iUnion.2 ⟨K₀, hy⟩

theorem rowMirror_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) :
    ∀ a ∈ R.rowSet, ∀ y ∈ (M.box K₀).solid, cylHeight y < 0 → c.row a y = mirror (c.row a (mirror y)) := by
  intro a _ y _ hy
  rw [hI.row_eq]
  unfold RowData.rowField
  rw [rs_mirror_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [rs_mirror_smul, ← rs_testField_mirror RD c.order b y hy]

private theorem rs_frameVec_apply (θ : ℝ) (u : Space) (i : Fin 3) : frameVec θ u i = inner ℝ u (frameUnit θ i) := by
  fin_cases i <;> rfl

private theorem rs_frameVec_cart (θ : ℝ) (w : Fin 3 → ℝ) (i : Fin 3) : frameVec θ (cartOfFrame θ w) i = w i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      PiLp.inner_apply] <;>
    first | linear_combination (w 0) * hs | linear_combination (w 1) * hs | ring

private theorem rs_frameVec_sum {N : ℕ} (θ : ℝ) (μ : Fin N → ℝ) (u : Fin N → Space) (i : Fin 3) :
    frameVec θ (∑ b, μ b • u b) i = ∑ b, μ b * frameVec θ (u b) i := by
  simp only [rs_frameVec_apply, sum_inner, real_inner_smul_left]

private theorem rs_cyl0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]

private theorem rs_cyl1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]

private theorem rs_cyl2 (r θ z : ℝ) : cylPoint r θ z 2 = z := by simp [cylPoint]

private theorem rs_cyl_radius {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  unfold cylRadius
  rw [rs_cyl0, rs_cyl1]
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [h, Real.sqrt_sq hr]

private theorem rs_cyl_angle {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    ∃ j : ℤ, cylAngle (cylPoint r θ z) = θ - j * (2 * Real.pi) := by
  have h : ((cylPoint r θ z 0 : ℝ) : ℂ) + ((cylPoint r θ z 1 : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    rw [rs_cyl0, rs_cyl1]
    push_cast
    ring
  unfold cylAngle
  rw [h, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]
  exact ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, by rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]⟩

private theorem rs_eval_axis {d : ℕ} (P : CellPoly d) (hP : ∀ l, P 0 l = 0) (z : ℝ) : evalPoly P 0 z = 0 := by
  unfold evalPoly
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hj : (j : ℕ) = 0
  · have : j = 0 := Fin.ext hj
    subst this
    simp [hP]
  · simp [zero_pow hj]

private theorem rs_exp_period (x : ℝ) (n : ℤ) :
    Complex.exp (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  rw [show (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = (x : ℂ) * Complex.I - n * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

private theorem rs_term_frame {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N)
    (hK : IsCellBox (M.box (R.cell b))) (p : ℝ × ℝ) (hp : p ∈ (M.box (R.cell b)).rect)
    (hax : p.1 = 0 → R.harmonic b = 0 ∧ ∀ l, R.profile b 0 0 l = 0 ∧ R.profile b 1 0 l = 0)
    (θ : ℝ) (i : Fin 3) :
    frameVec θ (R.testField m b (cylPoint p.1 θ p.2)) i =
      (evalPoly (R.profile b i) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 hr1
  have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 hz1
  have hR : cylRadius (cylPoint p.1 θ p.2) = p.1 := rs_cyl_radius hr0 θ p.2
  have hH : cylHeight (cylPoint p.1 θ p.2) = p.2 := rs_cyl2 _ _ _
  have hmem : cylPoint p.1 θ p.2 ∈ (M.box (R.cell b)).solid := by
    show _ ∧ _
    rw [hR, hH, abs_of_nonneg hz0]
    exact ⟨hr1, hr2, hz1, hz2⟩
  unfold RowData.testField
  rw [Set.indicator_of_mem hmem]
  have hvs : ∀ c, vectorSign (cylPoint p.1 θ p.2) c = 1 := by
    intro c
    simp [vectorSign, hH, not_lt.2 hz0]
  simp only [hR, hH, abs_of_nonneg hz0, hvs, one_mul]
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · obtain ⟨hβ, hP⟩ := hax h0.symm
    have hang : cylAngle (cylPoint p.1 θ p.2) = 0 := by
      simp [cylAngle, rs_cyl0, rs_cyl1, ← h0]
    have hE0 : evalPoly (R.profile b 0) p.1 p.2 = 0 := by
      rw [← h0]; exact rs_eval_axis _ (fun l => (hP l).1) _
    have hE1 : evalPoly (R.profile b 1) p.1 p.2 = 0 := by
      rw [← h0]; exact rs_eval_axis _ (fun l => (hP l).2) _
    rw [hang, hβ]
    fin_cases i <;>
      simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
        PiLp.inner_apply, hE0, hE1, azimuth]
  · obtain ⟨j, hj⟩ := rs_cyl_angle hpos θ p.2
    rw [hj]
    have hf : frameUnit (θ - j * (2 * Real.pi)) = frameUnit θ := by
      simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
    have hc : ∀ w, cartOfFrame (θ - j * (2 * Real.pi)) w = cartOfFrame θ w := fun w => by
      unfold cartOfFrame; rw [hf]
    rw [hc]
    rw [show azimuth m (R.harmonic b : ℤ) * (θ - j * (2 * Real.pi)) =
        azimuth m (R.harmonic b : ℤ) * θ - ((R.harmonic b * m * j : ℤ) : ℝ) * (2 * Real.pi) by
      unfold azimuth; push_cast; ring, rs_exp_period]
    exact rs_frameVec_cart θ _ i

private theorem rs_row_frame {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ) (hp : p ∈ (M.box K₀).rect)
    (θ : ℝ) (i : Fin 3) :
    frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      ((∑ b, (RD.mix a b : ℂ) * evalPoly (RD.profile b i) p.1 p.2) *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re := by
  have hK0 : RD.cell a = K₀ := (hI.rowSet_eq a).1 ha
  rw [hI.row_eq]
  unfold RowData.rowField
  rw [rs_frameVec_sum, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : RD.mix a b = 0
  · simp [hab]
  · obtain ⟨hc, hh⟩ := rs_mix_support RD c.order c.rowMax hR a b hab
    have hcb : RD.cell b = K₀ := hc ▸ hK0
    have hpb : p ∈ (M.box (RD.cell b)).rect := hcb ▸ hp
    have hax : p.1 = 0 → RD.harmonic b = 0 ∧ ∀ l, RD.profile b 0 0 l = 0 ∧ RD.profile b 1 0 l = 0 := by
      intro h0
      have hr1 : (M.box (RD.cell b)).r₁ = 0 :=
        le_antisymm (h0 ▸ hpb.1.1) (hM.boxes (RD.cell b)).r_order.1
      exact ⟨hR.axis_zeroMode b hr1, hR.axis_regular b hr1⟩
    rw [rs_term_frame RD c.order b (hM.boxes _) p hpb hax θ i, hh, mul_assoc, Complex.re_ofReal_mul]

private theorem rs_int_exp (j : ℤ) (hj : j ≠ 0) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp ((j : ℂ) * Complex.I * (x : ℂ)) = 0 := by
  have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [show (j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = j * (2 * Real.pi * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I j
  rw [h1]
  simp

private theorem rs_mode_term (m : ℕ) (hm : 0 < m) (n : ℤ) (β : ℕ) (hn1 : n ≠ β) (hn2 : n ≠ -β) (E : ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (((E * Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) = 0 := by
  have key : ∀ θ : ℝ, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (((E * Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
      (E / 2) * Complex.exp ((((β - n) * m : ℤ) : ℂ) * Complex.I * θ) +
      ((starRingEnd ℂ) E / 2) * Complex.exp (((-(β + n) * m : ℤ) : ℂ) * Complex.I * θ) := by
    intro θ
    have h2 : (starRingEnd ℂ) (Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)) =
        Complex.exp (-(azimuth m (β : ℤ) * θ : ℝ) * Complex.I) := by
      rw [← Complex.exp_conj]
      simp
    rw [Complex.re_eq_add_conj, map_mul, h2]
    have hx : -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + ((azimuth m (β : ℤ) * θ : ℝ) : ℂ) * Complex.I =
        (((β - n) * m : ℤ) : ℂ) * Complex.I * θ := by
      unfold azimuth; push_cast; ring
    have hy : -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + -((azimuth m (β : ℤ) * θ : ℝ) : ℂ) * Complex.I =
        ((-(β + n) * m : ℤ) : ℂ) * Complex.I * θ := by
      unfold azimuth; push_cast; ring
    rw [← hx, ← hy, Complex.exp_add, Complex.exp_add]
    ring
  simp only [key]
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  have h1 : ((β : ℤ) - n) * m ≠ 0 := mul_ne_zero (sub_ne_zero.2 (Ne.symm hn1)) hm'
  have h2 : (-((β : ℤ) + n)) * m ≠ 0 := by
    refine mul_ne_zero (neg_ne_zero.2 ?_) hm'
    intro h
    exact hn2 (by linarith)
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    rs_int_exp _ h1, rs_int_exp _ h2]
  · simp
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

theorem rowModeOf_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order) :
    ∀ a ∈ R.rowSet, ∀ n, n ≠ R.rowModeOf a → n ≠ -R.rowModeOf a → ∀ p ∈ (M.box K₀).rect,
      CellScalars.rowMode c a n p = 0 := by
  intro a ha n hn1 hn2 p hp
  rw [hI.rowModeOf_eq a ha] at hn1 hn2
  funext i
  have key : ∀ θ, frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      ((∑ b, (RD.mix a b : ℂ) * evalPoly (RD.profile b i) p.1 p.2) *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re :=
    fun θ => rs_row_frame c M RD K₀ R hM hR hI a ha p hp θ i
  simp only [CellScalars.rowMode, modeVec, key, rs_mode_term c.order hm n (RD.harmonic a) hn1 hn2, mul_zero,
    Pi.zero_apply]

theorem rowModes_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order) :
    ∀ a ∈ R.rowSet, ∀ n ∉ R.rowModes, ∀ p ∈ (M.box K₀).rect, CellScalars.rowMode c a n p = 0 := by
  intro a ha n hn p hp
  obtain ⟨h1, h2⟩ := hI.rowModes_cover a ha
  refine rowModeOf_of c M RD K₀ R hM hR hI hm a ha n ?_ ?_ p hp
  · rw [hI.rowModeOf_eq a ha]; rintro rfl; exact hn h1
  · rw [hI.rowModeOf_eq a ha]; rintro rfl; exact hn h2

private theorem rs_poly_eval {d : ℕ} (P : CellPoly d) : (fun p : ℝ × ℝ => evalPoly P p.1 p.2) ∈ polyFn d d :=
  ⟨P, fun _ => rfl⟩

private theorem rs_poly_conj {d : ℕ} (P : CellPoly d) :
    (fun p : ℝ × ℝ => (starRingEnd ℂ) (evalPoly P p.1 p.2)) ∈ polyFn d d :=
  ⟨fun j l => (starRingEnd ℂ) (P j l), fun p => by simp [evalPoly, map_sum, map_mul, map_pow]⟩

private theorem rs_poly_zero (d d' : ℕ) : (fun _ : ℝ × ℝ => (0 : ℂ)) ∈ polyFn d d' :=
  ⟨fun _ _ => 0, fun p => by simp⟩

private theorem rs_poly_add {d d' : ℕ} {F G : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d') (hG : G ∈ polyFn d d') :
    (fun p => F p + G p) ∈ polyFn d d' := by
  obtain ⟨a, ha⟩ := hF
  obtain ⟨b, hb⟩ := hG
  refine ⟨fun j l => a j l + b j l, fun p => ?_⟩
  dsimp only
  rw [ha, hb, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem rs_poly_smul {d d' : ℕ} {F : ℝ × ℝ → ℂ} (s : ℂ) (hF : F ∈ polyFn d d') :
    (fun p => s * F p) ∈ polyFn d d' := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun j l => s * a j l, fun p => ?_⟩
  dsimp only
  rw [ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem rs_poly_sum {d d' N : ℕ} {F : Fin N → ℝ × ℝ → ℂ} (hF : ∀ b, F b ∈ polyFn d d') :
    (fun p => ∑ b, F b p) ∈ polyFn d d' := by
  classical
  have : ∀ s : Finset (Fin N), (fun p => ∑ b ∈ s, F b p) ∈ polyFn d d' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using rs_poly_zero d d'
    | insert b s hb ih => simpa [Finset.sum_insert hb] using rs_poly_add (hF b) ih
  exact this Finset.univ

private theorem rs_poly_fst {d d' : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d') :
    (fun p => (p.1 : ℂ) * F p) ∈ polyFn (d + 1) d' := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨Fin.cases (motive := fun _ => Fin (d' + 1) → ℂ) (fun _ => 0) a, fun p => ?_⟩
  dsimp only
  rw [ha, Finset.mul_sum, Fin.sum_univ_succ (n := d + 1)]
  simp only [Fin.cases_zero, Fin.cases_succ, zero_mul, Finset.sum_const_zero, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem rs_poly_snd {d d' : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d') :
    (fun p => (p.2 : ℂ) * F p) ∈ polyFn d (d' + 1) := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun j => Fin.cases (motive := fun _ => ℂ) 0 (a j), fun p => ?_⟩
  dsimp only
  rw [ha, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum, Fin.sum_univ_succ (n := d' + 1)]
  simp only [Fin.cases_zero, Fin.cases_succ, zero_mul, zero_add, Fin.val_succ]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem rs_poly_mono {d d' e e' : ℕ} (h1 : d ≤ e) (h2 : d' ≤ e') {F : ℝ × ℝ → ℂ}
    (hF : F ∈ polyFn d d') : F ∈ polyFn e e' := by
  obtain ⟨a, ha⟩ := hF
  refine ⟨fun j l => if h : (j : ℕ) < d + 1 ∧ (l : ℕ) < d' + 1 then a ⟨j, h.1⟩ ⟨l, h.2⟩ else 0, fun p => ?_⟩
  rw [ha]
  refine Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _) _ _ ?_ ?_
  · intro j hj
    refine Finset.sum_eq_zero fun l _ => ?_
    have : ¬ ((j : ℕ) < d + 1) := fun h => hj ⟨⟨j, h⟩, Fin.ext rfl⟩
    simp [this]
  · intro j
    refine Fintype.sum_of_injective (Fin.castLE (by omega)) (Fin.castLE_injective _) _ _ ?_ ?_
    · intro l hl
      have : ¬ ((l : ℕ) < d' + 1) := fun h => hl ⟨⟨l, h⟩, Fin.ext rfl⟩
      simp [this]
    · intro l
      simp only [Fin.coe_castLE]
      rw [dif_pos ⟨j.isLt, l.isLt⟩]

private theorem rs_rhat_poly (K : CellBox) {d : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d) :
    ∃ P ∈ polyFn (d + 1) (d + 1), ∀ p : ℝ × ℝ, p.1 ≠ 0 → ((CellScalars.rHat K p : ℝ) : ℂ) * F p = P p := by
  by_cases hK : K.r₁ = 0
  · refine ⟨F, rs_poly_mono (e := d + 1) (e' := d + 1) (by omega) (by omega) hF, fun p hp => ?_⟩
    simp [CellScalars.rHat, CellBox.lineWeight, hK, div_self hp]
  · refine ⟨fun p => (p.1 : ℂ) * F p, rs_poly_mono (e := d + 1) (e' := d + 1) le_rfl (by omega) (rs_poly_fst hF), fun p _ => ?_⟩
    simp [CellScalars.rHat, CellBox.lineWeight, hK]

private theorem rs_frameY_poly {d : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d) (b : Fin 3) :
    (fun p => frameY p b * F p) ∈ polyFn (d + 1) (d + 1) := by
  fin_cases b
  · exact rs_poly_mono (d := d + 1) (d' := d) (e := d + 1) (e' := d + 1) le_rfl (by omega) (by simpa [frameY] using rs_poly_fst hF)
  · simpa [frameY] using rs_poly_zero (d + 1) (d + 1)
  · exact rs_poly_mono (d := d) (d' := d + 1) (e := d + 1) (e' := d + 1) (by omega) le_rfl (by simpa [frameY] using rs_poly_snd hF)

private theorem rs_frameTurnY_poly {d : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d) (b : Fin 3) :
    (fun p => frameTurnY p b * F p) ∈ polyFn (d + 1) (d + 1) := by
  fin_cases b
  · simpa [frameTurnY] using rs_poly_zero (d + 1) (d + 1)
  · exact rs_poly_mono (d := d + 1) (d' := d) (e := d + 1) (e' := d + 1) le_rfl (by omega) (by simpa [frameTurnY] using rs_poly_fst hF)
  · simpa [frameTurnY] using rs_poly_zero (d + 1) (d + 1)

private def rowProfileSum {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ b, (RD.mix a b : ℂ) * evalPoly (RD.profile b i) p.1 p.2

private def rowModeValue {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (n : ℤ) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (if n = (RD.harmonic a : ℤ) then rowProfileSum RD a i p / 2 else 0) +
    (if n = -(RD.harmonic a : ℤ) then (starRingEnd ℂ) (rowProfileSum RD a i p) / 2 else 0)

private theorem rs_value_poly {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (n : ℤ) (i : Fin 3) :
    (fun p => rowModeValue RD a n i p) ∈ polyFn RD.degree RD.degree := by
  have hQ : (fun p => rowProfileSum RD a i p) ∈ polyFn RD.degree RD.degree :=
    rs_poly_sum (fun b => rs_poly_smul _ (rs_poly_eval _))
  have hQc : (fun p => (starRingEnd ℂ) (rowProfileSum RD a i p)) ∈ polyFn RD.degree RD.degree := by
    have e : (fun p => (starRingEnd ℂ) (rowProfileSum RD a i p)) =
        fun p => ∑ b, (RD.mix a b : ℂ) * (starRingEnd ℂ) (evalPoly (RD.profile b i) p.1 p.2) := by
      funext p
      simp [rowProfileSum, map_sum]
    rw [e]
    exact rs_poly_sum fun b => rs_poly_smul _ (rs_poly_conj _)
  unfold rowModeValue
  refine rs_poly_add ?_ ?_
  · by_cases h : n = (RD.harmonic a : ℤ)
    · simp only [h, if_true]
      have := rs_poly_smul (1 / 2 : ℂ) hQ
      convert this using 1
      funext p
      ring
    · simp only [h, if_false]
      exact rs_poly_zero _ _
  · by_cases h : n = -(RD.harmonic a : ℤ)
    · simp only [h, if_true]
      have := rs_poly_smul (1 / 2 : ℂ) hQc
      convert this using 1
      funext p
      ring
    · simp only [h, if_false]
      exact rs_poly_zero _ _

private theorem rs_int_exp' (j : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp ((j : ℂ) * Complex.I * (x : ℂ)) =
      if j = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hj
  · subst hj
    simp
  · exact rs_int_exp j hj

private theorem rs_mode_key (m : ℕ) (n : ℤ) (β : ℕ) (E : ℂ) (θ : ℝ) :
    Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (((E * Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
      (E / 2) * Complex.exp ((((β - n) * m : ℤ) : ℂ) * Complex.I * θ) +
      ((starRingEnd ℂ) E / 2) * Complex.exp (((-(β + n) * m : ℤ) : ℂ) * Complex.I * θ) := by
  have h2 : (starRingEnd ℂ) (Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)) =
      Complex.exp (-(azimuth m (β : ℤ) * θ : ℝ) * Complex.I) := by
    rw [← Complex.exp_conj]
    simp
  rw [Complex.re_eq_add_conj, map_mul, h2]
  have hx : -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + ((azimuth m (β : ℤ) * θ : ℝ) : ℂ) * Complex.I =
      (((β - n) * m : ℤ) : ℂ) * Complex.I * θ := by
    unfold azimuth; push_cast; ring
  have hy : -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + -((azimuth m (β : ℤ) * θ : ℝ) : ℂ) * Complex.I =
      ((-(β + n) * m : ℤ) : ℂ) * Complex.I * θ := by
    unfold azimuth; push_cast; ring
  rw [← hx, ← hy, Complex.exp_add, Complex.exp_add]
  ring

private theorem rs_mode_val (m : ℕ) (hm : 0 < m) (n : ℤ) (β : ℕ) (E : ℂ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (((E * Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
      (if n = (β : ℤ) then E / 2 else 0) + (if n = -(β : ℤ) then (starRingEnd ℂ) E / 2 else 0) := by
  simp only [rs_mode_key]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    rs_int_exp', rs_int_exp']
  · have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    have c1 : ((β : ℤ) - n) * m = 0 ↔ n = β := by
      rw [mul_eq_zero, or_iff_left hm', sub_eq_zero, eq_comm]
    have c2 : (-((β : ℤ) + n)) * m = 0 ↔ n = -β := by
      rw [mul_eq_zero, or_iff_left hm', neg_eq_zero]
      constructor <;> intro h <;> linarith
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [c1, c2]
    split_ifs <;> field_simp <;> ring
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem rs_mode_formula {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order) (a : Fin N) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3)
    (p : ℝ × ℝ) (hp : p ∈ (M.box K₀).rect) :
    rowModeVec c a n p i = rowModeValue RD a n i p := by
  have key : ∀ θ, frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      ((∑ b, (RD.mix a b : ℂ) * evalPoly (RD.profile b i) p.1 p.2) *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re :=
    fun θ => rs_row_frame c M RD K₀ R hM hR hI a ha p hp θ i
  simp only [rowModeVec, modeVec, key]
  rw [rs_mode_val c.order hm n (RD.harmonic a)]
  rfl

theorem rowLow_of_gradient {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (S : CellScalars) (hM : IsCellMesh M)
    (hR : IsRowData RD c.order c.rowMax) (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order)
    (hdeg : RD.degree + 2 ≤ S.degHigh)
    (hG : ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p) :
    (∀ a ∈ R.rowSet, ∀ n i, ∃ P ∈ polyFn (S.degHigh - 1) (S.degHigh - 1),
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeVec c a n p i = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * (frameY p b * rowModeVec c a n p i) = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * (frameTurnY p b * rowModeVec c a n p i) = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p) := by
  refine ⟨?_, ?_, ?_, hG⟩
  · intro a ha n i
    obtain ⟨P, hP, hE⟩ := rs_rhat_poly (M.box K₀) (rs_value_poly RD a n i)
    refine ⟨P, rs_poly_mono (by omega) (by omega) hP, fun p hp h0 => ?_⟩
    rw [rs_mode_formula c M RD K₀ R hM hR hI hm a ha n i p hp, hE p h0]
  · intro a ha n i b
    obtain ⟨P, hP, hE⟩ := rs_rhat_poly (M.box K₀) (rs_frameY_poly (rs_value_poly RD a n i) b)
    refine ⟨P, rs_poly_mono (by omega) (by omega) hP, fun p hp h0 => ?_⟩
    rw [rs_mode_formula c M RD K₀ R hM hR hI hm a ha n i p hp, hE p h0]
  · intro a ha n i b
    obtain ⟨P, hP, hE⟩ := rs_rhat_poly (M.box K₀) (rs_frameTurnY_poly (rs_value_poly RD a n i) b)
    refine ⟨P, rs_poly_mono (by omega) (by omega) hP, fun p hp h0 => ?_⟩
    rw [rs_mode_formula c M RD K₀ R hM hR hI hm a ha n i p hp, hE p h0]

private def smoothRadius (δ : ℝ) (y : Space) : ℝ :=
  Real.sqrt (δ ^ 2 / 4 + (y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) *
    Real.smoothTransition ((y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) * (2 / δ ^ 2)))

private theorem rs_inner_pos {δ : ℝ} (hδ : 0 < δ) (y : Space) :
    0 < δ ^ 2 / 4 + (y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) *
      Real.smoothTransition ((y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) * (2 / δ ^ 2)) := by
  have h4 : 0 < δ ^ 2 / 4 := by positivity
  have h2 : 0 < 2 / δ ^ 2 := by positivity
  rcases le_or_gt (y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) 0 with h | h
  · rw [Real.smoothTransition.zero_of_nonpos (by nlinarith)]
    linarith
  · have := Real.smoothTransition.nonneg ((y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) * (2 / δ ^ 2))
    nlinarith

private theorem rs_rho_ne {δ : ℝ} (hδ : 0 < δ) (y : Space) : smoothRadius δ y ≠ 0 :=
  (Real.sqrt_pos.2 (rs_inner_pos hδ y)).ne'

private theorem rs_rho_eq {δ : ℝ} (hδ : 0 < δ) (y : Space) (hr : δ ≤ cylRadius y) :
    smoothRadius δ y = cylRadius y := by
  have hs : δ ^ 2 ≤ y 0 ^ 2 + y 1 ^ 2 := by
    have h1 := pow_le_pow_left₀ hδ.le hr 2
    rwa [cylRadius, Real.sq_sqrt (by positivity)] at h1
  have h1 : 1 ≤ (y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) * (2 / δ ^ 2) := by
    rw [show (y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) * (2 / δ ^ 2) = (2 * (y 0 ^ 2 + y 1 ^ 2) - δ ^ 2 / 2) / δ ^ 2 by
      field_simp; ring, le_div_iff₀ (by positivity)]
    nlinarith
  unfold smoothRadius cylRadius
  rw [Real.smoothTransition.one_of_one_le h1]
  congr 1
  ring

private theorem rs_coord_smooth (i : Fin 3) : ContDiff ℝ 2 (fun y : Space => y i) := contDiff_piLp_apply 2

private theorem rs_rho_smooth {δ : ℝ} (hδ : 0 < δ) : ContDiff ℝ 2 (smoothRadius δ) := by
  have h0 := rs_coord_smooth 0
  have h1 := rs_coord_smooth 1
  have hT : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  have hs : ContDiff ℝ 2 (fun y : Space => y 0 ^ 2 + y 1 ^ 2 - δ ^ 2 / 4) :=
    ((h0.pow 2).add (h1.pow 2)).sub contDiff_const
  exact ContDiff.sqrt (contDiff_const.add (hs.mul (hT.comp (hs.mul contDiff_const))))
    (fun y => (rs_inner_pos hδ y).ne')

private def frameCart (u v : ℝ) (w : Fin 3 → ℝ) : Space :=
  w 0 • (EuclideanSpace.single 0 u + EuclideanSpace.single 1 v) +
    w 1 • (EuclideanSpace.single 0 (-v) + EuclideanSpace.single 1 u) + w 2 • EuclideanSpace.single 2 1

private theorem rs_cart_eq (θ : ℝ) (w : Fin 3 → ℝ) :
    cartOfFrame θ w = frameCart (Real.cos θ) (Real.sin θ) w := by
  ext i
  fin_cases i <;> simp [cartOfFrame, frameCart, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit]

private theorem rs_frameCart0 (u v : ℝ) (w : Fin 3 → ℝ) : frameCart u v w 0 = w 0 * u - w 1 * v := by
  simp [frameCart]
  ring

private theorem rs_frameCart1 (u v : ℝ) (w : Fin 3 → ℝ) : frameCart u v w 1 = w 0 * v + w 1 * u := by
  simp [frameCart]

private theorem rs_frameCart2 (u v : ℝ) (w : Fin 3 → ℝ) : frameCart u v w 2 = w 2 := by
  simp [frameCart]

private theorem rs_frameCart_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u v : E → ℝ}
    {w : E → Fin 3 → ℝ} (hu : ContDiff ℝ 2 u)
    (hv : ContDiff ℝ 2 v) (hw : ∀ c, ContDiff ℝ 2 (fun y => w y c)) :
    ContDiff ℝ 2 (fun y => frameCart (u y) (v y) (w y)) := by
  refine contDiff_piLp' 2 fun i => ?_
  fin_cases i
  · show ContDiff ℝ 2 (fun y => frameCart (u y) (v y) (w y) 0)
    simp only [rs_frameCart0]
    exact ((hw 0).mul hu).sub ((hw 1).mul hv)
  · show ContDiff ℝ 2 (fun y => frameCart (u y) (v y) (w y) 1)
    simp only [rs_frameCart1]
    exact ((hw 0).mul hv).add ((hw 1).mul hu)
  · show ContDiff ℝ 2 (fun y => frameCart (u y) (v y) (w y) 2)
    simp only [rs_frameCart2]
    exact hw 2

private theorem rs_angle_trig {y : Space} (hr : 0 < cylRadius y) :
    Real.cos (cylAngle y) = y 0 / cylRadius y ∧ Real.sin (cylAngle y) = y 1 / cylRadius y := by
  have hn : ‖((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)‖ = cylRadius y := by
    rw [Complex.norm_add_mul_I]
    rfl
  have hx : ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ≠ 0 := by
    intro h
    rw [h, norm_zero] at hn
    rw [← hn] at hr
    exact lt_irrefl _ hr
  unfold cylAngle
  rw [Complex.cos_arg hx, Complex.sin_arg, hn]
  simp

private theorem rs_exp_pow (m β : ℕ) (θ : ℝ) :
    Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ^ (β * m) := by
  rw [show ((azimuth m (β : ℤ) * θ : ℝ) : ℂ) * Complex.I = ((β * m : ℕ) : ℂ) * ((θ : ℂ) * Complex.I) by
    unfold azimuth; push_cast; ring, Complex.exp_nat_mul, Complex.exp_mul_I, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin]

private def smoothTestField {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (δ : ℝ) (b : Fin N) (y : Space) :
    Space :=
  frameCart (y 0 / smoothRadius δ y) (y 1 / smoothRadius δ y) (fun c =>
    (evalPoly (R.profile b c) (smoothRadius δ y) (y 2) *
      (((y 0 / smoothRadius δ y : ℝ) : ℂ) + ((y 1 / smoothRadius δ y : ℝ) : ℂ) * Complex.I) ^ (R.harmonic b * m)).re)

private theorem rs_smoothTest_smooth {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (b : Fin N) : ContDiff ℝ 2 (smoothTestField R m δ b) := by
  have hρ := rs_rho_smooth hδ
  have hu : ContDiff ℝ 2 (fun y : Space => y 0 / smoothRadius δ y) :=
    (rs_coord_smooth 0).div hρ (rs_rho_ne hδ)
  have hv : ContDiff ℝ 2 (fun y : Space => y 1 / smoothRadius δ y) :=
    (rs_coord_smooth 1).div hρ (rs_rho_ne hδ)
  have hρc : ContDiff ℝ 2 (fun y : Space => ((smoothRadius δ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hρ
  have hzc : ContDiff ℝ 2 (fun y : Space => ((y 2 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (rs_coord_smooth 2)
  have huc : ContDiff ℝ 2 (fun y : Space => ((y 0 / smoothRadius δ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hu
  have hvc : ContDiff ℝ 2 (fun y : Space => ((y 1 / smoothRadius δ y : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp hv
  refine rs_frameCart_smooth hu hv fun c => ?_
  have hE : ContDiff ℝ 2 (fun y : Space => evalPoly (R.profile b c) (smoothRadius δ y) (y 2)) := by
    unfold evalPoly
    exact ContDiff.sum fun j _ => ContDiff.sum fun l _ => (contDiff_const.mul (hρc.pow _)).mul (hzc.pow _)
  have hF : ContDiff ℝ 2 (fun y : Space => evalPoly (R.profile b c) (smoothRadius δ y) (y 2) *
      (((y 0 / smoothRadius δ y : ℝ) : ℂ) + ((y 1 / smoothRadius δ y : ℝ) : ℂ) * Complex.I) ^ (R.harmonic b * m)) :=
    hE.mul ((huc.add (hvc.mul contDiff_const)).pow _)
  exact Complex.reCLM.contDiff.comp hF

private theorem rs_smoothTest_eq {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) {δ : ℝ} (hδ : 0 < δ)
    (b : Fin N) (y : Space) (hy : y ∈ (M.box (R.cell b)).solid) (hz : 0 ≤ cylHeight y) (hr : δ ≤ cylRadius y) :
    R.testField m b y = smoothTestField R m δ b y := by
  have hpos : 0 < cylRadius y := lt_of_lt_of_le hδ hr
  obtain ⟨hc, hs⟩ := rs_angle_trig hpos
  have hvs : ∀ c, vectorSign y c = 1 := by
    intro c
    simp [vectorSign, not_lt.2 hz]
  unfold RowData.testField smoothTestField
  rw [Set.indicator_of_mem hy, rs_cart_eq, rs_rho_eq hδ y hr, hc, hs]
  simp only [hvs, one_mul, abs_of_nonneg hz, rs_exp_pow, hc, hs]
  rfl

theorem rowSmooth_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R) :
    ∀ a, ∀ δ : ℝ, 0 < δ → ∃ f : Space → Space, ContDiff ℝ 2 f ∧
      ∀ y ∈ (M.box (R.cell a)).solid, 0 ≤ cylHeight y → δ ≤ cylRadius y → c.row a y = f y := by
  intro a δ hδ
  refine ⟨fun y => ∑ b, R.mix a b • smoothTestField R c.order δ b y,
    ContDiff.sum fun b _ => (contDiff_const (c := R.mix a b)).smul (rs_smoothTest_smooth R c.order hδ b), ?_⟩
  intro y hy hz hr
  rw [hI.row_eq]
  unfold RowData.rowField
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : R.mix a b = 0
  · simp [hab]
  · have hcb := (rs_mix_support R c.order c.rowMax hR a b hab).1
    rw [rs_smoothTest_eq R c.order hδ b y (hcb ▸ hy) hz hr]

private theorem rs_norm_le (K : CellBox) (hK : IsCellBox K) {y : Space} (hy : y ∈ K.solid) :
    ‖y‖ ≤ K.r₂ + K.z₂ := by
  obtain ⟨_, h2, _, h4⟩ := hy
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hsq : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have hn : ‖y‖ = Real.sqrt (y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) := by
    rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hz2 : 0 ≤ K.z₂ := le_trans (abs_nonneg _) h4
  have hr2 : 0 ≤ K.r₂ := le_trans hr0 h2
  have a1 : cylRadius y ^ 2 ≤ K.r₂ ^ 2 := pow_le_pow_left₀ hr0 h2 2
  have a2 : |cylHeight y| ^ 2 ≤ K.z₂ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h4 2
  have a3 : 0 ≤ K.r₂ * K.z₂ := mul_nonneg hr2 hz2
  have a4 : |cylHeight y| ^ 2 = y 2 ^ 2 := by rw [sq_abs]; rfl
  rw [hn, ← Real.sqrt_sq (add_nonneg hr2 hz2)]
  apply Real.sqrt_le_sqrt
  nlinarith

private theorem rs_slope_of_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    {F : E → Space} (hF : ContDiff ℝ 2 F) (ρ : ℝ) : ∃ K, LipschitzOnWith K F (Metric.closedBall 0 ρ) :=
  ((hF.of_le (by norm_num)).locallyLipschitz.locallyLipschitzOn).exists_lipschitzOnWith_of_compact
    (isCompact_closedBall 0 ρ)

private theorem rs_radius_slope : LipschitzWith 1 cylRadius := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  have hr : ∀ u : Space, cylRadius u = ‖((u 0 : ℂ) + (u 1 : ℂ) * Complex.I)‖ := fun u => by
    rw [Complex.norm_add_mul_I]
    rfl
  rw [Real.dist_eq, hr x, hr y, NNReal.coe_one, one_mul]
  refine (abs_norm_sub_norm_le _ _).trans ?_
  have e : ((x 0 : ℂ) + (x 1 : ℂ) * Complex.I) - ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) =
      ((x 0 - y 0 : ℝ) : ℂ) + ((x 1 - y 1 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.norm_add_mul_I, EuclideanSpace.dist_eq, Fin.sum_univ_three]
  apply Real.sqrt_le_sqrt
  simp only [Real.dist_eq, sq_abs]
  nlinarith [sq_nonneg (x 2 - y 2)]

private def divPoly {d : ℕ} (P : CellPoly d) (s z : ℝ) : ℂ :=
  ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), P j l * (s : ℂ) ^ ((j : ℕ) - 1) * (z : ℂ) ^ (l : ℕ)

private theorem rs_divPoly {d : ℕ} (P : CellPoly d) (hP : ∀ l, P 0 l = 0) (s z : ℝ) :
    evalPoly P s z = (s : ℂ) * divPoly P s z := by
  unfold evalPoly divPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases hj : (j : ℕ) = 0
  · have : j = 0 := Fin.ext hj
    subst this
    simp [hP]
  · obtain ⟨i, hi⟩ : ∃ i, (j : ℕ) = i + 1 := ⟨(j : ℕ) - 1, by omega⟩
    rw [hi, Nat.add_sub_cancel, pow_succ]
    ring

private def axisField {M : CellMesh} {N : ℕ} (R : RowData M N) (b : Fin N) (q : ℝ × Space) : Space :=
  frameCart (q.2 0) (q.2 1) (fun c => if c = 2 then (evalPoly (R.profile b 2) q.1 (q.2 2)).re
    else (divPoly (R.profile b c) q.1 (q.2 2)).re)

private theorem rs_axisField_smooth {M : CellMesh} {N : ℕ} (R : RowData M N) (b : Fin N) :
    ContDiff ℝ 2 (axisField R b) := by
  have hs : ContDiff ℝ 2 (fun q : ℝ × Space => ((q.1 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have hc : ∀ i : Fin 3, ContDiff ℝ 2 (fun q : ℝ × Space => q.2 i) :=
    fun i => (contDiff_piLp_apply 2).comp contDiff_snd
  have hz : ContDiff ℝ 2 (fun q : ℝ × Space => ((q.2 2 : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp (hc 2)
  refine rs_frameCart_smooth (hc 0) (hc 1) fun c => ?_
  by_cases h2 : c = 2
  · simp only [h2, if_true]
    have hE : ContDiff ℝ 2 (fun q : ℝ × Space => evalPoly (R.profile b 2) q.1 (q.2 2)) := by
      unfold evalPoly
      exact ContDiff.sum fun j _ => ContDiff.sum fun l _ => (contDiff_const.mul (hs.pow _)).mul (hz.pow _)
    exact Complex.reCLM.contDiff.comp hE
  · simp only [h2, if_false]
    have hE : ContDiff ℝ 2 (fun q : ℝ × Space => divPoly (R.profile b c) q.1 (q.2 2)) := by
      unfold divPoly
      exact ContDiff.sum fun j _ => ContDiff.sum fun l _ => (contDiff_const.mul (hs.pow _)).mul (hz.pow _)
    exact Complex.reCLM.contDiff.comp hE

private theorem rs_axis_eq {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N)
    (hβ : R.harmonic b = 0) (hP : ∀ l, R.profile b 0 0 l = 0 ∧ R.profile b 1 0 l = 0)
    (y : Space) (hy : y ∈ (M.box (R.cell b)).solid) (hz : 0 ≤ cylHeight y) :
    R.testField m b y = axisField R b (cylRadius y, y) := by
  have hvs : ∀ c, vectorSign y c = 1 := by
    intro c
    simp [vectorSign, not_lt.2 hz]
  unfold RowData.testField
  rw [Set.indicator_of_mem hy]
  simp only [hvs, one_mul, abs_of_nonneg hz, hβ, azimuth, Nat.cast_zero, Int.cast_zero, zero_mul,
    Complex.ofReal_zero, Complex.exp_zero, mul_one]
  have e0 := rs_divPoly (R.profile b 0) (fun l => (hP l).1)
  have e1 := rs_divPoly (R.profile b 1) (fun l => (hP l).2)
  have hr0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have hsq : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  rcases eq_or_lt_of_le hr0 with h0 | hpos
  · rw [← h0] at hsq
    have hy0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have hy1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
    have hang : cylAngle y = 0 := by simp [cylAngle, hy0, hy1]
    rw [hang, ← h0]
    ext i
    fin_cases i <;> simp [cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      axisField, frameCart, hy0, hy1, cylHeight, e0, e1]
  · obtain ⟨hc, hs⟩ := rs_angle_trig hpos
    rw [rs_cart_eq, hc, hs]
    have hne : cylRadius y ≠ 0 := hpos.ne'
    ext i
    fin_cases i <;> simp [axisField, frameCart, cylHeight, e0, e1] <;> field_simp <;> ring

theorem rowHalfSlope_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R) :
    ∀ a, ∃ L : NNReal, LipschitzOnWith L (c.row a) ((M.box (R.cell a)).solid ∩ {y | 0 ≤ cylHeight y}) := by
  intro a
  have hK := hM.boxes (R.cell a)
  have hsub : ∀ y ∈ (M.box (R.cell a)).solid ∩ {y | 0 ≤ cylHeight y},
      y ∈ Metric.closedBall (0 : Space) ((M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂) :=
    fun y hy => mem_closedBall_zero_iff.2 (rs_norm_le _ hK hy.1)
  by_cases h0 : (M.box (R.cell a)).r₁ = 0
  · set G : ℝ × Space → Space := fun q => ∑ b, R.mix a b • axisField R b q with hG
    have hGs : ContDiff ℝ 2 G :=
      ContDiff.sum fun b _ => (contDiff_const (c := R.mix a b)).smul (rs_axisField_smooth R b)
    obtain ⟨K, hKl⟩ := rs_slope_of_smooth hGs ((M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂)
    have heq : ∀ y ∈ (M.box (R.cell a)).solid ∩ {y | 0 ≤ cylHeight y}, c.row a y = G (cylRadius y, y) := by
      intro y hy
      rw [hI.row_eq]
      unfold RowData.rowField
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : R.mix a b = 0
      · simp [hab]
      · have hcb := (rs_mix_support R c.order c.rowMax hR a b hab).1
        have h0b : (M.box (R.cell b)).r₁ = 0 := hcb ▸ h0
        rw [rs_axis_eq R c.order b (hR.axis_zeroMode b h0b) (hR.axis_regular b h0b) y (hcb ▸ hy.1) hy.2]
    have hmap : ∀ y ∈ (M.box (R.cell a)).solid ∩ {y | 0 ≤ cylHeight y},
        (cylRadius y, y) ∈ Metric.closedBall (0 : ℝ × Space) ((M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂) := by
      intro y hy
      have h1 := mem_closedBall_zero_iff.1 (hsub y hy)
      have h2 : cylRadius y ≤ (M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂ := by
        have := hy.1.2.1
        have : 0 ≤ (M.box (R.cell a)).z₂ := le_trans (abs_nonneg _) hy.1.2.2.2
        linarith
      rw [mem_closedBall_zero_iff, Prod.norm_def]
      refine max_le ?_ h1
      show ‖cylRadius y‖ ≤ _
      rw [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ cylRadius y from Real.sqrt_nonneg _)]
      exact h2
    have hg : LipschitzWith 1 (fun y : Space => (cylRadius y, y)) := by
      simpa using rs_radius_slope.prodMk LipschitzWith.id
    refine ⟨K * 1, fun x hx y hy => ?_⟩
    rw [heq x hx, heq y hy]
    calc edist (G (cylRadius x, x)) (G (cylRadius y, y)) ≤ K * edist (cylRadius x, x) (cylRadius y, y) :=
          hKl (hmap x hx) (hmap y hy)
      _ ≤ K * (((1 : NNReal) : ENNReal) * edist x y) := by gcongr; exact hg x y
      _ = ((K * 1 : NNReal) : ENNReal) * edist x y := by rw [ENNReal.coe_mul, mul_assoc]
  · have hδ : 0 < (M.box (R.cell a)).r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    obtain ⟨f, hf, hE⟩ := rowSmooth_of c M R hM hR hI a _ hδ
    obtain ⟨L, hL⟩ := rs_slope_of_smooth hf ((M.box (R.cell a)).r₂ + (M.box (R.cell a)).z₂)
    refine ⟨L, fun x hx y hy => ?_⟩
    rw [hE x hx.1 hx.2 hx.1.1, hE y hy.1 hy.2 hy.1.1]
    exact hL (hsub x hx) (hsub y hy)

private theorem rs_smooth_core {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hrow : c.row = R.rowField c.order) (hR : IsRowData R c.order c.rowMax) (a : Fin N) (δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Space → Space, ContDiff ℝ 2 f ∧
      ∀ y ∈ (M.box (R.cell a)).solid, 0 ≤ cylHeight y → δ ≤ cylRadius y → c.row a y = f y := by
  refine ⟨fun y => ∑ b, R.mix a b • smoothTestField R c.order δ b y,
    ContDiff.sum fun b _ => (contDiff_const (c := R.mix a b)).smul (rs_smoothTest_smooth R c.order hδ b), ?_⟩
  intro y hy hz hr
  rw [hrow]
  unfold RowData.rowField
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : R.mix a b = 0
  · simp [hab]
  · have hcb := (rs_mix_support R c.order c.rowMax hR a b hab).1
    rw [rs_smoothTest_eq R c.order hδ b y (hcb ▸ hy) hz hr]

private theorem rs_cart_frameVec (θ : ℝ) (u : Space) : cartOfFrame θ (fun i => frameVec θ u i) = u := by
  have hs := Real.sin_sq_add_cos_sq θ
  ext j
  fin_cases j <;>
    simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      PiLp.inner_apply] <;>
    first | linear_combination (u 0) * hs | linear_combination (u 1) * hs | ring

private theorem rs_row_cyl {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ) (hp : p ∈ (M.box K₀).rect)
    (θ : ℝ) :
    c.row a (cylPoint p.1 θ p.2) = cartOfFrame θ (fun i => (rowProfileSum RD a i p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re) := by
  rw [← rs_cart_frameVec θ (c.row a (cylPoint p.1 θ p.2))]
  congr 1
  funext i
  exact rs_row_frame c M RD K₀ R hM hR hI a ha p hp θ i

private theorem rs_row_hasFDeriv {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ)
    (h1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (h2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ) :
    HasFDerivAt (c.row a) (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) (cylPoint p.1 θ p.2) := by
  have hK := hM.boxes K₀
  have hK0 : RD.cell a = K₀ := (hI.rowSet_eq a).1 ha
  have hr : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 h1.1
  have hz : 0 < p.2 := lt_of_le_of_lt hK.z_order.1 h2.1
  obtain ⟨f, hf, hE⟩ := rs_smooth_core c M RD hI.row_eq hR a (p.1 / 2) (by linarith)
  have hcont : Continuous cylRadius := rs_radius_slope.continuous
  have hzc : Continuous cylHeight := (rs_coord_smooth 2).continuous
  set U : Set Space := {y | (M.box K₀).r₁ < cylRadius y} ∩ {y | cylRadius y < (M.box K₀).r₂} ∩
    {y | (M.box K₀).z₁ < cylHeight y} ∩ {y | cylHeight y < (M.box K₀).z₂} ∩ {y | p.1 / 2 < cylRadius y} with hU
  have hUo : IsOpen U :=
    ((((isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)).inter
      (isOpen_lt continuous_const hzc)).inter (isOpen_lt hzc continuous_const)).inter (isOpen_lt continuous_const hcont)
  have hR0 : cylRadius (cylPoint p.1 θ p.2) = p.1 := rs_cyl_radius hr.le θ p.2
  have hH0 : cylHeight (cylPoint p.1 θ p.2) = p.2 := rs_cyl2 _ _ _
  have hmem : cylPoint p.1 θ p.2 ∈ U := by
    simp only [hU, Set.mem_inter_iff, Set.mem_setOf_eq, hR0, hH0]
    exact ⟨⟨⟨⟨h1.1, h1.2⟩, h2.1⟩, h2.2⟩, by linarith⟩
  have hev : c.row a =ᶠ[nhds (cylPoint p.1 θ p.2)] f := by
    filter_upwards [hUo.mem_nhds hmem] with y hy
    simp only [hU, Set.mem_inter_iff, Set.mem_setOf_eq] at hy
    obtain ⟨⟨⟨⟨hy1, hy2⟩, hy3⟩, hy4⟩, hy5⟩ := hy
    have hz0 : 0 ≤ cylHeight y := le_trans hK.z_order.1 hy3.le
    have hsol : y ∈ (M.box (RD.cell a)).solid := by
      rw [hK0]
      exact ⟨hy1.le, hy2.le, by rw [abs_of_nonneg hz0]; exact hy3.le, by rw [abs_of_nonneg hz0]; exact hy4.le⟩
    exact hE y hsol hz0 hy5.le
  have hd : HasFDerivAt f (fderiv ℝ f (cylPoint p.1 θ p.2)) (cylPoint p.1 θ p.2) :=
    ((hf.differentiable (by norm_num)) _).hasFDerivAt
  rw [hev.fderiv_eq]
  exact hd.congr_of_eventuallyEq hev

private theorem rs_deriv_eval_r {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    HasDerivAt (fun s : ℝ => evalPoly P (r + s) z) (polyDr P r z) 0 := by
  unfold evalPoly polyDr
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => ?_
  have h1 := (hasDerivAt_pow (j : ℕ) (r + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add r)
  rw [add_zero, mul_one] at h1
  have h2 := ((h1.ofReal_comp).const_mul (P j l)).mul_const (((z : ℂ)) ^ (l : ℕ))
  refine (h2.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem rs_deriv_eval_z {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    HasDerivAt (fun s : ℝ => evalPoly P r (z + s)) (polyDz P r z) 0 := by
  unfold evalPoly polyDz
  refine HasDerivAt.fun_sum fun j _ => HasDerivAt.fun_sum fun l _ => ?_
  have h1 := (hasDerivAt_pow (l : ℕ) (z + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add z)
  rw [add_zero, mul_one] at h1
  have h2 := (h1.ofReal_comp).const_mul (P j l * ((r : ℂ)) ^ (j : ℕ))
  refine (h2.congr_deriv (by push_cast; ring)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem rs_curve_r (r θ z s : ℝ) : cylPoint (r + s) θ z = cylPoint r θ z + s • radialUnit θ := by
  ext i
  fin_cases i <;> simp [cylPoint, radialUnit] <;> ring

private theorem rs_curve_z (r θ z s : ℝ) : cylPoint r θ (z + s) = cylPoint r θ z + s • axialUnit := by
  ext i
  fin_cases i <;> simp [cylPoint, axialUnit]

private theorem rs_line_deriv (y v : Space) : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add y

private theorem rs_cos_deriv (θ : ℝ) : HasDerivAt (fun s : ℝ => Real.cos (θ + s)) (-Real.sin θ) 0 := by
  have h := (Real.hasDerivAt_cos (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

private theorem rs_sin_deriv (θ : ℝ) : HasDerivAt (fun s : ℝ => Real.sin (θ + s)) (Real.cos θ) 0 := by
  have h := (Real.hasDerivAt_sin (θ + 0)).comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add θ)
  rw [add_zero, mul_one] at h
  exact h

private theorem rs_curve_t (r θ z : ℝ) : HasDerivAt (fun s => cylPoint r (θ + s) z) (r • angularUnit θ) 0 := by
  have e : (fun s => cylPoint r (θ + s) z) = fun s =>
      (r * Real.cos (θ + s)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (r * Real.sin (θ + s)) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) + EuclideanSpace.single (2 : Fin 3) z := by
    funext s
    ext i
    fin_cases i <;> simp [cylPoint]
  have e2 : r • angularUnit θ = (r * -Real.sin θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
      (r * Real.cos θ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) + 0 := by
    ext i
    fin_cases i <;> simp [angularUnit]
  rw [e, e2]
  exact ((((rs_cos_deriv θ).const_mul r).smul_const _).add (((rs_sin_deriv θ).const_mul r).smul_const _)).add
    (hasDerivAt_const _ _)

private theorem rs_frame_deriv (θ : ℝ) (c : Fin 3) :
    HasDerivAt (fun s => frameUnit (θ + s) c) (![angularUnit θ, -radialUnit θ, 0] c) 0 := by
  fin_cases c
  · have e : (fun s => frameUnit (θ + s) 0) = fun s =>
        Real.cos (θ + s) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        Real.sin (θ + s) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
      funext s
      ext i
      fin_cases i <;> simp [frameUnit, radialUnit]
    have e2 : ![angularUnit θ, -radialUnit θ, 0] 0 = (-Real.sin θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        Real.cos θ • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
      ext i
      fin_cases i <;> simp [angularUnit]
    show HasDerivAt (fun s => frameUnit (θ + s) 0) (![angularUnit θ, -radialUnit θ, 0] 0) 0
    rw [e, e2]
    exact ((rs_cos_deriv θ).smul_const _).add ((rs_sin_deriv θ).smul_const _)
  · have e : (fun s => frameUnit (θ + s) 1) = fun s =>
        (-Real.sin (θ + s)) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        Real.cos (θ + s) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
      funext s
      ext i
      fin_cases i <;> simp [frameUnit, angularUnit]
    have e2 : ![angularUnit θ, -radialUnit θ, 0] 1 = (-Real.cos θ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (-Real.sin θ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) := by
      ext i
      fin_cases i <;> simp [radialUnit]
    show HasDerivAt (fun s => frameUnit (θ + s) 1) (![angularUnit θ, -radialUnit θ, 0] 1) 0
    rw [e, e2]
    exact ((rs_sin_deriv θ).neg.smul_const _).add ((rs_cos_deriv θ).smul_const _)
  · show HasDerivAt (fun s => frameUnit (θ + s) 2) (![angularUnit θ, -radialUnit θ, 0] 2) 0
    simpa [frameUnit] using hasDerivAt_const (0 : ℝ) axialUnit

private def rowDrSum {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ b, (RD.mix a b : ℂ) * polyDr (RD.profile b i) p.1 p.2

private def rowDzSum {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ b, (RD.mix a b : ℂ) * polyDz (RD.profile b i) p.1 p.2

private def turnPart {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ![-rowProfileSum RD a 1 p, rowProfileSum RD a 0 p, 0] i

private def gradCoef {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (m : ℕ) (i b' : Fin 3) (p : ℝ × ℝ) : ℂ :=
  if b' = 0 then rowDrSum RD a i p else if b' = 2 then rowDzSum RD a i p else
    ((p.1⁻¹ : ℝ) : ℂ) * (rowProfileSum RD a i p * ((azimuth m (RD.harmonic a : ℤ) : ℂ) * Complex.I) + turnPart RD a i p)

private theorem rs_re_deriv {f : ℝ → ℂ} {f' : ℂ} (hf : HasDerivAt f f' 0) :
    HasDerivAt (fun s => (f s).re) f'.re 0 := by
  exact Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hf

private theorem rs_cart_deriv (θ : ℝ) {w : Fin 3 → ℝ → ℝ} {w' : Fin 3 → ℝ} (hw : ∀ c, HasDerivAt (w c) (w' c) 0) :
    HasDerivAt (fun s => cartOfFrame θ (fun c => w c s)) (cartOfFrame θ w') 0 := by
  unfold cartOfFrame
  exact HasDerivAt.fun_sum fun c _ => (hw c).smul_const _

private theorem rs_dir_radial {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ)
    (h1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (h2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ) :
    fderiv ℝ (c.row a) (cylPoint p.1 θ p.2) (radialUnit θ) = cartOfFrame θ (fun i => (rowDrSum RD a i p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re) := by
  have hL := rs_row_hasFDeriv c M RD K₀ R hM hR hI a ha p h1 h2 θ
  have hg := hL.comp_hasDerivAt_of_eq (0 : ℝ) (rs_line_deriv (cylPoint p.1 θ p.2) (radialUnit θ)) (by simp)
  have hΨ : HasDerivAt (fun s => cartOfFrame θ (fun i => (rowProfileSum RD a i (p.1 + s, p.2) *
      Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re))
      (cartOfFrame θ (fun i => (rowDrSum RD a i p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re)) 0 := by
    refine rs_cart_deriv θ fun i => rs_re_deriv (HasDerivAt.mul_const ?_ _)
    unfold rowProfileSum rowDrSum
    exact HasDerivAt.fun_sum fun b _ => (rs_deriv_eval_r _ _ _).const_mul _
  have hK := hM.boxes K₀
  have hev : (c.row a ∘ fun s : ℝ => cylPoint p.1 θ p.2 + s • radialUnit θ) =ᶠ[nhds 0]
      (fun s => cartOfFrame θ (fun i => (rowProfileSum RD a i (p.1 + s, p.2) *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re)) := by
    have hn : Set.Ioo ((M.box K₀).r₁ - p.1) ((M.box K₀).r₂ - p.1) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [h1.1]) (by linarith [h1.2])
    filter_upwards [hn] with s hs
    simp only [Function.comp, ← rs_curve_r]
    exact rs_row_cyl c M RD K₀ R hM hR hI a ha (p.1 + s, p.2)
      ⟨⟨by linarith [hs.1], by linarith [hs.2]⟩, ⟨h2.1.le, h2.2.le⟩⟩ θ
  exact hg.unique (hΨ.congr_of_eventuallyEq hev)

private theorem rs_dir_axial {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ)
    (h1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (h2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ) :
    fderiv ℝ (c.row a) (cylPoint p.1 θ p.2) axialUnit = cartOfFrame θ (fun i => (rowDzSum RD a i p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re) := by
  have hL := rs_row_hasFDeriv c M RD K₀ R hM hR hI a ha p h1 h2 θ
  have hg := hL.comp_hasDerivAt_of_eq (0 : ℝ) (rs_line_deriv (cylPoint p.1 θ p.2) axialUnit) (by simp)
  have hΨ : HasDerivAt (fun s => cartOfFrame θ (fun i => (rowProfileSum RD a i (p.1, p.2 + s) *
      Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re))
      (cartOfFrame θ (fun i => (rowDzSum RD a i p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re)) 0 := by
    refine rs_cart_deriv θ fun i => rs_re_deriv (HasDerivAt.mul_const ?_ _)
    unfold rowProfileSum rowDzSum
    exact HasDerivAt.fun_sum fun b _ => (rs_deriv_eval_z _ _ _).const_mul _
  have hev : (c.row a ∘ fun s : ℝ => cylPoint p.1 θ p.2 + s • axialUnit) =ᶠ[nhds 0]
      (fun s => cartOfFrame θ (fun i => (rowProfileSum RD a i (p.1, p.2 + s) *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re)) := by
    have hn : Set.Ioo ((M.box K₀).z₁ - p.2) ((M.box K₀).z₂ - p.2) ∈ nhds (0 : ℝ) :=
      Ioo_mem_nhds (by linarith [h2.1]) (by linarith [h2.2])
    filter_upwards [hn] with s hs
    simp only [Function.comp, ← rs_curve_z]
    exact rs_row_cyl c M RD K₀ R hM hR hI a ha (p.1, p.2 + s)
      ⟨⟨h1.1.le, h1.2.le⟩, ⟨by linarith [hs.1], by linarith [hs.2]⟩⟩ θ
  exact hg.unique (hΨ.congr_of_eventuallyEq hev)

private theorem rs_exp_deriv (k θ : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp ((k * (θ + s) : ℝ) * Complex.I))
      (Complex.exp ((k * θ : ℝ) * Complex.I) * ((k : ℂ) * Complex.I)) 0 := by
  have h1 := (((hasDerivAt_id (0 : ℝ)).const_add θ).const_mul k).ofReal_comp.mul_const Complex.I
  have h2 := h1.cexp
  refine (h2.congr_deriv (by simp)).congr_of_eventuallyEq (Filter.Eventually.of_forall fun s => ?_)
  simp

private theorem rs_dir_angular {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ)
    (h1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (h2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ) :
    fderiv ℝ (c.row a) (cylPoint p.1 θ p.2) (angularUnit θ) = cartOfFrame θ (fun i => (gradCoef RD a c.order i 1 p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re) := by
  have hK := hM.boxes K₀
  have hr : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 h1.1
  have hp : p ∈ (M.box K₀).rect := ⟨⟨h1.1.le, h1.2.le⟩, ⟨h2.1.le, h2.2.le⟩⟩
  set κ : ℝ := azimuth c.order (RD.harmonic a : ℤ) with hκ
  set e : ℂ := Complex.exp ((κ * θ : ℝ) * Complex.I) with he
  have hL := rs_row_hasFDeriv c M RD K₀ R hM hR hI a ha p h1 h2 θ
  have hg := hL.comp_hasDerivAt_of_eq (0 : ℝ) (rs_curve_t p.1 θ p.2) (by simp)
  have hfun : (c.row a ∘ fun s => cylPoint p.1 (θ + s) p.2) = fun s =>
      ∑ j : Fin 3, (rowProfileSum RD a j p * Complex.exp ((κ * (θ + s) : ℝ) * Complex.I)).re • frameUnit (θ + s) j := by
    funext s
    simp only [Function.comp]
    rw [rs_row_cyl c M RD K₀ R hM hR hI a ha p hp (θ + s)]
    rfl
  have hΨ : HasDerivAt (fun s => ∑ j : Fin 3,
      (rowProfileSum RD a j p * Complex.exp ((κ * (θ + s) : ℝ) * Complex.I)).re • frameUnit (θ + s) j)
      (∑ j : Fin 3, ((rowProfileSum RD a j p * Complex.exp ((κ * (θ + 0) : ℝ) * Complex.I)).re •
        ![angularUnit θ, -radialUnit θ, 0] j +
        (rowProfileSum RD a j p * (e * ((κ : ℂ) * Complex.I))).re • frameUnit (θ + 0) j)) 0 := by
    refine HasDerivAt.fun_sum fun j _ => ?_
    exact (rs_re_deriv ((rs_exp_deriv κ θ).const_mul (rowProfileSum RD a j p))).smul (rs_frame_deriv θ j)
  rw [hfun] at hg
  have hu := hg.unique hΨ
  rw [map_smul] at hu
  have key : p.1 • cartOfFrame θ (fun i => (gradCoef RD a c.order i 1 p * e).re) =
      ∑ j : Fin 3, ((rowProfileSum RD a j p * Complex.exp ((κ * (θ + 0) : ℝ) * Complex.I)).re •
        ![angularUnit θ, -radialUnit θ, 0] j +
        (rowProfileSum RD a j p * (e * ((κ : ℂ) * Complex.I))).re • frameUnit (θ + 0) j) := by
    have hG : ∀ i, (gradCoef RD a c.order i 1 p * e).re =
        p.1⁻¹ * ((rowProfileSum RD a i p * ((κ : ℂ) * Complex.I) + turnPart RD a i p) * e).re := by
      intro i
      simp only [gradCoef, if_neg (by decide : (1 : Fin 3) ≠ 0), if_neg (by decide : (1 : Fin 3) ≠ 2)]
      rw [mul_assoc, Complex.re_ofReal_mul]
    simp only [hG]
    have hne : p.1 ≠ 0 := hr.ne'
    ext j
    fin_cases j <;>
      simp [cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, turnPart,
        Complex.mul_re, he] <;> field_simp <;> ring
  have hfin := hu.trans key.symm
  exact smul_right_injective Space hr.ne' hfin

private theorem rs_grad_entry {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ)
    (h1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (h2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ)
    (i b' : Fin 3) :
    frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i b' = (gradCoef RD a c.order i b' p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re := by
  have hv : ∀ b' : Fin 3, fderiv ℝ (c.row a) (cylPoint p.1 θ p.2) (frameUnit θ b') =
      cartOfFrame θ (fun i => (gradCoef RD a c.order i b' p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re) := by
    intro b'
    fin_cases b'
    · exact rs_dir_radial c M RD K₀ R hM hR hI a ha p h1 h2 θ
    · exact rs_dir_angular c M RD K₀ R hM hR hI a ha p h1 h2 θ
    · exact rs_dir_axial c M RD K₀ R hM hR hI a ha p h1 h2 θ
  calc frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i b' =
        frameVec θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2) (frameUnit θ b')) i := by
          rw [rs_frameVec_apply]
          rfl
    _ = _ := by rw [hv, rs_frameVec_cart]

private theorem rs_poly_monomial {d : ℕ} (s : ℂ) (j l : ℕ) (hj : j ≤ d) (hl : l ≤ d) :
    (fun p : ℝ × ℝ => s * (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) ∈ polyFn d d := by
  refine ⟨fun j' l' => if (j' : ℕ) = j ∧ (l' : ℕ) = l then s else 0, fun p => ?_⟩
  dsimp only
  rw [Fintype.sum_eq_single (⟨j, by omega⟩ : Fin (d + 1)) ?_]
  · rw [Fintype.sum_eq_single (⟨l, by omega⟩ : Fin (d + 1)) ?_]
    · simp
    · intro l' hl'
      have : (l' : ℕ) ≠ l := fun h => hl' (Fin.ext h)
      simp [this]
  · intro j' hj'
    have : (j' : ℕ) ≠ j := fun h => hj' (Fin.ext h)
    exact Finset.sum_eq_zero fun l' _ => by simp [this]

private theorem rs_poly_dr {d : ℕ} (P : CellPoly d) : (fun p : ℝ × ℝ => polyDr P p.1 p.2) ∈ polyFn d d := by
  unfold polyDr
  exact rs_poly_sum fun j => rs_poly_sum fun l =>
    rs_poly_monomial (P j l * ((j : ℕ) : ℂ)) ((j : ℕ) - 1) l (by have := j.isLt; omega) (by have := l.isLt; omega)

private theorem rs_poly_dz {d : ℕ} (P : CellPoly d) : (fun p : ℝ × ℝ => polyDz P p.1 p.2) ∈ polyFn d d := by
  have h : (fun p : ℝ × ℝ => polyDz P p.1 p.2) = fun p => ∑ j : Fin (d + 1), ∑ l : Fin (d + 1),
      (P j l * ((l : ℕ) : ℂ)) * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ ((l : ℕ) - 1) := by
    funext p
    unfold polyDz
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [h]
  exact rs_poly_sum fun j => rs_poly_sum fun l =>
    rs_poly_monomial (P j l * ((l : ℕ) : ℂ)) j ((l : ℕ) - 1) (by have := j.isLt; omega) (by have := l.isLt; omega)

private theorem rs_poly_div {d : ℕ} (P : CellPoly d) : (fun p : ℝ × ℝ => divPoly P p.1 p.2) ∈ polyFn d d := by
  unfold divPoly
  exact rs_poly_sum fun j => rs_poly_sum fun l =>
    rs_poly_monomial (P j l) ((j : ℕ) - 1) l (by have := j.isLt; omega) (by have := l.isLt; omega)

private theorem rs_poly_conj_gen {d d' : ℕ} {F : ℝ × ℝ → ℂ} (hF : F ∈ polyFn d d') :
    (fun p => (starRingEnd ℂ) (F p)) ∈ polyFn d d' := by
  obtain ⟨a, ha⟩ := hF
  exact ⟨fun j l => (starRingEnd ℂ) (a j l), fun p => by simp [ha, map_sum, map_mul, map_pow]⟩

private theorem rs_mode_wrap (K : CellBox) {d : ℕ} (n : ℤ) (β : ℤ) {X W : ℝ × ℝ → ℂ} (hW : W ∈ polyFn d d)
    (hXW : ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo K.r₁ K.r₂ → p.2 ∈ Set.Ioo K.z₁ K.z₂ →
      ((CellScalars.rHat K p : ℝ) : ℂ) * X p = W p) :
    ∃ P ∈ polyFn d d, ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo K.r₁ K.r₂ → p.2 ∈ Set.Ioo K.z₁ K.z₂ →
      ((CellScalars.rHat K p : ℝ) : ℂ) * ((if n = β then X p / 2 else 0) +
        (if n = -β then (starRingEnd ℂ) (X p) / 2 else 0)) = P p := by
  refine ⟨fun p => (if n = β then W p / 2 else 0) + (if n = -β then (starRingEnd ℂ) (W p) / 2 else 0), ?_, ?_⟩
  · refine rs_poly_add ?_ ?_
    · by_cases h : n = β
      · simp only [h, if_true]
        have := rs_poly_smul (1 / 2 : ℂ) hW
        convert this using 1
        funext p
        ring
      · simp only [h, if_false]
        exact rs_poly_zero _ _
    · by_cases h : n = -β
      · simp only [h, if_true]
        have := rs_poly_smul (1 / 2 : ℂ) (rs_poly_conj_gen hW)
        convert this using 1
        funext p
        ring
      · simp only [h, if_false]
        exact rs_poly_zero _ _
  · intro p hp1 hp2
    have e := hXW p hp1 hp2
    have ec : (starRingEnd ℂ) (W p) = ((CellScalars.rHat K p : ℝ) : ℂ) * (starRingEnd ℂ) (X p) := by
      rw [← e, map_mul, Complex.conj_ofReal]
    dsimp only
    rw [ec, ← e]
    split_ifs <;> ring

private def rowDivSum {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ b, (RD.mix a b : ℂ) * divPoly (RD.profile b i) p.1 p.2

theorem rowLowGradient_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (S : CellScalars) (hM : IsCellMesh M)
    (hR : IsRowData RD c.order c.rowMax) (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order)
    (hdeg : RD.degree + 2 ≤ S.degHigh) :
    ∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p := by
  intro a ha n i b'
  have hK := hM.boxes K₀
  have hK0 : RD.cell a = K₀ := (hI.rowSet_eq a).1 ha
  have hmode : ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      rowModeGrad c a n p i b' = (if n = (RD.harmonic a : ℤ) then gradCoef RD a c.order i b' p / 2 else 0) +
        (if n = -(RD.harmonic a : ℤ) then (starRingEnd ℂ) (gradCoef RD a c.order i b' p) / 2 else 0) := by
    intro p h1 h2
    have key : ∀ θ, frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i b' = (gradCoef RD a c.order i b' p *
        Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re :=
      fun θ => rs_grad_entry c M RD K₀ R hM hR hI a ha p h1 h2 θ i b'
    simp only [rowModeGrad, modeMat, key]
    rw [rs_mode_val c.order hm n (RD.harmonic a)]
  suffices hW : ∃ W ∈ polyFn S.degHigh S.degHigh, ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ →
      p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * gradCoef RD a c.order i b' p = W p by
    obtain ⟨W, hWm, hWe⟩ := hW
    obtain ⟨P, hP, hPe⟩ := rs_mode_wrap (M.box K₀) n (RD.harmonic a : ℤ) hWm hWe
    refine ⟨P, hP, fun p h1 h2 => ?_⟩
    rw [hmode p h1 h2]
    exact hPe p h1 h2
  have hne_of : ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.1 ≠ 0 :=
    fun p h1 => (lt_of_le_of_lt hK.r_order.1 h1.1).ne'
  have hDr : (fun p => rowDrSum RD a i p) ∈ polyFn RD.degree RD.degree :=
    rs_poly_sum fun b => rs_poly_smul _ (rs_poly_dr _)
  have hDz : (fun p => rowDzSum RD a i p) ∈ polyFn RD.degree RD.degree :=
    rs_poly_sum fun b => rs_poly_smul _ (rs_poly_dz _)
  have hQ : ∀ j, (fun p => rowProfileSum RD a j p) ∈ polyFn RD.degree RD.degree :=
    fun j => rs_poly_sum fun b => rs_poly_smul _ (rs_poly_eval _)
  have hDv : ∀ j, (fun p => rowDivSum RD a j p) ∈ polyFn RD.degree RD.degree :=
    fun j => rs_poly_sum fun b => rs_poly_smul _ (rs_poly_div _)
  have hneg : ∀ {F : ℝ × ℝ → ℂ}, F ∈ polyFn RD.degree RD.degree → (fun p => -F p) ∈ polyFn RD.degree RD.degree := by
    intro F hF
    have := rs_poly_smul (-1 : ℂ) hF
    convert this using 1
    funext p
    ring
  by_cases h0 : (M.box K₀).r₁ = 0
  · have hβ : RD.harmonic a = 0 := hR.axis_zeroMode a (by rw [hK0]; exact h0)
    have hrh : ∀ p : ℝ × ℝ, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) = 1 := by
      intro p hp
      simp [CellScalars.rHat, CellBox.lineWeight, h0, div_self hp]
    have hA : ∀ j : Fin 3, j ≠ 2 → ∀ p : ℝ × ℝ, rowProfileSum RD a j p = (p.1 : ℂ) * rowDivSum RD a j p := by
      intro j hj p
      unfold rowProfileSum rowDivSum
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hab : RD.mix a b = 0
      · simp [hab]
      · have hcb : RD.cell b = K₀ := (rs_mix_support RD c.order c.rowMax hR a b hab).1 ▸ hK0
        have hax := hR.axis_regular b (by rw [hcb]; exact h0)
        have hP : ∀ l, RD.profile b j 0 l = 0 := by
          intro l
          fin_cases j
          · exact (hax l).1
          · exact (hax l).2
          · exact absurd rfl hj
        rw [rs_divPoly _ hP]
        ring
    fin_cases b'
    · exact ⟨_, rs_poly_mono (by omega) (by omega) hDr, fun p h1 _ => by rw [hrh p (hne_of p h1), one_mul]; rfl⟩
    · refine ⟨fun p => ![-rowDivSum RD a 1 p, rowDivSum RD a 0 p, 0] i, ?_, fun p h1 _ => ?_⟩
      · refine rs_poly_mono (d := RD.degree) (d' := RD.degree) (by omega) (by omega) ?_
        fin_cases i
        · simpa using hneg (hDv 1)
        · simpa using hDv 0
        · simpa using rs_poly_zero RD.degree RD.degree
      · have hp := hne_of p h1
        rw [hrh p hp, one_mul]
        show gradCoef RD a c.order i 1 p = _
        simp only [gradCoef, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false, hβ]
        have hpc : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp
        fin_cases i <;>
          simp [turnPart, hA 0 (by decide) p, hA 1 (by decide) p, azimuth] <;> field_simp
    · exact ⟨_, rs_poly_mono (by omega) (by omega) hDz, fun p h1 _ => by rw [hrh p (hne_of p h1), one_mul]; rfl⟩
  · have hrh : ∀ p : ℝ × ℝ, ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) = (p.1 : ℂ) := by
      intro p
      simp [CellScalars.rHat, CellBox.lineWeight, h0]
    fin_cases b'
    · exact ⟨fun p => (p.1 : ℂ) * rowDrSum RD a i p, rs_poly_mono (by omega) (by omega) (rs_poly_fst hDr),
        fun p _ _ => by rw [hrh]; rfl⟩
    · refine ⟨fun p => rowProfileSum RD a i p * ((azimuth c.order (RD.harmonic a : ℤ) : ℂ) * Complex.I) +
        turnPart RD a i p, ?_, fun p h1 _ => ?_⟩
      · refine rs_poly_mono (d := RD.degree) (d' := RD.degree) (by omega) (by omega) (rs_poly_add ?_ ?_)
        · have := rs_poly_smul ((azimuth c.order (RD.harmonic a : ℤ) : ℂ) * Complex.I) (hQ i)
          convert this using 1
          funext p
          ring
        · fin_cases i
          · convert hneg (hQ 1) using 1
            try (funext p; rfl)
          · convert hQ 0 using 1
            try (funext p; rfl)
          · convert rs_poly_zero RD.degree RD.degree using 1
            try (funext p; rfl)
      · have hp := hne_of p h1
        rw [hrh p]
        show (p.1 : ℂ) * gradCoef RD a c.order i 1 p = _
        simp only [gradCoef, show (1 : Fin 3) ≠ 0 by decide, show (1 : Fin 3) ≠ 2 by decide, if_false]
        rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hp, Complex.ofReal_one, one_mul]
    · exact ⟨fun p => (p.1 : ℂ) * rowDzSum RD a i p, rs_poly_mono (by omega) (by omega) (rs_poly_fst hDz),
        fun p _ _ => by rw [hrh]; rfl⟩

theorem rowLow_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (S : CellScalars) (hM : IsCellMesh M)
    (hR : IsRowData RD c.order c.rowMax) (hI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order)
    (hdeg : RD.degree + 2 ≤ S.degHigh) :
    (∀ a ∈ R.rowSet, ∀ n i, ∃ P ∈ polyFn (S.degHigh - 1) (S.degHigh - 1),
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeVec c a n p i = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * (frameY p b * rowModeVec c a n p i) = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p ∈ (M.box K₀).rect, p.1 ≠ 0 → ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * (frameTurnY p b * rowModeVec c a n p i) = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n i b, ∃ P ∈ polyFn S.degHigh S.degHigh,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * rowModeGrad c a n p i b = P p) :=
  rowLow_of_gradient c M RD K₀ R S hM hR hI hm hdeg (rowLowGradient_of c M RD K₀ R S hM hR hI hm hdeg)

end GivenModel

end CellCert

end Breakdown

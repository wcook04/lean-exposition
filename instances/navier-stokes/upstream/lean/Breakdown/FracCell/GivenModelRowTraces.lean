import Breakdown.FracCell.GivenModelDefs
import Breakdown.FracCell.GivenModelMixClauses

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

private theorem rt_mix_support {M : CellMesh} {N : ℕ} (R : RowData M N) {m : ℕ} {rowMax : ℝ}
    (hR : IsRowData R m rowMax) (a b : Fin N) (h : R.mix a b ≠ 0) :
    R.cell a = R.cell b ∧ R.harmonic a = R.harmonic b :=
  (mix_clauses R m rowMax hR).2.1 a b h

private theorem rt_frameVec_apply (θ : ℝ) (u : Space) (i : Fin 3) : frameVec θ u i = inner ℝ u (frameUnit θ i) := by
  fin_cases i <;> rfl

private theorem rt_frameVec_cart (θ : ℝ) (w : Fin 3 → ℝ) (i : Fin 3) : frameVec θ (cartOfFrame θ w) i = w i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
      PiLp.inner_apply] <;>
    first | linear_combination (w 0) * hs | linear_combination (w 1) * hs

private theorem rt_frameVec_sum {N : ℕ} (θ : ℝ) (μ : Fin N → ℝ) (u : Fin N → Space) (i : Fin 3) :
    frameVec θ (∑ b, μ b • u b) i = ∑ b, μ b * frameVec θ (u b) i := by
  simp only [rt_frameVec_apply, sum_inner, real_inner_smul_left]

private theorem rt_cyl0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]

private theorem rt_cyl1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]

private theorem rt_cyl2 (r θ z : ℝ) : cylPoint r θ z 2 = z := by simp [cylPoint]

private theorem rt_cyl_radius {r : ℝ} (hr : 0 ≤ r) (θ z : ℝ) : cylRadius (cylPoint r θ z) = r := by
  unfold cylRadius
  rw [rt_cyl0, rt_cyl1]
  have h : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
    linear_combination r ^ 2 * Real.sin_sq_add_cos_sq θ
  rw [h, Real.sqrt_sq hr]

private theorem rt_cyl_angle {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    ∃ j : ℤ, cylAngle (cylPoint r θ z) = θ - j * (2 * Real.pi) := by
  have h : ((cylPoint r θ z 0 : ℝ) : ℂ) + ((cylPoint r θ z 1 : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Complex.cos θ + Complex.sin θ * Complex.I) := by
    rw [rt_cyl0, rt_cyl1]
    push_cast
    ring
  unfold cylAngle
  rw [h, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]
  exact ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, by rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]⟩

private theorem rt_eval_axis {d : ℕ} (P : CellPoly d) (hP : ∀ l, P 0 l = 0) (z : ℝ) : evalPoly P 0 z = 0 := by
  unfold evalPoly
  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun l _ => ?_
  by_cases hj : (j : ℕ) = 0
  · have : j = 0 := Fin.ext hj
    subst this
    simp [hP]
  · simp [zero_pow hj]

private theorem rt_exp_period (x : ℝ) (n : ℤ) :
    Complex.exp (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = Complex.exp ((x : ℂ) * Complex.I) := by
  rw [show (((x - n * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = (x : ℂ) * Complex.I - n * (2 * Real.pi * Complex.I) by
    push_cast; ring, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

private theorem rt_term_frame {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N)
    (hK : IsCellBox (M.box (R.cell b))) (p : ℝ × ℝ) (hp : p ∈ (M.box (R.cell b)).rect)
    (hax : p.1 = 0 → R.harmonic b = 0 ∧ ∀ l, R.profile b 0 0 l = 0 ∧ R.profile b 1 0 l = 0)
    (θ : ℝ) (i : Fin 3) :
    frameVec θ (R.testField m b (cylPoint p.1 θ p.2)) i =
      (evalPoly (R.profile b i) p.1 p.2 * Complex.exp ((azimuth m (R.harmonic b : ℤ) * θ : ℝ) * Complex.I)).re := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 hr1
  have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 hz1
  have hR : cylRadius (cylPoint p.1 θ p.2) = p.1 := rt_cyl_radius hr0 θ p.2
  have hH : cylHeight (cylPoint p.1 θ p.2) = p.2 := rt_cyl2 _ _ _
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
      simp [cylAngle, rt_cyl0, rt_cyl1, ← h0]
    have hE0 : evalPoly (R.profile b 0) p.1 p.2 = 0 := by
      rw [← h0]; exact rt_eval_axis _ (fun l => (hP l).1) _
    have hE1 : evalPoly (R.profile b 1) p.1 p.2 = 0 := by
      rw [← h0]; exact rt_eval_axis _ (fun l => (hP l).2) _
    rw [hang, hβ]
    fin_cases i <;>
      simp [frameVec, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit,
        PiLp.inner_apply, hE0, hE1, azimuth]
  · obtain ⟨j, hj⟩ := rt_cyl_angle hpos θ p.2
    rw [hj]
    have hf : frameUnit (θ - j * (2 * Real.pi)) = frameUnit θ := by
      simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
    have hc : ∀ w, cartOfFrame (θ - j * (2 * Real.pi)) w = cartOfFrame θ w := fun w => by
      unfold cartOfFrame; rw [hf]
    rw [hc]
    rw [show azimuth m (R.harmonic b : ℤ) * (θ - j * (2 * Real.pi)) =
        azimuth m (R.harmonic b : ℤ) * θ - ((R.harmonic b * m * j : ℤ) : ℝ) * (2 * Real.pi) by
      unfold azimuth; push_cast; ring, rt_exp_period]
    exact rt_frameVec_cart θ _ i

private def rt_profileSum {M : CellMesh} {N : ℕ} (RD : RowData M N) (a : Fin N) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ∑ b, (RD.mix a b : ℂ) * evalPoly (RD.profile b i) p.1 p.2

private theorem rt_row_frame {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (p : ℝ × ℝ) (hp : p ∈ (M.box K₀).rect)
    (θ : ℝ) (i : Fin 3) :
    frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      (rt_profileSum RD a i p * Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re := by
  have hK0 : RD.cell a = K₀ := (hI.rowSet_eq a).1 ha
  rw [hI.row_eq]
  unfold RowData.rowField rt_profileSum
  rw [rt_frameVec_sum, Finset.sum_mul, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : RD.mix a b = 0
  · simp [hab]
  · obtain ⟨hc, hh⟩ := rt_mix_support RD hR a b hab
    have hcb : RD.cell b = K₀ := hc ▸ hK0
    have hpb : p ∈ (M.box (RD.cell b)).rect := hcb ▸ hp
    have hax : p.1 = 0 → RD.harmonic b = 0 ∧ ∀ l, RD.profile b 0 0 l = 0 ∧ RD.profile b 1 0 l = 0 := by
      intro h0
      have hr1 : (M.box (RD.cell b)).r₁ = 0 :=
        le_antisymm (h0 ▸ hpb.1.1) (hM.boxes (RD.cell b)).r_order.1
      exact ⟨hR.axis_zeroMode b hr1, hR.axis_regular b hr1⟩
    rw [rt_term_frame RD c.order b (hM.boxes _) p hpb hax θ i, hh, mul_assoc, Complex.re_ofReal_mul]

private theorem rt_int_exp (j : ℤ) :
    ∫ x in (0 : ℝ)..(2 * Real.pi), Complex.exp ((j : ℂ) * Complex.I * (x : ℂ)) =
      if j = 0 then 2 * (Real.pi : ℂ) else 0 := by
  split_ifs with hj
  · subst hj
    simp
  · have hc : (j : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hj) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show (j : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ) = j * (2 * Real.pi * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I j
    rw [h1]
    simp

private theorem rt_mode_key (m : ℕ) (n : ℤ) (β : ℕ) (E : ℂ) (θ : ℝ) :
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

private theorem rt_mode_val (m : ℕ) (n : ℤ) (β : ℕ) (E : ℂ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (((E * Complex.exp ((azimuth m (β : ℤ) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
      (if ((β : ℤ) - n) * m = 0 then (1 / 2 : ℂ) else 0) * E +
        (if (-((β : ℤ) + n)) * m = 0 then (1 / 2 : ℂ) else 0) * (starRingEnd ℂ) E := by
  simp only [rt_mode_key]
  rw [intervalIntegral.integral_add, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    rt_int_exp, rt_int_exp]
  · have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    split_ifs <;> field_simp <;> ring
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _
  · exact (by fun_prop : Continuous _).intervalIntegrable _ _

private theorem rt_mode_formula {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (a : Fin N) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3)
    (p : ℝ × ℝ) (hp : p ∈ (M.box K₀).rect) :
    rowModeVec c a n p i =
      (if ((RD.harmonic a : ℤ) - n) * c.order = 0 then (1 / 2 : ℂ) else 0) * rt_profileSum RD a i p +
        (if (-((RD.harmonic a : ℤ) + n)) * c.order = 0 then (1 / 2 : ℂ) else 0) *
          (starRingEnd ℂ) (rt_profileSum RD a i p) := by
  have key : ∀ θ, frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      (rt_profileSum RD a i p * Complex.exp ((azimuth c.order (RD.harmonic a : ℤ) * θ : ℝ) * Complex.I)).re :=
    fun θ => rt_row_frame c M RD K₀ R hM hR hI a ha p hp θ i
  simp only [rowModeVec, modeVec, key]
  exact rt_mode_val c.order n (RD.harmonic a) _

private theorem rt_eval_fixR {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    evalPoly P r z = ∑ l : Fin (d + 1), (∑ j, P j l * (r : ℂ) ^ (j : ℕ)) * (z : ℂ) ^ (l : ℕ) := by
  unfold evalPoly
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]

private theorem rt_eval_fixZ {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    evalPoly P r z = ∑ j : Fin (d + 1), (∑ l, P j l * (z : ℂ) ^ (l : ℕ)) * (r : ℂ) ^ (j : ℕ) := by
  unfold evalPoly
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem rt_lin {d N : ℕ} (α β : ℂ) (μ : Fin N → ℂ) (g : Fin N → Fin (d + 1) → ℂ) (t : ℝ) :
    α * (∑ b, μ b * ∑ l, g b l * (t : ℂ) ^ (l : ℕ)) + β * (starRingEnd ℂ) (∑ b, μ b * ∑ l, g b l * (t : ℂ) ^ (l : ℕ)) =
      ∑ l, (α * (∑ b, μ b * g b l) + β * (starRingEnd ℂ) (∑ b, μ b * g b l)) * (t : ℂ) ^ (l : ℕ) := by
  have h1 : (∑ b, μ b * ∑ l, g b l * (t : ℂ) ^ (l : ℕ)) = ∑ l, (∑ b, μ b * g b l) * (t : ℂ) ^ (l : ℕ) := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun b _ => by ring
  rw [h1]
  have h2 : (starRingEnd ℂ) (∑ l, (∑ b, μ b * g b l) * (t : ℂ) ^ (l : ℕ)) =
      ∑ l, (starRingEnd ℂ) (∑ b, μ b * g b l) * (t : ℂ) ^ (l : ℕ) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, map_pow, Complex.conj_ofReal]
  rw [h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun l _ => by ring

private def rt_ext {d : ℕ} (g : Fin (d + 1) → ℂ) (i : ℕ) : ℂ := if h : i < d + 1 then g ⟨i, h⟩ else 0

private theorem rt_pad {d : ℕ} (g : Fin (d + 1) → ℂ) (D : ℕ) (hg : ∀ l : Fin (d + 1), D ≤ (l : ℕ) → g l = 0)
    (t : ℂ) : ∑ l, g l * t ^ (l : ℕ) = ∑ i ∈ Finset.range D, rt_ext g i * t ^ i := by
  have e1 : ∑ l, g l * t ^ (l : ℕ) = ∑ i ∈ Finset.range (d + 1), rt_ext g i * t ^ i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => rt_ext g i * t ^ i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp [rt_ext, l.is_lt]
  have hz : ∀ i, d + 1 ≤ i → rt_ext g i = 0 := fun i hi => by simp [rt_ext, not_lt.2 hi]
  have hz' : ∀ i, D ≤ i → rt_ext g i = 0 := fun i hi => by
    unfold rt_ext
    split_ifs with h
    · exact hg ⟨i, h⟩ hi
    · rfl
  have s1 : ∑ i ∈ Finset.range (d + 1), rt_ext g i * t ^ i = ∑ i ∈ Finset.range (d + 1 + D), rt_ext g i * t ^ i :=
    Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => by
      rw [hz i (by simpa using hi), zero_mul]
  have s2 : ∑ i ∈ Finset.range D, rt_ext g i * t ^ i = ∑ i ∈ Finset.range (d + 1 + D), rt_ext g i * t ^ i :=
    Finset.sum_subset (Finset.range_subset_range.2 (by omega)) fun i _ hi => by
      rw [hz' i (by simpa using hi), zero_mul]
  rw [e1, s1, s2]

private theorem rt_span (S : FaceSegment) (hS : ∀ d, S.testCoef d d ≠ 0) :
    ∀ (D : ℕ) (c : ℕ → ℂ), ∃ cf : ℕ → ℂ, ∀ t : ℝ,
      ∑ i ∈ Finset.range D, c i * (t : ℂ) ^ i = ∑ d ∈ Finset.range D, cf d * ((S.test d t : ℝ) : ℂ) := by
  intro D
  induction D with
  | zero => intro c; exact ⟨0, fun t => by simp⟩
  | succ D ih =>
    intro c
    obtain ⟨cf, hcf⟩ := ih (fun i => c i - c D / (S.testCoef D D : ℂ) * (S.testCoef D i : ℂ))
    refine ⟨fun d => if d = D then c D / (S.testCoef D D : ℂ) else cf d, fun t => ?_⟩
    have hT : ((S.test D t : ℝ) : ℂ) = ∑ i ∈ Finset.range D, (S.testCoef D i : ℂ) * (t : ℂ) ^ i +
        (S.testCoef D D : ℂ) * (t : ℂ) ^ D := by
      simp [FaceSegment.test, Finset.sum_range_succ]
    have hne : (S.testCoef D D : ℂ) ≠ 0 := by exact_mod_cast hS D
    have hκ : c D / (S.testCoef D D : ℂ) * (S.testCoef D D : ℂ) = c D := by
      field_simp
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    beta_reduce
    rw [if_pos rfl]
    have hrest : ∑ d ∈ Finset.range D, (if d = D then c D / (S.testCoef D D : ℂ) else cf d) * ((S.test d t : ℝ) : ℂ) =
        ∑ d ∈ Finset.range D, cf d * ((S.test d t : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun d hd => by rw [if_neg (Finset.mem_range.1 hd).ne]
    rw [hrest, ← hcf t, hT]
    have hsplit : ∑ i ∈ Finset.range D, (c i - c D / (S.testCoef D D : ℂ) * (S.testCoef D i : ℂ)) * (t : ℂ) ^ i =
        ∑ i ∈ Finset.range D, c i * (t : ℂ) ^ i -
          c D / (S.testCoef D D : ℂ) * ∑ i ∈ Finset.range D, (S.testCoef D i : ℂ) * (t : ℂ) ^ i := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsplit]
    linear_combination (-(t : ℂ) ^ D) * hκ

theorem rowTraces_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (hL : IsPressureLayout c (M.box K₀) S B L) (hq : RD.degree ≤ L.degSide) :
    ∀ a ∈ R.rowSet, ∀ s n i, ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
        ∀ p ∈ (M.box K₀).rect, ((L.segment s).radial → p.1 = (L.segment s).level → CellFormula.rowModeVec c a n p i = Pl p.2) ∧
          (¬ (L.segment s).radial → p.2 = (L.segment s).level → CellFormula.rowModeVec c a n p i = Pl p.1) := by
  intro a ha s n i
  have hlead : ∀ d, (L.segment s).testCoef d d ≠ 0 := (hL.layout.segment_valid s).test_leading
  have hpad : ∀ l : Fin (RD.degree + 1), L.degSide + 1 ≤ (l : ℕ) → False := fun l hl => by
    have := l.is_lt
    omega
  by_cases hrad : (L.segment s).radial = true
  · obtain ⟨cf, hcf⟩ := rt_span _ hlead (L.degSide + 1)
      (rt_ext (fun l : Fin (RD.degree + 1) =>
        (if ((RD.harmonic a : ℤ) - n) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (∑ b, (RD.mix a b : ℂ) * ∑ j, RD.profile b i j l * ((L.segment s).level : ℂ) ^ (j : ℕ)) +
          (if (-((RD.harmonic a : ℤ) + n)) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (starRingEnd ℂ) (∑ b, (RD.mix a b : ℂ) * ∑ j, RD.profile b i j l * ((L.segment s).level : ℂ) ^ (j : ℕ))))
    refine ⟨fun t => ∑ d ∈ Finset.range (L.degSide + 1), cf d * (((L.segment s).test d t : ℝ) : ℂ),
      ⟨fun d => cf d, fun t => (Fin.sum_univ_eq_sum_range (fun d => cf d * (((L.segment s).test d t : ℝ) : ℂ)) _).symm⟩,
      fun p hp => ⟨fun _ hp1 => ?_, fun h => absurd hrad h⟩⟩
    show _ = ∑ d ∈ Finset.range (L.degSide + 1), cf d * (((L.segment s).test d p.2 : ℝ) : ℂ)
    rw [rt_mode_formula c M RD K₀ R hM hR hI a ha n i p hp, ← hcf, ← rt_pad _ _ (fun l hl => (hpad l hl).elim)]
    unfold rt_profileSum
    simp only [rt_eval_fixR, hp1]
    exact rt_lin _ _ _ _ _
  · obtain ⟨cf, hcf⟩ := rt_span _ hlead (L.degSide + 1)
      (rt_ext (fun j : Fin (RD.degree + 1) =>
        (if ((RD.harmonic a : ℤ) - n) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (∑ b, (RD.mix a b : ℂ) * ∑ l, RD.profile b i j l * ((L.segment s).level : ℂ) ^ (l : ℕ)) +
          (if (-((RD.harmonic a : ℤ) + n)) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (starRingEnd ℂ) (∑ b, (RD.mix a b : ℂ) * ∑ l, RD.profile b i j l * ((L.segment s).level : ℂ) ^ (l : ℕ))))
    refine ⟨fun t => ∑ d ∈ Finset.range (L.degSide + 1), cf d * (((L.segment s).test d t : ℝ) : ℂ),
      ⟨fun d => cf d, fun t => (Fin.sum_univ_eq_sum_range (fun d => cf d * (((L.segment s).test d t : ℝ) : ℂ)) _).symm⟩,
      fun p hp => ⟨fun h => absurd h hrad, fun _ hp2 => ?_⟩⟩
    show _ = ∑ d ∈ Finset.range (L.degSide + 1), cf d * (((L.segment s).test d p.1 : ℝ) : ℂ)
    rw [rt_mode_formula c M RD K₀ R hM hR hI a ha n i p hp, ← hcf, ← rt_pad _ _ (fun l hl => (hpad l hl).elim)]
    unfold rt_profileSum
    simp only [rt_eval_fixZ, hp2]
    exact rt_lin _ _ _ _ _

theorem rowNormalTraces_of {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (RD : RowData M N)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hM : IsCellMesh M) (hR : IsRowData RD c.order c.rowMax)
    (hI : IsRowsInstance c M RD K₀ R) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (hL : IsPressureLayout c (M.box K₀) S B L) (hq : RD.degree ≤ L.degSide) :
    ∀ a ∈ R.rowSet, ∀ s n, ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin L.degSide → ℂ, ∀ t, Pl t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
        ∀ p ∈ (M.box K₀).rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
            CellFormula.rowModeVec c a n p 0 = Pl p.2) ∧
          (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → CellFormula.rowModeVec c a n p 2 = Pl p.1) := by
  intro a ha s n
  have hlead : ∀ d, (L.presSegment s).testCoef d d ≠ 0 := (hL.layout.presSegment_valid s).test_leading
  have hlast : ∀ l : Fin (RD.degree + 1), L.degSide ≤ (l : ℕ) → l = Fin.last RD.degree := fun l hl => by
    have := l.is_lt
    ext
    simp only [Fin.val_last]
    omega
  by_cases hrad : (L.presSegment s).radial = true
  · obtain ⟨cf, hcf⟩ := rt_span _ hlead L.degSide
      (rt_ext (fun l : Fin (RD.degree + 1) =>
        (if ((RD.harmonic a : ℤ) - n) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (∑ b, (RD.mix a b : ℂ) * ∑ j, RD.profile b 0 j l * ((L.presSegment s).level : ℂ) ^ (j : ℕ)) +
          (if (-((RD.harmonic a : ℤ) + n)) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (starRingEnd ℂ) (∑ b, (RD.mix a b : ℂ) * ∑ j, RD.profile b 0 j l * ((L.presSegment s).level : ℂ) ^ (j : ℕ))))
    refine ⟨fun t => ∑ d ∈ Finset.range L.degSide, cf d * (((L.presSegment s).test d t : ℝ) : ℂ),
      ⟨fun d => cf d, fun t => (Fin.sum_univ_eq_sum_range (fun d => cf d * (((L.presSegment s).test d t : ℝ) : ℂ)) _).symm⟩,
      fun p hp => ⟨fun _ hp1 => ?_, fun h => absurd hrad h⟩⟩
    show _ = ∑ d ∈ Finset.range L.degSide, cf d * (((L.presSegment s).test d p.2 : ℝ) : ℂ)
    rw [rt_mode_formula c M RD K₀ R hM hR hI a ha n 0 p hp, ← hcf, ← rt_pad _ _ (fun l hl => by
      rw [hlast l hl]
      simp [(hR.normal_degree _ _).1])]
    unfold rt_profileSum
    simp only [rt_eval_fixR, hp1]
    exact rt_lin _ _ _ _ _
  · obtain ⟨cf, hcf⟩ := rt_span _ hlead L.degSide
      (rt_ext (fun j : Fin (RD.degree + 1) =>
        (if ((RD.harmonic a : ℤ) - n) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (∑ b, (RD.mix a b : ℂ) * ∑ l, RD.profile b 2 j l * ((L.presSegment s).level : ℂ) ^ (l : ℕ)) +
          (if (-((RD.harmonic a : ℤ) + n)) * c.order = 0 then (1 / 2 : ℂ) else 0) *
            (starRingEnd ℂ) (∑ b, (RD.mix a b : ℂ) * ∑ l, RD.profile b 2 j l * ((L.presSegment s).level : ℂ) ^ (l : ℕ))))
    refine ⟨fun t => ∑ d ∈ Finset.range L.degSide, cf d * (((L.presSegment s).test d t : ℝ) : ℂ),
      ⟨fun d => cf d, fun t => (Fin.sum_univ_eq_sum_range (fun d => cf d * (((L.presSegment s).test d t : ℝ) : ℂ)) _).symm⟩,
      fun p hp => ⟨fun h => absurd h hrad, fun _ hp2 => ?_⟩⟩
    show _ = ∑ d ∈ Finset.range L.degSide, cf d * (((L.presSegment s).test d p.1 : ℝ) : ℂ)
    rw [rt_mode_formula c M RD K₀ R hM hR hI a ha n 2 p hp, ← hcf, ← rt_pad _ _ (fun l hl => by
      rw [hlast l hl]
      simp [(hR.normal_degree _ _).2])]
    unfold rt_profileSum
    simp only [rt_eval_fixZ, hp2]
    exact rt_lin _ _ _ _ _

end GivenModel

end CellCert

end Breakdown

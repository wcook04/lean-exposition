import Breakdown.FracCell.GivenModelDefs
import Breakdown.FracCell.CylinderComp

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

namespace ModeCoverInternal

open SteadyCert CellAnalysis


open SteadyCert CellAnalysis

theorem exp_circle (m : ℕ) (hm : 0 < m) (k : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (((azimuth m k * θ : ℝ) : ℂ) * Complex.I) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  have hpt : ∀ θ : ℝ, Complex.exp (((azimuth m k * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((azimuth m k : ℂ) * Complex.I) * (θ : ℂ)) := fun θ => by
    congr 1; push_cast; ring
  simp_rw [hpt]
  split_ifs with hk
  · subst hk
    simp [azimuth]
  · have hc0 : ((azimuth m k : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      unfold azimuth
      push_cast
      exact mul_ne_zero (by exact_mod_cast hk) (by exact_mod_cast hm.ne')
    rw [integral_exp_mul_complex hc0]
    have h2 : Complex.exp (((azimuth m k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (k * m)
      rw [← this]
      congr 1
      unfold azimuth
      push_cast
      ring
    rw [h2]
    simp

theorem term_eq (m : ℕ) (n k : ℤ) (A : ℂ) (θ : ℝ) :
    Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        ((A * Complex.exp ((azimuth m k * θ : ℝ) * Complex.I)
          + (starRingEnd ℂ) (A * Complex.exp ((azimuth m k * θ : ℝ) * Complex.I))) / 2) =
      (1 / 2 : ℂ) * A * Complex.exp (((azimuth m (k - n) * θ : ℝ) : ℂ) * Complex.I)
        + (1 / 2 : ℂ) * (starRingEnd ℂ) A * Complex.exp (((azimuth m (-k - n) * θ : ℝ) : ℂ) * Complex.I) := by
  rw [map_mul, ← Complex.exp_conj]
  have e1 : (starRingEnd ℂ) (((azimuth m k * θ : ℝ) : ℂ) * Complex.I) = -(((azimuth m k * θ : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [e1]
  have e2 : ∀ a b : ℂ, Complex.exp a * Complex.exp b = Complex.exp (a + b) := fun a b => (Complex.exp_add a b).symm
  have h3 : Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Complex.exp (((azimuth m k * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((azimuth m (k - n) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [e2]
    congr 1
    unfold azimuth
    push_cast
    ring
  have h4 : Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Complex.exp (-(((azimuth m k * θ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((azimuth m (-k - n) * θ : ℝ) : ℂ) * Complex.I) := by
    rw [e2]
    congr 1
    unfold azimuth
    push_cast
    ring
  rw [← h3, ← h4]
  ring

theorem mode_re {ι : Type*} (s : Finset ι) (m : ℕ) (hm : 0 < m) (n : ℤ) (k : ι → ℤ) (A : ι → ℂ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (((∑ i ∈ s, A i * Complex.exp ((azimuth m (k i) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
    (1 / 2 : ℂ) * ∑ i ∈ s, ((if n = k i then A i else 0) + (if n = -k i then (starRingEnd ℂ) (A i) else 0)) := by
  have hpt : ∀ θ : ℝ, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (((∑ i ∈ s, A i * Complex.exp ((azimuth m (k i) * θ : ℝ) * Complex.I)).re : ℝ) : ℂ) =
      ∑ i ∈ s, ((1 / 2 : ℂ) * A i * Complex.exp (((azimuth m (k i - n) * θ : ℝ) : ℂ) * Complex.I)
        + (1 / 2 : ℂ) * (starRingEnd ℂ) (A i) * Complex.exp (((azimuth m (-k i - n) * θ : ℝ) : ℂ) * Complex.I)) := by
    intro θ
    rw [Complex.re_eq_add_conj, map_sum, ← Finset.sum_add_distrib, Finset.sum_div, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => term_eq m n (k i) (A i) θ)
  simp_rw [hpt]
  have hc : ∀ (j : ℤ) (B : ℂ), IntervalIntegrable (fun θ : ℝ => B * Complex.exp (((azimuth m j * θ : ℝ) : ℂ) * Complex.I))
      volume 0 (2 * Real.pi) := by
    intro j B
    apply Continuous.intervalIntegrable
    fun_prop
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hc _ _).add (hc _ _))]
  simp_rw [intervalIntegral.integral_add (hc _ _) (hc _ _), intervalIntegral.integral_const_mul, exp_circle m hm]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hpi : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by positivity : (2 * Real.pi) ≠ 0)
  have a1 : (k i - n = 0) ↔ (n = k i) := by omega
  have a2 : (-k i - n = 0) ↔ (n = -k i) := by omega
  simp only [a1, a2]
  split_ifs <;> push_cast at hpi ⊢ <;> field_simp <;> ring


theorem cyl_coords (r θ z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    cylRadius (cylPoint r θ z) = r ∧ cylHeight (cylPoint r θ z) = z ∧ |cylHeight (cylPoint r θ z)| = z := by
  have e0 : (cylPoint r θ z) 0 = r * Real.cos θ := by simp [cylPoint]
  have e1 : (cylPoint r θ z) 1 = r * Real.sin θ := by simp [cylPoint]
  have e2 : (cylPoint r θ z) 2 = z := by simp [cylPoint]
  refine ⟨?_, e2, ?_⟩
  · unfold cylRadius
    rw [e0, e1]
    have : (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 := by
      have := Real.sin_sq_add_cos_sq θ
      nlinarith
    rw [this, Real.sqrt_sq hr]
  · unfold cylHeight
    rw [e2, abs_of_nonneg hz]

theorem angle_cyl (r θ z : ℝ) (hr : 0 < r) : ∃ j : ℤ, cylAngle (cylPoint r θ z) = θ - j * (2 * Real.pi) := by
  have e0 : (cylPoint r θ z) 0 = r * Real.cos θ := by simp [cylPoint]
  have e1 : (cylPoint r θ z) 1 = r * Real.sin θ := by simp [cylPoint]
  unfold cylAngle
  rw [e0, e1]
  have h : ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * (Complex.cos (θ : ℂ) + Complex.sin (θ : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.arg_mul_cos_add_sin_mul_I_eq_toIocMod hr]
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, ?_⟩
  rw [← self_sub_toIocDiv_zsmul, zsmul_eq_mul]

theorem frame_angle (r θ z : ℝ) (hr : 0 < r) (a : Fin 3) : frameUnit (cylAngle (cylPoint r θ z)) a = frameUnit θ a := by
  obtain ⟨j, hj⟩ := angle_cyl r θ z hr
  rw [hj]
  fin_cases a <;> simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem exp_angle (r θ z : ℝ) (hr : 0 < r) (m : ℕ) (b : ℤ) :
    Complex.exp ((azimuth m b * cylAngle (cylPoint r θ z) : ℝ) * Complex.I) =
      Complex.exp ((azimuth m b * θ : ℝ) * Complex.I) := by
  obtain ⟨j, hj⟩ := angle_cyl r θ z hr
  rw [hj]
  have e : (((azimuth m b * (θ - j * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I) =
      (((azimuth m b * θ : ℝ) : ℂ) * Complex.I) + ((-(b * m * j) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold azimuth
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem frame_orth (θ : ℝ) (i j : Fin 3) :
    inner ℝ (frameUnit θ i) (frameUnit θ j) = if i = j then 1 else 0 := by
  have h := Real.sin_sq_add_cos_sq θ
  fin_cases i <;> fin_cases j <;> rw [PiLp.inner_apply] <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three] <;> nlinarith [h]

theorem frameVec_cart (θ : ℝ) (w : Fin 3 → ℝ) (a : Fin 3) : frameVec θ (cartOfFrame θ w) a = w a := by
  have hv : frameVec θ (cartOfFrame θ w) a = inner ℝ (cartOfFrame θ w) (frameUnit θ a) := by
    fin_cases a <;> rfl
  rw [hv]
  unfold cartOfFrame
  rw [sum_inner]
  simp only [real_inner_smul_left, frame_orth, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem frameMat_cart (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) : frameMat θ (cartOpOfFrame θ M) a b = M a b := by
  have hv : frameMat θ (cartOpOfFrame θ M) a b = inner ℝ (cartOpOfFrame θ M (frameUnit θ b)) (frameUnit θ a) := rfl
  rw [hv]
  unfold cartOpOfFrame
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, sum_inner, real_inner_smul_left, frame_orth]
  simp [Finset.sum_ite_eq']

theorem piece_iff (M : CellMesh) (K : Fin M.cellCount) {y y' : Space} (h1 : cylRadius y = cylRadius y')
    (h2 : |cylHeight y| = |cylHeight y'|) : y ∈ M.piece K ↔ y' ∈ M.piece K := by
  simp only [CellMesh.piece, CellBox.solid, Set.mem_sdiff, Set.mem_ofPred_eq, Set.mem_iUnion, h1, h2]

theorem region_iff (M : CellMesh) {y y' : Space} (h1 : cylRadius y = cylRadius y')
    (h2 : |cylHeight y| = |cylHeight y'|) : y ∈ M.region ↔ y' ∈ M.region := by
  simp only [CellMesh.region, CellBox.solid, Set.mem_ofPred_eq, Set.mem_iUnion, h1, h2]


theorem cart_angle (r θ z : ℝ) (hr : 0 < r) (w : Fin 3 → ℝ) :
    cartOfFrame (cylAngle (cylPoint r θ z)) w = cartOfFrame θ w := by
  unfold cartOfFrame
  simp only [frame_angle r θ z hr]

theorem cartOp_angle (r θ z : ℝ) (hr : 0 < r) (M : Fin 3 → Fin 3 → ℝ) :
    cartOpOfFrame (cylAngle (cylPoint r θ z)) M = cartOpOfFrame θ M := by
  unfold cartOpOfFrame
  simp only [frame_angle r θ z hr]

theorem signs_up (r θ z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) (a : Fin 3) :
    vectorSign (cylPoint r θ z) a = 1 ∧ pseudoSign (cylPoint r θ z) a = 1 := by
  have h := (cyl_coords r θ z hr hz).2.1
  have hn : ¬ cylHeight (cylPoint r θ z) < 0 := by rw [h]; exact not_lt.2 hz
  unfold vectorSign pseudoSign
  simp [hn]

theorem harm_circle (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (r θ z : ℝ) (hr : 0 < r) (hz : 0 ≤ z) :
    harmonicValue m P (cylPoint r θ z) =
      (∑ β : Fin (J + 1), ((((if (β : ℕ) = 0 then (1 : ℝ) else 2) : ℝ) : ℂ) * evalPoly (P β) r z) *
        Complex.exp ((azimuth m ((β : ℕ) : ℤ) * θ : ℝ) * Complex.I)).re := by
  obtain ⟨h1, -, h3⟩ := cyl_coords r θ z hr.le hz
  unfold harmonicValue
  rw [h1, h3]
  simp only [exp_angle r θ z hr]

theorem vec_circle (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → CellPoly d) (r θ z : ℝ) (hr : 0 < r) (hz : 0 ≤ z)
    (a : Fin 3) :
    frameVec θ (vectorOf m P (cylPoint r θ z)) a = harmonicValue m (fun β => P β a) (cylPoint r θ z) ∧
    frameVec θ (pseudoOf m P (cylPoint r θ z)) a = harmonicValue m (fun β => P β a) (cylPoint r θ z) := by
  unfold vectorOf pseudoOf
  rw [cart_angle r θ z hr, cart_angle r θ z hr, frameVec_cart, frameVec_cart]
  simp [(signs_up r θ z hr.le hz a).1, (signs_up r θ z hr.le hz a).2]

theorem mat_circle (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (r θ z : ℝ) (hr : 0 < r)
    (hz : 0 ≤ z) (a b : Fin 3) :
    frameMat θ (tensorOf m P (cylPoint r θ z)) a b = harmonicValue m (fun β => P β a b) (cylPoint r θ z) ∧
    frameMat θ (pseudoTensorOf m P (cylPoint r θ z)) a b = harmonicValue m (fun β => P β a b) (cylPoint r θ z) := by
  unfold tensorOf pseudoTensorOf
  rw [cartOp_angle r θ z hr, cartOp_angle r θ z hr, frameMat_cart, frameMat_cart]
  simp [(signs_up r θ z hr.le hz a).1, (signs_up r θ z hr.le hz a).2, (signs_up r θ z hr.le hz b).1]

open Classical in
theorem piecewise_circle {E : Type*} [AddCommMonoid E] (M : CellMesh) (f : Fin M.cellCount → Space → E)
    (r θ z : ℝ) (hr : 0 ≤ r) (hz : 0 ≤ z) :
    M.piecewise f (cylPoint r θ z) =
      ∑ K, if cylPoint r 0 z ∈ M.piece K then f K (cylPoint r θ z) else 0 := by
  unfold CellMesh.piecewise
  refine Finset.sum_congr rfl (fun K _ => ?_)
  obtain ⟨a1, -, a3⟩ := cyl_coords r θ z hr hz
  obtain ⟨b1, -, b3⟩ := cyl_coords r 0 z hr hz
  rw [Set.indicator_apply, piece_iff M K (y' := cylPoint r 0 z) (by rw [a1, b1]) (by rw [a3, b3])]

theorem frameVec_eq (θ : ℝ) (u : Space) (a : Fin 3) : frameVec θ u a = inner ℝ u (frameUnit θ a) := by
  fin_cases a <;> rfl

theorem frameVec_sum {ι : Type*} (s : Finset ι) (θ : ℝ) (u : ι → Space) (a : Fin 3) :
    frameVec θ (∑ i ∈ s, u i) a = ∑ i ∈ s, frameVec θ (u i) a := by
  simp only [frameVec_eq, sum_inner]

theorem frameVec_ite (θ : ℝ) (p : Prop) [Decidable p] (u : Space) (a : Fin 3) :
    frameVec θ (if p then u else 0) a = if p then frameVec θ u a else 0 := by
  split_ifs <;> simp [frameVec_eq]

theorem frameMat_eq (θ : ℝ) (X : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ X a b = inner ℝ (X (frameUnit θ b)) (frameUnit θ a) := rfl

theorem frameMat_sum {ι : Type*} (s : Finset ι) (θ : ℝ) (X : ι → Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ (∑ i ∈ s, X i) a b = ∑ i ∈ s, frameMat θ (X i) a b := by
  simp only [frameMat_eq, ContinuousLinearMap.sum_apply, sum_inner]

theorem frameMat_ite (θ : ℝ) (p : Prop) [Decidable p] (X : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ (if p then X else 0) a b = if p then frameMat θ X a b else 0 := by
  split_ifs <;> simp [frameMat_eq]

theorem re_collect (C J : ℕ) (c : Fin C → Prop) [DecidablePred c] (A : Fin C → Fin (J + 1) → ℂ) (m : ℕ) (θ : ℝ) :
    (∑ K, if c K then (∑ β : Fin (J + 1), A K β * Complex.exp ((azimuth m ((β : ℕ) : ℤ) * θ : ℝ) * Complex.I)).re else 0) =
      (∑ q : Fin C × Fin (J + 1), (if c q.1 then A q.1 q.2 else 0) *
        Complex.exp ((azimuth m ((q.2 : ℕ) : ℤ) * θ : ℝ) * Complex.I)).re := by
  rw [Fintype.sum_prod_type, Complex.re_sum]
  refine Finset.sum_congr rfl (fun K _ => ?_)
  split_ifs <;> simp


theorem vec_mode {ι : Type*} (s : Finset ι) (m : ℕ) (hm : 0 < m) (n : ℤ) (v : Space → Space) (r z : ℝ) (a : Fin 3)
    (k : ι → ℤ) (A : ι → ℂ)
    (h : ∀ θ : ℝ, frameVec θ (v (cylPoint r θ z)) a =
      (∑ i ∈ s, A i * Complex.exp ((azimuth m (k i) * θ : ℝ) * Complex.I)).re) :
    modeVec m n v r z a =
      (1 / 2 : ℂ) * ∑ i ∈ s, ((if n = k i then A i else 0) + (if n = -k i then (starRingEnd ℂ) (A i) else 0)) := by
  unfold modeVec
  simp_rw [h]
  exact mode_re s m hm n k A

theorem mat_mode {ι : Type*} (s : Finset ι) (m : ℕ) (hm : 0 < m) (n : ℤ) (G : Space → (Space →L[ℝ] Space))
    (r z : ℝ) (a b : Fin 3) (k : ι → ℤ) (A : ι → ℂ)
    (h : ∀ θ : ℝ, frameMat θ (G (cylPoint r θ z)) a b =
      (∑ i ∈ s, A i * Complex.exp ((azimuth m (k i) * θ : ℝ) * Complex.I)).re) :
    modeMat m n G r z a b =
      (1 / 2 : ℂ) * ∑ i ∈ s, ((if n = k i then A i else 0) + (if n = -k i then (starRingEnd ℂ) (A i) else 0)) := by
  unfold modeMat
  simp_rw [h]
  exact mode_re s m hm n k A

def wt {J : ℕ} (β : Fin (J + 1)) : ℂ := (((if (β : ℕ) = 0 then (1 : ℝ) else 2) : ℝ) : ℂ)

open Classical in
def cellCoef (M : CellMesh) {d J : ℕ} (E : Fin M.cellCount → Fin (J + 1) → CellPoly d) (r z : ℝ)
    (q : Fin M.cellCount × Fin (J + 1)) : ℂ :=
  if cylPoint r 0 z ∈ M.piece q.1 then wt q.2 * evalPoly (E q.1 q.2) r z else 0

theorem vec_field_mode (M : CellMesh) (m : ℕ) (hm : 0 < m) (n : ℤ) {d J : ℕ}
    (P : Fin M.cellCount → Fin (J + 1) → Fin 3 → CellPoly d) (r z : ℝ) (hr : 0 < r) (hz : 0 ≤ z) (a : Fin 3) :
    modeVec m n (M.piecewise (fun K => vectorOf m (P K))) r z a =
      (1 / 2 : ℂ) * ∑ q, ((if n = ((q.2 : ℕ) : ℤ) then cellCoef M (fun K β => P K β a) r z q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (cellCoef M (fun K β => P K β a) r z q) else 0)) ∧
    modeVec m n (M.piecewise (fun K => pseudoOf m (P K))) r z a =
      (1 / 2 : ℂ) * ∑ q, ((if n = ((q.2 : ℕ) : ℤ) then cellCoef M (fun K β => P K β a) r z q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (cellCoef M (fun K β => P K β a) r z q) else 0)) := by
  classical
  constructor
  · refine vec_mode Finset.univ m hm n _ r z a (fun q : Fin M.cellCount × Fin (J + 1) => ((q.2 : ℕ) : ℤ))
      (cellCoef M (fun K β => P K β a) r z) (fun θ => ?_)
    rw [piecewise_circle M _ r θ z hr.le hz, frameVec_sum]
    simp_rw [frameVec_ite, (vec_circle m _ r θ z hr hz a).1, harm_circle m _ r θ z hr hz]
    rw [re_collect]
    simp only [cellCoef, wt]
  · refine vec_mode Finset.univ m hm n _ r z a (fun q : Fin M.cellCount × Fin (J + 1) => ((q.2 : ℕ) : ℤ))
      (cellCoef M (fun K β => P K β a) r z) (fun θ => ?_)
    rw [piecewise_circle M _ r θ z hr.le hz, frameVec_sum]
    simp_rw [frameVec_ite, (vec_circle m _ r θ z hr hz a).2, harm_circle m _ r θ z hr hz]
    rw [re_collect]
    simp only [cellCoef, wt]

theorem mat_field_mode (M : CellMesh) (m : ℕ) (hm : 0 < m) (n : ℤ) {d J : ℕ}
    (P : Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (r z : ℝ) (hr : 0 < r) (hz : 0 ≤ z)
    (a b : Fin 3) :
    modeMat m n (M.piecewise (fun K => tensorOf m (P K))) r z a b =
      (1 / 2 : ℂ) * ∑ q, ((if n = ((q.2 : ℕ) : ℤ) then cellCoef M (fun K β => P K β a b) r z q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (cellCoef M (fun K β => P K β a b) r z q) else 0)) ∧
    modeMat m n (M.piecewise (fun K => pseudoTensorOf m (P K))) r z a b =
      (1 / 2 : ℂ) * ∑ q, ((if n = ((q.2 : ℕ) : ℤ) then cellCoef M (fun K β => P K β a b) r z q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (cellCoef M (fun K β => P K β a b) r z q) else 0)) := by
  classical
  constructor
  · refine mat_mode Finset.univ m hm n _ r z a b (fun q : Fin M.cellCount × Fin (J + 1) => ((q.2 : ℕ) : ℤ))
      (cellCoef M (fun K β => P K β a b) r z) (fun θ => ?_)
    rw [piecewise_circle M _ r θ z hr.le hz, frameMat_sum]
    simp_rw [frameMat_ite, (mat_circle m _ r θ z hr hz a b).1, harm_circle m _ r θ z hr hz]
    rw [re_collect]
    simp only [cellCoef, wt]
  · refine mat_mode Finset.univ m hm n _ r z a b (fun q : Fin M.cellCount × Fin (J + 1) => ((q.2 : ℕ) : ℤ))
      (cellCoef M (fun K β => P K β a b) r z) (fun θ => ?_)
    rw [piecewise_circle M _ r θ z hr.le hz, frameMat_sum]
    simp_rw [frameMat_ite, (mat_circle m _ r θ z hr hz a b).2, harm_circle m _ r θ z hr hz]
    rw [re_collect]
    simp only [cellCoef, wt]


theorem modeMat_congr (m : ℕ) (n : ℤ) (G G' : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (h : ∀ θ : ℝ, G (cylPoint r θ z) = G' (cylPoint r θ z)) : modeMat m n G r z = modeMat m n G' r z := by
  unfold modeMat
  simp_rw [h]

theorem modeVec_congr (m : ℕ) (n : ℤ) (v v' : Space → Space) (r z : ℝ)
    (h : ∀ θ : ℝ, v (cylPoint r θ z) = v' (cylPoint r θ z)) : modeVec m n v r z = modeVec m n v' r z := by
  unfold modeVec
  simp_rw [h]

theorem cyl_mem_solid (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  obtain ⟨h1, -, h3⟩ := cyl_coords p.1 θ p.2 (hK.r_order.1.trans hp.1.1) (hK.z_order.1.trans hp.2.1)
  simp only [CellBox.solid, Set.mem_ofPred_eq]
  rw [h1, h3]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

theorem strain_in (M : CellMesh) {k : ℕ} (D : ModelData M k) (m : ℕ) (cg : Space → (Space →L[ℝ] Space))
    (y : Space) (hy : y ∈ M.region) :
    D.strainField m cg y = M.piecewise (fun K => tensorOf m (D.strain K)) y := by
  unfold ModelData.strainField
  rw [Set.indicator_of_notMem (by simpa using hy), add_zero]

theorem curlGrad_in (M : CellMesh) {k : ℕ} (D : ModelData M k) (m : ℕ)
    (cs : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) (hy : y ∈ M.region) :
    D.curlGradField m cs y = M.piecewise (fun K => pseudoTensorOf m (D.curlGrad K)) y := by
  unfold ModelData.curlGradField
  rw [Set.indicator_of_notMem (by simpa using hy), add_zero]

theorem sum_zero_of {C J : ℕ} (n : ℤ) (f : Fin C × Fin (J + 1) → ℂ)
    (hβ : ∀ β : Fin (J + 1), n ≠ ((β : ℕ) : ℤ) ∧ n ≠ -((β : ℕ) : ℤ)) :
    (1 / 2 : ℂ) * ∑ q : Fin C × Fin (J + 1), ((if n = ((q.2 : ℕ) : ℤ) then f q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (f q) else 0)) = 0 := by
  rw [Finset.sum_eq_zero (fun q _ => by rw [if_neg (hβ q.2).1, if_neg (hβ q.2).2, add_zero]), mul_zero]


theorem poly_sum' {d d' : ℕ} {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} (h : ∀ i ∈ s, f i ∈ polyFn d d') :
    (fun p => ∑ i ∈ s, f i p) ∈ polyFn d d' := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ _ => 0, fun p => by simp⟩
  | insert i s hi ih =>
    obtain ⟨c1, h1⟩ := h i (Finset.mem_insert_self i s)
    obtain ⟨c2, h2⟩ := ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
    refine ⟨fun j l => c1 j l + c2 j l, fun p => ?_⟩
    beta_reduce at h2 ⊢
    rw [Finset.sum_insert hi, h1 p, h2 p, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring

theorem poly_smul' {d d' : ℕ} {f : ℝ × ℝ → ℂ} (c : ℂ) (h : f ∈ polyFn d d') : (fun p => c * f p) ∈ polyFn d d' := by
  obtain ⟨c0, hc0⟩ := h
  refine ⟨fun j l => c * c0 j l, fun p => ?_⟩
  beta_reduce
  rw [hc0 p, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  ring

theorem poly_add' {d d' : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') (hg : g ∈ polyFn d d') :
    (fun p => f p + g p) ∈ polyFn d d' := by
  have := poly_sum' (Finset.univ : Finset (Fin 2)) (f := ![f, g]) (fun i _ => by fin_cases i <;> simpa)
  simpa [Fin.sum_univ_two] using this

theorem poly_zero' {d d' : ℕ} : (fun _ : ℝ × ℝ => (0 : ℂ)) ∈ polyFn d d' := ⟨fun _ _ => 0, fun p => by simp⟩

theorem poly_congr' {d d' : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') (h : ∀ p, g p = f p) : g ∈ polyFn d d' := by
  have : g = f := funext h
  rw [this]
  exact hf

theorem poly_ite' {d d' : ℕ} (c : Prop) [Decidable c] {f : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') :
    (fun p => if c then f p else 0) ∈ polyFn d d' := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using (poly_zero' (d := d) (d' := d'))

theorem poly_mon' {d d' j l : ℕ} (hj : j ≤ d) (hl : l ≤ d') :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l) ∈ polyFn d d' := by
  refine ⟨fun a b => if (a : ℕ) = j ∧ (b : ℕ) = l then 1 else 0, fun p => ?_⟩
  rw [Finset.sum_eq_single (⟨j, by omega⟩ : Fin (d + 1))]
  · rw [Finset.sum_eq_single (⟨l, by omega⟩ : Fin (d' + 1))]
    · simp
    · intro b _ hb
      have : (b : ℕ) ≠ l := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  · intro a _ ha
    have : (a : ℕ) ≠ j := fun h => ha (Fin.ext h)
    simp [this]
  · simp

theorem poly_mono' {d d' e e' : ℕ} (he : d ≤ e) (he' : d' ≤ e') {f : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') :
    f ∈ polyFn e e' := by
  obtain ⟨c0, hc0⟩ := hf
  refine poly_congr' (poly_sum' Finset.univ (fun j _ => poly_sum' Finset.univ (fun l _ =>
    poly_smul' (c0 j l) (poly_mon' (d := e) (d' := e') (j := (j : ℕ)) (l := (l : ℕ)) (by omega) (by omega))))) ?_
  intro p
  rw [hc0 p]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem poly_mul' {d d' e e' : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') (hg : g ∈ polyFn e e') :
    (fun p => f p * g p) ∈ polyFn (d + e) (d' + e') := by
  obtain ⟨c1, h1⟩ := hf
  obtain ⟨c2, h2⟩ := hg
  refine poly_congr' (poly_sum' Finset.univ (fun j _ => poly_sum' Finset.univ (fun l _ =>
    poly_sum' Finset.univ (fun j' _ => poly_sum' Finset.univ (fun l' _ =>
    poly_smul' (c1 j l * c2 j' l') (poly_mon' (d := d + e) (d' := d' + e') (j := (j : ℕ) + (j' : ℕ))
      (l := (l : ℕ) + (l' : ℕ)) (by omega) (by omega))))))) ?_
  intro p
  rw [h1 p, h2 p, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j' _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l' _ => ?_)
  ring

theorem poly_conj' {d d' : ℕ} {f : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') :
    (fun p => (starRingEnd ℂ) (f p)) ∈ polyFn d d' := by
  obtain ⟨c0, hc0⟩ := hf
  refine ⟨fun j l => (starRingEnd ℂ) (c0 j l), fun p => ?_⟩
  beta_reduce
  rw [hc0 p]
  simp [map_sum, map_mul, map_pow, Complex.conj_ofReal]

theorem poly_eval' {d : ℕ} (E : CellPoly d) : (fun p : ℝ × ℝ => evalPoly E p.1 p.2) ∈ polyFn d d :=
  ⟨E, fun p => rfl⟩

theorem poly_fst' : (fun p : ℝ × ℝ => (p.1 : ℂ)) ∈ polyFn 1 0 := by
  refine poly_congr' (poly_mon' (d := 1) (d' := 0) (j := 1) (l := 0) le_rfl le_rfl) ?_
  intro p
  simp

theorem poly_const' {d d' : ℕ} (c : ℂ) : (fun _ : ℝ × ℝ => c) ∈ polyFn d d' := by
  refine poly_congr' (poly_smul' c (poly_mon' (d := d) (d' := d') (j := 0) (l := 0) (Nat.zero_le _) (Nat.zero_le _))) ?_
  intro p
  simp


theorem interior_mem (M : CellMesh) (hM : IsCellMesh M) (K₀ K : Fin M.cellCount) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (hp2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) (θ : ℝ) :
    (cylPoint p.1 θ p.2 ∈ (M.box K).solid ↔ K = K₀) ∧ (cylPoint p.1 θ p.2 ∈ M.piece K ↔ K = K₀) := by
  have hB := hM.boxes K₀
  have hr : 0 ≤ p.1 := hB.r_order.1.trans hp1.1.le
  have hz : 0 ≤ p.2 := hB.z_order.1.trans hp2.1.le
  obtain ⟨h1, -, h3⟩ := cyl_coords p.1 θ p.2 hr hz
  have hsol : ∀ K' : Fin M.cellCount, cylPoint p.1 θ p.2 ∈ (M.box K').solid ↔ K' = K₀ := by
    intro K'
    simp only [CellBox.solid, Set.mem_ofPred_eq]
    rw [h1, h3]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩
      by_contra hne
      rcases hM.interiors_disjoint K₀ K' (Ne.symm hne) with h | h | h | h
      · linarith [hp1.2]
      · linarith [hp1.1]
      · linarith [hp2.2]
      · linarith [hp2.1]
    · rintro rfl
      exact ⟨hp1.1.le, hp1.2.le, hp2.1.le, hp2.2.le⟩
  refine ⟨hsol K, ?_⟩
  constructor
  · intro h
    exact (hsol K).1 h.1
  · rintro rfl
    refine ⟨(hsol K).2 rfl, ?_⟩
    simp only [Set.mem_iUnion, not_exists]
    intro K' hK' hmem
    have := (hsol K').1 hmem
    subst this
    simp at hK'

theorem cellCoef_interior (M : CellMesh) (hM : IsCellMesh M) (K₀ : Fin M.cellCount) {d J : ℕ}
    (E : Fin M.cellCount → Fin (J + 1) → CellPoly d) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (hp2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂)
    (q : Fin M.cellCount × Fin (J + 1)) :
    cellCoef M E p.1 p.2 q = if q.1 = K₀ then wt q.2 * evalPoly (E q.1 q.2) p.1 p.2 else 0 := by
  unfold cellCoef
  by_cases h : q.1 = K₀
  · rw [if_pos ((interior_mem M hM K₀ q.1 p hp1 hp2 0).2.2 h), if_pos h]
  · rw [if_neg (fun hh => h ((interior_mem M hM K₀ q.1 p hp1 hp2 0).2.1 hh)), if_neg h]

def interiorPoly (M : CellMesh) (K₀ : Fin M.cellCount) {d J : ℕ} (E : Fin M.cellCount → Fin (J + 1) → CellPoly d)
    (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑ q : Fin M.cellCount × Fin (J + 1),
    ((if n = ((q.2 : ℕ) : ℤ) then (if q.1 = K₀ then wt q.2 * evalPoly (E q.1 q.2) p.1 p.2 else 0) else 0) +
      (if n = -((q.2 : ℕ) : ℤ) then
        (starRingEnd ℂ) (if q.1 = K₀ then wt q.2 * evalPoly (E q.1 q.2) p.1 p.2 else 0) else 0))

theorem interiorPoly_mem (M : CellMesh) (K₀ : Fin M.cellCount) {d J : ℕ}
    (E : Fin M.cellCount → Fin (J + 1) → CellPoly d) (n : ℤ) : interiorPoly M K₀ E n ∈ polyFn d d := by
  unfold interiorPoly
  refine poly_smul' _ (poly_sum' _ (fun q _ => poly_add' ?_ ?_))
  · exact poly_ite' _ (poly_ite' _ (poly_smul' _ (poly_eval' _)))
  · exact poly_ite' _ (poly_conj' (poly_ite' _ (poly_smul' _ (poly_eval' _))))

theorem vec_interior (M : CellMesh) (hM : IsCellMesh M) (K₀ : Fin M.cellCount) (m : ℕ) (hm : 0 < m) (n : ℤ)
    {d J : ℕ} (P : Fin M.cellCount → Fin (J + 1) → Fin 3 → CellPoly d) (a : Fin 3) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (hp2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) :
    modeVec m n (M.piecewise (fun K => vectorOf m (P K))) p.1 p.2 a = interiorPoly M K₀ (fun K β => P K β a) n p ∧
    modeVec m n (M.piecewise (fun K => pseudoOf m (P K))) p.1 p.2 a = interiorPoly M K₀ (fun K β => P K β a) n p := by
  have hB := hM.boxes K₀
  have hr : 0 < p.1 := lt_of_le_of_lt hB.r_order.1 hp1.1
  have hz : 0 ≤ p.2 := hB.z_order.1.trans hp2.1.le
  obtain ⟨e1, e2⟩ := vec_field_mode M m hm n P p.1 p.2 hr hz a
  rw [e1, e2]
  simp only [cellCoef_interior M hM K₀ _ p hp1 hp2, interiorPoly, and_self]

theorem mat_interior (M : CellMesh) (hM : IsCellMesh M) (K₀ : Fin M.cellCount) (m : ℕ) (hm : 0 < m) (n : ℤ)
    {d J : ℕ} (P : Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (a b : Fin 3) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (hp2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) :
    modeMat m n (M.piecewise (fun K => tensorOf m (P K))) p.1 p.2 a b = interiorPoly M K₀ (fun K β => P K β a b) n p ∧
    modeMat m n (M.piecewise (fun K => pseudoTensorOf m (P K))) p.1 p.2 a b =
      interiorPoly M K₀ (fun K β => P K β a b) n p := by
  have hB := hM.boxes K₀
  have hr : 0 < p.1 := lt_of_le_of_lt hB.r_order.1 hp1.1
  have hz : 0 ≤ p.2 := hB.z_order.1.trans hp2.1.le
  obtain ⟨e1, e2⟩ := mat_field_mode M m hm n P p.1 p.2 hr hz a b
  rw [e1, e2]
  simp only [cellCoef_interior M hM K₀ _ p hp1 hp2, interiorPoly, and_self]

def rHatPoly (K : CellBox) (p : ℝ × ℝ) : ℂ := if K.r₁ = 0 then 1 else (p.1 : ℂ)

theorem rHatPoly_mem (K : CellBox) : rHatPoly K ∈ polyFn 1 0 := by
  unfold rHatPoly
  by_cases h : K.r₁ = 0
  · simpa [h] using (poly_const' (d := 1) (d' := 0) 1)
  · simpa [h] using poly_fst'

theorem rHat_interior (K : CellBox) (hK : IsCellBox K) (p : ℝ × ℝ) (hp1 : p.1 ∈ Set.Ioo K.r₁ K.r₂) :
    ((CellScalars.rHat K p : ℝ) : ℂ) = rHatPoly K p := by
  have hr : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hp1.1
  unfold CellScalars.rHat CellBox.lineWeight rHatPoly
  by_cases h : K.r₁ = 0
  · rw [if_pos h, if_pos h, div_self hr.ne', Complex.ofReal_one]
  · rw [if_neg h, if_neg h, div_one]


theorem poly_sub' {d d' : ℕ} {f g : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') (hg : g ∈ polyFn d d') :
    (fun p => f p - g p) ∈ polyFn d d' := by
  refine poly_congr' (poly_add' hf (poly_smul' (-1) hg)) ?_
  intro p
  ring

theorem cross_poly {d e : ℕ} (u v : Fin 3 → ℝ × ℝ → ℂ) (hu : ∀ j, u j ∈ polyFn d d) (hv : ∀ j, v j ∈ polyFn e e)
    (i : Fin 3) : (fun p => crossC (fun j => u j p) (fun j => v j p) i) ∈ polyFn (d + e) (d + e) := by
  fin_cases i
  · exact poly_sub' (poly_mul' (hu 1) (hv 2)) (poly_mul' (hu 2) (hv 1))
  · exact poly_sub' (poly_mul' (hu 2) (hv 0)) (poly_mul' (hu 0) (hv 2))
  · exact poly_sub' (poly_mul' (hu 0) (hv 1)) (poly_mul' (hu 1) (hv 0))

theorem curlAdj_poly {d : ℕ} (u : Fin 3 → ℝ × ℝ → ℂ) (hu : ∀ j, u j ∈ polyFn d d) (i l : Fin 3) :
    (fun p => curlAdj (fun j => u j p) i l) ∈ polyFn d d := by
  unfold curlAdj
  exact poly_sum' _ (fun j _ => poly_smul' _ (hu j))

theorem turn_poly {d : ℕ} (k : ℝ) (u : Fin 3 → ℝ × ℝ → ℂ) (hu : ∀ j, u j ∈ polyFn d d) (i : Fin 3) :
    (fun p => turnAdjInv k (fun j => u j p) i) ∈ polyFn d d := by
  fin_cases i
  · exact poly_smul' _ (poly_sub' (poly_smul' _ (hu 0)) (hu 1))
  · exact poly_smul' _ (poly_sub' (hu 0) (poly_smul' _ (hu 1)))
  · refine poly_congr' (poly_smul' (1 / (-(k : ℂ) * Complex.I)) (hu 2)) ?_
    intro p
    simp [turnAdjInv, div_eq_mul_inv, mul_comm]

theorem mulFst_poly {d d' : ℕ} {f : ℝ × ℝ → ℂ} (hf : f ∈ polyFn d d') : (fun p => (p.1 : ℂ) * f p) ∈ polyFn (1 + d) (0 + d') :=
  poly_mul' poly_fst' hf

def rowPoly {M : CellMesh} {N : ℕ} (RD : RowData M N) (K₀ : Fin M.cellCount) (a : Fin N) (n : ℤ) (c' : Fin 3)
    (p : ℝ × ℝ) : ℂ :=
  (1 / 2 : ℂ) * ∑ b : Fin N,
    ((if n = ((RD.harmonic b : ℕ) : ℤ) then ((RD.mix a b : ℝ) : ℂ) *
        (if RD.cell b = K₀ then evalPoly (RD.profile b c') p.1 p.2 else 0) else 0) +
      (if n = -((RD.harmonic b : ℕ) : ℤ) then (starRingEnd ℂ) (((RD.mix a b : ℝ) : ℂ) *
        (if RD.cell b = K₀ then evalPoly (RD.profile b c') p.1 p.2 else 0)) else 0))

theorem rowPoly_mem {M : CellMesh} {N : ℕ} (RD : RowData M N) (K₀ : Fin M.cellCount) (a : Fin N) (n : ℤ)
    (c' : Fin 3) : rowPoly RD K₀ a n c' ∈ polyFn RD.degree RD.degree := by
  unfold rowPoly
  refine poly_smul' _ (poly_sum' _ (fun b _ => poly_add' ?_ ?_))
  · exact poly_ite' _ (poly_smul' _ (poly_ite' _ (poly_eval' _)))
  · exact poly_ite' _ (poly_conj' (poly_smul' _ (poly_ite' _ (poly_eval' _))))

theorem row_interior (M : CellMesh) (hM : IsCellMesh M) {N : ℕ} (RD : RowData M N) (K₀ : Fin M.cellCount)
    (m : ℕ) (hm : 0 < m) (a : Fin N) (n : ℤ) (c' : Fin 3) (p : ℝ × ℝ)
    (hp1 : p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂) (hp2 : p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂) :
    modeVec m n (RD.rowField m a) p.1 p.2 c' = rowPoly RD K₀ a n c' p := by
  classical
  have hB := hM.boxes K₀
  have hr : 0 < p.1 := lt_of_le_of_lt hB.r_order.1 hp1.1
  have hz : 0 ≤ p.2 := hB.z_order.1.trans hp2.1.le
  refine (vec_mode Finset.univ m hm n _ p.1 p.2 c' (fun b => ((RD.harmonic b : ℕ) : ℤ))
    (fun b => ((RD.mix a b : ℝ) : ℂ) * (if RD.cell b = K₀ then evalPoly (RD.profile b c') p.1 p.2 else 0))
    (fun θ => ?_)).trans rfl
  obtain ⟨h1, -, h3⟩ := cyl_coords p.1 θ p.2 hr.le hz
  unfold RowData.rowField
  rw [frameVec_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [frameVec_eq, real_inner_smul_left, ← frameVec_eq]
  unfold RowData.testField
  rw [Set.indicator_apply]
  by_cases hb : RD.cell b = K₀
  · rw [if_pos ((interior_mem M hM K₀ (RD.cell b) p hp1 hp2 θ).1.2 hb), if_pos hb]
    rw [cart_angle p.1 θ p.2 hr, frameVec_cart, (signs_up p.1 θ p.2 hr.le hz c').1, h1, h3,
      exp_angle p.1 θ p.2 hr]
    rw [mul_assoc, Complex.re_ofReal_mul, one_mul]
  · rw [if_neg (fun hh => hb ((interior_mem M hM K₀ (RD.cell b) p hp1 hp2 θ).1.1 hh)), if_neg hb]
    simp [frameVec_eq]


theorem angle_meas' : Measurable cylAngle := by
  unfold cylAngle
  exact Complex.measurable_arg.comp (by fun_prop)

theorem radius_cont' : Continuous cylRadius := by
  unfold cylRadius
  fun_prop

theorem height_cont' : Continuous cylHeight := by
  unfold cylHeight
  fun_prop

theorem evalPoly_cont' {d : ℕ} (P : CellPoly d) : Continuous (fun x : ℝ × ℝ => evalPoly P x.1 x.2) := by
  unfold evalPoly
  fun_prop

theorem harm_meas' (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) : Measurable (harmonicValue m P) := by
  unfold harmonicValue
  refine Complex.measurable_re.comp (Finset.measurable_sum _ (fun β _ => ?_))
  refine (measurable_const.mul ?_).mul ?_
  · exact ((evalPoly_cont' (P β)).comp (radius_cont'.prodMk (continuous_abs.comp height_cont'))).measurable
  · have hc : Continuous (fun t : ℝ => Complex.exp (((azimuth m ((β : ℕ) : ℤ) * t : ℝ) : ℂ) * Complex.I)) := by fun_prop
    exact hc.measurable.comp angle_meas'

theorem sign_meas' (a : Fin 3) : Measurable (fun y => vectorSign y a) ∧ Measurable (fun y => pseudoSign y a) := by
  have hs : MeasurableSet {y : Space | cylHeight y < 0} := measurableSet_lt height_cont'.measurable measurable_const
  have hv : Measurable (fun y => vectorSign y a) := by
    unfold vectorSign
    exact Measurable.ite (hs.inter (MeasurableSet.const _)) measurable_const measurable_const
  refine ⟨hv, ?_⟩
  unfold pseudoSign
  exact Measurable.ite hs hv.neg measurable_const

theorem single_cont' (i : Fin 3) : Continuous (fun x : ℝ => (EuclideanSpace.single i x : Space)) := by
  have e : (fun x : ℝ => (EuclideanSpace.single i x : Space)) = fun x => x • (EuclideanSpace.single i (1 : ℝ) : Space) := by
    funext x
    ext j
    simp
  rw [e]
  exact continuous_id.smul continuous_const

theorem frame_cont' (a : Fin 3) : Continuous (fun θ : ℝ => frameUnit θ a) := by
  fin_cases a
  · exact ((single_cont' 0).comp Real.continuous_cos).add ((single_cont' 1).comp Real.continuous_sin)
  · exact ((single_cont' 0).comp Real.continuous_sin.neg).add ((single_cont' 1).comp Real.continuous_cos)
  · exact continuous_const


theorem entry_meas' (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (a b : Fin 3) :
    Measurable (fun y => vectorSign y a * vectorSign y b * harmonicValue m (fun β => P β a b) y) ∧
    Measurable (fun y => pseudoSign y a * vectorSign y b * harmonicValue m (fun β => P β a b) y) :=
  ⟨((sign_meas' a).1.mul (sign_meas' b).1).mul (harm_meas' m _),
    ((sign_meas' a).2.mul (sign_meas' b).1).mul (harm_meas' m _)⟩

theorem cartOp_meas' {μ : Measure Space} (g : Space → ℝ) (M : Space → Fin 3 → Fin 3 → ℝ) (hg : Measurable g)
    (hM : ∀ a b, Measurable (fun y => M y a b)) :
    AEStronglyMeasurable (fun y => cartOpOfFrame (g y) (M y)) μ := by
  unfold cartOpOfFrame
  refine Finset.aestronglyMeasurable_fun_sum _ (fun a _ => Finset.aestronglyMeasurable_fun_sum _ (fun b _ => ?_))
  refine (hM a b).aestronglyMeasurable.smul ?_
  have h1 : Continuous (fun θ : ℝ => innerSL ℝ (frameUnit θ b)) := (innerSL ℝ).continuous.comp (frame_cont' b)
  have hS : Continuous (fun θ : ℝ => (innerSL ℝ (frameUnit θ b)).smulRight (frameUnit θ a)) :=
    (ContinuousLinearMap.smulRightL ℝ Space Space).continuous₂.comp (h1.prodMk (frame_cont' a))
  exact hS.comp_aestronglyMeasurable hg.aestronglyMeasurable

theorem tensor_meas' {μ : Measure Space} (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) :
    AEStronglyMeasurable (tensorOf m P) μ ∧ AEStronglyMeasurable (pseudoTensorOf m P) μ :=
  ⟨cartOp_meas' cylAngle _ angle_meas' (fun a b => (entry_meas' m P a b).1),
    cartOp_meas' cylAngle _ angle_meas' (fun a b => (entry_meas' m P a b).2)⟩

theorem solid_meas' (K : CellBox) : MeasurableSet K.solid := by
  have h1 := radius_cont'.measurable
  have h2 : Measurable (fun y => |cylHeight y|) := (continuous_abs.comp height_cont').measurable
  unfold CellBox.solid
  simp only [Set.setOf_and]
  exact (measurableSet_le measurable_const h1).inter ((measurableSet_le h1 measurable_const).inter
    ((measurableSet_le measurable_const h2).inter (measurableSet_le h2 measurable_const)))

theorem piece_meas' (M : CellMesh) (K : Fin M.cellCount) : MeasurableSet (M.piece K) := by
  unfold CellMesh.piece
  exact (solid_meas' _).diff (MeasurableSet.biUnion (Set.to_countable _) (fun K' _ => solid_meas' _))

theorem piecewise_meas' {μ : Measure Space} (M : CellMesh) (f : Fin M.cellCount → Space → (Space →L[ℝ] Space))
    (hf : ∀ K, AEStronglyMeasurable (f K) μ) : AEStronglyMeasurable (M.piecewise f) μ := by
  unfold CellMesh.piecewise
  exact Finset.aestronglyMeasurable_fun_sum _ (fun K _ => (hf K).indicator (piece_meas' M K))


theorem frame_norm' (θ : ℝ) (a : Fin 3) : ‖frameUnit θ a‖ = 1 := by
  have h := frame_orth θ a a
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
  have h0 := norm_nonneg (frameUnit θ a)
  nlinarith

theorem cartOp_norm' (θ : ℝ) (A : Fin 3 → Fin 3 → ℝ) : ‖cartOpOfFrame θ A‖ ≤ ∑ a, ∑ b, |A a b| := by
  unfold cartOpOfFrame
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum (fun b _ => ?_))))
  rw [norm_smul, ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, frame_norm', frame_norm',
    Real.norm_eq_abs]
  simp

theorem harm_bound' (K : CellBox) (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (hK : IsCellBox K) :
    ∃ C : ℝ, ∀ p ∈ K.rect, ∀ θ : ℝ, |harmonicValue m P (cylPoint p.1 θ p.2)| ≤ C := by
  have hc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hb : ∀ β : Fin (J + 1), ∃ C : ℝ, ∀ p ∈ K.rect, ‖evalPoly (P β) p.1 p.2‖ ≤ C := fun β =>
    hc.exists_bound_of_continuousOn (evalPoly_cont' (P β)).continuousOn
  choose C hC using hb
  refine ⟨∑ β, 2 * C β, fun p hp θ => ?_⟩
  obtain ⟨h1, -, h3⟩ := cyl_coords p.1 θ p.2 (hK.r_order.1.trans hp.1.1) (hK.z_order.1.trans hp.2.1)
  unfold harmonicValue
  rw [h1, h3]
  refine (Complex.abs_re_le_norm _).trans ((norm_sum_le _ _).trans (Finset.sum_le_sum (fun β _ => ?_)))
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hw : |(if (β : ℕ) = 0 then (1 : ℝ) else 2)| ≤ 2 := by split_ifs <;> norm_num
  have := hC β p hp
  have h0 : 0 ≤ ‖evalPoly (P β) p.1 p.2‖ := norm_nonneg _
  nlinarith [abs_nonneg (if (β : ℕ) = 0 then (1 : ℝ) else 2)]

theorem tensor_bound' (K : CellBox) (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (hK : IsCellBox K) :
    ∃ C : ℝ, ∀ p ∈ K.rect, ∀ θ : ℝ, ‖tensorOf m P (cylPoint p.1 θ p.2)‖ ≤ C ∧
      ‖pseudoTensorOf m P (cylPoint p.1 θ p.2)‖ ≤ C := by
  have hb : ∀ a b : Fin 3, ∃ C : ℝ, ∀ p ∈ K.rect, ∀ θ : ℝ,
      |harmonicValue m (fun β => P β a b) (cylPoint p.1 θ p.2)| ≤ C := fun a b => harm_bound' K m _ hK
  choose C hC using hb
  have hs : ∀ y a, |vectorSign y a| = 1 ∧ |pseudoSign y a| = 1 := by
    intro y a
    unfold pseudoSign vectorSign
    split_ifs <;> simp
  refine ⟨∑ a, ∑ b, C a b, fun p hp θ => ⟨?_, ?_⟩⟩
  · unfold tensorOf
    refine (cartOp_norm' _ _).trans (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_)))
    rw [abs_mul, abs_mul, (hs _ a).1, (hs _ b).1, one_mul, one_mul]
    exact hC a b p hp θ
  · unfold pseudoTensorOf
    refine (cartOp_norm' _ _).trans (Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => ?_)))
    rw [abs_mul, abs_mul, (hs _ a).2, (hs _ b).1, one_mul, one_mul]
    exact hC a b p hp θ

theorem piecewise_bound' (M : CellMesh) (f : Fin M.cellCount → Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖M.piecewise f y‖ ≤ ∑ K, ‖f K y‖ := by
  unfold CellMesh.piecewise
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun K _ => norm_indicator_le_norm_self _ _))

theorem model_bound' (M : CellMesh) (hM : IsCellMesh M) (K₀ : Fin M.cellCount) (m : ℕ) {d J : ℕ}
    (P Q : Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) :
    ∃ C : ℝ, ∀ p ∈ (M.box K₀).rect, ∀ θ : ℝ, ‖M.piecewise (fun K => tensorOf m (P K)) (cylPoint p.1 θ p.2)‖ ≤ C ∧
      ‖M.piecewise (fun K => pseudoTensorOf m (Q K)) (cylPoint p.1 θ p.2)‖ ≤ C := by
  have hP : ∀ K, ∃ C : ℝ, ∀ p ∈ (M.box K₀).rect, ∀ θ : ℝ, ‖tensorOf m (P K) (cylPoint p.1 θ p.2)‖ ≤ C ∧
      ‖pseudoTensorOf m (Q K) (cylPoint p.1 θ p.2)‖ ≤ C := by
    intro K
    obtain ⟨C1, h1⟩ := tensor_bound' (M.box K₀) m (P K) (hM.boxes K₀)
    obtain ⟨C2, h2⟩ := tensor_bound' (M.box K₀) m (Q K) (hM.boxes K₀)
    exact ⟨max C1 C2, fun p hp θ => ⟨(h1 p hp θ).1.trans (le_max_left _ _), (h2 p hp θ).2.trans (le_max_right _ _)⟩⟩
  choose C hC using hP
  exact ⟨∑ K, C K, fun p hp θ => ⟨(piecewise_bound' _ _ _).trans (Finset.sum_le_sum (fun K _ => (hC K p hp θ).1)),
    (piecewise_bound' _ _ _).trans (Finset.sum_le_sum (fun K _ => (hC K p hp θ).2))⟩⟩

end ModeCoverInternal

open SteadyCert CellAnalysis ModeCoverInternal

theorem sum_zero_or {C J : ℕ} (n : ℤ) (f : Fin C × Fin (J + 1) → ℂ)
    (hβ : ∀ q : Fin C × Fin (J + 1), (n ≠ ((q.2 : ℕ) : ℤ) ∧ n ≠ -((q.2 : ℕ) : ℤ)) ∨ f q = 0) :
    (1 / 2 : ℂ) * ∑ q : Fin C × Fin (J + 1), ((if n = ((q.2 : ℕ) : ℤ) then f q else 0) +
        (if n = -((q.2 : ℕ) : ℤ) then (starRingEnd ℂ) (f q) else 0)) = 0 := by
  rw [Finset.sum_eq_zero (fun q _ => by rcases hβ q with h | h <;> simp [h]), mul_zero]

theorem classCover_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hD : IsModelData D) (hI : IsModelInstance c M D) (hm : 0 < c.order) (K₀ : Fin M.cellCount)
    (K : CellBox) (hbox : K = M.box K₀)
    (hK : K.solid ⊆ c.cellRegion) (hKb : IsCellBox K) (S : CellScalars)
    (Cl : CellClasses)
    (hcov : ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band, ∀ β : Fin (D.harmonicCount + 1),
      (β : ℕ) ≤ D.harmonicsOf K₀ → (n - n' = (β : ℤ) ∨ n - n' = -(β : ℤ)) → ∃ i, n - n' ∈ Cl.modes i) :
    ∀ n ∈ S.resolved, ∀ n' ∉ S.resolved ∪ S.band,
      (∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity p.1 p.2 ≠ 0 ∨
        modeVec c.order (n - n') c.modelCurl p.1 p.2 ≠ 0 ∨
        modeMat c.order (n - n') c.modelStrain p.1 p.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 ≠ 0)) →
      ∃ i, n - n' ∈ Cl.modes i := by
  subst hbox
  intro n hn n' hn' ⟨p, hp, hp1, hne⟩
  by_contra hcl
  have hβ : ∀ β : Fin (D.harmonicCount + 1), (β : ℕ) ≤ D.harmonicsOf K₀ →
      n - n' ≠ ((β : ℕ) : ℤ) ∧ n - n' ≠ -((β : ℕ) : ℤ) := fun β hb =>
    ⟨fun h => hcl (hcov n hn n' hn' β hb (Or.inl h)), fun h => hcl (hcov n hn n' hn' β hb (Or.inr h))⟩
  have hpc : p ∈ (M.box K₀).rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have hr : 0 < p.1 := lt_of_le_of_ne (hKb.r_order.1.trans hpc.1.1) (Ne.symm hp1)
  have hz : 0 ≤ p.2 := hKb.z_order.1.trans hpc.2.1
  have hout : ∀ K', K' ≠ K₀ → cylPoint p.1 0 p.2 ∉ M.piece K' := fun K' hK' hmem => by
    have hs : cylPoint p.1 0 p.2 ∈ (M.box K').solid := by
      unfold CellMesh.piece at hmem
      exact hmem.1
    obtain ⟨h1, -, h3⟩ := cyl_coords p.1 0 p.2 hr.le hz
    simp only [CellBox.solid, Set.mem_ofPred_eq] at hs
    rw [h1, h3] at hs
    obtain ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ := hp
    rcases hM.interiors_disjoint K' K₀ hK' with h | h | h | h <;> linarith [hs.1, hs.2.1, hs.2.2.1, hs.2.2.2]
  have hz0 : ∀ E : Fin M.cellCount → Fin (D.harmonicCount + 1) → CellPoly D.degree,
      (∀ β : Fin (D.harmonicCount + 1), D.harmonicsOf K₀ < (β : ℕ) → ∀ i j, E K₀ β i j = 0) →
      ∀ q, (n - n' ≠ ((q.2 : ℕ) : ℤ) ∧ n - n' ≠ -((q.2 : ℕ) : ℤ)) ∨ cellCoef M E p.1 p.2 q = 0 := by
    intro E hE q
    by_cases hq : q.1 = K₀
    · by_cases hb : (q.2 : ℕ) ≤ D.harmonicsOf K₀
      · exact Or.inl (hβ q.2 hb)
      · right
        have h0 := hE q.2 (by omega)
        unfold cellCoef
        rw [hq]
        simp [evalPoly, h0]
    · right
      unfold cellCoef
      rw [if_neg (hout q.1 hq)]
  have hreg : ∀ θ : ℝ, cylPoint p.1 θ p.2 ∈ M.region := fun θ => by
    rw [← hI.region_eq]
    exact hK (cyl_mem_solid (M.box K₀) hKb p hpc θ)
  have h1 : modeVec c.order (n - n') c.modelVelocity p.1 p.2 = 0 := by
    funext a
    rw [hI.velocity_eq]
    exact ((vec_field_mode M c.order hm (n - n') D.velocity p.1 p.2 hr hz a).1).trans
      (sum_zero_or _ _ (hz0 _ fun β hb i j => (hD.zero_above K₀ β hb).1 a i j))
  have h2 : modeVec c.order (n - n') c.modelCurl p.1 p.2 = 0 := by
    funext a
    rw [hI.curl_eq]
    exact ((vec_field_mode M c.order hm (n - n') D.curl p.1 p.2 hr hz a).2).trans
      (sum_zero_or _ _ (hz0 _ fun β hb i j => (hD.zero_above K₀ β hb).2.1 a i j))
  have h3 : modeMat c.order (n - n') c.modelStrain p.1 p.2 = 0 := by
    funext a b
    rw [hI.strain_eq, modeMat_congr _ _ _ (M.piecewise (fun K => tensorOf c.order (D.strain K))) _ _
      (fun θ => strain_in M D c.order c.centreGrad _ (hreg θ))]
    exact ((mat_field_mode M c.order hm (n - n') D.strain p.1 p.2 hr hz a b).1).trans
      (sum_zero_or _ _ (hz0 _ fun β hb i j => (hD.zero_above K₀ β hb).2.2.1 a b i j))
  have h4 : modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 = 0 := by
    funext a b
    rw [hI.curlGrad_eq, modeMat_congr _ _ _ (M.piecewise (fun K => pseudoTensorOf c.order (D.curlGrad K))) _ _
      (fun θ => curlGrad_in M D c.order c.centreSecond _ (hreg θ))]
    exact ((mat_field_mode M c.order hm (n - n') D.curlGrad p.1 p.2 hr hz a b).2).trans
      (sum_zero_or _ _ (hz0 _ fun β hb i j => (hD.zero_above K₀ β hb).2.2.2 a b i j))
  rcases hne with h | h | h | h
  · exact h h1
  · exact h h2
  · exact h h3
  · exact h h4


theorem actuatorPoly_interior {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hI : IsModelInstance c M D) (hm : 0 < c.order) (K₀ : Fin M.cellCount)
    (S : CellScalars) (R : CellRows N slots k) (hdeg : D.columnDegree + 1 ≤ S.degNear) :
    (∀ i : Fin k, ∀ n ∈ R.yModes, ∀ a b : Fin 3, ∃ P ∈ polyFn S.degNear S.degNear,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b = P p) ∧
    (∀ i : Fin k, ∀ n ∈ R.yModes, ∀ a b : Fin 3, ∃ P ∈ polyFn S.degNear S.degNear,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        ((CellScalars.rHat (M.box K₀) p : ℝ) : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b = P p) := by
  have hmem : ∀ (E : Fin M.cellCount → Fin (D.harmonicCount + 1) → CellPoly D.columnDegree) (n : ℤ),
      (fun p => rHatPoly (M.box K₀) p * interiorPoly M K₀ E n p) ∈ polyFn S.degNear S.degNear := fun E n =>
    poly_mono' (by omega) (by omega) (poly_mul' (rHatPoly_mem (M.box K₀)) (interiorPoly_mem M K₀ E n))
  refine ⟨fun i n _ a b => ?_, fun i n _ a b => ?_⟩
  · refine ⟨_, hmem (fun K β => D.actuatorGrad i K β a b) n, fun p hp1 hp2 => ?_⟩
    rw [hI.actuatorGrad_eq i, rHat_interior _ (hM.boxes K₀) p hp1]
    exact congrArg _ (mat_interior M hM K₀ c.order hm n (D.actuatorGrad i) a b p hp1 hp2).1
  · refine ⟨_, hmem (fun K β => D.pinField i K β a b) n, fun p hp1 hp2 => ?_⟩
    rw [hI.pinField_eq i, rHat_interior _ (hM.boxes K₀) p hp1]
    exact congrArg _ (mat_interior M hM K₀ c.order hm n (D.pinField i) a b p hp1 hp2).1

theorem rowPolynomial_interior {k N slots : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (RD : RowData M N) (hM : IsCellMesh M) (hI : IsModelInstance c M D) (hR : IsRowData RD c.order c.rowMax)
    (K₀ : Fin M.cellCount) (R : CellRows N slots k) (hRI : IsRowsInstance c M RD K₀ R) (hm : 0 < c.order)
    (S : CellScalars) (E : ℕ) (hdeg : RD.degree + D.degree + 2 ≤ E) :
    (∀ a ∈ R.rowSet, ∀ n' ∈ S.resolved ∪ S.band, ∀ i q : Fin 3, ∃ P ∈ polyFn E E,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        CellScalars.rowCouplingFolded c (M.box K₀) S R a n' p i q = P p) ∧
    (∀ a ∈ R.rowSet, ∀ n' ∈ S.resolved, ∀ i : Fin 3, ∃ P ∈ polyFn E E,
      ∀ p : ℝ × ℝ, p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
        CellScalars.rowCouplingVelocity c (M.box K₀) R a n' p i = P p) := by
  have hB := hM.boxes K₀
  have hU : ∀ a n (p : ℝ × ℝ), p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      CellScalars.rowMode c a n p = fun j => rowPoly RD K₀ a n j p := by
    intro a n p hp1 hp2
    funext j
    unfold CellScalars.rowMode
    rw [hRI.row_eq]
    exact row_interior M hM RD K₀ c.order hm a n j p hp1 hp2
  have hV : ∀ n n' (p : ℝ × ℝ), p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      modeVec c.order (n - n') c.modelVelocity p.1 p.2 =
        fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p := by
    intro n n' p hp1 hp2
    funext j
    rw [hI.velocity_eq]
    exact (vec_interior M hM K₀ c.order hm (n - n') D.velocity j p hp1 hp2).1
  have hW : ∀ n n' (p : ℝ × ℝ), p.1 ∈ Set.Ioo (M.box K₀).r₁ (M.box K₀).r₂ → p.2 ∈ Set.Ioo (M.box K₀).z₁ (M.box K₀).z₂ →
      modeVec c.order (n - n') c.modelCurl p.1 p.2 =
        fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p := by
    intro n n' p hp1 hp2
    funext j
    rw [hI.curl_eq]
    exact (vec_interior M hM K₀ c.order hm (n - n') D.curl j p hp1 hp2).2
  have hYs : ∀ a n' (i l : Fin 3), (fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
      curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
        (fun j => rowPoly RD K₀ a n j p)) i l) ∈ polyFn (1 + (D.degree + RD.degree)) (0 + (D.degree + RD.degree)) := by
    intro a n' i l
    refine poly_mul' (rHatPoly_mem _) (poly_sum' _ (fun n _ => ?_))
    exact curlAdj_poly (fun i' p => crossC (fun j => (starRingEnd ℂ) (interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
        (fun j => rowPoly RD K₀ a n j p) i')
      (fun i' => cross_poly _ _ (fun j => poly_conj' (interiorPoly_mem M K₀ _ _)) (fun j => rowPoly_mem RD K₀ a n j) i') i l
  have hYv : ∀ a n' (i : Fin 3), (fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
      crossC (fun j => rowPoly RD K₀ a n j p)
        (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i) ∈
        polyFn (1 + RD.degree + D.degree) (1 + RD.degree + D.degree) := by
    intro a n' i
    refine poly_mono' (d := 1 + (RD.degree + D.degree)) (d' := 0 + (RD.degree + D.degree)) (by omega) (by omega)
      (poly_mul' (rHatPoly_mem _) (poly_sum' _ (fun n _ => ?_)))
    exact cross_poly (fun j p => rowPoly RD K₀ a n j p)
      (fun j p => (starRingEnd ℂ) (interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p))
      (fun j => rowPoly_mem RD K₀ a n j) (fun j => poly_conj' (interiorPoly_mem M K₀ _ _)) i
  refine ⟨fun a _ n' _ i q => ?_, fun a _ n' _ i => ?_⟩
  · refine ⟨fun p => if n' ∈ S.resolved then
        rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
          curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
            (fun j => rowPoly RD K₀ a n j p)) i q
      else (rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes,
          curlAdj (crossC (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.velocity K β j) (n - n') p))
            (fun j => rowPoly RD K₀ a n j p)) i q +
        if q = 1 then (p.1 : ℂ) * turnAdjInv (azimuth c.order n') (fun i' => rHatPoly (M.box K₀) p *
          ∑ n ∈ R.rowModes, crossC (fun j => rowPoly RD K₀ a n j p)
            (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i') i else 0), ?_, ?_⟩
    · by_cases hn : n' ∈ S.resolved
      · simp only [hn, if_true]
        exact poly_mono' (by omega) (by omega) (hYs a n' i q)
      · simp only [hn, if_false]
        refine poly_add' (poly_mono' (by omega) (by omega) (hYs a n' i q)) ?_
        by_cases hq : q = 1
        · simp only [hq, if_true]
          exact poly_mono' (d := 1 + (1 + RD.degree + D.degree)) (d' := 0 + (1 + RD.degree + D.degree)) (by omega) (by omega)
            (mulFst_poly (turn_poly _ _ (fun i' => hYv a n' i') i))
        · simp only [hq, if_false]
          exact poly_zero'
    · intro p hp1 hp2
      unfold CellScalars.rowCouplingFolded CellScalars.rowCouplingStrain CellScalars.rowCouplingVelocity foldVelocity
      simp only [hU a _ p hp1 hp2, hV _ n' p hp1 hp2, hW _ n' p hp1 hp2, rHat_interior _ hB p hp1]
      by_cases hn : n' ∈ S.resolved <;> by_cases hq : q = 1 <;> simp only [hn, hq, if_true, if_false, add_zero]
  · refine ⟨fun p => rHatPoly (M.box K₀) p * ∑ n ∈ R.rowModes, crossC (fun j => rowPoly RD K₀ a n j p)
        (conjVec3 (fun j => interiorPoly M K₀ (fun K β => D.curl K β j) (n - n') p)) i,
      poly_mono' (by omega) (by omega) (hYv a n' i), fun p hp1 hp2 => ?_⟩
    unfold CellScalars.rowCouplingVelocity
    simp only [hU a _ p hp1 hp2, hW _ n' p hp1 hp2, rHat_interior _ hB p hp1]

open CellAnalysis.MeshFarRegularInternal in
theorem tailRegular_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hD : IsModelData D) (hI : IsModelInstance c M D) (hC : IsCentreRegular c)
    (K₀ : Fin M.cellCount) (S : CellScalars) (F : FarMajorantData) :
    IsTailRegular (M.box K₀) (CellScalars.strainGroupFamily c (M.box K₀) S F) ∧
      IsTailRegular (M.box K₀) (CellScalars.velocityGroupFamily c (M.box K₀) S F) ∧
      IsTailRegular (M.box K₀) (CellScalars.bandGroupFamily c (M.box K₀) S F) := by
  set K := M.box K₀ with hKdef
  have hK : IsCellBox K := hM.boxes K₀
  set PS := M.piecewise (fun K' => tensorOf c.order (D.strain K')) with hPS
  set PG := M.piecewise (fun K' => pseudoTensorOf c.order (D.curlGrad K')) with hPG
  have hin : ∀ p ∈ K.rect, ∀ θ : ℝ, cylPoint p.1 θ p.2 ∈ M.region := fun p hp θ =>
    Set.mem_iUnion.2 ⟨K₀, cyl_mem_solid K hK p hp θ⟩
  have eS : ∀ p ∈ K.rect, ∀ θ : ℝ, c.modelStrain (cylPoint p.1 θ p.2) = PS (cylPoint p.1 θ p.2) := fun p hp θ => by
    rw [hI.strain_eq]
    exact strain_in M D c.order c.centreGrad _ (hin p hp θ)
  have eG : ∀ p ∈ K.rect, ∀ θ : ℝ, c.modelCurlGrad (cylPoint p.1 θ p.2) = PG (cylPoint p.1 θ p.2) := fun p hp θ => by
    rw [hI.curlGrad_eq]
    exact curlGrad_in M D c.order c.centreSecond _ (hin p hp θ)
  have hPSm : AEStronglyMeasurable PS volume :=
    piecewise_meas' M _ (fun K' => (tensor_meas' c.order (D.strain K')).1)
  have hPGm : AEStronglyMeasurable PG volume :=
    piecewise_meas' M _ (fun K' => (tensor_meas' c.order (D.curlGrad K')).2)
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hae : ∀ᵐ q ∂((volume.restrict K.rect).prod (volume : Measure ℝ)), q.1 ∈ K.rect := by
    have e : (volume.restrict K.rect).prod (volume : Measure ℝ) =
        ((volume : Measure (ℝ × ℝ)).prod (volume : Measure ℝ)).restrict (K.rect ×ˢ Set.univ) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    rw [e]
    filter_upwards [ae_restrict_mem (hrect.prod MeasurableSet.univ)] with q hq using hq.1
  have hSm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => CellScalars.strainAt c q.1 q.2)
      ((volume.restrict K.rect).prod volume) := by
    refine (mat_meas _ (fun a b => entry_meas cylinderComp K PS hPSm a b)).congr ?_
    filter_upwards [hae] with q hq
    funext a b
    simp only [CellScalars.strainAt]
    rw [eS q.1 hq q.2]
  have hGm : AEStronglyMeasurable (fun q : (ℝ × ℝ) × ℝ => CellScalars.curlGradAt c q.1 q.2)
      ((volume.restrict K.rect).prod volume) := by
    refine (mat_meas _ (fun a b => entry_meas cylinderComp K PG hPGm a b)).congr ?_
    filter_upwards [hae] with q hq
    funext a b
    simp only [CellScalars.curlGradAt]
    rw [eG q.1 hq q.2]
  obtain ⟨Cm, hCm⟩ := model_bound' M hM K₀ c.order D.strain D.curlGrad
  have hSb : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖CellScalars.strainAt c p θ‖ ≤ 4 * Cm := fun p hp θ => by
    unfold CellScalars.strainAt
    rw [eS p hp θ]
    exact mat_bound _ Cm (hCm p hp θ).1 θ
  have hGb : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖CellScalars.curlGradAt c p θ‖ ≤ 4 * Cm := fun p hp θ => by
    unfold CellScalars.curlGradAt
    rw [eG p hp θ]
    exact mat_bound _ Cm (hCm p hp θ).2 θ
  have hρ1 : Measurable (fun q : (ℝ × ℝ) × ℝ => ((CellScalars.rHat K q.1 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((rHat_measurable K).comp measurable_fst)
  have hρ2 : Measurable (fun q : (ℝ × ℝ) × ℝ => ((q.1.1 * CellScalars.rHat K q.1 : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp ((measurable_fst.comp measurable_fst).mul ((rHat_measurable K).comp measurable_fst))
  have hX1 : ∀ p ∈ K.rect, ∀ θ : ℝ, ‖(((CellScalars.rHat K p : ℝ) : ℂ), CellScalars.strainAt c p θ,
      CellScalars.curlGradAt c p θ)‖ ≤ max (max 1 K.r₂) (4 * Cm) := fun p hp θ => by
    refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact (rHat_bound K hK p hp).trans (le_max_left _ _)
    · exact (hSb p hp θ).trans (le_max_right _ _)
    · exact (hGb p hp θ).trans (le_max_right _ _)
  refine ⟨?_, ?_, ?_⟩
  · refine regular_of K _ (fun q => (((CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ1.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) _ (fun p hp θ => hX1 p hp θ)
      (fun i o c' x => x.1 * (if i = 0 then -curlAdj (matVec x.2.1 (CellScalars.unitVec3 c')) o.1 o.2
        else (1 / 2 : ℂ) * couplingMap x.2.2 (CellScalars.unitVec3 c') o.1 o.2)) ?_ (fun i o c' p θ => rfl)
    intro i o c'
    by_cases hi : i = 0
    · simp only [hi, if_true]
      unfold curlAdj matVec
      fun_prop
    · simp only [hi, if_false]
      unfold couplingMap bracketMat
      fun_prop
  · refine regular_of K _ (fun q => (((CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ1.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) _ (fun p hp θ => hX1 p hp θ)
      (fun _ o e x => x.1 * waveActionVelocity x.2.2 (CellScalars.unitMat e) o) ?_ (fun i o e p θ => rfl)
    intro i o e
    unfold waveActionVelocity couplingAdj
    fun_prop
  · refine regular_of K _ (fun q => (((q.1.1 * CellScalars.rHat K q.1 : ℝ) : ℂ), CellScalars.strainAt c q.1 q.2,
      CellScalars.curlGradAt c q.1 q.2))
      (hρ2.aestronglyMeasurable.prodMk (hSm.prodMk hGm)) (max (K.r₂ * max 1 K.r₂) (4 * Cm)) ?_
      (fun _ o e x => x.1 * waveActionVelocity x.2.2 (CellScalars.unitMat e) o) ?_ (fun i o e p θ => rfl)
    · intro p hp θ
      refine norm_prod_le_iff.mpr ⟨?_, norm_prod_le_iff.mpr ⟨?_, ?_⟩⟩
      · rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
        have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
        rw [abs_of_nonneg h0]
        exact (mul_le_mul hp.1.2 (rHat_bound K hK p hp) (abs_nonneg _) (h0.trans hp.1.2)).trans (le_max_left _ _)
      · exact (hSb p hp θ).trans (le_max_right _ _)
      · exact (hGb p hp θ).trans (le_max_right _ _)
    · intro i o e
      unfold waveActionVelocity couplingAdj
      fun_prop

end GivenModel

end CellCert

end Breakdown

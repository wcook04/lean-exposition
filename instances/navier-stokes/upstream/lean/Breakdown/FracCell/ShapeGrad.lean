import Breakdown.FracCell.OffAxisCoreSlopeSt
import Breakdown.FracCell.CylIntegral

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.ShapeSlope

open Internal.SpectralBlocksMode

def planar (y : Space) : ℂ := ⟨y 0, y 1⟩

theorem planar_dist (x y : Space) : ‖planar x - planar y‖ ≤ ‖x - y‖ := by
  rw [Complex.norm_def, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.normSq_apply, planar, Complex.sub_re, Complex.sub_im, Fin.sum_univ_three,
    Real.norm_eq_abs, sq_abs, PiLp.sub_apply]
  nlinarith [sq_nonneg (x 2 - y 2)]

theorem radial_eq (y : Space) : radialCoord y = ‖planar y‖ := by
  rw [radialCoord, Complex.norm_def, Complex.normSq_apply]
  simp only [planar]
  ring_nf

theorem angle_eq (y : Space) : angleCoord y = Complex.arg (planar y) := rfl

theorem unit_bound (a b : ℂ) :
    ‖b‖ * ‖Complex.exp (a.arg * Complex.I) - Complex.exp (b.arg * Complex.I)‖ ≤ 2 * ‖a - b‖ := by
  have ha := Complex.norm_mul_exp_arg_mul_I a
  have hb := Complex.norm_mul_exp_arg_mul_I b
  have e : (‖b‖ : ℂ) * (Complex.exp (a.arg * Complex.I) - Complex.exp (b.arg * Complex.I)) =
      ((‖b‖ : ℂ) - ‖a‖) * Complex.exp (a.arg * Complex.I) + (a - b) := by
    linear_combination ha - hb
  have h1 : ‖b‖ * ‖Complex.exp (a.arg * Complex.I) - Complex.exp (b.arg * Complex.I)‖ =
      ‖(‖b‖ : ℂ) * (Complex.exp (a.arg * Complex.I) - Complex.exp (b.arg * Complex.I))‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
  rw [h1, e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]
  have h2 : ‖((‖b‖ : ℂ) - ‖a‖)‖ = |‖b‖ - ‖a‖| := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  have h3 := abs_norm_sub_norm_le b a
  rw [norm_sub_rev b a] at h3
  linarith

theorem pow_bound (E F : ℂ) (hE : ‖E‖ = 1) (hF : ‖F‖ = 1) (m : ℕ) : ‖E ^ m - F ^ m‖ ≤ m * ‖E - F‖ := by
  induction m with
  | zero => simp
  | succ k ih =>
    have e : E ^ (k + 1) - F ^ (k + 1) = E ^ k * (E - F) + (E ^ k - F ^ k) * F := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, hE, hF, one_pow, one_mul, mul_one]
    push_cast
    linarith

theorem trig_eq (t : Fin 2) (m : ℕ) (θ : ℝ) : trigMode t (m * θ) =
    if t = 0 then (Complex.exp (θ * Complex.I) ^ m).re else (Complex.exp (θ * Complex.I) ^ m).im := by
  rw [← Complex.exp_nat_mul, show (m : ℂ) * (θ * Complex.I) = ((m * θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
  unfold trigMode
  split_ifs
  · rw [Complex.exp_ofReal_mul_I_re]
  · rw [Complex.exp_ofReal_mul_I_im]

theorem trig_le (t : Fin 2) (m : ℕ) (θ : ℝ) : |trigMode t (m * θ)| ≤ 1 := by
  unfold trigMode
  split_ifs
  · exact Real.abs_cos_le_one _
  · exact Real.abs_sin_le_one _

theorem trig_dist (t : Fin 2) (m : ℕ) (θ φ : ℝ) :
    |trigMode t (m * θ) - trigMode t (m * φ)| ≤ m * ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ := by
  rw [trig_eq, trig_eq]
  refine le_trans ?_ (pow_bound _ _ (Complex.norm_exp_ofReal_mul_I θ) (Complex.norm_exp_ofReal_mul_I φ) m)
  split_ifs
  · rw [← Complex.sub_re]; exact Complex.abs_re_le_norm _
  · rw [← Complex.sub_im]; exact Complex.abs_im_le_norm _

theorem frame_norm (c : Fin 3) (θ : ℝ) : ‖frameAt c θ‖ ≤ 1 := by
  have h := frame_inner c c θ
  rw [if_pos rfl, real_inner_self_eq_norm_sq] at h
  nlinarith [norm_nonneg (frameAt c θ)]

theorem frame_dist (c : Fin 3) (θ φ : ℝ) :
    ‖frameAt c θ - frameAt c φ‖ ≤ ‖Complex.exp (θ * Complex.I) - Complex.exp (φ * Complex.I)‖ := by
  rw [EuclideanSpace.norm_eq, Complex.norm_def, Complex.normSq_apply]
  refine Real.sqrt_le_sqrt ?_
  simp only [Complex.sub_re, Complex.sub_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  fin_cases c <;> simp [frameAt, unitVector] <;> nlinarith

def angFactor (m : ℕ) (c : Fin 3) (t : Fin 2) (y : Space) : Space :=
  trigMode t (m * angleCoord y) • frameVector c y

theorem ang_norm (m : ℕ) (c : Fin 3) (t : Fin 2) (y : Space) : ‖angFactor m c t y‖ ≤ 1 := by
  rw [angFactor, norm_smul, Real.norm_eq_abs, frame_eq]
  have h1 := trig_le t m (angleCoord y)
  have h2 := frame_norm c (angleCoord y)
  nlinarith [abs_nonneg (trigMode t (m * angleCoord y)), norm_nonneg (frameAt c (angleCoord y))]

theorem ang_rel (m : ℕ) (c : Fin 3) (t : Fin 2) {R : ℝ} (hR : 0 < R) (x y : Space) (hy : R ≤ radialCoord y) :
    ‖angFactor m c t x - angFactor m c t y‖ ≤ (m + 1) * (2 / R) * ‖x - y‖ := by
  set E := ‖Complex.exp (angleCoord x * Complex.I) - Complex.exp (angleCoord y * Complex.I)‖ with hE
  have hub := unit_bound (planar x) (planar y)
  rw [← angle_eq, ← angle_eq, ← radial_eq, ← hE] at hub
  have hpd := planar_dist x y
  have hE0 : 0 ≤ E := norm_nonneg _
  have hEb : E ≤ 2 / R * ‖x - y‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hR]
    nlinarith
  have e : angFactor m c t x - angFactor m c t y =
      (trigMode t (m * angleCoord x) - trigMode t (m * angleCoord y)) • frameVector c x
        + trigMode t (m * angleCoord y) • (frameVector c x - frameVector c y) := by
    simp only [angFactor, sub_smul, smul_sub]
    abel
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, frame_eq, frame_eq]
  have h1 := trig_dist t m (angleCoord x) (angleCoord y)
  have h2 := frame_dist c (angleCoord x) (angleCoord y)
  have h3 := frame_norm c (angleCoord x)
  have h4 := trig_le t m (angleCoord y)
  rw [← hE] at h1 h2
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have k1 : |trigMode t (m * angleCoord x) - trigMode t (m * angleCoord y)| * ‖frameAt c (angleCoord x)‖ ≤ m * E :=
    (mul_le_mul h1 h3 (norm_nonneg _) (by positivity)).trans (le_of_eq (mul_one _))
  have k2 : |trigMode t (m * angleCoord y)| * ‖frameAt c (angleCoord x) - frameAt c (angleCoord y)‖ ≤ E :=
    (mul_le_mul h4 h2 (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
  have k3 : (m + 1) * E ≤ (m + 1) * (2 / R * ‖x - y‖) := mul_le_mul_of_nonneg_left hEb (by positivity)
  nlinarith

theorem prod_slope {h : Space → ℝ} {A : Space → Space} {Lh M LA : ℝ} (hh : ∀ x y, |h x - h y| ≤ Lh * ‖x - y‖)
    (hM : ∀ y, |h y| ≤ M) (hA : ∀ y, ‖A y‖ ≤ 1) (hrel : ∀ x y, h y ≠ 0 → ‖A x - A y‖ ≤ LA * ‖x - y‖)
    (hLA : 0 ≤ LA) (x y : Space) : ‖h x • A x - h y • A y‖ ≤ (Lh + M * LA) * ‖x - y‖ := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM y)
  by_cases hy : h y = 0
  · by_cases hx : h x = 0
    · rw [hx, hy, zero_smul, zero_smul, sub_zero, norm_zero]
      have : 0 ≤ Lh * ‖x - y‖ := (abs_nonneg _).trans (hh x y)
      have h2 : 0 ≤ M * LA * ‖x - y‖ := by positivity
      nlinarith
    · have e : h x • A x - h y • A y = (h x - h y) • A y + h x • (A x - A y) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have k1 := mul_le_mul (hh x y) (hA y) (norm_nonneg _) ((abs_nonneg _).trans (hh x y))
      have k2 := hrel y x hx
      rw [norm_sub_rev, norm_sub_rev y x] at k2
      have k3 := mul_le_mul (hM x) k2 (norm_nonneg _) hM0
      nlinarith
  · have e : h x • A x - h y • A y = (h x - h y) • A x + h y • (A x - A y) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    have k1 := mul_le_mul (hh x y) (hA x) (norm_nonneg _) ((abs_nonneg _).trans (hh x y))
    have k3 := mul_le_mul (hM y) (hrel x y hy) (norm_nonneg _) hM0
    nlinarith

theorem clamp_slope (a b x y : ℝ) : |max a (min x b) - max a (min y b)| ≤ |x - y| := by
  have h := ((LipschitzWith.id.min_const b).const_max a).dist_le_mul x y
  simpa [Real.dist_eq] using h

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (x : ℝ) : max a (min x b) ∈ Set.Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩

theorem clamp_of_mem {a b x : ℝ} (hx : x ∈ Set.Icc a b) : max a (min x b) = x := by
  rw [min_eq_left hx.2, max_eq_right hx.1]

theorem radial_slope (x y : Space) : |radialCoord x - radialCoord y| ≤ ‖x - y‖ := by
  rw [radial_eq, radial_eq]
  exact (abs_norm_sub_norm_le _ _).trans (planar_dist x y)

theorem coord_slope (x y : Space) (i : Fin 3) : |x i - y i| ≤ ‖x - y‖ := by
  have := PiLp.norm_apply_le (x - y) i
  simpa [Real.norm_eq_abs] using this

theorem height_slopeBound (x y : Space) : |x 2 - y 2| ≤ ‖x - y‖ := coord_slope x y 2

def clampedCoef (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (s : Fin 2) (c : Fin 3) (t : Fin 2)
    (y : Space) : ℝ :=
  Q s c t (max g.innerRadius (min (radialCoord y) g.outerRadius)) (max (solidLower g s) (min (y 2) (solidUpper g s)))

theorem solid_mem (g : CellBlock) (s : Fin 2) (y : Space) : y ∈ cellSolid g s ↔
    radialCoord y ∈ Set.Icc g.innerRadius g.outerRadius ∧ y 2 ∈ Set.Icc (solidLower g s) (solidUpper g s) := by
  fin_cases s
  · simp [cellSolid, solidLower, solidUpper, and_assoc]
  · simp only [cellSolid, solidLower, solidUpper, Set.mem_setOf_eq, Set.mem_Icc]
    simp only [Fin.mk_one, one_ne_zero, if_false]
    constructor
    · rintro ⟨a1, a2, a3, a4⟩
      exact ⟨⟨a1, a2⟩, by linarith, by linarith⟩
    · rintro ⟨⟨a1, a2⟩, a3, a4⟩
      exact ⟨a1, a2, by linarith, by linarith⟩

theorem solid_le (g : CellBlock) (hL : g.lowerHeight < g.upperHeight) (s : Fin 2) : solidLower g s ≤ solidUpper g s := by
  unfold solidLower solidUpper
  split_ifs <;> linarith

theorem clamp_zero {F : ℝ → ℝ → ℝ} {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) (ha : ∀ z, F a z = 0)
    (hb : ∀ z, F b z = 0) (hc : ∀ r, F r c = 0) (hd : ∀ r, F r d = 0) {x w : ℝ}
    (h : ¬ (x ∈ Set.Icc a b ∧ w ∈ Set.Icc c d)) : F (max a (min x b)) (max c (min w d)) = 0 := by
  simp only [Set.mem_Icc, not_and_or, not_le] at h
  rcases h with (h | h) | (h | h)
  · rw [max_eq_left ((min_le_left _ _).trans h.le)]; exact ha _
  · rw [min_eq_right h.le, max_eq_right hab]; exact hb _
  · rw [max_eq_left ((min_le_left _ _).trans h.le)]; exact hc _
  · rw [min_eq_right h.le, max_eq_right hcd]; exact hd _

theorem shape_eq (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hRo : g.innerRadius < g.outerRadius)
    (hL : g.lowerHeight < g.upperHeight)
    (h1 : ∀ s c t z, Q s c t g.innerRadius z = 0) (h2 : ∀ s c t z, Q s c t g.outerRadius z = 0)
    (h3 : ∀ s c t r, Q s c t r (solidLower g s) = 0) (h4 : ∀ s c t r, Q s c t r (solidUpper g s) = 0)
    (y : Space) : shapeField g Q y =
      ∑ s : Fin 2, ∑ c : Fin 3, ∑ t : Fin 2, clampedCoef g Q s c t y • angFactor g.mode c t y := by
  unfold shapeField
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ cellSolid g s
  · rw [Set.indicator_of_mem hy]
    have hm := (solid_mem g s y).1 hy
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_smul]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [clampedCoef, clamp_of_mem hm.1, clamp_of_mem hm.2, angFactor, smul_smul, mul_comm]
  · rw [Set.indicator_of_notMem hy]
    have hm : ¬ (radialCoord y ∈ Set.Icc g.innerRadius g.outerRadius ∧
        y 2 ∈ Set.Icc (solidLower g s) (solidUpper g s)) := fun h => hy ((solid_mem g s y).2 h)
    symm
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun t _ => ?_
    rw [clampedCoef, clamp_zero (F := Q s c t) hRo.le (solid_le g hL s) (h1 s c t) (h2 s c t) (h3 s c t) (h4 s c t) hm,
      zero_smul]

theorem term_bound (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hR : 0 < g.innerRadius)
    (hRo : g.innerRadius < g.outerRadius) (hL : g.lowerHeight < g.upperHeight)
    (hQ : ∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t)))
    (h1 : ∀ s c t z, Q s c t g.innerRadius z = 0) (s : Fin 2) (c : Fin 3) (t : Fin 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y, ‖clampedCoef g Q s c t x • angFactor g.mode c t x
      - clampedCoef g Q s c t y • angFactor g.mode c t y‖ ≤ C * ‖x - y‖ := by
  set rect : Set (ℝ × ℝ) := Set.Icc g.innerRadius g.outerRadius ×ˢ Set.Icc (solidLower g s) (solidUpper g s)
  have hconv : Convex ℝ rect := (convex_Icc _ _).prod (convex_Icc _ _)
  have hcpt : IsCompact rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨K, hK⟩ := (hQ s c t).contDiffOn.exists_lipschitzOnWith (by norm_num) hconv hcpt
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hQ s c t).continuous.continuousOn
  have hmem : ∀ y, (max g.innerRadius (min (radialCoord y) g.outerRadius),
      max (solidLower g s) (min (y 2) (solidUpper g s))) ∈ rect :=
    fun y => ⟨clamp_mem hRo.le _, clamp_mem (solid_le g hL s) _⟩
  have hh : ∀ x y, |clampedCoef g Q s c t x - clampedCoef g Q s c t y| ≤ (K : ℝ) * ‖x - y‖ := by
    intro x y
    have hd := hK.dist_le_mul _ (hmem x) _ (hmem y)
    rw [Real.dist_eq] at hd
    refine hd.trans (mul_le_mul_of_nonneg_left ?_ K.coe_nonneg)
    rw [Prod.dist_eq, Real.dist_eq, Real.dist_eq]
    exact max_le ((clamp_slope _ _ _ _).trans (radial_slope x y)) ((clamp_slope _ _ _ _).trans (height_slopeBound x y))
  have hMb : ∀ y, |clampedCoef g Q s c t y| ≤ max M 0 := fun y =>
    ((Real.norm_eq_abs _).symm.le.trans (hM _ (hmem y))).trans (le_max_left _ _)
  have hrel : ∀ x y, clampedCoef g Q s c t y ≠ 0 →
      ‖angFactor g.mode c t x - angFactor g.mode c t y‖ ≤ ((g.mode : ℝ) + 1) * (2 / g.innerRadius) * ‖x - y‖ := by
    intro x y hy
    refine ang_rel g.mode c t hR x y ?_
    by_contra hlt0
    have hlt := not_le.mp hlt0
    apply hy
    rw [clampedCoef, max_eq_left ((min_le_left _ _).trans hlt.le)]
    exact h1 s c t _
  have hLA : (0 : ℝ) ≤ ((g.mode : ℝ) + 1) * (2 / g.innerRadius) := by positivity
  refine ⟨(K : ℝ) + max M 0 * (((g.mode : ℝ) + 1) * (2 / g.innerRadius)), by positivity, ?_⟩
  exact prod_slope hh hMb (ang_norm g.mode c t) hrel hLA

theorem shapeSlope : ShapeSlopeStatement := by
  intro g Q hR hRo hL _ hQ h1 h2 h3 h4
  have hC := term_bound g Q hR hRo hL hQ h1
  choose C hC0 hC using hC
  refine ⟨_, LipschitzWith.of_dist_le' (K := ∑ s, ∑ c, ∑ t, C s c t) fun x y => ?_⟩
  rw [dist_eq_norm, dist_eq_norm, shape_eq g Q hRo hL h1 h2 h3 h4, shape_eq g Q hRo hL h1 h2 h3 h4]
  simp only [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  simp only [Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum fun c _ => (norm_sum_le _ _).trans ?_
  exact Finset.sum_le_sum fun t _ => hC s c t x y

end Internal.ShapeSlope

namespace Internal.ShapeDeriv

open Internal.SpectralBlocksMode Internal.ShapeSlope

theorem vec_deriv {F : ℝ → Space} {v : Space} {x : ℝ} (h : ∀ i, HasDerivAt (fun ε => F ε i) (v i) x) :
    HasDerivAt F v x := by
  have h2 := (EuclideanSpace.equiv (Fin 3) ℝ).symm.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_pi.2 h)
  exact h2

def frameDer (c : Fin 3) (θ : ℝ) : Space :=
  match c with
  | 0 => frameAt 1 θ
  | 1 => -frameAt 0 θ
  | 2 => 0

theorem frame_deriv (c : Fin 3) (θ : ℝ) : HasDerivAt (fun x => frameAt c x) (frameDer c θ) θ := by
  refine vec_deriv fun i => ?_
  fin_cases c <;> fin_cases i <;> simp [frameAt, frameDer, unitVector]
  all_goals first
    | exact Real.hasDerivAt_cos θ
    | exact Real.hasDerivAt_sin θ
    | exact (Real.hasDerivAt_sin θ).neg
    | exact (Real.hasDerivAt_cos θ).neg
    | exact hasDerivAt_const θ _

theorem polar (y : Space) : y = cylPoint (radialCoord y) (angleCoord y) (y 2) := by
  have hc := Complex.norm_mul_cos_arg (⟨y 0, y 1⟩ : ℂ)
  have hs := Complex.norm_mul_sin_arg (⟨y 0, y 1⟩ : ℂ)
  have hr : radialCoord y = ‖(⟨y 0, y 1⟩ : ℂ)‖ := by
    rw [radialCoord, Complex.norm_def, Complex.normSq_apply]
    ring_nf
  ext i
  fin_cases i
  · simp only [cyl0, Fin.zero_eta]
    rw [hr]
    exact hc.symm
  · simp only [cyl1, Fin.mk_one]
    rw [hr]
    exact hs.symm
  · simp [cyl2]

theorem angle_mod {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    ∃ k : ℤ, angleCoord (cylPoint r θ z) = θ - k * (2 * Real.pi) := by
  have hmem := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ
  have hk := self_sub_toIocDiv_mul Real.two_pi_pos (-Real.pi) θ
  have hI : toIocMod Real.two_pi_pos (-Real.pi) θ ∈ Set.Ioc (-Real.pi) Real.pi := ⟨hmem.1, by linarith [hmem.2]⟩
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) θ, ?_⟩
  have e : cylPoint r θ z = cylPoint r (θ - (toIocDiv Real.two_pi_pos (-Real.pi) θ : ℝ) * (2 * Real.pi)) z := by
    simp only [cylPoint, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]
  rw [e, hk, angle_cyl hr hI]

theorem trig_mod (t : Fin 2) (m : ℕ) (θ : ℝ) (k : ℤ) :
    trigMode t (m * (θ - k * (2 * Real.pi))) = trigMode t (m * θ) := by
  rw [show (m : ℝ) * (θ - k * (2 * Real.pi)) = m * θ - ((m * k : ℤ) : ℝ) * (2 * Real.pi) by push_cast; ring]
  unfold trigMode
  split_ifs
  · exact Real.cos_sub_int_mul_two_pi _ _
  · exact Real.sin_sub_int_mul_two_pi _ _

theorem frame_mod (c : Fin 3) (θ : ℝ) (k : ℤ) : frameAt c (θ - k * (2 * Real.pi)) = frameAt c θ := by
  fin_cases c <;> simp [frameAt, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

def localField (m : ℕ) (a : Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (r θ z : ℝ) : Space :=
  ∑ c : Fin 3, (∑ t : Fin 2, trigMode t (m * θ) * a c t r z) • frameAt c θ

theorem shape_local (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (s : Fin 2) {r : ℝ} (hr : 0 < r)
    (θ z : ℝ) (hin : cylPoint r θ z ∈ cellSolid g s) (hout : ∀ s', s' ≠ s → cylPoint r θ z ∉ cellSolid g s') :
    shapeField g Q (cylPoint r θ z) = localField g.mode (Q s) r θ z := by
  obtain ⟨k, hk⟩ := angle_mod hr θ z
  unfold shapeField
  rw [Finset.sum_eq_single s, Set.indicator_of_mem hin]
  · unfold localField
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [frame_eq, hk, frame_mod, radial_cyl hr, cyl2]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [trig_mod]
  · intro s' _ hs'
    rw [Set.indicator_of_notMem (hout s' hs')]
  · intro h
    exact absurd (Finset.mem_univ s) h

theorem shift_deriv {f : ℝ → ℝ} {f' r0 : ℝ} (h : HasDerivAt f f' r0) : HasDerivAt (fun ε => f (r0 + ε)) f' 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => r0 + ε) 1 0 := (hasDerivAt_id 0).const_add r0
  have h2 : HasDerivAt f f' (r0 + 0) := by rwa [add_zero]
  have h3 := h2.comp 0 h1
  rw [mul_one] at h3
  exact h3

theorem radial_dir (m : ℕ) (a : Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (r0 θ z : ℝ)
    (ha : ∀ c t, HasDerivAt (fun x => a c t x z) (deriv (fun x => a c t x z) r0) r0) :
    HasDerivAt (fun ε => localField m a (r0 + ε) θ z)
      (∑ c : Fin 3, (∑ t : Fin 2, trigMode t (m * θ) * deriv (fun x => a c t x z) r0) • frameAt c θ) 0 := by
  unfold localField
  refine HasDerivAt.sum (u := Finset.univ)
    (A := fun c ε => (∑ t : Fin 2, trigMode t (m * θ) * a c t (r0 + ε) z) • frameAt c θ) fun c _ => ?_
  refine HasDerivAt.smul_const ?_ _
  exact HasDerivAt.sum (u := Finset.univ) (A := fun t ε => trigMode t (m * θ) * a c t (r0 + ε) z)
    fun t _ => (shift_deriv (ha c t)).const_mul _

theorem height_dir (m : ℕ) (a : Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (r θ z0 : ℝ)
    (ha : ∀ c t, HasDerivAt (fun w => a c t r w) (deriv (fun w => a c t r w) z0) z0) :
    HasDerivAt (fun ε => localField m a r θ (z0 + ε))
      (∑ c : Fin 3, (∑ t : Fin 2, trigMode t (m * θ) * deriv (fun w => a c t r w) z0) • frameAt c θ) 0 := by
  unfold localField
  refine HasDerivAt.sum (u := Finset.univ)
    (A := fun c ε => (∑ t : Fin 2, trigMode t (m * θ) * a c t r (z0 + ε)) • frameAt c θ) fun c _ => ?_
  refine HasDerivAt.smul_const ?_ _
  exact HasDerivAt.sum (u := Finset.univ) (A := fun t ε => trigMode t (m * θ) * a c t r (z0 + ε))
    fun t _ => (shift_deriv (ha c t)).const_mul _

def tderiv (t : Fin 2) (x : ℝ) : ℝ := if t = 0 then -Real.sin x else Real.cos x

theorem turn_inner (m : ℕ) (θ0 r0 : ℝ) : HasDerivAt (fun ε : ℝ => (m : ℝ) * (θ0 + ε / r0)) (m * r0⁻¹) 0 := by
  have h : HasDerivAt (fun ε : ℝ => θ0 + ε / r0) r0⁻¹ 0 := by
    simpa [div_eq_mul_inv] using ((hasDerivAt_id (0 : ℝ)).mul_const r0⁻¹).const_add θ0
  exact h.const_mul _

theorem trig_turn (t : Fin 2) (m : ℕ) (θ0 r0 : ℝ) :
    HasDerivAt (fun ε : ℝ => trigMode t (m * (θ0 + ε / r0))) (tderiv t (m * θ0) * (m * r0⁻¹)) 0 := by
  have h := turn_inner m θ0 r0
  unfold trigMode tderiv
  split_ifs
  · convert h.cos using 2
    simp
  · convert h.sin using 2
    simp

theorem angle_inner (θ0 r0 : ℝ) : HasDerivAt (fun ε : ℝ => θ0 + ε / r0) r0⁻¹ 0 := by
  simpa [div_eq_mul_inv] using ((hasDerivAt_id (0 : ℝ)).mul_const r0⁻¹).const_add θ0

theorem frame_turn (c : Fin 3) (θ0 r0 : ℝ) :
    HasDerivAt (fun ε : ℝ => frameAt c (θ0 + ε / r0)) (r0⁻¹ • frameDer c θ0) 0 := by
  have h := (frame_deriv c θ0)
  have h2 : HasDerivAt (fun x => frameAt c x) (frameDer c θ0) (θ0 + 0 / r0) := by simpa using h
  exact h2.scomp 0 (angle_inner θ0 r0)

theorem turn_dir (m : ℕ) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (s : Fin 2) (r0 θ0 z : ℝ) (hr : 0 < r0) :
    HasDerivAt (fun ε => localField m (Q s) r0 (θ0 + ε / r0) z)
      (∑ c : Fin 3, (∑ t : Fin 2, trigMode t (m * θ0) *
        (r0⁻¹ * angularCoef m Q s c t r0 z)) • frameAt c θ0) 0 := by
  set a := Q s with ha_def
  have hd : HasDerivAt (fun ε => localField m a r0 (θ0 + ε / r0) z)
      (∑ c : Fin 3, ((∑ t : Fin 2, trigMode t (m * (θ0 + 0 / r0)) * a c t r0 z) • (r0⁻¹ • frameDer c θ0)
        + (∑ t : Fin 2, tderiv t (m * θ0) * (m * r0⁻¹) * a c t r0 z) • frameAt c (θ0 + 0 / r0))) 0 := by
    unfold localField
    refine HasDerivAt.sum (u := Finset.univ)
      (A := fun c ε => (∑ t : Fin 2, trigMode t (m * (θ0 + ε / r0)) * a c t r0 z) • frameAt c (θ0 + ε / r0))
      fun c _ => ?_
    refine HasDerivAt.smul (𝕜' := ℝ) (c := fun ε => ∑ t : Fin 2, trigMode t (m * (θ0 + ε / r0)) * a c t r0 z)
      ?_ (frame_turn c θ0 r0)
    exact HasDerivAt.sum (u := Finset.univ) (A := fun t ε => trigMode t (m * (θ0 + ε / r0)) * a c t r0 z)
      fun t _ => (trig_turn t m θ0 r0).mul_const _
  convert hd using 1
  have hr' : r0 ≠ 0 := hr.ne'
  simp only [zero_div, add_zero]
  ext i
  fin_cases i <;>
    simp [Fin.sum_univ_three, Fin.sum_univ_two, frameAt, frameDer, trigMode, tderiv, angularCoef, ha_def,
      unitVector] <;>
    field_simp <;> ring

theorem curve_r (r0 θ z : ℝ) : HasDerivAt (fun ε => cylPoint (r0 + ε) θ z) (frameAt 0 θ) 0 := by
  refine vec_deriv fun i => ?_
  fin_cases i
  · have hX : HasDerivAt (fun ε : ℝ => (r0 + ε) * Real.cos θ) ((frameAt 0 θ) 0) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add r0).mul_const (Real.cos θ)).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl0 _ _ _)
  · have hX : HasDerivAt (fun ε : ℝ => (r0 + ε) * Real.sin θ) ((frameAt 0 θ) 1) 0 :=
      (((hasDerivAt_id (0 : ℝ)).const_add r0).mul_const (Real.sin θ)).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl1 _ _ _)
  · have hX : HasDerivAt (fun _ : ℝ => z) ((frameAt 0 θ) 2) 0 :=
      (hasDerivAt_const (0 : ℝ) z).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl2 _ _ _)

theorem curve_z (r θ z0 : ℝ) : HasDerivAt (fun ε => cylPoint r θ (z0 + ε)) (frameAt 2 θ) 0 := by
  refine vec_deriv fun i => ?_
  fin_cases i
  · have hX : HasDerivAt (fun _ : ℝ => r * Real.cos θ) ((frameAt 2 θ) 0) 0 :=
      (hasDerivAt_const (0 : ℝ) (r * Real.cos θ)).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl0 _ _ _)
  · have hX : HasDerivAt (fun _ : ℝ => r * Real.sin θ) ((frameAt 2 θ) 1) 0 :=
      (hasDerivAt_const (0 : ℝ) (r * Real.sin θ)).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl1 _ _ _)
  · have hX : HasDerivAt (fun ε : ℝ => z0 + ε) ((frameAt 2 θ) 2) 0 :=
      ((hasDerivAt_id (0 : ℝ)).const_add z0).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl2 _ _ _)

theorem curve_t (r0 θ0 z : ℝ) (hr : r0 ≠ 0) :
    HasDerivAt (fun ε => cylPoint r0 (θ0 + ε / r0) z) (frameAt 1 θ0) 0 := by
  refine vec_deriv fun i => ?_
  fin_cases i
  · have hX : HasDerivAt (fun ε : ℝ => r0 * Real.cos (θ0 + ε / r0)) ((frameAt 1 θ0) 0) 0 :=
      ((angle_inner θ0 r0).cos.const_mul r0).congr_deriv (by simp [frameAt]; field_simp)
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl0 _ _ _)
  · have hX : HasDerivAt (fun ε : ℝ => r0 * Real.sin (θ0 + ε / r0)) ((frameAt 1 θ0) 1) 0 :=
      ((angle_inner θ0 r0).sin.const_mul r0).congr_deriv (by simp [frameAt]; field_simp)
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl1 _ _ _)
  · have hX : HasDerivAt (fun _ : ℝ => z) ((frameAt 1 θ0) 2) 0 :=
      (hasDerivAt_const (0 : ℝ) z).congr_deriv (by simp [frameAt, unitVector])
    exact hX.congr_of_eventuallyEq (Filter.Eventually.of_forall fun ε => cyl2 _ _ _)

theorem frame_expand (θ : ℝ) (v : Space) : v = ∑ d : Fin 3, inner ℝ (frameAt d θ) v • frameAt d θ := by
  have h := Real.cos_sq_add_sin_sq θ
  ext i
  fin_cases i <;> simp [frameAt, Fin.sum_univ_three, PiLp.inner_apply, unitVector] <;>
    linear_combination (-(v _)) * h

theorem grad_apply (g : CellBlock) (f : Fin 2 → Fin 3 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (y : Space) (d : Fin 3) :
    shapeGradField g f y (frameVector d y) = shapeField g (fun s c t => f s c d t) y := by
  classical
  unfold shapeGradField shapeField
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ => ?_
  by_cases hy : y ∈ cellSolid g s
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, frame_eq, frame_inner, smul_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp [ite_smul, Finset.sum_ite_eq']
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]
    simp

theorem interior_mem (g : CellBlock) (hL0 : 0 ≤ g.lowerHeight) (s : Fin 2) {r : ℝ} (hr : 0 < r) (θ z : ℝ)
    (h1 : g.innerRadius < r) (h2 : r < g.outerRadius) (h3 : solidLower g s < z) (h4 : z < solidUpper g s) :
    cylPoint r θ z ∈ cellSolid g s ∧ ∀ s', s' ≠ s → cylPoint r θ z ∉ cellSolid g s' := by
  have key : ∀ s', cylPoint r θ z ∈ cellSolid g s' ↔
      r ∈ Set.Icc g.innerRadius g.outerRadius ∧ z ∈ Set.Icc (solidLower g s') (solidUpper g s') := by
    intro s'
    rw [solid_mem, radial_cyl hr, cyl2]
  refine ⟨(key s).2 ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩, fun s' hs' hm => ?_⟩
  have hz := ((key s').1 hm).2
  fin_cases s <;> fin_cases s' <;> simp_all [solidLower, solidUpper] <;> linarith

theorem diff_fst {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (r z : ℝ) :
    HasDerivAt (fun x => F x z) (deriv (fun x => F x z) r) r := by
  have hd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (r, z)) (r, z) :=
    ((hF.differentiable (by norm_num)) (r, z)).hasFDerivAt
  exact (hd.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r z))).differentiableAt.hasDerivAt

theorem diff_snd {F : ℝ → ℝ → ℝ} (hF : ContDiff ℝ 1 (Function.uncurry F)) (r z : ℝ) :
    HasDerivAt (fun w => F r w) (deriv (fun w => F r w) z) z := by
  have hd : HasFDerivAt (Function.uncurry F) (fderiv ℝ (Function.uncurry F) (r, z)) (r, z) :=
    ((hF.differentiable (by norm_num)) (r, z)).hasFDerivAt
  exact (hd.comp_hasDerivAt z ((hasDerivAt_const z r).prodMk (hasDerivAt_id z))).differentiableAt.hasDerivAt

theorem shift_tendsto (a : ℝ) : Filter.Tendsto (fun ε : ℝ => a + ε) (nhds 0) (nhds a) := by
  have h := (tendsto_const_nhds (x := a)).add (Filter.tendsto_id (x := nhds (0 : ℝ)))
  rw [add_zero] at h
  exact h

theorem deriv_interior (g : CellBlock) (Q : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (hR : 0 < g.innerRadius)
    (hL0 : 0 ≤ g.lowerHeight) (hQ : ∀ s c t, ContDiff ℝ 1 (Function.uncurry (Q s c t))) (s : Fin 2) (y : Space)
    (h1 : g.innerRadius < radialCoord y) (h2 : radialCoord y < g.outerRadius)
    (h3 : solidLower g s < y 2) (h4 : y 2 < solidUpper g s)
    (hy : DifferentiableAt ℝ (shapeField g Q) y) :
    fderiv ℝ (shapeField g Q) y = shapeGradField g (shapeGradCoef g Q) y := by
  set r0 := radialCoord y with hr0_def
  set θ0 := angleCoord y with hθ0_def
  set z0 := y 2 with hz0_def
  have hr0 : 0 < r0 := hR.trans h1
  have hp : y = cylPoint r0 θ0 z0 := polar y
  have hloc : ∀ (F : Fin 2 → Fin 3 → Fin 2 → ℝ → ℝ → ℝ) (r θ z : ℝ), g.innerRadius < r → r < g.outerRadius →
      solidLower g s < z → z < solidUpper g s → shapeField g F (cylPoint r θ z) = localField g.mode (F s) r θ z := by
    intro F r θ z k1 k2 k3 k4
    have hr : 0 < r := hR.trans k1
    obtain ⟨hin, hout⟩ := interior_mem g hL0 s hr θ z k1 k2 k3 k4
    exact shape_local g F s hr θ z hin hout
  have hyd : ∀ x, x = y → HasFDerivAt (shapeField g Q) (fderiv ℝ (shapeField g Q) y) x := by
    rintro x rfl
    exact hy.hasFDerivAt
  have k0 : fderiv ℝ (shapeField g Q) y (frameAt 0 θ0) =
      localField g.mode (fun c t => shapeGradCoef g Q s c 0 t) r0 θ0 z0 := by
    · have hA := (hyd (cylPoint (r0 + 0) θ0 z0) (by rw [add_zero, ← hp])).comp_hasDerivAt (0 : ℝ) (curve_r r0 θ0 z0)
      have ht := shift_tendsto r0
      have hev : (shapeField g Q ∘ fun ε => cylPoint (r0 + ε) θ0 z0) =ᶠ[nhds 0]
          fun ε => localField g.mode (Q s) (r0 + ε) θ0 z0 := by
        filter_upwards [ht.eventually (Ioo_mem_nhds h1 h2)] with ε hε
        exact hloc Q _ _ _ hε.1 hε.2 h3 h4
      have hB := (radial_dir g.mode (Q s) r0 θ0 z0 fun c t => diff_fst (hQ s c t) r0 z0).congr_of_eventuallyEq hev
      rw [hA.unique hB]
      unfold localField
      simp [shapeGradCoef]
  have k1 : fderiv ℝ (shapeField g Q) y (frameAt 1 θ0) =
      localField g.mode (fun c t => shapeGradCoef g Q s c 1 t) r0 θ0 z0 := by
    · have hA := (hyd (cylPoint r0 (θ0 + 0 / r0) z0) (by rw [zero_div, add_zero, ← hp])).comp_hasDerivAt (0 : ℝ)
        (curve_t r0 θ0 z0 hr0.ne')
      have hev : (shapeField g Q ∘ fun ε => cylPoint r0 (θ0 + ε / r0) z0) =ᶠ[nhds 0]
          fun ε => localField g.mode (Q s) r0 (θ0 + ε / r0) z0 :=
        Filter.Eventually.of_forall fun ε => hloc Q _ _ _ h1 h2 h3 h4
      have hB := (turn_dir g.mode Q s r0 θ0 z0 hr0).congr_of_eventuallyEq hev
      rw [hA.unique hB]
      unfold localField
      simp [shapeGradCoef, max_eq_left h1.le]
  have k2 : fderiv ℝ (shapeField g Q) y (frameAt 2 θ0) =
      localField g.mode (fun c t => shapeGradCoef g Q s c 2 t) r0 θ0 z0 := by
    · have hA := (hyd (cylPoint r0 θ0 (z0 + 0)) (by rw [add_zero, ← hp])).comp_hasDerivAt (0 : ℝ) (curve_z r0 θ0 z0)
      have ht := shift_tendsto z0
      have hev : (shapeField g Q ∘ fun ε => cylPoint r0 θ0 (z0 + ε)) =ᶠ[nhds 0]
          fun ε => localField g.mode (Q s) r0 θ0 (z0 + ε) := by
        filter_upwards [ht.eventually (Ioo_mem_nhds h3 h4)] with ε hε
        exact hloc Q _ _ _ h1 h2 hε.1 hε.2
      have hB := (height_dir g.mode (Q s) r0 θ0 z0 fun c t => diff_snd (hQ s c t) r0 z0).congr_of_eventuallyEq hev
      rw [hA.unique hB]
      unfold localField
      simp [shapeGradCoef]
  have key : ∀ d : Fin 3, fderiv ℝ (shapeField g Q) y (frameAt d θ0) =
      localField g.mode (fun c t => shapeGradCoef g Q s c d t) r0 θ0 z0 := by
    intro d
    fin_cases d
    · exact k0
    · exact k1
    · exact k2
  ext1 v
  rw [frame_expand θ0 v, map_sum, map_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [map_smul, map_smul, key d]
  congr 1
  have e1 : frameAt d θ0 = frameVector d y := (frame_eq d y).symm
  rw [e1, grad_apply]
  conv_rhs => rw [hp]
  exact (hloc (fun s c t => shapeGradCoef g Q s c d t) r0 θ0 z0 h1 h2 h3 h4).symm

end Internal.ShapeDeriv

namespace Internal.ShapeNull

open Internal.CylIntegral

theorem coord0 (a b z : ℝ) : toSpace ((a, b), z) 0 = a := rfl
theorem coord1 (a b z : ℝ) : toSpace ((a, b), z) 1 = b := rfl
theorem coord2 (a b z : ℝ) : toSpace ((a, b), z) 2 = z := rfl

theorem null_height (c : ℝ) : volume {y : Space | y 2 = c} = 0 := by
  have hm : MeasurableSet {y : Space | y 2 = c} :=
    (isClosed_eq (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous continuous_const).measurableSet
  rw [← toSpace_mp.measure_preimage hm.nullMeasurableSet]
  have e : toSpace ⁻¹' {y : Space | y 2 = c} = (Set.univ : Set (ℝ × ℝ)) ×ˢ {c} := by
    ext ⟨⟨a, b⟩, z⟩
    simp [coord2]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]

theorem circle_null (ρ : ℝ) : volume {p : ℝ × ℝ | Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = ρ} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = ρ} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  rw [Measure.volume_eq_prod, Measure.measure_prod_null hm]
  refine Filter.Eventually.of_forall fun a => ?_
  have hsub : Prod.mk a ⁻¹' {p : ℝ × ℝ | Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = ρ} ⊆
      ({Real.sqrt (ρ ^ 2 - a ^ 2), -Real.sqrt (ρ ^ 2 - a ^ 2)} : Set ℝ) := by
    intro b hb
    simp only [Set.mem_preimage, Set.mem_setOf_eq] at hb
    have h2 : a ^ 2 + b ^ 2 = ρ ^ 2 := by
      rw [← hb, Real.sq_sqrt (by positivity)]
    have h3 : |b| = Real.sqrt (ρ ^ 2 - a ^ 2) := by
      rw [← Real.sqrt_sq_eq_abs]
      congr 1
      linarith
    rcases abs_cases b with ⟨hb1, _⟩ | ⟨hb1, _⟩
    · left; rw [← h3, hb1]
    · right; rw [← h3, hb1, neg_neg]; rfl
  exact measure_mono_null hsub ((Set.toFinite _).measure_zero _)

theorem null_radial (ρ : ℝ) : volume {y : Space | radialCoord y = ρ} = 0 := by
  have hm : MeasurableSet {y : Space | radialCoord y = ρ} := by
    refine (isClosed_eq ?_ continuous_const).measurableSet
    unfold radialCoord
    have h0 := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous
    have h1 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous
    exact ((h0.pow 2).add (h1.pow 2)).sqrt
  rw [← toSpace_mp.measure_preimage hm.nullMeasurableSet]
  have e : toSpace ⁻¹' {y : Space | radialCoord y = ρ} =
      {p : ℝ × ℝ | Real.sqrt (p.1 ^ 2 + p.2 ^ 2) = ρ} ×ˢ (Set.univ : Set ℝ) := by
    ext ⟨⟨a, b⟩, z⟩
    simp [radialCoord, coord0, coord1]
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, circle_null, zero_mul]

end Internal.ShapeNull

namespace Internal.ShapeAe

open Internal.ShapeSlope Internal.ShapeDeriv Internal.ShapeNull

theorem solid_closed (g : CellBlock) (s : Fin 2) : IsClosed (cellSolid g s) := by
  have e : cellSolid g s = (radialCoord ⁻¹' Set.Icc g.innerRadius g.outerRadius) ∩
      ((fun y : Space => y 2) ⁻¹' Set.Icc (solidLower g s) (solidUpper g s)) := by
    ext y
    rw [solid_mem]
    rfl
  have h0 := (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).continuous
  have h1 := (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).continuous
  have h2 := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).continuous
  have hr : Continuous radialCoord := ((h0.pow 2).add (h1.pow 2)).sqrt
  rw [e]
  exact (isClosed_Icc.preimage hr).inter (isClosed_Icc.preimage h2)

theorem lower_ne (g : CellBlock) (s : Fin 2) {z : ℝ} (a : z ≠ g.lowerHeight) (b : z ≠ -g.upperHeight) :
    solidLower g s ≠ z := by
  fin_cases s
  · exact fun h => a (by simpa [solidLower] using h.symm)
  · exact fun h => b (by simpa [solidLower] using h.symm)

theorem upper_ne (g : CellBlock) (s : Fin 2) {z : ℝ} (a : z ≠ g.upperHeight) (b : z ≠ -g.lowerHeight) :
    z ≠ solidUpper g s := by
  fin_cases s
  · exact fun h => a (by simpa [solidUpper] using h)
  · exact fun h => b (by simpa [solidUpper] using h)

end Internal.ShapeAe

theorem shapeSlope_holds : ShapeSlopeStatement := Internal.ShapeSlope.shapeSlope

open Internal.ShapeSlope Internal.ShapeDeriv Internal.ShapeNull Internal.ShapeAe in
theorem shapeDeriv_holds : ShapeDerivStatement := by
  intro g Q hR hRo hL hL0 hQ h1 h2 h3 h4
  obtain ⟨K, hK⟩ := shapeSlope_holds g Q hR hRo hL hL0 hQ h1 h2 h3 h4
  have hnull : volume ({y : Space | radialCoord y = g.innerRadius} ∪ {y | radialCoord y = g.outerRadius} ∪
      {y | y 2 = g.lowerHeight} ∪ {y | y 2 = g.upperHeight} ∪ {y | y 2 = -g.lowerHeight} ∪
      {y | y 2 = -g.upperHeight}) = 0 := by
    simp only [measure_union_null_iff, null_radial, null_height, and_self]
  filter_upwards [hK.ae_differentiableAt, measure_eq_zero_iff_ae_notMem.1 hnull] with y hy hyN
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hyN
  obtain ⟨⟨⟨⟨⟨n1, n2⟩, n3⟩, n4⟩, n5⟩, n6⟩ := hyN
  by_cases hin : ∃ s, y ∈ cellSolid g s
  · obtain ⟨s, hs⟩ := hin
    have hm := (solid_mem g s y).1 hs
    have k1 : g.innerRadius < radialCoord y := lt_of_le_of_ne hm.1.1 (Ne.symm n1)
    have k2 : radialCoord y < g.outerRadius := lt_of_le_of_ne hm.1.2 n2
    have k3 : solidLower g s < y 2 := lt_of_le_of_ne hm.2.1 (lower_ne g s n3 n6)
    have k4 : y 2 < solidUpper g s := lt_of_le_of_ne hm.2.2 (upper_ne g s n4 n5)
    rw [← deriv_interior g Q hR hL0 hQ s y k1 k2 k3 k4 hy]
    exact hy.hasFDerivAt
  · have hout : ∀ s, y ∉ cellSolid g s := fun s h => hin ⟨s, h⟩
    have hD : shapeGradField g (shapeGradCoef g Q) y = 0 := by
      unfold shapeGradField
      simp [Set.indicator_of_notMem (hout _)]
    have hopen : IsOpen (⋃ s, cellSolid g s)ᶜ :=
      (isClosed_iUnion_of_finite fun s => solid_closed g s).isOpen_compl
    have hmem : y ∈ (⋃ s, cellSolid g s)ᶜ := by
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
      exact hout
    have hev : shapeField g Q =ᶠ[nhds y] fun _ => 0 := by
      filter_upwards [hopen.mem_nhds hmem] with w hw
      simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hw
      unfold shapeField
      simp [Set.indicator_of_notMem (hw _)]
    rw [hD]
    exact (hasFDerivAt_const (0 : Space) y).congr_of_eventuallyEq hev

end Spectral

end CellCert

end Breakdown

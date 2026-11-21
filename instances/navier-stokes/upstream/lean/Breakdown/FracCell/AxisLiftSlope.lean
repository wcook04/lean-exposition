import Breakdown.FracCell.AxisLiftWeak

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.AxisLiftSlope

theorem slope_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → ℝ} {g : Space → E}
    (hf : ∃ K, LipschitzWith K f) (hfb : ∃ M, ∀ x, |f x| ≤ M) (hg : ∃ K, LipschitzWith K g)
    (hgb : ∃ B, ∀ x, f x ≠ 0 → ‖g x‖ ≤ B) : ∃ K, LipschitzWith K (fun x => f x • g x) := by
  obtain ⟨Kf, hKf⟩ := hf
  obtain ⟨M, hM⟩ := hfb
  obtain ⟨Kg, hKg⟩ := hg
  obtain ⟨B, hB⟩ := hgb
  have hM0 : ∀ x, |f x| ≤ max M 0 := fun x => (hM x).trans (le_max_left _ _)
  have hB0 : ∀ x, f x ≠ 0 → ‖g x‖ ≤ max B 0 := fun x hx => (hB x hx).trans (le_max_left _ _)
  have hKf0 : (0 : ℝ) ≤ Kf := Kf.2
  have hKg0 : (0 : ℝ) ≤ Kg := Kg.2
  have hpos : 0 ≤ (Kf : ℝ) * max B 0 + max M 0 * Kg := by positivity
  refine ⟨Real.toNNReal (Kf * max B 0 + max M 0 * Kg), LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.coe_toNNReal _ hpos, dist_eq_norm]
  have d1 : |f x - f y| ≤ Kf * dist x y := by rw [← Real.dist_eq]; exact hKf.dist_le_mul x y
  have d2 : ‖g x - g y‖ ≤ Kg * dist x y := by rw [← dist_eq_norm]; exact hKg.dist_le_mul x y
  have hd : 0 ≤ dist x y := dist_nonneg
  by_cases hx : f x ≠ 0
  · have e : f x • g x - f y • g y = (f x - f y) • g x + f y • (g x - g y) := by
      rw [sub_smul, smul_sub]; abel
    rw [e]
    calc ‖(f x - f y) • g x + f y • (g x - g y)‖ ≤ ‖(f x - f y) • g x‖ + ‖f y • (g x - g y)‖ := norm_add_le _ _
      _ = |f x - f y| * ‖g x‖ + |f y| * ‖g x - g y‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ (Kf * dist x y) * max B 0 + max M 0 * (Kg * dist x y) :=
          add_le_add (mul_le_mul d1 (hB0 x hx) (norm_nonneg _) (by positivity))
            (mul_le_mul (hM0 y) d2 (norm_nonneg _) (le_max_right _ _))
      _ = (Kf * max B 0 + max M 0 * Kg) * dist x y := by ring
  · by_cases hy : f y ≠ 0
    · have e : f x • g x - f y • g y = (f x - f y) • g y + f x • (g x - g y) := by
        rw [sub_smul, smul_sub]; abel
      rw [e]
      calc ‖(f x - f y) • g y + f x • (g x - g y)‖ ≤ ‖(f x - f y) • g y‖ + ‖f x • (g x - g y)‖ := norm_add_le _ _
        _ = |f x - f y| * ‖g y‖ + |f x| * ‖g x - g y‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ (Kf * dist x y) * max B 0 + max M 0 * (Kg * dist x y) :=
            add_le_add (mul_le_mul d1 (hB0 y hy) (norm_nonneg _) (by positivity))
              (mul_le_mul (hM0 x) d2 (norm_nonneg _) (le_max_right _ _))
        _ = (Kf * max B 0 + max M 0 * Kg) * dist x y := by ring
    · push_neg at hx hy
      rw [hx, hy]
      simp only [zero_smul, sub_self, norm_zero]
      positivity

theorem bl_mul {f g : Space → ℝ} (hf : ∃ K, LipschitzWith K f) (hfb : ∃ M, ∀ x, |f x| ≤ M)
    (hg : ∃ K, LipschitzWith K g) (hgb : ∃ M, ∀ x, |g x| ≤ M) :
    (∃ K, LipschitzWith K (fun x => f x * g x)) ∧ ∃ M, ∀ x, |f x * g x| ≤ M := by
  obtain ⟨M1, h1⟩ := hfb
  obtain ⟨M2, h2⟩ := hgb
  refine ⟨slope_smul hf ⟨M1, h1⟩ hg ⟨M2, fun x _ => by rw [Real.norm_eq_abs]; exact h2 x⟩, M1 * M2, fun x => ?_⟩
  rw [abs_mul]
  exact mul_le_mul (h1 x) (h2 x) (abs_nonneg _) ((abs_nonneg _).trans (h1 x))

theorem slope_sum {E : Type*} [NormedAddCommGroup E] {ι : Type*} (s : Finset ι) (F : ι → Space → E)
    (h : ∀ i, ∃ K, LipschitzWith K (F i)) : ∃ K, LipschitzWith K (fun x => ∑ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using LipschitzWith.const (α := Space) (0 : E)⟩
  | insert a s ha ih =>
    obtain ⟨K1, h1⟩ := h a
    obtain ⟨K2, h2⟩ := ih
    refine ⟨K1 + K2, ?_⟩
    simpa only [Finset.sum_insert ha] using h1.add h2

theorem rad_le (v : Space) : radialCoord v ≤ ‖v‖ := by
  rw [radialCoord, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (v 2)]

theorem rad_cx (v : Space) : radialCoord v = ‖(⟨v 0, v 1⟩ : ℂ)‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  rfl

theorem rad_slope : LipschitzWith 1 radialCoord := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  refine le_trans ?_ (rad_le (x - y))
  rw [rad_cx, rad_cx, rad_cx]
  have e : (⟨(x - y) 0, (x - y) 1⟩ : ℂ) = ⟨x 0, x 1⟩ - ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp
  rw [e]
  exact abs_norm_sub_norm_le _ _

theorem coord_slope (i : Fin 3) : LipschitzWith 1 (fun y : Space => y i) := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul]
  have := PiLp.norm_apply_le (x - y) i
  simpa [Real.norm_eq_abs] using this

theorem coord_le (y : Space) (i : Fin 2) : |y i.castSucc| ≤ radialCoord y := by
  rw [radialCoord]
  apply Real.abs_le_sqrt
  fin_cases i <;> simp <;> nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]


theorem pow_bl {f : Space → ℝ} (hf : ∃ K, LipschitzWith K f) (hfb : ∃ M, ∀ x, |f x| ≤ M) (n : ℕ) :
    (∃ K, LipschitzWith K (fun x => f x ^ n)) ∧ ∃ M, ∀ x, |f x ^ n| ≤ M := by
  induction n with
  | zero => exact ⟨⟨0, by simpa using LipschitzWith.const (α := Space) (1 : ℝ)⟩, 1, fun x => by simp⟩
  | succ n ih =>
    have h := bl_mul ih.1 ih.2 hf hfb
    simp only [pow_succ]
    exact h

theorem clamp_slope {v : ℝ → ℝ} (hv : ContDiff ℝ 1 v) {a b : ℝ} (hab : a ≤ b) :
    (∃ K, LipschitzWith K (fun t => v (max a (min t b)))) ∧ ∃ M, ∀ t, |v (max a (min t b))| ≤ M := by
  have hmem : ∀ t, max a (min t b) ∈ Set.Icc a b := fun t =>
    ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (hv.continuous_deriv le_rfl).continuousOn
    (s := Set.Icc a b)
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hv.continuous.continuousOn (s := Set.Icc a b)
  have hL : LipschitzOnWith (Real.toNNReal C) v (Set.Icc a b) := by
    refine (convex_Icc a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun x _ => (hv.differentiable (by norm_num)).differentiableAt) (fun x hx => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
    exact (hC x hx).trans (le_max_left _ _)
  have hcl : ∀ x y : ℝ, dist (max a (min x b)) (max a (min y b)) ≤ dist x y := by
    intro x y
    have h := ((LipschitzWith.const a).max (LipschitzWith.id.min (LipschitzWith.const b))).dist_le_mul x y
    simpa using h
  refine ⟨⟨Real.toNNReal C, LipschitzWith.of_dist_le_mul fun x y => ?_⟩, M, fun t => ?_⟩
  · calc dist (v (max a (min x b))) (v (max a (min y b)))
        ≤ Real.toNNReal C * dist (max a (min x b)) (max a (min y b)) := hL.dist_le_mul _ (hmem x) _ (hmem y)
      _ ≤ Real.toNNReal C * dist x y := by
          gcongr
          exact hcl x y
  · rw [← Real.norm_eq_abs]
    exact hM _ (hmem t)

def wvec (c : Fin 3) (y : Space) : Space :=
  if c = 0 then y 0 • unitVector 0 + y 1 • unitVector 1
  else if c = 1 then y 0 • unitVector 1 - y 1 • unitVector 0 else unitVector 2

theorem wvec_slope (c : Fin 3) : ∃ K, LipschitzWith K (wvec c) := by
  fin_cases c
  · let L : Space →L[ℝ] Space := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).smulRight (unitVector 0)
      + (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).smulRight (unitVector 1)
    have e : wvec 0 = fun y => L y := by
      funext y
      simp [wvec, L]
    refine ⟨‖L‖₊, ?_⟩
    show LipschitzWith _ (wvec 0)
    rw [e]
    exact L.lipschitz
  · let L : Space →L[ℝ] Space := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).smulRight (unitVector 1)
      - (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).smulRight (unitVector 0)
    have e : wvec 1 = fun y => L y := by
      funext y
      simp [wvec, L]
    refine ⟨‖L‖₊, ?_⟩
    show LipschitzWith _ (wvec 1)
    rw [e]
    exact L.lipschitz
  · exact ⟨0, by simpa [wvec] using LipschitzWith.const (α := Space) (unitVector 2)⟩

theorem c0_le (y : Space) : |y 0| ≤ radialCoord y := by
  rw [radialCoord]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (y 1)]

theorem c1_le (y : Space) : |y 1| ≤ radialCoord y := by
  rw [radialCoord]
  apply Real.abs_le_sqrt
  nlinarith [sq_nonneg (y 0)]

theorem unit_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  rw [unitVector, PiLp.norm_single, norm_one]

theorem wvec_bd (c : Fin 3) (y : Space) : ‖wvec c y‖ ≤ 2 * radialCoord y + 1 := by
  have h0 := c0_le y
  have h1 := c1_le y
  have hr : 0 ≤ radialCoord y := Real.sqrt_nonneg _
  fin_cases c
  · simp only [wvec]
    calc ‖y 0 • unitVector 0 + y 1 • unitVector 1‖ ≤ ‖y 0 • unitVector 0‖ + ‖y 1 • unitVector 1‖ := norm_add_le _ _
      _ = |y 0| + |y 1| := by rw [norm_smul, norm_smul, unit_norm, unit_norm, Real.norm_eq_abs, Real.norm_eq_abs,
            mul_one, mul_one]
      _ ≤ 2 * radialCoord y + 1 := by linarith
  · simp only [wvec]
    simp only [Fin.mk_one, one_ne_zero, if_false, if_true]
    calc ‖y 0 • unitVector 1 - y 1 • unitVector 0‖ ≤ ‖y 0 • unitVector 1‖ + ‖y 1 • unitVector 0‖ := norm_sub_le _ _
      _ = |y 0| + |y 1| := by rw [norm_smul, norm_smul, unit_norm, unit_norm, Real.norm_eq_abs, Real.norm_eq_abs,
            mul_one, mul_one]
      _ ≤ 2 * radialCoord y + 1 := by linarith
  · simp only [wvec]
    simp only [Fin.reduceFinMk, Fin.isValue, Fin.reduceEq, if_false]
    rw [unit_norm]
    linarith

theorem frame_w (y : Space) (c : Fin 3) (hc : c ≠ 2) : radialCoord y • frameVector c y = wvec c y := by
  have hcs : radialCoord y * Real.cos (angleCoord y) = y 0 := by
    rw [rad_cx, angleCoord]
    exact Complex.norm_mul_cos_arg _
  have hsn : radialCoord y * Real.sin (angleCoord y) = y 1 := by
    rw [rad_cx, angleCoord]
    exact Complex.norm_mul_sin_arg _
  fin_cases c
  · ext i
    fin_cases i <;> simp [frameVector, wvec, unitVector, hcs, hsn]
  · ext i
    fin_cases i <;> simp [frameVector, wvec, unitVector, hcs, hsn]
  · exact absurd rfl hc

theorem mem_iff (g : CellBlock) (hin : g.innerRadius = 0) (s : Fin 2) (y : Space) :
    y ∈ cellSolid g s ↔ radialCoord y ≤ g.outerRadius ∧ Internal.OnAxisNorm.zLow g s ≤ y 2 ∧
      y 2 ≤ Internal.OnAxisNorm.zHigh g s := by
  have hr : 0 ≤ radialCoord y := Real.sqrt_nonneg _
  simp only [cellSolid, Set.mem_ofPred_eq, hin, Internal.OnAxisNorm.zLow, Internal.OnAxisNorm.zHigh]
  fin_cases s
  · simp only [Fin.zero_eta, if_true]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hr, h1, h2, h3⟩
  · simp only [Fin.mk_one, one_ne_zero, if_false]
    constructor
    · rintro ⟨-, h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨hr, h1, by linarith, by linarith⟩

end Internal.AxisLiftSlope

open Internal.AxisLiftSlope Internal.OnAxisNorm in
theorem liftSlope_holds : LiftSlopeStatement := by
  intro g χ u ψ hin hmode hR hz hlow hχ1 hχL hu hend hu0 hψ
  obtain ⟨Kχ, hKχ⟩ := hχL
  set R := g.outerRadius with hRdef
  have hab : ∀ s : Fin 2, zLow g s ≤ zHigh g s := by
    intro s
    unfold zLow zHigh
    split_ifs <;> linarith
  have hρL : ∃ K, LipschitzWith K (fun y : Space => min (radialCoord y) R) :=
    ⟨_, rad_slope.min (LipschitzWith.const R)⟩
  have hρ0 : ∀ y : Space, 0 ≤ min (radialCoord y) R := fun y => le_min (Real.sqrt_nonneg _) hR.le
  have hρb : ∃ M, ∀ y : Space, |min (radialCoord y) R| ≤ M :=
    ⟨R, fun y => by rw [abs_of_nonneg (hρ0 y)]; exact min_le_right _ _⟩
  have hsL : ∃ K, LipschitzWith K (fun y : Space => R⁻¹ * min (radialCoord y) R) :=
    (bl_mul ⟨0, LipschitzWith.const _⟩ ⟨|R⁻¹|, fun _ => le_rfl⟩ hρL hρb).1
  have hsI : ∀ y : Space, R⁻¹ * min (radialCoord y) R ∈ Set.Icc (0 : ℝ) 1 := by
    intro y
    refine ⟨mul_nonneg (inv_nonneg.mpr hR.le) (hρ0 y), ?_⟩
    rw [inv_mul_le_iff₀ hR, mul_one]
    exact min_le_right _ _
  obtain ⟨Mχ, hMχ⟩ := isCompact_Icc.exists_bound_of_continuousOn hKχ.continuous.continuousOn
    (s := Set.Icc (0 : ℝ) 1)
  have hAL : ∃ K, LipschitzWith K (fun y : Space => χ (R⁻¹ * min (radialCoord y) R)) := by
    obtain ⟨K, hK⟩ := hsL
    exact ⟨_, hKχ.comp hK⟩
  have hAb : ∃ M, ∀ y : Space, |χ (R⁻¹ * min (radialCoord y) R)| ≤ M :=
    ⟨Mχ, fun y => by rw [← Real.norm_eq_abs]; exact hMχ _ (hsI y)⟩
  have hAsupp : ∀ y : Space, χ (R⁻¹ * min (radialCoord y) R) ≠ 0 → radialCoord y < R := by
    intro y hy
    by_contra hc
    push_neg at hc
    apply hy
    rw [min_eq_right hc, inv_mul_cancel₀ hR.ne', hχ1]
  have hBL : ∀ s c j, (∃ K, LipschitzWith K
      (fun y : Space => u s c j (max (zLow g s) (min (y 2) (zHigh g s))))) ∧
      ∃ M, ∀ y : Space, |u s c j (max (zLow g s) (min (y 2) (zHigh g s)))| ≤ M := by
    intro s c j
    obtain ⟨⟨K, hK⟩, M, hM⟩ := clamp_slope (hu s c j) (hab s)
    exact ⟨⟨_, hK.comp (coord_slope 2)⟩, M, fun y => hM _⟩
  have hid : ∀ y, ψ y = ∑ s : Fin 2, ∑ c : Fin 3, ∑ j ∈ Finset.range (g.degree + 1),
      (χ (R⁻¹ * min (radialCoord y) R) * u s c j (max (zLow g s) (min (y 2) (zHigh g s)))
        * min (radialCoord y) R ^ (if c = 2 then j else j - 1)) • wvec c y := by
    intro y
    rw [hψ y]
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hm : y ∈ cellSolid g s
    · rw [Set.indicator_of_mem hm]
      obtain ⟨h1, h2, h3⟩ := (mem_iff g hin s y).1 hm
      have hρ : min (radialCoord y) R = radialCoord y := min_eq_left h1
      have hcl : max (zLow g s) (min (y 2) (zHigh g s)) = y 2 := by
        rw [min_eq_left h3, max_eq_right h2]
      simp only [hρ, hcl, inv_mul_eq_div]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [Finset.mul_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hc : c = 2
      · subst hc
        simp only [if_true]
        rw [show frameVector 2 y = wvec 2 y by simp [frameVector, wvec]]
        congr 1
        ring
      · rw [if_neg hc]
        rcases Nat.eq_zero_or_pos j with hj | hj
        · subst hj
          rw [hu0 s c hc]
          simp
        · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
          rw [← frame_w y c hc, smul_smul]
          congr 1
          simp only [Nat.add_sub_cancel]
          ring
    · rw [Set.indicator_of_notMem hm]
      symm
      refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun j _ => ?_
      have hz0 : χ (R⁻¹ * min (radialCoord y) R) * u s c j (max (zLow g s) (min (y 2) (zHigh g s))) = 0 := by
        by_cases h1 : radialCoord y ≤ R
        · have hn : ¬ (zLow g s ≤ y 2 ∧ y 2 ≤ zHigh g s) := fun h => hm ((mem_iff g hin s y).2 ⟨h1, h.1, h.2⟩)
          have hu2 : u s c j (max (zLow g s) (min (y 2) (zHigh g s))) = 0 := by
            by_cases h2 : y 2 < zLow g s
            · rw [max_eq_left ((min_le_left _ _).trans h2.le)]
              exact (hend s c j).1
            · have h3 : zHigh g s < y 2 := by
                by_contra h3
                push_neg at h3 h2
                exact hn ⟨h2, h3⟩
              rw [min_eq_right h3.le, max_eq_right (hab s)]
              exact (hend s c j).2
          rw [hu2, mul_zero]
        · push_neg at h1
          rw [min_eq_right h1.le, inv_mul_cancel₀ hR.ne', hχ1, zero_mul]
      rw [hz0, zero_mul, zero_smul]
  have hψe : ψ = fun y => ∑ s : Fin 2, ∑ c : Fin 3, ∑ j ∈ Finset.range (g.degree + 1),
      (χ (R⁻¹ * min (radialCoord y) R) * u s c j (max (zLow g s) (min (y 2) (zHigh g s)))
        * min (radialCoord y) R ^ (if c = 2 then j else j - 1)) • wvec c y := funext hid
  refine ⟨?_, ?_⟩
  · rw [hψe]
    refine slope_sum _ _ fun s => slope_sum _ _ fun c => slope_sum _ _ fun j => ?_
    have h1 := bl_mul hAL hAb (hBL s c j).1 (hBL s c j).2
    have hS := bl_mul h1.1 h1.2 (pow_bl hρL hρb (if c = 2 then j else j - 1)).1
      (pow_bl hρL hρb (if c = 2 then j else j - 1)).2
    refine slope_smul hS.1 hS.2 (wvec_slope c) ⟨2 * R + 1, fun y hy => ?_⟩
    have hA : χ (R⁻¹ * min (radialCoord y) R) ≠ 0 := fun h => hy (by rw [h]; ring)
    have := hAsupp y hA
    linarith [wvec_bd c y]
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Space) (R + g.upperHeight)) fun y hy => ?_
    rw [hψ y]
    refine Finset.sum_eq_zero fun s _ => Set.indicator_of_notMem (fun hm => hy ?_) _
    obtain ⟨h1, h2, h3⟩ := (mem_iff g hin s y).1 hm
    have hz2 : |y 2| ≤ g.upperHeight := by
      rw [abs_le]
      simp only [zLow, zHigh] at h2 h3
      fin_cases s <;> simp at h2 h3 <;> constructor <;> linarith
    rw [Metric.mem_closedBall, dist_zero_right, EuclideanSpace.norm_eq]
    have hr0 : 0 ≤ radialCoord y := Real.sqrt_nonneg _
    have hrsq : radialCoord y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
    have hup : 0 ≤ g.upperHeight := by linarith
    have e1 : y 2 ^ 2 ≤ g.upperHeight ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hz2 2
    have e2 : radialCoord y ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hr0 h1 2
    calc √(∑ i : Fin 3, ‖y i‖ ^ 2) ≤ √((R + g.upperHeight) ^ 2) := by
          apply Real.sqrt_le_sqrt
          simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
          nlinarith
      _ = R + g.upperHeight := Real.sqrt_sq (by linarith)

end Spectral

end CellCert

end Breakdown

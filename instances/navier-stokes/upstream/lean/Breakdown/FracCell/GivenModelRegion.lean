import Breakdown.FracCell.GivenModelDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis

namespace GivenModelRegionInternal

theorem cylRadius_nonneg (y : Space) : 0 ≤ cylRadius y := Real.sqrt_nonneg _

theorem cylRadius_sq (y : Space) : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem norm_sq_eq (y : Space) : ‖y‖ ^ 2 = cylRadius y ^ 2 + cylHeight y ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), cylRadius_sq, cylHeight, Fin.sum_univ_three]
  simp [Real.norm_eq_abs, sq_abs]

theorem continuous_cylRadius : Continuous cylRadius := by
  unfold cylRadius
  fun_prop

theorem continuous_cylHeight : Continuous cylHeight := by
  unfold cylHeight
  fun_prop

theorem le_of_sq_le {a b : ℝ} (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h1 := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq hb] at h1
  exact (le_abs_self a).trans h1

theorem cylRadius_le_norm (y : Space) : cylRadius y ≤ ‖y‖ :=
  le_of_sq_le (norm_nonneg y) (by rw [norm_sq_eq]; nlinarith [sq_nonneg (cylHeight y)])

theorem abs_cylHeight_le_norm (y : Space) : |cylHeight y| ≤ ‖y‖ :=
  le_of_sq_le (norm_nonneg y) (by rw [norm_sq_eq, sq_abs]; nlinarith [sq_nonneg (cylRadius y)])

theorem measurableSet_solid (K : CellBox) : MeasurableSet K.solid := by
  have hρ := continuous_cylRadius.measurable
  have hh := (continuous_abs.comp continuous_cylHeight).measurable
  exact (measurableSet_le measurable_const hρ).inter ((measurableSet_le hρ measurable_const).inter
    ((measurableSet_le measurable_const hh).inter (measurableSet_le hh measurable_const)))

theorem region_eq (M : CellMesh) (hM : IsCellMesh M) :
    M.region = {y | cylRadius y ≤ M.outerSize ∧ |cylHeight y| ≤ M.outerSize} := by
  ext y
  simp only [CellMesh.region, Set.mem_iUnion, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨K, hK⟩
    simp only [CellBox.solid, Set.mem_ofPred_eq] at hK
    exact ⟨hK.2.1.trans (hM.boxes_inside K).1, hK.2.2.2.trans (hM.boxes_inside K).2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨K, hK⟩ := hM.boxes_cover (cylRadius y, |cylHeight y|) (cylRadius_nonneg y) h1 (abs_nonneg _) h2
    refine ⟨K, ?_⟩
    simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc] at hK
    simp only [CellBox.solid, Set.mem_ofPred_eq]
    exact ⟨hK.1.1, hK.1.2, hK.2.1, hK.2.2⟩

theorem cylRadius_turnStep (m : ℕ) (y : Space) : cylRadius (turnStep m y) = cylRadius y := by
  unfold cylRadius
  congr 1
  simp only [turnStep, PiLp.add_apply, PiLp.single_apply]
  simp
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * Real.pi / m)

theorem cylHeight_turnStep (m : ℕ) (y : Space) : cylHeight (turnStep m y) = cylHeight y := by
  simp [cylHeight, turnStep]

theorem cylRadius_mirror (y : Space) : cylRadius (mirror y) = cylRadius y := by
  simp [cylRadius, mirror]

theorem cylHeight_mirror (y : Space) : cylHeight (mirror y) = -cylHeight y := by
  simp [cylHeight, mirror]

def boxMax (y : Space) : ℝ := max (cylRadius y) |cylHeight y|

theorem continuous_boxMax : Continuous boxMax :=
  continuous_cylRadius.max (continuous_abs.comp continuous_cylHeight)

theorem boxMax_nonneg (y : Space) : 0 ≤ boxMax y := (cylRadius_nonneg y).trans (le_max_left _ _)

theorem boxMax_le_norm (y : Space) : boxMax y ≤ ‖y‖ :=
  max_le (cylRadius_le_norm y) (abs_cylHeight_le_norm y)

theorem norm_le_boxMax (y : Space) : ‖y‖ ≤ Real.sqrt 2 * boxMax y := by
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hρ : cylRadius y ≤ boxMax y := le_max_left _ _
  have hh : |cylHeight y| ≤ boxMax y := le_max_right _ _
  refine le_of_sq_le (mul_nonneg (Real.sqrt_nonneg 2) (boxMax_nonneg y)) ?_
  rw [norm_sq_eq, mul_pow, h2, ← sq_abs (cylHeight y)]
  have := cylRadius_nonneg y
  have := abs_nonneg (cylHeight y)
  nlinarith

theorem one_le_sqrt_two : (1 : ℝ) ≤ Real.sqrt 2 := by
  have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ 2 by norm_num)
  rwa [Real.sqrt_one] at this

theorem boxMax_smul (t : ℝ) (ht : 0 < t) (y : Space) : boxMax (t • y) = t * boxMax y := by
  have hρ : cylRadius (t • y) = t * cylRadius y := by
    unfold cylRadius
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [show (t * y 0) ^ 2 + (t * y 1) ^ 2 = t ^ 2 * (y 0 ^ 2 + y 1 ^ 2) by ring,
      Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht.le]
  have hh : |cylHeight (t • y)| = t * |cylHeight y| := by
    simp only [cylHeight, PiLp.smul_apply, smul_eq_mul, abs_mul, abs_of_pos ht]
  rw [boxMax, boxMax, hρ, hh, mul_max_of_nonneg _ _ ht.le]

theorem boxRadius_eq (L : ℝ) (y : Space) :
    boxRadius L y = if boxMax y = 0 then L else L * ‖y‖ / boxMax y := rfl

end GivenModelRegionInternal

open GivenModelRegionInternal

theorem cellRegion_clauses {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (hM : IsCellMesh M)
    (hR : c.cellRegion = M.region) :
    MeasurableSet c.cellRegion ∧ Bornology.IsBounded c.cellRegion ∧
      ∀ y ∈ c.cellRegion, turnStep c.order y ∈ c.cellRegion ∧ mirror y ∈ c.cellRegion := by
  rw [hR]
  refine ⟨MeasurableSet.iUnion fun K => measurableSet_solid _, ?_, ?_⟩
  · rw [region_eq M hM]
    refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := 2 * M.outerSize)).subset ?_
    rintro y ⟨h1, h2⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have := norm_le_boxMax y
    have h3 : boxMax y ≤ M.outerSize := max_le h1 h2
    have h4 : Real.sqrt 2 ≤ 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [boxMax_nonneg y, Real.sqrt_nonneg 2]
  · rw [region_eq M hM]
    rintro y ⟨h1, h2⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · rwa [cylRadius_turnStep]
    · rwa [cylHeight_turnStep]
    · rwa [cylRadius_mirror]
    · rwa [cylHeight_mirror, abs_neg]

theorem exterior_clauses {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (hM : IsCellMesh M)
    (hR : c.cellRegion = M.region) (e : Exterior.ExteriorData) (he : e.radius = boxRadius M.outerSize)
    (hmin : e.radiusMin = M.outerSize) (hmax : e.radiusMax = Real.sqrt 2 * M.outerSize) :
    Measurable e.radius ∧ 0 < e.radiusMin ∧ (∀ y, e.radiusMin ≤ e.radius y ∧ e.radius y ≤ e.radiusMax) ∧
      (∀ (t : ℝ) (y : Space), 0 < t → e.radius (t • y) = e.radius y) ∧
      c.cellRegionᶜ =ᵐ[volume] {y : Space | e.radius y < ‖y‖} := by
  have hL := hM.outerSize_pos
  rw [he, hmin, hmax]
  refine ⟨?_, hL, ?_, ?_, ?_⟩
  · have hDm := continuous_boxMax.measurable
    have : boxRadius M.outerSize = fun y => if boxMax y = 0 then M.outerSize else M.outerSize * ‖y‖ / boxMax y :=
      funext (boxRadius_eq _)
    rw [this]
    exact Measurable.ite (measurableSet_eq_fun hDm measurable_const) measurable_const
      ((measurable_const.mul measurable_norm).div hDm)
  · intro y
    rw [boxRadius_eq]
    split_ifs with hD
    · exact ⟨le_rfl, le_mul_of_one_le_left hL.le one_le_sqrt_two⟩
    · have hDp : 0 < boxMax y := lt_of_le_of_ne (boxMax_nonneg y) (Ne.symm hD)
      constructor
      · rw [le_div_iff₀ hDp]
        exact mul_le_mul_of_nonneg_left (boxMax_le_norm y) hL.le
      · rw [div_le_iff₀ hDp]
        have := mul_le_mul_of_nonneg_left (norm_le_boxMax y) hL.le
        nlinarith
  · intro t y ht
    rw [boxRadius_eq, boxRadius_eq, boxMax_smul t ht y, norm_smul, Real.norm_of_nonneg ht.le]
    by_cases hD : boxMax y = 0
    · simp [hD]
    · have ht0 : t ≠ 0 := ht.ne'
      rw [if_neg (mul_ne_zero ht0 hD), if_neg hD]
      field_simp
  · have hset : (M.region)ᶜ = {y : Space | boxRadius M.outerSize y < ‖y‖} := by
      ext y
      rw [region_eq M hM]
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      rw [boxRadius_eq]
      have hiff : ¬(cylRadius y ≤ M.outerSize ∧ |cylHeight y| ≤ M.outerSize) ↔ M.outerSize < boxMax y := by
        rw [boxMax, lt_max_iff, not_and_or, not_le, not_le]
      rw [hiff]
      split_ifs with hD
      · have h0 : ‖y‖ ≤ 0 := by have := norm_le_boxMax y; rw [hD, mul_zero] at this; exact this
        rw [hD]
        constructor
        · intro h; linarith
        · intro h; linarith [norm_nonneg y]
      · have hDp : 0 < boxMax y := lt_of_le_of_ne (boxMax_nonneg y) (Ne.symm hD)
        have hn : 0 < ‖y‖ := hDp.trans_le (boxMax_le_norm y)
        rw [div_lt_iff₀ hDp]
        constructor
        · intro h; nlinarith
        · intro h; nlinarith
    refine Filter.Eventually.of_forall fun y => ?_
    show (y ∈ c.cellRegionᶜ) = (y ∈ {y : Space | boxRadius M.outerSize y < ‖y‖})
    rw [hR, hset]

end GivenModel

namespace GivenModel

open SteadyCert CellAnalysis CellFormula

theorem ball_subset_region (M : CellMesh) (hM : IsCellMesh M) :
    ∀ y : Space, ‖y‖ ≤ M.outerSize → y ∈ M.region := by
  intro y hy
  rw [GivenModelRegionInternal.region_eq M hM]
  exact ⟨(GivenModelRegionInternal.cylRadius_le_norm y).trans hy, (GivenModelRegionInternal.abs_cylHeight_le_norm y).trans hy⟩

end GivenModel

end CellCert

end Breakdown

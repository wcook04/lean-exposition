import Breakdown.FracCell.CellSystemDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellSystem


open SteadyCert Assembly Reduction GivenFields GivenModel Exterior Spectral CellAnalysis CellCoordinates CellFormula

private theorem turnBy_two (φ : ℝ) (y : Space) : turnBy φ y 2 = y 2 := by
  simp [turnBy]

private theorem horizontalNorm_turnBy (φ : ℝ) (y : Space) : horizontalNorm (turnBy φ y) = horizontalNorm y := by
  unfold horizontalNorm
  congr 1
  simp [turnBy]
  have := Real.sin_sq_add_cos_sq φ
  nlinarith [this]

private theorem norm_turnBy (φ : ℝ) (y : Space) : ‖turnBy φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  simp [turnBy]
  have := Real.sin_sq_add_cos_sq φ
  nlinarith [this]

private theorem mirror_two (y : Space) : mirror y 2 = -(y 2) := by
  simp [mirror]

private theorem horizontalNorm_mirror (y : Space) : horizontalNorm (mirror y) = horizontalNorm y := by
  unfold horizontalNorm
  simp [mirror]

private theorem measurable_horizontalNorm : Measurable horizontalNorm := by
  unfold horizontalNorm
  fun_prop

private theorem measurable_coord_two : Measurable (fun y : Space => y 2) := by
  fun_prop

private theorem pieceSolidOf_measurable (lo : ℝ) (hi : Option ℝ) (zlo : ℝ) (zhi : Option ℝ) :
    MeasurableSet (pieceSolidOf lo hi zlo zhi) := by
  have h1 : MeasurableSet {y : Space | lo ≤ horizontalNorm y} := measurableSet_le measurable_const measurable_horizontalNorm
  have h3 : MeasurableSet {y : Space | zlo ≤ y 2} := measurableSet_le measurable_const measurable_coord_two
  cases hi with
  | none =>
    cases zhi with
    | none =>
      have : pieceSolidOf lo none zlo none = {y | lo ≤ horizontalNorm y} ∩ {y | zlo ≤ y 2} := by
        ext y; simp [pieceSolidOf]
      rw [this]; exact h1.inter h3
    | some b =>
      have : pieceSolidOf lo none zlo (some b) = {y | lo ≤ horizontalNorm y} ∩ ({y | zlo ≤ y 2} ∩ {y | y 2 ≤ b}) := by
        ext y; simp [pieceSolidOf]
      rw [this]; exact h1.inter (h3.inter (measurableSet_le measurable_coord_two measurable_const))
  | some a =>
    cases zhi with
    | none =>
      have : pieceSolidOf lo (some a) zlo none = ({y | lo ≤ horizontalNorm y} ∩ {y | horizontalNorm y ≤ a}) ∩ {y | zlo ≤ y 2} := by
        ext y; simp [pieceSolidOf, and_assoc]
      rw [this]; exact (h1.inter (measurableSet_le measurable_horizontalNorm measurable_const)).inter h3
    | some b =>
      have : pieceSolidOf lo (some a) zlo (some b) = ({y | lo ≤ horizontalNorm y} ∩ {y | horizontalNorm y ≤ a}) ∩
          ({y | zlo ≤ y 2} ∩ {y | y 2 ≤ b}) := by
        ext y; simp [pieceSolidOf, and_assoc]
      rw [this]
      exact (h1.inter (measurableSet_le measurable_horizontalNorm measurable_const)).inter
        (h3.inter (measurableSet_le measurable_coord_two measurable_const))

private theorem chartSolid_measurable (L t₀ t₁ x₀ x₁ : ℝ) : MeasurableSet (chartSolid L t₀ t₁ x₀ x₁) := by
  have hq : Measurable (fun y : Space => ‖y‖ / (‖y‖ + L)) := by fun_prop
  have hn : Measurable (fun y : Space => ‖y‖) := by fun_prop
  have : chartSolid L t₀ t₁ x₀ x₁ = ({y | t₀ ≤ ‖y‖ / (‖y‖ + L)} ∩ {y | ‖y‖ / (‖y‖ + L) ≤ t₁}) ∩
      ({y | x₀ * ‖y‖ ≤ y 2} ∩ {y | y 2 ≤ x₁ * ‖y‖}) := by
    ext y; simp [chartSolid, and_assoc]
  rw [this]
  exact ((measurableSet_le measurable_const hq).inter (measurableSet_le hq measurable_const)).inter
    ((measurableSet_le (measurable_const.mul hn) measurable_coord_two).inter
      (measurableSet_le measurable_coord_two (measurable_const.mul hn)))

private theorem pieceSolid_measurable (T : CellSumValues) (b : Fin T.pieceCount) : MeasurableSet (T.pieceSolid b) := by
  unfold CellSumValues.pieceSolid
  rcases T.pieceChart b with _ | ⟨t₀, t₁, x₀, x₁⟩
  · exact pieceSolidOf_measurable _ _ _ _
  · exact chartSolid_measurable _ _ _ _ _

private theorem pieceSolid_turn (T : CellSumValues) (b : Fin T.pieceCount) (φ : ℝ) (y : Space) :
    y ∈ T.pieceSolid b ↔ turnBy φ y ∈ T.pieceSolid b := by
  unfold CellSumValues.pieceSolid
  rcases T.pieceChart b with _ | ⟨t₀, t₁, x₀, x₁⟩
  · simp only [pieceSolidOf, Set.mem_setOf_eq, horizontalNorm_turnBy, turnBy_two]
  · simp only [chartSolid, Set.mem_setOf_eq, norm_turnBy, turnBy_two]

private theorem pieceSolid_box (m : ℕ) (T : CellSumValues) (h₁ : IsCellSumValues m T) (b : Fin T.pieceCount) :
    ∀ y ∈ T.pieceSolid b, T.pieceRhoLo b ≤ horizontalNorm y ∧
      (∀ h, T.pieceRhoHi b = some h → horizontalNorm y ≤ h) ∧ T.pieceZLo b ≤ y 2 ∧
      (∀ h, T.pieceZHi b = some h → y 2 ≤ h) := by
  intro y hy
  unfold CellSumValues.pieceSolid at hy
  rcases hc : T.pieceChart b with _ | ⟨t₀, t₁, x₀, x₁⟩
  · rw [hc] at hy; exact hy
  · rw [hc] at hy; exact (h₁.chart_box b t₀ t₁ x₀ x₁ hc).2 y hy

private theorem foldl_inv {α β : Type} (P : β → Prop) (g : Option β → α → Option β)
    (hg : ∀ acc f l, (∀ l', acc = some l' → P l') → g acc f = some l → P l) :
    ∀ (fs : List α) (acc : Option β), (∀ l', acc = some l' → P l') → ∀ l, fs.foldl g acc = some l → P l := by
  intro fs
  induction fs with
  | nil => intro acc hacc l h; exact hacc l h
  | cons f fs ih =>
    intro acc hacc l h
    simp only [List.foldl_cons] at h
    exact ih _ (fun l' h' => hg acc f l' hacc h') l h

private theorem bestNear_valid (T : CellSumValues) (m : ℕ) (a : Fin T.boxCount) (b : Fin T.pieceCount) (mirrored : Bool)
    (l : ℝ) (hl : T.bestNear m a b mirrored = some l) : T.NearValid m a b l := by
  classical
  unfold CellSumValues.bestNear at hl
  refine foldl_inv (T.NearValid m a b) _ ?_ _ none (fun _ h => by simp at h) l hl
  intro acc f l' hacc h
  dsimp only at h
  split_ifs at h with hv
  · rcases acc with _ | l₀
    · simp only [Option.some.injEq] at h; rw [← h]; exact hv
    · dsimp only at h
      split_ifs at h with hlt
      · simp only [Option.some.injEq] at h; rw [← h]; exact hv
      · simp only [Option.some.injEq] at h; rw [← h]; exact hacc l₀ rfl
  · exact hacc l' h

private theorem toData_near_valid (T : CellSumValues) (m : ℕ) : ∀ a b mirrored, (T.toData m).rule a b mirrored = 2 →
    0 < (T.toData m).sectorLength a b mirrored ∧ 0 < (T.toData m).sectorConst m a b ∧
      ((T.toData m).pieceRhoHi b).isSome ∧ ((T.toData m).pieceZHi b).isSome := by
  intro a b mirrored h
  show 0 < T.lengthOf m a b mirrored ∧ 0 < T.baseData.sectorConst m a b ∧ (T.pieceRhoHi b).isSome ∧ (T.pieceZHi b).isSome
  change T.ruleOf m a b mirrored = 2 at h
  unfold CellSumValues.ruleOf at h
  rcases hb : T.bestNear m a b mirrored with _ | l
  · rw [hb] at h
    dsimp only at h
    split_ifs at h <;> exact absurd h (by decide)
  · have hv := bestNear_valid T m a b mirrored l hb
    unfold CellSumValues.lengthOf
    rw [hb]
    exact hv

private theorem cellSumData_holds (m : ℕ) (V : Space → ℝ) (T : CellSumValues) (h₁ : IsCellSumValues m T)
    (h₂ : IsCellSumBounded m V T) (h₃ : IsSumWeight m V) : IsCellSumData m V (T.toData m) where
  order_even := h₁.order_even
  measurable := h₃.measurable
  nonneg := h₃.nonneg
  turn_invariant := h₃.turn_invariant
  mirror_even := h₃.mirror_even
  piece_box := h₁.piece_box
  piece_solid := pieceSolid_box m T h₁
  solid_measurable := pieceSolid_measurable T
  solid_turn := pieceSolid_turn T
  sup_le := h₂.sup_le
  sup_nonneg := h₁.sup_nonneg
  mass_integrable := fun _ => h₃.integrable.integrableOn
  mass_le := h₂.mass_le
  support := by
    intro y _
    by_cases hz : 0 ≤ y 2
    · obtain ⟨b, hb⟩ := h₁.pieces_cover y hz
      exact ⟨b, Or.inl hb⟩
    · have hz' : 0 ≤ mirror y 2 := by rw [mirror_two]; linarith [lt_of_not_ge hz]
      obtain ⟨b, hb⟩ := h₁.pieces_cover (mirror y) hz'
      exact ⟨b, Or.inr hb⟩
  box_cover := h₁.box_cover
  box_lower := h₁.box_lower
  near_valid := toData_near_valid T m
  box_sum := h₂.box_sum


theorem cellSumData_of (m : ℕ) (V : Space → ℝ) (T : CellSumValues) (h₁ : IsCellSumValues m T)
    (h₂ : IsCellSumBounded m V T) (h₃ : IsSumWeight m V) : IsCellSumData m V (T.toData m) := by
  exact cellSumData_holds m V T h₁ h₂ h₃

end CellSystem

end CellCert

end Breakdown

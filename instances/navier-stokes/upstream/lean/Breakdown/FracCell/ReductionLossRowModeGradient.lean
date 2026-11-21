import Breakdown.FracCell.ReductionLossDefs

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def CellAngularBoundStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N), IsRowTurnData c T →
    ∀ v G H, IsSecondOrderField c.order v G H → ∀ i : ℕ,
      (∑ a ∈ Finset.univ.filter (fun a => T.cellOf a = i),
          ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair v (c.row a) ^ 2)
        ≤ ∫ y in T.cellSet i, ‖G y (axialTurn y)‖ ^ 2

def RotationDifferenceStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ S : Set Space, MeasurableSet S → Bornology.IsBounded S → (∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) →
      ∀ φ : ℝ, (∫ y in S, ‖v (turnBy φ y) - v y‖ ^ 2) ≤ φ ^ 2 * ∫ y in S, ‖G y (axialTurn y)‖ ^ 2

def RowRotationCoefEnergyStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (T : RowTurnData N), IsRowTurnData c T →
    ∀ (i : ℕ) (f : Space → Space), MemLp f 2 (volume.restrict (T.cellSet i)) → ∀ X : ℝ,
      (∀ φ : ℝ, (∫ y in T.cellSet i, ‖f (turnBy φ y) - f y‖ ^ 2) ≤ φ ^ 2 * X) →
        (∑ a ∈ Finset.univ.filter (fun a => T.cellOf a = i),
            ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair f (c.row a) ^ 2) ≤ X

namespace RowModeGradientInternal

theorem axialTurn_eq (y : Space) :
    axialTurn y = (-(y 1)) • unitVector 0 + (y 0) • unitVector 1 := by
  ext j
  fin_cases j <;> simp [axialTurn, unitVector]

theorem turn_sq_le (M : Space →L[ℝ] Space) (y : Space) :
    ‖M (axialTurn y)‖ ^ 2 ≤ horizontalNorm y ^ 2 * entrySq M := by
  have hh : horizontalNorm y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [horizontalNorm, Real.sq_sqrt (by positivity)]
  have he : ‖M (unitVector 0)‖ ^ 2 + ‖M (unitVector 1)‖ ^ 2 ≤ entrySq M := by
    rw [entrySq, Fin.sum_univ_three]
    nlinarith [sq_nonneg ‖M (unitVector 2)‖]
  have hn : ‖M (axialTurn y)‖ ≤ |y 1| * ‖M (unitVector 0)‖ + |y 0| * ‖M (unitVector 1)‖ := by
    rw [axialTurn_eq, map_add, map_smul, map_smul]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_neg]
  have h0 : 0 ≤ ‖M (axialTurn y)‖ := norm_nonneg _
  have hcs : (|y 1| * ‖M (unitVector 0)‖ + |y 0| * ‖M (unitVector 1)‖) ^ 2 ≤
      (y 0 ^ 2 + y 1 ^ 2) * (‖M (unitVector 0)‖ ^ 2 + ‖M (unitVector 1)‖ ^ 2) := by
    have a0 : |y 0| ^ 2 = y 0 ^ 2 := sq_abs _
    have a1 : |y 1| ^ 2 = y 1 ^ 2 := sq_abs _
    nlinarith [sq_nonneg (|y 1| * ‖M (unitVector 1)‖ - |y 0| * ‖M (unitVector 0)‖)]
  calc ‖M (axialTurn y)‖ ^ 2
      ≤ (|y 1| * ‖M (unitVector 0)‖ + |y 0| * ‖M (unitVector 1)‖) ^ 2 := pow_le_pow_left₀ h0 hn 2
    _ ≤ (y 0 ^ 2 + y 1 ^ 2) * (‖M (unitVector 0)‖ ^ 2 + ‖M (unitVector 1)‖ ^ 2) := hcs
    _ ≤ horizontalNorm y ^ 2 * entrySq M := by
        rw [hh]; exact mul_le_mul_of_nonneg_left he (by positivity)

theorem entrySq_nonneg (M : Space →L[ℝ] Space) : 0 ≤ entrySq M := by
  unfold entrySq; positivity

theorem cell_turn_le {E : Space → ℝ} {G : Space → (Space →L[ℝ] Space)} (hE : ∀ y, E y = entrySq (G y))
    (hEi : Integrable E) (S : Set Space) (hS : MeasurableSet S) (ρ : ℝ)
    (hρ : ∀ y ∈ S, horizontalNorm y ≤ ρ) :
    (∫ y in S, ‖G y (axialTurn y)‖ ^ 2) ≤ ρ ^ 2 * ∫ y in S, E y := by
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
    (hEi.integrableOn.const_mul _) ?_
  refine (ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun y hy => ?_)
  have h1 := turn_sq_le (G y) y
  have h2 : horizontalNorm y ^ 2 ≤ ρ ^ 2 := by
    have : 0 ≤ horizontalNorm y := Real.sqrt_nonneg _
    exact pow_le_pow_left₀ this (hρ y hy) 2
  show ‖G y (axialTurn y)‖ ^ 2 ≤ ρ ^ 2 * E y
  rw [hE y]
  exact h1.trans (mul_le_mul_of_nonneg_right h2 (entrySq_nonneg _))

theorem sum_cells_le {E : Space → ℝ} (hE0 : ∀ y, 0 ≤ E y) (hEi : Integrable E) (C : ℕ → Set Space)
    (hC : ∀ i, MeasurableSet (C i)) (hd : ∀ i j, i ≠ j → volume (C i ∩ C j) = 0) (I : Finset ℕ) :
    (∑ i ∈ I, ∫ y in C i, E y) ≤ ∫ y, E y := by
  have hind : ∀ i ∈ I, Integrable ((C i).indicator E) := fun i _ => hEi.indicator (hC i)
  calc (∑ i ∈ I, ∫ y in C i, E y) = ∑ i ∈ I, ∫ y, (C i).indicator E y := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_indicator (hC i)]
    _ = ∫ y, ∑ i ∈ I, (C i).indicator E y := (integral_finsetSum I hind).symm
    _ ≤ ∫ y, E y := by
        refine integral_mono_ae (integrable_finsetSum I hind) hEi ?_
        have hae : ∀ᵐ y ∂volume, ∀ p : ℕ × ℕ, p.1 ≠ p.2 → y ∉ C p.1 ∩ C p.2 := by
          rw [ae_all_iff]
          intro p
          by_cases hp : p.1 = p.2
          · exact Filter.Eventually.of_forall fun y h => absurd hp h
          · filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hd p.1 p.2 hp)] with y hy _ using hy
        filter_upwards [hae] with y hy
        by_cases hex : ∃ i₀ ∈ I, y ∈ C i₀
        · obtain ⟨i₀, hi₀, hy₀⟩ := hex
          rw [Finset.sum_eq_single i₀]
          · rw [Set.indicator_of_mem hy₀]
          · intro j _ hj
            have hyj : y ∉ C j := fun hyj => hy (j, i₀) hj ⟨hyj, hy₀⟩
            rw [Set.indicator_of_notMem hyj]
          · intro h; exact absurd hi₀ h
        · push Not at hex
          rw [Finset.sum_eq_zero fun i hi => Set.indicator_of_notMem (hex i hi) _]
          exact hE0 y

end RowModeGradientInternal

open RowModeGradientInternal in
theorem rowModeGradient_of (h : CellAngularBoundStatement) : RowModeGradientStatement := by
  intro k N c T hT v G H hv
  set w : Fin N → ℝ := fun a => ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair v (c.row a) ^ 2 with hw
  set E : Space → ℝ := fun y => entrySq (G y) with hEdef
  set R := T.rateRowConst
  have hE0 : ∀ y, 0 ≤ E y := fun y => entrySq_nonneg _
  have hEi : Integrable E := hv.gradient_two
  have hw0 : ∀ a, 0 ≤ w a := fun a => by simp only [hw]; positivity
  have hwz : ∀ a, T.modeNum a = 0 → w a = 0 := by
    intro a ha
    simp only [hw, ha, Int.cast_zero, abs_zero, zero_sub]
    norm_num
  have hcell : ∀ i, (∑ a ∈ Finset.univ.filter (fun a => T.cellOf a = i), c.rowWeight a * w a)
      ≤ R ^ 2 * ∫ y in T.cellSet i, E y := by
    intro i
    set F := Finset.univ.filter (fun a => T.cellOf a = i)
    set ρ := T.outerRadius i
    have hB : (∑ a ∈ F, w a) ≤ ρ ^ 2 * ∫ y in T.cellSet i, E y :=
      (h c T hT v G H hv i).trans
        (cell_turn_le (fun y => rfl) hEi (T.cellSet i) (hT.cell_measurable i) ρ (hT.cell_radius i))
    have hI0 : 0 ≤ ∫ y in T.cellSet i, E y := setIntegral_nonneg (hT.cell_measurable i) fun y _ => hE0 y
    have hterm : ∀ a ∈ F, ρ ^ 2 * (c.rowWeight a * w a) ≤ R ^ 2 * w a := by
      intro a ha
      have hca : T.cellOf a = i := (Finset.mem_filter.1 ha).2
      by_cases hk : T.modeNum a = 0
      · rw [hwz a hk]; simp
      · have h1 := (hT.const_ge.2 a hk)
        rw [hca] at h1
        have : ρ ^ 2 * (c.rowWeight a * w a) = (c.rowWeight a * ρ ^ 2) * w a := by ring
        rw [this]
        exact mul_le_mul_of_nonneg_right h1 (hw0 a)
    have hmain : ρ ^ 2 * (∑ a ∈ F, c.rowWeight a * w a) ≤ ρ ^ 2 * (R ^ 2 * ∫ y in T.cellSet i, E y) := by
      rw [Finset.mul_sum]
      calc (∑ a ∈ F, ρ ^ 2 * (c.rowWeight a * w a)) ≤ ∑ a ∈ F, R ^ 2 * w a := Finset.sum_le_sum hterm
        _ = R ^ 2 * ∑ a ∈ F, w a := (Finset.mul_sum _ _ _).symm
        _ ≤ R ^ 2 * (ρ ^ 2 * ∫ y in T.cellSet i, E y) := mul_le_mul_of_nonneg_left hB (sq_nonneg _)
        _ = ρ ^ 2 * (R ^ 2 * ∫ y in T.cellSet i, E y) := by ring
    rcases (sq_nonneg ρ).lt_or_eq with hpos | hzero
    · exact le_of_mul_le_mul_left hmain hpos
    · have hB0 : (∑ a ∈ F, w a) ≤ 0 := by rw [← hzero] at hB; simpa using hB
      have hall : ∀ a ∈ F, w a = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun a _ => hw0 a).1
          (le_antisymm hB0 (Finset.sum_nonneg fun a _ => hw0 a))
      rw [Finset.sum_eq_zero fun a ha => by rw [hall a ha, mul_zero]]
      exact mul_nonneg (sq_nonneg _) hI0
  have hlhs : (∑ a, c.rowWeight a * ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * l2Pair v (c.row a) ^ 2)
      = ∑ i ∈ Finset.univ.image T.cellOf,
          ∑ a ∈ Finset.univ.filter (fun a => T.cellOf a = i), c.rowWeight a * w a := by
    rw [Finset.sum_fiberwise_of_maps_to (fun a _ => Finset.mem_image_of_mem T.cellOf (Finset.mem_univ a))]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [hw]; ring
  rw [hlhs]
  calc _ ≤ ∑ i ∈ Finset.univ.image T.cellOf, R ^ 2 * ∫ y in T.cellSet i, E y := Finset.sum_le_sum fun i _ => hcell i
    _ = R ^ 2 * ∑ i ∈ Finset.univ.image T.cellOf, ∫ y in T.cellSet i, E y := (Finset.mul_sum _ _ _).symm
    _ ≤ R ^ 2 * ∫ y, E y := mul_le_mul_of_nonneg_left
        (sum_cells_le hE0 hEi T.cellSet hT.cell_measurable hT.cell_disjoint _) (sq_nonneg _)

theorem cellAngularBound_of (h1 : RotationDifferenceStatement) (h2 : RowRotationCoefEnergyStatement) :
    CellAngularBoundStatement := by
  intro k N c T hT v G H hv i
  have hfin : IsFiniteMeasure (volume.restrict (T.cellSet i)) :=
    isFiniteMeasure_restrict.2 (hT.cell_bounded i).measure_lt_top.ne
  have hL2 : MemLp v 2 (volume.restrict (T.cellSet i)) :=
    (hv.velocity_six.restrict _).mono_exponent (by norm_num)
  exact h2 c T hT i v hL2 _ (h1 c.order v G H hv (T.cellSet i) (hT.cell_measurable i) (hT.cell_bounded i)
    (hT.cell_turn i))

theorem rowModeGradient_of_parts (h1 : RotationDifferenceStatement) (h2 : RowRotationCoefEnergyStatement) :
    RowModeGradientStatement :=
  rowModeGradient_of (cellAngularBound_of h1 h2)

end Reduction

end CellCert

end Breakdown

import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCell.RowTurnPair

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

private theorem mode_sq_le {m : ℝ} (hm : 2 ≤ m) (x : ℝ) (hx : x ≠ 0 → m ≤ |x|) :
    x ^ 2 ≤ (m / (m - 1)) ^ 2 * ((|x| - 1) ⊔ 0) ^ 2 := by
  by_cases h0 : x = 0
  · subst h0
    simp
  · have hxm := hx h0
    have hmax : (|x| - 1) ⊔ 0 = |x| - 1 := sup_eq_left.mpr (by linarith)
    rw [hmax, ← mul_pow, ← sq_abs x]
    have hpos : 0 < m - 1 := by linarith
    have hle : |x| ≤ m / (m - 1) * (|x| - 1) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hpos]
      nlinarith
    exact pow_le_pow_left₀ (abs_nonneg x) hle 2

private theorem pair_smul (r : ℝ) (F E : Space → Space) :
    l2Pair (fun y => r • F y) E = r * l2Pair F E := by
  unfold l2Pair
  simp_rw [inner_smul_left]
  simp only [conj_trivial]
  exact integral_const_mul r _

private theorem sum_partner {N : ℕ} (σ : Fin N → Fin N) (hσ : ∀ a, σ (σ a) = a) (f : Fin N → ℝ) :
    ∑ a, f (σ a) = ∑ a, f a :=
  Equiv.sum_comp (Function.Involutive.toPerm σ hσ) f

private theorem energy_ge {k N : ℕ} (c : FracCellData k N) (hw : 0 < c.weightMin)
    (hlow : ∀ y, c.weightMin ≤ c.weight y) (hmeas : Measurable c.weight) (hhigh : ∀ y, c.weight y ≤ c.weightMax)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsSecondOrderField c.order v G H) :
    c.weightMin * ∫ y, entrySq (G y) ≤ c.energy G H := by
  have hI : Integrable (fun y => entrySq (G y)) := hv.gradient_two
  have hwI : Integrable (fun y => c.weight y * entrySq (G y)) := by
    refine hI.bdd_mul (c := c.weightMax) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (lt_of_lt_of_le hw (hlow y))]
    exact hhigh y
  have h1 : c.weightMin * ∫ y, entrySq (G y) ≤ ∫ y, c.weight y * entrySq (G y) := by
    rw [← integral_const_mul]
    refine integral_mono (hI.const_mul _) hwI fun y => ?_
    have : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun i _ => sq_nonneg _
    exact mul_le_mul_of_nonneg_right (hlow y) this
  have h2 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  show c.weightMin * ∫ y, entrySq (G y) ≤ SteadyCert.weightedEnergy c.weight G H
  unfold SteadyCert.weightedEnergy
  linarith

theorem rateLoss_of_rows (hM : RowModeGradientStatement) {k N : ℕ} (c : FracCellData k N)
    (hw : 0 < c.weightMin) (hlow : ∀ y, c.weightMin ≤ c.weight y)
    (hmeas : Measurable c.weight) (hhigh : ∀ y, c.weight y ≤ c.weightMax) (T : RowTurnData N) (hT : IsRowTurnData c T)
    (hbound : ∀ p ∈ box c.radius, |c.rotationRate p - c.modelRate| * ((c.order : ℝ) / ((c.order : ℝ) - 1))
      * T.rateRowConst ≤ c.rateLoss * Real.sqrt c.weightMin) :
    ∀ p ∈ box c.radius, ∀ v G H, IsSecondOrderField c.order v G H →
      c.toFracCertData.rows (fun y => (c.rotationRate p - c.modelRate) • (G y (axialTurn y) - axialTurn (v y)))
        ≤ c.rateLoss * Real.sqrt (c.energy G H) := by
  intro p hp v G H hv
  set Δ := c.rotationRate p - c.modelRate with hΔ
  set m : ℝ := (c.order : ℝ) with hm
  set R := T.rateRowConst with hR
  set I := ∫ y, entrySq (G y) with hI
  set P : Fin N → ℝ := fun a => l2Pair v (c.row a) with hP
  have hm2 : (2 : ℝ) ≤ m := by
    rw [hm]
    exact_mod_cast hT.order_ge
  have hI0 : 0 ≤ I := integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hterm : ∀ a, c.rowWeight a * l2Pair (fun y => Δ • (G y (axialTurn y) - axialTurn (v y))) (c.row a) ^ 2
      = Δ ^ 2 * (c.rowWeight (T.partner a) * (T.modeNum (T.partner a) : ℝ) ^ 2 * P (T.partner a) ^ 2) := by
    intro a
    rw [pair_smul, turnPair_row c T hT hv a, hT.partner_weight, hT.partner_mode]
    simp only [hP, Int.cast_neg]
    ring
  have hsum : c.toFracCertData.rows (fun y => Δ • (G y (axialTurn y) - axialTurn (v y))) ^ 2
      = Δ ^ 2 * ∑ a, c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2 := by
    have hnn : 0 ≤ ∑ a, c.rowWeight a * l2Pair (fun y => Δ • (G y (axialTurn y) - axialTurn (v y))) (c.row a) ^ 2 :=
      Finset.sum_nonneg fun a _ => mul_nonneg (hT.weight_nonneg a) (sq_nonneg _)
    show rowSize c.row c.rowWeight _ ^ 2 = _
    unfold rowSize
    rw [Real.sq_sqrt hnn, Finset.sum_congr rfl fun a _ => hterm a, ← Finset.mul_sum]
    congr 1
    exact sum_partner T.partner hT.partner_invol
      (fun a => c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2)
  have hS : ∑ a, c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2 ≤ (m / (m - 1)) ^ 2 * (R ^ 2 * I) := by
    have hM' := hM c T hT v G H hv
    calc ∑ a, c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2
        ≤ ∑ a, (m / (m - 1)) ^ 2 * (c.rowWeight a * ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * P a ^ 2) := by
          refine Finset.sum_le_sum fun a _ => ?_
          have hk := mode_sq_le hm2 (T.modeNum a : ℝ) fun h => hT.mode_large a (Int.cast_ne_zero.mp h)
          have hτ := hT.weight_nonneg a
          have hP2 := sq_nonneg (P a)
          calc c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2
              ≤ c.rowWeight a * ((m / (m - 1)) ^ 2 * ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2) * P a ^ 2 :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk hτ) hP2
            _ = _ := by ring
      _ = (m / (m - 1)) ^ 2 * ∑ a, c.rowWeight a * ((|(T.modeNum a : ℝ)| - 1) ⊔ 0) ^ 2 * P a ^ 2 :=
          (Finset.mul_sum _ _ _).symm
      _ ≤ (m / (m - 1)) ^ 2 * (R ^ 2 * I) := mul_le_mul_of_nonneg_left hM' (sq_nonneg _)
  have hR0 : 0 ≤ R := hT.const_ge.1
  have hq0 : 0 ≤ m / (m - 1) := div_nonneg (by linarith) (by linarith)
  set X := |Δ| * (m / (m - 1)) * R with hX
  have hX0 : 0 ≤ X := mul_nonneg (mul_nonneg (abs_nonneg _) hq0) hR0
  set rowsVal := c.toFracCertData.rows (fun y => Δ • (G y (axialTurn y) - axialTurn (v y))) with hrowsVal
  have hrw0 : 0 ≤ rowsVal := Real.sqrt_nonneg _
  have hrows : rowsVal ≤ X * Real.sqrt I := by
    refine (pow_le_pow_iff_left₀ hrw0 (mul_nonneg hX0 (Real.sqrt_nonneg _)) two_ne_zero).mp ?_
    rw [hsum, mul_pow, Real.sq_sqrt hI0, hX, mul_pow, mul_pow, sq_abs]
    calc Δ ^ 2 * ∑ a, c.rowWeight a * (T.modeNum a : ℝ) ^ 2 * P a ^ 2
        ≤ Δ ^ 2 * ((m / (m - 1)) ^ 2 * (R ^ 2 * I)) := mul_le_mul_of_nonneg_left hS (sq_nonneg _)
      _ = _ := by ring
  have hsw : 0 < Real.sqrt c.weightMin := Real.sqrt_pos.mpr hw
  have hb := hbound p hp
  have hL : 0 ≤ c.rateLoss := by
    have : 0 * Real.sqrt c.weightMin ≤ c.rateLoss * Real.sqrt c.weightMin := by
      rw [zero_mul]
      exact hX0.trans hb
    exact le_of_mul_le_mul_right this hsw
  have hE := energy_ge c hw hlow hmeas hhigh hv
  calc rowsVal ≤ X * Real.sqrt I := hrows
    _ ≤ c.rateLoss * Real.sqrt c.weightMin * Real.sqrt I := mul_le_mul_of_nonneg_right hb (Real.sqrt_nonneg _)
    _ = c.rateLoss * Real.sqrt (c.weightMin * I) := by rw [Real.sqrt_mul hw.le, mul_assoc]
    _ ≤ c.rateLoss * Real.sqrt (c.energy G H) := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hE) hL

end Reduction

end CellCert

end Breakdown

import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEpsInternal

abbrev slabMeasure : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)

theorem lintegral_tsum_slab {F : ℤ × ℤ → ℝ × Space → ℝ≥0∞} (hF : ∀ ι, AEMeasurable (F ι) slabMeasure) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, F ι (σ, y)) = ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, F ι (σ, y) := by
  have hsum : AEMeasurable (fun z => ∑' ι, F ι z) slabMeasure := AEMeasurable.tsum hF
  rw [← lintegral_prod (fun z => ∑' ι, F ι z) hsum, lintegral_tsum hF]
  exact tsum_congr fun ι => lintegral_prod (F ι) (hF ι)

theorem ofReal_eq_ofReal_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, ENNReal.ofReal_of_nonpos h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem real_of_tsum_bound {a b : ℝ≥0∞} {T : ℤ × ℤ → ℝ} (hT : Summable T)
    (h : a + ∑' ι, ENNReal.ofReal (-T ι) ≤ (∑' ι, ENNReal.ofReal (T ι)) + b) :
    a + ENNReal.ofReal (-∑' ι, T ι) ≤ ENNReal.ofReal (∑' ι, T ι) + b := by
  have hA : Summable fun ι => |T ι| := hT.abs
  have hp : Summable fun ι => max (T ι) 0 :=
    Summable.of_nonneg_of_le (fun ι => le_max_right _ _) (fun ι => max_le (le_abs_self _) (abs_nonneg _)) hA
  have hn : Summable fun ι => max (-T ι) 0 :=
    Summable.of_nonneg_of_le (fun ι => le_max_right _ _) (fun ι => max_le (neg_le_abs _) (abs_nonneg _)) hA
  have ep : (∑' ι, ENNReal.ofReal (T ι)) = ENNReal.ofReal (∑' ι, max (T ι) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ι => le_max_right _ _) hp]
    exact tsum_congr fun ι => ofReal_eq_ofReal_max _
  have en : (∑' ι, ENNReal.ofReal (-T ι)) = ENNReal.ofReal (∑' ι, max (-T ι) 0) := by
    rw [ENNReal.ofReal_tsum_of_nonneg (fun ι => le_max_right _ _) hn]
    exact tsum_congr fun ι => ofReal_eq_ofReal_max _
  have eX : (∑' ι, T ι) = (∑' ι, max (T ι) 0) - ∑' ι, max (-T ι) 0 := by
    rw [← hp.tsum_sub hn]
    exact tsum_congr fun ι => (max_zero_sub_eq_self (T ι)).symm
  set p := ∑' ι, max (T ι) 0
  set n := ∑' ι, max (-T ι) 0
  have p0 : 0 ≤ p := tsum_nonneg fun ι => le_max_right _ _
  have n0 : 0 ≤ n := tsum_nonneg fun ι => le_max_right _ _
  rw [ep, en] at h
  rw [eX]
  rcases le_total n p with hnp | hpn
  · have e1 : ENNReal.ofReal (-(p - n)) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    have e2 : ENNReal.ofReal p = ENNReal.ofReal (p - n) + ENNReal.ofReal n := by
      rw [← ENNReal.ofReal_add (by linarith) n0]; congr 1; ring
    rw [e1, add_zero]
    rw [e2, add_right_comm] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h
  · have e1 : ENNReal.ofReal (p - n) = 0 := ENNReal.ofReal_of_nonpos (by linarith)
    have e2 : ENNReal.ofReal n = ENNReal.ofReal (-(p - n)) + ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_add (by linarith) p0]; congr 1; ring
    rw [e1, zero_add]
    rw [e2, ← add_assoc, add_comm (ENNReal.ofReal p) b] at h
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).1 h

theorem isSplitLowerBound_of_modes {T : ℤ × ℤ → ℝ} {Pos Rest : ℝ → Space → ℤ × ℤ → ℝ}
    (hRest : ∀ σ y ι, Rest σ y ι ≤ 0)
    (hPm : ∀ ι, AEMeasurable (fun z : ℝ × Space => Pos z.1 z.2 ι) slabMeasure)
    (hRm : ∀ ι, AEMeasurable (fun z : ℝ × Space => Rest z.1 z.2 ι) slabMeasure)
    (hT : Summable T)
    (hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-Rest σ y ι)) < ⊤)
    (hmode : ∀ ι, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (Pos σ y ι)) + ENNReal.ofReal (-T ι)
      ≤ ENNReal.ofReal (T ι) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-Rest σ y ι)) :
    IsSplitLowerBound (∑' ι, T ι) Pos Rest (fun _ _ => 0) (fun _ _ => 0) := by
  have hR0 : ∀ σ y, (∑' ι, ENNReal.ofReal (Rest σ y ι)) = 0 := fun σ y =>
    ENNReal.tsum_eq_zero.mpr fun ι => ENNReal.ofReal_of_nonpos (hRest σ y ι)
  refine ⟨?_, ?_⟩
  · simpa only [neg_zero, ENNReal.ofReal_zero, add_zero] using hfin
  · simp only [neg_zero, ENNReal.ofReal_zero, add_zero, hR0]
    have sP := lintegral_tsum_slab (F := fun ι z => ENNReal.ofReal (Pos z.1 z.2 ι))
      (fun ι => (hPm ι).ennreal_ofReal)
    have sR := lintegral_tsum_slab (F := fun ι z => ENNReal.ofReal (-Rest z.1 z.2 ι))
      (fun ι => (hRm ι).neg.ennreal_ofReal)
    simp only at sP sR
    rw [sP, sR]
    apply real_of_tsum_bound hT
    calc (∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (Pos σ y ι)) + ∑' ι, ENNReal.ofReal (-T ι)
        = ∑' ι, ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (Pos σ y ι)) + ENNReal.ofReal (-T ι)) :=
          ENNReal.tsum_add.symm
      _ ≤ ∑' ι, (ENNReal.ofReal (T ι) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-Rest σ y ι)) :=
          ENNReal.tsum_le_tsum hmode
      _ = _ := ENNReal.tsum_add

end SmoothEpsInternal

end Coercive

end Breakdown

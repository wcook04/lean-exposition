import Breakdown.Cert.CoercivePieceDensityPassageLimit
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveSmoothDensityMeasure

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.DensityPassage

open PairingSplitInternal (periodMeasure)

theorem iterated_lintegral_add_right (f : ℝ → Space → ℝ≥0∞) {g : ℝ → Space → ℝ≥0∞}
    (hg : AEMeasurable (fun z : ℝ × Space => g z.1 z.2) periodMeasure) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y)) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), AEMeasurable (fun y => g σ y) volume := by
    filter_upwards [Measure.ae_ae_of_ae_prod hg.ae_eq_mk] with σ hσ
    exact ⟨fun y => hg.mk _ (σ, y), hg.measurable_mk.comp measurable_prodMk_left, hσ⟩
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y))
      = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, f σ y) + ∫⁻ y, g σ y) := by
        refine lintegral_congr_ae ?_
        filter_upwards [hae] with σ hσ
        exact lintegral_add_right' _ hσ
    _ = _ := lintegral_add_right' _ hg.lintegral_prod_right'

theorem negPart_tendsto {J : ℕ → ℝ → Space → ℝ} {J₀ : ℝ → Space → ℝ}
    (hm : ∀ n, AEMeasurable (fun z : ℝ × Space => J n z.1 z.2) periodMeasure)
    (hm₀ : AEMeasurable (fun z : ℝ × Space => J₀ z.1 z.2) periodMeasure)
    (hf : periodLIntegral (fun σ y => |J₀ σ y|) < ⊤)
    (hc : Tendsto (fun n => periodLIntegral (fun σ y => |J n σ y - J₀ σ y|)) atTop (𝓝 0)) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J₀ σ y)) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J n σ y)) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J₀ σ y))) := by
  set a := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J₀ σ y) with ha
  set e : ℕ → ℝ≥0∞ := fun n => periodLIntegral (fun σ y => |J n σ y - J₀ σ y|) with he
  have hmd : ∀ n, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (|J n z.1 z.2 - J₀ z.1 z.2|))
      periodMeasure := fun n =>
    (continuous_abs.measurable.comp_aemeasurable ((hm n).sub hm₀)).ennreal_ofReal
  have hfin : a < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) hf
    exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  have up : ∀ n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J n σ y)) ≤ a + e n := fun n => by
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J n σ y))
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            (ENNReal.ofReal (-J₀ σ y) + ENNReal.ofReal (|J n σ y - J₀ σ y|)) :=
          lintegral_mono fun σ => lintegral_mono fun y =>
            (ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (J n σ y - J₀ σ y)])).trans ENNReal.ofReal_add_le
      _ = a + e n := iterated_lintegral_add_right _ (hmd n)
  have low : ∀ n, a ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J n σ y)) + e n := fun n => by
    calc a ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
            (ENNReal.ofReal (-J n σ y) + ENNReal.ofReal (|J n σ y - J₀ σ y|)) :=
          lintegral_mono fun σ => lintegral_mono fun y =>
            (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (J n σ y - J₀ σ y)])).trans ENNReal.ofReal_add_le
      _ = _ := iterated_lintegral_add_right _ (hmd n)
  refine ⟨hfin, ?_⟩
  have hl : Tendsto (fun n => a - e n) atTop (𝓝 (a - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hc (Or.inl hfin.ne)
  have hu : Tendsto (fun n => a + e n) atTop (𝓝 (a + 0)) := tendsto_const_nhds.add hc
  rw [tsub_zero] at hl
  rw [add_zero] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun n => tsub_le_iff_right.2 (low n)) up

theorem splitRight_integral_eq {R : ℝ → Space → ℤ × ℤ → ℝ} {J : ℝ → Space → ℝ}
    (hJ : AEMeasurable (fun z : ℝ × Space => J z.1 z.2) periodMeasure) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight R (fun _ _ => 0) J σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-R σ y ι)) +
        ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-J σ y) := by
  simp only [splitRight, neg_zero, ENNReal.ofReal_zero, add_zero]
  exact iterated_lintegral_add_right _ hJ.neg.ennreal_ofReal

theorem lintegral_tendsto_of_sandwich {A : ℕ → ℝ → Space → ℝ≥0∞} {A₀ : ℝ → Space → ℝ≥0∞}
    {E : ℕ → ℝ → Space → ℝ≥0∞}
    (hE : ∀ n, AEMeasurable (fun z : ℝ × Space => E n z.1 z.2) periodMeasure)
    (hup : ∀ n σ y, A n σ y ≤ A₀ σ y + E n σ y) (hlow : ∀ n σ y, A₀ σ y ≤ A n σ y + E n σ y)
    (hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A₀ σ y) < ⊤)
    (hc : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E n σ y) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A n σ y) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A₀ σ y)) := by
  set a := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A₀ σ y with ha
  set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, E n σ y with he
  have up : ∀ n, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A n σ y) ≤ a + e n := fun n =>
    (lintegral_mono fun σ => lintegral_mono fun y => hup n σ y).trans_eq (iterated_lintegral_add_right _ (hE n))
  have low : ∀ n, a ≤ (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A n σ y) + e n := fun n =>
    (lintegral_mono fun σ => lintegral_mono fun y => hlow n σ y).trans_eq (iterated_lintegral_add_right _ (hE n))
  have hl : Tendsto (fun n => a - e n) atTop (𝓝 (a - 0)) :=
    ENNReal.Tendsto.sub tendsto_const_nhds hc (Or.inl hfin.ne)
  have hu : Tendsto (fun n => a + e n) atTop (𝓝 (a + 0)) := tendsto_const_nhds.add hc
  rw [tsub_zero] at hl
  rw [add_zero] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu (fun n => tsub_le_iff_right.2 (low n)) up

theorem tsum_negPart_tendsto {R : ℕ → ℝ → Space → ℤ × ℤ → ℝ} {R₀ : ℝ → Space → ℤ × ℤ → ℝ}
    (hm : ∀ n, AEMeasurable (fun z : ℝ × Space =>
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R n z.1 z.2 ι - R₀ z.1 z.2 ι|)) periodMeasure)
    (hf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R₀ σ y ι|)) < ⊤)
    (hc : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ∑' ι : ℤ × ℤ, ENNReal.ofReal (|R n σ y ι - R₀ σ y ι|)) atTop (𝓝 0)) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-R₀ σ y ι)) < ⊤ ∧
      Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-R n σ y ι)) atTop
        (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-R₀ σ y ι))) := by
  have hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (-R₀ σ y ι)) < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y =>
      ENNReal.tsum_le_tsum fun ι => ENNReal.ofReal_le_ofReal (neg_le_abs _)) hf
  refine ⟨hfin, lintegral_tendsto_of_sandwich hm (fun n σ y => ?_) (fun n σ y => ?_) hfin hc⟩
  · rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun ι =>
      (ENNReal.ofReal_le_ofReal (by linarith [neg_abs_le (R n σ y ι - R₀ σ y ι)])).trans ENNReal.ofReal_add_le
  · rw [← ENNReal.tsum_add]
    exact ENNReal.tsum_le_tsum fun ι =>
      (ENNReal.ofReal_le_ofReal (by linarith [le_abs_self (R n σ y ι - R₀ σ y ι)])).trans ENNReal.ofReal_add_le

theorem periodL2_sub_of {A B : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖A σ y - B σ y‖ ^ 2) < ⊤ := by
  have h := PassageLimit.periodL2_add (B := fun σ y => -B σ y) hA hB.neg hA2 (by simpa using hB2)
  simpa [sub_eq_add_neg] using h

end Internal.DensityPassage

end Coercive

end Breakdown

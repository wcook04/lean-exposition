import Breakdown.Cert.CoerciveNodes

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

def splitLeft (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) (Blk J : ℝ → Space → ℝ) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)) + (∑' ι : ℤ × ℤ, ENNReal.ofReal (Rest σ y ι))
    + ENNReal.ofReal (Blk σ y) + ENNReal.ofReal (J σ y)

def splitRight (Rest : ℝ → Space → ℤ × ℤ → ℝ) (Blk J : ℝ → Space → ℝ) (σ : ℝ) (y : Space) : ℝ≥0∞ :=
  (∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y) + ENNReal.ofReal (-J σ y)

def rightSideLimit {k : ℕ} (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (σ : ℝ) (y : Space) : Space :=
  g σ y - secondDerivTrace (H σ y) + G σ y (W σ y) + fderiv ℝ (W σ) y (v σ y) + ∑ i, κ i • act i σ y

namespace Internal.PassageLimit

theorem isSplitLowerBound_iff (X : ℝ) (Pos Rest : ℝ → Space → ℤ × ℤ → ℝ) (Blk J : ℝ → Space → ℝ) :
    IsSplitLowerBound X Pos Rest Blk J ↔
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))) < ⊤ ∧
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitLeft Pos Rest Blk J σ y) + ENNReal.ofReal (-X)
        ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest Blk J σ y :=
  Iff.rfl

theorem isSplitLowerBound_of_liminf {X : ℕ → ℝ} {X₀ : ℝ}
    {Pos Rest : ℕ → ℝ → Space → ℤ × ℤ → ℝ} {Blk J : ℕ → ℝ → Space → ℝ}
    {Pos₀ Rest₀ : ℝ → Space → ℤ × ℤ → ℝ} {Blk₀ J₀ : ℝ → Space → ℝ}
    (hS : ∀ n, IsSplitLowerBound (X n) (Pos n) (Rest n) (Blk n) (J n))
    (hX : Tendsto X atTop (𝓝 X₀))
    (hN : Tendsto (fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (Rest n) (Blk n) (J n) σ y) atTop
      (𝓝 (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest₀ Blk₀ J₀ σ y)))
    (hNfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest₀ Blk₀ J₀ σ y) < ⊤)
    (hmy : ∀ n, ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      AEMeasurable (fun y => splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y) volume)
    (hms : ∀ n, AEMeasurable (fun σ => ∫⁻ y, splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y)
      (volume.restrict (Set.Icc (0 : ℝ) 1)))
    (hlow : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y, splitLeft Pos₀ Rest₀ Blk₀ J₀ σ y
      ≤ liminf (fun n => splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y) atTop) :
    IsSplitLowerBound X₀ Pos₀ Rest₀ Blk₀ J₀ := by
  rw [isSplitLowerBound_iff]
  refine ⟨lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) hNfin, ?_⟩
  · unfold splitRight
    exact le_self_add
  set L : ℕ → ℝ≥0∞ := fun n => ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y
    with hL
  have hliminf : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitLeft Pos₀ Rest₀ Blk₀ J₀ σ y) ≤ liminf L atTop := by
    calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitLeft Pos₀ Rest₀ Blk₀ J₀ σ y)
        ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, liminf (fun n => ∫⁻ y, splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y) atTop := by
          refine lintegral_mono_ae ?_
          have hall := ae_all_iff.2 hmy
          filter_upwards [hall, hlow] with σ hσ hlσ
          calc (∫⁻ y, splitLeft Pos₀ Rest₀ Blk₀ J₀ σ y)
              ≤ ∫⁻ y, liminf (fun n => splitLeft (Pos n) (Rest n) (Blk n) (J n) σ y) atTop :=
                lintegral_mono_ae hlσ
            _ ≤ _ := lintegral_liminf_le' hσ
      _ ≤ liminf L atTop := lintegral_liminf_le' hms
  obtain ⟨φ, hLφ, hφt⟩ : ∃ φ : ℕ → ℕ, Tendsto (L ∘ φ) atTop (𝓝 (liminf L atTop)) ∧ Tendsto φ atTop atTop :=
    exists_seq_tendsto_liminf
  have hXm : Tendsto (fun n => ENNReal.ofReal (-X (φ n))) atTop (𝓝 (ENNReal.ofReal (-X₀))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((hX.comp hφt).neg)
  have hXp : Tendsto (fun n => ENNReal.ofReal (X (φ n))) atTop (𝓝 (ENNReal.ofReal X₀)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hX.comp hφt)
  have hleft : Tendsto (fun n => L (φ n) + ENNReal.ofReal (-X (φ n))) atTop
      (𝓝 (liminf L atTop + ENNReal.ofReal (-X₀))) :=
    hLφ.add hXm
  have hright : Tendsto (fun n => ENNReal.ofReal (X (φ n))
      + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight (Rest (φ n)) (Blk (φ n)) (J (φ n)) σ y) atTop
      (𝓝 (ENNReal.ofReal X₀ + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest₀ Blk₀ J₀ σ y)) :=
    hXp.add (hN.comp hφt)
  have hlim : liminf L atTop + ENNReal.ofReal (-X₀) ≤
      ENNReal.ofReal X₀ + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, splitRight Rest₀ Blk₀ J₀ σ y :=
    le_of_tendsto_of_tendsto' hleft hright fun n => ((isSplitLowerBound_iff _ _ _ _ _).1 (hS (φ n))).2
  exact (add_le_add_left hliminf _).trans hlim

theorem period_integrable_inner {A B : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2) (B z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  set μ : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume with hμ
  have hμ' : μ = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [hμ, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hAμ : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) μ := by rw [hμ']; exact hA.restrict
  have hBμ : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) μ := by rw [hμ']; exact hB.restrict
  have hsq : ∀ (u : ℝ × Space → Space), AEStronglyMeasurable u μ →
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)) < ⊤ →
      Integrable (fun z => ‖u z‖ ^ 2) μ := by
    intro u hu hfin
    have e : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)
        = ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂μ := by
      rw [hμ]
      exact (lintegral_prod (fun z => ENNReal.ofReal (‖u z‖ ^ 2))
        ((hu.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm
    rw [e] at hfin
    refine (integrable_toReal_of_lintegral_ne_top (hu.norm.pow 2).aemeasurable.ennreal_ofReal
      hfin.ne).congr ?_
    exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))
  have hAi := hsq _ hAμ hA2
  have hBi := hsq _ hBμ hB2
  refine Integrable.mono' ((hAi.add hBi).div_const 2) (hAμ.inner hBμ) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  show ‖A z.1 z.2‖ * ‖B z.1 z.2‖ ≤ (‖A z.1 z.2‖ ^ 2 + ‖B z.1 z.2‖ ^ 2) / 2
  nlinarith [sq_nonneg (‖A z.1 z.2‖ - ‖B z.1 z.2‖)]

theorem periodPairing_eq_integral {A B : ℝ → Space → Space}
    (hi : Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2) (B z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    periodPairing A B = ∫ z, inner ℝ (A z.1 z.2) (B z.1 z.2)
      ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  rw [integral_prod _ hi]
  rfl

theorem periodPairing_sub_right {A B B' : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hB' : AEStronglyMeasurable (fun z : ℝ × Space => B' z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤)
    (hB'2 : periodLIntegral (fun σ y => ‖B' σ y‖ ^ 2) < ⊤)
    (hD2 : periodLIntegral (fun σ y => ‖B σ y - B' σ y‖ ^ 2) < ⊤) :
    periodPairing A B - periodPairing A B' = periodPairing A (fun σ y => B σ y - B' σ y) := by
  have h1 := period_integrable_inner hA hB hA2 hB2
  have h2 := period_integrable_inner hA hB' hA2 hB'2
  have hD : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2 - B' z.1 z.2) volume := hB.sub hB'
  have h3 := period_integrable_inner (B := fun σ y => B σ y - B' σ y) hA hD hA2 hD2
  calc periodPairing A B - periodPairing A B'
      = (∫ z, inner ℝ (A z.1 z.2) (B z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
        - ∫ z, inner ℝ (A z.1 z.2) (B' z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
          rw [periodPairing_eq_integral (A := A) (B := B) h1, periodPairing_eq_integral (A := A) (B := B') h2]
    _ = ∫ z, inner ℝ (A z.1 z.2) (B z.1 z.2 - B' z.1 z.2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
          rw [← integral_sub h1 h2]
          exact integral_congr_ae (ae_of_all _ fun z => (inner_sub_right _ _ _).symm)
    _ = periodPairing A (fun σ y => B σ y - B' σ y) :=
          (periodPairing_eq_integral (A := A) (B := fun σ y => B σ y - B' σ y) h3).symm

theorem periodPairing_tendsto_right {A : ℝ → Space → Space} {B : ℕ → ℝ → Space → Space}
    {B₀ : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => B n z.1 z.2) volume)
    (hB2 : ∀ n, periodLIntegral (fun σ y => ‖B n σ y‖ ^ 2) < ⊤)
    (hB₀ : AEStronglyMeasurable (fun z : ℝ × Space => B₀ z.1 z.2) volume)
    (hB₀2 : periodLIntegral (fun σ y => ‖B₀ σ y‖ ^ 2) < ⊤)
    (hconv : Tendsto (fun n => periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n => periodPairing A (B n)) atTop (𝓝 (periodPairing A B₀)) := by
  have hev : ∀ᶠ n in atTop, periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2) < ⊤ :=
    hconv.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  have hnorm : Tendsto (fun n => periodNorm A
      * Real.sqrt (periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2)).toReal) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => Real.sqrt (periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2)).toReal)
        atTop (𝓝 0) := by
      have h0 := ((Real.continuous_sqrt.tendsto _).comp
        ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hconv))
      rw [ENNReal.toReal_zero, Real.sqrt_zero] at h0
      exact h0
    have h1 := ht.const_mul (periodNorm A)
    rw [mul_zero] at h1
    exact h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hnorm
  filter_upwards [hev] with n hn
  rw [periodPairing_sub_right (A := A) (B := B n) (B' := B₀) hA (hB n) hB₀ hA2 (hB2 n) hB₀2 hn, Real.norm_eq_abs]
  have hD : AEStronglyMeasurable (fun z : ℝ × Space => B n z.1 z.2 - B₀ z.1 z.2) volume := (hB n).sub hB₀
  exact periodPairing_abs_le (M := fun σ y => B n σ y - B₀ σ y) hA hD hA2 hn

theorem periodPairing_comm (A B : ℝ → Space → Space) : periodPairing A B = periodPairing B A := by
  unfold periodPairing
  congr 1
  funext σ
  congr 1
  funext y
  exact real_inner_comm _ _

theorem periodPairing_expand {A A₀ B B₀ : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hA₀ : AEStronglyMeasurable (fun z : ℝ × Space => A₀ z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hB₀ : AEStronglyMeasurable (fun z : ℝ × Space => B₀ z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hA₀2 : periodLIntegral (fun σ y => ‖A₀ σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤)
    (hB₀2 : periodLIntegral (fun σ y => ‖B₀ σ y‖ ^ 2) < ⊤)
    (hDA : periodLIntegral (fun σ y => ‖A σ y - A₀ σ y‖ ^ 2) < ⊤)
    (hDB : periodLIntegral (fun σ y => ‖B σ y - B₀ σ y‖ ^ 2) < ⊤) :
    periodPairing A B = periodPairing (fun σ y => A σ y - A₀ σ y) (fun σ y => B σ y - B₀ σ y)
      + periodPairing B₀ A + periodPairing A₀ B - periodPairing A₀ B₀ := by
  have hmA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2 - A₀ z.1 z.2) volume := hA.sub hA₀
  have hmB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2 - B₀ z.1 z.2) volume := hB.sub hB₀
  have i0 := period_integrable_inner (A := A) (B := B) hA hB hA2 hB2
  have i1 := period_integrable_inner (A := fun σ y => A σ y - A₀ σ y) (B := fun σ y => B σ y - B₀ σ y)
    hmA hmB hDA hDB
  have i2 := period_integrable_inner (A := B₀) (B := A) hB₀ hA hB₀2 hA2
  have i3 := period_integrable_inner (A := A₀) (B := B) hA₀ hB hA₀2 hB2
  have i4 := period_integrable_inner (A := A₀) (B := B₀) hA₀ hB₀ hA₀2 hB₀2
  rw [periodPairing_eq_integral (A := A) (B := B) i0,
    periodPairing_eq_integral (A := fun σ y => A σ y - A₀ σ y) (B := fun σ y => B σ y - B₀ σ y) i1,
    periodPairing_eq_integral (A := B₀) (B := A) i2, periodPairing_eq_integral (A := A₀) (B := B) i3,
    periodPairing_eq_integral (A := A₀) (B := B₀) i4]
  have i12 : Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2 - A₀ z.1 z.2) (B z.1 z.2 - B₀ z.1 z.2)
      + inner ℝ (B₀ z.1 z.2) (A z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := i1.add i2
  have i123 : Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2 - A₀ z.1 z.2) (B z.1 z.2 - B₀ z.1 z.2)
      + inner ℝ (B₀ z.1 z.2) (A z.1 z.2) + inner ℝ (A₀ z.1 z.2) (B z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := i12.add i3
  rw [← integral_add i1 i2, ← integral_add i12 i3, ← integral_sub i123 i4]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only [inner_sub_left, inner_sub_right, real_inner_comm (A z.1 z.2) (B₀ z.1 z.2)]
  ring

theorem periodPairing_tendsto {A B : ℕ → ℝ → Space → Space} {A₀ B₀ : ℝ → Space → Space}
    (hA : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => A n z.1 z.2) volume)
    (hA2 : ∀ n, periodLIntegral (fun σ y => ‖A n σ y‖ ^ 2) < ⊤)
    (hA₀ : AEStronglyMeasurable (fun z : ℝ × Space => A₀ z.1 z.2) volume)
    (hA₀2 : periodLIntegral (fun σ y => ‖A₀ σ y‖ ^ 2) < ⊤)
    (hB : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => B n z.1 z.2) volume)
    (hB2 : ∀ n, periodLIntegral (fun σ y => ‖B n σ y‖ ^ 2) < ⊤)
    (hB₀ : AEStronglyMeasurable (fun z : ℝ × Space => B₀ z.1 z.2) volume)
    (hB₀2 : periodLIntegral (fun σ y => ‖B₀ σ y‖ ^ 2) < ⊤)
    (hcA : Tendsto (fun n => periodLIntegral (fun σ y => ‖A n σ y - A₀ σ y‖ ^ 2)) atTop (𝓝 0))
    (hcB : Tendsto (fun n => periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun n => periodPairing (A n) (B n)) atTop (𝓝 (periodPairing A₀ B₀)) := by
  have evA : ∀ᶠ n in atTop, periodLIntegral (fun σ y => ‖A n σ y - A₀ σ y‖ ^ 2) < ⊤ :=
    hcA.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  have evB : ∀ᶠ n in atTop, periodLIntegral (fun σ y => ‖B n σ y - B₀ σ y‖ ^ 2) < ⊤ :=
    hcB.eventually (gt_mem_nhds ENNReal.zero_lt_top)
  have t1 := periodPairing_tendsto_right hB₀ hB₀2 hA hA2 hA₀ hA₀2 hcA
  have t2 := periodPairing_tendsto_right hA₀ hA₀2 hB hB2 hB₀ hB₀2 hcB
  have sq : ∀ {c : ℕ → ℝ≥0∞}, Tendsto c atTop (𝓝 0) → Tendsto (fun n => Real.sqrt (c n).toReal) atTop (𝓝 0) := by
    intro c hc
    have h0 := (Real.continuous_sqrt.tendsto _).comp ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hc)
    rw [ENNReal.toReal_zero, Real.sqrt_zero] at h0
    exact h0
  have t3 : Tendsto (fun n => periodPairing (fun σ y => A n σ y - A₀ σ y) (fun σ y => B n σ y - B₀ σ y))
      atTop (𝓝 0) := by
    have hprod := (sq hcA).mul (sq hcB)
    rw [mul_zero] at hprod
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hprod
    filter_upwards [evA, evB] with n hn1 hn2
    have hmA : AEStronglyMeasurable (fun z : ℝ × Space => A n z.1 z.2 - A₀ z.1 z.2) volume := (hA n).sub hA₀
    have hmB : AEStronglyMeasurable (fun z : ℝ × Space => B n z.1 z.2 - B₀ z.1 z.2) volume := (hB n).sub hB₀
    rw [Real.norm_eq_abs]
    exact periodPairing_abs_le (F := fun σ y => A n σ y - A₀ σ y) (M := fun σ y => B n σ y - B₀ σ y)
      hmA hmB hn1 hn2
  have hlim := ((t3.add t1).add t2).sub (tendsto_const_nhds (x := periodPairing A₀ B₀))
  rw [zero_add, periodPairing_comm B₀ A₀, add_sub_cancel_right] at hlim
  refine hlim.congr' ?_
  filter_upwards [evA, evB] with n hn1 hn2
  exact (periodPairing_expand (hA n) hA₀ (hB n) hB₀ (hA2 n) hA₀2 (hB2 n) hB₀2 hn1 hn2).symm

theorem periodLIntegral_mono {f g : ℝ → Space → ℝ} (h : ∀ σ y, f σ y ≤ g σ y) :
    periodLIntegral f ≤ periodLIntegral g :=
  lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h σ y)

theorem periodLIntegral_le_mul {f g : ℝ → Space → ℝ} {C : ℝ} (hC : 0 ≤ C) (h : ∀ σ y, f σ y ≤ C * g σ y) :
    periodLIntegral f ≤ ENNReal.ofReal C * periodLIntegral g := by
  unfold periodLIntegral
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal C * ENNReal.ofReal (g σ y) :=
        lintegral_mono fun σ => lintegral_mono fun y => by
          rw [← ENNReal.ofReal_mul hC]; exact ENNReal.ofReal_le_ofReal (h σ y)
    _ = ENNReal.ofReal C * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (g σ y) := by
        simp only [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem periodLIntegral_eq_prod {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hμ' : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ']; exact hf.ennreal_ofReal.restrict
  exact (lintegral_prod _ hm).symm

theorem periodLIntegral_add {f g : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEMeasurable (fun z : ℝ × Space => g z.1 z.2) volume)
    (hf0 : ∀ σ y, 0 ≤ f σ y) (hg0 : ∀ σ y, 0 ≤ g σ y) :
    periodLIntegral (fun σ y => f σ y + g σ y) = periodLIntegral f + periodLIntegral g := by
  have hμ' : (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  have hfg : AEMeasurable (fun z : ℝ × Space => f z.1 z.2 + g z.1 z.2) volume := hf.add hg
  rw [periodLIntegral_eq_prod (f := fun σ y => f σ y + g σ y) hfg, periodLIntegral_eq_prod hf,
    periodLIntegral_eq_prod hg]
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ']; exact hf.ennreal_ofReal.restrict
  rw [← lintegral_add_left' hm]
  refine lintegral_congr fun z => ?_
  exact ENNReal.ofReal_add (hf0 z.1 z.2) (hg0 z.1 z.2)

theorem periodL2_of_le {A : ℝ → Space → Space} {f : ℝ → Space → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ σ y, ‖A σ y‖ ^ 2 ≤ C * f σ y) (hf : periodLIntegral f < ⊤) :
    periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤ :=
  lt_of_le_of_lt (periodLIntegral_le_mul hC h) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

theorem periodL2_add {A B : ℝ → Space → Space}
    (hA : AEStronglyMeasurable (fun z : ℝ × Space => A z.1 z.2) volume)
    (hB : AEStronglyMeasurable (fun z : ℝ × Space => B z.1 z.2) volume)
    (hA2 : periodLIntegral (fun σ y => ‖A σ y‖ ^ 2) < ⊤)
    (hB2 : periodLIntegral (fun σ y => ‖B σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖A σ y + B σ y‖ ^ 2) < ⊤ := by
  have hmA : AEMeasurable (fun z : ℝ × Space => 2 * ‖A z.1 z.2‖ ^ 2) volume :=
    (hA.norm.aemeasurable.pow_const 2).const_mul 2
  have hmB : AEMeasurable (fun z : ℝ × Space => 2 * ‖B z.1 z.2‖ ^ 2) volume :=
    (hB.norm.aemeasurable.pow_const 2).const_mul 2
  have hle := periodLIntegral_mono (f := fun σ y => ‖A σ y + B σ y‖ ^ 2)
    (g := fun σ y => 2 * ‖A σ y‖ ^ 2 + 2 * ‖B σ y‖ ^ 2) fun σ y => by
      have := norm_add_le (A σ y) (B σ y)
      nlinarith [norm_nonneg (A σ y), norm_nonneg (B σ y), norm_nonneg (A σ y + B σ y),
        sq_nonneg (‖A σ y‖ - ‖B σ y‖)]
  rw [periodLIntegral_add (f := fun σ y => 2 * ‖A σ y‖ ^ 2) (g := fun σ y => 2 * ‖B σ y‖ ^ 2) hmA hmB
    (fun σ y => by positivity) (fun σ y => by positivity)] at hle
  refine lt_of_le_of_lt hle (ENNReal.add_lt_top.2 ⟨?_, ?_⟩)
  · exact lt_of_le_of_lt (periodLIntegral_le_mul (g := fun σ y => ‖A σ y‖ ^ 2) (by norm_num)
      fun σ y => le_refl _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hA2)
  · exact lt_of_le_of_lt (periodLIntegral_le_mul (g := fun σ y => ‖B σ y‖ ^ 2) (by norm_num)
      fun σ y => le_refl _) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hB2)

theorem periodL2_sum {ι : Type*} (s : Finset ι) {A : ι → ℝ → Space → Space}
    (hA : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => A i z.1 z.2) volume)
    (hA2 : ∀ i, periodLIntegral (fun σ y => ‖A i σ y‖ ^ 2) < ⊤) :
    AEStronglyMeasurable (fun z : ℝ × Space => ∑ i ∈ s, A i z.1 z.2) volume ∧
      periodLIntegral (fun σ y => ‖∑ i ∈ s, A i σ y‖ ^ 2) < ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨by simpa using (aestronglyMeasurable_const (b := (0 : Space))), ?_⟩
    simp [periodLIntegral]
  | insert a s ha ih =>
    have hm : AEStronglyMeasurable (fun z : ℝ × Space => A a z.1 z.2 + ∑ i ∈ s, A i z.1 z.2) volume :=
      (hA a).add ih.1
    simp only [Finset.sum_insert ha]
    exact ⟨hm, periodL2_add (A := A a) (B := fun σ y => ∑ i ∈ s, A i σ y) (hA a) ih.1 (hA2 a) ih.2⟩

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem continuous_fderiv_of_contDiff_two {W : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) := by
  have hf : ContDiff ℝ 2 (fun p : (ℝ × Space) × Space => W p.1.1 p.2) :=
    hW.comp (contDiff_fst.fst.prodMk contDiff_snd)
  exact (ContDiff.fderiv (f := fun (z : ℝ × Space) (x : Space) => W z.1 x) (g := fun z => z.2) (n := 1) hf
    contDiff_snd (by norm_num)).continuous


end Internal.PassageLimit

end Coercive

end Breakdown

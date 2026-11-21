import Breakdown.CertCell.BridgeTraceStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace SideTrace

namespace Internal

namespace HarmonicFlip

private theorem flipPoint_coord_zero (y : Space) : flipPoint y 0 = y 0 := by
  simp [flipPoint, unitVector]

private theorem flipPoint_coord_one (y : Space) : flipPoint y 1 = -y 1 := by
  simp [flipPoint, unitVector]

private theorem flipPoint_coord_two (y : Space) : flipPoint y 2 = -y 2 := by
  simp [flipPoint, unitVector]

private theorem flipPoint_coord (y : Space) (i : Fin 3) :
    flipPoint y i = if i = 0 then y i else -y i := by
  fin_cases i
  · simp [flipPoint_coord_zero]
  · simp [flipPoint_coord_one]
  · simp [flipPoint_coord_two]

def flipLinearEquiv : Space ≃L[ℝ] Space :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := flipPoint
      invFun := flipPoint
      map_add' := fun x z => by
        ext i
        simp only [flipPoint_coord, PiLp.add_apply]
        split_ifs <;> ring
      map_smul' := fun c x => by
        ext i
        simp only [flipPoint_coord, PiLp.smul_apply, RingHom.id_apply, smul_eq_mul]
        split_ifs <;> ring
      left_inv := fun x => by
        ext i
        simp only [flipPoint_coord]
        split_ifs <;> simp
      right_inv := fun x => by
        ext i
        simp only [flipPoint_coord]
        split_ifs <;> simp }

theorem flipLinearEquiv_apply (y : Space) : flipLinearEquiv y = flipPoint y := rfl

theorem ae_slices_of_ae_prod {f : ℝ → Space → Space}
    (h : ∀ᵐ z : ℝ × Space, f z.1 (flipPoint z.2) = flipPoint (f z.1 z.2)) :
    ∀ᵐ y : Space, ∀ᵐ τ : ℝ, f τ (flipPoint y) = flipPoint (f τ y) := by
  have hs : ∀ᵐ w : Space × ℝ, f w.2 (flipPoint w.1) = flipPoint (f w.2 w.1) :=
    (Measure.measurePreserving_swap (μ := (volume : Measure Space)) (ν := (volume : Measure ℝ))).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hs

theorem weighted_integral_flip {f : ℝ → Space → Space} (w : ℝ → ℝ)
    (h : ∀ᵐ z : ℝ × Space, f z.1 (flipPoint z.2) = flipPoint (f z.1 z.2)) :
    ∀ᵐ y : Space, (∫ τ in Set.Icc (0 : ℝ) 1, w τ • f τ (flipPoint y))
      = flipPoint (∫ τ in Set.Icc (0 : ℝ) 1, w τ • f τ y) := by
  filter_upwards [ae_slices_of_ae_prod h] with y hy
  have hr : ∀ᵐ τ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      w τ • f τ (flipPoint y) = flipLinearEquiv (w τ • f τ y) := by
    filter_upwards [ae_restrict_of_ae hy] with τ hτ
    rw [map_smul, flipLinearEquiv_apply, hτ]
  rw [integral_congr_ae hr, ContinuousLinearEquiv.integral_comp_comm, flipLinearEquiv_apply]

end HarmonicFlip

end Internal

theorem harmonicPressureFlip : HarmonicPressureFlipHolds := by
  intro Pg _ hflip ν
  refine ⟨?_, ?_⟩
  · filter_upwards [Internal.HarmonicFlip.weighted_integral_flip
      (fun τ => Real.cos (2 * Real.pi * ν * τ)) hflip] with y hy
    simpa only [CellCalculus.harmonicCos] using hy
  · filter_upwards [Internal.HarmonicFlip.weighted_integral_flip
      (fun τ => Real.sin (2 * Real.pi * ν * τ)) hflip] with y hy
    simp only [CellCalculus.harmonicSin]
    rw [hy, ← Internal.HarmonicFlip.flipLinearEquiv_apply, ← Internal.HarmonicFlip.flipLinearEquiv_apply,
      map_neg]

end SideTrace

end CertCell

end Breakdown

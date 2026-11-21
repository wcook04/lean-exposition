import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

theorem bilinX_symm (τ : ℝ) (u v : X) : bilinX τ u v = bilinX τ v u := by
  unfold bilinX
  split_ifs with h
  · apply ext_inner_right ℝ
    intro ψ
    rw [h.2.choose_spec u v ψ, h.2.choose_spec v u ψ]
    unfold bilinForm
    ring
  · rfl

theorem bilinX_opNorm_le (hB : BilinBound) (τ : ℝ) (hτ : 0 < τ) :
    ‖bilinX τ‖ ≤ hB.choose * τ ^ (-(3 / 4 : ℝ)) :=
  ContinuousLinearMap.opNorm_le_bound₂ _ (mul_nonneg hB.choose_spec.1 (Real.rpow_nonneg hτ.le _))
    (hB.choose_spec.2 τ hτ)

def frameOf (hH : HeatSemigroup) (hD : DilationAlgebra) (hDc : DilationContinuous)
    (hB : BilinBound) (hBc : BilinContinuous) (hBs : BilinShift) (hBd : BilinDilate)
    (hT : TestDense) (hK : BilinCompact) : MildFramework X where
  G := heatX
  G_zero := hH.1
  G_add := hH.2.1
  G_norm := hH.2.2.1
  G_cont := hH.2.2.2.1
  K := bilinX
  K_symm := bilinX_symm
  CK := hB.choose
  K_bound := fun τ hτ _ => bilinX_opNorm_le hB τ hτ
  K_cont := hBc
  K_shift := hBs
  D := dilX
  D_norm := hD.1
  D_one := hD.2.1
  D_mul := hD.2.2.1
  D_cont := hDc
  D_G := hD.2.2.2.1
  D_K := hBd
  compact := ⟨testSpan, hT, hK⟩

def realizationOf (hH : HeatSemigroup) (hD : DilationAlgebra) (hDc : DilationContinuous)
    (hB : BilinBound) (hBc : BilinContinuous) (hBs : BilinShift) (hBd : BilinDilate)
    (hT : TestDense) (hK : BilinCompact) (hR : RotationAlgebra) (hBr : BilinRotate)
    (hEl : EmbedLinear) (hEn : EmbedNorm) (hEz : EmbedNeZero) (hEr : EmbedRot) (hEd : EmbedDilate)
    (hM : MildOfWeak) (hS : TestSpanSpec) : Realization X where
  F := frameOf hH hD hDc hB hBc hBs hBd hT hK
  rot := rotX
  rot_commutes := fun R => ⟨(hR R).2.1, hBr R, (hR R).2.2⟩
  embed := embedX
  embed_sub := hEl.2.1
  embed_norm := hEn
  embed_ne_zero := hEz
  embed_rot := hEr
  embed_dilate := hEd
  mild_of_weak := fun v a b hab h1 h2 h3 h4 h5 h6 => hM v a b hab ⟨h1, h2, h3, h4, h5, h6⟩
  test := testSpan
  test_dense := hT
  test_spec := hS

end Breakdown.Freq

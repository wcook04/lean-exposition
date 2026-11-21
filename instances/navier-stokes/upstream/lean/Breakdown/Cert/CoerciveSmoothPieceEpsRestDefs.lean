import Breakdown.Cert.CoerciveSmoothPieceEpsCore
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoerciveCurlEnergy
import Breakdown.Cert.CoerciveStretch
import Breakdown.Cert.CoerciveSmoothPieceEpsFrequency

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEpsCore

open Internal.PieceAbsorb

def axialPerp (x : Space) : Space := -(x 1) • unitVector 0 + x 0 • unitVector 1

def vortField (v : ℝ → Space → Space) : ℝ → Space → Space := fun s x => curlVec (fderiv ℝ (v s) x)

def frameRest (a : ℝ) (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (vortField v s) x (W s x + (1 / 2 : ℝ) • x - a • axialPerp x)
    - fderiv ℝ (W s) x (vortField v s x) + fderiv ℝ (vortField W s) x (v s x)
    - fderiv ℝ (v s) x (vortField W s x) + a • axialPerp (vortField v s x)

def vortMode (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : Fin 3 → ℂ :=
  curlOfGrad (modeGrad ι (gradField v) σ y)

def restTerm (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (a : ℝ) (W v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y)
    (modeVel ι (frameRest a W v) σ y)).re


def transportRest (a : ℝ) (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (vortField v s) x (W s x + (1 / 2 : ℝ) • x - a • axialPerp x)

def stretchRest (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (W s) x (vortField v s x)

def vortTransportRest (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (vortField W s) x (v s x)

def vortStretchRest (W v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  fderiv ℝ (v s) x (vortField W s x)

def rotationRest (a : ℝ) (v : ℝ → Space → Space) : ℝ → Space → Space := fun s x =>
  a • axialPerp (vortField v s x)

def restPart (T : Set (ℤ × ℤ)) (wt : Space → ℝ) (v Z : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * ((PieceWeights.sgn T ι * wt y : ℝ) : ℂ) * cdot (vortMode v ι σ y) (modeVel ι Z σ y)).re

theorem edge_nonneg (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ)
    (hX : ∀ α, 0 ≤ X α) (hg : ∀ κ, 0 ≤ g κ) : 0 ≤ edgeSum h T X g ι := by
  classical
  unfold edgeSum
  split_ifs
  · refine Finset.sum_nonneg fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hX β) (hg _)
  · refine Finset.sum_nonneg fun β _ => ?_
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (hX β) (hg _)
  · exact le_rfl

theorem secondDeriv_continuous {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) := by
  have hg : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    ContDiff.fderiv (f := fun (p : ℝ × Space) (x : Space) => W p.1 x) (g := fun p => p.2)
      (hW.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => fderiv ℝ (W p.1) x)
    (g := fun p => p.2) (hg.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous

theorem vortField_continuous {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => vortField W z.1 z.2) :=
  Internal.SmoothPieceEps.curlLinear.continuous.comp (continuous_fderiv_slice hW)

theorem vortGrad_continuous {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (vortField W z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (vortField W z.1) z.2)
      = fun z => Internal.SmoothPieceEps.curlLinear.comp (fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) := by
    funext z
    exact vortGrad_eq hW z.1 z.2
  rw [e]
  exact continuous_const.clm_comp (secondDeriv_continuous hW)

theorem axialPerp_continuous : Continuous axialPerp := by
  have c0 : Continuous (fun x : Space => x 0) := by fun_prop
  have c1 : Continuous (fun x : Space => x 1) := by fun_prop
  unfold axialPerp
  fun_prop

theorem modeVel_sub' {X₁ X₂ : ℝ → Space → Space} (h₁ : Continuous (fun z : ℝ × Space => X₁ z.1 z.2))
    (h₂ : Continuous (fun z : ℝ × Space => X₂ z.1 z.2)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (X₁ - X₂) σ y = modeVel ι X₁ σ y - modeVel ι X₂ σ y := by
  have e : X₁ - X₂ = X₁ + (-1 : ℝ) • X₂ := by
    funext s x
    simp [sub_eq_add_neg]
  have h₃ : Continuous (fun z : ℝ × Space => ((-1 : ℝ) • X₂) z.1 z.2) := by
    show Continuous (fun z : ℝ × Space => (-1 : ℝ) • X₂ z.1 z.2)
    exact h₂.const_smul (-1 : ℝ)
  rw [e, Internal.Field.modeVel_add h₁ h₃, Internal.Field.modeVel_smul]
  funext i
  simp [sub_eq_add_neg]

theorem cdot_add (x y z : Fin 3 → ℂ) : cdot x (y + z) = cdot x y + cdot x z := by
  unfold cdot
  simp only [Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem cdot_sub (x y z : Fin 3 → ℂ) : cdot x (y - z) = cdot x y - cdot x z := by
  unfold cdot
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem fderiv_slice_continuous {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) :=
  (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => F p.1 x) (g := fun p => p.2)
    (hF.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)).continuous

theorem vortField_smooth {v : ℝ → Space → Space} (hv : ContDiff ℝ ∞ (fun z : ℝ × Space => v z.1 z.2)) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => vortField v z.1 z.2) := by
  have hg : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (m := ∞) (n := ∞) (f := fun (p : ℝ × Space) (x : Space) => v p.1 x) (g := fun p => p.2)
      (hv.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by simp)
  exact Internal.SmoothPieceEps.curlLinear.contDiff.comp hg

theorem frameRest_continuous {a : ℝ} {W v : ℝ → Space → Space} (hv2 : ContDiff ℝ 2 (fun z : ℝ × Space => v z.1 z.2))
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => frameRest a W v z.1 z.2) := by
  have cv : Continuous (fun z : ℝ × Space => v z.1 z.2) := hv2.continuous
  have cW : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hx : Continuous (fun z : ℝ × Space => (1 / 2 : ℝ) • z.2) := by fun_prop
  have hp : Continuous (fun z : ℝ × Space => a • axialPerp z.2) :=
    (axialPerp_continuous.comp continuous_snd).const_smul a
  have c1 := (vortGrad_continuous hv2).clm_apply ((cW.add hx).sub hp)
  have c2 := (continuous_fderiv_slice hW).clm_apply (vortField_continuous hv2)
  have c3 := (vortGrad_continuous hW).clm_apply cv
  have c4 := (continuous_fderiv_slice hv2).clm_apply (vortField_continuous hW)
  have c5 := (axialPerp_continuous.comp (vortField_continuous hv2)).const_smul a
  exact (((c1.sub c2).add c3).sub c4).add c5

theorem vortMode_eq_modeVel {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : vortMode F ι σ y = modeVel ι (vortField F) σ y := by
  have hc : Continuous (fun p : ℝ × ℝ => gradField F (σ + p.1) (axialRot p.2 y)) :=
    (fderiv_slice_continuous hF).comp ((continuous_const.add continuous_fst).prodMk
      (Internal.Field.axialRot_comp_continuous continuous_snd continuous_const))
  exact Internal.CurlEnergy.curlOfGrad_modeGrad_eq (z := (σ, y)) ι
    (StretchInternal.integrable_box_of_continuous hc)

theorem abs_sgn_eq (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) :
    |PieceWeights.sgn T ι| = ModeWeights.ind (PieceWeights.inPiece T ι) := by
  unfold PieceWeights.sgn ModeWeights.ind PieceWeights.inPiece
  split_ifs <;> simp_all


end Internal.SmoothPieceEpsCore

end Coercive

end Breakdown

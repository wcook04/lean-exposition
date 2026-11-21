import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.MeanStretchTorus
import Breakdown.CertCell.MeanStretchOrbit
import Breakdown.Cert.CoerciveStretch
import Breakdown.Cert.CoerciveTorus
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.MeanStretch

abbrev Slot := Fin 3 ⊕ (Fin 3 × Fin 3)

def pairForm (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (x y : Slot → ℂ) : ℂ :=
  stretchBilin gW hW (fun i => x (Sum.inl i)) (fun ij => x (Sum.inr ij)) (fun i => y (Sum.inl i))
    (fun ij => y (Sum.inr ij))

theorem curlOfGrad_add (g g' : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (fun ij => g ij + g' ij) i = curlOfGrad g i + curlOfGrad g' i := by
  simp only [curlOfGrad, mul_add, Finset.sum_add_distrib]

theorem curlOfGrad_smul (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (fun ij => c * g ij) i = c * curlOfGrad g i := by
  simp only [curlOfGrad, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem curlGradOfSecondDeriv_add (h h' : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (fun ijl => h ijl + h' ijl) il = curlGradOfSecondDeriv h il + curlGradOfSecondDeriv h' il := by
  simp only [curlGradOfSecondDeriv, mul_add, Finset.sum_add_distrib]

theorem curlGradOfSecondDeriv_smul (c : ℂ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (fun ijl => c * h ijl) il = c * curlGradOfSecondDeriv h il := by
  simp only [curlGradOfSecondDeriv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem curlGradOfSecondDeriv_add' (h h' : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (h + h') il = curlGradOfSecondDeriv h il + curlGradOfSecondDeriv h' il :=
  curlGradOfSecondDeriv_add h h' il

theorem curlGradOfSecondDeriv_smul' (c : ℂ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (c • h) il = c * curlGradOfSecondDeriv h il :=
  curlGradOfSecondDeriv_smul c h il

theorem curlOfGrad_zero (i : Fin 3) : curlOfGrad (fun _ => 0) i = 0 := by
  simp [curlOfGrad]

theorem curlGradOfSecondDeriv_zero (il : Fin 3 × Fin 3) : curlGradOfSecondDeriv (fun _ => 0) il = 0 := by
  simp [curlGradOfSecondDeriv]

theorem pairForm_add_left (gW hW) (x x' y : Slot → ℂ) :
    pairForm gW hW (x + x') y = pairForm gW hW x y + pairForm gW hW x' y := by
  simp only [pairForm, stretchBilin, Pi.add_apply, curlOfGrad_add, Fin.sum_univ_three]
  ring

theorem pairForm_add_right (gW hW) (x y y' : Slot → ℂ) :
    pairForm gW hW x (y + y') = pairForm gW hW x y + pairForm gW hW x y' := by
  simp only [pairForm, stretchBilin, Pi.add_apply, curlOfGrad_add, Fin.sum_univ_three]
  ring

theorem pairForm_smul_left (gW hW) (c : ℂ) (x y : Slot → ℂ) :
    pairForm gW hW (c • x) y = c * pairForm gW hW x y := by
  simp only [pairForm, stretchBilin, Pi.smul_apply, smul_eq_mul, curlOfGrad_smul, Fin.sum_univ_three]
  ring

theorem pairForm_smul_right (gW hW) (c : ℂ) (x y : Slot → ℂ) :
    pairForm gW hW x (c • y) = c * pairForm gW hW x y := by
  simp only [pairForm, stretchBilin, Pi.smul_apply, smul_eq_mul, curlOfGrad_smul, Fin.sum_univ_three]
  ring

def pairLinear (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    (Slot → ℂ) →ₗ[ℂ] (Slot → ℂ) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (pairForm gW hW) (pairForm_add_left gW hW) (pairForm_smul_left gW hW)
    (pairForm_add_right gW hW) (pairForm_smul_right gW hW)

theorem pairForm_expand (gW hW) (x y : Slot → ℂ) :
    pairForm gW hW x y = ∑ p, ∑ q, x p * y q * pairForm gW hW (Pi.single p 1) (Pi.single q 1) := by
  have hx : x = ∑ p, x p • (Pi.single p 1 : Slot → ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have hy : y = ∑ q, y q • (Pi.single q 1 : Slot → ℂ) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply]
  have h : pairForm gW hW x y = pairLinear gW hW x y := rfl
  rw [h]
  conv_lhs => rw [hx, hy]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  have e : pairLinear gW hW (Pi.single p 1) (Pi.single q 1) = pairForm gW hW (Pi.single p 1) (Pi.single q 1) := rfl
  rw [e]
  ring

theorem pairForm_add_W (gW gW' hW hW') (x y : Slot → ℂ) :
    pairForm (gW + gW') (hW + hW') x y = pairForm gW hW x y + pairForm gW' hW' x y := by
  simp only [pairForm, stretchBilin, Pi.add_apply, curlGradOfSecondDeriv_add', add_mul, mul_add, add_div,
    Finset.sum_add_distrib]
  ring

theorem pairForm_smul_W (c : ℂ) (gW hW) (x y : Slot → ℂ) :
    pairForm (c • gW) (c • hW) x y = c * pairForm gW hW x y := by
  simp only [pairForm, stretchBilin, Pi.smul_apply, smul_eq_mul, curlGradOfSecondDeriv_smul', Fin.sum_univ_three]
  ring

theorem pairForm_zero_W (x y : Slot → ℂ) : pairForm 0 0 x y = 0 := by
  have h := pairForm_smul_W 0 0 0 x y
  simp only [zero_smul, zero_mul] at h
  exact h

theorem pairForm_sum_W {ι : Type*} (S : Finset ι) (gW : ι → Fin 3 × Fin 3 → ℂ) (hW : ι → Fin 3 × Fin 3 × Fin 3 → ℂ)
    (x y : Slot → ℂ) :
    pairForm (∑ b ∈ S, gW b) (∑ b ∈ S, hW b) x y = ∑ b ∈ S, pairForm (gW b) (hW b) x y := by
  classical
  induction S using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, pairForm_zero_W]
  | insert a S ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Finset.sum_insert ha, pairForm_add_W, ih]

theorem pairForm_conj (gW hW) (x y : Slot → ℂ) :
    pairForm (fun ij => (starRingEnd ℂ) (gW ij)) (fun ijl => (starRingEnd ℂ) (hW ijl))
      (fun k => (starRingEnd ℂ) (x k)) (fun k => (starRingEnd ℂ) (y k))
      = (starRingEnd ℂ) (pairForm gW hW x y) := by
  simp only [pairForm, stretchBilin, curlOfGrad, curlGradOfSecondDeriv, map_add, map_neg, map_sum, map_mul,
    map_div₀, map_one, map_ofNat, Complex.conj_ofReal]

theorem pairForm_real_conj (gW hW) (x : Slot → ℝ) :
    pairForm (fun ij => (starRingEnd ℂ) (gW ij)) (fun ijl => (starRingEnd ℂ) (hW ijl))
      (fun k => ((x k : ℝ) : ℂ)) (fun k => ((x k : ℝ) : ℂ))
      = (starRingEnd ℂ) (pairForm gW hW (fun k => ((x k : ℝ) : ℂ)) (fun k => ((x k : ℝ) : ℂ))) := by
  rw [← pairForm_conj]
  simp only [Complex.conj_ofReal]

theorem re_pairForm_of_expansion {ι : Type*} (S : Finset ι) (z : ι → ℂ) (Ag : ι → Fin 3 × Fin 3 → ℂ)
    (Ah : ι → Fin 3 × Fin 3 × Fin 3 → ℂ) (wg : Fin 3 × Fin 3 → ℝ) (wh : Fin 3 × Fin 3 × Fin 3 → ℝ)
    (hg : ∀ ij, wg ij = ∑ b ∈ S, (z b * Ag b ij).re) (hh : ∀ ijl, wh ijl = ∑ b ∈ S, (z b * Ah b ijl).re)
    (x : Slot → ℝ) :
    pairForm (fun ij => ((wg ij : ℝ) : ℂ)) (fun ijl => ((wh ijl : ℝ) : ℂ)) (fun k => ((x k : ℝ) : ℂ))
        (fun k => ((x k : ℝ) : ℂ))
      = ((∑ b ∈ S, (z b * pairForm (Ag b) (Ah b) (fun k => ((x k : ℝ) : ℂ)) (fun k => ((x k : ℝ) : ℂ))).re : ℝ) : ℂ) := by
  have eg : (fun ij => ((wg ij : ℝ) : ℂ)) = ∑ b ∈ S, ((1 / 2 : ℂ) • (z b • Ag b)
      + (1 / 2 : ℂ) • (fun ij => (starRingEnd ℂ) ((z b • Ag b) ij))) := by
    funext ij
    rw [hg ij, Finset.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.re_eq_add_conj]
    ring
  have eh : (fun ijl => ((wh ijl : ℝ) : ℂ)) = ∑ b ∈ S, ((1 / 2 : ℂ) • (z b • Ah b)
      + (1 / 2 : ℂ) • (fun ijl => (starRingEnd ℂ) ((z b • Ah b) ijl))) := by
    funext ijl
    rw [hh ijl, Finset.sum_apply]
    push_cast
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Complex.re_eq_add_conj]
    ring
  rw [eg, eh, pairForm_sum_W]
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [pairForm_add_W, pairForm_smul_W, pairForm_smul_W, pairForm_smul_W, pairForm_real_conj, pairForm_smul_W,
    Complex.re_eq_add_conj]
  ring

section Rotation

open Coercive.StretchInternal Coercive.Internal.ModeRotation

def frameSecondDeriv (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) (i j l : Fin 3) : ℝ :=
  axialRot (-φ) (H τ (axialRot φ y) (axialRot φ (unitVector j)) (axialRot φ (unitVector l))) i

def curlGradReal (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (k n : Fin 3) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, alternatingSymbol k a b * h b n a

def realForm (wg vg : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(∑ i : Fin 3, ∑ j : Fin 3, curlMat s i * ((wg i j + wg j i) / 2) * curlMat s j) + bilin vg u s

theorem stretchFormWith_eq_realForm (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (x : Space) :
    CoerciveWeak.stretchFormWith W HW v G σ x = realForm (coordMat (fderiv ℝ (W σ) x))
      (fun j m => vortGrad (HW σ x) j m) (fun m => v σ x m) (coordMat (G σ x)) := by
  simp only [CoerciveWeak.stretchFormWith, realForm, bilin, curlVec_eq_curlMat, curlMat, coordMat]
  ring

theorem unit_expand (φ : ℝ) (j : Fin 3) :
    unitVector j = ∑ b : Fin 3, rm φ j b • axialRot φ (unitVector b) := by
  have h := Real.sin_sq_add_cos_sq φ
  ext k
  fin_cases j <;> fin_cases k <;> simp [rm_eq, axialRot, unitVector, Fin.sum_univ_three] <;> grind

theorem axialRot_sum_smul (ψ : ℝ) (r : Fin 3 → ℝ) (X : Fin 3 → Space) :
    axialRot ψ (∑ b : Fin 3, r b • X b) = ∑ b : Fin 3, r b • axialRot ψ (X b) := by
  have e : ∀ z, axialRot ψ z = Coercive.RotationInternal.axialRotEquiv ψ z := fun _ => rfl
  simp only [e, map_sum, map_smul]

theorem secondDeriv_coord_conj (φ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) (i j l : Fin 3) :
    B (unitVector j) (unitVector l) i = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3,
      rm φ i a * rm φ j b * rm φ l c *
        axialRot (-φ) (B (axialRot φ (unitVector b)) (axialRot φ (unitVector c))) a := by
  have h1 : B (unitVector j) (unitVector l) = ∑ b : Fin 3, rm φ j b •
      ∑ c : Fin 3, rm φ l c • B (axialRot φ (unitVector b)) (axialRot φ (unitVector c)) := by
    conv_lhs => rw [unit_expand φ j, unit_expand φ l]
    simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum,
      smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm]
  have h2 := vec_coord_rot φ (B (unitVector j) (unitVector l)) i
  rw [h2, h1, rotVec]
  simp only [axialRot_sum_smul, coord_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem vortGrad_conj (φ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) :
    vortGrad B j m = conjM φ (curlGradReal (fun a b c =>
      axialRot (-φ) (B (axialRot φ (unitVector b)) (axialRot φ (unitVector c))) a)) j m := by
  set h : Fin 3 → Fin 3 → Fin 3 → ℝ := fun a b c =>
    axialRot (-φ) (B (axialRot φ (unitVector b)) (axialRot φ (unitVector c))) a with hh
  have e1 : vortGrad B j m = ∑ n : Fin 3, rm φ m n * curlMat (conjM φ (fun a c => h a n c)) j := by
    simp only [vortGrad, secondDeriv_coord_conj φ B, curlMat, conjM, Fin.sum_univ_three]
    ring
  have e2 : ∀ n, curlMat (conjM φ (fun a c => h a n c)) j = ∑ k : Fin 3, rm φ j k * curlGradReal h k n := by
    intro n
    rw [curlMat_conjM, rotVec]
    rfl
  rw [e1]
  simp only [e2, conjM, Fin.sum_univ_three]
  ring

theorem rotT_rotVec (φ : ℝ) (c : Fin 3 → ℝ) : rotT φ (rotVec φ c) = c := by
  have h := Real.sin_sq_add_cos_sq φ
  funext a
  fin_cases a <;> simp [rotT, rotVec, rm_eq, Fin.sum_univ_three] <;> grind

theorem realForm_conj (φ : ℝ) (wg vg : Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) :
    realForm (conjM φ wg) (conjM φ vg) (rotVec φ u) (conjM φ s) = realForm wg vg u s := by
  have hc : ∀ i, curlMat (conjM φ s) i = rotVec φ (curlMat s) i := curlMat_conjM φ s
  have hsym : ∀ i j, (conjM φ wg i j + conjM φ wg j i) / 2 = conjM φ (fun a c => (wg a c + wg c a) / 2) i j := by
    intro i j
    simp only [conjM, Fin.sum_univ_three]
    ring
  have hq := quad_conjM φ (fun a c => (wg a c + wg c a) / 2) (rotVec φ (curlMat s))
  rw [rotT_rotVec] at hq
  unfold realForm
  rw [bilin_conjM]
  simp only [hc, hsym]
  rw [hq]

theorem curlOfGrad_ofReal (s : Fin 3 → Fin 3 → ℝ) (i : Fin 3) :
    curlOfGrad (fun ij => ((s ij.1 ij.2 : ℝ) : ℂ)) i = ((curlMat s i : ℝ) : ℂ) := by
  simp only [curlOfGrad, curlMat]
  push_cast
  rfl

theorem curlGradOfSecondDeriv_ofReal (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (fun ijl => ((h ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ)) il = ((curlGradReal h il.1 il.2 : ℝ) : ℂ) := by
  simp only [curlGradOfSecondDeriv, curlGradReal]
  push_cast
  rfl

def slotOf (u : Fin 3 → ℝ) (s : Fin 3 → Fin 3 → ℝ) : Slot → ℝ := Sum.elim u (fun ij => s ij.1 ij.2)

theorem pairForm_ofReal (wg : Fin 3 → Fin 3 → ℝ) (wh : Fin 3 → Fin 3 → Fin 3 → ℝ) (u : Fin 3 → ℝ)
    (s : Fin 3 → Fin 3 → ℝ) :
    pairForm (fun ij => ((wg ij.1 ij.2 : ℝ) : ℂ)) (fun ijl => ((wh ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ))
        (fun k => ((slotOf u s k : ℝ) : ℂ)) (fun k => ((slotOf u s k : ℝ) : ℂ))
      = ((realForm wg (curlGradReal wh) u s : ℝ) : ℂ) := by
  have e0 : (fun i : Fin 3 => ((slotOf u s (Sum.inl i) : ℝ) : ℂ)) = fun i => ((u i : ℝ) : ℂ) := rfl
  have e1 : (fun ij : Fin 3 × Fin 3 => ((slotOf u s (Sum.inr ij) : ℝ) : ℂ)) = fun ij => ((s ij.1 ij.2 : ℝ) : ℂ) := rfl
  have eb : bilin (curlGradReal wh) u s = ∑ j : Fin 3, (∑ m : Fin 3, u m * curlGradReal wh j m) * curlMat s j
      + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * curlGradReal wh j m * s i j * u l := rfl
  unfold pairForm
  rw [e0, e1]
  unfold stretchBilin
  simp only [curlOfGrad_ofReal, curlGradOfSecondDeriv_ofReal]
  unfold realForm
  rw [eb]
  push_cast
  ring

end Rotation


open Coercive.StretchInternal Coercive.Internal.ModeRotation Coercive.RotationInternal


theorem rotNeg_apply (φ : ℝ) (z : Space) (i : Fin 3) : axialRot (-φ) z i = ∑ a : Fin 3, rm φ a i * z a := by
  fin_cases i <;> simp [rm_eq, axialRot, unitVector, Fin.sum_univ_three, Real.cos_neg, Real.sin_neg]

theorem col_expand (φ : ℝ) (j : Fin 3) : axialRot φ (unitVector j) = ∑ b : Fin 3, rm φ b j • unitVector b := by
  ext k
  fin_cases k <;> simp [rm, unitVector, Fin.sum_univ_three]

theorem frame_shift3 (φ φ' : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) (i j l : Fin 3) :
    ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, rm φ a i * rm φ b j * rm φ c l *
        axialRot (-φ') (B (axialRot φ' (unitVector b)) (axialRot φ' (unitVector c))) a
      = axialRot (-(φ' + φ)) (B (axialRot (φ' + φ) (unitVector j)) (axialRot (φ' + φ) (unitVector l))) i := by
  have e1 : ∀ m, axialRot (φ' + φ) (unitVector m) = ∑ b : Fin 3, rm φ b m • axialRot φ' (unitVector b) := by
    intro m
    rw [axialRot_add, col_expand φ m, axialRot_sum_smul]
  have e2 : ∀ z, axialRot (-(φ' + φ)) z = axialRot (-φ) (axialRot (-φ') z) := by
    intro z
    rw [← axialRot_add]
    congr 1
    ring
  rw [e2, rotNeg_apply, e1 j, e1 l]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, axialRot_sum_smul,
    coord_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  ring

theorem frame_shift2 (φ φ' : ℝ) (A : Space →L[ℝ] Space) (i j : Fin 3) :
    ∑ a : Fin 3, ∑ b : Fin 3, rm φ a i * rm φ b j * axialRot (-φ') (A (axialRot φ' (unitVector b))) a
      = axialRot (-(φ' + φ)) (A (axialRot (φ' + φ) (unitVector j))) i := by
  have e1 : ∀ m, axialRot (φ' + φ) (unitVector m) = ∑ b : Fin 3, rm φ b m • axialRot φ' (unitVector b) := by
    intro m
    rw [axialRot_add, col_expand φ m, axialRot_sum_smul]
  have e2 : ∀ z, axialRot (-(φ' + φ)) z = axialRot (-φ) (axialRot (-φ') z) := by
    intro z
    rw [← axialRot_add]
    congr 1
    ring
  rw [e2, rotNeg_apply, e1 j]
  simp only [map_sum, map_smul, axialRot_sum_smul, coord_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring


theorem axialRot_add_two_pi (x : ℝ) (z : Space) : axialRot (x + 2 * Real.pi) z = axialRot x z :=
  Coercive.axialRotationHolds_proof.2.2.2.1 x z

theorem axialRot_neg_add_two_pi (x : ℝ) (z : Space) : axialRot (-(x + 2 * Real.pi)) z = axialRot (-x) z := by
  rw [← axialRot_add_two_pi (-(x + 2 * Real.pi)) z]
  congr 1
  ring

theorem frameSecondDeriv_periodic_time {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hper : IsTimePeriodic HW)
    (y : Space) (τ φ : ℝ) (i j l : Fin 3) : frameSecondDeriv HW y (τ + 1) φ i j l = frameSecondDeriv HW y τ φ i j l := by
  simp only [frameSecondDeriv, hper τ]

theorem frameSecondDeriv_periodic_angle (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ)
    (i j l : Fin 3) : frameSecondDeriv HW y τ (φ + 2 * Real.pi) i j l = frameSecondDeriv HW y τ φ i j l := by
  simp only [frameSecondDeriv, axialRot_add_two_pi, axialRot_neg_add_two_pi]

theorem fibGrad_periodic_time {G : ℝ → Space → (Space →L[ℝ] Space)} (hper : IsTimePeriodic G)
    (y : Space) (τ φ : ℝ) (i j : Fin 3) : fibGrad G y (τ + 1) φ i j = fibGrad G y τ φ i j := by
  simp only [fibGrad, hper τ]

theorem fibGrad_periodic_angle (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ)
    (i j : Fin 3) : fibGrad G y τ (φ + 2 * Real.pi) i j = fibGrad G y τ φ i j := by
  simp only [fibGrad, axialRot_add_two_pi, axialRot_neg_add_two_pi]

theorem modeSecondDeriv_zero_eq (β : ℤ × ℤ) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y : Space)
    (i j l : Fin 3) :
    modeSecondDeriv β HW 0 y (i, j, l) = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor β τ φ * ((frameSecondDeriv HW y τ φ i j l : ℝ) : ℂ) := by
  simp only [modeSecondDeriv, modeAverage_eq, zero_add, frameSecondDeriv]

theorem modeGrad_zero_eq (β : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (i j : Fin 3) :
    modeGrad β G 0 y (i, j) = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
      expFactor β τ φ * ((fibGrad G y τ φ i j : ℝ) : ℂ) := by
  simp only [modeGrad, modeAverage_eq, zero_add, fibGrad]

theorem sum_triple {M : Type*} [AddCommMonoid M] (f : Fin 3 → Fin 3 → Fin 3 → M) :
    ∑ x : Fin 3 × Fin 3 × Fin 3, f x.1 x.2.1 x.2.2 = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, f a b c := by
  simp only [Fintype.sum_prod_type]

theorem sum_pair {M : Type*} [AddCommMonoid M] (f : Fin 3 → Fin 3 → M) :
    ∑ x : Fin 3 × Fin 3, f x.1 x.2 = ∑ a : Fin 3, ∑ b : Fin 3, f a b := by
  simp only [Fintype.sum_prod_type]

theorem frameSecondDeriv_expansion {S : Finset (ℤ × ℤ)} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hE : IsHarmonicExpansion S W HW)
    (hper : IsTimePeriodic HW) (y : Space)
    (hint : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
      axialRot (-θ.2) (HW (τ + θ.1) (axialRot θ.2 (axialRot φ y)) (axialRot θ.2 (unitVector x.2.1))
        (axialRot θ.2 (unitVector x.2.2))) x.1) boxMeasure)
    (τ φ : ℝ) (i j l : Fin 3) :
    frameSecondDeriv HW y τ φ i j l = ∑ β ∈ S, (phase β τ φ * modeSecondDeriv β HW 0 y (i, j, l)).re := by
  set r : Fin 3 × Fin 3 × Fin 3 → ℝ := fun x => rm φ x.1 i * rm φ x.2.1 j * rm φ x.2.2 l with hr
  have h0 := frame_shift3 φ 0 (HW τ (axialRot φ y)) i j l
  simp only [neg_zero, zero_add, axialRot_zero] at h0
  have hf : frameSecondDeriv HW y τ φ i j l = ∑ x : Fin 3 × Fin 3 × Fin 3,
      r x * ∑ β ∈ S, (modeSecondDeriv β HW τ (axialRot φ y) x).re := by
    rw [frameSecondDeriv, ← h0, ← sum_triple]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hE.hessian_span τ (axialRot φ y) x.1 x.2.1 x.2.2]
  have hβ : ∀ β : ℤ × ℤ, ∑ x : Fin 3 × Fin 3 × Fin 3, ((r x : ℝ) : ℂ) * modeSecondDeriv β HW τ (axialRot φ y) x
      = phase β τ φ * modeSecondDeriv β HW 0 y (i, j, l) := by
    intro β
    have hsum := modeAverage_sum β r (fun x τ' φ' => axialRot (-φ') (HW (τ + τ') (axialRot φ' (axialRot φ y))
      (axialRot φ' (unitVector x.2.1)) (axialRot φ' (unitVector x.2.2))) x.1) (hint τ φ)
    have hpt : ∀ τ' φ' : ℝ, (∑ x : Fin 3 × Fin 3 × Fin 3, r x * axialRot (-φ') (HW (τ + τ')
        (axialRot φ' (axialRot φ y)) (axialRot φ' (unitVector x.2.1)) (axialRot φ' (unitVector x.2.2))) x.1)
        = frameSecondDeriv HW y (τ + τ') (φ' + φ) i j l := by
      intro τ' φ'
      rw [frameSecondDeriv, ← axialRot_add, ← frame_shift3 φ φ', ← sum_triple]
    simp only [hpt] at hsum
    have hsh := shifted_average β (fun τ φ => ((frameSecondDeriv HW y τ φ i j l : ℝ) : ℂ))
      (fun τ φ => by simp only [frameSecondDeriv_periodic_time hper]) (fun τ φ => by simp only [frameSecondDeriv_periodic_angle])
      τ φ
    rw [modeSecondDeriv_zero_eq, ← mul_assoc, mul_comm (phase β τ φ), mul_assoc, ← hsh, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show modeSecondDeriv β HW τ (axialRot φ y) x = (1 / (2 * Real.pi) : ℂ) * ∫ τ' in (0 : ℝ)..1,
      ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β τ' φ' * ((axialRot (-φ') (HW (τ + τ') (axialRot φ' (axialRot φ y))
        (axialRot φ' (unitVector x.2.1)) (axialRot φ' (unitVector x.2.2))) x.1 : ℝ) : ℂ) from rfl]
    ring
  rw [hf]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← hβ β, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.re_ofReal_mul]

theorem frameGrad_expansion {S : Finset (ℤ × ℤ)} {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hE : IsHarmonicExpansion S W HW)
    (hper : IsTimePeriodic (gradField W)) (y : Space)
    (hint : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
      axialRot (-θ.2) (gradField W (τ + θ.1) (axialRot θ.2 (axialRot φ y)) (axialRot θ.2 (unitVector x.2))) x.1)
      boxMeasure)
    (τ φ : ℝ) (i j : Fin 3) :
    fibGrad (gradField W) y τ φ i j = ∑ β ∈ S, (phase β τ φ * modeGrad β (gradField W) 0 y (i, j)).re := by
  set r : Fin 3 × Fin 3 → ℝ := fun x => rm φ x.1 i * rm φ x.2 j with hr
  have h0 := frame_shift2 φ 0 (gradField W τ (axialRot φ y)) i j
  simp only [neg_zero, zero_add, axialRot_zero] at h0
  have hf : fibGrad (gradField W) y τ φ i j = ∑ x : Fin 3 × Fin 3,
      r x * ∑ β ∈ S, (modeGrad β (gradField W) τ (axialRot φ y) x).re := by
    rw [fibGrad, ← h0, ← sum_pair]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← hE.gradient_span τ (axialRot φ y) x.1 x.2]
    rfl
  have hβ : ∀ β : ℤ × ℤ, ∑ x : Fin 3 × Fin 3, ((r x : ℝ) : ℂ) * modeGrad β (gradField W) τ (axialRot φ y) x
      = phase β τ φ * modeGrad β (gradField W) 0 y (i, j) := by
    intro β
    have hsum := modeAverage_sum β r (fun x τ' φ' => axialRot (-φ') (gradField W (τ + τ')
      (axialRot φ' (axialRot φ y)) (axialRot φ' (unitVector x.2))) x.1) (hint τ φ)
    have hpt : ∀ τ' φ' : ℝ, (∑ x : Fin 3 × Fin 3, r x * axialRot (-φ') (gradField W (τ + τ')
        (axialRot φ' (axialRot φ y)) (axialRot φ' (unitVector x.2))) x.1)
        = fibGrad (gradField W) y (τ + τ') (φ' + φ) i j := by
      intro τ' φ'
      rw [fibGrad, ← axialRot_add, ← frame_shift2 φ φ', ← sum_pair]
    simp only [hpt] at hsum
    have hsh := shifted_average β (fun τ φ => ((fibGrad (gradField W) y τ φ i j : ℝ) : ℂ))
      (fun τ φ => by simp only [fibGrad_periodic_time hper]) (fun τ φ => by simp only [fibGrad_periodic_angle])
      τ φ
    rw [modeGrad_zero_eq, ← mul_assoc, mul_comm (phase β τ φ), mul_assoc, ← hsh, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [show modeGrad β (gradField W) τ (axialRot φ y) x = (1 / (2 * Real.pi) : ℂ) * ∫ τ' in (0 : ℝ)..1,
      ∫ φ' in (0 : ℝ)..(2 * Real.pi), expFactor β τ' φ' * ((axialRot (-φ') (gradField W (τ + τ')
        (axialRot φ' (axialRot φ y)) (axialRot φ' (unitVector x.2))) x.1 : ℝ) : ℂ) from rfl]
    ring
  rw [hf]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [← hβ β, Complex.re_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Complex.re_ofReal_mul]



theorem stretchFormWith_orbit (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) :
    CoerciveWeak.stretchFormWith W HW v G τ (axialRot φ y) = realForm (fibGrad (gradField W) y τ φ)
      (curlGradReal (frameSecondDeriv HW y τ φ)) (fibVel v y τ φ) (fibGrad G y τ φ) := by
  rw [stretchFormWith_eq_realForm]
  have hg : coordMat (fderiv ℝ (W τ) (axialRot φ y)) = conjM φ (fibGrad (gradField W) y τ φ) := by
    funext i j
    exact clm_coord_conj φ _ i j
  have hG : coordMat (G τ (axialRot φ y)) = conjM φ (fibGrad G y τ φ) := by
    funext i j
    exact clm_coord_conj φ _ i j
  have hv : (fun m => v τ (axialRot φ y) m) = rotVec φ (fibVel v y τ φ) := by
    funext m
    exact vec_coord_rot φ _ m
  have hH : (fun j m => vortGrad (HW τ (axialRot φ y)) j m) = conjM φ (curlGradReal (frameSecondDeriv HW y τ φ)) := by
    funext j m
    exact vortGrad_conj φ _ j m
  rw [hg, hG, hv, hH, realForm_conj]

def slotFn (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (k : Slot) (τ φ : ℝ) : ℝ :=
  slotOf (fibVel v y τ φ) (fibGrad G y τ φ) k

def slotMode (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (ξ : ℤ × ℤ) : Slot → ℂ :=
  Sum.elim (modeVel ξ v 0 y) (modeGrad ξ G 0 y)

theorem torusMode_slotFn (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space)
    (ξ : ℤ × ℤ) (k : Slot) : torusMode ξ (slotFn v G y k) = slotMode v G y ξ k := by
  rcases k with i | ij
  · simp only [torusMode, slotFn, slotOf, slotMode, Sum.elim_inl, modeVel, modeAverage, zero_add, fibVel]
  · simp only [torusMode, slotFn, slotOf, slotMode, Sum.elim_inr, modeGrad, modeAverage, zero_add, fibGrad]

theorem orbit_stretch_expansion {S : Finset (ℤ × ℤ)} (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ)
    (hg : ∀ i j, fibGrad (gradField W) y τ φ i j = ∑ β ∈ S, (phase β τ φ * modeGrad β (gradField W) 0 y (i, j)).re)
    (hh : ∀ i j l, frameSecondDeriv HW y τ φ i j l = ∑ β ∈ S, (phase β τ φ * modeSecondDeriv β HW 0 y (i, j, l)).re) :
    CoerciveWeak.stretchFormWith W HW v G τ (axialRot φ y) = ∑ β ∈ S, (phase β τ φ *
      pairForm (modeGrad β (gradField W) 0 y) (modeSecondDeriv β HW 0 y) (fun k => ((slotFn v G y k τ φ : ℝ) : ℂ))
        (fun k => ((slotFn v G y k τ φ : ℝ) : ℂ))).re := by
  rw [stretchFormWith_orbit]
  have h1 := pairForm_ofReal (fibGrad (gradField W) y τ φ) (frameSecondDeriv HW y τ φ) (fibVel v y τ φ) (fibGrad G y τ φ)
  have h2 := re_pairForm_of_expansion S (fun β => phase β τ φ) (fun β => modeGrad β (gradField W) 0 y)
    (fun β => modeSecondDeriv β HW 0 y) (fun ij => fibGrad (gradField W) y τ φ ij.1 ij.2)
    (fun ijl => frameSecondDeriv HW y τ φ ijl.1 ijl.2.1 ijl.2.2) (fun ij => hg ij.1 ij.2)
    (fun ijl => hh ijl.1 ijl.2.1 ijl.2.2) (slotOf (fibVel v y τ φ) (fibGrad G y τ φ))
  rw [h1] at h2
  have h3 := congrArg Complex.re h2
  rw [Complex.ofReal_re, Complex.ofReal_re] at h3
  rw [h3]
  rfl

theorem iter_eq_box_real (f : ℝ → ℝ → ℝ) (hf : Integrable (fun p : ℝ × ℝ => f p.1 p.2) boxMeasure) :
    ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), f τ φ = ∫ p, f p.1 p.2 ∂boxMeasure := by
  rw [integral_prod _ hf, intervalIntegral.integral_of_le zero_le_one]
  congr 1
  funext τ
  rw [intervalIntegral.integral_of_le (by positivity)]

theorem norm_pairForm_le (gW hW) (x y : Slot → ℂ) :
    ‖pairForm gW hW x y‖ ≤ ∑ p, ∑ q, ‖pairForm gW hW (Pi.single p 1) (Pi.single q 1)‖ * (‖x p‖ * ‖y q‖) := by
  rw [pairForm_expand]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun q _ => le_of_eq ?_))
  rw [norm_mul, norm_mul]
  ring

theorem pairing_mean (hTorus : Coercive.TorusSquareSumHolds) (X : Slot → ℝ → ℝ → ℝ)
    (hX : ∀ k, MemLp (fun p : ℝ × ℝ => X k p.1 p.2) 2 boxMeasure) (gW : Fin 3 × Fin 3 → ℂ)
    (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (β : ℤ × ℤ) :
    Integrable (fun p : ℝ × ℝ => phase β p.1 p.2 * pairForm gW hW (fun k => ((X k p.1 p.2 : ℝ) : ℂ))
      (fun k => ((X k p.1 p.2 : ℝ) : ℂ))) boxMeasure ∧
    HasSum (fun ξ : ℤ × ℤ => (pairForm gW hW (fun k => torusMode ξ (X k))
        (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k)))
        + pairForm gW hW (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k))) (fun k => torusMode ξ (X k))) / 2)
      ((1 / (2 * Real.pi) : ℂ) * ∫ p, phase β p.1 p.2 * pairForm gW hW (fun k => ((X k p.1 p.2 : ℝ) : ℂ))
        (fun k => ((X k p.1 p.2 : ℝ) : ℂ)) ∂boxMeasure) ∧
    Summable (fun ξ : ℤ × ℤ => ‖(pairForm gW hW (fun k => torusMode ξ (X k))
        (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k)))
        + pairForm gW hW (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k))) (fun k => torusMode ξ (X k))) / 2‖) := by
  set c : Slot → Slot → ℂ := fun p q => pairForm gW hW (Pi.single p 1) (Pi.single q 1) with hc
  set A : Slot → Slot → ℂ := fun p q => (1 / (2 * Real.pi) : ℂ) *
    ∫ θ, phase β θ.1 θ.2 * ((X p θ.1 θ.2 * X q θ.1 θ.2 : ℝ) : ℂ) ∂boxMeasure with hA
  have hint : ∀ p q, Integrable (fun θ : ℝ × ℝ => phase β θ.1 θ.2 * ((X p θ.1 θ.2 * X q θ.1 θ.2 : ℝ) : ℂ))
      boxMeasure := fun p q => integrable_phase_mul β ((hX p).integrable_mul (hX q))
  have hpt : (fun θ : ℝ × ℝ => phase β θ.1 θ.2 * pairForm gW hW (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ))
      (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ))) = fun θ => ∑ p, ∑ q, c p q *
        (phase β θ.1 θ.2 * ((X p θ.1 θ.2 * X q θ.1 θ.2 : ℝ) : ℂ)) := by
    funext θ
    rw [pairForm_expand, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  have hI : Integrable (fun θ : ℝ × ℝ => phase β θ.1 θ.2 * pairForm gW hW (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ))
      (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ))) boxMeasure := by
    rw [hpt]
    exact integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => (hint p q).const_mul _
  have hval : (1 / (2 * Real.pi) : ℂ) * ∫ θ, phase β θ.1 θ.2 * pairForm gW hW (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ))
      (fun k => ((X k θ.1 θ.2 : ℝ) : ℂ)) ∂boxMeasure = ∑ p, ∑ q, A p q * c p q := by
    rw [hpt, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => (hint p q).const_mul _,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [integral_finsetSum _ fun q _ => (hint p q).const_mul _, Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_const_mul, hA]
    ring
  have hPQ : ∀ p q, HasSum (fun ξ : ℤ × ℤ => torusMode ξ (X p) * (starRingEnd ℂ) (torusMode (ξ + β) (X q))) (A p q) :=
    fun p q => hasSum_pairing hTorus (X p) (X q) (hX p) (hX q) β
  have hAsymm : ∀ p q, A q p = A p q := by
    intro p q
    simp only [hA, mul_comm (X q _ _)]
  have h1 : HasSum (fun ξ : ℤ × ℤ => pairForm gW hW (fun k => torusMode ξ (X k))
      (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k)))) (∑ p, ∑ q, A p q * c p q) := by
    have := hasSum_sum (s := Finset.univ) fun p _ => hasSum_sum (s := Finset.univ) fun q _ => (hPQ p q).mul_right (c p q)
    refine this.congr_fun fun ξ => ?_
    rw [pairForm_expand]
  have h2 : HasSum (fun ξ : ℤ × ℤ => pairForm gW hW (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (X k)))
      (fun k => torusMode ξ (X k))) (∑ p, ∑ q, A p q * c p q) := by
    have := hasSum_sum (s := Finset.univ) fun p _ => hasSum_sum (s := Finset.univ) fun q _ => (hPQ q p).mul_right (c p q)
    simp only [hAsymm] at this
    refine this.congr_fun fun ξ => ?_
    rw [pairForm_expand]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  refine ⟨hI, ?_, ?_⟩
  · rw [hval]
    have := (h1.add h2).div_const 2
    rw [← two_mul, mul_div_cancel_left₀ _ two_ne_zero] at this
    exact this
  · have hb : ∀ p q, Summable (fun ξ : ℤ × ℤ => ‖c p q‖ * (‖torusMode ξ (X p)‖ * ‖torusMode (ξ + β) (X q)‖)) :=
      fun p q => (summable_norm_pairing hTorus (X p) (X q) (hX p) (hX q) β).mul_left _
    have hsum : Summable (fun ξ : ℤ × ℤ => ((∑ p, ∑ q, ‖c p q‖ * (‖torusMode ξ (X p)‖ * ‖torusMode (ξ + β) (X q)‖))
        + ∑ p, ∑ q, ‖c p q‖ * (‖torusMode ξ (X q)‖ * ‖torusMode (ξ + β) (X p)‖)) / 2) :=
      ((summable_sum fun p _ => summable_sum fun q _ => hb p q).add
        (summable_sum fun p _ => summable_sum fun q _ =>
          (summable_norm_pairing hTorus (X q) (X p) (hX q) (hX p) β).mul_left ‖c p q‖)).div_const 2
    refine Summable.of_nonneg_of_le (fun ξ => norm_nonneg _) (fun ξ => ?_) hsum
    rw [norm_div, Complex.norm_ofNat]
    refine div_le_div_of_nonneg_right ((norm_add_le _ _).trans (add_le_add ?_ ?_)) (by norm_num)
    · refine (norm_pairForm_le gW hW _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.norm_conj]
    · refine (norm_pairForm_le gW hW _ _).trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      rw [Complex.norm_conj]
      ring

theorem stretchTriple_eq_pairForm (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (ξ β : ℤ × ℤ) :
    stretchTriple gW hW (modeVel ξ v 0 y) (modeGrad ξ G 0 y) (star (modeVel (ξ + β) v 0 y))
        (star (modeGrad (ξ + β) G 0 y))
      = (pairForm gW hW (fun k => torusMode ξ (slotFn v G y k))
          (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (slotFn v G y k)))
        + pairForm gW hW (fun k => (starRingEnd ℂ) (torusMode (ξ + β) (slotFn v G y k)))
          (fun k => torusMode ξ (slotFn v G y k))) / 2 := by
  simp only [torusMode_slotFn]
  rfl

theorem point_identity (hTorus : Coercive.TorusSquareSumHolds) {S : Finset (ℤ × ℤ)} (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space)
    (hX : ∀ k, MemLp (fun p : ℝ × ℝ => slotFn v G y k p.1 p.2) 2 boxMeasure)
    (hg : ∀ τ φ i j, fibGrad (gradField W) y τ φ i j
      = ∑ β ∈ S, (phase β τ φ * modeGrad β (gradField W) 0 y (i, j)).re)
    (hh : ∀ τ φ i j l, frameSecondDeriv HW y τ φ i j l = ∑ β ∈ S, (phase β τ φ * modeSecondDeriv β HW 0 y (i, j, l)).re) :
    (∀ β ∈ S, Summable (fun ξ : ℤ × ℤ => ‖stretchTriple (modeGrad β (gradField W) 0 y) (modeSecondDeriv β HW 0 y)
        (modeVel ξ v 0 y) (modeGrad ξ G 0 y) (star (modeVel (ξ + β) v 0 y)) (star (modeGrad (ξ + β) G 0 y))‖)) ∧
    (1 / (2 * Real.pi)) * (∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        CoerciveWeak.stretchFormWith W HW v G τ (axialRot φ y))
      = ∑ β ∈ S, ∑' ξ : ℤ × ℤ, (stretchTriple (modeGrad β (gradField W) 0 y) (modeSecondDeriv β HW 0 y)
        (modeVel ξ v 0 y) (modeGrad ξ G 0 y) (star (modeVel (ξ + β) v 0 y)) (star (modeGrad (ξ + β) G 0 y))).re := by
  set F : ℤ × ℤ → ℝ × ℝ → ℂ := fun β θ => phase β θ.1 θ.2 * pairForm (modeGrad β (gradField W) 0 y)
    (modeSecondDeriv β HW 0 y) (fun k => ((slotFn v G y k θ.1 θ.2 : ℝ) : ℂ)) (fun k => ((slotFn v G y k θ.1 θ.2 : ℝ) : ℂ))
    with hF
  have PM := fun β => pairing_mean hTorus (slotFn v G y) hX (modeGrad β (gradField W) 0 y) (modeSecondDeriv β HW 0 y) β
  refine ⟨fun β _ => ?_, ?_⟩
  · refine (PM β).2.2.congr fun ξ => ?_
    rw [stretchTriple_eq_pairForm]
  have hpt : ∀ θ : ℝ × ℝ, CoerciveWeak.stretchFormWith W HW v G θ.1 (axialRot θ.2 y)
      = ∑ β ∈ S, (F β θ).re := fun θ =>
    orbit_stretch_expansion W HW v G y θ.1 θ.2 (hg θ.1 θ.2) (hh θ.1 θ.2)
  have hFi : ∀ β, Integrable (F β) boxMeasure := fun β => (PM β).1
  have hFre : ∀ β, Integrable (fun θ : ℝ × ℝ => (F β θ).re) boxMeasure := fun β => (hFi β).re
  have hreI : Integrable (fun θ : ℝ × ℝ => ∑ β ∈ S, (F β θ).re) boxMeasure :=
    integrable_finsetSum _ fun β _ => hFre β
  have hI : Integrable (fun θ : ℝ × ℝ => CoerciveWeak.stretchFormWith W HW v G θ.1 (axialRot θ.2 y)) boxMeasure := by
    refine hreI.congr (Filter.Eventually.of_forall fun θ => ?_)
    exact (hpt θ).symm
  rw [iter_eq_box_real (fun τ φ => CoerciveWeak.stretchFormWith W HW v G τ (axialRot φ y)) hI]
  simp only [hpt]
  rw [integral_finsetSum _ fun β _ => hFre β, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  have hre : ∫ θ, (F β θ).re ∂boxMeasure = (∫ θ, F β θ ∂boxMeasure).re := by
    have := integral_re (hFi β)
    simpa using this
  have hsum := Complex.hasSum_re (PM β).2.1
  rw [hre]
  calc (1 / (2 * Real.pi)) * (∫ θ, F β θ ∂boxMeasure).re
      = ((1 / (2 * Real.pi) : ℂ) * ∫ θ, F β θ ∂boxMeasure).re := by
        rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.re_ofReal_mul]
    _ = _ := hsum.tsum_eq.symm
    _ = _ := tsum_congr fun ξ => by rw [stretchTriple_eq_pairForm]



theorem basis_expand (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext k
  fin_cases k <;> simp [unitVector, Fin.sum_univ_three]

theorem norm_unitVector (j : Fin 3) : ‖unitVector j‖ = 1 := by
  rw [unitVector, PiLp.norm_single, norm_one]

theorem opNorm_sq_le_matSq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have hb : ‖A‖ ≤ ∑ j : Fin 3, ‖A (unitVector j)‖ := by
    refine A.opNorm_le_bound (Finset.sum_nonneg fun j _ => norm_nonneg _) fun x => ?_
    conv_lhs => rw [basis_expand x]
    rw [map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [map_smul, norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs _).symm ▸ PiLp.norm_apply_le x j) (norm_nonneg _)
  have h0 : 0 ≤ ‖A‖ := norm_nonneg _
  unfold matSq
  simp only [Fin.sum_univ_three] at hb ⊢
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖), sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖), norm_nonneg (A (unitVector 0)),
    norm_nonneg (A (unitVector 1)), norm_nonneg (A (unitVector 2))]

theorem continuous_gradField {W : ℝ → Space → Space} (hW : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradField W z.1 z.2) := by
  have hd : ∀ z : ℝ × Space, gradField W z.1 z.2
      = (fderiv ℝ (fun w : ℝ × Space => W w.1 w.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
    rintro ⟨σ, y⟩
    have h1 := (hW.differentiable one_ne_zero (σ, y)).hasFDerivAt
    have h2 := h1.comp y (hasFDerivAt_prodMk_right (𝕜 := ℝ) σ y)
    exact h2.fderiv
  have hc : Continuous (fun z : ℝ × Space =>
      (fderiv ℝ (fun w : ℝ × Space => W w.1 w.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space)) :=
    (hW.continuous_fderiv one_ne_zero).clm_comp continuous_const
  exact hc.congr fun z => (hd z).symm

theorem memLp_slot (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (y : Space)
    (hv : MemLp (fun θ : ℝ × ℝ => v θ.1 (axialRot θ.2 y)) 2 boxMeasure)
    (hG : MemLp (fun θ : ℝ × ℝ => G θ.1 (axialRot θ.2 y)) 2 boxMeasure) (k : Slot) :
    MemLp (fun θ : ℝ × ℝ => slotFn v G y k θ.1 θ.2) 2 boxMeasure := by
  rcases k with i | ij
  · have hc : Continuous (fun q : (ℝ × ℝ) × Space => axialRot (-q.1.2) q.2 i) := by
      unfold axialRot
      fun_prop
    have hm := hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hv.1)
    refine hv.of_le hm (Filter.Eventually.of_forall fun θ => ?_)
    exact (PiLp.norm_apply_le _ i).trans (axialRot_norm _ _).le
  · have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space) =>
        axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector ij.2))) ij.1) := by
      unfold axialRot
      fun_prop
    have hm := hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk hG.1)
    refine hG.of_le hm (Filter.Eventually.of_forall fun θ => ?_)
    refine (PiLp.norm_apply_le _ ij.1).trans ?_
    rw [axialRot_norm]
    refine ((G θ.1 (axialRot θ.2 y)).le_opNorm _).trans ?_
    rw [axialRot_norm, norm_unitVector, mul_one]

theorem measurePreserving_shift (c : ℝ × ℝ) :
    MeasurePreserving (fun θ : ℝ × ℝ => ((θ.1 + c.1, θ.2 + c.2) : ℝ × ℝ)) volume volume :=
  (measurePreserving_add_right volume c.1).prod (measurePreserving_add_right volume c.2)

theorem integrable_shift_secondDeriv (B : ℝ × ℝ → (Space →L[ℝ] Space →L[ℝ] Space)) (hB : AEStronglyMeasurable B volume)
    (C : ℝ) (hC : ∀ θ, ‖B θ‖ ≤ C) (c : ℝ × ℝ) (x : Fin 3 × Fin 3 × Fin 3) :
    Integrable (fun θ : ℝ × ℝ => axialRot (-θ.2) (B (θ.1 + c.1, θ.2 + c.2) (axialRot θ.2 (unitVector x.2.1))
      (axialRot θ.2 (unitVector x.2.2))) x.1) boxMeasure := by
  have h1 := hB.comp_measurePreserving (measurePreserving_shift c)
  have h2 : AEStronglyMeasurable (fun θ : ℝ × ℝ => B (θ.1 + c.1, θ.2 + c.2)) boxMeasure :=
    h1.mono_ac boxMeasure_ac
  have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector x.2.1)) (axialRot q.1.2 (unitVector x.2.2))) x.1) := by
    unfold axialRot
    fun_prop
  have hm := hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk h2)
  refine Integrable.mono' (integrable_const C) hm (Filter.Eventually.of_forall fun θ => ?_)
  refine (PiLp.norm_apply_le _ x.1).trans ?_
  rw [axialRot_norm]
  refine ((B _ _).le_opNorm _).trans ?_
  rw [axialRot_norm, norm_unitVector, mul_one]
  refine ((B _).le_opNorm _).trans ?_
  rw [axialRot_norm, norm_unitVector, mul_one]
  exact hC _

theorem integrable_shift_grad (B : ℝ × ℝ → (Space →L[ℝ] Space)) (hB : AEStronglyMeasurable B volume)
    (C : ℝ) (hC : ∀ θ, ‖B θ‖ ≤ C) (c : ℝ × ℝ) (x : Fin 3 × Fin 3) :
    Integrable (fun θ : ℝ × ℝ => axialRot (-θ.2) (B (θ.1 + c.1, θ.2 + c.2) (axialRot θ.2 (unitVector x.2))) x.1)
      boxMeasure := by
  have h1 := hB.comp_measurePreserving (measurePreserving_shift c)
  have h2 : AEStronglyMeasurable (fun θ : ℝ × ℝ => B (θ.1 + c.1, θ.2 + c.2)) boxMeasure :=
    h1.mono_ac boxMeasure_ac
  have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space) =>
      axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector x.2))) x.1) := by
    unfold axialRot
    fun_prop
  have hm := hc.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk h2)
  refine Integrable.mono' (integrable_const C) hm (Filter.Eventually.of_forall fun θ => ?_)
  refine (PiLp.norm_apply_le _ x.1).trans ?_
  rw [axialRot_norm]
  refine ((B _).le_opNorm _).trans ?_
  rw [axialRot_norm, norm_unitVector, mul_one]
  exact hC _

end Internal.MeanStretch

open Internal.MeanStretch Coercive.StretchInternal Coercive.Internal.ModeRotation Coercive.RotationInternal in
theorem meanStretchModeSum (hPair : PairingModeIdentityHolds) : MeanStretchModeSumHolds := by
  intro k C nE nM D D₀ hW hE Γ P v G H g hv
  have hD0 : 0 ≤ D₀ := by
    have h := (hW.decay 0 0).1
    rw [norm_zero, add_zero, div_one] at h
    exact (norm_nonneg _).trans h
  have hone : ∀ y : Space, (1 : ℝ) ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  have hHb : ∀ σ y, ‖D.givenHess σ y‖ ≤ D₀ := fun σ y =>
    (hW.decay σ y).2.2.trans (div_le_self hD0 (one_le_pow₀ (hone y)))
  have hGb : ∀ σ y, ‖gradField D.given σ y‖ ≤ D₀ := fun σ y =>
    (hW.decay σ y).2.1.trans (div_le_self hD0 (one_le_pow₀ (hone y)))
  have hgc := continuous_gradField hW.smooth
  have hperG : IsTimePeriodic (gradField D.given) := by
    intro σ y
    have e : D.given (σ + 1) = D.given σ := funext (hW.periodic σ)
    simp only [gradField, e]
  have hGloc : ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖G σ y‖ ^ 2) < ⊤ := by
    intro R
    refine lt_of_le_of_lt ?_ (ENNReal.mul_lt_top (ENNReal.ofReal_lt_top (r := 3)) hv.gradient_finite)
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun σ => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (setLIntegral_le_lintegral _ _).trans (lintegral_mono fun y => ?_)
    rw [← ENNReal.ofReal_mul (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (opNorm_sq_le_matSq _)
  have hvL := ae_memLp_orbit hv.measurable_velocity
    (Coercive.perturbationLocalSquareIntegrabilityHolds_proof Γ P v G H g hv)
  have hGL := ae_memLp_orbit (u := G) hv.measurable_gradient hGloc
  have hHm := ae_aestronglyMeasurable_orbit hW.secondDeriv_measurable
  have hWm := ae_aestronglyMeasurable_orbit hgc.aestronglyMeasurable
  filter_upwards [hvL, hGL, hHm, hWm] with p hp1 hp2 hp3 hp4
  have hX := memLp_slot v G (planePoint p) hp1 hp2
  have hintH : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
      axialRot (-θ.2) (D.givenHess (τ + θ.1) (axialRot θ.2 (axialRot φ (planePoint p)))
        (axialRot θ.2 (unitVector x.2.1)) (axialRot θ.2 (unitVector x.2.2))) x.1) boxMeasure := by
    intro τ φ x
    have hi := integrable_shift_secondDeriv (fun θ : ℝ × ℝ => D.givenHess θ.1 (axialRot θ.2 (planePoint p))) hp3 D₀
      (fun θ => hHb _ _) (τ, φ) x
    refine hi.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only
    rw [add_comm θ.1 τ, axialRot_add]
  have hintG : ∀ τ φ : ℝ, ∀ x : Fin 3 × Fin 3, Integrable (fun θ : ℝ × ℝ =>
      axialRot (-θ.2) (gradField D.given (τ + θ.1) (axialRot θ.2 (axialRot φ (planePoint p)))
        (axialRot θ.2 (unitVector x.2))) x.1) boxMeasure := by
    intro τ φ x
    have hi := integrable_shift_grad (fun θ : ℝ × ℝ => gradField D.given θ.1 (axialRot θ.2 (planePoint p))) hp4 D₀
      (fun θ => hGb _ _) (τ, φ) x
    refine hi.congr (Filter.Eventually.of_forall fun θ => ?_)
    simp only
    rw [add_comm θ.1 τ, axialRot_add]
  have hh := frameSecondDeriv_expansion hE hW.secondDeriv_periodic (planePoint p) hintH
  have hg := frameGrad_expansion hE hperG (planePoint p) hintG
  exact point_identity Coercive.torusSquareSumHolds_proof D.given D.givenHess v G (planePoint p) hX hg hh

end Bridge

end CertCell

end Breakdown

import Breakdown.FracCell.StCentrePairing
import Breakdown.FracCell.CentreIdentityParts
import Breakdown.FracCell.ModelFormParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CentrePairingCentreInternal

open SteadyCert

def leftPoly (u : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℝ)
    (h : Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  -∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, (u l * g i l + a i l * w l) * h i j j

def curlPoly (g : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : ℝ := ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * g l j

def curlGradPoly (k : Fin 3 → Fin 3 → Fin 3 → ℝ) (r m : Fin 3) : ℝ :=
  ∑ b : Fin 3, ∑ q : Fin 3, permSign r b q * k q m b

def rightPoly (a : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℝ) : ℝ :=
  -(∑ i : Fin 3, ∑ l : Fin 3, curlPoly g i * a i l * curlPoly g l)
    + ∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * ∑ m : Fin 3, curlGradPoly k j m * w m)
        + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * w q * curlGradPoly k l j) * g i l

def gradTerm (a : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℝ)
    (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (q l i b j d : Fin 3) : ℝ :=
  k q j l * w i * g b d + a q l * g i j * g b d + a q l * w i * h b j d

def valueTerm (u : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (g : Fin 3 → Fin 3 → ℝ)
    (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (q i b d e j : Fin 3) : ℝ :=
  a q j * g i b * g d e + u q * h i j b * g d e + u q * g i b * h d j e

def partsSum (fA fU : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) : ℝ :=
  (-1 / 2 : ℝ) * fU 0 0 0 0 0 0
    + (-1 : ℝ) * fU 0 0 0 0 1 1
    + (-1 : ℝ) * fU 0 0 0 0 2 2
    + (1 / 2 : ℝ) * fU 0 0 1 0 1 0
    + (1 / 2 : ℝ) * fU 0 0 2 0 2 0
    + (-1 / 2 : ℝ) * fU 0 1 0 1 0 0
    + (-1 : ℝ) * fU 0 1 0 1 1 1
    + (-1 : ℝ) * fU 0 1 0 1 2 2
    + (1 / 2 : ℝ) * fU 0 1 1 1 1 0
    + (1 / 2 : ℝ) * fU 0 1 2 1 2 0
    + (-1 / 2 : ℝ) * fU 0 2 0 2 0 0
    + (-1 : ℝ) * fU 0 2 0 2 1 1
    + (-1 : ℝ) * fU 0 2 0 2 2 2
    + (1 / 2 : ℝ) * fU 0 2 1 2 1 0
    + (1 / 2 : ℝ) * fU 0 2 2 2 2 0
    + (1 / 2 : ℝ) * fU 1 0 0 0 0 1
    + (-1 : ℝ) * fU 1 0 1 0 0 0
    + (-1 / 2 : ℝ) * fU 1 0 1 0 1 1
    + (-1 : ℝ) * fU 1 0 1 0 2 2
    + (1 / 2 : ℝ) * fU 1 0 2 0 2 1
    + (1 / 2 : ℝ) * fU 1 1 0 1 0 1
    + (-1 : ℝ) * fU 1 1 1 1 0 0
    + (-1 / 2 : ℝ) * fU 1 1 1 1 1 1
    + (-1 : ℝ) * fU 1 1 1 1 2 2
    + (1 / 2 : ℝ) * fU 1 1 2 1 2 1
    + (1 / 2 : ℝ) * fU 1 2 0 2 0 1
    + (-1 : ℝ) * fU 1 2 1 2 0 0
    + (-1 / 2 : ℝ) * fU 1 2 1 2 1 1
    + (-1 : ℝ) * fU 1 2 1 2 2 2
    + (1 / 2 : ℝ) * fU 1 2 2 2 2 1
    + (1 / 2 : ℝ) * fU 2 0 0 0 0 2
    + (1 / 2 : ℝ) * fU 2 0 1 0 1 2
    + (-1 : ℝ) * fU 2 0 2 0 0 0
    + (-1 : ℝ) * fU 2 0 2 0 1 1
    + (-1 / 2 : ℝ) * fU 2 0 2 0 2 2
    + (1 / 2 : ℝ) * fU 2 1 0 1 0 2
    + (1 / 2 : ℝ) * fU 2 1 1 1 1 2
    + (-1 : ℝ) * fU 2 1 2 1 0 0
    + (-1 : ℝ) * fU 2 1 2 1 1 1
    + (-1 / 2 : ℝ) * fU 2 1 2 1 2 2
    + (1 / 2 : ℝ) * fU 2 2 0 2 0 2
    + (1 / 2 : ℝ) * fU 2 2 1 2 1 2
    + (-1 : ℝ) * fU 2 2 2 2 0 0
    + (-1 : ℝ) * fU 2 2 2 2 1 1
    + (-1 / 2 : ℝ) * fU 2 2 2 2 2 2
    + (-1 : ℝ) * fA 0 0 0 0 0 0
    + (-1 : ℝ) * fA 0 0 0 0 1 1
    + (-1 : ℝ) * fA 0 0 0 0 2 2
    + (-1 : ℝ) * fA 0 0 0 1 0 1
    + (1 : ℝ) * fA 0 0 0 1 1 0
    + (-1 : ℝ) * fA 0 0 0 2 0 2
    + (1 : ℝ) * fA 0 0 0 2 2 0
    + (1 : ℝ) * fA 0 0 1 2 1 2
    + (-1 : ℝ) * fA 0 0 1 2 2 1
    + (-1 / 2 : ℝ) * fA 0 1 0 2 1 2
    + (1 / 2 : ℝ) * fA 0 1 0 2 2 1
    + (-1 : ℝ) * fA 0 1 1 0 0 0
    + (-1 : ℝ) * fA 0 1 1 0 1 1
    + (-1 : ℝ) * fA 0 1 1 0 2 2
    + (-1 : ℝ) * fA 0 1 1 1 0 1
    + (1 : ℝ) * fA 0 1 1 1 1 0
    + (-3 / 2 : ℝ) * fA 0 1 1 2 0 2
    + (3 / 2 : ℝ) * fA 0 1 1 2 2 0
    + (1 / 2 : ℝ) * fA 0 1 2 0 1 2
    + (-1 / 2 : ℝ) * fA 0 1 2 0 2 1
    + (-1 / 2 : ℝ) * fA 0 1 2 1 0 2
    + (1 / 2 : ℝ) * fA 0 1 2 1 2 0
    + (1 / 2 : ℝ) * fA 0 2 0 1 1 2
    + (-1 / 2 : ℝ) * fA 0 2 0 1 2 1
    + (-1 / 2 : ℝ) * fA 0 2 1 0 1 2
    + (1 / 2 : ℝ) * fA 0 2 1 0 2 1
    + (1 / 2 : ℝ) * fA 0 2 1 2 0 1
    + (-1 / 2 : ℝ) * fA 0 2 1 2 1 0
    + (-1 : ℝ) * fA 0 2 2 0 0 0
    + (-1 : ℝ) * fA 0 2 2 0 1 1
    + (-1 : ℝ) * fA 0 2 2 0 2 2
    + (-1 / 2 : ℝ) * fA 0 2 2 1 0 1
    + (1 / 2 : ℝ) * fA 0 2 2 1 1 0
    + (-1 : ℝ) * fA 0 2 2 2 0 2
    + (1 : ℝ) * fA 0 2 2 2 2 0
    + (1 : ℝ) * fA 1 0 0 0 0 1
    + (-1 : ℝ) * fA 1 0 0 0 1 0
    + (-1 : ℝ) * fA 1 0 0 1 0 0
    + (-1 : ℝ) * fA 1 0 0 1 1 1
    + (-1 : ℝ) * fA 1 0 0 1 2 2
    + (-3 / 2 : ℝ) * fA 1 0 0 2 1 2
    + (3 / 2 : ℝ) * fA 1 0 0 2 2 1
    + (-1 / 2 : ℝ) * fA 1 0 1 2 0 2
    + (1 / 2 : ℝ) * fA 1 0 1 2 2 0
    + (-1 / 2 : ℝ) * fA 1 0 2 0 1 2
    + (1 / 2 : ℝ) * fA 1 0 2 0 2 1
    + (1 / 2 : ℝ) * fA 1 0 2 1 0 2
    + (-1 / 2 : ℝ) * fA 1 0 2 1 2 0
    + (1 : ℝ) * fA 1 1 0 2 0 2
    + (-1 : ℝ) * fA 1 1 0 2 2 0
    + (1 : ℝ) * fA 1 1 1 0 0 1
    + (-1 : ℝ) * fA 1 1 1 0 1 0
    + (-1 : ℝ) * fA 1 1 1 1 0 0
    + (-1 : ℝ) * fA 1 1 1 1 1 1
    + (-1 : ℝ) * fA 1 1 1 1 2 2
    + (-1 : ℝ) * fA 1 1 1 2 1 2
    + (1 : ℝ) * fA 1 1 1 2 2 1
    + (-1 / 2 : ℝ) * fA 1 2 0 1 0 2
    + (1 / 2 : ℝ) * fA 1 2 0 1 2 0
    + (-1 / 2 : ℝ) * fA 1 2 0 2 0 1
    + (1 / 2 : ℝ) * fA 1 2 0 2 1 0
    + (1 / 2 : ℝ) * fA 1 2 1 0 0 2
    + (-1 / 2 : ℝ) * fA 1 2 1 0 2 0
    + (1 / 2 : ℝ) * fA 1 2 2 0 0 1
    + (-1 / 2 : ℝ) * fA 1 2 2 0 1 0
    + (-1 : ℝ) * fA 1 2 2 1 0 0
    + (-1 : ℝ) * fA 1 2 2 1 1 1
    + (-1 : ℝ) * fA 1 2 2 1 2 2
    + (-1 : ℝ) * fA 1 2 2 2 1 2
    + (1 : ℝ) * fA 1 2 2 2 2 1
    + (1 : ℝ) * fA 2 0 0 0 0 2
    + (-1 : ℝ) * fA 2 0 0 0 2 0
    + (3 / 2 : ℝ) * fA 2 0 0 1 1 2
    + (-3 / 2 : ℝ) * fA 2 0 0 1 2 1
    + (-1 : ℝ) * fA 2 0 0 2 0 0
    + (-1 : ℝ) * fA 2 0 0 2 1 1
    + (-1 : ℝ) * fA 2 0 0 2 2 2
    + (1 / 2 : ℝ) * fA 2 0 1 0 1 2
    + (-1 / 2 : ℝ) * fA 2 0 1 0 2 1
    + (1 / 2 : ℝ) * fA 2 0 1 2 0 1
    + (-1 / 2 : ℝ) * fA 2 0 1 2 1 0
    + (-1 / 2 : ℝ) * fA 2 0 2 1 0 1
    + (1 / 2 : ℝ) * fA 2 0 2 1 1 0
    + (-1 / 2 : ℝ) * fA 2 1 0 1 0 2
    + (1 / 2 : ℝ) * fA 2 1 0 1 2 0
    + (-1 / 2 : ℝ) * fA 2 1 0 2 0 1
    + (1 / 2 : ℝ) * fA 2 1 0 2 1 0
    + (1 / 2 : ℝ) * fA 2 1 1 0 0 2
    + (-1 / 2 : ℝ) * fA 2 1 1 0 2 0
    + (1 : ℝ) * fA 2 1 1 1 1 2
    + (-1 : ℝ) * fA 2 1 1 1 2 1
    + (-1 : ℝ) * fA 2 1 1 2 0 0
    + (-1 : ℝ) * fA 2 1 1 2 1 1
    + (-1 : ℝ) * fA 2 1 1 2 2 2
    + (1 / 2 : ℝ) * fA 2 1 2 0 0 1
    + (-1 / 2 : ℝ) * fA 2 1 2 0 1 0
    + (1 : ℝ) * fA 2 2 0 1 0 1
    + (-1 : ℝ) * fA 2 2 0 1 1 0
    + (1 : ℝ) * fA 2 2 2 0 0 2
    + (-1 : ℝ) * fA 2 2 2 0 2 0
    + (1 : ℝ) * fA 2 2 2 1 1 2
    + (-1 : ℝ) * fA 2 2 2 1 2 1
    + (-1 : ℝ) * fA 2 2 2 2 0 0
    + (-1 : ℝ) * fA 2 2 2 2 1 1
    + (-1 : ℝ) * fA 2 2 2 2 2 2

theorem poly_identity (u : Fin 3 → ℝ) (a : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (g : Fin 3 → Fin 3 → ℝ) (h : Fin 3 → Fin 3 → Fin 3 → ℝ) (ha : a 0 0 + a 1 1 + a 2 2 = 0)
    (hg : g 0 0 + g 1 1 + g 2 2 = 0) (hk : ∀ q j l, k q j l = k q l j) (hh : ∀ i j l, h i j l = h i l j) :
    leftPoly u a w g h = rightPoly a k w g + partsSum (gradTerm a k w g h) (valueTerm u a g h) := by
  have hk10 : ∀ q, k q 1 0 = k q 0 1 := fun q => hk q 1 0
  have hk20 : ∀ q, k q 2 0 = k q 0 2 := fun q => hk q 2 0
  have hk21 : ∀ q, k q 2 1 = k q 1 2 := fun q => hk q 2 1
  have hh10 : ∀ i, h i 1 0 = h i 0 1 := fun i => hh i 1 0
  have hh20 : ∀ i, h i 2 0 = h i 0 2 := fun i => hh i 2 0
  have hh21 : ∀ i, h i 2 1 = h i 1 2 := fun i => hh i 2 1
  have ha' : a 2 2 = -a 0 0 - a 1 1 := by linarith
  have hg' : g 2 2 = -g 0 0 - g 1 1 := by linarith
  simp only [leftPoly, rightPoly, curlPoly, curlGradPoly, partsSum, gradTerm, valueTerm, Fin.sum_univ_three]
  simp only [permSign, Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Prod.mk.injEq]
  norm_num
  simp only [hk10, hk20, hk21, hh10, hh20, hh21, ha', hg']
  ring


theorem iz_add {f g : Space → ℝ} (hf : Integrable f ∧ ∫ y, f y = 0) (hg : Integrable g ∧ ∫ y, g y = 0) :
    Integrable (fun y => f y + g y) ∧ ∫ y, f y + g y = 0 :=
  ⟨hf.1.add hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2, add_zero]⟩

theorem iz_mul (r : ℝ) {f : Space → ℝ} (hf : Integrable f ∧ ∫ y, f y = 0) :
    Integrable (fun y => r * f y) ∧ ∫ y, r * f y = 0 :=
  ⟨hf.1.const_mul r, by rw [integral_const_mul, hf.2, mul_zero]⟩

theorem parts_zero (fA fU : Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Fin 3 → Space → ℝ)
    (hA : ∀ q l a b j d, Integrable (fA q l a b j d) ∧ ∫ y, fA q l a b j d y = 0)
    (hU : ∀ q a b d e j, Integrable (fU q a b d e j) ∧ ∫ y, fU q a b d e j y = 0) :
    Integrable (fun y => partsSum (fun q l a b j d => fA q l a b j d y) (fun q a b d e j => fU q a b d e j y)) ∧
      ∫ y, partsSum (fun q l a b j d => fA q l a b j d y) (fun q a b d e j => fU q a b d e j y) = 0 := by
  simp only [partsSum]
  repeat' first | refine iz_add ?_ ?_ | refine iz_mul _ ?_ | exact hA _ _ _ _ _ _ | exact hU _ _ _ _ _ _

theorem left_eq (U x : Space) (A M : Space →L[ℝ] Space) (Hm : Space →L[ℝ] Space →L[ℝ] Space) :
    inner ℝ ((2 : ℝ) • ((1 / 2 : ℝ) • (M U + A x))) (-secondTrace Hm)
      = leftPoly (fun q => U q) (fun q l => A (unitVector l) q) (fun i => x i) (fun b d => M (unitVector d) b)
          (fun b j d => Hm (unitVector j) (unitVector d) b) := by
  rw [ModelFormInternal.inner_coord]
  simp only [secondTrace, Fin.sum_univ_three, PiLp.smul_apply, PiLp.add_apply, PiLp.neg_apply, smul_eq_mul,
    ModelFormInternal.coord_apply M U, ModelFormInternal.coord_apply A x]
  simp only [entry, leftPoly, Fin.sum_univ_three]
  ring

theorem inner_symPart (M : Space →L[ℝ] Space) (w : Space) : inner ℝ w (symPart M w) = inner ℝ w (M w) := by
  simp only [symPart, FunLike.coe_smul, FunLike.coe_add, Pi.smul_apply, Pi.add_apply, inner_smul_right,
    inner_add_right, ContinuousLinearMap.adjoint_inner_right]
  rw [real_inner_comm (M w) w]
  ring

theorem curl_apply (M : Space →L[ℝ] Space) (i : Fin 3) :
    curlOf M i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * entry M l j := by
  fin_cases i <;> simp [curlOf, unitVector, Fin.sum_univ_three]

theorem curlGrad_entry (K : Space →L[ℝ] Space →L[ℝ] Space) (r m : Fin 3) :
    entry (curlGradMatrix K) r m = ∑ b : Fin 3, ∑ q : Fin 3, permSign r b q * K (unitVector m) (unitVector b) q := by
  fin_cases r <;> fin_cases m <;>
    simp [entry, curlGradMatrix, Fin.sum_univ_three, unitVector, EuclideanSpace.inner_single_left]

theorem right_eq (A : Space →L[ℝ] Space) (K : Space →L[ℝ] Space →L[ℝ] Space) (M : Space →L[ℝ] Space) (x : Space) :
    jForm (symPart A) (curlGradMatrix K) M x
      = rightPoly (fun q l => A (unitVector l) q) (fun q j l => K (unitVector j) (unitVector l) q) (fun i => x i)
          (fun b d => M (unitVector d) b) := by
  rw [jForm, inner_symPart, ModelFormInternal.inner_coord]
  simp only [ModelFormInternal.coord_apply A (curlOf M), ModelFormInternal.coord_apply (curlGradMatrix K) x]
  simp only [curl_apply, curlGrad_entry]
  simp only [entry, rightPoly, curlPoly, curlGradPoly, Fin.sum_univ_three]
  simp (config := {decide := true}) only [permSign, Fin.isValue, ↓reduceIte, one_mul, zero_mul, neg_mul, neg_zero,
    add_zero, zero_add]
  ring

end CentrePairingCentreInternal

open SteadyCert CentrePairingCentreInternal CentreIdentityParts in
theorem centreIdentity : CentreIdentityStatement := by
  intro α k N c hc v G H hs
  have hC := parts_zero (fun q l a b j d => gradPart c v G H q l a b j d)
    (fun q a b d e j => valuePart c G H q a b d e j) (gradPart_integral hc hs) (valuePart_integral hc hs)
  have hae : (fun y => inner ℝ ((2 : ℝ) • symProduct c.centre c.centreGrad v G y) (negSecondTrace H y))
      =ᵐ[volume] fun y => jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y)
        + partsSum (fun q l a b j d => gradPart c v G H q l a b j d y)
          (fun q a b d e j => valuePart c G H q a b d e j y) := by
    filter_upwards [ModelFormInternal.second_symm hc, second_symm_field hs, hs.divergence] with y hKy hHy hGy
    have e1 := left_eq (c.centre y) (v y) (c.centreGrad y) (G y) (H y)
    have e2 := right_eq (c.centreGrad y) (c.centreSecond y) (G y) (v y)
    have htA : c.centreGrad y (unitVector 0) 0 + c.centreGrad y (unitVector 1) 1
        + c.centreGrad y (unitVector 2) 2 = 0 := by
      have h := hc.centre_divergence y
      simp only [divergenceAt, Fin.sum_univ_three] at h
      exact h
    have htG : G y (unitVector 0) 0 + G y (unitVector 1) 1 + G y (unitVector 2) 2 = 0 := by
      simp only [Fin.sum_univ_three, unitVector, EuclideanSpace.inner_single_right] at hGy
      simp only [unitVector]
      simpa using hGy
    have hp := poly_identity (fun q => c.centre y q) (fun q l => c.centreGrad y (unitVector l) q)
      (fun q j l => c.centreSecond y (unitVector j) (unitVector l) q) (fun i => v y i)
      (fun b d => G y (unitVector d) b) (fun b j d => H y (unitVector j) (unitVector d) b) htA htG
      (fun q j l => congrArg (fun z : Space => z q) (hKy j l)) (fun i j l => congrArg (fun z : Space => z i) (hHy j l))
    show inner ℝ ((2 : ℝ) • ((1 / 2 : ℝ) • (G y (c.centre y) + c.centreGrad y (v y)))) (-secondTrace (H y)) = _
    rw [e1]
    show _ = jForm (symPart (c.centreGrad y)) (curlGradMatrix (c.centreSecond y)) (G y) (v y) + _
    rw [e2]
    exact hp
  unfold l2Pair
  rw [integral_congr_ae hae, integral_add (ModelFormInternal.centre_integrable hc hs) hC.1, hC.2, add_zero]

end CellCert

end Breakdown

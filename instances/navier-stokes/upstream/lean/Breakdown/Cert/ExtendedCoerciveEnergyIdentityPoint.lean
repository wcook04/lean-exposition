import Breakdown.Cert.CoerciveEnergyIdentityStretch

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal

set_option maxHeartbeats 2000000 in
theorem curl_grad_weak (u W₀ : Space → Space) (H : Space →L[ℝ] Space →L[ℝ] Space) (hu : ContDiff ℝ 2 u)
    (hd : ∀ y, divergenceAt u y = 0) (y : Space) (hWd : divergenceAt W₀ y = 0)
    (hH : ∀ a b, H a b = H b a) :
    -∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l *
        (∑ k : Fin 3, (W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i
          + fderiv ℝ W₀ y (unitVector j) k * fderiv ℝ u y (unitVector k) i
          + u y k * H (unitVector j) (unitVector k) i
          + fderiv ℝ u y (unitVector j) k * fderiv ℝ W₀ y (unitVector k) i)) *
          curlVec (fderiv ℝ u y) l =
      ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad H j m) * curlVec (fderiv ℝ u y) j)
      + -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
          curlVec (fderiv ℝ u y) i) := by
  simp only [curl_deriv u hu]
  simp only [curlVec_apply, vortGrad]
  have tu := hd y
  have tW := hWd
  simp only [divergenceAt, Fin.sum_univ_three] at tu tW
  have eu : fderiv ℝ u y (unitVector 2) 2 = -fderiv ℝ u y (unitVector 0) 0 - fderiv ℝ u y (unitVector 1) 1 := by
    linarith
  have eW : fderiv ℝ W₀ y (unitVector 2) 2 = -fderiv ℝ W₀ y (unitVector 0) 0 - fderiv ℝ W₀ y (unitVector 1) 1 := by
    linarith
  have s10 := d2_symm_two u hu y (unitVector 1) (unitVector 0)
  have s20 := d2_symm_two u hu y (unitVector 2) (unitVector 0)
  have s21 := d2_symm_two u hu y (unitVector 2) (unitVector 1)
  have r10 := hH (unitVector 1) (unitVector 0)
  have r20 := hH (unitVector 2) (unitVector 0)
  have r21 := hH (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [eps_000, eps_001, eps_002, eps_010, eps_011, eps_012, eps_020, eps_021, eps_022, eps_100, eps_101, eps_102, eps_110, eps_111, eps_112, eps_120, eps_121, eps_122, eps_200, eps_201, eps_202, eps_210, eps_211, eps_212, eps_220, eps_221, eps_222]
  simp only [s10, s20, s21, r10, r20, r21]
  rw [eu, eW]
  ring

set_option maxHeartbeats 4000000 in
theorem x_expand_weak (u W₀ : Space → Space) (H : Space →L[ℝ] Space →L[ℝ] Space) (hu : ContDiff ℝ ∞ u)
    (y : Space) :
    -(∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad H t.2.1 t.2.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1
          + curlVec (fderiv ℝ W₀ y) t.2.1 *
            fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.1) t.1) y (unitVector t.2.2.1))) * u y t.2.2.2) =
      2 * ((1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad H j m * fderiv ℝ u y (unitVector j) i * u y l) +
      ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) := by
  simp only [d2_eq u hu, Fintype.sum_prod_type]
  have s10 := d2_symm u hu y (unitVector 1) (unitVector 0)
  have s20 := d2_symm u hu y (unitVector 2) (unitVector 0)
  have s21 := d2_symm u hu y (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [s10, s20, s21]
  ring

set_option maxHeartbeats 2000000 in
theorem y_point_weak (u W₀ : Space → Space) (H : Space →L[ℝ] Space →L[ℝ] Space) (y : Space)
    (hH : ∀ a b, H a b = H b a) :
    ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad H t.2.1 t.2.1 * u y t.2.2.2
          + curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.2.2.2)) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 =
      -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) := by
  simp only [Fintype.sum_prod_type, curlVec_apply, vortGrad]
  have r10 := hH (unitVector 1) (unitVector 0)
  have r20 := hH (unitVector 2) (unitVector 0)
  have r21 := hH (unitVector 2) (unitVector 1)
  simp only [Fin.sum_univ_three]
  simp only [eps_000, eps_001, eps_002, eps_010, eps_011, eps_012, eps_020, eps_021, eps_022, eps_100, eps_101, eps_102, eps_110, eps_111, eps_112, eps_120, eps_121, eps_122, eps_200, eps_201, eps_202, eps_210, eps_211, eps_212, eps_220, eps_221, eps_222]
  simp only [r10, r20, r21]
  ring

end EnergyIdentityWeakInternal

end CoerciveWeak

end Breakdown

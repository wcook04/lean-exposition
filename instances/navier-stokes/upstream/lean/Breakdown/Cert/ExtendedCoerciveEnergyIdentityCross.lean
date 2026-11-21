import Breakdown.Cert.ExtendedCoerciveEnergyIdentitySlice

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal Coercive.SmoothEnergyIdentityInternal

namespace CrossInternal

open Coercive.SmoothEnergyIdentityInternal.Stretch

variable {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}

theorem atom_sq_weak (h : WeakSliceData u W₀ H D) : Integrable (fun y => atom u y ^ 2) := by
  have cu := h.hu.continuous
  have c1 : Continuous (fun y => fderiv ℝ u y) := h.hu.continuous_fderiv (by simp)
  have c2 : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (h.hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have ca : Continuous (atom u) := by
    unfold atom
    exact ((cu.norm.div (continuous_const.add continuous_norm)
      (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')).add
      c1.norm).add c2.norm
  refine Integrable.mono' (((h.i0.add h.i1).add h.i2).const_mul 3) (ca.pow 2).aestronglyMeasurable
    (Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show atom u y ^ 2 ≤ 3 * (‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2 + ‖fderiv ℝ u y‖ ^ 2
    + ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ ^ 2)
  unfold atom
  rw [← div_pow]
  nlinarith [sq_nonneg (‖u y‖ / (1 + ‖y‖) - ‖fderiv ℝ u y‖),
    sq_nonneg (‖u y‖ / (1 + ‖y‖) - ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖),
    sq_nonneg (‖fderiv ℝ u y‖ - ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖)]

theorem int_atom (hN : Integrable (fun y => atom u y ^ 2)) (f : Space → ℝ) (hf : AEStronglyMeasurable f)
    (K : ℝ) (hK : 0 ≤ K) (hb : ∀ y, |f y| ≤ K * (atom u y * atom u y)) : Integrable f := by
  refine int_dom f (fun y => K * atom u y) (atom u) hf (sq_const_mul hN K) hN
    (fun y => ?_) (fun y => mul_nonneg hK (atom_nonneg u y)) (atom_nonneg u)
  show |f y| ≤ K * atom u y * atom u y
  rw [mul_assoc]
  exact hb y

theorem dec_le (D0 : 0 ≤ D) (y : Space) (c x K : ℝ) (hK : 0 ≤ K) (hc : |c| ≤ K * (D / (1 + ‖y‖)))
    (hx : |x| ≤ ‖u y‖) : |c * x| ≤ K * D * atom u y := by
  rw [abs_mul]
  have hD : 0 ≤ D / (1 + ‖y‖) := div_nonneg D0 (by positivity)
  calc |c| * |x| ≤ K * (D / (1 + ‖y‖)) * ‖u y‖ :=
        mul_le_mul hc hx (abs_nonneg x) (mul_nonneg hK hD)
    _ = K * D * (‖u y‖ / (1 + ‖y‖)) := by ring
    _ ≤ K * D * atom u y := mul_le_mul_of_nonneg_left (le0 u y) (mul_nonneg hK D0)

theorem omega_le (h : WeakSliceData u W₀ H D) (y : Space) (j : Fin 3) :
    |curlVec (fderiv ℝ W₀ y) j| ≤ 9 * (D / (1 + ‖y‖)) :=
  (curl_abs_le _ j).trans (by linarith [h.W1 y])

theorem omega_le' (h : WeakSliceData u W₀ H D) (y : Space) (j : Fin 3) :
    |curlVec (fderiv ℝ W₀ y) j| ≤ 9 * D :=
  (omega_le h y j).trans (by linarith [div_le_self h.D0 (one_le_add_norm y)])

theorem vg_le (h : WeakSliceData u W₀ H D) (y : Space) (j m : Fin 3) :
    |vortGrad (H y) j m| ≤ 9 * (D / (1 + ‖y‖)) :=
  (vortGrad_abs_le _ j m).trans (by linarith [h.W2 y])

theorem vortGrad_continuous (j m : Fin 3) :
    Continuous (fun L : Space →L[ℝ] Space →L[ℝ] Space => vortGrad L j m) := by
  unfold vortGrad
  fun_prop

theorem vg_meas (h : WeakSliceData u W₀ H D) (j m : Fin 3) :
    AEStronglyMeasurable (fun y => vortGrad (H y) j m) :=
  (vortGrad_continuous j m).comp_aestronglyMeasurable h.hHm

theorem omega_cont (h : WeakSliceData u W₀ H D) (j : Fin 3) :
    Continuous (fun x => curlVec (fderiv ℝ W₀ x) j) :=
  (curl_contDiff W₀ h.hW (n := 0) (by simp) j).continuous

theorem omega_weak (h : WeakSliceData u W₀ H D) (j m : Fin 3) :
    WeakPartial (fun y => curlVec (fderiv ℝ W₀ y) j) (fun y => vortGrad (H y) j m) m := by
  have e1 : (fun y => curlVec (fderiv ℝ W₀ y) j) =
      fun y => ∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ,
        alternatingSymbol j a b * fderiv ℝ W₀ y (unitVector a) b := by
    funext y
    rw [curlVec_apply]
  have e2 : (fun y => vortGrad (H y) j m) =
      fun y => ∑ a ∈ Finset.univ, ∑ b ∈ Finset.univ,
        alternatingSymbol j a b * H y (unitVector m) (unitVector a) b := by
    funext y
    rfl
  rw [e1, e2]
  exact WeakPartial.sum Finset.univ (f := fun a y => ∑ b ∈ Finset.univ,
      alternatingSymbol j a b * fderiv ℝ W₀ y (unitVector a) b)
    (F := fun a y => ∑ b ∈ Finset.univ, alternatingSymbol j a b * H y (unitVector m) (unitVector a) b)
    (fun a _ => WeakPartial.sum Finset.univ
      (f := fun b y => alternatingSymbol j a b * fderiv ℝ W₀ y (unitVector a) b)
      (F := fun b y => alternatingSymbol j a b * H y (unitVector m) (unitVector a) b)
      (fun b _ => (weakPartial_secondDeriv a (h.hweak a) b m).const_mul _))

theorem int_weight (hN : Integrable (fun y => atom u y ^ 2)) (f g : Space → ℝ) (hf : Continuous f)
    (hg : Continuous g) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ y, |f y| * |g y| ≤ K * (atom u y * atom u y)) :
    Integrable (fun y => |f y| * |g y| / (1 + ‖y‖)) := by
  refine int_atom hN _ ?_ K hK (fun y => ?_)
  · exact ((hf.abs.mul hg.abs).div (continuous_const.add continuous_norm)
      (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')).aestronglyMeasurable
  · have h1 : 0 ≤ |f y| * |g y| := by positivity
    have h2 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    rw [abs_of_nonneg (by positivity)]
    exact (div_le_self h1 h2).trans (hb y)

end CrossInternal

open CrossInternal Coercive.SmoothEnergyIdentityInternal.Stretch in
theorem x_term_weak {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) :
    ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l := by
  have hu := h.hu
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hN0 := atom_nonneg u
  have hN := atom_sq_weak h
  have D0 := h.D0
  have cO := omega_cont h
  have cDu : ∀ j i, Continuous (fun x => fderiv ℝ u x (unitVector j) i) := fun j i =>
    (d1_smooth u hu j i).continuous
  have cU : ∀ l, Continuous (fun x => u x l) := fun l => (comp_smooth u hu l).continuous
  have cdU : ∀ l m, Continuous (fun y => fderiv ℝ (fun x => u x l) y (unitVector m)) := fun l m =>
    ((comp_smooth u hu l).continuous_fderiv (by simp)).clm_apply continuous_const
  have cddU : ∀ j i m, Continuous
      (fun y => fderiv ℝ (fun x => fderiv ℝ u x (unitVector j) i) y (unitVector m)) := fun j i m =>
    ((d1_smooth u hu j i).continuous_fderiv (by simp)).clm_apply continuous_const
  have hK : (0 : ℝ) ≤ 18 * D := by linarith
  have hdecO : ∀ y (j l : Fin 3), |curlVec (fderiv ℝ W₀ y) j * u y l| ≤ 9 * D * atom u y :=
    fun y j l => dec_le D0 y _ _ 9 (by norm_num) (omega_le h y j) (coord_abs_le _ l)
  have hdecV : ∀ y (j m l : Fin 3), |vortGrad (H y) j m * u y l| ≤ 9 * D * atom u y :=
    fun y j m l => dec_le D0 y _ _ 9 (by norm_num) (vg_le h y j m) (coord_abs_le _ l)
  have iI : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l) := by
    refine Integrable.const_mul (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => ?_))))) _
    refine int_atom hN _ (((aestronglyMeasurable_const.mul (vg_meas h j m)).mul
      (cDu j i).aestronglyMeasurable).mul (cU l).aestronglyMeasurable) (9 * D) (by linarith) (fun y => ?_)
    have hd := hdecV y j m l
    rw [abs_mul] at hd
    have he := eps_abs_le i m l
    have hdu' := du_le u y j i
    have hn := hN0 y
    calc |alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l|
          = (|alternatingSymbol i m l| * |fderiv ℝ u y (unitVector j) i|)
            * (|vortGrad (H y) j m| * |u y l|) := by
          rw [abs_mul, abs_mul, abs_mul]; ring
      _ ≤ (1 * atom u y) * (9 * D * atom u y) :=
          mul_le_mul (mul_le_mul he hdu' (abs_nonneg _) zero_le_one) hd (by positivity) (by positivity)
      _ = 9 * D * (atom u y * atom u y) := by ring
  have iY : Integrable (fun y => ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3,
      (alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
        fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1)) := by
    refine integrable_finsetSum _ (fun t _ => ?_)
    refine int_atom hN _ ((continuous_const.mul ((cO _).mul (cU _))).mul (cddU _ _ _)).aestronglyMeasurable
      (9 * D) (by linarith) (fun y => ?_)
    rw [d2_eq u hu]
    exact (prod_le (prod_le (eps_abs_le _ _ _) (hdecO y _ _)) (ddu_le u y _ _ _)).trans (le_of_eq (by ring))
  have e1 : ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) := by
    congr 1; funext y; exact x_split u W₀ hdu y
  have wp2 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, WeakPartial
      (fun y => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1))
      (fun y => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1
          + curlVec (fderiv ℝ W₀ y) t.2.1 *
            fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.1) t.1) y (unitVector t.2.2.1))) t.2.2.1 :=
    fun t => ((omega_weak h t.2.1 t.2.2.1).mul_smooth (cO _) (d1_smooth u hu _ _)).const_mul _
  have e2 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1
          + curlVec (fderiv ℝ W₀ y) t.2.1 *
            fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.1) t.1) y (unitVector t.2.2.1))) * u y t.2.2.2 := by
    have i1 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
          (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
            fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1)) := by
      intro t
      refine int_atom hN _ ((continuous_const.mul ((cO _).mul (cDu _ _))).mul (cdU _ _)).aestronglyMeasurable
        (9 * D) (by linarith) (fun y => ?_)
      rw [fderiv_component u (hdu y)]
      exact (prod_le (prod_le (neps_abs_le _ _ _) (prod_le (omega_le' h y _) (du_le u y _ _)))
        (du_le u y _ _)).trans (le_of_eq (by ring))
    have i2 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
          (vortGrad (H y) t.2.1 t.2.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1
            + curlVec (fderiv ℝ W₀ y) t.2.1 *
              fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.1) t.1) y (unitVector t.2.2.1))) * u y t.2.2.2) := by
      intro t
      refine int_atom hN _ ((aestronglyMeasurable_const.mul (((vg_meas h _ _).mul
        (cDu _ _).aestronglyMeasurable).add ((cO _).mul (cddU _ _ _)).aestronglyMeasurable)).mul
          (cU _).aestronglyMeasurable) (18 * D) hK (fun y => ?_)
      rw [d2_eq u hu]
      have h1 := hdecV y t.2.1 t.2.2.1 t.2.2.2
      have h2 := hdecO y t.2.1 t.2.2.2
      rw [abs_mul] at h1 h2
      exact (two_term_le (neps_abs_le _ _ _) h1 h2 (du_le u y _ _) (ddu_le u y _ _ _)).trans
        (le_of_eq (by ring))
    have i3 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        |-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
          (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)| * |u y t.2.2.2|
          / (1 + ‖y‖)) := by
      intro t
      refine int_weight hN _ _ (continuous_const.mul ((cO _).mul (cDu _ _))) (cU _) (18 * D) hK (fun y => ?_)
      have h2 := hdecO y t.2.1 t.2.2.2
      rw [abs_mul] at h2
      have he := neps_abs_le t.1 t.2.2.1 t.2.2.2
      have hx := du_le u y t.2.1 t.1
      have hn := hN0 y
      calc |-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
            (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)| * |u y t.2.2.2|
          = (|-alternatingSymbol t.1 t.2.2.1 t.2.2.2| * |fderiv ℝ u y (unitVector t.2.1) t.1|)
            * (|curlVec (fderiv ℝ W₀ y) t.2.1| * |u y t.2.2.2|) := by
            rw [abs_mul, abs_mul]; ring
        _ ≤ (1 * atom u y) * (9 * D * atom u y) :=
            mul_le_mul (mul_le_mul he hx (abs_nonneg _) zero_le_one) h2 (by positivity) (by positivity)
        _ ≤ 18 * D * (atom u y * atom u y) := by nlinarith [mul_self_nonneg (atom u y)]
    rw [integral_finsetSum _ (fun t _ => i1 t), integral_finsetSum _ (fun t _ => i2 t),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => weak_ibp (wp2 t) (comp_smooth u hu _) (i1 t) (i2 t) (i3 t))
  have e3 : -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1
          + curlVec (fderiv ℝ W₀ y) t.2.1 *
            fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.1) t.1) y (unitVector t.2.2.1))) * u y t.2.2.2 =
      2 * (∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l) +
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3,
        (alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) := by
    rw [← integral_neg, ← integral_const_mul, ← integral_add (iI.const_mul 2) iY]
    congr 1; funext y; exact x_expand_weak u W₀ (H y) hu y
  have wp4 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, WeakPartial
      (fun y => alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2))
      (fun y => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.1 * u y t.2.2.2
          + curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.1))) t.2.1 :=
    fun t => ((omega_weak h t.2.1 t.2.1).mul_smooth (cO _) (comp_smooth u hu _)).const_mul _
  have e4 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3,
        (alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.1 * u y t.2.2.2
          + curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.1))) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 := by
    have i1 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        (alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1)) := by
      intro t
      refine int_atom hN _ ((continuous_const.mul ((cO _).mul (cU _))).mul (cddU _ _ _)).aestronglyMeasurable
        (9 * D) (by linarith) (fun y => ?_)
      rw [d2_eq u hu]
      exact (prod_le (prod_le (eps_abs_le _ _ _) (hdecO y _ _)) (ddu_le u y _ _ _)).trans
        (le_of_eq (by ring))
    have i2 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
          (vortGrad (H y) t.2.1 t.2.1 * u y t.2.2.2
            + curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.1))) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1) := by
      intro t
      refine int_atom hN _ ((aestronglyMeasurable_const.mul (((vg_meas h _ _).mul
        (cU _).aestronglyMeasurable).add ((cO _).mul (cdU _ _)).aestronglyMeasurable)).mul
          (cDu _ _).aestronglyMeasurable) (18 * D) hK (fun y => ?_)
      rw [fderiv_component u (hdu y)]
      exact (sum_term_le (eps_abs_le _ _ _) (hdecV y _ _ _)
        (prod_le (omega_le' h y _) (du_le u y _ _)) (du_le u y _ _)).trans (le_of_eq (by ring))
    have i3 : ∀ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, Integrable (fun y =>
        |alternatingSymbol t.1 t.2.2.1 t.2.2.2 * (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)| *
          |fderiv ℝ u y (unitVector t.2.2.1) t.1| / (1 + ‖y‖)) := by
      intro t
      refine int_weight hN _ _ (continuous_const.mul ((cO _).mul (cU _))) (cDu _ _) (9 * D) (by linarith)
        (fun y => ?_)
      rw [← abs_mul]
      exact (prod_le (prod_le (eps_abs_le _ _ _) (hdecO y _ _)) (du_le u y _ _)).trans
        (le_of_eq (by ring))
    rw [integral_finsetSum _ (fun t _ => i1 t), integral_finsetSum _ (fun t _ => i2 t),
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun t _ => weak_ibp (wp4 t) (d1_smooth u hu _ _) (i1 t) (i2 t) (i3 t))
  have e5 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (vortGrad (H y) t.2.1 t.2.1 * u y t.2.2.2
          + curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.1))) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 =
      ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) := by
    refine integral_congr_ae ?_
    filter_upwards [h.hsym] with y hy
    simp only [fderiv_component u (hdu y)]
    exact y_point_weak u W₀ (H y) y hy
  linarith [e1, e2, e3, e4, e5]

end EnergyIdentityWeakInternal

end CoerciveWeak

end Breakdown

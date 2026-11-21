import Breakdown.Cert.ExtendedCoerciveEnergyIdentityCross

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace EnergyIdentityWeakInternal

open Coercive Coercive.EnergyIdentityInternal Coercive.SmoothEnergyIdentityInternal

namespace SliceStretchInternal

open Coercive.SmoothEnergyIdentityInternal.Stretch

theorem atom_sq_slice {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) : Integrable (fun y => atom u y ^ 2) := by
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

theorem grad_le_const {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (y : Space) : ‖fderiv ℝ W₀ y‖ ≤ D :=
  (h.W1 y).trans (div_le_self h.D0 (one_le_add_norm y))

theorem decay_mul_le {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (y : Space) (c x K : ℝ)
    (hK : 0 ≤ K) (hc : |c| ≤ K * (D / (1 + ‖y‖))) (hx : |x| ≤ ‖u y‖) :
    |c * x| ≤ K * D * atom u y := by
  rw [abs_mul]
  have hD : 0 ≤ D / (1 + ‖y‖) := div_nonneg h.D0 (by positivity)
  calc |c| * |x| ≤ K * (D / (1 + ‖y‖)) * ‖u y‖ :=
        mul_le_mul hc hx (abs_nonneg x) (mul_nonneg hK hD)
    _ = K * D * (‖u y‖ / (1 + ‖y‖)) := by ring
    _ ≤ K * D * atom u y := mul_le_mul_of_nonneg_left (le0 u y) (mul_nonneg hK h.D0)

end SliceStretchInternal

open SliceStretchInternal Coercive.SmoothEnergyIdentityInternal.Stretch in
theorem transport_weak {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) :
    ∫ y, ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) = 0 := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hN0 := atom_nonneg u
  have hN := atom_sq_slice h
  have D0 := h.D0
  have hdW : Differentiable ℝ W₀ := hW.differentiable (by norm_num)
  have cWk : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => W₀ x k) := fun k => by
    have e := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW
    exact e
  have ch : ∀ l : Fin 3, ContDiff ℝ 1 (fun x => curlVec (fderiv ℝ u x) l) := fun l =>
    curl_contDiff u h2 (by norm_num) l
  have iT : ∀ l : Fin 3, Integrable (fun y => ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) := by
    intro l
    refine integrable_finsetSum _ (fun k _ => ?_)
    refine int_N (atom u) _ hN0 hN (((cWk k).continuous.mul (ch l).continuous).mul
      (((ch l).continuous_fderiv (by norm_num)).clm_apply continuous_const)) (81 * D) (by linarith)
      (fun y => ?_)
    exact (prod_le (prod_le ((coord_abs_le _ k).trans (h.W0 y)) (curl_le u y l)) (dcurl_le u h2 y l k)).trans
      (le_of_eq (by ring))
  have per : ∀ l : Fin 3, ∫ y, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) = 0 := by
    intro l
    have e : ∫ y, ∑ k ∈ Finset.univ, (W₀ y k * curlVec (fderiv ℝ u y) l) *
        fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) =
        -∫ y, ∑ k ∈ Finset.univ, fderiv ℝ (fun x => W₀ x k * curlVec (fderiv ℝ u x) l) y (unitVector k) *
          curlVec (fderiv ℝ u y) l :=
      wibp_N Finset.univ (atom u) hN0 hN (fun (k : Fin 3) x => W₀ x k * curlVec (fderiv ℝ u x) l)
        (fun _ x => curlVec (fderiv ℝ u x) l) (fun k => k) (162 * D) (by linarith)
        (fun k _ => (cWk k).mul (ch l)) (fun _ _ => ch l)
        (fun k _ y => kmono ((prod_le (prod_le ((coord_abs_le _ k).trans (h.W0 y)) (curl_le u y l))
          (dcurl_le u h2 y l k)).trans (le_of_eq (by ring))) (by linarith : 81 * D ≤ 162 * D))
        (fun k _ y => by
          rw [mul_deriv _ _ y _ ((cWk k).differentiable (by norm_num) y) ((ch l).differentiable (by norm_num) y),
            fderiv_component W₀ (hdW y)]
          have hS := (abs_add_le _ _).trans (add_le_add
            (prod_le ((entry_abs_le (fderiv ℝ W₀ y) k k).trans (grad_le_const h y)) (curl_le u y l))
            (prod_le ((coord_abs_le (W₀ y) k).trans (h.W0 y)) (dcurl_le u h2 y l k)))
          exact (prod_le hS (curl_le u y l)).trans (le_of_eq (by ring)))
        (fun k _ y => by
          rw [← abs_mul]
          exact kmono ((prod_le (prod_le ((coord_abs_le _ k).trans (h.W0 y)) (curl_le u y l))
            (curl_le u y l)).trans (le_of_eq (by ring))) (by linarith : 81 * D ≤ 162 * D))
    have pt : ∀ y, ∑ k : Fin 3, fderiv ℝ (fun x => W₀ x k * curlVec (fderiv ℝ u x) l) y (unitVector k) *
          curlVec (fderiv ℝ u y) l =
        ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) := by
      intro y
      have md : ∀ k : Fin 3, fderiv ℝ (fun x => W₀ x k * curlVec (fderiv ℝ u x) l) y (unitVector k) =
          fderiv ℝ W₀ y (unitVector k) k * curlVec (fderiv ℝ u y) l
            + W₀ y k * fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) := fun k => by
        rw [mul_deriv _ _ y _ ((cWk k).differentiable (by norm_num) y) ((ch l).differentiable (by norm_num) y),
          fderiv_component W₀ (hdW y)]
      simp only [md, add_mul, Finset.sum_add_distrib]
      have hw := h.hWd y
      unfold divergenceAt at hw
      have hz : ∑ k : Fin 3, fderiv ℝ W₀ y (unitVector k) k * curlVec (fderiv ℝ u y) l *
          curlVec (fderiv ℝ u y) l = 0 := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, hw]
        simp
      rw [hz, zero_add]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    simp_rw [pt] at e
    linarith
  rw [integral_finsetSum _ (fun l _ => iT l)]
  exact Finset.sum_eq_zero (fun l _ => per l)

namespace SliceStretchInternal

open Coercive.SmoothEnergyIdentityInternal.Stretch

def jetA (u W₀ : Space → Space) (L : Space →L[ℝ] Space →L[ℝ] Space) (y : Space) (i j : Fin 3) : ℝ :=
  ∑ k : Fin 3, (W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i
    + fderiv ℝ W₀ y (unitVector j) k * fderiv ℝ u y (unitVector k) i
    + u y k * L (unitVector j) (unitVector k) i
    + fderiv ℝ u y (unitVector j) k * fderiv ℝ W₀ y (unitVector k) i)

theorem aesm_pair {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) {Φ : Space × (Space →L[ℝ] Space →L[ℝ] Space) → ℝ} (hΦ : Continuous Φ) :
    AEStronglyMeasurable (fun y => Φ (y, H y)) :=
  hΦ.comp_aestronglyMeasurable (aestronglyMeasurable_id.prodMk h.hHm)

theorem weakPartial_congr {f g F G : Space → ℝ} {j : Fin 3} (hf : WeakPartial f F j)
    (e1 : ∀ y, f y = g y) (e2 : ∀ y, F y = G y) : WeakPartial g G j := by
  obtain rfl : f = g := funext e1
  obtain rfl : F = G := funext e2
  exact hf

theorem weakPartial_adv {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (i j : Fin 3) :
    WeakPartial (fun y => (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i)
      (fun y => jetA u W₀ (H y) y i j) j := by
  have hu := h.hu
  have hW := h.hW
  have hdW : Differentiable ℝ W₀ := hW.differentiable (by norm_num)
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have cWk : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => W₀ x k) := fun k => by
    have e := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hW
    exact e
  have cdW : ∀ k : Fin 3, Continuous (fun y => fderiv ℝ W₀ y (unitVector k) i) := fun k =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp
      ((hW.continuous_fderiv (by norm_num)).clm_apply continuous_const)
  have P : ∀ k : Fin 3, WeakPartial
      (fun y => W₀ y k * fderiv ℝ u y (unitVector k) i + fderiv ℝ W₀ y (unitVector k) i * u y k)
      (fun y => (fderiv ℝ (fun x => W₀ x k) y (unitVector j) * fderiv ℝ u y (unitVector k) i
          + W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x (unitVector k) i) y (unitVector j))
        + (H y (unitVector j) (unitVector k) i * u y k
          + fderiv ℝ W₀ y (unitVector k) i * fderiv ℝ (fun x => u x k) y (unitVector j))) j := fun k =>
    ((weakPartial_of_contDiff _ (cWk k) j).mul_smooth (cWk k).continuous (d1_smooth u hu k i)).add
      ((weakPartial_secondDeriv k (h.hweak k) i j).mul_smooth (cdW k) (comp_smooth u hu k))
  refine weakPartial_congr (WeakPartial.sum Finset.univ (fun k _ => P k)) (fun y => ?_) (fun y => ?_)
  · simp only [PiLp.add_apply]
    rw [apply_self (fderiv ℝ u y) (W₀ y) i, apply_self (fderiv ℝ W₀ y) (u y) i, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  · unfold jetA
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [fderiv_component W₀ (hdW y), d2_eq u hu y i k j, fderiv_component u (hdu y)]
    ring

end SliceStretchInternal

namespace SliceStretchInternal

open Coercive.SmoothEnergyIdentityInternal.Stretch

theorem adv_le {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (y : Space) (i : Fin 3) :
    |(fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i| ≤ 2 * D * atom u y := by
  have e1 : ‖fderiv ℝ u y (W₀ y)‖ ≤ atom u y * D :=
    ((fderiv ℝ u y).le_opNorm _).trans (mul_le_mul (le1 u y) (h.W0 y) (norm_nonneg _) (atom_nonneg u y))
  have e2 : ‖fderiv ℝ W₀ y (u y)‖ ≤ 1 * D * atom u y := by
    have h3 := decay_mul_le h y ‖fderiv ℝ W₀ y‖ ‖u y‖ 1 zero_le_one
      (by rw [abs_norm, one_mul]; exact h.W1 y) (by rw [abs_norm])
    rw [abs_mul, abs_norm, abs_norm] at h3
    exact ((fderiv ℝ W₀ y).le_opNorm (u y)).trans h3
  refine (coord_abs_le _ i).trans ((norm_add_le _ _).trans ?_)
  linarith

theorem jetA_le {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (y : Space) (i j : Fin 3) :
    |jetA u W₀ (H y) y i j| ≤ 12 * D * atom u y := by
  unfold jetA
  have hN := atom_nonneg u y
  have hb : ∀ k : Fin 3, |W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i
        + fderiv ℝ W₀ y (unitVector j) k * fderiv ℝ u y (unitVector k) i
        + u y k * H y (unitVector j) (unitVector k) i
        + fderiv ℝ u y (unitVector j) k * fderiv ℝ W₀ y (unitVector k) i| ≤ 4 * D * atom u y := by
    intro k
    have t1 := prod_le ((coord_abs_le _ k).trans (h.W0 y)) (ddu_le u y j k i)
    have t2 := prod_le ((entry_abs_le _ j k).trans (grad_le_const h y)) (du_le u y k i)
    have t3 : |u y k * H y (unitVector j) (unitVector k) i| ≤ 1 * D * atom u y := by
      rw [mul_comm]
      exact decay_mul_le h y _ _ 1 zero_le_one (by rw [one_mul]; exact (entry2_abs_le _ j k i).trans (h.W2 y))
        (coord_abs_le _ k)
    have t4 := prod_le (du_le u y j k) ((entry_abs_le _ k i).trans (grad_le_const h y))
    have abs4 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
      have h1 := abs_add_le (a + b + c) d
      have h2 := abs_add_le (a + b) c
      have h3 := abs_add_le a b
      linarith
    refine (abs4 _ _ _ _).trans ?_
    linarith
  have := sum3_le _ _ hb
  linarith

theorem int_adv_term {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (i j l : Fin 3) :
    Integrable (fun y => (alternatingSymbol i j l * (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i) *
        fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j)) := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have D0 := h.D0
  have cw : ContDiff ℝ ∞ (fun x => curlVec (fderiv ℝ u x) l) := curl_contDiff u hu (n := ∞) (by simp) l
  have cu : Continuous u := hu.continuous
  have c1 : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cA : Continuous (fun y => (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i) := by fun_prop
  have cdw : Continuous (fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j)) :=
    (cw.continuous_fderiv (by simp)).clm_apply continuous_const
  refine int_N (atom u) _ (atom_nonneg u) (atom_sq_slice h) ((continuous_const.mul cA).mul cdw) (18 * D)
    (by linarith) (fun y => ?_)
  exact (prod_le (prod_le (eps_abs_le _ _ _) (adv_le h y i)) (dcurl_le u h2 y l j)).trans
    (le_of_eq (by ring))

theorem int_jet_term {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (i j l : Fin 3) :
    Integrable (fun y => (alternatingSymbol i j l * jetA u W₀ (H y) y i j) * curlVec (fderiv ℝ u y) l) := by
  have hu := h.hu
  have hW := h.hW
  have hN0 := atom_nonneg u
  have hN := atom_sq_slice h
  have D0 := h.D0
  have cu : Continuous u := hu.continuous
  have c1 : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have c2 : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cP : Continuous (fun p : Space × (Space →L[ℝ] Space →L[ℝ] Space) =>
      (alternatingSymbol i j l * jetA u W₀ p.2 p.1 i j) * curlVec (fderiv ℝ u p.1) l) := by
    unfold jetA curlVec
    fun_prop
  refine int_dom _ (fun y => 108 * D * atom u y) (atom u) (aesm_pair h cP) (sq_const_mul hN _) hN
    (fun y => ?_) (fun y => mul_nonneg (by linarith) (hN0 y)) hN0
  exact (prod_le (prod_le (eps_abs_le _ _ _) (jetA_le h y i j)) (curl_le u y l)).trans
    (le_of_eq (by ring))

theorem term_ibp {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) (i j l : Fin 3) :
    ∫ y, (alternatingSymbol i j l * (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i) *
        fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j) =
      -∫ y, (alternatingSymbol i j l * jetA u W₀ (H y) y i j) * curlVec (fderiv ℝ u y) l := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hN0 := atom_nonneg u
  have hN := atom_sq_slice h
  have D0 := h.D0
  have cw : ContDiff ℝ ∞ (fun x => curlVec (fderiv ℝ u x) l) := curl_contDiff u hu (n := ∞) (by simp) l
  have cu : Continuous u := hu.continuous
  have c1 : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have c2 : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ u x) y) :=
    (hu.fderiv_right (m := ∞) (by simp)).continuous_fderiv (by simp)
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cA : Continuous (fun y => (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i) := by fun_prop
  have cdw : Continuous (fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j)) :=
    (cw.continuous_fderiv (by simp)).clm_apply continuous_const
  refine weak_ibp ((weakPartial_adv h i j).const_mul (alternatingSymbol i j l)) cw ?_ ?_ ?_
  · refine int_N (atom u) _ hN0 hN ((continuous_const.mul cA).mul cdw) (18 * D) (by linarith) (fun y => ?_)
    exact (prod_le (prod_le (eps_abs_le _ _ _) (adv_le h y i)) (dcurl_le u h2 y l j)).trans
      (le_of_eq (by ring))
  · have cP : Continuous (fun p : Space × (Space →L[ℝ] Space →L[ℝ] Space) =>
        (alternatingSymbol i j l * jetA u W₀ p.2 p.1 i j) * curlVec (fderiv ℝ u p.1) l) := by
      unfold jetA curlVec
      fun_prop
    refine int_dom _ (fun y => 108 * D * atom u y) (atom u) (aesm_pair h cP) (sq_const_mul hN _) hN
      (fun y => ?_) (fun y => mul_nonneg (by linarith) (hN0 y)) hN0
    exact (prod_le (prod_le (eps_abs_le _ _ _) (jetA_le h y i j)) (curl_le u y l)).trans
      (le_of_eq (by ring))
  · refine int_N (atom u) _ hN0 hN ?_ (18 * D) (by linarith) (fun y => ?_)
    · exact ((continuous_const.mul cA).abs.mul cw.continuous.abs).div
        (continuous_const.add continuous_norm) (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')
    · have h1 : 0 ≤ |alternatingSymbol i j l * (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i| *
          |curlVec (fderiv ℝ u y) l| := by positivity
      rw [abs_of_nonneg (by positivity)]
      refine (div_le_self h1 (one_le_add_norm y)).trans ?_
      rw [← abs_mul]
      exact (prod_le (prod_le (eps_abs_le _ _ _) (adv_le h y i)) (curl_le u y l)).trans
        (le_of_eq (by ring))

end SliceStretchInternal

open SliceStretchInternal Coercive.SmoothEnergyIdentityInternal.Stretch in
theorem stretch_weak {u W₀ : Space → Space} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (h : WeakSliceData u W₀ H D) :
    ∫ y, inner ℝ (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y))
        (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (H y) j m) * curlVec (fderiv ℝ u y) j
        + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l) := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hN0 := atom_nonneg u
  have hN := atom_sq_slice h
  have D0 := h.D0
  have cu : Continuous u := hu.continuous
  have c1 : Continuous (fun y => fderiv ℝ u y) := hu.continuous_fderiv (by simp)
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cO : ∀ j, Continuous (fun x => curlVec (fderiv ℝ W₀ x) j) := fun j => by
    unfold curlVec
    fun_prop
  have cw : ∀ l, Continuous (fun x => curlVec (fderiv ℝ u x) l) := fun l =>
    (curl_contDiff u hu (n := ∞) (by simp) l).continuous
  have cDu : ∀ j i, Continuous (fun x => fderiv ℝ u x (unitVector j) i) := fun j i =>
    (d1_smooth u hu j i).continuous
  have cU : ∀ l, Continuous (fun x => u x l) := fun l => (comp_smooth u hu l).continuous
  have cS : ∀ i j, Continuous (fun x => (fderiv ℝ W₀ x (unitVector j) i + fderiv ℝ W₀ x (unitVector i) j) / 2) := by
    intro i j
    fun_prop
  have cWk : ∀ k, Continuous (fun x => W₀ x k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp cW
  have cdw : ∀ l k, Continuous (fun y => fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) :=
    fun l k => ((curl_contDiff u hu (n := ∞) (by simp) l).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have sa : ∀ y, inner ℝ (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y))
      (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∑ t : Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) t.1) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) t.2.2) y (unitVector t.2.1) := by
    intro y
    rw [inner_coord]
    simp only [ssp_curl u h2 h.hd y, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have ae : (fun y => -∑ t : Fin 3 × Fin 3 × Fin 3,
        (alternatingSymbol t.1 t.2.1 t.2.2 * jetA u W₀ (H y) y t.1 t.2.1) * curlVec (fderiv ℝ u y) t.2.2)
      =ᵐ[volume] fun y => ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (H y) j m) * curlVec (fderiv ℝ u y) j)
      + -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
          curlVec (fderiv ℝ u y) i) := by
    filter_upwards [h.hsym] with y hy
    have e := curl_grad_weak u W₀ (H y) h2 h.hd y (h.hWd y) hy
    simp only [Fintype.sum_prod_type]
    unfold jetA
    exact e
  have iTs : Integrable (fun y => ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) := by
    refine integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun k _ => ?_))
    refine int_N (atom u) _ hN0 hN (((cWk k).mul (cw l)).mul (cdw l k)) (81 * D) (by linarith) (fun y => ?_)
    exact (prod_le (prod_le ((coord_abs_le _ k).trans (h.W0 y)) (curl_le u y l)) (dcurl_le u h2 y l k)).trans
      (le_of_eq (by ring))
  have iR1 : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)) := by
    refine (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))).neg
    refine int_N (atom u) _ hN0 hN (((cw i).mul (cS i j)).mul (cw j)) (81 * D) (by linarith) (fun y => ?_)
    have hs : |(fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2| ≤ D := by
      rw [abs_div, abs_two]
      have := (entry_abs_le (fderiv ℝ W₀ y) j i).trans (grad_le_const h y)
      have := (entry_abs_le (fderiv ℝ W₀ y) i j).trans (grad_le_const h y)
      rw [div_le_iff₀ (by norm_num)]
      linarith [abs_add_le (fderiv ℝ W₀ y (unitVector j) i) (fderiv ℝ W₀ y (unitVector i) j)]
    exact (prod_le (prod_le (curl_le u y i) hs) (curl_le u y j)).trans (le_of_eq (by ring))
  have iR2 : Integrable (fun y => ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (H y) j m) *
          curlVec (fderiv ℝ u y) j) := by
    refine integrable_finsetSum _ (fun j _ => ?_)
    have cP : Continuous (fun p : Space × (Space →L[ℝ] Space →L[ℝ] Space) =>
        (∑ m : Fin 3, u p.1 m * vortGrad p.2 j m) * curlVec (fderiv ℝ u p.1) j) := by
      unfold vortGrad curlVec
      fun_prop
    refine int_dom _ (fun y => 243 * D * atom u y) (atom u) (aesm_pair h cP) (sq_const_mul hN _) hN
      (fun y => ?_) (fun y => mul_nonneg (by linarith) (hN0 y)) hN0
    have hs : |∑ m : Fin 3, u y m * vortGrad (H y) j m| ≤ 3 * (9 * D * atom u y) := by
      refine sum3_le _ _ (fun m => ?_)
      rw [mul_comm]
      exact decay_mul_le h y _ _ 9 (by norm_num) ((vortGrad_abs_le _ j m).trans (by linarith [h.W2 y]))
        (coord_abs_le _ m)
    exact (prod_le hs (curl_le u y j)).trans (le_of_eq (by ring))
  have iR : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (H y) j m) * curlVec (fderiv ℝ u y) j) := iR1.add iR2
  have iX : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j *
      fderiv ℝ u y (unitVector j) i * curlVec (fderiv ℝ u y) i)) := by
    refine (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))).neg
    refine int_N (atom u) _ hN0 hN (((cO j).mul (cDu j i)).mul (cw i)) (81 * D) (by linarith) (fun y => ?_)
    have hO : |curlVec (fderiv ℝ W₀ y) j| ≤ 9 * D := (curl_abs_le _ j).trans (by linarith [grad_le_const h y])
    exact (prod_le (prod_le hO (du_le u y j i)) (curl_le u y i)).trans (le_of_eq (by ring))
  have i3 : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l) := by
    refine Integrable.const_mul (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => ?_))))) _
    have cP : Continuous (fun p : Space × (Space →L[ℝ] Space →L[ℝ] Space) =>
        alternatingSymbol i m l * vortGrad p.2 j m * fderiv ℝ u p.1 (unitVector j) i * u p.1 l) := by
      unfold vortGrad
      fun_prop
    refine int_dom _ (fun y => 9 * D * atom u y) (atom u) (aesm_pair h cP) (sq_const_mul hN _) hN
      (fun y => ?_) (fun y => mul_nonneg (by linarith) (hN0 y)) hN0
    have hdec := decay_mul_le h y (vortGrad (H y) j m) (u y l) 9 (by norm_num)
      ((vortGrad_abs_le _ j m).trans (by linarith [h.W2 y])) (coord_abs_le _ l)
    rw [abs_mul] at hdec
    have he := eps_abs_le i m l
    have hdu := du_le u y j i
    have hn := hN0 y
    calc |alternatingSymbol i m l * vortGrad (H y) j m * fderiv ℝ u y (unitVector j) i * u y l|
          = (|alternatingSymbol i m l| * |fderiv ℝ u y (unitVector j) i|)
            * (|vortGrad (H y) j m| * |u y l|) := by
          rw [abs_mul, abs_mul, abs_mul]; ring
      _ ≤ (1 * atom u y) * (9 * D * atom u y) :=
          mul_le_mul (mul_le_mul he hdu (abs_nonneg _) zero_le_one) hdec (by positivity) (by positivity)
      _ = 9 * D * atom u y * atom u y := by ring
  have iTR : Integrable (fun y => ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (H y) j m) * curlVec (fderiv ℝ u y) j)) := iTs.add iR
  simp_rw [sa]
  rw [integral_finsetSum _ (fun t _ => int_adv_term h t.1 t.2.1 t.2.2),
    Finset.sum_congr rfl (fun t _ => term_ibp h t.1 t.2.1 t.2.2), Finset.sum_neg_distrib,
    ← integral_finsetSum _ (fun t _ => int_jet_term h t.1 t.2.1 t.2.2), ← integral_neg,
    integral_congr_ae ae, integral_add iTR iX, integral_add iTs iR, transport_weak h,
    x_term_weak h, zero_add, ← integral_add iR i3]

end EnergyIdentityWeakInternal

end CoerciveWeak

end Breakdown

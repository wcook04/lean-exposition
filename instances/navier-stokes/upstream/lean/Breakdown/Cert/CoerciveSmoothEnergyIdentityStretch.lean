import Breakdown.Cert.CoerciveSmoothEnergyIdentityDefs

open scoped ContDiff ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace Coercive

namespace SmoothEnergyIdentityInternal

open EnergyIdentityInternal

namespace Stretch

theorem eps_abs_le (i j l : Fin 3) : |alternatingSymbol i j l| ≤ 1 := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol]

theorem entry_abs_le (G : Space →L[ℝ] Space) (j i : Fin 3) : |G (unitVector j) i| ≤ ‖G‖ := by
  refine (coord_abs_le _ i).trans ?_
  have := G.le_opNorm (unitVector j)
  rwa [unitVector_norm, mul_one] at this

theorem entry2_abs_le (H : Space →L[ℝ] Space →L[ℝ] Space) (j k i : Fin 3) :
    |H (unitVector j) (unitVector k) i| ≤ ‖H‖ := by
  refine (entry_abs_le _ k i).trans ?_
  have := H.le_opNorm (unitVector j)
  rwa [unitVector_norm, mul_one] at this

theorem sum9_le (f : Fin 3 → Fin 3 → ℝ) (M : ℝ) (h : ∀ a b, |f a b| ≤ M) :
    |∑ a : Fin 3, ∑ b : Fin 3, f a b| ≤ 9 * M := by
  calc |∑ a : Fin 3, ∑ b : Fin 3, f a b| ≤ ∑ a : Fin 3, |∑ b : Fin 3, f a b| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, |f a b| :=
        Finset.sum_le_sum (fun a _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, M :=
        Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => h a b))
    _ = 9 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem eps_mul_le (i j l : Fin 3) (x : ℝ) (M : ℝ) (hx : |x| ≤ M) : |alternatingSymbol i j l * x| ≤ M := by
  rw [abs_mul]
  have h0 : 0 ≤ M := (abs_nonneg x).trans hx
  calc |alternatingSymbol i j l| * |x| ≤ 1 * M := by
        gcongr
        exact eps_abs_le i j l
    _ = M := one_mul M

theorem curl_abs_le (G : Space →L[ℝ] Space) (l : Fin 3) : |curlVec G l| ≤ 9 * ‖G‖ := by
  rw [curlVec_apply]
  exact sum9_le _ _ (fun a b => eps_mul_le _ _ _ _ _ (entry_abs_le G a b))

theorem curl_deriv_abs_le (u : Space → Space) (hu : ContDiff ℝ 2 u) (y : Space) (l j : Fin 3) :
    |fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j)|
      ≤ 9 * ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ := by
  rw [curl_deriv u hu]
  exact sum9_le _ _ (fun a b => eps_mul_le _ _ _ _ _ (entry2_abs_le _ j a b))

theorem vortGrad_abs_le (H : Space →L[ℝ] Space →L[ℝ] Space) (j m : Fin 3) :
    |vortGrad H j m| ≤ 9 * ‖H‖ := by
  unfold vortGrad
  exact sum9_le _ _ (fun a b => eps_mul_le _ _ _ _ _ (entry2_abs_le _ m a b))

theorem int_dom (h a b : Space → ℝ) (hh : AEStronglyMeasurable h) (ha : Integrable (fun y => a y ^ 2))
    (hb : Integrable (fun y => b y ^ 2)) (hab : ∀ y, |h y| ≤ a y * b y) (ha0 : ∀ y, 0 ≤ a y)
    (hb0 : ∀ y, 0 ≤ b y) : Integrable h := by
  refine Integrable.mono' ((ha.add hb).div_const 2) hh (Eventually.of_forall (fun y => ?_))
  rw [Real.norm_eq_abs]
  show |h y| ≤ (a y ^ 2 + b y ^ 2) / 2
  refine (hab y).trans ?_
  have := ha0 y; have := hb0 y
  nlinarith [sq_nonneg (a y - b y)]

theorem sq_const_mul {a : Space → ℝ} (ha : Integrable (fun y => a y ^ 2)) (c : ℝ) :
    Integrable (fun y => (c * a y) ^ 2) := by
  have := ha.const_mul (c ^ 2)
  refine this.congr (Eventually.of_forall (fun y => ?_))
  simp only
  ring

theorem wibp (f g : Space → ℝ) (j : Fin 3) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (h1 : Integrable (fun y => f y * fderiv ℝ g y (unitVector j)))
    (h2 : Integrable (fun y => fderiv ℝ f y (unitVector j) * g y))
    (h3 : Integrable (fun y => |f y| * |g y| / (1 + ‖y‖))) :
    ∫ y, f y * fderiv ℝ g y (unitVector j) = -∫ y, fderiv ℝ f y (unitVector j) * g y := by
  have ha : ContDiff ℝ 1 (fun y => f y • unitVector j) := hf.smul contDiff_const
  have e1 : (fun y => fderiv ℝ g y (f y • unitVector j)) = fun y => f y * fderiv ℝ g y (unitVector j) := by
    funext y
    rw [map_smul, smul_eq_mul]
  have e2 : (fun y => divergenceAt (fun x => f x • unitVector j) y * g y) =
      fun y => fderiv ℝ f y (unitVector j) * g y := by
    funext y
    rw [div_smul f (fun _ => unitVector j) y ((hf.differentiable (by norm_num)) y)
      (differentiableAt_const _)]
    simp [divergenceAt]
  have e3 : (fun y => ‖f y • unitVector j‖ * |g y| / (1 + ‖y‖)) = fun y => |f y| * |g y| / (1 + ‖y‖) := by
    funext y
    rw [norm_smul, unitVector_norm, mul_one, Real.norm_eq_abs]
  have h := weighted_ibp (fun y => f y • unitVector j) g ha hg (by rw [e1]; exact h1) (by rw [e2]; exact h2)
    (by rw [e3]; exact h3)
  rw [e1, e2] at h
  exact h

theorem wibp_sum {ι : Type*} (s : Finset ι) (f g : ι → Space → ℝ) (m : ι → Fin 3)
    (hf : ∀ t ∈ s, ContDiff ℝ 1 (f t)) (hg : ∀ t ∈ s, ContDiff ℝ 1 (g t))
    (i1 : ∀ t ∈ s, Integrable (fun y => f t y * fderiv ℝ (g t) y (unitVector (m t))))
    (i2 : ∀ t ∈ s, Integrable (fun y => fderiv ℝ (f t) y (unitVector (m t)) * g t y))
    (i3 : ∀ t ∈ s, Integrable (fun y => |f t y| * |g t y| / (1 + ‖y‖))) :
    ∫ y, ∑ t ∈ s, f t y * fderiv ℝ (g t) y (unitVector (m t)) =
      -∫ y, ∑ t ∈ s, fderiv ℝ (f t) y (unitVector (m t)) * g t y := by
  rw [integral_finsetSum _ i1, integral_finsetSum _ i2, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl (fun t ht => wibp _ _ _ (hf t ht) (hg t ht) (i1 t ht) (i2 t ht) (i3 t ht))

end Stretch


namespace Stretch

theorem prod_le {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]
  exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem neps_abs_le (i j l : Fin 3) : |-alternatingSymbol i j l| ≤ 1 := by
  rw [abs_neg]
  exact eps_abs_le i j l

theorem sum_term_le {c p1 p2 x M1 M2 B : ℝ} (hc : |c| ≤ 1) (h1 : |p1| ≤ M1) (h2 : |p2| ≤ M2)
    (hx : |x| ≤ B) : |c * (p1 + p2) * x| ≤ (M1 + M2) * B := by
  have hS : |p1 + p2| ≤ M1 + M2 := (abs_add_le _ _).trans (add_le_add h1 h2)
  have := prod_le (prod_le hc hS) hx
  rwa [one_mul] at this

theorem two_term_le {c a1 b1 a2 b2 g M1 M2 B1 B2 : ℝ} (hc : |c| ≤ 1) (h1 : |a1| * |g| ≤ M1)
    (h2 : |a2| * |g| ≤ M2) (hb1 : |b1| ≤ B1) (hb2 : |b2| ≤ B2) :
    |c * (a1 * b1 + a2 * b2) * g| ≤ M1 * B1 + M2 * B2 := by
  have hS : |a1 * b1 + a2 * b2| ≤ |a1| * |b1| + |a2| * |b2| :=
    (abs_add_le _ _).trans (by rw [abs_mul, abs_mul])
  have n1 : (0 : ℝ) ≤ |a1| * |g| := by positivity
  have n2 : (0 : ℝ) ≤ |a2| * |g| := by positivity
  calc |c * (a1 * b1 + a2 * b2) * g| = |c| * |a1 * b1 + a2 * b2| * |g| := by rw [abs_mul, abs_mul]
    _ ≤ 1 * (|a1| * |b1| + |a2| * |b2|) * |g| := by gcongr
    _ = (|a1| * |g|) * |b1| + (|a2| * |g|) * |b2| := by ring
    _ ≤ M1 * B1 + M2 * B2 :=
        add_le_add (mul_le_mul h1 hb1 (abs_nonneg _) (n1.trans h1))
          (mul_le_mul h2 hb2 (abs_nonneg _) (n2.trans h2))

theorem int_N (N f : Space → ℝ) (hN0 : ∀ y, 0 ≤ N y) (hN : Integrable (fun y => N y ^ 2))
    (hf : Continuous f) (K : ℝ) (hK : 0 ≤ K) (hb : ∀ y, |f y| ≤ K * (N y * N y)) : Integrable f := by
  refine int_dom f (fun y => K * N y) N hf.aestronglyMeasurable (sq_const_mul hN K) hN
    (fun y => ?_) (fun y => mul_nonneg hK (hN0 y)) hN0
  show |f y| ≤ K * N y * N y
  rw [mul_assoc]
  exact hb y

theorem wibp_N {ι : Type*} (s : Finset ι) (N : Space → ℝ) (hN0 : ∀ y, 0 ≤ N y)
    (hN : Integrable (fun y => N y ^ 2)) (f g : ι → Space → ℝ) (m : ι → Fin 3) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ t ∈ s, ContDiff ℝ 1 (f t)) (hg : ∀ t ∈ s, ContDiff ℝ 1 (g t))
    (b1 : ∀ t ∈ s, ∀ y, |f t y * fderiv ℝ (g t) y (unitVector (m t))| ≤ K * (N y * N y))
    (b2 : ∀ t ∈ s, ∀ y, |fderiv ℝ (f t) y (unitVector (m t)) * g t y| ≤ K * (N y * N y))
    (b3 : ∀ t ∈ s, ∀ y, |f t y| * |g t y| ≤ K * (N y * N y)) :
    ∫ y, ∑ t ∈ s, f t y * fderiv ℝ (g t) y (unitVector (m t)) =
      -∫ y, ∑ t ∈ s, fderiv ℝ (f t) y (unitVector (m t)) * g t y := by
  refine wibp_sum s f g m hf hg (fun t ht => ?_) (fun t ht => ?_) (fun t ht => ?_)
  · exact int_N N _ hN0 hN (((hf t ht).continuous).mul
      (((hg t ht).continuous_fderiv (by norm_num)).clm_apply continuous_const)) K hK (b1 t ht)
  · exact int_N N _ hN0 hN ((((hf t ht).continuous_fderiv (by norm_num)).clm_apply
      continuous_const).mul (hg t ht).continuous) K hK (b2 t ht)
  · refine int_N N _ hN0 hN ?_ K hK (fun y => ?_)
    · exact ((hf t ht).continuous.abs.mul (hg t ht).continuous.abs).div
        (continuous_const.add continuous_norm) (fun y => (add_pos_of_pos_of_nonneg one_pos (norm_nonneg y)).ne')
    · have h1 : 0 ≤ |f t y| * |g t y| := by positivity
      have h2 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      rw [abs_of_nonneg (by positivity)]
      exact (div_le_self h1 h2).trans (b3 t ht y)

structure DecayData (u W₀ : Space → Space) (D : ℝ) : Prop where
  hu : ContDiff ℝ ∞ u
  hW : ContDiff ℝ 2 W₀
  D0 : 0 ≤ D
  W0 : ∀ y, ‖W₀ y‖ ≤ D
  W1 : ∀ y, ‖fderiv ℝ W₀ y‖ ≤ D / (1 + ‖y‖)
  W2 : ∀ y, ‖fderiv ℝ (fun x => fderiv ℝ W₀ x) y‖ ≤ D / (1 + ‖y‖)
  i0 : Integrable (fun y => ‖u y‖ ^ 2 / (1 + ‖y‖) ^ 2)
  i1 : Integrable (fun y => ‖fderiv ℝ u y‖ ^ 2)
  i2 : Integrable (fun y => ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ ^ 2)

def atom (u : Space → Space) (y : Space) : ℝ :=
  ‖u y‖ / (1 + ‖y‖) + ‖fderiv ℝ u y‖ + ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖

theorem atom_nonneg (u : Space → Space) (y : Space) : 0 ≤ atom u y := by
  unfold atom
  positivity

theorem atom_sq {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) :
    Integrable (fun y => atom u y ^ 2) := by
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

theorem le0 (u : Space → Space) (y : Space) : ‖u y‖ / (1 + ‖y‖) ≤ atom u y := by
  unfold atom
  linarith [norm_nonneg (fderiv ℝ u y), norm_nonneg (fderiv ℝ (fun x => fderiv ℝ u x) y)]

theorem le1 (u : Space → Space) (y : Space) : ‖fderiv ℝ u y‖ ≤ atom u y := by
  unfold atom
  have : 0 ≤ ‖u y‖ / (1 + ‖y‖) := by positivity
  linarith [norm_nonneg (fderiv ℝ (fun x => fderiv ℝ u x) y)]

theorem le2 (u : Space → Space) (y : Space) : ‖fderiv ℝ (fun x => fderiv ℝ u x) y‖ ≤ atom u y := by
  unfold atom
  have : 0 ≤ ‖u y‖ / (1 + ‖y‖) := by positivity
  linarith [norm_nonneg (fderiv ℝ u y)]

theorem du_le (u : Space → Space) (y : Space) (j i : Fin 3) :
    |fderiv ℝ u y (unitVector j) i| ≤ atom u y :=
  (entry_abs_le _ j i).trans (le1 u y)

theorem ddu_le (u : Space → Space) (y : Space) (j k i : Fin 3) :
    |fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i| ≤ atom u y :=
  (entry2_abs_le _ j k i).trans (le2 u y)

theorem curl_le (u : Space → Space) (y : Space) (l : Fin 3) :
    |curlVec (fderiv ℝ u y) l| ≤ 9 * atom u y :=
  (curl_abs_le _ l).trans (by linarith [le1 u y])

theorem dcurl_le (u : Space → Space) (hu : ContDiff ℝ 2 u) (y : Space) (l j : Fin 3) :
    |fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector j)| ≤ 9 * atom u y :=
  (curl_deriv_abs_le u hu y l j).trans (by linarith [le2 u y])

theorem one_le_add_norm (y : Space) : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]

theorem decay_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (c x K : ℝ)
    (hK : 0 ≤ K) (hc : |c| ≤ K * (D / (1 + ‖y‖))) (hx : |x| ≤ ‖u y‖) :
    |c * x| ≤ K * D * atom u y := by
  rw [abs_mul]
  have hD : 0 ≤ D / (1 + ‖y‖) := div_nonneg h.D0 (by positivity)
  calc |c| * |x| ≤ K * (D / (1 + ‖y‖)) * ‖u y‖ :=
        mul_le_mul hc hx (abs_nonneg x) (mul_nonneg hK hD)
    _ = K * D * (‖u y‖ / (1 + ‖y‖)) := by ring
    _ ≤ K * D * atom u y := mul_le_mul_of_nonneg_left (le0 u y) (mul_nonneg hK h.D0)

theorem W1_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) :
    ‖fderiv ℝ W₀ y‖ ≤ D :=
  (h.W1 y).trans (div_le_self h.D0 (one_le_add_norm y))

theorem curlW_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (j : Fin 3) :
    |curlVec (fderiv ℝ W₀ y) j| ≤ 9 * (D / (1 + ‖y‖)) :=
  (curl_abs_le _ j).trans (by linarith [h.W1 y])

theorem curlW_le' {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (j : Fin 3) :
    |curlVec (fderiv ℝ W₀ y) j| ≤ 9 * D :=
  (curl_abs_le _ j).trans (by linarith [W1_le h y])

theorem dcurlW_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (j k : Fin 3) :
    |fderiv ℝ (fun x => curlVec (fderiv ℝ W₀ x) j) y (unitVector k)| ≤ 9 * (D / (1 + ‖y‖)) :=
  (curl_deriv_abs_le W₀ h.hW y j k).trans (by linarith [h.W2 y])

end Stretch


namespace Stretch

theorem sum3_le (f : Fin 3 → ℝ) (M : ℝ) (h : ∀ a, |f a| ≤ M) : |∑ a : Fin 3, f a| ≤ 3 * M := by
  calc |∑ a : Fin 3, f a| ≤ ∑ a : Fin 3, |f a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a : Fin 3, M := Finset.sum_le_sum (fun a _ => h a)
    _ = 3 * M := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

theorem kmono {a c K N : ℝ} (ha : a ≤ c * (N * N)) (hc : c ≤ K) : a ≤ K * (N * N) :=
  ha.trans (mul_le_mul_of_nonneg_right hc (mul_self_nonneg N))

theorem x_term_decay {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) :
    ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l := by
  have hu := h.hu
  have hW := h.hW
  have hdu : Differentiable ℝ u := hu.differentiable (by simp)
  have hN0 := atom_nonneg u
  have hN := atom_sq h
  have D0 := h.D0
  have cO : ∀ j, ContDiff ℝ 1 (fun x => curlVec (fderiv ℝ W₀ x) j) := fun j =>
    curl_contDiff W₀ hW (by norm_num) j
  have cddW : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ W₀ x) y) :=
    (hW.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have cVG : ∀ j m, Continuous (fun x => vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) x) j m) := by
    intro j m
    unfold vortGrad
    fun_prop
  have cDu : ∀ j i, Continuous (fun x => fderiv ℝ u x (unitVector j) i) := fun j i =>
    (d1_smooth u hu j i).continuous
  have cU : ∀ l, Continuous (fun x => u x l) := fun l => (comp_smooth u hu l).continuous
  have hdec : ∀ y (j l : Fin 3), |curlVec (fderiv ℝ W₀ y) j * u y l| ≤ 9 * D * atom u y := fun y j l =>
    decay_le h y _ _ 9 (by norm_num) (curlW_le h y j) (coord_abs_le _ l)
  have hdec' : ∀ y (j k l : Fin 3),
      |fderiv ℝ (fun x => curlVec (fderiv ℝ W₀ x) j) y (unitVector k) * u y l| ≤ 9 * D * atom u y :=
    fun y j k l => decay_le h y _ _ 9 (by norm_num) (dcurlW_le h y j k) (coord_abs_le _ l)
  have hK : (0 : ℝ) ≤ 18 * D := by linarith
  have iR3 : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l) := by
    refine Integrable.const_mul (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => ?_))))) _
    refine int_N (atom u) _ hN0 hN (((continuous_const.mul (cVG j m)).mul (cDu j i)).mul (cU l)) (9 * D)
      (by linarith) (fun y => ?_)
    have hd := decay_le h y (vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) (u y l) 9 (by norm_num)
      ((vortGrad_abs_le _ j m).trans (by linarith [h.W2 y])) (coord_abs_le _ l)
    rw [abs_mul] at hd
    have he := eps_abs_le i m l
    have hdu' := du_le u y j i
    have hn := hN0 y
    calc |alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l|
          = (|alternatingSymbol i m l| * |fderiv ℝ u y (unitVector j) i|)
            * (|vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m| * |u y l|) := by
          rw [abs_mul, abs_mul, abs_mul]; ring
      _ ≤ (1 * atom u y) * (9 * D * atom u y) :=
          mul_le_mul (mul_le_mul he hdu' (abs_nonneg _) zero_le_one) hd (by positivity) (by positivity)
      _ = 9 * D * (atom u y * atom u y) := by ring
  have iY : Integrable (fun y => ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1)) := by
    refine integrable_finsetSum _ (fun t _ => ?_)
    refine int_N (atom u) _ hN0 hN ((continuous_const.mul ((cO _).continuous.mul (cU _))).mul
      (((d1_smooth u hu _ _).continuous_fderiv (by simp)).clm_apply continuous_const)) (9 * D)
      (by linarith) (fun y => ?_)
    rw [d2_eq u hu]
    exact (prod_le (prod_le (eps_abs_le _ _ _) (hdec y _ _)) (ddu_le u y _ _ _)).trans (le_of_eq (by ring))
  have e1 : ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) =
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) := by
    congr 1; funext y; exact x_split u W₀ hdu y
  have e2 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (-alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * fderiv ℝ u y (unitVector t.2.1) t.1)) *
          fderiv ℝ (fun x => u x t.2.2.2) y (unitVector t.2.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) y (unitVector t.2.2.1) *
          u y t.2.2.2 :=
    wibp_N _ (atom u) hN0 hN (fun (t : Fin 3 × Fin 3 × Fin 3 × Fin 3) (x : Space) => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) (fun t x => u x t.2.2.2)
      (fun t => t.2.2.1) (18 * D) hK
      (fun t _ => cmul_contDiff _ _ _ (cO _) ((d1_smooth u hu _ _).of_le one_le_inf))
      (fun t _ => (comp_smooth u hu _).of_le one_le_inf)
      (fun t _ y => by
        rw [fderiv_component u (hdu y)]
        exact kmono ((prod_le (prod_le (neps_abs_le _ _ _) (prod_le (curlW_le' h y _) (du_le u y _ _)))
          (du_le u y _ _)).trans (le_of_eq (by ring))) (by linarith : 9 * D ≤ 18 * D))
      (fun t _ y => by
        rw [cmul_deriv _ _ _ y _ ((cO _).differentiable (by norm_num) y)
          (((d1_smooth u hu _ _).differentiable (by simp)) y), d2_eq u hu]
        have h1 := hdec' y t.2.1 t.2.2.1 t.2.2.2
        have h2 := hdec y t.2.1 t.2.2.2
        rw [abs_mul] at h1 h2
        exact (two_term_le (neps_abs_le _ _ _) h1 h2 (du_le u y _ _) (ddu_le u y _ _ _)).trans
          (le_of_eq (by ring)))
      (fun t _ y => by
        have h2 := hdec y t.2.1 t.2.2.2
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
          _ ≤ 18 * D * (atom u y * atom u y) := by nlinarith [mul_self_nonneg (atom u y)])
  have e3 : -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => -alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * fderiv ℝ u x (unitVector t.2.1) t.1)) y (unitVector t.2.2.1) *
          u y t.2.2.2 =
      2 * (∫ y, (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
        alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
          * fderiv ℝ u y (unitVector j) i * u y l) +
      ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) := by
    rw [← integral_neg, ← integral_const_mul, ← integral_add (iR3.const_mul 2) iY]
    congr 1; funext y; exact x_expand u W₀ hu hW y
  have e4 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ y) t.2.1 * u y t.2.2.2)) *
          fderiv ℝ (fun x => fderiv ℝ u x (unitVector t.2.2.1) t.1) y (unitVector t.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) y (unitVector t.2.1) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 :=
    wibp_N _ (atom u) hN0 hN (fun (t : Fin 3 × Fin 3 × Fin 3 × Fin 3) (x : Space) => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) (fun t x => fderiv ℝ u x (unitVector t.2.2.1) t.1)
      (fun t => t.2.1) (18 * D) hK
      (fun t _ => cmul_contDiff _ _ _ (cO _) ((comp_smooth u hu _).of_le one_le_inf))
      (fun t _ => (d1_smooth u hu _ _).of_le one_le_inf)
      (fun t _ y => by
        rw [d2_eq u hu]
        exact kmono ((prod_le (prod_le (eps_abs_le _ _ _) (hdec y _ _)) (ddu_le u y _ _ _)).trans
          (le_of_eq (by ring))) (by linarith : 9 * D ≤ 18 * D))
      (fun t _ y => by
        rw [cmul_deriv _ _ _ y _ ((cO _).differentiable (by norm_num) y)
          (((comp_smooth u hu _).differentiable (by simp)) y), fderiv_component u (hdu y)]
        exact (sum_term_le (eps_abs_le _ _ _) (hdec' y _ _ _)
          (prod_le (curlW_le' h y _) (du_le u y _ _)) (du_le u y _ _)).trans (le_of_eq (by ring)))
      (fun t _ y => by
        rw [← abs_mul]
        exact kmono ((prod_le (prod_le (eps_abs_le _ _ _) (hdec y _ _)) (du_le u y _ _)).trans
          (le_of_eq (by ring))) (by linarith : 9 * D ≤ 18 * D))
  have e5 : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.2.1 t.2.2.2 *
        (curlVec (fderiv ℝ W₀ x) t.2.1 * u x t.2.2.2)) y (unitVector t.2.1) *
          fderiv ℝ u y (unitVector t.2.2.1) t.1 =
      ∫ y, -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
        curlVec (fderiv ℝ u y) i) := by
    congr 1; funext y; exact y_point u W₀ hu hW y
  rw [e4, e5] at e3
  rw [e1, e2, e3]
  rw [← e2, ← e1] at e3
  linarith

theorem transport_decay {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D)
    (hWd : ∀ y, divergenceAt W₀ y = 0) :
    ∫ y, ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k) = 0 := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hN0 := atom_nonneg u
  have hN := atom_sq h
  have D0 := h.D0
  have hdW : Differentiable ℝ W₀ := hW.differentiable (by norm_num)
  have cWk : ∀ k : Fin 3, ContDiff ℝ 1 (fun x => W₀ x k) := fun k => by
    have e := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp
      (hW.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
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
            (prod_le ((entry_abs_le (fderiv ℝ W₀ y) k k).trans (W1_le h y)) (curl_le u y l))
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
      have hw := hWd y
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

theorem A_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (i : Fin 3) :
    |(fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) i| ≤ 2 * D * atom u y := by
  have e1 : ‖fderiv ℝ u y (W₀ y)‖ ≤ atom u y * D :=
    ((fderiv ℝ u y).le_opNorm _).trans (mul_le_mul (le1 u y) (h.W0 y) (norm_nonneg _) (atom_nonneg u y))
  have e2 : ‖fderiv ℝ W₀ y (u y)‖ ≤ 1 * D * atom u y := by
    have h3 := decay_le h y ‖fderiv ℝ W₀ y‖ ‖u y‖ 1 zero_le_one (by rw [abs_norm, one_mul]; exact h.W1 y)
      (by rw [abs_norm])
    rw [abs_mul, abs_norm, abs_norm] at h3
    exact ((fderiv ℝ W₀ y).le_opNorm (u y)).trans h3
  refine (coord_abs_le _ i).trans ((norm_add_le _ _).trans ?_)
  linarith

theorem dA_le {u W₀ : Space → Space} {D : ℝ} (h : DecayData u W₀ D) (y : Space) (i j : Fin 3) :
    |fderiv ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) y (unitVector j) i|
      ≤ 12 * D * atom u y := by
  have h2 : ContDiff ℝ 2 u := h.hu.of_le (WithTop.coe_le_coe.mpr le_top)
  rw [A_deriv_jets u W₀ h2 h.hW y i j]
  have hN := atom_nonneg u y
  have hb : ∀ k : Fin 3, |W₀ y k * fderiv ℝ (fun x => fderiv ℝ u x) y (unitVector j) (unitVector k) i
        + fderiv ℝ W₀ y (unitVector j) k * fderiv ℝ u y (unitVector k) i
        + u y k * fderiv ℝ (fun x => fderiv ℝ W₀ x) y (unitVector j) (unitVector k) i
        + fderiv ℝ u y (unitVector j) k * fderiv ℝ W₀ y (unitVector k) i| ≤ 4 * D * atom u y := by
    intro k
    have t1 := prod_le ((coord_abs_le _ k).trans (h.W0 y)) (ddu_le u y j k i)
    have t2 := prod_le ((entry_abs_le _ j k).trans (W1_le h y)) (du_le u y k i)
    have t3 : |u y k * fderiv ℝ (fun x => fderiv ℝ W₀ x) y (unitVector j) (unitVector k) i|
        ≤ 1 * D * atom u y := by
      rw [mul_comm]
      exact decay_le h y _ _ 1 zero_le_one (by rw [one_mul]; exact (entry2_abs_le _ j k i).trans (h.W2 y))
        (coord_abs_le _ k)
    have t4 := prod_le (du_le u y j k) ((entry_abs_le _ k i).trans (W1_le h y))
    have abs4 : ∀ a b c d : ℝ, |a + b + c + d| ≤ |a| + |b| + |c| + |d| := fun a b c d => by
      have h1 := abs_add_le (a + b + c) d
      have h2 := abs_add_le (a + b) c
      have h3 := abs_add_le a b
      linarith
    refine (abs4 _ _ _ _).trans ?_
    linarith
  have := sum3_le _ _ hb
  linarith

end Stretch

open Stretch in
theorem stretch_decay (u W₀ : Space → Space) (D : ℝ) (h : DecayData u W₀ D)
    (hd : ∀ y, divergenceAt u y = 0) (hWd : ∀ y, divergenceAt W₀ y = 0) :
    ∫ y, inner ℝ (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y))
        (-secondDerivTrace (fderiv ℝ (fun x => fderiv ℝ u x) y)) =
      ∫ y, (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j
        + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l) := by
  have hu := h.hu
  have hW := h.hW
  have h2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  have hA := A_contDiff u W₀ h2 hW
  have dA : Differentiable ℝ (fun x => fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) :=
    hA.differentiable (by norm_num)
  have hAi : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) i) := by
    intro i
    have h := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hA
    exact h
  have hN0 := atom_nonneg u
  have hN := atom_sq h
  have D0 := h.D0
  have cW : Continuous W₀ := hW.continuous
  have cdW : Continuous (fun y => fderiv ℝ W₀ y) := hW.continuous_fderiv (by norm_num)
  have cddW : Continuous (fun y => fderiv ℝ (fun x => fderiv ℝ W₀ x) y) :=
    (hW.fderiv_right (m := 1) (by norm_num)).continuous_fderiv (by norm_num)
  have cO : ∀ j, Continuous (fun x => curlVec (fderiv ℝ W₀ x) j) := fun j =>
    (curl_contDiff W₀ hW (n := 1) (by norm_num) j).continuous
  have cw : ∀ l, Continuous (fun x => curlVec (fderiv ℝ u x) l) := fun l =>
    (curl_contDiff u hu (n := ∞) (by simp) l).continuous
  have cDu : ∀ j i, Continuous (fun x => fderiv ℝ u x (unitVector j) i) := fun j i =>
    (d1_smooth u hu j i).continuous
  have cU : ∀ l, Continuous (fun x => u x l) := fun l => (comp_smooth u hu l).continuous
  have cVG : ∀ j m, Continuous (fun x => vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) x) j m) := by
    intro j m
    unfold vortGrad
    fun_prop
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
    simp only [ssp_curl u h2 hd y, Fintype.sum_prod_type, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => by ring
  have hK : (0 : ℝ) ≤ 108 * D := by linarith
  have sb : ∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3, (alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u y (W₀ y) + fderiv ℝ W₀ y (u y)) t.1) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) t.2.2) y (unitVector t.2.1) =
      -∫ y, ∑ t : Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) y (unitVector t.2.1) *
          curlVec (fderiv ℝ u y) t.2.2 := by
    refine wibp_N _ (atom u) hN0 hN (fun (t : Fin 3 × Fin 3 × Fin 3) (x : Space) => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) (fun t x => curlVec (fderiv ℝ u x) t.2.2)
      (fun t => t.2.1) (108 * D) hK (fun t _ => cmul_contDiff_one _ _ (hAi _))
      (fun t _ => curl_contDiff u h2 (by norm_num) _) (fun t _ y => ?_) (fun t _ y => ?_) (fun t _ y => ?_)
    · refine kmono ((prod_le (prod_le (eps_abs_le _ _ _) (A_le h y _)) (dcurl_le u h2 y _ _)).trans
        (le_of_eq (by ring))) (by linarith : 18 * D ≤ 108 * D)
    · rw [const_mul_deriv _ _ y _ ((hAi _).differentiable (by norm_num) y), fderiv_component _ (dA y)]
      refine kmono ((prod_le (prod_le (eps_abs_le _ _ _) (dA_le h y _ _)) (curl_le u y _)).trans
        (le_of_eq (by ring))) (le_refl _)
    · rw [← abs_mul]
      refine kmono ((prod_le (prod_le (eps_abs_le _ _ _) (A_le h y _)) (curl_le u y _)).trans
        (le_of_eq (by ring))) (by linarith : 18 * D ≤ 108 * D)
  have sc : ∀ y, -(∑ t : Fin 3 × Fin 3 × Fin 3, fderiv ℝ (fun x => alternatingSymbol t.1 t.2.1 t.2.2 *
        (fderiv ℝ u x (W₀ x) + fderiv ℝ W₀ x (u x)) t.1) y (unitVector t.2.1) *
          curlVec (fderiv ℝ u y) t.2.2) =
      ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
          fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)
      + (-(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j)
      + -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j * fderiv ℝ u y (unitVector j) i *
          curlVec (fderiv ℝ u y) i) := by
    intro y
    rw [← curl_grad_point u W₀ h2 hW hd hWd y]
    simp only [const_mul_deriv _ _ y _ ((hAi _).differentiable (by norm_num) y),
      fderiv_component _ (dA y), Fintype.sum_prod_type]
  have tz := transport_decay h hWd
  have iR1 : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)) := by
    refine (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))).neg
    refine int_N (atom u) _ hN0 hN (((cw i).mul (cS i j)).mul (cw j)) (81 * D) (by linarith) (fun y => ?_)
    have hs : |(fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2| ≤ D := by
      rw [abs_div, abs_two]
      have := (entry_abs_le (fderiv ℝ W₀ y) j i).trans (W1_le h y)
      have := (entry_abs_le (fderiv ℝ W₀ y) i j).trans (W1_le h y)
      rw [div_le_iff₀ (by norm_num)]
      linarith [abs_add_le (fderiv ℝ W₀ y (unitVector j) i) (fderiv ℝ W₀ y (unitVector i) j)]
    exact (prod_le (prod_le (curl_le u y i) hs) (curl_le u y j)).trans (le_of_eq (by ring))
  have iR2 : Integrable (fun y => ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j) := by
    refine integrable_finsetSum _ (fun j _ => ?_)
    refine int_N (atom u) _ hN0 hN ((continuous_finsetSum _ (fun m _ => (cU m).mul (cVG j m))).mul (cw j))
      (243 * D) (by linarith) (fun y => ?_)
    have hs : |∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m| ≤ 3 * (9 * D * atom u y) := by
      refine sum3_le _ _ (fun m => ?_)
      rw [mul_comm]
      exact decay_le h y _ _ 9 (by norm_num) ((vortGrad_abs_le _ j m).trans (by linarith [h.W2 y]))
        (coord_abs_le _ m)
    exact (prod_le hs (curl_le u y j)).trans (le_of_eq (by ring))
  have iR : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ u y) i *
          ((fderiv ℝ W₀ y (unitVector j) i + fderiv ℝ W₀ y (unitVector i) j) / 2) * curlVec (fderiv ℝ u y) j)
        + ∑ j : Fin 3, (∑ m : Fin 3, u y m * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) *
          curlVec (fderiv ℝ u y) j) := iR1.add iR2
  have iX : Integrable (fun y => -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (fderiv ℝ W₀ y) j *
      fderiv ℝ u y (unitVector j) i * curlVec (fderiv ℝ u y) i)) := by
    refine (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ?_))).neg
    refine int_N (atom u) _ hN0 hN (((cO j).mul (cDu j i)).mul (cw i)) (81 * D) (by linarith) (fun y => ?_)
    exact (prod_le (prod_le (curlW_le' h y j) (du_le u y j i)) (curl_le u y i)).trans (le_of_eq (by ring))
  have i3 : Integrable (fun y => (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ m : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3,
          alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l) := by
    refine Integrable.const_mul (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun m _ =>
      integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun j _ => ?_))))) _
    refine int_N (atom u) _ hN0 hN (((continuous_const.mul (cVG j m)).mul (cDu j i)).mul (cU l)) (9 * D)
      (by linarith) (fun y => ?_)
    have hdec := decay_le h y (vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m) (u y l) 9 (by norm_num)
      ((vortGrad_abs_le _ j m).trans (by linarith [h.W2 y])) (coord_abs_le _ l)
    rw [abs_mul] at hdec
    have he := eps_abs_le i m l
    have hdu := du_le u y j i
    have hn := hN0 y
    calc |alternatingSymbol i m l * vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m
            * fderiv ℝ u y (unitVector j) i * u y l|
          = (|alternatingSymbol i m l| * |fderiv ℝ u y (unitVector j) i|)
            * (|vortGrad (fderiv ℝ (fun x => fderiv ℝ W₀ x) y) j m| * |u y l|) := by
          rw [abs_mul, abs_mul, abs_mul]; ring
      _ ≤ (1 * atom u y) * (9 * D * atom u y) :=
          mul_le_mul (mul_le_mul he hdu (abs_nonneg _) zero_le_one) hdec (by positivity) (by positivity)
      _ = 9 * D * (atom u y * atom u y) := by ring
  have iTs : Integrable (fun y => ∑ l : Fin 3, ∑ k : Fin 3, (W₀ y k * curlVec (fderiv ℝ u y) l) *
      fderiv ℝ (fun x => curlVec (fderiv ℝ u x) l) y (unitVector k)) := by
    refine integrable_finsetSum _ (fun l _ => integrable_finsetSum _ (fun k _ => ?_))
    refine int_N (atom u) _ hN0 hN (((cWk k).mul (cw l)).mul (cdw l k)) (81 * D) (by linarith) (fun y => ?_)
    exact (prod_le (prod_le ((coord_abs_le _ k).trans (h.W0 y)) (curl_le u y l)) (dcurl_le u h2 y l k)).trans
      (le_of_eq (by ring))
  simp_rw [sa]
  rw [sb, ← integral_neg]
  simp_rw [sc]
  rw [integral_add _ iX, integral_add _ iR, tz, x_term_decay h, integral_add _ i3]
  all_goals first
    | exact iR
    | exact iTs
    | exact iTs.add iR
    | ring

open Stretch in
theorem stretch_slice (P : ℝ) (W v : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWd : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdec : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hv : IsSmoothPerturbation P v) (σ : ℝ) (hs : SliceBounds P v σ) :
    ∫ y, inner ℝ (advectionPart W v σ y) (-secondDerivTrace (secondDerivField v σ y)) =
      ∫ y, stretchForm W v (gradField v) σ y := by
  obtain ⟨D, hD⟩ := hWdec
  have hWs : ContDiff ℝ 2 (W σ) := hW.comp (contDiff_const.prodMk contDiff_id)
  have hvs : ContDiff ℝ ∞ (v σ) := hv.smooth.comp (contDiff_const.prodMk contDiff_id)
  have b0 : ∀ y, ‖W σ y‖ ≤ D / (1 + ‖y‖) := by
    intro y
    have := hD σ y 0 (by norm_num)
    rwa [norm_iteratedFDeriv_zero, zero_add, pow_one] at this
  have D0 : 0 ≤ D := by
    have := b0 0
    rw [norm_zero, add_zero, div_one] at this
    exact (norm_nonneg _).trans this
  have b1 : ∀ y, ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) := by
    intro y
    have := hD σ y 1 (by norm_num)
    rw [norm_iteratedFDeriv_one] at this
    exact this.trans (div_le_div_of_nonneg_left D0 (by positivity)
      (le_self_pow₀ (one_le_add_norm y) (by norm_num)))
  have b2 : ∀ y, ‖fderiv ℝ (fun x => fderiv ℝ (W σ) x) y‖ ≤ D / (1 + ‖y‖) := by
    intro y
    have := hD σ y 2 (by norm_num)
    rw [show (2 : ℕ) = 1 + 1 from rfl, ← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one] at this
    exact this.trans (div_le_div_of_nonneg_left D0 (by positivity)
      (le_self_pow₀ (one_le_add_norm y) (by norm_num)))
  have hdd : DecayData (v σ) (W σ) D :=
    { hu := hvs, hW := hWs, D0 := D0,
      W0 := fun y => (b0 y).trans (div_le_self D0 (one_le_add_norm y)),
      W1 := b1, W2 := b2, i0 := hs.weighted, i1 := hs.first, i2 := hs.second }
  exact stretch_decay (v σ) (W σ) D hdd (hv.divergence_free σ) (hWd σ)

end SmoothEnergyIdentityInternal

end Coercive

end Breakdown

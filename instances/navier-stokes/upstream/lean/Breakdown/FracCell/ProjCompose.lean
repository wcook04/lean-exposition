import Breakdown.FracCell.VelocityTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

namespace ProjCompose.Internal

def pairMat (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun j t => ∫ x in Set.Icc a b, (ρ x : ℂ) * (x : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))

def mom (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) (f : ℝ → ℂ) : Fin (d + 1) → ℂ :=
  fun t => ∫ x in Set.Icc a b, (ρ x : ℂ) * f x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))

theorem conj_pow (x : ℝ) (n : ℕ) : (starRingEnd ℂ) ((x : ℂ) ^ n) = (x : ℂ) ^ n := by
  rw [map_pow, Complex.conj_ofReal]

theorem pairMat_symm (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) (j t : Fin (d + 1)) :
    pairMat ρ a b d j t = pairMat ρ a b d t j := by
  unfold pairMat
  congr 1
  funext x
  rw [conj_pow, conj_pow]
  ring

theorem pairMat_transpose (ρ : ℝ → ℝ) (a b : ℝ) (d : ℕ) : (pairMat ρ a b d).transpose = pairMat ρ a b d := by
  ext j t
  exact pairMat_symm ρ a b d t j

theorem mono_integrable {ρ : ℝ → ℝ} (hρ : Continuous ρ) (a b : ℝ) (j t : ℕ) :
    IntegrableOn (fun x : ℝ => (ρ x : ℂ) * (x : ℂ) ^ j * (starRingEnd ℂ) ((x : ℂ) ^ t)) (Set.Icc a b) := by
  have e : (fun x : ℝ => (ρ x : ℂ) * (x : ℂ) ^ j * (starRingEnd ℂ) ((x : ℂ) ^ t))
      = fun x : ℝ => (ρ x : ℂ) * (x : ℂ) ^ j * (x : ℂ) ^ t := by
    funext x
    rw [conj_pow]
  rw [e]
  exact (by fun_prop : Continuous fun x : ℝ => (ρ x : ℂ) * (x : ℂ) ^ j * (x : ℂ) ^ t).integrableOn_Icc

theorem normal_eq {ρ : ℝ → ℝ} (hρ : Continuous ρ) {a b : ℝ} {d : ℕ} {f : ℝ → ℂ}
    (hf : ∀ t : Fin (d + 1),
      IntegrableOn (fun x => (ρ x : ℂ) * f x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) (Set.Icc a b))
    (c : Fin (d + 1) → ℂ) (t : Fin (d + 1)) :
    ∫ x in Set.Icc a b, (ρ x : ℂ) * (f x - ∑ j, c j * (x : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))
      = mom ρ a b d f t - (pairMat ρ a b d).mulVec c t := by
  have e : ∀ x : ℝ, (ρ x : ℂ) * (f x - ∑ j, c j * (x : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))
      = (ρ x : ℂ) * f x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))
        - ∑ j, c j * ((ρ x : ℂ) * (x : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) := by
    intro x
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by ring)
  simp_rw [e]
  have hi : ∀ j ∈ (Finset.univ : Finset (Fin (d + 1))), IntegrableOn
      (fun x : ℝ => c j * ((ρ x : ℂ) * (x : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)))) (Set.Icc a b) :=
    fun j _ => (mono_integrable hρ a b j t).const_mul (c j)
  rw [integral_sub (hf t) (integrable_finsetSum _ hi), integral_finsetSum _ hi]
  simp_rw [integral_const_mul]
  unfold mom Matrix.mulVec dotProduct
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  show _ = pairMat ρ a b d t j * c j
  rw [pairMat_symm ρ a b d t j]
  unfold pairMat
  ring

theorem poly_zero_of_vanish {d : ℕ} (c : Fin (d + 1) → ℂ) {s : Set ℝ} (hs : s.Infinite)
    (h : ∀ x ∈ s, ∑ j, c j * (x : ℂ) ^ (j : ℕ) = 0) : c = 0 := by
  set p : Polynomial ℂ := ∑ j : Fin (d + 1), Polynomial.C (c j) * Polynomial.X ^ (j : ℕ) with hp
  have heval : ∀ x : ℂ, p.eval x = ∑ j, c j * x ^ (j : ℕ) := by
    intro x
    simp [hp, Polynomial.eval_finsetSum]
  have hp0 : p = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.Infinite.mono (s := (fun x : ℝ => (x : ℂ)) '' s)
    · rintro _ ⟨x, hx, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, heval]
      exact h x hx
    · exact Set.Infinite.image (fun x _ y _ hxy => Complex.ofReal_injective hxy) hs
  funext j
  have hc : p.coeff (j : ℕ) = c j := by
    simp only [hp, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hij
      rw [if_neg]
      exact fun h => hij (Fin.ext h).symm
    · simp
  rw [← hc, hp0]
  simp

theorem vanish_of_integral_zero {g : ℝ → ℝ} (hg : Continuous g) {a b : ℝ}
    (hg0 : ∀ x ∈ Set.Icc a b, 0 ≤ g x) (hint : ∫ x in Set.Icc a b, g x = 0) :
    ∀ x ∈ Set.Ioo a b, g x = 0 := by
  intro x hx
  by_contra hne
  have hpos : 0 < ∫ x in Set.Icc a b, g x := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsub : Function.support g ∩ Set.Ioo a b ⊆ Function.support g ∩ Set.Icc a b :=
        Set.inter_subset_inter_right _ Set.Ioo_subset_Icc_self
      refine lt_of_lt_of_le ?_ (measure_mono hsub)
      exact (hg.isOpen_support.inter isOpen_Ioo).measure_pos volume ⟨x, hne, hx⟩
    · exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ hg0)
    · exact hg.integrableOn_Icc
  linarith

theorem pairMat_inj {ρ : ℝ → ℝ} (hρ : Continuous ρ) {a b : ℝ} (hab : a < b)
    (hρ0 : ∀ x ∈ Set.Icc a b, 0 ≤ ρ x) (hρp : ∀ x ∈ Set.Ioo a b, 0 < ρ x) (d : ℕ) :
    Function.Injective (pairMat ρ a b d).mulVec := by
  intro c c' hcc
  have hsub : (pairMat ρ a b d).mulVec (c - c') = 0 := by rw [Matrix.mulVec_sub, hcc, sub_self]
  suffices h0 : c - c' = 0 from sub_eq_zero.1 h0
  set e := c - c' with he
  set P : ℝ → ℂ := fun x => ∑ j, e j * (x : ℂ) ^ (j : ℕ) with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hPi : ∀ t : Fin (d + 1),
      IntegrableOn (fun x => (ρ x : ℂ) * P x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) (Set.Icc a b) := by
    intro t
    refine Continuous.integrableOn_Icc ?_
    have : Continuous fun x : ℝ => (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)) :=
      Complex.continuous_conj.comp (by fun_prop)
    exact ((Complex.continuous_ofReal.comp hρ).mul hPc).mul this
  have hmom : ∀ t, mom ρ a b d P t = 0 := by
    intro t
    have h1 := normal_eq hρ hPi e t
    have h2 : (fun x : ℝ => (ρ x : ℂ) * (P x - ∑ j, e j * (x : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) = fun _ => 0 := by
      funext x
      simp [hP]
    rw [h2, integral_zero, hsub] at h1
    simpa using h1.symm
  have hq : ∫ x in Set.Icc a b, (ρ x : ℂ) * P x * (starRingEnd ℂ) (P x) = 0 := by
    have e2 : ∀ x : ℝ, (ρ x : ℂ) * P x * (starRingEnd ℂ) (P x)
        = ∑ t, (starRingEnd ℂ) (e t) * ((ρ x : ℂ) * P x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) := by
      intro x
      have hcP : (starRingEnd ℂ) (P x)
          = ∑ t, (starRingEnd ℂ) (e t) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)) := by
        simp only [hP, map_sum, map_mul]
      rw [hcP, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun t _ => by ring)
    simp_rw [e2]
    rw [integral_finsetSum _ (fun t _ => (hPi t).const_mul _)]
    simp_rw [integral_const_mul]
    refine Finset.sum_eq_zero (fun t _ => ?_)
    have := hmom t
    unfold mom at this
    rw [this, mul_zero]
  have hreal : ∫ x in Set.Icc a b, ρ x * Complex.normSq (P x) = 0 := by
    have e3 : ∀ x : ℝ, (ρ x : ℂ) * P x * (starRingEnd ℂ) (P x) = ((ρ x * Complex.normSq (P x) : ℝ) : ℂ) := by
      intro x
      rw [mul_assoc, Complex.mul_conj]
      push_cast
      ring
    simp_rw [e3] at hq
    rw [integral_complex_ofReal] at hq
    exact_mod_cast hq
  have hv := vanish_of_integral_zero (hρ.mul (Complex.continuous_normSq.comp hPc))
    (fun x hx => mul_nonneg (hρ0 x hx) (Complex.normSq_nonneg _)) hreal
  apply poly_zero_of_vanish e (Set.Ioo_infinite hab)
  intro x hx
  have h1 := hv x hx
  have h2 : Complex.normSq (P x) = 0 := by
    rcases mul_eq_zero.1 h1 with h | h
    · exact absurd h (ne_of_gt (hρp x hx))
    · exact h
  exact Complex.normSq_eq_zero.1 h2

theorem lineProj_eq {ρ : ℝ → ℝ} (hρ : Continuous ρ) {a b : ℝ} {d : ℕ}
    (hinj : Function.Injective (pairMat ρ a b d).mulVec) {f : ℝ → ℂ}
    (hf : ∀ t : Fin (d + 1),
      IntegrableOn (fun x => (ρ x : ℂ) * f x * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) (Set.Icc a b))
    (x : ℝ) :
    lineProj ρ a b d f x = ∑ j, ((pairMat ρ a b d)⁻¹.mulVec (mom ρ a b d f)) j * (x : ℂ) ^ (j : ℕ) := by
  have hu : IsUnit (pairMat ρ a b d) := Matrix.mulVec_injective_iff_isUnit.1 hinj
  have hdet : IsUnit (pairMat ρ a b d).det := (Matrix.isUnit_iff_isUnit_det _).1 hu
  have hsol : (pairMat ρ a b d).mulVec ((pairMat ρ a b d)⁻¹.mulVec (mom ρ a b d f)) = mom ρ a b d f := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have hex : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1),
      ∫ r in Set.Icc a b, (ρ r : ℂ) * (f r - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0 :=
    ⟨_, fun t => by rw [normal_eq hρ hf, hsol, sub_self]⟩
  unfold lineProj
  rw [dif_pos hex]
  have hc : hex.choose = (pairMat ρ a b d)⁻¹.mulVec (mom ρ a b d f) := by
    apply hinj
    rw [hsol]
    funext t
    have h := hex.choose_spec t
    rw [normal_eq hρ hf] at h
    exact (sub_eq_zero.1 h).symm
  rw [hc]

theorem lw_cont (K : CellBox) : Continuous K.lineWeight := by
  by_cases h : K.r₁ = 0
  · have e : K.lineWeight = fun r => r := funext fun r => by simp [CellBox.lineWeight, h]
    rw [e]
    exact continuous_id
  · have e : K.lineWeight = fun _ => 1 := funext fun r => by simp [CellBox.lineWeight, h]
    rw [e]
    exact continuous_const

theorem lw_nonneg (K : CellBox) {x : ℝ} (hx : x ∈ Set.Icc K.r₁ K.r₂) :
    0 ≤ K.lineWeight x := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hx.1]
  · norm_num

theorem lw_pos (K : CellBox) {x : ℝ} (hx : x ∈ Set.Ioo K.r₁ K.r₂) :
    0 < K.lineWeight x := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hx.1]
  · norm_num

theorem rect_measure (K : CellBox) : volume.restrict K.rect
    = (volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]
  rfl

theorem mono_cont (t k : ℕ) : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) ^ t * (p.2 : ℂ) ^ k := by
  fun_prop

theorem poly_cont {d : ℕ} (c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    Continuous fun p : ℝ × ℝ => ∑ j, ∑ l, c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) := by
  fun_prop

theorem cross_int (K : CellBox) {F : ℝ × ℝ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    {T : ℝ × ℝ → ℂ} (hT : Continuous T) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) (T p)) K.rect := by
  have hw := lw_cont K
  have hTi : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖T p‖ ^ 2) K.rect :=
    ((hw.comp continuous_fst).mul (hT.norm.pow 2)).continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)
  refine Integrable.mono' (hFi.add hTi) ?_ ?_
  · exact (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).aestronglyMeasurable).mul hFm).mul
      (Complex.continuous_conj.comp hT).aestronglyMeasurable
  · refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)).2 (ae_of_all _ (fun p hp => ?_))
    have h0 : 0 ≤ K.lineWeight p.1 := lw_nonneg K hp.1
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
    nlinarith [sq_nonneg (‖F p‖ - ‖T p‖), norm_nonneg (F p), norm_nonneg (T p),
      mul_nonneg h0 (sq_nonneg (‖F p‖ - ‖T p‖))]

theorem sub_int (K : CellBox) {F : ℝ × ℝ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    {P T : ℝ × ℝ → ℂ} (hP : Continuous P) (hT : Continuous T) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (F p - P p) * (starRingEnd ℂ) (T p)) K.rect := by
  have hw := lw_cont K
  have h2 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * P p * (starRingEnd ℂ) (T p)) K.rect :=
    (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).mul hP).mul
      (Complex.continuous_conj.comp hT)).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  refine ((cross_int K hFm hFi hT).sub h2).congr (ae_of_all _ (fun p => ?_))
  simp only [Pi.sub_apply]
  ring

theorem prod_mono (K : CellBox) (j l t k : ℕ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * ((p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l)
        * (starRingEnd ℂ) ((p.1 : ℂ) ^ t * (p.2 : ℂ) ^ k)
      = (∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * (x : ℂ) ^ j * (starRingEnd ℂ) ((x : ℂ) ^ t))
        * ∫ y in Set.Icc K.z₁ K.z₂, (((fun _ : ℝ => (1 : ℝ)) y : ℝ) : ℂ) * (y : ℂ) ^ l
          * (starRingEnd ℂ) ((y : ℂ) ^ k) := by
  rw [rect_measure, ← integral_prod_mul]
  congr 1
  funext p
  simp only [map_mul, Complex.ofReal_one]
  ring

theorem pair_poly (K : CellBox) {d : ℕ} {F : ℝ × ℝ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    (c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) (t k : Fin (d + 1)) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ)
        * (F p - ∑ j, ∑ l, c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
        * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ))
      = (∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p
          * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)))
        - (pairMat K.lineWeight K.r₁ K.r₂ d * c * pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d) t k := by
  have hw := lw_cont K
  have hm : ∀ j l : Fin (d + 1), IntegrableOn (fun p : ℝ × ℝ => c j l * ((K.lineWeight p.1 : ℂ)
      * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)))) K.rect := by
    intro j l
    refine (Continuous.continuousOn ?_).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    exact continuous_const.mul (((Complex.continuous_ofReal.comp (hw.comp continuous_fst)).mul
      (mono_cont j l)).mul (Complex.continuous_conj.comp (mono_cont t k)))
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ)
      * (F p - ∑ j, ∑ l, c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ))
      = (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ))
        - ∑ j, ∑ l, c j l * ((K.lineWeight p.1 : ℂ) * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
          * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ))) := by
    intro p
    rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  simp_rw [e]
  rw [integral_sub (cross_int K hFm hFi (mono_cont t k))
      (integrable_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hm j l))),
    integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun l _ => hm j l))]
  congr 1
  have hL : ∀ j : Fin (d + 1), ∫ p in K.rect, ∑ l, c j l * ((K.lineWeight p.1 : ℂ)
      * ((p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)))
      = ∑ l, c j l * (pairMat K.lineWeight K.r₁ K.r₂ d j t * pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d l k) := by
    intro j
    rw [integral_finsetSum _ (fun l _ => hm j l)]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [integral_const_mul, prod_mono]
    rfl
  rw [Finset.sum_congr rfl (fun j _ => hL j)]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by
    rw [pairMat_symm K.lineWeight K.r₁ K.r₂ d t j]
    ring)

theorem mono_mem {d : ℕ} (t k : Fin (d + 1)) :
    (fun p : ℝ × ℝ => (p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)) ∈ polyFn d d := by
  refine ⟨fun j l => if j = t then (if l = k then 1 else 0) else 0, fun p => ?_⟩
  simp [ite_mul, Finset.sum_ite_eq']

theorem orth_poly (K : CellBox) {d : ℕ} {F : ℝ × ℝ → ℂ}
    (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    {P : ℝ × ℝ → ℂ} (hP : Continuous P)
    (h : ∀ t k : Fin (d + 1), ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * (F p - P p)
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)) = 0)
    (T : ℝ × ℝ → ℂ) (hT : T ∈ polyFn d d) : K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 := by
  obtain ⟨τ, hτ⟩ := hT
  simp only [CellBox.pairOn, CellBox.lineWeightFn]
  have e : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * (F p - P p) * (starRingEnd ℂ) (T p)
      = ∑ t, ∑ k, (starRingEnd ℂ) (τ t k) * ((K.lineWeight p.1 : ℂ) * (F p - P p)
        * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ))) := by
    intro p
    rw [hτ p]
    simp only [map_sum, map_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun k _ => by ring))
  simp_rw [e]
  have hi : ∀ t k : Fin (d + 1), IntegrableOn (fun p => (starRingEnd ℂ) (τ t k)
      * ((K.lineWeight p.1 : ℂ) * (F p - P p)
        * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)))) K.rect :=
    fun t k => (sub_int K hFm hFi hP (mono_cont t k)).const_mul _
  rw [integral_finsetSum _ (fun t _ => integrable_finsetSum _ (fun k _ => hi t k))]
  refine Finset.sum_eq_zero (fun t _ => ?_)
  rw [integral_finsetSum _ (fun k _ => hi t k)]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [integral_const_mul, h t k, mul_zero]

theorem cancel_two {n : ℕ} {G H X Y : Matrix (Fin n) (Fin n) ℂ} (hG : IsUnit G.det) (hH : IsUnit H.det)
    (h : G * X * H = G * Y * H) : X = Y := by
  have e : ∀ Z : Matrix (Fin n) (Fin n) ℂ, Z = G⁻¹ * (G * Z * H) * H⁻¹ := by
    intro Z
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hG, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hH, Matrix.mul_one]
  calc X = G⁻¹ * (G * X * H) * H⁻¹ := e X
    _ = G⁻¹ * (G * Y * H) * H⁻¹ := by rw [h]
    _ = Y := (e Y).symm

theorem coef_identity {n : ℕ} (A N : Matrix (Fin n) (Fin n) ℂ) (R Z : Fin n → ℂ) :
    ∑ l, (A.mulVec (Matrix.vecMul R N)) l * Z l = ∑ j, ∑ l, (N * A.transpose) j l * R j * Z l := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.mul_apply, Matrix.transpose_apply,
    Finset.sum_mul, Finset.mul_sum]
  exact Eq.symm (Finset.sum_comm.trans (Finset.sum_congr rfl fun l _ => Finset.sum_comm.trans
    (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring)))

theorem dot_swap {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (b R : Fin n → ℂ) :
    ∑ j, (A.mulVec b) j * R j = ∑ t, (Matrix.vecMul R A) t * b t := by
  simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm.trans (Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun j _ => by ring)

def bvec (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) (y : ℝ) : Fin (d + 1) → ℂ :=
  mom K.lineWeight K.r₁ K.r₂ d (fun x => F (x, y))

def bmat (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun t k => ∫ y in Set.Icc K.z₁ K.z₂, bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))

def coefM (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹ * bmat K d F * ((pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d)⁻¹).transpose

end ProjCompose.Internal

open ProjCompose.Internal in
theorem projCompose : ProjComposeStatement := by
  intro K hK d F hFm hFi r z
  have hw := lw_cont K
  have hinjG : Function.Injective (pairMat K.lineWeight K.r₁ K.r₂ d).mulVec :=
    pairMat_inj hw hK.r_order.2 (fun x hx => lw_nonneg K hx) (fun x hx => lw_pos K hx) d
  have hinjH : Function.Injective (pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d).mulVec :=
    pairMat_inj continuous_const hK.z_order.2 (fun _ _ => zero_le_one) (fun _ _ => zero_lt_one) d
  have hdG : IsUnit (pairMat K.lineWeight K.r₁ K.r₂ d).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hinjG)
  have hdH : IsUnit (pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d).det :=
    (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.mulVec_injective_iff_isUnit.1 hinjH)
  have hΨ : ∀ t k : Fin (d + 1), Integrable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)))
      ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
    intro t k
    rw [← rect_measure]
    exact cross_int K hFm hFi (mono_cont t k)
  have hinner : ∀ (t k : Fin (d + 1)) (y : ℝ), ∫ x in Set.Icc K.r₁ K.r₂, (K.lineWeight x : ℂ) * F (x, y)
      * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ) * (y : ℂ) ^ (k : ℕ))
      = bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ)) := by
    intro t k y
    unfold bvec mom
    rw [← integral_mul_const]
    congr 1
    funext x
    simp only [map_mul]
    ring
  have hBrect : ∀ t k : Fin (d + 1), bmat K d F t k = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)) := by
    intro t k
    rw [rect_measure, integral_prod_symm _ (hΨ t k)]
    show ∫ y in Set.Icc K.z₁ K.z₂, bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ)) = _
    congr 1
    funext y
    exact (hinner t k y).symm
  have hbint : ∀ t k : Fin (d + 1), IntegrableOn
      (fun y => bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))) (Set.Icc K.z₁ K.z₂) := by
    intro t k
    exact ((hΨ t k).integral_prod_right).congr (ae_of_all _ (fun y => hinner t k y))
  have hgood : ∀ᵐ y ∂(volume.restrict (Set.Icc K.z₁ K.z₂)), ∀ t : Fin (d + 1),
      IntegrableOn (fun x => (K.lineWeight x : ℂ) * F (x, y) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ)))
        (Set.Icc K.r₁ K.r₂) := by
    rw [Filter.eventually_all]
    intro t
    have h : Integrable (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ)))
        ((volume.restrict (Set.Icc K.r₁ K.r₂)).prod (volume.restrict (Set.Icc K.z₁ K.z₂))) := by
      rw [← rect_measure]
      exact cross_int K hFm hFi (by fun_prop : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) ^ (t : ℕ))
    exact h.prod_left_ae
  have hR : ∀ y, (∀ t : Fin (d + 1), IntegrableOn
      (fun x => (K.lineWeight x : ℂ) * F (x, y) * (starRingEnd ℂ) ((x : ℂ) ^ (t : ℕ))) (Set.Icc K.r₁ K.r₂)) →
      K.projR d F (r, y) = ∑ t, (Matrix.vecMul (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ))
        (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹) t * bvec K d F y t := by
    intro y hy
    change lineProj K.lineWeight K.r₁ K.r₂ d (fun x => F (x, y)) r = _
    rw [lineProj_eq hw hinjG hy r]
    exact dot_swap _ _ (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ))
  have hae : (fun y => K.projR d F (r, y)) =ᵐ[volume.restrict (Set.Icc K.z₁ K.z₂)]
      (fun y => ∑ t, (Matrix.vecMul (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ))
        (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹) t * bvec K d F y t) := by
    filter_upwards [hgood] with y hy
    exact hR y hy
  have he : ∀ k : Fin (d + 1), (fun y => (((fun _ : ℝ => (1 : ℝ)) y : ℝ) : ℂ) * K.projR d F (r, y)
      * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))) =ᵐ[volume.restrict (Set.Icc K.z₁ K.z₂)]
      fun y => ∑ t, (Matrix.vecMul (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ)) (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹) t
        * (bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))) := by
    intro k
    filter_upwards [hae] with y hy
    simp only [hy, Complex.ofReal_one, one_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun t _ => by ring)
  have hsumi : ∀ k : Fin (d + 1), IntegrableOn (fun y => ∑ t, (Matrix.vecMul (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ))
      (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹) t * (bvec K d F y t * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))))
      (Set.Icc K.z₁ K.z₂) :=
    fun k => integrable_finsetSum _ (fun t _ => (hbint t k).const_mul _)
  have hzint : ∀ k : Fin (d + 1), IntegrableOn (fun y => (((fun _ : ℝ => (1 : ℝ)) y : ℝ) : ℂ)
      * K.projR d F (r, y) * (starRingEnd ℂ) ((y : ℂ) ^ (k : ℕ))) (Set.Icc K.z₁ K.z₂) :=
    fun k => (hsumi k).congr (he k).symm
  have hmomz : mom (fun _ => (1 : ℝ)) K.z₁ K.z₂ d (fun y => K.projR d F (r, y))
      = Matrix.vecMul (Matrix.vecMul (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ)) (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹)
        (bmat K d F) := by
    funext k
    show ∫ y in Set.Icc K.z₁ K.z₂, _ = _
    rw [integral_congr_ae (he k), integral_finsetSum _ (fun t _ => (hbint t k).const_mul _)]
    simp only [integral_const_mul]
    rfl
  have hL : lineProj (fun _ => (1 : ℝ)) K.z₁ K.z₂ d (fun y => K.projR d F (r, y)) z
      = ∑ j, ∑ l, coefM K d F j l * (r : ℂ) ^ (j : ℕ) * (z : ℂ) ^ (l : ℕ) := by
    rw [lineProj_eq continuous_const hinjH hzint z, hmomz, Matrix.vecMul_vecMul]
    exact coef_identity _ _ (fun j : Fin (d + 1) => (r : ℂ) ^ (j : ℕ)) (fun l : Fin (d + 1) => (z : ℂ) ^ (l : ℕ))
  have hMsol : pairMat K.lineWeight K.r₁ K.r₂ d * coefM K d F * pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d
      = bmat K d F := by
    unfold coefM
    rw [Matrix.transpose_nonsing_inv, pairMat_transpose]
    calc _ = (pairMat K.lineWeight K.r₁ K.r₂ d * (pairMat K.lineWeight K.r₁ K.r₂ d)⁻¹) * bmat K d F
          * ((pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d)⁻¹ * pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d) := by
          simp only [Matrix.mul_assoc]
      _ = bmat K d F := by
          rw [Matrix.mul_nonsing_inv _ hdG, Matrix.nonsing_inv_mul _ hdH, Matrix.one_mul, Matrix.mul_one]
  have hpairM : ∀ t k : Fin (d + 1), ∫ p in K.rect, (K.lineWeight p.1 : ℂ)
      * (F p - ∑ j, ∑ l, coefM K d F j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ))
      * (starRingEnd ℂ) ((p.1 : ℂ) ^ (t : ℕ) * (p.2 : ℂ) ^ (k : ℕ)) = 0 := by
    intro t k
    rw [pair_poly K hFm hFi (coefM K d F) t k, hMsol, ← hBrect, sub_self]
  have hex : ∃ P ∈ polyFn d d, ∀ T ∈ polyFn d d,
      K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 :=
    ⟨fun p => ∑ j, ∑ l, coefM K d F j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ), ⟨coefM K d F, fun p => rfl⟩,
      orth_poly K hFm hFi (poly_cont (coefM K d F)) hpairM⟩
  have hproj : K.proj d d F = fun p => ∑ j, ∑ l, coefM K d F j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) := by
    unfold CellBox.proj
    rw [dif_pos hex]
    have hc' : ∃ c : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ, ∀ p : ℝ × ℝ,
        hex.choose p = ∑ j, ∑ l, c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) := hex.choose_spec.1
    obtain ⟨c, hc⟩ := hc'
    have horth := hex.choose_spec.2
    have hch : hex.choose = fun p => ∑ j, ∑ l, c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) := funext hc
    have hcs : pairMat K.lineWeight K.r₁ K.r₂ d * c * pairMat (fun _ => (1 : ℝ)) K.z₁ K.z₂ d = bmat K d F := by
      ext t k
      have h1 := horth _ (mono_mem t k)
      rw [hch] at h1
      simp only [CellBox.pairOn, CellBox.lineWeightFn] at h1
      rw [pair_poly K hFm hFi c t k, ← hBrect] at h1
      exact (sub_eq_zero.1 h1).symm
    have hcoef : c = coefM K d F := cancel_two hdG hdH (hcs.trans hMsol.symm)
    rw [hch, hcoef]
  rw [hL, hproj]

end CellAnalysis

end CellCert

end Breakdown

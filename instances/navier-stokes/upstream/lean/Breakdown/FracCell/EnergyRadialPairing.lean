import Breakdown.FracCell.EnergyRadialForm

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy.RadialForm

open CellAnalysis CellFormula

theorem poly_indep (s : Set ℝ) (hs : s.Infinite) {n : ℕ} (a : Fin n → ℂ)
    (h : ∀ r ∈ s, ∑ j, a j * (r : ℂ) ^ (j : ℕ) = 0) : a = 0 := by
  set p : Polynomial ℂ := ∑ j : Fin n, Polynomial.C (a j) * Polynomial.X ^ (j : ℕ) with hp
  have hev : ∀ x : ℂ, p.eval x = ∑ j : Fin n, a j * x ^ (j : ℕ) := by
    intro x
    simp [hp, Polynomial.eval_finsetSum]
  have hroots : Set.Infinite {x | Polynomial.IsRoot p x} := by
    apply Set.Infinite.mono (s := (fun r : ℝ => (r : ℂ)) '' s)
    · rintro x ⟨r, hr, rfl⟩
      simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, hev]
      exact h r hr
    · exact hs.image (fun x _ y _ hxy => Complex.ofReal_injective hxy)
  have hp0 := Polynomial.eq_zero_of_infinite_isRoot p hroots
  funext i
  have hc : p.coeff i = a i := by
    rw [hp, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [if_neg]
      intro he
      exact hj (Fin.ext he.symm)
    · simp
  rw [← hc, hp0]
  simp

theorem monomial_indep {a b c d : ℝ} (hab : a < b) (hcd : c < d) {J L : ℕ} (coef : Fin J → Fin L → ℂ)
    (h : ∀ r ∈ Set.Ioo a b, ∀ z ∈ Set.Ioo c d,
      ∑ j, ∑ l, coef j l * (r : ℂ) ^ (j : ℕ) * (z : ℂ) ^ (l : ℕ) = 0) : coef = 0 := by
  have hinf : ∀ {x y : ℝ}, x < y → (Set.Ioo x y).Infinite := fun hxy => Set.Ioo_infinite hxy
  have step : ∀ z ∈ Set.Ioo c d, ∀ j, ∑ l, coef j l * (z : ℂ) ^ (l : ℕ) = 0 := by
    intro z hz
    have := poly_indep (Set.Ioo a b) (hinf hab) (fun j => ∑ l, coef j l * (z : ℂ) ^ (l : ℕ)) (by
      intro r hr
      rw [← h r hr z hz]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      ring)
    intro j
    exact congrFun this j
  funext j
  exact poly_indep (Set.Ioo c d) (hinf hcd) (coef j) (fun z hz => step z hz j)

section PairingMatrix

variable {ι : Type} [Fintype ι]

theorem pairing_selfAdj (K : CellBox) (m : ℝ × ℝ → ℝ) (P : ι → ℝ × ℝ → ℝ) :
    (testInnerMatrix K m P).IsHermitian := by
  ext i i'
  simp only [Matrix.conjTranspose_apply, testInnerMatrix, RCLike.star_def, Complex.conj_ofReal]
  unfold rectIntegral
  congr 2
  funext p
  ring

theorem pairing_value (K : CellBox) (m : ℝ × ℝ → ℝ) (P : ι → ℝ × ℝ → ℝ)
    (hint : ∀ i i', IntegrableOn (fun p => m p * P i p * P i' p) K.rect) (c : ι → ℂ) :
    (star c ⬝ᵥ (testInnerMatrix K m P *ᵥ c)).re =
      ∫ p in K.rect, m p * ‖∑ i, c i * (P i p : ℂ)‖ ^ 2 := by
  have hpt : ∀ p, m p * ‖∑ i, c i * (P i p : ℂ)‖ ^ 2 =
      ∑ i, ∑ i', ((starRingEnd ℂ) (c i) * c i').re * (m p * P i p * P i' p) := by
    intro p
    rw [← Complex.normSq_eq_norm_sq, ← Complex.ofReal_re (Complex.normSq _), Complex.normSq_eq_conj_mul_self]
    simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun i' _ => (hint i i').const_mul _))]
  simp_rw [integral_finsetSum _ (fun i' _ => (hint _ i').const_mul _), integral_const_mul]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  simp only [testInnerMatrix, rectIntegral]
  have : (starRingEnd ℂ) (c i) * (((∫ p in K.rect, m p * P i p * P i' p : ℝ)) * c i') =
      ((starRingEnd ℂ) (c i) * c i') * ((∫ p in K.rect, m p * P i p * P i' p : ℝ) : ℂ) := by ring
  rw [this, Complex.re_mul_ofReal]

theorem pairing_pos (K : CellBox) (m : ℝ × ℝ → ℝ) (P : ι → ℝ × ℝ → ℝ)
    (hm : Continuous m) (hP : ∀ i, Continuous (P i)) (hm0 : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmpos : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, 0 < m p)
    (hind : ∀ c : ι → ℂ, (∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, ∑ i, c i * (P i p : ℂ) = 0) → c = 0)
    (c : ι → ℂ) (hc : c ≠ 0) : 0 < (star c ⬝ᵥ (testInnerMatrix K m P *ᵥ c)).re := by
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hint : ∀ i i', IntegrableOn (fun p => m p * P i p * P i' p) K.rect := fun i i' =>
    ((hm.mul (hP i)).mul (hP i')).continuousOn.integrableOn_compact hcomp
  rw [pairing_value K m P hint c]
  set g : ℝ × ℝ → ℝ := fun p => m p * ‖∑ i, c i * (P i p : ℂ)‖ ^ 2 with hg
  have hgc : Continuous g := hm.mul ((continuous_finsetSum _ fun i _ =>
    continuous_const.mul (Complex.continuous_ofReal.comp (hP i))).norm.pow 2)
  obtain ⟨p₀, hp₀, hne⟩ : ∃ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, ∑ i, c i * (P i p : ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hc (hind c hcon)
  have hg0 : 0 < g p₀ := mul_pos (hmpos p₀ hp₀) (pow_pos (norm_pos_iff.mpr hne) 2)
  rw [setIntegral_pos_iff_support_of_nonneg_ae]
  · have hopen : IsOpen ({p | 0 < g p} ∩ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) :=
      (isOpen_lt continuous_const hgc).inter (isOpen_Ioo.prod isOpen_Ioo)
    have hpos := hopen.measure_pos volume ⟨p₀, hg0, hp₀⟩
    refine lt_of_lt_of_le hpos (measure_mono ?_)
    rintro p ⟨h1, h2⟩
    exact ⟨(show 0 < g p from h1).ne', Set.Ioo_subset_Icc_self h2.1, Set.Ioo_subset_Icc_self h2.2⟩
  · have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
    rw [Filter.EventuallyLE, ae_restrict_iff' hmeas]
    exact Filter.Eventually.of_forall fun p hp => mul_nonneg (hm0 p hp) (sq_nonneg _)
  · exact hgc.continuousOn.integrableOn_compact hcomp

theorem pairing_unit [DecidableEq ι] (G : Matrix ι ι ℂ) (hpos : ∀ c : ι → ℂ, c ≠ 0 → 0 < (star c ⬝ᵥ (G *ᵥ c)).re) :
    IsUnit G.det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  intro x y hxy
  by_contra hne
  have h := hpos (x - y) (sub_ne_zero.mpr hne)
  rw [Matrix.mulVec_sub, hxy, sub_self, dotProduct_zero] at h
  simp at h

end PairingMatrix

end Breakdown.CellCert.CellEnergy.RadialForm

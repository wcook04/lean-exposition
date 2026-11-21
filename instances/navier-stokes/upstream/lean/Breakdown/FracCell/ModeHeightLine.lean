import Breakdown.FracCell.VelocityTailSt
import Breakdown.FracCell.StHeightModeIbp

open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

namespace Internal.ModeHeightLine

def moments (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) (z : ℝ) : Fin (d + 1) → ℂ :=
  fun t => ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * F (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))

def momentMatrix (K : CellBox) (d : ℕ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ :=
  fun t j => ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))

theorem weight_cont (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs <;> fun_prop

theorem weight_nonneg (K : CellBox) (hK : IsCellBox K) {r : ℝ} (hr : r ∈ Icc K.r₁ K.r₂) :
    0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · exact le_trans hK.r_order.1 hr.1
  · exact zero_le_one

theorem weight_pos (K : CellBox) (hK : IsCellBox K) {r : ℝ} (hr : r ∈ Ioo K.r₁ K.r₂) :
    0 < K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs
  · exact lt_of_le_of_lt hK.r_order.1 hr.1
  · exact zero_lt_one

theorem weight_le (K : CellBox) (hK : IsCellBox K) {r : ℝ} (hr : r ∈ Icc K.r₁ K.r₂) :
    K.lineWeight r ≤ K.r₂ + 1 := by
  unfold CellBox.lineWeight
  split_ifs
  · linarith [hr.2]
  · linarith [hK.r_order.1, hK.r_order.2]

theorem poly_zero (s : Set ℝ) (hs : s.Infinite) {n : ℕ} (a : Fin n → ℂ)
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

theorem cond_iff (K : CellBox) (d : ℕ) (F : ℝ × ℝ → ℂ) (z : ℝ)
    (hs : IntegrableOn (fun r => (K.lineWeight r : ℂ) * F (r, z)) (Icc K.r₁ K.r₂)) (c : Fin (d + 1) → ℂ) :
    (∀ t : Fin (d + 1), ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (F (r, z) - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0)
      ↔ momentMatrix K d *ᵥ c = moments K d F z := by
  have key : ∀ t : Fin (d + 1), ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * (F (r, z) - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = moments K d F z t - (momentMatrix K d *ᵥ c) t := by
    intro t
    have e : ∀ r : ℝ, (K.lineWeight r : ℂ) * (F (r, z) - ∑ j, c j * (r : ℂ) ^ (j : ℕ))
        * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = (K.lineWeight r : ℂ) * F (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))
          - ∑ j, c j * ((K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) := by
      intro r
      simp only [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    simp_rw [e]
    have hw : Continuous (fun r : ℝ => (K.lineWeight r : ℂ)) := Complex.continuous_ofReal.comp (weight_cont K)
    rw [integral_sub]
    · rw [integral_finsetSum]
      · simp only [integral_const_mul, moments, momentMatrix, Matrix.mulVec, dotProduct]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      · intro j _
        refine Integrable.const_mul ?_ _
        exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    · exact hs.mul_continuousOn (by fun_prop) isCompact_Icc
    · refine integrable_finsetSum _ fun j _ => ?_
      refine Integrable.const_mul ?_ _
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  constructor
  · intro h
    funext t
    have := (key t).symm.trans (h t)
    exact (sub_eq_zero.mp this).symm
  · intro h t
    rw [key t, h, sub_self]

theorem momentMatrix_inj (K : CellBox) (hK : IsCellBox K) (d : ℕ) : Function.Injective (momentMatrix K d).mulVec := by
  intro x y hxy
  set c := x - y with hc
  have hMc : momentMatrix K d *ᵥ c = 0 := by rw [hc, Matrix.mulVec_sub, hxy, sub_self]
  have hw : Continuous (fun r : ℝ => (K.lineWeight r : ℂ)) := Complex.continuous_ofReal.comp (weight_cont K)
  set P : ℝ → ℂ := fun r => ∑ j : Fin (d + 1), c j * (r : ℂ) ^ (j : ℕ) with hP
  have hPc : Continuous P := by rw [hP]; fun_prop
  have hexp : ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * P r * (starRingEnd ℂ) (P r)
      = ∑ t, star (c t) * (momentMatrix K d *ᵥ c) t := by
    have e : ∀ r : ℝ, (K.lineWeight r : ℂ) * P r * (starRingEnd ℂ) (P r) =
        ∑ t : Fin (d + 1), ∑ j : Fin (d + 1), star (c t) * (((K.lineWeight r : ℂ) * (r : ℂ) ^ (j : ℕ) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ))) * c j) := by
      intro r
      simp only [hP, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      simp only [Complex.star_def]
      ring
    simp_rw [e]
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun t _ => ?_
      rw [integral_finsetSum]
      · simp only [integral_const_mul, integral_mul_const, Matrix.mulVec, dotProduct, Finset.mul_sum, momentMatrix]
      · intro j _
        exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
    · intro t _
      refine integrable_finsetSum _ fun j _ => ?_
      exact (Continuous.continuousOn (by fun_prop)).integrableOn_compact isCompact_Icc
  have hzero : ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * P r * (starRingEnd ℂ) (P r) = 0 := by
    rw [hexp, hMc]
    simp
  have hreal : ∫ r in Icc K.r₁ K.r₂, K.lineWeight r * ‖P r‖ ^ 2 = 0 := by
    have e : ∀ r : ℝ, (K.lineWeight r : ℂ) * P r * (starRingEnd ℂ) (P r) = ((K.lineWeight r * ‖P r‖ ^ 2 : ℝ) : ℂ) := by
      intro r
      rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      ring
    simp_rw [e] at hzero
    rw [integral_complex_ofReal] at hzero
    exact_mod_cast hzero
  have hint : IntegrableOn (fun r => K.lineWeight r * ‖P r‖ ^ 2) (Icc K.r₁ K.r₂) :=
    (Continuous.continuousOn (by have := weight_cont K; fun_prop)).integrableOn_compact isCompact_Icc
  have hnn : 0 ≤ᵐ[volume.restrict (Icc K.r₁ K.r₂)] (fun r => K.lineWeight r * ‖P r‖ ^ 2) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact mul_nonneg (weight_nonneg K hK hr) (by positivity)
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hreal
  have hae2 : ∀ᵐ r, r ∈ Icc K.r₁ K.r₂ → K.lineWeight r * ‖P r‖ ^ 2 = 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp hae
  have hinf : {r | r ∈ Ioo K.r₁ K.r₂ ∧ P r = 0}.Infinite := by
    intro hfin
    have h0 := hfin.measure_zero volume
    have hnot : ∀ᵐ r, r ∉ Ioo K.r₁ K.r₂ := by
      filter_upwards [hae2, measure_eq_zero_iff_ae_notMem.mp h0] with r h1 h2 hr
      apply h2
      refine ⟨hr, ?_⟩
      have h3 := h1 (Ioo_subset_Icc_self hr)
      have hw0 := weight_pos K hK hr
      have : ‖P r‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp h3 with h | h
        · exact absurd h hw0.ne'
        · exact h
      simpa using this
    have := measure_eq_zero_iff_ae_notMem.mpr hnot
    rw [Real.volume_Ioo] at this
    have hlt := hK.r_order.2
    simp at this
    linarith
  have hc0 := poly_zero _ hinf c (fun r hr => hr.2)
  exact sub_eq_zero.mp (hc.symm.trans hc0)

theorem momentMatrix_unit (K : CellBox) (hK : IsCellBox K) (d : ℕ) : IsUnit (momentMatrix K d) :=
  Matrix.mulVec_injective_iff_isUnit.mp (momentMatrix_inj K hK d)

theorem momentMatrix_inv_spec (K : CellBox) (hK : IsCellBox K) (d : ℕ) (b : Fin (d + 1) → ℂ) :
    momentMatrix K d *ᵥ ((momentMatrix K d)⁻¹ *ᵥ b) = b := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (momentMatrix_unit K hK d)),
    Matrix.one_mulVec]

theorem projR_eq (K : CellBox) (hK : IsCellBox K) (d : ℕ) (F : ℝ × ℝ → ℂ) (z : ℝ)
    (hs : IntegrableOn (fun r => (K.lineWeight r : ℂ) * F (r, z)) (Icc K.r₁ K.r₂)) (r' : ℝ) :
    K.projR d F (r', z) = ∑ j, ((momentMatrix K d)⁻¹ *ᵥ moments K d F z) j * (r' : ℂ) ^ (j : ℕ) := by
  have hex : ∃ c : Fin (d + 1) → ℂ, ∀ t : Fin (d + 1), ∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) *
      (F (r, z) - ∑ j, c j * (r : ℂ) ^ (j : ℕ)) * (starRingEnd ℂ) ((r : ℂ) ^ (t : ℕ)) = 0 :=
    ⟨_, (cond_iff K d F z hs _).mpr (momentMatrix_inv_spec K hK d _)⟩
  simp only [CellBox.projR, dif_pos hex]
  have hch := (cond_iff K d F z hs _).mp hex.choose_spec
  have : hex.choose = (momentMatrix K d)⁻¹ *ᵥ moments K d F z :=
    momentMatrix_inj K hK d (hch.trans (momentMatrix_inv_spec K hK d _).symm)
  rw [this]

end Internal.ModeHeightLine

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

namespace Internal.ModeHeightLine

theorem rect_eq (K : CellBox) :
    volume.restrict K.rect = (volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂)) := by
  rw [CellBox.rect, Measure.volume_eq_prod, Measure.prod_restrict]

theorem primitive_ibp {a b : ℝ} (_hab : a ≤ b) {A : ℝ → ℂ} (hA : IntegrableOn A (Icc a b))
    {k : ℝ → ℂ} (hk : Continuous k) :
    ∫ z in Icc a b, (∫ u in a..z, A u) * k z = ∫ u in Icc a b, A u * ∫ z in u..b, k z := by
  set μ := volume.restrict (Icc a b)
  have hkI : Integrable k μ := hk.continuousOn.integrableOn_compact isCompact_Icc
  have hmeas : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} := measurableSet_le measurable_fst measurable_snd
  have hint : Integrable ({p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2)) (μ.prod μ) :=
    (Integrable.mul_prod hA hkI).indicator hmeas
  have h1 : ∀ z ∈ Icc a b, ∫ u in Icc a b, {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2) (u, z)
      = (∫ u in a..z, A u) * k z := by
    intro z hz
    have e : (fun u => {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2) (u, z))
        = (Iic z).indicator (fun u => A u * k z) := by
      funext u
      simp [Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Iic, integral_mul_const]
    congr 1
    have hs : Icc a b ∩ Iic z = Icc a z := by
      ext u
      simp only [mem_inter_iff, mem_Icc, mem_Iic]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨h1, le_trans h3 hz.2⟩, h3⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hz.1]
  have h2 : ∀ u ∈ Icc a b, ∫ z in Icc a b, {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2) (u, z)
      = A u * ∫ z in u..b, k z := by
    intro u hu
    have e : (fun z => {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2) (u, z))
        = (Ici u).indicator (fun z => A u * k z) := by
      funext z
      simp [Set.indicator]
    rw [e, setIntegral_indicator measurableSet_Ici, integral_const_mul]
    congr 1
    have hs : Icc a b ∩ Ici u = Icc u b := by
      ext z
      simp only [mem_inter_iff, mem_Icc, mem_Ici]
      constructor
      · rintro ⟨⟨_, h2⟩, h3⟩
        exact ⟨h3, h2⟩
      · rintro ⟨h1, h3⟩
        exact ⟨⟨le_trans hu.1 h1, h3⟩, h1⟩
    rw [hs, integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hu.2]
  have hswap := integral_integral_swap (μ := μ) (ν := μ)
    (f := fun u z => {p : ℝ × ℝ | p.1 ≤ p.2}.indicator (fun p => A p.1 * k p.2) (u, z)) hint
  rw [← setIntegral_congr_fun measurableSet_Icc h1, ← setIntegral_congr_fun measurableSet_Icc h2]
  exact hswap.symm

theorem primitive_ibp_real {a b : ℝ} (hab : a ≤ b) {A : ℝ → ℂ} (hA : IntegrableOn A (Icc a b))
    {h : ℝ → ℝ} (hh : ContDiff ℝ 1 h) (hb : h b = 0) :
    ∫ z in Icc a b, (∫ u in a..z, A u) * ((deriv h z : ℝ) : ℂ) = -∫ u in Icc a b, A u * (h u : ℂ) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv le_rfl
  rw [primitive_ibp hab hA (k := fun z => ((deriv h z : ℝ) : ℂ)) (Complex.continuous_ofReal.comp hd), ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun u hu => ?_
  rw [intervalIntegral.integral_ofReal, intervalIntegral.integral_deriv_eq_sub' h rfl
    (fun x _ => (hh.differentiable one_ne_zero).differentiableAt) hd.continuousOn, hb]
  push_cast
  ring

theorem eq_const_add_primitive {a b : ℝ} (hab : a < b) {B A : ℝ → ℂ} (hB : IntegrableOn B (Icc a b)) (hA : IntegrableOn A (Icc a b))
    (hyp : ∀ h : ℝ → ℝ, ContDiff ℝ 1 h → h a = 0 → h b = 0 →
      ∫ z in Icc a b, B z * ((deriv h z : ℝ) : ℂ) = -∫ z in Icc a b, A z * (h z : ℂ)) :
    ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict (Icc a b)), B z = c + ∫ u in a..z, A u := by
  set P : ℝ → ℂ := fun z => ∫ u in a..z, A u with hP
  have hPc : ContinuousOn P (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := a) (b := b) (f := A)
      (by rw [uIcc_of_le hab.le]; exact hA)
    rwa [uIcc_of_le hab.le] at this
  have hPI : IntegrableOn P (Icc a b) := hPc.integrableOn_compact isCompact_Icc
  set L : ℝ := b - a with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  set cD : ℂ := (∫ z in Icc a b, (B z - P z)) / L with hcD
  refine ⟨cD, ?_⟩
  have hloc : LocallyIntegrable (fun z => B z - P z - cD) (volume.restrict (Icc a b)) :=
    (((hB.sub hPI).sub (integrable_const cD))).locallyIntegrable
  have hz := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · filter_upwards [hz] with z hz
    have : B z - P z - cD = 0 := hz
    rw [hP] at this
    linear_combination this
  intro g hg hgs
  have hgc : Continuous g := hg.continuous
  set m : ℝ := (∫ z in Icc a b, g z) / L with hm
  set h : ℝ → ℝ := fun z => ∫ u in a..z, (g u - m) with hh
  have hcont : Continuous (fun u => g u - m) := hgc.sub continuous_const
  have hder : ∀ z, HasDerivAt h (g z - m) z := fun z =>
    (hcont.integral_hasStrictDerivAt a z).hasDerivAt
  have hderiv : deriv h = fun z => g z - m := funext fun z => (hder z).deriv
  have hC1 : ContDiff ℝ 1 h := by
    rw [contDiff_one_iff_deriv]
    exact ⟨fun z => (hder z).differentiableAt, by rw [hderiv]; exact hcont⟩
  have ha0 : h a = 0 := by simp [hh]
  have hgI : IntegrableOn g (Icc a b) := hgc.continuousOn.integrableOn_compact isCompact_Icc
  have hb0 : h b = 0 := by
    simp only [hh]
    rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _) intervalIntegrable_const,
      intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc, intervalIntegral.integral_const,
      hm, smul_eq_mul, ← hL]
    field_simp
    ring
  have h1 := hyp h hC1 ha0 hb0
  have h2 := primitive_ibp_real hab.le hA hC1 hb0
  have hD : ∫ z in Icc a b, (B z - P z) * ((g z - m : ℝ) : ℂ) = 0 := by
    have e : ∀ z, (B z - P z) * ((g z - m : ℝ) : ℂ) = B z * ((deriv h z : ℝ) : ℂ) - P z * ((deriv h z : ℝ) : ℂ) := by
      intro z; rw [hderiv]; ring
    simp_rw [e]
    rw [integral_sub, h1, h2]
    · ring
    · exact hB.mul_continuousOn (Complex.continuous_ofReal.comp (hC1.continuous_deriv le_rfl)).continuousOn isCompact_Icc
    · exact hPI.mul_continuousOn (Complex.continuous_ofReal.comp (hC1.continuous_deriv le_rfl)).continuousOn isCompact_Icc
  have hgC : Continuous (fun z => (g z : ℂ)) := Complex.continuous_ofReal.comp hgc
  have hBP : IntegrableOn (fun z => B z - P z) (Icc a b) := hB.sub hPI
  have i1 : ∫ z in Icc a b, (B z - P z) * ((g z - m : ℝ) : ℂ)
      = (∫ z in Icc a b, (B z - P z) * (g z : ℂ)) - (m : ℂ) * ∫ z in Icc a b, (B z - P z) := by
    have e : ∀ z, (B z - P z) * ((g z - m : ℝ) : ℂ) = (B z - P z) * (g z : ℂ) - (m : ℂ) * (B z - P z) := by
      intro z; push_cast; ring
    simp_rw [e]
    rw [integral_sub (hBP.mul_continuousOn hgC.continuousOn isCompact_Icc) (hBP.const_mul _), integral_const_mul]
  have i2 : ∫ z in Icc a b, g z • (B z - P z - cD)
      = (∫ z in Icc a b, (B z - P z) * (g z : ℂ)) - cD * ∫ z in Icc a b, (g z : ℂ) := by
    have e : ∀ z, g z • (B z - P z - cD) = (B z - P z) * (g z : ℂ) - cD * (g z : ℂ) := by
      intro z; rw [Complex.real_smul]; ring
    simp_rw [e]
    rw [integral_sub (hBP.mul_continuousOn hgC.continuousOn isCompact_Icc) ((hgC.continuousOn.integrableOn_compact isCompact_Icc).const_mul _), integral_const_mul]
  rw [i2]
  rw [i1] at hD
  have hgint : ∫ z in Icc a b, (g z : ℂ) = ((∫ z in Icc a b, g z : ℝ) : ℂ) := integral_ofReal
  rw [hgint]
  rw [hcD]
  rw [hm] at hD
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hLpos.ne'
  push_cast at hD
  field_simp
  field_simp at hD
  linear_combination hD

end Internal.ModeHeightLine

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

namespace Internal.ModeHeightLine

theorem slice_facts (K : CellBox) (Φ : ℝ × ℝ → ℂ) (hΦ : IntegrableOn Φ K.rect) (t : ℕ) :
    Integrable (fun z => ∫ r in Icc K.r₁ K.r₂, Φ (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t))
        (volume.restrict (Icc K.z₁ K.z₂)) ∧
      ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), IntegrableOn (fun r => Φ (r, z)) (Icc K.r₁ K.r₂) := by
  have h1 : Integrable Φ ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← rect_eq]; exact hΦ
  have h2 : Integrable (fun p : ℝ × ℝ => Φ p * (starRingEnd ℂ) ((p.1 : ℂ) ^ t))
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← rect_eq]
    exact hΦ.mul_continuousOn (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  exact ⟨h2.integral_prod_right, h1.prod_left_ae⟩

theorem rect_integral_split (K : CellBox) (Φ : ℝ × ℝ → ℂ) (hΦ : IntegrableOn Φ K.rect) (t : ℕ) (k : ℝ → ℝ) (hk : Continuous k) :
    ∫ p in K.rect, Φ p * ((p.1 ^ t * k p.2 : ℝ) : ℂ)
      = ∫ z in Icc K.z₁ K.z₂, (∫ r in Icc K.r₁ K.r₂, Φ (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)) * (k z : ℂ) := by
  have h2 : Integrable (fun p : ℝ × ℝ => Φ p * ((p.1 ^ t * k p.2 : ℝ) : ℂ))
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← rect_eq]
    exact hΦ.mul_continuousOn (by fun_prop) (isCompact_Icc.prod isCompact_Icc)
  rw [rect_eq, integral_prod_symm _ h2]
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  simp only
  rw [← integral_mul_const]
  congr 1
  funext r
  simp only [map_pow, Complex.conj_ofReal]
  push_cast
  ring

theorem sq_norm_integral_le {a b : ℝ} (hab : a < b) (φ : ℝ → ℂ) (hφ : IntegrableOn φ (Icc a b))
    (hφ2 : IntegrableOn (fun r => ‖φ r‖ ^ 2) (Icc a b)) :
    ‖∫ r in Icc a b, φ r‖ ^ 2 ≤ (b - a) * ∫ r in Icc a b, ‖φ r‖ ^ 2 := by
  set A := ∫ r in Icc a b, ‖φ r‖ with hA
  set L := b - a with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  have h1 : ‖∫ r in Icc a b, φ r‖ ≤ A := norm_integral_le_integral_norm _
  have hA0 : 0 ≤ A := integral_nonneg fun _ => norm_nonneg _
  have key : ∫ r in Icc a b, 2 * A * ‖φ r‖ ≤ ∫ r in Icc a b, (A ^ 2 / L + L * ‖φ r‖ ^ 2) := by
    refine integral_mono (hφ.norm.const_mul _) ((integrable_const _).add (hφ2.const_mul _)) fun r => ?_
    have := sq_nonneg (A - L * ‖φ r‖)
    rw [div_add' _ _ _ hLpos.ne', le_div_iff₀ hLpos]
    nlinarith
  rw [integral_const_mul, integral_add (integrable_const _) (hφ2.const_mul _), integral_const_mul,
    setIntegral_const, smul_eq_mul, ← hA] at key
  have hv : volume.real (Icc a b) = L := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  rw [hv] at key
  have h3 : A ^ 2 ≤ L * ∫ r in Icc a b, ‖φ r‖ ^ 2 := by
    field_simp at key
    nlinarith
  calc ‖∫ r in Icc a b, φ r‖ ^ 2 ≤ A ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h3

theorem moment_sq_le (K : CellBox) (hK : IsCellBox K) (g : ℝ × ℝ → ℂ) (z : ℝ) (t : ℕ)
    (hs : IntegrableOn (fun r => (K.lineWeight r : ℂ) * g (r, z)) (Icc K.r₁ K.r₂))
    (hs2 : IntegrableOn (fun r => K.lineWeight r * ‖g (r, z)‖ ^ 2) (Icc K.r₁ K.r₂)) :
    ‖∫ r in Icc K.r₁ K.r₂, (K.lineWeight r : ℂ) * g (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)‖ ^ 2
      ≤ (K.r₂ - K.r₁) * ((K.r₂ + 1) * (K.r₂ ^ t) ^ 2) * ∫ r in Icc K.r₁ K.r₂, K.lineWeight r * ‖g (r, z)‖ ^ 2 := by
  set C := (K.r₂ + 1) * (K.r₂ ^ t) ^ 2 with hC
  have hφ : IntegrableOn (fun r => (K.lineWeight r : ℂ) * g (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)) (Icc K.r₁ K.r₂) :=
    hs.mul_continuousOn (by fun_prop) isCompact_Icc
  have hpt : ∀ r ∈ Icc K.r₁ K.r₂, ‖(K.lineWeight r : ℂ) * g (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)‖ ^ 2
      ≤ C * (K.lineWeight r * ‖g (r, z)‖ ^ 2) := by
    intro r hr
    have hw0 := weight_nonneg K hK hr
    have hw1 := weight_le K hK hr
    have hr0 : 0 ≤ r := le_trans hK.r_order.1 hr.1
    have hrt : r ^ t ≤ K.r₂ ^ t := pow_le_pow_left₀ hr0 hr.2 t
    have hrt0 : 0 ≤ r ^ t := pow_nonneg hr0 t
    rw [norm_mul, norm_mul, RCLike.norm_conj, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hw0, Real.norm_of_nonneg hr0, hC]
    have hg0 : 0 ≤ ‖g (r, z)‖ := norm_nonneg _
    have e1 : (r ^ t) ^ 2 ≤ (K.r₂ ^ t) ^ 2 := pow_le_pow_left₀ hrt0 hrt 2
    have e2 : K.lineWeight r * K.lineWeight r ≤ (K.r₂ + 1) * K.lineWeight r := mul_le_mul_of_nonneg_right hw1 hw0
    calc (K.lineWeight r * ‖g (r, z)‖ * r ^ t) ^ 2
        = (K.lineWeight r * K.lineWeight r) * (r ^ t) ^ 2 * ‖g (r, z)‖ ^ 2 := by ring
      _ ≤ ((K.r₂ + 1) * K.lineWeight r) * (K.r₂ ^ t) ^ 2 * ‖g (r, z)‖ ^ 2 := by
          gcongr
          exact mul_nonneg (le_trans hw0 hw1) hw0
      _ = (K.r₂ + 1) * (K.r₂ ^ t) ^ 2 * (K.lineWeight r * ‖g (r, z)‖ ^ 2) := by ring
  have hφ2 : IntegrableOn (fun r => ‖(K.lineWeight r : ℂ) * g (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)‖ ^ 2)
      (Icc K.r₁ K.r₂) := by
    refine Integrable.mono' (hs2.const_mul C) (hφ.aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    rw [Real.norm_of_nonneg (by positivity)]
    exact hpt r hr
  calc _ ≤ (K.r₂ - K.r₁) * ∫ r in Icc K.r₁ K.r₂, ‖(K.lineWeight r : ℂ) * g (r, z) * (starRingEnd ℂ) ((r : ℂ) ^ t)‖ ^ 2 :=
        sq_norm_integral_le hK.r_order.2 _ hφ hφ2
    _ ≤ (K.r₂ - K.r₁) * ∫ r in Icc K.r₁ K.r₂, C * (K.lineWeight r * ‖g (r, z)‖ ^ 2) := by
        gcongr ?_ * ?_
        · linarith [hK.r_order.2]
        · exact setIntegral_mono_on hφ2 (hs2.const_mul C) measurableSet_Icc hpt
    _ = _ := by rw [integral_const_mul]; ring

end Internal.ModeHeightLine

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly

namespace Internal.ModeHeightLine

theorem line_core (K : CellBox) (hK : IsCellBox K) (d : ℕ) (F g : ℝ × ℝ → ℂ)
    (hF : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hg : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * g p) K.rect)
    (hg2 : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖g p‖ ^ 2) K.rect)
    (hibp : ∀ f h : ℝ → ℝ, Continuous f → ContDiff ℝ 1 h → h K.z₁ = 0 → h K.z₂ = 0 →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((f p.1 * deriv h p.2 : ℝ) : ℂ) =
          -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p * ((f p.1 * h p.2 : ℝ) : ℂ))
    (r : ℝ) : ∃ f : ℝ → ℂ,
        (∀ x ∈ Ioc K.z₁ K.z₂, ∀ y ∈ Ioc K.z₁ K.z₂,
          f y = f x + ∫ t in x..y, K.projR d g (r, t)) ∧
        ContinuousOn f (Ioc K.z₁ K.z₂) ∧
        AEStronglyMeasurable (fun z => K.projR d g (r, z)) (volume.restrict (Icc K.z₁ K.z₂)) ∧
        IntegrableOn (fun z => (1 : ℝ) * ‖K.projR d g (r, z)‖ ^ 2) (Icc K.z₁ K.z₂) ∧
        IntegrableOn (fun z => (1 : ℝ) * ‖f z‖ ^ 2) (Icc K.z₁ K.z₂) ∧
        (fun z => K.projR d F (r, z)) =ᵐ[volume.restrict (Icc K.z₁ K.z₂)] f := by
  have hz12 : K.z₁ < K.z₂ := hK.z_order.2
  set Minv := (momentMatrix K d)⁻¹ with hMinv
  have hFI : ∀ t : Fin (d + 1), IntegrableOn (fun z => moments K d F z t) (Icc K.z₁ K.z₂) := fun t =>
    (slice_facts K _ hF t).1
  have hgI : ∀ t : Fin (d + 1), IntegrableOn (fun z => moments K d g z t) (Icc K.z₁ K.z₂) := fun t =>
    (slice_facts K _ hg t).1
  have hsF : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)),
      IntegrableOn (fun r => (K.lineWeight r : ℂ) * F (r, z)) (Icc K.r₁ K.r₂) := (slice_facts K _ hF 0).2
  have hsg : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)),
      IntegrableOn (fun r => (K.lineWeight r : ℂ) * g (r, z)) (Icc K.r₁ K.r₂) := (slice_facts K _ hg 0).2
  have hg2p : Integrable (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖g p‖ ^ 2)
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    rw [← rect_eq]; exact hg2
  have hsg2 : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)),
      IntegrableOn (fun r => K.lineWeight r * ‖g (r, z)‖ ^ 2) (Icc K.r₁ K.r₂) := hg2p.prod_left_ae
  have hG2 : IntegrableOn (fun z => ∫ r in Icc K.r₁ K.r₂, K.lineWeight r * ‖g (r, z)‖ ^ 2) (Icc K.z₁ K.z₂) :=
    hg2p.integral_prod_right
  have hyp : ∀ t : Fin (d + 1), ∀ h : ℝ → ℝ, ContDiff ℝ 1 h → h K.z₁ = 0 → h K.z₂ = 0 →
      ∫ z in Icc K.z₁ K.z₂, moments K d F z t * ((deriv h z : ℝ) : ℂ) =
        -∫ z in Icc K.z₁ K.z₂, moments K d g z t * (h z : ℂ) := by
    intro t h hh h1 h2
    have e1 := rect_integral_split K (fun p => (K.lineWeight p.1 : ℂ) * F p) hF t (deriv h) (hh.continuous_deriv le_rfl)
    have e2 := rect_integral_split K (fun p => (K.lineWeight p.1 : ℂ) * g p) hg t h hh.continuous
    have e3 := hibp (fun r => r ^ (t : ℕ)) h (continuous_pow _) hh h1 h2
    exact e1.symm.trans (e3.trans (congrArg Neg.neg e2))
  have hc : ∀ t : Fin (d + 1), ∃ c : ℂ, ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)),
      moments K d F z t = c + ∫ u in K.z₁..z, moments K d g u t := fun t =>
    eq_const_add_primitive hz12 (hFI t) (hgI t) (hyp t)
  choose c hc using hc
  have hcAll : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), ∀ t : Fin (d + 1),
      moments K d F z t = c t + ∫ u in K.z₁..z, moments K d g u t := ae_all_iff.mpr hc
  set Lg : ℝ → ℂ := fun z => ∑ j : Fin (d + 1), ∑ t : Fin (d + 1), Minv j t * moments K d g z t * (r : ℂ) ^ (j : ℕ)
    with hLg
  set f : ℝ → ℂ := fun z => ∑ j : Fin (d + 1), ∑ t : Fin (d + 1),
    Minv j t * (c t + ∫ u in K.z₁..z, moments K d g u t) * (r : ℂ) ^ (j : ℕ) with hf
  have hprojg : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), K.projR d g (r, z) = Lg z := by
    filter_upwards [hsg] with z hz
    rw [projR_eq K hK d g z hz r, hLg]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    rfl
  have hprojF : ∀ᵐ z ∂(volume.restrict (Icc K.z₁ K.z₂)), K.projR d F (r, z) = f z := by
    filter_upwards [hsF, hcAll] with z hz hcz
    rw [projR_eq K hK d F z hz r, hf]
    simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun t _ => ?_
    rw [hcz t]
  have hmomL2 : ∀ t : Fin (d + 1), MemLp (fun z => moments K d g z t) 2 (volume.restrict (Icc K.z₁ K.z₂)) := by
    intro t
    refine (memLp_two_iff_integrable_sq_norm (hgI t).aestronglyMeasurable).mpr ?_
    refine Integrable.mono' (hG2.const_mul ((K.r₂ - K.r₁) * ((K.r₂ + 1) * (K.r₂ ^ (t : ℕ)) ^ 2)))
      ((hgI t).aestronglyMeasurable.norm.pow 2) ?_
    filter_upwards [hsg, hsg2] with z h1 h2
    rw [Real.norm_of_nonneg (by positivity)]
    exact moment_sq_le K hK g z t h1 h2
  have hLgL2 : MemLp Lg 2 (volume.restrict (Icc K.z₁ K.z₂)) := by
    rw [hLg]
    refine memLp_finsetSum _ fun j _ => memLp_finsetSum _ fun t _ => ?_
    exact ((hmomL2 t).const_mul (Minv j t)).mul_const _
  have hPc : ∀ t : Fin (d + 1), ContinuousOn (fun z => ∫ u in K.z₁..z, moments K d g u t) (Icc K.z₁ K.z₂) := by
    intro t
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := K.z₁) (b := K.z₂)
      (f := fun u => moments K d g u t) (by rw [uIcc_of_le hz12.le]; exact hgI t)
    rwa [uIcc_of_le hz12.le] at this
  have hfc : ContinuousOn f (Icc K.z₁ K.z₂) := by
    rw [hf]
    refine continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun t _ => ?_
    exact (continuousOn_const.mul (continuousOn_const.add (hPc t))).mul continuousOn_const
  have hII : ∀ t : Fin (d + 1), ∀ x ∈ Icc K.z₁ K.z₂, ∀ y ∈ Icc K.z₁ K.z₂,
      IntervalIntegrable (fun u => moments K d g u t) volume x y := by
    intro t x hx y hy
    refine IntegrableOn.intervalIntegrable ((hgI t).mono_set ?_)
    exact uIcc_subset_Icc hx hy
  refine ⟨f, ?_, hfc.mono Ioc_subset_Icc_self, ?_, ?_, ?_, hprojF⟩
  · intro x hx y hy
    have hx' : x ∈ Icc K.z₁ K.z₂ := Ioc_subset_Icc_self hx
    have hy' : y ∈ Icc K.z₁ K.z₂ := Ioc_subset_Icc_self hy
    have hz1 : K.z₁ ∈ Icc K.z₁ K.z₂ := left_mem_Icc.mpr hz12.le
    have hcongr : ∫ u in x..y, K.projR d g (r, u) = ∫ u in x..y, Lg u := by
      refine intervalIntegral.integral_congr_ae ?_
      have := (ae_restrict_iff' measurableSet_Icc).mp hprojg
      filter_upwards [this] with u hu hmem
      refine hu ?_
      exact uIoc_subset_uIcc.trans (uIcc_subset_Icc hx' hy') hmem
    rw [hcongr, hLg, hf]
    simp only
    rw [intervalIntegral.integral_finsetSum]
    · rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul,
          ← intervalIntegral.integral_interval_sub_left (hII t _ hz1 _ hy') (hII t _ hz1 _ hx')]
        ring
      · intro t _
        exact ((hII t x hx' y hy').const_mul _).mul_const _
    · intro j _
      have := IntervalIntegrable.sum Finset.univ fun t _ =>
        ((hII t x hx' y hy').const_mul (Minv j t)).mul_const ((r : ℂ) ^ (j : ℕ))
      have e : (fun u => ∑ t : Fin (d + 1), Minv j t * moments K d g u t * (r : ℂ) ^ (j : ℕ))
          = ∑ t : Fin (d + 1), fun u => Minv j t * moments K d g u t * (r : ℂ) ^ (j : ℕ) := by
        funext u
        simp [Finset.sum_apply]
      rw [e]
      exact this
  · exact hLgL2.aestronglyMeasurable.congr (hprojg.mono fun z hz => hz.symm)
  · have h1 := (memLp_two_iff_integrable_sq_norm hLgL2.aestronglyMeasurable).mp hLgL2
    refine (h1.congr ?_)
    filter_upwards [hprojg] with z hz
    rw [hz, one_mul]
  · have : ContinuousOn (fun z => (1 : ℝ) * ‖f z‖ ^ 2) (Icc K.z₁ K.z₂) :=
      continuousOn_const.mul (hfc.norm.pow 2)
    exact this.integrableOn_compact isCompact_Icc

end Internal.ModeHeightLine

end Breakdown.CellCert.CellAnalysis

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly Internal.ModeHeightLine

theorem modeHeightLine_of (h1 : CellFormula.HeightModeIbpStatement) (h2 : ModeGradSquareStatement)
    (h3 : ModeVelSquareStatement) : ModeHeightLineStatement := by
  intro K hK m v G H hS n a Q r
  obtain ⟨hgI, hibp⟩ := h1 m n v G H hS K hK a
  obtain ⟨_, hg2⟩ := h2 K hK m v G H hS n a 2
  obtain ⟨hFm, hF2⟩ := h3 K hK m v G H hS n a
  have hrect : MeasurableSet K.rect := by
    rw [CellBox.rect]; exact measurableSet_Icc.prod measurableSet_Icc
  have hF : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect := by
    have hw : IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1) K.rect := by
      have hc : Continuous (fun p : ℝ × ℝ => K.lineWeight p.1) := (weight_cont K).comp continuous_fst
      rw [CellBox.rect]
      exact hc.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
    refine Integrable.mono' (hw.add hF2)
      (((Complex.continuous_ofReal.comp ((weight_cont K).comp continuous_fst)).aestronglyMeasurable).mul hFm) ?_
    filter_upwards [ae_restrict_mem hrect] with p hp
    rw [CellBox.rect] at hp
    have hw0 := weight_nonneg K hK hp.1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hw0]
    have hx : ‖modeVec m n v p.1 p.2 a‖ ≤ 1 + ‖modeVec m n v p.1 p.2 a‖ ^ 2 := by
      nlinarith [norm_nonneg (modeVec m n v p.1 p.2 a)]
    simp only [Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left hx hw0]
  exact line_core K hK (Q - 1) (fun p => modeVec m n v p.1 p.2 a) (gradMode m n G a 2) hF hgI hg2 hibp r

end Breakdown.CellCert.CellAnalysis

import Breakdown.FracCell.SharpYSharpEnergyTail
import Breakdown.FracCell.SharpCoefTail
import Breakdown.FracCell.EnergyTop
import Breakdown.FracCell.BasisEnergySum
import Breakdown.FracCell.ModeRadialWeakProof
import Breakdown.FracCell.HeightModeIbp

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown.CellCert.CellAnalysis

namespace SharpEnergyVelocityCoefInternal

open CellSharpBoundInternal SharpCoefTailInternal SteadyCert Assembly

def antider (P : ℝ[X]) : ℝ[X] :=
  ∑ n ∈ Finset.range (P.natDegree + 1), C (P.coeff n / (n + 1)) * X ^ (n + 1)

theorem antider_deriv (P : ℝ[X]) : derivative (antider P) = P := by
  unfold antider
  rw [derivative_sum]
  conv_rhs => rw [P.as_sum_range_C_mul_X_pow]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [derivative_C_mul_X_pow]
  have h : (n : ℝ) + 1 ≠ 0 := by positivity
  congr 1
  · congr 1
    push_cast
    field_simp

theorem antider_deg (P : ℝ[X]) : (antider P).natDegree ≤ P.natDegree + 1 := by
  unfold antider
  refine natDegree_sum_le_of_forall_le _ _ fun n hn => ?_
  have := Finset.mem_range.1 hn
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem rad_low {K : CellBox} {B : CellBases} (hK : K.r₁ < K.r₂) (hB : IsCellBases K B) {i j : ℕ}
    (hij : i + 1 < j) :
    ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * B.radialPoly i r = 0 := by
  open CellFormula.Internal.RelRadialCoef in
  have hd : (antider (poly B i)).natDegree ≤ i + 1 :=
    (antider_deg _).trans (by have := poly_natDegree B i; omega)
  obtain ⟨c, hc⟩ := span B (fun j => (hB.radial_leading j).ne') (i + 1) _ hd
  have e : ∀ r, B.radialPoly i r = ∑ k ∈ Finset.range (i + 1 + 1), c k * rd B k r := by
    intro r
    rw [← poly_eval, ← antider_deriv (poly B i), hc, derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_C_mul, eval_C_mul]
    rfl
  have hcont : ∀ k, Continuous (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * rd B k r) :=
    fun k => (((lw_cont K).mul (continuous_const.sub ((refR_cont K).pow 2))).mul (rd_cont B j)).mul (rd_cont B k)
  simp_rw [e, Finset.mul_sum]
  rw [integral_finsetSum _ (fun k _ => ((hcont k).const_mul (c k)).integrableOn_Icc.congr_fun
    (fun r _ => by ring) measurableSet_Icc)]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have h1 := rad_orth hK hB j k
  rw [if_neg (by omega)] at h1
  calc ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * (c k * rd B k r)
      = ∫ r in Set.Icc K.r₁ K.r₂, c k * (K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r * rd B k r) := by
        congr 1; funext r; ring
    _ = 0 := by rw [integral_const_mul, h1, mul_zero]

theorem ht_low {K : CellBox} {B : CellBases} (hK : K.z₁ < K.z₂) (hB : IsCellBases K B) {i l : ℕ}
    (hil : i + 1 < l) :
    ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * B.heightPoly i z * hd B l z = 0 := by
  open CellFormula.Internal.RelHeightCoef in
  have hpe : ∀ l z, (hp B.heightCoef l).eval z = B.heightPoly l z := by
    intro l z; rw [hp_eval]; rfl
  have hd' : (antider (hp B.heightCoef i)).natDegree ≤ i + 1 :=
    (antider_deg _).trans (by have := hp_natDegree B.heightCoef i; omega)
  obtain ⟨c, hc⟩ := span (a := B.heightCoef) (fun l => (hB.height_leading l).ne') (i + 1) _ hd'
  have hpoly : antider (hp B.heightCoef i) = ∑ k ∈ Finset.range (i + 1 + 1), C (c k) * hp B.heightCoef k := by
    apply Polynomial.funext
    intro z
    rw [hc z, eval_finsetSum]
    simp only [eval_mul, eval_C]
  have e : ∀ z, B.heightPoly i z = ∑ k ∈ Finset.range (i + 1 + 1), c k * hd B k z := by
    intro z
    rw [← hpe, ← antider_deriv (hp B.heightCoef i), hpoly, derivative_sum, eval_finsetSum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [derivative_C_mul, eval_C_mul]
    rfl
  have hcont : ∀ k, Continuous (fun z => (1 - K.refZ z ^ 2) * hd B k z * hd B l z) :=
    fun k => ((continuous_const.sub ((refZ_cont K).pow 2)).mul (hd_cont B k)).mul (hd_cont B l)
  simp_rw [e, Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _ => ((hcont k).const_mul (c k)).integrableOn_Icc.congr_fun
    (fun z _ => by ring) measurableSet_Icc)]
  refine Finset.sum_eq_zero fun k hk => ?_
  have hk' := Finset.mem_range.1 hk
  have h1 := ht_orth hK hB k l
  rw [if_neg (by omega)] at h1
  calc ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * (c k * hd B k z) * hd B l z
      = ∫ z in Set.Icc K.z₁ K.z₂, c k * ((1 - K.refZ z ^ 2) * hd B k z * hd B l z) := by
        congr 1; funext z; ring
    _ = 0 := by rw [integral_const_mul, h1, mul_zero]


theorem wle_int {K : CellBox} (W : ℝ × ℝ → ℝ) (hWc : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (hWl : ∀ p ∈ K.rect, W p ≤ K.lineWeight p.1) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => W p * ‖F p‖ ^ 2) K.rect := by
  refine Integrable.mono' hF2 (hWc.aestronglyMeasurable.mul (hF.norm.pow 2)) ?_
  refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  rw [Real.norm_of_nonneg (mul_nonneg (hW0 p hp) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_right (hWl p hp) (sq_nonneg _)

theorem sq_split {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (U : Finset (ℕ × ℕ)) :
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p - ∑ u ∈ U, B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ)‖ ^ 2)
        K.rect ∧
      ∫ p in K.rect, K.lineWeight p.1 * ‖F p - ∑ u ∈ U, B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ)‖ ^ 2
        = (∫ p in K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2) - ∑ u ∈ U, ‖B.coef K F u.1 u.2‖ ^ 2 := by
  set c : ℕ × ℕ → ℂ := fun u => B.coef K F u.1 u.2 with hc
  have hg := g_int B F hF hF2
  have hcg : ∀ u, c u = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((bas B u p : ℝ) : ℂ) := fun u => rfl
  have hpt : ∀ p : ℝ × ℝ, K.lineWeight p.1 * ‖F p - ∑ u ∈ U, c u * ((bas B u p : ℝ) : ℂ)‖ ^ 2
      = K.lineWeight p.1 * ‖F p‖ ^ 2
        - 2 * ∑ u ∈ U, ((starRingEnd ℂ) (c u) * ((K.lineWeight p.1 : ℂ) * F p * ((bas B u p : ℝ) : ℂ))).re
        + ∑ u ∈ U, ∑ u' ∈ U, (c u * (starRingEnd ℂ) (c u')).re * (K.lineWeight p.1 * bas B u p * bas B u' p) :=
    fun p => pt_id (K.lineWeight p.1) (F p) U c (fun u => bas B u p)
  have iA : ∀ u ∈ U, Integrable (fun p => ((starRingEnd ℂ) (c u) *
      ((K.lineWeight p.1 : ℂ) * F p * ((bas B u p : ℝ) : ℂ))).re) (volume.restrict K.rect) :=
    fun u _ => ((hg u).const_mul _).re
  have iB : ∀ u ∈ U, ∀ u' ∈ U, Integrable (fun p => (c u * (starRingEnd ℂ) (c u')).re *
      (K.lineWeight p.1 * bas B u p * bas B u' p)) (volume.restrict K.rect) :=
    fun u _ u' _ => (wbb_int K B u u').const_mul _
  have iB' : ∀ u ∈ U, Integrable (fun p => ∑ u' ∈ U, (c u * (starRingEnd ℂ) (c u')).re *
      (K.lineWeight p.1 * bas B u p * bas B u' p)) (volume.restrict K.rect) :=
    fun u hu => integrable_finsetSum _ (iB u hu)
  have iA2 := (integrable_finsetSum U iA).const_mul 2
  have hsub : Integrable (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2
      - 2 * ∑ u ∈ U, ((starRingEnd ℂ) (c u) * ((K.lineWeight p.1 : ℂ) * F p * ((bas B u p : ℝ) : ℂ))).re)
      (volume.restrict K.rect) := hF2.sub iA2
  have hI := hsub.add (integrable_finsetSum _ iB')
  refine ⟨hI.congr (Filter.Eventually.of_forall fun p => (hpt p).symm), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_add hsub (integrable_finsetSum _ iB'),
    integral_sub hF2 iA2, integral_const_mul, integral_finsetSum _ iA, integral_finsetSum _ iB']
  have eA : ∀ u, ∫ p in K.rect, ((starRingEnd ℂ) (c u) *
      ((K.lineWeight p.1 : ℂ) * F p * ((bas B u p : ℝ) : ℂ))).re = ‖c u‖ ^ 2 := by
    intro u
    have h := integral_re (𝕜 := ℂ) ((hg u).const_mul ((starRingEnd ℂ) (c u)))
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul, ← hcg, sqn, mul_comm]
  have eB : ∀ u ∈ U, ∫ p in K.rect, ∑ u' ∈ U, (c u * (starRingEnd ℂ) (c u')).re *
      (K.lineWeight p.1 * bas B u p * bas B u' p) = ‖c u‖ ^ 2 := by
    intro u hu
    rw [integral_finsetSum _ (iB u hu)]
    rw [Finset.sum_congr rfl (fun u' _ => by rw [integral_const_mul, orth hB u u'])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq U u, if_pos hu, sqn]
  rw [Finset.sum_congr rfl eB]
  simp only [eA]
  ring

theorem proj_coef_le {K : CellBox} {B : CellBases} (hB : IsCellBases K B)
    (W : ℝ × ℝ → ℝ) (hWc : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (hWl : ∀ p ∈ K.rect, W p ≤ K.lineWeight p.1)
    (b : ℕ × ℕ → ℝ × ℝ → ℝ) (hb : ∀ i, Continuous (b i)) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (T U : Finset (ℕ × ℕ))
    (horth : ∀ i ∈ T, ∀ i' ∈ T, ∫ p in K.rect, W p * b i p * b i' p = if i = i' then 1 else 0)
    (hzero : ∀ u ∈ U, ∀ i ∈ T, ∫ p in K.rect, W p * bas B u p * b i p = 0) :
    ∑ i ∈ T, ‖∫ p in K.rect, (W p : ℂ) * F p * ((b i p : ℝ) : ℂ)‖ ^ 2
      + ∑ u ∈ U, ‖B.coef K F u.1 u.2‖ ^ 2 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2 := by
  obtain ⟨hi, he⟩ := sq_split hB F hF hF2 U
  set h : ℝ × ℝ → ℂ := fun p => F p - ∑ u ∈ U, B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ) with hh
  have hhm : AEStronglyMeasurable h (volume.restrict K.rect) :=
    hF.sub (continuous_finsetSum _ fun u _ =>
      continuous_const.mul (Complex.continuous_ofReal.comp (bas_cont B u))).aestronglyMeasurable
  have hhW := wle_int W hWc hW0 hWl h hhm hi
  have hFW := wle_int W hWc hW0 hWl F hF hF2
  have key : ∀ i ∈ T, ∫ p in K.rect, (W p : ℂ) * F p * ((b i p : ℝ) : ℂ)
      = ∫ p in K.rect, (W p : ℂ) * h p * ((b i p : ℝ) : ℂ) := by
    intro i hiT
    have hz : ∀ u ∈ U, ∫ p in K.rect, (W p : ℂ) * (B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ))
        * ((b i p : ℝ) : ℂ) = 0 := by
      intro u hu
      have e : ∀ p : ℝ × ℝ, (W p : ℂ) * (B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ)) * ((b i p : ℝ) : ℂ)
          = B.coef K F u.1 u.2 * ((W p * bas B u p * b i p : ℝ) : ℂ) := by
        intro p; push_cast; ring
      simp_rw [e]
      rw [integral_const_mul, integral_complex_ofReal, hzero u hu i hiT, Complex.ofReal_zero, mul_zero]
    have hint : ∀ u ∈ U, IntegrableOn (fun p => (W p : ℂ) * (B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ))
        * ((b i p : ℝ) : ℂ)) K.rect := fun u _ =>
      (((Complex.continuous_ofReal.comp hWc).mul (continuous_const.mul
        (Complex.continuous_ofReal.comp (bas_cont B u)))).mul
        (Complex.continuous_ofReal.comp (hb i))).continuousOn.integrableOn_compact (rect_cpt K)
    have e : ∀ p : ℝ × ℝ, (W p : ℂ) * h p * ((b i p : ℝ) : ℂ) = (W p : ℂ) * F p * ((b i p : ℝ) : ℂ)
        - ∑ u ∈ U, (W p : ℂ) * (B.coef K F u.1 u.2 * ((bas B u p : ℝ) : ℂ)) * ((b i p : ℝ) : ℂ) := by
      intro p
      simp only [hh]
      rw [mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
    simp_rw [e]
    rw [integral_sub (g_int' K W hWc hW0 b hb F hF hFW i) (integrable_finsetSum _ hint),
      integral_finsetSum _ hint, Finset.sum_eq_zero hz, sub_zero]
  have hb1 := sq_coef_le K W hWc hW0 b hb h hhm hhW T horth
  have hmono : ∫ p in K.rect, W p * ‖h p‖ ^ 2 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖h p‖ ^ 2 :=
    setIntegral_mono_on hhW hi (rect_meas K) fun p hp => mul_le_mul_of_nonneg_right (hWl p hp) (sq_nonneg _)
  rw [Finset.sum_congr rfl fun i hiT => by rw [key i hiT]]
  linarith

def wr (K : CellBox) (p : ℝ × ℝ) : ℝ := K.lineWeight p.1 * (1 - K.refR p.1 ^ 2)

def wz (K : CellBox) (p : ℝ × ℝ) : ℝ := K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2)

def br (K : CellBox) (B : CellBases) (i : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  rd B i.1 p.1 * B.heightPoly i.2 p.2 / Real.sqrt (radialEigen K i.1)

def bz (K : CellBox) (B : CellBases) (i : ℕ × ℕ) (p : ℝ × ℝ) : ℝ :=
  B.radialPoly i.1 p.1 * hd B i.2 p.2 / Real.sqrt (heightEigen K i.2)

theorem wr_cont (K : CellBox) : Continuous (wr K) :=
  ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))

theorem wz_cont (K : CellBox) : Continuous (wz K) :=
  ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))

theorem br_cont (K : CellBox) (B : CellBases) (i : ℕ × ℕ) : Continuous (br K B i) :=
  (((rd_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)).div_const _

theorem bz_cont (K : CellBox) (B : CellBases) (i : ℕ × ℕ) : Continuous (bz K B i) :=
  (((rp_cont B _).comp continuous_fst).mul ((hd_cont B _).comp continuous_snd)).div_const _

theorem wr_nonneg {K : CellBox} (hK : IsCellBox K) : ∀ p ∈ K.rect, 0 ≤ wr K p := fun _ hp =>
  mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hK.r_order.2 hp.1.1 hp.1.2)

theorem wz_nonneg {K : CellBox} (hK : IsCellBox K) : ∀ p ∈ K.rect, 0 ≤ wz K p := fun _ hp =>
  mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hK.z_order.2 hp.2.1 hp.2.2)

theorem wr_le {K : CellBox} : ∀ p ∈ K.rect, wr K p ≤ K.lineWeight p.1 := by
  intro p hp
  have h1 := lw_nonneg (K := K) hp.1.1
  have h2 := sq_nonneg (K.refR p.1)
  unfold wr
  nlinarith

theorem wz_le {K : CellBox} : ∀ p ∈ K.rect, wz K p ≤ K.lineWeight p.1 := by
  intro p hp
  have h1 := lw_nonneg (K := K) hp.1.1
  have h2 := sq_nonneg (K.refZ p.2)
  unfold wz
  nlinarith

theorem br_orth {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {i i' : ℕ × ℕ}
    (hj : i.1 ≠ 0) (hj' : i'.1 ≠ 0) :
    ∫ p in K.rect, wr K p * br K B i p * br K B i' p = if i = i' then 1 else 0 := by
  have hr := hK.r_order.2
  have e : ∀ p : ℝ × ℝ, wr K p * br K B i p * br K B i' p
      = (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B i.1 p.1 * rd B i'.1 p.1
          / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
        * (B.heightPoly i.2 p.2 * B.heightPoly i'.2 p.2) := by
    intro p; simp only [wr, br]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B i.1 r * rd B i'.1 r
        / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
      (fun z => B.heightPoly i.2 z * B.heightPoly i'.2 z),
    integral_div, rad_orth hr hB, hB.height_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hj hj' ⊢
  have hp := radialEigen_pos (K := K) hr hj
  by_cases h1 : j = j'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', one_mul]
    by_cases h2 : l = l' <;> simp [h2]
  · simp [h1]

theorem bz_orth {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {i i' : ℕ × ℕ}
    (hl : i.2 ≠ 0) (hl' : i'.2 ≠ 0) :
    ∫ p in K.rect, wz K p * bz K B i p * bz K B i' p = if i = i' then 1 else 0 := by
  have hz := hK.z_order.2
  have e : ∀ p : ℝ × ℝ, wz K p * bz K B i p * bz K B i' p
      = (K.lineWeight p.1 * B.radialPoly i.1 p.1 * B.radialPoly i'.1 p.1)
        * ((1 - K.refZ p.2 ^ 2) * hd B i.2 p.2 * hd B i'.2 p.2
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))) := by
    intro p; simp only [wz, bz]; field_simp
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly i.1 r * B.radialPoly i'.1 r)
      (fun z => (1 - K.refZ z ^ 2) * hd B i.2 z * hd B i'.2 z
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))),
    integral_div, ht_orth hz hB, hB.radial_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq] at hl hl' ⊢
  have hp := heightEigen_pos (K := K) hz hl
  by_cases h1 : l = l'
  · subst h1
    rw [if_pos rfl, Real.mul_self_sqrt hp.le, div_self hp.ne', mul_one]
    by_cases h2 : j = j' <;> simp [h2]
  · simp [h1]

theorem br_zero {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {u i : ℕ × ℕ}
    (h : u.1 + 1 < i.1) : ∫ p in K.rect, wr K p * bas B u p * br K B i p = 0 := by
  have e : ∀ p : ℝ × ℝ, wr K p * bas B u p * br K B i p
      = (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B i.1 p.1 * B.radialPoly u.1 p.1
          / Real.sqrt (radialEigen K i.1)) * (B.heightPoly u.2 p.2 * B.heightPoly i.2 p.2) := by
    intro p; simp only [wr, bas, br]; ring
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B i.1 r * B.radialPoly u.1 r
        / Real.sqrt (radialEigen K i.1))
      (fun z => B.heightPoly u.2 z * B.heightPoly i.2 z),
    integral_div, rad_low hK.r_order.2 hB h, zero_div, zero_mul]

theorem bz_zero {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) {u i : ℕ × ℕ}
    (h : u.1 ≠ i.1 ∨ u.2 + 1 < i.2) : ∫ p in K.rect, wz K p * bas B u p * bz K B i p = 0 := by
  have e : ∀ p : ℝ × ℝ, wz K p * bas B u p * bz K B i p
      = (K.lineWeight p.1 * B.radialPoly u.1 p.1 * B.radialPoly i.1 p.1)
        * ((1 - K.refZ p.2 ^ 2) * B.heightPoly u.2 p.2 * hd B i.2 p.2 / Real.sqrt (heightEigen K i.2)) := by
    intro p; simp only [wz, bas, bz]; ring
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly u.1 r * B.radialPoly i.1 r)
      (fun z => (1 - K.refZ z ^ 2) * B.heightPoly u.2 z * hd B i.2 z / Real.sqrt (heightEigen K i.2)),
    integral_div, hB.radial_orthonormal]
  rcases h with h | h
  · rw [if_neg h, zero_mul]
  · rw [ht_low hK.z_order.2 hB h, zero_div, mul_zero]

theorem radial_term {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    {i : ℕ × ℕ} (hj : i.1 ≠ 0) :
    radialEigen K i.1 * ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (wr K p : ℂ) * gradMode m n G a 0 p * ((br K B i p : ℝ) : ℂ)‖ ^ 2 := by
  unfold br
  rw [int_scale K (wr K) (fun p => rd B i.1 p.1 * B.heightPoly i.2 p.2) (gradMode m n G a 0)]
  exact term_eq _ (radialEigen_pos hK.r_order.2 hj) _ _ (vel_radial hK hB modeRadialWeak hs n a i.1 i.2 hj)

theorem height_term {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    {i : ℕ × ℕ} (hl : i.2 ≠ 0) :
    heightEigen K i.2 * ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (wz K p : ℂ) * gradMode m n G a 2 p * ((bz K B i p : ℝ) : ℂ)‖ ^ 2 := by
  unfold bz
  rw [int_scale K (wz K) (fun p => B.radialPoly i.1 p.1 * hd B i.2 p.2) (gradMode m n G a 2)]
  exact term_eq _ (heightEigen_pos hK.z_order.2 hl) _ _
    (vel_height hK hB CellFormula.heightModeIbp_holds hs n a i.1 i.2 hl)

theorem radial_fin {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    {Q : ℕ} (hQ : 1 ≤ Q) (T U : Finset (ℕ × ℕ)) (hT : ∀ i ∈ T, Q ≤ i.1) (hU : ∀ u ∈ U, u.1 + 2 ≤ Q) :
    ∑ i ∈ T, radialEigen K i.1 * ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2
      + ∑ u ∈ U, ‖B.coef K (gradMode m n G a 0) u.1 u.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode m n G a 0 p‖ ^ 2 := by
  obtain ⟨hF, hF2⟩ := modeGradSquare K hK m v G H hs n a 0
  have h := proj_coef_le hB (wr K) (wr_cont K) (wr_nonneg hK) wr_le (br K B) (br_cont K B) _ hF hF2 T U
    (fun i hi i' hi' => br_orth hK hB (by have := hT i hi; omega) (by have := hT i' hi'; omega))
    (fun u hu i hi => br_zero hK hB (by have := hU u hu; have := hT i hi; omega))
  rw [Finset.sum_congr rfl fun i hi => radial_term hK hB hs n a (i := i) (by have := hT i hi; omega)]
  exact h

theorem height_fin {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    {Q : ℕ} (hQ : 1 ≤ Q) (T U : Finset (ℕ × ℕ)) (hT : ∀ i ∈ T, i.1 < Q ∧ Q ≤ i.2)
    (hU : ∀ u ∈ U, Q ≤ u.1 ∨ u.2 + 2 ≤ Q) :
    ∑ i ∈ T, heightEigen K i.2 * ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2
      + ∑ u ∈ U, ‖B.coef K (gradMode m n G a 2) u.1 u.2‖ ^ 2
      ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖gradMode m n G a 2 p‖ ^ 2 := by
  obtain ⟨hF, hF2⟩ := modeGradSquare K hK m v G H hs n a 2
  have h := proj_coef_le hB (wz K) (wz_cont K) (wz_nonneg hK) wz_le (bz K B) (bz_cont K B) _ hF hF2 T U
    (fun i hi i' hi' => bz_orth hK hB (by have := (hT i hi).2; omega) (by have := (hT i' hi').2; omega))
    (fun u hu i hi => bz_zero hK hB (by
      have h1 := hT i hi
      rcases hU u hu with h2 | h2
      · left; omega
      · right; omega))
  rw [Finset.sum_congr rfl fun i hi => height_term hK hB hs n a (i := i) (by have := (hT i hi).2; omega)]
  exact h

theorem coef_hasSum {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    HasSum (fun i : ℕ × ℕ => ‖B.coef K F i.1 i.2‖ ^ 2) (∫ p in K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2) := by
  have h := basisEnergySum_holds K B hK hB Unit (fun _ => F) (fun _ => F) (fun _ => ⟨hF, hF2⟩) (fun _ => ⟨hF, hF2⟩)
  simp only [Finset.univ_unique, Finset.sum_singleton] at h
  have e1 : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have e2 : (∫ p in K.rect, ((K.lineWeight p.1 : ℝ) : ℂ) * (F p * (starRingEnd ℂ) (F p)))
      = (((∫ p in K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2) : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext p
    rw [e1]; push_cast; ring
  rw [e2] at h
  simp only [e1] at h
  exact Complex.hasSum_ofReal.1 h

theorem tail_le (f : ℕ × ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (S : ℝ) (hS : HasSum f S) (A : ℕ × ℕ → Prop)
    [DecidablePred A] (X : ℝ) (h : ∀ U : Finset (ℕ × ℕ), (∀ u ∈ U, ¬ A u) → X + ∑ u ∈ U, f u ≤ S) :
    X ≤ ∑' i, if A i then f i else 0 := by
  have hs1 : Summable (fun i => if A i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [hf0 i, le_rfl])
      (fun i => by split_ifs; exacts [le_rfl, hf0 i]) hS.summable
  have hs2 : Summable (fun i => if A i then 0 else f i) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [le_rfl, hf0 i])
      (fun i => by split_ifs; exacts [hf0 i, le_rfl]) hS.summable
  have hsum : (∑' i, if A i then f i else 0) + (∑' i, if A i then 0 else f i) = S := by
    rw [← hs1.tsum_add hs2, ← hS.tsum_eq]
    congr 1; funext i; split_ifs <;> simp
  have hle : (∑' i, if A i then 0 else f i) ≤ S - X := by
    refine hs2.tsum_le_of_sum_le fun U => ?_
    have h1 := h (U.filter fun u => ¬ A u) (fun u hu => (Finset.mem_filter.1 hu).2)
    rw [Finset.sum_filter] at h1
    have e : ∑ i ∈ U, (if A i then 0 else f i) = ∑ i ∈ U, (if ¬ A i then f i else 0) :=
      Finset.sum_congr rfl fun i _ => by by_cases hA : A i <;> simp [hA]
    linarith
  linarith

theorem split_le (f : ℕ × ℕ → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf : Summable f) (A C : ℕ × ℕ → Prop)
    [DecidablePred A] [DecidablePred C] (s : Finset (ℕ × ℕ)) (h : ∀ i, A i → i ∈ s ∨ C i) :
    (∑' i, if A i then f i else 0) ≤ ∑ i ∈ s, f i + ∑' i, if C i then f i else 0 := by
  have hs1 : Summable (fun i => if i ∈ s then f i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [hf0 i, le_rfl])
      (fun i => by split_ifs; exacts [le_rfl, hf0 i]) hf
  have hs2 : Summable (fun i => if C i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [hf0 i, le_rfl])
      (fun i => by split_ifs; exacts [le_rfl, hf0 i]) hf
  have hs0 : Summable (fun i => if A i then f i else 0) :=
    Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [hf0 i, le_rfl])
      (fun i => by split_ifs; exacts [le_rfl, hf0 i]) hf
  have e : (∑' i, if i ∈ s then f i else 0) = ∑ i ∈ s, f i := by
    rw [tsum_eq_sum (s := s) (fun i hi => if_neg hi)]
    exact Finset.sum_congr rfl fun i hi => if_pos hi
  rw [← e, ← hs1.tsum_add hs2]
  refine hs0.tsum_le_tsum (fun i => ?_) (hs1.add hs2)
  by_cases hA : A i
  · rw [if_pos hA]
    rcases h i hA with h1 | h1
    · rw [if_pos h1]; split_ifs <;> linarith [hf0 i]
    · rw [if_pos h1]; split_ifs <;> linarith [hf0 i]
  · rw [if_neg hA]
    split_ifs <;> linarith [hf0 i]

theorem range_split (F : ℕ → ℝ) {d N : ℕ} (h : d ≤ N) :
    ∑ j ∈ Finset.range N, F j = ∑ j ∈ Finset.range d, F j + ∑ j ∈ Finset.range N, if d ≤ j then F j else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_range_add_sum_Ico F h]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j; simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]; omega

theorem top_eq {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (gr gz : ℝ × ℝ → ℂ)
    (hr : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gr p) K.rect)
    (hz : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gz p) K.rect) {Q : ℕ} (hQ : 2 ≤ Q) :
    K.topPart Q gr gz
      = ∑ i ∈ ((Finset.range (Q + 1)).filter (fun j => Q - 1 ≤ j)) ×ˢ Finset.range (Q + 1), ‖B.coef K gr i.1 i.2‖ ^ 2
        + ∑ i ∈ Finset.range Q ×ˢ ((Finset.range (Q + 1)).filter (fun l => Q - 1 ≤ l)),
            ‖B.coef K gz i.1 i.2‖ ^ 2 := by
  rw [CellBox.topPart, CellEnergy.TopFormInternal.normSq_proj K hB hr Q Q,
    CellEnergy.TopFormInternal.normSq_proj K hB hr (Q - 2) Q,
    CellEnergy.TopFormInternal.normSq_proj K hB hz (Q - 1) Q,
    CellEnergy.TopFormInternal.normSq_proj K hB hz (Q - 1) (Q - 2),
    Finset.sum_product, Finset.sum_product, Finset.sum_filter]
  have e1 : Q - 2 + 1 = Q - 1 := by omega
  have e2 : Q - 1 + 1 = Q := by omega
  rw [e1, e2, range_split (fun j => ∑ l ∈ Finset.range (Q + 1), ‖B.coef K gr j l‖ ^ 2) (d := Q - 1) (N := Q + 1)
    (by omega), ← Finset.sum_sub_distrib]
  congr 1
  · ring
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_filter, range_split (fun l => ‖B.coef K gz j l‖ ^ 2) (d := Q - 1) (N := Q + 1) (by omega)]
    ring

theorem top_bound {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (gr gz : ℝ × ℝ → ℂ)
    (hr : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gr p) K.rect)
    (hz : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gz p) K.rect)
    (sr : Summable (fun i : ℕ × ℕ => ‖B.coef K gr i.1 i.2‖ ^ 2))
    (sz : Summable (fun i : ℕ × ℕ => ‖B.coef K gz i.1 i.2‖ ^ 2)) {Q : ℕ} (hQ : 2 ≤ Q) :
    (∑' i : ℕ × ℕ, if Q ≤ i.1 + 1 then ‖B.coef K gr i.1 i.2‖ ^ 2 else 0)
        + (∑' i : ℕ × ℕ, if i.1 < Q ∧ Q ≤ i.2 + 1 then ‖B.coef K gz i.1 i.2‖ ^ 2 else 0)
      ≤ K.topPart Q gr gz + ((∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K gr i.1 i.2‖ ^ 2 else 0)
        + ∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K gz i.1 i.2‖ ^ 2 else 0) := by
  rw [top_eq hB gr gz hr hz hQ]
  have h1 := split_le (fun i : ℕ × ℕ => ‖B.coef K gr i.1 i.2‖ ^ 2) (fun _ => sq_nonneg _) sr
    (fun i => Q ≤ i.1 + 1) (fun i => Q < max i.1 i.2)
    (((Finset.range (Q + 1)).filter (fun j => Q - 1 ≤ j)) ×ˢ Finset.range (Q + 1)) (by
      intro i hi
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, lt_max_iff]
      omega)
  have h2 := split_le (fun i : ℕ × ℕ => ‖B.coef K gz i.1 i.2‖ ^ 2) (fun _ => sq_nonneg _) sz
    (fun i => i.1 < Q ∧ Q ≤ i.2 + 1) (fun i => Q < max i.1 i.2)
    (Finset.range Q ×ˢ ((Finset.range (Q + 1)).filter (fun l => Q - 1 ≤ l))) (by
      intro i hi
      simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_range, lt_max_iff]
      omega)
  linarith

theorem sym_anti (Y : Fin 3 → Fin 3 → ℂ) : symSq Y + antiSq Y = sumSq Y := by
  rw [← swap_avg]
  unfold symSq antiSq
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [norm_div, norm_div, Complex.norm_two, div_pow, div_pow, norm_add_sq_real, norm_sub_sq_real]
  ring

theorem fin_bound {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ)
    {Q : ℕ} (hQ : 1 ≤ Q) (T : Finset (ℕ × ℕ)) :
    ∑ i ∈ T, (if Q ≤ max i.1 i.2 then (if Q ≤ i.1 then radialEigen K i.1 else heightEigen K i.2)
        * ∑ a : Fin 3, ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 else 0)
      ≤ ∑ a : Fin 3, ((∑' i : ℕ × ℕ, if Q ≤ i.1 + 1 then ‖B.coef K (gradMode m n G a 0) i.1 i.2‖ ^ 2 else 0)
        + ∑' i : ℕ × ℕ, if i.1 < Q ∧ Q ≤ i.2 + 1 then ‖B.coef K (gradMode m n G a 2) i.1 i.2‖ ^ 2 else 0) := by
  have e : ∀ i : ℕ × ℕ, (if Q ≤ max i.1 i.2 then (if Q ≤ i.1 then radialEigen K i.1 else heightEigen K i.2)
        * ∑ a : Fin 3, ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 else 0)
      = ∑ a : Fin 3, ((if Q ≤ i.1 then radialEigen K i.1 *
            ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 else 0)
        + (if i.1 < Q ∧ Q ≤ i.2 then heightEigen K i.2 *
            ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 else 0)) := by
    intro i
    by_cases h1 : Q ≤ i.1
    · rw [if_pos (le_max_of_le_left h1), if_pos h1, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [if_pos h1, if_neg (by omega), add_zero]
    · by_cases h2 : Q ≤ i.2
      · rw [if_pos (le_max_of_le_right h2), if_neg h1, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [if_neg h1, if_pos ⟨by omega, h2⟩, zero_add]
      · rw [if_neg (by rw [le_max_iff]; omega)]
        refine (Finset.sum_eq_zero fun a _ => ?_).symm
        rw [if_neg h1, if_neg (by omega), add_zero]
  rw [Finset.sum_congr rfl fun i _ => e i, Finset.sum_comm]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
  obtain ⟨hr0, hr2⟩ := modeGradSquare K hK m v G H hs n a 0
  obtain ⟨hz0, hz2⟩ := modeGradSquare K hK m v G H hs n a 2
  refine add_le_add ?_ ?_
  · refine tail_le _ (fun _ => sq_nonneg _) _ (coef_hasSum hK hB _ hr0 hr2) (fun i => Q ≤ i.1 + 1) _
      fun U hU => ?_
    exact radial_fin hK hB hs n a hQ _ U (fun i hi => (Finset.mem_filter.1 hi).2)
      (fun u hu => by have := hU u hu; omega)
  · refine tail_le _ (fun _ => sq_nonneg _) _ (coef_hasSum hK hB _ hz0 hz2)
      (fun i => i.1 < Q ∧ Q ≤ i.2 + 1) _ fun U hU => ?_
    exact height_fin hK hB hs n a hQ _ U (fun i hi => (Finset.mem_filter.1 hi).2)
      (fun u hu => by have := hU u hu; omega)

theorem vel_summ {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (Q : ℕ) :
    Summable (fun i : ℕ × ℕ => if Q ≤ max i.1 i.2 then (if Q ≤ i.1 then radialEigen K i.1 else heightEigen K i.2)
        * ∑ a : Fin 3, ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 else 0) := by
  have hs3 : Summable (fun i : ℕ × ℕ => ∑ a : Fin 3, (1 + (radialEigen K i.1 + heightEigen K i.2)) *
      ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2) :=
    summable_sum fun a _ => vel_tail hK hB modeRadialWeak CellFormula.heightModeIbp_holds hs n a
  refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hs3
  · have hl := radialEigen_nonneg (K := K) i.1
    have hm := heightEigen_nonneg (K := K) i.2
    have hX : 0 ≤ ∑ a : Fin 3, ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    split_ifs
    · exact mul_nonneg hl hX
    · exact mul_nonneg hm hX
    · exact le_rfl
  · rw [← Finset.mul_sum]
    have hl := radialEigen_nonneg (K := K) i.1
    have hm := heightEigen_nonneg (K := K) i.2
    have hX : 0 ≤ ∑ a : Fin 3, ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) i.1 i.2‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    split_ifs
    · exact mul_le_mul_of_nonneg_right (by linarith) hX
    · exact mul_le_mul_of_nonneg_right (by linarith) hX
    · exact mul_nonneg (by linarith) hX

theorem strain_bound {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (Q : ℕ)
    (P : ℕ × ℕ → Prop) [DecidablePred P] (hP : ∀ i, P i ↔ Q < max i.1 i.2) :
    ∑ a : Fin 3, ((∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 0) i.1 i.2‖ ^ 2 else 0)
        + ∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 2) i.1 i.2‖ ^ 2 else 0)
      ≤ ∑' i : ℕ × ℕ, if P i then symSq (fun a b => B.coef K (gradMode m n G a b) i.1 i.2)
          + antiSq (fun a b => B.coef K (gradMode m n G a b) i.1 i.2) else 0 := by
  have sc : ∀ a b, Summable (fun i : ℕ × ℕ => ‖B.coef K (gradMode m n G a b) i.1 i.2‖ ^ 2) := fun a b => by
    obtain ⟨h1, h2⟩ := modeGradSquare K hK m v G H hs n a b
    exact coef_summable hB _ h1 h2
  have si : ∀ a b, Summable (fun i : ℕ × ℕ =>
      if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a b) i.1 i.2‖ ^ 2 else 0) :=
    fun a b => Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [sq_nonneg _, le_rfl])
      (fun i => by split_ifs; exacts [le_rfl, sq_nonneg _]) (sc a b)
  have sS : Summable (fun i : ℕ × ℕ => if P i then symSq (fun a b => B.coef K (gradMode m n G a b) i.1 i.2)
          + antiSq (fun a b => B.coef K (gradMode m n G a b) i.1 i.2) else 0) := by
    have hsb : Summable (fun i : ℕ × ℕ => ∑ a : Fin 3, ∑ b : Fin 3, ‖B.coef K (gradMode m n G a b) i.1 i.2‖ ^ 2) :=
      summable_sum fun a _ => summable_sum fun b _ => sc a b
    refine Summable.of_nonneg_of_le (fun i => ?_) (fun i => ?_) hsb
    · split_ifs
      · exact add_nonneg (symSq_nonneg' _) (antiSq_nonneg' _)
      · exact le_rfl
    · split_ifs
      · rw [sym_anti]; exact le_rfl
      · exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∑ a : Fin 3, ((∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 0) i.1 i.2‖ ^ 2 else 0)
        + ∑' i : ℕ × ℕ, if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 2) i.1 i.2‖ ^ 2 else 0)
      = ∑' i : ℕ × ℕ, ∑ a : Fin 3, ((if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 0) i.1 i.2‖ ^ 2 else 0)
        + if Q < max i.1 i.2 then ‖B.coef K (gradMode m n G a 2) i.1 i.2‖ ^ 2 else 0) := by
    rw [Summable.tsum_finsetSum (fun a _ => (si a 0).add (si a 2))]
    exact Finset.sum_congr rfl fun a _ => ((si a 0).tsum_add (si a 2)).symm
  rw [e]
  refine Summable.tsum_le_tsum (fun i => ?_) (summable_sum fun a _ => (si a 0).add (si a 2)) sS
  by_cases h : Q < max i.1 i.2
  · rw [if_pos ((hP i).2 h), sym_anti]
    simp only [if_pos h]
    unfold sumSq
    refine Finset.sum_le_sum fun a _ => ?_
    rw [Fin.sum_univ_three]
    have := sq_nonneg ‖B.coef K (gradMode m n G a 1) i.1 i.2‖
    linarith
  · rw [if_neg (fun h' => h ((hP i).1 h'))]
    simp [h]

end SharpEnergyVelocityCoefInternal

open SharpEnergyVelocityCoefInternal SharpEnergyTailParts in
open Classical in
theorem modeVelocityCoef_holds : ModeVelocityCoefStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hw x hx n hn
  have hK := hd.box
  have hB := hd.bases
  have hs := hx.1
  have hQ : 5 ≤ S.degHigh := by
    have := hd.scalars.degrees
    omega
  have hsum := vel_summ hK hB hs n S.degHigh
  refine ⟨hsum, ?_⟩
  refine (hsum.tsum_le_of_sum_le fun T => fin_bound hK hB hs n (by omega) T).trans ?_
  have gi : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode c.order n x.2.1 a b p) K.rect :=
    fun a b => LowEntry.Internal.gradMode_int K hK c.order n hs.measurable_gradient hs.gradient_two a b
  have sc : ∀ a b, Summable (fun i : ℕ × ℕ => ‖B.coef K (gradMode c.order n x.2.1 a b) i.1 i.2‖ ^ 2) :=
    fun a b => by
      obtain ⟨h1, h2⟩ := modeGradSquare K hK c.order x.1 x.2.1 x.2.2.1 hs n a b
      exact CellSharpBoundInternal.coef_summable hB _ h1 h2
  have ht : ∀ a : Fin 3, _ := fun a => top_bound hB (gradMode c.order n x.2.1 a 0) (gradMode c.order n x.2.1 a 2)
    (gi a 0) (gi a 2) (sc a 0) (sc a 2) (Q := S.degHigh) (by omega)
  have hst := strain_bound hK hB hs n S.degHigh (strainIdx S n) (fun i => by simp [strainIdx, hn])
  calc _ ≤ ∑ a : Fin 3, (K.topPart S.degHigh (gradMode c.order n x.2.1 a 0) (gradMode c.order n x.2.1 a 2)
          + ((∑' i : ℕ × ℕ, if S.degHigh < max i.1 i.2 then
                ‖B.coef K (gradMode c.order n x.2.1 a 0) i.1 i.2‖ ^ 2 else 0)
            + ∑' i : ℕ × ℕ, if S.degHigh < max i.1 i.2 then
                ‖B.coef K (gradMode c.order n x.2.1 a 2) i.1 i.2‖ ^ 2 else 0)) :=
        Finset.sum_le_sum fun a _ => ht a
    _ = _ := Finset.sum_add_distrib
    _ ≤ _ := add_le_add (le_refl _) hst


end Breakdown.CellCert.CellAnalysis

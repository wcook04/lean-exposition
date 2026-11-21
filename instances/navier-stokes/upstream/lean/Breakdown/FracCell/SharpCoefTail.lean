import Breakdown.FracCell.CellSharpBound
import Breakdown.FracCell.RelRadialCoef
import Breakdown.FracCell.RelHeightCoef
import Breakdown.FracCell.SharpCoreSt
import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.FracCell.ModeRadialWeak
import Breakdown.FracCell.StHeightModeIbp
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare

open MeasureTheory Polynomial

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

namespace SharpCoefTailInternal

open CellSharpBoundInternal SteadyCert Assembly

def rd (B : CellBases) (j : ℕ) (r : ℝ) : ℝ :=
  (derivative (CellFormula.Internal.RelRadialCoef.poly B j)).eval r

def hd (B : CellBases) (l : ℕ) (z : ℝ) : ℝ :=
  (derivative (CellFormula.Internal.RelHeightCoef.hp B.heightCoef l)).eval z

lemma rd_cont (B : CellBases) (j : ℕ) : Continuous (rd B j) := Polynomial.continuous _

lemma hd_cont (B : CellBases) (l : ℕ) : Continuous (hd B l) := Polynomial.continuous _

lemma refR_sq_le {K : CellBox} (hK : K.r₁ < K.r₂) {r : ℝ} (h1 : K.r₁ ≤ r) (h2 : r ≤ K.r₂) :
    0 ≤ 1 - K.refR r ^ 2 := by
  have a : K.refR r ≤ 1 := by
    rw [CellBox.refR, div_le_one (by linarith)]; linarith
  have b : -1 ≤ K.refR r := by
    rw [CellBox.refR, le_div_iff₀ (by linarith)]; linarith
  nlinarith

lemma refZ_sq_le {K : CellBox} (hK : K.z₁ < K.z₂) {z : ℝ} (h1 : K.z₁ ≤ z) (h2 : z ≤ K.z₂) :
    0 ≤ 1 - K.refZ z ^ 2 := by
  have a : K.refZ z ≤ 1 := by
    rw [CellBox.refZ, div_le_one (by linarith)]; linarith
  have b : -1 ≤ K.refZ z := by
    rw [CellBox.refZ, le_div_iff₀ (by linarith)]; linarith
  nlinarith

lemma radialEigen_nonneg {K : CellBox} (j : ℕ) : 0 ≤ radialEigen K j := by
  unfold radialEigen; split_ifs <;> positivity

lemma heightEigen_nonneg {K : CellBox} (l : ℕ) : 0 ≤ heightEigen K l := by
  unfold heightEigen; positivity

lemma radialEigen_pos {K : CellBox} (hK : K.r₁ < K.r₂) {j : ℕ} (hj : j ≠ 0) : 0 < radialEigen K j := by
  have h1 : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hj
  have h2 : 0 < K.r₂ - K.r₁ := sub_pos.2 hK
  unfold radialEigen; split_ifs <;> positivity

lemma heightEigen_pos {K : CellBox} (hK : K.z₁ < K.z₂) {l : ℕ} (hl : l ≠ 0) : 0 < heightEigen K l := by
  have h1 : (1 : ℝ) ≤ l := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hl
  have h2 : 0 < K.z₂ - K.z₁ := sub_pos.2 hK
  unfold heightEigen; positivity

lemma icc_interval (f : ℝ → ℝ) {a b : ℝ} (h : a ≤ b) :
    ∫ r in Set.Icc a b, f r = ∫ r in a..b, f r := by
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le h]

lemma rad_orth {K : CellBox} {B : CellBases} (hK : K.r₁ < K.r₂) (hB : IsCellBases K B) (i j : ℕ) :
    ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B i r * rd B j r =
      if i = j then radialEigen K j else 0 := by
  open CellFormula.Internal.RelRadialCoef in
  have hlead : ∀ j, B.radialCoef j j ≠ 0 := fun j => (hB.radial_leading j).ne'
  have horth : ∀ j j', ip K (poly B j) (poly B j') = if j = j' then 1 else 0 := by
    intro j j'
    unfold ip
    rw [← hB.radial_orthonormal j j']
    congr 1; funext r
    simp only [eval_mul, wpoly_eval, poly_eval]
  have e1 : ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * (1 - K.refR r ^ 2) * rd B i r * rd B j r =
      -ip K (F B K j) (poly B i) := by
    rw [ip_F B K hK i j, neg_neg, icc_interval _ hK.le]
    congr 1; funext r
    simp only [rd, Wp, eval_mul, eval_sub, eval_one, eval_pow, wpoly_eval, rho_eval]
  rw [e1]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have h0 : derivative (poly B 0) = 0 := by
      apply derivative_of_natDegree_zero
      have := poly_natDegree B 0
      omega
    rw [ip_F B K hK i 0, h0]
    have : radialEigen K 0 = 0 := by unfold radialEigen; split_ifs <;> simp
    simp [this]
  · rw [eigen B K hlead horth hK j hj.ne']
    have hs : ip K (C (-radialEigen K j) * poly B j) (poly B i) = -radialEigen K j * ip K (poly B j) (poly B i) := by
      have := ip_sum K {0} (fun _ => -radialEigen K j) (fun _ => poly B j) (poly B i)
      simpa using this
    rw [hs, horth]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring

lemma ht_orth {K : CellBox} {B : CellBases} (hK : K.z₁ < K.z₂) (hB : IsCellBases K B) (i l : ℕ) :
    ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * hd B i z * hd B l z =
      if i = l then heightEigen K l else 0 := by
  open CellFormula.Internal.RelHeightCoef in
  have hpe : ∀ l z, (hp B.heightCoef l).eval z = B.heightPoly l z := by
    intro l z; rw [hp_eval]; rfl
  have hlead : ∀ l, B.heightCoef l l ≠ 0 := fun l => (hB.height_leading l).ne'
  have horth : ∀ l l', ∫ z in K.z₁..K.z₂, (hp B.heightCoef l).eval z * (hp B.heightCoef l').eval z =
      if l = l' then 1 else 0 := by
    intro l l'
    rw [← hB.height_orthonormal l l', icc_interval _ hK.le]
    simp only [hpe]
  have e1 : ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * hd B i z * hd B l z =
      ∫ z in K.z₁..K.z₂, (gp B.heightCoef K.z₁ K.z₂ l).eval z * (derivative (hp B.heightCoef i)).eval z := by
    rw [icc_interval _ hK.le]
    congr 1; funext z
    simp only [hd, gp, eval_mul, zp_eval, CellBox.refZ]
    ring
  rw [e1, ibp (z₁ := K.z₁) (z₂ := K.z₂) _ _ (by simp [gp, zp_left hK]) (by simp [gp, zp_right hK])]
  rcases Nat.eq_zero_or_pos l with rfl | hl
  · have h0 : derivative (hp B.heightCoef 0) = 0 := by
      apply derivative_of_natDegree_zero
      have := hp_natDegree B.heightCoef 0
      omega
    have : heightEigen K 0 = 0 := by unfold heightEigen; simp
    simp [gp, h0, this]
  · have e2 : ∀ z, (derivative (gp B.heightCoef K.z₁ K.z₂ l)).eval z * (hp B.heightCoef i).eval z =
        -(heightEigen K l * ((hp B.heightCoef l).eval z * (hp B.heightCoef i).eval z)) := by
      intro z
      have h := tp_eigen hlead horth hK hl z
      simp only [tp, eval_neg] at h
      unfold heightEigen
      linear_combination (hp B.heightCoef i).eval z * (-h)
    simp_rw [e2]
    rw [intervalIntegral.integral_neg, neg_neg, intervalIntegral.integral_const_mul, horth]
    split_ifs with h1 h2 h2
    · ring
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring

lemma wbb_int' (K : CellBox) (W : ℝ × ℝ → ℝ) (hW : Continuous W) (b : ℕ × ℕ → ℝ × ℝ → ℝ)
    (hb : ∀ i, Continuous (b i)) (i i' : ℕ × ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => W p * b i p * b i' p) K.rect :=
  ((hW.mul (hb i)).mul (hb i')).continuousOn.integrableOn_compact (rect_cpt K)

lemma g_int' (K : CellBox) (W : ℝ × ℝ → ℝ) (hW : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (b : ℕ × ℕ → ℝ × ℝ → ℝ) (hb : ∀ i, Continuous (b i)) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => W p * ‖F p‖ ^ 2) K.rect) (i : ℕ × ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (W p : ℂ) * F p * ((b i p : ℝ) : ℂ)) K.rect := by
  have hbb := wbb_int' K W hW b hb i i
  refine Integrable.mono' (hF2.add hbb) ?_ ?_
  · exact (((Complex.continuous_ofReal.comp hW).aestronglyMeasurable).mul hF).mul
      (Complex.continuous_ofReal.comp (hb i)).aestronglyMeasurable
  · refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have hw := hW0 p hp
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hw, Real.norm_eq_abs]
    have h1 := norm_nonneg (F p)
    have h2 := abs_nonneg (b i p)
    have h3 : b i p * b i p = |b i p| ^ 2 := by rw [sq_abs]; ring
    simp only [Pi.add_apply]
    nlinarith [mul_nonneg hw (sq_nonneg (‖F p‖ - |b i p|))]

lemma sq_coef_le (K : CellBox) (W : ℝ × ℝ → ℝ) (hW : Continuous W) (hW0 : ∀ p ∈ K.rect, 0 ≤ W p)
    (b : ℕ × ℕ → ℝ × ℝ → ℝ) (hb : ∀ i, Continuous (b i)) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => W p * ‖F p‖ ^ 2) K.rect) (T : Finset (ℕ × ℕ))
    (horth : ∀ i ∈ T, ∀ i' ∈ T, ∫ p in K.rect, W p * b i p * b i' p = if i = i' then 1 else 0) :
    ∑ i ∈ T, ‖∫ p in K.rect, (W p : ℂ) * F p * ((b i p : ℝ) : ℂ)‖ ^ 2 ≤ ∫ p in K.rect, W p * ‖F p‖ ^ 2 := by
  set c : ℕ × ℕ → ℂ := fun i => ∫ p in K.rect, (W p : ℂ) * F p * ((b i p : ℝ) : ℂ) with hc
  have hg := g_int' K W hW hW0 b hb F hF hF2
  have hcg : ∀ i, c i = ∫ p in K.rect, (W p : ℂ) * F p * ((b i p : ℝ) : ℂ) := fun i => rfl
  have h0 : 0 ≤ ∫ p in K.rect, W p * ‖F p - ∑ i ∈ T, c i * ((b i p : ℝ) : ℂ)‖ ^ 2 :=
    setIntegral_nonneg (rect_meas K) fun p hp => mul_nonneg (hW0 p hp) (sq_nonneg _)
  have h0' : 0 ≤ ∫ p in K.rect, (W p * ‖F p‖ ^ 2
      - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((W p : ℂ) * F p * ((b i p : ℝ) : ℂ))).re
      + ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (W p * b i p * b i' p)) :=
    h0.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun p =>
      pt_id (W p) (F p) T c (fun i => b i p)))
  have iA : ∀ i ∈ T, Integrable (fun p => ((starRingEnd ℂ) (c i) *
      ((W p : ℂ) * F p * ((b i p : ℝ) : ℂ))).re) (volume.restrict K.rect) :=
    fun i _ => ((hg i).const_mul _).re
  have iB : ∀ i ∈ T, ∀ i' ∈ T, Integrable (fun p => (c i * (starRingEnd ℂ) (c i')).re *
      (W p * b i p * b i' p)) (volume.restrict K.rect) :=
    fun i _ i' _ => (wbb_int' K W hW b hb i i').const_mul _
  have iB' : ∀ i ∈ T, Integrable (fun p => ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re *
      (W p * b i p * b i' p)) (volume.restrict K.rect) :=
    fun i hi => integrable_finsetSum _ (iB i hi)
  have iA2 := (integrable_finsetSum T iA).const_mul 2
  have hsub : Integrable (fun p => W p * ‖F p‖ ^ 2
      - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((W p : ℂ) * F p * ((b i p : ℝ) : ℂ))).re)
      (volume.restrict K.rect) := hF2.sub iA2
  rw [integral_add hsub (integrable_finsetSum _ iB'), integral_sub hF2 iA2, integral_const_mul,
    integral_finsetSum _ iA, integral_finsetSum _ iB'] at h0'
  have eA : ∀ i, ∫ p in K.rect, ((starRingEnd ℂ) (c i) *
      ((W p : ℂ) * F p * ((b i p : ℝ) : ℂ))).re = ‖c i‖ ^ 2 := by
    intro i
    have h := integral_re (𝕜 := ℂ) ((hg i).const_mul ((starRingEnd ℂ) (c i)))
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul, ← hcg, sqn, mul_comm]
  have eB : ∀ i ∈ T, ∫ p in K.rect, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re *
      (W p * b i p * b i' p) = ‖c i‖ ^ 2 := by
    intro i hi
    rw [integral_finsetSum _ (iB i hi)]
    rw [Finset.sum_congr rfl (fun i' hi' => by rw [integral_const_mul, horth i hi i' hi'])]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq T i, if_pos hi, sqn]
  rw [Finset.sum_congr rfl eB] at h0'
  simp only [eA] at h0'
  linarith

lemma term_eq (lam : ℝ) (hl : 0 < lam) (c I : ℂ) (h : (lam : ℂ) * c = I) :
    lam * ‖c‖ ^ 2 = ‖I * ((1 / Real.sqrt lam : ℝ) : ℂ)‖ ^ 2 := by
  have hs : 0 < Real.sqrt lam := Real.sqrt_pos.2 hl
  have hss : Real.sqrt lam ^ 2 = lam := Real.sq_sqrt hl.le
  rw [← h, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hl.le,
    Real.norm_of_nonneg (by positivity)]
  rw [mul_pow, mul_pow, div_pow, hss]
  field_simp

lemma int_scale (K : CellBox) (W x : ℝ × ℝ → ℝ) (F : ℝ × ℝ → ℂ) (s : ℝ) :
    ∫ p in K.rect, (W p : ℂ) * F p * ((x p / s : ℝ) : ℂ)
      = (∫ p in K.rect, (W p : ℂ) * F p * ((x p : ℝ) : ℂ)) * ((1 / s : ℝ) : ℂ) := by
  rw [← integral_mul_const]
  congr 1; funext p
  push_cast; ring

lemma refR_cont (K : CellBox) : Continuous K.refR := by unfold CellBox.refR; fun_prop

lemma refZ_cont (K : CellBox) : Continuous K.refZ := by unfold CellBox.refZ; fun_prop

lemma tail_radial {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr : ℝ × ℝ → ℂ)
    (hFr : AEStronglyMeasurable Fr (volume.restrict K.rect))
    (hFr2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2) K.rect)
    (hR : ∀ j l, j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :
    Summable (fun jl : ℕ × ℕ => radialEigen K jl.1 * ‖B.coef K F jl.1 jl.2‖ ^ 2) := by
  have hr := hK.r_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refR_sq_le hr hp.1.1 hp.1.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => rd B i.1 p.1 * B.heightPoly i.2 p.2 / Real.sqrt (radialEigen K i.1)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rd_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)).div_const _
  refine summable_of_sum_le (fun jl => mul_nonneg (radialEigen_nonneg _) (sq_nonneg _)) (c := ∫ p in K.rect, W p * ‖Fr p‖ ^ 2) ?_
  intro T
  set T' := T.filter (fun i => i.1 ≠ 0)
  have e1 : ∑ i ∈ T, radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ∑ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne fun i _ hne => ?_).symm
    intro h0
    apply hne
    have : radialEigen K 0 = 0 := by unfold radialEigen; split_ifs <;> simp
    rw [h0, this, zero_mul]
  have e2 : ∀ i ∈ T', radialEigen K i.1 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fr p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => rd B i.1 p.1 * B.heightPoly i.2 p.2) Fr]
    exact term_eq _ (radialEigen_pos hr hj) _ _ (hR i.1 i.2 hj)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fr hFr hFr2 T' ?_
  intro i hi i' hi'
  have hj : i.1 ≠ 0 := (Finset.mem_filter.1 hi).2
  have hj' : i'.1 ≠ 0 := (Finset.mem_filter.1 hi').2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * rd B i.1 p.1 * rd B i'.1 p.1
          / (Real.sqrt (radialEigen K i.1) * Real.sqrt (radialEigen K i'.1)))
        * (B.heightPoly i.2 p.2 * B.heightPoly i'.2 p.2) := by
    intro p; simp only [hWdef, hbdef]; field_simp
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

lemma tail_height {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fz : ℝ × ℝ → ℂ)
    (hFz : AEStronglyMeasurable Fz (volume.restrict K.rect))
    (hFz2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2) K.rect)
    (hZ : ∀ j l, l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)) :
    Summable (fun jl : ℕ × ℕ => heightEigen K jl.2 * ‖B.coef K F jl.1 jl.2‖ ^ 2) := by
  have hz := hK.z_order.2
  set W : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) with hWdef
  have hWc : Continuous W :=
    ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2))
  have hW0 : ∀ p ∈ K.rect, 0 ≤ W p := fun p hp =>
    mul_nonneg (lw_nonneg hp.1.1) (refZ_sq_le hz hp.2.1 hp.2.2)
  set b : ℕ × ℕ → ℝ × ℝ → ℝ := fun i p => B.radialPoly i.1 p.1 * hd B i.2 p.2 / Real.sqrt (heightEigen K i.2)
    with hbdef
  have hbc : ∀ i, Continuous (b i) := fun i =>
    (((rp_cont B _).comp continuous_fst).mul ((hd_cont B _).comp continuous_snd)).div_const _
  refine summable_of_sum_le (fun jl => mul_nonneg (heightEigen_nonneg _) (sq_nonneg _)) (c := ∫ p in K.rect, W p * ‖Fz p‖ ^ 2) ?_
  intro T
  set T' := T.filter (fun i => i.2 ≠ 0)
  have e1 : ∑ i ∈ T, heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ∑ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2 := by
    refine (Finset.sum_filter_of_ne fun i _ hne => ?_).symm
    intro h0
    apply hne
    have : heightEigen K 0 = 0 := by unfold heightEigen; simp
    rw [h0, this, zero_mul]
  have e2 : ∀ i ∈ T', heightEigen K i.2 * ‖B.coef K F i.1 i.2‖ ^ 2
      = ‖∫ p in K.rect, (W p : ℂ) * Fz p * ((b i p : ℝ) : ℂ)‖ ^ 2 := by
    intro i hi
    have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2
    rw [hbdef]
    simp only
    rw [int_scale K W (fun p => B.radialPoly i.1 p.1 * hd B i.2 p.2) Fz]
    exact term_eq _ (heightEigen_pos hz hl) _ _ (hZ i.1 i.2 hl)
  rw [e1, Finset.sum_congr rfl e2]
  refine sq_coef_le K W hWc hW0 b hbc Fz hFz hFz2 T' ?_
  intro i hi i' hi'
  have hl : i.2 ≠ 0 := (Finset.mem_filter.1 hi).2
  have hl' : i'.2 ≠ 0 := (Finset.mem_filter.1 hi').2
  have e : ∀ p : ℝ × ℝ, W p * b i p * b i' p
      = (K.lineWeight p.1 * B.radialPoly i.1 p.1 * B.radialPoly i'.1 p.1)
        * ((1 - K.refZ p.2 ^ 2) * hd B i.2 p.2 * hd B i'.2 p.2
          / (Real.sqrt (heightEigen K i.2) * Real.sqrt (heightEigen K i'.2))) := by
    intro p; simp only [hWdef, hbdef]; field_simp
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

lemma tail_all {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (F Fr Fz : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    (hFr : AEStronglyMeasurable Fr (volume.restrict K.rect))
    (hFr2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) * ‖Fr p‖ ^ 2) K.rect)
    (hR : ∀ j l, j ≠ 0 → ((radialEigen K j : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * Fr p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (hFz : AEStronglyMeasurable Fz (volume.restrict K.rect))
    (hFz2 : IntegrableOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) * ‖Fz p‖ ^ 2) K.rect)
    (hZ : ∀ j l, l ≠ 0 → ((heightEigen K l : ℝ) : ℂ) * B.coef K F j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * Fz p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ)) :
    Summable (fun jl : ℕ × ℕ => (1 + (radialEigen K jl.1 + heightEigen K jl.2)) * ‖B.coef K F jl.1 jl.2‖ ^ 2) := by
  have h := ((coef_summable hB F hF hF2).add (tail_radial hK hB F Fr hFr hFr2 hR)).add
    (tail_height hK hB F Fz hFz hFz2 hZ)
  refine h.congr fun jl => ?_
  ring

lemma pcd (P : ℝ[X]) : ContDiff ℝ 1 (fun x : ℝ => P.eval x) := by
  simpa using Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P 1

lemma rad_ip_orth {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (j j' : ℕ) :
    CellFormula.Internal.RelRadialCoef.ip K (CellFormula.Internal.RelRadialCoef.poly B j)
      (CellFormula.Internal.RelRadialCoef.poly B j') = if j = j' then 1 else 0 := by
  unfold CellFormula.Internal.RelRadialCoef.ip
  rw [← hB.radial_orthonormal j j']
  congr 1; funext r
  simp only [Polynomial.eval_mul, CellFormula.Internal.RelRadialCoef.wpoly_eval,
    CellFormula.Internal.RelRadialCoef.poly_eval]

lemma ht_int_orth {K : CellBox} {B : CellBases} (hK : K.z₁ < K.z₂) (hB : IsCellBases K B) (l l' : ℕ) :
    ∫ z in K.z₁..K.z₂, (CellFormula.Internal.RelHeightCoef.hp B.heightCoef l).eval z *
      (CellFormula.Internal.RelHeightCoef.hp B.heightCoef l').eval z = if l = l' then 1 else 0 := by
  open CellFormula.Internal.RelHeightCoef in
  have hpe : ∀ l z, (hp B.heightCoef l).eval z = B.heightPoly l z := by
    intro l z; rw [hp_eval]; rfl
  rw [← hB.height_orthonormal l l', icc_interval _ hK.le]
  refine intervalIntegral.integral_congr fun z _ => ?_
  exact congrArg₂ (· * ·) (hpe l z) (hpe l' z)

lemma radial_hasDeriv {K : CellBox} {B : CellBases} (hK : K.r₁ < K.r₂) (hB : IsCellBases K B) {j : ℕ}
    (hj : j ≠ 0) (r : ℝ) :
    HasDerivAt (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r)
      (-(radialEigen K j) * K.lineWeight r * B.radialPoly j r) r := by
  open CellFormula.Internal.RelRadialCoef in
  have e : (fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r)
      = fun r => (Wp K * derivative (poly B j)).eval r := by
    funext r; simp only [rd, Wp, eval_mul, eval_sub, eval_one, eval_pow, wpoly_eval, rho_eval]
  rw [e]
  have h := Polynomial.hasDerivAt (Wp K * derivative (poly B j)) r
  rw [← F_spec B K hK j, eigen B K (fun j => (hB.radial_leading j).ne') (rad_ip_orth hB) hK j hj] at h
  refine h.congr_deriv ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, CellFormula.Internal.RelRadialCoef.wpoly_eval,
    CellFormula.Internal.RelRadialCoef.poly_eval]
  ring

lemma height_hasDeriv {K : CellBox} {B : CellBases} (hK : K.z₁ < K.z₂) (hB : IsCellBases K B) {l : ℕ}
    (hl : l ≠ 0) (z : ℝ) :
    HasDerivAt (fun z => (1 - K.refZ z ^ 2) * hd B l z) (-(heightEigen K l) * B.heightPoly l z) z := by
  open CellFormula.Internal.RelHeightCoef in
  have e : (fun z => (1 - K.refZ z ^ 2) * hd B l z) = fun z => (gp B.heightCoef K.z₁ K.z₂ l).eval z := by
    funext z; simp only [hd, gp, eval_mul, zp_eval, CellBox.refZ]
  rw [e]
  have h := Polynomial.hasDerivAt (gp B.heightCoef K.z₁ K.z₂ l) z
  have h2 := tp_eigen (fun l => (hB.height_leading l).ne') (ht_int_orth hK hB) hK (Nat.one_le_iff_ne_zero.2 hl) z
  simp only [tp, eval_neg] at h2
  refine h.congr_deriv ?_
  rw [show B.heightPoly l z = (hp B.heightCoef l).eval z by rw [hp_eval]; rfl]
  unfold heightEigen
  linarith

lemma refR_left (K : CellBox) (hK : K.r₁ < K.r₂) : 1 - K.refR K.r₁ ^ 2 = 0 := by
  have : K.refR K.r₁ = -1 := by
    unfold CellBox.refR; field_simp [(sub_pos.2 hK).ne']; ring
  rw [this]; norm_num

lemma refR_right (K : CellBox) (hK : K.r₁ < K.r₂) : 1 - K.refR K.r₂ ^ 2 = 0 := by
  have : K.refR K.r₂ = 1 := by
    unfold CellBox.refR; field_simp [(sub_pos.2 hK).ne']; ring
  rw [this]; norm_num

lemma refZ_left (K : CellBox) (hK : K.z₁ < K.z₂) : 1 - K.refZ K.z₁ ^ 2 = 0 := by
  have : K.refZ K.z₁ = -1 := by
    unfold CellBox.refZ; field_simp [(sub_pos.2 hK).ne']; ring
  rw [this]; norm_num

lemma refZ_right (K : CellBox) (hK : K.z₁ < K.z₂) : 1 - K.refZ K.z₂ ^ 2 = 0 := by
  have : K.refZ K.z₂ = 1 := by
    unfold CellBox.refZ; field_simp [(sub_pos.2 hK).ne']; ring
  rw [this]; norm_num

lemma radF_cd (K : CellBox) (B : CellBases) (j : ℕ) : ContDiff ℝ 1 (fun r => (1 - K.refR r ^ 2) * rd B j r) := by
  have h1 : ContDiff ℝ 1 (fun r => 1 - K.refR r ^ 2) := by unfold CellBox.refR; fun_prop
  exact h1.mul (pcd _)

lemma htF_cd (K : CellBox) (B : CellBases) (l : ℕ) : ContDiff ℝ 1 (fun z => (1 - K.refZ z ^ 2) * hd B l z) := by
  have h1 : ContDiff ℝ 1 (fun z => 1 - K.refZ z ^ 2) := by unfold CellBox.refZ; fun_prop
  exact h1.mul (pcd _)

lemma rpoly_cd (B : CellBases) (j : ℕ) : ContDiff ℝ 1 (B.radialPoly j) := by
  unfold CellBases.radialPoly; fun_prop

lemma hpoly_cd (B : CellBases) (l : ℕ) : ContDiff ℝ 1 (B.heightPoly l) := by
  unfold CellBases.heightPoly; fun_prop

lemma prod_cd (f g : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (fun p : ℝ × ℝ => ((f p.1 * g p.2 : ℝ) : ℂ)) := by
  have h := Complex.ofRealCLM.contDiff.comp ((hf.comp contDiff_fst).mul (hg.comp contDiff_snd))
  simpa [Function.comp_def] using h

lemma coef_eq (K : CellBox) (B : CellBases) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    B.coef K F j l = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) :=
  rfl

def unitMat (a b : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a' b' => if a' = a ∧ b' = b then 1 else 0

lemma combo_grad (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    comboGrad (unitMat a b) m n G p = gradMode m n G a b p := by
  simp [comboGrad, unitMat, ite_and]

lemma combo_third (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3) (p : ℝ × ℝ) :
    comboThird (unitMat a b) m n H c p = modeThird m n H a b c p := by
  simp [comboThird, unitMat, ite_and]

lemma rderiv_psi {K : CellBox} {B : CellBases} (hK : K.r₁ < K.r₂) (hB : IsCellBases K B) {j : ℕ}
    (hj : j ≠ 0) (l : ℕ) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
        (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) p
      = ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
  unfold CellBox.radialDeriv
  have e : (fun r : ℝ => (K.lineWeight r : ℂ) * (((1 - K.refR r ^ 2) * rd B j r * B.heightPoly l p.2 : ℝ) : ℂ))
      = fun r => (((K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r) * B.heightPoly l p.2 : ℝ) : ℂ) := by
    funext r; push_cast; ring
  simp only
  rw [e, (((radial_hasDeriv hK hB hj p.1).mul_const (B.heightPoly l p.2)).ofReal_comp).deriv]

lemma hderiv_psi {K : CellBox} {B : CellBases} (hK : K.z₁ < K.z₂) (hB : IsCellBases K B) (j : ℕ) {l : ℕ}
    (hl : l ≠ 0) (p : ℝ × ℝ) :
    CellBox.heightDeriv (fun p : ℝ × ℝ =>
        ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ)) p
      = ((B.radialPoly j p.1 * (-(heightEigen K l) * B.heightPoly l p.2) : ℝ) : ℂ) := by
  unfold CellBox.heightDeriv
  simp only
  rw [(((height_hasDeriv hK hB hl p.2).const_mul (B.radialPoly j p.1)).ofReal_comp).deriv]

lemma strain_radial {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hRP : ModeRadialPartsStatement) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (j l : ℕ) (hj : j ≠ 0) :
    ((radialEigen K j : ℝ) : ℂ) * B.coef K (gradMode m n G a b) j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * modeThird m n H a b 0 p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
  have hr := hK.r_order.2
  have h := hRP K hK m v G H hs n (unitMat a b)
    (fun p => (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
    (prod_cd _ _ (radF_cd K B j) (hpoly_cd B l))
    (fun z => by simp [refR_left K hr]) (fun z => by simp [refR_right K hr])
  simp only [combo_grad, combo_third, rderiv_psi hr hB hj] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((radialEigen K j : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, gradMode m n G a b p *
          ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 0 p *
          (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := h.symm
      _ = _ := by congr 1; funext p; push_cast; ring

lemma strain_height {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hHP : ModeHeightPartsStatement) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (j l : ℕ) (hl : l ≠ 0) :
    ((heightEigen K l : ℝ) : ℂ) * B.coef K (gradMode m n G a b) j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * modeThird m n H a b 2 p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) := by
  have hz := hK.z_order.2
  have h := hHP K hK m v G H hs n (unitMat a b)
    (fun p => ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ))
    (prod_cd _ _ (rpoly_cd B j) (htF_cd K B l))
    (fun r => by simp [refZ_left K hz]) (fun r => by simp [refZ_right K hz])
  simp only [combo_grad, combo_third, hderiv_psi hz hB j hl] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((heightEigen K l : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a b p *
          ((B.radialPoly j p.1 * (-(heightEigen K l) * B.heightPoly l p.2) : ℝ) : ℂ) := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p *
          ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ) := h.symm
      _ = _ := by congr 1; funext p; push_cast; ring

lemma vel_radial {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hW : ModeRadialWeakStatement) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    (j l : ℕ) (hj : j ≠ 0) :
    ((radialEigen K j : ℝ) : ℂ) * B.coef K (fun p => modeVec m n v p.1 p.2 a) j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refR p.1 ^ 2) : ℝ) : ℂ) * gradMode m n G a 0 p *
        ((rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
  have hr := hK.r_order.2
  obtain ⟨hV, hGm, hw⟩ := hW K hK m v G H hs n a
  set ψ : ℝ → ℝ := fun r => K.lineWeight r * (1 - K.refR r ^ 2) * rd B j r with hψ
  have hψd : ∀ r, deriv ψ r = -(radialEigen K j) * K.lineWeight r * B.radialPoly j r :=
    fun r => (radial_hasDeriv hr hB hj r).deriv
  have hψc : ContDiff ℝ 1 ψ := by
    have e : ψ = fun r => (CellFormula.Internal.RelRadialCoef.Wp K *
        derivative (CellFormula.Internal.RelRadialCoef.poly B j)).eval r := by
      funext r
      simp only [hψ, rd, CellFormula.Internal.RelRadialCoef.Wp, Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_one, Polynomial.eval_pow, CellFormula.Internal.RelRadialCoef.wpoly_eval,
        CellFormula.Internal.RelRadialCoef.rho_eval]
    rw [e]; exact pcd _
  have h0 := hw ψ hψc (by simp [hψ, refR_left K hr]) (by simp [hψ, refR_right K hr]) (B.heightPoly l)
    (hp_cont B l)
  simp only [hψd] at h0
  have iA : IntegrableOn (fun p : ℝ × ℝ =>
      ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
        modeVec m n v p.1 p.2 a) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      ((((continuous_const.mul ((lw_cont K).comp continuous_fst)).mul ((rp_cont B j).comp continuous_fst)).mul
        ((hp_cont B l).comp continuous_snd)))).continuousOn hV (rect_cpt K)
  have iB : IntegrableOn (fun p : ℝ × ℝ =>
      (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
        ((K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p)) K.rect :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp
      ((((continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)).mul ((rd_cont B j).comp continuous_fst)).mul
        ((hp_cont B l).comp continuous_snd)))).continuousOn hGm (rect_cpt K)
  have h1 : ∫ p in K.rect, ((((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 : ℝ) : ℂ) *
        modeVec m n v p.1 p.2 a + ((ψ p.1 : ℝ) : ℂ) * gradMode m n G a 0 p) * ((B.heightPoly l p.2 : ℝ) : ℂ))
      = (∫ p in K.rect, ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
          modeVec m n v p.1 p.2 a)
        + ∫ p in K.rect, (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p) := by
    rw [← integral_add iA iB]
    congr 1; funext p; simp only [hψ]; push_cast; ring
  rw [h1] at h0
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((radialEigen K j : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, ((-(radialEigen K j) * K.lineWeight p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
          modeVec m n v p.1 p.2 a := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (((1 - K.refR p.1 ^ 2) * rd B j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 0 p) := by
          linear_combination -h0
      _ = _ := by congr 1; funext p; push_cast; ring

lemma vel_height {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hIbp : CellFormula.HeightModeIbpStatement) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3)
    (j l : ℕ) (hl : l ≠ 0) :
    ((heightEigen K l : ℝ) : ℂ) * B.coef K (fun p => modeVec m n v p.1 p.2 a) j l =
      ∫ p in K.rect, ((K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) : ℝ) : ℂ) * gradMode m n G a 2 p *
        ((B.radialPoly j p.1 * hd B l p.2 : ℝ) : ℂ) := by
  have hz := hK.z_order.2
  obtain ⟨_, hI⟩ := hIbp m n v G H hs K hK a
  have h := hI (B.radialPoly j) (fun z => (1 - K.refZ z ^ 2) * hd B l z) (rp_cont B j) (htF_cd K B l)
    (by simp [refZ_left K hz]) (by simp [refZ_right K hz])
  simp only [fun z => (height_hasDeriv hz hB hl z).deriv] at h
  rw [coef_eq, ← integral_const_mul]
  calc ∫ p in K.rect, ((heightEigen K l : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
          ((B.radialPoly j p.1 * (-(heightEigen K l) * B.heightPoly l p.2) : ℝ) : ℂ) := by
          rw [← integral_neg]; congr 1; funext p; push_cast; ring
      _ = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p *
          ((B.radialPoly j p.1 * ((1 - K.refZ p.2 ^ 2) * hd B l p.2) : ℝ) : ℂ) := by
          rw [h, neg_neg]
      _ = _ := by congr 1; funext p; push_cast; ring

lemma wmono {K : CellBox} (F : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (g : ℝ × ℝ → ℝ) (hg : Continuous g) (hg01 : ∀ p ∈ K.rect, 0 ≤ g p ∧ g p ≤ 1)
    (h : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => K.lineWeight p.1 * g p * ‖F p‖ ^ 2) K.rect := by
  refine Integrable.mono' h ((((lw_cont K).comp continuous_fst).mul hg).aestronglyMeasurable.mul
    (hF.norm.pow 2)) ?_
  refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have hw := lw_nonneg (K := K) hp.1.1
  obtain ⟨g0, g1⟩ := hg01 p hp
  rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg hw g0) (sq_nonneg _))]
  have := sq_nonneg ‖F p‖
  nlinarith [mul_nonneg hw this]

lemma rmono {K : CellBox} (hK : IsCellBox K) (F : ℝ × ℝ → ℂ) (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (h : IntegrableOn (fun p => p.1 * ‖F p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect := by
  refine Integrable.mono' (h.const_mul (K.innerRadius)⁻¹)
    (((lw_cont K).comp continuous_fst).aestronglyMeasurable.mul (hF.norm.pow 2)) ?_
  refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  have hw := lw_nonneg (K := K) hp.1.1
  rw [Real.norm_of_nonneg (mul_nonneg hw (sq_nonneg _))]
  have hs := sq_nonneg ‖F p‖
  unfold CellBox.lineWeight CellBox.innerRadius
  split_ifs with h0
  · simp
  · have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
    have hr : K.r₁ ≤ p.1 := hp.1.1
    rw [one_mul, ← mul_assoc]
    have : 1 ≤ K.r₁⁻¹ * p.1 := by
      rw [inv_mul_eq_div, le_div_iff₀ hr1]; linarith
    nlinarith

lemma gR01 {K : CellBox} (hK : IsCellBox K) : ∀ p ∈ K.rect, 0 ≤ 1 - K.refR p.1 ^ 2 ∧ 1 - K.refR p.1 ^ 2 ≤ 1 :=
  fun p hp => ⟨refR_sq_le hK.r_order.2 hp.1.1 hp.1.2, by nlinarith [sq_nonneg (K.refR p.1)]⟩

lemma gZ01 {K : CellBox} (hK : IsCellBox K) : ∀ p ∈ K.rect, 0 ≤ 1 - K.refZ p.2 ^ 2 ∧ 1 - K.refZ p.2 ^ 2 ≤ 1 :=
  fun p hp => ⟨refZ_sq_le hK.z_order.2 hp.2.1 hp.2.2, by nlinarith [sq_nonneg (K.refZ p.2)]⟩

lemma strain_tail {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hS : ModeSquareIntegrableStatement) (hRP : ModeRadialPartsStatement) (hHP : ModeHeightPartsStatement)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    Summable (fun jl : ℕ × ℕ => (1 + (radialEigen K jl.1 + heightEigen K jl.2)) *
      ‖B.coef K (gradMode m n G a b) jl.1 jl.2‖ ^ 2) := by
  obtain ⟨_, _, h3⟩ := hS K hK m v G H hs n (unitMat a b)
  obtain ⟨hr0, hr2⟩ := h3 0
  obtain ⟨hz0, hz2⟩ := h3 2
  have eT : ∀ c : Fin 3, comboThird (unitMat a b) m n H c = modeThird m n H a b c :=
    fun c => funext (combo_third m n H a b c)
  rw [eT] at hr0 hr2 hz0 hz2
  obtain ⟨hF, hF2⟩ := modeGradSquare K hK m v G H hs n a b
  exact tail_all hK hB _ _ _ hF hF2 hr0
    (wmono _ hr0 _ (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)) (gR01 hK)
      (rmono hK _ hr0 hr2))
    (fun j l hj => strain_radial hK hB hRP hs n a b j l hj) hz0
    (wmono _ hz0 _ (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2)) (gZ01 hK)
      (rmono hK _ hz0 hz2))
    (fun j l hl => strain_height hK hB hHP hs n a b j l hl)

lemma vel_tail {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (hW : ModeRadialWeakStatement) (hIbp : CellFormula.HeightModeIbpStatement)
    {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a : Fin 3) :
    Summable (fun jl : ℕ × ℕ => (1 + (radialEigen K jl.1 + heightEigen K jl.2)) *
      ‖B.coef K (fun p => modeVec m n v p.1 p.2 a) jl.1 jl.2‖ ^ 2) := by
  obtain ⟨hF, hF2⟩ := modeVelSquare K hK m v G H hs n a
  obtain ⟨hr0, hr2⟩ := modeGradSquare K hK m v G H hs n a 0
  obtain ⟨hz0, hz2⟩ := modeGradSquare K hK m v G H hs n a 2
  exact tail_all hK hB _ _ _ hF hF2 hr0
    (wmono _ hr0 _ (continuous_const.sub (((refR_cont K).comp continuous_fst).pow 2)) (gR01 hK) hr2)
    (fun j l hj => vel_radial hK hB hW hs n a j l hj) hz0
    (wmono _ hz0 _ (continuous_const.sub (((refZ_cont K).comp continuous_snd).pow 2)) (gZ01 hK) hz2)
    (fun j l hl => vel_height hK hB hIbp hs n a j l hl)

end SharpCoefTailInternal

open SharpCoefTailInternal in
theorem sharpCoefTail_of (hS : ModeSquareIntegrableStatement) (hRP : ModeRadialPartsStatement)
    (hHP : ModeHeightPartsStatement) (hW : ModeRadialWeakStatement)
    (hIbp : CellFormula.HeightModeIbpStatement) : SharpCoefTailStatement := by
  intro α _ _ k N c _ K S B Cl slots R hD _ x hx
  exact ⟨fun n _ a b => strain_tail hD.box hD.bases hS hRP hHP hx.1 n a b,
    fun n _ a => vel_tail hD.box hD.bases hW hIbp hx.1 n a⟩

end CellAnalysis

end CellCert

end Breakdown

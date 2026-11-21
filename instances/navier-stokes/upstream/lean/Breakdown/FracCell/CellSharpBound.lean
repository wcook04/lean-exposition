import Breakdown.FracCell.CellSharpBoundSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace CellSharpBoundInternal

lemma lw_cont (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight; split_ifs <;> fun_prop

lemma lw_nonneg {K : CellBox} {r : ℝ} (hr : K.r₁ ≤ r) : 0 ≤ K.lineWeight r := by
  unfold CellBox.lineWeight; split_ifs with h
  · linarith
  · norm_num

lemma rp_cont (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly; fun_prop

lemma hp_cont (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly; fun_prop

def bas (B : CellBases) (i : ℕ × ℕ) (p : ℝ × ℝ) : ℝ := B.radialPoly i.1 p.1 * B.heightPoly i.2 p.2

lemma bas_cont (B : CellBases) (i : ℕ × ℕ) : Continuous (bas B i) := by
  unfold bas
  exact ((rp_cont B _).comp continuous_fst).mul ((hp_cont B _).comp continuous_snd)

lemma rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

lemma rect_cpt (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

lemma orth {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (i i' : ℕ × ℕ) :
    ∫ p in K.rect, K.lineWeight p.1 * bas B i p * bas B i' p = if i = i' then 1 else 0 := by
  have e : ∀ p : ℝ × ℝ, K.lineWeight p.1 * bas B i p * bas B i' p
      = (K.lineWeight p.1 * B.radialPoly i.1 p.1 * B.radialPoly i'.1 p.1)
        * (B.heightPoly i.2 p.2 * B.heightPoly i'.2 p.2) := by
    intro p; unfold bas; ring
  simp_rw [e]
  rw [CellBox.rect, Measure.volume_eq_prod,
    setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly i.1 r * B.radialPoly i'.1 r)
      (fun z => B.heightPoly i.2 z * B.heightPoly i'.2 z),
    hB.radial_orthonormal, hB.height_orthonormal]
  obtain ⟨j, l⟩ := i
  obtain ⟨j', l'⟩ := i'
  simp only [Prod.mk.injEq]
  split_ifs <;> simp_all

lemma wbb_int (K : CellBox) (B : CellBases) (i i' : ℕ × ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => K.lineWeight p.1 * bas B i p * bas B i' p) K.rect :=
  (((lw_cont K).comp continuous_fst).mul (bas_cont B i) |>.mul (bas_cont B i')).continuousOn.integrableOn_compact
    (rect_cpt K)

lemma g_int {K : CellBox} (B : CellBases) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (i : ℕ × ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ)) K.rect := by
  have hb := wbb_int K B i i
  refine Integrable.mono' (hF2.add hb) ?_ ?_
  · exact (((Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)).aestronglyMeasurable).mul hF).mul
      (Complex.continuous_ofReal.comp (bas_cont B i)).aestronglyMeasurable
  · refine (ae_restrict_iff' (rect_meas K)).2 (Filter.Eventually.of_forall fun p hp => ?_)
    have hw := lw_nonneg hp.1.1
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg hw, Real.norm_eq_abs]
    have h1 := norm_nonneg (F p)
    have h2 := abs_nonneg (bas B i p)
    have h3 : bas B i p * bas B i p = |bas B i p| ^ 2 := by rw [sq_abs]; ring
    simp only [Pi.add_apply]
    nlinarith [mul_nonneg hw (sq_nonneg (‖F p‖ - |bas B i p|))]

lemma sqn (z : ℂ) : ‖z‖ ^ 2 = (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj, Complex.ofReal_re, Complex.sq_norm]

lemma pt_id (w : ℝ) (f : ℂ) (T : Finset (ℕ × ℕ)) (c : ℕ × ℕ → ℂ) (b : ℕ × ℕ → ℝ) :
    w * ‖f - ∑ i ∈ T, c i * (b i : ℂ)‖ ^ 2 =
      w * ‖f‖ ^ 2 - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))).re
        + ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (w * b i * b i') := by
  set P := ∑ i ∈ T, c i * (b i : ℂ) with hPdef
  have e1 : (f - P) * (starRingEnd ℂ) (f - P) = f * (starRingEnd ℂ) f
      - (f * (starRingEnd ℂ) P + (starRingEnd ℂ) (f * (starRingEnd ℂ) P)) + P * (starRingEnd ℂ) P := by
    simp only [map_sub, map_mul, Complex.conj_conj]; ring
  have e2 : (f * (starRingEnd ℂ) P).re = ∑ i ∈ T, b i * ((starRingEnd ℂ) (c i) * f).re := by
    rw [hPdef, map_sum, Finset.mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, Complex.conj_ofReal, show f * ((starRingEnd ℂ) (c i) * (b i : ℂ))
      = (b i : ℂ) * ((starRingEnd ℂ) (c i) * f) by ring, Complex.re_ofReal_mul]
  have e3 : (P * (starRingEnd ℂ) P).re
      = ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (b i * b i') := by
    rw [hPdef, map_sum, Finset.sum_mul_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i' _ => ?_
    rw [map_mul, Complex.conj_ofReal, show c i * (b i : ℂ) * ((starRingEnd ℂ) (c i') * (b i' : ℂ))
      = ((b i * b i' : ℝ) : ℂ) * (c i * (starRingEnd ℂ) (c i')) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have e4 : ∀ i, ((starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))).re
      = w * (b i * ((starRingEnd ℂ) (c i) * f).re) := by
    intro i
    rw [show (starRingEnd ℂ) (c i) * ((w : ℂ) * f * (b i : ℂ))
      = ((w * b i : ℝ) : ℂ) * ((starRingEnd ℂ) (c i) * f) by push_cast; ring, Complex.re_ofReal_mul]
    ring
  have e5 : ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (w * b i * b i')
      = w * ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (b i * b i') := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i' _ => by ring
  rw [sqn (f - P), sqn f, e1, Complex.add_re, Complex.sub_re, Complex.add_re, Complex.conj_re, e3, e2, e5]
  simp only [e4, ← Finset.mul_sum]
  ring

lemma coefEnergy_fin {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) (T : Finset (ℕ × ℕ)) :
    ∑ i ∈ T, ‖B.coef K F i.1 i.2‖ ^ 2 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖F p‖ ^ 2 := by
  set c : ℕ × ℕ → ℂ := fun i => B.coef K F i.1 i.2 with hc
  have hg := g_int B F hF hF2
  have hcg : ∀ i, c i = ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ) := fun i => rfl
  have h0 : 0 ≤ ∫ p in K.rect, K.lineWeight p.1 * ‖F p - ∑ i ∈ T, c i * ((bas B i p : ℝ) : ℂ)‖ ^ 2 :=
    setIntegral_nonneg (rect_meas K) fun p hp => mul_nonneg (lw_nonneg hp.1.1) (sq_nonneg _)
  have h0' : 0 ≤ ∫ p in K.rect, (K.lineWeight p.1 * ‖F p‖ ^ 2
      - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ))).re
      + ∑ i ∈ T, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re * (K.lineWeight p.1 * bas B i p * bas B i' p)) :=
    h0.trans_eq (integral_congr_ae (Filter.Eventually.of_forall fun p =>
      pt_id (K.lineWeight p.1) (F p) T c (fun i => bas B i p)))
  have iA : ∀ i ∈ T, Integrable (fun p => ((starRingEnd ℂ) (c i) *
      ((K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ))).re) (volume.restrict K.rect) :=
    fun i _ => ((hg i).const_mul _).re
  have iB : ∀ i ∈ T, ∀ i' ∈ T, Integrable (fun p => (c i * (starRingEnd ℂ) (c i')).re *
      (K.lineWeight p.1 * bas B i p * bas B i' p)) (volume.restrict K.rect) :=
    fun i _ i' _ => (wbb_int K B i i').const_mul _
  have iB' : ∀ i ∈ T, Integrable (fun p => ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re *
      (K.lineWeight p.1 * bas B i p * bas B i' p)) (volume.restrict K.rect) :=
    fun i hi => integrable_finsetSum _ (iB i hi)
  have iA2 := (integrable_finsetSum T iA).const_mul 2
  have hsub : Integrable (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2
      - 2 * ∑ i ∈ T, ((starRingEnd ℂ) (c i) * ((K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ))).re)
      (volume.restrict K.rect) := hF2.sub iA2
  rw [integral_add hsub (integrable_finsetSum _ iB'), integral_sub hF2 iA2, integral_const_mul,
    integral_finsetSum _ iA, integral_finsetSum _ iB'] at h0'
  have eA : ∀ i, ∫ p in K.rect, ((starRingEnd ℂ) (c i) *
      ((K.lineWeight p.1 : ℂ) * F p * ((bas B i p : ℝ) : ℂ))).re = ‖c i‖ ^ 2 := by
    intro i
    have h := integral_re (𝕜 := ℂ) ((hg i).const_mul ((starRingEnd ℂ) (c i)))
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul, ← hcg, sqn, mul_comm]
  have eB : ∀ i ∈ T, ∫ p in K.rect, ∑ i' ∈ T, (c i * (starRingEnd ℂ) (c i')).re *
      (K.lineWeight p.1 * bas B i p * bas B i' p) = ‖c i‖ ^ 2 := by
    intro i hi
    rw [integral_finsetSum _ (iB i hi)]
    simp only [integral_const_mul, orth hB, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq T i, if_pos hi, sqn]
  rw [Finset.sum_congr rfl eB] at h0'
  simp only [eA] at h0'
  linarith

lemma coef_summable {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (F : ℝ × ℝ → ℂ)
    (hF : AEStronglyMeasurable F (volume.restrict K.rect))
    (hF2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    Summable (fun i : ℕ × ℕ => ‖B.coef K F i.1 i.2‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (coefEnergy_fin hB F hF hF2)

end CellSharpBoundInternal

namespace CellSharpBoundInternal

lemma symSq_nonneg' (Y : Fin 3 → Fin 3 → ℂ) : 0 ≤ symSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma antiSq_nonneg' (Y : Fin 3 → Fin 3 → ℂ) : 0 ≤ antiSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma vecSq_nonneg' (Y : Fin 3 → ℂ) : 0 ≤ vecSq Y :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma ep_self (W : Fin 3 → Fin 3 → ℂ) : (entryPairing W W).re = ∑ a : Fin 3, ∑ b : Fin 3, ‖W a b‖ ^ 2 := by
  unfold entryPairing
  simp only [Complex.re_sum, sqn]

lemma swp_self (W : Fin 3 → Fin 3 → ℂ) (hs ha : ℝ) :
    (CellScalars.sigmaWeightedPair W W hs ha).re = symSq W / hs + antiSq W / ha := by
  unfold CellScalars.sigmaWeightedPair
  rw [Complex.add_re, Complex.div_ofReal_re, Complex.div_ofReal_re, ep_self, ep_self]
  rfl

section
variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
  {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}

lemma sym_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l) :
    0 < S.symWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.sym_weight n j l h).1

lemma anti_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l) :
    0 < S.antiWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.anti_weight n j l h).1

lemma vel_pos (hd : IsCellData α c K S B Cl R) {n : ℤ} (hn : n ∈ S.resolved) {j l : ℕ} (h : S.degHigh ≤ max j l) :
    0 < S.velWeight n j l :=
  lt_of_lt_of_le hd.scalars.weightFloor_pos (hd.scalars.vel_weight n hn j l h).1
end

lemma half_add (x y : ℂ) : ‖(x + y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_div, Complex.norm_two, div_pow]
  have h1 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

lemma half_sub (x y : ℂ) : ‖(x - y) / 2‖ ^ 2 ≤ (‖x‖ ^ 2 + ‖y‖ ^ 2) / 2 := by
  rw [norm_div, Complex.norm_two, div_pow]
  have h1 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

lemma swap_avg (Y : Fin 3 → Fin 3 → ℂ) :
    ∑ a : Fin 3, ∑ b : Fin 3, (‖Y a b‖ ^ 2 + ‖Y b a‖ ^ 2) / 2 = sumSq Y := by
  have hc : ∑ a : Fin 3, ∑ b : Fin 3, ‖Y b a‖ ^ 2 = ∑ a : Fin 3, ∑ b : Fin 3, ‖Y a b‖ ^ 2 := Finset.sum_comm
  unfold sumSq
  simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, hc]
  ring

lemma symSq_le (Y : Fin 3 → Fin 3 → ℂ) : symSq Y ≤ sumSq Y := by
  rw [← swap_avg]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => half_add _ _

lemma antiSq_le (Y : Fin 3 → Fin 3 → ℂ) : antiSq Y ≤ sumSq Y := by
  rw [← swap_avg]
  exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => half_sub _ _

lemma sumSq_nn (Y : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq Y :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma sumInner_sq {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (c : ι → ℂ) :
    ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ^ 2 ≤ T.card * ∑ a ∈ T, μ a ^ 2 * ‖c a‖ ^ 2 := by
  have h1 : ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ≤ ∑ a ∈ T, |μ a| * ‖c a‖ :=
    (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun a _ => by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]))
  have h2 := sq_sum_le_card_mul_sum_sq (s := T) (f := fun a => |μ a| * ‖c a‖)
  have h3 : ‖∑ a ∈ T, ((μ a : ℝ) : ℂ) * c a‖ ^ 2 ≤ (∑ a ∈ T, |μ a| * ‖c a‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  refine h3.trans (h2.trans (le_of_eq ?_))
  congr 1
  exact Finset.sum_congr rfl fun a _ => by rw [mul_pow, sq_abs]

lemma sumSq_summable (Y : ℕ × ℕ → Fin 3 → Fin 3 → ℂ) (h : ∀ a b, Summable (fun jl => ‖Y jl a b‖ ^ 2)) :
    Summable (fun jl => sumSq (Y jl)) := by
  unfold sumSq
  exact summable_sum fun a _ => summable_sum fun b _ => h a b

lemma vecSq_summable (Y : ℕ × ℕ → Fin 3 → ℂ) (h : ∀ a, Summable (fun jl => ‖Y jl a‖ ^ 2)) :
    Summable (fun jl => vecSq (Y jl)) := by
  unfold vecSq
  exact summable_sum fun a _ => h a

lemma combo_summable {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (X : ι → ℕ × ℕ → Fin 3 → Fin 3 → ℂ)
    (h : ∀ a ∈ T, ∀ i q, Summable (fun jl => ‖X a jl i q‖ ^ 2)) :
    Summable (fun jl => sumSq (fun i q => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a jl i q)) := by
  refine Summable.of_nonneg_of_le
    (f := fun jl => ∑ i : Fin 3, ∑ q : Fin 3, (T.card : ℝ) * ∑ a ∈ T, μ a ^ 2 * ‖X a jl i q‖ ^ 2)
    (fun jl => sumSq_nn _) (fun jl => ?_)
    (summable_sum (s := Finset.univ) fun i _ => summable_sum (s := Finset.univ) fun q _ =>
      (summable_sum (s := T) fun a ha => (h a ha i q).mul_left (μ a ^ 2)).mul_left (T.card : ℝ))
  exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun q _ => sumInner_sq T μ _

lemma combo_vec_summable {ι : Type*} (T : Finset ι) (μ : ι → ℝ) (X : ι → ℕ × ℕ → Fin 3 → ℂ)
    (h : ∀ a ∈ T, ∀ i, Summable (fun jl => ‖X a jl i‖ ^ 2)) :
    Summable (fun jl => vecSq (fun i => ∑ a ∈ T, ((μ a : ℝ) : ℂ) * X a jl i)) := by
  refine Summable.of_nonneg_of_le
    (f := fun jl => ∑ i : Fin 3, (T.card : ℝ) * ∑ a ∈ T, μ a ^ 2 * ‖X a jl i‖ ^ 2)
    (fun jl => vecSq_nonneg' _) (fun jl => ?_)
    (summable_sum (s := Finset.univ) fun i _ =>
      (summable_sum (s := T) fun a ha => (h a ha i).mul_left (μ a ^ 2)).mul_left (T.card : ℝ))
  exact Finset.sum_le_sum fun i _ => sumInner_sq T μ _

variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
  {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}

lemma pair_bound (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l)
    (Y : Fin 3 → Fin 3 → ℂ) :
    symSq Y / S.symWeight n j l + antiSq Y / S.antiWeight n j l ≤ 2 / S.weightFloor * sumSq Y := by
  have hf := hd.scalars.weightFloor_pos
  have e1 := div_le_div₀ (sumSq_nn _) (symSq_le Y) hf (hd.scalars.sym_weight n j l h).1
  have e2 := div_le_div₀ (sumSq_nn _) (antiSq_le Y) hf (hd.scalars.anti_weight n j l h).1
  have : 2 / S.weightFloor * sumSq Y = sumSq Y / S.weightFloor + sumSq Y / S.weightFloor := by ring
  linarith

lemma pair_nonneg (hd : IsCellData α c K S B Cl R) {n : ℤ} {j l : ℕ} (h : n ∉ S.resolved ∨ S.degHigh < max j l)
    (Y : Fin 3 → Fin 3 → ℂ) :
    0 ≤ symSq Y / S.symWeight n j l + antiSq Y / S.antiWeight n j l :=
  add_nonneg (div_nonneg (symSq_nonneg' _) (sym_pos hd h).le) (div_nonneg (antiSq_nonneg' _) (anti_pos hd h).le)

lemma vel_bound (hd : IsCellData α c K S B Cl R) {n : ℤ} (hn : n ∈ S.resolved) {j l : ℕ} (h : S.degHigh ≤ max j l)
    (V : Fin 3 → ℂ) : vecSq V / S.velWeight n j l ≤ 1 / S.weightFloor * vecSq V := by
  rw [one_div_mul_eq_div]
  exact div_le_div₀ (vecSq_nonneg' _) le_rfl hd.scalars.weightFloor_pos (hd.scalars.vel_weight n hn j l h).1

lemma far_y (hd : IsCellData α c K S B Cl R) (T1 : Finset ℤ) (Y : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (V : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (hY : ∀ n ∈ T1, Summable (fun jl : ℕ × ℕ => sumSq (Y n jl.1 jl.2)))
    (hV : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (V n jl.1 jl.2))) :
    Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
      (∑ n ∈ T1, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
          symSq (Y n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (Y n jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0)
        + ∑ n ∈ S.resolved, vecSq (V n jl.1 jl.2) / S.velWeight n jl.1 jl.2
      else 0) := by
  have hf := hd.scalars.weightFloor_pos
  obtain ⟨_, _, hdeg⟩ := hd.scalars.degrees
  refine Summable.of_nonneg_of_le (fun jl => ?_) (fun jl => ?_)
    ((summable_sum fun n hn => (hY n hn).mul_left (2 / S.weightFloor)).add
      (summable_sum fun n hn => (hV n hn).mul_left (1 / S.weightFloor)))
  · split_ifs with hfar
    · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
      refine add_nonneg (Finset.sum_nonneg fun n _ => ?_) (Finset.sum_nonneg fun n hn => ?_)
      · rw [if_pos (Or.inr hlt)]
        exact pair_nonneg hd (Or.inr hlt) _
      · exact div_nonneg (vecSq_nonneg' _) (vel_pos hd hn hlt.le).le
    · exact le_refl 0
  · have g0 : 0 ≤ (∑ n ∈ T1, 2 / S.weightFloor * sumSq (Y n jl.1 jl.2))
        + ∑ n ∈ S.resolved, 1 / S.weightFloor * vecSq (V n jl.1 jl.2) :=
      add_nonneg (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (sumSq_nn _))
        (Finset.sum_nonneg fun n _ => mul_nonneg (by positivity) (vecSq_nonneg' _))
    split_ifs with hfar
    · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
      refine add_le_add (Finset.sum_le_sum fun n _ => ?_) (Finset.sum_le_sum fun n hn => vel_bound hd hn hlt.le _)
      split_ifs with hc
      · exact pair_bound hd hc _
      · exact mul_nonneg (by positivity) (sumSq_nn _)
    · exact g0

lemma far_row (hd : IsCellData α c K S B Cl R) (T1 : Finset ℤ) (W : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ)
    (V : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (hW : ∀ n ∈ T1, Summable (fun jl : ℕ × ℕ => sumSq (W n jl.1 jl.2)))
    (hV : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (V n jl.1 jl.2))) :
    Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
      (∑ n ∈ T1, (CellScalars.sigmaWeightedPair (W n jl.1 jl.2) (W n jl.1 jl.2)
          (S.symWeight n jl.1 jl.2) (S.antiWeight n jl.1 jl.2)).re)
        + ∑ n ∈ S.resolved, vecSq (V n jl.1 jl.2) / S.velWeight n jl.1 jl.2
      else 0) := by
  have h := far_y hd T1 W V hW hV
  refine h.congr fun jl => ?_
  obtain ⟨_, _, hdeg⟩ := hd.scalars.degrees
  split_ifs with hfar
  · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [if_pos (Or.inr hlt), swp_self]
  · rfl

end CellSharpBoundInternal

namespace CellSharpBoundInternal

lemma cc {h : ℝ} (hh : 0 < h) (a b : ℂ) : -(‖b‖ ^ 2 / h) ≤ h * ‖a‖ ^ 2 + 2 * (a * (starRingEnd ℂ) b).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  have key : h * (a.re * a.re + a.im * a.im) + 2 * (a.re * b.re - a.im * -b.im) + (b.re * b.re + b.im * b.im) / h
      = ((h * a.re + b.re) ^ 2 + (h * a.im + b.im) ^ 2) / h := by
    field_simp; ring
  have : 0 ≤ ((h * a.re + b.re) ^ 2 + (h * a.im + b.im) ^ 2) / h := by positivity
  linarith

lemma cc' {h : ℝ} (hh : 0 < h) (a b : ℂ) : 2 * (a * (starRingEnd ℂ) b).re ≤ h * ‖a‖ ^ 2 + ‖b‖ ^ 2 / h := by
  have := cc hh (-a) b
  rw [norm_neg, neg_mul, Complex.neg_re] at this
  linarith

lemma pen_lo {hs ha : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (σ Z : Fin 3 → Fin 3 → ℂ) :
    -(symSq Z / hs + antiSq Z / ha) ≤ strainPen hs ha σ Z := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cc hs0 ((σ a b + σ b a) / 2) ((Z a b + Z b a) / 2))
  have e2 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cc ha0 ((σ a b - σ b a) / 2) ((Z a b - Z b a) / 2))
  unfold strainPen symSq antiSq entryPairing
  simp only [Complex.add_re, Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div] at e1 e2 ⊢
  linarith

lemma pen_hi {hs ha : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (σ Z : Fin 3 → Fin 3 → ℂ) :
    strainPen hs ha σ Z ≤ 2 * (hs * symSq σ + ha * antiSq σ) + (symSq Z / hs + antiSq Z / ha) := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cc' hs0 ((σ a b + σ b a) / 2) ((Z a b + Z b a) / 2))
  have e2 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => Finset.sum_nonneg
    fun (b : Fin 3) (_ : b ∈ Finset.univ) =>
      sub_nonneg.2 (cc' ha0 ((σ a b - σ b a) / 2) ((Z a b - Z b a) / 2))
  unfold strainPen symSq antiSq entryPairing
  simp only [Complex.add_re, Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div] at e1 e2 ⊢
  linarith

lemma vpen_lo {hv : ℝ} (hv0 : 0 < hv) (τ Z : Fin 3 → ℂ) : -(vecSq Z / hv) ≤ velPen hv τ Z := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => sub_nonneg.2 (cc hv0 (τ a) (Z a))
  unfold velPen vecSq CellScalars.vecPair
  simp only [Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, ← Finset.mul_sum, ← Finset.sum_div] at e1 ⊢
  linarith

lemma vpen_hi {hv : ℝ} (hv0 : 0 < hv) (τ Z : Fin 3 → ℂ) :
    velPen hv τ Z ≤ 2 * (hv * vecSq τ) + vecSq Z / hv := by
  have e1 := Finset.sum_nonneg fun (a : Fin 3) (_ : a ∈ Finset.univ) => sub_nonneg.2 (cc' hv0 (τ a) (Z a))
  unfold velPen vecSq CellScalars.vecPair
  simp only [Complex.re_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_div] at e1 ⊢
  linarith

lemma sq_add_le (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h1 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le x y) 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

lemma symSq_add_le (Y W : Fin 3 → Fin 3 → ℂ) :
    symSq (fun a b => Y a b + W a b) ≤ 2 * symSq Y + 2 * symSq W := by
  unfold symSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [show (Y a b + W a b + (Y b a + W b a)) / 2 = (Y a b + Y b a) / 2 + (W a b + W b a) / 2 by ring]
  exact sq_add_le _ _

lemma antiSq_add_le (Y W : Fin 3 → Fin 3 → ℂ) :
    antiSq (fun a b => Y a b + W a b) ≤ 2 * antiSq Y + 2 * antiSq W := by
  unfold antiSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [show (Y a b + W a b - (Y b a + W b a)) / 2 = (Y a b - Y b a) / 2 + (W a b - W b a) / 2 by ring]
  exact sq_add_le _ _

lemma vecSq_add_le (Y W : Fin 3 → ℂ) : vecSq (fun a => Y a + W a) ≤ 2 * vecSq Y + 2 * vecSq W := by
  unfold vecSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => sq_add_le _ _

lemma strain_abs {hs ha : ℝ} (hs0 : 0 < hs) (ha0 : 0 < ha) (σ Y W : Fin 3 → Fin 3 → ℂ) (q : Prop) [Decidable q] :
    |strainPen hs ha σ (fun i j => Y i j + if q then W i j else 0)|
      ≤ 2 * (hs * symSq σ + ha * antiSq σ) + 2 * (symSq Y / hs + antiSq Y / ha)
        + (if q then 2 * (symSq W / hs + antiSq W / ha) else 0) := by
  have hσ : 0 ≤ hs * symSq σ + ha * antiSq σ :=
    add_nonneg (mul_nonneg hs0.le (symSq_nonneg' _)) (mul_nonneg ha0.le (antiSq_nonneg' _))
  have hY : 0 ≤ symSq Y / hs + antiSq Y / ha :=
    add_nonneg (div_nonneg (symSq_nonneg' _) hs0.le) (div_nonneg (antiSq_nonneg' _) ha0.le)
  have hZ : symSq (fun i j => Y i j + if q then W i j else 0) / hs
      + antiSq (fun i j => Y i j + if q then W i j else 0) / ha
      ≤ 2 * (symSq Y / hs + antiSq Y / ha) + (if q then 2 * (symSq W / hs + antiSq W / ha) else 0) := by
    by_cases hq : q
    · simp only [hq, if_true]
      have f1 := div_le_div_of_nonneg_right (symSq_add_le Y W) hs0.le
      have f2 := div_le_div_of_nonneg_right (antiSq_add_le Y W) ha0.le
      have e : (2 * symSq Y + 2 * symSq W) / hs + (2 * antiSq Y + 2 * antiSq W) / ha
          = 2 * (symSq Y / hs + antiSq Y / ha) + 2 * (symSq W / hs + antiSq W / ha) := by ring
      linarith
    · simp only [hq, if_false, add_zero]
      linarith
  have hZ0 : 0 ≤ symSq (fun i j => Y i j + if q then W i j else 0) / hs
      + antiSq (fun i j => Y i j + if q then W i j else 0) / ha :=
    add_nonneg (div_nonneg (symSq_nonneg' _) hs0.le) (div_nonneg (antiSq_nonneg' _) ha0.le)
  have lo := pen_lo hs0 ha0 σ (fun i j => Y i j + if q then W i j else 0)
  have hi := pen_hi hs0 ha0 σ (fun i j => Y i j + if q then W i j else 0)
  rw [abs_le]
  constructor <;> linarith

lemma vel_abs {hv : ℝ} (hv0 : 0 < hv) (τ Y W : Fin 3 → ℂ) :
    |velPen hv τ (fun i => Y i + W i)| ≤ 2 * (hv * vecSq τ) + 2 * (vecSq Y / hv) + 2 * (vecSq W / hv) := by
  have hτ : 0 ≤ hv * vecSq τ := mul_nonneg hv0.le (vecSq_nonneg' _)
  have hY : 0 ≤ vecSq Y / hv := div_nonneg (vecSq_nonneg' _) hv0.le
  have hW : 0 ≤ vecSq W / hv := div_nonneg (vecSq_nonneg' _) hv0.le
  have f := div_le_div_of_nonneg_right (vecSq_add_le Y W) hv0.le
  have e : (2 * vecSq Y + 2 * vecSq W) / hv = 2 * (vecSq Y / hv) + 2 * (vecSq W / hv) := by ring
  have lo := vpen_lo hv0 τ (fun i => Y i + W i)
  have hi := vpen_hi hv0 τ (fun i => Y i + W i)
  rw [abs_le]
  constructor <;> linarith

end CellSharpBoundInternal

namespace CellSharpBoundInternal

variable {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
  {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}

lemma far_a (hd : IsCellData α c K S B Cl R) (μ : Fin N → ℝ) (κ ζ : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (σ : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (τ : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (Y W : ℤ → ℕ → ℕ → Fin 3 → Fin 3 → ℂ) (Yv Wv : ℤ → ℕ → ℕ → Fin 3 → ℂ)
    (hT : ∀ n j l, CellScalars.targetStrain c K S R B μ κ ζ v G n j l
      = fun i q => Y n j l i q + if n ∈ S.resolved ∪ S.band then W n j l i q else 0)
    (hTv : ∀ n j l, CellScalars.targetVelocity c K S R B μ v G n j l = fun i => Yv n j l i + Wv n j l i)
    (hE : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
            (∑ n ∈ R.yModes, (S.symWeight n jl.1 jl.2 * symSq (σ n jl.1 jl.2)
              + S.antiWeight n jl.1 jl.2 * antiSq (σ n jl.1 jl.2)))
            + ∑ n ∈ S.resolved, S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2)
          else 0))
    (hb : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
      (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
          symSq (Y n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (Y n jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0)
        + ∑ n ∈ S.resolved, vecSq (Yv n jl.1 jl.2) / S.velWeight n jl.1 jl.2
      else 0))
    (hw : Summable (fun jl : ℕ × ℕ => if S.degNear < max jl.1 jl.2 then
      (∑ n ∈ S.resolved ∪ S.band, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
          symSq (W n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (W n jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0)
        + ∑ n ∈ S.resolved, vecSq (Wv n jl.1 jl.2) / S.velWeight n jl.1 jl.2
      else 0)) :
    Summable (CellScalars.sharpFarTerm c K S R B μ κ ζ v G σ τ) := by
  obtain ⟨_, _, hdeg⟩ := hd.scalars.degrees
  refine Summable.of_norm_bounded ((hE.mul_left 2).add ((hb.mul_left 2).add (hw.mul_left 2))) fun jl => ?_
  rw [Real.norm_eq_abs]
  unfold CellScalars.sharpFarTerm
  by_cases hfar : S.degNear < max jl.1 jl.2
  · have hlt : S.degHigh < max jl.1 jl.2 := lt_of_le_of_lt (by omega) hfar
    have hcnd : ∀ n : ℤ, n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2 := fun _ => Or.inr hlt
    simp only [hfar, if_true]
    have eB : (∑ n ∈ R.yModes, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
          symSq (Y n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (Y n jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0) = ∑ n ∈ R.yModes,
          (symSq (Y n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (Y n jl.1 jl.2) / S.antiWeight n jl.1 jl.2) :=
      Finset.sum_congr rfl fun n _ => if_pos (hcnd n)
    have eW : (∑ n ∈ S.resolved ∪ S.band, if (n ∉ S.resolved ∨ S.degHigh < max jl.1 jl.2) then
          symSq (W n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (W n jl.1 jl.2) / S.antiWeight n jl.1 jl.2
        else 0) = ∑ n ∈ S.resolved ∪ S.band,
          (symSq (W n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (W n jl.1 jl.2) / S.antiWeight n jl.1 jl.2) :=
      Finset.sum_congr rfl fun n _ => if_pos (hcnd n)
    have hS : ∀ n ∈ R.yModes, |CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n jl.1 jl.2|
        ≤ 2 * (S.symWeight n jl.1 jl.2 * symSq (σ n jl.1 jl.2) + S.antiWeight n jl.1 jl.2 * antiSq (σ n jl.1 jl.2))
          + 2 * (symSq (Y n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (Y n jl.1 jl.2) / S.antiWeight n jl.1 jl.2)
          + (if n ∈ S.resolved ∪ S.band then
              2 * (symSq (W n jl.1 jl.2) / S.symWeight n jl.1 jl.2 + antiSq (W n jl.1 jl.2) / S.antiWeight n jl.1 jl.2)
            else 0) := by
      intro n _
      unfold CellScalars.sharpStrainTerm
      rw [if_pos (hcnd n), hT]
      exact strain_abs (sym_pos hd (hcnd n)) (anti_pos hd (hcnd n)) _ _ _ _
    have hV : ∀ n ∈ S.resolved, |CellScalars.sharpVelocityTerm c K S R B μ v G τ n jl.1 jl.2|
        ≤ 2 * (S.velWeight n jl.1 jl.2 * vecSq (τ n jl.1 jl.2)) + 2 * (vecSq (Yv n jl.1 jl.2) / S.velWeight n jl.1 jl.2)
          + 2 * (vecSq (Wv n jl.1 jl.2) / S.velWeight n jl.1 jl.2) := by
      intro n hn
      unfold CellScalars.sharpVelocityTerm
      rw [if_pos hlt.le, hTv]
      exact vel_abs (vel_pos hd hn hlt.le) _ _ _
    have s1 := Finset.abs_sum_le_sum_abs (fun n => CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n jl.1 jl.2) R.yModes
    have s2 := Finset.sum_le_sum hS
    have s3 := Finset.abs_sum_le_sum_abs (fun n => CellScalars.sharpVelocityTerm c K S R B μ v G τ n jl.1 jl.2) S.resolved
    have s4 := Finset.sum_le_sum hV
    simp only [Finset.sum_add_distrib] at s2 s4
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 hd.yModes_contain] at s2
    simp only [← Finset.mul_sum] at s2 s4
    have s5 := abs_add_le (∑ n ∈ R.yModes, CellScalars.sharpStrainTerm c K S R B μ κ ζ v G σ n jl.1 jl.2)
      (∑ n ∈ S.resolved, CellScalars.sharpVelocityTerm c K S R B μ v G τ n jl.1 jl.2)
    rw [eB, eW]
    simp only [Finset.sum_add_distrib] at s2 s4 ⊢
    linarith
  · simp [hfar]

end CellSharpBoundInternal

open CellSharpBoundInternal in
theorem cellSharpBound_of (h1 : SharpTargetSquareStatement) (h2 : SharpCoreStatement) :
    CellSharpBoundStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hd hax x hx ζ μ hμ
  obtain ⟨hY, hV, hX, hXv⟩ := h1 α hα1 hα2 c hc K S B Cl R hd hax x hx ζ
  obtain ⟨σ, τ, hE, hmain⟩ := h2 α hα1 hα2 c hc K S B Cl R hd hax x hx ζ μ hμ
  have sY : ∀ n ∈ R.yModes, Summable (fun jl : ℕ × ℕ => sumSq (fun a b =>
      B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)) :=
    fun n hn => sumSq_summable
      (fun jl a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) jl.1 jl.2)
      (fun a b => coef_summable hd.bases _ (hY n hn a b).1 (hY n hn a b).2)
  have sV : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (fun a =>
      B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) jl.1 jl.2)) :=
    fun n hn => vecSq_summable
      (fun jl a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) jl.1 jl.2)
      (fun a => coef_summable hd.bases _ (hV n hn a).1 (hV n hn a).2)
  have sW : ∀ n ∈ S.resolved ∪ S.band, Summable (fun jl : ℕ × ℕ => sumSq (fun i q =>
      ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)) :=
    fun n hn => combo_summable R.rowSet μ
      (fun a jl i q => B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) jl.1 jl.2)
      (fun a ha i q => coef_summable hd.bases _ (hX a ha n hn i q).1 (hX a ha n hn i q).2)
  have sWv : ∀ n ∈ S.resolved, Summable (fun jl : ℕ × ℕ => vecSq (fun i =>
      ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) * B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) jl.1 jl.2)) :=
    fun n hn => combo_vec_summable R.rowSet μ
      (fun a jl i => B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) jl.1 jl.2)
      (fun a ha i => coef_summable hd.bases _ (hXv a ha n hn i).1 (hXv a ha n hn i).2)
  have hb := far_y hd R.yModes
    (fun n j l a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l)
    (fun n j l a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) j l) sY sV
  have hw := far_y hd (S.resolved ∪ S.band)
    (fun n j l i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
    (fun n j l i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l) sW sWv
  have hr := far_row hd (S.resolved ∪ S.band)
    (fun n j l i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
    (fun n j l i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l) sW sWv
  refine ⟨σ, τ, far_a hd μ x.2.2.2.1 ζ x.1 x.2.1 σ τ
    (fun n j l a b => B.coef K (fun p => CellScalars.yFolded c K S x.2.2.2.1 ζ x.1 x.2.1 n p a b) j l)
    (fun n j l i q => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingFolded c K S R a n p i q) j l)
    (fun n j l a => B.coef K (fun p => CellScalars.yVelocity c K S x.1 x.2.1 n p a) j l)
    (fun n j l i => ∑ a ∈ R.rowSet, ((μ a : ℝ) : ℂ) *
      B.coef K (fun p => CellScalars.rowCouplingVelocity c K R a n p i) j l)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) hE hb hw, hb, hr, hmain⟩

end CellAnalysis

end CellCert

end Breakdown

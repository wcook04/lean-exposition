import Breakdown.FracCert.StFree

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert


private theorem lp_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : Lp (α := Space) E 2) : ‖f‖ ^ 2 = ∫ ξ, ‖f ξ‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  ext ξ
  exact real_inner_self_eq_norm_sq _

private theorem norm_complexifyVec_eq (z : Space) : ‖Freq.complexifyVec z‖ = ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [Freq.complexifyVec]

private theorem integral_norm_sq_complexify (g : Freq.L2R) :
    ∫ ξ, ‖(Freq.complexify g : Space → Freq.CSpace) ξ‖ ^ 2 = ∫ y, ‖(g : Space → Space) y‖ ^ 2 := by
  apply integral_congr_ae
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := volume) Freq.complexifyVec g] with y hy
  rw [Freq.complexify, hy, norm_complexifyVec_eq]

private theorem toLpOrZero_coe {f : Space → Space} (hf : MemLp f 2 volume) :
    (Freq.toLpOrZero 2 f : Space → Space) =ᵐ[volume] f := by
  unfold Freq.toLpOrZero
  rw [dif_pos hf]
  exact hf.coeFn_toLp

private theorem integral_fieldSymbol_sq {P : Space → Space} (hP : MemLp P 2 volume) :
    ∫ ξ, ‖(fieldSymbol P : Space → Freq.CSpace) ξ‖ ^ 2 = ∫ y, ‖P y‖ ^ 2 := by
  have e1 : ‖fieldSymbol P‖ = ‖Freq.complexify (Freq.toLpOrZero 2 P)‖ :=
    LinearIsometryEquiv.norm_map Freq.freqTrL2 _
  rw [← lp_norm_sq (fieldSymbol P), e1, lp_norm_sq, integral_norm_sq_complexify]
  apply integral_congr_ae
  filter_upwards [toLpOrZero_coe hP] with y hy
  rw [hy]

private theorem secondTrace_sq_le (H : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondTrace H‖ ^ 2 ≤ 3 * ∑ i : Fin 3, ∑ j : Fin 3, ‖H (unitVector i) (unitVector j)‖ ^ 2 := by
  have h := norm_sum_le (Finset.univ : Finset (Fin 3)) fun j => H (unitVector j) (unitVector j)
  simp only [secondTrace, Fin.sum_univ_three] at h ⊢
  have h0 := norm_nonneg (H (unitVector 0) (unitVector 0) + H (unitVector 1) (unitVector 1) +
    H (unitVector 2) (unitVector 2))
  have key := mul_self_le_mul_self h0 h
  nlinarith [sq_nonneg (‖H (unitVector 0) (unitVector 0)‖ - ‖H (unitVector 1) (unitVector 1)‖),
    sq_nonneg (‖H (unitVector 1) (unitVector 1)‖ - ‖H (unitVector 2) (unitVector 2)‖),
    sq_nonneg (‖H (unitVector 0) (unitVector 0)‖ - ‖H (unitVector 2) (unitVector 2)‖),
    sq_nonneg ‖H (unitVector 0) (unitVector 1)‖, sq_nonneg ‖H (unitVector 0) (unitVector 2)‖,
    sq_nonneg ‖H (unitVector 1) (unitVector 0)‖, sq_nonneg ‖H (unitVector 1) (unitVector 2)‖,
    sq_nonneg ‖H (unitVector 2) (unitVector 0)‖, sq_nonneg ‖H (unitVector 2) (unitVector 1)‖]

private theorem memLp_negSecondTrace {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    MemLp (negSecondTrace H) 2 volume := by
  have hc : Continuous fun B : Space →L[ℝ] Space →L[ℝ] Space => -secondTrace B := by
    unfold secondTrace
    fun_prop
  have hm : AEStronglyMeasurable (negSecondTrace H) volume :=
    hc.comp_aestronglyMeasurable hs.measurable_second
  rw [memLp_two_iff_integrable_sq_norm hm]
  refine (hs.second_two.const_mul 3).mono' (hm.norm.pow 2) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [negSecondTrace, norm_neg] using secondTrace_sq_le (H y)

private theorem integrable_pair {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    Integrable (fun y => inner ℝ (X y) (Y y)) volume := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hX.toLp X) (hY.toLp Y)).congr ?_
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
  rw [a, b]

private theorem pair_eq_inner {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    l2Pair X Y = inner ℝ (hX.toLp X) (hY.toLp Y) := by
  rw [L2.inner_def, l2Pair]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
  rw [a, b]

private theorem l2Norm_eq_norm {X : Space → Space} (hX : MemLp X 2 volume) : l2Norm X = ‖hX.toLp X‖ := by
  have e : ∫ y, ‖X y‖ ^ 2 = ‖hX.toLp X‖ ^ 2 := by
    rw [lp_norm_sq]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp] with y hy
    rw [hy]
  rw [l2Norm, e, Real.sqrt_sq (norm_nonneg _)]

private theorem abs_pair_le {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    |l2Pair X Y| ≤ l2Norm X * l2Norm Y := by
  rw [pair_eq_inner hX hY, l2Norm_eq_norm hX, l2Norm_eq_norm hY]
  exact abs_real_inner_le_norm _ _

private theorem pointwise_le {ξ : Space} (hξ : ξ ≠ 0) {β : ℝ} (hβ : 0 ≤ β) {s : ℝ} (hs : 0 ≤ s) :
    s ≤ s / freqPow 2 ξ + freqPow β ξ ^ 2 * s := by
  have hx : 0 < 2 * π * ‖ξ‖ := by
    have := norm_pos_iff.mpr hξ
    positivity
  unfold freqPow
  rw [Real.rpow_two]
  rcases le_total (2 * π * ‖ξ‖) 1 with h | h
  · have hsq : (2 * π * ‖ξ‖) ^ 2 ≤ 1 := by nlinarith
    have h1 : s ≤ s / (2 * π * ‖ξ‖) ^ 2 := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_left hsq hs]
    have : 0 ≤ ((2 * π * ‖ξ‖) ^ β) ^ 2 * s := by positivity
    linarith
  · have h1 : 1 ≤ (2 * π * ‖ξ‖) ^ β := Real.one_le_rpow h hβ
    have h2 : 0 ≤ s / (2 * π * ‖ξ‖) ^ 2 := by positivity
    have h3 : 1 ≤ ((2 * π * ‖ξ‖) ^ β) ^ 2 := one_le_pow₀ h1
    nlinarith [mul_le_mul_of_nonneg_right h3 hs]

private theorem ae_ne_zero : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
  have : volume ({0} : Set Space) = 0 := measure_singleton 0
  filter_upwards [compl_mem_ae_iff.mpr this] with ξ hξ
  simpa using hξ


private theorem trace_le {α : ℝ} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {G : Space → (Space →L[ℝ] Space)}
    {P : Space → Space}
    (hi1 : Integrable (fun ξ => ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ) volume)
    (hg : ∫ y, entrySq (G y) = ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ)
    (hn : ∫ y, ‖secondTrace (H y)‖ ^ 2 = ∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2)
    (hsym : (fieldSymbol P : Space → Freq.CSpace) =ᵐ[volume]
      fun ξ => freqPow (2 * α - 2) ξ • (secondSymbol H : Space → Freq.CSpace) ξ)
    (hP : MemLp P 2 volume) (hα : 0 ≤ 2 * α - 2) :
    ∫ y, ‖secondTrace (H y)‖ ^ 2 ≤ (∫ y, entrySq (G y)) + ∫ y, ‖P y‖ ^ 2 := by
  have iS : Integrable (fun ξ => ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) volume :=
    (Lp.memLp (secondSymbol H)).integrable_norm_pow two_ne_zero
  have eFS : (fun ξ => ‖(fieldSymbol P : Space → Freq.CSpace) ξ‖ ^ 2) =ᵐ[volume]
      fun ξ => freqPow (2 * α - 2) ξ ^ 2 * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    filter_upwards [hsym] with ξ hξ
    rw [hξ, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have iPS : Integrable
      (fun ξ => freqPow (2 * α - 2) ξ ^ 2 * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) volume :=
    ((Lp.memLp (fieldSymbol P)).integrable_norm_pow two_ne_zero).congr eFS
  have hpS : ∫ y, ‖P y‖ ^ 2 =
      ∫ ξ, freqPow (2 * α - 2) ξ ^ 2 * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 := by
    rw [← integral_fieldSymbol_sq hP]
    exact integral_congr_ae eFS
  have e : ∫ ξ, (‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ +
      freqPow (2 * α - 2) ξ ^ 2 * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2) =
      (∫ ξ, ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 / freqPow 2 ξ) +
      ∫ ξ, freqPow (2 * α - 2) ξ ^ 2 * ‖(secondSymbol H : Space → Freq.CSpace) ξ‖ ^ 2 :=
    integral_add hi1 iPS
  rw [hn, hg, hpS, ← e]
  apply integral_mono_ae iS (hi1.add iPS)
  filter_upwards [ae_ne_zero] with ξ hξ
  exact pointwise_le hξ hα (sq_nonneg _)

private theorem sq_split {X Y Z : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume)
    (hsum : ∀ᵐ y ∂volume, X y + Y y = Z y) :
    ∫ y, ‖Z y‖ ^ 2 = (∫ y, ‖X y‖ ^ 2) + 2 * l2Pair X Y + ∫ y, ‖Y y‖ ^ 2 := by
  have iX : Integrable (fun y => ‖X y‖ ^ 2) volume := hX.integrable_norm_pow two_ne_zero
  have iY : Integrable (fun y => ‖Y y‖ ^ 2) volume := hY.integrable_norm_pow two_ne_zero
  have iXY : Integrable (fun y => 2 * inner ℝ (X y) (Y y)) volume := (integrable_pair hX hY).const_mul 2
  have e : (fun y => ‖Z y‖ ^ 2) =ᵐ[volume]
      fun y => ‖X y‖ ^ 2 + 2 * inner ℝ (X y) (Y y) + ‖Y y‖ ^ 2 := by
    filter_upwards [hsum] with y hy
    rw [← hy, norm_add_sq_real]
  have e2 : ∫ y, (‖X y‖ ^ 2 + 2 * inner ℝ (X y) (Y y) + ‖Y y‖ ^ 2) =
      (∫ y, (‖X y‖ ^ 2 + 2 * inner ℝ (X y) (Y y))) + ∫ y, ‖Y y‖ ^ 2 := integral_add (iX.add iXY) iY
  have e3 : ∫ y, (‖X y‖ ^ 2 + 2 * inner ℝ (X y) (Y y)) =
      (∫ y, ‖X y‖ ^ 2) + ∫ y, 2 * inner ℝ (X y) (Y y) := integral_add iX iXY
  rw [integral_congr_ae e, e2, e3, integral_const_mul]
  rfl

private theorem pair_split {X Y Z W : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume)
    (hW : MemLp W 2 volume) (hsum : ∀ᵐ y ∂volume, X y + Y y = Z y) :
    l2Pair Z W = l2Pair X W + l2Pair Y W := by
  have e : ∫ y, (inner ℝ (X y) (W y) + inner ℝ (Y y) (W y)) =
      (∫ y, inner ℝ (X y) (W y)) + ∫ y, inner ℝ (Y y) (W y) :=
    integral_add (integrable_pair hX hW) (integrable_pair hY hW)
  unfold l2Pair
  rw [← e]
  apply integral_congr_ae
  filter_upwards [hsum] with y hy
  rw [← hy, inner_add_left]

private theorem final_alg {κ f g n p A B : ℝ} (hk : 0 < κ) (hk1 : κ ≤ 1) (hf0 : 0 ≤ f) (hg0 : 0 ≤ g)
    (hn0 : 0 ≤ n) (hpf : p ≤ f) (hp0 : 0 ≤ p) (hn : n ^ 2 ≤ g ^ 2 + p ^ 2) (hA : |A| ≤ f * n)
    (hB : |B| ≤ p * n) (hsplit : κ * g ^ 2 + B = A) : n + g ≤ (6 / κ + 1) * f := by
  have hngf : n ≤ g + f := by
    have h1 : p ^ 2 ≤ f ^ 2 := by nlinarith
    have : n ^ 2 ≤ (g + f) ^ 2 := by nlinarith
    nlinarith
  have hkg : κ * g ^ 2 ≤ 2 * f * n := by
    have h5 := le_abs_self A
    have h6 := neg_abs_le B
    have h7 : p * n ≤ f * n := mul_le_mul_of_nonneg_right hpf hn0
    linarith
  have hfn : 2 * f * n ≤ 2 * f * (g + f) := by
    have := mul_le_mul_of_nonneg_left hngf hf0
    linarith
  have h3f : κ * g ≤ 3 * f := by
    by_contra hcon0
    have hcon : 3 * f < κ * g := lt_of_not_ge hcon0
    have hgk : κ * g ≤ g := by nlinarith
    have hgpos : 0 < g := by linarith
    have h8 : 3 * f * g < κ * g * g := mul_lt_mul_of_pos_right hcon hgpos
    have h9 : 0 ≤ f * (g - 2 * f) := mul_nonneg hf0 (by linarith)
    nlinarith
  have hg3 : g ≤ 3 / κ * f := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hk]
    linarith
  have e : (6 / κ + 1) * f = 2 * (3 / κ * f) + f := by ring
  rw [e]
  linarith


theorem freeBounds_grouped_of (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement)
    (h3 : DriftEnergyStatement) (h4 : DriftPowerStatement) :
    ∀ α : ℝ, 1 < α → α < 5 / 4 → ∃ C₀ : ℝ, ∀ (a : ℝ) (m : ℕ) (v : Space → Space)
      (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P F : Space → Space),
      IsSecondOrderField m v G H → IsWeakFractionalPower α v P → MemLp (driftField α a v G) 2 volume →
      MemLp F 2 volume → (∀ᵐ y ∂volume, driftField α a v G y + P y = F y) →
      l2Norm P ≤ l2Norm F ∧ l2Norm (driftField α a v G) ≤ l2Norm F ∧
      (1 - 3 / (4 * α)) * (∫ y, entrySq (G y)) + l2Pair P (negSecondTrace H) = l2Pair F (negSecondTrace H) ∧
      Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) + Real.sqrt (∫ y, entrySq (G y)) ≤ C₀ * l2Norm F := by
  intro α hα1 hα2
  have hk : 0 < 1 - 3 / (4 * α) := by
    have : 3 / (4 * α) < 1 := by
      rw [div_lt_one (by linarith)]
      linarith
    linarith
  have hk1 : 1 - 3 / (4 * α) ≤ 1 := by
    have : 0 ≤ 3 / (4 * α) := by positivity
    linarith
  have hc2 : 0 ≤ 3 / 2 - 5 / (4 * α) := by
    have : 5 / (4 * α) ≤ 5 / 4 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      nlinarith
    linarith
  refine ⟨6 / (1 - 3 / (4 * α)) + 1, ?_⟩
  intro a m v G H P F hs hP hD hF hsum
  have hP2 : MemLp P 2 volume := hP.1
  have hN : MemLp (negSecondTrace H) 2 volume := memLp_negSecondTrace hs
  obtain ⟨hi1, hg, -, hn⟩ := h1 m v G H hs
  have hsym := h2 α hα1 (by linarith) m v G H P hs hP
  have hDN := h3 α hα1 hα2 a m v G H hs hD
  obtain ⟨-, hDP⟩ := h4 α hα1 hα2 a m v G H P hs hP hD
  have hDPnn : 0 ≤ l2Pair (driftField α a v G) P := by
    rw [hDP]
    refine mul_nonneg hc2 (integral_nonneg fun ξ => mul_nonneg ?_ (sq_nonneg _))
    exact Real.rpow_nonneg (by positivity) _
  have hFsq := sq_split hD hP2 hsum
  have hD0 : 0 ≤ ∫ y, ‖driftField α a v G y‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hP0 : 0 ≤ ∫ y, ‖P y‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hpf : ∫ y, ‖P y‖ ^ 2 ≤ ∫ y, ‖F y‖ ^ 2 := by rw [hFsq]; linarith
  have hdf : ∫ y, ‖driftField α a v G y‖ ^ 2 ≤ ∫ y, ‖F y‖ ^ 2 := by rw [hFsq]; linarith
  have hb1 : l2Norm P ≤ l2Norm F := Real.sqrt_le_sqrt hpf
  have hb2 : l2Norm (driftField α a v G) ≤ l2Norm F := Real.sqrt_le_sqrt hdf
  have hFN := pair_split hD hP2 hN hsum
  have hb3 : (1 - 3 / (4 * α)) * (∫ y, entrySq (G y)) + l2Pair P (negSecondTrace H) =
      l2Pair F (negSecondTrace H) := by rw [hFN, hDN]
  refine ⟨hb1, hb2, hb3, ?_⟩
  have hnle := trace_le hi1 hg hn hsym hP2 (by linarith)
  have hg0 : 0 ≤ ∫ y, entrySq (G y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hF0 : 0 ≤ ∫ y, ‖F y‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hn0 : 0 ≤ ∫ y, ‖secondTrace (H y)‖ ^ 2 := integral_nonneg fun y => sq_nonneg _
  have hNn : l2Norm (negSecondTrace H) = Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) := by
    simp only [l2Norm, negSecondTrace, norm_neg]
  have hA := abs_pair_le hF hN
  have hB := abs_pair_le hP2 hN
  rw [hNn] at hA hB
  have hgsq : Real.sqrt (∫ y, entrySq (G y)) ^ 2 = ∫ y, entrySq (G y) := Real.sq_sqrt hg0
  have hnsq : Real.sqrt (∫ y, ‖secondTrace (H y)‖ ^ 2) ^ 2 = ∫ y, ‖secondTrace (H y)‖ ^ 2 :=
    Real.sq_sqrt hn0
  have hpsq : l2Norm P ^ 2 = ∫ y, ‖P y‖ ^ 2 := Real.sq_sqrt hP0
  refine final_alg hk hk1 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hb1 (Real.sqrt_nonneg _) ?_ hA hB ?_
  · rw [hnsq, hgsq, hpsq]
    exact hnle
  · rw [hgsq]
    exact hb3

theorem freeBounds_of (h1 : SecondSymbolEnergyStatement) (h2 : WeakPowerSymbolStatement)
    (h3 : DriftEnergyStatement) (h4 : DriftPowerStatement) : FreeBoundsStatement :=
  freeBounds_grouped_of h1 h2 h3 h4

end SteadyCert

end Breakdown

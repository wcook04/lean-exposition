import Breakdown.Torus.ShellTorusBase
import Breakdown.Torus.Advection
import Breakdown.Torus.CoefCalculus

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ShellTorus.Internal

theorem finiteCellMeasure : IsFiniteMeasure (volume.restrict cell) :=
  isFiniteMeasure_restrict.2 FreqTrSeries.Internal.isCompact_cell.measure_lt_top.ne

theorem character_sub_eq (k m : Lattice) (x : Space) :
    character (k - m) x = character k x * character (-m) x := by
  rw [sub_eq_add_neg, Trilinear.Internal.character_add]

theorem integral_character_mul (k j : Lattice) :
    ∫ x in cell, character k x * character (-j) x = if j = k then 1 else 0 := by
  simp_rw [← character_sub_eq]
  rw [Trilinear.Internal.integral_character]
  by_cases h : j = k
  · simp [h]
  · have h' : k - j ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp [h, h']

theorem integral_norm_le_Lp (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ⊤) :
    ∃ K : NNReal, ∀ g : Lp Coef p (volume.restrict cell),
      ∫ x in cell, ‖(g : Space → Coef) x‖ ≤ K * ‖g‖ := by
  have := finiteCellMeasure
  obtain ⟨M, hM⟩ : ∃ M, M = (volume.restrict cell) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
    ⟨_, rfl⟩
  have hMt : M ≠ ⊤ := by
    rw [hM]
    refine ENNReal.rpow_ne_top_of_nonneg ?_ (measure_ne_top _ _)
    have h1 : (1 : ℝ) ≤ p.toReal := by
      have := ENNReal.toReal_mono hpt (Fact.out : (1 : ℝ≥0∞) ≤ p)
      simpa using this
    rw [ENNReal.toReal_one, div_one, sub_nonneg]
    exact div_le_one_of_le₀ h1 (by linarith)
  refine ⟨M.toNNReal, fun g => ?_⟩
  have hb := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict cell)
    (Fact.out : (1 : ℝ≥0∞) ≤ p) (Lp.aestronglyMeasurable g)
  rw [← hM] at hb
  have h2 : (eLpNorm (g : Space → Coef) 1 (volume.restrict cell)).toReal ≤
      (eLpNorm (g : Space → Coef) p (volume.restrict cell)).toReal * M.toReal := by
    rw [← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top g) hMt) hb
  rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable g), ← eLpNorm_one_eq_lintegral_enorm,
    ENNReal.coe_toNNReal_eq_toReal, Lp.norm_def]
  linarith

theorem integral_character_torusSeries (p : ℝ≥0∞) [Fact (1 ≤ p)] (hpt : p ≠ ⊤) (c : Lattice → Coef)
    (hs : Summable fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k))
    (k : Lattice) :
    ∫ x in cell, character k x • (torusSeries p c : Space → Coef) x = c k := by
  have := finiteCellMeasure
  obtain ⟨K, hK⟩ := integral_norm_le_Lp p hpt
  have hint : ∀ g : Lp Coef p (volume.restrict cell),
      Integrable (fun x => character k x • (g : Space → Coef) x) (volume.restrict cell) := fun g =>
    Force.Internal.integrableOn_character_smul k (MemLp.integrable Fact.out (Lp.memLp g))
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : Lp Coef p (volume.restrict cell) → Coef,
      Φ = fun g : Lp Coef p (volume.restrict cell) => ∫ x in cell, character k x • (g : Space → Coef) x := ⟨_, rfl⟩
  have hslope : LipschitzWith K Φ := by
    refine LipschitzWith.of_dist_le_mul fun g g' => ?_
    rw [dist_eq_norm, dist_eq_norm, hΦ]
    simp only
    rw [← integral_sub (hint g) (hint g')]
    refine (norm_integral_le_integral_norm _).trans ((le_of_eq ?_).trans (hK (g - g')))
    refine integral_congr_ae ?_
    filter_upwards [Lp.coeFn_sub g g'] with x hx
    rw [hx, Pi.sub_apply, ← smul_sub, norm_smul, FreqTrSeries.Internal.norm_character, one_mul]
  have hlim := (hslope.continuous.tendsto _).comp hs.hasSum
  have hev : ∀ s : Finset Lattice, k ∈ s →
      Φ (∑ j ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-j) x • c j)) = c k := by
    intro s hks
    rw [hΦ, TorusSeries.Internal.sum_lpOrZero]
    simp only
    have hae := (TorusSeries.Internal.memLp_of_continuous p
      (TorusSeries.Internal.continuous_partialSum c s)).coeFn_toLp
    have hae2 : ∀ᵐ x ∂(volume.restrict cell), character k x •
        (((TorusSeries.Internal.memLp_of_continuous p (TorusSeries.Internal.continuous_partialSum c s)).toLp
          (TorusSeries.Internal.partialSum c s) : Lp Coef p (volume.restrict cell)) : Space → Coef) x =
        character k x • TorusSeries.Internal.partialSum c s x := hae.mono fun x hx => by rw [hx]
    rw [integral_congr_ae hae2]
    unfold TorusSeries.Internal.partialSum
    simp_rw [Finset.smul_sum]
    have hi : ∀ j ∈ s, Integrable (fun x => character k x • (character (-j) x • c j))
        (volume.restrict cell) := fun j _ => ((FreqTrSeries.Internal.continuous_character k).smul
      (TorusSeries.Internal.continuous_term c j)).continuousOn.integrableOn_compact
        FreqTrSeries.Internal.isCompact_cell
    rw [integral_finsetSum s hi]
    simp_rw [smul_smul, integral_smul_const, integral_character_mul, ite_smul, one_smul, zero_smul]
    simp [hks]
  have h2 : Tendsto (fun s : Finset Lattice =>
      Φ (∑ j ∈ s, lpOrZero p (volume.restrict cell) (fun x => character (-j) x • c j)))
      (SummationFilter.unconditional Lattice).filter (𝓝 (c k)) :=
    tendsto_const_nhds.congr' (Filter.eventually_atTop.2 ⟨{k}, fun s hs =>
      (hev s (hs (Finset.mem_singleton_self k))).symm⟩)
  have := tendsto_nhds_unique hlim h2
  rw [hΦ] at this
  exact this

theorem real_torusSeries (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Lattice → Coef)
    (hc : ∀ k i, c (-k) i = starRingEnd ℂ (c k i))
    (hs : Summable fun k => lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)) :
    ∀ᵐ x ∂(volume.restrict cell),
      complexify (Freq.realVec ((torusSeries p c : Space → Coef) x)) = (torusSeries p c : Space → Coef) x := by
  have hterm : ∀ k, Freq.conjVec.compLpL p (volume.restrict cell)
      (lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c k)) =
      lpOrZero p (volume.restrict cell) (fun x => character (-(-k)) x • c (-k)) := by
    intro k
    rw [TorusSeries.Internal.lpOrZero_term, TorusSeries.Internal.lpOrZero_term]
    refine Lp.ext ?_
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p) Freq.conjVec
        ((TorusSeries.Internal.memLp_of_continuous p (TorusSeries.Internal.continuous_term c k)).toLp _),
      (TorusSeries.Internal.memLp_of_continuous p (TorusSeries.Internal.continuous_term c k)).coeFn_toLp,
      (TorusSeries.Internal.memLp_of_continuous p
        (TorusSeries.Internal.continuous_term c (-k))).coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3]
    ext i
    show star ((character (-k) x • c k) i) = (character (-(-k)) x • c (-k)) i
    rw [PiLp.smul_apply, PiLp.smul_apply, smul_eq_mul, smul_eq_mul, hc, star_mul', Complex.star_def,
      Trilinear.Internal.conj_character]
  have hT : Freq.conjVec.compLpL p (volume.restrict cell) (torusSeries p c) = torusSeries p c := by
    unfold torusSeries
    rw [ContinuousLinearMap.map_tsum _ hs]
    simp only [hterm]
    exact (Equiv.neg Lattice).tsum_eq (fun k => lpOrZero p (volume.restrict cell)
      (fun x => character (-k) x • c k))
  filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := p) Freq.conjVec (torusSeries p c)] with x hx
  rw [hT] at hx
  ext i
  have hi : starRingEnd ℂ (((torusSeries p c : Space → Coef) x) i) = ((torusSeries p c : Space → Coef) x) i := by
    have h := congrArg (fun v : Coef => v i) hx
    exact h.symm
  show ((((torusSeries p c : Space → Coef) x) i).re : ℂ) = ((torusSeries p c : Space → Coef) x) i
  exact Complex.conj_eq_iff_re.mp hi

theorem coeff_neg_apply (z : V) (k : Lattice) (i : Fin 3) :
    coeff z (-k) i = starRingEnd ℂ (coeff z k i) := by
  have h : ((z : Seq) (-k)) i = starRingEnd ℂ (((z : Seq) k) i) := z.2.1 k i
  simp only [coeff, PiLp.smul_apply, FreqTrSeries.Internal.weight_neg, h]
  simp [Complex.real_smul]

theorem gradCoef_neg_apply (j : Fin 3) (z : V) (k : Lattice) (i : Fin 3) :
    gradCoef j z (-k) i = starRingEnd ℂ (gradCoef j z k i) := by
  simp only [gradCoef, PiLp.smul_apply, smul_eq_mul, coeff_neg_apply, map_mul, Complex.conj_ofReal,
    Complex.conj_I, map_intCast, Pi.neg_apply, Int.cast_neg, map_ofNat]
  ring

theorem hasSum_scalar_series {H : Space → Coef} (hH : IntegrableOn H cell) {β : Lattice → ℂ}
    (hβ : Summable fun l => ‖β l‖) {g : Space → ℂ}
    (hg : ∀ x, HasSum (fun l => character (-l) x * β l) (g x)) (k : Lattice) :
    HasSum (fun l => β l • ∫ x in cell, character (k - l) x • H x)
      (∫ x in cell, g x • (character k x • H x)) := by
  have key : HasSum (fun l => ∫ x in cell, β l • (character (k - l) x • H x))
      (∫ x in cell, g x • (character k x • H x)) := by
    refine hasSum_integral_of_dominated_convergence (fun l x => ‖β l‖ * ‖H x‖) (fun l => ?_)
      (fun l => ?_) ?_ ?_ ?_
    · exact (Force.Internal.integrableOn_character_smul (k - l) hH).aestronglyMeasurable.const_smul (β l)
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, norm_smul, FreqTrSeries.Internal.norm_character, one_mul]
    · exact Filter.Eventually.of_forall fun x => hβ.mul_right _
    · simp_rw [tsum_mul_right]
      exact hH.norm.const_mul _
    · refine Filter.Eventually.of_forall fun x => ?_
      have e : (fun l => β l • (character (k - l) x • H x)) =
          fun l => (character (-l) x * β l) • (character k x • H x) := by
        funext l
        rw [smul_smul, smul_smul, character_sub_eq]
        congr 1
        ring
      rw [e]
      exact (hg x).smul_const _
  simpa only [integral_smul] using key

theorem hasSum_vector_series {h : Space → ℂ} (hh : IntegrableOn h cell) {β : Lattice → Coef}
    (hβ : Summable fun l => ‖β l‖) {g : Space → Coef}
    (hg : ∀ x, HasSum (fun l => character (-l) x • β l) (g x)) (k : Lattice) :
    HasSum (fun l => (∫ x in cell, character (k - l) x * h x) • β l)
      (∫ x in cell, h x • (character k x • g x)) := by
  have hc : ∀ l, IntegrableOn (fun x => character (k - l) x * h x) cell := fun l => by
    simpa only [smul_eq_mul] using hh.continuousOn_smul
      (FreqTrSeries.Internal.continuous_character (k - l)).continuousOn FreqTrSeries.Internal.isCompact_cell
  have key : HasSum (fun l => ∫ x in cell, (character (k - l) x * h x) • β l)
      (∫ x in cell, h x • (character k x • g x)) := by
    refine hasSum_integral_of_dominated_convergence (fun l x => ‖h x‖ * ‖β l‖) (fun l => ?_)
      (fun l => ?_) ?_ ?_ ?_
    · exact (hc l).aestronglyMeasurable.smul_const (β l)
    · exact Filter.Eventually.of_forall fun x => by
        rw [norm_smul, norm_mul, FreqTrSeries.Internal.norm_character, one_mul]
    · exact Filter.Eventually.of_forall fun x => hβ.mul_left _
    · simp_rw [tsum_mul_left]
      exact hh.norm.mul_const _
    · refine Filter.Eventually.of_forall fun x => ?_
      have e : (fun l => (character (k - l) x * h x) • β l) =
          fun l => (h x * character k x) • (character (-l) x • β l) := by
        funext l
        rw [smul_smul, character_sub_eq]
        congr 1
        ring
      rw [e, smul_smul]
      exact (hg x).const_smul _
  simpa only [integral_smul_const] using key

theorem complexify_finsum (F : Fin 3 → Space) : complexify (∑ j, F j) = ∑ j, complexify (F j) :=
  map_sum CoefCalculus.Internal.complexifyL F Finset.univ

theorem complexify_add_smul (r s : ℝ) (v w : Space) :
    complexify (r • v + s • w) = (r : ℂ) • complexify v + (s : ℂ) • complexify w := by
  change CoefCalculus.Internal.complexifyL (r • v + s • w) = _
  rw [map_add, map_smul, map_smul, Complex.coe_smul, Complex.coe_smul]
  rfl

theorem advCoef_product (hF : FreqTrSeriesSpec) {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodic f) (hd : ∀ x, divergenceAt f x = 0) (a z : V)
    (ha : ∀ k, coeff a k = freqTrCoef f k) (k : Lattice) :
    advCoef a z k + advCoef z a k = freqTrCoef (productField f z) k := by
  have := finiteCellMeasure
  obtain ⟨-, hsum, hser⟩ := hF f hf hp hd
  have hI6 : IntegrableOn (torusSeries 6 (coeff z) : Space → Coef) cell :=
    MemLp.integrable (by norm_num) (Lp.memLp _)
  have hI2 : ∀ j, IntegrableOn (torusSeries 2 (gradCoef j z) : Space → Coef) cell := fun j =>
    MemLp.integrable (by norm_num) (Lp.memLp _)
  have hC6 : ∀ l, ∫ x in cell, character l x • (torusSeries 6 (coeff z) : Space → Coef) x = coeff z l :=
    integral_character_torusSeries 6 (by simp) (coeff z) (summable_torusSeries 6 (Or.inr rfl) z)
  have hC2 : ∀ j l, ∫ x in cell, character l x • (torusSeries 2 (gradCoef j z) : Space → Coef) x =
      gradCoef j z l := fun j =>
    integral_character_torusSeries 2 (by simp) (gradCoef j z) (summable_torusSeries_grad j z)
  have hR6 : ∀ᵐ x ∂(volume.restrict cell),
      complexify (zField z x) = (torusSeries 6 (coeff z) : Space → Coef) x :=
    real_torusSeries 6 (coeff z) (coeff_neg_apply z) (summable_torusSeries 6 (Or.inr rfl) z)
  have hR2 : ∀ᵐ x ∂(volume.restrict cell), ∀ j,
      complexify (gField j z x) = (torusSeries 2 (gradCoef j z) : Space → Coef) x :=
    ae_all_iff.2 fun j => real_torusSeries 2 (gradCoef j z) (gradCoef_neg_apply j z)
      (summable_torusSeries_grad j z)
  have hP1 : ∀ j : Fin 3, HasSum (fun l => freqTrCoef f l j • gradCoef j z (k - l))
      (∫ x in cell, ((f x j : ℝ) : ℂ) •
        (character k x • (torusSeries 2 (gradCoef j z) : Space → Coef) x)) := by
    intro j
    have hgj : ∀ x, HasSum (fun l => character (-l) x * freqTrCoef f l j) ((f x j : ℝ) : ℂ) := fun x => by
      have h1 := (hser x).mapL (EuclideanSpace.proj j : Coef →L[ℂ] ℂ)
      simpa [Advection.Internal.complexify_apply] using h1
    have key := hasSum_scalar_series (hI2 j) (β := fun l => freqTrCoef f l j)
      (hsum.of_nonneg_of_le (fun _ => norm_nonneg _) fun l => PiLp.norm_apply_le (freqTrCoef f l) j)
      hgj k
    simpa only [hC2] using key
  have hh : ∀ j : Fin 3, IntegrableOn (fun x => ((torusSeries 6 (coeff z) : Space → Coef) x) j) cell :=
    fun j => (EuclideanSpace.proj j : Coef →L[ℂ] ℂ).integrable_comp hI6
  have hP2 : ∀ j : Fin 3, HasSum
      (fun l => coeff z (k - l) j • ((2 * π * Complex.I * (l j : ℂ)) • freqTrCoef f l))
      (∫ x in cell, ((torusSeries 6 (coeff z) : Space → Coef) x) j •
        (character k x • complexify (fderiv ℝ f x (unitVector j)))) := by
    intro j
    have hD := FreqTrSeries.Internal.hasSum_apply coefDeriv
      (FreqTrSeries.Internal.contDiff_partialD j hf) (FreqTrSeries.Internal.isPeriodic_partialD j hp)
    have hS := (FreqTrSeries.Internal.summable_bounds coefDeriv
      (FreqTrSeries.Internal.contDiff_partialD j hf) (FreqTrSeries.Internal.isPeriodic_partialD j hp)).1
    have key := hasSum_vector_series (hh j) hS hD k
    have e1 : ∀ l, ∫ x in cell, character (k - l) x * ((torusSeries 6 (coeff z) : Space → Coef) x) j =
        coeff z (k - l) j := fun l => by
      rw [← hC6 (k - l), Force.Internal.integral_apply (Force.Internal.integrableOn_character_smul _ hI6)]
      simp only [PiLp.smul_apply, smul_eq_mul]
    have e2 : ∀ l, freqTrCoef (FreqTrSeries.Internal.partialD j f) l =
        (2 * π * Complex.I * (l j : ℂ)) • freqTrCoef f l := fun l =>
      FreqTrSeries.Internal.freqTrCoef_partialD coefDeriv j hf hp l
    simp only [e1, e2] at key
    exact key
  have hall1 := hasSum_sum (s := Finset.univ) (fun j _ => hP1 j)
  have hall2 := hasSum_sum (s := Finset.univ) (fun j _ => hP2 j)
  have hA1 : advCoef a z k = ∑ j : Fin 3, ∫ x in cell, ((f x j : ℝ) : ℂ) •
      (character k x • (torusSeries 2 (gradCoef j z) : Space → Coef) x) := by
    unfold advCoef
    refine ((Equiv.subLeft k).hasSum_iff.mp ?_).tsum_eq
    convert hall1 using 1
    funext l
    simp only [Function.comp_apply, Equiv.subLeft_apply, sub_sub_cancel, ha l]
    rw [divPairing, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gradCoef, smul_smul]
    congr 1
    push_cast
    ring
  have hA2 : advCoef z a k = ∑ j : Fin 3, ∫ x in cell, ((torusSeries 6 (coeff z) : Space → Coef) x) j •
      (character k x • complexify (fderiv ℝ f x (unitVector j))) := by
    unfold advCoef
    rw [← hall2.tsum_eq]
    congr 1
    funext l
    rw [ha l, divPairing, Finset.mul_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul]
    congr 1
    push_cast
    ring
  have hAint : ∀ j : Fin 3, Integrable (fun x => ((f x j : ℝ) : ℂ) •
      (character k x • (torusSeries 2 (gradCoef j z) : Space → Coef) x)) (volume.restrict cell) :=
    fun j => (Force.Internal.integrableOn_character_smul k (hI2 j)).continuousOn_smul
      (Complex.continuous_ofReal.comp ((PiLp.continuous_apply 2 _ j).comp hf.continuous)).continuousOn
      FreqTrSeries.Internal.isCompact_cell
  have hBint : ∀ j : Fin 3, Integrable (fun x => ((torusSeries 6 (coeff z) : Space → Coef) x) j •
      (character k x • complexify (fderiv ℝ f x (unitVector j)))) (volume.restrict cell) :=
    fun j => (hh j).smul_continuousOn ((FreqTrSeries.Internal.continuous_character k).smul
      (Advection.Internal.continuous_partial hf j)).continuousOn FreqTrSeries.Internal.isCompact_cell
  have hABint : ∀ j : Fin 3, Integrable (fun x => ((f x j : ℝ) : ℂ) •
      (character k x • (torusSeries 2 (gradCoef j z) : Space → Coef) x) +
      ((torusSeries 6 (coeff z) : Space → Coef) x) j •
      (character k x • complexify (fderiv ℝ f x (unitVector j)))) (volume.restrict cell) :=
    fun j => (hAint j).add (hBint j)
  rw [hA1, hA2, ← Finset.sum_add_distrib,
    Finset.sum_congr rfl fun j _ => (integral_add (hAint j) (hBint j)).symm,
    ← integral_finsetSum _ fun j _ => hABint j]
  unfold freqTrCoef
  refine integral_congr_ae ?_
  filter_upwards [hR6, hR2] with x h6 h2
  simp only [productField]
  rw [complexify_finsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [complexify_add_smul, smul_add, h2 j]
  have hz : ((zField z x j : ℝ) : ℂ) = ((torusSeries 6 (coeff z) : Space → Coef) x) j := by
    rw [← h6]
    rfl
  rw [hz, smul_comm (character k x), smul_comm (character k x)]

end ShellTorus.Internal

end Breakdown.Periodic

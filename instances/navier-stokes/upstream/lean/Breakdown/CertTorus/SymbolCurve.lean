import Breakdown.CertTorus.RegularStatements

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.SymbolCurve

theorem measurable_lerayC_prod : Measurable (fun p : Space × CSpace => divFreeC p.1 p.2) := by
  have hq : Measurable freqVec := complexifyVec.continuous.measurable
  unfold divFreeC
  fun_prop

def velOf (g : Space → CSpace) (ξ : Space) : CSpace :=
  ((2 * π * ‖ξ‖)⁻¹ : ℝ) • divFreeC ξ ((1 / 2 : ℝ) • (g ξ + conjVec (g (-ξ))))

theorem velSymbol_eq (x : X) : velSymbol x = velOf (symX x) := rfl

theorem measurable_velOf {g : Space → CSpace} (hg : Measurable g) : Measurable (velOf g) := by
  have h0 : Measurable fun ξ : Space => g ξ + conjVec (g (-ξ)) :=
    hg.add (conjVec.continuous.measurable.comp (hg.comp measurable_neg))
  have h1 : Measurable fun ξ : Space => (1 / 2 : ℝ) • (g ξ + conjVec (g (-ξ))) :=
    h0.const_smul (1 / 2 : ℝ)
  have h2 : Measurable fun ξ : Space => divFreeC ξ ((1 / 2 : ℝ) • (g ξ + conjVec (g (-ξ)))) :=
    measurable_lerayC_prod.comp (measurable_id.prodMk h1)
  have h3 : Measurable fun ξ : Space => ((2 * π * ‖ξ‖)⁻¹ : ℝ) :=
    (measurable_const.mul measurable_norm).inv
  exact h3.smul h2

theorem divFreeC_sub (ξ : Space) (z w : CSpace) : divFreeC ξ (z - w) = divFreeC ξ z - divFreeC ξ w := by
  ext i
  simp [divFreeC, Fin.sum_univ_three]
  ring

theorem velOf_sub (g h : Space → CSpace) : velOf (g - h) = velOf g - velOf h := by
  funext ξ
  simp only [velOf, Pi.sub_apply, map_sub]
  rw [show g ξ - h ξ + (conjVec (g (-ξ)) - conjVec (h (-ξ))) =
      (g ξ + conjVec (g (-ξ))) - (h ξ + conjVec (h (-ξ))) by abel, smul_sub, divFreeC_sub, smul_sub]

theorem velOf_congr_ae {g h : Space → CSpace} (hgh : g =ᵐ[volume] h) :
    velOf g =ᵐ[volume] velOf h := by
  have hn : g ∘ Neg.neg =ᵐ[volume] h ∘ Neg.neg :=
    (Measure.measurePreserving_neg (volume : Measure Space)).quasiMeasurePreserving.ae_eq_comp hgh
  filter_upwards [hgh, hn] with ξ h1 h2
  simp only [Function.comp_apply] at h2
  simp only [velOf, h1, h2]

theorem symX_sub_ae (x y : X) : symX (x - y) =ᵐ[volume] symX x - symX y := by
  unfold symX
  rw [Submodule.coe_sub]
  exact Lp.coeFn_sub _ _

theorem velSymbol_sub_ae (x y : X) :
    velSymbol (x - y) =ᵐ[volume] velSymbol x - velSymbol y := by
  rw [velSymbol_eq, velSymbol_eq, velSymbol_eq, ← velOf_sub]
  exact velOf_congr_ae (symX_sub_ae x y)

theorem measurable_velSymbol (x : X) : Measurable (velSymbol x) :=
  measurable_velOf (Lp.stronglyMeasurable _).measurable

theorem lintegral_weightL1 (k : ℕ) (g : Space → ℝ≥0∞) :
    ∫⁻ ξ, g ξ ∂weightL1Measure k = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * g ξ :=
  lintegral_weightedVolume k g

theorem volume_ac_weightL1 (k : ℕ) : (volume : Measure Space) ≪ weightL1Measure k :=
  withDensity_absolutelyContinuous' (SmoothFlow.Internal.measurable_weight k).aemeasurable
    (Eventually.of_forall (SmoothFlow.Internal.weight_ne_zero k))

theorem toWeightL1_eq {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    toWeightL1 k f = hf.toLp f := by
  unfold toWeightL1
  rw [dif_pos hf]

theorem lintegral_weight_mul_le (k j : ℕ) (g : Space → ℝ≥0∞) :
    ∫⁻ ξ, ENNReal.ofReal (‖ξ‖ ^ j) * g ξ ∂weightL1Measure k ≤ ∫⁻ ξ, g ξ ∂weightL1Measure (k + j) := by
  rw [lintegral_weightL1, lintegral_weightL1]
  refine lintegral_mono fun ξ => ?_
  rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  gcongr
  rw [pow_add]
  gcongr
  linarith [norm_nonneg ξ]

theorem memLp_velSymbol (hW : HomWiener) (k : ℕ) {x : X} (h0 : homSob 0 x < ⊤)
    (hk : homSob (k + 1) x < ⊤) : MemLp (velSymbol x) 1 (weightL1Measure k) := by
  obtain ⟨C, hC⟩ := hW k
  refine ⟨(measurable_velSymbol x).aestronglyMeasurable, ?_⟩
  rw [eLpNorm_one_eq_lintegral_enorm, lintegral_weightL1]
  exact lt_of_le_of_lt (hC x) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.add_lt_top.2 ⟨h0, hk⟩).ne))

theorem lintegral_velSymbol_sub_le (hW : HomWiener) (k : ℕ) : ∃ C : ℝ, ∀ x y : X,
    ∫⁻ ξ, ‖velSymbol x ξ - velSymbol y ξ‖ₑ ∂weightL1Measure k ≤
      ENNReal.ofReal C * (homSob 0 (x - y) + homSob (k + 1) (x - y)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := hW k
  refine ⟨C, fun x y => ?_⟩
  rw [lintegral_weightL1]
  calc ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol x ξ - velSymbol y ξ‖ₑ
      = ∫⁻ ξ, ENNReal.ofReal ((1 + ‖ξ‖) ^ k) * ‖velSymbol (x - y) ξ‖ₑ := by
        refine lintegral_congr_ae ?_
        filter_upwards [velSymbol_sub_ae x y] with ξ hξ
        rw [hξ, Pi.sub_apply]
    _ ≤ _ := hC (x - y)

section Curve

variable {u : ℝ → X} {S : Set ℝ}

theorem memLp_curve (hW : HomWiener) (hc : ∀ k, IsHomSobolevCurve k u S) (k : ℕ) {s : ℝ}
    (hs : s ∈ S) : MemLp (velSymbol (u s)) 1 (weightL1Measure k) :=
  memLp_velSymbol hW k ((hc 0).1 s hs) ((hc (k + 1)).1 s hs)

theorem tendsto_lintegral_vel_sub (hW : HomWiener) (hc : ∀ k, IsHomSobolevCurve k u S) (k : ℕ)
    {t : ℝ} (ht : t ∈ S) :
    Tendsto (fun s => ∫⁻ ξ, ‖velSymbol (u s) ξ - velSymbol (u t) ξ‖ₑ ∂weightL1Measure k)
      (𝓝[S] t) (𝓝 0) := by
  obtain ⟨C, hC⟩ := lintegral_velSymbol_sub_le hW k
  have h1 : Tendsto (fun s => homSob 0 (u s - u t) + homSob (k + 1) (u s - u t)) (𝓝[S] t)
      (𝓝 0) := by
    simpa using ((hc 0).2 t ht).add ((hc (k + 1)).2 t ht)
  have h2 := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h1
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
  have h3 := ENNReal.Tendsto.const_mul h2 (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal C)
  rw [mul_zero] at h3
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h3 (fun _ => zero_le)
    (fun s => hC _ _)

theorem continuousOn_toWeightL1_vel (hW : HomWiener) (hc : ∀ k, IsHomSobolevCurve k u S)
    (k : ℕ) : ContinuousOn (fun s => toWeightL1 k (velSymbol (u s))) S := by
  intro t ht
  rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0]
  refine Tendsto.congr' ?_ (tendsto_lintegral_vel_sub hW hc k ht)
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [toWeightL1_eq (memLp_curve hW hc k hs), toWeightL1_eq (memLp_curve hW hc k ht),
    Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm]
  rfl

end Curve

theorem exists_nonlin_map (k : ℕ) :
    ∃ Q : Lp CSpace 1 (weightL1Measure (k + 1)) → Lp CSpace 1 (weightL1Measure k), Continuous Q ∧
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (nonlinSymbol f) 1 (weightL1Measure k), Q (hf.toLp f) = h.toLp _ := by
  obtain ⟨B, hB⟩ : ∃ B : Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ]
      Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 1)))
        (hg : MemLp g 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (advectionBilin f g) 1 (weightL1Measure k),
          B (hf.toLp f) (hg.toLp g) = h.toLp _ := exists_bilin_advection k
  obtain ⟨P, hP⟩ : ∃ L : Lp CSpace 1 (weightL1Measure k) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure k)),
        ∃ hg : MemLp (fun ξ => -divFreeC ξ (f ξ)) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_divFree k
  refine ⟨fun v => P (B v v), P.continuous.comp (B.continuous₂.comp
    (continuous_id.prodMk continuous_id)), fun f hf => ?_⟩
  obtain ⟨hb, hBb⟩ := hB f f hf hf
  obtain ⟨hp, hPp⟩ := hP _ hb
  exact ⟨hp, by simp only; rw [hBb, hPp]; rfl⟩

theorem exists_measurable_version {μ : Measure Space} {V : ℝ → Lp CSpace 1 μ} {a b : ℝ}
    (hV : ContinuousOn V (Icc a b)) :
    ∃ G : ℝ × Space → CSpace, StronglyMeasurable G ∧
      ∀ σ ∈ Icc a b, (fun ξ => G (σ, ξ)) =ᵐ[μ] V σ := by
  have huc := Metric.uniformContinuousOn_iff.1 (isCompact_Icc.uniformContinuousOn_of_continuous hV)
  choose δ hδ hδV using fun m : ℕ => huc ((1 / 2 : ℝ) ^ m) (by positivity)
  let g : ℕ → ℝ → ℝ := fun m σ => a + δ m / 2 * ⌊(σ - a) / (δ m / 2)⌋
  have hg : ∀ m, ∀ σ ∈ Icc a b, g m σ ∈ Icc a b ∧ dist (g m σ) σ < δ m := by
    intro m σ hσ
    have hd : 0 < δ m / 2 := by linarith [hδ m]
    have h1 : (⌊(σ - a) / (δ m / 2)⌋ : ℝ) ≤ (σ - a) / (δ m / 2) := Int.floor_le _
    have h2 : (σ - a) / (δ m / 2) < ⌊(σ - a) / (δ m / 2)⌋ + 1 := Int.lt_floor_add_one _
    have h3 : (0 : ℝ) ≤ ⌊(σ - a) / (δ m / 2)⌋ := by
      exact_mod_cast Int.floor_nonneg.2 (div_nonneg (by linarith [hσ.1]) hd.le)
    have e1 : δ m / 2 * ⌊(σ - a) / (δ m / 2)⌋ ≤ σ - a := by
      have := mul_le_mul_of_nonneg_left h1 hd.le
      rwa [mul_div_cancel₀ _ hd.ne'] at this
    have e2 : σ - a < δ m / 2 * ⌊(σ - a) / (δ m / 2)⌋ + δ m / 2 := by
      have := mul_lt_mul_of_pos_left h2 hd
      rwa [mul_div_cancel₀ _ hd.ne', mul_add, mul_one] at this
    have e3 : 0 ≤ δ m / 2 * ⌊(σ - a) / (δ m / 2)⌋ := mul_nonneg hd.le h3
    refine ⟨⟨by simp only [g]; linarith, by simp only [g]; linarith [hσ.2]⟩, ?_⟩
    rw [Real.dist_eq, abs_lt]
    simp only [g]
    constructor <;> linarith
  let h : ℕ → ℝ × Space → CSpace := fun m p => (V (g m p.1) : Space → CSpace) p.2
  have hmeas : ∀ m, StronglyMeasurable (h m) := by
    intro m
    have hΦ : Measurable fun q : ℤ × Space => (V (a + δ m / 2 * q.1) : Space → CSpace) q.2 :=
      measurable_from_prod_countable_right fun j =>
        (Lp.stronglyMeasurable (V (a + δ m / 2 * (j : ℝ)))).measurable
    have hi : Measurable fun p : ℝ × Space => ((⌊(p.1 - a) / (δ m / 2)⌋ : ℤ), p.2) :=
      (Int.measurable_floor.comp ((measurable_fst.sub_const a).div_const _)).prodMk measurable_snd
    exact (hΦ.comp hi).stronglyMeasurable
  refine ⟨fun p => limUnder atTop fun m => h m p, StronglyMeasurable.limUnder hmeas,
    fun σ hσ => ?_⟩
  have hsec : ∀ m, Measurable fun ξ => ‖h m (σ, ξ) - (V σ : Space → CSpace) ξ‖ₑ := fun m =>
    (((hmeas m).measurable.comp measurable_prodMk_left).sub
      (Lp.stronglyMeasurable (V σ)).measurable).enorm
  have hbound : ∀ m, ∫⁻ ξ, ‖h m (σ, ξ) - (V σ : Space → CSpace) ξ‖ₑ ∂μ ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ m) := by
    intro m
    have hlt := hδV m (g m σ) (hg m σ hσ).1 σ hσ (hg m σ hσ).2
    calc ∫⁻ ξ, ‖h m (σ, ξ) - (V σ : Space → CSpace) ξ‖ₑ ∂μ = edist (V (g m σ)) (V σ) := by
          rw [Lp.edist_def, eLpNorm_one_eq_lintegral_enorm]
          rfl
      _ ≤ _ := by
          rw [edist_dist]
          exact ENNReal.ofReal_le_ofReal hlt.le
  have htsum : ∫⁻ ξ, ∑' m, ‖h m (σ, ξ) - (V σ : Space → CSpace) ξ‖ₑ ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun m => (hsec m).aemeasurable]
    refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hbound)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) summable_geometric_two]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_lt_top (Measurable.tsum hsec) htsum] with ξ hξ
  have hz := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hξ.ne
  have ht : Tendsto (fun m => h m (σ, ξ)) atTop (𝓝 ((V σ : Space → CSpace) ξ)) := by
    rw [tendsto_iff_edist_tendsto_0]
    simpa [edist_eq_enorm_sub] using hz
  exact ht.limUnder_eq

theorem advectionBilin_congr_ae {f f' g g' : Space → CSpace} (hf : f =ᵐ[volume] f')
    (hg : g =ᵐ[volume] g') : advectionBilin f g = advectionBilin f' g' := by
  funext ξ
  have hg' : g ∘ (fun η => ξ - η) =ᵐ[volume] g' ∘ (fun η => ξ - η) :=
    (Measure.measurePreserving_sub_left (volume : Measure Space) ξ).quasiMeasurePreserving.ae_eq_comp hg
  unfold advectionBilin convC
  congr 1
  funext i
  refine Finset.sum_congr rfl fun j _ => integral_congr_ae ?_
  filter_upwards [hf, hg'] with η h1 h2
  simp only [Function.comp_apply] at h2
  simp only [h1, h2]

theorem nonlinSymbol_congr_ae {f f' : Space → CSpace} (h : f =ᵐ[volume] f') :
    nonlinSymbol f = nonlinSymbol f' := by
  funext ξ
  simp only [nonlinSymbol, advectionSymbol, advectionBilin_congr_ae h h]

theorem measurable_nonlin_section {G : ℝ × Space → CSpace} (hG : Measurable G) :
    Measurable fun p : ℝ × Space => nonlinSymbol (fun ξ => G (p.1, ξ)) p.2 := by
  have hpr : ∀ j : Fin 3, Measurable fun v : CSpace => v j := fun j =>
    (PiLp.continuous_apply 2 _ j).measurable
  have hps : ∀ j : Fin 3, Measurable fun v : Space => v j := fun j =>
    (PiLp.continuous_apply 2 _ j).measurable
  have hc : ∀ i j : Fin 3, Measurable fun p : ℝ × Space =>
      ∫ η, G (p.1, η) j * (2 * (π : ℂ) * Complex.I * (((p.2 - η) j : ℝ) : ℂ) * G (p.1, p.2 - η) i) := by
    intro i j
    have m1 : Measurable fun q : (ℝ × Space) × Space => G (q.1.1, q.2) :=
      hG.comp (measurable_fst.fst.prodMk measurable_snd)
    have m2 : Measurable fun q : (ℝ × Space) × Space => G (q.1.1, q.1.2 - q.2) :=
      hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.sub measurable_snd))
    have m3 : Measurable fun q : (ℝ × Space) × Space => (((q.1.2 - q.2) j : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp ((hps j).comp (measurable_fst.snd.sub measurable_snd))
    have hm : StronglyMeasurable fun q : (ℝ × Space) × Space =>
        G (q.1.1, q.2) j * (2 * (π : ℂ) * Complex.I * (((q.1.2 - q.2) j : ℝ) : ℂ) *
          G (q.1.1, q.1.2 - q.2) i) :=
      (((hpr j).comp m1).mul ((measurable_const.mul m3).mul ((hpr i).comp m2))).stronglyMeasurable
    exact (hm.integral_prod_right' (ν := (volume : Measure Space))).measurable
  have hadv : Measurable fun p : ℝ × Space =>
      advectionBilin (fun ξ => G (p.1, ξ)) (fun ξ => G (p.1, ξ)) p.2 := by
    show Measurable fun p : ℝ × Space => WithLp.toLp 2 (fun i : Fin 3 => ∑ j : Fin 3,
      ∫ η, G (p.1, η) j * (2 * (π : ℂ) * Complex.I * (((p.2 - η) j : ℝ) : ℂ) * G (p.1, p.2 - η) i))
    exact (PiLp.continuous_toLp 2 _).measurable.comp
      (measurable_pi_lambda _ fun i => Finset.measurable_sum _ fun j _ => hc i j)
  exact (measurable_lerayC_prod.comp (measurable_snd.prodMk hadv)).neg

theorem heatSymbol_add (x y : ℝ) (ξ : Space) :
    heatSymbol (x + y) ξ = heatSymbol x ξ * heatSymbol y ξ := by
  unfold heatSymbol
  rw [← Real.exp_add]
  congr 1
  ring

theorem continuous_heat_coe (q : ℝ) (ξ : Space) :
    Continuous fun σ : ℝ => ((heatSymbol (q - σ) ξ : ℝ) : ℂ) := by
  unfold heatSymbol
  fun_prop

theorem duhamel_restart {ξ : Space} {a p q : ℝ} {x n : ℝ → CSpace} (hap : a ≤ p) (hpq : p ≤ q)
    (hn : IntervalIntegrable n volume a q)
    (hp : x p = ((heatSymbol (p - a) ξ : ℝ) : ℂ) • x a +
      ∫ σ in a..p, ((heatSymbol (p - σ) ξ : ℝ) : ℂ) • n σ)
    (hq : x q = ((heatSymbol (q - a) ξ : ℝ) : ℂ) • x a +
      ∫ σ in a..q, ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) :
    x q = ((heatSymbol (q - p) ξ : ℝ) : ℂ) • x p +
      ∫ σ in p..q, ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ := by
  have hi : IntervalIntegrable (fun σ => ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) volume a q :=
    hn.continuousOn_smul (continuous_heat_coe q ξ).continuousOn
  have h1 : IntervalIntegrable (fun σ => ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) volume a p :=
    hi.mono_set (by
      rw [uIcc_of_le hap, uIcc_of_le (hap.trans hpq)]
      exact Icc_subset_Icc le_rfl hpq)
  have h2 : IntervalIntegrable (fun σ => ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) volume p q :=
    hi.mono_set (by
      rw [uIcc_of_le hpq, uIcc_of_le (hap.trans hpq)]
      exact Icc_subset_Icc hap le_rfl)
  have h3 : ∫ σ in a..p, ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ =
      ((heatSymbol (q - p) ξ : ℝ) : ℂ) • ∫ σ in a..p, ((heatSymbol (p - σ) ξ : ℝ) : ℂ) • n σ := by
    rw [← intervalIntegral.integral_smul]
    refine intervalIntegral.integral_congr fun σ _ => ?_
    rw [show q - σ = q - p + (p - σ) by ring, heatSymbol_add, Complex.ofReal_mul, smul_smul]
  rw [hq, ← intervalIntegral.integral_add_adjacent_intervals h1 h2, h3, hp, smul_add, smul_smul,
    ← Complex.ofReal_mul, ← heatSymbol_add, show q - p + (p - a) = q - a by ring, add_assoc]

theorem abs_exp_neg_sub_le {y : ℝ} (hy : 0 ≤ y) : |Real.exp (-y) - 1 + y| ≤ y ^ 2 := by
  rcases le_or_gt y 1 with h | h
  · have := Real.abs_exp_sub_one_sub_id_le (x := -y) (by rw [abs_neg, abs_of_nonneg hy]; exact h)
    rwa [neg_sq, sub_neg_eq_add] at this
  · have h1 : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    have h2 : 0 < Real.exp (-y) := Real.exp_pos _
    rw [abs_le]
    constructor <;> nlinarith

theorem one_sub_exp_neg_le (y : ℝ) : 1 - Real.exp (-y) ≤ y := by
  linarith [Real.add_one_le_exp (-y)]

theorem enorm_duhamel_sub_le {ξ : Space} {p q r : ℝ} {n : ℝ → CSpace} (hpq : p ≤ q)
    (hn : IntervalIntegrable n volume p q) :
    ‖(∫ σ in p..q, ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) - (q - p) • n r‖ₑ ≤
      (∫⁻ σ in Ioc p q, ‖n σ - n r‖ₑ) +
        ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p) * (q - p)) * ‖n r‖ₑ := by
  have hi : IntervalIntegrable (fun σ => ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ) volume p q :=
    hn.continuousOn_smul (continuous_heat_coe q ξ).continuousOn
  have hc0 : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [← intervalIntegral.integral_const, ← intervalIntegral.integral_sub hi intervalIntegrable_const,
    intervalIntegral.integral_of_le hpq]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have hpt : ∀ σ ∈ Ioc p q, ‖((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ - n r‖ₑ ≤
      ‖n σ - n r‖ₑ + ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p)) * ‖n r‖ₑ := by
    intro σ hσ
    have hqσ : 0 ≤ q - σ := by linarith [hσ.2]
    have he0 : 0 ≤ heatSymbol (q - σ) ξ := (Real.exp_pos _).le
    have he1 : heatSymbol (q - σ) ξ ≤ 1 := by
      unfold heatSymbol
      exact Real.exp_le_one_iff.2 (neg_nonpos.2 (by positivity))
    have he2 : 1 - heatSymbol (q - σ) ξ ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p) := by
      have h1 := one_sub_exp_neg_le (4 * π ^ 2 * (q - σ) * ‖ξ‖ ^ 2)
      unfold heatSymbol
      have h2 : q - σ ≤ q - p := by linarith [hσ.1]
      nlinarith
    have heq : ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ - n r =
        ((heatSymbol (q - σ) ξ : ℝ) : ℂ) • (n σ - n r) -
          ((1 - heatSymbol (q - σ) ξ : ℝ) : ℂ) • n r := by
      rw [smul_sub, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul]
      abel
    have hreal : ‖((heatSymbol (q - σ) ξ : ℝ) : ℂ) • (n σ - n r) -
        ((1 - heatSymbol (q - σ) ξ : ℝ) : ℂ) • n r‖ ≤
        ‖n σ - n r‖ + 4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p) * ‖n r‖ := by
      calc _ ≤ ‖((heatSymbol (q - σ) ξ : ℝ) : ℂ) • (n σ - n r)‖ +
            ‖((1 - heatSymbol (q - σ) ξ : ℝ) : ℂ) • n r‖ := norm_sub_le _ _
        _ = heatSymbol (q - σ) ξ * ‖n σ - n r‖ + (1 - heatSymbol (q - σ) ξ) * ‖n r‖ := by
          rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
            Real.norm_of_nonneg he0, Real.norm_of_nonneg (by linarith)]
        _ ≤ 1 * ‖n σ - n r‖ + 4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p) * ‖n r‖ := by
          gcongr
        _ = _ := by ring
    rw [heq, ← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (norm_nonneg _) (by positivity)]
    exact ENNReal.ofReal_le_ofReal hreal
  calc ∫⁻ σ in Ioc p q, ‖((heatSymbol (q - σ) ξ : ℝ) : ℂ) • n σ - n r‖ₑ
      ≤ ∫⁻ σ in Ioc p q, (‖n σ - n r‖ₑ +
          ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p)) * ‖n r‖ₑ) :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = (∫⁻ σ in Ioc p q, ‖n σ - n r‖ₑ) +
          ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * (q - p)) * ‖n r‖ₑ * ENNReal.ofReal (q - p) := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const, Real.volume_Ioc]
    _ = _ := by
        rw [mul_right_comm, ← ENNReal.ofReal_mul (mul_nonneg hc0 (sub_nonneg.2 hpq))]

theorem enorm_smul_real (r : ℝ) (v : CSpace) :
    ‖((r : ℝ) : ℂ) • v‖ₑ = ENNReal.ofReal |r| * ‖v‖ₑ := by
  rw [← ofReal_norm, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    ENNReal.ofReal_mul (abs_nonneg _), ofReal_norm]

theorem enorm_increment_le {ξ : Space} {s t : ℝ} {x n : ℝ → CSpace}
    (hn : IntervalIntegrable n volume (min s t) (max s t))
    (hid : x (max s t) = ((heatSymbol (max s t - min s t) ξ : ℝ) : ℂ) • x (min s t) +
      ∫ σ in (min s t)..(max s t), ((heatSymbol (max s t - σ) ξ : ℝ) : ℂ) • n σ) :
    ‖x s - x t - (s - t) • (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • x t + n t)‖ₑ ≤
      ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 * |s - t| ^ 2) * (2 * ‖x t‖ₑ + ‖x s - x t‖ₑ) +
      ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * |s - t|) * ‖x s - x t‖ₑ +
      ((∫⁻ σ in Ioc (min s t) (max s t), ‖n σ - n t‖ₑ) +
        ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * |s - t| * |s - t|) * ‖n t‖ₑ) := by
  have hc0 : 0 ≤ 4 * π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have he : ∀ h : ℝ, heatSymbol h ξ = Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * h)) := fun h => by
    unfold heatSymbol
    ring_nf
  have hxt : ‖x t‖ₑ ≤ 2 * ‖x t‖ₑ + ‖x s - x t‖ₑ :=
    le_add_right (le_mul_of_one_le_left' (by norm_num))
  rcases le_total t s with hts | hst
  · rw [min_eq_right hts, max_eq_left hts] at hn hid ⊢
    rw [abs_of_nonneg (sub_nonneg.2 hts)]
    have hkey : x s - x t - (s - t) • (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • x t + n t) =
        ((Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (s - t))) - 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 * (s - t) : ℝ) : ℂ) •
          x t + ((∫ σ in t..s, ((heatSymbol (s - σ) ξ : ℝ) : ℂ) • n σ) - (s - t) • n t) := by
      rw [hid, he (s - t)]
      ext i
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul,
        Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat]
      ring
    rw [hkey]
    have hA : ‖((Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (s - t))) - 1 + 4 * π ^ 2 * ‖ξ‖ ^ 2 * (s - t) : ℝ) :
        ℂ) • x t‖ₑ ≤
        ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 * (s - t) ^ 2) * (2 * ‖x t‖ₑ + ‖x s - x t‖ₑ) := by
      rw [enorm_smul_real]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) hxt
      rw [← mul_pow]
      exact abs_exp_neg_sub_le (mul_nonneg hc0 (sub_nonneg.2 hts))
    calc _ ≤ _ := enorm_add_le _ _
      _ ≤ _ := add_le_add hA (enorm_duhamel_sub_le hts hn)
      _ ≤ _ := add_le_add le_self_add le_rfl
  · rw [min_eq_left hst, max_eq_right hst] at hn hid ⊢
    rw [abs_of_nonpos (sub_nonpos.2 hst), neg_sub]
    have hkey : x s - x t - (s - t) • (-(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • x t + n t) =
        ((1 - Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s))) - 4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s) : ℝ) : ℂ) •
          x s + ((4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s) : ℝ) : ℂ) • (x s - x t) -
        ((∫ σ in s..t, ((heatSymbol (t - σ) ξ : ℝ) : ℂ) • n σ) - (t - s) • n t) := by
      rw [he (t - s)] at hid
      ext i
      have hi := congrArg (fun v : CSpace => v i) hid
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi
      simp only [PiLp.add_apply, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul,
        Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_mul,
        Complex.ofReal_one, Complex.ofReal_pow, Complex.ofReal_ofNat]
      linear_combination (-1 : ℂ) * hi
    rw [hkey]
    have hA : ‖((1 - Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s))) - 4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s) :
        ℝ) : ℂ) • x s‖ₑ ≤
        ENNReal.ofReal ((4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 * (t - s) ^ 2) * (2 * ‖x t‖ₑ + ‖x s - x t‖ₑ) := by
      rw [enorm_smul_real]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) ?_
      · rw [← mul_pow, show 1 - Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s))) -
            4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s) = -(Real.exp (-(4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s))) - 1 +
            4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s)) by ring, abs_neg]
        exact abs_exp_neg_sub_le (mul_nonneg hc0 (sub_nonneg.2 hst))
      · calc ‖x s‖ₑ = ‖x t + (x s - x t)‖ₑ := by rw [add_sub_cancel]
          _ ≤ ‖x t‖ₑ + ‖x s - x t‖ₑ := enorm_add_le _ _
          _ ≤ _ := add_le_add (le_mul_of_one_le_left' (by norm_num)) le_rfl
    have hB : ‖((4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s) : ℝ) : ℂ) • (x s - x t)‖ₑ =
        ENNReal.ofReal (4 * π ^ 2 * ‖ξ‖ ^ 2 * (t - s)) * ‖x s - x t‖ₑ := by
      rw [enorm_smul_real, abs_of_nonneg (mul_nonneg hc0 (sub_nonneg.2 hst))]
    calc _ ≤ _ := enorm_sub_le
      _ ≤ _ := add_le_add (enorm_add_le _ _) (enorm_duhamel_sub_le hst hn)
      _ ≤ _ := add_le_add (add_le_add hA hB.le) le_rfl

theorem ofReal_mul_split {X h X' Z : ℝ} (hh : 0 ≤ h) (hX' : 0 ≤ X') (e : X = h * X' * Z)
    (Y : ℝ≥0∞) :
    ENNReal.ofReal X * Y = ENNReal.ofReal h * ENNReal.ofReal X' * (ENNReal.ofReal Z * Y) := by
  rw [e, ENNReal.ofReal_mul (mul_nonneg hh hX'), ENNReal.ofReal_mul hh]
  ring

theorem hasDerivWithinAt_of_increment {F : ℝ → Space → CSpace} {N : ℝ × Space → CSpace}
    {a b t : ℝ} (k : ℕ) (ht : t ∈ Icc a b) (hNm : Measurable N)
    (hF : ∀ s ∈ Icc a b, ∀ m, MemLp (F s) 1 (weightL1Measure m))
    (hFc : ∀ m, Tendsto (fun s => ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure m) (𝓝[Icc a b] t)
      (𝓝 0))
    (hNt : ∀ m, MemLp (fun ξ => N (t, ξ)) 1 (weightL1Measure m))
    (hNc : Tendsto (fun s => ∫⁻ ξ, ‖N (s, ξ) - N (t, ξ)‖ₑ ∂weightL1Measure k) (𝓝[Icc a b] t)
      (𝓝 0))
    (hD : ∀ s ∈ Icc a b, ∀ᵐ ξ ∂volume,
      IntervalIntegrable (fun σ => N (σ, ξ)) volume (min s t) (max s t) ∧
      F (max s t) ξ = ((heatSymbol (max s t - min s t) ξ : ℝ) : ℂ) • F (min s t) ξ +
        ∫ σ in (min s t)..(max s t), ((heatSymbol (max s t - σ) ξ : ℝ) : ℂ) • N (σ, ξ))
    (hT : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + N (t, ξ)) 1
      (weightL1Measure k)) :
    HasDerivWithinAt (fun s => toWeightL1 k (F s))
      (toWeightL1 k (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + N (t, ξ)))
      (Icc a b) t := by
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hAfin : ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) ≠ ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact (hF t ht (k + 4)).eLpNorm_ne_top
  have hNfin : ∫⁻ ξ, ‖N (t, ξ)‖ₑ ∂weightL1Measure (k + 2) ≠ ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm]
    exact (hNt (k + 2)).eLpNorm_ne_top
  have h0 : ∀ C : ℝ, Tendsto (fun s => ENNReal.ofReal (C * |s - t|)) (𝓝[Icc a b] t) (𝓝 0) := by
    intro C
    have hc : Continuous fun s : ℝ => C * |s - t| :=
      continuous_const.mul (continuous_abs.comp (continuous_id.sub continuous_const))
    have : Tendsto (fun s => C * |s - t|) (𝓝 t) (𝓝 0) := by
      simpa using hc.tendsto t
    simpa using (ENNReal.tendsto_ofReal this).mono_left nhdsWithin_le_nhds
  have hYt : Tendsto (fun s =>
      ENNReal.ofReal (16 * π ^ 4 * |s - t|) * (2 * ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) +
        ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 4)) +
      ENNReal.ofReal (4 * π ^ 2) * ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 2) +
      ENNReal.ofReal (4 * π ^ 2 * |s - t|) * ∫⁻ ξ, ‖N (t, ξ)‖ₑ ∂weightL1Measure (k + 2))
      (𝓝[Icc a b] t) (𝓝 0) := by
    have htd : Tendsto (fun s => 2 * ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) +
        ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 4)) (𝓝[Icc a b] t)
        (𝓝 (2 * ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) + 0)) :=
      tendsto_const_nhds.add (hFc (k + 4))
    rw [add_zero] at htd
    have t1 := ENNReal.Tendsto.mul (h0 (16 * π ^ 4))
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofNat_ne_top hAfin)) htd (Or.inr ENNReal.zero_ne_top)
    have t2 := ENNReal.Tendsto.const_mul (hFc (k + 2)) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (4 * π ^ 2))
    have t3 := ENNReal.Tendsto.mul_const (h0 (4 * π ^ 2)) (Or.inr hNfin)
    have := (t1.add t2).add t3
    simp only [mul_zero, zero_mul, add_zero] at this
    exact this
  have hY2 := (ENNReal.tendsto_nhds_zero.1 hYt) _ (ENNReal.ofReal_pos.2 (by linarith : 0 < ε / 2))
  obtain ⟨δ, hδ, hδN⟩ : ∃ δ > 0, ∀ σ ∈ Icc a b, dist σ t < δ →
      ∫⁻ ξ, ‖N (σ, ξ) - N (t, ξ)‖ₑ ∂weightL1Measure k ≤ ENNReal.ofReal (ε / 2) := by
    have h1 := (ENNReal.tendsto_nhds_zero.1 hNc) _
      (ENNReal.ofReal_pos.2 (by linarith : 0 < ε / 2))
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at h1
    obtain ⟨δ, hδ, h⟩ := h1
    exact ⟨δ, hδ, fun σ hσ hd => h hd hσ⟩
  filter_upwards [self_mem_nhdsWithin, hY2, nhdsWithin_le_nhds (Metric.ball_mem_nhds t hδ)]
    with s hs hYs hsb
  rw [toWeightL1_eq (hF s hs k), toWeightL1_eq (hF t ht k), toWeightL1_eq hT,
    ← MemLp.toLp_const_smul, ← MemLp.toLp_sub, ← MemLp.toLp_sub, Lp.norm_toLp,
    eLpNorm_one_eq_lintegral_enorm, Real.norm_eq_abs]
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  have hac : weightL1Measure k ≪ (volume : Measure Space) := withDensity_absolutelyContinuous _ _
  have : SFinite (weightL1Measure k) := by
    unfold weightL1Measure
    infer_instance
  have hst0 : 0 ≤ |s - t| := abs_nonneg _
  have hpt : ∀ᵐ ξ ∂weightL1Measure k, ‖(F s - F t - (s - t) • fun ξ =>
      -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • F t ξ + N (t, ξ)) ξ‖ₑ ≤
      ENNReal.ofReal |s - t| * ENNReal.ofReal (16 * π ^ 4 * |s - t|) *
        (ENNReal.ofReal (‖ξ‖ ^ 4) * (2 * ‖F t ξ‖ₑ + ‖F s ξ - F t ξ‖ₑ)) +
      ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F s ξ - F t ξ‖ₑ) +
      ((∫⁻ σ in Ioc (min s t) (max s t), ‖N (σ, ξ) - N (t, ξ)‖ₑ) +
        ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2 * |s - t|) *
          (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖N (t, ξ)‖ₑ)) := by
    filter_upwards [hac.ae_le (hD s hs)] with ξ hξ
    refine (enorm_increment_le (x := fun σ => F σ ξ) (n := fun σ => N (σ, ξ)) hξ.1 hξ.2).trans
      (le_of_eq ?_)
    rw [ofReal_mul_split (X := (4 * π ^ 2 * ‖ξ‖ ^ 2) ^ 2 * |s - t| ^ 2) (h := |s - t|)
        (X' := 16 * π ^ 4 * |s - t|) (Z := ‖ξ‖ ^ 4) hst0 (by positivity) (by ring),
      ofReal_mul_split (X := 4 * π ^ 2 * ‖ξ‖ ^ 2 * |s - t|) (h := |s - t|)
        (X' := 4 * π ^ 2) (Z := ‖ξ‖ ^ 2) hst0 (by positivity) (by ring),
      ofReal_mul_split (X := 4 * π ^ 2 * ‖ξ‖ ^ 2 * |s - t| * |s - t|) (h := |s - t|)
        (X' := 4 * π ^ 2 * |s - t|) (Z := ‖ξ‖ ^ 2) hst0 (by positivity) (by ring)]
  have mFt := (hF t ht k).1
  have mFs := (hF s hs k).1
  have hW4 : Measurable fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ 4) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 4)
  have hW2 : Measurable fun ξ : Space => ENNReal.ofReal (‖ξ‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (measurable_norm.pow_const 2)
  have hLm : Measurable fun ξ => ∫⁻ σ in Ioc (min s t) (max s t), ‖N (σ, ξ) - N (t, ξ)‖ₑ :=
    Measurable.lintegral_prod_left' (f := fun p : ℝ × Space => ‖N p - N (t, p.2)‖ₑ)
      (hNm.sub (hNm.comp (measurable_const.prodMk measurable_snd))).enorm
  have hIL : ∫⁻ ξ, (∫⁻ σ in Ioc (min s t) (max s t), ‖N (σ, ξ) - N (t, ξ)‖ₑ) ∂weightL1Measure k ≤
      ENNReal.ofReal |s - t| * ENNReal.ofReal (ε / 2) := by
    rw [lintegral_lintegral_swap (((hNm.comp measurable_swap).sub
      (hNm.comp (measurable_const.prodMk measurable_fst))).enorm.aemeasurable)]
    have h1 : |s - t| < δ := by simpa [Real.dist_eq] using Metric.mem_ball.1 hsb
    calc ∫⁻ σ in Ioc (min s t) (max s t), ∫⁻ ξ, ‖N (σ, ξ) - N (t, ξ)‖ₑ ∂weightL1Measure k
        ≤ ∫⁻ σ in Ioc (min s t) (max s t), ENNReal.ofReal (ε / 2) := by
          refine setLIntegral_mono' measurableSet_Ioc fun σ hσ => hδN σ ?_ ?_
          · exact ⟨(le_min hs.1 ht.1).trans hσ.1.le, hσ.2.trans (max_le hs.2 ht.2)⟩
          · have h2 : |σ - t| ≤ |s - t| := by
              rw [abs_sub_comm s t, ← max_sub_min_eq_abs s t]
              exact abs_sub_le_iff.2 ⟨by linarith [hσ.2, min_le_right s t],
                by linarith [hσ.1, le_max_right s t]⟩
            rw [Real.dist_eq]
            exact lt_of_le_of_lt h2 h1
      _ = _ := by rw [setLIntegral_const, Real.volume_Ioc, max_sub_min_eq_abs, abs_sub_comm, mul_comm]
  have hI1 : ∫⁻ ξ, ENNReal.ofReal |s - t| * ENNReal.ofReal (16 * π ^ 4 * |s - t|) *
        (ENNReal.ofReal (‖ξ‖ ^ 4) * (2 * ‖F t ξ‖ₑ + ‖F s ξ - F t ξ‖ₑ)) ∂weightL1Measure k ≤
      ENNReal.ofReal |s - t| * ENNReal.ofReal (16 * π ^ 4 * |s - t|) *
        (2 * ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) +
          ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 4)) := by
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    refine mul_le_mul' le_rfl ((lintegral_weight_mul_le k 4 _).trans (le_of_eq ?_))
    rw [lintegral_add_left' (((hF t ht (k + 4)).1.enorm).const_mul 2),
      lintegral_const_mul' _ _ ENNReal.ofNat_ne_top]
  have hI2 : ∫⁻ ξ, ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F s ξ - F t ξ‖ₑ) ∂weightL1Measure k ≤
      ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2) *
        ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 2) := by
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    exact mul_le_mul' le_rfl (lintegral_weight_mul_le k 2 _)
  have hI4 : ∫⁻ ξ, ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2 * |s - t|) *
        (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖N (t, ξ)‖ₑ) ∂weightL1Measure k ≤
      ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2 * |s - t|) *
        ∫⁻ ξ, ‖N (t, ξ)‖ₑ ∂weightL1Measure (k + 2) := by
    rw [lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)]
    exact mul_le_mul' le_rfl (lintegral_weight_mul_le k 2 _)
  have mT1 : AEMeasurable (fun ξ => ENNReal.ofReal |s - t| * ENNReal.ofReal (16 * π ^ 4 * |s - t|) *
        (ENNReal.ofReal (‖ξ‖ ^ 4) * (2 * ‖F t ξ‖ₑ + ‖F s ξ - F t ξ‖ₑ))) (weightL1Measure k) :=
    (hW4.aemeasurable.mul ((mFt.enorm.const_mul 2).add (mFs.sub mFt).enorm)).const_mul _
  have mT2 : AEMeasurable (fun ξ => ENNReal.ofReal |s - t| * ENNReal.ofReal (4 * π ^ 2) *
        (ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F s ξ - F t ξ‖ₑ)) (weightL1Measure k) :=
    (hW2.aemeasurable.mul (mFs.sub mFt).enorm).const_mul _
  calc _ ≤ _ := lintegral_mono_ae hpt
    _ = _ := by
        refine (lintegral_add_left' (mT1.add mT2) _).trans ?_
        congr 1
        · exact lintegral_add_left' mT1 _
        · exact lintegral_add_left' hLm.aemeasurable _
    _ ≤ _ := add_le_add (add_le_add hI1 hI2) (add_le_add hIL hI4)
    _ = ENNReal.ofReal |s - t| * (ENNReal.ofReal (16 * π ^ 4 * |s - t|) *
          (2 * ∫⁻ ξ, ‖F t ξ‖ₑ ∂weightL1Measure (k + 4) +
            ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 4)) +
          ENNReal.ofReal (4 * π ^ 2) * ∫⁻ ξ, ‖F s ξ - F t ξ‖ₑ ∂weightL1Measure (k + 2) +
          ENNReal.ofReal (4 * π ^ 2 * |s - t|) * ∫⁻ ξ, ‖N (t, ξ)‖ₑ ∂weightL1Measure (k + 2)) +
          ENNReal.ofReal |s - t| * ENNReal.ofReal (ε / 2) := by ring
    _ ≤ ENNReal.ofReal |s - t| * ENNReal.ofReal (ε / 2) +
          ENNReal.ofReal |s - t| * ENNReal.ofReal (ε / 2) :=
        add_le_add (mul_le_mul' le_rfl hYs) le_rfl
    _ = ENNReal.ofReal (ε * |s - t|) := by
        rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul hst0]
        congr 1
        ring

end Internal.SymbolCurve

open Internal.SymbolCurve in
theorem symbolCurveOfDuhamel_holds : SymbolCurveOfDuhamel := by
  intro hDA hW u a b hab hmild hc k t ht
  have hI : ∀ m, ContinuousOn (fun s => toWeightL1 m (velSymbol (u s))) (Icc a b) :=
    continuousOn_toWeightL1_vel hW hc
  obtain ⟨G, hGs, hGeq⟩ := exists_measurable_version (hI 0)
  have hGF : ∀ σ ∈ Icc a b, (fun ξ => G (σ, ξ)) =ᵐ[volume] velSymbol (u σ) := by
    intro σ hσ
    have h1 : (fun ξ => G (σ, ξ)) =ᵐ[volume] ⇑(toWeightL1 0 (velSymbol (u σ))) :=
      (volume_ac_weightL1 0).ae_le (hGeq σ hσ)
    rw [toWeightL1_eq (memLp_curve hW hc 0 hσ)] at h1
    have h2 : ⇑(MemLp.toLp (velSymbol (u σ)) (memLp_curve hW hc 0 hσ)) =ᵐ[volume]
        velSymbol (u σ) := (volume_ac_weightL1 0).ae_le (MemLp.coeFn_toLp _)
    exact Filter.EventuallyEq.trans h1 h2
  set N : ℝ × Space → CSpace := fun p => nonlinSymbol (fun ξ => G (p.1, ξ)) p.2 with hNdef
  have hNm : Measurable N := measurable_nonlin_section hGs.measurable
  have hNeq : ∀ σ ∈ Icc a b, ∀ ξ, N (σ, ξ) = nonlinSymbol (velSymbol (u σ)) ξ := by
    intro σ hσ ξ
    simp only [hNdef]
    rw [nonlinSymbol_congr_ae (hGF σ hσ)]
  have hNmem : ∀ m, ∀ σ ∈ Icc a b, MemLp (fun ξ => N (σ, ξ)) 1 (weightL1Measure m) := by
    intro m σ hσ
    obtain ⟨Q, -, hQ⟩ := exists_nonlin_map m
    obtain ⟨h, -⟩ := hQ _ (memLp_curve hW hc (m + 1) hσ)
    have : (fun ξ => N (σ, ξ)) = nonlinSymbol (velSymbol (u σ)) := funext (hNeq σ hσ)
    rw [this]
    exact h
  have hNlp : ∀ m, ∃ Q : Lp CSpace 1 (weightL1Measure (m + 1)) → Lp CSpace 1 (weightL1Measure m),
      Continuous Q ∧ ∀ σ ∈ Icc a b, Q (toWeightL1 (m + 1) (velSymbol (u σ))) =
        toWeightL1 m (fun ξ => N (σ, ξ)) := by
    intro m
    obtain ⟨Q, hQc, hQ⟩ := exists_nonlin_map m
    refine ⟨Q, hQc, fun σ hσ => ?_⟩
    obtain ⟨h, hh⟩ := hQ _ (memLp_curve hW hc (m + 1) hσ)
    rw [toWeightL1_eq (memLp_curve hW hc (m + 1) hσ), hh, toWeightL1_eq (hNmem m σ hσ)]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun ξ => (hNeq σ hσ ξ).symm)
  have hNc : Tendsto (fun s => ∫⁻ ξ, ‖N (s, ξ) - N (t, ξ)‖ₑ ∂weightL1Measure k)
      (𝓝[Icc a b] t) (𝓝 0) := by
    obtain ⟨Q, hQc, hQ⟩ := hNlp k
    have hcont : ContinuousWithinAt (fun s => Q (toWeightL1 (k + 1) (velSymbol (u s))))
        (Icc a b) t := (hQc.comp_continuousOn (hI (k + 1))) t ht
    rw [ContinuousWithinAt, tendsto_iff_edist_tendsto_0] at hcont
    refine hcont.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [hQ s hs, hQ t ht, toWeightL1_eq (hNmem k s hs), toWeightL1_eq (hNmem k t ht),
      Lp.edist_toLp_toLp, eLpNorm_one_eq_lintegral_enorm]
    rfl
  have hint : ∀ᵐ ξ ∂volume, IntegrableOn (fun σ => N (σ, ξ)) (Icc a b) := by
    obtain ⟨Q, hQc, hQ⟩ := hNlp 0
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn (hQc.comp_continuousOn (hI (0 + 1)))
    have hbd : ∀ σ ∈ Icc a b, ∫⁻ ξ, ‖N (σ, ξ)‖ₑ ≤ ENNReal.ofReal M := by
      intro σ hσ
      have h1 := hM σ hσ
      simp only [Function.comp_apply] at h1
      rw [hQ σ hσ, toWeightL1_eq (hNmem 0 σ hσ), Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm] at h1
      have hfin : ∫⁻ ξ, ‖N (σ, ξ)‖ₑ ∂weightL1Measure 0 ≠ ⊤ := by
        rw [← eLpNorm_one_eq_lintegral_enorm]
        exact (hNmem 0 σ hσ).eLpNorm_ne_top
      have h2 := (ENNReal.le_ofReal_iff_toReal_le hfin (ENNReal.toReal_nonneg.trans h1)).2 h1
      rw [lintegral_weightL1] at h2
      simpa using h2
    have hfin : ∫⁻ ξ, (∫⁻ σ in Icc a b, ‖N (σ, ξ)‖ₑ) ≠ ⊤ := by
      rw [lintegral_lintegral_swap ((hNm.comp measurable_swap).enorm.aemeasurable)]
      have hle : ∫⁻ σ in Icc a b, ∫⁻ ξ, ‖N (σ, ξ)‖ₑ ≤ ENNReal.ofReal M * volume (Icc a b) :=
        calc ∫⁻ σ in Icc a b, ∫⁻ ξ, ‖N (σ, ξ)‖ₑ ≤ ∫⁻ σ in Icc a b, ENNReal.ofReal M :=
              setLIntegral_mono' measurableSet_Icc hbd
          _ = ENNReal.ofReal M * volume (Icc a b) := setLIntegral_const _ _
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) hle
    have hmeas : Measurable fun ξ => ∫⁻ σ in Icc a b, ‖N (σ, ξ)‖ₑ :=
      Measurable.lintegral_prod_left' (f := fun p : ℝ × Space => ‖N p‖ₑ) hNm.enorm
    filter_upwards [ae_lt_top hmeas hfin] with ξ hξ
    exact ⟨(hNm.comp measurable_prodMk_right).aestronglyMeasurable, hξ⟩
  have hDA' : ∀ r ∈ Icc a b, ∀ᵐ ξ ∂volume, velSymbol (u r) ξ =
      ((heatSymbol (r - a) ξ : ℝ) : ℂ) • velSymbol (u a) ξ +
        ∫ σ in a..r, ((heatSymbol (r - σ) ξ : ℝ) : ℂ) • N (σ, ξ) := by
    intro r hr
    filter_upwards [hDA u a b hab hmild hc r hr] with ξ hξ
    rw [hξ]
    congr 1
    refine intervalIntegral.integral_congr fun σ hσ => ?_
    rw [uIcc_of_le hr.1] at hσ
    simp only [hNeq σ ⟨hσ.1, hσ.2.trans hr.2⟩ ξ]
  have hD : ∀ s ∈ Icc a b, ∀ᵐ ξ ∂volume,
      IntervalIntegrable (fun σ => N (σ, ξ)) volume (min s t) (max s t) ∧
      velSymbol (u (max s t)) ξ = ((heatSymbol (max s t - min s t) ξ : ℝ) : ℂ) •
        velSymbol (u (min s t)) ξ +
        ∫ σ in (min s t)..(max s t), ((heatSymbol (max s t - σ) ξ : ℝ) : ℂ) • N (σ, ξ) := by
    intro s hs
    have hp : min s t ∈ Icc a b := ⟨le_min hs.1 ht.1, (min_le_left _ _).trans hs.2⟩
    have hq : max s t ∈ Icc a b := ⟨hs.1.trans (le_max_left _ _), max_le hs.2 ht.2⟩
    have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
    filter_upwards [hDA' _ hp, hDA' _ hq, hint] with ξ h1 h2 h3
    exact ⟨(h3.mono_set (uIcc_subset_Icc hp hq)).intervalIntegrable,
      duhamel_restart (x := fun σ => velSymbol (u σ) ξ) (n := fun σ => N (σ, ξ)) hp.1 min_le_max
        ((h3.mono_set (uIcc_subset_Icc ha hq)).intervalIntegrable) h1 h2⟩
  have hT : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • velSymbol (u t) ξ + N (t, ξ)) 1
      (weightL1Measure k) := by
    obtain ⟨L, hL⟩ : ∃ L : Lp CSpace 1 (weightL1Measure (k + 2)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
        ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 2))),
          ∃ hg : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ) 1 (weightL1Measure k),
            L (hf.toLp f) = hg.toLp _ := exists_clm_mulNormSq k
    obtain ⟨hg, -⟩ := hL _ (memLp_curve hW hc (k + 2) ht)
    exact hg.add (hNmem k t ht)
  have hderiv := hasDerivWithinAt_of_increment (F := fun s => velSymbol (u s)) k ht hNm
    (fun s hs m => memLp_curve hW hc m hs) (fun m => tendsto_lintegral_vel_sub hW hc m ht)
    (fun m => hNmem m t ht) hNc hD hT
  have htd : timeDerivSymbol (velSymbol (u t)) = fun ξ =>
      -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • velSymbol (u t) ξ + N (t, ξ) := by
    funext ξ
    rw [hNeq t ht ξ]
    rfl
  rw [htd]
  exact hderiv

end Breakdown.FarField

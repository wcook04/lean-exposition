import Breakdown.Cert.CoerciveNodes

open scoped ENNReal Topology
open MeasureTheory Filter

namespace Breakdown

namespace Coercive

namespace Internal

namespace DensityPassageEnergy

theorem norm_add_sq_le (a b : Space) {ε : ℝ} (hε : 0 < ε) :
    ‖a + b‖ ^ 2 ≤ (1 + ε) * ‖a‖ ^ 2 + (1 + 1 / ε) * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h0 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have key : 2 * ‖a‖ * ‖b‖ ≤ ε * ‖a‖ ^ 2 + (1 / ε) * ‖b‖ ^ 2 := by
    have hnn : 0 ≤ (ε * ‖a‖ - ‖b‖) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
    have e : (ε * ‖a‖ - ‖b‖) ^ 2 / ε = ε * ‖a‖ ^ 2 - 2 * ‖a‖ * ‖b‖ + (1 / ε) * ‖b‖ ^ 2 := by
      field_simp
      ring
    linarith
  nlinarith

theorem continuous_secondDerivSq : Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => secondDerivSq K) := by
  unfold secondDerivSq
  fun_prop

theorem secondDerivSq_sub_comm (K K' : Space →L[ℝ] Space →L[ℝ] Space) : secondDerivSq (K - K') = secondDerivSq (K' - K) := by
  unfold secondDerivSq
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  simp only [sub_apply]
  rw [norm_sub_rev]

theorem matSq_sub_comm (L L' : Space →L[ℝ] Space) : matSq (L - L') = matSq (L' - L) := by
  unfold matSq
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sub_apply]
  rw [norm_sub_rev]

theorem continuous_traceSq :
    Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => ‖secondDerivTrace K‖ ^ 2) := by
  unfold secondDerivTrace
  fun_prop

theorem continuous_matNorm : Continuous (fun K : Space →L[ℝ] Space => matSq K) := by
  unfold matSq
  fun_prop

theorem restrict_prod_eq : (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
    = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem periodLIntegral_eq_prod_measure {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) volume) :
    periodLIntegral f = ∫⁻ z, ENNReal.ofReal (f z.1 z.2) ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  rw [lintegral_prod _ (by rw [← restrict_prod_eq]; exact hf.restrict)]
  rfl

theorem matSq_nonneg (L : Space →L[ℝ] Space) : 0 ≤ matSq L := by
  unfold matSq
  positivity

theorem secondDerivSq_nonneg (K : Space →L[ℝ] Space →L[ℝ] Space) : 0 ≤ secondDerivSq K := by
  unfold secondDerivSq
  positivity

theorem trace_sq_le (X : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace X‖ ^ 2 ≤ 3 * secondDerivSq X := by
  unfold secondDerivTrace secondDerivSq
  have h1 : ‖∑ j : Fin 3, X (unitVector j) (unitVector j)‖
      ≤ ∑ j : Fin 3, ‖X (unitVector j) (unitVector j)‖ := norm_sum_le _ _
  have h0 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h2 : (∑ j : Fin 3, ‖X (unitVector j) (unitVector j)‖) ^ 2
      ≤ 3 * ∑ j : Fin 3, ‖X (unitVector j) (unitVector j)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin 3 => ‖X (unitVector j) (unitVector j)‖)
    simpa using this
  have h3 : ∑ j : Fin 3, ‖X (unitVector j) (unitVector j)‖ ^ 2
      ≤ ∑ j : Fin 3, ∑ l : Fin 3, ‖X (unitVector j) (unitVector l)‖ ^ 2 :=
    Finset.sum_le_sum fun j _ => Finset.single_le_sum
      (f := fun l => ‖X (unitVector j) (unitVector l)‖ ^ 2) (fun l _ => sq_nonneg _) (Finset.mem_univ j)
  linarith

theorem secondDerivTrace_add_sub (K K' : Space →L[ℝ] Space →L[ℝ] Space) :
    secondDerivTrace K' = secondDerivTrace K + secondDerivTrace (K' - K) := by
  unfold secondDerivTrace
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp

theorem matSq_le (L L' : Space →L[ℝ] Space) {ε : ℝ} (hε : 0 < ε) :
    matSq L' ≤ (1 + ε) * matSq L + (1 + 1 / ε) * matSq (L' - L) := by
  unfold matSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have := norm_add_sq_le (L (unitVector i)) ((L' - L) (unitVector i)) hε
  simpa using this

theorem energy_point_le (K K' : Space →L[ℝ] Space →L[ℝ] Space) (L L' : Space →L[ℝ] Space)
    {wy B ε : ℝ} (hw0 : 0 ≤ wy) (hwB : wy ≤ B) (hε : 0 < ε) :
    ‖secondDerivTrace K'‖ ^ 2 + wy * matSq L'
      ≤ (1 + ε) * (‖secondDerivTrace K‖ ^ 2 + wy * matSq L)
        + (1 + 1 / ε) * (3 * secondDerivSq (K' - K) + B * matSq (L' - L)) := by
  have h1 := norm_add_sq_le (secondDerivTrace K) (secondDerivTrace (K' - K)) hε
  rw [← secondDerivTrace_add_sub] at h1
  have h2 := trace_sq_le (K' - K)
  have hf := matSq_le L L' hε
  have hfn := matSq_nonneg (L' - L)
  have hc : 0 ≤ 1 + 1 / ε := by positivity
  have a1 := mul_le_mul_of_nonneg_left hf hw0
  have a2 := mul_le_mul_of_nonneg_right hwB hfn
  have a3 := mul_le_mul_of_nonneg_left a2 hc
  have a4 := mul_le_mul_of_nonneg_left h2 hc
  nlinarith

theorem periodLIntegral_const_mul {c : ℝ} (hc : 0 ≤ c) (f : ℝ → Space → ℝ) :
    periodLIntegral (fun σ y => c * f σ y) = ENNReal.ofReal c * periodLIntegral f := by
  unfold periodLIntegral
  simp_rw [ENNReal.ofReal_mul hc]
  have hin : ∀ σ, ∫⁻ y, ENNReal.ofReal c * ENNReal.ofReal (f σ y)
      = ENNReal.ofReal c * ∫⁻ y, ENNReal.ofReal (f σ y) :=
    fun σ => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  simp_rw [hin]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem periodLIntegral_mono {f g : ℝ → Space → ℝ} (h : ∀ σ y, f σ y ≤ g σ y) :
    periodLIntegral f ≤ periodLIntegral g := by
  unfold periodLIntegral
  exact lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (h σ y)

theorem aem_ofReal {f : ℝ × Space → ℝ} (hf : AEStronglyMeasurable f volume) :
    AEMeasurable (fun z => ENNReal.ofReal (f z)) volume :=
  ENNReal.measurable_ofReal.comp_aemeasurable hf.aemeasurable

theorem periodLIntegral_add_le' {f g : ℝ → Space → ℝ}
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) :
    periodLIntegral (fun σ y => f σ y + g σ y) ≤ periodLIntegral f + periodLIntegral g :=
  by
    rw [periodLIntegral_eq_prod_measure (f := fun σ y => f σ y + g σ y) (aem_ofReal (hf.add hg)),
      periodLIntegral_eq_prod_measure (aem_ofReal hf), periodLIntegral_eq_prod_measure (aem_ofReal hg),
      ← lintegral_add_left' (by rw [← restrict_prod_eq]; exact (aem_ofReal hf).restrict)]
    exact lintegral_mono fun z => ENNReal.ofReal_add_le

theorem tendsto_of_eps_bounds {a : ℝ≥0∞} {A D : ℕ → ℝ≥0∞} (ha : a ≠ ⊤)
    (hD : Tendsto D atTop (𝓝 0))
    (hup : ∀ ε : ℝ, 0 < ε → ∀ n, A n ≤ ENNReal.ofReal (1 + ε) * a + ENNReal.ofReal (1 + 1 / ε) * D n)
    (hlow : ∀ ε : ℝ, 0 < ε → ∀ n, a ≤ ENNReal.ofReal (1 + ε) * A n + ENNReal.ofReal (1 + 1 / ε) * D n) :
    Tendsto A atTop (𝓝 a) := by
  have hε : Tendsto (fun j : ℕ => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 1) := by
    have h : Tendsto (fun j : ℕ => 1 + 1 / ((j : ℝ) + 1)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h
    have h2 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1))) atTop (𝓝 (ENNReal.ofReal 1)) :=
      (ENNReal.continuous_ofReal.tendsto 1).comp h
    rwa [ENNReal.ofReal_one] at h2
  have hpos : ∀ j : ℕ, (0 : ℝ) < 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hcD : ∀ c : ℝ≥0∞, c ≠ ⊤ → Tendsto (fun n => c * D n) atTop (𝓝 0) := fun c hc => by
    simpa using ENNReal.Tendsto.const_mul hD (Or.inr hc)
  refine tendsto_of_le_liminf_of_limsup_le ?_ ?_ (by isBoundedDefault) (by isBoundedDefault)
  · have key : ∀ j : ℕ, a ≤ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * liminf A atTop := by
      intro j
      have h1 : a ≤ liminf (fun n => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop :=
        le_liminf_of_le (by isBoundedDefault) (Eventually.of_forall fun n => hlow _ (hpos j) n)
      have e1 : liminf (fun n => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop
          = liminf (fun n => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * A n) atTop :=
        ENNReal.liminf_add_of_right_tendsto_zero (hcD _ ENNReal.ofReal_ne_top) _
      rw [e1, ENNReal.liminf_const_mul_of_ne_top ENNReal.ofReal_ne_top] at h1
      exact h1
    have ht := ENNReal.Tendsto.mul_const hε (Or.inl one_ne_zero) (b := liminf A atTop)
    rw [one_mul] at ht
    exact ge_of_tendsto' ht key
  · have key : ∀ j : ℕ, limsup A atTop ≤ ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a := by
      intro j
      have ht : Tendsto (fun n => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a
          + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop
          (𝓝 (ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a)) := by
        simpa using tendsto_const_nhds.add (hcD _ ENNReal.ofReal_ne_top)
      calc limsup A atTop ≤ limsup (fun n => ENNReal.ofReal (1 + 1 / ((j : ℝ) + 1)) * a
            + ENNReal.ofReal (1 + 1 / (1 / ((j : ℝ) + 1))) * D n) atTop :=
            limsup_le_limsup (Eventually.of_forall fun n => hup _ (hpos j) n)
        _ = _ := ht.limsup_eq
    have ht := ENNReal.Tendsto.mul_const hε (Or.inr ha)
    rw [one_mul] at ht
    exact ge_of_tendsto' ht key

end DensityPassageEnergy

end Internal

open Internal.DensityPassageEnergy in
theorem weightedEnergy_tendsto {w : Space → ℝ} {B : ℝ} (hw : Measurable w) (hw0 : ∀ y, 0 ≤ w y)
    (hwB : ∀ y, w y ≤ B) {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {Gn : ℕ → ℝ → Space → (Space →L[ℝ] Space)}
    {Hn : ℕ → ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume)
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume)
    (hGn : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => Gn n z.1 z.2) volume)
    (hHn : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => Hn n z.1 z.2) volume)
    (hG2 : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤)
    (hH2 : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) < ⊤)
    (hcG : Tendsto (fun n => periodLIntegral (fun σ y => matSq (Gn n σ y - G σ y))) atTop (𝓝 0))
    (hcH : Tendsto (fun n => periodLIntegral (fun σ y => secondDerivSq (Hn n σ y - H σ y))) atTop (𝓝 0)) :
    Tendsto (fun n => weightedEnergy w (Gn n) (Hn n)) atTop (𝓝 (weightedEnergy w G H)) := by
  have hB0 : 0 ≤ B := (hw0 0).trans (hwB 0)
  have mW : AEStronglyMeasurable (fun z : ℝ × Space => w z.2) volume :=
    (hw.comp measurable_snd).aestronglyMeasurable
  have mE : ∀ (G' : ℝ → Space → (Space →L[ℝ] Space)) (H' : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      AEStronglyMeasurable (fun z : ℝ × Space => G' z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => H' z.1 z.2) volume →
      AEStronglyMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H' z.1 z.2)‖ ^ 2 + w z.2 * matSq (G' z.1 z.2))
        volume := fun G' H' hG' hH' =>
    (continuous_traceSq.comp_aestronglyMeasurable hH').add
      (mW.mul (continuous_matNorm.comp_aestronglyMeasurable hG'))
  have mD : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space =>
      3 * secondDerivSq (Hn n z.1 z.2 - H z.1 z.2) + B * matSq (Gn n z.1 z.2 - G z.1 z.2)) volume := fun n =>
    (aestronglyMeasurable_const.mul (continuous_secondDerivSq.comp_aestronglyMeasurable ((hHn n).sub hH))).add
      (aestronglyMeasurable_const.mul (continuous_matNorm.comp_aestronglyMeasurable ((hGn n).sub hG)))
  set a := periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) with ha_def
  set D : ℕ → ℝ≥0∞ := fun n => periodLIntegral (fun σ y =>
    3 * secondDerivSq (Hn n σ y - H σ y) + B * matSq (Gn n σ y - G σ y)) with hD_def
  have hfin : a ≠ ⊤ := by
    have h1 : a ≤ periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + B * matSq (G σ y)) :=
      periodLIntegral_mono fun σ y => by
        have := mul_le_mul_of_nonneg_right (hwB y) (matSq_nonneg (G σ y))
        linarith
    have h2 := periodLIntegral_add_le' (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)
      (g := fun σ y => B * matSq (G σ y)) (continuous_traceSq.comp_aestronglyMeasurable hH)
      (aestronglyMeasurable_const.mul (continuous_matNorm.comp_aestronglyMeasurable hG))
    rw [periodLIntegral_const_mul hB0] at h2
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hH2.ne, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG2.ne⟩)
      (h1.trans h2)
  have hDt : Tendsto D atTop (𝓝 0) := by
    have hb : Tendsto (fun n => ENNReal.ofReal 3 * periodLIntegral (fun σ y => secondDerivSq (Hn n σ y - H σ y))
        + ENNReal.ofReal B * periodLIntegral (fun σ y => matSq (Gn n σ y - G σ y))) atTop (𝓝 0) := by
      have h3 := (ENNReal.Tendsto.const_mul hcH (Or.inr (ENNReal.ofReal_ne_top (r := 3)))).add
        (ENNReal.Tendsto.const_mul hcG (Or.inr (ENNReal.ofReal_ne_top (r := B))))
      simpa using h3
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb (fun _ => zero_le) fun n => ?_
    have h := periodLIntegral_add_le' (f := fun σ y => 3 * secondDerivSq (Hn n σ y - H σ y))
      (g := fun σ y => B * matSq (Gn n σ y - G σ y))
      (aestronglyMeasurable_const.mul (continuous_secondDerivSq.comp_aestronglyMeasurable ((hHn n).sub hH)))
      (aestronglyMeasurable_const.mul (continuous_matNorm.comp_aestronglyMeasurable ((hGn n).sub hG)))
    rw [periodLIntegral_const_mul (by norm_num), periodLIntegral_const_mul hB0] at h
    exact h
  have key : Tendsto (fun n => periodLIntegral (fun σ y =>
      ‖secondDerivTrace (Hn n σ y)‖ ^ 2 + w y * matSq (Gn n σ y))) atTop (𝓝 a) := by
    refine tendsto_of_eps_bounds hfin hDt (fun ε hε n => ?_) (fun ε hε n => ?_)
    · have h1 := periodLIntegral_mono (f := fun σ y => ‖secondDerivTrace (Hn n σ y)‖ ^ 2 + w y * matSq (Gn n σ y))
        (g := fun σ y => (1 + ε) * (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y))
          + (1 + 1 / ε) * (3 * secondDerivSq (Hn n σ y - H σ y) + B * matSq (Gn n σ y - G σ y)))
        fun σ y => energy_point_le _ _ _ _ (hw0 y) (hwB y) hε
      have h2 := periodLIntegral_add_le'
        (f := fun σ y => (1 + ε) * (‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)))
        (g := fun σ y => (1 + 1 / ε) * (3 * secondDerivSq (Hn n σ y - H σ y) + B * matSq (Gn n σ y - G σ y)))
        (aestronglyMeasurable_const.mul (mE G H hG hH)) (aestronglyMeasurable_const.mul (mD n))
      rw [periodLIntegral_const_mul (by positivity), periodLIntegral_const_mul (by positivity)] at h2
      exact h1.trans h2
    · have h1 := periodLIntegral_mono (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y))
        (g := fun σ y => (1 + ε) * (‖secondDerivTrace (Hn n σ y)‖ ^ 2 + w y * matSq (Gn n σ y))
          + (1 + 1 / ε) * (3 * secondDerivSq (Hn n σ y - H σ y) + B * matSq (Gn n σ y - G σ y)))
        fun σ y => by
          have := energy_point_le (Hn n σ y) (H σ y) (Gn n σ y) (G σ y) (hw0 y) (hwB y) hε
          rwa [secondDerivSq_sub_comm, matSq_sub_comm] at this
      have h2 := periodLIntegral_add_le'
        (f := fun σ y => (1 + ε) * (‖secondDerivTrace (Hn n σ y)‖ ^ 2 + w y * matSq (Gn n σ y)))
        (g := fun σ y => (1 + 1 / ε) * (3 * secondDerivSq (Hn n σ y - H σ y) + B * matSq (Gn n σ y - G σ y)))
        (aestronglyMeasurable_const.mul (mE (Gn n) (Hn n) (hGn n) (hHn n)))
        (aestronglyMeasurable_const.mul (mD n))
      rw [periodLIntegral_const_mul (by positivity), periodLIntegral_const_mul (by positivity)] at h2
      exact h1.trans h2
  exact (ENNReal.tendsto_toReal hfin).comp key

end Coercive

end Breakdown

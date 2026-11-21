import Breakdown.FracCert.HeldStateLimitBParts
import Breakdown.FracCert.HeldStateLimitBWeak
import Breakdown.FracCert.SixthGradientBound

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace SecondOrderWeakLimitInternal

private theorem mul_pow_five_le {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) : a * c ^ 5 ≤ (a ^ 6 + 5 * c ^ 6) / 6 := by
  have hq : 0 ≤ a ^ 4 + 2 * a ^ 3 * c + 3 * a ^ 2 * c ^ 2 + 4 * a * c ^ 3 + 5 * c ^ 4 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (a - c)) hq]

private theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  rw [ae_iff]
  simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton]
  exact measure_singleton 0

private theorem unitVector_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

private theorem pair_tendsto {u : ℕ → Space → Space} {w₀ : Space → Space}
    (hl : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) atTop (nhds (∫ y, inner ℝ (w₀ y) (g y))))
    {h : Space → Space} (hh : MemLp (fun y => ‖y‖ • h y) 2 volume) :
    Tendsto (fun n => ∫ y, inner ℝ (u n y) (h y)) atTop (nhds (∫ y, inner ℝ (‖y‖ • w₀ y) (h y))) := by
  have e1 : ∀ n, ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (‖y‖ • h y) = ∫ y, inner ℝ (u n y) (h y) := by
    intro n
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_zero] with y hy
    have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]
  have e2 : ∫ y, inner ℝ (w₀ y) (‖y‖ • h y) = ∫ y, inner ℝ (‖y‖ • w₀ y) (h y) := by
    congr 1
    funext y
    rw [real_inner_smul_left, real_inner_smul_right]
  rw [← e2]
  exact (hl _ hh).congr e1

private theorem test_integrable {f : Space → Space} {p : ℝ≥0∞} (hf : MemLp f p volume) (hp : 1 ≤ p)
    {g : Space → ℝ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun y => g y • f y) volume :=
  (hf.locallyIntegrable hp).integrable_smul_left_of_hasCompactSupport hg hgc

private theorem inner_integral {f : Space → Space} {c : Space → ℝ}
    (hf : Integrable (fun y => c y • f y) volume) (v : Space) :
    inner ℝ (∫ y, c y • f y) v = ∫ y, inner ℝ (f y) (c y • v) := by
  rw [real_inner_comm, ← integral_inner hf]
  congr 1
  funext y
  rw [real_inner_smul_right, real_inner_smul_right, real_inner_comm]

private theorem test_memLp {c : Space → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c) (v : Space) :
    MemLp (fun y => c y • v) 2 volume :=
  (hc.smul continuous_const).memLp_of_hasCompactSupport
    (hcs.mono fun y hy => fun h0 => hy (by simp [h0]))

private theorem test_memLp_weight {c : Space → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c) (v : Space) :
    MemLp (fun y => ‖y‖ • (c y • v)) 2 volume :=
  (continuous_norm.smul (hc.smul continuous_const)).memLp_of_hasCompactSupport
    (hcs.mono fun y hy => fun h0 => hy (by simp [h0]))

private theorem deriv_test_continuous {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

private theorem deriv_test_support {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
  (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)

private theorem col_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
      h.measurable_gradient
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h.gradient_two.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)

private theorem entry_memLp {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {m : ℕ} (h : IsSecondOrderField m v G H) (i j : Fin 3) :
    MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector i)).continuous.comp_aestronglyMeasurable
        h.measurable_second)
  refine (memLp_two_iff_integrable_sq_norm hm).2 (h.second_two.mono' (hm.norm.pow 2) ?_)
  refine Filter.Eventually.of_forall fun y => ?_
  rw [Real.norm_of_nonneg (by positivity)]
  calc ‖H y (unitVector i) (unitVector j)‖ ^ 2 ≤ ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ ∑ i' : Fin 3, ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i)

private theorem turnStep_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

private theorem turnStep_smul (m : ℕ) (c : ℝ) (a : Space) : turnStep m (c • a) = c • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep, EuclideanSpace.single_apply] <;> ring

private theorem turnStep_norm (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, turnStep, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * Real.pi / m)

private theorem mirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply] <;> ring

private theorem mirror_smul (c : ℝ) (a : Space) : mirror (c • a) = c • mirror a := by
  ext i
  fin_cases i <;> simp [mirror, EuclideanSpace.single_apply]

private theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror, EuclideanSpace.single_apply, Real.norm_eq_abs, sq_abs]

private def turnIso (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := turnStep m, map_add' := turnStep_add m, map_smul' := turnStep_smul m,
      norm_map' := turnStep_norm m } rfl

private def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := mirror, map_add' := mirror_add, map_smul' := mirror_smul, norm_map' := mirror_norm } rfl

private theorem turnIso_coe (m : ℕ) : ⇑(turnIso m) = turnStep m := by
  unfold turnIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

private theorem mirrorIso_coe : ⇑mirrorIso = mirror := by
  unfold mirrorIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

private theorem inner_symm (e : Space ≃ₗᵢ[ℝ] Space) (a b : Space) :
    inner ℝ a (e.symm b) = inner ℝ (e a) b := by
  rw [← e.inner_map_map, e.apply_symm_apply]

private theorem sym_limit (e : Space ≃ₗᵢ[ℝ] Space) {u : ℕ → Space → Space} {w₀ : Space → Space}
    (hw₀ : MemLp w₀ 2 volume) (hs : ∀ n, ∀ᵐ y ∂volume, u n (e y) = e (u n y))
    (hl : ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g y)) atTop (nhds (∫ y, inner ℝ (w₀ y) (g y)))) :
    ∀ᵐ y ∂volume, ‖e y‖ • w₀ (e y) = e (‖y‖ • w₀ y) := by
  have hmp : MeasurePreserving e volume volume := e.measurePreserving
  have hmps : MeasurePreserving e.symm volume volume := e.symm.measurePreserving
  have hemb : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  have cv : ∀ F : Space → ℝ, ∫ y, F y = ∫ z, F (e z) := fun F => (hmp.integral_comp hemb F).symm
  have hA : MemLp (fun y => w₀ (e y)) 2 volume := hw₀.comp_measurePreserving hmp
  have hB : MemLp (fun y => e (w₀ y)) 2 volume :=
    hw₀.of_le (e.continuous.comp_aestronglyMeasurable hw₀.1) (ae_of_all _ fun y => by rw [e.norm_map])
  have key : ∀ g : Space → Space, MemLp g 2 volume →
      ∫ y, inner ℝ (w₀ (e y)) (g y) = ∫ y, inner ℝ (e (w₀ y)) (g y) := by
    intro g hg
    have h1 := hl (fun y => g (e.symm y)) (hg.comp_measurePreserving hmps)
    have h2 := hl (fun y => e.symm (g y))
      (hg.of_le (e.symm.continuous.comp_aestronglyMeasurable hg.1) (ae_of_all _ fun y => by rw [e.symm.norm_map]))
    have r1 : ∀ n, ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (g (e.symm y)) =
        ∫ z, inner ℝ (‖z‖⁻¹ • u n (e z)) (g z) := by
      intro n
      rw [cv (fun y => inner ℝ (‖y‖⁻¹ • u n y) (g (e.symm y)))]
      simp only [LinearIsometryEquiv.norm_map, LinearIsometryEquiv.symm_apply_apply]
    have r2 : ∀ n, ∫ y, inner ℝ (‖y‖⁻¹ • u n y) (e.symm (g y)) =
        ∫ z, inner ℝ (‖z‖⁻¹ • u n (e z)) (g z) := by
      intro n
      refine integral_congr_ae ?_
      filter_upwards [hs n] with z hz
      rw [hz, inner_symm, LinearIsometryEquiv.map_smul]
    have l1 : ∫ y, inner ℝ (w₀ y) (g (e.symm y)) = ∫ z, inner ℝ (w₀ (e z)) (g z) := by
      rw [cv (fun y => inner ℝ (w₀ y) (g (e.symm y)))]
      simp only [LinearIsometryEquiv.symm_apply_apply]
    have l2 : ∫ y, inner ℝ (w₀ y) (e.symm (g y)) = ∫ z, inner ℝ (e (w₀ z)) (g z) := by
      congr 1
      funext z
      rw [inner_symm]
    rw [l1] at h1
    rw [l2] at h2
    exact tendsto_nhds_unique (h1.congr r1) (h2.congr r2)
  have hDm : MemLp (fun y => w₀ (e y) - e (w₀ y)) 2 volume := hA.sub hB
  have h0 : ∫ y, ‖w₀ (e y) - e (w₀ y)‖ ^ 2 = 0 := by
    have k := key _ hDm
    have e1 : ∫ y, ‖w₀ (e y) - e (w₀ y)‖ ^ 2 = (∫ y, inner ℝ (w₀ (e y)) (w₀ (e y) - e (w₀ y))) -
        ∫ y, inner ℝ (e (w₀ y)) (w₀ (e y) - e (w₀ y)) := by
      rw [← integral_sub (WeakFieldLimit.pair_integrable hA hDm) (WeakFieldLimit.pair_integrable hB hDm)]
      congr 1
      funext y
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    rw [e1, k, sub_self]
  have hi : Integrable (fun y => ‖w₀ (e y) - e (w₀ y)‖ ^ 2) volume :=
    (memLp_two_iff_integrable_sq_norm hDm.1).1 hDm
  have hz := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hi).1 h0
  filter_upwards [hz] with y hy
  have hy' : w₀ (e y) = e (w₀ y) := by simpa [sub_eq_zero] using hy
  rw [e.norm_map, hy', LinearIsometryEquiv.map_smul]

private theorem six_of_pairing {u : ℕ → Space → Space} {u₀ : Space → Space}
    (hu₀ : AEStronglyMeasurable u₀ volume) (A : ℝ) (hu : ∀ n, MemLp (u n) 6 volume)
    (hA : ∀ n, ∫ y, ‖u n y‖ ^ 6 ≤ A)
    (hl : ∀ h : Space → Space, MemLp (fun y => ‖y‖ • h y) 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (u n y) (h y)) atTop (nhds (∫ y, inner ℝ (u₀ y) (h y)))) :
    MemLp u₀ 6 volume := by
  set v := hu₀.mk u₀ with hv
  have hvs : StronglyMeasurable v := hu₀.stronglyMeasurable_mk
  have hae : u₀ =ᵐ[volume] v := hu₀.ae_eq_mk
  have hvm : Measurable v := hvs.measurable
  set F : Space → ℝ := fun y => ‖v y‖ ^ 6 with hF
  have hF0 : ∀ y, 0 ≤ F y := fun y => by positivity
  have hFm : Measurable F := hvm.norm.pow_const 6
  set E : ℕ → Set Space := fun k => {y | ‖y‖ ≤ k ∧ ‖v y‖ ≤ k} with hEdef
  have hE : ∀ k, MeasurableSet (E k) := fun k =>
    (measurableSet_le measurable_norm measurable_const).inter (measurableSet_le hvm.norm measurable_const)
  have hEfin : ∀ k, volume (E k) ≠ ⊤ := fun k =>
    ((measure_mono (fun y (hy : y ∈ E k) =>
      (mem_closedBall_zero_iff.2 hy.1 : y ∈ Metric.closedBall (0 : Space) k))).trans_lt
      measure_closedBall_lt_top).ne
  have hFint : ∀ k, Integrable ((E k).indicator F) volume := fun k =>
    (Measure.integrableOn_of_bounded (M := (k : ℝ) ^ 6) (hEfin k) hFm.aestronglyMeasurable
      ((ae_restrict_iff' (hE k)).2 (Eventually.of_forall fun y hy => by
        rw [Real.norm_of_nonneg (hF0 y)]
        exact pow_le_pow_left₀ (norm_nonneg _) hy.2 6))).integrable_indicator (hE k)
  have hu6 : ∀ n, Integrable (fun y => ‖u n y‖ ^ 6) volume := by
    intro n
    have h6 : MemLp (u n) ((6 : ℕ) : ℝ≥0∞) volume := by simpa using hu n
    exact h6.integrable_norm_pow (by norm_num)
  have hbnd : ∀ k, ∫ y, (E k).indicator F y ≤ A := by
    intro k
    set h : Space → Space := (E k).indicator (fun y => ‖v y‖ ^ 4 • v y) with hh
    have hhmeas : AEStronglyMeasurable h volume :=
      (((hvm.norm.pow_const 4).smul hvm).indicator (hE k)).aestronglyMeasurable
    have hhm : MemLp (fun y => ‖y‖ • h y) 2 volume := by
      have e : (fun y => ‖y‖ • h y) = (E k).indicator (fun y => ‖y‖ • (‖v y‖ ^ 4 • v y)) := by
        funext y
        by_cases hy : y ∈ E k
        · rw [hh, Set.indicator_of_mem hy, Set.indicator_of_mem hy]
        · rw [hh, Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero]
      rw [e, memLp_indicator_iff_restrict (hE k)]
      haveI : IsFiniteMeasure (volume.restrict (E k)) := isFiniteMeasure_restrict.2 (hEfin k)
      refine MemLp.of_bound (continuous_norm.aestronglyMeasurable.smul
        ((hvm.norm.pow_const 4).aestronglyMeasurable.smul hvs.aestronglyMeasurable))
        ((k : ℝ) * ((k : ℝ) ^ 4 * k)) ?_
      refine (ae_restrict_iff' (hE k)).2 (Eventually.of_forall fun y hy => ?_)
      simp only [norm_smul, norm_pow, norm_norm]
      have h3 : ‖v y‖ ^ 4 ≤ (k : ℝ) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hy.2 4
      exact mul_le_mul hy.1 (mul_le_mul h3 hy.2 (norm_nonneg _) (by positivity)) (by positivity)
        (by positivity)
    have hlim := hl h hhm
    have e0 : ∫ y, inner ℝ (u₀ y) (h y) = ∫ y, (E k).indicator F y := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hy]
      by_cases hyE : y ∈ E k
      · rw [hh, Set.indicator_of_mem hyE, Set.indicator_of_mem hyE, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        simp only [hF]
        ring
      · rw [hh, Set.indicator_of_notMem hyE, Set.indicator_of_notMem hyE, inner_zero_right]
    rw [e0] at hlim
    have hnh : ∀ y, ‖h y‖ = (E k).indicator (fun y => ‖v y‖ ^ 5) y := by
      intro y
      by_cases hyE : y ∈ E k
      · rw [hh, Set.indicator_of_mem hyE, Set.indicator_of_mem hyE, norm_smul, norm_pow, norm_norm]
        ring
      · rw [hh, Set.indicator_of_notMem hyE, Set.indicator_of_notMem hyE, norm_zero]
    have hpt : ∀ n y, ‖u n y‖ * ‖h y‖ ≤ (‖u n y‖ ^ 6 + 5 * (E k).indicator F y) / 6 := by
      intro n y
      rw [hnh]
      by_cases hyE : y ∈ E k
      · rw [Set.indicator_of_mem hyE, Set.indicator_of_mem hyE]
        exact mul_pow_five_le (norm_nonneg _) (norm_nonneg _)
      · rw [Set.indicator_of_notMem hyE, Set.indicator_of_notMem hyE, mul_zero, mul_zero, add_zero]
        positivity
    have hBi : ∀ n, Integrable (fun y => (‖u n y‖ ^ 6 + 5 * (E k).indicator F y) / 6) volume := fun n =>
      ((hu6 n).add ((hFint k).const_mul 5)).div_const 6
    have hpi : ∀ n, Integrable (fun y => inner ℝ (u n y) (h y)) volume := fun n =>
      (hBi n).mono' ((hu n).1.inner hhmeas) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (hpt n y))
    have hle : ∀ n, ∫ y, inner ℝ (u n y) (h y) ≤ (A + 5 * ∫ y, (E k).indicator F y) / 6 := by
      intro n
      calc ∫ y, inner ℝ (u n y) (h y) ≤ ∫ y, (‖u n y‖ ^ 6 + 5 * (E k).indicator F y) / 6 :=
            integral_mono (hpi n) (hBi n) fun y => (real_inner_le_norm _ _).trans (hpt n y)
        _ = ((∫ y, ‖u n y‖ ^ 6) + 5 * ∫ y, (E k).indicator F y) / 6 := by
            rw [integral_div, integral_add (hu6 n) ((hFint k).const_mul 5), integral_const_mul]
        _ ≤ _ := by linarith [hA n]
    have := le_of_tendsto' hlim hle
    linarith
  have hFi : Integrable F volume := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall hF0)]
    have hsup : ∀ y, ENNReal.ofReal (F y) = ⨆ k : ℕ, ENNReal.ofReal ((E k).indicator F y) := by
      intro y
      refine le_antisymm ?_ (iSup_le fun k =>
        ENNReal.ofReal_le_ofReal (Set.indicator_le_self' (fun _ _ => hF0 _) y))
      obtain ⟨k, hk⟩ := exists_nat_ge (max ‖y‖ ‖v y‖)
      have hyk : y ∈ E k := ⟨(le_max_left _ _).trans hk, (le_max_right _ _).trans hk⟩
      exact le_iSup_of_le k (by rw [Set.indicator_of_mem hyk])
    have hmono : Monotone (fun k : ℕ => fun y => ENNReal.ofReal ((E k).indicator F y)) := by
      intro k l hkl y
      have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
      exact ENNReal.ofReal_le_ofReal (Set.indicator_le_indicator_of_subset
        (fun z (hz : z ∈ E k) => (⟨hz.1.trans hkl', hz.2.trans hkl'⟩ : z ∈ E l)) (fun z => hF0 z) y)
    calc ∫⁻ y, ENNReal.ofReal (F y) = ∫⁻ y, ⨆ k : ℕ, ENNReal.ofReal ((E k).indicator F y) :=
          lintegral_congr hsup
      _ = ⨆ k : ℕ, ∫⁻ y, ENNReal.ofReal ((E k).indicator F y) :=
          lintegral_iSup (fun k => ENNReal.measurable_ofReal.comp (hFm.indicator (hE k))) hmono
      _ ≤ ENNReal.ofReal A := iSup_le fun k => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hFint k)
            (Eventually.of_forall fun y => Set.indicator_nonneg (fun z _ => hF0 z) y)]
          exact ENNReal.ofReal_le_ofReal (hbnd k)
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hv6 : MemLp v 6 volume := by
    refine (integrable_norm_rpow_iff hvs.aestronglyMeasurable (p := 6) (by norm_num) (by norm_num)).1 ?_
    refine hFi.congr (Eventually.of_forall fun y => ?_)
    simp [hF]
  exact hv6.ae_eq hae.symm

end SecondOrderWeakLimitInternal

open SecondOrderWeakLimitInternal

theorem secondOrderWeakLimit_holds : SecondOrderWeakLimitStatement := by
  intro m K u G H w₀ G₀ H₀ hf hGK hHK hG₀m hH₀m hw₀ hGc hHc hGl hHl hwl
  obtain ⟨C, hC⟩ := sixthGradientBound
  have hK : ∀ n, ∫ y, ‖u n y‖ ^ 6 ≤ max C 0 * K ^ 3 := by
    intro n
    have h1 := hC (u n) (G n) (hf n).measurable_velocity (hf n).velocity_six (hf n).gradient_two
      (hf n).weak_gradient
    have h0 : 0 ≤ ∫ y, entrySq (G n y) := integral_nonneg fun y => by unfold entrySq; positivity
    have h3 : (∫ y, entrySq (G n y)) ^ 3 ≤ K ^ 3 := pow_le_pow_left₀ h0 (hGK n) 3
    calc _ ≤ C * (∫ y, entrySq (G n y)) ^ 3 := h1
      _ ≤ max C 0 * (∫ y, entrySq (G n y)) ^ 3 :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * K ^ 3 := mul_le_mul_of_nonneg_left h3 (le_max_right _ _)
  have hu₀m : AEStronglyMeasurable (fun y => ‖y‖ • w₀ y) volume :=
    continuous_norm.aestronglyMeasurable.smul hw₀.1
  have hu6 : MemLp (fun y => ‖y‖ • w₀ y) 6 volume :=
    six_of_pairing hu₀m (max C 0 * K ^ 3) (fun n => (hf n).velocity_six) hK
      (fun h hh => pair_tendsto hwl hh)
  refine ⟨hu₀m, hG₀m, hH₀m, hu6, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [entrySq]
    exact integrable_finsetSum _ fun i _ => (memLp_two_iff_integrable_sq_norm (hGc i).1).1 (hGc i)
  · exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (memLp_two_iff_integrable_sq_norm (hHc i j).1).1 (hHc i j)
  · intro φ hφ j
    beta_reduce
    have hc := deriv_test_continuous hφ j
    have hs := deriv_test_support hφ j
    refine ext_inner_right ℝ fun v => ?_
    have hI0 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • (‖y‖ • w₀ y)) volume :=
      test_integrable hu6 (by norm_num) hc hs
    have hJ0 : Integrable (fun y => φ y • G₀ y (unitVector j)) volume :=
      test_integrable (hGc j) (by norm_num) hφ.1.continuous hφ.2
    have lim1 : Tendsto (fun n => inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • u n y) v) atTop
        (nhds (inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • (‖y‖ • w₀ y)) v)) := by
      rw [inner_integral hI0]
      refine (pair_tendsto hwl (test_memLp_weight hc hs v)).congr fun n => ?_
      rw [inner_integral (test_integrable (hf n).velocity_six (by norm_num) hc hs)]
    have lim2 : Tendsto (fun n => inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • u n y) v) atTop
        (nhds (inner ℝ (-∫ y, φ y • G₀ y (unitVector j)) v)) := by
      rw [inner_neg_left, inner_integral hJ0]
      refine ((hGl j _ (test_memLp hφ.1.continuous hφ.2 v)).neg).congr fun n => ?_
      rw [(hf n).weak_gradient φ hφ j, inner_neg_left,
        inner_integral (test_integrable (col_memLp (hf n) j) (by norm_num) hφ.1.continuous hφ.2)]
    exact tendsto_nhds_unique lim1 lim2
  · intro φ hφ i j
    have hc := deriv_test_continuous hφ j
    have hs := deriv_test_support hφ j
    refine ext_inner_right ℝ fun v => ?_
    have hI0 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G₀ y (unitVector i)) volume :=
      test_integrable (hGc i) (by norm_num) hc hs
    have hJ0 : Integrable (fun y => φ y • H₀ y (unitVector j) (unitVector i)) volume :=
      test_integrable (hHc j i) (by norm_num) hφ.1.continuous hφ.2
    have lim1 : Tendsto (fun n => inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • G n y (unitVector i)) v)
        atTop (nhds (inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • G₀ y (unitVector i)) v)) := by
      rw [inner_integral hI0]
      refine (hGl i _ (test_memLp hc hs v)).congr fun n => ?_
      rw [inner_integral (test_integrable (col_memLp (hf n) i) (by norm_num) hc hs)]
    have lim2 : Tendsto (fun n => inner ℝ (∫ y, fderiv ℝ φ y (unitVector j) • G n y (unitVector i)) v)
        atTop (nhds (inner ℝ (-∫ y, φ y • H₀ y (unitVector j) (unitVector i)) v)) := by
      rw [inner_neg_left, inner_integral hJ0]
      refine ((hHl j i _ (test_memLp hφ.1.continuous hφ.2 v)).neg).congr fun n => ?_
      rw [(hf n).weak_second φ hφ i j, inner_neg_left,
        inner_integral (test_integrable (entry_memLp (hf n) j i) (by norm_num) hφ.1.continuous hφ.2)]
    exact tendsto_nhds_unique lim1 lim2
  · have hti : ∀ i : Fin 3, MemLp (fun y => inner ℝ (G₀ y (unitVector i)) (unitVector i)) 2 volume :=
      fun i => (hGc i).of_le ((hGc i).1.inner aestronglyMeasurable_const) (Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        exact (abs_real_inner_le_norm _ _).trans (by rw [unitVector_norm, mul_one]))
    have htm : MemLp (fun y => ∑ i : Fin 3, inner ℝ (G₀ y (unitVector i)) (unitVector i)) 2 volume := by
      simp only [Fin.sum_univ_three]
      exact ((hti 0).add (hti 1)).add (hti 2)
    set t : Space → ℝ := fun y => ∑ i : Fin 3, inner ℝ (G₀ y (unitVector i)) (unitVector i) with ht
    have hg : ∀ i : Fin 3, MemLp (fun y => t y • unitVector i) 2 volume := fun i =>
      htm.of_le (htm.1.smul aestronglyMeasurable_const) (Eventually.of_forall fun y => by
        rw [norm_smul, unitVector_norm, mul_one])
    have hS0 : ∀ n, ∑ i : Fin 3, ∫ y, inner ℝ (G n y (unitVector i)) (t y • unitVector i) = 0 := by
      intro n
      rw [← integral_finsetSum _ fun i _ => WeakFieldLimit.pair_integrable (col_memLp (hf n) i) (hg i)]
      refine (integral_congr_ae ?_).trans (integral_zero _ _)
      filter_upwards [(hf n).divergence] with y hy
      simp only [real_inner_smul_right]
      rw [← Finset.mul_sum, hy, mul_zero]
    have hlim := tendsto_finset_sum Finset.univ (fun i _ => hGl i (fun y => t y • unitVector i) (hg i))
    have hz : ∑ i : Fin 3, ∫ y, inner ℝ (G₀ y (unitVector i)) (t y • unitVector i) = 0 :=
      tendsto_nhds_unique hlim (tendsto_const_nhds.congr fun n => (hS0 n).symm)
    have hsq : ∫ y, t y ^ 2 = 0 := by
      rw [← hz, ← integral_finsetSum _ fun i _ => WeakFieldLimit.pair_integrable (hGc i) (hg i)]
      congr 1
      funext y
      simp only [real_inner_smul_right]
      rw [← Finset.mul_sum, sq]
    have hti2 : Integrable (fun y => t y ^ 2) volume := by
      have := (memLp_two_iff_integrable_sq_norm htm.1).1 htm
      simpa [Real.norm_eq_abs, sq_abs] using this
    have hae := (integral_eq_zero_iff_of_nonneg (fun y => by positivity) hti2).1 hsq
    filter_upwards [hae] with y hy
    simpa [ht] using hy
  · refine ⟨?_, ?_⟩
    · have h := sym_limit (turnIso m) hw₀ (fun n => by rw [turnIso_coe]; exact (hf n).symmetric.1) hwl
      rw [turnIso_coe] at h
      exact h
    · have h := sym_limit mirrorIso hw₀ (fun n => by rw [mirrorIso_coe]; exact (hf n).symmetric.2) hwl
      rw [mirrorIso_coe] at h
      exact h

end SteadyCert

end Breakdown

import Breakdown.FracCert.HeldStateLimitAApply
import Breakdown.FracCert.HeldStateLimitACross
import Breakdown.FracCert.SecondOrderComplete

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProfileLocalLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Tendsto p atTop (nhds q) → ∀ r : ℝ,
        Tendsto (fun n => ∫ y in Metric.ball (0 : Space) r, ‖d.profile (p n) y - d.profile q y‖ ^ 2) atTop
          (nhds 0)

namespace CrossTestInternal

theorem col_sub_memLp {A B : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume)
    (hAi : Integrable (fun y => entrySq (A y))) (hB : AEStronglyMeasurable B volume)
    (hBi : Integrable (fun y => entrySq (B y))) (i : Fin 3) :
    MemLp (fun y => (A y - B y) (unitVector i)) 2 volume :=
  (ActiveEnclosureInternal.col_memLp hA hAi i).sub (ActiveEnclosureInternal.col_memLp hB hBi i)

theorem entrySq_sub_integrable {A B : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume)
    (hAi : Integrable (fun y => entrySq (A y))) (hB : AEStronglyMeasurable B volume)
    (hBi : Integrable (fun y => entrySq (B y))) : Integrable (fun y => entrySq (A y - B y)) := by
  unfold entrySq
  exact integrable_finsetSum _ fun i _ =>
    (col_sub_memLp hA hAi hB hBi i).integrable_norm_pow (p := 2) (by norm_num)

theorem strong_weak {A : ℕ → Space → (Space →L[ℝ] Space)} {A₀ : Space → (Space →L[ℝ] Space)}
    (hAm : ∀ n, AEStronglyMeasurable (A n) volume) (hAi : ∀ n, Integrable (fun y => entrySq (A n y)))
    (hA₀m : AEStronglyMeasurable A₀ volume) (hA₀i : Integrable (fun y => entrySq (A₀ y)))
    (h : Tendsto (fun n => ∫ y, entrySq (A n y - A₀ y)) atTop (nhds 0))
    (E : Space → (Space →L[ℝ] Space)) (hEm : AEStronglyMeasurable E volume)
    (hEi : Integrable (fun y => entrySq (E y))) :
    Tendsto (fun n => ∫ y, entryInner (A n y) (E y)) atTop (nhds (∫ y, entryInner (A₀ y) (E y))) := by
  have hc := fun i => ActiveEnclosureInternal.col_memLp hEm hEi i
  have split : ∀ (B : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable B volume →
      Integrable (fun y => entrySq (B y)) →
      ∫ y, entryInner (B y) (E y) = ∑ i : Fin 3, ∫ y, inner ℝ (B y (unitVector i)) (E y (unitVector i)) := by
    intro B hBm hBi
    unfold entryInner
    exact integral_finsetSum _ fun i _ =>
      ActiveEnclosureInternal.pair_integrable (ActiveEnclosureInternal.col_memLp hBm hBi i) (hc i)
  have diff : ∀ n, (∫ y, entryInner (A n y) (E y)) - ∫ y, entryInner (A₀ y) (E y) =
      ∑ i : Fin 3, ∫ y, inner ℝ ((A n y - A₀ y) (unitVector i)) (E y (unitVector i)) := by
    intro n
    rw [split _ (hAm n) (hAi n), split _ hA₀m hA₀i, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_sub (ActiveEnclosureInternal.pair_integrable
      (ActiveEnclosureInternal.col_memLp (hAm n) (hAi n) i) (hc i))
      (ActiveEnclosureInternal.pair_integrable (ActiveEnclosureInternal.col_memLp hA₀m hA₀i i) (hc i))]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sub_apply, inner_sub_left]
  have hcol : ∀ (B : Space → (Space →L[ℝ] Space)) (i : Fin 3), Integrable (fun y => entrySq (B y)) →
      ∫ y, ‖B y (unitVector i)‖ ^ 2 ≤ ∫ y, entrySq (B y) := by
    intro B i hBi
    by_cases hI : Integrable (fun y => ‖B y (unitVector i)‖ ^ 2)
    · exact integral_mono hI hBi fun y => LinearStateClosedInternal.entry_le (B y) i
    · rw [integral_undef hI]
      exact integral_nonneg fun y => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) (a := fun n => 3 * (Real.sqrt (∫ y, entrySq (A n y - A₀ y)) *
    Real.sqrt (∫ y, entrySq (E y)))) ?_
  · rw [norm_norm, Real.norm_eq_abs, diff n]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hb : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
        |∫ y, inner ℝ ((A n y - A₀ y) (unitVector i)) (E y (unitVector i))| ≤
          Real.sqrt (∫ y, entrySq (A n y - A₀ y)) * Real.sqrt (∫ y, entrySq (E y)) := by
      intro i _
      refine (ApplyPairingInternal.abs_pair_le
        (col_sub_memLp (hAm n) (hAi n) hA₀m hA₀i i) (hc i)).trans ?_
      exact mul_le_mul (Real.sqrt_le_sqrt (hcol (fun y => A n y - A₀ y) i
        (entrySq_sub_integrable (hAm n) (hAi n) hA₀m hA₀i)))
        (Real.sqrt_le_sqrt (hcol E i hEi)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    refine (Finset.sum_le_sum hb).trans (le_of_eq ?_)
    simp
  · have := (h.sqrt.mul_const (Real.sqrt (∫ y, entrySq (E y)))).const_mul 3
    simpa using this

theorem local_sq {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (r : ℝ) :
    IntegrableOn (fun y => ‖v y‖ ^ 2) (Metric.ball (0 : Space) r) volume := by
  have : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Space) r)) :=
    isFiniteMeasure_restrict.2 measure_ball_lt_top.ne
  have h6 : MemLp v 6 (volume.restrict (Metric.ball (0 : Space) r)) := hs.velocity_six.restrict _
  have h2 : MemLp v 2 (volume.restrict (Metric.ball (0 : Space) r)) := h6.mono_exponent (by norm_num)
  exact h2.integrable_norm_pow (p := 2) (by norm_num)

theorem cont_sq {f : Space → Space} (hf : Continuous f) (r : ℝ) :
    IntegrableOn (fun y => ‖f y‖ ^ 2) (Metric.ball (0 : Space) r) volume :=
  ((hf.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
    Metric.ball_subset_closedBall

theorem grad_tendsto {α : ℝ} {k N : ℕ} {d : FracCertData k N} (hd : IsFracCert α d) {p : ℕ → Fin k → ℝ}
    {q : Fin k → ℝ} (hp : ∀ n, p n ∈ box d.radius) (hq : q ∈ box d.radius) (hpq : Tendsto p atTop (nhds q)) :
    Tendsto (fun n => ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hδp⟩ := hd.profile_continuous q hq ε hε
  obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hpq δ hδ
  refine ⟨M, fun n hn => ?_⟩
  have h0 : 0 ≤ ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y) :=
    integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
  exact hδp (p n) (hp n) (hM n hn)

theorem second_two_of {α : ℝ} {k N : ℕ} {d : FracCertData k N} (hd : IsFracCert α d) {p : Fin k → ℝ}
    (hp : p ∈ box d.radius) :
    Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖d.profileSecond p y (unitVector i) (unitVector j)‖ ^ 2) := by
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hm : AEStronglyMeasurable (d.profileSecond p) volume := (hd.profile_second p hp).2
  have hcont : Continuous (fun L : Space →L[ℝ] Space →L[ℝ] Space =>
      ∑ i : Fin 3, ∑ j : Fin 3, ‖L (unitVector i) (unitVector j)‖ ^ 2) := by fun_prop
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  refine (ActiveEnclosureInternal.decay_six.const_mul (9 * C ^ 2)).mono'
    (hcont.comp_aestronglyMeasurable hm) ?_
  filter_upwards [(hC p hp 0).2.2] with y hy
  have hy1 : 0 < 1 + ‖y‖ := by positivity
  have e3 : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖)⁻¹) ^ 3 := by
    rw [Real.rpow_neg hy1.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, inv_pow]
  rw [e3] at hy
  have h0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖d.profileSecond p y (unitVector i) (unitVector j)‖ ^ 2 :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  rw [Real.norm_of_nonneg h0]
  have hij : ∀ i j : Fin 3, ‖d.profileSecond p y (unitVector i) (unitVector j)‖ ^ 2 ≤
      C ^ 2 * ((1 + ‖y‖)⁻¹) ^ 6 := by
    intro i j
    have h1 : ‖d.profileSecond p y (unitVector i) (unitVector j)‖ ≤ ‖d.profileSecond p y‖ := by
      calc ‖d.profileSecond p y (unitVector i) (unitVector j)‖
          ≤ ‖d.profileSecond p y (unitVector i)‖ * ‖unitVector j‖ := (d.profileSecond p y (unitVector i)).le_opNorm _
        _ ≤ ‖d.profileSecond p y‖ * ‖unitVector i‖ * ‖unitVector j‖ :=
            mul_le_mul_of_nonneg_right ((d.profileSecond p y).le_opNorm _) (norm_nonneg _)
        _ = ‖d.profileSecond p y‖ := by rw [hu, hu, mul_one, mul_one]
    have h2 := (h1.trans hy)
    have h3 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc _ ≤ (C * ((1 + ‖y‖)⁻¹) ^ 3) ^ 2 := h3
      _ = C ^ 2 * ((1 + ‖y‖)⁻¹) ^ 6 := by ring
  simp only [Fin.sum_univ_three]
  linarith [hij 0 0, hij 0 1, hij 0 2, hij 1 0, hij 1 1, hij 1 2, hij 2 0, hij 2 1, hij 2 2]

theorem profile_second_order {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} {d : FracCertData k N}
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) :
    IsSecondOrderField d.order (d.profile p) (d.gradProfile p) (d.profileSecond p) := by
  obtain ⟨m1, m6, mG, iG, wG, dG⟩ := profileEmbedData α hα1 hα2 d hd p hp
  exact ⟨m1, mG, (hd.profile_second p hp).2, m6, iG, second_two_of hd hp, wG, (hd.profile_second p hp).1, dG,
    hd.profile_class p hp⟩

end CrossTestInternal

open CrossTestInternal in
theorem profileLocalLimit : ProfileLocalLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq r
  have hdn := grad_tendsto hd hp hq hpq
  have hq2 := profile_second_order hα1 hα2 hd hq
  have bound : ∀ n, ∫ y in Metric.ball (0 : Space) r, ‖d.profile (p n) y - d.profile q y‖ ^ 2 ≤
      r ^ 2 * (4 * ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) := by
    intro n
    have hs := secondOrderLinear d.order _ _ _ _ _ _ (-1) (profile_second_order hα1 hα2 hd (hp n)) hq2
    obtain ⟨hI, hIb⟩ := inverseSquareBound _ _ hs.measurable_velocity hs.velocity_six hs.gradient_two
      hs.weak_gradient
    simp only [neg_one_smul, ← sub_eq_add_neg] at hI hIb
    have hfc : Continuous (fun y => d.profile (p n) y - d.profile q y) :=
      (hd.profile_smooth _ (hp n)).continuous.sub (hd.profile_smooth q hq).continuous
    have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
      have : (volume : Measure Space) {0} = 0 := measure_singleton 0
      filter_upwards [compl_mem_ae_iff.2 this] with y hy
      simpa using hy
    calc ∫ y in Metric.ball (0 : Space) r, ‖d.profile (p n) y - d.profile q y‖ ^ 2
        ≤ ∫ y in Metric.ball (0 : Space) r, r ^ 2 * (‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2) := by
          refine setIntegral_mono_ae_restrict (cont_sq hfc r) (hI.const_mul _).integrableOn ?_
          rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_ball]
          filter_upwards [hne] with y hy hyb
          have hy0 : 0 < ‖y‖ := norm_pos_iff.2 hy
          have hyr : ‖y‖ < r := by simpa using hyb
          have hsq : ‖y‖ ^ 2 ≤ r ^ 2 := by nlinarith
          rw [mul_div_assoc', le_div_iff₀ (by positivity)]
          exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _) |>.trans_eq (by ring)
      _ ≤ ∫ y, r ^ 2 * (‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2) :=
          setIntegral_le_integral (hI.const_mul _) (Eventually.of_forall fun y => by positivity)
      _ = r ^ 2 * ∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2 := integral_const_mul _ _
      _ ≤ r ^ 2 * (4 * ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) :=
          mul_le_mul_of_nonneg_left hIb (sq_nonneg _)
  refine squeeze_zero (fun n => setIntegral_nonneg measurableSet_ball fun y _ => sq_nonneg _) bound ?_
  simpa using (hdn.const_mul 4).const_mul (r ^ 2)

open CrossTestInternal in
theorem crossTestLimit_of (hprof : ProfileLocalLimitStatement) : CrossTestLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H u₀ G₀ H₀ B hs hs₀ hE hGw hloc ψ hψ
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  have hw0 : 0 ≤ d.weightMin⁻¹ := inv_nonneg.2 hd.weightMin_pos.le
  have hGK : ∀ n, ∫ y, entrySq (G n y) ≤ d.weightMin⁻¹ * B := fun n =>
    (LinearStateClosedInternal.entry_le_energy hd.weightMin_pos hd.weight_measurable hd.weight_lower
      hd.weight_upper (hs n).gradient_two (L := H n)).trans (mul_le_mul_of_nonneg_left (hE n) hw0)
  have hψ2 : MemLp ψ 2 volume := hψ.1.continuous.memLp_of_hasCompactSupport hψ.2
  have hWc : ∀ p' ∈ box d.radius, Continuous (d.profile p') := fun p' hp' => (hd.profile_smooth p' hp').continuous
  have hDc : ∀ p' ∈ box d.radius, Continuous (d.gradProfile p') := fun p' hp' =>
    (hd.profile_smooth p' hp').continuous_fderiv one_ne_zero
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  have h1 := ApplyPairingInternal.apply_pairing_limit (A := G) (A₀ := G₀) (a := u) (a₀ := u₀)
    (fun n => (hs n).measurable_gradient) (fun n => (hs n).gradient_two) hGK hGw
    (fun n => (hs n).measurable_velocity) hs₀.measurable_velocity (fun n r => local_sq (hs n) r)
    (local_sq hs₀) hloc hψ
  have h2 := ApplyPairingInternal.apply_pairing_limit (A := G) (A₀ := G₀)
    (a := fun n => d.profile (p n)) (a₀ := d.profile q)
    (fun n => (hs n).measurable_gradient) (fun n => (hs n).gradient_two) hGK hGw
    (fun n => (hWc _ (hp n)).aestronglyMeasurable) (hWc q hq).aestronglyMeasurable
    (fun n r => cont_sq (hWc _ (hp n)) r) (cont_sq (hWc q hq))
    (hprof α hα1 hα2 d hd p q hp hq hpq) hψ
  have hDm := fun p' (hp' : p' ∈ box d.radius) => (hemb p' hp').2.2.1
  have hDi := fun p' (hp' : p' ∈ box d.radius) => (hemb p' hp').2.2.2.1
  have hdn : Tendsto (fun n => ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := hd.profile_continuous q hq ε hε
    obtain ⟨M, hM⟩ := Metric.tendsto_atTop.1 hpq δ hδ
    refine ⟨M, fun n hn => ?_⟩
    have h0 : 0 ≤ ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y) :=
      integral_nonneg fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h0]
    exact hδp (p n) (hp n) (hM n hn)
  obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.1 (Metric.isBounded_range_of_tendsto _ hdn)
  have hDK : ∀ n, ∫ y, entrySq (d.gradProfile (p n) y) ≤
      2 * D + 2 * ∫ y, entrySq (d.gradProfile q y) := by
    intro n
    have hsub := entrySq_sub_integrable (hDm _ (hp n)) (hDi _ (hp n)) (hDm q hq) (hDi q hq)
    have hDn : ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y) ≤ D := by
      have := hD _ ⟨n, rfl⟩
      exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using this)
    calc ∫ y, entrySq (d.gradProfile (p n) y) ≤
        ∫ y, (2 * entrySq (d.gradProfile (p n) y - d.gradProfile q y) + 2 * entrySq (d.gradProfile q y)) := by
          refine integral_mono (hDi _ (hp n)) ((hsub.const_mul 2).add ((hDi q hq).const_mul 2)) fun y => ?_
          simp only [entrySq, sub_apply]
          have hh : ∀ a b : Space, ‖a‖ ^ 2 ≤ 2 * ‖a - b‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
            intro a b
            have := norm_le_insert' a b
            have h3 : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
              calc ‖a‖ = ‖(a - b) + b‖ := by rw [sub_add_cancel]
                _ ≤ ‖a - b‖ + ‖b‖ := norm_add_le _ _
            have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
            nlinarith [sq_nonneg (‖a - b‖ - ‖b‖)]
          simp only [Fin.sum_univ_three]
          linarith [hh (d.gradProfile (p n) y (unitVector 0)) (d.gradProfile q y (unitVector 0)),
            hh (d.gradProfile (p n) y (unitVector 1)) (d.gradProfile q y (unitVector 1)),
            hh (d.gradProfile (p n) y (unitVector 2)) (d.gradProfile q y (unitVector 2))]
      _ = 2 * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) + 2 * ∫ y, entrySq (d.gradProfile q y) := by
          rw [integral_add (hsub.const_mul 2) ((hDi q hq).const_mul 2), integral_const_mul, integral_const_mul]
      _ ≤ _ := by linarith
  have h3 := ApplyPairingInternal.apply_pairing_limit (A := fun n => d.gradProfile (p n))
    (A₀ := d.gradProfile q) (a := u) (a₀ := u₀)
    (fun n => hDm _ (hp n)) (fun n => hDi _ (hp n)) hDK
    (strong_weak (fun n => hDm _ (hp n)) (fun n => hDi _ (hp n)) (hDm q hq) (hDi q hq) hdn)
    (fun n => (hs n).measurable_velocity) hs₀.measurable_velocity (fun n r => local_sq (hs n) r)
    (local_sq hs₀) hloc hψ
  have hu6 : ∀ {v : Space → Space} {K : Space → (Space →L[ℝ] Space)} {L : Space → (Space →L[ℝ] Space →L[ℝ] Space)},
      IsSecondOrderField d.order v K L → Integrable (fun y => ‖v y‖ ^ 6) volume :=
    fun h => h.velocity_six.integrable_norm_pow (p := 6) (by norm_num)
  have split : ∀ p' ∈ box d.radius, ∀ (v : Space → Space) (K : Space → (Space →L[ℝ] Space))
      (L : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField d.order v K L →
      ∫ y, inner ℝ (d.gradProfile p' y (v y) + K y (d.profile p' y) + K y (v y)) (ψ y) =
        (∫ y, inner ℝ (d.gradProfile p' y (v y)) (ψ y)) + (∫ y, inner ℝ (K y (d.profile p' y)) (ψ y))
          + ∫ y, inner ℝ (K y (v y)) (ψ y) := by
    intro p' hp' v K L hv
    have ma := ActiveEnclosureInternal.decay_apply_memLp (hDc p' hp') (fun y => (hC p' hp' y).2)
      hv.measurable_velocity (hu6 hv)
    have mb := ActiveEnclosureInternal.bounded_apply_memLp hv.measurable_gradient hv.gradient_two (hWc p' hp')
      (ActiveEnclosureInternal.profile_le (fun y => (hC p' hp' y).1))
    have mc := quadraticSquareIntegrable d.order v K L hv
    have ia := ActiveEnclosureInternal.pair_integrable ma hψ2
    have ib := ActiveEnclosureInternal.pair_integrable mb hψ2
    have ic := ActiveEnclosureInternal.pair_integrable mc hψ2
    have iab : Integrable (fun y => inner ℝ (d.gradProfile p' y (v y)) (ψ y)
        + inner ℝ (K y (d.profile p' y)) (ψ y)) volume := ia.add ib
    rw [← integral_add ia ib, ← integral_add iab ic]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [inner_add_left]
  rw [split q hq u₀ G₀ H₀ hs₀]
  exact ((h3.add h2).add h1).congr (fun n => (split (p n) (hp n) (u n) (G n) (H n) (hs n)).symm)

end SteadyCert

end Breakdown

import Breakdown.Transfer.StatementsLocal

open MeasureTheory Set Real Filter Topology

noncomputable section

namespace Breakdown

namespace VarConstIntegralInternal

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (H : HeatBilinear X)

theorem ck_nonneg : 0 ≤ H.CK := by
  have h := H.K_bound 1 one_pos le_rfl
  rw [Real.one_rpow, mul_one] at h
  exact (norm_nonneg _).trans h

theorem norm_K_le_one {τ : ℝ} (hτ : 1 ≤ τ) : ‖H.K τ‖ ≤ ‖H.K 1‖ := by
  refine ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg _) fun x y => ?_
  have hs := H.K_shift (τ - 1) 1 (by linarith) one_pos x y
  rw [sub_add_cancel] at hs
  rw [← hs]
  calc ‖H.G (τ - 1) (H.K 1 x y)‖ ≤ ‖H.G (τ - 1)‖ * ‖H.K 1 x y‖ := (H.G (τ - 1)).le_opNorm _
    _ ≤ 1 * (‖H.K 1‖ * ‖x‖ * ‖y‖) :=
        mul_le_mul (H.G_norm _ (by linarith)) ((H.K 1).le_opNorm₂ x y) (norm_nonneg _) zero_le_one
    _ = ‖H.K 1‖ * ‖x‖ * ‖y‖ := one_mul _

theorem norm_K_le {τ : ℝ} (hτ : 0 < τ) : ‖H.K τ‖ ≤ H.CK * (τ ^ (-(3 / 4 : ℝ)) + 1) := by
  have hck := ck_nonneg H
  have hp : 0 ≤ τ ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hτ.le _
  rcases le_or_gt τ 1 with h1 | h1
  · calc ‖H.K τ‖ ≤ H.CK * τ ^ (-(3 / 4 : ℝ)) := H.K_bound τ hτ h1
      _ ≤ _ := by nlinarith
  · have h := H.K_bound 1 one_pos le_rfl
    rw [Real.one_rpow, mul_one] at h
    calc ‖H.K τ‖ ≤ ‖H.K 1‖ := norm_K_le_one H h1.le
      _ ≤ H.CK := h
      _ ≤ _ := by nlinarith

theorem tendsto_K {α : Type*} {l : Filter α} {τ : α → ℝ} {w z : α → X} {τ₀ : ℝ} {x₀ y₀ : X}
    (h₀ : 0 < τ₀) (hτ : Tendsto τ l (𝓝 τ₀)) (hw : Tendsto w l (𝓝 x₀))
    (hz : Tendsto z l (𝓝 y₀)) :
    Tendsto (fun x => H.K (τ x) (w x) (z x)) l (𝓝 (H.K τ₀ x₀ y₀)) := by
  have h1 : Tendsto (fun x => H.K (τ x) x₀ y₀) l (𝓝 (H.K τ₀ x₀ y₀)) :=
    ((H.K_cont x₀ y₀).continuousAt (Ioi_mem_nhds h₀)).tendsto.comp hτ
  obtain ⟨C, hC⟩ : ∃ C : ℝ, ∀ s, τ₀ / 2 < s → ‖H.K s‖ ≤ C := by
    refine ⟨H.CK * ((τ₀ / 2) ^ (-(3 / 4 : ℝ)) + 1), fun s hs => ?_⟩
    have hs0 : 0 < s := by linarith
    refine (norm_K_le H hs0).trans (mul_le_mul_of_nonneg_left ?_ (ck_nonneg H))
    have := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < τ₀ / 2) hs.le
      (by norm_num : (-(3 / 4 : ℝ)) ≤ 0)
    linarith
  have hev : ∀ᶠ x in l, τ₀ / 2 < τ x := hτ.eventually (lt_mem_nhds (by linarith))
  have hbd : ∀ᶠ x in l, ‖H.K (τ x) (w x) (z x) - H.K (τ x) x₀ y₀‖ ≤
      C * (‖w x - x₀‖ * ‖z x‖ + ‖x₀‖ * ‖z x - y₀‖) := by
    filter_upwards [hev] with x hx
    have hK := hC _ hx
    have heq : H.K (τ x) (w x) (z x) - H.K (τ x) x₀ y₀ =
        H.K (τ x) (w x - x₀) (z x) + H.K (τ x) x₀ (z x - y₀) := by
      simp only [map_sub, _root_.sub_apply]
      abel
    rw [heq]
    calc _ ≤ ‖H.K (τ x) (w x - x₀) (z x)‖ + ‖H.K (τ x) x₀ (z x - y₀)‖ := norm_add_le _ _
      _ ≤ ‖H.K (τ x)‖ * ‖w x - x₀‖ * ‖z x‖ + ‖H.K (τ x)‖ * ‖x₀‖ * ‖z x - y₀‖ :=
          add_le_add ((H.K (τ x)).le_opNorm₂ _ _) ((H.K (τ x)).le_opNorm₂ _ _)
      _ ≤ C * ‖w x - x₀‖ * ‖z x‖ + C * ‖x₀‖ * ‖z x - y₀‖ := by gcongr
      _ = _ := by ring
  have hlim : Tendsto (fun x => C * (‖w x - x₀‖ * ‖z x‖ + ‖x₀‖ * ‖z x - y₀‖)) l (𝓝 0) := by
    have hw' : Tendsto (fun x => ‖w x - x₀‖) l (𝓝 0) := by
      simpa using (hw.sub_const x₀).norm
    have hz' : Tendsto (fun x => ‖z x - y₀‖) l (𝓝 0) := by
      simpa using (hz.sub_const y₀).norm
    simpa using ((hw'.mul hz.norm).add (hz'.const_mul ‖x₀‖)).const_mul C
  simpa using (squeeze_zero_norm' hbd hlim).add h1

theorem continuousOn_K {α : Type*} [TopologicalSpace α] {S : Set α} {τ : α → ℝ} {w z : α → X}
    (hτ : ContinuousOn τ S) (hpos : ∀ x ∈ S, 0 < τ x) (hw : ContinuousOn w S)
    (hz : ContinuousOn z S) : ContinuousOn (fun x => H.K (τ x) (w x) (z x)) S :=
  fun x hx => tendsto_K H (hpos x hx) (hτ x hx) (hw x hx) (hz x hx)

theorem clamp_mem {a b : ℝ} (hab : a ≤ b) (s : ℝ) : max a (min b s) ∈ Icc a b :=
  ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩

theorem clamp_eq {a b s : ℝ} (hs : s ∈ Icc a b) : max a (min b s) = s := by
  rw [min_eq_right hs.2, max_eq_right hs.1]

theorem continuous_clamp {a b : ℝ} (hab : a ≤ b) {u : ℝ → X} (hu : ContinuousOn u (Icc a b)) :
    Continuous (fun s => u (max a (min b s))) :=
  hu.comp_continuous (continuous_const.max (continuous_const.min continuous_id)) (clamp_mem hab)

def kern (a b : ℝ) (u v : ℝ → X) (t r : ℝ) : X :=
  H.K r (u (max a (min b (t - r)))) (v (max a (min b (t - r))))

theorem kern_continuousOn {a b : ℝ} (hab : a ≤ b) {u v : ℝ → X} (hu : ContinuousOn u (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (t : ℝ) : ContinuousOn (kern H a b u v t) (Ioi 0) := by
  have hw := (continuous_clamp hab hu).comp (continuous_const.sub continuous_id : Continuous (fun r : ℝ => t - r))
  have hz := (continuous_clamp hab hv).comp (continuous_const.sub continuous_id : Continuous (fun r : ℝ => t - r))
  exact continuousOn_K H continuousOn_id (fun r hr => hr) hw.continuousOn hz.continuousOn

theorem kern_continuous_left {a b : ℝ} (hab : a ≤ b) {u v : ℝ → X} (hu : ContinuousOn u (Icc a b))
    (hv : ContinuousOn v (Icc a b)) (r : ℝ) : Continuous (fun t => kern H a b u v t r) := by
  have hw := (continuous_clamp hab hu).comp (continuous_id.sub continuous_const : Continuous (fun t : ℝ => t - r))
  have hz := (continuous_clamp hab hv).comp (continuous_id.sub continuous_const : Continuous (fun t : ℝ => t - r))
  exact (continuous_const.clm_apply hw).clm_apply hz

theorem norm_kern_le {a b M N : ℝ} (hab : a ≤ b) {u v : ℝ → X} (huM : ∀ s ∈ Icc a b, ‖u s‖ ≤ M)
    (hvN : ∀ s ∈ Icc a b, ‖v s‖ ≤ N) (t r : ℝ) (hr : 0 < r) :
    ‖kern H a b u v t r‖ ≤ H.CK * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (huM a ⟨le_rfl, hab⟩)
  have hc : 0 ≤ H.CK * (r ^ (-(3 / 4 : ℝ)) + 1) :=
    mul_nonneg (ck_nonneg H) (add_nonneg (Real.rpow_nonneg hr.le _) zero_le_one)
  unfold kern
  calc _ ≤ ‖H.K r‖ * ‖u (max a (min b (t - r)))‖ * ‖v (max a (min b (t - r)))‖ :=
        (H.K r).le_opNorm₂ _ _
    _ ≤ _ := mul_le_mul (mul_le_mul (norm_K_le H hr) (huM _ (clamp_mem hab _)) (norm_nonneg _) hc)
        (hvN _ (clamp_mem hab _)) (norm_nonneg _) (mul_nonneg hc hM)

theorem norm_kern_le_small {a b M N : ℝ} (hab : a ≤ b) {u v : ℝ → X}
    (huM : ∀ s ∈ Icc a b, ‖u s‖ ≤ M) (hvN : ∀ s ∈ Icc a b, ‖v s‖ ≤ N) (t r : ℝ) (hr : 0 < r)
    (hr1 : r ≤ 1) : ‖kern H a b u v t r‖ ≤ H.CK * M * N * r ^ (-(3 / 4 : ℝ)) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (huM a ⟨le_rfl, hab⟩)
  have hc : 0 ≤ H.CK * r ^ (-(3 / 4 : ℝ)) := mul_nonneg (ck_nonneg H) (Real.rpow_nonneg hr.le _)
  unfold kern
  calc _ ≤ ‖H.K r‖ * ‖u (max a (min b (t - r)))‖ * ‖v (max a (min b (t - r)))‖ :=
        (H.K r).le_opNorm₂ _ _
    _ ≤ H.CK * r ^ (-(3 / 4 : ℝ)) * M * N :=
        mul_le_mul (mul_le_mul (H.K_bound r hr hr1) (huM _ (clamp_mem hab _)) (norm_nonneg _) hc)
          (hvN _ (clamp_mem hab _)) (norm_nonneg _) (mul_nonneg hc hM)
    _ = _ := by ring

theorem bound_integrableOn (C M N : ℝ) {c : ℝ} (hc : 0 ≤ c) :
    IntegrableOn (fun r : ℝ => C * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N) (Ioc 0 c) := by
  have h := (((intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := c) (by norm_num : (-1 : ℝ) < -(3 / 4))).add
    (intervalIntegrable_const (c := (1 : ℝ)))).const_mul C).mul_const M |>.mul_const N
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hc).1 h

theorem kern_intervalIntegrable {a b M N : ℝ} (hab : a ≤ b) {u v : ℝ → X}
    (hu : ContinuousOn u (Icc a b)) (hv : ContinuousOn v (Icc a b))
    (huM : ∀ s ∈ Icc a b, ‖u s‖ ≤ M) (hvN : ∀ s ∈ Icc a b, ‖v s‖ ≤ N) (t : ℝ) {c : ℝ}
    (hc : 0 ≤ c) : IntervalIntegrable (kern H a b u v t) volume 0 c := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc]
  refine Integrable.mono' (bound_integrableOn H.CK M N hc)
    (((kern_continuousOn H hab hu hv t).mono Ioc_subset_Ioi_self).aestronglyMeasurable
      measurableSet_Ioc) ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun r hr => norm_kern_le H hab huM hvN t r hr.1

theorem integral_eq_kern {a b : ℝ} {u v : ℝ → X} {t : ℝ} (ht : t ∈ Icc a b) :
    ∫ s in a..t, H.K (t - s) (u s) (v s) = ∫ r in (0 : ℝ)..(t - a), kern H a b u v t r := by
  calc ∫ s in a..t, H.K (t - s) (u s) (v s) = ∫ s in a..t, kern H a b u v t (t - s) := by
        refine intervalIntegral.integral_congr fun s hs => ?_
        rw [uIcc_of_le ht.1] at hs
        have hsab : s ∈ Icc a b := ⟨hs.1, hs.2.trans ht.2⟩
        simp only [kern, sub_sub_cancel, clamp_eq hsab]
    _ = ∫ r in t - t..t - a, kern H a b u v t r :=
        intervalIntegral.integral_comp_sub_left (kern H a b u v t) t
    _ = _ := by rw [sub_self]

theorem integral_rpow_three_quarters {c : ℝ} :
    ∫ r in (0 : ℝ)..c, r ^ (-(3 / 4 : ℝ)) = 4 * c ^ (1 / 4 : ℝ) := by
  rw [integral_rpow (Or.inl (by norm_num))]
  have e : (-(3 / 4 : ℝ)) + 1 = 1 / 4 := by norm_num
  rw [e, Real.zero_rpow (by norm_num)]
  ring

end VarConstIntegralInternal

open VarConstIntegralInternal in
theorem varConstIntegral : VarConstIntegralStatement := by
  intro X _ _ _ H u v a b M N hab hu hv huM hvN
  refine ⟨fun t ht => ?_, fun t ht h1 => ?_, ?_⟩
  · have h2 := (kern_intervalIntegrable H hab hu hv huM hvN t (sub_nonneg.2 ht.1)).comp_sub_left t
    rw [sub_zero, sub_sub_cancel] at h2
    refine h2.symm.congr_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    rw [uIoc_of_le ht.1] at hs
    have hsab : s ∈ Icc a b := ⟨hs.1.le, hs.2.trans ht.2⟩
    simp only [kern, sub_sub_cancel, clamp_eq hsab]
  · rw [integral_eq_kern H ht]
    have hc : 0 ≤ t - a := sub_nonneg.2 ht.1
    calc ‖∫ r in (0 : ℝ)..(t - a), kern H a b u v t r‖
        ≤ ∫ r in (0 : ℝ)..(t - a), H.CK * M * N * r ^ (-(3 / 4 : ℝ)) :=
          intervalIntegral.norm_integral_le_of_norm_le hc
            (Eventually.of_forall fun r hr =>
              norm_kern_le_small H hab huM hvN t r hr.1 (hr.2.trans h1))
            ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul _)
      _ = H.CK * M * N * (4 * (t - a) ^ (1 / 4 : ℝ)) := by
          rw [intervalIntegral.integral_const_mul, integral_rpow_three_quarters]
      _ = _ := by ring
  · have hrep : ∀ t ∈ Icc a b, ∫ s in a..t, H.K (t - s) (u s) (v s) =
        ∫ r in Ioc 0 (b - a), (Iic (t - a)).indicator (kern H a b u v t) r := by
      intro t ht
      rw [integral_eq_kern H ht, intervalIntegral.integral_of_le (sub_nonneg.2 ht.1),
        setIntegral_indicator measurableSet_Iic]
      have e : Ioc 0 (b - a) ∩ Iic (t - a) = Ioc 0 (t - a) := by
        ext r
        simp only [mem_Ioc, mem_inter_iff, mem_Iic]
        constructor
        · rintro ⟨⟨h1, _⟩, h3⟩
          exact ⟨h1, h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨⟨h1, by linarith [ht.2]⟩, h2⟩
      rw [e]
    have hcont : Continuous (fun t =>
        ∫ r in Ioc 0 (b - a), (Iic (t - a)).indicator (kern H a b u v t) r) := by
      rw [continuous_iff_continuousAt]
      intro t₀
      refine tendsto_integral_filter_of_dominated_convergence
        (fun r => H.CK * (r ^ (-(3 / 4 : ℝ)) + 1) * M * N) ?_ ?_
        (bound_integrableOn H.CK M N (sub_nonneg.2 hab)) ?_
      · exact Eventually.of_forall fun t =>
          (((kern_continuousOn H hab hu hv t).mono Ioc_subset_Ioi_self).aestronglyMeasurable
            measurableSet_Ioc).indicator measurableSet_Iic
      · exact Eventually.of_forall fun t => (ae_restrict_mem measurableSet_Ioc).mono fun r hr =>
          (norm_indicator_le_norm_self _ _).trans (norm_kern_le H hab huM hvN t r hr.1)
      · have hne : ∀ᵐ r ∂(volume.restrict (Ioc 0 (b - a))), r ≠ t₀ - a := by
          refine ae_restrict_of_ae ?_
          rw [ae_iff]
          simp
        filter_upwards [hne] with r hne
        have hk := (kern_continuous_left H hab hu hv r).tendsto t₀
        have hsub : Tendsto (fun t : ℝ => t - a) (𝓝 t₀) (𝓝 (t₀ - a)) :=
          (continuous_id.sub continuous_const).tendsto t₀
        rcases lt_or_gt_of_ne hne with h | h
        · rw [indicator_of_mem (mem_Iic.2 h.le)]
          refine hk.congr' ?_
          filter_upwards [hsub.eventually (lt_mem_nhds h)] with t ht
          exact (indicator_of_mem (mem_Iic.2 ht.le) _).symm
        · rw [indicator_of_notMem (by simpa using h)]
          refine tendsto_const_nhds.congr' ?_
          filter_upwards [hsub.eventually (gt_mem_nhds h)] with t ht
          exact (indicator_of_notMem (by simpa using ht) _).symm
    exact hcont.continuousOn.congr hrep

end Breakdown

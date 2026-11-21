import Breakdown.Cert.Nodes

open scoped ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

namespace Internal.TranslationCriterion

def boxSet (R : ℝ) : Set (ℝ × Space) := Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R

def boxMeasure (R : ℝ) : Measure (ℝ × Space) := (volume : Measure (ℝ × Space)).restrict (boxSet R)

theorem isCompact_boxSet (R : ℝ) : IsCompact (boxSet R) :=
  isCompact_Icc.prod (isCompact_closedBall _ _)

theorem measurableSet_boxSet (R : ℝ) : MeasurableSet (boxSet R) :=
  measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet

instance (R : ℝ) : IsFiniteMeasure (boxMeasure R) :=
  isFiniteMeasure_restrict.2 (isCompact_boxSet R).measure_lt_top.ne

theorem periodBallLIntegral_eq (R : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    periodBallLIntegral R (fun σ y => ‖f σ y‖ ^ 2) =
      eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R) ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  have hm : AEMeasurable (fun z : ℝ × Space => ‖f z.1 z.2‖ₑ ^ (2 : ℕ))
      (((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod
        ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) R))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.restrict.enorm).pow_const 2
  unfold periodBallLIntegral boxMeasure boxSet
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm]
  refine lintegral_congr fun σ => lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem periodBallNorm_eq (R : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    periodBallNorm R f = (eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R)).toReal := by
  unfold periodBallNorm
  rw [periodBallLIntegral_eq R f hf, ENNReal.toReal_pow, Real.sqrt_sq ENNReal.toReal_nonneg]

theorem periodBallLIntegral_mono {R R' : ℝ} (h : R ≤ R') (f : ℝ → Space → ℝ) :
    periodBallLIntegral R f ≤ periodBallLIntegral R' f :=
  lintegral_mono fun _ => lintegral_mono_set (Metric.closedBall_subset_closedBall h)

theorem exists_finset_net {X : Type*} [PseudoMetricSpace X] (v : ℕ → X)
    (h : TotallyBounded (range v)) {η : ℝ} (hη : 0 < η) :
    ∃ I : Finset ℕ, ∀ n, ∃ i ∈ I, dist (v n) (v i) < η := by
  classical
  obtain ⟨t, hts, htf, hcov⟩ := totallyBounded_iff_subset.1 h _ (Metric.dist_mem_uniformity hη)
  let idx : X → ℕ := fun y => if hy : y ∈ range v then hy.choose else 0
  refine ⟨htf.toFinset.image idx, fun n => ?_⟩
  obtain ⟨y, hy, hny⟩ := mem_iUnion₂.1 (hcov (mem_range_self n))
  have hyr := hts hy
  refine ⟨idx y, Finset.mem_image_of_mem _ (htf.mem_toFinset.2 hy), ?_⟩
  have hidx : v (idx y) = y := by
    simp only [idx, dif_pos hyr]
    exact hyr.choose_spec
  rw [hidx]
  exact hny

theorem exists_uniform_net (R : ℝ) (g : ℕ → ℝ × Space → Space) (M : ℝ) (hM : ∀ n z, ‖g n z‖ ≤ M)
    (hmod : ∀ η > 0, ∃ δ > 0, ∀ n z z', dist z z' < δ → dist (g n z) (g n z') < η)
    {η : ℝ} (hη : 0 < η) :
    ∃ I : Finset ℕ, ∀ n, ∃ i ∈ I, ∀ z ∈ boxSet R, dist (g n z) (g i z) < η := by
  classical
  obtain ⟨δ, hδ, hgδ⟩ := hmod (η / 3) (by positivity)
  obtain ⟨T, hTK, hTf, hcov⟩ := finite_cover_balls_of_compact (isCompact_boxSet R) hδ
  let P := hTf.toFinset
  let v : ℕ → (P → Space) := fun n p => g n p.1
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 0)
  have hv : range v ⊆ Metric.closedBall (0 : P → Space) M := by
    rintro _ ⟨n, rfl⟩
    rw [mem_closedBall_zero_iff]
    exact (pi_norm_le_iff_of_nonneg hM0).2 fun p => hM n p.1
  have htb : TotallyBounded (range v) := (isCompact_closedBall _ _).totallyBounded.subset hv
  obtain ⟨I, hI⟩ := exists_finset_net v htb (η := η / 3) (by positivity)
  refine ⟨I, fun n => ?_⟩
  obtain ⟨i, hi, hni⟩ := hI n
  refine ⟨i, hi, fun z hz => ?_⟩
  obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.1 (hcov hz)
  have hpP : p ∈ P := hTf.mem_toFinset.2 hp
  have h1 : dist (g n z) (g n p) < η / 3 := hgδ n z p (Metric.mem_ball.1 hzp)
  have h2 : dist (g n p) (g i p) < η / 3 :=
    lt_of_le_of_lt (dist_le_pi_dist (v n) (v i) ⟨p, hpP⟩) hni
  have h3 : dist (g i p) (g i z) < η / 3 := by
    rw [dist_comm]
    exact hgδ i z p (Metric.mem_ball.1 hzp)
  calc dist (g n z) (g i z) ≤ dist (g n z) (g n p) + dist (g n p) (g i p) + dist (g i p) (g i z) :=
        dist_triangle4 _ _ _ _
    _ < η / 3 + η / 3 + η / 3 := by gcongr
    _ = η := by ring

theorem lintegral_Icc_add (Φ : ℝ → ℝ≥0∞) (hΦ : ∀ σ, Φ (σ + 1) = Φ σ) (c : ℝ) :
    ∫⁻ σ in Icc (0 : ℝ) 1, Φ (σ + c) = ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by
  have hp : Function.Periodic Φ 1 := hΦ
  have hq : Function.Periodic (fun σ => Φ (σ + c)) 1 := fun σ => by
    simp only [add_right_comm σ 1 c]
    exact hΦ (σ + c)
  have e1 := AddCircle.lintegral_preimage (T := 1) 0 hq.lift
  have e0 := AddCircle.lintegral_preimage (T := 1) 0 hp.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e0
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc, e1, e0]
  have hl : hq.lift = fun t => hp.lift (t + (c : AddCircle (1 : ℝ))) := by
    funext t
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective t
    change hq.lift (x : AddCircle (1 : ℝ)) = hp.lift ((x : AddCircle (1 : ℝ)) + (c : AddCircle (1 : ℝ)))
    rw [← AddCircle.coe_add, Function.Periodic.lift_coe, Function.Periodic.lift_coe]
  rw [hl]
  exact lintegral_add_right_eq_self _ _

theorem lintegral_Icc_shift (Φ : ℝ → ℝ≥0∞) (hΦ : ∀ σ, Φ (σ + 1) = Φ σ) (a : ℝ) :
    ∫⁻ σ in Icc a (a + 1), Φ σ = ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by
  have hp : Function.Periodic Φ 1 := hΦ
  have e1 := AddCircle.lintegral_preimage (T := 1) a hp.lift
  have e0 := AddCircle.lintegral_preimage (T := 1) 0 hp.lift
  simp only [Function.Periodic.lift_coe, zero_add] at e1 e0
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc, ← Measure.restrict_congr_set Ioc_ae_eq_Icc, e1, e0]

theorem periodBallLIntegral_shift (R : ℝ) (f : ℝ → Space → ℝ) (hf : ∀ σ y, f (σ + 1) y = f σ y)
    (c : ℝ) : periodBallLIntegral R (fun σ y => f (σ + c) y) = periodBallLIntegral R f := by
  unfold periodBallLIntegral
  exact lintegral_Icc_add (fun σ => ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (f σ y))
    (fun σ => by simp only [hf]) c

theorem aestronglyMeasurable_comp_map (F : ℝ → Space → Space)
    (hmeas : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (p : ℝ → ℝ) (q : Space → Space)
    (hp : MeasurePreserving p volume volume) (hq : MeasurePreserving q volume volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => F (p z.1) (q z.2)) volume :=
  hmeas.comp_measurePreserving (hp.prod hq)

theorem eLpNorm_lt_top_of_bound (R : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (C : ℝ)
    (hb : periodBallLIntegral R (fun σ y => ‖f σ y‖ ^ 2) ≤ ENNReal.ofReal C) :
    eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R) < ⊤ := by
  have h : eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R) ^ 2 < ⊤ :=
    ((periodBallLIntegral_eq R f hf).symm.trans_le hb).trans_lt ENNReal.ofReal_lt_top
  simpa using h

theorem periodBallLIntegral_sub_lt_top (R : ℝ) (f g : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hg : AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume) (C₁ C₂ : ℝ)
    (hfb : periodBallLIntegral R (fun σ y => ‖f σ y‖ ^ 2) ≤ ENNReal.ofReal C₁)
    (hgb : periodBallLIntegral R (fun σ y => ‖g σ y‖ ^ 2) ≤ ENNReal.ofReal C₂) :
    periodBallLIntegral R (fun σ y => ‖f σ y - g σ y‖ ^ 2) < ⊤ := by
  rw [periodBallLIntegral_eq R (fun σ y => f σ y - g σ y) (hf.sub hg)]
  refine ENNReal.pow_lt_top ?_
  exact (eLpNorm_sub_le hf.restrict hg.restrict (by norm_num)).trans_lt
    (ENNReal.add_lt_top.2 ⟨eLpNorm_lt_top_of_bound R f hf C₁ hfb, eLpNorm_lt_top_of_bound R g hg C₂ hgb⟩)

theorem eLpNorm_le_of_periodBallNorm_le (R : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hfin : periodBallLIntegral R (fun σ y => ‖f σ y‖ ^ 2) < ⊤) (r : ℝ)
    (hr : periodBallNorm R f ≤ r) :
    0 ≤ r ∧ eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R) ≤ ENNReal.ofReal r := by
  have hne : eLpNorm (fun z : ℝ × Space => f z.1 z.2) 2 (boxMeasure R) ≠ ⊤ := by
    intro htop
    rw [periodBallLIntegral_eq R f hf, htop] at hfin
    simp at hfin
  rw [periodBallNorm_eq R f hf] at hr
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg.trans hr
  exact ⟨hr0, (ENNReal.le_ofReal_iff_toReal_le hne hr0).2 hr⟩

theorem lintegral_ball_sub_le (Φ : Space → ℝ≥0∞) (R : ℝ) (h : Space) (hh : ‖h‖ ≤ 1) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, Φ (y - h) ≤
      ∫⁻ y in Metric.closedBall (0 : Space) (R + 1), Φ y := by
  classical
  rw [← lintegral_indicator Metric.isClosed_closedBall.measurableSet,
    ← lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  set g : Space → ℝ≥0∞ := fun x => (Metric.closedBall (0 : Space) R).indicator (fun _ => (1 : ℝ≥0∞)) (x + h) * Φ x
    with hg
  have e : (fun y => (Metric.closedBall (0 : Space) R).indicator (fun y => Φ (y - h)) y) =
      fun y => g (y - h) := by
    funext y
    simp only [hg, sub_add_cancel, Set.indicator_apply]
    split_ifs <;> simp
  rw [e, lintegral_sub_right_eq_self g h]
  refine lintegral_mono fun x => ?_
  simp only [hg, Set.indicator_apply]
  split_ifs with h1 h2 h2
  · simp
  · exfalso
    apply h2
    rw [Metric.mem_closedBall, dist_zero_right] at h1 ⊢
    calc ‖x‖ = ‖(x + h) - h‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x + h‖ + ‖h‖ := norm_sub_le _ _
      _ ≤ R + 1 := by linarith
  · simp
  · simp

def shiftRate (rate : ℝ → ℝ) (t : ℝ) : ℝ := if t = 0 then 0 else rate t

theorem window_bound (F : ℝ → Space → Space) (R C : ℝ) (hper : IsTimePeriodic F)
    (hbound : periodBallLIntegral (R + 1) (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal C) :
    ∫⁻ σ in Icc (-1 : ℝ) 2, ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
      ENNReal.ofReal (‖F σ y‖ ^ 2) ≤ ENNReal.ofReal (3 * C) := by
  set Φ : ℝ → ℝ≥0∞ := fun σ => ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
    ENNReal.ofReal (‖F σ y‖ ^ 2) with hΦdef
  have hΦ : ∀ σ, Φ (σ + 1) = Φ σ := fun σ => by simp only [hΦdef, hper σ]
  have e1 : ∫⁻ σ in Icc (-1 : ℝ) 0, Φ σ = ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by
    have h := lintegral_Icc_shift Φ hΦ (-1)
    norm_num at h
    exact h
  have e2 : ∫⁻ σ in Icc (1 : ℝ) 2, Φ σ = ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by
    have h := lintegral_Icc_shift Φ hΦ 1
    norm_num at h
    exact h
  have hsub : Icc (-1 : ℝ) 2 ⊆ (Icc (-1 : ℝ) 0 ∪ Icc 0 1) ∪ Icc 1 2 := by
    rintro x ⟨h1, h2⟩
    by_cases a : x ≤ 0
    · exact Or.inl (Or.inl ⟨h1, a⟩)
    by_cases b : x ≤ 1
    · exact Or.inl (Or.inr ⟨by linarith, b⟩)
    · exact Or.inr ⟨by linarith, h2⟩
  have hb : ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ ≤ ENNReal.ofReal C := hbound
  calc ∫⁻ σ in Icc (-1 : ℝ) 2, Φ σ ≤ ∫⁻ σ in (Icc (-1 : ℝ) 0 ∪ Icc 0 1) ∪ Icc 1 2, Φ σ :=
        lintegral_mono_set hsub
    _ ≤ (∫⁻ σ in Icc (-1 : ℝ) 0 ∪ Icc 0 1, Φ σ) + (∫⁻ σ in Icc (1 : ℝ) 2, Φ σ) :=
        lintegral_union_le _ _ _
    _ ≤ ((∫⁻ σ in Icc (-1 : ℝ) 0, Φ σ) + (∫⁻ σ in Icc (0 : ℝ) 1, Φ σ)) +
          (∫⁻ σ in Icc (1 : ℝ) 2, Φ σ) :=
        add_le_add (lintegral_union_le _ _ _) le_rfl
    _ = 3 * ∫⁻ σ in Icc (0 : ℝ) 1, Φ σ := by rw [e1, e2]; ring
    _ ≤ 3 * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (3 * C) := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem joint_shift_bound (F : ℝ → Space → Space) (R C : ℝ) (rate : ℝ → ℝ)
    (hmeas : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hper : IsTimePeriodic F)
    (hbound : periodBallLIntegral (R + 1) (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal C)
    (htime : ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      periodBallNorm R (fun σ y => F (σ + δ) y - F σ y) ≤ rate δ)
    (hspace : ∀ h : Space, 0 < ‖h‖ → ‖h‖ ≤ 1 →
      periodBallNorm R (fun σ y => F σ (y + h) - F σ y) ≤ rate ‖h‖)
    (s : ℝ) (h : Space) (hs : |s| ≤ 1) (hh : ‖h‖ ≤ 1) :
    periodBallLIntegral R (fun σ y => ‖F σ y - F (σ - s) (y - h)‖ ^ 2) ≤
      ENNReal.ofReal ((shiftRate rate |s| + shiftRate rate ‖h‖) ^ 2) := by
  have hRle : R ≤ R + 1 := by linarith
  have hbR : periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) ≤ ENNReal.ofReal C :=
    (periodBallLIntegral_mono hRle _).trans hbound
  have hper2 : ∀ σ y, ‖F (σ + 1) y‖ ^ 2 = ‖F σ y‖ ^ 2 := fun σ y => by rw [hper]
  have hmt : AEStronglyMeasurable (fun z : ℝ × Space => F (z.1 - s) z.2) volume :=
    aestronglyMeasurable_comp_map F hmeas (fun σ => σ - s) id
      (measurePreserving_sub_right volume s) (MeasurePreserving.id volume)
  have hmts : AEStronglyMeasurable (fun z : ℝ × Space => F (z.1 - s) (z.2 - h)) volume :=
    aestronglyMeasurable_comp_map F hmeas (fun σ => σ - s) (fun y => y - h)
      (measurePreserving_sub_right volume s) (measurePreserving_sub_right volume h)
  have hms : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 (z.2 - h)) volume :=
    aestronglyMeasurable_comp_map F hmeas id (fun y => y - h)
      (MeasurePreserving.id volume) (measurePreserving_sub_right volume h)
  have hIt : periodBallLIntegral R (fun σ y => ‖F (σ - s) y‖ ^ 2) ≤ ENNReal.ofReal C := by
    have e := periodBallLIntegral_shift R (fun σ y => ‖F σ y‖ ^ 2) hper2 (-s)
    simp only [← sub_eq_add_neg] at e
    rw [e]
    exact hbR
  have hIs : periodBallLIntegral R (fun σ y => ‖F σ (y - h)‖ ^ 2) ≤ ENNReal.ofReal C :=
    (lintegral_mono fun σ => lintegral_ball_sub_le (fun y => ENNReal.ofReal (‖F σ y‖ ^ 2)) R h hh).trans
      hbound
  have hA : 0 ≤ shiftRate rate |s| ∧
      eLpNorm (fun z : ℝ × Space => F z.1 z.2 - F (z.1 - s) z.2) 2 (boxMeasure R) ≤
        ENNReal.ofReal (shiftRate rate |s|) := by
    have hfin : periodBallLIntegral R (fun σ y => ‖F σ y - F (σ - s) y‖ ^ 2) < ⊤ :=
      periodBallLIntegral_sub_lt_top R F (fun σ y => F (σ - s) y) hmeas hmt C C hbR hIt
    refine eLpNorm_le_of_periodBallNorm_le R (fun σ y => F σ y - F (σ - s) y) (hmeas.sub hmt) hfin _ ?_
    rcases lt_trichotomy s 0 with hs0 | rfl | hs0
    · have hd : -s ∈ Set.Ioc (0 : ℝ) 1 := ⟨by linarith, by rw [abs_of_neg hs0] at hs; exact hs⟩
      have ha : shiftRate rate |s| = rate (-s) := by
        rw [shiftRate, abs_of_neg hs0, if_neg (by linarith)]
      have e : (fun σ y => ‖F σ y - F (σ - s) y‖ ^ 2) = fun σ y => ‖F (σ + -s) y - F σ y‖ ^ 2 := by
        funext σ y
        rw [norm_sub_rev, ← sub_eq_add_neg]
      rw [ha]
      refine le_of_eq_of_le ?_ (htime (-s) hd)
      unfold periodBallNorm
      rw [e]
    · have e : (fun σ y => F σ y - F (σ - 0) y) = fun _ _ => (0 : Space) := by
        funext σ y
        simp
      rw [e]
      simp [shiftRate, periodBallNorm, periodBallLIntegral]
    · have hd : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨hs0, by rw [abs_of_pos hs0] at hs; exact hs⟩
      have ha : shiftRate rate |s| = rate s := by
        rw [shiftRate, abs_of_pos hs0, if_neg (by linarith)]
      have e := periodBallLIntegral_shift R (fun σ y => ‖F (σ + s) y - F σ y‖ ^ 2)
        (fun σ y => by rw [add_right_comm, hper, hper]) (-s)
      simp only [← sub_eq_add_neg, sub_add_cancel] at e
      rw [ha]
      refine le_of_eq_of_le ?_ (htime s hd)
      unfold periodBallNorm
      beta_reduce
      rw [e]
  have hB : 0 ≤ shiftRate rate ‖h‖ ∧
      eLpNorm (fun z : ℝ × Space => F (z.1 - s) z.2 - F (z.1 - s) (z.2 - h)) 2 (boxMeasure R) ≤
        ENNReal.ofReal (shiftRate rate ‖h‖) := by
    have e : periodBallLIntegral R (fun σ y => ‖F (σ - s) y - F (σ - s) (y - h)‖ ^ 2) =
        periodBallLIntegral R (fun σ y => ‖F σ (y - h) - F σ y‖ ^ 2) := by
      have e0 := periodBallLIntegral_shift R (fun σ y => ‖F σ (y - h) - F σ y‖ ^ 2)
        (fun σ y => by rw [hper, hper]) (-s)
      simp only [← sub_eq_add_neg] at e0
      rw [← e0]
      congr 1
      funext σ y
      rw [norm_sub_rev]
    have hfin : periodBallLIntegral R (fun σ y => ‖F (σ - s) y - F (σ - s) (y - h)‖ ^ 2) < ⊤ := by
      rw [e]
      exact periodBallLIntegral_sub_lt_top R (fun σ y => F σ (y - h)) F hms hmeas C C hIs hbR
    refine eLpNorm_le_of_periodBallNorm_le R (fun σ y => F (σ - s) y - F (σ - s) (y - h))
      (hmt.sub hmts) hfin _ ?_
    rcases eq_or_ne h 0 with rfl | hh0
    · have e1 : (fun σ y => F (σ - s) y - F (σ - s) (y - 0)) = fun _ _ => (0 : Space) := by
        funext σ y
        simp
      rw [e1]
      simp [shiftRate, periodBallNorm, periodBallLIntegral]
    · have hn : 0 < ‖-h‖ := by rw [norm_neg]; exact norm_pos_iff.2 hh0
      have hsp := hspace (-h) hn (by rw [norm_neg]; exact hh)
      rw [norm_neg] at hsp
      simp only [← sub_eq_add_neg] at hsp
      have hb : shiftRate rate ‖h‖ = rate ‖h‖ := by
        rw [shiftRate, if_neg (norm_ne_zero_iff.2 hh0)]
      rw [hb]
      refine le_of_eq_of_le ?_ hsp
      unfold periodBallNorm
      rw [e]
  have hD : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2 - F (z.1 - s) (z.2 - h)) volume :=
    hmeas.sub hmts
  have hsplit : (fun z : ℝ × Space => F z.1 z.2 - F (z.1 - s) (z.2 - h)) =
      (fun z : ℝ × Space => F z.1 z.2 - F (z.1 - s) z.2) +
        (fun z : ℝ × Space => F (z.1 - s) z.2 - F (z.1 - s) (z.2 - h)) := by
    funext z
    simp only [Pi.add_apply]
    abel
  refine (periodBallLIntegral_eq R (fun σ y => F σ y - F (σ - s) (y - h)) hD).trans_le ?_
  calc eLpNorm (fun z : ℝ × Space => F z.1 z.2 - F (z.1 - s) (z.2 - h)) 2 (boxMeasure R) ^ 2
      ≤ (ENNReal.ofReal (shiftRate rate |s|) + ENNReal.ofReal (shiftRate rate ‖h‖)) ^ 2 := by
        rw [hsplit]
        gcongr
        exact (eLpNorm_add_le (hmeas.sub hmt).restrict (hmt.sub hmts).restrict (by norm_num)).trans
          (add_le_add hA.2 hB.2)
    _ = ENNReal.ofReal ((shiftRate rate |s| + shiftRate rate ‖h‖) ^ 2) := by
        rw [← ENNReal.ofReal_add hA.1 hB.1, ENNReal.ofReal_pow (add_nonneg hA.1 hB.1)]

def windowSet (R : ℝ) : Set (ℝ × Space) := Icc (-1 : ℝ) 2 ×ˢ Metric.closedBall (0 : Space) (R + 1)

def bumpOfRadius (η : ℝ) (hη : 0 < η) : ContDiffBump (0 : ℝ × Space) :=
  ⟨η / 2, η, by positivity, by linarith⟩

def mollifier (η : ℝ) (hη : 0 < η) : ℝ × Space → ℝ := (bumpOfRadius η hη).normed volume

def smoothed (R η : ℝ) (hη : 0 < η) (f : ℝ → Space → Space) (z : ℝ × Space) : Space :=
  ∫ w, mollifier η hη (z - w) • (windowSet R).indicator (fun w : ℝ × Space => f w.1 w.2) w

theorem smoothed_bounds (R B η : ℝ) (hη : 0 < η) :
    ∃ M L : ℝ, ∀ f : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume →
      ∫⁻ σ in Icc (-1 : ℝ) 2, ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
        ENNReal.ofReal (‖f σ y‖ ^ 2) ≤ ENNReal.ofReal B →
      (∀ z, ‖smoothed R η hη f z‖ ≤ M) ∧
        ∀ z z', dist (smoothed R η hη f z) (smoothed R η hη f z') ≤ L * dist z z' := by
  classical
  set ρ := mollifier η hη with hρdef
  have hρc : Continuous ρ := (bumpOfRadius η hη).continuous_normed
  have hρs : HasCompactSupport ρ := (bumpOfRadius η hη).hasCompactSupport_normed
  obtain ⟨Cl, hCl⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hρs
    ((bumpOfRadius η hη).contDiff_normed (n := 1)) one_ne_zero
  obtain ⟨Sρ, hSρ⟩ := hρs.exists_bound_of_continuous hρc
  have hSρ0 : 0 ≤ Sρ := (norm_nonneg _).trans (hSρ 0)
  have hWc : IsCompact (windowSet R) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hWm : MeasurableSet (windowSet R) :=
    measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hWf : volume (windowSet R) ≠ ⊤ := hWc.measure_lt_top.ne
  set K1 := (volume (windowSet R)).toReal + max B 0 with hK1
  have hK10 : 0 ≤ K1 := add_nonneg ENNReal.toReal_nonneg (le_max_right _ _)
  refine ⟨Sρ * K1, Cl * K1, fun f hf hB => ?_⟩
  set ft := (windowSet R).indicator (fun w : ℝ × Space => f w.1 w.2) with hft
  have hftm : AEStronglyMeasurable ft volume := hf.indicator hWm
  have hL1 : ∫⁻ w, ‖ft w‖ₑ ≤ ENNReal.ofReal K1 := by
    have hsq : ∫⁻ w in windowSet R, ENNReal.ofReal (‖f w.1 w.2‖ ^ 2) ≤ ENNReal.ofReal B := by
      refine le_of_eq_of_le ?_ hB
      have hm : AEMeasurable (fun w : ℝ × Space => ENNReal.ofReal (‖f w.1 w.2‖ ^ 2))
          (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 2)).prod
            ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) (R + 1)))) := by
        rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
        exact ((hf.restrict.norm.aemeasurable.pow_const 2).ennreal_ofReal)
      unfold windowSet
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm]
    calc ∫⁻ w, ‖ft w‖ₑ = ∫⁻ w in windowSet R, ‖f w.1 w.2‖ₑ := by
          rw [hft, ← lintegral_indicator hWm]
          refine lintegral_congr fun w => ?_
          simp only [Set.indicator_apply]
          split_ifs <;> simp
      _ ≤ ∫⁻ w in windowSet R, (1 + ENNReal.ofReal (‖f w.1 w.2‖ ^ 2)) := by
          refine lintegral_mono fun w => ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith [norm_nonneg (f w.1 w.2)]
      _ = volume (windowSet R) + ∫⁻ w in windowSet R, ENNReal.ofReal (‖f w.1 w.2‖ ^ 2) := by
          rw [lintegral_add_left measurable_const]
          simp
      _ ≤ ENNReal.ofReal (volume (windowSet R)).toReal + ENNReal.ofReal (max B 0) := by
          rw [ENNReal.ofReal_toReal hWf]
          exact add_le_add le_rfl (hsq.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)))
      _ = ENNReal.ofReal K1 := by
          rw [hK1, ENNReal.ofReal_add ENNReal.toReal_nonneg (le_max_right _ _)]
  have hfti : Integrable ft volume := ⟨hftm, hL1.trans_lt ENNReal.ofReal_lt_top⟩
  have hint : ∀ z, Integrable (fun w => ρ (z - w) • ft w) volume := fun z =>
    Integrable.mono' (hfti.norm.const_mul Sρ)
      ((hρc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.smul hftm)
      (Eventually.of_forall fun w => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hSρ _) (norm_nonneg _))
  have key : ∀ (v : Space) (c : ℝ), 0 ≤ c → ‖v‖ₑ ≤ ENNReal.ofReal c * ∫⁻ w, ‖ft w‖ₑ → ‖v‖ ≤ c * K1 := by
    intro v c hc hv
    have h2 : ENNReal.ofReal ‖v‖ ≤ ENNReal.ofReal (c * K1) := by
      rw [ofReal_norm, ENNReal.ofReal_mul hc]
      exact hv.trans (mul_le_mul' le_rfl hL1)
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc hK10)).1 h2
  refine ⟨fun z => ?_, fun z z' => ?_⟩
  · refine key _ Sρ hSρ0 ((enorm_integral_le_lintegral_enorm _).trans ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun w => ?_
    rw [enorm_smul, ← ofReal_norm]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hSρ _)) le_rfl
  · rw [dist_eq_norm, smoothed, smoothed, ← integral_sub (hint z) (hint z'),
      show (Cl : ℝ) * K1 * dist z z' = Cl * dist z z' * K1 by ring]
    refine key _ (Cl * dist z z') (by positivity) ((enorm_integral_le_lintegral_enorm _).trans ?_)
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun w => ?_
    rw [← sub_smul, enorm_smul, ← ofReal_norm]
    refine mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl
    have h := hCl.dist_le_mul (z - w) (z' - w)
    rw [dist_sub_right, Real.dist_eq] at h
    rw [Real.norm_eq_abs]
    exact h

theorem periodBallLIntegral_eq_lintegral (R : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    periodBallLIntegral R (fun σ y => ‖f σ y‖ ^ 2) = ∫⁻ z, ‖f z.1 z.2‖ₑ ^ 2 ∂(boxMeasure R) := by
  have hm : AEMeasurable (fun z : ℝ × Space => ‖f z.1 z.2‖ₑ ^ (2 : ℕ))
      (((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod
        ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) R))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact (hf.restrict.enorm).pow_const 2
  symm
  unfold periodBallLIntegral boxMeasure boxSet
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm]
  refine lintegral_congr fun σ => lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem integrable_window (R B : ℝ) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hB : ∫⁻ σ in Icc (-1 : ℝ) 2, ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
      ENNReal.ofReal (‖f σ y‖ ^ 2) ≤ ENNReal.ofReal B) :
    Integrable ((windowSet R).indicator (fun w : ℝ × Space => f w.1 w.2)) volume := by
  classical
  have hWc : IsCompact (windowSet R) := isCompact_Icc.prod (isCompact_closedBall _ _)
  have hWm : MeasurableSet (windowSet R) :=
    measurableSet_Icc.prod Metric.isClosed_closedBall.measurableSet
  have hWf : volume (windowSet R) ≠ ⊤ := hWc.measure_lt_top.ne
  refine ⟨hf.indicator hWm, ?_⟩
  have hsq : ∫⁻ w in windowSet R, ENNReal.ofReal (‖f w.1 w.2‖ ^ 2) ≤ ENNReal.ofReal B := by
    refine le_of_eq_of_le ?_ hB
    have hm : AEMeasurable (fun w : ℝ × Space => ENNReal.ofReal (‖f w.1 w.2‖ ^ 2))
        (((volume : Measure ℝ).restrict (Icc (-1 : ℝ) 2)).prod
          ((volume : Measure Space).restrict (Metric.closedBall (0 : Space) (R + 1)))) := by
      rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
      exact ((hf.restrict.norm.aemeasurable.pow_const 2).ennreal_ofReal)
    unfold windowSet
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod _ hm]
  calc ∫⁻ w, ‖(windowSet R).indicator (fun w : ℝ × Space => f w.1 w.2) w‖ₑ
        = ∫⁻ w in windowSet R, ‖f w.1 w.2‖ₑ := by
        rw [← lintegral_indicator hWm]
        refine lintegral_congr fun w => ?_
        simp only [Set.indicator_apply]
        split_ifs <;> simp
    _ ≤ ∫⁻ w in windowSet R, (1 + ENNReal.ofReal (‖f w.1 w.2‖ ^ 2)) := by
        refine lintegral_mono fun w => ?_
        rw [← ofReal_norm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [norm_nonneg (f w.1 w.2)]
    _ = volume (windowSet R) + ∫⁻ w in windowSet R, ENNReal.ofReal (‖f w.1 w.2‖ ^ 2) := by
        rw [lintegral_add_left measurable_const]
        simp
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hWc.measure_lt_top, hsq.trans_lt ENNReal.ofReal_lt_top⟩

theorem lintegral_sq_le_of_lintegral_eq_one {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (a b : X → ℝ≥0∞) (ha : AEMeasurable a μ) (hb : AEMeasurable b μ) (h1 : ∫⁻ x, a x ∂μ = 1) :
    (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ ∫⁻ x, a x * b x ^ 2 ∂μ := by
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    (f := fun x => a x ^ (1 / 2 : ℝ)) (g := fun x => a x ^ (1 / 2 : ℝ) * b x)
    (ha.pow_const _) ((ha.pow_const _).mul hb)
  have e1 : ∀ x, a x ^ (1 / 2 : ℝ) * (a x ^ (1 / 2 : ℝ) * b x) = a x * b x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (a x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (a x ^ (1 / 2 : ℝ) * b x) ^ (2 : ℝ) = a x * b x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ← ENNReal.rpow_natCast]
    norm_num
  simp only [Pi.mul_apply, e1, e2, e3, h1, ENNReal.one_rpow, one_mul] at hH
  calc (∫⁻ x, a x * b x ∂μ) ^ 2 ≤ ((∫⁻ x, a x * b x ^ 2 ∂μ) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = ∫⁻ x, a x * b x ^ 2 ∂μ := by
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num

instance isAddLeftInvariant_volume_prod : (volume : Measure (ℝ × Space)).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

instance isAddRightInvariant_volume_prod : (volume : Measure (ℝ × Space)).IsAddRightInvariant := by
  rw [Measure.volume_eq_prod]
  infer_instance

theorem smoothed_error (R B η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) (f : ℝ → Space → Space)
    (hf : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (hB : ∫⁻ σ in Icc (-1 : ℝ) 2, ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
      ENNReal.ofReal (‖f σ y‖ ^ 2) ≤ ENNReal.ofReal B) :
    periodBallLIntegral R (fun σ y => ‖f σ y - smoothed R η hη f (σ, y)‖ ^ 2) ≤
      ⨆ (s : ℝ) (h : Space) (_ : |s| ≤ η) (_ : ‖h‖ ≤ η),
        periodBallLIntegral R (fun σ y => ‖f σ y - f (σ - s) (y - h)‖ ^ 2) := by
  classical
  set ρ := mollifier η hη with hρdef
  have hρc : Continuous ρ := (bumpOfRadius η hη).continuous_normed
  have hρs : HasCompactSupport ρ := (bumpOfRadius η hη).hasCompactSupport_normed
  obtain ⟨Sρ, hSρ⟩ := hρs.exists_bound_of_continuous hρc
  have hρ0 : ∀ x, 0 ≤ ρ x := (bumpOfRadius η hη).nonneg_normed
  have hρi : Integrable ρ volume := (bumpOfRadius η hη).integrable_normed
  have hρ1 : ∫ x, ρ x = 1 := (bumpOfRadius η hη).integral_normed
  have hρneg : ∀ x, ρ (-x) = ρ x := (bumpOfRadius η hη).normed_neg
  have hρsupp : ∀ v, ρ v ≠ 0 → ‖v‖ < η := fun v hv => by
    have hv' : v ∈ Function.support ρ := hv
    rw [hρdef, mollifier, (bumpOfRadius η hη).support_normed_eq] at hv'
    simpa [bumpOfRadius] using hv'
  have hρl : ∫⁻ v, ENNReal.ofReal (ρ v) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal hρi (Eventually.of_forall hρ0), hρ1,
      ENNReal.ofReal_one]
  set ft := (windowSet R).indicator (fun w : ℝ × Space => f w.1 w.2) with hft
  have hfti : Integrable ft volume := integrable_window R B f hf hB
  have hftm : AEStronglyMeasurable ft volume := hfti.aestronglyMeasurable
  have hg : ∀ z, smoothed R η hη f z = ∫ v, ρ v • ft (z + v) := by
    intro z
    rw [smoothed, ← integral_add_right_eq_self (fun w => ρ (z - w) • ft w) z]
    congr 1
    funext v
    rw [show z - (v + z) = -v by abel, hρneg, add_comm]
  have hint1 : ∀ z, Integrable (fun v => ρ v • ft (z + v)) volume := fun z =>
    Integrable.mono' ((hfti.comp_add_left z).norm.const_mul Sρ)
      (hρc.aestronglyMeasurable.smul (hftm.comp_measurePreserving (measurePreserving_add_left volume z)))
      (Eventually.of_forall fun v => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (hSρ _) (norm_nonneg _))
  have hpt : ∀ z, ‖f z.1 z.2 - smoothed R η hη f z‖ₑ ^ 2 ≤
      ∫⁻ v, ENNReal.ofReal (ρ v) * ‖f z.1 z.2 - ft (z + v)‖ₑ ^ 2 := by
    intro z
    have e : f z.1 z.2 - smoothed R η hη f z = ∫ v, ρ v • (f z.1 z.2 - ft (z + v)) := by
      rw [hg]
      simp_rw [smul_sub]
      rw [integral_sub (hρi.smul_const _) (hint1 z), integral_smul_const, hρ1, one_smul]
    rw [e]
    refine (pow_le_pow_left₀ zero_le (enorm_integral_le_lintegral_enorm _) 2).trans ?_
    have e2 : ∀ v, ‖ρ v • (f z.1 z.2 - ft (z + v))‖ₑ =
        ENNReal.ofReal (ρ v) * ‖f z.1 z.2 - ft (z + v)‖ₑ := fun v => by
      rw [enorm_smul, ← ofReal_norm, Real.norm_of_nonneg (hρ0 _)]
    simp_rw [e2]
    exact lintegral_sq_le_of_lintegral_eq_one volume _ _ hρc.measurable.ennreal_ofReal.aemeasurable
      ((aestronglyMeasurable_const.sub
        (hftm.comp_measurePreserving (measurePreserving_add_left volume z))).enorm) hρl
  obtain ⟨M, L, hML⟩ := smoothed_bounds R B η hη
  have hgc : Continuous (smoothed R η hη f) := by
    have hl : LipschitzWith (Real.toNNReal (max L 0)) (smoothed R η hη f) :=
      LipschitzWith.of_dist_le_mul fun z z' => by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]
        exact ((hML f hf hB).2 z z').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    exact hl.continuous
  set S := ⨆ (s : ℝ) (h : Space) (_ : |s| ≤ η) (_ : ‖h‖ ≤ η),
      periodBallLIntegral R (fun σ y => ‖f σ y - f (σ - s) (y - h)‖ ^ 2) with hS
  have hpr : (boxMeasure R).prod (volume : Measure (ℝ × Space)) =
      ((volume : Measure (ℝ × Space)).prod volume).restrict (boxSet R ×ˢ univ) := by
    rw [boxMeasure, ← Measure.prod_restrict, Measure.restrict_univ]
  have hjoint : AEMeasurable (Function.uncurry fun (z : ℝ × Space) (v : ℝ × Space) =>
      ENNReal.ofReal (ρ v) * ‖f z.1 z.2 - ft (z + v)‖ₑ ^ 2) ((boxMeasure R).prod volume) := by
    have h1 : AEStronglyMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => f p.1.1 p.1.2)
        ((boxMeasure R).prod volume) := hf.restrict.comp_fst
    have h2 : AEStronglyMeasurable (fun p : (ℝ × Space) × (ℝ × Space) => ft (p.1 + p.2))
        ((boxMeasure R).prod volume) := by
      rw [hpr]
      exact (hftm.comp_snd.comp_measurePreserving (measurePreserving_prod_add volume volume)).restrict
    exact (hρc.measurable.comp measurable_snd).ennreal_ofReal.aemeasurable.mul
      ((h1.sub h2).enorm.pow_const 2)
  have hfg : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2 - smoothed R η hη f (z.1, z.2))
      volume := hf.sub hgc.aestronglyMeasurable
  rw [periodBallLIntegral_eq_lintegral R (fun σ y => f σ y - smoothed R η hη f (σ, y)) hfg]
  calc ∫⁻ z, ‖f z.1 z.2 - smoothed R η hη f (z.1, z.2)‖ₑ ^ 2 ∂(boxMeasure R)
      ≤ ∫⁻ z, (∫⁻ v, ENNReal.ofReal (ρ v) * ‖f z.1 z.2 - ft (z + v)‖ₑ ^ 2) ∂(boxMeasure R) :=
        lintegral_mono fun z => hpt z
    _ = ∫⁻ v, ∫⁻ z, ENNReal.ofReal (ρ v) * ‖f z.1 z.2 - ft (z + v)‖ₑ ^ 2 ∂(boxMeasure R) :=
        lintegral_lintegral_swap hjoint
    _ ≤ ∫⁻ v, ENNReal.ofReal (ρ v) * S := by
        refine lintegral_mono fun v => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        by_cases hv : ρ v = 0
        · simp [hv]
        refine mul_le_mul' le_rfl ?_
        have hvn := hρsupp v hv
        have hv1 : |v.1| ≤ η := (norm_fst_le v).trans hvn.le
        have hv2 : ‖v.2‖ ≤ η := (norm_snd_le v).trans hvn.le
        have hin : ∫⁻ z, ‖f z.1 z.2 - ft (z + v)‖ₑ ^ 2 ∂(boxMeasure R) =
            ∫⁻ z, ‖f z.1 z.2 - f (z.1 - -v.1) (z.2 - -v.2)‖ₑ ^ 2 ∂(boxMeasure R) := by
          unfold boxMeasure
          refine setLIntegral_congr_fun (measurableSet_boxSet R) fun z hz => ?_
          have hmem : z + v ∈ windowSet R := by
            obtain ⟨⟨hz1, hz2⟩, hz3⟩ := hz
            rw [Metric.mem_closedBall, dist_zero_right] at hz3
            refine ⟨⟨?_, ?_⟩, ?_⟩
            · have := neg_abs_le v.1
              simp only [Prod.fst_add]
              linarith
            · have := le_abs_self v.1
              simp only [Prod.fst_add]
              linarith
            · rw [Metric.mem_closedBall, dist_zero_right, Prod.snd_add]
              calc ‖z.2 + v.2‖ ≤ ‖z.2‖ + ‖v.2‖ := norm_add_le _ _
                _ ≤ R + 1 := by linarith
          rw [hft, Set.indicator_of_mem hmem, sub_neg_eq_add, sub_neg_eq_add]
          rfl
        rw [hin, ← periodBallLIntegral_eq_lintegral R (fun σ y => f σ y - f (σ - -v.1) (y - -v.2))
          (hf.sub (aestronglyMeasurable_comp_map f hf (fun σ => σ - -v.1) (fun y => y - -v.2)
            (measurePreserving_sub_right volume _) (measurePreserving_sub_right volume _)))]
        exact le_iSup_of_le (-v.1) (le_iSup_of_le (-v.2)
          (le_iSup_of_le (by rwa [abs_neg]) (le_iSup_of_le (by rwa [norm_neg]) le_rfl)))
    _ = S := by
        rw [lintegral_mul_const _ hρc.measurable.ennreal_ofReal, hρl, one_mul]

theorem exists_mollified (R B η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ M L : ℝ, ∀ f : ℝ → Space → Space,
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume →
      ∫⁻ σ in Icc (-1 : ℝ) 2, ∫⁻ y in Metric.closedBall (0 : Space) (R + 1),
        ENNReal.ofReal (‖f σ y‖ ^ 2) ≤ ENNReal.ofReal B →
      ∃ g : ℝ × Space → Space, Continuous g ∧ (∀ z, ‖g z‖ ≤ M) ∧
        (∀ z z', dist (g z) (g z') ≤ L * dist z z') ∧
        periodBallLIntegral R (fun σ y => ‖f σ y - g (σ, y)‖ ^ 2) ≤
          ⨆ (s : ℝ) (h : Space) (_ : |s| ≤ η) (_ : ‖h‖ ≤ η),
            periodBallLIntegral R (fun σ y => ‖f σ y - f (σ - s) (y - h)‖ ^ 2) := by
  obtain ⟨M, L, hML⟩ := smoothed_bounds R B η hη
  refine ⟨M, max L 0, fun f hf hB => ⟨smoothed R η hη f, ?_, (hML f hf hB).1, fun z z' => ?_,
    smoothed_error R B η hη hη1 f hf hB⟩⟩
  · have hl : LipschitzWith (Real.toNNReal (max L 0)) (smoothed R η hη f) :=
      LipschitzWith.of_dist_le_mul fun z z' => by
        rw [Real.coe_toNNReal _ (le_max_right _ _)]
        exact ((hML f hf hB).2 z z').trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)
    exact hl.continuous
  · exact ((hML f hf hB).2 z z').trans (mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg)

theorem exists_smooth_approx (F : ℕ → ℝ → Space → Space) (R C : ℝ) (rate : ℝ → ℝ)
    (hrate : Tendsto rate (𝓝[>] 0) (𝓝 0))
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => F n z.1 z.2) volume)
    (hper : ∀ n, IsTimePeriodic (F n))
    (hbound : ∀ n, periodBallLIntegral (R + 1) (fun σ y => ‖F n σ y‖ ^ 2) ≤ ENNReal.ofReal C)
    (htime : ∀ n, ∀ δ ∈ Set.Ioc (0 : ℝ) 1,
      periodBallNorm R (fun σ y => F n (σ + δ) y - F n σ y) ≤ rate δ)
    (hspace : ∀ n, ∀ h : Space, 0 < ‖h‖ → ‖h‖ ≤ 1 →
      periodBallNorm R (fun σ y => F n σ (y + h) - F n σ y) ≤ rate ‖h‖)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (g : ℕ → ℝ × Space → Space) (M : ℝ), (∀ n, Continuous (g n)) ∧ (∀ n z, ‖g n z‖ ≤ M) ∧
      (∀ η > 0, ∃ δ > 0, ∀ n z z', dist z z' < δ → dist (g n z) (g n z') < η) ∧
      ∀ n, periodBallLIntegral R (fun σ y => ‖F n σ y - g n (σ, y)‖ ^ 2) ≤ ENNReal.ofReal ε := by
  obtain ⟨δ0, hδ0, hδ0'⟩ := Metric.tendsto_nhdsWithin_nhds.1 hrate (Real.sqrt ε / 2) (by positivity)
  set η := min (δ0 / 2) 1 with hη
  have hη0 : 0 < η := lt_min (by positivity) one_pos
  have hη1 : η ≤ 1 := min_le_right _ _
  have hsmall : ∀ t, 0 ≤ t → t ≤ η → |shiftRate rate t| ≤ Real.sqrt ε / 2 := by
    intro t ht0 htη
    unfold shiftRate
    split_ifs with h0
    · simp only [abs_zero]
      positivity
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm h0)
      have hlt : dist t 0 < δ0 := by
        rw [Real.dist_eq, sub_zero, abs_of_pos htpos]
        linarith [min_le_left (δ0 / 2) 1]
      have h1 := hδ0' (x := t) htpos hlt
      rw [Real.dist_eq, sub_zero] at h1
      exact h1.le
  obtain ⟨M, L, hML⟩ := exists_mollified R (3 * C) η hη0 hη1
  choose g hgc hgM hgL hgerr using fun n =>
    hML (F n) (hmeas n) (window_bound (F n) R C (hper n) (hbound n))
  refine ⟨g, M, hgc, hgM, fun η' hη' => ⟨η' / (|L| + 1), by positivity, fun n z z' hzz' => ?_⟩,
    fun n => ?_⟩
  · have h1 : L * dist z z' ≤ (|L| + 1) * dist z z' :=
      mul_le_mul_of_nonneg_right (by linarith [le_abs_self L]) dist_nonneg
    have h2 : (|L| + 1) * dist z z' < η' := by
      rw [lt_div_iff₀' (by positivity)] at hzz'
      exact hzz'
    exact (hgL n z z').trans_lt (h1.trans_lt h2)
  · refine (hgerr n).trans (iSup_le fun s => iSup_le fun h => iSup_le fun hs => iSup_le fun hh => ?_)
    refine (joint_shift_bound (F n) R C rate (hmeas n) (hper n) (hbound n) (htime n) (hspace n) s h
      (hs.trans hη1) (hh.trans hη1)).trans (ENNReal.ofReal_le_ofReal ?_)
    have ha := hsmall |s| (abs_nonneg s) hs
    have hb := hsmall ‖h‖ (norm_nonneg h) hh
    have hxy : |shiftRate rate |s| + shiftRate rate ‖h‖| ≤ Real.sqrt ε :=
      (abs_add_le _ _).trans (by linarith)
    rw [← sq_abs]
    calc |shiftRate rate |s| + shiftRate rate ‖h‖| ^ 2 ≤ Real.sqrt ε ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hxy 2
      _ = ε := Real.sq_sqrt hε.le

theorem fundamental_subseq_of_approx (F : ℕ → ℝ → Space → Space) (R C : ℝ)
    (hmeas : ∀ n, AEStronglyMeasurable (fun z : ℝ × Space => F n z.1 z.2) volume)
    (hbound : ∀ n, periodBallLIntegral (R + 1) (fun σ y => ‖F n σ y‖ ^ 2) ≤ ENNReal.ofReal C)
    (happrox : ∀ ε > 0, ∃ (g : ℕ → ℝ × Space → Space) (M : ℝ), (∀ n, Continuous (g n)) ∧
      (∀ n z, ‖g n z‖ ≤ M) ∧
      (∀ η > 0, ∃ δ > 0, ∀ n z z', dist z z' < δ → dist (g n z) (g n z') < η) ∧
      ∀ n, periodBallLIntegral R (fun σ y => ‖F n σ y - g n (σ, y)‖ ^ 2) ≤ ENNReal.ofReal ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      periodBallNorm R (fun σ y => F (φ m) σ y - F (φ n) σ y) < ε := by
  have hRle : R ≤ R + 1 := by linarith
  have hmem : ∀ n, MemLp (fun z : ℝ × Space => F n z.1 z.2) 2 (boxMeasure R) := by
    intro n
    refine ⟨(hmeas n).restrict, ?_⟩
    have h := (periodBallLIntegral_eq R (F n) (hmeas n)).symm.trans_le
      ((periodBallLIntegral_mono hRle _).trans (hbound n))
    have h' : eLpNorm (fun z : ℝ × Space => F n z.1 z.2) 2 (boxMeasure R) ^ 2 < ∞ :=
      h.trans_lt ENNReal.ofReal_lt_top
    simpa using h'
  let u : ℕ → Lp Space 2 (boxMeasure R) := fun n => (hmem n).toLp _
  have hed : ∀ m n, edist (u m) (u n) =
      eLpNorm ((fun z : ℝ × Space => F m z.1 z.2) - (fun z : ℝ × Space => F n z.1 z.2)) 2
        (boxMeasure R) := fun m n => Lp.edist_toLp_toLp _ _ (hmem m) (hmem n)
  have hdist : ∀ m n, dist (u m) (u n) = periodBallNorm R (fun σ y => F m σ y - F n σ y) := by
    intro m n
    rw [dist_edist, hed, periodBallNorm_eq R _ ((hmeas m).sub (hmeas n))]
    rfl
  have hnet : ∀ ε > 0, ∃ I : Finset ℕ, ∀ n, ∃ i ∈ I, dist (u n) (u i) < ε := by
    intro ε hε
    have he : 0 < ε / 4 := by positivity
    obtain ⟨g, M, hgc, hgM, hgmod, hgerr⟩ := happrox ((ε / 4) ^ 2) (by positivity)
    have hgm : ∀ n, AEStronglyMeasurable (g n) (boxMeasure R) :=
      fun n => (hgc n).aestronglyMeasurable
    have herr : ∀ n, eLpNorm ((fun z : ℝ × Space => F n z.1 z.2) - g n) 2 (boxMeasure R) ≤
        ENNReal.ofReal (ε / 4) := by
      intro n
      have h := periodBallLIntegral_eq R (fun σ y => F n σ y - g n (σ, y))
        ((hmeas n).sub (hgc n).aestronglyMeasurable)
      have h2 := h.symm.trans_le (hgerr n)
      rw [ENNReal.ofReal_pow he.le] at h2
      exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h2
    have hK0ne : (boxMeasure R Set.univ) ^ ((2 : ℝ≥0∞).toReal⁻¹) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    set K0 := ((boxMeasure R Set.univ) ^ ((2 : ℝ≥0∞).toReal⁻¹)).toReal with hK0
    have hK0nn : 0 ≤ K0 := ENNReal.toReal_nonneg
    set η := ε / 4 / (K0 + 1) with hη_def
    have hη : 0 < η := by positivity
    have hKη : K0 * η ≤ ε / 4 := by
      rw [hη_def, mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    obtain ⟨I, hI⟩ := exists_uniform_net R g M hgM hgmod hη
    refine ⟨I, fun n => ?_⟩
    obtain ⟨i, hi, hni⟩ := hI n
    refine ⟨i, hi, ?_⟩
    have hmid : eLpNorm (g n - g i) 2 (boxMeasure R) ≤ ENNReal.ofReal (ε / 4) := by
      have hae : ∀ᵐ z ∂(boxMeasure R), ‖(g n - g i) z‖ ≤ η :=
        (ae_restrict_mem (measurableSet_boxSet R)).mono fun z hz => by
          rw [Pi.sub_apply, ← dist_eq_norm]
          exact (hni z hz).le
      calc eLpNorm (g n - g i) 2 (boxMeasure R)
          ≤ (boxMeasure R Set.univ) ^ ((2 : ℝ≥0∞).toReal⁻¹) * ENNReal.ofReal η :=
            eLpNorm_le_of_ae_bound hae
        _ = ENNReal.ofReal (K0 * η) := by
            rw [ENNReal.ofReal_mul hK0nn, hK0, ENNReal.ofReal_toReal hK0ne]
        _ ≤ ENNReal.ofReal (ε / 4) := ENNReal.ofReal_le_ofReal hKη
    have hsplit : (fun z : ℝ × Space => F n z.1 z.2) - (fun z : ℝ × Space => F i z.1 z.2) =
        ((fun z : ℝ × Space => F n z.1 z.2) - g n) +
          ((g n - g i) + (g i - (fun z : ℝ × Space => F i z.1 z.2))) := by
      funext z
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    have htri : eLpNorm ((fun z : ℝ × Space => F n z.1 z.2) - (fun z : ℝ × Space => F i z.1 z.2))
        2 (boxMeasure R) ≤
        ENNReal.ofReal (ε / 4) + (ENNReal.ofReal (ε / 4) + ENNReal.ofReal (ε / 4)) := by
      rw [hsplit]
      refine (eLpNorm_add_le ((hmeas n).restrict.sub (hgm n))
        (((hgm n).sub (hgm i)).add ((hgm i).sub (hmeas i).restrict)) (by norm_num)).trans ?_
      refine add_le_add (herr n) ?_
      refine (eLpNorm_add_le ((hgm n).sub (hgm i)) ((hgm i).sub (hmeas i).restrict)
        (by norm_num)).trans ?_
      refine add_le_add hmid ?_
      rw [eLpNorm_sub_comm]
      exact herr i
    rw [← edist_lt_ofReal, hed]
    refine htri.trans_lt ?_
    rw [← ENNReal.ofReal_add he.le he.le, ← ENNReal.ofReal_add he.le (by positivity)]
    exact (ENNReal.ofReal_lt_ofReal_iff hε).2 (by linarith)
  have htb : TotallyBounded (range u) := by
    refine Metric.totallyBounded_iff.2 fun ε hε => ?_
    obtain ⟨I, hI⟩ := hnet ε hε
    refine ⟨u '' (I : Set ℕ), I.finite_toSet.image _, ?_⟩
    rintro _ ⟨n, rfl⟩
    obtain ⟨i, hi, hni⟩ := hI n
    exact mem_iUnion₂.2 ⟨u i, ⟨i, hi, rfl⟩, Metric.mem_ball.2 hni⟩
  obtain ⟨a, -, φ, hφ, hlim⟩ := (htb.closure.isCompact_of_isClosed isClosed_closure).tendsto_subseq
    (fun n => subset_closure (mem_range_self n))
  refine ⟨φ, hφ, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hlim.cauchySeq ε hε
  exact ⟨N, fun m hm n hn => by rw [← hdist]; exact hN m hm n hn⟩

end Internal.TranslationCriterion

open Internal.TranslationCriterion in
theorem translationCriterionHolds_proof : TranslationCriterionHolds := by
  intro F R C rate _ hrate hmeas hper hbound htime hspace
  exact fundamental_subseq_of_approx F R C hmeas hbound
    (fun ε hε => exists_smooth_approx F R C rate hrate hmeas hper hbound htime hspace ε hε)

end Breakdown.Cert

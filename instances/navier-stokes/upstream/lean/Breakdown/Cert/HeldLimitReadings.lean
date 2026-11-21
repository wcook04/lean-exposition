import Breakdown.Cert.LocalCompactness

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldLimitReadings

def ballMeasure (R : ℝ) : Measure (ℝ × Space) :=
  (volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume.restrict (Metric.closedBall (0 : Space) R))

theorem aestronglyMeasurable_ball {E : Type*} [TopologicalSpace E] {R : ℝ} {F : ℝ × Space → E}
    (hF : AEStronglyMeasurable F volume) : AEStronglyMeasurable F (ballMeasure R) := by
  rw [ballMeasure, Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact hF.restrict

theorem ae_prod_of_ae_ae {E : Type*} [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E]
    {μ : Measure ℝ} {ν : Measure Space} [SFinite ν] {F G : ℝ × Space → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) (hG : AEStronglyMeasurable G (μ.prod ν))
    (h : ∀ᵐ σ ∂μ, ∀ᵐ y ∂ν, F (σ, y) = G (σ, y)) : F =ᵐ[μ.prod ν] G := by
  have h1 := Measure.ae_ae_of_ae_prod hF.ae_eq_mk
  have h2 := Measure.ae_ae_of_ae_prod hG.ae_eq_mk
  have hs : MeasurableSet {z | hF.mk F z = hG.mk G z} :=
    hF.stronglyMeasurable_mk.measurableSet_eq_fun hG.stronglyMeasurable_mk
  have h3 : ∀ᵐ z ∂μ.prod ν, hF.mk F z = hG.mk G z := by
    refine (Measure.ae_prod_iff_ae_ae hs).2 ?_
    filter_upwards [h, h1, h2] with σ a b c
    filter_upwards [a, b, c] with y a b c
    rw [← b, ← c, a]
  filter_upwards [hF.ae_eq_mk, hG.ae_eq_mk, h3] with z a b c
  rw [a, b]
  exact c

theorem ae_ball {R : ℝ} {F G : ℝ × Space → Space} (hF : AEStronglyMeasurable F volume)
    (hG : AEStronglyMeasurable G volume) (h : ∀ᵐ σ : ℝ, ∀ᵐ y : Space, F (σ, y) = G (σ, y)) :
    F =ᵐ[ballMeasure R] G := by
  have hF' := aestronglyMeasurable_ball (R := R) hF
  have hG' := aestronglyMeasurable_ball (R := R) hG
  unfold ballMeasure at hF' hG' ⊢
  exact ae_prod_of_ae_ae hF' hG' ((ae_restrict_of_ae h).mono fun σ hσ => ae_restrict_of_ae hσ)

theorem periodBallLIntegral_eq (R : ℝ) (F : ℝ → Space → Space)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) ∂ballMeasure R := by
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2)) (ballMeasure R) :=
    ((aestronglyMeasurable_ball hF).norm.pow 2).aemeasurable.ennreal_ofReal
  unfold ballMeasure at hm ⊢
  rw [lintegral_prod _ hm]
  rfl

theorem memLp_of_lintegral (R : ℝ) (F : ℝ → Space → Space)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hfin : periodBallLIntegral R (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    MemLp (fun z : ℝ × Space => F z.1 z.2) 2 (ballMeasure R) := by
  have hF' := aestronglyMeasurable_ball (R := R) hF
  refine (memLp_two_iff_integrable_sq_norm hF').2 ⟨hF'.norm.pow 2, ?_⟩
  refine (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).2 ?_
  have e := periodBallLIntegral_eq R F hF
  rw [e] at hfin
  exact hfin

structure IsLocalFamily {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (R K : ℝ)
    (ρ : E → ℝ → Space → Space) : Prop where
  nonneg : 0 ≤ K
  measurable : ∀ u, AEStronglyMeasurable (fun z : ℝ × Space => ρ u z.1 z.2) volume
  bound : ∀ u, periodBallLIntegral R (fun σ y => ‖ρ u σ y‖ ^ 2) ≤ ENNReal.ofReal (‖u‖ ^ 2 * K)
  add : ∀ u u', ∀ᵐ σ : ℝ, ∀ᵐ y : Space, ρ (u + u') σ y = ρ u σ y + ρ u' σ y
  smul : ∀ (c : ℝ) u, ∀ᵐ σ : ℝ, ∀ᵐ y : Space, ρ (c • u) σ y = c • ρ u σ y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {R K : ℝ}
  {ρ : E → ℝ → Space → Space}

theorem IsLocalFamily.memLp (h : IsLocalFamily R K ρ) (u : E) :
    MemLp (fun z : ℝ × Space => ρ u z.1 z.2) 2 (ballMeasure R) :=
  memLp_of_lintegral R (ρ u) (h.measurable u) (lt_of_le_of_lt (h.bound u) ENNReal.ofReal_lt_top)

theorem IsLocalFamily.ofReal_norm_sq (h : IsLocalFamily R K ρ) (u : E) :
    ENNReal.ofReal (‖(h.memLp u).toLp _‖ ^ 2) = periodBallLIntegral R (fun σ y => ‖ρ u σ y‖ ^ 2) := by
  refine (Internal.LocalCompactness.lintegral_norm_sq ((h.memLp u).toLp _)).symm.trans
    ((lintegral_congr_ae ?_).trans (periodBallLIntegral_eq R (ρ u) (h.measurable u)).symm)
  filter_upwards [(h.memLp u).coeFn_toLp] with z hz
  rw [hz]

theorem IsLocalFamily.norm_le (h : IsLocalFamily R K ρ) (u : E) :
    ‖(h.memLp u).toLp _‖ ≤ Real.sqrt K * ‖u‖ := by
  have h1 : ENNReal.ofReal (‖(h.memLp u).toLp _‖ ^ 2) ≤ ENNReal.ofReal (‖u‖ ^ 2 * K) :=
    (h.ofReal_norm_sq u).trans_le (h.bound u)
  have hK := h.nonneg
  have hle : ‖(h.memLp u).toLp _‖ ^ 2 ≤ ‖u‖ ^ 2 * K :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  calc ‖(h.memLp u).toLp _‖ = Real.sqrt (‖(h.memLp u).toLp _‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (‖u‖ ^ 2 * K) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt K * ‖u‖ := by rw [mul_comm, Real.sqrt_mul hK, Real.sqrt_sq (norm_nonneg _)]

def IsLocalFamily.lin (h : IsLocalFamily R K ρ) : E →ₗ[ℝ] Lp Space 2 (ballMeasure R) where
  toFun u := (h.memLp u).toLp _
  map_add' u u' := by
    rw [← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _
      (ae_ball (h.measurable _) ((h.measurable u).add (h.measurable u')) (h.add u u'))
  map_smul' c u := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _
      (ae_ball (h.measurable _) ((h.measurable u).const_smul c) (h.smul c u))

theorem IsLocalFamily.lin_apply (h : IsLocalFamily R K ρ) (u : E) :
    h.lin u = (h.memLp u).toLp _ := rfl

theorem IsLocalFamily.lin_norm_le (h : IsLocalFamily R K ρ) (u : E) :
    ‖h.lin u‖ ≤ Real.sqrt K * ‖u‖ := by
  rw [h.lin_apply u]
  exact h.norm_le u

def IsLocalFamily.clm (h : IsLocalFamily R K ρ) : E →L[ℝ] Lp Space 2 (ballMeasure R) :=
  h.lin.mkContinuous (Real.sqrt K) fun u => h.lin_norm_le u

theorem IsLocalFamily.clm_apply (h : IsLocalFamily R K ρ) (u : E) :
    h.clm u = (h.memLp u).toLp _ :=
  (LinearMap.mkContinuous_apply _ _ _ _).trans (h.lin_apply u)

theorem IsLocalFamily.clm_ae (h : IsLocalFamily R K ρ) (u : E) :
    (h.clm u : ℝ × Space → Space) =ᵐ[ballMeasure R] fun z => ρ u z.1 z.2 := by
  rw [h.clm_apply u]
  exact (h.memLp u).coeFn_toLp

theorem IsLocalFamily.ofReal_norm_sub_sq (h : IsLocalFamily R K ρ) (u u' : E) :
    ENNReal.ofReal (‖h.clm u - h.clm u'‖ ^ 2) =
      periodBallLIntegral R (fun σ y => ‖ρ u σ y - ρ u' σ y‖ ^ 2) := by
  refine (Internal.LocalCompactness.lintegral_norm_sq (h.clm u - h.clm u')).symm.trans
    ((lintegral_congr_ae ?_).trans (periodBallLIntegral_eq R (fun σ y => ρ u σ y - ρ u' σ y)
      ((h.measurable u).sub (h.measurable u'))).symm)
  have e : ((h.clm u - h.clm u' : Lp Space 2 (ballMeasure R)) : ℝ × Space → Space)
      =ᵐ[ballMeasure R] (fun z => ρ u z.1 z.2) - fun z => ρ u' z.1 z.2 :=
    (Lp.coeFn_sub (h.clm u) (h.clm u')).trans ((h.clm_ae u).sub (h.clm_ae u'))
  exact e.mono fun z hz => congrArg (fun x : Space => ENNReal.ofReal (‖x‖ ^ 2)) hz

theorem tendsto_of_fundamental_weak {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) (x : ℕ → E) (x₀ : E)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (x n) y) atTop (𝓝 (inner ℝ x₀ y)))
    (hc : CauchySeq fun n => T (x n)) : Tendsto (fun n => T (x n)) atTop (𝓝 (T x₀)) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hc
  have hz : ∀ z, inner ℝ g z = inner ℝ (T x₀) z := fun z => by
    have h1 : Tendsto (fun n => inner ℝ (T (x n)) z) atTop (𝓝 (inner ℝ g z)) :=
      hg.inner tendsto_const_nhds
    have h2 : Tendsto (fun n => inner ℝ (T (x n)) z) atTop (𝓝 (inner ℝ (T x₀) z)) := by
      have := hw (ContinuousLinearMap.adjoint T z)
      simpa only [ContinuousLinearMap.adjoint_inner_right] using this
    exact tendsto_nhds_unique h1 h2
  have hgx : g = T x₀ := by
    have h := hz (g - T x₀)
    rw [← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℝ), inner_sub_left, h, sub_self]
  rw [hgx] at hg
  exact hg

theorem IsLocalFamily.tendsto [CompleteSpace E] (h : IsLocalFamily R K ρ) (u : ℕ → E) (u₀ : E)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hc : ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      periodBallNorm R (fun σ y => ρ (u m) σ y - ρ (u n) σ y) < ε) :
    Tendsto (fun n => periodBallLIntegral R (fun σ y => ‖ρ (u n) σ y - ρ u₀ σ y‖ ^ 2)) atTop
      (𝓝 0) := by
  have hdist : ∀ m n, dist (h.clm (u m)) (h.clm (u n)) =
      periodBallNorm R (fun σ y => ρ (u m) σ y - ρ (u n) σ y) := fun m n => by
    rw [dist_eq_norm, periodBallNorm, ← h.ofReal_norm_sub_sq, ENNReal.toReal_ofReal (sq_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
  have hcs : CauchySeq fun n => h.clm (u n) :=
    Metric.cauchySeq_iff.2 fun ε hε => (hc ε hε).imp fun N hN m hm n hn => by
      rw [hdist]
      exact hN m hm n hn
  have ht := tendsto_of_fundamental_weak h.clm u u₀ hw hcs
  have hn : Tendsto (fun n => ‖h.clm (u n) - h.clm u₀‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.1 ht
  have h0 : Tendsto (fun n => ENNReal.ofReal (‖h.clm (u n) - h.clm u₀‖ ^ 2)) atTop
      (𝓝 (ENNReal.ofReal ((0 : ℝ) ^ 2))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp (hn.pow 2)
  rw [show ENNReal.ofReal ((0 : ℝ) ^ 2) = 0 by simp] at h0
  exact h0.congr fun n => h.ofReal_norm_sub_sq _ _

theorem add_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (L : Freq.X →L[ℝ] Lp (α := Space) Space p)
    (w w' w'' : ℝ → Space → Space) (u u' : XX)
    (h : ∀ᵐ σ : ℝ, w σ =ᵐ[volume]
      (L (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (h' : ∀ᵐ σ : ℝ, w' σ =ᵐ[volume]
      (L (gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (h'' : ∀ᵐ σ : ℝ, w'' σ =ᵐ[volume]
      (L (gradPart (((u + u' : XX) : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)) :
    ∀ᵐ σ : ℝ, ∀ᵐ y : Space, w'' σ y = w σ y + w' σ y := by
  have hs : ∀ᵐ σ : ℝ, ((u + u' : XX) : TimeCircle → XBar) (σ : TimeCircle) =
      (u : TimeCircle → XBar) σ + (u' : TimeCircle → XBar) σ :=
    (ae_coe_iff (fun t => ((u + u' : XX) : TimeCircle → XBar) t =
      (u : TimeCircle → XBar) t + (u' : TimeCircle → XBar) t)).1 (Lp.coeFn_add u u')
  have hsum : ∀ᵐ σ : ℝ, (fun y => w σ y + w' σ y) =ᵐ[volume]
      (L (gradPart (((u + u' : XX) : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
    filter_upwards [h, h', hs] with σ a b c
    rw [c, map_add, map_add]
    exact (a.add b).trans (Lp.coeFn_add _ _).symm
  filter_upwards [hsum, h''] with σ a b
  filter_upwards [a, b] with y a b
  exact b.trans a.symm

theorem smul_ae {p : ℝ≥0∞} [Fact (1 ≤ p)] (L : Freq.X →L[ℝ] Lp (α := Space) Space p)
    (w w'' : ℝ → Space → Space) (c : ℝ) (u : XX)
    (h : ∀ᵐ σ : ℝ, w σ =ᵐ[volume]
      (L (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space))
    (h'' : ∀ᵐ σ : ℝ, w'' σ =ᵐ[volume]
      (L (gradPart (((c • u : XX) : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space)) :
    ∀ᵐ σ : ℝ, ∀ᵐ y : Space, w'' σ y = c • w σ y := by
  have hs : ∀ᵐ σ : ℝ, ((c • u : XX) : TimeCircle → XBar) (σ : TimeCircle) =
      c • (u : TimeCircle → XBar) σ :=
    (ae_coe_iff (fun t => ((c • u : XX) : TimeCircle → XBar) t =
      c • (u : TimeCircle → XBar) t)).1 (Lp.coeFn_smul c u)
  have hsc : ∀ᵐ σ : ℝ, (fun y => c • w σ y) =ᵐ[volume]
      (L (gradPart (((c • u : XX) : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) := by
    filter_upwards [h, hs] with σ a d
    rw [d, map_smul, map_smul]
    exact (a.const_smul c).trans (Lp.coeFn_smul _ _).symm
  filter_upwards [hsc, h''] with σ a b
  filter_upwards [a, b] with y a b
  exact b.trans a.symm

theorem velocity_family (h12 : ReadingExistsHolds) (R : ℝ) :
    IsLocalFamily R (volume (Metric.closedBall (0 : Space) R)).toReal
      (fun u => (readingOf u).1) where
  nonneg := ENNReal.toReal_nonneg
  measurable u := (Internal.LocalCompactness.reading_spec h12 u).measurable_velocity
  bound u := Internal.LocalCompactness.period_velocity_le R _ u
    (Internal.LocalCompactness.reading_spec h12 u).velocity_eq
  add u u' := add_ae velocity _ _ _ u u'
    (Internal.LocalCompactness.reading_spec h12 u).velocity_eq
    (Internal.LocalCompactness.reading_spec h12 u').velocity_eq
    (Internal.LocalCompactness.reading_spec h12 (u + u')).velocity_eq
  smul c u := smul_ae velocity _ _ c u
    (Internal.LocalCompactness.reading_spec h12 u).velocity_eq
    (Internal.LocalCompactness.reading_spec h12 (c • u)).velocity_eq

theorem column_family (h12 : ReadingExistsHolds) (R : ℝ) (j : Fin 3) :
    IsLocalFamily R 1 (fun u => gradColumn (readingOf u).2.1 j) where
  nonneg := zero_le_one
  measurable u := (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
    (Internal.LocalCompactness.reading_spec h12 u).measurable_gradient
  bound u := by
    rw [mul_one]
    exact Internal.LocalCompactness.period_column_le R j _ u
      (Internal.LocalCompactness.reading_column_ae (Internal.LocalCompactness.reading_spec h12 u) j)
  add u u' := add_ae (partialX j) _ _ _ u u'
    (Internal.LocalCompactness.reading_column_ae (Internal.LocalCompactness.reading_spec h12 u) j)
    (Internal.LocalCompactness.reading_column_ae (Internal.LocalCompactness.reading_spec h12 u') j)
    (Internal.LocalCompactness.reading_column_ae
      (Internal.LocalCompactness.reading_spec h12 (u + u')) j)
  smul c u := smul_ae (partialX j) _ _ c u
    (Internal.LocalCompactness.reading_column_ae (Internal.LocalCompactness.reading_spec h12 u) j)
    (Internal.LocalCompactness.reading_column_ae
      (Internal.LocalCompactness.reading_spec h12 (c • u)) j)

end Internal.HeldLimitReadings

namespace Internal.HeldLimit

def IsLocalReadingLimit (v : ℕ → VelField) (G : ℕ → GradField) (v₀ : VelField)
    (G₀ : GradField) : Prop :=
  ∀ R > 0,
    periodBallLIntegral R (fun σ y => ‖v₀ σ y‖ ^ 2) < ⊤ ∧
    (∀ j, periodBallLIntegral R (fun σ y => ‖gradColumn G₀ j σ y‖ ^ 2) < ⊤) ∧
    Tendsto (fun n => periodBallLIntegral R (fun σ y => ‖v n σ y - v₀ σ y‖ ^ 2)) atTop (𝓝 0) ∧
    ∀ j, Tendsto (fun n => periodBallLIntegral R
      (fun σ y => ‖gradColumn (G n) j σ y - gradColumn G₀ j σ y‖ ^ 2)) atTop (𝓝 0)

theorem isLocalReadingLimit_of (h12 : ReadingExistsHolds) (u : ℕ → XX) (u₀ : XX)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (u n) y) atTop (𝓝 (inner ℝ u₀ y)))
    (hc : ∀ R > 0, ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N,
      periodBallNorm R (fun σ y => (readingOf (u m)).1 σ y - (readingOf (u n)).1 σ y) < ε ∧
      ∀ j, periodBallNorm R (fun σ y => gradColumn (readingOf (u m)).2.1 j σ y
        - gradColumn (readingOf (u n)).2.1 j σ y) < ε) :
    IsLocalReadingLimit (fun n => (readingOf (u n)).1) (fun n => (readingOf (u n)).2.1)
      (readingOf u₀).1 (readingOf u₀).2.1 := fun R hR =>
  ⟨lt_of_le_of_lt ((Internal.HeldLimitReadings.velocity_family h12 R).bound u₀)
      ENNReal.ofReal_lt_top,
    fun j => lt_of_le_of_lt ((Internal.HeldLimitReadings.column_family h12 R j).bound u₀)
      ENNReal.ofReal_lt_top,
    (Internal.HeldLimitReadings.velocity_family h12 R).tendsto u u₀ hw
      fun ε hε => (hc R hR ε hε).imp fun _ hN m hm n hn => (hN m hm n hn).1,
    fun j => (Internal.HeldLimitReadings.column_family h12 R j).tendsto u u₀ hw
      fun ε hε => (hc R hR ε hε).imp fun _ hN m hm n hn => (hN m hm n hn).2 j⟩

theorem reading_tendsto_local (h1 : PeriodContinuityHolds) (h2 : LocalCompactnessHolds)
    (h9 : FreeInvHolds) (h12 : ReadingExistsHolds) (a b : ℝ) (ha : 0 < a)
    (P : ℕ → ℝ) (P₀ : ℝ) (f : ℕ → HH) (f₀ : HH) (hP : ∀ n, P n ∈ Set.Icc a b)
    (hP₀ : Tendsto P atTop (𝓝 P₀)) (C : ℝ) (hC : ∀ n, ‖f n‖ ≤ C)
    (hw : ∀ y, Tendsto (fun n => inner ℝ (f n) y) atTop (𝓝 (inner ℝ f₀ y))) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      IsLocalReadingLimit (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).1)
        (fun n => (readingOf (freeInv (P (ψ n)) (f (ψ n)))).2.1) (readingOf (freeInv P₀ f₀)).1
        (readingOf (freeInv P₀ f₀)).2.1 := by
  have hP₀a : P₀ ∈ Set.Icc a b := isClosed_Icc.mem_of_tendsto hP₀ (Eventually.of_forall hP)
  exact (h2 a b ha P f hP ⟨C, hC⟩).imp fun ψ hψ => ⟨hψ.1,
    isLocalReadingLimit_of h12 (fun n => freeInv (P (ψ n)) (f (ψ n))) (freeInv P₀ f₀)
      (h1 (fun n => P (ψ n)) P₀ (fun n => f (ψ n)) f₀ (ha.trans_le hP₀a.1)
        (fun n => ha.trans_le (hP (ψ n)).1) (hP₀.comp hψ.1.tendsto_atTop) ⟨C, fun n => hC (ψ n)⟩
        fun y => (hw y).comp hψ.1.tendsto_atTop) hψ.2⟩

end Internal.HeldLimit

end Breakdown.Cert

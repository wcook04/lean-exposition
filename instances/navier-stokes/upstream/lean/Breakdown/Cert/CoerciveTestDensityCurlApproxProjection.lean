import Breakdown.Cert.CoerciveTestDensityCurlApproxBase

open scoped ContDiff ENNReal
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.Coercive

namespace Internal.CurlGraphMollify

open Internal.TestDensityProof

private theorem slice_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Space → E} {n : WithTop ℕ∞} (h : ContDiff ℝ n (fun z : ℝ × Space => f z.1 z.2))
    (σ : ℝ) : ContDiff ℝ n (f σ) :=
  h.comp (contDiff_const.prodMk contDiff_id)

private theorem slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → Space → E} (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    fderiv ℝ (f σ) y =
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y) := hf.differentiable (by simp) _
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)).fderiv

private theorem hasCompactSupport_of_bound {E : Type*} [NormedAddCommGroup E] {f : Space → E} {R : ℝ}
    (h : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy =>
    h y (by simpa [Metric.mem_closedBall, not_le] using hy)

private theorem isPeriodicTestField_zero : IsPeriodicTestField (fun _ _ => (0 : Space)) :=
  ⟨contDiff_const, fun _ _ => rfl, ⟨0, fun _ _ _ => rfl⟩, fun σ y => by simp [divergenceAt]⟩

private theorem isPeriodicTestField_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) : IsPeriodicTestField (fun σ y => ψ₁ σ y + ψ₂ σ y) := by
  obtain ⟨R₁, hR₁⟩ := h₁.2.2.1
  obtain ⟨R₂, hR₂⟩ := h₂.2.2.1
  refine ⟨h₁.1.add h₂.1, fun σ y => by simp only [h₁.2.1 σ y, h₂.2.1 σ y],
    ⟨max R₁ R₂, fun σ y hy => by
      dsimp only
      rw [hR₁ σ y (lt_of_le_of_lt (le_max_left _ _) hy), hR₂ σ y (lt_of_le_of_lt (le_max_right _ _) hy),
        add_zero]⟩, fun σ y => ?_⟩
  have d1 := ((slice_contDiff h₁.1 σ).differentiable (by simp)) y
  have d2 := ((slice_contDiff h₂.1 σ).differentiable (by simp)) y
  have e1 := h₁.2.2.2 σ y
  have e2 := h₂.2.2.2 σ y
  unfold divergenceAt at e1 e2 ⊢
  dsimp only
  rw [show (fun y => ψ₁ σ y + ψ₂ σ y) = ψ₁ σ + ψ₂ σ from rfl, fderiv_add d1 d2]
  simp only [add_apply, PiLp.add_apply, Finset.sum_add_distrib, e1, e2, add_zero]

private theorem isPeriodicTestField_smul (c : ℝ) {ψ : ℝ → Space → Space} (h : IsPeriodicTestField ψ) :
    IsPeriodicTestField (fun σ y => c • ψ σ y) := by
  obtain ⟨R, hR⟩ := h.2.2.1
  refine ⟨h.1.const_smul c, fun σ y => by simp only [h.2.1 σ y],
    ⟨R, fun σ y hy => by dsimp only; rw [hR σ y hy, smul_zero]⟩, fun σ y => ?_⟩
  rw [divergenceAt_smul c ((slice_contDiff h.1 σ).differentiable (by simp)), h.2.2.2 σ y, mul_zero]

private theorem memLp_of_test {ψ : ℝ → Space → Space} (h : IsPeriodicTestField ψ) :
    MemLp (fun z : ℝ × Space => ψ z.1 z.2) 2 periodMeasure :=
  memLp_of_continuous h.1.continuous h.2.2.1

private theorem toL2_eq_of_ae {X : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure) (f : Lp Space 2 periodMeasure)
    (h : (f : ℝ × Space → Space) =ᵐ[periodMeasure] fun z => X z.1 z.2) : toL2 X = f :=
  Lp.ext ((coeFn_toL2 hX).trans h.symm)

private def testSubmodule : Submodule ℝ (Lp Space 2 periodMeasure) where
  carrier := {f | ∃ ψ, IsPeriodicTestField ψ ∧ toL2 ψ = f}
  zero_mem' := ⟨_, isPeriodicTestField_zero, toL2_eq_of_ae (memLp_of_test isPeriodicTestField_zero) _
    (Lp.coeFn_zero _ _ _)⟩
  add_mem' := by
    rintro _ _ ⟨ψ₁, h₁, rfl⟩ ⟨ψ₂, h₂, rfl⟩
    refine ⟨_, isPeriodicTestField_add h₁ h₂, toL2_eq_of_ae (memLp_of_test (isPeriodicTestField_add h₁ h₂))
      _ ?_⟩
    filter_upwards [Lp.coeFn_add (toL2 ψ₁) (toL2 ψ₂), coeFn_toL2 (memLp_of_test h₁),
      coeFn_toL2 (memLp_of_test h₂)] with z a b c
    rw [a, Pi.add_apply, b, c]
  smul_mem' := by
    rintro c _ ⟨ψ, h, rfl⟩
    refine ⟨_, isPeriodicTestField_smul c h, toL2_eq_of_ae (memLp_of_test (isPeriodicTestField_smul c h))
      _ ?_⟩
    filter_upwards [Lp.coeFn_smul c (toL2 ψ), coeFn_toL2 (memLp_of_test h)] with z a b
    rw [a, Pi.smul_apply, b]

private theorem pairing_eq_inner {X Y : ℝ → Space → Space}
    (hX : MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure)
    (hY : MemLp (fun z : ℝ × Space => Y z.1 z.2) 2 periodMeasure) :
    ∫ σ in Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) = inner ℝ (toL2 X) (toL2 Y) := by
  have hi : Integrable (fun z : ℝ × Space => inner ℝ (X z.1 z.2) (Y z.1 z.2)) periodMeasure := by
    refine (L2.integrable_inner (𝕜 := ℝ) (toL2 X) (toL2 Y)).congr ?_
    filter_upwards [coeFn_toL2 hX, coeFn_toL2 hY] with z a b
    rw [a, b]
  have hc : (fun z : ℝ × Space => inner ℝ (toL2 X z) (toL2 Y z)) =ᵐ[periodMeasure]
      fun z => inner ℝ (X z.1 z.2) (Y z.1 z.2) := by
    filter_upwards [coeFn_toL2 hX, coeFn_toL2 hY] with z a b
    rw [a, b]
  rw [L2.inner_def, integral_congr_ae hc, integral_prod _ hi]

private theorem coord_fderiv {w : Space → Space} (hw : Differentiable ℝ w) (i : Fin 3) (y v : Space) :
    fderiv ℝ (fun x => w x i) y v = fderiv ℝ w y v i := by
  have h := ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt).comp y (hw y).hasFDerivAt
  rw [show (fun x => w x i) = (EuclideanSpace.proj i : Space →L[ℝ] ℝ) ∘ w from rfl, h.fderiv]
  rfl

private theorem inner_gradient (w : Space) (c : Space → ℝ) (y : Space) :
    inner ℝ w (gradientAt c y) = ∑ i : Fin 3, w i * fderiv ℝ c y (unitVector i) := by
  unfold gradientAt unitVector
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, EuclideanSpace.inner_single_right]
  simp [mul_comm]

private theorem integral_inner_gradient {w : Space → Space} {c : Space → ℝ} (hw : ContDiff ℝ ∞ w)
    (hws : HasCompactSupport w) (hdiv : ∀ y, divergenceAt w y = 0) (hc : ContDiff ℝ ∞ c)
    (hcs : HasCompactSupport c) : ∫ y, inner ℝ (w y) (gradientAt c y) = 0 := by
  have hwd : Differentiable ℝ w := hw.differentiable (by simp)
  have hcd : Differentiable ℝ c := hc.differentiable (by simp)
  have hwi : ∀ i : Fin 3, ContDiff ℝ ∞ (fun x => w x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hw
  have hwis : ∀ i : Fin 3, HasCompactSupport (fun x => w x i) := fun i =>
    hws.comp_left (g := fun v : Space => v i) rfl
  have hdc : ∀ v, Continuous (fun x => fderiv ℝ c x v) := fun v =>
    (hc.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdw : ∀ i : Fin 3, ∀ v, Continuous (fun x => fderiv ℝ (fun x => w x i) x v) := fun i v =>
    ((hwi i).continuous_fderiv (by simp)).clm_apply continuous_const
  have step : ∀ i : Fin 3, ∫ y, w y i * fderiv ℝ c y (unitVector i) =
      -∫ y, fderiv ℝ w y (unitVector i) i * c y := by
    intro i
    have e := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun x => w x i) (g := c) (v := unitVector i)
      (((hdw i _).mul hc.continuous).integrable_of_hasCompactSupport (hcs.mul_left))
      (((hwi i).continuous.mul (hdc _)).integrable_of_hasCompactSupport ((hwis i).mul_right))
      (((hwi i).continuous.mul hc.continuous).integrable_of_hasCompactSupport ((hwis i).mul_right))
      (fun x _ => ((hwi i).differentiable (by simp)) x) (fun x _ => hcd x)
    rw [e]
    simp only [coord_fderiv hwd]
  have hi1 : ∀ i : Fin 3, Integrable (fun y => w y i * fderiv ℝ c y (unitVector i)) := by
    intro i
    exact ((hwi i).continuous.mul (hdc _)).integrable_of_hasCompactSupport ((hwis i).mul_right)
  have hi2 : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ w y (unitVector i) i * c y) := by
    intro i
    refine (((hdw i (unitVector i)).mul hc.continuous).integrable_of_hasCompactSupport
      (hcs.mul_left)).congr (ae_of_all _ fun x => ?_)
    simp only [coord_fderiv hwd, Pi.mul_apply]
  simp_rw [inner_gradient]
  rw [integral_finsetSum _ (fun i _ => hi1 i)]
  simp_rw [step]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => hi2 i)]
  have hz : ∀ y, ∑ i : Fin 3, fderiv ℝ w y (unitVector i) i * c y = 0 := fun y => by
    rw [← Finset.sum_mul]
    have := hdiv y
    unfold divergenceAt at this
    rw [this, zero_mul]
  simp [hz]

private theorem gradient_continuous' {q : ℝ → Space → ℝ}
    (hq : ContDiff ℝ ∞ (fun z : ℝ × Space => q z.1 z.2)) :
    Continuous (fun z : ℝ × Space => gradientAt (q z.1) z.2) := by
  have e : (fun z : ℝ × Space => gradientAt (q z.1) z.2) = fun z => ∑ i : Fin 3,
      fderiv ℝ (fun z : ℝ × Space => q z.1 z.2) z (ContinuousLinearMap.inr ℝ ℝ Space (unitVector i)) •
        unitVector i := by
    funext z
    unfold gradientAt
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [slice_fderiv (hq.of_le (by simp))]
    rfl
  rw [e]
  exact continuous_finsetSum _ fun i _ =>
    ((hq.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

private theorem gradient_bound {q : ℝ → Space → ℝ} {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → q σ y = 0) :
    ∀ σ y, R < ‖y‖ → gradientAt (q σ) y = 0 := by
  intro σ y hy
  have hev : q σ =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with x hx
    exact hR σ x hx
  unfold gradientAt
  rw [hev.fderiv_eq]
  simp

private theorem lintegral_sq_eq (g : Lp Space 2 periodMeasure) :
    ∫⁻ z, ENNReal.ofReal (‖g z‖ ^ 2) ∂periodMeasure = ENNReal.ofReal (‖g‖ ^ 2) := by
  have hi : Integrable (fun z => ‖g z‖ ^ 2) periodMeasure :=
    (L2.integrable_inner (𝕜 := ℝ) g g).congr (ae_of_all _ fun z => real_inner_self_eq_norm_sq _)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _)]
  congr 1
  rw [← real_inner_self_eq_norm_sq g, L2.inner_def]
  exact integral_congr_ae (ae_of_all _ fun z => (real_inner_self_eq_norm_sq (g z)).symm)

theorem exists_solenoidal_part_seq (F : ℝ → Space → Space)
    (_hFv : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (_hp : IsTimePeriodic F)
    (hFm : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure) :
    ∃ Q' : ℝ → Space → Space, IsSolenoidalPartOf F Q' ∧
      ∃ φ : ℕ → ℝ → Space → Space, (∀ n, IsPeriodicTestField (φ n)) ∧
        Tendsto (fun n => periodLIntegral (fun σ y => ‖φ n σ y - Q' σ y‖ ^ 2)) atTop (nhds 0) := by
  set V := testSubmodule.topologicalClosure with hVdef
  have : CompleteSpace V := (Submodule.isClosed_topologicalClosure testSubmodule).completeSpace_coe
  set Q : Lp Space 2 periodMeasure := V.starProjection (toL2 F) with hQdef
  have hQV : Q ∈ V := V.starProjection_apply_mem _
  set Q' : ℝ → Space → Space := fun σ y => Q (Int.fract σ, y) with hQ'def
  have hQ'meas : StronglyMeasurable (fun z : ℝ × Space => Q' z.1 z.2) :=
    (Lp.stronglyMeasurable Q).comp_measurable ((measurable_fract.comp measurable_fst).prodMk measurable_snd)
  have hIco : ∀ᵐ z ∂periodMeasure, z.1 ∈ Ico (0 : ℝ) 1 := by
    have h1 : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), σ ∈ Ico (0 : ℝ) 1 := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have hne : ∀ᵐ σ : ℝ, σ ≠ 1 := by
        simp [ae_iff]
      filter_upwards [hne] with σ hσ hσ'
      exact ⟨hσ'.1, lt_of_le_of_ne hσ'.2 hσ⟩
    exact Measure.quasiMeasurePreserving_fst.ae h1
  have hae : (fun z : ℝ × Space => Q' z.1 z.2) =ᵐ[periodMeasure] Q := by
    filter_upwards [hIco] with z hz
    simp only [hQ'def, Int.fract_eq_self.2 hz]
  have hQ'm : MemLp (fun z : ℝ × Space => Q' z.1 z.2) 2 periodMeasure := (Lp.memLp Q).ae_eq hae.symm
  have htoQ : toL2 Q' = Q := toL2_eq_of_ae hQ'm Q hae.symm
  have hint : ∀ {X : ℝ → Space → Space}, MemLp (fun z : ℝ × Space => X z.1 z.2) 2 periodMeasure →
      periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ := by
    intro X hX
    have hi := (memLp_two_iff_integrable_sq_norm hX.1).1 hX
    rw [periodLIntegral_eq_lintegral (hX.1.norm.aemeasurable.pow_const 2).ennreal_ofReal]
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)).1 hi.2
  refine ⟨Q', ⟨hQ'meas.aestronglyMeasurable, fun σ y => by simp only [hQ'def, Int.fract_add_one],
    hint hQ'm, ?_, ?_⟩, ?_⟩
  · intro q hq
    obtain ⟨R, hR⟩ := hq.2.2
    have hG : MemLp (fun z : ℝ × Space => gradientAt (q z.1) z.2) 2 periodMeasure :=
      memLp_of_continuous (gradient_continuous' hq.1) ⟨R, gradient_bound hR⟩
    rw [pairing_eq_inner hQ'm hG, htoQ]
    have hzero : ∀ f ∈ testSubmodule, inner ℝ f (toL2 (fun σ y => gradientAt (q σ) y)) = 0 := by
      rintro _ ⟨ψ, hψ, rfl⟩
      rw [← pairing_eq_inner (memLp_of_test hψ) hG]
      obtain ⟨Rψ, hRψ⟩ := hψ.2.2.1
      have hs : ∀ σ, ∫ y, inner ℝ (ψ σ y) (gradientAt (q σ) y) = 0 := fun σ =>
        integral_inner_gradient (slice_contDiff hψ.1 σ) (hasCompactSupport_of_bound (hRψ σ))
          (hψ.2.2.2 σ) (slice_contDiff hq.1 σ) (hasCompactSupport_of_bound (hR σ))
      simp [hs]
    have hcl : IsClosed {f : Lp Space 2 periodMeasure | inner ℝ f (toL2 (fun σ y => gradientAt (q σ) y)) = 0} :=
      isClosed_eq (continuous_id.inner continuous_const) continuous_const
    have hsub : (testSubmodule : Set (Lp Space 2 periodMeasure)) ⊆
        {f | inner ℝ f (toL2 (fun σ y => gradientAt (q σ) y)) = 0} := fun f hf => hzero f hf
    have := closure_minimal hsub hcl
    rw [← Submodule.topologicalClosure_coe] at this
    exact this hQV
  · intro ψ hψ
    rw [pairing_eq_inner hQ'm (memLp_of_test hψ), pairing_eq_inner hFm (memLp_of_test hψ), htoQ]
    have hmem : toL2 ψ ∈ V := Submodule.le_topologicalClosure _ ⟨ψ, hψ, rfl⟩
    have h0 := V.starProjection_inner_eq_zero (toL2 F) (toL2 ψ) hmem
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0.symm
  · have hcQ : Q ∈ closure (testSubmodule : Set (Lp Space 2 periodMeasure)) := by
      rw [← Submodule.topologicalClosure_coe]
      exact hQV
    obtain ⟨f, hfS, hf⟩ := mem_closure_iff_seq_limit.1 hcQ
    choose φ hφ hφeq using hfS
    refine ⟨φ, hφ, ?_⟩
    have he : ∀ n, periodLIntegral (fun σ y => ‖φ n σ y - Q' σ y‖ ^ 2) = ENNReal.ofReal (‖f n - Q‖ ^ 2) := by
      intro n
      rw [periodLIntegral_eq_lintegral (((memLp_of_test (hφ n)).1.sub hQ'm.1).norm.aemeasurable.pow_const
        2).ennreal_ofReal, ← lintegral_sq_eq]
      refine lintegral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (f n) Q, coeFn_toL2 (memLp_of_test (hφ n)), hae] with z a b c
      rw [a, Pi.sub_apply, ← hφeq n, b, ← c]
    simp_rw [he]
    have hn : Tendsto (fun n => ‖f n - Q‖) atTop (nhds 0) := tendsto_iff_norm_sub_tendsto_zero.1 hf
    have h2 : Tendsto (fun n => ‖f n - Q‖ ^ 2) atTop (nhds 0) := by simpa using hn.pow 2
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    rw [ENNReal.ofReal_zero] at this
    exact this

end Internal.CurlGraphMollify

end Breakdown.Coercive

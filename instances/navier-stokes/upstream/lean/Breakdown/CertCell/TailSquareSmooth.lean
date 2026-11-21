import Breakdown.CertCell.TailStatements

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

def SquareExteriorAxialSmoothStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → (∀ x, g (x, 0) = 0) →
    ENNReal.ofReal 2 * ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (g p ^ 2 / planeRadius p ^ 2 * p.1)
      ≤ ∫⁻ p in planeSquareExterior R,
          ENNReal.ofReal ((fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1)

def SquareExteriorTransverseSmoothStatement : Prop :=
  ∀ R : ℝ, 0 < R → ∀ g : ℝ × ℝ → ℝ, ContDiff ℝ 1 g → HasCompactSupport g → (∀ z, g (0, z) = 0) →
    ENNReal.ofReal 2 * ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (g p ^ 2 / planeRadius p ^ 2 * p.1)
      ≤ ∫⁻ p in planeSquareExterior R,
          ENNReal.ofReal ((fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2 + g p ^ 2 / p.1 ^ 2) * p.1)

def SquareExteriorSmoothStatement : Prop :=
  SquareExteriorAxialSmoothStatement ∧ SquareExteriorTransverseSmoothStatement

private lemma partial_fst {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) {d : ℝ}
    (hd : HasDerivAt (fun t => f (t, x.2)) d x.1) : fderiv ℝ f x (1, 0) = d := by
  have h1 : HasDerivAt (fun t : ℝ => (t, x.2)) ((1 : ℝ), (0 : ℝ)) x.1 :=
    (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (t, x.2)) x.1 h1).unique hd

private lemma partial_snd {f : ℝ × ℝ → ℝ} {x : ℝ × ℝ} (hf : DifferentiableAt ℝ f x) {d : ℝ}
    (hd : HasDerivAt (fun t => f (x.1, t)) d x.2) : fderiv ℝ f x (0, 1) = d := by
  have h1 : HasDerivAt (fun t : ℝ => (x.1, t)) ((0 : ℝ), (1 : ℝ)) x.2 :=
    (hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (x.1, t)) x.2 h1).unique hd

private lemma line_fst {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    HasDerivAt (fun t => g (t, x.2)) (fderiv ℝ g x (1, 0)) x.1 :=
  (hg x).hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (t, x.2)) x.1
    ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))

private lemma line_snd {g : ℝ × ℝ → ℝ} (hg : Differentiable ℝ g) (x : ℝ × ℝ) :
    HasDerivAt (fun t => g (x.1, t)) (fderiv ℝ g x (0, 1)) x.2 :=
  (hg x).hasFDerivAt.comp_hasDerivAt (f := fun t : ℝ => (x.1, t)) x.2
    ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))

private lemma box_divergence {g W₁ W₂ D₁ D₂ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hg : ContDiff ℝ 1 g) (hW₁ : ContDiffOn ℝ 1 W₁ U) (hW₂ : ContDiffOn ℝ 1 W₂ U)
    (hD₁ : ∀ x ∈ U, HasDerivAt (fun t => W₁ (t, x.2)) (D₁ x) x.1)
    (hD₂ : ∀ x ∈ U, HasDerivAt (fun t => W₂ (x.1, t)) (D₂ x) x.2)
    {a₁ a₂ b₁ b₂ : ℝ} (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂) (hsub : Icc (a₁, a₂) (b₁, b₂) ⊆ U) :
    IntegrableOn (fun x => 2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x)) (Icc (a₁, a₂) (b₁, b₂)) ∧
    ∫ x in Icc (a₁, a₂) (b₁, b₂), (2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x)) =
      (((∫ t in a₁..b₁, g (t, b₂) ^ 2 * W₂ (t, b₂)) - ∫ t in a₁..b₁, g (t, a₂) ^ 2 * W₂ (t, a₂))
        + ∫ t in a₂..b₂, g (b₁, t) ^ 2 * W₁ (b₁, t)) - ∫ t in a₂..b₂, g (a₁, t) ^ 2 * W₁ (a₁, t) := by
  have hF₁ : ContDiffOn ℝ 1 (fun x => g x ^ 2 * W₁ x) U := (hg.contDiffOn.pow 2).mul hW₁
  have hF₂ : ContDiffOn ℝ 1 (fun x => g x ^ 2 * W₂ x) U := (hg.contDiffOn.pow 2).mul hW₂
  have hd₁ : ∀ x ∈ U, DifferentiableAt ℝ (fun x => g x ^ 2 * W₁ x) x := fun x hx =>
    (hF₁.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hd₂ : ∀ x ∈ U, DifferentiableAt ℝ (fun x => g x ^ 2 * W₂ x) x := fun x hx =>
    (hF₂.differentiableOn one_ne_zero x hx).differentiableAt (hU.mem_nhds hx)
  have hgd : Differentiable ℝ g := hg.differentiable one_ne_zero
  have heq : ∀ x ∈ U, fderiv ℝ (fun x => g x ^ 2 * W₁ x) x (1, 0)
      + fderiv ℝ (fun x => g x ^ 2 * W₂ x) x (0, 1)
      = 2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x) := by
    intro x hx
    rw [partial_fst (hd₁ x hx) (((line_fst hgd x).pow 2).mul (hD₁ x hx)),
      partial_snd (hd₂ x hx) (((line_snd hgd x).pow 2).mul (hD₂ x hx))]
    norm_num
    ring
  have hi : IntegrableOn (fun x => fderiv ℝ (fun x => g x ^ 2 * W₁ x) x (1, 0)
      + fderiv ℝ (fun x => g x ^ 2 * W₂ x) x (0, 1)) (Icc (a₁, a₂) (b₁, b₂)) := by
    refine ContinuousOn.integrableOn_compact isCompact_Icc (ContinuousOn.mono ?_ hsub)
    exact ((hF₁.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).add
      ((hF₂.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const)
  have hcongr := setIntegral_congr_fun (μ := volume) measurableSet_Icc (fun x hx => heq x (hsub hx))
  refine ⟨hi.congr_fun (fun x hx => heq x (hsub hx)) measurableSet_Icc, ?_⟩
  rw [← hcongr]
  have hint : ∀ x ∈ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂ \ (∅ : Set (ℝ × ℝ)), x ∈ U := fun x hx =>
    hsub ⟨⟨hx.1.1.1.le, hx.1.2.1.le⟩, ⟨hx.1.1.2.le, hx.1.2.2.le⟩⟩
  exact integral_divergence_prod_Icc_of_hasFDerivAt_off_countable_of_le _ _ _ _ (a₁, a₂) (b₁, b₂)
    ⟨h₁, h₂⟩ ∅ countable_empty (hF₁.continuousOn.mono hsub) (hF₂.continuousOn.mono hsub)
    (fun x hx => (hd₁ x (hint x hx)).hasFDerivAt) (fun x hx => (hd₂ x (hint x hx)).hasFDerivAt) hi


private lemma quad_le {ϱ g a b W₁ W₂ : ℝ} (hϱ : 0 < ϱ) :
    2 * g * (a * W₁ + b * W₂) ≤ (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ) := by
  have h : (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * ((W₁ ^ 2 + W₂ ^ 2) / ϱ) - 2 * g * (a * W₁ + b * W₂)
      = ((ϱ * a - g * W₁) ^ 2 + (ϱ * b - g * W₂) ^ 2) / ϱ := by
    field_simp
    ring
  have : 0 ≤ ((ϱ * a - g * W₁) ^ 2 + (ϱ * b - g * W₂) ^ 2) / ϱ := by positivity
  linarith

private lemma axial_deriv_fst (x : ℝ × ℝ) (hx : 0 < x.2) :
    HasDerivAt (fun t => -2 * t ^ 2 / (t ^ 2 + x.2 ^ 2))
      (-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.1 := by
  have hq : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by positivity
  refine (((hasDerivAt_pow 2 x.1).const_mul (-2)).fun_div
    ((hasDerivAt_pow 2 x.1).add_const (x.2 ^ 2)) hq).congr_deriv ?_
  field_simp
  ring

private lemma axial_deriv_snd (x : ℝ × ℝ) (hx : 0 < x.2) :
    HasDerivAt (fun t => x.1 * (x.1 ^ 2 - t ^ 2) / (t * (x.1 ^ 2 + t ^ 2)))
      (x.1 * (x.2 ^ 4 - 4 * x.1 ^ 2 * x.2 ^ 2 - x.1 ^ 4) / (x.2 ^ 2 * (x.1 ^ 2 + x.2 ^ 2) ^ 2)) x.2 := by
  have h2 : x.2 ≠ 0 := hx.ne'
  have h3 : x.1 ^ 2 + x.2 ^ 2 ≠ 0 := by positivity
  have hq : x.2 * (x.1 ^ 2 + x.2 ^ 2) ≠ 0 := mul_ne_zero h2 h3
  refine ((((hasDerivAt_pow 2 x.2).const_sub (x.1 ^ 2)).const_mul x.1).fun_div
    ((hasDerivAt_id' x.2).mul ((hasDerivAt_pow 2 x.2).const_add (x.1 ^ 2))) hq).congr_deriv ?_
  simp only [Pi.mul_apply]
  field_simp
  ring

private lemma cross_deriv_fst (x : ℝ × ℝ) (hx : 0 < x.1 ^ 2 + x.2 ^ 2) :
    HasDerivAt (fun t => (x.2 ^ 2 - t ^ 2) / (t ^ 2 + x.2 ^ 2))
      (-4 * x.1 * x.2 ^ 2 / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.1 := by
  refine (((hasDerivAt_pow 2 x.1).const_sub (x.2 ^ 2)).fun_div
    ((hasDerivAt_pow 2 x.1).add_const (x.2 ^ 2)) hx.ne').congr_deriv ?_
  have := hx.ne'
  field_simp
  ring

private lemma cross_deriv_snd (x : ℝ × ℝ) (hx : 0 < x.1 ^ 2 + x.2 ^ 2) :
    HasDerivAt (fun t => -2 * x.1 * t / (x.1 ^ 2 + t ^ 2))
      (-2 * x.1 * (x.1 ^ 2 - x.2 ^ 2) / (x.1 ^ 2 + x.2 ^ 2) ^ 2) x.2 := by
  refine (((hasDerivAt_id' x.2).const_mul (-2 * x.1)).fun_div
    ((hasDerivAt_pow 2 x.2).const_add (x.1 ^ 2)) hx.ne').congr_deriv ?_
  have := hx.ne'
  field_simp
  ring

private lemma axial_pointwise {ϱ z g a b : ℝ} (hϱ : 0 ≤ ϱ) (hz : 0 < z) :
    2 * g * (a * (-2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2)) + b * (ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))))
      + g ^ 2 * (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2
        + ϱ * (z ^ 4 - 4 * ϱ ^ 2 * z ^ 2 - ϱ ^ 4) / (z ^ 2 * (ϱ ^ 2 + z ^ 2) ^ 2))
      ≤ (a ^ 2 + b ^ 2) * ϱ - 2 * (g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ) := by
  rcases hϱ.eq_or_lt with h | h
  · subst h; simp
  have hq : 0 < ϱ ^ 2 + z ^ 2 := by positivity
  have key := quad_le (g := g) (a := a) (b := b) (W₁ := -2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2))
    (W₂ := ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))) h
  have hid : ((-2 * ϱ ^ 2 / (ϱ ^ 2 + z ^ 2)) ^ 2 + (ϱ * (ϱ ^ 2 - z ^ 2) / (z * (ϱ ^ 2 + z ^ 2))) ^ 2) / ϱ
      + (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2
        + ϱ * (z ^ 4 - 4 * ϱ ^ 2 * z ^ 2 - ϱ ^ 4) / (z ^ 2 * (ϱ ^ 2 + z ^ 2) ^ 2))
      = -2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by
    field_simp
    ring
  have : g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ = g ^ 2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by ring
  rw [this]
  nlinarith [hid, key]

private lemma cross_pointwise {ϱ z g a b : ℝ} (hϱ : 0 < ϱ) :
    2 * g * (a * ((z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2)) + b * (-2 * ϱ * z / (ϱ ^ 2 + z ^ 2)))
      + g ^ 2 * (-4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2 + -2 * ϱ * (ϱ ^ 2 - z ^ 2) / (ϱ ^ 2 + z ^ 2) ^ 2)
      ≤ (a ^ 2 + b ^ 2 + g ^ 2 / ϱ ^ 2) * ϱ - 2 * (g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ) := by
  have key := quad_le (g := g) (a := a) (b := b) (W₁ := (z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2))
    (W₂ := -2 * ϱ * z / (ϱ ^ 2 + z ^ 2)) hϱ
  have hid : (((z ^ 2 - ϱ ^ 2) / (ϱ ^ 2 + z ^ 2)) ^ 2 + (-2 * ϱ * z / (ϱ ^ 2 + z ^ 2)) ^ 2) / ϱ
      = ϱ / ϱ ^ 2 := by
    field_simp
    ring
  have hid2 : -4 * ϱ * z ^ 2 / (ϱ ^ 2 + z ^ 2) ^ 2 + -2 * ϱ * (ϱ ^ 2 - z ^ 2) / (ϱ ^ 2 + z ^ 2) ^ 2
      = -2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by
    field_simp
    ring
  have e1 : g ^ 2 / (ϱ ^ 2 + z ^ 2) * ϱ = g ^ 2 * (ϱ / (ϱ ^ 2 + z ^ 2)) := by ring
  have e2 : (a ^ 2 + b ^ 2 + g ^ 2 / ϱ ^ 2) * ϱ = (a ^ 2 + b ^ 2) * ϱ + g ^ 2 * (ϱ / ϱ ^ 2) := by ring
  rw [e1, e2, hid2]
  rw [hid] at key
  nlinarith [key]

private lemma sq_planeRadius (p : ℝ × ℝ) : planeRadius p ^ 2 = p.1 ^ 2 + p.2 ^ 2 :=
  Real.sq_sqrt (by positivity)

private lemma measurableSet_exterior (R ε : ℝ) :
    MeasurableSet (planeSquareExterior R ∩ {p : ℝ × ℝ | ε < p.2}) :=
  ((measurableSet_Ioi.prod measurableSet_Ioi).inter
    ((measurableSet_lt measurable_const measurable_fst).union
      (measurableSet_lt measurable_const measurable_snd))).inter
    (measurableSet_lt measurable_const measurable_snd)

private lemma support_bound {g : ℝ × ℝ → ℝ} (hs : HasCompactSupport g) (R : ℝ) :
    ∃ L, R < L ∧ ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → g p = 0 ∧ fderiv ℝ g p = 0 := by
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hs.isCompact.isBounded
  refine ⟨max r R + 1, by linarith [le_max_right r R], fun p hp => ?_⟩
  have hn : p ∉ tsupport g := by
    intro h
    have h1 : ‖p‖ ≤ r := by simpa using hr h
    have h2 := le_max_left r R
    rcases hp with hp | hp
    · have := (le_abs_self p.1).trans ((Real.norm_eq_abs p.1).symm ▸ norm_fst_le p)
      linarith
    · have := (le_abs_self p.2).trans ((Real.norm_eq_abs p.2).symm ▸ norm_snd_le p)
      linarith
  exact ⟨image_eq_zero_of_notMem_tsupport hn, fderiv_of_notMem_tsupport ℝ hn⟩

private lemma plane_bound {g : ℝ × ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K g)
    (h0 : ∀ x, g (x, 0) = 0) (p : ℝ × ℝ) : |g p| ≤ K * |p.2| := by
  have := hK.dist_le_mul p (p.1, 0)
  rw [h0, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at this
  simpa using this

private lemma axis_bound {g : ℝ × ℝ → ℝ} {K : NNReal} (hK : LipschitzWith K g)
    (h0 : ∀ z, g (0, z) = 0) (p : ℝ × ℝ) : |g p| ≤ K * |p.1| := by
  have := hK.dist_le_mul p (0, p.2)
  rw [h0, Prod.dist_eq, Real.dist_eq, Real.dist_eq, Real.dist_eq] at this
  simpa using this

private lemma integrableOn_bounded {φ : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hm : Measurable φ) {L C : ℝ} (h0 : ∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2)
    (hC : ∀ p ∈ s, p.1 ≤ L → |φ p| ≤ C) (hz : ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → φ p = 0) :
    IntegrableOn φ s := by
  have hK : IntegrableOn φ (s ∩ Icc (0, 0) (L, L)) := by
    refine Measure.integrableOn_of_bounded (M := C) ?_ hm.aestronglyMeasurable ?_
    · exact ((measure_mono inter_subset_right).trans_lt isCompact_Icc.measure_lt_top).ne
    · filter_upwards [ae_restrict_mem (hs.inter measurableSet_Icc)] with p hp
      rw [Real.norm_eq_abs]
      exact hC p hp.1 hp.2.2.1
  refine hK.of_forall_sdiff_eq_zero hs (fun p hp => hz p ?_)
  by_contra h
  push Not at h
  exact hp.2 ⟨hp.1, ⟨(h0 p hp.1).1, (h0 p hp.1).2⟩, h.1.le, h.2.le⟩

private lemma split_exterior {φ : ℝ × ℝ → ℝ} {R L ε : ℝ} (hε : 0 ≤ ε) (hεR : ε < R)
    (hz : ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → φ p = 0)
    (h1 : IntegrableOn φ (Icc (0, R) (L, L))) (h2 : IntegrableOn φ (Icc (R, ε) (L, R))) :
    ∫ p in planeSquareExterior R ∩ {p | ε < p.2}, φ p
      = (∫ p in Icc (0, R) (L, L), φ p) + ∫ p in Icc (R, ε) (L, R), φ p := by
  have e1 : (Ioc 0 L ×ˢ Ioc R L : Set (ℝ × ℝ)) =ᵐ[volume] Icc ((0 : ℝ), R) (L, L) := by
    rw [Icc_prod_eq]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioc_ae_eq_Icc
  have e2 : (Ioc R L ×ˢ Ioc ε R : Set (ℝ × ℝ)) =ᵐ[volume] Icc (R, ε) (L, R) := by
    rw [Icc_prod_eq]
    exact Measure.set_prod_ae_eq Ioc_ae_eq_Icc Ioc_ae_eq_Icc
  have hsub : Ioc 0 L ×ˢ Ioc R L ∪ Ioc R L ×ˢ Ioc ε R ⊆ planeSquareExterior R ∩ {p | ε < p.2} := by
    rintro p (⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ | ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩)
    · exact ⟨⟨⟨h1, mem_Ioi.2 (by linarith)⟩, Or.inr h3⟩, show ε < p.2 by linarith⟩
    · exact ⟨⟨⟨mem_Ioi.2 (by linarith), mem_Ioi.2 (by linarith)⟩, Or.inl h1⟩, h3⟩
  have hdis : Disjoint (Ioc 0 L ×ˢ Ioc R L : Set (ℝ × ℝ)) (Ioc R L ×ˢ Ioc ε R) :=
    Set.disjoint_left.2 fun p h1 h2 => by linarith [h1.2.1, h2.2.2]
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (measurableSet_exterior R ε) hsub ?_,
    setIntegral_union hdis (measurableSet_Ioc.prod measurableSet_Ioc) (h1.congr_set_ae e1)
      (h2.congr_set_ae e2), setIntegral_congr_set e1, setIntegral_congr_set e2]
  rintro p ⟨⟨⟨⟨hp1, hp2⟩, hp3⟩, hp4⟩, hn⟩
  refine hz p ?_
  by_contra h
  push Not at h
  apply hn
  by_cases hR : R < p.2
  · exact Or.inl ⟨⟨hp1, h.1.le⟩, ⟨hR, h.2.le⟩⟩
  · push Not at hR
    exact Or.inr ⟨⟨hp3.resolve_right (not_lt.2 hR), h.1.le⟩, ⟨hp4, hR⟩⟩

private lemma iint_zero {f : ℝ → ℝ} {a b : ℝ} (h : ∀ t, f t = 0) : ∫ t in a..b, f t = 0 := by
  simp [h]

private lemma line_integrable {g W : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hg : Continuous g)
    (hW : ContinuousOn W U) {c a b : ℝ} (h : ∀ t ∈ uIcc a b, (t, c) ∈ U) :
    IntervalIntegrable (fun t => g (t, c) ^ 2 * W (t, c)) volume a b :=
  ContinuousOn.intervalIntegrable
    (((hg.comp (continuous_id.prodMk continuous_const)).pow 2).continuousOn.mul
      (hW.comp (continuous_id.prodMk continuous_const).continuousOn h))

private lemma two_box {g W₁ W₂ D₁ D₂ φ : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hg : ContDiff ℝ 1 g) (hW₁ : ContDiffOn ℝ 1 W₁ U) (hW₂ : ContDiffOn ℝ 1 W₂ U)
    (hD₁ : ∀ x ∈ U, HasDerivAt (fun t => W₁ (t, x.2)) (D₁ x) x.1)
    (hD₂ : ∀ x ∈ U, HasDerivAt (fun t => W₂ (x.1, t)) (D₂ x) x.2)
    {R L ε : ℝ} (hε : 0 ≤ ε) (hεR : ε < R) (hRL : R < L)
    (hT : Icc (0, R) (L, L) ⊆ U) (hS : Icc (R, ε) (L, R) ⊆ U)
    (hgL : ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → g p = 0)
    (hφz : ∀ p : ℝ × ℝ, (L ≤ p.1 ∨ L ≤ p.2) → φ p = 0)
    (hφT : IntegrableOn φ (Icc (0, R) (L, L))) (hφS : IntegrableOn φ (Icc (R, ε) (L, R)))
    (hle : ∀ x ∈ Icc (0, R) (L, L) ∪ Icc (R, ε) (L, R),
      2 * g x * (fderiv ℝ g x (1, 0) * W₁ x + fderiv ℝ g x (0, 1) * W₂ x)
        + g x ^ 2 * (D₁ x + D₂ x) ≤ φ x)
    (haxis : ∀ t, g (0, t) ^ 2 * W₁ (0, t) = 0) :
    -(∫ t in (0)..R, g (t, R) ^ 2 * W₂ (t, R)) - (∫ t in R..L, g (t, ε) ^ 2 * W₂ (t, ε))
        - ∫ t in ε..R, g (R, t) ^ 2 * W₁ (R, t)
      ≤ ∫ p in planeSquareExterior R ∩ {p | ε < p.2}, φ p := by
  have hR : 0 < R := hε.trans_lt hεR
  obtain ⟨iT, eT⟩ := box_divergence hU hg hW₁ hW₂ hD₁ hD₂ (hR.le.trans hRL.le) hRL.le hT
  obtain ⟨iS, eS⟩ := box_divergence hU hg hW₁ hW₂ hD₁ hD₂ hRL.le hεR.le hS
  have mT := setIntegral_mono_on iT hφT measurableSet_Icc (fun x hx => hle x (Or.inl hx))
  have mS := setIntegral_mono_on iS hφS measurableSet_Icc (fun x hx => hle x (Or.inr hx))
  rw [eT] at mT
  rw [eS] at mS
  rw [split_exterior hε hεR hφz hφT hφS]
  have z1 : ∫ t in (0 : ℝ)..L, g (t, L) ^ 2 * W₂ (t, L) = 0 :=
    iint_zero fun t => by simp [hgL (t, L) (Or.inr le_rfl)]
  have z2 : ∫ t in R..L, g (L, t) ^ 2 * W₁ (L, t) = 0 :=
    iint_zero fun t => by simp [hgL (L, t) (Or.inl le_rfl)]
  have z3 : ∫ t in R..L, g (0, t) ^ 2 * W₁ (0, t) = 0 := iint_zero haxis
  have z4 : ∫ t in ε..R, g (L, t) ^ 2 * W₁ (L, t) = 0 :=
    iint_zero fun t => by simp [hgL (L, t) (Or.inl le_rfl)]
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    (line_integrable (c := R) (a := 0) (b := R) hg.continuous hW₂.continuousOn fun t ht => by
      rw [uIcc_of_le hR.le] at ht
      exact hT ⟨⟨ht.1, le_rfl⟩, ⟨by linarith [ht.2], hRL.le⟩⟩)
    (line_integrable (c := R) (a := R) (b := L) hg.continuous hW₂.continuousOn fun t ht => by
      rw [uIcc_of_le hRL.le] at ht
      exact hT ⟨⟨by linarith [ht.1], le_rfl⟩, ⟨ht.2, hRL.le⟩⟩)
  rw [z1, z2, z3, ← hsplit] at mT
  rw [z4] at mS
  linarith

private lemma measurableSet_square (R : ℝ) : MeasurableSet (planeSquareExterior R) :=
  (measurableSet_Ioi.prod measurableSet_Ioi).inter
    ((measurableSet_lt measurable_const measurable_fst).union
      (measurableSet_lt measurable_const measurable_snd))

private lemma grad_integrable {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g) :
    Integrable (fun p : ℝ × ℝ => (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1) := by
  have c1 : Continuous fun p => fderiv ℝ g p (1, 0) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have c2 : Continuous fun p => fderiv ℝ g p (0, 1) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine Continuous.integrable_of_hasCompactSupport (by fun_prop) ?_
  exact (hs.fderiv (𝕜 := ℝ)).mono' (fun p hp => subset_tsupport _ fun h => hp (by simp [h]))

private lemma ratio_integrable {R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) {s : Set (ℝ × ℝ)} (hsm : MeasurableSet s)
    (h0 : ∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2) (hq : ∀ p ∈ s, R ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2) :
    IntegrableOn (fun p : ℝ × ℝ => g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1) s := by
  obtain ⟨L, -, hL⟩ := support_bound hs R
  obtain ⟨M, hM⟩ := hg.continuous.bounded_above_of_compact_support hs
  have hgm : Measurable g := hg.continuous.measurable
  refine integrableOn_bounded hsm (by fun_prop) (L := L) (C := M ^ 2 / R ^ 2 * L) h0
    (fun p hp hpL => ?_) (fun p hp => by simp [(hL p hp).1])
  have hp1 := (h0 p hp).1
  have hq' := hq p hp
  rw [abs_of_nonneg (by positivity)]
  have h1 : g p ^ 2 ≤ M ^ 2 := by
    have := hM p
    rw [Real.norm_eq_abs] at this
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  gcongr

private lemma axis_integrable {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g) (hs : HasCompactSupport g)
    (h0 : ∀ z, g (0, z) = 0) {s : Set (ℝ × ℝ)} (hsm : MeasurableSet s)
    (hs0 : ∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2) :
    IntegrableOn (fun p : ℝ × ℝ => g p ^ 2 / p.1 ^ 2 * p.1) s := by
  obtain ⟨L, hL0, hL⟩ := support_bound hs 0
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hg one_ne_zero
  have hgm : Measurable g := hg.continuous.measurable
  refine integrableOn_bounded hsm (by fun_prop) (L := L) (C := (K : ℝ) ^ 2 * L) hs0
    (fun p hp hpL => ?_) (fun p hp => by simp [(hL p hp).1])
  have hp1 := (hs0 p hp).1
  have hb := axis_bound hK h0 p
  rw [abs_of_nonneg hp1] at hb
  rcases hp1.eq_or_lt with h | h
  · rw [← h]
    simp only [mul_zero, abs_zero]
    exact mul_nonneg (sq_nonneg _) hL0.le
  rw [abs_of_nonneg (by positivity)]
  have h1 : g p ^ 2 ≤ ((K : ℝ) * p.1) ^ 2 :=
    sq_le_sq' (by linarith [(abs_le.1 hb).1]) (abs_le.1 hb).2
  calc g p ^ 2 / p.1 ^ 2 * p.1 ≤ ((K : ℝ) * p.1) ^ 2 / p.1 ^ 2 * p.1 := by gcongr
    _ = (K : ℝ) ^ 2 * p.1 := by field_simp
    _ ≤ (K : ℝ) ^ 2 * L := by gcongr

private lemma to_lintegral {R : ℝ} {g F : ℝ × ℝ → ℝ} (hFi : IntegrableOn F (planeSquareExterior R))
    (hNi : IntegrableOn (fun p : ℝ × ℝ => g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1) (planeSquareExterior R))
    (hF0 : ∀ p ∈ planeSquareExterior R, 0 ≤ F p)
    (h : 2 * ∫ p in planeSquareExterior R, g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1
      ≤ ∫ p in planeSquareExterior R, F p) :
    ENNReal.ofReal 2 * ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (g p ^ 2 / planeRadius p ^ 2 * p.1)
      ≤ ∫⁻ p in planeSquareExterior R, ENNReal.ofReal (F p) := by
  have hQ := measurableSet_square R
  simp_rw [sq_planeRadius]
  rw [← ofReal_integral_eq_lintegral_ofReal hNi (ae_restrict_of_forall_mem hQ fun p hp =>
      mul_nonneg (div_nonneg (sq_nonneg _) (by positivity)) (le_of_lt hp.1.1)),
    ← ofReal_integral_eq_lintegral_ofReal hFi (ae_restrict_of_forall_mem hQ hF0),
    ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal h

private lemma axial_main {R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (h0 : ∀ x, g (x, 0) = 0) :
    2 * ∫ p in planeSquareExterior R, g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1
      ≤ ∫ p in planeSquareExterior R, (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1 := by
  obtain ⟨L, hRL, hL⟩ := support_bound hs R
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hg one_ne_zero
  have hP := grad_integrable hg hs
  have hU : IsOpen {p : ℝ × ℝ | 0 < p.2} := isOpen_lt continuous_const continuous_snd
  have hW₁ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -2 * p.1 ^ 2 / (p.1 ^ 2 + p.2 ^ 2)) {p | 0 < p.2} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx => by
      have : 0 < x.2 := hx
      positivity
  have hW₂ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => p.1 * (p.1 ^ 2 - p.2 ^ 2) / (p.2 * (p.1 ^ 2 + p.2 ^ 2)))
      {p | 0 < p.2} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx => by
      have : 0 < x.2 := hx
      positivity
  have hN : ∀ s : Set (ℝ × ℝ), MeasurableSet s → (∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ p ∈ s, R ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2) →
      IntegrableOn (fun p : ℝ × ℝ => (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1
        - 2 * (g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1)) s := fun s hsm h0s hqs =>
    hP.integrableOn.sub ((ratio_integrable hR hg hs hsm h0s hqs).const_mul 2)
  have key : ∀ ε, 0 < ε → ε < R → -((L - R) * ((K : ℝ) ^ 2 * ε * L)) ≤
      ∫ p in planeSquareExterior R ∩ {p | ε < p.2},
        ((fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2) * p.1
          - 2 * (g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1)) := by
    intro ε hε hεR
    have hT : Icc (0, R) (L, L) ⊆ {p : ℝ × ℝ | 0 < p.2} := fun x hx => hR.trans_le hx.1.2
    have hS : Icc (R, ε) (L, R) ⊆ {p : ℝ × ℝ | 0 < p.2} := fun x hx => hε.trans_le hx.1.2
    refine le_trans ?_ (two_box hU hg hW₁ hW₂ (fun x hx => axial_deriv_fst x hx)
      (fun x hx => axial_deriv_snd x hx) hε.le hεR hRL hT hS (fun p hp => (hL p hp).1)
      (fun p hp => by simp [(hL p hp).1, (hL p hp).2])
      (hN _ measurableSet_Icc (fun x hx => ⟨hx.1.1, hR.le.trans hx.1.2⟩)
        (fun x hx => by nlinarith [hx.1.2, sq_nonneg x.1]))
      (hN _ measurableSet_Icc (fun x hx => ⟨hR.le.trans hx.1.1, hε.le.trans hx.1.2⟩)
        (fun x hx => by nlinarith [hx.1.1, sq_nonneg x.2]))
      (fun x hx => ?_) (fun t => by simp))
    swap
    · rcases hx with hx | hx
      · exact axial_pointwise hx.1.1 (hR.trans_le hx.1.2)
      · exact axial_pointwise (hR.le.trans hx.1.1) (hε.trans_le hx.1.2)
    have hA : ∫ t in (0)..R, g (t, R) ^ 2 * (t * (t ^ 2 - R ^ 2) / (R * (t ^ 2 + R ^ 2))) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t =>
        -(g (t, R) ^ 2 * (t * (t ^ 2 - R ^ 2) / (R * (t ^ 2 + R ^ 2))))) hR.le fun t ht => by
          have h1 : t * (t ^ 2 - R ^ 2) ≤ 0 :=
            mul_nonpos_of_nonneg_of_nonpos ht.1 (by nlinarith [ht.1, ht.2])
          have h2 : t * (t ^ 2 - R ^ 2) / (R * (t ^ 2 + R ^ 2)) ≤ 0 :=
            div_nonpos_iff.2 (Or.inr ⟨h1, by positivity⟩)
          exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h2)
      rw [intervalIntegral.integral_neg] at this
      linarith
    have hC : ∫ t in ε..R, g (R, t) ^ 2 * (-2 * R ^ 2 / (R ^ 2 + t ^ 2)) ≤ 0 := by
      have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t =>
        -(g (R, t) ^ 2 * (-2 * R ^ 2 / (R ^ 2 + t ^ 2)))) hεR.le fun t _ => by
          have h2 : -2 * R ^ 2 / (R ^ 2 + t ^ 2) ≤ 0 :=
            div_nonpos_iff.2 (Or.inr ⟨by nlinarith, by positivity⟩)
          exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h2)
      rw [intervalIntegral.integral_neg] at this
      linarith
    have hB : ∫ t in R..L, g (t, ε) ^ 2 * (t * (t ^ 2 - ε ^ 2) / (ε * (t ^ 2 + ε ^ 2)))
        ≤ (L - R) * ((K : ℝ) ^ 2 * ε * L) := by
      have hi := line_integrable (c := ε) (a := R) (b := L) hg.continuous hW₂.continuousOn
        fun t _ => hε
      have := intervalIntegral.integral_mono_on hRL.le hi intervalIntegrable_const
        (fun t ht => show g (t, ε) ^ 2 * (t * (t ^ 2 - ε ^ 2) / (ε * (t ^ 2 + ε ^ 2)))
          ≤ (K : ℝ) ^ 2 * ε * L from by
          have ht0 : 0 ≤ t := hR.le.trans ht.1
          have hb := plane_bound hK h0 (t, ε)
          rw [abs_of_pos hε] at hb
          have hg2 : g (t, ε) ^ 2 ≤ ((K : ℝ) * ε) ^ 2 :=
            sq_le_sq' (by linarith [(abs_le.1 hb).1]) (abs_le.1 hb).2
          have hw : t * (t ^ 2 - ε ^ 2) / (ε * (t ^ 2 + ε ^ 2)) ≤ t / ε := by
            rw [div_le_div_iff₀ (by positivity) hε]
            nlinarith [sq_nonneg ε, sq_nonneg t, mul_nonneg ht0 (sq_nonneg ε)]
          calc g (t, ε) ^ 2 * (t * (t ^ 2 - ε ^ 2) / (ε * (t ^ 2 + ε ^ 2)))
              ≤ g (t, ε) ^ 2 * (t / ε) := mul_le_mul_of_nonneg_left hw (sq_nonneg _)
            _ ≤ ((K : ℝ) * ε) ^ 2 * (t / ε) :=
              mul_le_mul_of_nonneg_right hg2 (div_nonneg ht0 hε.le)
            _ = (K : ℝ) ^ 2 * ε * t := by field_simp
            _ ≤ (K : ℝ) ^ 2 * ε * L := by gcongr; exact ht.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at this
      exact this
    dsimp only at hA hB hC ⊢
    linarith
  have hQ := measurableSet_square R
  set εs : ℕ → ℝ := fun n => R / 2 * (1 / ((n : ℝ) + 1)) with hεs
  have hεpos : ∀ n, 0 < εs n := fun n => by positivity
  have hεlt : ∀ n, εs n < R := fun n => by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    simp only [hεs]
    nlinarith
  have hmono : Monotone fun n => planeSquareExterior R ∩ {p : ℝ × ℝ | εs n < p.2} := by
    intro n m hnm p hp
    refine ⟨hp.1, show εs m < p.2 from lt_of_le_of_lt ?_ (show εs n < p.2 from hp.2)⟩
    simp only [hεs]
    gcongr
  have hunion : (⋃ n, planeSquareExterior R ∩ {p : ℝ × ℝ | εs n < p.2}) = planeSquareExterior R := by
    refine Subset.antisymm (iUnion_subset fun n => inter_subset_left) fun p hp => ?_
    have hp2 : 0 < p.2 := hp.1.2
    obtain ⟨n, hn⟩ := exists_nat_gt (R / 2 / p.2)
    refine mem_iUnion.2 ⟨n, hp, ?_⟩
    show R / 2 * (1 / ((n : ℝ) + 1)) < p.2
    rw [div_lt_iff₀ hp2] at hn
    rw [mul_one_div, div_lt_iff₀ (by positivity)]
    nlinarith
  have hint := hN _ hQ (fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩) (fun p hp => by
    rcases hp.2 with h | h
    · nlinarith [sq_nonneg p.2]
    · nlinarith [sq_nonneg p.1])
  have ht := tendsto_setIntegral_of_monotone (fun n => measurableSet_exterior R (εs n)) hmono
    (by rw [hunion]; exact hint)
  rw [hunion] at ht
  have hlow := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
    (-((L - R) * ((K : ℝ) ^ 2 * (R / 2) * L)))
  rw [mul_zero] at hlow
  have h := le_of_tendsto_of_tendsto' hlow ht fun n => by
    have := key (εs n) (hεpos n) (hεlt n)
    simp only [hεs] at this
    linarith
  rw [integral_sub hP.integrableOn ((ratio_integrable hR hg hs hQ
    (fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩) (fun p hp => by
      rcases hp.2 with h | h
      · nlinarith [sq_nonneg p.2]
      · nlinarith [sq_nonneg p.1])).const_mul 2), integral_const_mul] at h
  linarith

private lemma transverse_main {R : ℝ} (hR : 0 < R) {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hs : HasCompactSupport g) (h0 : ∀ z, g (0, z) = 0) :
    2 * ∫ p in planeSquareExterior R, g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1
      ≤ ∫ p in planeSquareExterior R,
          (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2 + g p ^ 2 / p.1 ^ 2) * p.1 := by
  obtain ⟨L, hRL, hL⟩ := support_bound hs R
  have hP := grad_integrable hg hs
  have hU : IsOpen {p : ℝ × ℝ | 0 < p.1 ^ 2 + p.2 ^ 2} := isOpen_lt continuous_const (by fun_prop)
  have hW₁ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (p.2 ^ 2 - p.1 ^ 2) / (p.1 ^ 2 + p.2 ^ 2))
      {p | 0 < p.1 ^ 2 + p.2 ^ 2} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx => ne_of_gt hx
  have hW₂ : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => -2 * p.1 * p.2 / (p.1 ^ 2 + p.2 ^ 2))
      {p | 0 < p.1 ^ 2 + p.2 ^ 2} :=
    ContDiffOn.div (by fun_prop) (by fun_prop) fun x hx => ne_of_gt hx
  have hF : ∀ s : Set (ℝ × ℝ), MeasurableSet s → (∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      IntegrableOn (fun p : ℝ × ℝ =>
        (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2 + g p ^ 2 / p.1 ^ 2) * p.1) s :=
    fun s hsm h0s => (hP.integrableOn.add (axis_integrable hg hs h0 hsm h0s)).congr_fun
      (fun p _ => by simp only [Pi.add_apply]; ring) hsm
  have hN : ∀ s : Set (ℝ × ℝ), MeasurableSet s → (∀ p ∈ s, 0 ≤ p.1 ∧ 0 ≤ p.2) →
      (∀ p ∈ s, R ^ 2 ≤ p.1 ^ 2 + p.2 ^ 2) →
      IntegrableOn (fun p : ℝ × ℝ =>
        (fderiv ℝ g p (1, 0) ^ 2 + fderiv ℝ g p (0, 1) ^ 2 + g p ^ 2 / p.1 ^ 2) * p.1
          - 2 * (g p ^ 2 / (p.1 ^ 2 + p.2 ^ 2) * p.1)) s := fun s hsm h0s hqs =>
    (hF s hsm h0s).sub ((ratio_integrable hR hg hs hsm h0s hqs).const_mul 2)
  have hT : Icc (0, R) (L, L) ⊆ {p : ℝ × ℝ | 0 < p.1 ^ 2 + p.2 ^ 2} := fun x hx => by
    have : R ≤ x.2 := hx.1.2
    show 0 < x.1 ^ 2 + x.2 ^ 2
    nlinarith [sq_nonneg x.1]
  have hS : Icc (R, 0) (L, R) ⊆ {p : ℝ × ℝ | 0 < p.1 ^ 2 + p.2 ^ 2} := fun x hx => by
    have : R ≤ x.1 := hx.1.1
    show 0 < x.1 ^ 2 + x.2 ^ 2
    nlinarith [sq_nonneg x.2]
  have hb := two_box hU hg hW₁ hW₂ (fun x hx => cross_deriv_fst x hx)
    (fun x hx => cross_deriv_snd x hx) le_rfl hR hRL hT hS (fun p hp => (hL p hp).1)
    (fun p hp => by simp [(hL p hp).1, (hL p hp).2])
    (hN _ measurableSet_Icc (fun x hx => ⟨hx.1.1, hR.le.trans hx.1.2⟩)
      (fun x hx => by nlinarith [hx.1.2, sq_nonneg x.1]))
    (hN _ measurableSet_Icc (fun x hx => ⟨hR.le.trans hx.1.1, hx.1.2⟩)
      (fun x hx => by nlinarith [hx.1.1, sq_nonneg x.2]))
    (fun x hx => ?_) (fun t => by simp [h0 t])
  swap
  · have hx1 : 0 ≤ x.1 := by rcases hx with hx | hx; exacts [hx.1.1, hR.le.trans hx.1.1]
    rcases hx1.eq_or_lt with h | h
    · have hgx : g x = 0 := by rw [show x = (0, x.2) from Prod.ext h.symm rfl]; exact h0 _
      simp [hgx, ← h]
    · exact cross_pointwise h
  have hA : ∫ t in (0)..R, g (t, R) ^ 2 * (-2 * t * R / (t ^ 2 + R ^ 2)) ≤ 0 := by
    have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t =>
      -(g (t, R) ^ 2 * (-2 * t * R / (t ^ 2 + R ^ 2)))) hR.le fun t ht => by
        have h2 : -2 * t * R / (t ^ 2 + R ^ 2) ≤ 0 :=
          div_nonpos_iff.2 (Or.inr ⟨by nlinarith [ht.1], by positivity⟩)
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h2)
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hC : ∫ t in (0)..R, g (R, t) ^ 2 * ((t ^ 2 - R ^ 2) / (R ^ 2 + t ^ 2)) ≤ 0 := by
    have := intervalIntegral.integral_nonneg (μ := volume) (f := fun t =>
      -(g (R, t) ^ 2 * ((t ^ 2 - R ^ 2) / (R ^ 2 + t ^ 2)))) hR.le fun t ht => by
        have h2 : (t ^ 2 - R ^ 2) / (R ^ 2 + t ^ 2) ≤ 0 :=
          div_nonpos_iff.2 (Or.inr ⟨by nlinarith [ht.1, ht.2], by positivity⟩)
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) h2)
    rw [intervalIntegral.integral_neg] at this
    linarith
  have hB : ∫ t in R..L, g (t, 0) ^ 2 * (-2 * t * 0 / (t ^ 2 + 0 ^ 2)) = 0 :=
    iint_zero fun t => by simp
  have hQ : planeSquareExterior R ∩ {p : ℝ × ℝ | 0 < p.2} = planeSquareExterior R :=
    inter_eq_left.2 fun p hp => hp.1.2
  rw [hQ] at hb
  dsimp only at hb
  have hq := measurableSet_square R
  rw [integral_sub (hF _ hq fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩)
    ((ratio_integrable hR hg hs hq (fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩) (fun p hp => by
      rcases hp.2 with h | h
      · nlinarith [sq_nonneg p.2]
      · nlinarith [sq_nonneg p.1])).const_mul 2), integral_const_mul] at hb
  linarith

theorem squareExteriorAxialSmoothStatement : SquareExteriorAxialSmoothStatement :=
  fun R hR g hg hs h0 => to_lintegral (grad_integrable hg hs).integrableOn
    (ratio_integrable hR hg hs (measurableSet_square R) (fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩)
      fun p hp => by
        rcases hp.2 with h | h
        · nlinarith [sq_nonneg p.2]
        · nlinarith [sq_nonneg p.1])
    (fun p hp => mul_nonneg (by positivity) (le_of_lt hp.1.1)) (axial_main hR hg hs h0)

theorem squareExteriorTransverseSmoothStatement : SquareExteriorTransverseSmoothStatement :=
  fun R hR g hg hs h0 => to_lintegral
    (((grad_integrable hg hs).integrableOn.add (axis_integrable hg hs h0 (measurableSet_square R)
      fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩)).congr_fun
      (fun p _ => by simp only [Pi.add_apply]; ring) (measurableSet_square R))
    (ratio_integrable hR hg hs (measurableSet_square R) (fun p hp => ⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩)
      fun p hp => by
        rcases hp.2 with h | h
        · nlinarith [sq_nonneg p.2]
        · nlinarith [sq_nonneg p.1])
    (fun p hp => mul_nonneg (by positivity) (le_of_lt hp.1.1)) (transverse_main hR hg hs h0)

theorem squareExteriorSmoothStatement : SquareExteriorSmoothStatement :=
  ⟨squareExteriorAxialSmoothStatement, squareExteriorTransverseSmoothStatement⟩

end TailBand

end CertCell

end Breakdown

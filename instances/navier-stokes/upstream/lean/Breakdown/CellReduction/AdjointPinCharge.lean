import Breakdown.CellReduction.AdjointPinChargeParts
import Breakdown.CertCell.ShapeActuator

open scoped ENNReal ContDiff
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace AdjointDefect

namespace Internal.PinCharge

open CertCell.InstancePair.Internal.ByPartsMollify

theorem weak_zero :
    IsWeakGradient (fun _ => (0 : Space)) (fun _ => (0 : Space →L[ℝ] Space)) :=
  ⟨locallyIntegrable_zero, locallyIntegrable_zero, fun φ _ i => by simp⟩

theorem weak_add {f f' : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (h' : IsWeakGradient f' g') :
    IsWeakGradient (fun y => f y + f' y) (fun y => g y + g' y) := by
  refine ⟨h.1.add h'.1, h.2.1.add h'.2.1, fun φ hφ i => ?_⟩
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hds : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) := hφ.2.fderiv_apply (𝕜 := ℝ) _
  have a1 : Integrable (fun y => φ y • g y (unitVector i)) := by
    simpa using (h.2.1.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).apply_continuousLinearMap
      (unitVector i)
  have a2 : Integrable (fun y => φ y • g' y (unitVector i)) := by
    simpa using (h'.2.1.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).apply_continuousLinearMap
      (unitVector i)
  have b1 := h.1.integrable_smul_left_of_hasCompactSupport hd hds
  have b2 := h'.1.integrable_smul_left_of_hasCompactSupport hd hds
  simp only [ContinuousLinearMap.add_apply, smul_add]
  rw [integral_add a1 a2, integral_add b1 b2, h.2.2 φ hφ i, h'.2.2 φ hφ i, neg_add]

theorem weak_smul (a : ℝ) {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) : IsWeakGradient (fun y => a • f y) (fun y => a • g y) := by
  refine ⟨h.1.smul a, h.2.1.smul a, fun φ hφ i => ?_⟩
  have e1 : ∀ y, φ y • (a • g y) (unitVector i) = a • (φ y • g y (unitVector i)) := fun y => by
    rw [ContinuousLinearMap.smul_apply, smul_comm]
  have e2 : ∀ y, fderiv ℝ φ y (unitVector i) • a • f y = a • (fderiv ℝ φ y (unitVector i) • f y) :=
    fun y => smul_comm _ _ _
  simp only [e1, e2, integral_smul, h.2.2 φ hφ i, smul_neg]

theorem weak_finsetSum {ι : Type*} (s : Finset ι) {f : ι → Space → Space}
    {g : ι → Space → (Space →L[ℝ] Space)} (h : ∀ i ∈ s, IsWeakGradient (f i) (g i)) :
    IsWeakGradient (fun y => ∑ i ∈ s, f i y) (fun y => ∑ i ∈ s, g i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weak_zero
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact weak_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem bounded_of_periodic {E : Type*} [NormedAddCommGroup E] {M : ℝ → Space → E}
    (hc : Continuous (fun z : ℝ × Space => M z.1 z.2)) (hp : IsTimePeriodic M)
    {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → M σ y = 0) : ∃ B, 0 ≤ B ∧ ∀ σ y, ‖M σ y‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc.prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    (s := Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) hc.continuousOn
  refine ⟨max B 0, le_max_right _ _, fun σ y => ?_⟩
  rcases lt_or_ge R ‖y‖ with hy | hy
  · rw [hs σ y hy, norm_zero]
    exact le_max_right _ _
  · have hper : Function.Periodic (fun s => M s y) 1 := fun s => hp s y
    have e : M σ y = M (Int.fract σ) y := by
      have h := hper.sub_int_mul_eq (x := σ) ⌊σ⌋
      rw [mul_one] at h
      exact h.symm
    rw [e]
    refine (hB (Int.fract σ, y) ⟨⟨Int.fract_nonneg σ, (Int.fract_lt_one σ).le⟩, ?_⟩).trans (le_max_left _ _)
    simpa [Metric.mem_closedBall, dist_zero_right] using hy

theorem mul_le_split_squares {a b u : ℝ} (hu : 0 < u) : a * b ≤ u * a ^ 2 / 2 + b ^ 2 / (2 * u) := by
  rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (u * a - b)]

theorem le_sqrt_mul {X a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u : ℝ, 0 < u → X ≤ u * a / 2 + b / (2 * u)) : X ≤ Real.sqrt a * Real.sqrt b := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · obtain ⟨sa, hsa⟩ : ∃ s, s = Real.sqrt a := ⟨_, rfl⟩
      obtain ⟨sb, hsb⟩ : ∃ s, s = Real.sqrt b := ⟨_, rfl⟩
      have hsa0 : 0 < sa := hsa ▸ Real.sqrt_pos.2 ha'
      have hsb0 : 0 < sb := hsb ▸ Real.sqrt_pos.2 hb'
      have ha2 : sa ^ 2 = a := hsa ▸ Real.sq_sqrt ha
      have hb2 : sb ^ 2 = b := hsb ▸ Real.sq_sqrt hb
      have h1 := h (sb / sa) (div_pos hsb0 hsa0)
      have key : sb / sa * a / 2 + b / (2 * (sb / sa)) = sa * sb := by
        rw [← ha2, ← hb2]
        field_simp
        ring
      rw [← hsa, ← hsb]
      linarith
    · subst hb'
      rw [Real.sqrt_zero, mul_zero]
      by_contra hX
      push Not at hX
      have h1 := h (X / a) (div_pos hX ha')
      have e : X / a * a / 2 + 0 / (2 * (X / a)) = X / 2 := by
        field_simp; ring
      linarith
  · subst ha'
    rw [Real.sqrt_zero, zero_mul]
    by_contra hX
    push Not at hX
    have h1 := h ((b + 1) / X) (div_pos (by linarith) hX)
    have e : (b + 1) / X * 0 / 2 + b / (2 * ((b + 1) / X)) = b * X / (2 * (b + 1)) := by
      field_simp; ring
    have h2 : b * X / (2 * (b + 1)) < X := by
      rw [div_lt_iff₀ (by positivity)]
      nlinarith
    linarith

theorem abs_pairMatrix_le (A B : Space →L[ℝ] Space) {u : ℝ} (hu : 0 < u) :
    |matInner A B| ≤ u * matSq A / 2 + matSq B / (2 * u) := by
  unfold matInner matSq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun i _ => (abs_real_inner_le_norm _ _).trans (mul_le_split_squares hu)

theorem abs_inner_le (x y : Space) {u : ℝ} (hu : 0 < u) :
    |inner ℝ x y| ≤ u * ‖x‖ ^ 2 / 2 + ‖y‖ ^ 2 / (2 * u) :=
  (abs_real_inner_le_norm _ _).trans (mul_le_split_squares hu)

theorem abs_integral_le {μ : Measure (ℝ × Space)} {f F1 F2 : ℝ × Space → ℝ} (hf : Integrable f μ)
    (h1 : Integrable F1 μ) (h2 : Integrable F2 μ) (hF1 : ∀ z, 0 ≤ F1 z) (hF2 : ∀ z, 0 ≤ F2 z)
    (hpt : ∀ u : ℝ, 0 < u → ∀ z, |f z| ≤ u * F1 z / 2 + F2 z / (2 * u)) :
    |∫ z, f z ∂μ| ≤ Real.sqrt (∫ z, F1 z ∂μ) * Real.sqrt (∫ z, F2 z ∂μ) := by
  refine le_sqrt_mul (integral_nonneg fun z => hF1 z) (integral_nonneg fun z => hF2 z) fun u hu => ?_
  calc |∫ z, f z ∂μ| ≤ ∫ z, |f z| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ z, (u * F1 z / 2 + F2 z / (2 * u)) ∂μ :=
        integral_mono hf.abs (((h1.const_mul u).div_const 2).add (h2.div_const (2 * u))) fun z => hpt u hu z
    _ = u * (∫ z, F1 z ∂μ) / 2 + (∫ z, F2 z ∂μ) / (2 * u) := by
        rw [integral_add ((h1.const_mul u).div_const 2) (h2.div_const (2 * u)), integral_div, integral_div,
          integral_const_mul]

theorem continuous_trace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem period_integrable {f : ℝ → Space → ℝ} (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (h0 : ∀ σ y, 0 ≤ f σ y) (hf : periodLIntegral f < ⊤) :
    Integrable (fun z : ℝ × Space => f z.1 z.2) periodMeasure := by
  have hm' := aesm_period hm
  refine ⟨hm', (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z : ℝ × Space => h0 z.1 z.2)).2 ?_⟩
  rw [← periodL_eq hm'.aemeasurable.ennreal_ofReal]
  exact hf

theorem integral_le_of_period {f : ℝ → Space → ℝ}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume)
    (h0 : ∀ σ y, 0 ≤ f σ y) {B : ℝ} (hB : 0 ≤ B) (h : periodLIntegral f ≤ ENNReal.ofReal B) :
    ∫ z, f z.1 z.2 ∂periodMeasure ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z : ℝ × Space => h0 z.1 z.2) (aesm_period hm),
    ← periodL_eq (aesm_period hm).aemeasurable.ennreal_ofReal]
  exact ENNReal.toReal_le_of_le_ofReal hB h

theorem ae_slice_finite {f : ℝ → Space → ℝ}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) (hf : periodLIntegral f < ⊤) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (f σ y) < ⊤ := by
  have h1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) periodMeasure :=
    (aesm_period hm).aemeasurable.ennreal_ofReal
  exact ae_lt_top' h1.lintegral_prod_right' hf.ne

theorem matrix_pairing_integrable {M N : ℝ × Space → (Space →L[ℝ] Space)}
    (hM : AEStronglyMeasurable M periodMeasure) (hN : AEStronglyMeasurable N periodMeasure)
    (iM : Integrable (fun z => matSq (M z)) periodMeasure) (iN : Integrable (fun z => matSq (N z)) periodMeasure) :
    Integrable (fun z => matInner (M z) (N z)) periodMeasure := by
  refine ((iM.div_const 2).add (iN.div_const 2)).mono' ?_ (ae_of_all _ fun z => ?_)
  · unfold matInner
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (hM.apply_continuousLinearMap _).inner (hN.apply_continuousLinearMap _)
  · rw [Real.norm_eq_abs]
    exact abs_matrixPairing_le _ _

theorem vector_pairing_integrable {x y : ℝ × Space → Space}
    (hx : AEStronglyMeasurable x periodMeasure) (hy : AEStronglyMeasurable y periodMeasure)
    (ix : Integrable (fun z => ‖x z‖ ^ 2) periodMeasure) (iy : Integrable (fun z => ‖y z‖ ^ 2) periodMeasure) :
    Integrable (fun z => inner ℝ (x z) (y z)) periodMeasure := by
  refine ((ix.div_const 2).add (iy.div_const 2)).mono' (hx.inner hy) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h := abs_inner_le (x z) (y z) one_pos
  simp only [one_mul, mul_one] at h
  exact h

theorem slice_contDiff {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (σ : ℝ) :
    ContDiff ℝ 1 (F σ) :=
  hF.comp (contDiff_const.prodMk contDiff_id)

theorem slice_fderiv_eq {F : ℝ → Space → Space} (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2))
    (σ : ℝ) (y : Space) :
    fderiv ℝ (F σ) y =
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => F z.1 z.2) (σ, y) :=
    (hF.differentiable one_ne_zero) _
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)).fderiv

theorem slice_fderiv_continuous {F : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) := by
  have e : (fun z : ℝ × Space => fderiv ℝ (F z.1) z.2) = fun z =>
      (fderiv ℝ (fun z : ℝ × Space => F z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) :=
    funext fun z => slice_fderiv_eq hF z.1 z.2
  rw [e]
  exact (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem fderiv_zero_outside {f : Space → Space} {R : ℝ} (hf : ∀ y, R ≤ ‖y‖ → f y = 0) {y : Space}
    (hy : R < ‖y‖) : fderiv ℝ f y = 0 := by
  have hev : f =ᶠ[𝓝 y] fun _ => 0 := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hy] with z hz
    exact hf z (le_of_lt hz)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply _

theorem compact_of_zero {E : Type*} [NormedAddCommGroup E] {f : Space → E} {R : ℝ}
    (h : ∀ y, R < ‖y‖ → f y = 0) : HasCompactSupport f :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) R) fun y hy =>
    h y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)

theorem compact_entrySq_integrable {M : ℝ → Space → (Space →L[ℝ] Space)}
    (hc : Continuous (fun z : ℝ × Space => M z.1 z.2)) (hp : IsTimePeriodic M) {R : ℝ}
    (hs : ∀ σ y, R < ‖y‖ → M σ y = 0) :
    Integrable (fun z : ℝ × Space => matSq (M z.1 z.2)) periodMeasure := by
  obtain ⟨K, -, hK⟩ := bounded_of_periodic hc hp hs
  have hi : Integrable ((Metric.closedBall (0 : Space) R).indicator (fun _ => 3 * K ^ 2)) volume :=
    (integrableOn_const measure_closedBall_lt_top.ne).integrable_indicator measurableSet_closedBall
  have hw : Integrable (fun z : ℝ × Space =>
      (1 : ℝ) * (Metric.closedBall (0 : Space) R).indicator (fun _ => 3 * K ^ 2) z.2) periodMeasure :=
    (integrable_const (1 : ℝ)).mul_prod hi
  refine hw.mono' (continuous_entrySq.comp hc).aestronglyMeasurable (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (entrySq_nonneg _), one_mul]
  by_cases hz : z.2 ∈ Metric.closedBall (0 : Space) R
  · rw [Set.indicator_of_mem hz]
    refine (entrySq_le _).trans ?_
    gcongr
    exact hK z.1 z.2
  · rw [Set.indicator_of_notMem hz,
      hs z.1 z.2 (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hz)]
    simp [matSq]

theorem weak_sub {f f' : Space → Space} {g g' : Space → (Space →L[ℝ] Space)}
    (h : IsWeakGradient f g) (h' : IsWeakGradient f' g') :
    IsWeakGradient (fun y => f y - f' y) (fun y => g y - g' y) := by
  have := weak_add h (weak_smul (-1) h')
  simpa [sub_eq_add_neg] using this

theorem pairMatrix_sub (G M N : Space →L[ℝ] Space) : matInner G (M - N) = matInner G M - matInner G N := by
  unfold matInner
  simp only [ContinuousLinearMap.sub_apply, inner_sub_right, Finset.sum_sub_distrib]

theorem pairMatrix_sum_smul {k : ℕ} (G : Space →L[ℝ] Space) (c : Fin k → ℝ) (M : Fin k → Space →L[ℝ] Space) :
    matInner G (∑ l, c l • M l) = ∑ l, c l * matInner G (M l) := by
  unfold matInner
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, inner_sum, inner_smul_right,
    Finset.mul_sum]
  exact Finset.sum_comm

theorem adjoint_sum_smul {k : ℕ} (c : Fin k → ℝ) (M : Fin k → Space →L[ℝ] Space) :
    ContinuousLinearMap.adjoint (∑ l, c l • M l) = ∑ l, c l • ContinuousLinearMap.adjoint (M l) := by
  simp [map_sum]

theorem sqrt_bound {b t s cn : ℝ} (hb : b ≤ t ^ 2 * s) (ht : 0 ≤ t)
    (hs : Real.sqrt s ≤ cn) : Real.sqrt b ≤ t * cn :=
  calc Real.sqrt b ≤ Real.sqrt (t ^ 2 * s) := Real.sqrt_le_sqrt hb
    _ = t * Real.sqrt s := by rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
    _ ≤ t * cn := mul_le_mul_of_nonneg_left hs ht

theorem final_bound {X iA iZ a h bA bZ E w₀ ε ρ cn : ℝ} (hX : X = iA - iZ)
    (hA1 : |iA| ≤ Real.sqrt a * Real.sqrt bA) (hZ1 : |iZ| ≤ Real.sqrt h * Real.sqrt bZ)
    (hsA : Real.sqrt bA ≤ ρ * cn) (hsZ : Real.sqrt bZ ≤ ε) (hE : E = h + w₀ * a) (hw : 0 < w₀)
    (ha0 : 0 ≤ a) (hh0 : 0 ≤ h) (hε : 0 ≤ ε) (hρ : 0 ≤ ρ) (hcn0 : 0 ≤ cn) :
    |X| ≤ (ε + cn * ρ / Real.sqrt w₀) * Real.sqrt E := by
  have hsw := Real.sqrt_pos.2 hw
  have hsa : Real.sqrt a ≤ Real.sqrt E / Real.sqrt w₀ := by
    rw [le_div_iff₀ hsw, ← Real.sqrt_mul ha0]
    exact Real.sqrt_le_sqrt (by rw [hE]; nlinarith)
  have hsh : Real.sqrt h ≤ Real.sqrt E := Real.sqrt_le_sqrt (by rw [hE]; nlinarith [mul_nonneg hw.le ha0])
  rw [hX]
  calc |iA - iZ| ≤ |iA| + |iZ| := abs_sub _ _
    _ ≤ Real.sqrt a * (ρ * cn) + Real.sqrt h * ε :=
        add_le_add (hA1.trans (mul_le_mul_of_nonneg_left hsA (Real.sqrt_nonneg _)))
          (hZ1.trans (mul_le_mul_of_nonneg_left hsZ (Real.sqrt_nonneg _)))
    _ ≤ Real.sqrt E / Real.sqrt w₀ * (ρ * cn) + Real.sqrt E * ε :=
        add_le_add (mul_le_mul_of_nonneg_right hsa (by positivity))
          (mul_le_mul_of_nonneg_right hsh (by positivity))
    _ = (ε + cn * ρ / Real.sqrt w₀) * Real.sqrt E := by ring

open CertCell.InstancePair.Internal.ByPartsMollify in
theorem slice_transpose {k : ℕ} {Γ : Set Symmetry} {P C R₀ : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)} {pd : PinData k} (c : Fin k → ℝ)
    (hp : IsPerturbation Γ P v G H g) (hpin : IsPinData χ pd C R₀) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫ y, matInner (G σ y) (ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l σ) y)) = 0 := by
  have hXsC : ∀ l σ, ContDiff ℝ 1 (pd.generator l σ) := fun l => slice_contDiff (hpin.generator_smooth l)
  have hXsZ : ∀ l σ y, R₀ < ‖y‖ → fderiv ℝ (pd.generator l σ) y = 0 :=
    fun l σ y hy => fderiv_zero_outside (hpin.generator_support l σ) hy
  have a1 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1) hp.weak_gradient
  have a3 := ae_slice_finite (f := fun σ y => matSq (G σ y))
    (Internal.continuous_entrySq.comp_aestronglyMeasurable hp.measurable_gradient) hp.gradient_finite
  have a7 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1) hp.divergence_free
  filter_upwards [a1, a3, a7] with σ h1 h3 h7
  have hf : IsWeakGradient (fun y => ∑ l, c l • pd.generator l σ y)
      (fun y => ∑ l, c l • fderiv ℝ (pd.generator l σ) y) :=
    weak_finsetSum _ fun l _ =>
      weak_smul (c l)
        (CertCell.GivenShape.Internal.isWeakGradient_of_contDiff (hXsC l σ))
  have hR : ∀ y, R₀ < ‖y‖ → ∑ l, c l • pd.generator l σ y = 0 := fun y hy =>
    Finset.sum_eq_zero fun l _ => by rw [hpin.generator_support l σ y hy.le, smul_zero]
  have hfL : MemLp (fun y => ∑ l, c l • pd.generator l σ y) 2 volume :=
    (continuous_finsetSum _ fun l _ => (hXsC l σ).continuous.const_smul (c l)).memLp_of_hasCompactSupport
      (compact_of_zero hR)
  have hDL : ∀ j, MemLp (fun y => (∑ l, c l • fderiv ℝ (pd.generator l σ) y) (unitVector j)) 2 volume := by
    intro j
    have hc : Continuous (fun y => (∑ l, c l • fderiv ℝ (pd.generator l σ) y) (unitVector j)) :=
      (continuous_finsetSum (f := fun l y => c l • fderiv ℝ (pd.generator l σ) y) _ fun l _ =>
        ((hXsC l σ).continuous_fderiv one_ne_zero).const_smul (c l)).clm_apply continuous_const
    refine hc.memLp_of_hasCompactSupport (compact_of_zero (R := R₀) fun y hy => ?_)
    rw [Finset.sum_eq_zero fun l _ => by rw [hXsZ l σ y hy, smul_zero], ContinuousLinearMap.zero_apply]
  have hGL : ∀ j, MemLp (fun y => G σ y (unitVector j)) 2 volume := fun j =>
    column_memLp j (Cert.Internal.ReadingEnergy.locallyIntegrable_column h1.2.1 j).aestronglyMeasurable h3
  exact transpose_pairing_zero h1 h7 hGL hf hR hfL hDL

open CertCell.InstancePair.Internal.ByPartsMollify in
theorem slice_by_parts {k : ℕ} {Γ : Set Symmetry} {P C R₀ ε : ℝ} {v g : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {χ : Fin k → ℝ → Space → (Space →L[ℝ] Space)} {pd : PinData k} (c : Fin k → ℝ)
    (hp : IsPerturbation Γ P v G H g) (hpin : IsPinData χ pd C R₀)
    (herr : periodLIntegral (fun σ y => ‖∑ l, c l • (pd.potential l σ y - pd.generator l σ y)‖ ^ 2) ≤
      ENNReal.ofReal (ε ^ 2)) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫ y, matInner (G σ y) (∑ l, c l • (fderiv ℝ (pd.potential l σ) y - fderiv ℝ (pd.generator l σ) y)) =
        -∫ y, inner ℝ (secondDerivTrace (H σ y)) (∑ l, c l • (pd.potential l σ y - pd.generator l σ y)) := by
  have hXsC : ∀ l σ, ContDiff ℝ 1 (pd.generator l σ) := fun l => slice_contDiff (hpin.generator_smooth l)
  have hXsZ : ∀ l σ y, R₀ < ‖y‖ → fderiv ℝ (pd.generator l σ) y = 0 :=
    fun l σ y hy => fderiv_zero_outside (hpin.generator_support l σ) hy
  have hZm : AEStronglyMeasurable (fun z : ℝ × Space =>
      ∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2)) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
      ((hpin.potential_measurable l).sub (hpin.generator_smooth l).continuous.aestronglyMeasurable).const_smul (c l)
  have hHm : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    continuous_trace.comp_aestronglyMeasurable hp.measurable_secondDeriv
  have a1 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1) hp.weak_gradient
  have a2 := ae_restrict_of_ae (s := Set.Icc (0 : ℝ) 1) hp.weak_secondDeriv
  have a3 := ae_slice_finite (f := fun σ y => matSq (G σ y))
    (Internal.continuous_entrySq.comp_aestronglyMeasurable hp.measurable_gradient) hp.gradient_finite
  have a4 := ae_slice_finite (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)
    ((continuous_norm.pow 2).comp_aestronglyMeasurable hHm) hp.sumSecondPartials_finite
  have a5 := ae_slice_finite (f := fun σ y => ‖∑ l, c l • (pd.potential l σ y - pd.generator l σ y)‖ ^ 2)
    ((continuous_norm.pow 2).comp_aestronglyMeasurable hZm) (lt_of_le_of_lt herr ENNReal.ofReal_lt_top)
  have a6 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∀ l, ∫⁻ y, ENNReal.ofReal (matSq (fderiv ℝ (pd.potential l σ) y)) < ⊤ :=
    ae_all_iff.2 fun l => ae_slice_finite (f := fun σ y => matSq (fderiv ℝ (pd.potential l σ) y))
      (Internal.continuous_entrySq.comp_aestronglyMeasurable (hpin.potentialGrad_measurable l))
      (hpin.potentialGrad_finite l)
  filter_upwards [a1, a2, a3, a4, a5, a6] with σ h1 h2 h3 h4 h5 h6
  have hf : IsWeakGradient (fun y => ∑ l, c l • (pd.potential l σ y - pd.generator l σ y))
      (fun y => ∑ l, c l • (fderiv ℝ (pd.potential l σ) y - fderiv ℝ (pd.generator l σ) y)) :=
    weak_finsetSum _ fun l _ =>
      weak_smul (c l)
        (weak_sub (hpin.potential_weak l σ) (CertCell.GivenShape.Internal.isWeakGradient_of_contDiff (hXsC l σ)))
  have hR : ∀ y, R₀ < ‖y‖ → ∑ l, c l • (pd.potential l σ y - pd.generator l σ y) = 0 := fun y hy =>
    Finset.sum_eq_zero fun l _ => by
      rw [hpin.potential_support l σ y hy.le, hpin.generator_support l σ y hy.le, sub_self, smul_zero]
  have hfL := memLp_two_of_lintegral hf.1.aestronglyMeasurable h5
  have hoL : ∀ l j, MemLp (fun y => fderiv ℝ (pd.potential l σ) y (unitVector j)) 2 volume := fun l j =>
    column_memLp j (Cert.Internal.ReadingEnergy.locallyIntegrable_column
      (hpin.potential_weak l σ).2.1 j).aestronglyMeasurable (h6 l)
  have hsL : ∀ l j, MemLp (fun y => fderiv ℝ (pd.generator l σ) y (unitVector j)) 2 volume := fun l j =>
    (((hXsC l σ).continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (compact_of_zero (R := R₀) fun y hy => by rw [hXsZ l σ y hy, ContinuousLinearMap.zero_apply])
  have hDL : ∀ j, MemLp (fun y => (∑ l, c l • (fderiv ℝ (pd.potential l σ) y
      - fderiv ℝ (pd.generator l σ) y)) (unitVector j)) 2 volume := by
    intro j
    refine (memLp_finsetSum' Finset.univ fun l _ => ((hoL l j).sub (hsL l j)).const_smul (c l)).ae_eq
      (Eventually.of_forall fun y => ?_)
    simp [Finset.sum_apply]
  have hGL : ∀ j, MemLp (fun y => G σ y (unitVector j)) 2 volume := fun j =>
    column_memLp j (Cert.Internal.ReadingEnergy.locallyIntegrable_column h1.2.1 j).aestronglyMeasurable h3
  have hTm : AEStronglyMeasurable (fun y => secondDerivTrace (H σ y)) volume := by
    have e : (fun y => secondDerivTrace (H σ y)) = fun y => ∑ j, H σ y (unitVector j) (unitVector j) := rfl
    rw [e]
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      (second_column_locallyIntegrable h2 j).aestronglyMeasurable
  exact trace_by_parts hf hR hfL hDL h2 hGL (memLp_two_of_lintegral hTm h4)

end Internal.PinCharge

open Internal.PinCharge CertCell.InstancePair.Internal.ByPartsMollify in
theorem pinChargeHolds_proof : PinChargeHolds := by
  intro k Γ P w₀ C R₀ ε ρ cn v g G H χ pd c hw hp hpin hχ hε hρ hcn herr hround
  have hXsC : ∀ l σ, ContDiff ℝ 1 (pd.generator l σ) := fun l => slice_contDiff (hpin.generator_smooth l)
  have hXsD : ∀ l, Continuous (fun z : ℝ × Space => fderiv ℝ (pd.generator l z.1) z.2) :=
    fun l => slice_fderiv_continuous (hpin.generator_smooth l)
  have hXsZ : ∀ l σ y, R₀ < ‖y‖ → fderiv ℝ (pd.generator l σ) y = 0 :=
    fun l σ y hy => fderiv_zero_outside (hpin.generator_support l σ) hy
  have hXsP : ∀ l σ, pd.generator l (σ + 1) = pd.generator l σ :=
    fun l σ => funext (hpin.generator_periodic l σ)
  have hadjc : Continuous (fun M : Space →L[ℝ] Space => ContinuousLinearMap.adjoint M) :=
    LinearIsometryEquiv.continuous _
  have hDc : ∀ l, Continuous (fun z : ℝ × Space =>
      fderiv ℝ (pd.generator l z.1) z.2 - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2)) :=
    fun l => (hXsD l).sub (hadjc.comp (hXsD l))
  have hSc : Continuous (fun z : ℝ × Space =>
      ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l z.1) z.2)) :=
    hadjc.comp (continuous_finsetSum _ fun l _ => (hXsD l).const_smul (c l))
  have hGm := Internal.aesm_period hp.measurable_gradient
  have IG := Internal.gradient_integrable hp
  have Iχ : ∀ l, Integrable (fun z : ℝ × Space => matSq (χ l z.1 z.2)) Internal.periodMeasure := fun l =>
    period_integrable (f := fun σ y => matSq (χ l σ y))
      (Internal.continuous_entrySq.comp_aestronglyMeasurable (hpin.pin_measurable l)) (fun _ _ => Internal.entrySq_nonneg _) (hχ l)
  have ID : ∀ l, Integrable (fun z : ℝ × Space => matSq (fderiv ℝ (pd.generator l z.1) z.2
      - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2))) Internal.periodMeasure := fun l =>
    compact_entrySq_integrable (M := fun σ y => fderiv ℝ (pd.generator l σ) y
      - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)) (hDc l)
      (fun σ y => by simp only [hXsP]) (R := R₀) (fun σ y hy => by
        show fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y) = 0
        rw [hXsZ l σ y hy, map_zero, sub_zero])
  have IT : Integrable (fun z : ℝ × Space => matSq (ContinuousLinearMap.adjoint
      (∑ l, c l • fderiv ℝ (pd.generator l z.1) z.2))) Internal.periodMeasure :=
    compact_entrySq_integrable
      (M := fun σ y => ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l σ) y))
      hSc (fun σ y => by simp only [hXsP]) (R := R₀) (fun σ y hy => by
        show ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l σ) y) = 0
        rw [Finset.sum_eq_zero fun l _ => by rw [hXsZ l σ y hy, smul_zero], map_zero])
  have hAm : AEStronglyMeasurable (fun z : ℝ × Space =>
      ∑ l, c l • (χ l z.1 z.2 - fderiv ℝ (pd.potential l z.1) z.2)) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
      ((hpin.pin_measurable l).sub (hpin.potentialGrad_measurable l)).const_smul (c l)
  have hZm : AEStronglyMeasurable (fun z : ℝ × Space =>
      ∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2)) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
      ((hpin.potential_measurable l).sub (hpin.generator_smooth l).continuous.aestronglyMeasurable).const_smul (c l)
  have hHm : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    continuous_trace.comp_aestronglyMeasurable hp.measurable_secondDeriv
  have IA := period_integrable (f := fun σ y => matSq (∑ l, c l • (χ l σ y - fderiv ℝ (pd.potential l σ) y)))
    (Internal.continuous_entrySq.comp_aestronglyMeasurable hAm) (fun _ _ => Internal.entrySq_nonneg _)
    (lt_of_le_of_lt hround ENNReal.ofReal_lt_top)
  have IZ := period_integrable (f := fun σ y => ‖∑ l, c l • (pd.potential l σ y - pd.generator l σ y)‖ ^ 2)
    ((continuous_norm.pow 2).comp_aestronglyMeasurable hZm) (fun _ _ => sq_nonneg _)
    (lt_of_le_of_lt herr ENNReal.ofReal_lt_top)
  have IH := period_integrable (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)
    ((continuous_norm.pow 2).comp_aestronglyMeasurable hHm) (fun _ _ => sq_nonneg _) hp.sumSecondPartials_finite
  have Pχ : ∀ l, Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (χ l z.1 z.2)) Internal.periodMeasure :=
    fun l => matrix_pairing_integrable hGm (Internal.aesm_period (hpin.pin_measurable l)) IG (Iχ l)
  have PD : ∀ l, Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (pd.generator l z.1) z.2
      - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2))) Internal.periodMeasure :=
    fun l => matrix_pairing_integrable hGm (hDc l).aestronglyMeasurable IG (ID l)
  have PA : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2)
      (∑ l, c l • (χ l z.1 z.2 - fderiv ℝ (pd.potential l z.1) z.2))) Internal.periodMeasure :=
    matrix_pairing_integrable hGm (Internal.aesm_period hAm) IG IA
  have PT : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2)
      (ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l z.1) z.2))) Internal.periodMeasure :=
    matrix_pairing_integrable hGm hSc.aestronglyMeasurable IG IT
  have PZ : Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2))
      (∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2))) Internal.periodMeasure :=
    vector_pairing_integrable (Internal.aesm_period hHm) (Internal.aesm_period hZm) IH IZ
  have hB := slice_by_parts c hp hpin herr
  have hT := slice_transpose c hp hpin
  have hid : ∀ z : ℝ × Space,
      (∑ l, c l * matInner (G z.1 z.2) (χ l z.1 z.2)) - ∑ l, c l * matInner (G z.1 z.2)
        (fderiv ℝ (pd.generator l z.1) z.2 - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2)) =
      matInner (G z.1 z.2) (∑ l, c l • (χ l z.1 z.2 - fderiv ℝ (pd.potential l z.1) z.2))
        + matInner (G z.1 z.2) (∑ l, c l • (fderiv ℝ (pd.potential l z.1) z.2 - fderiv ℝ (pd.generator l z.1) z.2))
        + matInner (G z.1 z.2) (ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l z.1) z.2)) := by
    intro z
    rw [adjoint_sum_smul, pairMatrix_sum_smul, pairMatrix_sum_smul, pairMatrix_sum_smul]
    simp only [pairMatrix_sub, mul_sub, Finset.sum_sub_distrib]
    ring
  have I1 : Integrable (fun z : ℝ × Space => ∑ l, c l * matInner (G z.1 z.2) (χ l z.1 z.2))
      Internal.periodMeasure := integrable_finsetSum _ fun l _ => (Pχ l).const_mul (c l)
  have I2 : Integrable (fun z : ℝ × Space => ∑ l, c l * matInner (G z.1 z.2)
      (fderiv ℝ (pd.generator l z.1) z.2 - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2)))
      Internal.periodMeasure := integrable_finsetSum _ fun l _ => (PD l).const_mul (c l)
  have PB : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2)
      (∑ l, c l • (fderiv ℝ (pd.potential l z.1) z.2 - fderiv ℝ (pd.generator l z.1) z.2)))
      Internal.periodMeasure := by
    refine (((I1.sub I2).sub PA).sub PT).congr (Eventually.of_forall fun z => ?_)
    have := hid z
    simp only [Pi.sub_apply]
    linarith
  have hTz : ∫ z, matInner (G z.1 z.2) (ContinuousLinearMap.adjoint
      (∑ l, c l • fderiv ℝ (pd.generator l z.1) z.2)) ∂Internal.periodMeasure = 0 := by
    rw [← Internal.iterated_eq (f := fun σ y => matInner (G σ y)
      (ContinuousLinearMap.adjoint (∑ l, c l • fderiv ℝ (pd.generator l σ) y))) PT, integral_congr_ae hT]
    simp
  have hBz : ∫ z, matInner (G z.1 z.2)
      (∑ l, c l • (fderiv ℝ (pd.potential l z.1) z.2 - fderiv ℝ (pd.generator l z.1) z.2)) ∂Internal.periodMeasure =
      -∫ z, inner ℝ (secondDerivTrace (H z.1 z.2))
        (∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2)) ∂Internal.periodMeasure := by
    rw [← Internal.iterated_eq (f := fun σ y => matInner (G σ y)
        (∑ l, c l • (fderiv ℝ (pd.potential l σ) y - fderiv ℝ (pd.generator l σ) y))) PB,
      ← Internal.iterated_eq (f := fun σ y => inner ℝ (secondDerivTrace (H σ y))
        (∑ l, c l • (pd.potential l σ y - pd.generator l σ y))) PZ, integral_congr_ae hB, integral_neg]
  have hpv : ∀ l, pinValue (χ l) G = ∫ z, matInner (G z.1 z.2) (χ l z.1 z.2) ∂Internal.periodMeasure :=
    fun l => Internal.iterated_eq (f := fun σ y => matInner (G σ y) (χ l σ y)) (Pχ l)
  have hpm : ∀ l, periodMatrixIntegral G (fun σ y => fderiv ℝ (pd.generator l σ) y
      - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)) =
      ∫ z, matInner (G z.1 z.2) (fderiv ℝ (pd.generator l z.1) z.2
        - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l z.1) z.2)) ∂Internal.periodMeasure :=
    fun l => Internal.iterated_eq (f := fun σ y => matInner (G σ y) (fderiv ℝ (pd.generator l σ) y
      - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y))) (PD l)
  have hX : (∑ l, c l * pinValue (χ l) G) - ∑ l, c l * periodMatrixIntegral G (fun σ y =>
      fderiv ℝ (pd.generator l σ) y - ContinuousLinearMap.adjoint (fderiv ℝ (pd.generator l σ) y)) =
      (∫ z, matInner (G z.1 z.2) (∑ l, c l • (χ l z.1 z.2 - fderiv ℝ (pd.potential l z.1) z.2))
        ∂Internal.periodMeasure)
      - ∫ z, inner ℝ (secondDerivTrace (H z.1 z.2))
        (∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2)) ∂Internal.periodMeasure := by
    have e1 := integral_congr_ae (μ := Internal.periodMeasure) (Eventually.of_forall hid)
    rw [integral_sub I1 I2, integral_finsetSum _ fun l _ => (Pχ l).const_mul (c l),
      integral_finsetSum _ fun l _ => (PD l).const_mul (c l), integral_add, integral_add, hBz, hTz] at e1
    · simp only [integral_const_mul, ← hpv, ← hpm] at e1
      linarith
    all_goals first | exact PT | exact PA.add PB | exact PA | exact PB
  have hE : weightedEnergy (fun _ => w₀) G H = (∫ z, ‖secondDerivTrace (H z.1 z.2)‖ ^ 2 ∂Internal.periodMeasure)
      + w₀ * ∫ z, matSq (G z.1 z.2) ∂Internal.periodMeasure := by
    have hI := IH.add (IG.const_mul w₀)
    rw [← integral_const_mul, ← integral_add IH (IG.const_mul w₀)]
    have hm : AEStronglyMeasurable (fun z : ℝ × Space =>
        ‖secondDerivTrace (H z.1 z.2)‖ ^ 2 + w₀ * matSq (G z.1 z.2)) Internal.periodMeasure := hI.aestronglyMeasurable
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun z : ℝ × Space =>
        add_nonneg (sq_nonneg _) (mul_nonneg hw.le (Internal.entrySq_nonneg _))) hm,
      ← Internal.periodL_eq (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w₀ * matSq (G σ y))
        hm.aemeasurable.ennreal_ofReal]
    rfl
  have s0 : 0 ≤ ∑ l, c l ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hbA := integral_le_of_period (f := fun σ y => matSq (∑ l, c l • (χ l σ y - fderiv ℝ (pd.potential l σ) y)))
    (Internal.continuous_entrySq.comp_aestronglyMeasurable hAm) (fun _ _ => Internal.entrySq_nonneg _)
    (mul_nonneg (sq_nonneg ρ) s0) hround
  have hbZ := integral_le_of_period (f := fun σ y => ‖∑ l, c l • (pd.potential l σ y - pd.generator l σ y)‖ ^ 2)
    ((continuous_norm.pow 2).comp_aestronglyMeasurable hZm) (fun _ _ => sq_nonneg _)
    (sq_nonneg ε) herr
  have hsZ : Real.sqrt (∫ z, ‖∑ l, c l • (pd.potential l z.1 z.2 - pd.generator l z.1 z.2)‖ ^ 2
      ∂Internal.periodMeasure) ≤ ε :=
    (Real.sqrt_le_sqrt hbZ).trans (Real.sqrt_sq hε).le
  have hA1 := abs_integral_le PA IG IA (fun _ => Internal.entrySq_nonneg _) (fun _ => Internal.entrySq_nonneg _)
    fun u hu z => abs_pairMatrix_le _ _ hu
  have hZ1 := abs_integral_le PZ IH IZ (fun _ => sq_nonneg _) (fun _ => sq_nonneg _)
    fun u hu z => abs_inner_le _ _ hu
  exact final_bound hX hA1 hZ1 (sqrt_bound hbA hρ hcn) hsZ hE hw
    (integral_nonneg fun _ => Internal.entrySq_nonneg _) (integral_nonneg fun _ => sq_nonneg _) hε hρ
    ((Real.sqrt_nonneg _).trans hcn)

end AdjointDefect

end Breakdown

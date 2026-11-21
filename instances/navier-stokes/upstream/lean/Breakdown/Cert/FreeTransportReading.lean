import Breakdown.Cert.Nodes
import Breakdown.Cert.JointRepresentative
import Breakdown.Cert.PeriodIntegral
import Breakdown.Cert.SliceFields
import Breakdown.Weak.VelocityWeakGradient
import Breakdown.FreqTr.Realization

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.FreePerturbation

def transportCurve (f : HH) (u : XX) : Lp (α := TimeCircle) L2R 2 :=
  ContinuousLinearMap.compLpL 2 volume toPhysH f -
    ContinuousLinearMap.compLpL 2 volume (toPhysH.comp secondPart) u

def IsTransportPart (f : HH) (u : XX) (g : ℝ → Space → Space) : Prop :=
  AEStronglyMeasurable (fun z : ℝ × Space => g z.1 z.2) volume ∧ IsTimePeriodic g ∧
    ∀ᵐ σ : ℝ, ((transportCurve f u (σ : TimeCircle) : L2R) : Space → Space) =ᵐ[volume] g σ

theorem exists_transportPart (f : HH) (u : XX) : ∃ g, IsTransportPart f u g :=
  exists_joint_representative (transportCurve f u)

theorem locallyIntegrable_column {g : Space → (Space →L[ℝ] Space)} (hg : LocallyIntegrable g volume)
    (i : Fin 3) : LocallyIntegrable (fun y => g y (unitVector i)) volume := by
  intro x
  obtain ⟨U, hU, hi⟩ := hg x
  exact ⟨U, hU, (ContinuousLinearMap.apply ℝ Space (unitVector i)).integrable_comp hi⟩

theorem column_ae_eq_partialX (x : X) {f : Space → Space} {g : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f g) (hf : f =ᵐ[volume] (velocity x : Space → Space)) (i : Fin 3) :
    (fun y => g y (unitVector i)) =ᵐ[volume] (partialX i x : Space → Space) := by
  refine ae_eq_of_integral_contDiff_smul_eq (locallyIntegrable_column hg.2.1 i)
    ((Lp.memLp (partialX i x)).locallyIntegrable (by norm_num)) fun φ hφ hφc => ?_
  rw [hg.2.2 φ ⟨hφ, hφc⟩ i, WeakProfile.velocityWeakGradient_holds x φ ⟨hφ, hφc⟩ i]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hf] with y hy
  rw [hy]

theorem lintegral_enorm_sq_Lp {α : Type*} [MeasurableSpace α] {μ : Measure α} {F : Type*}
    [NormedAddCommGroup F] (f : Lp F 2 μ) : ∫⁻ y, ‖(f : α → F) y‖ₑ ^ 2 ∂μ = ‖f‖ₑ ^ 2 := by
  rw [Lp.enorm_def, JointRepresentativeInternal.sq_eLpNorm_two]

theorem ofReal_sum_norm_sq {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] (a : ι → F) :
    ENNReal.ofReal (∑ i, ‖a i‖ ^ 2) = ∑ i, ‖a i‖ₑ ^ 2 := by
  rw [ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem lintegral_sum_slices {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    (c : ι → Lp (α := Space) F 2) :
    ∫⁻ y, ENNReal.ofReal (∑ i, ‖(c i : Space → F) y‖ ^ 2) = ∑ i, ‖c i‖ₑ ^ 2 := by
  simp only [ofReal_sum_norm_sq]
  rw [lintegral_finsetSum' _ fun i _ => (Lp.aestronglyMeasurable (c i)).enorm.pow_const 2]
  exact Finset.sum_congr rfl fun i _ => lintegral_enorm_sq_Lp (c i)

theorem lintegral_sum_curve {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    (c : ι → Lp (α := TimeCircle) E 2) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∑ i, ‖c i (σ : TimeCircle)‖ₑ ^ 2 < ⊤ := by
  have hm : ∀ i, AEMeasurable (fun t : TimeCircle => ‖c i t‖ₑ ^ 2) volume := fun i =>
    (Lp.aestronglyMeasurable (c i)).enorm.pow_const 2
  have hs : AEMeasurable (fun t : TimeCircle => ∑ i, ‖c i t‖ₑ ^ 2) volume :=
    Finset.aemeasurable_fun_sum _ fun i _ => hm i
  have h1 := lintegral_Icc_coe (fun t : TimeCircle => ∑ i, ‖c i t‖ₑ ^ 2) hs
  have h2 := lintegral_finsetSum' (μ := (volume : Measure TimeCircle)) Finset.univ fun i _ => hm i
  refine lt_of_eq_of_lt (h1.trans h2) (ENNReal.sum_lt_top.2 fun i _ => ?_)
  rw [lintegral_enorm_sq_Lp]
  exact ENNReal.pow_lt_top enorm_lt_top

theorem periodLIntegral_lt_top_of_slices {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]
    (c : ι → Lp (α := TimeCircle) (Lp (α := Space) F 2) 2) (q : ℝ → Space → ℝ)
    (h : ∀ᵐ σ : ℝ, ∀ᵐ y, q σ y = ∑ i, ‖((c i (σ : TimeCircle) : Lp (α := Space) F 2) : Space → F) y‖ ^ 2) :
    periodLIntegral q < ⊤ := by
  have hin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (q σ y) = ∑ i, ‖c i (σ : TimeCircle)‖ₑ ^ 2 := by
    refine ae_restrict_of_ae ?_
    filter_upwards [h] with σ hσ
    rw [← lintegral_sum_slices]
    exact lintegral_congr_ae (hσ.mono fun y hy => congrArg ENNReal.ofReal hy)
  unfold periodLIntegral
  rw [lintegral_congr_ae hin]
  exact lintegral_sum_curve c

theorem sumSecondPartials_finite_of_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
  refine periodLIntegral_lt_top_of_slices
    (fun _ : Unit => ContinuousLinearMap.compLpL 2 volume (toPhysH.comp secondPart) u) _ ?_
  have hc : ∀ᵐ σ : ℝ,
      (ContinuousLinearMap.compLpL 2 volume (toPhysH.comp secondPart) u (σ : TimeCircle) : L2R) =
        toPhysH (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) :=
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL _ u)
  filter_upwards [hr.trace_eq, hc] with σ h1 h2
  filter_upwards [h1] with y hy
  simp only [hy, h2, norm_neg, Finset.univ_unique, Finset.sum_singleton]

theorem derivative_finite_of_transportPart {f : HH} {u : XX} {g : ℝ → Space → Space}
    (hg : IsTransportPart f u g) : periodLIntegral (fun σ y => ‖g σ y‖ ^ 2) < ⊤ := by
  refine periodLIntegral_lt_top_of_slices (fun _ : Unit => transportCurve f u) _ ?_
  filter_upwards [hg.2.2] with σ h1
  filter_upwards [h1] with y hy
  simp only [hy, Finset.univ_unique, Finset.sum_singleton]

theorem continuous_secondDerivTrace : Continuous secondDerivTrace := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ =>
    (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp
      (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).continuous

def fullField (g : ℝ → Space → Space) (H : SecondField) : ℝ → Space → Space :=
  fun σ y => g σ y - secondDerivTrace (H σ y)

theorem transportCurve_ae (f : HH) (u : XX) : ∀ᵐ σ : ℝ,
    (transportCurve f u (σ : TimeCircle) : L2R) =
      toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) -
        toPhysH (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) := by
  refine (ae_coe_iff (fun t => (transportCurve f u t : L2R) = toPhysH ((f : TimeCircle → HBar) t) -
    toPhysH (secondPart ((u : TimeCircle → XBar) t)))).1 ?_
  unfold transportCurve
  filter_upwards [Lp.coeFn_sub (ContinuousLinearMap.compLpL 2 volume toPhysH f)
      (ContinuousLinearMap.compLpL 2 volume (toPhysH.comp secondPart) u),
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle)) toPhysH f,
    ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure TimeCircle))
      (toPhysH.comp secondPart) u] with t a b c
  exact a.trans (congrArg₂ (· - ·) b c)

theorem sub_sub_neg_self (a b : Space) : a - b - -b = a := by
  abel

theorem fullField_slices {f : HH} {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {g : ℝ → Space → Space} (hg : IsTransportPart f u g) :
    ∀ᵐ σ : ℝ, fullField g H σ =ᵐ[volume]
      (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) := by
  filter_upwards [hg.2.2, hr.trace_eq, transportCurve_ae f u] with σ h1 h2 h3
  filter_upwards [h1, h2, Lp.coeFn_sub (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)))
    (toPhysH (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))))] with y a b c
  have e1 : g σ y = (toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) : Space → Space) y -
      (toPhysH (secondPart ((u : TimeCircle → XBar) (σ : TimeCircle))) : Space → Space) y :=
    a.symm.trans ((congrArg (fun w : L2R => (w : Space → Space) y) h3).trans c)
  exact (congrArg₂ (fun p q : Space => p - q) e1 b).trans (sub_sub_neg_self _ _)

theorem isPeriodicField_fullField {f : HH} {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) {g : ℝ → Space → Space} (hg : IsTransportPart f u g) :
    IsPeriodicField (fullField g H) := by
  refine ⟨hg.1.sub (continuous_secondDerivTrace.comp_aestronglyMeasurable hr.measurable_second),
    fun σ y => by simp only [fullField, hg.2.1 σ y, hr.periodic_second σ y], ?_⟩
  refine periodLIntegral_lt_top_of_slices
    (fun _ : Unit => ContinuousLinearMap.compLpL 2 volume toPhysH f) _ ?_
  have hc : ∀ᵐ σ : ℝ, (ContinuousLinearMap.compLpL 2 volume toPhysH f (σ : TimeCircle) : L2R) =
      toPhysH ((f : TimeCircle → HBar) (σ : TimeCircle)) :=
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL _ f)
  filter_upwards [fullField_slices hr hg, hc] with σ h1 h2
  filter_upwards [h1] with y hy
  simp only [hy, h2, Finset.univ_unique, Finset.sum_singleton]

theorem lintegral_unit_of_periodic (q : ℝ → ℝ≥0∞) (hq : ∀ σ, q (σ + 1) = q σ) (k : ℝ) :
    ∫⁻ σ in Set.Ioc k (k + 1), q σ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, q σ := by
  have hl : ∀ σ : ℝ, Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq (σ : AddCircle (1 : ℝ)) = q σ :=
    fun σ => Function.Periodic.lift_coe _ _
  have h1 := AddCircle.lintegral_preimage (T := (1 : ℝ)) k (Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq)
  have h0 := AddCircle.lintegral_preimage (T := (1 : ℝ)) 0 (Function.Periodic.lift (c := (1 : ℝ)) (f := q) hq)
  simp only [hl, zero_add] at h1 h0
  rw [h1, ← h0, Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem lintegral_Ioc_le_of_unit (q : ℝ → ℝ≥0∞) (c : ℝ≥0∞)
    (hc : ∀ k : ℝ, ∫⁻ σ in Set.Ioc k (k + 1), q σ = c) (a : ℝ) (n : ℕ) :
    ∫⁻ σ in Set.Ioc a (a + n), q σ ≤ n * c := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hs : Set.Ioc a (a + ((n + 1 : ℕ) : ℝ)) = Set.Ioc a (a + n) ∪ Set.Ioc (a + n) (a + n + 1) := by
      rw [Set.Ioc_union_Ioc_eq_Ioc (by simp) (by linarith)]
      push_cast
      ring_nf
    rw [hs]
    refine (lintegral_union_le _ _ _).trans ?_
    rw [hc (a + n)]
    calc (∫⁻ σ in Set.Ioc a (a + n), q σ) + c ≤ n * c + c := add_le_add ih le_rfl
      _ = ((n + 1 : ℕ) : ℝ≥0∞) * c := by push_cast; ring

theorem integrable_inner_of_periodic {F : ℝ → Space → Space}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hp : IsTimePeriodic F)
    (hf : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) {ψ : ℝ → Space → Space}
    (hψc : Continuous (fun z : ℝ × Space => ψ z.1 z.2))
    (hψs : HasCompactSupport (fun z : ℝ × Space => ψ z.1 z.2)) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ψ z.1 z.2)) := by
  obtain ⟨r, hr⟩ := hψs.isCompact.isBounded.subset_closedBall (0 : ℝ × Space)
  obtain ⟨C, hC⟩ := hψc.bounded_above_of_compact_support hψs
  set N : ℕ := ⌈r⌉₊ + 1 with hN
  set S : Set (ℝ × Space) := Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)) ×ˢ Metric.closedBall (0 : Space) r
  have hrN : r < N := by
    rw [hN]; push_cast; linarith [Nat.le_ceil r]
  have hsupp : ∀ z, z ∉ S → ψ z.1 z.2 = 0 := by
    intro z hz
    refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => ψ z.1 z.2) fun ht => hz ?_
    have h1 := hr ht
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    have h2 : ‖z.1‖ ≤ r := (norm_fst_le z).trans h1
    have h3 : ‖z.2‖ ≤ r := (norm_snd_le z).trans h1
    rw [Real.norm_eq_abs, abs_le] at h2
    refine ⟨⟨by linarith, ?_⟩, by rw [Metric.mem_closedBall, dist_zero_right]; exact h3⟩
    push_cast
    linarith
  have hS : volume S < ⊤ := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top measure_Ioc_lt_top measure_closedBall_lt_top
  have : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.2 hS.ne
  have hq : ∀ σ, (fun σ => ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)) (σ + 1) =
      (fun σ => ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)) σ := fun σ => by
    simp only [hp σ]
  have hlin : ∫⁻ z in S, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) < ⊤ := by
    have hsub : S ⊆ Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)) ×ˢ Set.univ :=
      Set.prod_mono le_rfl (Set.subset_univ _)
    refine lt_of_le_of_lt (lintegral_mono_set hsub) ?_
    have h0 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
        ((volume : Measure ℝ).prod (volume : Measure Space)) := by
      have h1 : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2)) volume :=
        (hm.norm.aemeasurable.pow_const 2).ennreal_ofReal
      rwa [Measure.volume_eq_prod] at h1
    have hle : (volume.restrict (Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)))).prod
        (volume : Measure Space) ≤ (volume : Measure ℝ).prod (volume : Measure Space) := by
      calc (volume.restrict (Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)))).prod (volume : Measure Space)
          = (volume.restrict (Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)))).prod
              ((volume : Measure Space).restrict Set.univ) := by rw [Measure.restrict_univ]
        _ = ((volume : Measure ℝ).prod (volume : Measure Space)).restrict
              (Set.Ioc (-(N : ℝ)) (-(N : ℝ) + ((2 * N : ℕ) : ℝ)) ×ˢ Set.univ) := Measure.prod_restrict _ _
        _ ≤ (volume : Measure ℝ).prod (volume : Measure Space) := Measure.restrict_le_self
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ,
      lintegral_prod _ (h0.mono_measure hle)]
    refine lt_of_le_of_lt (lintegral_Ioc_le_of_unit _ _
      (fun k => lintegral_unit_of_periodic _ hq k) _ _) ?_
    exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) hf
  have hL2 : MemLp (fun z : ℝ × Space => F z.1 z.2) 2 (volume.restrict S) := by
    refine (memLp_two_iff_integrable_sq_norm hm.restrict).2 ⟨(hm.norm.pow 2).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun z => sq_nonneg _)]
    exact hlin
  have hFi := hL2.integrable one_le_two
  have hon : IntegrableOn (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (ψ z.1 z.2)) S := by
    refine (hFi.norm.const_mul C).mono' (hm.restrict.inner hψc.aestronglyMeasurable.restrict)
      (ae_of_all _ fun z => ?_)
    calc ‖inner ℝ (F z.1 z.2) (ψ z.1 z.2)‖ ≤ ‖F z.1 z.2‖ * ‖ψ z.1 z.2‖ := norm_inner_le_norm _ _
      _ ≤ ‖F z.1 z.2‖ * C := mul_le_mul_of_nonneg_left (hC z) (norm_nonneg _)
      _ = C * ‖F z.1 z.2‖ := mul_comm _ _
  exact hon.integrable_of_forall_notMem_eq_zero fun z hz => by rw [hsupp z hz, inner_zero_right]

theorem inner_eq_sum_coord (a b : Space) : inner ℝ a b = ∑ k : Fin 3, a k * b k := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, mul_comm]

theorem isTestFunction_coord {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ)
    (k : Fin 3) : IsTestFunction (fun y => ψ y k) :=
  ⟨(EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hψ,
    hψs.comp_left (g := fun w : Space => w k) (by simp)⟩

theorem fderiv_coord {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (k : Fin 3) (y v : Space) :
    fderiv ℝ (fun y => ψ y k) y v = fderiv ℝ ψ y v k := by
  have hd : DifferentiableAt ℝ ψ y := (hψ.differentiable (by simp)) y
  have h := ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  have h2 : (fun y => ψ y k) = (EuclideanSpace.proj k : Space →L[ℝ] ℝ) ∘ ψ := rfl
  rw [h2, h]
  rfl

theorem slice_component {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (j k : Fin 3) :
    ∫ y, ψ y k * H y (unitVector j) (unitVector j) k =
      -∫ y, fderiv ℝ ψ y (unitVector j) k * G y (unitVector j) k := by
  have ht := isTestFunction_coord hψ hψs k
  have h := (hw j).2.2 _ ht j
  have hi1 : Integrable (fun y => ψ y k • (H y).flip (unitVector j) (unitVector j)) :=
    (locallyIntegrable_column (hw j).2.1 j).integrable_smul_left_of_hasCompactSupport ht.1.continuous ht.2
  have hi2 : Integrable (fun y => fderiv ℝ (fun y => ψ y k) y (unitVector j) • G y (unitVector j)) :=
    (hw j).1.integrable_smul_left_of_hasCompactSupport
      ((ht.1.continuous_fderiv (by simp)).clm_apply continuous_const) (ht.2.fderiv_apply (𝕜 := ℝ) _)
  have e1 := congrArg (fun w : Space => w k) h
  simp only [PiLp.neg_apply] at e1
  have e2 : ∫ y, (ψ y k • (H y).flip (unitVector j) (unitVector j)) k =
      (∫ y, ψ y k • (H y).flip (unitVector j) (unitVector j)) k :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hi1
  have e3 : ∫ y, (fderiv ℝ (fun y => ψ y k) y (unitVector j) • G y (unitVector j)) k =
      (∫ y, fderiv ℝ (fun y => ψ y k) y (unitVector j) • G y (unitVector j)) k :=
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm hi2
  rw [← e2, ← e3] at e1
  simp only [PiLp.smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply,
    fderiv_coord hψ] at e1
  exact e1

theorem coord_sum (v : Fin 3 → Space) (x : Fin 3) : (∑ j, v j) x = ∑ j, v j x :=
  map_sum (EuclideanSpace.proj x : Space →L[ℝ] ℝ) v Finset.univ

theorem slice_terms_integrable {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) (j k : Fin 3) :
    Integrable (fun y => ψ y k * H y (unitVector j) (unitVector j) k) ∧
      Integrable (fun y => fderiv ℝ ψ y (unitVector j) k * G y (unitVector j) k) := by
  have ht := isTestFunction_coord hψ hψs k
  have hi1 : Integrable (fun y => ψ y k • (H y).flip (unitVector j) (unitVector j)) :=
    (locallyIntegrable_column (hw j).2.1 j).integrable_smul_left_of_hasCompactSupport ht.1.continuous ht.2
  have hi2 : Integrable (fun y => fderiv ℝ (fun y => ψ y k) y (unitVector j) • G y (unitVector j)) :=
    (hw j).1.integrable_smul_left_of_hasCompactSupport
      ((ht.1.continuous_fderiv (by simp)).clm_apply continuous_const) (ht.2.fderiv_apply (𝕜 := ℝ) _)
  have e1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp hi1
  have e2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integrable_comp hi2
  refine ⟨e1.congr (ae_of_all _ fun y => ?_), e2.congr (ae_of_all _ fun y => ?_)⟩
  · show (ψ y k • (H y).flip (unitVector j) (unitVector j)) k = _
    simp only [PiLp.smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply]
  · show (fderiv ℝ (fun y => ψ y k) y (unitVector j) • G y (unitVector j)) k = _
    simp only [PiLp.smul_apply, smul_eq_mul, fderiv_coord hψ]

theorem slice_byParts {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hw : ∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j)))
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψs : HasCompactSupport ψ) :
    ∫ y, matInner (G y) (fderiv ℝ ψ y) = -∫ y, inner ℝ (secondDerivTrace (H y)) (ψ y) := by
  have hI := slice_terms_integrable hw hψ hψs
  have hl : (fun y => matInner (G y) (fderiv ℝ ψ y)) =
      fun y => ∑ j : Fin 3, ∑ k : Fin 3, fderiv ℝ ψ y (unitVector j) k * G y (unitVector j) k := by
    funext y
    simp only [matInner, inner_eq_sum_coord, mul_comm]
  have hr : (fun y => inner ℝ (secondDerivTrace (H y)) (ψ y)) =
      fun y => ∑ j : Fin 3, ∑ k : Fin 3, ψ y k * H y (unitVector j) (unitVector j) k := by
    funext y
    rw [Finset.sum_comm]
    simp only [secondDerivTrace, inner_eq_sum_coord, coord_sum]
    exact Finset.sum_congr rfl fun x _ => by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  rw [hl, hr, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hI j k).2,
    integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hI j k).1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_finsetSum _ fun k _ => (hI j k).2, integral_finsetSum _ fun k _ => (hI j k).1,
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [slice_component hw hψ hψs j k, neg_neg]

theorem fderiv_slice {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (s : ℝ) (y : Space) : fderiv ℝ (φ s) y =
      (fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => φ z.1 z.2) (s, y) := (hφ.differentiable (by simp)) _
  exact (hd.hasFDerivAt.comp y (hasFDerivAt_prodMk_right s y)).fderiv

theorem contDiff_slice {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (s : ℝ) : ContDiff ℝ ∞ (φ s) :=
  hφ.comp (contDiff_prodMk_right s)

theorem hasCompactSupport_slice {φ : ℝ → Space → Space}
    (hφ : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) (s : ℝ) : HasCompactSupport (φ s) := by
  refine HasCompactSupport.intro (hφ.isCompact.image continuous_snd) fun y hy => ?_
  refine image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => φ z.1 z.2) (x := (s, y)) fun ht => hy ?_
  exact ⟨(s, y), ht, rfl⟩

theorem partial_continuous {φ : ℝ → Space → Space} (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (j : Fin 3) : Continuous (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) =
      fun z => fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) z (ContinuousLinearMap.inr ℝ ℝ Space (unitVector j)) := by
    funext z
    rw [fderiv_slice hφ z.1 z.2]
    rfl
  rw [h]
  exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const

theorem partial_hasCompactSupport {φ : ℝ → Space → Space}
    (hφ : ContDiff ℝ ∞ (fun z : ℝ × Space => φ z.1 z.2))
    (hφs : HasCompactSupport (fun z : ℝ × Space => φ z.1 z.2)) (j : Fin 3) :
    HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) := by
  have h : (fun z : ℝ × Space => fderiv ℝ (φ z.1) z.2 (unitVector j)) =
      (fun L : ℝ × Space →L[ℝ] Space => L (ContinuousLinearMap.inr ℝ ℝ Space (unitVector j))) ∘
        fderiv ℝ (fun z : ℝ × Space => φ z.1 z.2) := by
    funext z
    rw [Function.comp_apply, fderiv_slice hφ z.1 z.2]
    rfl
  rw [h]
  exact (hφs.fderiv (𝕜 := ℝ)).comp_left (by simp)

theorem column_finite_of_reading {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (j : Fin 3) :
    periodLIntegral (fun σ y => ‖G σ y (unitVector j)‖ ^ 2) < ⊤ := by
  refine periodLIntegral_lt_top_of_slices
    (fun _ : Unit => ContinuousLinearMap.compLpL 2 volume ((partialX j).comp gradPart) u) _ ?_
  have hc : ∀ᵐ σ : ℝ,
      (ContinuousLinearMap.compLpL 2 volume ((partialX j).comp gradPart) u (σ : TimeCircle) : L2R) =
        partialX j (gradPart ((u : TimeCircle → XBar) (σ : TimeCircle))) :=
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL _ u)
  filter_upwards [hr.velocity_eq, hr.weak_gradient, hc] with σ h1 h2 h3
  filter_upwards [column_ae_eq_partialX _ h2 h1 j] with y hy
  simp only [hy, h3, Finset.univ_unique, Finset.sum_singleton]

theorem integral_matInner_eq {u : XX} {v : VelField} {G : GradField} {H : SecondField}
    (hr : IsReadingOf u v G H) (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestVector φ) :
    Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) ∧
      ∫ z : ℝ × Space, matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) =
        -∫ z : ℝ × Space, inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2) := by
  have hcol := column_finite_of_reading hr
  have hcm : ∀ j : Fin 3, AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector j)) volume :=
    fun j => (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous.comp_aestronglyMeasurable
      hr.measurable_gradient
  have hint : ∀ j : Fin 3, Integrable (fun z : ℝ × Space =>
      inner ℝ (G z.1 z.2 (unitVector j)) (fderiv ℝ (φ z.1) z.2 (unitVector j))) := fun j =>
    integrable_inner_of_periodic (F := fun σ y => G σ y (unitVector j))
      (ψ := fun s y => fderiv ℝ (φ s) y (unitVector j)) (hcm j)
      (fun σ y => by simp only [hr.periodic_gradient σ y]) (hcol j) (partial_continuous hφ.1 j)
      (partial_hasCompactSupport hφ.1 hφ.2 j)
  have hfe : (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) =
      fun z => ∑ j : Fin 3, inner ℝ (G z.1 z.2 (unitVector j)) (fderiv ℝ (φ z.1) z.2 (unitVector j)) := by
    funext z
    simp only [matInner]
  have hfi : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) := by
    rw [hfe]
    exact integrable_finsetSum _ fun j _ => hint j
  refine ⟨hfi, ?_⟩
  have htr : Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) :=
    integrable_inner_of_periodic (F := fun σ y => secondDerivTrace (H σ y))
      (continuous_secondDerivTrace.comp_aestronglyMeasurable hr.measurable_second)
      (fun σ y => by simp only [hr.periodic_second σ y]) (sumSecondPartials_finite_of_reading hr)
      hφ.1.continuous hφ.2
  rw [Measure.volume_eq_prod] at hfi htr ⊢
  rw [integral_prod _ hfi, integral_prod _ htr, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hr.weak_second] with σ hσ
  exact slice_byParts hσ (contDiff_slice hφ.1 σ) (hasCompactSupport_slice hφ.2 σ)

end Internal.FreePerturbation

end Breakdown.Cert

import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.ModeRadialLine
import Breakdown.FracCell.ModeHeightLine
import Breakdown.FracCell.LowEntry

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown.FracInternal.ModeHeightParts

open Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.CellCert.CellFormula
open Breakdown.CellCert.CellAnalysis.ModeRadialLineInternal

def unitAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

theorem unitAt_circle (θ : ℝ) : unitAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

def rowQ (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, unitAt q a k • EuclideanSpace.proj k

theorem rowQ_apply (a : Fin 3) (θ : ℝ) (u : Space) :
    rowQ a (Real.cos θ, Real.sin θ) u = inner ℝ u (frameUnit θ a) := by
  simp [rowQ, unitAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem unitAt_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [unitAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

theorem unitAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a) :=
  (contDiff_piLp 2).2 fun k => unitAt_coord_smooth a k

theorem rowQ_smooth (a : Fin 3) : ContDiff ℝ ∞ (rowQ a) := by
  unfold rowQ
  exact ContDiff.sum fun k _ => (unitAt_coord_smooth a k).smul contDiff_const

def entQ (a b : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (rowQ a q).comp (ContinuousLinearMap.apply ℝ Space (unitAt q b))

theorem entQ_smooth (a b : Fin 3) : ContDiff ℝ ∞ (entQ a b) :=
  (rowQ_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (unitAt_smooth b))

theorem entQ_apply (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    entQ a b (Real.cos θ, Real.sin θ) M = frameMat θ M a b := by
  simp only [entQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  exact rowQ_apply a θ _

theorem vec_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem memLp_of_entry {A : Space → (Space →L[ℝ] Space)} (h1 : AEStronglyMeasurable A volume)
    (h2 : Integrable (fun y => entrySq (A y))) : MemLp A 2 volume := by
  refine (memLp_two_iff_integrable_sq_norm h1).2 ((h2.const_mul 3).mono'
    ((h1.norm.aemeasurable.pow_const 2).aestronglyMeasurable) (Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact EmbedWeak.Internal.norm_sq_le (A y)

theorem col_entry {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j : Fin 3) :
    Integrable (fun y => entrySq (H y (unitVector j))) := by
  have hc : ∀ i, AEStronglyMeasurable (fun y => ‖H y (unitVector j) (unitVector i)‖ ^ 2) volume :=
    fun i => ((hm.apply_continuousLinearMap _).apply_continuousLinearMap _).norm.pow 2
  refine h2.mono' ?_ (Eventually.of_forall fun y => ?_)
  · simp only [entrySq, Fin.sum_univ_three]
    exact ((hc 0).add (hc 1)).add (hc 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold entrySq; positivity)]
    exact Finset.single_le_sum (f := fun j' => ∑ i : Fin 3, ‖H y (unitVector j') (unitVector i)‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem weak_clm {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : LocallyIntegrable G volume) (hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume)
    (hw : IsWeakSecondDerivOf G H) (φ : Space → ℝ) (hφ : IsTestScalar φ) (j : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
    hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
    (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
      (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
    intro i
    rw [neg_apply, ContinuousLinearMap.integral_apply i1,
      ContinuousLinearMap.integral_apply i2]
    simpa using hw φ hφ i j
  refine ContinuousLinearMap.ext fun u => ?_
  rw [vec_expand u]
  simp only [map_sum, map_smul, key]

theorem scale {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem weak_pair {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p =
      -∫ p, (ψ p : ℂ) * gradMode m n (fun y => H y axialUnit) a b p := by
  have hG : LocallyIntegrable G volume :=
    (memLp_of_entry hs.measurable_gradient hs.gradient_two).locallyIntegrable (by norm_num)
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    (memLp_of_entry (hs.measurable_second.apply_continuousLinearMap _)
      (col_entry hs.measurable_second hs.second_two j)).locallyIntegrable (by norm_num)
  have e := (cylModeWeak (Space →L[ℝ] Space) G H hG hHc (weak_clm hG hHc hs.weak_second) (entQ a b)
    (entQ_smooth a b) m n ψ hψ hc hpos).2
  have hgm : ∀ (A : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ), gradMode m n A a b p =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (entQ a b (Real.cos θ, Real.sin θ) (A (cylPoint p.1 θ p.2)) : ℂ) := by
    intro A p
    simp only [gradMode, modeMat, entQ_apply]
  simp only [hgm]
  exact scale _ e

theorem test_smooth (k : ℕ) (x y : ℝ) : ContDiff ℝ ∞ (test k x y) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun r => (test_hasDeriv k x y r).differentiableAt, ?_⟩
  rw [show deriv (test k x y) = fun r => kern k (r - x) - kern k (r - y) from funext (test_deriv k x y)]
  have hk : ContDiff ℝ ∞ (kern k) := by
    show ContDiff ℝ ∞ (fun t => (bumpAt k).normed volume t)
    exact (bumpAt k).contDiff_normed
  exact (hk.comp (contDiff_id.sub contDiff_const)).sub (hk.comp (contDiff_id.sub contDiff_const))

theorem weight_smooth (K : CellBox) : ContDiff ℝ ∞ K.lineWeight := by
  by_cases h0 : K.r₁ = 0
  · have : K.lineWeight = fun r => r := by funext r; rw [CellBox.lineWeight, if_pos h0]
    rw [this]; exact contDiff_id
  · have : K.lineWeight = fun _ => 1 := by funext r; rw [CellBox.lineWeight, if_neg h0]
    rw [this]; exact contDiff_const

theorem rect_eq' (K : CellBox) :
    volume.restrict K.rect = (volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂)) :=
  Internal.ModeHeightLine.rect_eq K

theorem bdd_int (K : CellBox) {F : ℝ × ℝ → ℂ} (hF : IntegrableOn F K.rect) (c : ℝ × ℝ → ℂ)
    (hc : Continuous c) : IntegrableOn (fun p => F p * c p) K.rect := by
  obtain ⟨C, hC⟩ := (LowEntry.Internal.rect_compact K).exists_bound_of_continuousOn hc.continuousOn
  have h := Integrable.bdd_mul (c := C) hF hc.aestronglyMeasurable
    (by filter_upwards [ae_restrict_mem (LowEntry.Internal.rect_meas K)] with p hp; exact hC p hp)
  exact h.congr (Eventually.of_forall fun p => mul_comm _ _)

theorem hd_cont {ψ : ℝ × ℝ → ℂ} (hψ : ContDiff ℝ 1 ψ) : Continuous (CellBox.heightDeriv ψ) := by
  have e : CellBox.heightDeriv ψ = fun p => fderiv ℝ ψ p (0, 1) := by
    funext p
    obtain ⟨r, z⟩ := p
    exact (((hψ.differentiable one_ne_zero) (r, z)).hasFDerivAt.comp_hasDerivAt z
      ((hasDerivAt_const z r).prodMk (hasDerivAt_id' z))).deriv
  rw [e]
  exact (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const


theorem ibp_line {a b : ℝ} (hab : a < b) {u q : ℝ → ℂ} {L : ℂ} (hq : IntegrableOn q (Icc a b))
    (hu : ∀ᵐ z ∂(volume.restrict (Icc a b)), u z = L - ∫ t in z..b, q t)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f) (ha : f a = 0) (hb : f b = 0) :
    ∫ z in Icc a b, u z * deriv f z = -∫ z in Icc a b, q z * f z := by
  have hdf : Continuous (deriv f) := hf.continuous_deriv le_rfl
  have hqi : ∀ c d, c ∈ Icc a b → d ∈ Icc a b → IntervalIntegrable q volume c d := fun c d hc hd =>
    (hq.mono_set (uIcc_subset_Icc hc hd)).intervalIntegrable
  have hu' : ∀ᵐ z ∂(volume.restrict (Icc a b)), u z * deriv f z =
      (L - ∫ t in a..b, q t) * deriv f z + (∫ t in a..z, q t) * deriv f z := by
    filter_upwards [hu, ae_restrict_mem measurableSet_Icc] with z hz hzm
    rw [hz, ← intervalIntegral.integral_interval_sub_left (hqi a b ⟨le_rfl, hab.le⟩ ⟨hab.le, le_rfl⟩)
      (hqi a z ⟨le_rfl, hab.le⟩ hzm)]
    ring
  have hPc : ContinuousOn (fun z => ∫ t in a..z, q t) (Icc a b) := by
    have := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := q) (a := a) (b := b)
      (by rw [uIcc_of_le hab.le]; exact hq)
    rwa [uIcc_of_le hab.le] at this
  have i1 : IntegrableOn (fun z => (L - ∫ t in a..b, q t) * deriv f z) (Icc a b) :=
    (continuous_const.mul hdf).continuousOn.integrableOn_compact isCompact_Icc
  have i2 : IntegrableOn (fun z => (∫ t in a..z, q t) * deriv f z) (Icc a b) :=
    (hPc.mul hdf.continuousOn).integrableOn_compact isCompact_Icc
  have hdiff : ∀ x ∈ uIcc a b, DifferentiableAt ℝ f x := fun x _ =>
    (hf.differentiable one_ne_zero).differentiableAt
  have hI : ∫ z in Icc a b, deriv f z = 0 := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
      intervalIntegral.integral_deriv_eq_sub' f rfl hdiff hdf.continuousOn, ha, hb, sub_zero]
  rw [integral_congr_ae hu', integral_add i1 i2, integral_const_mul, hI, mul_zero, zero_add,
    Internal.ModeHeightLine.primitive_ibp hab.le hq hdf, ← integral_neg]
  refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
  have hdz : ∀ x ∈ uIcc z b, DifferentiableAt ℝ f x := fun x _ =>
    (hf.differentiable one_ne_zero).differentiableAt
  rw [intervalIntegral.integral_deriv_eq_sub' f rfl hdz hdf.continuousOn, hb]
  ring

theorem line_zero (K : CellBox) (hK : IsCellBox K) {g h : ℝ × ℝ → ℂ}
    (hW : ∀ Ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → (∀ p ∈ tsupport Ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ Ψ p (0, 1) : ℝ) : ℂ) * g p = -∫ p, (Ψ p : ℂ) * h p)
    (hg : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p) K.rect)
    (hh : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * h p) K.rect)
    (k : ℕ) (x y : ℝ) (hx1 : K.z₁ < x - width k) (hx2 : x + width k < K.z₂)
    (hy1 : K.z₁ < y - width k) (hy2 : y + width k < K.z₂) :
    ∀ᵐ r ∂(volume.restrict (Icc K.r₁ K.r₂)), r ∈ Ioo K.r₁ K.r₂ →
      ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) * ((deriv (test k x y) z : ℝ) : ℂ) +
        (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) = 0 := by
  have hTc : Continuous (test k x y) := test_cont k x y
  have hdTc : Continuous (deriv (test k x y)) := test_deriv_cont k x y
  have hA : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * g p *
      ((deriv (test k x y) p.2 : ℝ) : ℂ)) K.rect :=
    bdd_int K hg (fun p => ((deriv (test k x y) p.2 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hdTc.comp continuous_snd))
  have hB : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * h p * ((test k x y p.2 : ℝ) : ℂ)) K.rect :=
    bdd_int K hh (fun p => ((test k x y p.2 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hTc.comp continuous_snd))
  have hj : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * g p * ((deriv (test k x y) p.2 : ℝ) : ℂ) +
      (K.lineWeight p.1 : ℂ) * h p * ((test k x y p.2 : ℝ) : ℂ)) K.rect := Integrable.add hA hB
  have hj' := hj
  rw [IntegrableOn, rect_eq'] at hj'
  have hF : Integrable (fun r => ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) *
      ((deriv (test k x y) z : ℝ) : ℂ) + (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)))
      (volume.restrict (Icc K.r₁ K.r₂)) := hj'.integral_prod_left
  refine isOpen_Ioo.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hF.integrableOn (s := Ioo K.r₁ K.r₂)).locallyIntegrableOn ?_
  intro φ hφ hφc hφs
  set Ψ : ℝ × ℝ → ℝ := fun p => φ p.1 * K.lineWeight p.1 * test k x y p.2 with hΨ
  set S : Set (ℝ × ℝ) := tsupport φ ×ˢ Icc (min x y - width k) (max x y + width k) with hSdef
  have hScomp : IsCompact S := hφc.isCompact.prod isCompact_Icc
  have hS0 : ∀ p, p ∉ S → Ψ p = 0 := by
    intro p hp
    by_cases h1 : p.1 ∈ tsupport φ
    · have h2 : p.2 ∉ Icc (min x y - width k) (max x y + width k) := fun h2 => hp ⟨h1, h2⟩
      rw [mem_Icc, not_and_or, not_le, not_le] at h2
      have hT0 : test k x y p.2 = 0 := by
        rcases h2 with h2 | h2
        · exact test_left k (by linarith [min_le_left x y]) (by linarith [min_le_right x y])
        · exact test_right k (by linarith [le_max_left x y]) (by linarith [le_max_right x y])
      simp [hΨ, hT0]
    · simp [hΨ, image_eq_zero_of_notMem_tsupport h1]
  have hsub : S ⊆ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ := by
    rintro p ⟨h1, h2⟩
    have hm1 := lt_min (show K.z₁ + width k < x by linarith) (show K.z₁ + width k < y by linarith)
    have hm2 := max_lt (show x < K.z₂ - width k by linarith) (show y < K.z₂ - width k by linarith)
    exact ⟨hφs h1, by linarith [h2.1], by linarith [h2.2]⟩
  have hsubR : S ⊆ K.rect := fun p hp =>
    ⟨⟨(hsub hp).1.1.le, (hsub hp).1.2.le⟩, ⟨(hsub hp).2.1.le, (hsub hp).2.2.le⟩⟩
  have htsub : tsupport Ψ ⊆ S :=
    closure_minimal (fun p hp => by_contra fun h => hp (hS0 p h)) hScomp.isClosed
  have hΨc : HasCompactSupport Ψ := HasCompactSupport.intro hScomp hS0
  have hpos : ∀ p ∈ tsupport Ψ, 0 < p.1 := fun p hp =>
    lt_of_le_of_lt hK.r_order.1 (hsub (htsub hp)).1.1
  have hΨs : ContDiff ℝ ∞ Ψ :=
    ((hφ.comp contDiff_fst).mul ((weight_smooth K).comp contDiff_fst)).mul
      ((test_smooth k x y).comp contDiff_snd)
  have hder : ∀ p : ℝ × ℝ, fderiv ℝ Ψ p (0, 1) = φ p.1 * K.lineWeight p.1 * deriv (test k x y) p.2 := by
    rintro ⟨r, z⟩
    have h1 : HasDerivAt (fun t => Ψ (r, t)) (fderiv ℝ Ψ (r, z) (0, 1)) z :=
      ((hΨs.differentiable (by simp)) (r, z)).hasFDerivAt.comp_hasDerivAt z
        ((hasDerivAt_const z r).prodMk (hasDerivAt_id' z))
    have h2 : HasDerivAt (fun t => Ψ (r, t)) (φ r * K.lineWeight r * deriv (test k x y) z) z :=
      ((test_hasDeriv k x y z).differentiableAt.hasDerivAt).const_mul (φ r * K.lineWeight r)
    exact h1.unique h2
  have hvan1 : ∀ p, p ∉ K.rect → ((fderiv ℝ Ψ p (0, 1) : ℝ) : ℂ) * g p = 0 := by
    intro p hp
    have : fderiv ℝ Ψ p = 0 :=
      Function.notMem_support.1 fun h => hp (hsubR (htsub (support_fderiv_subset ℝ h)))
    simp [this]
  have hvan2 : ∀ p, p ∉ K.rect → (Ψ p : ℂ) * h p = 0 := fun p hp => by
    simp [hS0 p fun h => hp (hsubR h)]
  have hw := hW Ψ hΨs hΨc hpos
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hvan1,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero hvan2] at hw
  simp only [hder] at hw
  have hA' : IntegrableOn (fun p : ℝ × ℝ => ((φ p.1 * K.lineWeight p.1 * deriv (test k x y) p.2 : ℝ) : ℂ) * g p)
      K.rect := by
    refine Integrable.congr (bdd_int K hg (fun p => ((φ p.1 * deriv (test k x y) p.2 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp
      ((hφ.continuous.comp continuous_fst).mul (hdTc.comp continuous_snd)))) (Eventually.of_forall fun p => ?_)
    push_cast; ring
  have hB' : IntegrableOn (fun p : ℝ × ℝ => ((Ψ p : ℝ) : ℂ) * h p) K.rect := by
    refine Integrable.congr (bdd_int K hh (fun p => ((φ p.1 * test k x y p.2 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp
      ((hφ.continuous.comp continuous_fst).mul (hTc.comp continuous_snd)))) (Eventually.of_forall fun p => ?_)
    simp only [hΨ]; push_cast; ring
  have hΦ : Integrable (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℂ) * g p * ((deriv (test k x y) p.2 : ℝ) : ℂ) +
      (K.lineWeight p.1 : ℂ) * h p * ((test k x y p.2 : ℝ) : ℂ)) * ((φ p.1 : ℝ) : ℂ))
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := by
    have := bdd_int K hj (fun p => ((φ p.1 : ℝ) : ℂ)) (Complex.continuous_ofReal.comp (hφ.continuous.comp continuous_fst))
    rwa [IntegrableOn, rect_eq'] at this
  have hsm : ∀ r, φ r • ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) *
        ((deriv (test k x y) z : ℝ) : ℂ) + (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) =
      ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) * ((deriv (test k x y) z : ℝ) : ℂ) +
        (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) * ((φ r : ℝ) : ℂ) := by
    intro r
    rw [Complex.real_smul, ← integral_const_mul]
    congr 1; funext z; ring
  simp only [hsm]
  have hprod : ∫ p in K.rect, ((K.lineWeight p.1 : ℂ) * g p * ((deriv (test k x y) p.2 : ℝ) : ℂ) +
      (K.lineWeight p.1 : ℂ) * h p * ((test k x y p.2 : ℝ) : ℂ)) * ((φ p.1 : ℝ) : ℂ) =
      ∫ r in Icc K.r₁ K.r₂, ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) *
        ((deriv (test k x y) z : ℝ) : ℂ) + (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) *
          ((φ r : ℝ) : ℂ) := by
    rw [rect_eq']; exact integral_prod _ hΦ
  rw [← hprod]
  have hsplit : (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℂ) * g p * ((deriv (test k x y) p.2 : ℝ) : ℂ) +
      (K.lineWeight p.1 : ℂ) * h p * ((test k x y p.2 : ℝ) : ℂ)) * ((φ p.1 : ℝ) : ℂ)) =
      fun p => ((φ p.1 * K.lineWeight p.1 * deriv (test k x y) p.2 : ℝ) : ℂ) * g p + ((Ψ p : ℝ) : ℂ) * h p := by
    funext p; simp only [hΨ]; push_cast; ring
  rw [hsplit, integral_add hA' hB', hw, neg_add_cancel]

theorem parts_of_weak (K : CellBox) (hK : IsCellBox K) {g h : ℝ × ℝ → ℂ}
    (hW : ∀ Ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ Ψ → HasCompactSupport Ψ → (∀ p ∈ tsupport Ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ Ψ p (0, 1) : ℝ) : ℂ) * g p = -∫ p, (Ψ p : ℂ) * h p)
    (hg : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * g p) K.rect)
    (hh : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * h p) K.rect)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ 1 ψ) (h1 : ∀ r, ψ (r, K.z₁) = 0) (h2 : ∀ r, ψ (r, K.z₂) = 0) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * h p * ψ p =
      -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * g p * CellBox.heightDeriv ψ p := by
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have i1 := bdd_int K hh ψ hψ.continuous
  have i2 := bdd_int K hg (CellBox.heightDeriv ψ) (hd_cont hψ)
  rw [eq_neg_iff_add_eq_zero, ← integral_add i1 i2]
  rw [IntegrableOn, rect_eq'] at i1 i2
  have i12 : Integrable (fun p => (K.lineWeight p.1 : ℂ) * h p * ψ p +
      (K.lineWeight p.1 : ℂ) * g p * CellBox.heightDeriv ψ p)
      ((volume.restrict (Icc K.r₁ K.r₂)).prod (volume.restrict (Icc K.z₁ K.z₂))) := i1.add i2
  rw [rect_eq', integral_prod _ i12]
  refine integral_eq_zero_of_ae ?_
  have hall : ∀ᵐ r ∂(volume.restrict (Icc K.r₁ K.r₂)), ∀ k : ℕ, ∀ x y : ℚ,
      K.z₁ < (x : ℝ) - width k → (x : ℝ) + width k < K.z₂ →
      K.z₁ < (y : ℝ) - width k → (y : ℝ) + width k < K.z₂ → r ∈ Ioo K.r₁ K.r₂ →
      ∫ z in Icc K.z₁ K.z₂, ((K.lineWeight r : ℂ) * g (r, z) * ((deriv (test k x y) z : ℝ) : ℂ) +
        (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) = 0 := by
    refine ae_all_iff.2 fun k => ae_all_iff.2 fun x => ae_all_iff.2 fun y => ?_
    by_cases hc : K.z₁ < (x : ℝ) - width k ∧ (x : ℝ) + width k < K.z₂ ∧
        K.z₁ < (y : ℝ) - width k ∧ (y : ℝ) + width k < K.z₂
    · obtain ⟨a1, a2, a3, a4⟩ := hc
      filter_upwards [line_zero K hK hW hg hh k x y a1 a2 a3 a4] with r hr
      intro _ _ _ _
      exact hr
    · exact Eventually.of_forall fun r a1 a2 a3 a4 => absurd ⟨a1, a2, a3, a4⟩ hc
  have hg' := hg
  have hh' := hh
  rw [IntegrableOn, rect_eq'] at hg' hh'
  filter_upwards [hall, hg'.prod_right_ae, hh'.prod_right_ae, i1.prod_right_ae, i2.prod_right_ae,
    ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae (ae_ne_pt K.r₁), ae_restrict_of_ae (ae_ne_pt K.r₂)]
    with r hr hgr hhr hi1 hi2 hrm hr1 hr2
  have hrI : r ∈ Ioo K.r₁ K.r₂ := ⟨lt_of_le_of_ne hrm.1 (Ne.symm hr1), lt_of_le_of_ne hrm.2 hr2⟩
  have hw0 : (K.lineWeight r : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (lw_ne K (lt_of_le_of_lt hK.r_order.1 hrI.1).ne')
  have hgI : IntegrableOn (fun z => g (r, z)) (Icc K.z₁ K.z₂) := by
    refine Integrable.congr (hgr.const_mul ((K.lineWeight r : ℂ)⁻¹)) (Eventually.of_forall fun z => ?_)
    show (K.lineWeight r : ℂ)⁻¹ * ((K.lineWeight r : ℂ) * g (r, z)) = g (r, z)
    rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
  have hhI : IntegrableOn (fun z => h (r, z)) (Icc K.z₁ K.z₂) := by
    refine Integrable.congr (hhr.const_mul ((K.lineWeight r : ℂ)⁻¹)) (Eventually.of_forall fun z => ?_)
    show (K.lineWeight r : ℂ)⁻¹ * ((K.lineWeight r : ℂ) * h (r, z)) = h (r, z)
    rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
  have hid : ∀ k : ℕ, ∀ x y : ℚ, K.z₁ < (x : ℝ) - width k → (x : ℝ) + width k < K.z₂ →
      K.z₁ < (y : ℝ) - width k → (y : ℝ) + width k < K.z₂ →
      ∫ z in Icc K.z₁ K.z₂, ((deriv (test k x y) z : ℝ) : ℂ) * g (r, z) +
        ((test k x y z : ℝ) : ℂ) * h (r, z) = 0 := by
    intro k x y a1 a2 a3 a4
    have e := hr k x y a1 a2 a3 a4 hrI
    have e2 : (fun z => (K.lineWeight r : ℂ) * g (r, z) * ((deriv (test k x y) z : ℝ) : ℂ) +
        (K.lineWeight r : ℂ) * h (r, z) * ((test k x y z : ℝ) : ℂ)) =
        fun z => (K.lineWeight r : ℂ) * (((deriv (test k x y) z : ℝ) : ℂ) * g (r, z) +
          ((test k x y z : ℝ) : ℂ) * h (r, z)) := by
      funext z; ring
    rw [e2, integral_const_mul] at e
    exact (mul_eq_zero.1 e).resolve_left hw0
  obtain ⟨L, hL⟩ := line_core K.z₁ K.z₂ hz (fun z => g (r, z)) (fun z => h (r, z)) hgI
    (fun x' hx' => hhI.mono_set (Icc_subset_Icc_left hx'.le)) hid
  have hψr : ContDiff ℝ 1 (fun z => ψ (r, z)) := hψ.comp (contDiff_const.prodMk contDiff_id)
  have hibp := ibp_line hz hhI hL hψr (h1 r) (h2 r)
  have e1 : ∫ z in Icc K.z₁ K.z₂, (K.lineWeight r : ℂ) * h (r, z) * ψ (r, z) =
      (K.lineWeight r : ℂ) * ∫ z in Icc K.z₁ K.z₂, h (r, z) * ψ (r, z) := by
    rw [← integral_const_mul]; congr 1; funext z; ring
  have e2 : ∫ z in Icc K.z₁ K.z₂, (K.lineWeight r : ℂ) * g (r, z) * CellBox.heightDeriv ψ (r, z) =
      (K.lineWeight r : ℂ) * ∫ z in Icc K.z₁ K.z₂, g (r, z) * deriv (fun z => ψ (r, z)) z := by
    rw [← integral_const_mul]; congr 1; funext z; simp only [CellBox.heightDeriv]; ring
  calc _ = (∫ z in Icc K.z₁ K.z₂, (K.lineWeight r : ℂ) * h (r, z) * ψ (r, z)) +
        ∫ z in Icc K.z₁ K.z₂, (K.lineWeight r : ℂ) * g (r, z) * CellBox.heightDeriv ψ (r, z) :=
        integral_add hi1 hi2
    _ = 0 := by rw [e1, e2, hibp]; ring

theorem sum_int (K : CellBox) {F : Fin 3 → Fin 3 → ℝ × ℝ → ℂ} (hF : ∀ a b, IntegrableOn (F a b) K.rect)
    (κ : Fin 3 → Fin 3 → ℂ) :
    ∫ p in K.rect, ∑ a, ∑ b, κ a b * F a b p = ∑ a, ∑ b, κ a b * ∫ p in K.rect, F a b p := by
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hF a b).const_mul (κ a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (hF a b).const_mul (κ a b)]
  exact Finset.sum_congr rfl fun b _ => integral_const_mul _ _

end Breakdown.FracInternal.ModeHeightParts

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Breakdown.FracInternal.ModeHeightParts

theorem modeHeightParts : ModeHeightPartsStatement := by
  intro K hK m v G H hs n κ ψ hψ h1 h2
  have hH1 : AEStronglyMeasurable (fun y => H y axialUnit) volume :=
    hs.measurable_second.apply_continuousLinearMap _
  have hH2 : Integrable (fun y => entrySq (H y axialUnit)) := col_entry hs.measurable_second hs.second_two 2
  have hGI := LowEntry.Internal.gradMode_int K hK m n hs.measurable_gradient hs.gradient_two
  have hHI := LowEntry.Internal.gradMode_int K hK m n hH1 hH2
  have hper : ∀ a b, ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p =
      -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p := fun a b =>
    parts_of_weak K hK (fun Ψ e1 e2 e3 => weak_pair hs n a b Ψ e1 e2 e3) (hGI a b) (hHI a b) ψ hψ h1 h2
  have F1 : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) K.rect :=
    fun a b => bdd_int K (hHI a b) ψ hψ.continuous
  have F2 : ∀ a b, IntegrableOn
      (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) K.rect :=
    fun a b => bdd_int K (hGI a b) (CellBox.heightDeriv ψ) (hd_cont hψ)
  have s1 := sum_int K F1 κ
  have s2 := sum_int K F2 κ
  have e1 : (fun p => (K.lineWeight p.1 : ℂ) * comboThird κ m n H 2 p * ψ p) =
      fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * modeThird m n H a b 2 p * ψ p) := by
    funext p
    simp only [comboThird, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have e2 : (fun p => (K.lineWeight p.1 : ℂ) * comboGrad κ m n G p * CellBox.heightDeriv ψ p) =
      fun p => ∑ a, ∑ b, κ a b * ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p * CellBox.heightDeriv ψ p) := by
    funext p
    simp only [comboGrad, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, s1, s2]
  simp only [hper, mul_neg, Finset.sum_neg_distrib]

end Breakdown.CellCert.CellAnalysis

import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

open scoped ContDiff
open MeasureTheory Set Filter Topology

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PatchRoughTest

def strip (ρ R : ℝ) : Set (ℝ × ℝ) := Icc ρ R ×ˢ Icc (-R) R

theorem measurableSet_strip (ρ R : ℝ) : MeasurableSet (strip ρ R) := measurableSet_Icc.prod measurableSet_Icc

theorem isCompact_strip (ρ R : ℝ) : IsCompact (strip ρ R) := isCompact_Icc.prod isCompact_Icc

theorem integrable_bdd_mul {f A : ℝ × ℝ → ℂ} {ρ R M : ℝ} (hf : AEStronglyMeasurable f volume)
    (hfb : ∀ p, ‖f p‖ ≤ M) (hfz : ∀ p, p ∉ strip ρ R → f p = 0) (hA : IntegrableOn A (strip ρ R)) :
    Integrable (fun p => f p * A p) := by
  have h1 : IntegrableOn (fun p => f p * A p) (strip ρ R) :=
    hA.bdd_mul hf.restrict (Eventually.of_forall fun p => hfb p)
  exact h1.integrable_of_forall_notMem_eq_zero fun p hp => by rw [hfz p hp, zero_mul]

theorem exists_strip {E : Type*} [Zero E] [TopologicalSpace E] {f : ℝ × ℝ → E} (hc : HasCompactSupport f)
    (hpos : ∀ p ∈ tsupport f, 0 < p.1) : ∃ ρ R : ℝ, 0 < ρ ∧ ∀ p, p ∉ strip ρ R → p ∉ tsupport f := by
  by_cases hne : (tsupport f).Nonempty
  · obtain ⟨q, hq, hmin⟩ := hc.isCompact.exists_isMinOn hne continuous_fst.continuousOn
    obtain ⟨R, hR⟩ := hc.isCompact.isBounded.subset_closedBall 0
    refine ⟨q.1, R, hpos q hq, fun p hp hps => hp ?_⟩
    have h1 := hR hps
    rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def] at h1
    have h2 : |p.1| ≤ R := (le_max_left _ _).trans h1
    have h3 : |p.2| ≤ R := (le_max_right _ _).trans h1
    exact ⟨⟨hmin hps, (le_abs_self _).trans h2⟩, (abs_le.1 h3).1, (abs_le.1 h3).2⟩
  · exact ⟨1, 1, one_pos, fun p _ hps => hne ⟨p, hps⟩⟩

theorem zero_off {E : Type*} [Zero E] [TopologicalSpace E] {f : ℝ × ℝ → E} {ρ R : ℝ}
    (h : ∀ p, p ∉ strip ρ R → p ∉ tsupport f) (p : ℝ × ℝ) (hp : p ∉ strip ρ R) : f p = 0 :=
  image_eq_zero_of_notMem_tsupport (h p hp)

theorem fderiv_zero_off {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ × ℝ → E} {ρ R : ℝ}
    (h : ∀ p, p ∉ strip ρ R → p ∉ tsupport f) (p : ℝ × ℝ) (hp : p ∉ strip ρ R) (u : ℝ × ℝ) :
    fderiv ℝ f p u = 0 := by
  rw [image_eq_zero_of_notMem_tsupport (fun h' => h p hp (tsupport_fderiv_subset ℝ h'))]
  rfl

theorem smooth_complex {A B C : ℝ × ℝ → ℂ}
    (hA : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn A (strip ρ R)) (hB : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn B (strip ρ R))
    (hC : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn C (strip ρ R))
    (hsm : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * A p) + (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * B p) +
        ∫ p, ((ψ p : ℝ) : ℂ) * C p = 0)
    (ψ : ℝ × ℝ → ℂ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    (∫ p, fderiv ℝ ψ p (1, 0) * A p) + (∫ p, fderiv ℝ ψ p (0, 1) * B p) + ∫ p, ψ p * C p = 0 := by
  obtain ⟨ρ, R, hρ, hS⟩ := exists_strip hc hpos
  set ψr : ℝ × ℝ → ℝ := fun p => (ψ p).re with hψr
  set ψi : ℝ × ℝ → ℝ := fun p => (ψ p).im with hψi
  have hdr : ∀ p u, fderiv ℝ ψr p u = (fderiv ℝ ψ p u).re := by
    intro p u
    have hd : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)).differentiableAt
    have := (Complex.reCLM.hasFDerivAt.comp p hd.hasFDerivAt).fderiv
    rw [show ψr = Complex.reCLM ∘ ψ from rfl, this]
    rfl
  have hdi : ∀ p u, fderiv ℝ ψi p u = (fderiv ℝ ψ p u).im := by
    intro p u
    have hd : DifferentiableAt ℝ ψ p := (hψ.differentiable (by simp)).differentiableAt
    have := (Complex.imCLM.hasFDerivAt.comp p hd.hasFDerivAt).fderiv
    rw [show ψi = Complex.imCLM ∘ ψ from rfl, this]
    rfl
  have sr : ContDiff ℝ ∞ ψr := Complex.reCLM.contDiff.comp hψ
  have si : ContDiff ℝ ∞ ψi := Complex.imCLM.contDiff.comp hψ
  have tr : tsupport ψr ⊆ tsupport ψ := tsupport_comp_subset Complex.zero_re ψ
  have ti : tsupport ψi ⊆ tsupport ψ := tsupport_comp_subset Complex.zero_im ψ
  have cr : HasCompactSupport ψr := hc.comp_left Complex.zero_re
  have ci : HasCompactSupport ψi := hc.comp_left Complex.zero_im
  have er := hsm ψr sr cr fun p hp => hpos p (tr hp)
  have ei := hsm ψi si ci fun p hp => hpos p (ti hp)
  have hd : Continuous (fun p => fderiv ℝ ψ p) := hψ.continuous_fderiv (by simp)
  have intg : ∀ (f : ℝ × ℝ → ℂ) (X : ℝ × ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ p, p ∉ strip ρ R → f p = 0) → IntegrableOn X (strip ρ R) → Integrable (fun p => f p * X p) := by
    intro f X hf hfc hfz hX
    obtain ⟨M, hM⟩ := hf.bounded_above_of_compact_support hfc
    exact integrable_bdd_mul hf.aestronglyMeasurable hM hfz hX
  have dzero : ∀ u p, p ∉ strip ρ R → fderiv ℝ ψ p u = 0 := fun u p hp => fderiv_zero_off hS p hp u
  have pzero : ∀ p, p ∉ strip ρ R → ψ p = 0 := zero_off hS
  have cpl : ∀ z : ℂ, z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := fun z => (Complex.re_add_im z).symm
  have key : ∀ (f : ℝ × ℝ → ℂ) (X : ℝ × ℝ → ℂ), Continuous f → HasCompactSupport f →
      (∀ p, p ∉ strip ρ R → f p = 0) → IntegrableOn X (strip ρ R) →
      ∫ p, f p * X p = (∫ p, (((f p).re : ℝ) : ℂ) * X p) + Complex.I * ∫ p, (((f p).im : ℝ) : ℂ) * X p := by
    intro f X hf hfc hfz hX
    have h1 := intg (fun p => (((f p).re : ℝ) : ℂ)) X (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf))
      (HasCompactSupport.comp_left (g := fun z : ℂ => ((z.re : ℝ) : ℂ)) hfc (by simp))
      (fun p hp => by simp [hfz p hp]) hX
    have h2 := intg (fun p => (((f p).im : ℝ) : ℂ)) X (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf))
      (HasCompactSupport.comp_left (g := fun z : ℂ => ((z.im : ℝ) : ℂ)) hfc (by simp))
      (fun p hp => by simp [hfz p hp]) hX
    rw [← integral_const_mul, ← integral_add h1 (h2.const_mul _)]
    congr 1
    funext p
    conv_lhs => rw [cpl (f p)]
    ring
  have fcont : ∀ u, Continuous (fun p => fderiv ℝ ψ p u) := fun u => hd.clm_apply continuous_const
  have fsupp : ∀ u, HasCompactSupport (fun p => fderiv ℝ ψ p u) := fun u =>
    (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℝ × ℝ →L[ℝ] ℂ => L u) (by simp)
  rw [key _ A (fcont _) (fsupp _) (dzero _) (hA ρ R hρ), key _ B (fcont _) (fsupp _) (dzero _) (hB ρ R hρ),
    key _ C hψ.continuous hc pzero (hC ρ R hρ)]
  simp only [hdr, hdi] at er ei
  linear_combination er + Complex.I * ei

def mollify (φ : ContDiffBump (0 : ℝ × ℝ)) (g : ℝ × ℝ → ℂ) : ℝ × ℝ → ℂ :=
  convolution (φ.normed volume) g (ContinuousLinearMap.lsmul ℝ ℝ) volume

theorem mollify_apply (φ : ContDiffBump (0 : ℝ × ℝ)) (g : ℝ × ℝ → ℂ) (x : ℝ × ℝ) :
    mollify φ g x = ∫ t, φ.normed volume t • g (x - t) := by
  rw [mollify, convolution_def]
  rfl

theorem mollify_smooth (φ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℂ} (hg : LocallyIntegrable g volume) :
    ContDiff ℝ ∞ (mollify φ g) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) φ.contDiff_normed hg

theorem mollify_norm_le (φ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℂ} {M : ℝ} (hg : ∀ q, ‖g q‖ ≤ M)
    (x : ℝ × ℝ) : ‖mollify φ g x‖ ≤ M := by
  rw [mollify_apply]
  have hb : Integrable (fun t => φ.normed volume t * M) := φ.integrable_normed.mul_const M
  refine (norm_integral_le_of_norm_le hb (Eventually.of_forall fun t => ?_)).trans (le_of_eq ?_)
  · rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t)]
    exact mul_le_mul_of_nonneg_left (hg _) (φ.nonneg_normed t)
  · rw [integral_mul_const, φ.integral_normed, one_mul]

theorem mollify_zero_off (φ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℂ} {ρ R δ : ℝ}
    (hg : ∀ q, q ∉ strip ρ R → g q = 0) (hδ : φ.rOut ≤ δ) (x : ℝ × ℝ) (hx : x ∉ strip (ρ - δ) (R + δ)) :
    mollify φ g x = 0 := by
  by_contra hne
  have hs := support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    (f := φ.normed volume) (g := g) hne
  rw [φ.support_normed_eq] at hs
  obtain ⟨t, ht, q, hq, rfl⟩ := hs
  have hq' : q ∈ strip ρ R := by
    by_contra h
    exact hq (hg q h)
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def] at ht
  have h1 : |t.1| < δ := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le ht hδ)
  have h2 : |t.2| < δ := lt_of_le_of_lt (le_max_right _ _) (lt_of_lt_of_le ht hδ)
  obtain ⟨⟨a1, a2⟩, b1, b2⟩ := hq'
  apply hx
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> simp only [Prod.fst_add, Prod.snd_add] <;>
    linarith [(abs_lt.1 h1).1, (abs_lt.1 h1).2, (abs_lt.1 h2).1, (abs_lt.1 h2).2]

theorem mollify_integrable_pair (φ : ContDiffBump (0 : ℝ × ℝ)) {g : ℝ × ℝ → ℂ} (hg : Continuous g) (x : ℝ × ℝ) :
    Integrable (fun t => φ.normed volume t • g (x - t)) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (φ.contDiff_normed (n := 0)).continuous.smul (hg.comp (continuous_const.sub continuous_id))
  · exact φ.hasCompactSupport_normed.smul_right

theorem fderiv_mollify {ψ : ℝ × ℝ → ℂ} {K : NNReal} (hψ : LipschitzWith K ψ) (φ : ContDiffBump (0 : ℝ × ℝ))
    (p u : ℝ × ℝ) : fderiv ℝ (mollify φ ψ) p u = mollify φ (fun q => fderiv ℝ ψ q u) p := by
  set ρ := φ.normed volume with hρ
  have hdiff : Differentiable ℝ (mollify φ ψ) := (mollify_smooth φ hψ.continuous.locallyIntegrable).differentiable (by simp)
  have hl : HasDerivAt (fun s : ℝ => p + s • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add p
  have hF : HasFDerivAt (mollify φ ψ) (fderiv ℝ (mollify φ ψ) p) ((fun s : ℝ => p + s • u) 0) := by
    simpa using (hdiff p).hasFDerivAt
  have hD := hF.comp_hasDerivAt (0 : ℝ) hl
  have hs : Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) atTop (𝓝[≠] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun j => by simp only [mem_compl_iff, mem_singleton_iff]; positivity⟩
  have t1 := (hasDerivAt_iff_tendsto_slope.1 hD).comp hs
  have hq : ∀ s : ℝ, 0 < s → slope (mollify φ ψ ∘ fun s : ℝ => p + s • u) 0 s =
      ∫ t, ρ t • (s⁻¹ • (ψ ((p - t) + s • u) - ψ (p - t))) := by
    intro s hs0
    rw [slope_def_module, sub_zero, Function.comp_apply, Function.comp_apply, zero_smul, add_zero,
      mollify_apply, mollify_apply, ← integral_sub (mollify_integrable_pair φ hψ.continuous _)
        (mollify_integrable_pair φ hψ.continuous _), ← integral_smul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp only
    rw [← smul_sub, smul_comm, show p + s • u - t = p - t + s • u by abel]
  have hlim : Tendsto (fun j : ℕ => ∫ t, ρ t • (((1 : ℝ) / ((j : ℝ) + 1))⁻¹ •
      (ψ ((p - t) + ((1 : ℝ) / ((j : ℝ) + 1)) • u) - ψ (p - t)))) atTop
      (𝓝 (∫ t, ρ t • fderiv ℝ ψ (p - t) u)) := by
    refine tendsto_integral_of_dominated_convergence (fun t => ρ t * (K * ‖u‖)) (fun j => ?_)
      (φ.integrable_normed.mul_const _) (fun j => Eventually.of_forall fun t => ?_) ?_
    · exact ((φ.contDiff_normed (n := 0)).continuous.smul
        ((continuous_const (y := ((1 : ℝ) / ((j : ℝ) + 1))⁻¹)).smul
        ((hψ.continuous.comp ((continuous_const.sub continuous_id).add continuous_const)).sub
          (hψ.continuous.comp (continuous_const.sub continuous_id))))).aestronglyMeasurable
    · have hj : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
      rw [norm_smul, Real.norm_of_nonneg (φ.nonneg_normed t), norm_smul]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
      have hL := hψ.norm_sub_le ((p - t) + ((1 : ℝ) / ((j : ℝ) + 1)) • u) (p - t)
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hj.le] at hL
      rw [norm_inv, Real.norm_of_nonneg hj.le]
      calc (1 / ((j : ℝ) + 1))⁻¹ * ‖ψ (p - t + (1 / ((j : ℝ) + 1)) • u) - ψ (p - t)‖
          ≤ (1 / ((j : ℝ) + 1))⁻¹ * (K * (1 / ((j : ℝ) + 1) * ‖u‖)) := by gcongr
        _ = K * ‖u‖ := by field_simp
    · have hae : ∀ᵐ t : ℝ × ℝ, DifferentiableAt ℝ ψ (p - t) :=
        (quasiMeasurePreserving_sub_left_of_right_invariant volume p).ae hψ.ae_differentiableAt
      filter_upwards [hae] with t ht
      refine Tendsto.const_smul ?_ (ρ t)
      have hl2 : HasDerivAt (fun s : ℝ => (p - t) + s • u) u 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add (p - t)
      have hF2 : HasFDerivAt ψ (fderiv ℝ ψ (p - t)) ((fun s : ℝ => (p - t) + s • u) 0) := by
        simpa using ht.hasFDerivAt
      have t2 := (hasDerivAt_iff_tendsto_slope.1 (hF2.comp_hasDerivAt (0 : ℝ) hl2)).comp hs
      refine t2.congr fun j => ?_
      simp only [Function.comp_apply, slope_def_module, sub_zero, zero_smul, add_zero]
  have e1 : ∀ j : ℕ, (slope (mollify φ ψ ∘ fun s : ℝ => p + s • u) 0 ∘ fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1)) j =
      ∫ t, ρ t • (((1 : ℝ) / ((j : ℝ) + 1))⁻¹ • (ψ ((p - t) + ((1 : ℝ) / ((j : ℝ) + 1)) • u) - ψ (p - t))) :=
    fun j => hq _ (by positivity)
  have t3 := t1.congr e1
  rw [tendsto_nhds_unique t3 hlim, mollify_apply]

def bumpSeq (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : ContDiffBump (0 : ℝ × ℝ) where
  rIn := δ / (2 * ((n : ℝ) + 1))
  rOut := δ / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_lt_div_iff₀ (by positivity) this]
    nlinarith

theorem bumpSeq_rOut_le (δ : ℝ) (hδ : 0 < δ) (n : ℕ) : (bumpSeq δ hδ n).rOut ≤ δ := by
  show δ / ((n : ℝ) + 1) ≤ δ
  exact div_le_self hδ.le (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])

theorem bumpSeq_tendsto (δ : ℝ) (hδ : 0 < δ) : Tendsto (fun n => (bumpSeq δ hδ n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => δ / ((n : ℝ) + 1)) atTop (𝓝 0)
  simpa [div_eq_mul_inv] using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul δ

theorem bumpSeq_ratio (δ : ℝ) (hδ : 0 < δ) : ∀ᶠ n in atTop, (bumpSeq δ hδ n).rOut ≤ 2 * (bumpSeq δ hδ n).rIn :=
  Eventually.of_forall fun n => by
    show δ / ((n : ℝ) + 1) ≤ 2 * (δ / (2 * ((n : ℝ) + 1)))
    refine le_of_eq ?_
    field_simp

theorem indicator_eq_of_zero_off {f X : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} (hf : ∀ p, p ∉ S → f p = 0) :
    (fun p => f p * X p) = fun p => f p * S.indicator X p := by
  funext p
  by_cases hp : p ∈ S
  · rw [indicator_of_mem hp]
  · rw [hf p hp, zero_mul, zero_mul]

end Internal.PatchRoughTest

open Internal.PatchRoughTest in
theorem weak_identity_rough {A B C : ℝ × ℝ → ℂ}
    (hA : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn A (Icc ρ R ×ˢ Icc (-R) R))
    (hB : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn B (Icc ρ R ×ˢ Icc (-R) R))
    (hC : ∀ ρ R : ℝ, 0 < ρ → IntegrableOn C (Icc ρ R ×ˢ Icc (-R) R))
    (hsm : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      (∫ p, ((fderiv ℝ ψ p (1, 0) : ℝ) : ℂ) * A p) + (∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * B p) +
        ∫ p, ((ψ p : ℝ) : ℂ) * C p = 0)
    {Ψ : ℝ × ℝ → ℂ} {K : NNReal} (hΨ : LipschitzWith K Ψ) (hc : HasCompactSupport Ψ)
    (hpos : ∀ p ∈ tsupport Ψ, 0 < p.1) :
    (∫ p, fderiv ℝ Ψ p (1, 0) * A p) + (∫ p, fderiv ℝ Ψ p (0, 1) * B p) + ∫ p, Ψ p * C p = 0 := by
  obtain ⟨ρ, R, hρ, hS⟩ := exists_strip hc hpos
  have hδ : 0 < ρ / 2 := by positivity
  set δ := ρ / 2 with hδdef
  set S' := strip (ρ - δ) (R + δ) with hS'
  have hρ' : 0 < ρ - δ := by rw [hδdef]; linarith
  have hsmC := smooth_complex hA hB hC hsm
  set φ := bumpSeq δ hδ with hφ
  have hz : ∀ q, q ∉ strip ρ R → Ψ q = 0 := zero_off hS
  have hdz : ∀ u q, q ∉ strip ρ R → fderiv ℝ Ψ q u = 0 := fun u q hq => fderiv_zero_off hS q hq u
  have hmz : ∀ (g : ℝ × ℝ → ℂ), (∀ q, q ∉ strip ρ R → g q = 0) → ∀ n p, p ∉ S' → mollify (φ n) g p = 0 :=
    fun g hg n p hp => mollify_zero_off (φ n) hg (bumpSeq_rOut_le δ hδ n) p hp
  have hsub : strip ρ R ⊆ S' := fun p hp => ⟨⟨by linarith [hp.1.1], by linarith [hp.1.2]⟩,
    by linarith [hp.2.1], by linarith [hp.2.2]⟩
  have hzS : ∀ q, q ∉ S' → Ψ q = 0 := fun q hq => hz q fun h => hq (hsub h)
  have hdzS : ∀ u q, q ∉ S' → fderiv ℝ Ψ q u = 0 := fun u q hq => hdz u q fun h => hq (hsub h)
  have hn : ∀ n, (∫ p, fderiv ℝ (mollify (φ n) Ψ) p (1, 0) * A p) +
      (∫ p, fderiv ℝ (mollify (φ n) Ψ) p (0, 1) * B p) + ∫ p, mollify (φ n) Ψ p * C p = 0 := by
    intro n
    have hsupp : tsupport (mollify (φ n) Ψ) ⊆ S' :=
      closure_minimal (fun p hp => by_contra fun h => hp (hmz Ψ hz n p h))
        ((isCompact_strip _ _).isClosed)
    exact hsmC _ (mollify_smooth (φ n) hΨ.continuous.locallyIntegrable)
      (HasCompactSupport.intro (isCompact_strip _ _) fun p hp => hmz Ψ hz n p hp)
      (fun p hp => lt_of_lt_of_le hρ' (hsupp hp).1.1)
  have hdn : ∀ n p u, fderiv ℝ (mollify (φ n) Ψ) p u = mollify (φ n) (fun q => fderiv ℝ Ψ q u) p :=
    fun n p u => fderiv_mollify hΨ (φ n) p u
  have gbd : ∀ u q, ‖fderiv ℝ Ψ q u‖ ≤ K * ‖u‖ := fun u q =>
    ((fderiv ℝ Ψ q).le_opNorm u).trans (mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hΨ) (norm_nonneg _))
  obtain ⟨M, hM⟩ := hΨ.continuous.bounded_above_of_compact_support hc
  have limD : ∀ (u : ℝ × ℝ) (X : ℝ × ℝ → ℂ), IntegrableOn X S' →
      Tendsto (fun n => ∫ p, fderiv ℝ (mollify (φ n) Ψ) p u * X p) atTop (𝓝 (∫ p, fderiv ℝ Ψ p u * X p)) := by
    intro u X hX
    have hXm : AEStronglyMeasurable (S'.indicator X) volume :=
      (aestronglyMeasurable_indicator_iff (measurableSet_strip _ _)).2 hX.aestronglyMeasurable
    have hXi : Integrable (S'.indicator X) := (integrable_indicator_iff (measurableSet_strip _ _)).2 hX
    simp_rw [hdn]
    rw [show (fun p => fderiv ℝ Ψ p u * X p) = fun p => fderiv ℝ Ψ p u * S'.indicator X p from
      indicator_eq_of_zero_off (hdzS u)]
    have e : ∀ n, (fun p => mollify (φ n) (fun q => fderiv ℝ Ψ q u) p * X p) =
        fun p => mollify (φ n) (fun q => fderiv ℝ Ψ q u) p * S'.indicator X p :=
      fun n => indicator_eq_of_zero_off (hmz _ (hdz u) n)
    simp_rw [e]
    have hgm : Measurable (fun q => fderiv ℝ Ψ q u) := measurable_fderiv_apply_const ℝ Ψ u
    have hgi : Integrable (fun q => fderiv ℝ Ψ q u) := by
      refine Integrable.mono' ((integrableOn_const (C := (K : ℝ) * ‖u‖)
        (isCompact_strip ρ R).measure_lt_top.ne).integrable_indicator (measurableSet_strip ρ R))
        hgm.aestronglyMeasurable (Eventually.of_forall fun q => ?_)
      by_cases hq : q ∈ strip ρ R
      · rw [indicator_of_mem hq]; exact gbd u q
      · rw [indicator_of_notMem hq, hdz u q hq, norm_zero]
    refine tendsto_integral_of_dominated_convergence (fun p => K * ‖u‖ * ‖S'.indicator X p‖) (fun n => ?_)
      (hXi.norm.const_mul _) (fun n => Eventually.of_forall fun p => ?_) ?_
    · exact (mollify_smooth (φ n) hgi.locallyIntegrable).continuous.aestronglyMeasurable.mul hXm
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mollify_norm_le (φ n) (gbd u) p) (norm_nonneg _)
    · have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume)
        (bumpSeq_tendsto δ hδ) (bumpSeq_ratio δ hδ) hgi.locallyIntegrable
      filter_upwards [h] with p hp
      exact hp.mul_const _
  have limC : Tendsto (fun n => ∫ p, mollify (φ n) Ψ p * C p) atTop (𝓝 (∫ p, Ψ p * C p)) := by
    have hX := hC (ρ - δ) (R + δ) hρ'
    have hXm : AEStronglyMeasurable (S'.indicator C) volume :=
      (aestronglyMeasurable_indicator_iff (measurableSet_strip _ _)).2 hX.aestronglyMeasurable
    have hXi : Integrable (S'.indicator C) := (integrable_indicator_iff (measurableSet_strip _ _)).2 hX
    rw [show (fun p => Ψ p * C p) = fun p => Ψ p * S'.indicator C p from indicator_eq_of_zero_off hzS]
    have e : ∀ n, (fun p => mollify (φ n) Ψ p * C p) = fun p => mollify (φ n) Ψ p * S'.indicator C p :=
      fun n => indicator_eq_of_zero_off (hmz _ hz n)
    simp_rw [e]
    refine tendsto_integral_of_dominated_convergence (fun p => M * ‖S'.indicator C p‖) (fun n => ?_)
      (hXi.norm.const_mul _) (fun n => Eventually.of_forall fun p => ?_) (Eventually.of_forall fun p => ?_)
    · exact (mollify_smooth (φ n) hΨ.continuous.locallyIntegrable).continuous.aestronglyMeasurable.mul hXm
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (mollify_norm_le (φ n) hM p) (norm_nonneg _)
    · exact (ContDiffBump.convolution_tendsto_right_of_continuous (μ := volume) (bumpSeq_tendsto δ hδ)
        hΨ.continuous p).mul_const _
  have hlim := ((limD (1, 0) A (hA _ _ hρ')).add (limD (0, 1) B (hB _ _ hρ'))).add limC
  simp_rw [hn] at hlim
  exact (tendsto_nhds_unique tendsto_const_nhds hlim).symm

end Bridge

end CertCell

end Breakdown

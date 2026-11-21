import Breakdown.FracCell.SegmentModesPressure
import Breakdown.FracCell.CornerIndependenceParts

open scoped ContDiff
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.FracInternal.SegmentRefl

open Breakdown.FracInternal.MeshDataAffineModes

theorem nz_set {K : Set ℝ} (hK : IsCompact K) (hKU : ∀ r ∈ K, r ≠ 0) :
    ∃ δ > 0, ∃ R : ℝ, ∀ r ∈ K, δ ≤ |r| ∧ |r| ≤ R := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  by_cases h : K.Nonempty
  · obtain ⟨r0, hr0, hmin⟩ := hK.exists_isMinOn h continuous_abs.continuousOn
    refine ⟨|r0|, abs_pos.2 (hKU r0 hr0), R, fun r hr => ⟨hmin hr, ?_⟩⟩
    have := hR hr
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  · exact ⟨1, one_pos, 0, fun r hr => absurd ⟨r, hr⟩ h⟩

theorem int_vanish {g : ℝ × ℝ → ℝ} {H : ℝ × ℝ → ℂ} {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    (hg : Continuous g) {B : ℝ} (hb : ∀ p, |g p| ≤ B) (hz : ∀ p, p ∉ S → g p = 0) (hH : IntegrableOn H S) :
    Integrable (fun p => (g p : ℂ) * H p) := by
  have h1 := ((integrable_indicator_iff hS).2 hH).bdd_mul (c := B) (f := fun p => (g p : ℂ))
    (Complex.continuous_ofReal.comp hg).aestronglyMeasurable
    (Eventually.of_forall fun p => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hb p)
  refine h1.congr (Eventually.of_forall fun p => ?_)
  by_cases hp : p ∈ S
  · simp only [Set.indicator_of_mem hp]
  · simp [hz p hp]

theorem piece_int {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) {S : Set (ℝ × ℝ)}
    (hS : MeasurableSet S) (hsub : tsupport φ ⊆ S) {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn F S)
    (hdF : IntegrableOn dF S) :
    Integrable (fun p => ((fderiv ℝ φ p (0, 1) : ℝ) : ℂ) * F p) ∧ Integrable (fun p => (φ p : ℂ) * dF p) := by
  have hd : Continuous (fun p => fderiv ℝ φ p (0, 1)) := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc : HasCompactSupport (fun p => fderiv ℝ φ p (0, 1)) := hc.fderiv_apply (𝕜 := ℝ) _
  obtain ⟨B1, hB1⟩ := hdc.exists_bound_of_continuous hd
  obtain ⟨B2, hB2⟩ := hc.exists_bound_of_continuous hφ.continuous
  refine ⟨int_vanish hS hd (B := B1) (fun p => by rw [← Real.norm_eq_abs]; exact hB1 p) (fun p hp => ?_) hF,
    int_vanish hS hφ.continuous (B := B2) (fun p => by rw [← Real.norm_eq_abs]; exact hB2 p)
      (fun p hp => image_eq_zero_of_notMem_tsupport fun hm => hp (hsub hm)) hdF⟩
  have : p ∉ Function.support (fderiv ℝ φ) := fun hm => hp (hsub (support_fderiv_subset ℝ hm))
  rw [Function.notMem_support] at this
  rw [this]
  rfl

theorem height_ident_refl {F dF : ℝ × ℝ → ℂ} {C : ℂ} (hC : C ≠ 0)
    (hF : ∀ p : ℝ × ℝ, F (-p.1, p.2) = C * F p) (hdF : ∀ p : ℝ × ℝ, dF (-p.1, p.2) = C * dF p)
    (hint : ∀ δ R Z : ℝ, 0 < δ → IntegrableOn F {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn dF {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z})
    (hpos : ∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hne : ∀ p ∈ tsupport ψ, p.1 ≠ 0) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p := by
  obtain ⟨δ, hδ, R, hR⟩ := nz_set (hc.isCompact.image continuous_fst) (by
    rintro r ⟨p, hp, rfl⟩
    exact hne p hp)
  obtain ⟨Z, hZ⟩ := (hc.isCompact.image continuous_snd).isBounded.subset_closedBall 0
  set S : Set (ℝ × ℝ) := {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} with hSd
  have hS : MeasurableSet S :=
    (measurableSet_le measurable_const (continuous_abs.measurable.comp measurable_fst)).inter
      ((measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
        (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))
  have hTS : tsupport ψ ⊆ S := by
    intro p hp
    have h1 := hR p.1 ⟨p, hp, rfl⟩
    have h2 := hZ ⟨p, hp, rfl⟩
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h2
    exact ⟨h1.1, h1.2, h2⟩
  have hψ0 : ∀ p : ℝ × ℝ, |p.1| < δ → ψ p = 0 := fun p hp =>
    image_eq_zero_of_notMem_tsupport fun hm => by linarith [(hTS hm).1]
  set σ : ℝ → ℝ := fun r => Real.smoothTransition (r / δ) with hσ
  have hσs : ContDiff ℝ ∞ σ := Real.smoothTransition.contDiff.comp (contDiff_id.div_const δ)
  have hσ1 : ∀ r, δ ≤ r → σ r = 1 := fun r hr =>
    Real.smoothTransition.one_of_one_le (by rw [le_div_iff₀ hδ]; linarith)
  have hσ0 : ∀ r, r ≤ 0 → σ r = 0 := fun r hr =>
    Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg hr hδ.le)
  set ψp : ℝ × ℝ → ℝ := fun p => ψ p * σ p.1 with hψp
  set ψm : ℝ × ℝ → ℝ := fun p => ψ p * (1 - σ p.1) with hψm
  have hsp : ContDiff ℝ ∞ ψp := hψ.mul (hσs.comp contDiff_fst)
  have hsm : ContDiff ℝ ∞ ψm := hψ.mul (contDiff_const.sub (hσs.comp contDiff_fst))
  have hcp : HasCompactSupport ψp := hc.mul_right
  have hcm : HasCompactSupport ψm := hc.mul_right
  have hTp : tsupport ψp ⊆ S := (tsupport_mul_subset_left).trans hTS
  have hTm : tsupport ψm ⊆ S := (tsupport_mul_subset_left).trans hTS
  have hpp : ∀ p ∈ tsupport ψp, 0 < p.1 := by
    have hsub : tsupport ψp ⊆ {p : ℝ × ℝ | δ ≤ p.1} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_fst)
      intro p hp
      have h1 : ψ p ≠ 0 := fun h => hp (by simp [hψp, h])
      have h2 : σ p.1 ≠ 0 := fun h => hp (by simp [hψp, h])
      have h3 : δ ≤ |p.1| := by
        by_contra h
        exact h1 (hψ0 p (lt_of_not_ge h))
      show δ ≤ p.1
      rcases le_or_gt p.1 0 with h | h
      · exact absurd (hσ0 _ h) h2
      · rwa [abs_of_pos h] at h3
    exact fun p hp => hδ.trans_le (hsub hp)
  set ρ : ℝ × ℝ → ℝ := fun p => ψm (-p.1, p.2) with hρ
  have hsr : ContDiff ℝ ∞ ρ := hsm.comp (contDiff_fst.neg.prodMk contDiff_snd)
  have hcr : HasCompactSupport ρ := by
    refine HasCompactSupport.intro ((hcm.isCompact).image (continuous_fst.neg.prodMk continuous_snd)) ?_
    intro p hp
    show ψm (-p.1, p.2) = 0
    refine image_eq_zero_of_notMem_tsupport fun hm => hp ⟨(-p.1, p.2), hm, by simp⟩
  have hrp : ∀ p ∈ tsupport ρ, 0 < p.1 := by
    have hsub : tsupport ρ ⊆ {p : ℝ × ℝ | δ ≤ p.1} := by
      refine closure_minimal ?_ (isClosed_le continuous_const continuous_fst)
      intro p hp
      have h1 : ψ (-p.1, p.2) ≠ 0 := fun h => hp (by simp [hρ, hψm, h])
      have h2 : 1 - σ (-p.1) ≠ 0 := fun h => hp (by simp [hρ, hψm, h])
      have h3 : δ ≤ |p.1| := by
        by_contra h
        exact h1 (hψ0 (-p.1, p.2) (by simpa [abs_neg] using lt_of_not_ge h))
      show δ ≤ p.1
      rcases le_or_gt p.1 0 with h | h
      · rw [abs_of_nonpos h] at h3
        exact absurd (by rw [hσ1 _ h3]; ring) h2
      · rwa [abs_of_pos h] at h3
    exact fun p hp => hδ.trans_le (hsub hp)
  have hdr : ∀ p : ℝ × ℝ, fderiv ℝ ρ p (0, 1) = fderiv ℝ ψm (-p.1, p.2) (0, 1) := by
    intro p
    set A : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) := (-ContinuousLinearMap.id ℝ ℝ).prodMap (ContinuousLinearMap.id ℝ ℝ)
    have hAe : (fun q : ℝ × ℝ => (-q.1, q.2)) = A := by
      funext q
      ext <;> simp [A, Prod.map]
    have hA : HasFDerivAt (fun q : ℝ × ℝ => (-q.1, q.2)) A p := by
      rw [hAe]
      exact A.hasFDerivAt
    have h := ((hsm.differentiable (by simp) (-p.1, p.2)).hasFDerivAt.comp p hA).fderiv
    have e : ρ = ψm ∘ (fun q : ℝ × ℝ => (-q.1, q.2)) := rfl
    rw [e, h]
    simp [A]
  have cv : ∀ (g : ℝ × ℝ → ℝ) (H : ℝ × ℝ → ℂ), (∀ p : ℝ × ℝ, H (-p.1, p.2) = C * H p) →
      ∫ p, (g (-p.1, p.2) : ℂ) * H p = C * ∫ p, (g p : ℂ) * H p := by
    intro g H hH
    have e : (fun p : ℝ × ℝ => (g (-p.1, p.2) : ℂ) * H p) =
        fun p => C * ((fun q : ℝ × ℝ => (g q : ℂ) * H q) (negFirst p)) := by
      funext p
      have := hH (-p.1, p.2)
      simp only [neg_neg, Prod.mk.eta] at this
      simp only [negFirst_apply]
      rw [this]
      ring
    rw [e, integral_const_mul]
    congr 1
    exact negFirst_mp.integral_comp' (fun q : ℝ × ℝ => (g q : ℂ) * H q)
  have kp := hpos ψp hsp hcp hpp
  have km : ∫ p, ((fderiv ℝ ψm p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψm p : ℂ) * dF p := by
    have k := hpos ρ hsr hcr hrp
    simp only [hdr] at k
    rw [cv (fun q => fderiv ℝ ψm q (0, 1)) F hF, cv ψm dF hdF, ← mul_neg] at k
    exact mul_left_cancel₀ hC k
  have hI := hint δ R Z hδ
  have ip := piece_int hsp hcp hS hTp hI.1 hI.2
  have im := piece_int hsm hcm hS hTm hI.1 hI.2
  have hsum : ψ = fun p => ψp p + ψm p := by
    funext p
    simp only [hψp, hψm]
    ring
  have hdsum : ∀ p, fderiv ℝ ψ p (0, 1) = fderiv ℝ ψp p (0, 1) + fderiv ℝ ψm p (0, 1) := by
    intro p
    have h := ((hsp.differentiable (by simp) p).hasFDerivAt.add (hsm.differentiable (by simp) p).hasFDerivAt).fderiv
    rw [hsum]
    exact congrArg (fun T : (ℝ × ℝ) →L[ℝ] ℝ => T (0, 1)) h
  have e1 : (fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p) = fun p =>
      ((fderiv ℝ ψp p (0, 1) : ℝ) : ℂ) * F p + ((fderiv ℝ ψm p (0, 1) : ℝ) : ℂ) * F p := by
    funext p
    rw [hdsum]
    push_cast
    ring
  have e2 : (fun p => (ψ p : ℂ) * dF p) = fun p => (ψp p : ℂ) * dF p + (ψm p : ℂ) * dF p := by
    funext p
    rw [hsum]
    push_cast
    ring
  rw [e1, e2, integral_add ip.1 im.1, integral_add ip.2 im.2, kp, km]
  ring

end Breakdown.FracInternal.SegmentRefl

namespace Breakdown.FracInternal.SegmentHeight

open Real Breakdown.SteadyCert Breakdown.CellCert Breakdown.CellCert.CellAnalysis
open Breakdown.CellCert.CellFormula Breakdown.FracInternal.MeshDataAffineModes
open Breakdown.CellCert.CellAnalysis.LowEntry.Internal
open Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal

def halfTurn (m : ℕ) (n : ℤ) : ℂ := Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I)

theorem sign_two : ((unitSign 2 : ℝ) : ℂ) = 1 := by simp [unitSign]

theorem sign_ne (a : Fin 3) : ((unitSign a : ℝ) : ℂ) ≠ 0 := by
  unfold unitSign; split_ifs <;> norm_num

theorem halfTurn_ne (m : ℕ) (n : ℤ) : halfTurn m n ≠ 0 := Complex.exp_ne_zero _

theorem vel_k_pi (m : ℕ) (n : ℤ) (a : Fin 3) (θ : ℝ) (u : Space) :
    velKernel m n a θ u = (halfTurn m n * (unitSign a : ℂ)) * velKernel m n a (θ + π) u := by
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  rw [halfTurn, velKernel, velKernel, phase_pi m n θ, frameVec_pi, Complex.ofReal_mul (unitSign a) (frameVec θ u a)]
  linear_combination (-(Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I) *
    Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I) * (frameVec θ u a : ℂ))) * hs

theorem grad_k_pi (m : ℕ) (n : ℤ) (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    gradKernel m n a b θ M = (halfTurn m n * (unitSign a : ℂ) * (unitSign b : ℂ)) * gradKernel m n a b (θ + π) M := by
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  have ht : ((unitSign b : ℝ) : ℂ) * (unitSign b : ℂ) = 1 := by exact_mod_cast unitSign_sq b
  rw [halfTurn, gradKernel, gradKernel, phase_pi m n θ, frameMat_pi, Complex.ofReal_mul (unitSign a * unitSign b),
    Complex.ofReal_mul (unitSign a) (unitSign b)]
  set A := Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I)
  set B := Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I)
  set F := ((frameMat θ M a b : ℝ) : ℂ)
  set s := ((unitSign a : ℝ) : ℂ)
  set t := ((unitSign b : ℝ) : ℂ)
  linear_combination (-(A * B * F) * t * t) * hs - A * B * F * ht

theorem third_k_pi (m : ℕ) (n : ℤ) (a b c : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) :
    thirdKernel m n a b c θ M = (halfTurn m n * (unitSign a : ℂ) * (unitSign b : ℂ) * (unitSign c : ℂ)) *
      thirdKernel m n a b c (θ + π) M := by
  have hs : ((unitSign a : ℝ) : ℂ) * (unitSign a : ℂ) = 1 := by exact_mod_cast unitSign_sq a
  have ht : ((unitSign b : ℝ) : ℂ) * (unitSign b : ℂ) = 1 := by exact_mod_cast unitSign_sq b
  have hu : ((unitSign c : ℝ) : ℂ) * (unitSign c : ℂ) = 1 := by exact_mod_cast unitSign_sq c
  rw [halfTurn, thirdKernel, thirdKernel, phase_pi m n θ, frameThird_pi,
    Complex.ofReal_mul (unitSign a * unitSign b * unitSign c), Complex.ofReal_mul (unitSign a * unitSign b),
    Complex.ofReal_mul (unitSign a) (unitSign b)]
  set A := Complex.exp (((azimuth m n * π : ℝ) : ℂ) * Complex.I)
  set B := Complex.exp (-((azimuth m n * (θ + π) : ℝ) : ℂ) * Complex.I)
  set F := ((frameThird θ M a b c : ℝ) : ℂ)
  set s := ((unitSign a : ℝ) : ℂ)
  set t := ((unitSign b : ℝ) : ℂ)
  set w := ((unitSign c : ℝ) : ℂ)
  linear_combination (-(A * B * F) * t * t * w * w) * hs - A * B * F * w * w * ht - A * B * F * hu

theorem pres_k_pi (m : ℕ) (n : ℤ) (θ t : ℝ) : presKernel m n θ t = halfTurn m n * presKernel m n (θ + π) t := by
  simp only [presKernel, halfTurn]
  rw [phase_pi m n θ]
  ring

theorem vel_refl (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (p : ℝ × ℝ) :
    modeVec m n v (-p.1) p.2 a = (halfTurn m n * (unitSign a : ℂ)) * modeVec m n v p.1 p.2 a := by
  rw [modeVec_k, modeVec_k, mode_neg _ _ (vel_k_pi m n a) (velKernel_per m n a)]
  ring

theorem grad_refl2 (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    gradMode m n G a 2 (-p.1, p.2) = (halfTurn m n * (unitSign a : ℂ)) * gradMode m n G a 2 p := by
  have hC : ∀ θ M, gradKernel m n a 2 θ M = (halfTurn m n * (unitSign a : ℂ)) * gradKernel m n a 2 (θ + π) M := by
    intro θ M
    rw [grad_k_pi m n a 2 θ M, sign_two, mul_one]
  show (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), gradKernel m n a 2 θ (G (cylPoint (-p.1) θ p.2)) =
    _ * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), gradKernel m n a 2 θ (G (cylPoint p.1 θ p.2)))
  rw [mode_neg _ _ hC (gradKernel_per m n a 2)]
  ring

theorem third_refl22 (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a 2 2 (-p.1, p.2) = (halfTurn m n * (unitSign a : ℂ)) * modeThird m n H a 2 2 p := by
  have hC : ∀ θ M, thirdKernel m n a 2 2 θ M =
      (halfTurn m n * (unitSign a : ℂ)) * thirdKernel m n a 2 2 (θ + π) M := by
    intro θ M
    rw [third_k_pi m n a 2 2 θ M, sign_two, mul_one, mul_one]
  show (1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), thirdKernel m n a 2 2 θ (H (cylPoint (-p.1) θ p.2)) =
    _ * ((1 / (2 * π) : ℂ) * ∫ θ in (0 : ℝ)..(2 * π), thirdKernel m n a 2 2 θ (H (cylPoint p.1 θ p.2)))
  rw [mode_neg _ _ hC (thirdKernel_per m n a 2 2)]
  ring

theorem pres_refl' (m : ℕ) (n : ℤ) (P : Space → ℝ) (p : ℝ × ℝ) :
    presMode m n P (-p.1) p.2 = halfTurn m n * presMode m n P p.1 p.2 := by
  rw [presMode_k, presMode_k, mode_neg _ _ (pres_k_pi m n) (presKernel_per m n)]
  ring

theorem weak_height {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (φ : ℝ × ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) (hpos : ∀ p ∈ tsupport φ, 0 < p.1) :
    ∫ p, ((fderiv ℝ φ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p = -∫ p, (φ p : ℂ) * modeThird m n H a b 2 p := by
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, entryQ_apply]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a b 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (entryQ a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) axialUnit) : ℂ) := by
    intro p
    simp only [modeThird, entryQ_apply]
    rfl
  simp only [hth, hgm]
  exact scale _ (cylModeWeak (Space →L[ℝ] Space) G H (locG hs) (locHc hs) (weakG hs) (entryQ a b)
    (entryQ_smooth a b) m n φ hφ hc hpos).2

theorem box_sub (δ R Z : ℝ) :
    {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ⊆ Icc (-R) R ×ˢ Icc (-Z) Z := by
  intro p hp
  exact ⟨abs_le.1 hp.2.1, abs_le.1 hp.2.2⟩

theorem box_meas (δ R Z : ℝ) : MeasurableSet {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
  (measurableSet_le measurable_const (continuous_abs.measurable.comp measurable_fst)).inter
    ((measurableSet_le (continuous_abs.measurable.comp measurable_fst) measurable_const).inter
      (measurableSet_le (continuous_abs.measurable.comp measurable_snd) measurable_const))

theorem weighted_rect {F : ℝ × ℝ → ℂ} {R Z : ℝ} (h : IntegrableOn F (Icc (-R) R ×ˢ Icc (-Z) Z)) :
    IntegrableOn (fun p : ℝ × ℝ => (((fun r : ℝ => r) p.1 : ℝ) : ℂ) * F p) (Icc (-R) R ×ˢ Icc (-Z) Z) :=
  h.continuousOn_mul (by fun_prop) (isCompact_Icc.prod isCompact_Icc)

end Breakdown.FracInternal.SegmentHeight

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis
open Breakdown.FracInternal.SegmentHeight Breakdown.FracInternal.SegmentRefl Breakdown.FracInternal.SegmentModes
open Breakdown.FracInternal.MeshDataAffineModes

theorem modes_height_pair_velocity {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsHeightWeakPair (fun _ => 1) (L.velMode n x a) (L.gradModeOf n x a 2) := by
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL]; exact hx.1
  have hrect := fun R Z : ℝ =>
    MeshDataAffineModes.secondOrder_modes_integrable L.order x.1 x.2.1 x.2.2.1 hs n (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, L.velMode n x a (-p.1, p.2) =
      (halfTurn L.order n * (unitSign a : ℂ)) * L.velMode n x a p := fun p => vel_refl L.order n x.1 a p
  have hdF : ∀ p : ℝ × ℝ, L.gradModeOf n x a 2 (-p.1, p.2) =
      (halfTurn L.order n * (unitSign a : ℂ)) * L.gradModeOf n x a 2 p := fun p => grad_refl2 L.order n x.2.1 a p
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (L.velMode n x a) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (L.gradModeOf n x a 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z _ => ⟨((hrect R Z).1 a).mono_set (box_sub δ R Z), ((hrect R Z).2.1 a 2).mono_set (box_sub δ R Z)⟩
  refine ⟨fun R Z => ⟨?_, ?_⟩, hoff, height_ident_refl (mul_ne_zero (halfTurn_ne _ _) (sign_ne a)) hF hdF hoff
    (fun ψ hψ hc hpos => (modes_weak_identities c x hx L hL n a ψ hψ hc hpos).2.1)⟩
  · exact ((hrect R Z).1 a).congr_fun (fun p _ => by simp only [Complex.ofReal_one, one_mul]; try rfl)
      (measurableSet_Icc.prod measurableSet_Icc)
  · exact ((hrect R Z).2.1 a 2).congr_fun (fun p _ => by simp only [Complex.ofReal_one, one_mul]; try rfl)
      (measurableSet_Icc.prod measurableSet_Icc)

theorem modes_height_pair_gradient {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) (a : Fin 3) :
    IsHeightWeakPair (fun r => r) (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 2) := by
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL]; exact hx.1
  have hrect := fun R Z : ℝ =>
    MeshDataAffineModes.secondOrder_modes_integrable L.order x.1 x.2.1 x.2.2.1 hs n (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, L.gradModeOf n x a 2 (-p.1, p.2) =
      (halfTurn L.order n * (unitSign a : ℂ)) * L.gradModeOf n x a 2 p := fun p => grad_refl2 L.order n x.2.1 a p
  have hdF : ∀ p : ℝ × ℝ, L.secondModeOf n x a 2 2 (-p.1, p.2) =
      (halfTurn L.order n * (unitSign a : ℂ)) * L.secondModeOf n x a 2 2 p :=
    fun p => third_refl22 L.order n x.2.2.1 a p
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (L.gradModeOf n x a 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (L.secondModeOf n x a 2 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z hδ => ⟨((hrect R Z).2.1 a 2).mono_set (box_sub δ R Z),
      off_axis_int (box_meas δ R Z) hδ (fun p hp => hp.1) (((hrect R Z).2.2 a 2 2).mono_set (box_sub δ R Z))⟩
  exact ⟨fun R Z => ⟨weighted_rect ((hrect R Z).2.1 a 2), (hrect R Z).2.2 a 2 2⟩, hoff,
    height_ident_refl (mul_ne_zero (halfTurn_ne _ _) (sign_ne a)) hF hdF hoff
      (fun ψ hψ hc hpos => weak_height hs n a 2 ψ hψ hc hpos)⟩

theorem modes_height_pair_pressure {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (hx : IsAdmissible c x)
    (L : CellLayout) (hL : L.order = c.order) (n : ℤ) :
    IsHeightWeakPair (fun r => r) (L.pressMode n x) (L.pressureGradMode n x 2) := by
  have hG : IsGradientField x.2.2.2.2 := hx.2.1
  have hrect := fun R Z : ℝ => MeshDataAffineModes.gradient_modes_integrable L.order x.2.2.2.2 hG n
    (L.gaugeValue x / L.gaugeUnit).re (-R) R (-Z) Z
  have hF : ∀ p : ℝ × ℝ, L.pressMode n x (-p.1, p.2) = halfTurn L.order n * L.pressMode n x p :=
    fun p => pres_refl' L.order n _ p
  have hdF : ∀ p : ℝ × ℝ, L.pressureGradMode n x 2 (-p.1, p.2) = halfTurn L.order n * L.pressureGradMode n x 2 p := by
    intro p
    have := vel_refl L.order n x.2.2.2.2 2 p
    rw [sign_two, mul_one] at this
    exact this
  have hoff : ∀ δ R Z : ℝ, 0 < δ →
      IntegrableOn (L.pressMode n x) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} ∧
      IntegrableOn (L.pressureGradMode n x 2) {p : ℝ × ℝ | δ ≤ |p.1| ∧ |p.1| ≤ R ∧ |p.2| ≤ Z} :=
    fun δ R Z hδ => ⟨(hrect R Z).1.mono_set (box_sub δ R Z),
      off_axis_int (box_meas δ R Z) hδ (fun p hp => hp.1) (((hrect R Z).2 2).mono_set (box_sub δ R Z))⟩
  refine ⟨fun R Z => ⟨weighted_rect (hrect R Z).1, (hrect R Z).2 2⟩, hoff,
    height_ident_refl (halfTurn_ne _ _) hF hdF hoff ?_⟩
  intro ψ hψ hc hpos
  have hq := MeshGaugeLinearPotential.potentialOf_spec x.2.2.2.2 hG
  obtain ⟨_, _, hQ2, hQm, _⟩ := hG
  have hQloc := Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
  have hf : LocallyIntegrable (L.pressureOf x) volume :=
    (Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq).sub (locallyIntegrable_const _)
  have hg : ∀ j : Fin 3, LocallyIntegrable
      (fun y => (innerSL ℝ (x.2.2.2.2 y) : Space →L[ℝ] ℝ) (unitVector j)) volume := by
    intro j
    refine (locallyIntegrable_iff).2 fun K hK => ?_
    refine Integrable.mono' ((hQloc.integrableOn_isCompact hK).norm)
      ((hQm.inner aestronglyMeasurable_const).restrict) (Filter.Eventually.of_forall fun y => ?_)
    rw [innerSL_apply_apply]
    refine (norm_inner_le_norm _ _).trans ?_
    simp [unitVector]
  have hw := (cylModeWeak ℝ (L.pressureOf x) (fun y => (innerSL ℝ (x.2.2.2.2 y) : Space →L[ℝ] ℝ)) hf hg
    (pressure_weak hx.2.1 _) (fun _ => ContinuousLinearMap.id ℝ ℝ) contDiff_const L.order n ψ hψ hc hpos).2
  have hpm : ∀ p : ℝ × ℝ, L.pressMode n x p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth L.order n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ (L.pressureOf x (cylPoint p.1 θ p.2)) : ℝ) : ℂ) := by
    intro p
    rfl
  have hgm : ∀ p : ℝ × ℝ, L.pressureGradMode n x 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth L.order n * θ : ℝ) * Complex.I) *
        ((ContinuousLinearMap.id ℝ ℝ ((innerSL ℝ (x.2.2.2.2 (cylPoint p.1 θ p.2)) : Space →L[ℝ] ℝ)
          axialUnit) : ℝ) : ℂ) := by
    intro p
    simp only [ContinuousLinearMap.id_apply, innerSL_apply_apply]
    rfl
  simp only [hpm, hgm]
  exact Breakdown.CellCert.CellAnalysis.ModeRadialPartsA.Internal.scale _ hw

end Breakdown.CellCert.CellFormula

import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.ModeRadialWeak
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeHeightAxis

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def RadialMixedWeakStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H → ∀ (n : ℤ) (a : Fin 3),
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
        ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * gradMode m n G a 2 p + ((ψ p.1 : ℝ) : ℂ) * modeThird m n H a 0 2 p)
          * ((t p.2 : ℝ) : ℂ) = 0

private theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

private theorem cmul {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f K.rect) {g : ℝ × ℝ → ℂ}
    (hg : Continuous g) : IntegrableOn (fun p => g p * f p) K.rect :=
  IntegrableOn.continuousOn_mul hg.continuousOn hf (rect_compact K)

private theorem ofReal_cont {g : ℝ × ℝ → ℝ} (hg : Continuous g) : Continuous (fun p => ((g p : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp hg

private theorem wmul {K : CellBox} {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    {q q' k : ℝ → ℝ} (hq : Continuous q) (hq' : Continuous q') (hk : Continuous k)
    (hax : K.r₁ = 0 → ∀ r, q r = r * q' r) :
    IntegrableOn (fun p => ((q p.1 * k p.2 : ℝ) : ℂ) * F p) K.rect := by
  by_cases h : K.r₁ = 0
  · have hl : ∀ r, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h]
    have e : (fun p : ℝ × ℝ => ((q p.1 * k p.2 : ℝ) : ℂ) * F p) =
        fun p => ((q' p.1 * k p.2 : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * F p) := by
      funext p
      rw [hl, hax h]
      push_cast
      ring
    rw [e]
    exact cmul hF (ofReal_cont ((hq'.comp continuous_fst).mul (hk.comp continuous_snd)))
  · have hl : ∀ r, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h]
    have hF' : IntegrableOn F K.rect := by simpa [hl] using hF
    exact cmul hF' (ofReal_cont ((hq.comp continuous_fst).mul (hk.comp continuous_snd)))

private theorem hbase (K : CellBox) (hK : IsCellBox K) (c o : ℝ) (hco : c ≠ o) (hmin : min c o = K.z₁)
    (hmax : max c o = K.z₂) (V G0 G2 S : ℝ × ℝ → ℂ) (hV : IntegrableOn V K.rect)
    (hG0 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * G0 p) K.rect)
    (hG2 : IntegrableOn G2 K.rect)
    (hS : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * S p) K.rect)
    (hW1 : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * V p + ((ψ p.1 : ℝ) : ℂ) * G0 p) * ((t p.2 : ℝ) : ℂ) = 0)
    (hW2 : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ K.r₁ = 0 → ψ K.r₂ = 0 → ∀ t : ℝ → ℝ, Continuous t →
      ∫ p in K.rect, (((deriv ψ p.1 : ℝ) : ℂ) * G2 p + ((ψ p.1 : ℝ) : ℂ) * S p) * ((t p.2 : ℝ) : ℂ) = 0)
    (t : ℝ → ℝ) (ht : IsAnyPolyFn t) :
    heightStripMoment c o K.r₁ K.r₂ (fun r => r) G0 S t =
      ((K.r₂ * t K.r₂ : ℝ) : ℂ) * cornerMoment K.r₂ K.r₁ c o V G0 G2 S
        - ((K.r₁ * t K.r₁ : ℝ) : ℂ) * cornerMoment K.r₁ K.r₂ c o V G0 G2 S
        - heightStripMoment c o K.r₁ K.r₂ (fun _ => 1) V G2 (deriv (fun r => r * t r)) := by
  obtain ⟨P, hP⟩ := ht
  have htP : t = fun u => P.eval u := funext hP
  subst htP
  have hr : K.r₁ < K.r₂ := hK.r_order.2
  have hr0 : K.r₂ - K.r₁ ≠ 0 := sub_ne_zero.2 hr.ne'
  have hr0' : K.r₁ - K.r₂ ≠ 0 := sub_ne_zero.2 hr.ne
  have hco' : c - o ≠ 0 := sub_ne_zero.2 hco
  have hPc : ContDiff ℝ 1 (fun u : ℝ => P.eval u) := by simpa using P.contDiff_aeval (𝕜 := ℝ) 1
  have hwd : ContDiff ℝ 1 (fun r : ℝ => r * P.eval r) := contDiff_id.mul hPc
  have hw' : Continuous (deriv (fun r : ℝ => r * P.eval r)) := hwd.continuous_deriv le_rfl
  set b₁ : ℝ := K.r₂ * P.eval K.r₂ with hb₁
  set b₀ : ℝ := K.r₁ * P.eval K.r₁ with hb₀
  set η : ℝ → ℝ := fun r => r * P.eval r - (b₁ * ((r - K.r₁) / (K.r₂ - K.r₁)) + b₀ * ((r - K.r₂) / (K.r₁ - K.r₂)))
    with hη
  have hηd : ContDiff ℝ 1 η := hwd.sub ((contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _)).add
    (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _)))
  have hη1 : η K.r₁ = 0 := by
    simp only [hη]
    rw [sub_self, zero_div, mul_zero, zero_add, div_self hr0', mul_one, hb₀, sub_self]
  have hη2 : η K.r₂ = 0 := by
    simp only [hη]
    rw [sub_self, zero_div, mul_zero, add_zero, div_self hr0, mul_one, hb₁, sub_self]
  have hdη : ∀ r, deriv η r = deriv (fun r : ℝ => r * P.eval r) r - (b₁ * (1 / (K.r₂ - K.r₁)) + b₀ * (1 / (K.r₁ - K.r₂))) := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => r * P.eval r) (deriv (fun r : ℝ => r * P.eval r) r) r :=
      ((hwd.differentiable (by norm_num)) r).hasDerivAt
    have h2 : HasDerivAt (fun r : ℝ => b₁ * ((r - K.r₁) / (K.r₂ - K.r₁)) + b₀ * ((r - K.r₂) / (K.r₁ - K.r₂)))
        (b₁ * (1 / (K.r₂ - K.r₁)) + b₀ * (1 / (K.r₁ - K.r₂))) r :=
      ((((hasDerivAt_id r).sub_const K.r₁).div_const _).const_mul b₁).add
        ((((hasDerivAt_id r).sub_const K.r₂).div_const _).const_mul b₀)
    exact (h1.sub h2).deriv
  have hηc : Continuous η := hηd.continuous
  have hdηc : Continuous (deriv η) := hηd.continuous_deriv le_rfl
  have X0 := hW1 η hηd hη1 hη2 (fun _ => 1 / (c - o)) continuous_const
  have Y0 := hW2 η hηd hη1 hη2 (fun z => (z - o) / (c - o)) ((continuous_id.sub continuous_const).div_const _)
  have hsetH : Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc (min c o) (max c o) = K.rect := by
    rw [hmin, hmax]; rfl
  have hsetA : Set.Icc (min K.r₂ K.r₁) (max K.r₂ K.r₁) ×ˢ Set.Icc (min c o) (max c o) = K.rect := by
    rw [hmin, hmax, min_eq_right hr.le, max_eq_left hr.le]; rfl
  have hsetB : Set.Icc (min K.r₁ K.r₂) (max K.r₁ K.r₂) ×ˢ Set.Icc (min c o) (max c o) = K.rect := by
    rw [hmin, hmax, min_eq_left hr.le, max_eq_right hr.le]; rfl
  have hs1 : edgeSign K.r₂ K.r₁ = 1 := by simp [edgeSign, hr]
  have hs0 : edgeSign K.r₁ K.r₂ = -1 := by simp [edgeSign, not_lt.2 hr.le]
  simp only [heightStripMoment, cornerMoment, hsetH, hsetA, hsetB, hs1, hs0]
  have hM : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hpc : Continuous (fun r : ℝ => Polynomial.eval r P) := hPc.continuous
  have hk1 : Continuous (fun _ : ℝ => 1 / (c - o)) := continuous_const
  have hk2 : Continuous (fun z : ℝ => (z - o) / (c - o)) := (continuous_id.sub continuous_const).div_const _
  have hwc : Continuous (fun r : ℝ => r * Polynomial.eval r P) := continuous_id.mul hpc
  have hχ1 : Continuous (fun r : ℝ => (r - K.r₁) / (K.r₂ - K.r₁)) := (continuous_id.sub continuous_const).div_const _
  have hχ0 : Continuous (fun r : ℝ => (r - K.r₂) / (K.r₁ - K.r₂)) := (continuous_id.sub continuous_const).div_const _
  have hwax : K.r₁ = 0 → ∀ r, r * Polynomial.eval r P = r * Polynomial.eval r P := fun _ _ => rfl
  have hχ1ax : K.r₁ = 0 → ∀ r, (r - K.r₁) / (K.r₂ - K.r₁) = r * (1 / (K.r₂ - K.r₁)) := by
    intro h r; rw [h]; ring
  have hηax : K.r₁ = 0 → ∀ r, η r = r * (Polynomial.eval r P - b₁ / (K.r₂ - K.r₁)) := by
    intro h r
    simp only [hη]
    rw [hb₀, h]
    ring
  have iA1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * G0 p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p)
      * ((p.1 * Polynomial.eval p.1 P : ℝ) : ℂ)) K.rect := by
    refine ((wmul hG0 hwc hpc hk1 hwax).add (wmul hS hwc hpc hk2 hwax)).congr_fun (fun p _ => ?_) hM
    try simp only [Pi.add_apply]
    push_cast
    ring
  have iA4 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * V p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p)
      * ((1 * deriv (fun r => r * Polynomial.eval r P) p.1 : ℝ) : ℂ)) K.rect := by
    refine ((cmul hV (ofReal_cont ((hw'.comp continuous_fst).mul (hk1.comp continuous_snd)))).add
      (cmul hG2 (ofReal_cont ((hw'.comp continuous_fst).mul (hk2.comp continuous_snd))))).congr_fun
        (fun p _ => ?_) hM
    try simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    push_cast
    ring
  have iA2 : IntegrableOn (fun p : ℝ × ℝ => ((b₁ : ℝ) : ℂ) * (((1 / (K.r₂ - K.r₁) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * V p
      + ((1 / (K.r₂ - K.r₁) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * G0 p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p)) K.rect := by
    refine IntegrableOn.congr_fun (Integrable.const_mul ((((cmul hV (continuous_const : Continuous (fun _ : ℝ × ℝ => ((1 / (K.r₂ - K.r₁) * (1 / (c - o)) : ℝ) : ℂ)))).add
      (cmul hG2 (ofReal_cont ((continuous_const : Continuous (fun _ : ℝ × ℝ => 1 / (K.r₂ - K.r₁))).mul (hk2.comp continuous_snd))))).add
      (wmul hG0 hχ1 continuous_const hk1 hχ1ax)).add (wmul hS hχ1 continuous_const hk2 hχ1ax))
        ((b₁ : ℝ) : ℂ)) (fun p _ => ?_) hM
    try simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    push_cast
    ring
  have iA3 : IntegrableOn (fun p : ℝ × ℝ => ((b₀ : ℝ) : ℂ) * (((1 / (K.r₁ - K.r₂) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * V p
      + ((1 / (K.r₁ - K.r₂) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * G0 p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p)) K.rect := by
    by_cases h0 : K.r₁ = 0
    · have hb : b₀ = 0 := by rw [hb₀, h0, zero_mul]
      simp only [hb, Complex.ofReal_zero, zero_mul]
      exact integrableOn_zero
    · have hax : K.r₁ = 0 → ∀ r, (r - K.r₂) / (K.r₁ - K.r₂) = r * 0 := fun h => absurd h h0
      refine IntegrableOn.congr_fun (Integrable.const_mul ((((cmul hV (continuous_const : Continuous (fun _ : ℝ × ℝ => ((1 / (K.r₁ - K.r₂) * (1 / (c - o)) : ℝ) : ℂ)))).add
        (cmul hG2 (ofReal_cont ((continuous_const : Continuous (fun _ : ℝ × ℝ => 1 / (K.r₁ - K.r₂))).mul (hk2.comp continuous_snd))))).add
        (wmul hG0 hχ0 continuous_const hk1 hax)).add (wmul hS hχ0 continuous_const hk2 hax))
          ((b₀ : ℝ) : ℂ)) (fun p _ => ?_) hM
      try simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
      push_cast
      ring
  have iX : IntegrableOn (fun p : ℝ × ℝ => (((deriv η p.1 : ℝ) : ℂ) * V p + ((η p.1 : ℝ) : ℂ) * G0 p)
      * ((1 / (c - o) : ℝ) : ℂ)) K.rect := by
    refine ((cmul hV (ofReal_cont ((hdηc.comp continuous_fst).mul (hk1.comp continuous_snd)))).add
      (wmul hG0 hηc (hpc.sub continuous_const) hk1 hηax)).congr_fun (fun p _ => ?_) hM
    try simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    push_cast
    ring
  have iY : IntegrableOn (fun p : ℝ × ℝ => (((deriv η p.1 : ℝ) : ℂ) * G2 p + ((η p.1 : ℝ) : ℂ) * S p)
      * (((p.2 - o) / (c - o) : ℝ) : ℂ)) K.rect := by
    refine ((cmul hG2 (ofReal_cont ((hdηc.comp continuous_fst).mul (hk2.comp continuous_snd)))).add
      (wmul hS hηc (hpc.sub continuous_const) hk2 hηax)).congr_fun (fun p _ => ?_) hM
    try simp only [Pi.add_apply, Pi.mul_apply, Function.comp_apply]
    push_cast
    ring
  set A1 := (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * G0 p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p)
      * ((p.1 * Polynomial.eval p.1 P : ℝ) : ℂ)) with hA1
  set A4 := (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * V p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p)
      * ((1 * deriv (fun r => r * Polynomial.eval r P) p.1 : ℝ) : ℂ)) with hA4
  set A2 := (fun p : ℝ × ℝ => ((1 / (K.r₂ - K.r₁) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * V p
      + ((1 / (K.r₂ - K.r₁) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * G0 p
      + (((p.1 - K.r₁) / (K.r₂ - K.r₁) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p) with hA2
  set A3 := (fun p : ℝ × ℝ => ((1 / (K.r₁ - K.r₂) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * V p
      + ((1 / (K.r₁ - K.r₂) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * G2 p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * ((1 / (c - o) : ℝ) : ℂ) * G0 p
      + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) * (((p.2 - o) / (c - o) : ℝ) : ℂ) * S p) with hA3
  have key : (∫ p in K.rect, A1 p) + (∫ p in K.rect, A4 p) - (∫ p in K.rect, ((b₁ : ℝ) : ℂ) * A2 p)
      - (∫ p in K.rect, ((b₀ : ℝ) : ℂ) * A3 p) = 0 := by
    have iA2' : IntegrableOn (fun p => ((b₁ : ℝ) : ℂ) * A2 p) K.rect := iA2
    have iA3' : IntegrableOn (fun p => ((b₀ : ℝ) : ℂ) * A3 p) K.rect := iA3
    have i14 : IntegrableOn (fun p => A1 p + A4 p) K.rect := iA1.add iA4
    have i142 : IntegrableOn (fun p => A1 p + A4 p - ((b₁ : ℝ) : ℂ) * A2 p) K.rect := i14.sub iA2'
    rw [← integral_add iA1 iA4, ← integral_sub i14 iA2', ← integral_sub i142 iA3']
    have e : (fun p => A1 p + A4 p - ((b₁ : ℝ) : ℂ) * A2 p - ((b₀ : ℝ) : ℂ) * A3 p) =
        fun p => (((deriv η p.1 : ℝ) : ℂ) * V p + ((η p.1 : ℝ) : ℂ) * G0 p) * ((1 / (c - o) : ℝ) : ℂ)
          + (((deriv η p.1 : ℝ) : ℂ) * G2 p + ((η p.1 : ℝ) : ℂ) * S p) * (((p.2 - o) / (c - o) : ℝ) : ℂ) := by
      funext p
      simp only [hA1, hA2, hA3, hA4]
      rw [hdη]
      simp only [hη]
      push_cast
      ring
    rw [e, integral_add iX iY, X0, Y0, add_zero]
  rw [integral_const_mul, integral_const_mul] at key
  linear_combination (edgeSign c o) * key

private theorem ax_meas {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume) :
    AEStronglyMeasurable (fun y => H y axialUnit) volume :=
  (ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) axialUnit).continuous.comp_aestronglyMeasurable hH

private theorem ax_sq {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  have hc : Continuous (fun M : Space →L[ℝ] Space => entrySq M) := by
    unfold entrySq
    fun_prop
  refine h2.mono' (hc.comp_aestronglyMeasurable (ax_meas hH)) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ entrySq (H y axialUnit) := by
    unfold entrySq
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have e : entrySq (H y axialUnit) = ∑ j : Fin 3, ‖H y (unitVector 2) (unitVector j)‖ ^ 2 := rfl
  rw [e]
  exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
    (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ 2)

theorem heightNormal_holds (hW : ModeRadialWeakStatement) (hM : RadialMixedWeakStatement) :
    HeightNormalStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hK : IsCellBox K := hL.box_valid
  have hs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by
    rw [hL.order_eq]
    exact hx.1
  obtain ⟨hV, hG0, hW1⟩ := hW K hK L.order x.1 x.2.1 x.2.2.1 hs n a
  have hW2 := hM K hK L.order x.1 x.2.1 x.2.2.1 hs n a
  have hG2 : IntegrableOn (gradMode L.order n x.2.1 a 2) K.rect := by
    refine (modeHeightAxis L.order x.1 x.2.1 x.2.2.1 hs n a K.r₂ K.z₂).mono_set ?_
    intro p hp
    simp only [CellBox.rect, Set.mem_prod, Set.mem_Icc] at hp ⊢
    exact ⟨⟨hK.r_order.1.trans hp.1.1, hp.1.2⟩, ⟨by linarith [hK.z_order.1, hp.2.1], hp.2.2⟩⟩
  have hS : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeThird L.order n x.2.2.1 a 0 2 p) K.rect :=
    LowEntry.Internal.gradMode_int K hK L.order n (ax_meas hs.measurable_second)
      (ax_sq hs.measurable_second hs.second_two) a 0
  have hbox : L.box = K := hL.box_eq
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have he4 := e.isLt
  have hlt : ¬ e.val < 2 := by omega
  rcases (show e.val = 2 ∨ e.val = 3 by omega) with h2 | h3
  · have hj : CellLayout.sideHeightIndex e = 0 := by simp [CellLayout.sideHeightIndex, h2]
    simp only [CellLayout.cornerValue, CellLayout.sideVelocityValue, heightFaceMoment, hj, hlt, hbox]
    simp only [Fin.isValue, zero_ne_one, one_ne_zero, if_false, if_true]
    exact hbase K hK K.z₁ K.z₂ hz.ne (min_eq_left hz.le) (max_eq_right hz.le) _ _ _ _ hV hG0 hG2 hS hW1 hW2 t ht
  · have hj : CellLayout.sideHeightIndex e = 1 := by simp [CellLayout.sideHeightIndex, h3]
    simp only [CellLayout.cornerValue, CellLayout.sideVelocityValue, heightFaceMoment, hj, hlt, hbox]
    simp only [Fin.isValue, one_ne_zero, if_false, if_true]
    exact hbase K hK K.z₂ K.z₁ hz.ne' (min_eq_right hz.le) (max_eq_left hz.le) _ _ _ _ hV hG0 hG2 hS hW1 hW2 t ht

end Breakdown.CellCert.CellFormula

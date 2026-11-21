import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.TimeCoef
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.Transplant
import Breakdown.Torus.ApproxField

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ApproxLinks.Internal

theorem coord_near_of_ne {f : Space → Space} (hf : ∀ y, 1 / 8 ≤ dist y center → f y = 0) {v : Space}
    (hv : f v ≠ 0) (j : Fin 3) : |v j - 1 / 2| ≤ 1 / 8 := by
  have hd : dist v center < 1 / 8 := lt_of_not_ge fun h => hv (hf v h)
  have h1 := Transplant.Internal.abs_apply_le (v - center) j
  rw [PiLp.sub_apply, Transplant.Internal.center_apply] at h1
  rw [dist_eq_norm] at hd
  linarith

theorem wrap_eq_shift {f : Space → Space} (hf : ∀ y, 1 / 8 ≤ dist y center → f y = 0) (y : Space)
    (n : Lattice) (hn : ∀ j, |y j - n j - 1 / 2| < 7 / 8) :
    f (wrap y) = f (y - freq n) := by
  have hw : (∀ j, round (y j - 1 / 2) = n j) → wrap y = y - freq n := by
    intro h
    ext j
    rw [Transplant.Internal.wrap_apply, PiLp.sub_apply, Transplant.Internal.freq_apply', h j]
  by_cases h1 : f (wrap y) = 0
  · by_cases h2 : f (y - freq n) = 0
    · rw [h1, h2]
    · rw [hw fun j => ?_]
      have a1 := coord_near_of_ne hf h2 j
      have a2 := abs_sub_round (y j - 1 / 2)
      rw [PiLp.sub_apply, Transplant.Internal.freq_apply'] at a1
      refine Transplant.Internal.int_eq_of_abs_lt ?_
      rw [abs_le] at a1 a2
      rw [abs_lt]
      constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]
  · rw [hw fun j => ?_]
    have a1 := coord_near_of_ne hf h1 j
    have a2 := hn j
    rw [Transplant.Internal.wrap_apply] at a1
    refine Transplant.Internal.int_eq_of_abs_lt ?_
    rw [abs_le] at a1
    rw [abs_lt] at a2 ⊢
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2]

theorem wrap_eq_near {f : Space → Space} (hf : ∀ y, 1 / 8 ≤ dist y center → f y = 0) {x y : Space}
    (hy : y ∈ Metric.ball x (1 / 4)) :
    f (wrap y) = f (y - freq (fun j => round (x j - 1 / 2))) := by
  refine wrap_eq_shift hf y _ fun j => ?_
  have h1 := Transplant.Internal.abs_apply_le (y - x) j
  rw [PiLp.sub_apply] at h1
  have h2 := abs_sub_round (x j - 1 / 2)
  rw [Metric.mem_ball, dist_eq_norm] at hy
  rw [abs_le] at h1 h2
  rw [abs_lt]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

variable {W : ℝ → Space → Space} {q : ℝ → Space → ℝ} {C T : ℝ}

theorem approxField_far (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C) (hT : 0 < T)
    {t : ℝ} (ht : t < T) (y : Space) (hy : 1 / 8 ≤ dist y center) : approxField W T t y = 0 := by
  refine (((hA W q C T hW hT).2.2 t ht y).2.1 ?_).1
  rw [show centralRadius / 2 = 1 / 8 by norm_num [centralRadius]]
  exact hy

theorem isPeriodic_approxPeriodic (t : ℝ) : IsPeriodic (approxPeriodic W T t) := fun i x => by
  show approxField W T t (wrap (x + unitVector i)) = approxField W T t (wrap x)
  rw [Transplant.Internal.wrap_add_unitVector]

theorem divergence_approxPeriodic (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) {t : ℝ} (ht : t < T) (x : Space) : divergenceAt (approxPeriodic W T t) x = 0 := by
  have e : approxPeriodic W T t =ᶠ[𝓝 x]
      fun y => approxField W T t (y - freq (fun j => round (x j - 1 / 2))) := by
    filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
    exact wrap_eq_near (approxField_far hA hW hT ht) hy
  have e' := e.fderiv_eq (𝕜 := ℝ)
  have h := ((hA W q C T hW hT).2.2 t ht (x - freq (fun j => round (x j - 1 / 2)))).1
  simp only [divergenceAt] at h
  simp only [divergenceAt, e', fderiv_comp_sub (f := approxField W T t)]
  exact h

theorem contDiff_approxPeriodic (hA : ApproxFieldProperties) (hW : IsSimilarityProfile W q C)
    (hT : 0 < T) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hcT : ∀ s, c s < T) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => approxPeriodic W T (c z.1) z.2) := by
  have hsm := (hA W q C T hW hT).1
  have hG : ∀ n : Lattice,
      ContDiff ℝ ∞ (fun z : ℝ × Space => approxField W T (c z.1) (z.2 - freq n)) := fun n =>
    hsm.comp_contDiff (f := fun z : ℝ × Space => (c z.1, z.2 - freq n))
      ((hc.comp contDiff_fst).prodMk (contDiff_snd.sub contDiff_const))
      (fun z => ⟨hcT z.1, mem_univ _⟩)
  refine contDiff_iff_contDiffAt.mpr fun z => ?_
  refine (hG (fun j => round (z.2 j - 1 / 2))).contDiffAt.congr_of_eventuallyEq ?_
  filter_upwards [continuousAt_snd.preimage_mem_nhds
    (Metric.ball_mem_nhds z.2 (by norm_num : (0 : ℝ) < 1 / 4))] with w hw
  exact wrap_eq_near (approxField_far hA hW hT (hcT w.1)) hw

theorem continuousOn_toV_approxPeriodic (hA : ApproxFieldProperties) (hF : FreqTrSeriesSpec)
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcT : ∀ s, c s < T) :
    ContinuousOn (fun s => toV (approxPeriodic W T (c s))) (Ici 0) :=
  toVContinuous coefDeriv hF (fun s => approxPeriodic W T (c s))
    (contDiff_approxPeriodic hA hW hT hc hcT).contDiffOn
    (fun s _ => isPeriodic_approxPeriodic (c s))
    (fun s _ x => divergence_approxPeriodic hA hW hT (hcT s) x)

theorem stepStart_succ (T lam : ℝ) (n : ℕ) :
    stepStart T lam (n + 1) = stepStart T lam n + stepScale T lam n * (1 - lam) := by
  simp only [stepStart, stepScale, pow_succ]
  ring

theorem continuous_approxPiece (hA : ApproxFieldProperties) (hF : FreqTrSeriesSpec)
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) {lam : ℝ} (hl : 0 < lam) (n : ℕ) :
    Continuous (fun s : Icc (0 : ℝ) (1 - lam) => (stepScale T lam n) ^ (1 / 4 : ℝ) •
      toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s))) := by
  have hμ := stepScale_pos hT hl n
  have hμ1 := stepScale_pos hT hl (n + 1)
  have haT : stepStart T lam (n + 1) < T := by
    simp only [stepStart]
    linarith
  have hδ : 0 < (T - stepStart T lam (n + 1)) / 2 := by linarith
  have hc : ContDiff ℝ ∞ (fun s => ApproxField.Internal.timeClamp (stepStart T lam (n + 1))
      ((T - stepStart T lam (n + 1)) / 2) (stepStart T lam n + stepScale T lam n * s)) :=
    (ApproxField.Internal.contDiff_timeClamp _ _).comp
      (contDiff_const.add (contDiff_const.mul contDiff_id))
  have hcT : ∀ s, ApproxField.Internal.timeClamp (stepStart T lam (n + 1))
      ((T - stepStart T lam (n + 1)) / 2) (stepStart T lam n + stepScale T lam n * s) < T := by
    intro s
    have := ApproxField.Internal.timeClamp_le (a := stepStart T lam (n + 1)) hδ (stepStart T lam n + stepScale T lam n * s)
    linarith
  have hcont := continuousOn_toV_approxPeriodic hA hF hW hT hc hcT
  have hon : ContinuousOn (fun s : ℝ => (stepScale T lam n) ^ (1 / 4 : ℝ) •
      toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s))) (Icc 0 (1 - lam)) := by
    refine ((hcont.mono Icc_subset_Ici_self).const_smul ((stepScale T lam n) ^ (1 / 4 : ℝ))).congr
      fun s hs => ?_
    have hle : stepStart T lam n + stepScale T lam n * s ≤ stepStart T lam (n + 1) := by
      rw [stepStart_succ]
      have := mul_le_mul_of_nonneg_left hs.2 hμ.le
      linarith
    rw [Pi.smul_apply, ApproxField.Internal.timeClamp_of_le hδ hle]
  exact hon.domRestrict

theorem approxPiece_apply (hA : ApproxFieldProperties) (hF : FreqTrSeriesSpec)
    (hW : IsSimilarityProfile W q C) (hT : 0 < T) {lam : ℝ} (hl : 0 < lam) (n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) :
    approxPiece W T lam n s = (stepScale T lam n) ^ (1 / 4 : ℝ) •
      toV (approxPeriodic W T (stepStart T lam n + stepScale T lam n * s)) := by
  unfold approxPiece toPiece
  rw [dif_pos (continuous_approxPiece hA hF hW hT hl n)]
  rfl

end ApproxLinks.Internal

open ApproxLinks.Internal in
theorem approxLinks (hA : ApproxFieldProperties) (_hT : TransplantSmooth) (hF : FreqTrSeriesSpec) :
    ApproxLinks := by
  intro W q C T lam hW hT0 _ hl hl1 n
  refine ⟨approxPiece_apply hA hF hW hT0 hl n, ?_⟩
  have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
  unfold extendPiece pieceEnd
  rw [dif_pos h0, dif_pos h0, Set.IccExtend_left, ContinuousMap.evalCLM_apply,
    approxPiece_apply hA hF hW hT0 hl, approxPiece_apply hA hF hW hT0 hl]
  have e1 : stepStart T lam n + stepScale T lam n * (1 - lam) =
      stepStart T lam (n + 1) + stepScale T lam (n + 1) * 0 := by
    rw [mul_zero, add_zero, stepStart_succ]
  have e2 : stepScale T lam (n + 1) ^ (1 / 4 : ℝ) =
      lam ^ (1 / 4 : ℝ) * stepScale T lam n ^ (1 / 4 : ℝ) := by
    rw [show stepScale T lam (n + 1) = lam * stepScale T lam n by
      simp only [stepScale, pow_succ]; ring]
    exact Real.mul_rpow hl.le (stepScale_pos hT0 hl n).le
  dsimp only
  rw [e1, e2, smul_smul]

end Breakdown.Periodic

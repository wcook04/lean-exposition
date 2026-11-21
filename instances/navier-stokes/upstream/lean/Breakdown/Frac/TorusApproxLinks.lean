import Breakdown.Frac.StTorusStepApprox
import Breakdown.Torus.StatementsApproxSteps
import Breakdown.Torus.TimeCoef
import Breakdown.Torus.CoefCalculus
import Breakdown.Torus.ApproxField

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracLinks.Internal

def nearShift (x : Space) : Lattice := fun i => -round (x i - 1 / 2)

theorem freq_coord (k : Lattice) (i : Fin 3) : freq k i = k i := by
  simp [freq, unitVector, Pi.single_apply]

theorem center_coord (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem coord_le (v w : Space) (j : Fin 3) : |v j - w j| ≤ dist v w := by
  rw [dist_eq_norm]
  have := PiLp.norm_apply_le (v - w) j
  rwa [Real.norm_eq_abs, PiLp.sub_apply] at this

theorem periodize_near {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x y : Space) (hy : dist y x < 1 / 4) :
    latticePeriodize f y = f (y + freq (nearShift x)) := by
  unfold latticePeriodize
  refine tsum_eq_single (nearShift x) fun j hj => ?_
  by_contra h
  apply hj
  funext i
  have a1 := (coord_le _ _ i).trans (hf _ h)
  rw [PiLp.add_apply, freq_coord, center_coord] at a1
  have a2 := (coord_le y x i).trans hy.le
  have a3 := abs_sub_round (x i - 1 / 2)
  rw [abs_le] at a1 a2 a3
  have key : |((j i + round (x i - 1 / 2) : ℤ) : ℝ)| < 1 := by
    push_cast
    rw [abs_lt]
    constructor <;> linarith [a1.1, a1.2, a2.1, a2.2, a3.1, a3.2]
  have h' : |j i + round (x i - 1 / 2)| < 1 := by exact_mod_cast key
  have := abs_lt.mp h'
  simp only [nearShift]
  omega

theorem periodize_eventually {E : Type*} [NormedAddCommGroup E] {f : Space → E}
    (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8) (x : Space) :
    latticePeriodize f =ᶠ[𝓝 x] fun y => f (y + freq (nearShift x)) := by
  filter_upwards [Metric.ball_mem_nhds x (by norm_num : (0 : ℝ) < 1 / 4)] with y hy
  exact periodize_near hf x y hy

theorem freq_add_single (j : Lattice) (i : Fin 3) :
    freq (j + Pi.single i 1) = freq j + unitVector i := by
  ext k
  rw [PiLp.add_apply, freq_coord, freq_coord]
  by_cases h : k = i
  · subst h
    simp [unitVector]
  · simp [unitVector, h]

theorem isPeriodic_periodize {E : Type*} [NormedAddCommGroup E] (f : Space → E) :
    IsPeriodic (latticePeriodize f) := fun i x => by
  unfold latticePeriodize
  have h := (Equiv.addRight (Pi.single i 1 : Lattice)).tsum_eq (fun j => f (x + freq j))
  rw [← h]
  congr 1
  funext j
  simp only [Equiv.coe_addRight, freq_add_single]
  exact congrArg f (by abel)

theorem divergence_periodize {f : Space → Space} (hf : ∀ v, f v ≠ 0 → dist v center ≤ 1 / 8)
    (hdiv : ∀ v, divergenceAt f v = 0) (x : Space) : divergenceAt (latticePeriodize f) x = 0 := by
  have e' := (periodize_eventually hf x).fderiv_eq (𝕜 := ℝ)
  have h := hdiv (x + freq (nearShift x))
  simp only [divergenceAt] at h
  simp only [divergenceAt, e', fderiv_comp_add_right (f := f)]
  exact h

theorem contDiffOn_periodize {S : Set ℝ} {Φ : ℝ → Space → Space}
    (hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 z.2) (S ×ˢ univ))
    (hsupp : ∀ t ∈ S, ∀ v, Φ t v ≠ 0 → dist v center ≤ 1 / 8) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => latticePeriodize (Φ z.1) z.2) (S ×ˢ univ) := by
  apply contDiffOn_of_locally_contDiffOn
  rintro ⟨t, x⟩ -
  refine ⟨univ ×ˢ Metric.ball x (1 / 4), isOpen_univ.prod Metric.isOpen_ball,
    ⟨mem_univ _, Metric.mem_ball_self (by norm_num)⟩, ?_⟩
  have hc : ContDiffOn ℝ ∞ (fun z : ℝ × Space => Φ z.1 (z.2 + freq (nearShift x))) (S ×ˢ univ) :=
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const)).contDiffOn
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  refine (hc.mono inter_subset_left).congr fun z hz => ?_
  exact periodize_near (hsupp z.1 hz.1.1) x z.2 hz.2.2

variable {α a : ℝ} {U : Space → Space} {P : Space → ℝ} {T : ℝ}

theorem field_support (hA : FracApproxFieldProperties α) (hR : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) {t : ℝ} (ht : t < T) (v : Space) (hv : fracApproxField α a U T t v ≠ 0) :
    dist v center ≤ 1 / 8 := by
  by_contra h
  refine hv (((hA a U P hR T hT).2.2 t ht v).2.1 ?_).1
  rw [show centralRadius / 2 = 1 / 8 by norm_num [centralRadius]]
  exact (lt_of_not_ge h).le

theorem contDiff_periodized (hA : FracApproxFieldProperties α) (hR : IsRotatingProfile α a 1 U P)
    (hT : 0 < T) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c) (hcT : ∀ s, c s < T) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => latticePeriodize (fracApproxField α a U T (c z.1)) z.2) := by
  have hP := contDiffOn_periodize (hA a U P hR T hT).1
    (fun t ht v hv => field_support hA hR hT ht v hv)
  exact hP.comp_contDiff (f := fun z : ℝ × Space => (c z.1, z.2))
    ((hc.comp contDiff_fst).prodMk contDiff_snd) (fun z => ⟨hcT z.1, mem_univ _⟩)

theorem continuousOn_toV_periodized (hA : FracApproxFieldProperties α) (hF : FreqTrSeriesSpec)
    (hR : IsRotatingProfile α a 1 U P) (hT : 0 < T) {c : ℝ → ℝ} (hc : ContDiff ℝ ∞ c)
    (hcT : ∀ s, c s < T) :
    ContinuousOn (fun s => toV (latticePeriodize (fracApproxField α a U T (c s)))) (Ici 0) :=
  toVContinuous coefDeriv hF (fun s => latticePeriodize (fracApproxField α a U T (c s)))
    (contDiff_periodized hA hR hT hc hcT).contDiffOn
    (fun _ _ => isPeriodic_periodize _)
    (fun s _ x => divergence_periodize (fun v hv => field_support hA hR hT (hcT s) v hv)
      (fun v => ((hA a U P hR T hT).2.2 (c s) (hcT s) v).1) x)

theorem stepStart_succ (T lam : ℝ) (n : ℕ) :
    stepStart T lam (n + 1) = stepStart T lam n + stepScale T lam n * (1 - lam) := by
  simp only [stepStart, stepScale, pow_succ]
  ring

theorem continuous_piece (hA : FracApproxFieldProperties α) (hF : FreqTrSeriesSpec)
    (hR : IsRotatingProfile α a 1 U P) (hT : 0 < T) {lam : ℝ} (hl : 0 < lam) (n : ℕ) :
    Continuous (fun s : Icc (0 : ℝ) (1 - lam) => (stepScale T lam n) ^ dilExponent α •
      toV (latticePeriodize (fracApproxField α a U T (stepStart T lam n + stepScale T lam n * s)))) := by
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
    have := ApproxField.Internal.timeClamp_le (a := stepStart T lam (n + 1)) hδ
      (stepStart T lam n + stepScale T lam n * s)
    linarith
  have hcont := continuousOn_toV_periodized hA hF hR hT hc hcT
  have hon : ContinuousOn (fun s : ℝ => (stepScale T lam n) ^ dilExponent α •
      toV (latticePeriodize (fracApproxField α a U T (stepStart T lam n + stepScale T lam n * s))))
      (Icc 0 (1 - lam)) := by
    refine ((hcont.mono Icc_subset_Ici_self).const_smul ((stepScale T lam n) ^ dilExponent α)).congr
      fun s hs => ?_
    have hle : stepStart T lam n + stepScale T lam n * s ≤ stepStart T lam (n + 1) := by
      rw [stepStart_succ]
      have := mul_le_mul_of_nonneg_left hs.2 hμ.le
      linarith
    rw [Pi.smul_apply, ApproxField.Internal.timeClamp_of_le hδ hle]
  exact hon.domRestrict

theorem piece_apply (hA : FracApproxFieldProperties α) (hF : FreqTrSeriesSpec)
    (hR : IsRotatingProfile α a 1 U P) (hT : 0 < T) {lam : ℝ} (hl : 0 < lam) (n : ℕ)
    (s : Icc (0 : ℝ) (1 - lam)) :
    fracApproxPiece α a U T lam n s = (stepScale T lam n) ^ dilExponent α •
      toV (latticePeriodize (fracApproxField α a U T (stepStart T lam n + stepScale T lam n * s))) := by
  unfold fracApproxPiece toPiece
  rw [dif_pos (continuous_piece hA hF hR hT hl n)]
  rfl

end FracLinks.Internal

open FracLinks.Internal in
theorem fracApproxLinks (α : ℝ) (hα : 1 < α) (hA : FracApproxFieldProperties α)
    (hF : FreqTrSeriesSpec) : FracApproxLinks α := by
  intro a U P T lam hR hT0 _ hl hl1 n
  refine ⟨piece_apply hA hF hR hT0 hl n, ?_⟩
  have h0 : (0 : ℝ) ≤ 1 - lam := by linarith
  unfold extendPiece pieceEnd
  rw [dif_pos h0, dif_pos h0, Set.IccExtend_left, ContinuousMap.evalCLM_apply,
    piece_apply hA hF hR hT0 hl, piece_apply hA hF hR hT0 hl]
  have e1 : stepStart T lam n + stepScale T lam n * (1 - lam) =
      stepStart T lam (n + 1) + stepScale T lam (n + 1) * 0 := by
    rw [mul_zero, add_zero, stepStart_succ]
  have e2 : stepScale T lam (n + 1) ^ dilExponent α =
      lam ^ dilExponent α * stepScale T lam n ^ dilExponent α := by
    rw [show stepScale T lam (n + 1) = lam * stepScale T lam n by
      simp only [stepScale, pow_succ]; ring]
    exact Real.mul_rpow hl.le (stepScale_pos hT0 hl n).le
  dsimp only
  rw [e1, e2, smul_smul]

end Breakdown.Periodic

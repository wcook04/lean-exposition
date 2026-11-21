import TorusEuler.TerminalTimeCutoffCommutation
import TorusEuler.TerminalTimeCutoffRates

/-! Velocity and increment estimates for the differentiated actual cutoff. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

private theorem cutoffTime_slice {T : ℝ} {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T))) (x : Vec3) :
    ContDiffOn ℝ ∞ (fun t => V t x) (Icc 0 T) :=
  hV.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ ht => ⟨ht, mem_univ x⟩)

/-- The constant of the fixed dyadic cutoff tail at the requested depth. -/
def terminalCutoffTailCost (depth : ℕ) : ℝ :=
  cutoffHolderTailUniformConstant (cutoffSchwartzKernel
    (fun ξ hξ => dyadicMultiplierCutoff_zero ξ hξ.le) dyadicMultiplierCutoff_smooth) depth

theorem terminalCutoffTailCost_nonneg (depth : ℕ) : 0 ≤ terminalCutoffTailCost depth := by
  unfold terminalCutoffTailCost cutoffHolderTailUniformConstant cutoffKernelAbsoluteMoment
  positivity

/-- Any fixed Eulerian time derivative of the actual velocity cutoff
satisfies the same Appendix B tail estimate on the closed slab. -/
theorem TruncatedChildStage.slabTimeJet_velocityTail {T Λ : ℝ} {V RV : Velocity}
    (s : TruncatedChildStage T Λ dyadicMultiplierCutoff V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hΛ : 0 < Λ) {q m depth : ℕ} (hm : m ≤ depth) {t : ℝ} (ht : t ∈ Icc 0 T) :
    let jet := slabTimeJet 0 T q (fun r x => s.velocity r x - V r x) t
    SpatialHolderHalf m jet ∧ spatialHolderHalfNorm m jet ≤
      terminalCutoffTailCost depth * Λ ^ ((m : ℤ) - depth) *
        spatialHolderHalfNorm depth (slabTimeJet 0 T q V t) := by
  intro jet
  obtain ⟨g, hg⟩ := exists_continuousTorusTimeJets hT hV hVper
  have hrep : (fun x => g q t (toUnitTorus x)) = slabTimeJet 0 T q V t := funext (hg q t ht)
  have hG : SpatialHolderHalf depth (fun x => g q t (toUnitTorus x)) := by
    rw [hrep]
    exact spatialHolderHalf_of_contDiff_periodic (slabTimeJet_slice_smooth hT hV q ht)
      (slabTimeJet_periodic hVper q ht) depth
  have h := spatialHolderHalfNorm_cutoffVelocityDifference
    (fun ξ hξ => dyadicMultiplierCutoff_zero ξ hξ.le) dyadicMultiplierCutoff_smooth
    dyadicMultiplierCutoff_unit hΛ (g q t) hm hG
  change SpatialHolderHalf m ((fun x => realVectorFourierCutoff dyadicMultiplierCutoff Λ (g q t)
    (toUnitTorus x)) - (fun x => g q t (toUnitTorus x))) ∧ _ at h
  have hJet : jet = (fun x => realVectorFourierCutoff dyadicMultiplierCutoff Λ (g q t)
      (toUnitTorus x)) - (fun x => g q t (toUnitTorus x)) := by
    funext x
    change iteratedDerivWithin q ((fun r => s.velocity r x) - (fun r => V r x)) (Icc 0 T) t = _
    rw [iteratedDerivWithin_sub ht (uniqueDiffOn_Icc hT)
      ((cutoffTime_slice (V := s.velocity) s.smooth_velocity x).of_le (by simp) t ht)
      ((cutoffTime_slice hV x).of_le (by simp) t ht)]
    change slabTimeJet 0 T q s.velocity t x - slabTimeJet 0 T q V t x = _
    rw [s.slabTimeJet_velocity hT hV g hg q ht x, Pi.sub_apply, hg q t ht x]
  rw [hJet]
  simpa only [terminalCutoffTailCost, hrep] using h

/-- A differentiated mean correction and the differentiated cutoff tail
add to the exact child-minus-parent-minus-oscillation time jet. -/
theorem TruncatedChildStage.slabTimeJet_increment {T Λ : ℝ} {V RV U O M : Velocity}
    (s : TruncatedChildStage T Λ dyadicMultiplierCutoff V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T)))
    (hSplit : ∀ t ∈ Icc 0 T, V t = U t + O t + M t)
    (hΛ : 0 < Λ) {q m depth : ℕ} (hm : m ≤ depth) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hMjet : SpatialHolderHalf m (slabTimeJet 0 T q M t)) :
    let jet := slabTimeJet 0 T q (fun r x => s.velocity r x - U r x - O r x) t
    SpatialHolderHalf m jet ∧ spatialHolderHalfNorm m jet ≤
      spatialHolderHalfNorm m (slabTimeJet 0 T q M t) +
      terminalCutoffTailCost depth * Λ ^ ((m : ℤ) - depth) *
        spatialHolderHalfNorm depth (slabTimeJet 0 T q V t) := by
  intro jet
  let tail : Velocity := fun r x => s.velocity r x - V r x
  have htail := s.slabTimeJet_velocityTail hT hV hVper hΛ hm (q := q) ht
  have hTail : ContDiffOn ℝ ∞ (Function.uncurry tail) (Slab(T)) := s.smooth_velocity.sub hV
  have hJet : jet = slabTimeJet 0 T q M t + slabTimeJet 0 T q tail t := by
    funext x
    have hh : EqOn (fun r => s.velocity r x - U r x - O r x)
        ((fun r => M r x) + fun r => tail r x) (Icc 0 T) := by
      intro r hr
      have hv := congrFun (hSplit r hr) x
      simp only [Pi.add_apply] at hv ⊢
      change s.velocity r x - U r x - O r x = M r x + (s.velocity r x - V r x)
      rw [hv]
      abel
    exact (iteratedDerivWithin_congr hh ht).trans
      (iteratedDerivWithin_add ht (uniqueDiffOn_Icc hT)
        ((cutoffTime_slice hM x).of_le (by simp) t ht)
        ((cutoffTime_slice hTail x).of_le (by simp) t ht))
  rw [hJet]
  have h := spatialHolderHalf_add_exact hMjet htail.1
  exact ⟨h.1, h.2.trans (add_le_add le_rfl htail.2)⟩

/-- The exact omitted increment satisfies the paper's bound once the
selected mean jet and the full-depth approximate velocity jet are bounded. -/
theorem TruncatedChildStage.slabTimeJet_increment_rate {T freq : ℝ} {V RV U O M : Velocity}
    (s : TruncatedChildStage T (freq ^ (5 : ℕ)) dyadicMultiplierCutoff V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hVper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (V t))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Slab(T)))
    (hSplit : ∀ t ∈ Icc 0 T, V t = U t + O t + M t)
    {q m depth : ℕ} (hm : m ≤ depth) {t exponent : ℝ} (ht : t ∈ Icc 0 T) (hf : 2 ≤ freq)
    (hD : 5 * (m : ℝ) + 5 + exponent ≤ 3 * depth)
    (hCost : terminalCutoffTailCost depth ≤ freq)
    (hVrate : spatialHolderHalfNorm depth (slabTimeJet 0 T q V t) ≤ freq ^ (2 * ((depth : ℝ) + 1) + exponent))
    (hMrate : SpatialHolderHalf m (slabTimeJet 0 T q M t) ∧
      spatialHolderHalfNorm m (slabTimeJet 0 T q M t) ≤ (1 / 2 : ℝ) * freq⁻¹) :
    let jet := slabTimeJet 0 T q (fun r x => s.velocity r x - U r x - O r x) t
    SpatialHolderHalf m jet ∧ spatialHolderHalfNorm m jet ≤ freq⁻¹ := by
  intro jet
  have hf₀ : 0 < freq := zero_lt_two.trans_le hf
  have h := s.slabTimeJet_increment hT hV hVper hM hSplit (pow_pos hf₀ _) hm ht hMrate.1
  refine ⟨h.1, h.2.trans ?_⟩
  have htail := terminalTime_cutoff_tail_rate hf hCost hD
  rw [Real.rpow_neg_one] at htail
  have hcoef : 0 ≤ terminalCutoffTailCost depth * (freq ^ (5 : ℕ)) ^ ((m : ℤ) - depth) :=
    mul_nonneg (terminalCutoffTailCost_nonneg _) (zpow_nonneg (pow_nonneg hf₀.le _) _)
  exact (add_le_add hMrate.2 ((mul_le_mul_of_nonneg_left hVrate hcoef).trans htail)).trans_eq (by ring)

end

end TorusEuler

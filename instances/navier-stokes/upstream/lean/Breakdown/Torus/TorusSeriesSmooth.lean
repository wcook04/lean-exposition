import Breakdown.Torus.StatementsShell
import Breakdown.Torus.FreqTrSeries
import Breakdown.Torus.CoefCalculus

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace TorusSeriesSmooth.Internal

instance finiteCell : IsFiniteMeasure (volume.restrict cell) :=
  isFiniteMeasure_restrict.mpr FreqTrSeries.Internal.isCompact_cell.measure_lt_top.ne

theorem continuous_term (c : Coef) (k : Lattice) : Continuous (fun x => character (-k) x • c) :=
  (FreqTrSeries.Internal.continuous_character (-k)).smul continuous_const

theorem norm_term (c : Coef) (k : Lattice) (x : Space) : ‖character (-k) x • c‖ = ‖c‖ := by
  rw [norm_smul, FreqTrSeries.Internal.norm_character, one_mul]

def termBCF (c : Coef) (k : Lattice) : BoundedContinuousFunction Space Coef :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x => character (-k) x • c) (continuous_term c k)
    ‖c‖ (fun x => (norm_term c k x).le)

theorem norm_termBCF_le (c : Coef) (k : Lattice) : ‖termBCF c k‖ ≤ ‖c‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _ (norm_nonneg c) _

theorem lpOrZero_term (p : ℝ≥0∞) [Fact (1 ≤ p)] (c : Coef) (k : Lattice) :
    lpOrZero p (volume.restrict cell) (fun x => character (-k) x • c) =
      BoundedContinuousFunction.toLp (E := Coef) p (volume.restrict cell) ℝ (termBCF c k) := by
  have hm : MemLp (fun x => character (-k) x • c) p (volume.restrict cell) :=
    MemLp.of_bound (continuous_term c k).aestronglyMeasurable ‖c‖
      (Filter.Eventually.of_forall fun x => (norm_term c k x).le)
  unfold lpOrZero
  rw [dif_pos hm]
  exact Lp.ext ((hm.coeFn_toLp).trans
    (BoundedContinuousFunction.coeFn_toLp (E := Coef) p (volume.restrict cell) ℝ (termBCF c k)).symm)

theorem series_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] {g : Space → Space} (c : Lattice → Coef)
    (hs : Summable (fun k => ‖c k‖))
    (hsum : ∀ x, HasSum (fun k => character (-k) x • c k) (complexify (g x))) :
    (torusSeries p c : Space → Coef) =ᵐ[volume.restrict cell] (fun x => complexify (g x)) := by
  have hb : Summable (fun k => termBCF (c k) k) :=
    Summable.of_norm_bounded hs (fun k => norm_termBCF_le (c k) k)
  have hS : ∀ x, (∑' k, termBCF (c k) k) x = complexify (g x) := by
    intro x
    have h := hb.hasSum.map (BoundedContinuousFunction.evalCLM ℝ x)
      (BoundedContinuousFunction.evalCLM ℝ x).continuous
    exact (show HasSum (fun k => character (-k) x • c k)
      ((∑' k, termBCF (c k) k) x) from h).unique (hsum x)
  have hT : torusSeries p c =
      BoundedContinuousFunction.toLp (E := Coef) p (volume.restrict cell) ℝ (∑' k, termBCF (c k) k) := by
    unfold torusSeries
    simp_rw [lpOrZero_term]
    exact (hb.hasSum.map (BoundedContinuousFunction.toLp (E := Coef) p (volume.restrict cell) ℝ)
      (BoundedContinuousFunction.toLp (E := Coef) p (volume.restrict cell) ℝ).continuous).tsum_eq
  rw [hT]
  exact (BoundedContinuousFunction.coeFn_toLp (E := Coef) p (volume.restrict cell) ℝ _).trans
    (Filter.Eventually.of_forall hS)

theorem freqTr_ae (p : ℝ≥0∞) [Fact (1 ≤ p)] {f : Space → Space} (hf : ContDiff ℝ ∞ f)
    (hp : IsPeriodic f) :
    (torusSeries p (freqTrCoef f) : Space → Coef) =ᵐ[volume.restrict cell]
      (fun x => complexify (f x)) :=
  series_ae p (freqTrCoef f) (FreqTrSeries.Internal.summable_bounds coefDeriv hf hp).1
    (FreqTrSeries.Internal.hasSum_apply coefDeriv hf hp)

end TorusSeriesSmooth.Internal

open TorusSeriesSmooth.Internal in
theorem torusSeriesSmooth : TorusSeriesSmooth := by
  intro f hf hp hdiv
  have hc : coeff (toV f) = freqTrCoef f :=
    funext (FreqTrSeries.Internal.coeff_toV coefDeriv hf hp hdiv)
  have hg : ∀ j, gradCoef j (toV f) = freqTrCoef (FreqTrSeries.Internal.partialD j f) := by
    intro j
    funext k
    rw [FreqTrSeries.Internal.freqTrCoef_partialD coefDeriv j hf hp, gradCoef, hc]
  refine ⟨?_, ?_, fun j => ?_⟩
  · rw [hc]
    exact freqTr_ae 2 hf hp
  · rw [hc]
    exact freqTr_ae 6 hf hp
  · rw [hg j]
    exact freqTr_ae 2 (FreqTrSeries.Internal.contDiff_partialD j hf)
      (FreqTrSeries.Internal.isPeriodic_partialD j hp)

end Breakdown.Periodic

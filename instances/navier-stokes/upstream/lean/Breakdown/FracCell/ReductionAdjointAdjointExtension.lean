import Breakdown.FracCell.ReductionAdjointDefs
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.LinearSolveCore
import Breakdown.FracCell.AdjointConvectionPairing
import Breakdown.FracCell.ReductionAdjointGradientSecondApprox

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

def DriftPairingStatement : Prop :=
  ∀ (α a : ℝ) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)) (Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsAdjointRegular ζ Dζ Hζ →
      Integrable (fun y => inner ℝ (v y) (driftAdjointField α a ζ Dζ y)) ∧
        l2Pair (driftField α a v G) ζ = ∫ y, inner ℝ (v y) (driftAdjointField α a ζ Dζ y)

def ConvectionPairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)) (Hζ : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsAdjointRegular ζ Dζ Hζ →
    ∀ (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (C : ℝ), ContDiff ℝ 1 W →
      (∀ y, DW y = fderiv ℝ W y) → (∀ y, divergenceAt W y = 0) →
      (∀ y, ‖W y‖ ≤ C * (1 + ‖y‖)⁻¹ ∧ ‖DW y‖ ≤ C * (1 + ‖y‖) ^ (-2 : ℝ)) →
      Integrable (fun y => inner ℝ (v y) (convectionAdjointField W DW ζ Dζ y)) ∧
        l2Pair (fun y => (2 : ℝ) • symProduct W DW v G y) ζ =
          ∫ y, inner ℝ (v y) (convectionAdjointField W DW ζ Dζ y)

def NegTracePairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ X L : Space → Space, IsWeakNegTraceOf X L → MemLp X 2 volume → AEStronglyMeasurable L volume →
      MemLp (fun y => ‖y‖ • L y) 2 volume → l2Pair (negSecondTrace H) X = l2Pair v L

def GradientTracePairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (X : Space → Space) (DX : Space → (Space →L[ℝ] Space)), IsWeakGradientOf X DX → MemLp X 2 volume →
      AEStronglyMeasurable DX volume → Integrable (fun y => entrySq (DX y)) →
      l2Pair (negSecondTrace H) X = ∫ y, entryInner (G y) (DX y)

def MatrixDivergencePairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (Y : Space → (Space →L[ℝ] Space)) (E : Space → Space), IsWeakMatrixDivergenceOf Y E →
      AEStronglyMeasurable Y volume → Integrable (fun y => entrySq (Y y)) → AEStronglyMeasurable E volume →
      MemLp (fun y => ‖y‖ • E y) 2 volume → ∫ y, entryInner (G y) (Y y) = -l2Pair v E

def ScalarGradientTracePairingStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (q : Space → ℝ) (Q : Space → Space), IsWeakScalarGradientOf q Q → MemLp q 2 volume →
      AEStronglyMeasurable Q volume → MemLp (fun y => ‖y‖ • Q y) 2 volume → l2Pair v Q = 0

def CompactTraceWeightStatement : Prop :=
  ∀ X L : Space → Space, ContDiff ℝ 1 X → HasCompactSupport X → IsWeakNegTraceOf X L →
    AEStronglyMeasurable L volume → (∃ C : ℝ, ∀ᵐ y ∂volume, ‖L y‖ ≤ C) → MemLp (fun y => ‖y‖ • L y) 2 volume

def CompactWeakGradientStatement : Prop :=
  ∀ X : Space → Space, ContDiff ℝ 1 X → HasCompactSupport X → IsWeakGradientOf X (fun y => fderiv ℝ X y)


def SecondOrderTestApproxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∃ u : ℕ → Space → Space, (∀ n, IsTestVectorField (u n)) ∧
      (∀ n, Integrable (fun y => entrySq (fderiv ℝ (u n) y - G y))) ∧
      Tendsto (fun n => ∫ y, entrySq (fderiv ℝ (u n) y - G y)) atTop (𝓝 0) ∧
      (∀ n, Integrable (fun y => CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u n)) y - H y))) ∧
      Tendsto (fun n => ∫ y, CellCert.fullSecondSq (fderiv ℝ (fderiv ℝ (u n)) y - H y)) atTop (𝓝 0) ∧
      (∀ n, Integrable (fun y => ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2)) ∧
      Tendsto (fun n => ∫ y, ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2) atTop (𝓝 0)

private theorem inner_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y a b
  rw [a, b]

private theorem sq_integral_toLp {X : Space → Space} (hX : MemLp X 2 volume) :
    ∫ y, ‖X y‖ ^ 2 = ‖hX.toLp X‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hX.coeFn_toLp] with y hy
  rw [hy, real_inner_self_eq_norm_sq]

private theorem abs_pair_le {X Y : Space → Space} (hX : MemLp X 2 volume) (hY : MemLp Y 2 volume) :
    |∫ y, inner ℝ (X y) (Y y)| ≤ Real.sqrt (∫ y, ‖X y‖ ^ 2) * Real.sqrt (∫ y, ‖Y y‖ ^ 2) := by
  have e : ∫ y, inner ℝ (X y) (Y y) = inner ℝ (hX.toLp X) (hY.toLp Y) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hX.coeFn_toLp, hY.coeFn_toLp] with y a b
    rw [a, b]
  rw [e, sq_integral_toLp hX, sq_integral_toLp hY, Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)]
  exact abs_real_inner_le_norm _ _

private theorem pair_tendsto {A : ℕ → Space → Space} {A₀ B : Space → Space}
    (h0 : MemLp A₀ 2 volume) (hd : ∀ n, MemLp (fun y => A n y - A₀ y) 2 volume) (hB : MemLp B 2 volume)
    (h : Tendsto (fun n => ∫ y, ‖A n y - A₀ y‖ ^ 2) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ y, inner ℝ (A n y) (B y)) atTop (𝓝 (∫ y, inner ℝ (A₀ y) (B y))) := by
  have hA : ∀ n, MemLp (A n) 2 volume := fun n => by
    have := (hd n).add h0
    convert this using 1
    ext y
    simp
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun n => Real.sqrt (∫ y, ‖A n y - A₀ y‖ ^ 2) * Real.sqrt (∫ y, ‖B y‖ ^ 2))
      atTop (𝓝 0) := by
    have := h.sqrt.mul_const (Real.sqrt (∫ y, ‖B y‖ ^ 2))
    simpa using this
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hs
  have e : (∫ y, inner ℝ (A n y) (B y)) - ∫ y, inner ℝ (A₀ y) (B y) =
      ∫ y, inner ℝ (A n y - A₀ y) (B y) := by
    rw [← integral_sub (inner_integrable (hA n) hB) (inner_integrable h0 hB)]
    congr 1
    ext y
    rw [inner_sub_left]
  rw [Real.norm_eq_abs, e]
  exact abs_pair_le (hd n) hB

private theorem memLp_of_sq {f : Space → Space} (hf : AEStronglyMeasurable f volume)
    (h : Integrable (fun y => ‖f y‖ ^ 2)) : MemLp f 2 volume :=
  (memLp_two_iff_integrable_sq_norm hf).2 h

private theorem trace_sq_le (K : Space →L[ℝ] Space →L[ℝ] Space) :
    ‖secondTrace K‖ ^ 2 ≤ 3 * CellCert.fullSecondSq K := by
  have h1 : ‖secondTrace K‖ ≤ ∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖ := norm_sum_le _ _
  have h2 : (∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖) ^ 2 ≤
      3 * ∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖ ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun j : Fin 3 => ‖K (unitVector j) (unitVector j)‖)
    simpa using this
  have h3 : ∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖ ^ 2 ≤ CellCert.fullSecondSq K := by
    unfold CellCert.fullSecondSq
    refine Finset.sum_le_sum fun a _ => ?_
    exact Finset.single_le_sum (f := fun b => ‖K (unitVector a) (unitVector b)‖ ^ 2)
      (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  calc ‖secondTrace K‖ ^ 2 ≤ (∑ j : Fin 3, ‖K (unitVector j) (unitVector j)‖) ^ 2 := by gcongr
    _ ≤ _ := h2
    _ ≤ _ := by linarith

private theorem column_sq_le (M : Space →L[ℝ] Space) (i : Fin 3) : ‖M (unitVector i)‖ ^ 2 ≤ entrySq M :=
  Finset.single_le_sum (f := fun j => ‖M (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private theorem trace_continuous : Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => secondTrace K) := by
  unfold secondTrace
  exact continuous_finsetSum _ fun _ _ =>
    (continuous_id.clm_apply continuous_const).clm_apply continuous_const

private theorem trace_memLp {K : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hK : AEStronglyMeasurable K volume)
    (hi : Integrable (fun y => CellCert.fullSecondSq (K y))) : MemLp (fun y => secondTrace (K y)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => secondTrace (K y)) volume :=
    trace_continuous.comp_aestronglyMeasurable hK
  refine memLp_of_sq hm ((hi.const_mul 3).mono' (hm.norm.pow 2) ?_)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact trace_sq_le _

private theorem column_memLp {K : Space → (Space →L[ℝ] Space)} (hK : AEStronglyMeasurable K volume)
    (hi : Integrable (fun y => entrySq (K y))) (i : Fin 3) : MemLp (fun y => K y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => K y (unitVector i)) volume :=
    (continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hK
  refine memLp_of_sq hm (hi.mono' (hm.norm.pow 2) ?_)
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact column_sq_le _ _

private theorem weighted_inner_ae (a b : Space → Space) :
    (fun y => inner ℝ (‖y‖⁻¹ • a y) (‖y‖ • b y)) =ᵐ[volume] fun y => inner ℝ (a y) (b y) := by
  have h0 : ({0}ᶜ : Set Space) ∈ ae volume := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [h0] with y hy
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [real_inner_smul_left, real_inner_smul_right, inv_mul_cancel_left₀ hy']

private theorem weighted_sq (a : Space) (y : Space) : ‖‖y‖⁻¹ • a‖ ^ 2 = ‖a‖ ^ 2 / ‖y‖ ^ 2 := by
  rw [norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, div_eq_inv_mul]

private theorem weighted_velocity {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H) :
    MemLp (fun y => ‖y‖⁻¹ • v y) 2 volume := by
  have hi := (inverseSquareBound v G hv.measurable_velocity hv.velocity_six hv.gradient_two hv.weak_gradient).1
  refine memLp_of_sq ((measurable_norm.inv).aestronglyMeasurable.smul hv.measurable_velocity) ?_
  refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [weighted_sq]

private theorem weighted_pair_tendsto {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H)
    {u : ℕ → Space → Space} (hum : ∀ n, AEStronglyMeasurable (u n) volume)
    (hVi : ∀ n, Integrable (fun y => ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2))
    (hVt : Tendsto (fun n => ∫ y, ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2) atTop (𝓝 0))
    {E : Space → Space} (hE : MemLp (fun y => ‖y‖ • E y) 2 volume) :
    Tendsto (fun n => ∫ y, inner ℝ (u n y) (E y)) atTop (𝓝 (∫ y, inner ℝ (v y) (E y))) := by
  have e : ∀ w : Space → Space, ∫ y, inner ℝ (w y) (E y) = ∫ y, inner ℝ (‖y‖⁻¹ • w y) (‖y‖ • E y) :=
    fun w => (integral_congr_ae (weighted_inner_ae w E)).symm
  simp only [e]
  have hd : ∀ n, (fun y => ‖y‖⁻¹ • u n y - ‖y‖⁻¹ • v y) = fun y => ‖y‖⁻¹ • (u n y - v y) := fun n => by
    ext1 y
    rw [smul_sub]
  refine pair_tendsto (weighted_velocity hv) (fun n => ?_) hE ?_
  · rw [hd n]
    refine memLp_of_sq ((measurable_norm.inv).aestronglyMeasurable.smul
      ((hum n).sub hv.measurable_velocity)) ?_
    refine (hVi n).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [weighted_sq]
  · refine hVt.congr fun n => ?_
    congr 1
    ext1 y
    rw [← smul_sub, weighted_sq]

private theorem test_second_continuous {φ : Space → Space} (hφ : IsTestVectorField φ) :
    Continuous (fun y => fderiv ℝ (fderiv ℝ φ) y) :=
  (contDiff_infty_iff_fderiv.1 hφ.1).2.continuous_fderiv (by simp)

private theorem test_first_continuous {φ : Space → Space} (hφ : IsTestVectorField φ) :
    Continuous (fun y => fderiv ℝ φ y) :=
  hφ.1.continuous_fderiv (by simp)

private theorem ssp_eq (φ : Space → Space) (y : Space) :
    sumSecondPartialsAt φ y = secondTrace (fderiv ℝ (fderiv ℝ φ) y) := by
  unfold sumSecondPartialsAt secondTrace
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [iteratedFDeriv_two_apply]

private theorem trace_tendsto {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hHm : AEStronglyMeasurable H volume) (hHi : Integrable (fun y => CellCert.fullSecondSq (H y)))
    {K : ℕ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hKm : ∀ n, AEStronglyMeasurable (K n) volume)
    (hKi : ∀ n, Integrable (fun y => CellCert.fullSecondSq (K n y - H y)))
    (hKt : Tendsto (fun n => ∫ y, CellCert.fullSecondSq (K n y - H y)) atTop (𝓝 0))
    {X : Space → Space} (hX : MemLp X 2 volume) :
    Tendsto (fun n => ∫ y, inner ℝ (negSecondTrace (K n) y) (X y)) atTop
      (𝓝 (∫ y, inner ℝ (negSecondTrace H y) (X y))) := by
  have hsub : ∀ n, (fun y => negSecondTrace (K n) y - negSecondTrace H y) =
      fun y => -secondTrace (K n y - H y) := by
    intro n
    ext1 y
    simp only [negSecondTrace, secondTrace, ContinuousLinearMap.sub_apply, Finset.sum_sub_distrib]
    abel
  refine pair_tendsto (trace_memLp hHm hHi).neg (fun n => ?_) hX ?_
  · rw [hsub n]
    exact (trace_memLp ((hKm n).sub hHm) (hKi n)).neg
  · have hb : ∀ n, ∫ y, ‖negSecondTrace (K n) y - negSecondTrace H y‖ ^ 2 ≤
        ∫ y, 3 * CellCert.fullSecondSq (K n y - H y) := by
      intro n
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
        ((hKi n).const_mul 3) (Filter.Eventually.of_forall fun y => ?_)
      show ‖negSecondTrace (K n) y - negSecondTrace H y‖ ^ 2 ≤ 3 * CellCert.fullSecondSq (K n y - H y)
      rw [show negSecondTrace (K n) y - negSecondTrace H y = -secondTrace (K n y - H y) from
        congrFun (hsub n) y, norm_neg]
      exact trace_sq_le _
    refine squeeze_zero (fun n => integral_nonneg fun y => sq_nonneg _) hb ?_
    simp only [integral_const_mul]
    simpa using hKt.const_mul 3

private theorem entry_tendsto {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (hGi : Integrable (fun y => entrySq (G y)))
    {K : ℕ → Space → (Space →L[ℝ] Space)} (hKm : ∀ n, AEStronglyMeasurable (K n) volume)
    (hKi : ∀ n, Integrable (fun y => entrySq (K n y - G y)))
    (hKt : Tendsto (fun n => ∫ y, entrySq (K n y - G y)) atTop (𝓝 0))
    {Y : Space → (Space →L[ℝ] Space)} (hYm : AEStronglyMeasurable Y volume)
    (hYi : Integrable (fun y => entrySq (Y y))) :
    Tendsto (fun n => ∫ y, entryInner (K n y) (Y y)) atTop (𝓝 (∫ y, entryInner (G y) (Y y))) := by
  have hK : ∀ n, ∀ i, MemLp (fun y => K n y (unitVector i)) 2 volume := fun n i => by
    have := (column_memLp ((hKm n).sub hGm) (hKi n) i).add (column_memLp hGm hGi i)
    convert this using 1
    ext1 y
    simp
  have e : ∀ Z : Space → (Space →L[ℝ] Space), (∀ i, MemLp (fun y => Z y (unitVector i)) 2 volume) →
      ∫ y, entryInner (Z y) (Y y) = ∑ i : Fin 3, ∫ y, inner ℝ (Z y (unitVector i)) (Y y (unitVector i)) := by
    intro Z hZ
    unfold entryInner
    exact integral_finsetSum _ fun i _ => inner_integrable (hZ i) (column_memLp hYm hYi i)
  have e' : (fun n => ∫ y, entryInner (K n y) (Y y)) =
      fun n => ∑ i : Fin 3, ∫ y, inner ℝ (K n y (unitVector i)) (Y y (unitVector i)) :=
    funext fun n => e _ (hK n)
  rw [e', e G (column_memLp hGm hGi)]
  refine tendsto_finsetSum _ fun i _ => ?_
  refine pair_tendsto (column_memLp hGm hGi i) (fun n => ?_) (column_memLp hYm hYi i) ?_
  · have := column_memLp ((hKm n).sub hGm) (hKi n) i
    simpa using this
  · refine squeeze_zero (fun n => integral_nonneg fun y => sq_nonneg _) (fun n => ?_) hKt
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _) (hKi n)
      (Filter.Eventually.of_forall fun y => ?_)
    have := column_sq_le (K n y - G y) i
    simpa using this


private theorem test_memLp {φ : Space → Space} (hφ : IsTestVectorField φ) : MemLp φ 2 volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2

private theorem test_dir {φ : Space → Space} (hφ : IsTestVectorField φ) (w : Space) :
    IsTestVectorField (fun z => fderiv ℝ φ z w) :=
  ⟨(contDiff_infty_iff_fderiv.1 hφ.1).2.clm_apply contDiff_const, hφ.2.fderiv_apply (𝕜 := ℝ) w⟩

private theorem dir_fderiv {φ : Space → Space} (hφ : IsTestVectorField φ) (w y a : Space) :
    fderiv ℝ (fun z => fderiv ℝ φ z w) y a = fderiv ℝ (fderiv ℝ φ) y a w := by
  have hd : DifferentiableAt ℝ (fderiv ℝ φ) y :=
    ((contDiff_infty_iff_fderiv.1 hφ.1).2.differentiable (by simp)) y
  rw [fderiv_clm_apply hd (differentiableAt_const w)]
  simp

private theorem coord_test {φ : Space → Space} (hφ : IsTestVectorField φ) (i : Fin 3) :
    IsTestScalar (fun y => φ y i) :=
  ⟨(EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp hφ.1,
    HasCompactSupport.comp_left (g := fun w : Space => w i) hφ.2 (by simp)⟩

private theorem coord_fderiv {φ : Space → Space} (hφ : IsTestVectorField φ) (i : Fin 3) (y w : Space) :
    fderiv ℝ (fun y => φ y i) y w = fderiv ℝ φ y w i := by
  have hψd : DifferentiableAt ℝ φ y := (hφ.1.differentiable (by simp)) y
  have : fderiv ℝ (fun y => φ y i) y = (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ φ y) :=
    ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y hψd.hasFDerivAt).fderiv
  rw [this]
  rfl

private theorem inner_coords (a b : Space) : inner ℝ a b = ∑ i : Fin 3, a i * b i := by
  simp [PiLp.inner_apply, mul_comm]

private theorem weak_vec {X : Space → Space} {DX : Space → (Space →L[ℝ] Space)} (hX : IsWeakGradientOf X DX)
    (hX2 : MemLp X 2 volume) (hD2 : ∀ j, MemLp (fun y => DX y (unitVector j)) 2 volume)
    {ψ : Space → Space} (hψ : IsTestVectorField ψ) (j : Fin 3) :
    ∫ y, inner ℝ (fderiv ℝ ψ y (unitVector j)) (X y) = -∫ y, inner ℝ (ψ y) (DX y (unitVector j)) := by
  have hXl : LocallyIntegrable X volume := hX2.locallyIntegrable (by norm_num)
  have hDl : LocallyIntegrable (fun y => DX y (unitVector j)) volume := (hD2 j).locallyIntegrable (by norm_num)
  have hcomp : ∀ i : Fin 3, ∫ y, fderiv ℝ ψ y (unitVector j) i * X y i =
      -∫ y, ψ y i * DX y (unitVector j) i := by
    intro i
    have hφ := coord_test hψ i
    have h := hX _ hφ j
    have i1 : Integrable (fun y => fderiv ℝ (fun y => ψ y i) y (unitVector j) • X y) :=
      hXl.integrable_smul_left_of_hasCompactSupport
        ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => ψ y i • DX y (unitVector j)) :=
      hDl.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have c1 := congrArg (fun w : Space => (EuclideanSpace.proj i : Space →L[ℝ] ℝ) w) h
    simp only [map_neg] at c1
    rw [← (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i1,
      ← (EuclideanSpace.proj i : Space →L[ℝ] ℝ).integral_comp_comm i2] at c1
    simpa [coord_fderiv hψ] using c1
  have hint : ∀ (a b : Space → Space), MemLp a 2 volume → MemLp b 2 volume → ∀ i : Fin 3,
      Integrable (fun y => a y i * b y i) := by
    intro a b ha hb i
    have hai : MemLp (fun y => a y i) 2 volume := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' ha
    have hbi : MemLp (fun y => b y i) 2 volume := (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp_memLp' hb
    exact hai.integrable_mul hbi
  have hψ2 := test_memLp hψ
  have hdψ2 := test_memLp (test_dir hψ (unitVector j))
  simp only [inner_coords]
  rw [integral_finsetSum _ fun i _ => hint _ _ hdψ2 hX2 i, integral_finsetSum _ fun i _ => hint _ _ hψ2 (hD2 j) i,
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => hcomp i

private theorem weighted_integrable {a b : Space → Space} (ha : MemLp (fun y => ‖y‖⁻¹ • a y) 2 volume)
    (hb : MemLp (fun y => ‖y‖ • b y) 2 volume) {f : Space → ℝ} (hf : AEStronglyMeasurable f volume)
    (hle : ∀ y, |f y| ≤ ‖a y‖ * ‖b y‖) : Integrable f := by
  have hp : Integrable (fun y => ‖‖y‖⁻¹ • a y‖ * ‖‖y‖ • b y‖) := ha.norm.integrable_mul hb.norm
  refine hp.mono' hf ?_
  have h0 : ({0}ᶜ : Set Space) ∈ ae volume := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [h0] with y hy
  have hy' : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  rw [Real.norm_eq_abs, norm_smul, norm_smul, norm_inv, norm_norm]
  calc |f y| ≤ ‖a y‖ * ‖b y‖ := hle y
    _ = ‖y‖⁻¹ * ‖a y‖ * (‖y‖ * ‖b y‖) := by field_simp

private theorem weighted_approx_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hv : IsSecondOrderField m v G H)
    {w : Space → Space} (hw : AEStronglyMeasurable w volume)
    (hi : Integrable (fun y => ‖w y - v y‖ ^ 2 / ‖y‖ ^ 2)) : MemLp (fun y => ‖y‖⁻¹ • w y) 2 volume := by
  have h1 : MemLp (fun y => ‖y‖⁻¹ • (w y - v y)) 2 volume := by
    refine memLp_of_sq ((measurable_norm.inv).aestronglyMeasurable.smul (hw.sub hv.measurable_velocity)) ?_
    refine hi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [weighted_sq]
  have := h1.add (weighted_velocity hv)
  convert this using 1
  ext1 y
  simp [smul_sub]

private theorem coord_abs_le (a : Space) (i : Fin 3) : |a i| ≤ ‖a‖ := by
  have := PiLp.norm_apply_le a i
  rwa [Real.norm_eq_abs] at this

private theorem inner_unit (a : Space) (i : Fin 3) : inner ℝ a (unitVector i) = a i := by
  simp [unitVector, EuclideanSpace.inner_single_right]

private theorem expand (x : Space) : x = ∑ k : Fin 3, x k • unitVector k := by
  ext i
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three, PiLp.single_apply]

private theorem apply_expand (M : Space →L[ℝ] Space) (x : Space) :
    M x = ∑ k : Fin 3, x k • M (unitVector k) := by
  conv_lhs => rw [expand x]
  simp [map_sum, map_smul]

private theorem coordL_contDiff (B : Space →L[ℝ] Space) (k : Fin 3) : ContDiff ℝ ∞ (fun y => B y k) :=
  (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp B.contDiff

private theorem coordL_fderiv (B : Space →L[ℝ] Space) (k : Fin 3) (y w : Space) :
    fderiv ℝ (fun y => B y k) y w = B w k := by
  have : fderiv ℝ (fun y => B y k) y = (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp B :=
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).hasFDerivAt.comp y B.hasFDerivAt).fderiv
  rw [this]
  rfl

private theorem ibp_test {u : Space → Space} (hu : IsTestVectorField u) (B : Space →L[ℝ] Space) (k : Fin 3) :
    IsTestVectorField (fun y => B y k • u y) :=
  ⟨(coordL_contDiff B k).smul hu.1, HasCompactSupport.smul_left (f := fun y => B y k) hu.2⟩

private theorem ibp_fderiv {u : Space → Space} (hu : IsTestVectorField u) (B : Space →L[ℝ] Space) (k : Fin 3)
    (y : Space) : fderiv ℝ (fun y => B y k • u y) y (unitVector k) =
      B y k • fderiv ℝ u y (unitVector k) + B (unitVector k) k • u y := by
  have hud : Differentiable ℝ u := hu.1.differentiable (by simp)
  rw [fderiv_fun_smul ((coordL_contDiff B k).differentiable (by simp) y) (hud y)]
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    coordL_fderiv]

private theorem ibp_lin {ζ : Space → Space} {Dζ : Space → (Space →L[ℝ] Space)} (hζ : IsWeakGradientOf ζ Dζ)
    (hζ2 : MemLp ζ 2 volume) (hD2 : ∀ j, MemLp (fun y => Dζ y (unitVector j)) 2 volume)
    {u : Space → Space} (hu : IsTestVectorField u) (B : Space →L[ℝ] Space) :
    ∫ y, inner ℝ (fderiv ℝ u y (B y)) (ζ y) =
      -((∑ k : Fin 3, B (unitVector k) k) * ∫ y, inner ℝ (u y) (ζ y)) -
        ∫ y, inner ℝ (u y) (Dζ y (B y)) := by
  have hu2 := test_memLp hu
  have i1 : ∀ k : Fin 3, Integrable (fun y => inner ℝ (B y k • fderiv ℝ u y (unitVector k)) (ζ y)) := by
    intro k
    have hm : MemLp (fun y => B y k • fderiv ℝ u y (unitVector k)) 2 volume :=
      ((coordL_contDiff B k).continuous.smul
        ((hu.1.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_of_hasCompactSupport
        (HasCompactSupport.smul_left (f := fun y => B y k) ((test_dir hu (unitVector k)).2))
    exact inner_integrable hm hζ2
  have i3 : ∀ k : Fin 3, Integrable (fun y => inner ℝ (u y) (B y k • Dζ y (unitVector k))) := by
    intro k
    have := inner_integrable (test_memLp (ibp_test hu B k)) (hD2 k)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [real_inner_smul_left, real_inner_smul_right]
  have hk : ∀ k : Fin 3, ∫ y, inner ℝ (B y k • fderiv ℝ u y (unitVector k)) (ζ y) =
      -(B (unitVector k) k * ∫ y, inner ℝ (u y) (ζ y)) -
        ∫ y, inner ℝ (u y) (B y k • Dζ y (unitVector k)) := by
    intro k
    have h := weak_vec hζ hζ2 hD2 (ibp_test hu B k) k
    simp only [ibp_fderiv hu B k, inner_add_left] at h
    have i2 : Integrable (fun y => inner ℝ (B (unitVector k) k • u y) (ζ y)) :=
      inner_integrable (by exact hu2.const_smul (B (unitVector k) k)) hζ2
    rw [integral_add (i1 k) i2] at h
    have e2 : ∫ y, inner ℝ (B (unitVector k) k • u y) (ζ y) =
        B (unitVector k) k * ∫ y, inner ℝ (u y) (ζ y) := by
      simp only [real_inner_smul_left, integral_const_mul]
    have e3 : ∫ y, inner ℝ (B y k • u y) (Dζ y (unitVector k)) =
        ∫ y, inner ℝ (u y) (B y k • Dζ y (unitVector k)) := by
      congr 1
      ext y
      rw [real_inner_smul_left, real_inner_smul_right]
    linarith
  have hl : ∀ y, inner ℝ (fderiv ℝ u y (B y)) (ζ y) =
      ∑ k : Fin 3, inner ℝ (B y k • fderiv ℝ u y (unitVector k)) (ζ y) := fun y => by
    rw [apply_expand (fderiv ℝ u y) (B y), sum_inner]
  have hr : ∀ y, inner ℝ (u y) (Dζ y (B y)) =
      ∑ k : Fin 3, inner ℝ (u y) (B y k • Dζ y (unitVector k)) := fun y => by
    rw [apply_expand (Dζ y) (B y), inner_sum]
  simp only [hl, hr]
  rw [integral_finsetSum _ fun k _ => i1 k, integral_finsetSum _ fun k _ => i3 k]
  simp only [hk, Finset.sum_sub_distrib, Finset.sum_neg_distrib, Finset.sum_mul]

private def turnL : Space →L[ℝ] Space :=
  (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).smulRight (unitVector 1) -
    (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).smulRight (unitVector 0)

private theorem turnL_apply (y : Space) : turnL y = axialTurn y := by
  ext i
  fin_cases i <;> simp [turnL, axialTurn, unitVector, PiLp.single_apply]

private theorem turn_trace : ∑ k : Fin 3, axialTurn (unitVector k) k = 0 := by
  simp [axialTurn, unitVector, Fin.sum_univ_three, PiLp.single_apply]

private theorem unit_trace : ∑ k : Fin 3, unitVector k k = 3 := by
  simp [unitVector, Fin.sum_univ_three, PiLp.single_apply]

private theorem turn_norm_le (x : Space) : ‖axialTurn x‖ ≤ ‖x‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [axialTurn, Fin.sum_univ_three, PiLp.single_apply]
  nlinarith [sq_nonneg (x 0), sq_nonneg (x 1), sq_nonneg (x 2)]

private theorem turn_inner (a b : Space) : inner ℝ (axialTurn a) b = -inner ℝ a (axialTurn b) := by
  simp only [inner_coords, Fin.sum_univ_three]
  simp [axialTurn, PiLp.single_apply]

private theorem clm_norm_le (K : Space →L[ℝ] Space) (x : Space) : ‖K x‖ ≤ Real.sqrt (entrySq K) * ‖x‖ := by
  have h := LinearStateClosedInternal.clm_sq_le K x
  have h0 : 0 ≤ entrySq K := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [← Real.sqrt_sq (norm_nonneg (K x)), ← Real.sqrt_sq (norm_nonneg x), ← Real.sqrt_mul h0]
  exact Real.sqrt_le_sqrt h

private theorem apply_meas {A : Space → (Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A volume)
    {b : Space → Space} (hb : AEStronglyMeasurable b volume) : AEStronglyMeasurable (fun y => A y (b y)) volume :=
  Continuous.comp_aestronglyMeasurable₂ (g := fun (L : Space →L[ℝ] Space) (x : Space) => L x)
    (continuous_fst.clm_apply continuous_snd) hA hb

private theorem turn_continuous : Continuous axialTurn := by
  have : axialTurn = fun y => turnL y := funext fun y => (turnL_apply y).symm
  rw [this]
  exact turnL.continuous

private theorem sq_add_le2 (p q : ℝ) : (p + q) ^ 2 ≤ 2 * p ^ 2 + 2 * q ^ 2 := by
  nlinarith [sq_nonneg (p - q)]

private theorem drift_norm_le (α a : ℝ) (w : Space → Space) (K : Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖driftField α a w K y‖ ≤ (|1 - 1 / (2 * α)| + |a|) * ‖w y‖ +
      (|1 / (2 * α)| + |a|) * (Real.sqrt (entrySq (K y)) * ‖y‖) := by
  set s := Real.sqrt (entrySq (K y))
  have hKy : ‖K y y‖ ≤ s * ‖y‖ := clm_norm_le _ _
  have hKJ : ‖K y (axialTurn y)‖ ≤ s * ‖y‖ :=
    (clm_norm_le _ _).trans (mul_le_mul_of_nonneg_left (turn_norm_le y) (Real.sqrt_nonneg _))
  have e2 : ‖K y (axialTurn y) - axialTurn (w y)‖ ≤ s * ‖y‖ + ‖w y‖ :=
    (norm_sub_le _ _).trans (add_le_add hKJ (turn_norm_le _))
  have e1 : ‖(1 - 1 / (2 * α)) • w y + (1 / (2 * α)) • K y y +
      a • (K y (axialTurn y) - axialTurn (w y))‖ ≤
      ‖(1 - 1 / (2 * α)) • w y‖ + ‖(1 / (2 * α)) • K y y‖ + ‖a • (K y (axialTurn y) - axialTurn (w y))‖ :=
    (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at e1
  unfold driftField
  have := add_le_add (add_le_add (le_refl (|1 - 1 / (2 * α)| * ‖w y‖))
    (mul_le_mul_of_nonneg_left hKy (abs_nonneg (1 / (2 * α)))))
    (mul_le_mul_of_nonneg_left e2 (abs_nonneg a))
  nlinarith [abs_nonneg a, norm_nonneg (w y), abs_nonneg (1 / (2 * α)), abs_nonneg (1 - 1 / (2 * α))]

private theorem drift_weighted_sq (α a : ℝ) (w : Space → Space) (K : Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖‖y‖⁻¹ • driftField α a w K y‖ ^ 2 ≤
      2 * (|1 - 1 / (2 * α)| + |a|) ^ 2 * (‖w y‖ ^ 2 / ‖y‖ ^ 2) + 2 * (|1 / (2 * α)| + |a|) ^ 2 * entrySq (K y) := by
  have h0 : 0 ≤ entrySq (K y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hy : y = 0
  · subst hy
    have hz : ‖‖(0 : Space)‖⁻¹ • driftField α a w K 0‖ ^ 2 = 0 := by simp
    rw [hz]
    exact add_nonneg (by positivity) (mul_nonneg (by positivity) h0)
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  set c1 := |1 - 1 / (2 * α)| + |a|
  set c2 := |1 / (2 * α)| + |a|
  set s := Real.sqrt (entrySq (K y))
  have hD := drift_norm_le α a w K y
  have hb : ‖‖y‖⁻¹ • driftField α a w K y‖ ≤ c1 * (‖w y‖ / ‖y‖) + c2 * s := by
    rw [norm_smul, norm_inv, norm_norm]
    rw [inv_mul_le_iff₀ hr]
    calc ‖driftField α a w K y‖ ≤ c1 * ‖w y‖ + c2 * (s * ‖y‖) := hD
      _ = ‖y‖ * (c1 * (‖w y‖ / ‖y‖) + c2 * s) := by field_simp
  have hs : s ^ 2 = entrySq (K y) := Real.sq_sqrt h0
  calc ‖‖y‖⁻¹ • driftField α a w K y‖ ^ 2 ≤ (c1 * (‖w y‖ / ‖y‖) + c2 * s) ^ 2 := by gcongr
    _ ≤ 2 * (c1 * (‖w y‖ / ‖y‖)) ^ 2 + 2 * (c2 * s) ^ 2 := sq_add_le2 _ _
    _ = _ := by rw [mul_pow, mul_pow, div_pow, hs]; ring

private theorem adj_norm_le (α a : ℝ) (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖driftAdjointField α a ζ Dζ y‖ ≤ (|1 - 4 * (1 / (2 * α))| + |a|) * ‖ζ y‖ +
      (|1 / (2 * α)| + |a|) * (Real.sqrt (entrySq (Dζ y)) * ‖y‖) := by
  set s := Real.sqrt (entrySq (Dζ y))
  have hKy : ‖Dζ y y‖ ≤ s * ‖y‖ := clm_norm_le _ _
  have hKJ : ‖Dζ y (axialTurn y)‖ ≤ s * ‖y‖ :=
    (clm_norm_le _ _).trans (mul_le_mul_of_nonneg_left (turn_norm_le y) (Real.sqrt_nonneg _))
  have e2 : ‖Dζ y (axialTurn y) - axialTurn (ζ y)‖ ≤ s * ‖y‖ + ‖ζ y‖ :=
    (norm_sub_le _ _).trans (add_le_add hKJ (turn_norm_le _))
  have e1 : ‖(1 - 4 * (1 / (2 * α))) • ζ y - (1 / (2 * α)) • Dζ y y -
      a • (Dζ y (axialTurn y) - axialTurn (ζ y))‖ ≤
      ‖(1 - 4 * (1 / (2 * α))) • ζ y‖ + ‖(1 / (2 * α)) • Dζ y y‖ +
        ‖a • (Dζ y (axialTurn y) - axialTurn (ζ y))‖ :=
    (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
  rw [norm_smul, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs] at e1
  unfold driftAdjointField
  have := add_le_add (add_le_add (le_refl (|1 - 4 * (1 / (2 * α))| * ‖ζ y‖))
    (mul_le_mul_of_nonneg_left hKy (abs_nonneg (1 / (2 * α)))))
    (mul_le_mul_of_nonneg_left e2 (abs_nonneg a))
  nlinarith [abs_nonneg a, norm_nonneg (ζ y), abs_nonneg (1 / (2 * α)), abs_nonneg (1 - 4 * (1 / (2 * α)))]

private theorem adj_weighted_sq (α a : ℝ) (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)) (y : Space) :
    ‖‖y‖ • driftAdjointField α a ζ Dζ y‖ ^ 2 ≤
      2 * (|1 - 4 * (1 / (2 * α))| + |a|) ^ 2 * ‖‖y‖ • ζ y‖ ^ 2 +
        2 * (|1 / (2 * α)| + |a|) ^ 2 * (‖y‖ ^ 4 * entrySq (Dζ y)) := by
  have h0 : 0 ≤ entrySq (Dζ y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  set c3 := |1 - 4 * (1 / (2 * α))| + |a|
  set c4 := |1 / (2 * α)| + |a|
  set s := Real.sqrt (entrySq (Dζ y))
  have hD := adj_norm_le α a ζ Dζ y
  have hb : ‖‖y‖ • driftAdjointField α a ζ Dζ y‖ ≤ c3 * (‖y‖ * ‖ζ y‖) + c4 * (s * ‖y‖ ^ 2) := by
    rw [norm_smul, norm_norm]
    calc ‖y‖ * ‖driftAdjointField α a ζ Dζ y‖ ≤ ‖y‖ * (c3 * ‖ζ y‖ + c4 * (s * ‖y‖)) :=
          mul_le_mul_of_nonneg_left hD (norm_nonneg _)
      _ = _ := by ring
  have hs : s ^ 2 = entrySq (Dζ y) := Real.sq_sqrt h0
  have hz : ‖‖y‖ • ζ y‖ = ‖y‖ * ‖ζ y‖ := by rw [norm_smul, norm_norm]
  rw [hz]
  calc ‖‖y‖ • driftAdjointField α a ζ Dζ y‖ ^ 2 ≤ (c3 * (‖y‖ * ‖ζ y‖) + c4 * (s * ‖y‖ ^ 2)) ^ 2 := by gcongr
    _ ≤ 2 * (c3 * (‖y‖ * ‖ζ y‖)) ^ 2 + 2 * (c4 * (s * ‖y‖ ^ 2)) ^ 2 := sq_add_le2 _ _
    _ = _ := by rw [mul_pow c4, mul_pow s, hs]; ring

private theorem integral_lin4 {f0 f1 f2 f3 : Space → ℝ} (h0 : Integrable f0) (h1 : Integrable f1)
    (h2 : Integrable f2) (h3 : Integrable f3) (c0 c1 c2 : ℝ) :
    ∫ y, (c0 * f0 y + c1 * f1 y + c2 * (f2 y - f3 y)) =
      c0 * (∫ y, f0 y) + c1 * (∫ y, f1 y) + c2 * ((∫ y, f2 y) - ∫ y, f3 y) := by
  have hA : Integrable (fun y => c0 * f0 y + c1 * f1 y) := (h0.const_mul c0).add (h1.const_mul c1)
  have hB : Integrable (fun y => c2 * (f2 y - f3 y)) := (h2.sub h3).const_mul c2
  have hC : Integrable (fun y => c0 * f0 y) := h0.const_mul c0
  have hD : Integrable (fun y => c1 * f1 y) := h1.const_mul c1
  rw [integral_add hA hB, integral_add hC hD, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_sub h2 h3]

private theorem clm_apply_memLp_weighted {Dζ : Space → (Space →L[ℝ] Space)} (hDm : AEStronglyMeasurable Dζ volume)
    (hD4 : Integrable (fun y => ‖y‖ ^ 4 * entrySq (Dζ y))) (B : Space →L[ℝ] Space) (hB : ∀ y, ‖B y‖ ≤ ‖y‖) :
    MemLp (fun y => ‖y‖ • Dζ y (B y)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => ‖y‖ • Dζ y (B y)) volume :=
    measurable_norm.aestronglyMeasurable.smul (apply_meas hDm B.continuous.aestronglyMeasurable)
  refine memLp_of_sq hm (hD4.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), norm_smul, norm_norm]
  have h0 : 0 ≤ entrySq (Dζ y) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h1 := LinearStateClosedInternal.clm_sq_le (Dζ y) (B y)
  have h2 : ‖B y‖ ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hB y) 2
  calc (‖y‖ * ‖Dζ y (B y)‖) ^ 2 = ‖y‖ ^ 2 * ‖Dζ y (B y)‖ ^ 2 := by ring
    _ ≤ ‖y‖ ^ 2 * (entrySq (Dζ y) * ‖y‖ ^ 2) := by
        gcongr
        exact h1.trans (mul_le_mul_of_nonneg_left h2 h0)
    _ = _ := by ring

def WeakGradientFirstOrderTestStatement : Prop :=
  ∀ (ζ : Space → Space) (Dζ : Space → (Space →L[ℝ] Space)), IsWeakGradientOf ζ Dζ →
    LocallyIntegrable ζ volume → (∀ j : Fin 3, LocallyIntegrable (fun y => Dζ y (unitVector j)) volume) →
    ∀ φ : Space → ℝ, ContDiff ℝ 1 φ → HasCompactSupport φ → ∀ j : Fin 3,
      ∫ y, (fderiv ℝ φ y (unitVector j)) • ζ y = -∫ y, φ y • Dζ y (unitVector j)

theorem weakGradientFirstOrderTest : WeakGradientFirstOrderTestStatement := by
  intro ζ Dζ hw hζ hD φ hφ hφc j
  exact FracInternal.ConvectionPairing.weak_of_C1 hζ j (hD j) hw hφ hφc

theorem compactWeakGradient : CompactWeakGradientStatement := by
  intro X hX hXc φ hφ j
  obtain ⟨hφs, hφc⟩ := hφ
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hXd : Differentiable ℝ X := hX.differentiable (by simp)
  have hφ' : Continuous (fun y => fderiv ℝ φ y) := hφs.continuous_fderiv (by simp)
  have hX' : Continuous (fun y => fderiv ℝ X y) := hX.continuous_fderiv one_ne_zero
  have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • X y) :=
    ((hφ'.clm_apply continuous_const).smul hX.continuous).integrable_of_hasCompactSupport hXc.smul_left
  have i2 : Integrable (fun y => φ y • fderiv ℝ X y (unitVector j)) :=
    (hφs.continuous.smul (hX'.clm_apply continuous_const)).integrable_of_hasCompactSupport hφc.smul_right
  have i3 : Integrable (fun y => φ y • X y) :=
    (hφs.continuous.smul hX.continuous).integrable_of_hasCompactSupport hφc.smul_right
  have h := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable i1 i2 i3 (fun x _ => hφd x)
    (fun x _ => hXd x)
  rw [h, neg_neg]

theorem secondOrderTestApprox_of (hB : GradientSecondApproxStatement) : SecondOrderTestApproxStatement := by
  intro m v G H hv
  obtain ⟨u, hut, hGi, hGt, hHi, hHt⟩ := hB m v G H hv
  have hvl : LocallyIntegrable v volume := hv.velocity_six.locallyIntegrable (by norm_num)
  have hGl : ∀ j : Fin 3, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (column_memLp hv.measurable_gradient hv.gradient_two j).locallyIntegrable (by norm_num)
  have hweak : ∀ n, IsWeakGradientOf (fun y => u n y - v y) (fun y => fderiv ℝ (u n) y - G y) := by
    intro n φ hφ j
    have hu1 : ContDiff ℝ 1 (u n) := (hut n).1.of_le (by simp)
    have h1 := compactWeakGradient (u n) hu1 (hut n).2 φ hφ j
    have h2 := hv.weak_gradient φ hφ j
    have hdφ : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdφc : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := hφ.2.fderiv_apply (𝕜 := ℝ) _
    have hDu : Continuous (fun y => fderiv ℝ (u n) y (unitVector j)) :=
      (hu1.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have ia : Integrable (fun y => fderiv ℝ φ y (unitVector j) • u n y) :=
      (hdφ.smul (hut n).1.continuous).integrable_of_hasCompactSupport (hdφc.smul_right)
    have ib : Integrable (fun y => fderiv ℝ φ y (unitVector j) • v y) :=
      hvl.integrable_smul_left_of_hasCompactSupport hdφ hdφc
    have ic : Integrable (fun y => φ y • fderiv ℝ (u n) y (unitVector j)) :=
      (hφ.1.continuous.smul hDu).integrable_of_hasCompactSupport (hφ.2.smul_right)
    have id : Integrable (fun y => φ y • G y (unitVector j)) :=
      (hGl j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have e1 : (fun y => fderiv ℝ φ y (unitVector j) • (u n y - v y)) =
        fun y => fderiv ℝ φ y (unitVector j) • u n y - fderiv ℝ φ y (unitVector j) • v y := by
      ext y
      rw [smul_sub]
    have e2 : (fun y => φ y • (fderiv ℝ (u n) y - G y) (unitVector j)) =
        fun y => φ y • fderiv ℝ (u n) y (unitVector j) - φ y • G y (unitVector j) := by
      ext y
      rw [ContinuousLinearMap.sub_apply, smul_sub]
    rw [e1, e2, integral_sub ia ib, integral_sub ic id, h1, h2]
    abel
  have hIS : ∀ n, Integrable (fun y => ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2) ∧
      ∫ y, ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2 ≤ 4 * ∫ y, entrySq (fderiv ℝ (u n) y - G y) := by
    intro n
    have hm : AEStronglyMeasurable (fun y => u n y - v y) volume :=
      (hut n).1.continuous.aestronglyMeasurable.sub hv.measurable_velocity
    have h6 : MemLp (fun y => u n y - v y) 6 volume :=
      ((hut n).1.continuous.memLp_of_hasCompactSupport (hut n).2).sub hv.velocity_six
    exact inverseSquareBound _ _ hm h6 (hGi n) (hweak n)
  refine ⟨u, hut, hGi, hGt, hHi, hHt, fun n => (hIS n).1, ?_⟩
  have h4 : Tendsto (fun n => 4 * ∫ y, entrySq (fderiv ℝ (u n) y - G y)) atTop (𝓝 0) := by
    simpa using hGt.const_mul 4
  exact squeeze_zero (fun n => integral_nonneg fun y => by positivity) (fun n => (hIS n).2) h4

theorem secondOrderTestApprox : SecondOrderTestApproxStatement :=
  secondOrderTestApprox_of gradientSecondApprox

theorem driftPairing_of (hA : SecondOrderTestApproxStatement) : DriftPairingStatement := by
  intro α a m v G H hv ζ Dζ Hζ hreg
  obtain ⟨hζ2, -, hζw, hDm, hDw, hDi, hD4, -, -, -⟩ := hreg
  obtain ⟨u, hut, hGi, hGt, -, -, hVi, hVt⟩ := hA m v G H hv
  have hD2 := column_memLp hDm hDi
  have hζm := hζ2.1
  have hJζ : MemLp (fun y => axialTurn (ζ y)) 2 volume := by
    have := turnL.comp_memLp' hζ2
    simpa only [Function.comp_def, turnL_apply] using this
  have hAm : AEStronglyMeasurable (fun y => driftAdjointField α a ζ Dζ y) volume := by
    have m1 : AEStronglyMeasurable (fun y => Dζ y y) volume := apply_meas hDm aestronglyMeasurable_id
    have m2 : AEStronglyMeasurable (fun y => Dζ y (axialTurn y)) volume :=
      apply_meas hDm turn_continuous.aestronglyMeasurable
    have m3 : AEStronglyMeasurable (fun y => axialTurn (ζ y)) volume :=
      turn_continuous.comp_aestronglyMeasurable hζm
    have m4 : AEStronglyMeasurable (fun y => Dζ y (axialTurn y) - axialTurn (ζ y)) volume := m2.sub m3
    have m5 : AEStronglyMeasurable (fun y => (1 - 4 * (1 / (2 * α))) • ζ y) volume := hζm.const_smul (1 - 4 * (1 / (2 * α)))
    have m6 : AEStronglyMeasurable (fun y => (1 / (2 * α)) • Dζ y y) volume := m1.const_smul (1 / (2 * α))
    have m7 : AEStronglyMeasurable (fun y => a • (Dζ y (axialTurn y) - axialTurn (ζ y))) volume := m4.const_smul a
    have m8 : AEStronglyMeasurable (fun y => (1 - 4 * (1 / (2 * α))) • ζ y - (1 / (2 * α)) • Dζ y y) volume :=
      m5.sub m6
    exact m8.sub m7
  have hE : MemLp (fun y => ‖y‖ • driftAdjointField α a ζ Dζ y) 2 volume := by
    have hm := measurable_norm.aestronglyMeasurable.smul hAm
    have hz2 : Integrable (fun y => ‖‖y‖ • ζ y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hζw.1).1 hζw
    refine memLp_of_sq hm (((hz2.const_mul (2 * (|1 - 4 * (1 / (2 * α))| + |a|) ^ 2)).add
      (hD4.const_mul (2 * (|1 / (2 * α)| + |a|) ^ 2))).mono' (hm.norm.pow 2)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact adj_weighted_sq α a ζ Dζ y
  have hint : Integrable (fun y => inner ℝ (v y) (driftAdjointField α a ζ Dζ y)) :=
    weighted_integrable (weighted_velocity hv) hE (hv.measurable_velocity.inner hAm)
      (fun y => abs_real_inner_le_norm _ _)
  have hWI := clm_apply_memLp_weighted hDm hD4 (ContinuousLinearMap.id ℝ Space) (fun y => le_rfl)
  have hWJ := clm_apply_memLp_weighted hDm hD4 turnL (fun y => by rw [turnL_apply]; exact turn_norm_le y)
  simp only [ContinuousLinearMap.id_apply] at hWI
  simp only [turnL_apply] at hWJ
  have hid : ∀ n, ∫ y, inner ℝ (driftField α a (u n) (fderiv ℝ (u n)) y) (ζ y) =
      ∫ y, inner ℝ (u n y) (driftAdjointField α a ζ Dζ y) := by
    intro n
    have hu := hut n
    have hu2 := test_memLp hu
    have hw := weighted_approx_memLp hv hu.1.continuous.aestronglyMeasurable (hVi n)
    have hDu : ∀ B : Space →L[ℝ] Space, MemLp (fun y => fderiv ℝ (u n) y (B y)) 2 volume := fun B => by
      refine ((test_first_continuous hu).clm_apply B.continuous).memLp_of_hasCompactSupport ?_
      exact (hu.2.fderiv (𝕜 := ℝ)).mono' fun y hy => subset_tsupport _ fun h => hy (by simp [h])
    have h1 := ibp_lin hDw hζ2 hD2 hu (ContinuousLinearMap.id ℝ Space)
    have h2 := ibp_lin hDw hζ2 hD2 hu turnL
    simp only [ContinuousLinearMap.id_apply, unit_trace] at h1
    simp only [turnL_apply, turn_trace, zero_mul, neg_zero, zero_sub] at h2
    have h3 : ∫ y, inner ℝ (axialTurn (u n y)) (ζ y) = -∫ y, inner ℝ (u n y) (axialTurn (ζ y)) := by
      rw [← integral_neg]
      congr 1
      ext y
      rw [turn_inner]
    have hJu : MemLp (fun y => axialTurn (u n y)) 2 volume := by
      have := turnL.comp_memLp' hu2
      simpa only [Function.comp_def, turnL_apply] using this
    have hDuI := hDu (ContinuousLinearMap.id ℝ Space)
    have hDuJ := hDu turnL
    simp only [ContinuousLinearMap.id_apply] at hDuI
    simp only [turnL_apply] at hDuJ
    have eL : ∀ y, inner ℝ (driftField α a (u n) (fderiv ℝ (u n)) y) (ζ y) =
        (1 - 1 / (2 * α)) * inner ℝ (u n y) (ζ y) + (1 / (2 * α)) * inner ℝ (fderiv ℝ (u n) y y) (ζ y) +
          a * (inner ℝ (fderiv ℝ (u n) y (axialTurn y)) (ζ y) - inner ℝ (axialTurn (u n y)) (ζ y)) := by
      intro y
      simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left]
    have eR : ∀ y, inner ℝ (u n y) (driftAdjointField α a ζ Dζ y) =
        (1 - 4 * (1 / (2 * α))) * inner ℝ (u n y) (ζ y) + (-(1 / (2 * α))) * inner ℝ (u n y) (Dζ y y) +
          (-a) * (inner ℝ (u n y) (Dζ y (axialTurn y)) - inner ℝ (u n y) (axialTurn (ζ y))) := by
      intro y
      simp only [driftAdjointField, inner_add_right, inner_sub_right, real_inner_smul_right]
      ring
    have i0 := inner_integrable hu2 hζ2
    have i1 := inner_integrable hDuI hζ2
    have i2 := inner_integrable hDuJ hζ2
    have i3 := inner_integrable hJu hζ2
    have iR1 : Integrable (fun y => inner ℝ (u n y) (Dζ y y)) :=
      weighted_integrable hw hWI (hu2.1.inner (apply_meas hDm aestronglyMeasurable_id))
        (fun y => abs_real_inner_le_norm _ _)
    have iR2 : Integrable (fun y => inner ℝ (u n y) (Dζ y (axialTurn y))) :=
      weighted_integrable hw hWJ (hu2.1.inner (apply_meas hDm turn_continuous.aestronglyMeasurable))
        (fun y => abs_real_inner_le_norm _ _)
    have iR3 := inner_integrable hu2 hJζ
    rw [integral_congr_ae (Filter.Eventually.of_forall eL), integral_congr_ae (Filter.Eventually.of_forall eR),
      integral_lin4 i0 i1 i2 i3, integral_lin4 i0 iR1 iR2 iR3]
    linear_combination (1 / (2 * α)) * h1 + a * h2 - a * h3
  set c1 := |1 - 1 / (2 * α)| + |a|
  set c2 := |1 / (2 * α)| + |a|
  have hGm := hv.measurable_gradient
  have hvm := hv.measurable_velocity
  have hdm : ∀ (w : Space → Space) (K : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable w volume →
      AEStronglyMeasurable K volume → AEStronglyMeasurable (fun y => ‖y‖⁻¹ • driftField α a w K y) volume := by
    intro w K hw hK
    refine (measurable_norm.inv).aestronglyMeasurable.smul ?_
    have m1 : AEStronglyMeasurable (fun y => K y y) volume := apply_meas hK aestronglyMeasurable_id
    have m2 : AEStronglyMeasurable (fun y => K y (axialTurn y)) volume :=
      apply_meas hK turn_continuous.aestronglyMeasurable
    have m3 : AEStronglyMeasurable (fun y => axialTurn (w y)) volume :=
      turn_continuous.comp_aestronglyMeasurable hw
    have m4 : AEStronglyMeasurable (fun y => K y (axialTurn y) - axialTurn (w y)) volume := m2.sub m3
    have m5 : AEStronglyMeasurable (fun y => (1 - 1 / (2 * α)) • w y) volume := hw.const_smul (1 - 1 / (2 * α))
    have m6 : AEStronglyMeasurable (fun y => (1 / (2 * α)) • K y y) volume := m1.const_smul (1 / (2 * α))
    have m7 : AEStronglyMeasurable (fun y => a • (K y (axialTurn y) - axialTurn (w y))) volume := m4.const_smul a
    have m8 : AEStronglyMeasurable (fun y => (1 - 1 / (2 * α)) • w y + (1 / (2 * α)) • K y y) volume :=
      m5.add m6
    exact m8.add m7
  have hdmem : ∀ (w : Space → Space) (K : Space → (Space →L[ℝ] Space)), AEStronglyMeasurable w volume →
      AEStronglyMeasurable K volume → Integrable (fun y => ‖w y‖ ^ 2 / ‖y‖ ^ 2) →
      Integrable (fun y => entrySq (K y)) → MemLp (fun y => ‖y‖⁻¹ • driftField α a w K y) 2 volume := by
    intro w K hw hK h1 h2
    have hm := hdm w K hw hK
    refine memLp_of_sq hm (((h1.const_mul (2 * c1 ^ 2)).add (h2.const_mul (2 * c2 ^ 2))).mono' (hm.norm.pow 2)
      (Filter.Eventually.of_forall fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact drift_weighted_sq α a w K y
  have hsub : ∀ n, (fun y => ‖y‖⁻¹ • driftField α a (u n) (fderiv ℝ (u n)) y - ‖y‖⁻¹ • driftField α a v G y) =
      fun y => ‖y‖⁻¹ • driftField α a (fun y => u n y - v y) (fun y => fderiv ℝ (u n) y - G y) y := by
    intro n
    ext1 y
    rw [← smul_sub]
    congr 1
    simp only [driftField, ContinuousLinearMap.sub_apply, smul_sub, ← turnL_apply, map_sub]
    abel
  have hvi := (inverseSquareBound v G hvm hv.velocity_six hv.gradient_two hv.weak_gradient).1
  have hA0 := hdmem v G hvm hGm hvi hv.gradient_two
  have hAd : ∀ n, MemLp (fun y => ‖y‖⁻¹ • driftField α a (u n) (fderiv ℝ (u n)) y -
      ‖y‖⁻¹ • driftField α a v G y) 2 volume := by
    intro n
    rw [hsub n]
    exact hdmem _ _ ((hut n).1.continuous.aestronglyMeasurable.sub hvm)
      ((test_first_continuous (hut n)).aestronglyMeasurable.sub hGm) (hVi n) (hGi n)
  have hlim : Tendsto (fun n => ∫ y, ‖‖y‖⁻¹ • driftField α a (u n) (fderiv ℝ (u n)) y -
      ‖y‖⁻¹ • driftField α a v G y‖ ^ 2) atTop (𝓝 0) := by
    have hb : ∀ n, ∫ y, ‖‖y‖⁻¹ • driftField α a (u n) (fderiv ℝ (u n)) y - ‖y‖⁻¹ • driftField α a v G y‖ ^ 2 ≤
        ∫ y, (2 * c1 ^ 2 * (‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2) + 2 * c2 ^ 2 * entrySq (fderiv ℝ (u n) y - G y)) := by
      intro n
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => sq_nonneg _)
        (((hVi n).const_mul _).add ((hGi n).const_mul _)) (Filter.Eventually.of_forall fun y => ?_)
      have hs := congrFun (hsub n) y
      show ‖‖y‖⁻¹ • driftField α a (u n) (fderiv ℝ (u n)) y - ‖y‖⁻¹ • driftField α a v G y‖ ^ 2 ≤ _
      rw [hs]
      exact drift_weighted_sq α a _ _ y
    refine squeeze_zero (fun n => integral_nonneg fun y => sq_nonneg _) hb ?_
    have ht : Tendsto (fun n => 2 * c1 ^ 2 * (∫ y, ‖u n y - v y‖ ^ 2 / ‖y‖ ^ 2) +
        2 * c2 ^ 2 * ∫ y, entrySq (fderiv ℝ (u n) y - G y)) atTop (𝓝 0) := by
      simpa using (hVt.const_mul (2 * c1 ^ 2)).add (hGt.const_mul (2 * c2 ^ 2))
    refine ht.congr fun n => ?_
    rw [integral_add ((hVi n).const_mul _) ((hGi n).const_mul _), integral_const_mul, integral_const_mul]
  have T1 := pair_tendsto hA0 hAd hζw hlim
  have e : ∀ (w : Space → Space) (K : Space → (Space →L[ℝ] Space)),
      ∫ y, inner ℝ (‖y‖⁻¹ • driftField α a w K y) (‖y‖ • ζ y) = ∫ y, inner ℝ (driftField α a w K y) (ζ y) :=
    fun w K => integral_congr_ae (weighted_inner_ae _ ζ)
  simp only [e, hid] at T1
  have T2 := weighted_pair_tendsto hv (fun n => (hut n).1.continuous.aestronglyMeasurable) hVi hVt hE
  exact ⟨hint, tendsto_nhds_unique T1 T2⟩

theorem driftPairing : DriftPairingStatement :=
  driftPairing_of secondOrderTestApprox

theorem convectionPairing : ConvectionPairingStatement := by
  intro m v G H hv ζ Dζ Hζ hreg W DW C hW hDW hdiv hbd
  have hinv := (inverseSquareBound v G hv.measurable_velocity hv.velocity_six hv.gradient_two hv.weak_gradient).1
  obtain ⟨hint, heq⟩ := convectionPairing_eq hreg hreg.1.1 hW hDW hdiv ⟨C, hbd⟩ hv hinv
  refine ⟨hint, ?_⟩
  rw [heq]
  have hDWf : (fun z => fderiv ℝ W z) = DW := funext fun z => (hDW z).symm
  have hsp : MemLp (symProduct W DW v G) 2 volume := by
    have h := LinearSolveCore.symProduct_memLp inverseSquareBound hW (C := C) (fun y =>
      ⟨by rw [Real.rpow_neg_one]; exact (hbd y).1, by rw [← hDW y]; exact (hbd y).2⟩) hv
    rwa [hDWf] at h
  have hC0 : 0 ≤ C := by
    have h := (hbd 0).1
    rw [norm_zero, add_zero, inv_one, mul_one] at h
    exact (norm_nonneg _).trans h
  have hDy : ∀ y, ‖y‖ * ‖DW y‖ ≤ C := by
    intro y
    have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have h2 : (1 + ‖y‖) ^ (-2 : ℝ) ≤ (1 + ‖y‖)⁻¹ := by
      rw [← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    have h3 : 0 < 1 + ‖y‖ := by positivity
    calc ‖y‖ * ‖DW y‖ ≤ ‖y‖ * (C * (1 + ‖y‖)⁻¹) :=
          mul_le_mul_of_nonneg_left ((hbd y).2.trans (mul_le_mul_of_nonneg_left h2 hC0)) (norm_nonneg _)
      _ = C * (‖y‖ / (1 + ‖y‖)) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left ((div_le_one h3).2 (by linarith)) hC0
      _ = C := mul_one C
  have hqm : AEStronglyMeasurable (fun y => ‖v y‖ / ‖y‖) volume :=
    (hv.measurable_velocity.norm.aemeasurable.div measurable_norm.aemeasurable).aestronglyMeasurable
  have hq : MemLp (fun y => ‖v y‖ / ‖y‖) 2 volume :=
    (memLp_two_iff_integrable_sq hqm).2 (by simpa only [div_pow] using hinv)
  have hDWc : Continuous DW := by rw [← hDWf]; exact hW.continuous_fderiv one_ne_zero
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  have hDv : MemLp (fun y => DW y (v y)) 2 volume := by
    refine FracInternal.ConvectionPairing.memLp_of_bound (hq.const_mul C)
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
        (hDWc.aestronglyMeasurable.prodMk hv.measurable_velocity)) (hne.mono fun y hy => ?_)
    have hy' : 0 < ‖y‖ := norm_pos_iff.2 hy
    calc ‖DW y (v y)‖ ≤ ‖DW y‖ * ‖v y‖ := (DW y).le_opNorm _
      _ ≤ C * (‖v y‖ / ‖y‖) := by
        rw [mul_div_assoc', le_div_iff₀ hy']
        nlinarith [hDy y, norm_nonneg (v y), norm_nonneg (DW y)]
  have i2 : Integrable (fun y => inner ℝ (ζ y) (DW y (v y))) :=
    FracInternal.ConvectionPairing.inner_int hreg.1 hDv
  have hpt : ∀ y, inner ℝ ((2 : ℝ) • symProduct W DW v G y) (ζ y) =
      inner ℝ (ζ y) (G y (W y)) + inner ℝ (ζ y) (DW y (v y)) := by
    intro y
    simp only [symProduct, smul_smul]
    norm_num
    rw [inner_add_left, real_inner_comm (ζ y), real_inner_comm (ζ y)]
  have hsum : Integrable (fun y => inner ℝ ((2 : ℝ) • symProduct W DW v G y) (ζ y)) :=
    FracInternal.ConvectionPairing.inner_int (hsp.const_smul (2 : ℝ)) hreg.1
  have i1 : Integrable (fun y => inner ℝ (ζ y) (G y (W y))) := by
    refine (hsum.sub i2).congr (ae_of_all _ fun y => ?_)
    simp only [Pi.sub_apply, hpt]
    ring
  unfold l2Pair
  simp only [hpt]
  exact integral_add i1 i2

theorem negTracePairing_of (hA : SecondOrderTestApproxStatement) : NegTracePairingStatement := by
  intro m v G H hv X L hXL hX hLm hL
  obtain ⟨u, hut, -, -, hHi, hHt, hVi, hVt⟩ := hA m v G H hv
  have hid : ∀ n, ∫ y, inner ℝ (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ (u n)) z) y) (X y) =
      ∫ y, inner ℝ (u n y) (L y) := by
    intro n
    have h := hXL (u n) (hut n)
    simp only [ssp_eq] at h
    calc _ = ∫ y, inner ℝ (X y) (-secondTrace (fderiv ℝ (fderiv ℝ (u n)) y)) := by
          congr 1
          ext y
          rw [real_inner_comm]
          rfl
      _ = _ := by
          rw [h]
          congr 1
          ext y
          rw [real_inner_comm]
  have T1 := trace_tendsto hv.measurable_second (by exact hv.second_two)
    (K := fun n z => fderiv ℝ (fderiv ℝ (u n)) z)
    (fun n => (test_second_continuous (hut n)).aestronglyMeasurable) hHi hHt hX
  have T2 := weighted_pair_tendsto hv (fun n => (hut n).1.continuous.aestronglyMeasurable) hVi hVt hL
  simp only [hid] at T1
  exact tendsto_nhds_unique T1 T2

theorem negTracePairing : NegTracePairingStatement :=
  negTracePairing_of secondOrderTestApprox

theorem gradientTracePairing_of (hA : SecondOrderTestApproxStatement) : GradientTracePairingStatement := by
  intro m v G H hv X DX hXD hX hDm hDi
  obtain ⟨u, hut, hGi, hGt, hHi, hHt, -, -⟩ := hA m v G H hv
  have hD2 := column_memLp hDm hDi
  have hid : ∀ n, ∫ y, inner ℝ (negSecondTrace (fun z => fderiv ℝ (fderiv ℝ (u n)) z) y) (X y) =
      ∫ y, entryInner (fderiv ℝ (u n) y) (DX y) := by
    intro n
    have key : ∀ j, ∫ y, inner ℝ (fderiv ℝ (fderiv ℝ (u n)) y (unitVector j) (unitVector j)) (X y) =
        -∫ y, inner ℝ (fderiv ℝ (u n) y (unitVector j)) (DX y (unitVector j)) := by
      intro j
      rw [← weak_vec hXD hX hD2 (test_dir (hut n) (unitVector j)) j]
      congr 1
      ext y
      rw [dir_fderiv (hut n)]
    have hi : ∀ j, Integrable (fun y =>
        inner ℝ (fderiv ℝ (fderiv ℝ (u n)) y (unitVector j) (unitVector j)) (X y)) := by
      intro j
      have hm := test_memLp (test_dir (test_dir (hut n) (unitVector j)) (unitVector j))
      simp only [dir_fderiv (hut n)] at hm
      exact inner_integrable hm hX
    have hi2 : ∀ j, Integrable (fun y => inner ℝ (fderiv ℝ (u n) y (unitVector j)) (DX y (unitVector j))) :=
      fun j => inner_integrable (test_memLp (test_dir (hut n) (unitVector j))) (hD2 j)
    simp only [negSecondTrace, secondTrace, inner_neg_left, sum_inner, entryInner]
    rw [integral_neg, integral_finsetSum _ fun j _ => hi j, integral_finsetSum _ fun j _ => hi2 j]
    simp only [key, Finset.sum_neg_distrib, neg_neg]
  have T1 := trace_tendsto hv.measurable_second (by exact hv.second_two)
    (K := fun n z => fderiv ℝ (fderiv ℝ (u n)) z)
    (fun n => (test_second_continuous (hut n)).aestronglyMeasurable) hHi hHt hX
  have T2 := entry_tendsto hv.measurable_gradient hv.gradient_two (K := fun n z => fderiv ℝ (u n) z)
    (fun n => (test_first_continuous (hut n)).aestronglyMeasurable) hGi hGt hDm hDi
  simp only [hid] at T1
  exact tendsto_nhds_unique T1 T2

theorem gradientTracePairing : GradientTracePairingStatement :=
  gradientTracePairing_of secondOrderTestApprox

theorem matrixDivergencePairing_of (hA : SecondOrderTestApproxStatement) : MatrixDivergencePairingStatement := by
  intro m v G H hv Y E hYE hYm hYi hEm hE
  obtain ⟨u, hut, hGi, hGt, -, -, hVi, hVt⟩ := hA m v G H hv
  have T1 := entry_tendsto hv.measurable_gradient hv.gradient_two (K := fun n z => fderiv ℝ (u n) z)
    (fun n => (test_first_continuous (hut n)).aestronglyMeasurable) hGi hGt hYm hYi
  have T2 := (weighted_pair_tendsto hv (fun n => (hut n).1.continuous.aestronglyMeasurable) hVi hVt hE).neg
  have hid : ∀ n, ∫ y, entryInner (fderiv ℝ (u n) y) (Y y) = -∫ y, inner ℝ (u n y) (E y) := by
    intro n
    rw [hYE (u n) (hut n)]
    congr 2
    ext y
    rw [real_inner_comm]
  simp only [hid] at T1
  exact tendsto_nhds_unique T1 T2

theorem matrixDivergencePairing : MatrixDivergencePairingStatement :=
  matrixDivergencePairing_of secondOrderTestApprox

theorem scalarGradientPairing_of (hA : SecondOrderTestApproxStatement) : ScalarGradientTracePairingStatement := by
  intro m v G H hv q Q hqQ hq hQm hQ
  obtain ⟨u, hut, hGi, hGt, -, -, hVi, hVt⟩ := hA m v G H hv
  set Y : Space → (Space →L[ℝ] Space) := fun y => q y • ContinuousLinearMap.id ℝ Space with hYdef
  have hYm : AEStronglyMeasurable Y volume := hq.1.smul aestronglyMeasurable_const
  have hq2 : Integrable (fun y => ‖q y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hq.1).1 hq
  have hYi : Integrable (fun y => entrySq (Y y)) := by
    refine (hq2.const_mul 3).congr (Filter.Eventually.of_forall fun y => ?_)
    simp [Y, entrySq, unitVector, norm_smul]
  have hent : ∀ n y, entryInner (fderiv ℝ (u n) y) (Y y) =
      ∑ j : Fin 3, fderiv ℝ (u n) y (unitVector j) j * q y := by
    intro n y
    simp only [entryInner, Y, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right, inner_unit]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hzero : ∫ y, entryInner (G y) (Y y) = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hv.divergence] with y hy
    simp only [entryInner, Y, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      real_inner_smul_right, ← Finset.mul_sum, hy, mul_zero, Pi.zero_apply]
  have hid : ∀ n, ∫ y, inner ℝ (u n y) (Q y) = -∫ y, entryInner (fderiv ℝ (u n) y) (Y y) := by
    intro n
    have hw := weighted_approx_memLp hv (hut n).1.continuous.aestronglyMeasurable (hVi n)
    have hiuQ : ∀ j : Fin 3, Integrable (fun y => u n y j * Q y j) := by
      intro j
      refine weighted_integrable hw hQ ?_ fun y => ?_
      · exact (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp (hut n).1.continuous).aestronglyMeasurable).mul
          ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hQm)
      · rw [abs_mul]
        exact mul_le_mul (coord_abs_le _ _) (coord_abs_le _ _) (abs_nonneg _) (norm_nonneg _)
    have hidq : ∀ j : Fin 3, Integrable (fun y => fderiv ℝ (u n) y (unitVector j) j * q y) := by
      intro j
      have h1 : MemLp (fun y => fderiv ℝ (u n) y (unitVector j) j) 2 volume :=
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp_memLp' (test_memLp (test_dir (hut n) (unitVector j)))
      exact h1.integrable_mul hq
    have hj : ∀ j : Fin 3, ∫ y, u n y j * Q y j = -∫ y, fderiv ℝ (u n) y (unitVector j) j * q y := by
      intro j
      have h := hqQ _ (coord_test (hut n) j) j
      simp only [coord_fderiv (hut n), inner_unit] at h
      rw [h, neg_neg]
    simp only [inner_coords, hent]
    rw [integral_finsetSum _ fun j _ => hiuQ j, integral_finsetSum _ fun j _ => hidq j,
      ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun j _ => hj j
  have T1 := (entry_tendsto hv.measurable_gradient hv.gradient_two (K := fun n z => fderiv ℝ (u n) z)
    (fun n => (test_first_continuous (hut n)).aestronglyMeasurable) hGi hGt hYm hYi).neg
  have T2 := weighted_pair_tendsto hv (fun n => (hut n).1.continuous.aestronglyMeasurable) hVi hVt hQ
  simp only [← hid, hzero, neg_zero] at T1
  exact tendsto_nhds_unique T2 T1

theorem scalarGradientPairing : ScalarGradientTracePairingStatement :=
  scalarGradientPairing_of secondOrderTestApprox

theorem compactTraceWeight : CompactTraceWeightStatement := by
  intro X L hX hXc hT hLm hLb
  obtain ⟨C, hC⟩ := hLb
  have hK : IsCompact (tsupport X) := hXc
  have hKm : MeasurableSet (tsupport X) := (isClosed_tsupport X).measurableSet
  have hU : IsOpen (tsupport X)ᶜ := (isClosed_tsupport X).isOpen_compl
  have hloc : LocallyIntegrable L volume := by
    rw [locallyIntegrable_iff]
    intro S hS
    exact Measure.integrableOn_of_bounded (M := C) hS.measure_lt_top.ne hLm (ae_restrict_of_ae hC)
  have hvan : ∀ᵐ y ∂volume, y ∈ (tsupport X)ᶜ → L y = 0 := by
    refine hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hloc.locallyIntegrableOn _) ?_
    intro g hg hgc hgU
    have hcomp : ∀ i : Fin 3, ∫ y, g y * inner ℝ (L y) (unitVector i) = 0 := by
      intro i
      have htest : IsTestVectorField (fun y => g y • unitVector i) :=
        ⟨hg.smul contDiff_const, hgc.smul_right⟩
      have h1 := hT _ htest
      have h0 : (∫ y, inner ℝ (X y) (-sumSecondPartialsAt (fun y => g y • unitVector i) y)) = 0 := by
        refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
        dsimp only [Pi.zero_apply]
        by_cases hy : y ∈ tsupport g
        · rw [image_eq_zero_of_notMem_tsupport (hgU hy), inner_zero_left]
        · have hφ : y ∉ tsupport (fun y => g y • unitVector i) :=
            fun h => hy (tsupport_smul_subset_left _ _ h)
          have hz : ∀ j : Fin 3, iteratedFDeriv ℝ 2 (fun y => g y • unitVector i) y
              ![unitVector j, unitVector j] = 0 := by
            intro j
            rw [image_eq_zero_of_notMem_tsupport
              (fun h => hφ (tsupport_iteratedFDeriv_subset 2 h))]
            rfl
          simp [sumSecondPartialsAt, hz]
      rw [h0] at h1
      rw [h1]
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      simp only [real_inner_smul_right]
    have hint : Integrable (fun y => g y • L y) := by
      obtain ⟨R, hR⟩ : ∃ R, ∀ y, ‖g y‖ ≤ R := hg.continuous.bounded_above_of_compact_support hgc
      have hgi : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
      refine Integrable.mono' (hgi.norm.mul_const C) (hg.continuous.aestronglyMeasurable.smul hLm) ?_
      filter_upwards [hC] with y hy
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    ext i
    have hi := hcomp i
    have e1 : (∫ y, g y • L y) i = inner ℝ (∫ y, g y • L y) (unitVector i) := by
      simp [unitVector, EuclideanSpace.inner_single_right]
    have e2 : ∫ y, inner ℝ (unitVector i) (g y • L y) = ∫ y, g y * inner ℝ (L y) (unitVector i) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => by
        simp only [real_inner_smul_right, real_inner_comm])
    rw [e1, real_inner_comm, ← integral_inner hint, e2, hi]
    simp
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
  have hfin : IsFiniteMeasure (volume.restrict (tsupport X)) :=
    isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hm : MemLp ((tsupport X).indicator (fun y => ‖y‖ • L y)) 2 volume := by
    rw [memLp_indicator_iff_restrict hKm]
    refine MemLp.of_bound (measurable_norm.aestronglyMeasurable.smul hLm).restrict (R * C) ?_
    filter_upwards [ae_restrict_mem hKm, ae_restrict_of_ae hC] with y hy hy2
    rw [norm_smul, norm_norm]
    have hyR : ‖y‖ ≤ R := by simpa using hR hy
    exact mul_le_mul hyR hy2 (norm_nonneg _) ((norm_nonneg _).trans hyR)
  refine hm.ae_eq ?_
  filter_upwards [hvan] with y hy
  by_cases hyK : y ∈ tsupport X
  · rw [Set.indicator_of_mem hyK]
  · rw [Set.indicator_of_notMem hyK, hy hyK, smul_zero]

end Reduction

end CellCert

end Breakdown

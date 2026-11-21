import Breakdown.Torus.StatementsForce
import Breakdown.Torus.StatementsSteps
import Breakdown.Torus.StatementsApprox
import Breakdown.Torus.TorusSeries
import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

abbrev ShellData := (Fin 3 → Freq.L2R) × Freq.L6R

def wrap (x : Space) : Space := x - ∑ i, (round (x i - center i) : ℝ) • unitVector i

def simCoord (μ : ℝ) (x : Space) : Space := (Real.sqrt μ)⁻¹ • (wrap x - center)

def transplantField (μ : ℝ) (φ : Space → Space) (x : Space) : Space :=
  (Real.sqrt μ)⁻¹ • φ (simCoord μ x)

def IsShellScale (μ b : ℝ) : Prop := 0 < μ ∧ μ ≤ 1 ∧ 0 < b ∧ Real.sqrt μ * b ≤ 1 / 8

namespace ShellDefs.Internal

theorem toLpOrZero_eq {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f : Space → F}
    (h : MemLp f p volume) : Freq.toLpOrZero p f = h.toLp f := by
  unfold Freq.toLpOrZero
  rw [dif_pos h]

theorem toLpOrZero_add {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} {f g k : Space → F}
    (hf : MemLp f p volume) (hg : MemLp g p volume) (hk : k =ᵐ[volume] f + g) :
    Freq.toLpOrZero p k = Freq.toLpOrZero p f + Freq.toLpOrZero p g := by
  have hk' : MemLp k p volume := (hf.add hg).ae_eq hk.symm
  rw [toLpOrZero_eq hk', toLpOrZero_eq hf, toLpOrZero_eq hg, ← MemLp.toLp_add]
  exact MemLp.toLp_congr hk' (hf.add hg) hk

theorem toLpOrZero_smul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞}
    {f k : Space → F} (r : ℝ) (hf : MemLp f p volume) (hk : k =ᵐ[volume] r • f) :
    Freq.toLpOrZero p k = r • Freq.toLpOrZero p f := by
  have hk' : MemLp k p volume := (hf.const_smul r).ae_eq hk.symm
  rw [toLpOrZero_eq hk', toLpOrZero_eq hf, ← MemLp.toLp_const_smul]
  exact MemLp.toLp_congr hk' (hf.const_smul r) hk

theorem norm_toLpOrZero_le {F : Type*} [NormedAddCommGroup F] {p : ℝ≥0∞} [Fact (1 ≤ p)]
    {f : Space → F} {B : ℝ≥0∞} (hB : B ≠ ⊤) (h : eLpNorm f p volume ≤ B) :
    ‖Freq.toLpOrZero p f‖ ≤ B.toReal := by
  unfold Freq.toLpOrZero
  split_ifs with hf
  · rw [Lp.norm_toLp]
    exact ENNReal.toReal_mono hB h
  · simp

theorem memLp_cut {p : ℝ≥0∞} (b : ℝ) (f : Lp (α := Space) Space p) :
    MemLp ((Metric.closedBall (0 : Space) b).indicator f) p volume :=
  (Lp.memLp f).indicator measurableSet_closedBall

theorem cut_add {p : ℝ≥0∞} (b : ℝ) (f g : Lp Space p (volume : Measure Space)) :
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (⇑(f + g) : Space → Space)) =
      Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f) +
        Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator g) := by
  classical
  refine toLpOrZero_add (memLp_cut b f) (memLp_cut b g) ?_
  filter_upwards [Lp.coeFn_add f g] with x hx
  rw [Pi.add_apply, Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · exact hx
  · simp

theorem cut_smul {p : ℝ≥0∞} (b r : ℝ) (f : Lp Space p (volume : Measure Space)) :
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator (⇑(r • f) : Space → Space)) =
      r • Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f) := by
  classical
  refine toLpOrZero_smul r (memLp_cut b f) ?_
  filter_upwards [Lp.coeFn_smul r f] with x hx
  rw [Pi.smul_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · exact hx
  · simp

theorem cut_norm_le {p : ℝ≥0∞} [Fact (1 ≤ p)] (b : ℝ) (f : Lp Space p (volume : Measure Space)) :
    ‖Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f)‖ ≤ 1 * ‖f‖ := by
  rw [one_mul, Lp.norm_def f]
  exact norm_toLpOrZero_le (Lp.eLpNorm_ne_top f) (eLpNorm_indicator_le _)

end ShellDefs.Internal

open ShellDefs.Internal in
def cutLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (b : ℝ) :
    Lp (α := Space) Space p →L[ℝ] Lp (α := Space) Space p :=
  LinearMap.mkContinuous
    { toFun := fun f => Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator f)
      map_add' := cut_add b
      map_smul' := cut_smul b } 1 (cut_norm_le b)

theorem cutLp_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (b : ℝ) (f : Lp (α := Space) Space p) :
    (cutLp p b f : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator f := by
  simp only [cutLp, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  rw [ShellDefs.Internal.toLpOrZero_eq (ShellDefs.Internal.memLp_cut b f)]
  exact MemLp.coeFn_toLp _

def restrictR3 (b : ℝ) : Freq.X →L[ℝ] ShellData :=
  ContinuousLinearMap.prod (ContinuousLinearMap.pi fun j => (cutLp 2 b).comp (Freq.partialX j))
    ((cutLp 6 b).comp Freq.velocity)

namespace ShellDefs.Internal

def shellMap (μ : ℝ) (y : Space) : Space := center + Real.sqrt μ • y

theorem measurableSet_cell : MeasurableSet cell :=
  FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet

theorem continuous_shellMap (μ : ℝ) : Continuous (shellMap μ) :=
  continuous_const.add (continuous_const_smul _)

theorem qmp_shellMap {μ : ℝ} (hμ : 0 < μ) :
    Measure.QuasiMeasurePreserving (shellMap μ) volume volume :=
  (measurePreserving_add_left volume center).quasiMeasurePreserving.comp
    (Measure.quasiMeasurePreserving_smul volume (Real.sqrt_pos.2 hμ).ne')

theorem center_apply (i : Fin 3) : center i = 1 / 2 := by
  simp [center, unitVector, Pi.single_apply]

theorem shellMap_mem {μ b : ℝ} (h : IsShellScale μ b) {y : Space}
    (hy : y ∈ Metric.closedBall (0 : Space) b) : shellMap μ y ∈ cell := by
  intro i
  have hyi : |y i| ≤ b := by
    have h1 := PiLp.norm_apply_le y i
    rw [mem_closedBall_zero_iff] at hy
    rw [← Real.norm_eq_abs]
    exact h1.trans hy
  have hs := Real.sqrt_nonneg μ
  have h2 : |Real.sqrt μ * y i| ≤ 1 / 8 := by
    rw [abs_mul, abs_of_nonneg hs]
    exact (mul_le_mul_of_nonneg_left hyi hs).trans h.2.2.2
  have e : (shellMap μ y) i = 1 / 2 + Real.sqrt μ * y i := by
    simp [shellMap, center_apply]
  rw [e]
  constructor <;> linarith [abs_le.1 h2]

theorem ae_shellMap {μ b : ℝ} (h : IsShellScale μ b) {P : Space → Prop}
    (hP : ∀ᵐ x ∂(volume.restrict cell), P x) :
    ∀ᵐ y ∂volume, y ∈ Metric.closedBall (0 : Space) b → P (shellMap μ y) := by
  rw [ae_restrict_iff' measurableSet_cell] at hP
  filter_upwards [(qmp_shellMap h.1).ae hP] with y hy hb
  exact hy (shellMap_mem h hb)

theorem scale_eq {μ : ℝ} (hμ : 0 < μ) :
    |(Real.sqrt μ ^ Module.finrank ℝ Space)⁻¹| = μ ^ (-(3 / 2 : ℝ)) := by
  rw [finrank_euclideanSpace_fin, abs_of_pos (by positivity), Real.sqrt_eq_rpow, ← Real.rpow_natCast,
    ← Real.rpow_mul hμ.le, Real.rpow_neg hμ.le]
  norm_num

theorem map_shellMap_le {μ b : ℝ} (h : IsShellScale μ b) :
    Measure.map (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b)) ≤
      ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) • volume.restrict cell := by
  have hs : Real.sqrt μ ≠ 0 := (Real.sqrt_pos.2 h.1).ne'
  have hmeas : Measurable (shellMap μ) := (continuous_shellMap μ).measurable
  have e1 : Measure.map (shellMap μ) volume = ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) • volume := by
    have e : shellMap μ = (fun x => center + x) ∘ (fun y => Real.sqrt μ • y) := rfl
    rw [e, ← Measure.map_map (measurable_const_add center) (measurable_const_smul _),
      Measure.map_addHaar_smul volume hs, Measure.map_smul, map_add_left_eq_self, scale_eq h.1]
  calc Measure.map (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b))
      ≤ Measure.map (shellMap μ) (volume.restrict (shellMap μ ⁻¹' cell)) :=
        Measure.map_mono (Measure.restrict_mono (fun y hy => shellMap_mem h hy) le_rfl) hmeas
    _ = (Measure.map (shellMap μ) volume).restrict cell :=
        (Measure.restrict_map hmeas measurableSet_cell).symm
    _ = _ := by rw [e1, Measure.restrict_smul]

theorem norm_realVec_le (v : Coef) : ‖Freq.realVec v‖ ≤ ‖v‖ := by
  have e : Freq.realVec v = WithLp.toLp 2 (fun i => (v i).re) := rfl
  rw [e, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [PiLp.toLp_apply, Real.norm_eq_abs]
  exact Complex.abs_re_le_norm _

theorem eLpNorm_shell_le (p : ℝ≥0∞) (hp : p ≠ ⊤) {μ b : ℝ} (h : IsShellScale μ b) {g : Space → Coef}
    (hg : AEStronglyMeasurable g (volume.restrict cell)) (k : ℝ) :
    AEStronglyMeasurable (fun y => k • Freq.realVec (g (center + Real.sqrt μ • y)))
        (volume.restrict (Metric.closedBall (0 : Space) b)) ∧
    eLpNorm (fun y => k • Freq.realVec (g (center + Real.sqrt μ • y))) p
        (volume.restrict (Metric.closedBall (0 : Space) b)) ≤
      ‖k‖ₑ * ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) ^ (1 / p).toReal * eLpNorm g p (volume.restrict cell) := by
  have hle := map_shellMap_le h
  have hT : AEMeasurable (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b)) :=
    (continuous_shellMap μ).measurable.aemeasurable
  have hgm : AEStronglyMeasurable g
      (Measure.map (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b))) :=
    (hg.smul_measure _).mono_measure hle
  have hc : AEStronglyMeasurable (g ∘ shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b)) :=
    hgm.comp_aemeasurable hT
  refine ⟨(Freq.realVec.continuous.comp_aestronglyMeasurable hc).const_smul k, ?_⟩
  refine (eLpNorm_const_smul_le (c := k)
    (f := fun y => Freq.realVec (g (center + Real.sqrt μ • y)))).trans ?_
  rw [mul_assoc]
  gcongr
  calc eLpNorm (fun y => Freq.realVec (g (center + Real.sqrt μ • y))) p
        (volume.restrict (Metric.closedBall (0 : Space) b))
      ≤ eLpNorm (g ∘ shellMap μ) p (volume.restrict (Metric.closedBall (0 : Space) b)) :=
        eLpNorm_mono fun y => norm_realVec_le _
    _ = eLpNorm g p (Measure.map (shellMap μ) (volume.restrict (Metric.closedBall (0 : Space) b))) :=
        (eLpNorm_map_measure hgm hT).symm
    _ ≤ eLpNorm g p (ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) • volume.restrict cell) :=
        eLpNorm_mono_measure _ hle
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_top hp, smul_eq_mul]

theorem scale_cancel {μ : ℝ} (hμ : 0 < μ) {a q : ℝ} (hq : 0 ≤ q) (ha : a = 3 / 2 * q) :
    ‖μ ^ a‖ₑ * ENNReal.ofReal (μ ^ (-(3 / 2 : ℝ))) ^ q = 1 := by
  rw [Real.enorm_of_nonneg (Real.rpow_nonneg hμ.le _),
    ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hμ.le _) hq,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hμ.le _), ← Real.rpow_mul hμ.le, ← Real.rpow_add hμ, ha,
    show 3 / 2 * q + -(3 / 2) * q = 0 by ring, Real.rpow_zero, ENNReal.ofReal_one]

theorem norm_shell_le (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) {μ b a : ℝ} (h : IsShellScale μ b)
    (ha : a = 3 / 2 * (1 / p).toReal) (g : Lp Coef p (volume.restrict cell)) :
    MemLp ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y)))) p volume ∧
    ‖Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y))))‖ ≤ ‖g‖ := by
  obtain ⟨hm, hn⟩ := eLpNorm_shell_le p hp h (Lp.aestronglyMeasurable g) (μ ^ a)
  rw [scale_cancel h.1 ENNReal.toReal_nonneg ha, one_mul] at hn
  have hmem : MemLp ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y)))) p volume :=
    (memLp_indicator_iff_restrict measurableSet_closedBall).2 ⟨hm, hn.trans_lt (Lp.eLpNorm_lt_top g)⟩
  refine ⟨hmem, ?_⟩
  rw [Lp.norm_def g]
  refine norm_toLpOrZero_le (Lp.eLpNorm_ne_top g) ?_
  rw [eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  exact hn

theorem shell_add (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) {μ b a : ℝ} (h : IsShellScale μ b)
    (ha : a = 3 / 2 * (1 / p).toReal) (g g' : Lp Coef p (volume.restrict cell)) :
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec ((g + g' : Lp Coef p (volume.restrict cell)) (center + Real.sqrt μ • y)))) =
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y)))) +
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g' (center + Real.sqrt μ • y)))) := by
  classical
  refine toLpOrZero_add (norm_shell_le p hp h ha g).1 (norm_shell_le p hp h ha g').1 ?_
  filter_upwards [ae_shellMap h (Lp.coeFn_add g g')] with y hy
  rw [Pi.add_apply, Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs with hb
  · have e := hy hb
    simp only [shellMap, Pi.add_apply] at e
    rw [e, map_add, smul_add]
  · simp

theorem shell_smul (p : ℝ≥0∞) [Fact (1 ≤ p)] (hp : p ≠ ⊤) {μ b a : ℝ} (h : IsShellScale μ b)
    (ha : a = 3 / 2 * (1 / p).toReal) (r : ℝ) (g : Lp Coef p (volume.restrict cell)) :
    Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec ((r • g : Lp Coef p (volume.restrict cell)) (center + Real.sqrt μ • y)))) =
    r • Freq.toLpOrZero p ((Metric.closedBall (0 : Space) b).indicator
      (fun y => μ ^ a • Freq.realVec (g (center + Real.sqrt μ • y)))) := by
  classical
  refine toLpOrZero_smul r (norm_shell_le p hp h ha g).1 ?_
  filter_upwards [ae_shellMap h (Lp.coeFn_smul r g)] with y hy
  rw [Pi.smul_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs with hb
  · have e := hy hb
    simp only [shellMap, Pi.smul_apply] at e
    rw [e, map_smul, smul_comm]
  · simp

theorem exp_two : (3 / 4 : ℝ) = 3 / 2 * (1 / (2 : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num

theorem exp_six : (1 / 4 : ℝ) = 3 / 2 * (1 / (6 : ℝ≥0∞)).toReal := by
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  norm_num

theorem summable_weight_coeff (z : V) : Summable fun k => weight k * ‖coeff z k‖ ^ 2 := by
  refine (Breakdown.Periodic.Internal.summable_sq (z : Seq)).congr fun k => ?_
  unfold coeff
  rw [norm_smul, mul_pow, norm_inv, Real.norm_eq_abs,
    abs_of_pos (Breakdown.Periodic.Internal.sqrt_weight_pos k), inv_pow,
    Real.sq_sqrt (Breakdown.Periodic.Internal.weight_pos k).le, ← mul_assoc,
    mul_inv_cancel₀ (Breakdown.Periodic.Internal.weight_pos k).ne', one_mul]

theorem norm_gradCoef_sq_le (j : Fin 3) (z : V) (k : Lattice) :
    ‖gradCoef j z k‖ ^ 2 ≤ weight k * ‖coeff z k‖ ^ 2 := by
  unfold gradCoef
  rw [norm_smul, mul_pow]
  have h1 : ‖(2 * π * Complex.I * (k j : ℂ))‖ ^ 2 = 4 * π ^ 2 * ((k j : ℝ)) ^ 2 := by
    simp only [norm_mul, Complex.norm_I, Complex.norm_intCast, Complex.norm_real, Complex.norm_ofNat,
      Real.norm_eq_abs, abs_of_pos pi_pos, mul_one]
    rw [mul_pow, mul_pow, sq_abs]
    ring
  have h2 : ((k j : ℝ)) ^ 2 ≤ ‖freq k‖ ^ 2 := by
    rw [Breakdown.Periodic.Internal.norm_freq_sq]
    exact Finset.single_le_sum (f := fun i => ((k i : ℝ)) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ j)
  have h3 : ‖(2 * π * Complex.I * (k j : ℂ))‖ ^ 2 ≤ weight k := by
    rw [h1]
    unfold weight
    nlinarith [pi_pos]
  exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)

theorem norm_grad_le (j : Fin 3) (z : V) : ‖torusSeries 2 (gradCoef j z)‖ ≤ ‖z‖ := by
  have hs : Summable fun k => ‖gradCoef j z k‖ ^ 2 :=
    (summable_weight_coeff z).of_nonneg_of_le (fun k => sq_nonneg _) (norm_gradCoef_sq_le j z)
  refine (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 ?_
  rw [torusSeries_norm_sq _ hs, norm_sq_eq_tsum]
  exact Summable.tsum_le_tsum (norm_gradCoef_sq_le j z) hs (summable_weight_coeff z)

theorem coeff_add' (z w : V) : coeff (z + w) = coeff z + coeff w := by
  funext k
  simp only [coeff, Pi.add_apply, Submodule.coe_add, lp.coeFn_add, smul_add]

theorem coeff_smul' (r : ℝ) (z : V) : coeff (r • z) = r • coeff z := by
  funext k
  simp only [coeff, Pi.smul_apply, Submodule.coe_smul, lp.coeFn_smul]
  exact smul_comm _ _ _

theorem gradCoef_add' (j : Fin 3) (z w : V) : gradCoef j (z + w) = gradCoef j z + gradCoef j w := by
  funext k
  simp only [gradCoef, coeff_add', Pi.add_apply, smul_add]

theorem gradCoef_smul' (j : Fin 3) (r : ℝ) (z : V) : gradCoef j (r • z) = r • gradCoef j z := by
  funext k
  simp only [gradCoef, coeff_smul', Pi.smul_apply]
  exact smul_comm _ _ _

end ShellDefs.Internal

open Classical in
def restrictTorusFun (μ b : ℝ) (z : V) : ShellData :=
  if IsShellScale μ b then
    (fun j => Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y)))),
      Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y)))))
  else 0

open ShellDefs.Internal in
theorem restrictTorusFun_bound : ∃ C : ℝ, 0 ≤ C ∧ ∀ μ b z, ‖restrictTorusFun μ b z‖ ≤ C * ‖z‖ := by
  obtain ⟨C6, hC6, h6⟩ := torusSeries_six_bound
  refine ⟨max 1 C6, le_max_of_le_left zero_le_one, fun μ b z => ?_⟩
  unfold restrictTorusFun
  split_ifs with h
  · rw [Prod.norm_def]
    refine max_le ?_ ?_
    · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
      refine ((norm_shell_le 2 (by norm_num) h exp_two _).2).trans ?_
      exact (norm_grad_le j z).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _))
    · refine ((norm_shell_le 6 (by norm_num) h exp_six _).2).trans ?_
      exact (h6 z).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rw [norm_zero]
    positivity

open ShellDefs.Internal in
theorem ShellDefs.Internal.restrictTorusFun_add (μ b : ℝ) (z w : V) :
    restrictTorusFun μ b (z + w) = restrictTorusFun μ b z + restrictTorusFun μ b w := by
  unfold restrictTorusFun
  split_ifs with h
  · refine Prod.ext ?_ ?_
    · funext j
      simp only [Prod.fst_add, Pi.add_apply]
      rw [gradCoef_add', torusSeries_add 2 _ _ (summable_torusSeries_grad j z) (summable_torusSeries_grad j w)]
      exact shell_add 2 (by norm_num) h exp_two _ _
    · simp only [Prod.snd_add]
      rw [coeff_add', torusSeries_add 6 _ _ (summable_torusSeries 6 (Or.inr rfl) z)
        (summable_torusSeries 6 (Or.inr rfl) w)]
      exact shell_add 6 (by norm_num) h exp_six _ _
  · simp

open ShellDefs.Internal in
theorem ShellDefs.Internal.restrictTorusFun_smul (μ b r : ℝ) (z : V) :
    restrictTorusFun μ b (r • z) = r • restrictTorusFun μ b z := by
  unfold restrictTorusFun
  split_ifs with h
  · refine Prod.ext ?_ ?_
    · funext j
      simp only [Prod.smul_fst, Pi.smul_apply]
      rw [gradCoef_smul', torusSeries_smul]
      exact shell_smul 2 (by norm_num) h exp_two r _
    · simp only [Prod.smul_snd]
      rw [coeff_smul', torusSeries_smul]
      exact shell_smul 6 (by norm_num) h exp_six r _
  · simp

def restrictTorus (μ b : ℝ) : V →L[ℝ] ShellData :=
  LinearMap.mkContinuous
    { toFun := restrictTorusFun μ b
      map_add' := ShellDefs.Internal.restrictTorusFun_add μ b
      map_smul' := ShellDefs.Internal.restrictTorusFun_smul μ b } restrictTorusFun_bound.choose
    (fun z => restrictTorusFun_bound.choose_spec.2 μ b z)

namespace ShellDefs.Internal

def advIntegrand (φ : Space → Space) (ζ : ShellData) (y : Space) : Space :=
  ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y + (ζ.2 : Space → Space) y j • Freq.partialField φ j y)

def advK (M0 M1 b : ℝ) : ℝ≥0∞ :=
  3 * (ENNReal.ofReal M0 + ENNReal.ofReal M1 *
    volume (Metric.closedBall (0 : Space) b) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal))

theorem advK_ne_top (M0 M1 b : ℝ) : advK M0 M1 b ≠ ⊤ := by
  have he : 0 ≤ 1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_ofNat, ENNReal.toReal_ofNat]
    norm_num
  unfold advK
  refine ENNReal.mul_ne_top (by norm_num) (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top,
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.rpow_ne_top_of_nonneg he measure_closedBall_lt_top.ne)⟩)

theorem enorm_le_of_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F] {a : E} {c : F}
    (h : ‖a‖ ≤ ‖c‖) : ‖a‖ₑ ≤ ‖c‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal h

theorem test_bounds {φ : Space → Space} (hφ : IsTestField φ) :
    ∃ M0 M1 : ℝ, 0 ≤ M0 ∧ 0 ≤ M1 ∧ (∀ y, ‖φ y‖ ≤ M0) ∧ ∀ j y, ‖Freq.partialField φ j y‖ ≤ M1 := by
  obtain ⟨M0, h0⟩ := hφ.1.continuous.bounded_above_of_compact_support hφ.2.1
  have hd : Continuous (fderiv ℝ φ) := (FreqTrSeries.Internal.contDiff_one hφ.1).continuous_fderiv one_ne_zero
  obtain ⟨M1, h1⟩ := hd.bounded_above_of_compact_support (hφ.2.1.fderiv (𝕜 := ℝ))
  refine ⟨max M0 0, max M1 0, le_max_right _ _, le_max_right _ _,
    fun y => (h0 y).trans (le_max_left _ _), fun j y => ?_⟩
  refine ((fderiv ℝ φ y).le_opNorm _).trans ?_
  rw [show ‖unitVector j‖ = 1 by simp [unitVector], mul_one]
  exact (h1 y).trans (le_max_left _ _)

theorem continuous_partialField {φ : Space → Space} (hφ : IsTestField φ) (j : Fin 3) :
    Continuous (Freq.partialField φ j) :=
  ((FreqTrSeries.Internal.contDiff_one hφ.1).continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem advect_bound {φ : Space → Space} (hφ : IsTestField φ) {M0 M1 : ℝ} (hM1 : 0 ≤ M1)
    (h0 : ∀ y, ‖φ y‖ ≤ M0) (h1 : ∀ j y, ‖Freq.partialField φ j y‖ ≤ M1) (b : ℝ) (ζ : ShellData) :
    MemLp ((Metric.closedBall (0 : Space) b).indicator (advIntegrand φ ζ)) 2 volume ∧
    eLpNorm ((Metric.closedBall (0 : Space) b).indicator (advIntegrand φ ζ)) 2 volume ≤
      advK M0 M1 b * ‖ζ‖ₑ := by
  set ν := volume.restrict (Metric.closedBall (0 : Space) b)
  have hcφ : Continuous φ := hφ.1.continuous
  have m1 : ∀ j, AEStronglyMeasurable (fun y => φ y j • (ζ.1 j : Space → Space) y) ν := fun j =>
    ((((PiLp.continuous_apply 2 _ j).comp hcφ).aestronglyMeasurable).smul
      (Lp.aestronglyMeasurable (ζ.1 j))).mono_measure Measure.restrict_le_self
  have m2 : ∀ j, AEStronglyMeasurable
      (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y) ν := fun j =>
    (((PiLp.continuous_apply 2 _ j).comp_aestronglyMeasurable (Lp.aestronglyMeasurable ζ.2)).smul
      (continuous_partialField hφ j).aestronglyMeasurable).mono_measure Measure.restrict_le_self
  have hz1 : ∀ j, ‖ζ.1 j‖ₑ ≤ ‖ζ‖ₑ := fun j =>
    enorm_le_of_norm_le ((norm_le_pi_norm ζ.1 j).trans (norm_fst_le ζ))
  have hz2 : ‖ζ.2‖ₑ ≤ ‖ζ‖ₑ := enorm_le_of_norm_le (norm_snd_le ζ)
  have b1 : ∀ j, eLpNorm (fun y => φ y j • (ζ.1 j : Space → Space) y) 2 ν ≤ ENNReal.ofReal M0 * ‖ζ‖ₑ := by
    intro j
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := (ζ.1 j : Space → Space)) (c := M0)
      (ae_of_all _ fun y => ?_) 2).trans ?_
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right ((PiLp.norm_apply_le (φ y) j).trans (h0 y)) (norm_nonneg _)
    · gcongr
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ((Lp.enorm_def _).symm.le.trans (hz1 j))
  have b2 : ∀ j, eLpNorm (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y) 2 ν ≤
      ENNReal.ofReal M1 * (‖ζ‖ₑ *
        volume (Metric.closedBall (0 : Space) b) ^ (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) := by
    intro j
    refine (eLpNorm_le_mul_eLpNorm_of_ae_le_mul (g := (ζ.2 : Space → Space)) (c := M1)
      (ae_of_all _ fun y => ?_) 2).trans ?_
    · rw [norm_smul, mul_comm]
      exact mul_le_mul (h1 j y) (PiLp.norm_apply_le _ j) (norm_nonneg _) hM1
    · gcongr
      have h26 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 2) (q := 6) (by norm_num)
        ((Lp.aestronglyMeasurable ζ.2).mono_measure (Measure.restrict_le_self (s := Metric.closedBall (0 : Space) b)))
      rw [Measure.restrict_apply_univ] at h26
      refine h26.trans ?_
      gcongr
      exact (eLpNorm_mono_measure _ Measure.restrict_le_self).trans ((Lp.enorm_def _).symm.le.trans hz2)
  have e : advIntegrand φ ζ = ∑ j : Fin 3, ((fun y => φ y j • (ζ.1 j : Space → Space) y) +
      (fun y => (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) := by
    funext y
    simp [advIntegrand, Finset.sum_apply]
  have hmeas : AEStronglyMeasurable (advIntegrand φ ζ) ν := by
    rw [e]
    exact Finset.aestronglyMeasurable_sum _ fun j _ => (m1 j).add (m2 j)
  have hmain : eLpNorm (advIntegrand φ ζ) 2 ν ≤ advK M0 M1 b * ‖ζ‖ₑ := by
    rw [e]
    refine (eLpNorm_sum_le (fun j _ => (m1 j).add (m2 j)) (by norm_num)).trans ?_
    refine (Finset.sum_le_sum fun j _ =>
      (eLpNorm_add_le (m1 j) (m2 j) (by norm_num)).trans (add_le_add (b1 j) (b2 j))).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, advK]
    push_cast
    ring
  rw [memLp_indicator_iff_restrict measurableSet_closedBall,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_closedBall]
  exact ⟨⟨hmeas, hmain.trans_lt (ENNReal.mul_lt_top (advK_ne_top M0 M1 b).lt_top enorm_lt_top)⟩, hmain⟩

theorem advIntegrand_add_ae (φ : Space → Space) (ζ ζ' : ShellData) :
    advIntegrand φ (ζ + ζ') =ᵐ[volume] advIntegrand φ ζ + advIntegrand φ ζ' := by
  have h1 : ∀ᵐ y ∂(volume : Measure Space), ∀ j, ((ζ + ζ').1 j : Space → Space) y =
      (ζ.1 j : Space → Space) y + (ζ'.1 j : Space → Space) y := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_add (ζ.1 j) (ζ'.1 j)] with y hy
    rw [Prod.fst_add, Pi.add_apply, hy, Pi.add_apply]
  filter_upwards [h1, Lp.coeFn_add ζ.2 ζ'.2] with y hy h2
  simp only [advIntegrand, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hy j, Prod.snd_add, h2, Pi.add_apply, PiLp.add_apply, smul_add, add_smul]
  abel

theorem advIntegrand_smul_ae (φ : Space → Space) (r : ℝ) (ζ : ShellData) :
    advIntegrand φ (r • ζ) =ᵐ[volume] r • advIntegrand φ ζ := by
  have h1 : ∀ᵐ y ∂(volume : Measure Space), ∀ j, ((r • ζ).1 j : Space → Space) y =
      r • (ζ.1 j : Space → Space) y := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul r (ζ.1 j)] with y hy
    rw [Prod.smul_fst, Pi.smul_apply, hy, Pi.smul_apply]
  filter_upwards [h1, Lp.coeFn_smul r ζ.2] with y hy h2
  simp only [advIntegrand, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hy j, Prod.smul_snd, h2, Pi.smul_apply, PiLp.smul_apply, smul_assoc, smul_add,
    smul_comm (φ y j) r]

end ShellDefs.Internal

def advectShellFun (φ : Space → Space) (b : ℝ) (ζ : ShellData) : Freq.L2R :=
  Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
    (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
      (ζ.2 : Space → Space) y j • Freq.partialField φ j y)))

open ShellDefs.Internal in
theorem advectShellFun_bound (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ, ‖advectShellFun φ b ζ‖ ≤ C * ‖ζ‖ := by
  obtain ⟨M0, M1, -, hM1, h0, h1⟩ := test_bounds hφ
  refine ⟨(advK M0 M1 b).toReal, ENNReal.toReal_nonneg, fun ζ => ?_⟩
  have h := (advect_bound hφ hM1 h0 h1 b ζ).2
  have hn := norm_toLpOrZero_le (ENNReal.mul_ne_top (advK_ne_top M0 M1 b) enorm_ne_top) h
  rw [ENNReal.toReal_mul, toReal_enorm] at hn
  exact hn

open ShellDefs.Internal in
theorem ShellDefs.Internal.advectShellFun_add (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) (ζ ζ' : ShellData) :
    advectShellFun φ b (ζ + ζ') = advectShellFun φ b ζ + advectShellFun φ b ζ' := by
  classical
  obtain ⟨M0, M1, -, hM1, h0, h1⟩ := test_bounds hφ
  refine toLpOrZero_add (advect_bound hφ hM1 h0 h1 b ζ).1 (advect_bound hφ hM1 h0 h1 b ζ').1 ?_
  filter_upwards [advIntegrand_add_ae φ ζ ζ'] with y hy
  rw [Pi.add_apply, Set.indicator_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · exact hy
  · simp

open ShellDefs.Internal in
theorem ShellDefs.Internal.advectShellFun_smul (φ : Space → Space) (hφ : IsTestField φ) (b r : ℝ) (ζ : ShellData) :
    advectShellFun φ b (r • ζ) = r • advectShellFun φ b ζ := by
  classical
  obtain ⟨M0, M1, -, hM1, h0, h1⟩ := test_bounds hφ
  refine toLpOrZero_smul r (advect_bound hφ hM1 h0 h1 b ζ).1 ?_
  filter_upwards [advIntegrand_smul_ae φ r ζ] with y hy
  rw [Pi.smul_apply, Set.indicator_apply, Set.indicator_apply]
  split_ifs
  · exact hy
  · simp

def advectShell (φ : Space → Space) (hφ : IsTestField φ) (b : ℝ) : ShellData →L[ℝ] Freq.L2R :=
  LinearMap.mkContinuous
    { toFun := advectShellFun φ b
      map_add' := ShellDefs.Internal.advectShellFun_add φ hφ b
      map_smul' := ShellDefs.Internal.advectShellFun_smul φ hφ b } (advectShellFun_bound φ hφ b).choose
    (fun ζ => (advectShellFun_bound φ hφ b).choose_spec.2 ζ)

def lambdaR3 (φ : Space → Space) (hφ : IsTestField φ) (b τ : ℝ) : ShellData →L[ℝ] Freq.X :=
  -((Freq.heatDivFree τ).comp (advectShell φ hφ b))

namespace ShellDefs.Internal

def simLin (μ : ℝ) (x : Space) : Space := (Real.sqrt μ)⁻¹ • (x - center)

def simConst (μ : ℝ) : ℝ≥0∞ := ENNReal.ofReal |((Real.sqrt μ)⁻¹ ^ Module.finrank ℝ Space)⁻¹|

def simK (μ : ℝ) : ℝ :=
  (simConst μ ^ (1 / (2 : ℝ≥0∞)).toReal).toReal *
    ((volume.restrict cell) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal

theorem simK_nonneg (μ : ℝ) : 0 ≤ simK μ := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

theorem continuous_simLin (μ : ℝ) : Continuous (simLin μ) := by
  unfold simLin
  fun_prop

theorem qmp_simLin {μ : ℝ} (hμ : 0 < μ) : Measure.QuasiMeasurePreserving (simLin μ) volume volume :=
  (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero (Real.sqrt_pos.2 hμ).ne')).comp
    (measurePreserving_sub_right volume center).quasiMeasurePreserving

theorem volume_coord_eq_one (i : Fin 3) : volume {x : Space | x i = 1} = 0 := by
  let K : Submodule ℝ Space := LinearMap.ker (EuclideanSpace.proj i : Space →L[ℝ] ℝ).toLinearMap
  have hK : K ≠ ⊤ := by
    intro h
    have h1 : unitVector i ∈ K := h ▸ Submodule.mem_top
    simp [K, unitVector] at h1
  have h0 : volume (K : Set Space) = 0 := Measure.addHaar_submodule volume K hK
  have e : {x : Space | x i = 1} = (fun x => x + -unitVector i) ⁻¹' (K : Set Space) := by
    ext x
    simp [K, unitVector, add_neg_eq_zero]
  rw [e, measure_preimage_add_right]
  exact h0

theorem simCoord_ae (μ : ℝ) : ∀ᵐ x ∂(volume.restrict cell), simCoord μ x = simLin μ x := by
  have h : ∀ᵐ x ∂(volume : Measure Space), ∀ i, x i ≠ 1 := by
    rw [ae_all_iff]
    intro i
    rw [ae_iff]
    simpa using volume_coord_eq_one i
  rw [ae_restrict_iff' measurableSet_cell]
  filter_upwards [h] with x hx hc
  have hr : ∀ i, round (x i - center i) = 0 := by
    intro i
    rw [center_apply, round_eq, sub_add_cancel, Int.floor_eq_zero_iff]
    exact ⟨(hc i).1, lt_of_le_of_ne (hc i).2 (hx i)⟩
  have hw : wrap x = x := by simp [wrap, hr]
  rw [simCoord, hw]
  rfl

theorem map_simLin_le {μ : ℝ} (hμ : 0 < μ) :
    Measure.map (simLin μ) (volume.restrict cell) ≤ simConst μ • volume := by
  have hm : Measurable (simLin μ) := (continuous_simLin μ).measurable
  have e : simLin μ = (fun y => (Real.sqrt μ)⁻¹ • y) ∘ (fun x => x - center) := rfl
  calc Measure.map (simLin μ) (volume.restrict cell) ≤ Measure.map (simLin μ) volume :=
        Measure.map_mono Measure.restrict_le_self hm
    _ = _ := by
        rw [e, ← Measure.map_map (measurable_const_smul _) (measurable_sub_const center),
          map_sub_right_eq_self, Measure.map_addHaar_smul volume (inv_ne_zero (Real.sqrt_pos.2 hμ).ne')]
        rfl

theorem eLpNorm_simCoord_le {μ : ℝ} (hμ : 0 < μ) (A : Freq.L2R) :
    AEStronglyMeasurable (fun x => (A : Space → Space) (simCoord μ x)) (volume.restrict cell) ∧
    eLpNorm (fun x => (A : Space → Space) (simCoord μ x)) 2 (volume.restrict cell) ≤
      simConst μ ^ (1 / (2 : ℝ≥0∞)).toReal * ‖A‖ₑ := by
  have hle := map_simLin_le hμ
  have hT : AEMeasurable (simLin μ) (volume.restrict cell) := (continuous_simLin μ).measurable.aemeasurable
  have hAm : AEStronglyMeasurable (A : Space → Space) (Measure.map (simLin μ) (volume.restrict cell)) :=
    ((Lp.aestronglyMeasurable A).smul_measure _).mono_measure hle
  have hae : (fun x => (A : Space → Space) (simCoord μ x)) =ᵐ[volume.restrict cell]
      (A : Space → Space) ∘ simLin μ := by
    filter_upwards [simCoord_ae μ] with x hx
    rw [Function.comp_apply, hx]
  refine ⟨(hAm.comp_aemeasurable hT).congr hae.symm, ?_⟩
  rw [eLpNorm_congr_ae hae, ← eLpNorm_map_measure hAm hT]
  calc eLpNorm (A : Space → Space) 2 (Measure.map (simLin μ) (volume.restrict cell))
      ≤ eLpNorm (A : Space → Space) 2 (simConst μ • volume) := eLpNorm_mono_measure _ hle
    _ = _ := by rw [eLpNorm_smul_measure_of_ne_top (by norm_num), smul_eq_mul, Lp.enorm_def]

theorem norm_complexify' (v : Space) : ‖complexify v‖ = ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [complexify, Complex.norm_real]

theorem finite_cell : volume cell ≠ ⊤ := FreqTrSeries.Internal.isCompact_cell.measure_lt_top.ne

theorem memLp_sim {μ : ℝ} (hμ : 0 < μ) (A : Freq.L2R) :
    MemLp (fun x => (A : Space → Space) (simCoord μ x)) 2 (volume.restrict cell) := by
  obtain ⟨hm, hn⟩ := eLpNorm_simCoord_le hμ A
  refine ⟨hm, hn.trans_lt ?_⟩
  refine ENNReal.mul_lt_top ?_ enorm_lt_top
  exact (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top)

theorem integral_simCoord_le {μ : ℝ} (hμ : 0 < μ) (A : Freq.L2R) :
    ∫ x in cell, ‖complexify ((A : Space → Space) (simCoord μ x))‖ ≤ simK μ * ‖A‖ := by
  obtain ⟨hm, hn⟩ := eLpNorm_simCoord_le hμ A
  simp only [norm_complexify']
  rw [integral_norm_eq_lintegral_enorm hm, ← eLpNorm_one_eq_lintegral_enorm]
  have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (p := 1) (q := 2) (by norm_num) hm
  have he : 0 ≤ 1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal := by
    rw [ENNReal.toReal_one, ENNReal.toReal_ofNat]
    norm_num
  have hf1 : simConst μ ^ (1 / (2 : ℝ≥0∞)).toReal ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg ENNReal.toReal_nonneg ENNReal.ofReal_ne_top
  have hf2 : (volume.restrict cell) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ := by
    refine ENNReal.rpow_ne_top_of_nonneg he ?_
    rw [Measure.restrict_apply_univ]
    exact finite_cell
  have hf : simConst μ ^ (1 / (2 : ℝ≥0∞)).toReal * ‖A‖ₑ *
      (volume.restrict cell) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top hf1 enorm_ne_top) hf2
  calc (eLpNorm (fun x => (A : Space → Space) (simCoord μ x)) 1 (volume.restrict cell)).toReal
      ≤ (simConst μ ^ (1 / (2 : ℝ≥0∞)).toReal * ‖A‖ₑ *
          (volume.restrict cell) univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)).toReal :=
        ENNReal.toReal_mono hf (h1.trans (mul_le_mul_left hn _))
    _ = simK μ * ‖A‖ := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_mul, toReal_enorm, simK]
        ring

theorem norm_forceV_le {s : ℝ} (hs : 0 < s) (F : Space → Space) :
    ‖forceV s F‖ ≤
      2 * Real.sqrt (∑' k, weight k * heatFactor s k ^ 2) * ∫ x in cell, ‖complexify (F x)‖ := by
  set I := ∫ x in cell, ‖complexify (F x)‖
  set W := ∑' k, weight k * heatFactor s k ^ 2
  have hI : 0 ≤ I := integral_nonneg fun x => norm_nonneg _
  have hW : 0 ≤ W := tsum_nonneg fun k =>
    mul_nonneg (Breakdown.Periodic.Internal.weight_pos k).le (sq_nonneg _)
  have hnorm : ‖forceV s F‖ = ‖((forceV s F : V) : Seq)‖ := rfl
  have hle : ‖((forceV s F : V) : Seq)‖ ^ 2 ≤ (2 * Real.sqrt W * I) ^ 2 := by
    rw [Breakdown.Periodic.Internal.norm_sq_seq, mul_pow, mul_pow, Real.sq_sqrt hW]
    have hb : ∀ k, ‖((forceV s F : V) : Seq) k‖ ^ 2 ≤ 4 * I ^ 2 * (weight k * heatFactor s k ^ 2) := by
      intro k
      change ‖forceSeq s F k‖ ^ 2 ≤ _
      refine (Force.Internal.sq_norm_forceSeq_le hs F k).trans ?_
      have hA : ‖freqTrCoef F k‖ ≤ I := FreqTrSeries.Internal.norm_freqTrCoef_le k
      have hw : 0 ≤ weight k * heatFactor s k ^ 2 :=
        mul_nonneg (Breakdown.Periodic.Internal.weight_pos k).le (sq_nonneg _)
      gcongr
    calc ∑' k, ‖((forceV s F : V) : Seq) k‖ ^ 2 ≤ ∑' k, 4 * I ^ 2 * (weight k * heatFactor s k ^ 2) :=
          Summable.tsum_le_tsum hb (Breakdown.Periodic.Internal.summable_sq _)
            ((Breakdown.Periodic.Internal.summable_weight_heat hs).mul_left _)
      _ = 2 ^ 2 * W * I ^ 2 := by
          rw [tsum_mul_left]
          ring
  rw [hnorm]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hle

theorem forceV_eq_zero {s : ℝ} (hs : ¬ 0 < s) (F : Space → Space) : forceV s F = 0 := by
  apply Subtype.ext
  apply lp.ext
  funext k
  exact if_neg hs

theorem divFree_add' (k : Lattice) (c d : Coef) : divFree k (c + d) = divFree k c + divFree k d := by
  unfold divFree
  split_ifs
  · rfl
  · have e : divPairing k (c + d) = divPairing k c + divPairing k d := by
      simp [divPairing, mul_add, Finset.sum_add_distrib]
    rw [e, add_div, add_smul]
    abel

theorem divFree_smul' (k : Lattice) (r : ℝ) (c : Coef) : divFree k (r • c) = r • divFree k c := by
  unfold divFree
  split_ifs
  · rfl
  · rw [Force.Internal.divPairing_real_smul, mul_div_assoc, mul_smul, smul_sub, Complex.coe_smul]

theorem forceV_add_of_coef {s : ℝ} {F G H : Space → Space}
    (h : ∀ k, freqTrCoef F k = freqTrCoef G k + freqTrCoef H k) :
    forceV s F = forceV s G + forceV s H := by
  apply Subtype.ext
  apply lp.ext
  funext k
  change forceSeq s F k = forceSeq s G k + forceSeq s H k
  unfold forceSeq
  split_ifs
  · rw [h, divFree_add', smul_add]
  · simp

theorem forceV_smul_of_coef {s : ℝ} (r : ℝ) {F G : Space → Space}
    (h : ∀ k, freqTrCoef F k = r • freqTrCoef G k) : forceV s F = r • forceV s G := by
  apply Subtype.ext
  apply lp.ext
  funext k
  change forceSeq s F k = r • forceSeq s G k
  unfold forceSeq
  split_ifs
  · rw [h, divFree_smul', smul_comm]
  · simp

theorem complexify_add' (a b : Space) : complexify (a + b) = complexify a + complexify b := by
  ext i
  simp [complexify]

theorem complexify_smul' (r : ℝ) (a : Space) : complexify (r • a) = r • complexify a := by
  ext i
  simp [complexify]

theorem integrableOn_sim {μ : ℝ} (hμ : 0 < μ) (A : Freq.L2R) :
    IntegrableOn (fun x => complexify ((A : Space → Space) (simCoord μ x))) cell := by
  have : IsFiniteMeasure (volume.restrict cell) := isFiniteMeasure_restrict.2 finite_cell
  have hI := (memLp_sim hμ A).integrable (by norm_num)
  exact hI.mono (FreqTrSeries.Internal.continuous_complexify.comp_aestronglyMeasurable hI.1)
    (ae_of_all _ fun x => (norm_complexify' _).le)

theorem freqTrCoef_add_ae {F G H : Space → Space}
    (hG : IntegrableOn (fun x => complexify (G x)) cell) (hH : IntegrableOn (fun x => complexify (H x)) cell)
    (hF : F =ᵐ[volume.restrict cell] G + H) (k : Lattice) :
    freqTrCoef F k = freqTrCoef G k + freqTrCoef H k := by
  unfold freqTrCoef
  rw [← integral_add (Force.Internal.integrableOn_character_smul k hG)
    (Force.Internal.integrableOn_character_smul k hH)]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, Pi.add_apply, complexify_add', smul_add]

theorem freqTrCoef_smul_ae {F G : Space → Space} (r : ℝ)
    (hF : F =ᵐ[volume.restrict cell] r • G) (k : Lattice) : freqTrCoef F k = r • freqTrCoef G k := by
  unfold freqTrCoef
  rw [← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [hF] with x hx
  rw [hx, Pi.smul_apply, complexify_smul', smul_comm]

theorem sim_add_ae {μ : ℝ} (hμ : 0 < μ) (A B : Freq.L2R) :
    (fun x => ((A + B : Freq.L2R) : Space → Space) (simCoord μ x)) =ᵐ[volume.restrict cell]
      (fun x => (A : Space → Space) (simCoord μ x)) + (fun x => (B : Space → Space) (simCoord μ x)) := by
  filter_upwards [simCoord_ae μ, ae_restrict_of_ae ((qmp_simLin hμ).ae (Lp.coeFn_add A B))] with x h1 h2
  rw [Pi.add_apply, h1]
  exact h2

theorem sim_smul_ae {μ : ℝ} (hμ : 0 < μ) (r : ℝ) (A : Freq.L2R) :
    (fun x => ((r • A : Freq.L2R) : Space → Space) (simCoord μ x)) =ᵐ[volume.restrict cell]
      r • (fun x => (A : Space → Space) (simCoord μ x)) := by
  filter_upwards [simCoord_ae μ, ae_restrict_of_ae ((qmp_simLin hμ).ae (Lp.coeFn_smul r A))] with x h1 h2
  rw [Pi.smul_apply, h1]
  exact h2

end ShellDefs.Internal

def sourceFun (μ τ : ℝ) (A : Freq.L2R) : V :=
  if 0 < μ then forceV (μ * τ) (fun x => (A : Space → Space) (simCoord μ x)) else 0

open ShellDefs.Internal in
theorem sourceFun_bound (μ τ : ℝ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ A, ‖sourceFun μ τ A‖ ≤ C * ‖A‖ := by
  have hK := simK_nonneg μ
  refine ⟨2 * Real.sqrt (∑' k, weight k * heatFactor (μ * τ) k ^ 2) * simK μ, by positivity, fun A => ?_⟩
  unfold sourceFun
  split_ifs with hμ
  · by_cases hs : 0 < μ * τ
    · refine (norm_forceV_le hs _).trans ?_
      rw [mul_assoc (2 * Real.sqrt (∑' k, weight k * heatFactor (μ * τ) k ^ 2))]
      exact mul_le_mul_of_nonneg_left (integral_simCoord_le hμ A) (by positivity)
    · rw [forceV_eq_zero hs, norm_zero]
      positivity
  · rw [norm_zero]
    positivity

open ShellDefs.Internal in
theorem ShellDefs.Internal.sourceFun_add (μ τ : ℝ) (A B : Freq.L2R) :
    sourceFun μ τ (A + B) = sourceFun μ τ A + sourceFun μ τ B := by
  unfold sourceFun
  split_ifs with hμ
  · exact forceV_add_of_coef fun k =>
      freqTrCoef_add_ae (integrableOn_sim hμ A) (integrableOn_sim hμ B) (sim_add_ae hμ A B) k
  · simp

open ShellDefs.Internal in
theorem ShellDefs.Internal.sourceFun_smul (μ τ r : ℝ) (A : Freq.L2R) : sourceFun μ τ (r • A) = r • sourceFun μ τ A := by
  unfold sourceFun
  split_ifs with hμ
  · exact forceV_smul_of_coef r fun k => freqTrCoef_smul_ae r (sim_smul_ae hμ r A) k
  · simp

def sourceOp (μ τ : ℝ) : Freq.L2R →L[ℝ] V :=
  LinearMap.mkContinuous
    { toFun := sourceFun μ τ
      map_add' := ShellDefs.Internal.sourceFun_add μ τ
      map_smul' := ShellDefs.Internal.sourceFun_smul μ τ } (sourceFun_bound μ τ).choose
    (fun A => (sourceFun_bound μ τ).choose_spec.2 A)

def lambdaTorus (φ : Space → Space) (hφ : IsTestField φ) (b μ τ : ℝ) : ShellData →L[ℝ] V :=
  -((μ ^ (-(1 / 4 : ℝ))) • (sourceOp μ τ).comp (advectShell φ hφ b))

end Breakdown.Periodic

import Breakdown.Torus.CompareStatements
import Breakdown.FreqTr.BilinDilate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace CompareFrame.Internal

theorem eLpNorm_comp_smul {p : ℝ≥0∞} {s : ℝ} (hs : 0 < s) (g : Space → Space)
    (hg : AEStronglyMeasurable g volume) :
    eLpNorm (fun y => g (s • y)) p volume =
      ENNReal.ofReal (s ^ 3)⁻¹ ^ (1 / p).toReal * eLpNorm g p volume := by
  have hmap := Measure.map_addHaar_smul (volume : Measure Space) hs.ne'
  have hg' : AEStronglyMeasurable g (Measure.map (s • ·) volume) := by
    rw [hmap]; exact hg.smul_measure _
  rw [show (fun y => g (s • y)) = g ∘ (s • ·) from rfl,
    ← eLpNorm_map_measure hg' (measurable_const_smul s).aemeasurable, hmap,
    eLpNorm_smul_measure_of_ne_zero]
  · simp [finrank_euclideanSpace, abs_of_pos hs]
  · simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity

theorem norm_of_ae_comp_smul {p : ℝ≥0∞} [Fact (1 ≤ p)] {s k : ℝ} (hs : 0 < s)
    (F G : Lp Space p (volume : Measure Space)) (h : (F : Space → Space) =ᵐ[volume] fun y => k • (G : Space → Space) (s • y)) :
    ‖F‖ = ‖k‖ * ((s ^ 3)⁻¹) ^ (1 / p).toReal * ‖G‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae h,
    show (fun y => k • (G : Space → Space) (s • y)) = k • (fun y => (G : Space → Space) (s • y)) from rfl,
    eLpNorm_const_smul, eLpNorm_comp_smul hs _ (Lp.aestronglyMeasurable G),
    ENNReal.toReal_mul, ENNReal.toReal_mul, Lp.norm_def, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (by positivity), toReal_enorm, mul_assoc]

theorem sub_ae_comp_smul {p : ℝ≥0∞} [Fact (1 ≤ p)] {s k : ℝ} (hs : 0 < s)
    (A1 A2 B1 B2 : Lp Space p (volume : Measure Space)) (f1 f2 g1 g2 : Space → Space)
    (h1 : (A1 : Space → Space) =ᵐ[volume] f1) (h2 : (A2 : Space → Space) =ᵐ[volume] f2)
    (h3 : (B1 : Space → Space) =ᵐ[volume] g1) (h4 : (B2 : Space → Space) =ᵐ[volume] g2)
    (hf : ∀ y, f1 y = k • f2 (s • y)) (hg : ∀ y, g1 y = k • g2 (s • y)) :
    ((A1 - B1 : Lp Space p (volume : Measure Space)) : Space → Space) =ᵐ[volume]
      fun y => k • ((A2 - B2 : Lp Space p (volume : Measure Space)) : Space → Space) (s • y) := by
  have hq := Measure.quasiMeasurePreserving_smul (volume : Measure Space) hs.ne'
  filter_upwards [Lp.coeFn_sub A1 B1, h1, h3, hq.ae_eq_comp (Lp.coeFn_sub A2 B2), hq.ae_eq_comp h2,
    hq.ae_eq_comp h4] with y ha hb hc hd he hf'
  simp only [Function.comp_apply, Pi.sub_apply] at ha hd he hf'
  rw [ha, hb, hc, hd, he, hf', hf, hg, smul_sub]

theorem mem_closedBall_smul {s b : ℝ} (hs : 0 < s) (y : Space) :
    s • y ∈ Metric.closedBall (0 : Space) (s * b) ↔ y ∈ Metric.closedBall (0 : Space) b := by
  rw [mem_closedBall_zero_iff, mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
  exact mul_le_mul_iff_of_pos_left hs

theorem indicator_scale {s b k0 k : ℝ} (hs : 0 < s) {f g : Space → Space}
    (h : ∀ y, k0 • f y = k • g (s • y)) (y : Space) :
    k0 • (Metric.closedBall (0 : Space) b).indicator f y =
      k • (Metric.closedBall (0 : Space) (s * b)).indicator g (s • y) := by
  classical
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases hy : y ∈ Metric.closedBall (0 : Space) b
  · rw [if_pos hy, if_pos ((mem_closedBall_smul hs y).2 hy), h]
  · rw [if_neg hy, if_neg (fun h' => hy ((mem_closedBall_smul hs y).1 h')), smul_zero, smul_zero]

theorem restrictTorus_fst {μ b : ℝ} (h : IsShellScale μ b) (z : V) (j : Fin 3) :
    (restrictTorus μ b z).1 j = Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y)))) := by
  simp only [restrictTorus, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  unfold restrictTorusFun
  rw [if_pos h]

theorem restrictTorus_snd {μ b : ℝ} (h : IsShellScale μ b) (z : V) :
    (restrictTorus μ b z).2 = Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y)))) := by
  simp only [restrictTorus, LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk]
  unfold restrictTorusFun
  rw [if_pos h]

theorem restrictTorus_fst_ae {μ b : ℝ} (h : IsShellScale μ b) (z : V) (j : Fin 3) :
    ((restrictTorus μ b z).1 j : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))) := by
  rw [restrictTorus_fst h z j, ShellDefs.Internal.toLpOrZero_eq
    (ShellDefs.Internal.norm_shell_le 2 (by norm_num) h ShellDefs.Internal.exp_two _).1]
  exact MemLp.coeFn_toLp _

theorem restrictTorus_snd_ae {μ b : ℝ} (h : IsShellScale μ b) (z : V) :
    ((restrictTorus μ b z).2 : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))) := by
  rw [restrictTorus_snd h z, ShellDefs.Internal.toLpOrZero_eq
    (ShellDefs.Internal.norm_shell_le 6 (by norm_num) h ShellDefs.Internal.exp_six _).1]
  exact MemLp.coeFn_toLp _

theorem restrictR3_fst (b : ℝ) (v : Freq.X) (j : Fin 3) :
    (restrictR3 b v).1 j = cutLp 2 b (Freq.partialX j v) := rfl

theorem restrictR3_snd (b : ℝ) (v : Freq.X) :
    (restrictR3 b v).2 = cutLp 6 b (Freq.velocity v) := rfl

theorem shellScale_mul {μ c b : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (h : IsShellScale μ (Real.sqrt c * b)) :
    IsShellScale (μ * c) b := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  refine ⟨mul_pos h1 hc, ?_, pos_of_mul_pos_right h3 hs.le, ?_⟩
  · nlinarith
  · rw [Real.sqrt_mul h1.le, mul_assoc]
    exact h4

theorem sqrt_cube_rpow {c : ℝ} (hc : 0 < c) (q : ℝ) :
    ((Real.sqrt c ^ 3)⁻¹) ^ q = c ^ (-(3 / 2 * q)) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc.le, ← Real.rpow_neg hc.le,
    ← Real.rpow_mul hc.le]
  congr 1
  push_cast
  ring

theorem grad_component {μ c b : ℝ} (hD : Freq.DilationAlgebra) (hF : Freq.FieldOpRealized)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsShellScale μ (Real.sqrt c * b)) (Z : V) (Y : Freq.X) (j : Fin 3) :
    ‖(restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).1 j‖ =
      c ^ (1 / 4 : ℝ) * ‖(restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).1 j‖ := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hμ : 0 < μ := hS.1
  have hS' := shellScale_mul hc hc1 hS
  have e1 : (restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).1 j =
      c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).1 j - cutLp 2 b (Freq.partialX j (Freq.dilX c Y)) := by
    simp only [Prod.fst_sub, Pi.sub_apply, restrictR3_fst, map_smul, Prod.smul_fst, Pi.smul_apply]
  have e2 : (restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).1 j =
      (restrictTorus μ (Real.sqrt c * b) Z).1 j - cutLp 2 (Real.sqrt c * b) (Freq.partialX j Y) := by
    simp only [Prod.fst_sub, Pi.sub_apply, restrictR3_fst]
  rw [e1, e2]
  have hA1 : ((c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).1 j : Freq.L2R) : Space → Space) =ᵐ[volume]
      fun y => c ^ (1 / 4 : ℝ) • (Metric.closedBall (0 : Space) b).indicator
        (fun y => ((μ * c) ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt (μ * c) • y))) y := by
    filter_upwards [Lp.coeFn_smul (c ^ (1 / 4 : ℝ)) ((restrictTorus (μ * c) b Z).1 j),
      restrictTorus_fst_ae hS' Z j] with y h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hB1 : ((cutLp 2 b (Freq.partialX j (Freq.dilX c Y)) : Freq.L2R) : Space → Space) =ᵐ[volume]
      (Metric.closedBall (0 : Space) b).indicator
        (fun y => c • (Freq.partialX j Y : Space → Space) (Real.sqrt c • y)) := by
    classical
    filter_upwards [cutLp_apply 2 b (Freq.partialX j (Freq.dilX c Y)),
      Freq.Internal.BilinDilate.partialX_dilX hD hF hc j Y] with y h1 h2
    rw [h1, Set.indicator_apply, Set.indicator_apply, h2]
  have e : c ^ (1 / 4 : ℝ) * (μ * c) ^ (3 / 4 : ℝ) = c * μ ^ (3 / 4 : ℝ) := by
    rw [Real.mul_rpow hμ.le hc.le, mul_left_comm, ← Real.rpow_add hc, mul_comm]
    norm_num
  have hf := indicator_scale (b := b) hs (k0 := c ^ (1 / 4 : ℝ)) (k := c)
    (f := fun y => ((μ * c) ^ (3 / 4 : ℝ)) •
      Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt (μ * c) • y)))
    (g := fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j Z) (center + Real.sqrt μ • y)))
    (fun y => by rw [smul_smul, e, Real.sqrt_mul hμ.le, mul_smul (Real.sqrt μ) (Real.sqrt c) y, smul_smul c])
  have hg := fun y => (one_smul ℝ _).symm.trans (indicator_scale (b := b) hs (k0 := 1) (k := c)
    (f := fun y => c • (Freq.partialX j Y : Space → Space) (Real.sqrt c • y))
    (g := (Freq.partialX j Y : Space → Space)) (fun y => one_smul ℝ _) y)
  have key := sub_ae_comp_smul (p := 2) (k := c) hs (c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).1 j)
    ((restrictTorus μ (Real.sqrt c * b) Z).1 j) (cutLp 2 b (Freq.partialX j (Freq.dilX c Y)))
    (cutLp 2 (Real.sqrt c * b) (Freq.partialX j Y)) _ _ _ _ hA1 (restrictTorus_fst_ae hS Z j) hB1
    (cutLp_apply 2 (Real.sqrt c * b) (Freq.partialX j Y)) hf hg
  rw [norm_of_ae_comp_smul (p := 2) hs _ _ key, sqrt_cube_rpow hc, Real.norm_eq_abs, abs_of_pos hc]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat]
  nth_rewrite 1 [← Real.rpow_one c]
  rw [← Real.rpow_add hc]
  norm_num

theorem velocity_component {μ c b : ℝ} (hV : Freq.VelocityDilate)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsShellScale μ (Real.sqrt c * b)) (Z : V) (Y : Freq.X) :
    ‖(restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).2‖ =
      c ^ (1 / 4 : ℝ) * ‖(restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).2‖ := by
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  have hμ : 0 < μ := hS.1
  have hS' := shellScale_mul hc hc1 hS
  have e1 : (restrictTorus (μ * c) b (c ^ (1 / 4 : ℝ) • Z) - restrictR3 b (Freq.dilX c Y)).2 =
      c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).2 - cutLp 6 b (Freq.velocity (Freq.dilX c Y)) := by
    simp only [Prod.snd_sub, restrictR3_snd, map_smul, Prod.smul_snd]
  have e2 : (restrictTorus μ (Real.sqrt c * b) Z - restrictR3 (Real.sqrt c * b) Y).2 =
      (restrictTorus μ (Real.sqrt c * b) Z).2 - cutLp 6 (Real.sqrt c * b) (Freq.velocity Y) := by
    simp only [Prod.snd_sub, restrictR3_snd]
  rw [e1, e2]
  have hA1 : ((c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).2 : Freq.L6R) : Space → Space) =ᵐ[volume]
      fun y => c ^ (1 / 4 : ℝ) • (Metric.closedBall (0 : Space) b).indicator
        (fun y => ((μ * c) ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt (μ * c) • y))) y := by
    filter_upwards [Lp.coeFn_smul (c ^ (1 / 4 : ℝ)) ((restrictTorus (μ * c) b Z).2),
      restrictTorus_snd_ae hS' Z] with y h1 h2
    rw [h1, Pi.smul_apply, h2]
  have hB1 : ((cutLp 6 b (Freq.velocity (Freq.dilX c Y)) : Freq.L6R) : Space → Space) =ᵐ[volume]
      (Metric.closedBall (0 : Space) b).indicator
        (fun y => Real.sqrt c • (Freq.velocity Y : Space → Space) (Real.sqrt c • y)) := by
    classical
    filter_upwards [cutLp_apply 6 b (Freq.velocity (Freq.dilX c Y)), hV c hc Y] with y h1 h2
    rw [h1, Set.indicator_apply, Set.indicator_apply, h2]
    rfl
  have e : c ^ (1 / 4 : ℝ) * (μ * c) ^ (1 / 4 : ℝ) = Real.sqrt c * μ ^ (1 / 4 : ℝ) := by
    rw [Real.mul_rpow hμ.le hc.le, mul_left_comm, ← Real.rpow_add hc, mul_comm, Real.sqrt_eq_rpow]
    norm_num
  have hf := indicator_scale (b := b) hs (k0 := c ^ (1 / 4 : ℝ)) (k := Real.sqrt c)
    (f := fun y => ((μ * c) ^ (1 / 4 : ℝ)) •
      Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt (μ * c) • y)))
    (g := fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff Z) (center + Real.sqrt μ • y)))
    (fun y => by rw [smul_smul, e, Real.sqrt_mul hμ.le, mul_smul (Real.sqrt μ) (Real.sqrt c) y, smul_smul (Real.sqrt c)])
  have hg := fun y => (one_smul ℝ _).symm.trans (indicator_scale (b := b) hs (k0 := 1) (k := Real.sqrt c)
    (f := fun y => Real.sqrt c • (Freq.velocity Y : Space → Space) (Real.sqrt c • y))
    (g := (Freq.velocity Y : Space → Space)) (fun y => one_smul ℝ _) y)
  have key := sub_ae_comp_smul (p := 6) (k := Real.sqrt c) hs (c ^ (1 / 4 : ℝ) • (restrictTorus (μ * c) b Z).2)
    ((restrictTorus μ (Real.sqrt c * b) Z).2) (cutLp 6 b (Freq.velocity (Freq.dilX c Y)))
    (cutLp 6 (Real.sqrt c * b) (Freq.velocity Y)) _ _ _ _ hA1 (restrictTorus_snd_ae hS Z) hB1
    (cutLp_apply 6 (Real.sqrt c * b) (Freq.velocity Y)) hf hg
  rw [norm_of_ae_comp_smul (p := 6) hs _ _ key, sqrt_cube_rpow hc, Real.norm_eq_abs, abs_of_pos hs]
  congr 1
  rw [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, Real.sqrt_eq_rpow,
    ← Real.rpow_add hc]
  norm_num

end CompareFrame.Internal

open CompareFrame.Internal in
theorem frameChange (hV : Freq.VelocityDilate) (hD : Freq.DilationAlgebra) (hF : Freq.FieldOpRealized) :
    FrameChange := by
  intro μ c b hc hc1 hS Z Y
  rw [Prod.norm_def]
  refine max_le ?_ ?_
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [grad_component hD hF hc hc1 hS Z Y j]
    gcongr
    exact (norm_le_pi_norm _ j).trans (norm_fst_le _)
  · rw [velocity_component hV hc hc1 hS Z Y]
    gcongr
    exact norm_snd_le _

end Breakdown.Periodic

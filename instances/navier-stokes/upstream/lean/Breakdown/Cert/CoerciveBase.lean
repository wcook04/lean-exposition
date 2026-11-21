import Breakdown.Cert.CoerciveNodes

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace BaseDensityInternal

def velSq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeVel ι v σ y)

def gradSq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeGrad ι (gradField v) σ y)

def vortSq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (curlOfGrad (modeGrad ι (gradField v) σ y))

def secondDerivModeSq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (modeSecondDeriv ι (secondDerivField v) σ y)

def vortGradSq (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  cnormSq (curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y))

def modeSum (F : ℤ × ℤ → ℝ → Space → ℝ) : ℝ≥0∞ :=
  ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (F ι σ y)

def baseMain (c : ℝ) (w : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y - c * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y)

def secondDerivDefect (θ : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y) - ModeWeights.secondDerivNorm θ y * gradSq v ι σ y

def gradDefect (θ : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  θ y * (gradSq v ι σ y - vortSq v ι σ y) - ModeWeights.secondDerivNorm θ y * velSq v ι σ y

def expanded (θD θZ : Space → ℝ) (c : ℝ) (w : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ)
    (y : Space) : ℝ :=
  (θD y - c) * secondDerivModeSq v ι σ y + (1 - θD y) * vortGradSq v ι σ y
    + (1 / 4 - θZ y) * vortSq v ι σ y
    + (θZ y - ModeWeights.secondDerivNorm θD y - c * w y) * gradSq v ι σ y
    - ModeWeights.secondDerivNorm θZ y * velSq v ι σ y

theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem continuous_cnormSq {β : Type*} [Fintype β] {X : Type*} [TopologicalSpace X]
    {F : X → β → ℂ} (hF : Continuous F) : Continuous fun x => cnormSq (F x) :=
  continuous_finsetSum _ fun b _ => ((continuous_apply b).comp hF).norm.pow 2

theorem continuous_curlOfGrad {X : Type*} [TopologicalSpace X] {F : X → Fin 3 × Fin 3 → ℂ}
    (hF : Continuous F) : Continuous fun x => curlOfGrad (F x) :=
  continuous_pi fun _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
    continuous_const.mul ((continuous_apply _).comp hF)

theorem continuous_curlGradOfSecondDeriv {X : Type*} [TopologicalSpace X]
    {F : X → Fin 3 × Fin 3 × Fin 3 → ℂ} (hF : Continuous F) :
    Continuous fun x => curlGradOfSecondDeriv (F x) :=
  continuous_pi fun _ => continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
    continuous_const.mul ((continuous_apply _).comp hF)

theorem modeValues_baseDensity {C : Type} (convD convZ : C → Space → ℝ) (d : C) (c : ℝ)
    (w : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeValues v ι σ y (baseDensity convD convZ d c w y) = expanded (convD d) (convZ d) c w v ι σ y := by
  simp only [modeValues, baseDensity, expanded, Real.sq_sqrt (cnormSq_nonneg _), velSq, gradSq, vortSq,
    secondDerivModeSq, vortGradSq]


theorem axialRot_coord_zero (φ : ℝ) (y : Space) :
    axialRot φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := by
  simp [axialRot, unitVector]

theorem axialRot_coord_one (φ : ℝ) (y : Space) :
    axialRot φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := by
  simp [axialRot, unitVector]

theorem axialRot_coord_two (φ : ℝ) (y : Space) : axialRot φ y 2 = y 2 := by
  simp [axialRot, unitVector]

theorem norm_axialRot (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Fin.sum_univ_three, Fin.sum_univ_three,
    axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq φ

theorem axialRot_zero_vec (φ : ℝ) : axialRot φ 0 = 0 := by
  simp [axialRot]

theorem continuous_axialRot_of {Y : Type*} [TopologicalSpace Y] {a : Y → ℝ} {u : Y → Space}
    (ha : Continuous a) (hu : Continuous u) : Continuous fun q => axialRot (a q) (u q) := by
  unfold axialRot
  fun_prop

theorem modeAverage_eq_zero {β : Type*} (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (b : β)
    (h : ∀ τ φ, f τ φ b = 0) : modeAverage ι f b = 0 := by
  simp [modeAverage, h]

theorem top_add_le (n : ℕ) : ((n : WithTop ℕ∞) + 1) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem modes_support_aux {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    ∃ R, ∀ s x, R < ‖x‖ → v s x = 0 ∧ gradField v s x = 0 ∧ secondDerivField v s x = 0 := by
  obtain ⟨R, hR⟩ := hv.2.2.1
  have hopen : IsOpen {x : Space | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  have hg : ∀ s x, R < ‖x‖ → gradField v s x = 0 := by
    intro s x hx
    have hev : v s =ᶠ[nhds x] fun _ => (0 : Space) :=
      Filter.eventually_of_mem (hopen.mem_nhds hx) fun x' hx' => hR s x' hx'
    rw [gradField, hev.fderiv_eq]
    exact fderiv_const_apply _
  refine ⟨R, fun s x hx => ⟨hR s x hx, hg s x hx, ?_⟩⟩
  have hev : (fun x' => fderiv ℝ (v s) x') =ᶠ[nhds x] fun _ => (0 : Space →L[ℝ] Space) :=
    Filter.eventually_of_mem (hopen.mem_nhds hx) fun x' hx' => hg s x' hx'
  rw [secondDerivField, hev.fderiv_eq]
  exact fderiv_const_apply _

theorem modes_support {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    ∃ R, ∀ ι σ y, R < ‖y‖ →
      modeVel ι v σ y = 0 ∧ modeGrad ι (gradField v) σ y = 0 ∧ modeSecondDeriv ι (secondDerivField v) σ y = 0 := by
  obtain ⟨R, hR⟩ := modes_support_aux hv
  refine ⟨R, fun ι σ y hy => ⟨?_, ?_, ?_⟩⟩
  all_goals
    funext i
    apply modeAverage_eq_zero
    intro τ φ
    have hx : R < ‖axialRot φ y‖ := by rw [norm_axialRot]; exact hy
    obtain ⟨h0, h1, h2⟩ := hR (σ + τ) (axialRot φ y) hx
  · simp [h0, axialRot_zero_vec]
  · simp [h1, axialRot_zero_vec]
  · simp [h2, axialRot_zero_vec]

theorem continuous_modeAverage {X β : Type*} [TopologicalSpace X] (ι : ℤ × ℤ)
    (f : X → ℝ → ℝ → β → ℝ) (b : β) (hf : Continuous fun q : X × ℝ × ℝ => f q.1 q.2.1 q.2.2 b) :
    Continuous fun x => modeAverage ι (f x) b := by
  unfold modeAverage
  refine continuous_const.mul ?_
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x τ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f x τ φ b : ℝ) : ℂ))
    ?_ 0 1
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun (p : X × ℝ) φ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f p.1 p.2 φ b : ℝ) : ℂ))
    ?_ 0 (2 * Real.pi)
  have h1 : Continuous fun q : (X × ℝ) × ℝ => f q.1.1 q.1.2 q.2 b :=
    hf.comp (continuous_fst.fst.prodMk (continuous_fst.snd.prodMk continuous_snd))
  have h2 : Continuous fun q : (X × ℝ) × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * q.1.2 + ι.2 * q.2 : ℝ) : ℂ) * Complex.I)) := by
    fun_prop
  exact h2.mul (Complex.continuous_ofReal.comp h1)

theorem fields_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    Continuous (fun z : ℝ × Space => v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => gradField v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => secondDerivField v z.1 z.2) := by
  have h0 := hv.1
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (h0.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have h2 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => fderiv ℝ (v z.1) y) (g := fun z => z.2)
      (h1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)
  exact ⟨h0.continuous, h1.continuous, h2.continuous⟩

theorem modes_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) :
    Continuous (fun z : ℝ × Space => modeVel ι v z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => modeGrad ι (gradField v) z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => modeSecondDeriv ι (secondDerivField v) z.1 z.2) := by
  obtain ⟨c0, c1, c2⟩ := fields_continuous hv
  have hrot : ∀ {a : (ℝ × Space) × ℝ × ℝ → ℝ} {u : (ℝ × Space) × ℝ × ℝ → Space}, Continuous a →
      Continuous u → Continuous fun q => axialRot (a q) (u q) := fun ha hu => continuous_axialRot_of ha hu
  have hcoord : ∀ {u : (ℝ × Space) × ℝ × ℝ → Space} (i : Fin 3), Continuous u →
      Continuous fun q => u q i := fun i hu => (PiLp.continuous_apply 2 _ i).comp hu
  have hs : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.1.1 + q.2.1 := by fun_prop
  have hy : Continuous fun q : (ℝ × Space) × ℝ × ℝ => axialRot q.2.2 q.1.2 :=
    continuous_axialRot_of (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.2.2)
      (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.1.2)
  have he : ∀ j : Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ => axialRot q.2.2 (unitVector j) := fun j =>
    continuous_axialRot_of (by fun_prop : Continuous fun q : (ℝ × Space) × ℝ × ℝ => q.2.2) continuous_const
  have hneg : Continuous fun q : (ℝ × Space) × ℝ × ℝ => -q.2.2 := by fun_prop
  have f0 : ∀ i : Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)) i := fun i =>
    hcoord i (hrot hneg (c0.comp (hs.prodMk hy)))
  have f1 : ∀ ij : Fin 3 × Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (gradField v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)
        (axialRot q.2.2 (unitVector ij.2))) ij.1 := fun ij =>
    hcoord ij.1 (hrot hneg ((c1.comp (hs.prodMk hy)).clm_apply (he ij.2)))
  have f2 : ∀ ijl : Fin 3 × Fin 3 × Fin 3, Continuous fun q : (ℝ × Space) × ℝ × ℝ =>
      axialRot (-q.2.2) (secondDerivField v (q.1.1 + q.2.1) (axialRot q.2.2 q.1.2)
        (axialRot q.2.2 (unitVector ijl.2.1)) (axialRot q.2.2 (unitVector ijl.2.2))) ijl.1 := fun ijl =>
    hcoord ijl.1 (hrot hneg (((c2.comp (hs.prodMk hy)).clm_apply (he ijl.2.1)).clm_apply (he ijl.2.2)))
  refine ⟨continuous_pi fun i => ?_, continuous_pi fun ij => ?_, continuous_pi fun ijl => ?_⟩
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (i : Fin 3) =>
      axialRot (-φ) (v (z.1 + τ) (axialRot φ z.2)) i) i (f0 i)
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (ij : Fin 3 × Fin 3) =>
      axialRot (-φ) (gradField v (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ij.2))) ij.1) ij (f1 ij)
  · exact continuous_modeAverage ι (fun (z : ℝ × Space) τ φ (ijl : Fin 3 × Fin 3 × Fin 3) =>
      axialRot (-φ) (secondDerivField v (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector ijl.2.1))
        (axialRot φ (unitVector ijl.2.2))) ijl.1) ijl (f2 ijl)

def secondDerivQuad (θ : Space → ℝ) (y : Space) (x : Fin 3 → ℂ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3, fderiv ℝ (fun x => fderiv ℝ θ x) y (unitVector i) (unitVector j) *
    (x i * (starRingEnd ℂ) (x j)).re

theorem norm_coordVec (r : Fin 3 → ℝ) : ‖∑ i : Fin 3, r i • unitVector i‖ ^ 2 = ∑ i : Fin 3, r i ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp [unitVector, Fin.sum_univ_three]

theorem secondDerivQuad_le (θ : Space → ℝ) (y : Space) (x : Fin 3 → ℂ) :
    secondDerivQuad θ y x ≤ ModeWeights.secondDerivNorm θ y * cnormSq x := by
  set A := fderiv ℝ (fun x => fderiv ℝ θ x) y with hAdef
  have hA : ‖A‖ = ModeWeights.secondDerivNorm θ y := by
    rw [hAdef, ModeWeights.secondDerivNorm, ← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one]
  set a : Space := ∑ i : Fin 3, (x i).re • unitVector i with ha
  set b : Space := ∑ i : Fin 3, (x i).im • unitVector i with hb
  have key : secondDerivQuad θ y x = A a a + A b b := by
    simp only [secondDerivQuad, ha, hb, map_sum, map_smul, ContinuousLinearMap.coe_sum', Finset.sum_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, Complex.mul_re, Complex.conj_re,
      Complex.conj_im, Fin.sum_univ_three, ← hAdef]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have bound : ∀ u : Space, A u u ≤ ‖A‖ * ‖u‖ ^ 2 := fun u =>
    calc A u u ≤ ‖A u u‖ := le_abs_self _
      _ ≤ ‖A u‖ * ‖u‖ := (A u).le_opNorm u
      _ ≤ (‖A‖ * ‖u‖) * ‖u‖ := mul_le_mul_of_nonneg_right (A.le_opNorm u) (norm_nonneg _)
      _ = ‖A‖ * ‖u‖ ^ 2 := by ring
  have hc : cnormSq x = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    rw [ha, hb, norm_coordVec, norm_coordVec, cnormSq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [key, hc, ← hA]
  linarith [bound a, bound b]

theorem squares_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) :
    Continuous (fun z : ℝ × Space => velSq v ι z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => gradSq v ι z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => vortSq v ι z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => secondDerivModeSq v ι z.1 z.2) ∧
      Continuous (fun z : ℝ × Space => vortGradSq v ι z.1 z.2) := by
  obtain ⟨h0, h1, h2⟩ := modes_continuous hv ι
  exact ⟨continuous_cnormSq h0, continuous_cnormSq h1, continuous_cnormSq (continuous_curlOfGrad h1),
    continuous_cnormSq h2, continuous_cnormSq (continuous_curlGradOfSecondDeriv h2)⟩

theorem squares_support {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    ∃ R, ∀ ι σ y, R < ‖y‖ → velSq v ι σ y = 0 ∧ gradSq v ι σ y = 0 ∧ vortSq v ι σ y = 0 ∧
      secondDerivModeSq v ι σ y = 0 ∧ vortGradSq v ι σ y = 0 := by
  obtain ⟨R, hR⟩ := modes_support hv
  refine ⟨R, fun ι σ y hy => ?_⟩
  obtain ⟨h0, h1, h2⟩ := hR ι σ y hy
  simp [velSq, gradSq, vortSq, secondDerivModeSq, vortGradSq, h0, h1, h2, cnormSq, curlOfGrad, curlGradOfSecondDeriv]

theorem integrable_of_vanish {m : Space → ℝ} (hm : Continuous m) {R : ℝ}
    (hR : ∀ y, R < ‖y‖ → m y = 0) : Integrable m :=
  hm.integrable_of_hasCompactSupport (HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy =>
    hR y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy))

theorem ennreal_le_of_integral_le {D P N : Space → ℝ} (hD : Integrable D) (hP : Integrable P)
    (hN : Integrable N) (hP0 : ∀ y, 0 ≤ P y) (hN0 : ∀ y, 0 ≤ N y)
    (h : ∫ y, D y ≤ (∫ y, P y) - ∫ y, N y) :
    (∫⁻ y, ENNReal.ofReal (D y)) + ∫⁻ y, ENNReal.ofReal (N y)
      ≤ (∫⁻ y, ENNReal.ofReal (P y)) + ∫⁻ y, ENNReal.ofReal (-D y) := by
  have a1 := hD.lintegral_lt_top
  have a2 : (∫⁻ y, ENNReal.ofReal (-D y)) < ⊤ := hD.neg.lintegral_lt_top
  have a3 := hP.lintegral_lt_top
  have a4 := hN.lintegral_lt_top
  rw [← ENNReal.toReal_le_toReal (ENNReal.add_lt_top.2 ⟨a1, a4⟩).ne (ENNReal.add_lt_top.2 ⟨a3, a2⟩).ne,
    ENNReal.toReal_add a1.ne a4.ne, ENNReal.toReal_add a3.ne a2.ne]
  have e1 := integral_eq_lintegral_pos_part_sub_lintegral_neg_part hD
  have e2 := integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hP0) hP.aestronglyMeasurable
  have e3 := integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hN0) hN.aestronglyMeasurable
  linarith

theorem lintegral_tsum_swap {F : ℤ × ℤ → ℝ → Space → ℝ}
    (hF : ∀ ι, Measurable fun z : ℝ × Space => F ι z.1 z.2) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (F ι σ y)) = modeSum F := by
  unfold modeSum
  have my : ∀ ι σ, Measurable fun y => ENNReal.ofReal (F ι σ y) := fun ι σ =>
    ENNReal.measurable_ofReal.comp ((hF ι).comp (measurable_const.prodMk measurable_id))
  have mσ : ∀ ι, Measurable fun σ => ∫⁻ y, ENNReal.ofReal (F ι σ y) := fun ι =>
    (ENNReal.measurable_ofReal.comp (hF ι)).lintegral_prod_right'
  have h1 : ∀ σ, (∫⁻ y, ∑' ι, ENNReal.ofReal (F ι σ y)) = ∑' ι, ∫⁻ y, ENNReal.ofReal (F ι σ y) :=
    fun σ => lintegral_tsum fun ι => (my ι σ).aemeasurable
  simp_rw [h1]
  exact lintegral_tsum fun ι => (mσ ι).aemeasurable

theorem modeSum_add {F G : ℤ × ℤ → ℝ → Space → ℝ} (hF0 : ∀ ι σ y, 0 ≤ F ι σ y)
    (hG0 : ∀ ι σ y, 0 ≤ G ι σ y) (hF : ∀ ι, Measurable fun z : ℝ × Space => F ι z.1 z.2) :
    modeSum (fun ι σ y => F ι σ y + G ι σ y) = modeSum F + modeSum G := by
  unfold modeSum
  have my : ∀ ι σ, Measurable fun y => ENNReal.ofReal (F ι σ y) := fun ι σ =>
    ENNReal.measurable_ofReal.comp ((hF ι).comp (measurable_const.prodMk measurable_id))
  have mσ : ∀ ι, Measurable fun σ => ∫⁻ y, ENNReal.ofReal (F ι σ y) := fun ι =>
    (ENNReal.measurable_ofReal.comp (hF ι)).lintegral_prod_right'
  rw [← ENNReal.tsum_add]
  congr 1
  funext ι
  rw [← lintegral_add_left (mσ ι)]
  congr 1
  funext σ
  rw [← lintegral_add_left (my ι σ)]
  congr 1
  funext y
  exact ENNReal.ofReal_add (hF0 ι σ y) (hG0 ι σ y)

theorem modeSum_const_mul {F : ℤ × ℤ → ℝ → Space → ℝ} {k : ℝ} (hk : 0 ≤ k) :
    modeSum (fun ι σ y => k * F ι σ y) = ENNReal.ofReal k * modeSum F := by
  unfold modeSum
  rw [← ENNReal.tsum_mul_left]
  congr 1
  funext ι
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext σ
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext y
  exact ENNReal.ofReal_mul hk

theorem final_algebra {p n N Q : ℝ≥0∞} {X : ℝ} (hN : N ≠ ⊤) (hQ : Q ≠ ⊤) (hX : Q.toReal - N.toReal = X)
    (h : p + N ≤ Q + n) : p + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + n := by
  have key : Q + ENNReal.ofReal (-X) = ENNReal.ofReal X + N := by
    rw [← ENNReal.toReal_eq_toReal_iff' (ENNReal.add_ne_top.2 ⟨hQ, ENNReal.ofReal_ne_top⟩)
      (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hN⟩), ENNReal.toReal_add hQ ENNReal.ofReal_ne_top,
      ENNReal.toReal_add ENNReal.ofReal_ne_top hN]
    rcases le_total 0 X with hx | hx
    · rw [ENNReal.toReal_ofReal hx, ENNReal.ofReal_of_nonpos (by linarith)]
      simp
      linarith
    · rw [ENNReal.toReal_ofReal (by linarith), ENNReal.ofReal_of_nonpos hx]
      simp
      linarith
  have h2 : p + ENNReal.ofReal (-X) + N ≤ ENNReal.ofReal X + n + N :=
    calc p + ENNReal.ofReal (-X) + N = (p + N) + ENNReal.ofReal (-X) := by ring
      _ ≤ (Q + n) + ENNReal.ofReal (-X) := by gcongr
      _ = (Q + ENNReal.ofReal (-X)) + n := by ring
      _ = ENNReal.ofReal X + n + N := by rw [key]; ring
  exact (ENNReal.add_le_add_iff_right hN).1 h2


def mainPos (c : ℝ) (w : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y
    + max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y)

def mainNeg (c : ℝ) (w : Space → ℝ) (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  max c 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y)

theorem squares_measurable {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) :
    Measurable (fun z : ℝ × Space => velSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => gradSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => vortSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => secondDerivModeSq v ι z.1 z.2) ∧
      Measurable (fun z : ℝ × Space => vortGradSq v ι z.1 z.2) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := squares_continuous hv ι
  exact ⟨c0.measurable, c1.measurable, c2.measurable, c3.measurable, c4.measurable⟩

theorem squares_nonneg (v : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ velSq v ι σ y ∧ 0 ≤ gradSq v ι σ y ∧ 0 ≤ vortSq v ι σ y ∧ 0 ≤ secondDerivModeSq v ι σ y ∧
      0 ≤ vortGradSq v ι σ y :=
  ⟨cnormSq_nonneg _, cnormSq_nonneg _, cnormSq_nonneg _, cnormSq_nonneg _, cnormSq_nonneg _⟩

theorem continuous_secondDerivNorm {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ) :
    Continuous (ModeWeights.secondDerivNorm θ) :=
  (hθ.continuous_iteratedFDeriv (m := 2) le_rfl).norm

theorem measurable_inner {F : ℝ → Space → ℝ} (hF : Measurable fun z : ℝ × Space => F z.1 z.2) :
    Measurable fun σ => ∫⁻ y, ENNReal.ofReal (F σ y) :=
  (ENNReal.measurable_ofReal.comp hF).lintegral_prod_right'

theorem measurable_expanded {θD θZ : Space → ℝ} (hD : ContDiff ℝ 2 θD) (hZ : ContDiff ℝ 2 θZ) (c : ℝ)
    {w : Space → ℝ} (hwm : Measurable w) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v)
    (ι : ℤ × ℤ) : Measurable fun z : ℝ × Space => expanded θD θZ c w v ι z.1 z.2 := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := squares_measurable hv ι
  have gD : Measurable fun z : ℝ × Space => θD z.2 := hD.continuous.measurable.comp measurable_snd
  have gZ : Measurable fun z : ℝ × Space => θZ z.2 := hZ.continuous.measurable.comp measurable_snd
  have hD' : Measurable fun z : ℝ × Space => ModeWeights.secondDerivNorm θD z.2 :=
    (continuous_secondDerivNorm hD).measurable.comp measurable_snd
  have hZ' : Measurable fun z : ℝ × Space => ModeWeights.secondDerivNorm θZ z.2 :=
    (continuous_secondDerivNorm hZ).measurable.comp measurable_snd
  have gw : Measurable fun z : ℝ × Space => w z.2 := hwm.comp measurable_snd
  unfold expanded
  exact (((((gD.sub measurable_const).mul m3).add ((measurable_const.sub gD).mul m4)).add
    ((measurable_const.sub gZ).mul m2)).add (((gZ.sub hD').sub (measurable_const.mul gw)).mul m1)).sub
    (hZ'.mul m0)

theorem measurable_mainPos (c : ℝ) {w : Space → ℝ} (hwm : Measurable w) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) :
    Measurable fun z : ℝ × Space => mainPos c w v ι z.1 z.2 := by
  obtain ⟨m0, m1, m2, m3, m4⟩ := squares_measurable hv ι
  have gw : Measurable fun z : ℝ × Space => w z.2 := hwm.comp measurable_snd
  unfold mainPos
  exact (m4.add (measurable_const.mul m2)).add (measurable_const.mul (m3.add (gw.mul m1)))

def curlLinear : (Space →L[ℝ] Space) →ₗ[ℝ] Space where
  toFun := curlVec
  map_add' G K := by
    simp only [curlVec, ContinuousLinearMap.add_apply, PiLp.add_apply, mul_add, Finset.sum_add_distrib,
      add_smul]
  map_smul' a G := by
    simp only [curlVec, ContinuousLinearMap.smul_apply, PiLp.smul_apply, smul_eq_mul, RingHom.id_apply,
      Finset.smul_sum, smul_smul, Finset.mul_sum]
    congr 1
    funext i
    congr 1
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring

theorem curlLinear_apply (G : Space →L[ℝ] Space) : curlLinear G = curlVec G := rfl

theorem continuous_matSq {X : Type*} [TopologicalSpace X] {G : X → Space →L[ℝ] Space}
    (hG : Continuous G) : Continuous fun x => matSq (G x) :=
  continuous_finsetSum _ fun i _ => (hG.clm_apply continuous_const).norm.pow 2

theorem energy_fields_continuous {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    Continuous (fun z : ℝ × Space => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2)) ∧
      Continuous (fun z : ℝ × Space => ‖curlVec (fderiv ℝ (v z.1) z.2)‖ ^ 2) ∧
      Continuous (fun z : ℝ × Space => ‖secondDerivTrace (secondDerivField v z.1 z.2)‖ ^ 2) ∧
      Continuous (fun z : ℝ × Space => matSq (gradField v z.1 z.2)) := by
  obtain ⟨-, c1, c2⟩ := fields_continuous hv
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (hv.1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have hL : ContDiff ℝ 2 fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  have h3 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => curlVec (fderiv ℝ (v z.1) y))
      (g := fun z => z.2) (hL.comp (h1.comp (contDiff_fst.fst.prodMk contDiff_snd))) contDiff_snd
      (by norm_num)
  have hc : Continuous fun z : ℝ × Space => curlVec (fderiv ℝ (v z.1) z.2) :=
    hL.continuous.comp c1
  refine ⟨continuous_matSq h3.continuous, hc.norm.pow 2, ?_, continuous_matSq c1⟩
  exact (continuous_finsetSum _ fun j _ => (c2.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2

theorem energy_fields_support {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    ∃ R, ∀ σ y, R < ‖y‖ →
      matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) = 0 ∧
      ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 = 0 ∧ ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 = 0 ∧
      matSq (gradField v σ y) = 0 := by
  obtain ⟨R, hR⟩ := modes_support_aux hv
  have hopen : IsOpen {x : Space | R < ‖x‖} := isOpen_lt continuous_const continuous_norm
  refine ⟨R, fun σ y hy => ?_⟩
  obtain ⟨-, h1, h2⟩ := hR σ y hy
  have hev : (fun x => curlVec (fderiv ℝ (v σ) x)) =ᶠ[nhds y] fun _ => (0 : Space) :=
    Filter.eventually_of_mem (hopen.mem_nhds hy) fun x hx => by
      have := (hR σ x hx).2.1
      simp only [gradField] at this
      simp [this, curlVec]
  have h1' : fderiv ℝ (v σ) y = 0 := h1
  rw [hev.fderiv_eq, fderiv_const_apply]
  simp [matSq, h1', curlVec, h2, secondDerivTrace, gradField]

theorem lintegral_slice_le {f : ℝ → Space → ℝ} (hf : Continuous fun z : ℝ × Space => f z.1 z.2) {R : ℝ}
    (hR : ∀ σ y, R < ‖y‖ → f σ y = 0) : ∃ M : ℝ≥0∞, M < ⊤ ∧
      ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y) ≤ M := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_closedBall (0 : Space) R)).exists_bound_of_continuousOn
    hf.continuousOn
  refine ⟨ENNReal.ofReal C * volume (Metric.closedBall (0 : Space) R),
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top, fun σ hσ => ?_⟩
  rw [← lintegral_indicator_const measurableSet_closedBall]
  refine lintegral_mono fun y => ?_
  by_cases hy : y ∈ Metric.closedBall (0 : Space) R
  · rw [Set.indicator_of_mem hy]
    exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by
      simpa [Real.norm_eq_abs] using hC (σ, y) ⟨hσ, hy⟩))
  · have : R < ‖y‖ := by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy
    simp [hR σ y this]

theorem periodLIntegral_lt_top {f : ℝ → Space → ℝ} (hf : Continuous fun z : ℝ × Space => f z.1 z.2)
    {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → f σ y = 0) : periodLIntegral f < ⊤ := by
  obtain ⟨M, hM, hle⟩ := lintegral_slice_le hf hR
  unfold periodLIntegral
  calc (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (f σ y))
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, M := setLIntegral_mono' measurableSet_Icc hle
    _ = M * volume (Set.Icc (0 : ℝ) 1) := setLIntegral_const _ _
    _ < ⊤ := ENNReal.mul_lt_top hM (by simp)

theorem periodLIntegral_add {f g : ℝ → Space → ℝ} (hf0 : ∀ σ y, 0 ≤ f σ y) (hg0 : ∀ σ y, 0 ≤ g σ y)
    (hf : Measurable fun z : ℝ × Space => f z.1 z.2) :
    periodLIntegral (fun σ y => f σ y + g σ y) = periodLIntegral f + periodLIntegral g := by
  unfold periodLIntegral
  have my : ∀ σ, Measurable fun y => ENNReal.ofReal (f σ y) := fun σ =>
    ENNReal.measurable_ofReal.comp (hf.comp (measurable_const.prodMk measurable_id))
  rw [← lintegral_add_left (measurable_inner hf)]
  congr 1
  funext σ
  rw [← lintegral_add_left (my σ)]
  congr 1
  funext y
  exact ENNReal.ofReal_add (hf0 σ y) (hg0 σ y)

theorem integral_eq_periodLIntegral {f : ℝ → Space → ℝ} (hf : Continuous fun z : ℝ × Space => f z.1 z.2)
    (hf0 : ∀ σ y, 0 ≤ f σ y) {R : ℝ} (hR : ∀ σ y, R < ‖y‖ → f σ y = 0) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, f σ y = (periodLIntegral f).toReal := by
  obtain ⟨M, hM, hle⟩ := lintegral_slice_le hf hR
  have hy : ∀ σ, ∫ y, f σ y = (∫⁻ y, ENNReal.ofReal (f σ y)).toReal := fun σ =>
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (hf0 σ))
      (hf.comp (Continuous.prodMk_right σ)).aestronglyMeasurable
  simp_rw [hy]
  unfold periodLIntegral
  refine integral_toReal (measurable_inner hf.measurable).aemeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun σ hσ => (hle σ hσ).trans_lt hM)

theorem fields_finite {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) {w : Space → ℝ}
    (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w) :
    periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)) < ⊤ ∧
      periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) < ⊤ ∧
      periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) < ⊤ ∧
      periodLIntegral (fun σ y => w y * matSq (gradField v σ y)) < ⊤ := by
  obtain ⟨e1, e2, e3, e4⟩ := energy_fields_continuous hv
  obtain ⟨R, hR⟩ := energy_fields_support hv
  refine ⟨periodLIntegral_lt_top e1 fun σ y hy => (hR σ y hy).1,
    periodLIntegral_lt_top e2 fun σ y hy => (hR σ y hy).2.1,
    periodLIntegral_lt_top e3 fun σ y hy => (hR σ y hy).2.2.1, ?_⟩
  have h4 : periodLIntegral (fun σ y => B * matSq (gradField v σ y)) < ⊤ :=
    periodLIntegral_lt_top (R := R) (continuous_const.mul e4) fun σ y hy => by simp [(hR σ y hy).2.2.2]
  refine lt_of_le_of_lt ?_ h4
  unfold periodLIntegral
  refine lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_
  exact mul_le_mul_of_nonneg_right (hB y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem vorticityEnergy_eq {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    vorticityEnergy v =
      (periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y))).toReal
        + 1 / 4 * (periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)).toReal := by
  obtain ⟨e1, e2, -, -⟩ := energy_fields_continuous hv
  obtain ⟨R, hR⟩ := energy_fields_support hv
  obtain ⟨f1, f2, -, -⟩ := fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0) (fun _ => le_rfl)
    measurable_const
  have n1 : ∀ σ y, 0 ≤ matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y) := fun σ y =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have n2 : ∀ σ y, 0 ≤ (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2 := fun σ y => by positivity
  unfold vorticityEnergy
  rw [integral_eq_periodLIntegral (e1.add (continuous_const.mul e2)) (fun σ y => add_nonneg (n1 σ y) (n2 σ y))
      (R := R) (fun σ y hy => by simp [(hR σ y hy).1, (hR σ y hy).2.1]),
    periodLIntegral_add n1 n2 e1.measurable]
  have e : periodLIntegral (fun σ y => (1 / 4 : ℝ) * ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)
      = ENNReal.ofReal (1 / 4) * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext σ
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    congr 1
    funext y
    exact ENNReal.ofReal_mul (by norm_num)
  rw [e, ENNReal.toReal_add f1.ne (ENNReal.mul_ne_top ENNReal.ofReal_ne_top f2.ne), ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by norm_num)]

theorem weightedEnergy_eq {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) {w : Space → ℝ}
    (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w) :
    weightedEnergy w (gradField v) (secondDerivField v) =
      (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)).toReal
        + (periodLIntegral (fun σ y => w y * matSq (gradField v σ y))).toReal := by
  obtain ⟨-, -, e3, -⟩ := energy_fields_continuous hv
  obtain ⟨-, -, f3, f4⟩ := fields_finite hv hw0 hB hwm
  unfold weightedEnergy
  rw [periodLIntegral_add (f := fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
      (g := fun σ y => w y * matSq (gradField v σ y)) (fun σ y => sq_nonneg _)
      (fun σ y => mul_nonneg (hw0 y) (Finset.sum_nonneg fun _ _ => sq_nonneg _)) e3.measurable,
    ENNReal.toReal_add f3.ne f4.ne]

theorem space_eq_of_coords {x y : Space} (h0 : x 0 = y 0) (h1 : x 1 = y 1) (h2 : x 2 = y 2) : x = y := by
  ext i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem axialRot_smul_vec (φ a : ℝ) (x : Space) : axialRot φ (a • x) = a • axialRot φ x := by
  apply space_eq_of_coords
  · simp only [axialRot_coord_zero, PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [axialRot_coord_one, PiLp.smul_apply, smul_eq_mul]; ring
  · simp only [axialRot_coord_two, PiLp.smul_apply, smul_eq_mul]

theorem modeAverage_const_mul {β : Type*} (ι : ℤ × ℤ) (a : ℝ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι (fun τ φ b' => a * f τ φ b') b = (a : ℂ) * modeAverage ι f b := by
  simp only [modeAverage, Complex.ofReal_mul]
  rw [mul_left_comm]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext τ
  rw [← intervalIntegral.integral_const_mul]
  congr 1
  funext φ
  ring

theorem squareSum_weighted_grad (hP : ModeSquareSumHolds) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v)
    {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ} (hB : ∀ y, w y ≤ B) (hwm : Measurable w)
    (hwa : IsAxisymmetric w) :
    modeSum (fun ι σ y => w y * gradSq v ι σ y) =
      periodLIntegral (fun σ y => w y * matSq (gradField v σ y)) := by
  obtain ⟨-, c1, -⟩ := fields_continuous hv
  set G' : ℝ → Space → (Space →L[ℝ] Space) := fun σ y => Real.sqrt (w y) • gradField v σ y with hG'
  have hfr : ∀ σ y, matSq (G' σ y) = w y * matSq (gradField v σ y) := by
    intro σ y
    simp only [hG', matSq, ContinuousLinearMap.smul_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw0 y), Finset.mul_sum]
  have hfin : periodLIntegral (fun σ y => matSq (G' σ y)) < ⊤ := by
    simp_rw [hfr]
    exact (fields_finite hv hw0 hB hwm).2.2.2
  have hmeas : AEStronglyMeasurable (fun z : ℝ × Space => G' z.1 z.2) volume :=
    ((hwm.comp measurable_snd).sqrt.aestronglyMeasurable).smul c1.aestronglyMeasurable
  have hper : IsTimePeriodic G' := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.2.1 σ)
    simp only [hG', gradField, this]
  have key := hP.2.1 G' hmeas hper hfin
  have hcn : ∀ ι σ y, cnormSq (modeGrad ι G' σ y) = w y * gradSq v ι σ y := by
    intro ι σ y
    have hm : modeGrad ι G' σ y = fun ij => (Real.sqrt (w y) : ℂ) * modeGrad ι (gradField v) σ y ij := by
      funext ij
      unfold modeGrad
      rw [← modeAverage_const_mul]
      congr 1
      funext τ φ ij'
      simp only [hG', hwa φ y, ContinuousLinearMap.smul_apply, axialRot_smul_vec, PiLp.smul_apply, smul_eq_mul]
    rw [hm]
    simp only [gradSq, cnormSq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs,
      Real.sq_sqrt (hw0 y), Finset.mul_sum]
  unfold modeSum
  simp_rw [hfr, hcn] at key
  exact key.symm

theorem modeAverage_finset_sum {β κ : Type*} (ι : ℤ × ℤ) (s : Finset κ) (c : κ → ℝ) (g : κ → ℝ → ℝ → ℝ)
    (hg : ∀ k, Continuous fun p : ℝ × ℝ => g k p.1 p.2) (b : β) :
    modeAverage ι (fun τ φ (_ : β) => ∑ k ∈ s, c k * g k τ φ) b =
      ∑ k ∈ s, (c k : ℂ) * modeAverage ι (fun τ φ (_ : β) => g k τ φ) b := by
  unfold modeAverage
  have hEc : Continuous fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I)) := by fun_prop
  have hin : ∀ k τ, IntervalIntegrable (fun φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g k τ φ : ℝ) : ℂ)) volume 0 (2 * Real.pi) :=
    fun k τ => (Continuous.mul (hEc.comp (Continuous.prodMk_right τ))
      (Complex.continuous_ofReal.comp ((hg k).comp (Continuous.prodMk_right τ)))).intervalIntegrable _ _
  have hout : ∀ k, IntervalIntegrable (fun τ => ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g k τ φ : ℝ) : ℂ))
      volume 0 1 := fun k =>
    (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g k τ φ : ℝ) : ℂ))
      (hEc.mul (Complex.continuous_ofReal.comp (hg k))) 0 (2 * Real.pi)).intervalIntegrable _ _
  have step1 : ∀ τ, (∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((∑ k ∈ s, c k * g k τ φ : ℝ) : ℂ)) =
      ∑ k ∈ s, (c k : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g k τ φ : ℝ) : ℂ) := by
    intro τ
    have : (fun φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((∑ k ∈ s, c k * g k τ φ : ℝ) : ℂ)) =
        fun φ => ∑ k ∈ s, (c k : ℂ) * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g k τ φ : ℝ) : ℂ)) := by
      funext φ
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [this, intervalIntegral.integral_finsetSum fun k _ => (hin k τ).const_mul _]
    exact Finset.sum_congr rfl fun k _ => intervalIntegral.integral_const_mul _ _
  simp_rw [step1]
  rw [intervalIntegral.integral_finsetSum fun k _ => (hout k).const_mul _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_const_mul]
  ring

theorem axialRot_unit_zero (φ : ℝ) :
    axialRot φ (unitVector 0) = Real.cos φ • unitVector 0 + Real.sin φ • unitVector 1 := by
  apply space_eq_of_coords <;> simp [axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, unitVector]

theorem axialRot_unit_one (φ : ℝ) :
    axialRot φ (unitVector 1) = (-Real.sin φ) • unitVector 0 + Real.cos φ • unitVector 1 := by
  apply space_eq_of_coords <;> simp [axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, unitVector]

theorem axialRot_unit_two (φ : ℝ) : axialRot φ (unitVector 2) = unitVector 2 := by
  apply space_eq_of_coords <;> simp [axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, unitVector]

theorem curlVec_coord (K : Space →L[ℝ] Space) (m : Fin 3) :
    curlVec K m = ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol m j l * K (unitVector j) l := by
  simp [curlVec, unitVector, Fin.sum_univ_three]
  fin_cases m <;> simp

theorem curl_covariant_aux (K : Space →L[ℝ] Space) (φ : ℝ) :
    (axialRot (-φ) (curlVec K) 0 =
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol 0 j l * axialRot (-φ) (K (axialRot φ (unitVector j))) l) ∧
    (axialRot (-φ) (curlVec K) 1 =
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol 1 j l * axialRot (-φ) (K (axialRot φ (unitVector j))) l) ∧
    (axialRot (-φ) (curlVec K) 2 =
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol 2 j l * axialRot (-φ) (K (axialRot φ (unitVector j))) l) := by
  have hs := Real.sin_sq_add_cos_sq φ
  simp only [Fin.sum_univ_three, axialRot_unit_zero, axialRot_unit_one, axialRot_unit_two, map_add, map_smul,
    axialRot_coord_zero, axialRot_coord_one, axialRot_coord_two, Real.cos_neg, Real.sin_neg, curlVec_coord,
    PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  norm_num [alternatingSymbol]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination (K (unitVector 1) 0 - K (unitVector 0) 1) * hs

theorem curl_covariant (K : Space →L[ℝ] Space) (φ : ℝ) (i : Fin 3) :
    axialRot (-φ) (curlVec K) i =
      ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * axialRot (-φ) (K (axialRot φ (unitVector j))) l := by
  obtain ⟨h0, h1, h2⟩ := curl_covariant_aux K φ
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem squareSum_vort (hP : ModeSquareSumHolds) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    modeSum (vortSq v) = periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2) := by
  obtain ⟨-, c1, -⟩ := fields_continuous hv
  set X : ℝ → Space → Space := fun σ y => curlVec (fderiv ℝ (v σ) y) with hX
  have hL : Continuous fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).continuous
  have hXc : Continuous fun z : ℝ × Space => X z.1 z.2 := hL.comp c1
  have hper : IsTimePeriodic X := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.2.1 σ)
    simp only [hX, this]
  have hfin : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ :=
    (fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0) (fun _ => le_rfl) measurable_const).2.1
  have key := hP.1 X hXc.aestronglyMeasurable hper hfin
  have hmode : ∀ ι σ y, modeVel ι X σ y = curlOfGrad (modeGrad ι (gradField v) σ y) := by
    intro ι σ y
    funext i
    have hs : Continuous fun q : ℝ × ℝ => σ + q.1 := by fun_prop
    have hy : Continuous fun q : ℝ × ℝ => axialRot q.2 y :=
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have hg : ∀ p : Fin 3 × Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (gradField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector p.1))) p.2 :=
      fun p => (PiLp.continuous_apply 2 _ p.2).comp (continuous_axialRot_of
        (by fun_prop : Continuous fun q : ℝ × ℝ => -q.2) ((c1.comp (hs.prodMk hy)).clm_apply
          (continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const)))
    have e1 : modeVel ι X σ y i = modeAverage ι (fun τ φ (_ : Fin 3) =>
        ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), alternatingSymbol i p.1 p.2 *
          axialRot (-φ) (gradField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector p.1))) p.2) i := by
      simp only [modeVel, modeAverage]
      congr 1
      refine intervalIntegral.integral_congr fun τ _ => ?_
      refine intervalIntegral.integral_congr fun φ _ => ?_
      simp only [hX]
      rw [curl_covariant, ← Finset.univ_product_univ, Finset.sum_product]
      rfl
    rw [e1, modeAverage_finset_sum ι _ _ _ hg, ← Finset.univ_product_univ, Finset.sum_product]
    rfl
  have hcn : ∀ ι σ y, cnormSq (modeVel ι X σ y) = vortSq v ι σ y := fun ι σ y => by
    rw [hmode]; rfl
  unfold modeSum
  simp_rw [hcn] at key
  exact key.symm

theorem fderiv_curl_apply {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) (y u : Space) :
    fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y u = curlVec (secondDerivField v σ y u) := by
  have hvs : ContDiff ℝ ∞ (v σ) := hv.1.comp (contDiff_const.prodMk contDiff_id)
  have hd : DifferentiableAt ℝ (fderiv ℝ (v σ)) y :=
    ((hvs.fderiv_right (m := 1) (top_add_le 1)).differentiable (by norm_num)) y
  have e : (fun x => curlVec (fderiv ℝ (v σ) x)) = (LinearMap.toContinuousLinearMap curlLinear) ∘ fderiv ℝ (v σ) :=
    funext fun x => rfl
  rw [e, ((LinearMap.toContinuousLinearMap curlLinear).hasFDerivAt.comp y hd.hasFDerivAt).fderiv]
  rfl

theorem squareSum_vortGrad (hP : ModeSquareSumHolds) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    modeSum (vortGradSq v) =
      periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y)) := by
  obtain ⟨-, -, c2⟩ := fields_continuous hv
  have h1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => v z.1 y) (g := fun z => z.2)
      (hv.1.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (top_add_le 2)
  have hL : ContDiff ℝ 2 fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  have h3 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (fun x => curlVec (fderiv ℝ (v z.1) x)) z.2) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => curlVec (fderiv ℝ (v z.1) y))
      (g := fun z => z.2) (hL.comp (h1.comp (contDiff_fst.fst.prodMk contDiff_snd))) contDiff_snd
      (by norm_num)
  set G : ℝ → Space → (Space →L[ℝ] Space) := fun σ y => fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y
    with hG
  have hper : IsTimePeriodic G := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.2.1 σ)
    simp only [hG, this]
  have hfin : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤ :=
    (fields_finite hv (w := fun _ => 0) (fun _ => le_rfl) (B := 0) (fun _ => le_rfl) measurable_const).1
  have key := hP.2.1 G h3.continuous.aestronglyMeasurable hper hfin
  have hmode : ∀ ι σ y, modeGrad ι G σ y = curlGradOfSecondDeriv (modeSecondDeriv ι (secondDerivField v) σ y) := by
    intro ι σ y
    funext il
    have hs : Continuous fun q : ℝ × ℝ => σ + q.1 := by fun_prop
    have hy : Continuous fun q : ℝ × ℝ => axialRot q.2 y :=
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have he : ∀ j : Fin 3, Continuous fun q : ℝ × ℝ => axialRot q.2 (unitVector j) := fun j =>
      continuous_axialRot_of (by fun_prop : Continuous fun q : ℝ × ℝ => q.2) continuous_const
    have hg : ∀ p : Fin 3 × Fin 3, Continuous fun q : ℝ × ℝ =>
        axialRot (-q.2) (secondDerivField v (σ + q.1) (axialRot q.2 y) (axialRot q.2 (unitVector il.2))
          (axialRot q.2 (unitVector p.1))) p.2 :=
      fun p => (PiLp.continuous_apply 2 _ p.2).comp (continuous_axialRot_of
        (by fun_prop : Continuous fun q : ℝ × ℝ => -q.2)
        (((c2.comp (hs.prodMk hy)).clm_apply (he il.2)).clm_apply (he p.1)))
    have e1 : modeGrad ι G σ y il = modeAverage ι (fun τ φ (_ : Fin 3 × Fin 3) =>
        ∑ p ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), alternatingSymbol il.1 p.1 p.2 *
          axialRot (-φ) (secondDerivField v (σ + τ) (axialRot φ y) (axialRot φ (unitVector il.2))
            (axialRot φ (unitVector p.1))) p.2) il := by
      simp only [modeGrad, modeAverage]
      congr 1
      refine intervalIntegral.integral_congr fun τ _ => ?_
      refine intervalIntegral.integral_congr fun φ _ => ?_
      simp only [hG]
      rw [fderiv_curl_apply hv, curl_covariant, ← Finset.univ_product_univ, Finset.sum_product]
    rw [e1, modeAverage_finset_sum ι _ _ _ hg, ← Finset.univ_product_univ, Finset.sum_product]
    rfl
  have hcn : ∀ ι σ y, cnormSq (modeGrad ι G σ y) = vortGradSq v ι σ y := fun ι σ y => by
    rw [hmode]; rfl
  unfold modeSum
  simp_rw [hcn] at key
  exact key.symm

theorem slice_smooth {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) :
    ContDiff ℝ ∞ (v σ) ∧ ContDiff ℝ ∞ (fderiv ℝ (v σ)) ∧
      ∀ y a b, fderiv ℝ (fderiv ℝ (v σ)) y a b = fderiv ℝ (fderiv ℝ (v σ)) y b a := by
  have hf : ContDiff ℝ ∞ (v σ) := hv.1.comp (contDiff_const.prodMk contDiff_id)
  have hDf : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hf.fderiv_right (m := ∞) (by
    rw [← WithTop.coe_one, ← WithTop.coe_add, top_add])
  exact ⟨hf, hDf, fun y a b => hf.contDiffAt.isSymmSndFDerivAt (by simp; exact le_trans (le_of_eq (by norm_num)) (top_add_le 1)) a b⟩

theorem column_fderiv {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) (l : Fin 3) (y a : Space) :
    fderiv ℝ (fun x => fderiv ℝ (v σ) x (unitVector l)) y a = fderiv ℝ (fderiv ℝ (v σ)) y a (unitVector l) := by
  obtain ⟨-, hDf, -⟩ := slice_smooth hv σ
  rw [fderiv_clm_apply ((hDf.differentiable (by simp)) y) (differentiableAt_const _)]
  simp

theorem divergence_deriv_zero {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (σ : ℝ) (y a : Space) :
    ∑ i : Fin 3, (fderiv ℝ (fderiv ℝ (v σ)) y a (unitVector i)) i = 0 := by
  obtain ⟨-, hDf, -⟩ := slice_smooth hv σ
  have hd : ∀ i : Fin 3, HasFDerivAt (fun x => (fderiv ℝ (v σ) x (unitVector i)) i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp ((fderiv ℝ (fderiv ℝ (v σ)) y).flip (unitVector i))) y := by
    intro i
    have h1 : HasFDerivAt (fun x => fderiv ℝ (v σ) x (unitVector i))
        ((fderiv ℝ (fderiv ℝ (v σ)) y).flip (unitVector i)) y := by
      have := ((hDf.differentiable (by simp)) y).hasFDerivAt.clm_apply (hasFDerivAt_const (unitVector i) y)
      simpa using this
    exact (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y h1
  have hsum := HasFDerivAt.fun_sum (u := Finset.univ) fun i _ => hd i
  have hzero : (fun x => ∑ i : Fin 3, (fderiv ℝ (v σ) x (unitVector i)) i) = fun _ => 0 :=
    funext fun x => hv.2.2.2 σ x
  rw [hzero] at hsum
  have := congrArg (fun L : Space →L[ℝ] ℝ => L a) ((hasFDerivAt_const (0 : ℝ) y).unique hsum)
  simpa using this.symm

theorem slice_secondDerivSq_eq (hI4 : CurlWeightIdentityHolds) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v)
    (σ : ℝ) :
    ∫⁻ y, ENNReal.ofReal (secondDerivSq (secondDerivField v σ y)) =
      ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
  obtain ⟨hf, hDf, hsym⟩ := slice_smooth hv σ
  obtain ⟨R, hR⟩ := modes_support_aux hv
  set H : Space → Space →L[ℝ] Space →L[ℝ] Space := fun y => fderiv ℝ (fderiv ℝ (v σ)) y with hHdef
  have hH : ∀ y, secondDerivField v σ y = H y := fun y => rfl
  have hs : ∀ y (a b c : Fin 3), H y (unitVector a) (unitVector b) c = H y (unitVector b) (unitVector a) c :=
    fun y a b c => by rw [hHdef]; simp only; rw [hsym]
  have hdz : ∀ y (m : Fin 3), ∑ i : Fin 3, H y (unitVector m) (unitVector i) i = 0 :=
    fun y m => divergence_deriv_zero hv σ y (unitVector m)
  have hL : ContDiff ℝ ∞ fun G : Space →L[ℝ] Space => curlVec G :=
    (LinearMap.toContinuousLinearMap curlLinear).contDiff
  have hgz : ∀ y, R < ‖y‖ → fderiv ℝ (v σ) y = 0 := fun y hy => (hR σ y hy).2.1
  have hcs : ∀ {u : Space → Space}, (∀ y, R < ‖y‖ → u y = 0) → HasCompactSupport u := fun hu =>
    HasCompactSupport.intro (isCompact_closedBall 0 R) fun y hy =>
      hu y (by simpa [Metric.mem_closedBall, dist_zero_right, not_le] using hy)
  set u : Fin 3 → Space → Space := fun l x => fderiv ℝ (v σ) x (unitVector l) with hudef
  set om : Space → Space := fun x => curlVec (fderiv ℝ (v σ) x) with homdef
  have hu_d : ∀ l y a, fderiv ℝ (u l) y a = H y a (unitVector l) := fun l y a => column_fderiv hv σ l y a
  have hom_d : ∀ y a, fderiv ℝ om y a = curlVec (H y a) := fun y a => fderiv_curl_apply hv σ y a
  have hu_cd : ∀ l, ContDiff ℝ ∞ (u l) := fun l => hDf.clm_apply contDiff_const
  have hom_cd : ContDiff ℝ ∞ om := hL.comp hDf
  have hu_s : ∀ l, HasCompactSupport (u l) := fun l => hcs fun y hy => by
    simp only [hudef, hgz y hy, ContinuousLinearMap.zero_apply]
  have hom_s : HasCompactSupport om := hcs fun y hy => by
    simp [homdef, hgz y hy, curlVec]
  have hu_div : ∀ l y, divergenceAt (u l) y = 0 := by
    intro l y
    simp only [divergenceAt, hu_d]
    rw [← hdz y l]
    exact Finset.sum_congr rfl fun i _ => hs y i l i
  have hom_div : ∀ y, divergenceAt om y = 0 := by
    intro y
    simp only [divergenceAt, hom_d, curlVec_coord, Fin.sum_univ_three]
    norm_num [alternatingSymbol]
    linear_combination hs y 0 1 2 + hs y 1 2 0 + hs y 2 0 1
  have hone : ContDiff ℝ 2 (fun _ : Space => (1 : ℝ)) := contDiff_const
  have I4u := fun l => hI4 (fun _ => 1) (u l) hone (hu_cd l) (hu_s l) (hu_div l)
  have I4w := hI4 (fun _ => 1) om hone hom_cd hom_s hom_div
  have hz : ∀ y, fderiv ℝ (fun x => fderiv ℝ (fun _ : Space => (1 : ℝ)) x) y = 0 := fun y => by simp
  simp only [hz, ContinuousLinearMap.zero_apply, zero_mul, Finset.sum_const_zero, integral_zero, sub_zero,
    one_mul] at I4u I4w
  have hcol : ∀ l y, fderiv ℝ (u l) y = H y (unitVector l) := by
    intro l y
    ext a : 1
    rw [hu_d]
    simp only [hHdef]
    exact hsym y a (unitVector l)
  have hdz' : ∀ y (m : Fin 3), H y (unitVector m) (unitVector 0) 0 + H y (unitVector m) (unitVector 1) 1
      + H y (unitVector m) (unitVector 2) 2 = 0 := fun y m => by
    have := hdz y m
    rwa [Fin.sum_univ_three] at this
  have P1 : ∀ y, secondDerivSq (secondDerivField v σ y) = ∑ l : Fin 3, matSq (fderiv ℝ (u l) y) := by
    intro y
    simp only [secondDerivSq, matSq, hu_d, hH]
    exact Finset.sum_comm
  have P2 : ∀ y, ∑ l : Fin 3, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 = matSq (fderiv ℝ om y) := by
    intro y
    simp only [matSq, hom_d, hcol]
  have P3 : ∀ y, ‖curlVec (fderiv ℝ om y)‖ ^ 2 = ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    intro y
    have hv3 : curlVec (fderiv ℝ om y) = -secondDerivTrace (H y) := by
      apply space_eq_of_coords
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 0 + hs y 1 0 1 + hs y 2 0 2
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 1 + hs y 0 1 0 + hs y 2 1 2
      · simp only [curlVec_coord, hom_d, secondDerivTrace, Fin.sum_univ_three, PiLp.neg_apply, PiLp.add_apply]
        norm_num [alternatingSymbol]
        linear_combination hdz' y 2 + hs y 0 2 0 + hs y 1 2 1
    rw [hv3, norm_neg, hH]
  have hHz : ∀ y, R < ‖y‖ → H y = 0 := fun y hy => (hR σ y hy).2.2
  have i1 : ∀ l, Integrable fun y => matSq (fderiv ℝ (u l) y) := fun l =>
    integrable_of_vanish (R := R) (continuous_matSq ((hu_cd l).continuous_fderiv
      (by simp))) fun y hy => by
        simp [hcol, hHz y hy, matSq]
  have i2 : ∀ l, Integrable fun y => ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := fun l =>
    integrable_of_vanish (R := R) ((hL.continuous.comp ((hu_cd l).continuous_fderiv
      (by simp))).norm.pow 2) fun y hy => by
        simp [hcol, hHz y hy, curlVec]
  have i3 : Integrable fun y => ‖curlVec (fderiv ℝ om y)‖ ^ 2 :=
    integrable_of_vanish (R := R) ((hL.continuous.comp (hom_cd.continuous_fderiv
      (by simp))).norm.pow 2) fun y hy => by
        have : fderiv ℝ om y = 0 := by
          ext a : 1
          simp [hom_d, hHz y hy, curlVec]
        simp [this, curlVec]
  have chain : ∫ y, secondDerivSq (secondDerivField v σ y) = ∫ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    calc ∫ y, secondDerivSq (secondDerivField v σ y) = ∫ y, ∑ l : Fin 3, matSq (fderiv ℝ (u l) y) := by simp only [P1]
      _ = ∑ l : Fin 3, ∫ y, matSq (fderiv ℝ (u l) y) := integral_finset_sum _ fun l _ => i1 l
      _ = ∑ l : Fin 3, ∫ y, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := by simp only [I4u]
      _ = ∫ y, ∑ l : Fin 3, ‖curlVec (fderiv ℝ (u l) y)‖ ^ 2 := (integral_finset_sum _ fun l _ => i2 l).symm
      _ = ∫ y, matSq (fderiv ℝ om y) := by simp only [P2]
      _ = ∫ y, ‖curlVec (fderiv ℝ om y)‖ ^ 2 := I4w.symm
      _ = ∫ y, ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by simp only [P3]
  have j1 : Integrable fun y => secondDerivSq (secondDerivField v σ y) := by
    simp only [P1]; exact integrable_finset_sum _ fun l _ => i1 l
  have j2 : Integrable fun y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2 := by
    simp only [← P3]; exact i3
  rw [← ofReal_integral_eq_lintegral_ofReal j1 (ae_of_all _ fun y =>
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal j2 (ae_of_all _ fun y => sq_nonneg _), chain]

theorem squareSum_secondDeriv (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityHolds) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) :
    modeSum (secondDerivModeSq v) = periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
  obtain ⟨-, -, c2⟩ := fields_continuous hv
  obtain ⟨R, hR⟩ := modes_support_aux hv
  have hc : Continuous fun z : ℝ × Space => secondDerivSq (secondDerivField v z.1 z.2) :=
    continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ =>
      ((c2.clm_apply continuous_const).clm_apply continuous_const).norm.pow 2
  have hfin : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) < ⊤ :=
    periodLIntegral_lt_top (R := R) hc fun σ y hy => by simp [secondDerivSq, (hR σ y hy).2.2]
  have hper : IsTimePeriodic (secondDerivField v) := by
    intro σ y
    have : v (σ + 1) = v σ := funext (hv.2.1 σ)
    simp only [secondDerivField, this]
  have key := hP.2.2.1 (secondDerivField v) c2.aestronglyMeasurable hper hfin
  have e : periodLIntegral (fun σ y => secondDerivSq (secondDerivField v σ y)) =
      periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2) := by
    unfold periodLIntegral
    congr 1
    funext σ
    exact slice_secondDerivSq_eq hI4 hv σ
  rw [← e, key]
  rfl

theorem per_mode_integrable {θD θZ : Space → ℝ} (hD : ContDiff ℝ 2 θD)
    (hZ : ContDiff ℝ 2 θZ) (c : ℝ) {w : Space → ℝ} (hwm : Measurable w) (hw0 : ∀ y, 0 ≤ w y) {B : ℝ}
    (hB : ∀ y, w y ≤ B) {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) (σ : ℝ) :
    Integrable (baseMain c w v ι σ) ∧ Integrable (secondDerivDefect θD v ι σ) ∧
      Integrable (gradDefect θZ v ι σ) ∧ Integrable (mainPos c w v ι σ) ∧
      Integrable (mainNeg c w v ι σ) := by
  obtain ⟨R, hR⟩ := squares_support hv
  obtain ⟨c0, c1, c2, c3, c4⟩ := squares_continuous hv ι
  have k0 : Continuous fun y => velSq v ι σ y := by
    simpa only [Function.comp_def] using c0.comp (Continuous.prodMk_right σ)
  have k1 : Continuous fun y => gradSq v ι σ y := by
    simpa only [Function.comp_def] using c1.comp (Continuous.prodMk_right σ)
  have k2 : Continuous fun y => vortSq v ι σ y := by
    simpa only [Function.comp_def] using c2.comp (Continuous.prodMk_right σ)
  have k3 : Continuous fun y => secondDerivModeSq v ι σ y := by
    simpa only [Function.comp_def] using c3.comp (Continuous.prodMk_right σ)
  have k4 : Continuous fun y => vortGradSq v ι σ y := by
    simpa only [Function.comp_def] using c4.comp (Continuous.prodMk_right σ)
  have i0 : Integrable fun y => velSq v ι σ y := integrable_of_vanish k0 fun y hy => (hR ι σ y hy).1
  have i1 : Integrable fun y => gradSq v ι σ y := integrable_of_vanish k1 fun y hy => (hR ι σ y hy).2.1
  have i2 : Integrable fun y => vortSq v ι σ y :=
    integrable_of_vanish k2 fun y hy => (hR ι σ y hy).2.2.1
  have i3 : Integrable fun y => secondDerivModeSq v ι σ y :=
    integrable_of_vanish k3 fun y hy => (hR ι σ y hy).2.2.2.1
  have i4 : Integrable fun y => vortGradSq v ι σ y :=
    integrable_of_vanish k4 fun y hy => (hR ι σ y hy).2.2.2.2
  have iw : Integrable fun y => w y * gradSq v ι σ y :=
    i1.bdd_mul (c := B) hwm.aestronglyMeasurable (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 y)]; exact hB y)
  have iS : Integrable fun y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y := i3.add iw
  have iA : Integrable fun y => θD y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y) :=
    integrable_of_vanish (R := R) (hD.continuous.mul (k3.sub k4)) fun y hy => by
      simp only [(hR ι σ y hy).2.2.2.1, (hR ι σ y hy).2.2.2.2, sub_zero, mul_zero]
  have iA' : Integrable fun y => ModeWeights.secondDerivNorm θD y * gradSq v ι σ y :=
    integrable_of_vanish (R := R) ((continuous_secondDerivNorm hD).mul k1) fun y hy => by
      simp only [(hR ι σ y hy).2.1, mul_zero]
  have iC : Integrable fun y => θZ y * (gradSq v ι σ y - vortSq v ι σ y) :=
    integrable_of_vanish (R := R) (hZ.continuous.mul (k1.sub k2)) fun y hy => by
      simp only [(hR ι σ y hy).2.1, (hR ι σ y hy).2.2.1, sub_zero, mul_zero]
  have iC' : Integrable fun y => ModeWeights.secondDerivNorm θZ y * velSq v ι σ y :=
    integrable_of_vanish (R := R) ((continuous_secondDerivNorm hZ).mul k0) fun y hy => by
      simp only [(hR ι σ y hy).1, mul_zero]
  have iM : Integrable fun y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y :=
    i4.add (i2.const_mul (1 / 4))
  have j1 : Integrable fun y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y
      - c * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := iM.sub (iS.const_mul c)
  have j2 : Integrable fun y => θD y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y)
      - ModeWeights.secondDerivNorm θD y * gradSq v ι σ y := iA.sub iA'
  have j3 : Integrable fun y => θZ y * (gradSq v ι σ y - vortSq v ι σ y)
      - ModeWeights.secondDerivNorm θZ y * velSq v ι σ y := iC.sub iC'
  have j4 : Integrable fun y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y
      + max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := iM.add (iS.const_mul _)
  have j5 : Integrable fun y => max c 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) :=
    iS.const_mul _
  exact ⟨j1, j2, j3, j4, j5⟩

theorem defect_parts_integrable {θ : Space → ℝ} (hθ : ContDiff ℝ 2 θ) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) (ι : ℤ × ℤ) (σ : ℝ) :
    Integrable (fun y => θ y * (secondDerivModeSq v ι σ y - vortGradSq v ι σ y)) ∧
      Integrable (fun y => ModeWeights.secondDerivNorm θ y * gradSq v ι σ y) ∧
      Integrable (fun y => θ y * (gradSq v ι σ y - vortSq v ι σ y)) ∧
      Integrable (fun y => ModeWeights.secondDerivNorm θ y * velSq v ι σ y) := by
  obtain ⟨R, hR⟩ := squares_support hv
  obtain ⟨c0, c1, c2, c3, c4⟩ := squares_continuous hv ι
  have k0 : Continuous fun y => velSq v ι σ y := by
    simpa only [Function.comp_def] using c0.comp (Continuous.prodMk_right σ)
  have k1 : Continuous fun y => gradSq v ι σ y := by
    simpa only [Function.comp_def] using c1.comp (Continuous.prodMk_right σ)
  have k2 : Continuous fun y => vortSq v ι σ y := by
    simpa only [Function.comp_def] using c2.comp (Continuous.prodMk_right σ)
  have k3 : Continuous fun y => secondDerivModeSq v ι σ y := by
    simpa only [Function.comp_def] using c3.comp (Continuous.prodMk_right σ)
  have k4 : Continuous fun y => vortGradSq v ι σ y := by
    simpa only [Function.comp_def] using c4.comp (Continuous.prodMk_right σ)
  refine ⟨integrable_of_vanish (R := R) (hθ.continuous.mul (k3.sub k4)) fun y hy => by
      simp only [(hR ι σ y hy).2.2.2.1, (hR ι σ y hy).2.2.2.2, sub_zero, mul_zero],
    integrable_of_vanish (R := R) ((continuous_secondDerivNorm hθ).mul k1) fun y hy => by
      simp only [(hR ι σ y hy).2.1, mul_zero],
    integrable_of_vanish (R := R) (hθ.continuous.mul (k1.sub k2)) fun y hy => by
      simp only [(hR ι σ y hy).2.1, (hR ι σ y hy).2.2.1, sub_zero, mul_zero],
    integrable_of_vanish (R := R) ((continuous_secondDerivNorm hθ).mul k0) fun y hy => by
      simp only [(hR ι σ y hy).1, mul_zero]⟩

theorem integral_le_of_pointwise {f g : Space → ℝ} (hg : Integrable g) (hg0 : ∀ y, 0 ≤ g y)
    (h : ∀ y, f y ≤ g y) : ∫ y, f y ≤ ∫ y, g y := by
  by_cases hf : Integrable f
  · exact integral_mono hf hg h
  · rw [integral_undef hf]
    exact integral_nonneg hg0

theorem modeSum_mainPos (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityHolds) (c : ℝ) {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ}
    (hB : ∀ y, w y ≤ B) (hwm : Measurable w) (hwa : IsAxisymmetric w) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) :
    modeSum (mainPos c w v) =
      periodLIntegral (fun σ y => matSq (fderiv ℝ (fun x => curlVec (fderiv ℝ (v σ) x)) y))
        + ENNReal.ofReal (1 / 4) * periodLIntegral (fun σ y => ‖curlVec (fderiv ℝ (v σ) y)‖ ^ 2)
        + ENNReal.ofReal (max (-c) 0) * (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
          + periodLIntegral (fun σ y => w y * matSq (gradField v σ y))) := by
  have nn := squares_nonneg v
  have mm := squares_measurable hv
  have e : mainPos c w v = fun ι σ y => (vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y)
      + max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := rfl
  rw [e, modeSum_add (F := fun ι σ y => vortGradSq v ι σ y + 1 / 4 * vortSq v ι σ y)
      (G := fun ι σ y => max (-c) 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y))
      (fun ι σ y => add_nonneg (nn ι σ y).2.2.2.2 (mul_nonneg (by norm_num) (nn ι σ y).2.2.1))
      (fun ι σ y => mul_nonneg (le_max_right _ _) (add_nonneg (nn ι σ y).2.2.2.1 (mul_nonneg (hw0 y) (nn ι σ y).2.1)))
      (fun ι => (mm ι).2.2.2.2.add (measurable_const.mul (mm ι).2.2.1)),
    modeSum_add (F := fun ι σ y => vortGradSq v ι σ y) (G := fun ι σ y => 1 / 4 * vortSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.2) (fun ι σ y => mul_nonneg (by norm_num) (nn ι σ y).2.2.1)
      (fun ι => (mm ι).2.2.2.2),
    modeSum_const_mul (F := fun ι σ y => vortSq v ι σ y) (by norm_num),
    modeSum_const_mul (F := fun ι σ y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) (le_max_right _ _),
    modeSum_add (F := fun ι σ y => secondDerivModeSq v ι σ y) (G := fun ι σ y => w y * gradSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.1) (fun ι σ y => mul_nonneg (hw0 y) (nn ι σ y).2.1)
      (fun ι => (mm ι).2.2.2.1)]
  rw [show (modeSum fun ι σ y => vortGradSq v ι σ y) = modeSum (vortGradSq v) from rfl,
    show (modeSum fun ι σ y => vortSq v ι σ y) = modeSum (vortSq v) from rfl,
    show (modeSum fun ι σ y => secondDerivModeSq v ι σ y) = modeSum (secondDerivModeSq v) from rfl,
    squareSum_vortGrad hP hv, squareSum_vort hP hv, squareSum_secondDeriv hP hI4 hv,
    squareSum_weighted_grad hP hv hw0 hB hwm hwa]

theorem modeSum_mainNeg (hP : ModeSquareSumHolds) (hI4 : CurlWeightIdentityHolds) (c : ℝ) {w : Space → ℝ} (hw0 : ∀ y, 0 ≤ w y) {B : ℝ}
    (hB : ∀ y, w y ≤ B) (hwm : Measurable w) (hwa : IsAxisymmetric w) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) :
    modeSum (mainNeg c w v) =
      ENNReal.ofReal (max c 0) * (periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField v σ y)‖ ^ 2)
          + periodLIntegral (fun σ y => w y * matSq (gradField v σ y))) := by
  have nn := squares_nonneg v
  have mm := squares_measurable hv
  have e : mainNeg c w v = fun ι σ y => max c 0 * (secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) := rfl
  rw [e, modeSum_const_mul (F := fun ι σ y => secondDerivModeSq v ι σ y + w y * gradSq v ι σ y) (le_max_right _ _),
    modeSum_add (F := fun ι σ y => secondDerivModeSq v ι σ y) (G := fun ι σ y => w y * gradSq v ι σ y)
      (fun ι σ y => (nn ι σ y).2.2.2.1) (fun ι σ y => mul_nonneg (hw0 y) (nn ι σ y).2.1)
      (fun ι => (mm ι).2.2.2.1),
    show (modeSum fun ι σ y => secondDerivModeSq v ι σ y) = modeSum (secondDerivModeSq v) from rfl,
    squareSum_secondDeriv hP hI4 hv, squareSum_weighted_grad hP hv hw0 hB hwm hwa]

end BaseDensityInternal

end Coercive

end Breakdown

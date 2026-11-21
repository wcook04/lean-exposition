import Breakdown.FracCert.StHeldParts

open scoped ContDiff ENNReal NNReal InnerProductSpace
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown.SteadyCert.Internal.SolenoidalSplit

abbrev L2F := Lp Space 2 (volume : Measure Space)

theorem fderiv_eq_inner (ψ : Space → ℝ) (y w : Space) :
    fderiv ℝ ψ y w = inner ℝ (gradientAt ψ y) w := by
  have hw : w = ∑ i : Fin 3, w i • unitVector i := by
    simpa [unitVector] using ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w).symm
  conv_lhs => rw [hw]
  simp [gradientAt, sum_inner, real_inner_smul_left, unitVector, EuclideanSpace.inner_single_left,
    map_sum, mul_comm]

theorem norm_fderiv_le (ψ : Space → ℝ) (y : Space) : ‖fderiv ℝ ψ y‖ ≤ ‖gradientAt ψ y‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun w => by
    rw [fderiv_eq_inner]; exact norm_inner_le_norm _ _

theorem test_one {φ : Space → ℝ} (hφ : IsTestScalar φ) : ContDiff ℝ 1 φ :=
  hφ.1.of_le (by exact_mod_cast le_top)

theorem test_diff {φ : Space → ℝ} (hφ : IsTestScalar φ) : Differentiable ℝ φ :=
  (test_one hφ).differentiable one_ne_zero

theorem continuous_grad {φ : Space → ℝ} (hφ : IsTestScalar φ) : Continuous (gradientAt φ) := by
  have hc : Continuous (fderiv ℝ φ) := (test_one hφ).continuous_fderiv one_ne_zero
  unfold gradientAt
  exact continuous_finsetSum _ fun i _ => (hc.clm_apply continuous_const).smul continuous_const

theorem support_grad {φ : Space → ℝ} (hφ : IsTestScalar φ) : HasCompactSupport (gradientAt φ) := by
  refine (hφ.2.fderiv (𝕜 := ℝ)).mono ?_
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro h
  apply hx
  simp [gradientAt, h]

theorem memLp_grad {φ : Space → ℝ} (hφ : IsTestScalar φ) (p : ℝ≥0∞) : MemLp (gradientAt φ) p volume :=
  (continuous_grad hφ).memLp_of_hasCompactSupport (support_grad hφ)

theorem memLp_test {φ : Space → ℝ} (hφ : IsTestScalar φ) (p : ℝ≥0∞) : MemLp φ p volume :=
  hφ.1.continuous.memLp_of_hasCompactSupport hφ.2

theorem test_zero : IsTestScalar (fun _ => (0 : ℝ)) := ⟨contDiff_const, HasCompactSupport.zero⟩

theorem test_add {φ ψ : Space → ℝ} (hφ : IsTestScalar φ) (hψ : IsTestScalar ψ) :
    IsTestScalar (fun y => φ y + ψ y) := ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩

theorem test_sub {φ ψ : Space → ℝ} (hφ : IsTestScalar φ) (hψ : IsTestScalar ψ) :
    IsTestScalar (fun y => φ y - ψ y) := ⟨hφ.1.sub hψ.1, hφ.2.sub hψ.2⟩

theorem test_mul (c : ℝ) {φ : Space → ℝ} (hφ : IsTestScalar φ) : IsTestScalar (fun y => c * φ y) :=
  ⟨contDiff_const.mul hφ.1, hφ.2.mul_left⟩

theorem test_comp (R : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    IsTestScalar (fun y => φ (R.symm y)) :=
  ⟨hφ.1.comp R.symm.toContinuousLinearEquiv.contDiff, hφ.2.comp_homeomorph R.symm.toHomeomorph⟩

theorem grad_zero (y : Space) : gradientAt (fun _ => (0 : ℝ)) y = 0 := by simp [gradientAt]

theorem grad_add {φ ψ : Space → ℝ} (hφ : IsTestScalar φ) (hψ : IsTestScalar ψ) (y : Space) :
    gradientAt (fun y => φ y + ψ y) y = gradientAt φ y + gradientAt ψ y := by
  have h : fderiv ℝ (fun y => φ y + ψ y) y = fderiv ℝ φ y + fderiv ℝ ψ y :=
    ((test_diff hφ y).hasFDerivAt.add (test_diff hψ y).hasFDerivAt).fderiv
  simp only [gradientAt, h, ContinuousLinearMap.add_apply, add_smul, Finset.sum_add_distrib]

theorem grad_sub {φ ψ : Space → ℝ} (hφ : IsTestScalar φ) (hψ : IsTestScalar ψ) (y : Space) :
    gradientAt (fun y => φ y - ψ y) y = gradientAt φ y - gradientAt ψ y := by
  have h : fderiv ℝ (fun y => φ y - ψ y) y = fderiv ℝ φ y - fderiv ℝ ψ y :=
    ((test_diff hφ y).hasFDerivAt.sub (test_diff hψ y).hasFDerivAt).fderiv
  simp only [gradientAt, h, ContinuousLinearMap.sub_apply, sub_smul, Finset.sum_sub_distrib]

theorem grad_mul (c : ℝ) {φ : Space → ℝ} (hφ : IsTestScalar φ) (y : Space) :
    gradientAt (fun y => c * φ y) y = c • gradientAt φ y := by
  simp [gradientAt, fderiv_const_mul (test_diff hφ y) c, smul_smul, Finset.smul_sum]

theorem grad_comp (R : Space ≃ₗᵢ[ℝ] Space) {φ : Space → ℝ} (hφ : IsTestScalar φ) (y : Space) :
    gradientAt (fun z => φ (R.symm z)) y = R (gradientAt φ (R.symm y)) := by
  refine ext_inner_right ℝ fun w => ?_
  rw [← fderiv_eq_inner]
  have h2 : HasFDerivAt (fun z => φ (R.symm z)) ((fderiv ℝ φ (R.symm y)).comp
      ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)) y :=
    (test_diff hφ (R.symm y)).hasFDerivAt.comp y (R.symm.toContinuousLinearEquiv).hasFDerivAt
  rw [h2.fderiv]
  change fderiv ℝ φ (R.symm y) (R.symm w) = _
  rw [fderiv_eq_inner, ← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply]


def grads : Submodule ℝ L2F where
  carrier := {g | ∃ φ : Space → ℝ, IsTestScalar φ ∧ (g : Space → Space) =ᵐ[volume] gradientAt φ}
  add_mem' := by
    rintro a b ⟨φ, hφ, ha⟩ ⟨ψ, hψ, hb⟩
    refine ⟨fun y => φ y + ψ y, test_add hφ hψ, ?_⟩
    filter_upwards [Lp.coeFn_add a b, ha, hb] with y h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, grad_add hφ hψ]
  zero_mem' := by
    refine ⟨fun _ => 0, test_zero, ?_⟩
    filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with y h
    rw [h, grad_zero]
    rfl
  smul_mem' := by
    rintro c a ⟨φ, hφ, ha⟩
    refine ⟨fun y => c * φ y, test_mul c hφ, ?_⟩
    filter_upwards [Lp.coeFn_smul c a, ha] with y h1 h2
    rw [h1, Pi.smul_apply, h2, grad_mul c hφ]

def gradClosure : Submodule ℝ L2F := grads.topologicalClosure

scoped instance completeClosure : CompleteSpace gradClosure :=
  (Submodule.isClosed_topologicalClosure grads).completeSpace_coe

theorem toLp_mem {φ : Space → ℝ} (hφ : IsTestScalar φ) : (memLp_grad hφ 2).toLp _ ∈ gradClosure :=
  Submodule.le_topologicalClosure _ ⟨φ, hφ, MemLp.coeFn_toLp _⟩

theorem inner_toLp {φ : Space → ℝ} (hφ : IsTestScalar φ) (z : L2F) :
    inner ℝ z ((memLp_grad hφ 2).toLp _) = ∫ y, inner ℝ (z y) (gradientAt φ y) := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_grad hφ 2)] with y h
  rw [h]

theorem solenoidal_of_mem {z : L2F} (hz : z ∈ gradClosureᗮ) : IsSolenoidalL2 z := by
  refine ⟨Lp.memLp z, fun φ hφ => ?_⟩
  rw [← inner_toLp hφ]
  exact Submodule.inner_left_of_mem_orthogonal (toLp_mem hφ) hz

theorem mem_orth_of {w : L2F} (h : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, inner ℝ (w y) (gradientAt φ y) = 0) :
    w ∈ gradClosureᗮ := by
  have hle : gradClosure ≤ (ℝ ∙ w)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rintro g ⟨φ, hφ, hg⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hgt : g = (memLp_grad hφ 2).toLp _ := by
      refine Lp.ext ?_
      filter_upwards [hg, MemLp.coeFn_toLp (memLp_grad hφ 2)] with y h1 h2
      rw [h1, h2]
    rw [hgt, real_inner_comm, inner_toLp hφ]
    exact h φ hφ
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact (Submodule.mem_orthogonal_singleton_iff_inner_left).1 (hle hu)

scoped instance factSix : Fact ((1 : ℝ≥0∞) ≤ 6) := ⟨by norm_num⟩

scoped instance tripleSix : ENNReal.HolderTriple (6 / 5 : ℝ≥0∞) 6 1 := by
  rw [ENNReal.holderTriple_iff, ENNReal.inv_div (by simp) (by simp), inv_one]
  have h : (5 : ℝ≥0∞) / 6 + 6⁻¹ = (5 + 1) / 6 := by rw [← one_div, ENNReal.div_add_div_same]
  rw [h, show (5 : ℝ≥0∞) + 1 = 6 by norm_num]
  exact ENNReal.div_self (by norm_num) (by norm_num)

theorem potential_bound : ∃ C : ℝ≥0, ∀ φ : Space → ℝ, IsTestScalar φ →
    eLpNorm φ 6 volume ≤ C * eLpNorm (gradientAt φ) 2 volume := by
  refine ⟨SNormLESNormFDerivOfEqConst ℝ (volume : Measure Space) 2, fun φ hφ => ?_⟩
  have hfin : Module.finrank ℝ Space = 3 := finrank_euclideanSpace_fin
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq (F := ℝ) (volume : Measure Space) (test_one hφ) hφ.2
    (p := 2) (p' := 6) (by norm_num) (by rw [hfin]; norm_num) (by rw [hfin]; norm_num)
  have h6 : (((6 : ℝ≥0)) : ℝ≥0∞) = 6 := rfl
  have h2 : (((2 : ℝ≥0)) : ℝ≥0∞) = 2 := rfl
  rw [h6, h2] at h
  refine h.trans (mul_le_mul' (le_of_eq rfl) (eLpNorm_mono fun y => norm_fderiv_le φ y))

theorem gradient_of_mem {Q : L2F} (hQ : Q ∈ gradClosure) : IsGradientField Q := by
  obtain ⟨C, hC⟩ := potential_bound
  have hcl : Q ∈ closure (grads : Set L2F) := by
    rw [← Submodule.topologicalClosure_coe]; exact hQ
  obtain ⟨g, hgm, hgQ⟩ := mem_closure_iff_seq_limit.1 hcl
  choose φ hφ hgφ using hgm
  let P : ℕ → Lp ℝ 6 (volume : Measure Space) := fun n => (memLp_test (hφ n) 6).toLp _
  have hedist : ∀ n k, edist (P n) (P k) ≤ C * edist (g n) (g k) := by
    intro n k
    rw [Lp.edist_toLp_toLp, Lp.edist_def]
    have h1 := hC _ (test_sub (hφ n) (hφ k))
    refine h1.trans (le_of_eq ?_)
    congr 1
    refine eLpNorm_congr_ae ?_
    filter_upwards [hgφ n, hgφ k] with y h1 h2
    rw [grad_sub (hφ n) (hφ k), Pi.sub_apply, h1, h2]
  have hcau : CauchySeq P := by
    have hg := EMetric.cauchySeq_iff.1 hgQ.cauchySeq
    rw [EMetric.cauchySeq_iff]
    intro ε hε
    have hC0 : ((C : ℝ≥0∞) + 1) ≠ 0 := by simp
    have hCt : ((C : ℝ≥0∞) + 1) ≠ ⊤ := by simp
    obtain ⟨N, hN⟩ := hg (ε / ((C : ℝ≥0∞) + 1)) (ENNReal.div_pos hε.ne' hCt)
    refine ⟨N, fun m hm n hn => ?_⟩
    calc edist (P m) (P n) ≤ C * edist (g m) (g n) := hedist m n
      _ ≤ ((C : ℝ≥0∞) + 1) * edist (g m) (g n) := by gcongr; exact le_self_add
      _ < ((C : ℝ≥0∞) + 1) * (ε / ((C : ℝ≥0∞) + 1)) := by
          rw [mul_comm _ (edist _ _), mul_comm _ (ε / _)]
          exact ENNReal.mul_lt_mul_left hC0 hCt (hN m hm n hn)
      _ = ε := ENNReal.mul_div_cancel hC0 hCt
  obtain ⟨qL, hqL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨qL, ?_, ?_, Lp.aestronglyMeasurable Q, ?_⟩
  · intro K hK
    have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hK.measure_lt_top.ne
    have h6 : MemLp (qL : Space → ℝ) 6 (volume.restrict K) := (Lp.memLp qL).restrict K
    have h2 : MemLp (qL : Space → ℝ) 2 (volume.restrict K) := h6.mono_exponent (by norm_num)
    exact (memLp_two_iff_integrable_sq h2.1).1 h2
  · intro K _
    exact ((Lp.memLp Q).integrable_norm_pow two_ne_zero).integrableOn
  · intro ψ hψ j
    have hψc : Continuous (fun y => fderiv ℝ ψ y (unitVector j)) :=
      ((test_one hψ).continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hψs : HasCompactSupport (fun y => fderiv ℝ ψ y (unitVector j)) :=
      (hψ.2.fderiv (𝕜 := ℝ)).mono fun y hy => by
        rw [Function.mem_support] at hy ⊢
        intro h; apply hy; simp [h]
    have hn : ∀ n, ∫ y, fderiv ℝ ψ y (unitVector j) * P n y =
        -∫ y, ψ y * inner ℝ (g n y) (unitVector j) := by
      intro n
      have hφn := hφ n
      have e1 : ∫ y, fderiv ℝ ψ y (unitVector j) * P n y = ∫ y, fderiv ℝ ψ y (unitVector j) * φ n y := by
        refine integral_congr_ae ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_test hφn 6)] with y h
        rw [h]
      have e2 : ∫ y, ψ y * inner ℝ (g n y) (unitVector j) = ∫ y, ψ y * fderiv ℝ (φ n) y (unitVector j) := by
        refine integral_congr_ae ?_
        filter_upwards [hgφ n] with y h
        rw [h, fderiv_eq_inner]
      have hφc : Continuous (fun y => fderiv ℝ (φ n) y (unitVector j)) :=
        ((test_one hφn).continuous_fderiv one_ne_zero).clm_apply continuous_const
      have ibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := ψ) (g := φ n)
        (v := unitVector j)
        ((hψc.mul hφn.1.continuous).integrable_of_hasCompactSupport hψs.mul_right)
        ((hψ.1.continuous.mul hφc).integrable_of_hasCompactSupport hψ.2.mul_right)
        ((hψ.1.continuous.mul hφn.1.continuous).integrable_of_hasCompactSupport hψ.2.mul_right)
        (fun y _ => test_diff hψ y) (fun y _ => test_diff hφn y)
      rw [e1, e2, ibp, neg_neg]
    have hw : MemLp (fun y => ψ y • unitVector j) 2 volume :=
      (hψ.1.continuous.smul continuous_const).memLp_of_hasCompactSupport hψ.2.smul_right
    have key : ∀ f : L2F, inner ℝ f (hw.toLp _) = ∫ y, ψ y * inner ℝ (f y) (unitVector j) := by
      intro f
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hw.coeFn_toLp] with y h
      rw [h, inner_smul_right]
    have hR : Tendsto (fun n => ∫ y, ψ y * inner ℝ (g n y) (unitVector j)) atTop
        (𝓝 (∫ y, ψ y * inner ℝ (Q y) (unitVector j))) := by
      simp only [← key]
      exact hgQ.inner tendsto_const_nhds
    have hh : MemLp (fun y => fderiv ℝ ψ y (unitVector j)) (6 / 5) volume :=
      hψc.memLp_of_hasCompactSupport hψs
    have hL : Tendsto (fun n => ∫ y, fderiv ℝ ψ y (unitVector j) * P n y) atTop
        (𝓝 (∫ y, fderiv ℝ ψ y (unitVector j) * qL y)) := by
      refine tendsto_integral_of_L1' _ (hh.integrable_mul (Lp.memLp qL)).1
        (Eventually.of_forall fun n => hh.integrable_mul (Lp.memLp (P n))) ?_
      have hb : ∀ n, eLpNorm ((fun y => fderiv ℝ ψ y (unitVector j) * P n y) -
          fun y => fderiv ℝ ψ y (unitVector j) * qL y) 1 volume ≤
          eLpNorm (fun y => fderiv ℝ ψ y (unitVector j)) (6 / 5) volume * edist (P n) qL := by
        intro n
        rw [Lp.edist_def]
        have e : ((fun y => fderiv ℝ ψ y (unitVector j) * P n y) -
            fun y => fderiv ℝ ψ y (unitVector j) * qL y) =
            (fun y => fderiv ℝ ψ y (unitVector j)) • (⇑(P n) - ⇑qL) := by
          funext y; simp [mul_sub]
        rw [e]
        exact eLpNorm_smul_le_mul_eLpNorm ((Lp.aestronglyMeasurable _).sub (Lp.aestronglyMeasurable _)) hh.1
      have ht : Tendsto (fun n => eLpNorm (fun y => fderiv ℝ ψ y (unitVector j)) (6 / 5) volume *
          edist (P n) qL) atTop (𝓝 0) := by
        have := ENNReal.Tendsto.const_mul (tendsto_iff_edist_tendsto_0.1 hqL) (Or.inr hh.eLpNorm_lt_top.ne)
        simpa using this
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hb
    have hR' := hR.neg
    simp only [← hn] at hR'
    exact tendsto_nhds_unique hL hR'

theorem turnStep_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem turnStep_smul (m : ℕ) (c : ℝ) (a : Space) : turnStep m (c • a) = c • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem turnStep_norm (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, turnStep, Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * Real.pi / m)

theorem mirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror]; ring

theorem mirror_smul (c : ℝ) (a : Space) : mirror (c • a) = c • mirror a := by
  ext i
  fin_cases i <;> simp [mirror]

theorem mirror_norm (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [Fin.sum_univ_three, mirror, Real.norm_eq_abs, sq_abs]

def turnIso (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := turnStep m, map_add' := turnStep_add m, map_smul' := turnStep_smul m,
      norm_map' := turnStep_norm m } rfl

def mirrorIso : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toFun := mirror, map_add' := mirror_add, map_smul' := mirror_smul, norm_map' := mirror_norm } rfl

theorem turnIso_coe (m : ℕ) : ⇑(turnIso m) = turnStep m := by
  unfold turnIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

theorem mirrorIso_coe : ⇑mirrorIso = mirror := by
  unfold mirrorIso
  rw [LinearIsometry.coe_toLinearIsometryEquiv]
  rfl

def act (R : Space ≃ₗᵢ[ℝ] Space) : L2F →L[ℝ] L2F :=
  (((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).compLpL 2 volume).comp
    (Lp.compMeasurePreservingₗᵢ ℝ R R.measurePreserving).toContinuousLinearMap

theorem act_ae (R : Space ≃ₗᵢ[ℝ] Space) (f : L2F) :
    (act R f : Space → Space) =ᵐ[volume] fun y => R.symm (f (R y)) := by
  have h1 := ContinuousLinearMap.coeFn_compLpL (μ := (volume : Measure Space)) (p := 2)
    ((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space)
    (Lp.compMeasurePreserving R R.measurePreserving f)
  have h2 := Lp.coeFn_compMeasurePreserving f R.measurePreserving
  filter_upwards [h1, h2] with y a b
  change ((((R.symm.toContinuousLinearEquiv : Space ≃L[ℝ] Space) : Space →L[ℝ] Space).compLpL 2 volume)
    (Lp.compMeasurePreserving R R.measurePreserving f) : Space → Space) y = _
  rw [a, b]
  rfl

theorem comp_ae (R : Space ≃ₗᵢ[ℝ] Space) {f g : Space → Space} (h : f =ᵐ[volume] g) :
    (fun y => f (R y)) =ᵐ[volume] fun y => g (R y) :=
  R.measurePreserving.quasiMeasurePreserving.ae_eq_comp h

theorem act_grads (R : Space ≃ₗᵢ[ℝ] Space) {g : L2F} (hg : g ∈ grads) : act R g ∈ grads := by
  obtain ⟨φ, hφ, h⟩ := hg
  refine ⟨fun z => φ (R.symm.symm z), test_comp R.symm hφ, ?_⟩
  filter_upwards [act_ae R g, comp_ae R h] with y a b
  rw [a, b, grad_comp R.symm hφ, LinearIsometryEquiv.symm_symm]

theorem act_closure (R : Space ≃ₗᵢ[ℝ] Space) {g : L2F} (hg : g ∈ gradClosure) : act R g ∈ gradClosure := by
  have hle : grads ≤ gradClosure.comap (act R).toLinearMap := fun x hx =>
    Submodule.le_topologicalClosure _ (act_grads R hx)
  have hcl : IsClosed ((gradClosure.comap (act R).toLinearMap : Submodule ℝ L2F) : Set L2F) :=
    (Submodule.isClosed_topologicalClosure grads).preimage (act R).continuous
  exact Submodule.topologicalClosure_minimal _ hle hcl hg

theorem act_orth (R : Space ≃ₗᵢ[ℝ] Space) {z : L2F} (hz : z ∈ gradClosureᗮ) : act R z ∈ gradClosureᗮ := by
  refine mem_orth_of fun φ hφ => ?_
  have hs := (solenoidal_of_mem hz).2 _ (test_comp R hφ)
  have e1 : ∫ y, inner ℝ (act R z y) (gradientAt φ y) =
      ∫ y, inner ℝ (z (R y)) (gradientAt (fun w => φ (R.symm w)) (R y)) := by
    refine integral_congr_ae ?_
    filter_upwards [act_ae R z] with y h
    rw [h, grad_comp R hφ, LinearIsometryEquiv.symm_apply_apply,
      ← R.inner_map_map (R.symm (z (R y))) (gradientAt φ y), LinearIsometryEquiv.apply_symm_apply]
  rw [e1, R.measurePreserving.integral_comp R.toHomeomorph.measurableEmbedding
    (fun x => inner ℝ (z x) (gradientAt (fun w => φ (R.symm w)) x))]
  exact hs

theorem act_fix (R : Space ≃ₗᵢ[ℝ] Space) {F : Space → Space} (hF : MemLp F 2 volume)
    (hc : ∀ᵐ y ∂volume, F (R y) = R (F y)) : act R (hF.toLp F) = hF.toLp F := by
  refine Lp.ext ?_
  filter_upwards [act_ae R (hF.toLp F), hF.coeFn_toLp, comp_ae R hF.coeFn_toLp, hc] with y a b c d
  rw [a, b, c, d, LinearIsometryEquiv.symm_apply_apply]

theorem fixed_part (R : Space ≃ₗᵢ[ℝ] Space) {F Qp Z : L2F} (hF : act R F = F) (hQ : Qp ∈ gradClosure)
    (hZ : Z ∈ gradClosureᗮ) (hs : F = Qp + Z) : act R Z = Z := by
  have h1 : Qp + Z = act R Qp + act R Z := by rw [← map_add, ← hs, hF]
  have hd : Z - act R Z ∈ gradClosure := by
    have e : Z - act R Z = act R Qp - Qp := by
      rw [sub_eq_sub_iff_add_eq_add, add_comm Z Qp, h1]
    rw [e]
    exact sub_mem (act_closure R hQ) hQ
  have hd' : Z - act R Z ∈ gradClosureᗮ := sub_mem hZ (act_orth R hZ)
  have h0 : Z - act R Z = 0 := inner_self_eq_zero.1 (Submodule.inner_right_of_mem_orthogonal hd hd')
  exact (sub_eq_zero.1 h0).symm

theorem class_part (R : Space ≃ₗᵢ[ℝ] Space) {F : Space → Space} (hF : MemLp F 2 volume)
    (hc : ∀ᵐ y ∂volume, F (R y) = R (F y)) {Qp Z : L2F} (hQ : Qp ∈ gradClosure)
    (hZ : Z ∈ gradClosureᗮ) (hs : hF.toLp F = Qp + Z) :
    ∀ᵐ y ∂volume, (Z : Space → Space) (R y) = R (Z y) := by
  have hfix := fixed_part R (act_fix R hF hc) hQ hZ hs
  have h := act_ae R Z
  rw [hfix] at h
  filter_upwards [h] with y hy
  rw [hy, LinearIsometryEquiv.apply_symm_apply]

theorem main : SolenoidalSplitStatement := by
  intro m F hF hc
  obtain ⟨Qp, hQ, Z, hZ, hs⟩ := Submodule.exists_add_mem_mem_orthogonal (K := gradClosure) (hF.toLp F)
  refine ⟨Z, Qp, solenoidal_of_mem hZ, ⟨?_, ?_⟩, gradient_of_mem hQ, Lp.memLp Qp, ?_⟩
  · have h := class_part (turnIso m) hF (by rw [turnIso_coe]; exact hc.1) hQ hZ hs
    rw [turnIso_coe] at h
    exact h
  · have h := class_part mirrorIso hF (by rw [mirrorIso_coe]; exact hc.2) hQ hZ hs
    rw [mirrorIso_coe] at h
    exact h
  · filter_upwards [hF.coeFn_toLp, Lp.coeFn_add Qp Z] with y a b
    rw [← a, hs, b, Pi.add_apply, add_comm]

end Breakdown.SteadyCert.Internal.SolenoidalSplit

namespace Breakdown.SteadyCert

theorem solenoidalSplit : SolenoidalSplitStatement := Internal.SolenoidalSplit.main

end Breakdown.SteadyCert


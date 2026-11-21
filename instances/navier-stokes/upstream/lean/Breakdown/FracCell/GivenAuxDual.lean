import Breakdown.FracCell.GivenAuxDualParts

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.GivenFields.TraceRegularInternal

open SteadyCert

theorem int_inner_two {X ψ : Space → Space} (hX : MemLp X 2 volume) (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) : Integrable (fun y => inner ℝ (X y) (ψ y)) := by
  have h1 : MemLp (fun y => ‖X y‖) 2 volume := hX.norm
  have h2 : MemLp (fun y => ‖ψ y‖) 2 volume :=
    (hψ.memLp_of_hasCompactSupport (p := 2) hc).norm
  have hprod : Integrable (fun y => ‖X y‖ * ‖ψ y‖) := h1.integrable_mul h2
  refine hprod.mono' (hX.aestronglyMeasurable.inner hψ.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun y => by
    simpa [Real.norm_eq_abs] using abs_real_inner_le_norm (X y) (ψ y))

theorem int_smul_two {X : Space → Space} {φ : Space → ℝ} (hX : MemLp X 2 volume) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable (fun y => φ y • X y) := by
  have h1 : MemLp (fun y => ‖X y‖) 2 volume := hX.norm
  have h2 : MemLp φ 2 volume := hφ.memLp_of_hasCompactSupport (p := 2) hc
  have hprod : Integrable (fun y => φ y * ‖X y‖) := h2.integrable_mul h1
  refine hprod.norm.mono' (hφ.aestronglyMeasurable.smul hX.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun y => by simp [norm_smul])

theorem int_inner_loc {L φ : Space → Space} (hL : LocallyIntegrable L volume) (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable (fun y => inner ℝ (L y) (φ y)) := by
  have hprod : Integrable (fun y => ‖φ y‖ • ‖L y‖) :=
    (hL.mono hL.aestronglyMeasurable.norm (Filter.Eventually.of_forall (fun y => by simp))).integrable_smul_left_of_hasCompactSupport hφ.norm hc.norm
  have hmeas : AEStronglyMeasurable L volume := hL.aestronglyMeasurable
  refine hprod.mono' (hmeas.inner hφ.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall (fun y => by
    have := abs_real_inner_le_norm (L y) (φ y)
    simp only [Real.norm_eq_abs, smul_eq_mul]
    linarith [mul_comm ‖L y‖ ‖φ y‖])

theorem test_deriv {φ : Space → ℝ} (hφ : IsTestScalar φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) ∧ HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := by
  refine ⟨(hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const, ?_⟩
  exact (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] ℝ => T (unitVector j)) (by simp)

theorem test_vec_deriv {φ : Space → Space} (hφ : IsTestVectorField φ) (j : Fin 3) :
    Continuous (fun y => fderiv ℝ φ y (unitVector j)) ∧ HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) := by
  refine ⟨(hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const, ?_⟩
  exact (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun T : Space →L[ℝ] Space => T (unitVector j)) (by simp)

theorem test_sumSecond {φ : Space → Space} (hφ : IsTestVectorField φ) :
    Continuous (fun y => -sumSecondPartialsAt φ y) ∧ HasCompactSupport (fun y => -sumSecondPartialsAt φ y) := by
  have hc : Continuous (iteratedFDeriv ℝ 2 φ) := hφ.1.continuous_iteratedFDeriv (by norm_cast)
  have hs : HasCompactSupport (iteratedFDeriv ℝ 2 φ) := hφ.2.iteratedFDeriv 2
  refine ⟨?_, ?_⟩
  · unfold sumSecondPartialsAt
    exact (continuous_finsetSum _ (fun i _ => (continuous_eval_const _).comp hc)).neg
  · unfold sumSecondPartialsAt
    refine HasCompactSupport.neg ?_
    refine (hs.comp_left (g := fun T : ContinuousMultilinearMap ℝ (fun _ : Fin 2 => Space) Space =>
      ∑ i : Fin 3, T ![unitVector i, unitVector i]) (by simp)).mono ?_
    intro y hy
    exact hy

theorem tr_zero : IsTraceRegular (fun _ : Space => (0 : Space)) := by
  refine ⟨MemLp.zero' , Filter.Eventually.of_forall (fun y => differentiableAt_const _), ?_, ?_, ?_⟩
  · intro φ hφ j
    simp
  · intro i
    simp
  · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
    · intro φ hφ
      simp
    · exact locallyIntegrable_zero
    · simp

theorem tr_add {X Y : Space → Space} (hX : IsTraceRegular X) (hY : IsTraceRegular Y) :
    IsTraceRegular (fun y => X y + Y y) := by
  have hae : ∀ᵐ y ∂volume, fderiv ℝ (fun y => X y + Y y) y = fderiv ℝ X y + fderiv ℝ Y y := by
    filter_upwards [hX.diff, hY.diff] with y h1 h2
    exact fderiv_add h1 h2
  refine ⟨hX.two.add hY.two, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hX.diff, hY.diff] with y h1 h2
    exact h1.add h2
  · intro φ hφ j
    obtain ⟨hdc, hds⟩ := test_deriv hφ j
    have e1 : ∫ y, (fderiv ℝ φ y (unitVector j)) • (X y + Y y) =
        (∫ y, (fderiv ℝ φ y (unitVector j)) • X y) + ∫ y, (fderiv ℝ φ y (unitVector j)) • Y y := by
      simp_rw [smul_add]
      exact integral_add (int_smul_two hX.two hdc hds) (int_smul_two hY.two hdc hds)
    have e2 : ∫ y, φ y • fderiv ℝ (fun y => X y + Y y) y (unitVector j) =
        (∫ y, φ y • fderiv ℝ X y (unitVector j)) + ∫ y, φ y • fderiv ℝ Y y (unitVector j) := by
      rw [← integral_add (int_smul_two (hX.gradTwo j) hφ.1.continuous hφ.2)
        (int_smul_two (hY.gradTwo j) hφ.1.continuous hφ.2)]
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hy, ContinuousLinearMap.add_apply, smul_add]
    rw [e1, e2, hX.grad φ hφ j, hY.grad φ hφ j]
    abel
  · intro i
    refine ((hX.gradTwo i).add (hY.gradTwo i)).ae_eq ?_
    filter_upwards [hae] with y hy
    rw [hy]
    rfl
  · obtain ⟨LX, hLX, hLXl, hLXw⟩ := hX.trace
    obtain ⟨LY, hLY, hLYl, hLYw⟩ := hY.trace
    refine ⟨fun y => LX y + LY y, ?_, hLXl.add hLYl, ?_⟩
    · intro φ hφ
      obtain ⟨hlc, hls⟩ := test_sumSecond hφ
      have e1 : ∫ y, inner ℝ (X y + Y y) (-sumSecondPartialsAt φ y) =
          (∫ y, inner ℝ (X y) (-sumSecondPartialsAt φ y)) + ∫ y, inner ℝ (Y y) (-sumSecondPartialsAt φ y) := by
        simp_rw [inner_add_left]
        exact integral_add (int_inner_two hX.two hlc hls) (int_inner_two hY.two hlc hls)
      have e2 : ∫ y, inner ℝ (LX y + LY y) (φ y) =
          (∫ y, inner ℝ (LX y) (φ y)) + ∫ y, inner ℝ (LY y) (φ y) := by
        simp_rw [inner_add_left]
        exact integral_add (int_inner_loc hLXl hφ.1.continuous hφ.2) (int_inner_loc hLYl hφ.1.continuous hφ.2)
      rw [e1, e2, hLX φ hφ, hLY φ hφ]
    · simp_rw [smul_add]
      exact hLXw.add hLYw

theorem tr_smul (c : ℝ) {X : Space → Space} (hX : IsTraceRegular X) :
    IsTraceRegular (fun y => c • X y) := by
  have hae : ∀ᵐ y ∂volume, fderiv ℝ (fun y => c • X y) y = c • fderiv ℝ X y := by
    filter_upwards [hX.diff] with y h1
    exact fderiv_const_smul h1 c
  refine ⟨hX.two.const_smul c, ?_, ?_, ?_, ?_⟩
  · filter_upwards [hX.diff] with y h1
    exact h1.const_smul c
  · intro φ hφ j
    have e1 : ∫ y, (fderiv ℝ φ y (unitVector j)) • (c • X y) =
        c • ∫ y, (fderiv ℝ φ y (unitVector j)) • X y := by
      rw [← integral_smul]
      simp_rw [smul_comm c]
    have e2 : ∫ y, φ y • fderiv ℝ (fun y => c • X y) y (unitVector j) =
        c • ∫ y, φ y • fderiv ℝ X y (unitVector j) := by
      rw [← integral_smul]
      refine integral_congr_ae ?_
      filter_upwards [hae] with y hy
      rw [hy, ContinuousLinearMap.smul_apply, smul_comm c]
    rw [e1, e2, hX.grad φ hφ j, smul_neg]
  · intro i
    refine ((hX.gradTwo i).const_smul c).ae_eq ?_
    filter_upwards [hae] with y hy
    rw [hy, ContinuousLinearMap.smul_apply]
    rfl
  · obtain ⟨LX, hLX, hLXl, hLXw⟩ := hX.trace
    refine ⟨fun y => c • LX y, ?_, hLXl.smul c, ?_⟩
    · intro φ hφ
      simp_rw [real_inner_smul_left]
      rw [integral_const_mul, integral_const_mul, hLX φ hφ]
    · simp_rw [smul_comm _ c]
      exact hLXw.const_smul c

theorem tr_sum {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (hf : ∀ i ∈ s, IsTraceRegular (f i)) :
    IsTraceRegular (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using tr_zero
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact tr_add (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem int_entry {Y : Space → (Space →L[ℝ] Space)} (hY : ∀ i : Fin 3, MemLp (fun y => Y y (unitVector i)) 2 volume)
    {φ : Space → Space} (hφ : IsTestVectorField φ) : Integrable (fun y => entryInner (fderiv ℝ φ y) (Y y)) := by
  unfold entryInner
  refine integrable_finsetSum _ (fun i _ => ?_)
  obtain ⟨hc, hs⟩ := test_vec_deriv hφ i
  exact (int_inner_two (hY i) hc hs).congr (Filter.Eventually.of_forall (fun y => real_inner_comm _ _))

theorem entry_add (G K K' : Space →L[ℝ] Space) : entryInner G (K + K') = entryInner G K + entryInner G K' := by
  unfold entryInner
  simp [inner_add_right, Finset.sum_add_distrib]

theorem entry_smul (G K : Space →L[ℝ] Space) (c : ℝ) : entryInner G (c • K) = c * entryInner G K := by
  unfold entryInner
  simp [real_inner_smul_right, Finset.mul_sum]

theorem fr_zero : IsRadialFluxRegular (fun _ : Space => (0 : Space →L[ℝ] Space)) := by
  refine ⟨aestronglyMeasurable_const, fun i => ?_, ?_⟩
  · simp
  · refine ⟨fun _ => 0, ?_, locallyIntegrable_zero, ?_⟩
    · intro φ hφ
      simp [entryInner]
    · simp

theorem fr_add {Y Z : Space → (Space →L[ℝ] Space)} (hY : IsRadialFluxRegular Y) (hZ : IsRadialFluxRegular Z) :
    IsRadialFluxRegular (fun y => Y y + Z y) := by
  refine ⟨hY.meas.add hZ.meas, fun i => ?_, ?_⟩
  · exact (hY.cols i).add (hZ.cols i)
  · obtain ⟨DY, hDY, hDYl, hDYw⟩ := hY.div
    obtain ⟨DZ, hDZ, hDZl, hDZw⟩ := hZ.div
    refine ⟨fun y => DY y + DZ y, ?_, hDYl.add hDZl, ?_⟩
    · intro φ hφ
      have e1 : ∫ y, entryInner (fderiv ℝ φ y) (Y y + Z y) =
          (∫ y, entryInner (fderiv ℝ φ y) (Y y)) + ∫ y, entryInner (fderiv ℝ φ y) (Z y) := by
        simp_rw [entry_add]
        exact integral_add (int_entry hY.cols hφ) (int_entry hZ.cols hφ)
      have e2 : ∫ y, inner ℝ (DY y + DZ y) (φ y) =
          (∫ y, inner ℝ (DY y) (φ y)) + ∫ y, inner ℝ (DZ y) (φ y) := by
        simp_rw [inner_add_left]
        exact integral_add (int_inner_loc hDYl hφ.1.continuous hφ.2) (int_inner_loc hDZl hφ.1.continuous hφ.2)
      rw [e1, e2, hDY φ hφ, hDZ φ hφ]
      ring
    · simp_rw [smul_add]
      exact hDYw.add hDZw

theorem fr_smul (c : ℝ) {Y : Space → (Space →L[ℝ] Space)} (hY : IsRadialFluxRegular Y) :
    IsRadialFluxRegular (fun y => c • Y y) := by
  refine ⟨hY.meas.const_smul c, fun i => ?_, ?_⟩
  · exact (hY.cols i).const_smul c
  · obtain ⟨DY, hDY, hDYl, hDYw⟩ := hY.div
    refine ⟨fun y => c • DY y, ?_, hDYl.smul c, ?_⟩
    · intro φ hφ
      simp_rw [entry_smul, real_inner_smul_left]
      rw [integral_const_mul, integral_const_mul, hDY φ hφ]
      ring
    · simp_rw [smul_comm _ c]
      exact hDYw.const_smul c

theorem fr_sum {ι : Type*} (s : Finset ι) (f : ι → Space → (Space →L[ℝ] Space))
    (hf : ∀ i ∈ s, IsRadialFluxRegular (f i)) : IsRadialFluxRegular (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using fr_zero
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact fr_add (hf a (Finset.mem_insert_self a s)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem single_smul (i : Fin 3) (c : ℝ) : EuclideanSpace.single i c = c • unitVector i := by
  ext l
  by_cases h : l = i
  · subst h
    simp [unitVector]
  · simp [unitVector, h]

theorem plane_re (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) :
    (atomPlane P X β y).re =
      (∑ j ∈ X.harmonics, ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re) +
      ∑ j ∈ X.harmonics.filter (fun j => 1 ≤ j), ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re := by
  simp only [atomPlane, mul_add, Finset.mul_sum, Complex.add_re, Complex.re_sum, one_mul]
  congr 1
  refine Finset.sum_congr rfl (fun j _ => ?_)
  simp [Complex.mul_re]

theorem plane_im (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) :
    (atomPlane P X β y).im =
      (∑ j ∈ X.harmonics, ((-Complex.I) * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re) +
      ∑ j ∈ X.harmonics.filter (fun j => 1 ≤ j), (Complex.I * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re := by
  simp only [atomPlane, mul_add, Finset.mul_sum, Complex.add_im, Complex.im_sum]
  congr 1
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Complex.mul_re, Complex.mul_im]
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    simp [Complex.mul_re, Complex.mul_im]

theorem height_re (P : ChartParams) (X : AtomData) (β : ℝ) (y : Space) :
    (atomHeight P X β y).re =
      ∑ j ∈ X.harmonics, ((((if j = 0 then 1 else 2 : ℝ)) : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 0 ((j : ℤ) * P.m) β (X.heightAmp j) y).re := by
  simp only [atomHeight, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← Complex.ofReal_mul]
  simp only [Complex.re_ofReal_mul]
  ring

theorem atom_eq (P : ChartParams) (X : AtomData) (β : ℝ) :
    atomOf P X β = fun y =>
      (((∑ j ∈ X.harmonics, ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
          atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re • unitVector 0) +
        ∑ j ∈ X.harmonics.filter (fun j => 1 ≤ j), ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
          atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re • unitVector 0) +
      ((∑ j ∈ X.harmonics, ((-Complex.I) * ((decayFactor P y : ℝ) : ℂ) *
          atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re • unitVector 1) +
        ∑ j ∈ X.harmonics.filter (fun j => 1 ≤ j), (Complex.I * ((decayFactor P y : ℝ) : ℂ) *
          atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re • unitVector 1)) +
      ∑ j ∈ X.harmonics, ((((if j = 0 then 1 else 2 : ℝ)) : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
        atomTerm P j 0 ((j : ℤ) * P.m) β (X.heightAmp j) y).re • unitVector 2 := by
  funext y
  rw [atomOf, ofComponents]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  rw [single_smul, single_smul, single_smul, plane_re, plane_im, height_re]
  simp only [add_smul, Finset.sum_smul]

theorem atom_reg (P : ChartParams) (hP : IsChartParams P) (X : AtomData) (hX : IsAtomData P X) (β : ℝ) :
    IsTraceRegular (atomOf P X β) := by
  rw [atom_eq]
  refine tr_add (tr_add (tr_add ?_ ?_) (tr_add ?_ ?_)) ?_
  · refine tr_sum _ (fun j y => ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re • unitVector 0) (fun j hj => ?_)
    exact atomTerm_traceRegular P hP j 1 _ β _ le_rfl (by simpa using hX.plus_shape j hj)
      (fun h => by subst h; simp) 1 0
  · refine tr_sum _ (fun j y => ((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re • unitVector 0) (fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact atomTerm_traceRegular P hP j 1 _ β _ le_rfl (by simpa using hX.minus_shape j hj1 hj2)
      (fun h => by omega) 1 0
  · refine tr_sum _ (fun j y => ((-Complex.I) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m + 1) β (X.plusAmp j) y).re • unitVector 1) (fun j hj => ?_)
    exact atomTerm_traceRegular P hP j 1 _ β _ le_rfl (by simpa using hX.plus_shape j hj)
      (fun h => by subst h; simp) (-Complex.I) 1
  · refine tr_sum _ (fun j y => (Complex.I * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m - 1) β (X.minusAmp j) y).re • unitVector 1) (fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact atomTerm_traceRegular P hP j 1 _ β _ le_rfl (by simpa using hX.minus_shape j hj1 hj2)
      (fun h => by omega) Complex.I 1
  · refine tr_sum _ (fun j y => ((((if j = 0 then 1 else 2 : ℝ)) : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 0 ((j : ℤ) * P.m) β (X.heightAmp j) y).re • unitVector 2) (fun j hj => ?_)
    exact atomTerm_traceRegular P hP j 0 _ β _ (by norm_num) (by simpa using hX.height_shape j hj)
      (fun h => by subst h; simp) _ 2

theorem sr_add (L : Space →L[ℝ] ℝ) (u v : Space) : L.smulRight (u + v) = L.smulRight u + L.smulRight v := by
  ext z
  simp [smul_add]

theorem sr_sum {ι : Type*} (L : Space →L[ℝ] ℝ) (s : Finset ι) (f : ι → Space) :
    L.smulRight (∑ i ∈ s, f i) = ∑ i ∈ s, L.smulRight (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    ext z
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sr_add, ih]

theorem flux_reg (P : ChartParams) (hP : IsChartParams P) (F : AtomData) (hF : IsFluxData F) (β : ℝ) :
    IsRadialFluxRegular (fluxOf P F β) := by
  unfold fluxOf
  rw [atom_eq]
  simp only [sr_add, sr_sum]
  refine fr_add (fr_add (fr_add ?_ ?_) (fr_add ?_ ?_)) ?_
  · refine fr_sum _ (fun j y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m + 1) β (F.plusAmp j) y).re • unitVector 0)) (fun j hj => ?_)
    exact fluxTerm_radialRegular P hP j 1 _ β _ (hF.plus_shape j hj) 1 0
  · refine fr_sum _ (fun j y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (((1 : ℂ) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m - 1) β (F.minusAmp j) y).re • unitVector 0)) (fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact fluxTerm_radialRegular P hP j 1 _ β _ (hF.minus_shape j hj1 hj2) 1 0
  · refine fr_sum _ (fun j y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (((-Complex.I) * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m + 1) β (F.plusAmp j) y).re • unitVector 1)) (fun j hj => ?_)
    exact fluxTerm_radialRegular P hP j 1 _ β _ (hF.plus_shape j hj) (-Complex.I) 1
  · refine fr_sum _ (fun j y => (innerSL ℝ (ofComponents (radialVec y))).smulRight ((Complex.I * ((decayFactor P y : ℝ) : ℂ) *
      atomTerm P j 1 ((j : ℤ) * P.m - 1) β (F.minusAmp j) y).re • unitVector 1)) (fun j hj => ?_)
    obtain ⟨hj1, hj2⟩ := Finset.mem_filter.1 hj
    exact fluxTerm_radialRegular P hP j 1 _ β _ (hF.minus_shape j hj1 hj2) Complex.I 1
  · refine fr_sum _ (fun j y => (innerSL ℝ (ofComponents (radialVec y))).smulRight (((((if j = 0 then 1 else 2 : ℝ)) : ℂ) *
      ((decayFactor P y : ℝ) : ℂ) * atomTerm P j 0 ((j : ℤ) * P.m) β (F.heightAmp j) y).re • unitVector 2)) (fun j hj => ?_)
    exact fluxTerm_radialRegular P hP j 0 _ β _ (hF.height_shape j hj) _ 2

theorem field_eq (P : ChartParams) (D : FieldData) (β : ℝ) :
    fieldOf P D β = fun y => ∑ n ∈ D.modes, ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re) := by
  funext y
  simp only [fieldOf, ofComponents, Finset.mul_sum, Complex.re_sum, single_smul, Finset.sum_smul,
    Finset.sum_add_distrib]

theorem field_reg (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D) (β : ℝ) :
    IsTraceRegular (fieldOf P D β) := by
  rw [field_eq]
  exact tr_sum _ (fun n y => ofComponents (fun i => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re))
    (fun n hn => fieldMode_traceRegular P hP D hD n hn β)

end Breakdown.CellCert.GivenFields.TraceRegularInternal

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem fderiv_meas (X : Space → Space) : AEStronglyMeasurable (fun y => fderiv ℝ X y) volume :=
  (measurable_fderiv ℝ X).aestronglyMeasurable

private theorem entry_int_of {G : Space → (Space →L[ℝ] Space)}
    (h : ∀ i : Fin 3, MemLp (fun y => G y (unitVector i)) 2 volume) : Integrable (fun y => entrySq (G y)) := by
  unfold entrySq
  refine integrable_finsetSum _ (fun i _ => ?_)
  exact (memLp_two_iff_integrable_sq_norm (h i).aestronglyMeasurable).1 (h i)

private theorem adjoint_reg (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) : IsTraceRegular (A.adjointField P j p) := by
  unfold AuxData.adjointField FieldFamily.eval
  exact TraceRegularInternal.tr_sum _ (fun γ y => multiPow γ p • fieldOf P ((A.adjointFamily j).coef γ) (A.phase p) y)
    (fun γ hγ => TraceRegularInternal.tr_smul _ (TraceRegularInternal.field_reg P hP _ (hA.adjoint_shape j γ hγ) _))

private theorem atoms_reg (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (F : AtomFamily k)
    (hF : ∀ γ ∈ F.indices, IsAtomData P (F.coef γ)) (phase : (Fin k → ℝ) → ℝ) (p : Fin k → ℝ) :
    IsTraceRegular (F.eval P phase p) := by
  unfold AtomFamily.eval
  exact TraceRegularInternal.tr_sum _ (fun γ y => multiPow γ p • atomOf P (F.coef γ) (phase p) y)
    (fun γ hγ => TraceRegularInternal.tr_smul _ (TraceRegularInternal.atom_reg P hP _ (hF γ hγ) _))

private theorem sharp_reg (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (ν : ℝ) (j : Fin k) (p : Fin k → ℝ) : IsTraceRegular (A.sharpField P ν j p) := by
  have hadj := adjoint_reg P hP A hA j p
  have hS := atoms_reg P hP (A.sharpSum j) (hA.sharp_shape j) A.phase p
  have h := TraceRegularInternal.tr_add (TraceRegularInternal.tr_add (TraceRegularInternal.tr_smul (A.sharpLead j) hadj)
    (TraceRegularInternal.tr_smul (-1) hS)) (TraceRegularInternal.tr_smul (-ν) hadj)
  have he : A.sharpField P ν j p = fun y => (A.sharpLead j • A.adjointField P j p y +
      (-1 : ℝ) • (A.sharpSum j).eval P A.phase p y) + (-ν) • A.adjointField P j p y := by
    funext y
    unfold AuxData.sharpField
    module
  rw [he]
  exact h

theorem adjointDualCore_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (ν : ℝ) (j : Fin k) (p : Fin k → ℝ) :
    IsWeakGradientOf (A.adjointField P j p) (fun y => fderiv ℝ (A.adjointField P j p) y) ∧
      (AEStronglyMeasurable (A.adjointField P j p) volume ∧
        AEStronglyMeasurable (fun y => fderiv ℝ (A.adjointField P j p) y) volume) ∧
      (∃ L : Space → Space, CellCert.Reduction.IsWeakNegTraceOf
          (fun y => ν • A.adjointField P j p y + A.sharpField P ν j p y) L ∧
        MemLp (fun y => ‖y‖ • L y) 2 volume) ∧
      MemLp (A.sharpField P ν j p) 2 volume ∧
      IsWeakGradientOf (A.sharpField P ν j p) (fun y => fderiv ℝ (A.sharpField P ν j p) y) ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.sharpField P ν j p) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.sharpField P ν j p) y)) := by
  have hadj := adjoint_reg P hP A hA j p
  have hsh := sharp_reg P hP A hA ν j p
  obtain ⟨L, hL, -, hLw⟩ := (TraceRegularInternal.tr_add (TraceRegularInternal.tr_smul ν hadj) hsh).trace
  exact ⟨hadj.grad, ⟨hadj.two.aestronglyMeasurable, fderiv_meas _⟩, ⟨L, hL, hLw⟩, hsh.two, hsh.grad,
    fderiv_meas _, entry_int_of hsh.gradTwo⟩

theorem dualFields_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) :
    (∃ L : Space → Space, CellCert.Reduction.IsWeakNegTraceOf (A.dualFieldOf P j p) L ∧
      MemLp (A.dualFieldOf P j p) 2 volume ∧ MemLp (fun y => ‖y‖ • L y) 2 volume ∧
      IsWeakGradientOf (A.dualFieldOf P j p) (fun y => fderiv ℝ (A.dualFieldOf P j p) y) ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.dualFieldOf P j p) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.dualFieldOf P j p) y))) ∧
    (∃ L : Space → Space, IsWeakGradientOf (A.potentialFieldOf P j p) (fun y => fderiv ℝ (A.potentialFieldOf P j p) y) ∧
      CellCert.Reduction.IsWeakNegTraceOf (A.potentialFieldOf P j p) L ∧
      MemLp (A.potentialFieldOf P j p) 2 volume ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.potentialFieldOf P j p) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.potentialFieldOf P j p) y)) ∧
      MemLp (fun y => ‖y‖ • L y) 2 volume) ∧
    (∃ Dv : Space → Space, CellCert.Reduction.IsWeakMatrixDivergenceOf (A.fluxFieldOf P j p) Dv ∧
      AEStronglyMeasurable (A.fluxFieldOf P j p) volume ∧ Integrable (fun y => entrySq (A.fluxFieldOf P j p y)) ∧
      MemLp (fun y => ‖y‖ • Dv y) 2 volume) := by
  have hD : IsTraceRegular (A.dualFieldOf P j p) := atoms_reg P hP (A.dualFamily j) (hA.dual_shape j) A.phase p
  have hT : IsTraceRegular (A.potentialFieldOf P j p) :=
    atoms_reg P hP (A.potentialFamily j) (hA.potential_shape j) A.phase p
  have hF : IsRadialFluxRegular (A.fluxFieldOf P j p) := by
    unfold AuxData.fluxFieldOf
    exact TraceRegularInternal.fr_sum _ (fun γ y => multiPow γ p • fluxOf P (A.fluxData j γ) (A.phase p) y)
      (fun γ hγ => TraceRegularInternal.fr_smul _ (TraceRegularInternal.flux_reg P hP _ (hA.flux_shape j γ hγ) _))
  obtain ⟨L1, hL1, -, hL1w⟩ := hD.trace
  obtain ⟨L2, hL2, -, hL2w⟩ := hT.trace
  obtain ⟨Dv, hDv, -, hDvw⟩ := hF.div
  exact ⟨⟨L1, hL1, hD.two, hL1w, hD.grad, fderiv_meas _, entry_int_of hD.gradTwo⟩,
    ⟨L2, hT.grad, hL2, hT.two, fderiv_meas _, entry_int_of hT.gradTwo, hL2w⟩,
    ⟨Dv, hDv, hF.meas, entry_int_of hF.cols, hDvw⟩⟩

end GivenFields

end CellCert

end Breakdown

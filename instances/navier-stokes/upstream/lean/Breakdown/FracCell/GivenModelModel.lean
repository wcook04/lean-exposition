import Breakdown.FracCell.GivenModelModelModes

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace Breakdown.FracInternal.GivenModelModelMain

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert Breakdown.FracInternal.GivenModelModelFrame

theorem symPart_cont : Continuous (symPart : (Space →L[ℝ] Space) → (Space →L[ℝ] Space)) := by
  unfold symPart
  exact (continuous_id.add (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Space) (F := Space)).continuous).const_smul
    (1 / 2 : ℝ)

theorem curlGradMatrix_cont :
    Continuous (curlGradMatrix : (Space →L[ℝ] Space →L[ℝ] Space) → (Space →L[ℝ] Space)) := by
  unfold curlGradMatrix
  fun_prop

theorem symPart_symm (A : Space →L[ℝ] Space) (u w : Space) :
    inner ℝ (symPart A u) w = inner ℝ u (symPart A w) := by
  simp only [symPart, smul_apply, add_apply, real_inner_smul_left,
    real_inner_smul_right, inner_add_left, inner_add_right, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_right]
  ring

theorem inner_unit (a b : Fin 3) : inner ℝ (unitVector a) (unitVector b) = if a = b then 1 else 0 := by
  simp [unitVector, EuclideanSpace.inner_single_left]

theorem curlGrad_entry (H : Space →L[ℝ] Space →L[ℝ] Space) (i : Fin 3) :
    entry (curlGradMatrix H) i i = ∑ b : Fin 3, ∑ q : Fin 3, permSign i b q * H (unitVector i) (unitVector b) q := by
  rw [entry_eq]
  simp only [curlGradMatrix, sum_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, sum_inner, real_inner_smul_left, inner_unit]
  simp [Finset.sum_ite_eq']

theorem curlGrad_trace (H : Space →L[ℝ] Space →L[ℝ] Space) (hH : ∀ u w, H u w = H w u) :
    ∑ i : Fin 3, entry (curlGradMatrix H) i i = 0 := by
  simp only [curlGrad_entry]
  simp [Fin.sum_univ_three, permSign]
  rw [hH (unitVector 1) (unitVector 0), hH (unitVector 2) (unitVector 0), hH (unitVector 2) (unitVector 1)]
  ring

theorem trace_add (A B : Space →L[ℝ] Space) :
    ∑ i : Fin 3, entry (A + B) i i = ∑ i : Fin 3, entry A i i + ∑ i : Fin 3, entry B i i := by
  simp [entry, Finset.sum_add_distrib]

theorem trace_zero : ∑ i : Fin 3, entry (0 : Space →L[ℝ] Space) i i = 0 := by
  simp [entry]

theorem harmonic_trace (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (hP : ∀ β j l, ∑ a : Fin 3, P β a a j l = 0) (y : Space) :
    ∑ a : Fin 3, harmonicValue m (fun β => P β a a) y = 0 := by
  unfold harmonicValue
  rw [← Complex.re_sum, Finset.sum_comm]
  have h0 : ∀ β, ∑ a : Fin 3, evalPoly (P β a a) (cylRadius y) |cylHeight y| = 0 := by
    intro β
    unfold evalPoly
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    simp [hP]
  rw [Finset.sum_eq_zero fun β _ => by rw [← Finset.sum_mul, ← Finset.mul_sum, h0 β, mul_zero, zero_mul]]
  simp

theorem sign_prod (y : Space) (a : Fin 3) : pseudoSign y a * vectorSign y a = if cylHeight y < 0 then -1 else 1 := by
  have h : vectorSign y a * vectorSign y a = 1 := by
    rw [← abs_mul_abs_self, vectorSign_abs, one_mul]
  unfold pseudoSign
  split_ifs
  · rw [neg_mul, h]
  · rw [one_mul]
    unfold vectorSign
    split_ifs with h'
    · exact absurd h'.1 ‹_›
    · rfl

theorem pseudoTensor_trace (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (hP : ∀ β j l, ∑ a : Fin 3, P β a a j l = 0) (y : Space) :
    ∑ i : Fin 3, entry (pseudoTensorOf m P y) i i = 0 := by
  unfold pseudoTensorOf
  rw [cartOp_trace]
  simp only [sign_prod]
  rw [← Finset.mul_sum, harmonic_trace m P hP y, mul_zero]

theorem tensor_symm (m : ℕ) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d)
    (hP : ∀ β a b, P β a b = P β b a) (y u w : Space) :
    inner ℝ (tensorOf m P y u) w = inner ℝ u (tensorOf m P y w) := by
  unfold tensorOf
  refine cartOp_symm _ _ (fun a b => ?_) u w
  have e : (fun β => P β a b) = fun β => P β b a := funext fun β => hP β a b
  simp only [e]
  ring

theorem norm_le_parts (y : Space) : ‖y‖ ≤ cylRadius y + |cylHeight y| := by
  have h0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
  have h1 : cylRadius y ^ 2 = y 0 ^ 2 + y 1 ^ 2 := Real.sq_sqrt (by positivity)
  have h2 : 0 ≤ cylRadius y + |cylHeight y| := add_nonneg h0 (abs_nonneg _)
  rw [EuclideanSpace.norm_eq, ← Real.sqrt_sq h2]
  refine Real.sqrt_le_sqrt ?_
  simp only [Real.norm_eq_abs, sq_abs, Fin.sum_univ_three, cylHeight]
  have h3 : |y 2| ^ 2 = y 2 ^ 2 := sq_abs _
  nlinarith [abs_nonneg (y 2)]

end Breakdown.FracInternal.GivenModelModelMain

namespace Breakdown.FracInternal.GivenModelModelMain

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert Breakdown.FracInternal.GivenModelModelFrame

theorem solid_bdd (K : CellBox) : Bornology.IsBounded K.solid := by
  refine (Metric.isBounded_closedBall (x := (0 : Space)) (r := |K.r₂| + |K.z₂|)).subset fun y hy => ?_
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (norm_le_parts y).trans (add_le_add ((hy.2.1).trans (le_abs_self _)) ((hy.2.2.2).trans (le_abs_self _)))

theorem region_fin (M : CellMesh) : volume M.region < ⊤ :=
  (Bornology.isBounded_iUnion.2 fun K => solid_bdd (M.box K)).measure_lt_top

theorem memLp_of_bd {E : Type*} [NormedAddCommGroup E] (s : Set Space) (hs : MeasurableSet s) (hfin : volume s < ⊤)
    (f : Space → E) (hf : AEStronglyMeasurable f volume) (C : ℝ) (hC : ∀ y, ‖f y‖ ≤ C) (h0 : ∀ y ∉ s, f y = 0)
    (p : ℝ≥0∞) : MemLp f p volume := by
  have e : f = s.indicator f := by
    funext y
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, h0 y hy]
  rw [e, memLp_indicator_iff_restrict hs]
  haveI : IsFiniteMeasure (volume.restrict s) := isFiniteMeasure_restrict.2 hfin.ne
  exact MemLp.of_bound hf.restrict C (ae_of_all _ hC)

theorem entrySq_cont : Continuous (entrySq : (Space →L[ℝ] Space) → ℝ) := by
  unfold entrySq
  fun_prop

theorem entrySq_le (G : Space →L[ℝ] Space) (C : ℝ) (hG : ‖G‖ ≤ C) : ‖entrySq G‖ ≤ 3 * C ^ 2 := by
  have h1 : ∀ i : Fin 3, ‖G (unitVector i)‖ ^ 2 ≤ C ^ 2 := fun i => by
    have : ‖G (unitVector i)‖ ≤ C := by
      refine (G.le_opNorm _).trans ?_
      simp [unitVector, EuclideanSpace.norm_single, hG]
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have h2 : 0 ≤ entrySq G := Finset.sum_nonneg fun i _ => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg h2]
  unfold entrySq
  rw [Fin.sum_univ_three]
  linarith [h1 0, h1 1, h1 2]

theorem entrySq_zero : entrySq (0 : Space →L[ℝ] Space) = 0 := by simp [entrySq]

theorem integrable_entrySq (M : CellMesh) (G : Space → (Space →L[ℝ] Space)) (hG : StronglyMeasurable G)
    (hb : ∃ C, ∀ y, ‖G y‖ ≤ C) (h0 : ∀ y ∉ M.region, G y = 0) : Integrable (fun y => entrySq (G y)) := by
  obtain ⟨C, hC⟩ := hb
  refine memLp_one_iff_integrable.1 (memLp_of_bd M.region (region_meas M) (region_fin M) _
    (entrySq_cont.comp_aestronglyMeasurable hG.aestronglyMeasurable) (3 * C ^ 2)
    (fun y => entrySq_le _ C (hC y)) (fun y hy => by simp only [h0 y hy, entrySq_zero]) 1)

end Breakdown.FracInternal.GivenModelModelMain

namespace Breakdown

namespace CellCert

namespace GivenModel

open SteadyCert CellAnalysis Breakdown.FracInternal.GivenModelModelFrame Breakdown.FracInternal.GivenModelModelMain
  Breakdown.FracInternal.GivenModelModelModes

theorem model_clauses {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hD : IsModelData D) (hI : IsModelInstance c M D) (hC : IsCentreRegular c) :
    (AEStronglyMeasurable c.modelVelocity volume ∧ AEStronglyMeasurable c.modelCurl volume ∧
      AEStronglyMeasurable c.modelStrain volume ∧ AEStronglyMeasurable c.modelCurlGrad volume) ∧
    (∃ C : ℝ, ∀ y ∈ c.cellRegion, ‖c.modelVelocity y‖ ≤ C ∧ ‖c.modelCurl y‖ ≤ C ∧
      ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C) ∧
    (∀ y ∉ c.cellRegion, c.modelVelocity y = 0 ∧ c.modelCurl y = 0) ∧
    (∀ y ∉ c.cellRegion, c.modelStrain y = c.centreStrain y ∧ c.modelCurlGrad y = c.centreCurlGrad y) ∧
    (∀ y (u w : Space), inner ℝ (c.modelStrain y u) w = inner ℝ u (c.modelStrain y w)) ∧
    (∀ y, ∑ i : Fin 3, entry (c.modelCurlGrad y) i i = 0) := by
  have hR := hI.region_eq
  have hV : c.modelVelocity = M.piecewise (fun K => vectorOf c.order (D.velocity K)) := hI.velocity_eq
  have hW : c.modelCurl = M.piecewise (fun K => pseudoOf c.order (D.curl K)) := hI.curl_eq
  have hS : ∀ y, c.modelStrain y = M.piecewise (fun K => tensorOf c.order (D.strain K)) y +
      Set.indicator M.regionᶜ (fun z => symPart (c.centreGrad z)) y := fun y => by rw [hI.strain_eq]; rfl
  have hG : ∀ y, c.modelCurlGrad y = M.piecewise (fun K => pseudoTensorOf c.order (D.curlGrad K)) y +
      Set.indicator M.regionᶜ (fun z => curlGradMatrix (c.centreSecond z)) y := fun y => by
    rw [hI.curlGrad_eq]; rfl
  have hgrad : Continuous c.centreGrad := hC.smooth.continuous_fderiv one_ne_zero
  have hcompl : MeasurableSet M.regionᶜ := (region_meas M).compl
  have hin : ∀ y ∈ c.cellRegion, y ∉ M.regionᶜ := fun y hy h => h (hR ▸ hy)
  have hout : ∀ y ∉ c.cellRegion, y ∉ M.region := fun y hy h => hy (hR ▸ h)
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hV]
    exact (piecewise_sm M _ fun K => vectorOf_sm _ _).aestronglyMeasurable
  · rw [hW]
    exact (piecewise_sm M _ fun K => pseudoOf_sm _ _).aestronglyMeasurable
  · have e : c.modelStrain = M.piecewise (fun K => tensorOf c.order (D.strain K)) +
        Set.indicator M.regionᶜ (fun z => symPart (c.centreGrad z)) := funext hS
    rw [e]
    exact (piecewise_sm M _ fun K => tensorOf_sm _ _).aestronglyMeasurable.add
      ((symPart_cont.comp hgrad).aestronglyMeasurable.indicator hcompl)
  · have e : c.modelCurlGrad = M.piecewise (fun K => pseudoTensorOf c.order (D.curlGrad K)) +
        Set.indicator M.regionᶜ (fun z => curlGradMatrix (c.centreSecond z)) := funext hG
    rw [e]
    exact (piecewise_sm M _ fun K => pseudoTensorOf_sm _ _).aestronglyMeasurable.add
      ((curlGradMatrix_cont.comp_aestronglyMeasurable hC.second_measurable).indicator hcompl)
  · obtain ⟨C1, h1⟩ := piecewise_bd M (fun K => vectorOf c.order (D.velocity K))
      fun K => vectorOf_bd c.order (D.velocity K) (M.box K)
    obtain ⟨C2, h2⟩ := piecewise_bd M (fun K => pseudoOf c.order (D.curl K))
      fun K => pseudoOf_bd c.order (D.curl K) (M.box K)
    obtain ⟨C3, h3⟩ := piecewise_bd M (fun K => tensorOf c.order (D.strain K))
      fun K => tensorOf_bd c.order (D.strain K) (M.box K)
    obtain ⟨C4, h4⟩ := piecewise_bd M (fun K => pseudoTensorOf c.order (D.curlGrad K))
      fun K => pseudoTensorOf_bd c.order (D.curlGrad K) (M.box K)
    refine ⟨max (max C1 C2) (max C3 C4), fun y hy => ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hV]
      exact (h1 y).trans (le_trans (le_max_left _ _) (le_max_left _ _))
    · rw [hW]
      exact (h2 y).trans (le_trans (le_max_right _ _) (le_max_left _ _))
    · rw [hS, Set.indicator_of_notMem (hin y hy), add_zero]
      exact (h3 y).trans (le_trans (le_max_left _ _) (le_max_right _ _))
    · rw [hG, Set.indicator_of_notMem (hin y hy), add_zero]
      exact (h4 y).trans (le_trans (le_max_right _ _) (le_max_right _ _))
  · intro y hy
    refine ⟨?_, ?_⟩
    · rw [hV]
      exact piecewise_out M _ (hout y hy)
    · rw [hW]
      exact piecewise_out M _ (hout y hy)
  · intro y hy
    have hy' : y ∈ M.regionᶜ := hout y hy
    refine ⟨?_, ?_⟩
    · rw [hS, piecewise_out M _ (hout y hy), zero_add, Set.indicator_of_mem hy']
      rfl
    · rw [hG, piecewise_out M _ (hout y hy), zero_add, Set.indicator_of_mem hy']
      rfl
  · intro y u w
    have h1 := piecewise_induct M (fun K => tensorOf c.order (D.strain K))
      (fun A : Space →L[ℝ] Space => ∀ u w, inner ℝ (A u) w = inner ℝ u (A w)) (fun u w => by simp)
      (fun A B hA hB u w => by simp only [add_apply, inner_add_left, inner_add_right, hA, hB]) y
      (fun K _ => tensor_symm _ _ (fun β a b => hD.strain_symm K β a b) y)
    have h2 : inner ℝ (Set.indicator M.regionᶜ (fun z => symPart (c.centreGrad z)) y u) w =
        inner ℝ u (Set.indicator M.regionᶜ (fun z => symPart (c.centreGrad z)) y w) := by
      by_cases hy : y ∈ M.regionᶜ
      · rw [Set.indicator_of_mem hy]
        exact symPart_symm _ u w
      · rw [Set.indicator_of_notMem hy]
        simp
    rw [hS, add_apply, add_apply, inner_add_left, inner_add_right, h1 u w, h2]
  · intro y
    rw [hG, trace_add]
    have h1 := piecewise_induct M (fun K => pseudoTensorOf c.order (D.curlGrad K))
      (fun A : Space →L[ℝ] Space => ∑ i : Fin 3, entry A i i = 0) trace_zero
      (fun A B hA hB => by rw [trace_add, hA, hB, add_zero]) y
      (fun K _ => pseudoTensor_trace _ _ (fun β j l => hD.curlGrad_traceFree K β j l) y)
    have h2 : ∑ i : Fin 3, entry (Set.indicator M.regionᶜ (fun z => curlGradMatrix (c.centreSecond z)) y) i i = 0 := by
      by_cases hy : y ∈ M.regionᶜ
      · rw [Set.indicator_of_mem hy]
        exact curlGrad_trace _ (hC.second_symm y)
      · rw [Set.indicator_of_notMem hy]
        exact trace_zero
    rw [h1, h2, add_zero]

theorem modelAux_clauses {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hI : IsModelInstance c M D) :
    (∀ i, MemLp (c.modelActuator i) 2 volume ∧ ∀ y ∉ c.cellRegion, c.modelActuator i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.modelActuatorGrad i) volume ∧
      Integrable (fun y => entrySq (c.modelActuatorGrad i y)) ∧ ∀ y ∉ c.cellRegion, c.modelActuatorGrad i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.modelPinField i) volume ∧
      Integrable (fun y => entrySq (c.modelPinField i y)) ∧ ∀ y ∉ c.cellRegion, c.modelPinField i y = 0) ∧
    (∀ i, AEStronglyMeasurable (c.pin i) volume ∧ Integrable (fun y => entrySq (c.pin i y))) ∧
    (∀ i, ∀ y ∉ c.cellRegion, c.pin i y = 0) := by
  have hR := hI.region_eq
  have hout : ∀ y ∉ c.cellRegion, y ∉ M.region := fun y hy h => hy (hR ▸ h)
  refine ⟨fun i => ⟨?_, ?_⟩, fun i => ⟨?_, ?_, ?_⟩, fun i => ⟨?_, ?_, ?_⟩, fun i => ⟨?_, ?_⟩, fun i y hy => ?_⟩
  · rw [hI.actuator_eq]
    show MemLp (M.piecewise (fun K => vectorOf c.order (D.actuator i K))) 2 volume
    obtain ⟨C, hC⟩ := piecewise_bd M (fun K => vectorOf c.order (D.actuator i K)) fun K => vectorOf_bd _ _ _
    exact memLp_of_bd M.region (region_meas M) (region_fin M) _
      (piecewise_sm M _ fun K => vectorOf_sm _ _).aestronglyMeasurable C hC (fun y hy => piecewise_out M _ hy) 2
  · intro y hy
    rw [hI.actuator_eq]
    exact piecewise_out M _ (hout y hy)
  · rw [hI.actuatorGrad_eq]
    exact (piecewise_sm M _ fun K => tensorOf_sm _ _).aestronglyMeasurable
  · rw [hI.actuatorGrad_eq]
    exact integrable_entrySq M _ (piecewise_sm M _ fun K => tensorOf_sm _ _)
      (piecewise_bd M (fun K => tensorOf c.order (D.actuatorGrad i K)) fun K => tensorOf_bd _ _ _)
      (fun y hy => piecewise_out M _ hy)
  · intro y hy
    rw [hI.actuatorGrad_eq]
    exact piecewise_out M _ (hout y hy)
  · rw [hI.pinField_eq]
    exact (piecewise_sm M _ fun K => tensorOf_sm _ _).aestronglyMeasurable
  · rw [hI.pinField_eq]
    exact integrable_entrySq M _ (piecewise_sm M _ fun K => tensorOf_sm _ _)
      (piecewise_bd M (fun K => tensorOf c.order (D.pinField i K)) fun K => tensorOf_bd _ _ _)
      (fun y hy => piecewise_out M _ hy)
  · intro y hy
    rw [hI.pinField_eq]
    exact piecewise_out M _ (hout y hy)
  · rw [hI.pin_eq]
    exact (piecewise_sm M _ fun K => tensorOf_sm _ _).aestronglyMeasurable
  · rw [hI.pin_eq]
    exact integrable_entrySq M _ (piecewise_sm M _ fun K => tensorOf_sm _ _)
      (piecewise_bd M (fun K => tensorOf c.order (D.pin i K)) fun K => tensorOf_bd _ _ _)
      (fun y hy => piecewise_out M _ hy)
  · rw [hI.pin_eq]
    exact piecewise_out M _ (hout y hy)

theorem modelMirror_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hI : IsModelInstance c M D) (K : CellBox) (hK : K.solid ⊆ c.cellRegion) :
    ∀ y ∈ K.solid, cylHeight y ≠ 0 → c.modelVelocity (mirror y) = mirror (c.modelVelocity y) ∧
      c.modelCurl (mirror y) = -mirror (c.modelCurl y) ∧
      (∀ u, c.modelStrain (mirror y) u = mirror (c.modelStrain y (mirror u))) ∧
      (∀ u, c.modelCurlGrad (mirror y) u = -mirror (c.modelCurlGrad y (mirror u))) ∧
      ∀ i, (∀ u, c.modelActuatorGrad i (mirror y) u = mirror (c.modelActuatorGrad i y (mirror u))) ∧
        (∀ u, c.modelPinField i (mirror y) u = mirror (c.modelPinField i y (mirror u))) := by
  have hR := hI.region_eq
  intro y hy hz
  have hyR : y ∈ M.region := hR ▸ hK hy
  have hmR : mirror y ∈ M.region := (mem_region_mirror M y).2 hyR
  have n1 : y ∉ M.regionᶜ := fun h => h hyR
  have n2 : mirror y ∉ M.regionᶜ := fun h => h hmR
  refine ⟨?_, ?_, fun u => ?_, fun u => ?_, fun i => ⟨fun u => ?_, fun u => ?_⟩⟩
  · rw [hI.velocity_eq]
    have := piecewise_mirror_vec M (fun K => vectorOf c.order (D.velocity K)) (fun K => vectorOf c.order (D.velocity K))
      1 y (fun K _ => vectorOf_mirror c.order (D.velocity K) hz)
    rw [one_smul] at this
    exact this
  · rw [hI.curl_eq]
    have := piecewise_mirror_vec M (fun K => pseudoOf c.order (D.curl K)) (fun K => pseudoOf c.order (D.curl K))
      (-1) y (fun K _ => pseudoOf_mirror c.order (D.curl K) hz)
    rw [neg_one_smul] at this
    exact this
  · rw [hI.strain_eq]
    simp only [ModelData.strainField, add_apply, Set.indicator_of_notMem n1, Set.indicator_of_notMem n2, zero_apply,
      add_zero]
    have := piecewise_mirror_op M (fun K => tensorOf c.order (D.strain K)) (fun K => tensorOf c.order (D.strain K))
      1 y (fun K _ u => tensorOf_mirror c.order (D.strain K) hz u) u
    rw [one_smul] at this
    exact this
  · rw [hI.curlGrad_eq]
    simp only [ModelData.curlGradField, add_apply, Set.indicator_of_notMem n1, Set.indicator_of_notMem n2, zero_apply,
      add_zero]
    have := piecewise_mirror_op M (fun K => pseudoTensorOf c.order (D.curlGrad K))
      (fun K => pseudoTensorOf c.order (D.curlGrad K)) (-1) y
      (fun K _ u => pseudoTensorOf_mirror c.order (D.curlGrad K) hz u) u
    rw [neg_one_smul] at this
    exact this
  · rw [hI.actuatorGrad_eq]
    have := piecewise_mirror_op M (fun K => tensorOf c.order (D.actuatorGrad i K))
      (fun K => tensorOf c.order (D.actuatorGrad i K)) 1 y
      (fun K _ u => tensorOf_mirror c.order (D.actuatorGrad i K) hz u) u
    rw [one_smul] at this
    exact this
  · rw [hI.pinField_eq]
    have := piecewise_mirror_op M (fun K => tensorOf c.order (D.pinField i K))
      (fun K => tensorOf c.order (D.pinField i K)) 1 y
      (fun K _ u => tensorOf_mirror c.order (D.pinField i K) hz u) u
    rw [one_smul] at this
    exact this

theorem linearModes_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (D : ModelData M k)
    (hM : IsCellMesh M) (hI : IsModelInstance c M D) (hm : 0 < c.order) (K : CellBox) (Y : Finset ℤ)
    (hY : ∀ β : Fin (D.harmonicCount + 1), (β : ℤ) ∈ Y ∧ -(β : ℤ) ∈ Y) :
    ∀ n ∉ Y, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ i,
      modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 = 0 ∧ modeMat c.order n (c.modelPinField i) p.1 p.2 = 0 := by
  intro n hn p _ hp i
  have hβ : ∀ β : Fin (D.harmonicCount + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n := fun β =>
    ⟨fun h => hn (h ▸ (hY β).1), fun h => hn (h ▸ (hY β).2)⟩
  refine ⟨?_, ?_⟩
  · rw [hI.actuatorGrad_eq]
    exact modes_zero M c.order hm (D.actuatorGrad i) p.1 p.2 hp n hβ
  · rw [hI.pinField_eq]
    exact modes_zero M c.order hm (D.pinField i) p.1 p.2 hp n hβ

end GivenModel

end CellCert

end Breakdown

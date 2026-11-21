import Breakdown.FracCert.HeldStateLimitBParts
import Breakdown.FracCert.HeldStateLimitBWeak
import Breakdown.FracCert.SecondSymbol
import Breakdown.FracCert.InverseSquare

open scoped ENNReal
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace WeakFieldLimit

def entryOp (h : Fin 3 → Fin 3 → Space → Space) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  ∑ j : Fin 3, ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space) (innerSL ℝ (unitVector j))
    (colOp (h j) y)

theorem entryOp_apply (h : Fin 3 → Fin 3 → Space → Space) (y : Space) (i j : Fin 3) :
    entryOp h y (unitVector i) (unitVector j) = h i j y := by
  have e : entryOp h y (unitVector i) = colOp (h i) y := by
    simp [entryOp, unitVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, ite_smul]
  rw [e, colOp_apply]

theorem entryOp_meas {h : Fin 3 → Fin 3 → Space → Space} (hh : ∀ i j, AEStronglyMeasurable (h i j) volume) :
    AEStronglyMeasurable (entryOp h) volume := by
  have e : entryOp h = fun y => ∑ j : Fin 3,
      ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space) (innerSL ℝ (unitVector j)) (colOp (h j) y) := rfl
  rw [e]
  refine (Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
    (ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space)
      (innerSL ℝ (unitVector j))).continuous.comp_aestronglyMeasurable (colOp_meas (hh j))).congr
    (ae_of_all _ fun y => ?_)
  simp [Finset.sum_apply]

def opOp (c : Fin 3 → Space → (Space →L[ℝ] Space)) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  ∑ j : Fin 3, ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space) (innerSL ℝ (unitVector j)) (c j y)

theorem opOp_apply (c : Fin 3 → Space → (Space →L[ℝ] Space)) (y : Space) (i : Fin 3) :
    opOp c y (unitVector i) = c i y := by
  simp [opOp, unitVector, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply, ite_smul]

theorem opOp_meas {c : Fin 3 → Space → (Space →L[ℝ] Space)} (hc : ∀ i, AEStronglyMeasurable (c i) volume) :
    AEStronglyMeasurable (opOp c) volume := by
  have e : opOp c = fun y => ∑ j : Fin 3,
      ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space) (innerSL ℝ (unitVector j)) (c j y) := rfl
  rw [e]
  refine (Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
    (ContinuousLinearMap.smulRightL ℝ Space (Space →L[ℝ] Space)
      (innerSL ℝ (unitVector j))).continuous.comp_aestronglyMeasurable (hc j)).congr
    (ae_of_all _ fun y => ?_)
  simp [Finset.sum_apply]

end WeakFieldLimit

open WeakFieldLimit LinearStateClosedInternal in
theorem heldLimitIdentify_of (hcl : HeldLimitClosureStatement) : HeldLimitIdentifyStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R B κ₀ hsol hsize hB hκ
  have hsec : ∀ n, IsSecondOrderField d.order (u n) (G n) (H n) := fun n => (hsol n).state.second
  have hwmin := hd.weightMin_pos
  have hE : ∀ n, d.energy (G n) (H n) ≤ R ^ 2 := by
    intro n
    have hE0 : 0 ≤ d.energy (G n) (H n) := energy_nonneg hwmin hd.weight_lower _ _
    have hsq : d.size (G n) (H n) (κ n) ^ 2 = d.energy (G n) (H n) + d.multiplierScale ^ 2 * ∑ i, κ n i ^ 2 := by
      unfold FracCertData.size sizeNorm
      rw [Real.sq_sqrt]
      · rfl
      · exact add_nonneg hE0 (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h2 : d.size (G n) (H n) (κ n) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsize n) 2
    have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ n i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  have hEG : ∀ n, ∫ y, entrySq (G n y) ≤ d.weightMin⁻¹ * R ^ 2 := fun n =>
    (entry_le_energy hwmin hd.weight_measurable hd.weight_lower hd.weight_upper (L := H n) (hsec n).gradient_two).trans
      (mul_le_mul_of_nonneg_left (hE n) (inv_nonneg.2 hwmin.le))
  have hTr : ∀ n, ∫ y, ‖secondTrace (H n y)‖ ^ 2 ≤ R ^ 2 := by
    intro n
    have h1 := hE n
    have h2 : 0 ≤ ∫ y, d.weight y * entrySq (G n y) :=
      integral_nonneg fun y => mul_nonneg (hwmin.le.trans (hd.weight_lower y)) (entrySq_nonneg _)
    unfold FracCertData.energy weightedEnergy at h1
    linarith
  have hHm : ∀ n i j, MemLp (fun y => H n y (unitVector i) (unitVector j)) 2 volume := by
    intro n i j
    have hm : AEStronglyMeasurable (fun y => H n y (unitVector i) (unitVector j)) volume :=
      ((hsec n).measurable_second.apply_continuousLinearMap (unitVector i)).apply_continuousLinearMap (unitVector j)
    refine (memLp_two_iff_integrable_sq_norm hm).2 ?_
    refine (hsec n).second_two.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_of_nonneg (by positivity)]
    have a1 := Finset.single_le_sum (f := fun j' : Fin 3 => ‖H n y (unitVector i) (unitVector j')‖ ^ 2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    have a2 := Finset.single_le_sum (f := fun i' : Fin 3 => ∑ j' : Fin 3, ‖H n y (unitVector i') (unitVector j')‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    exact a1.trans a2
  have hHb : ∀ n i j, l2Norm (fun y => H n y (unitVector i) (unitVector j)) ≤ R := by
    intro n i j
    have hR0 : 0 ≤ R := (Real.sqrt_nonneg _).trans (hsize n)
    have hfe := (secondSymbolEnergy d.order (u n) (G n) (H n) (hsec n))
    have hfull : ∫ y, fullSecondSq (H n y) = ∫ y, ‖secondTrace (H n y)‖ ^ 2 := by
      rw [hfe.2.2.1, hfe.2.2.2]
    have hle : ∫ y, ‖H n y (unitVector i) (unitVector j)‖ ^ 2 ≤ ∫ y, fullSecondSq (H n y) := by
      refine integral_mono ((hHm n i j).integrable_norm_pow (by norm_num)) (hsec n).second_two fun y => ?_
      have a1 := Finset.single_le_sum (f := fun j' : Fin 3 => ‖H n y (unitVector i) (unitVector j')‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      have a2 := Finset.single_le_sum
        (f := fun i' : Fin 3 => ∑ j' : Fin 3, ‖H n y (unitVector i') (unitVector j')‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      exact a1.trans a2
    unfold l2Norm
    rw [← Real.sqrt_sq hR0]
    exact Real.sqrt_le_sqrt (hle.trans (hfull.le.trans (hTr n)))
  have hWm : ∀ n, MemLp (fun y => ‖y‖⁻¹ • u n y) 2 volume ∧
      l2Norm (fun y => ‖y‖⁻¹ • u n y) ≤ 2 * Real.sqrt (d.weightMin⁻¹ * R ^ 2) := by
    intro n
    obtain ⟨hI, hIb⟩ := inverseSquareBound (u n) (G n) (hsec n).measurable_velocity (hsec n).velocity_six
      (hsec n).gradient_two (hsec n).weak_gradient
    have e : (fun y => ‖‖y‖⁻¹ • u n y‖ ^ 2) = fun y => ‖u n y‖ ^ 2 / ‖y‖ ^ 2 := by
      funext y
      rw [norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, div_eq_inv_mul]
    have hm : AEStronglyMeasurable (fun y => ‖y‖⁻¹ • u n y) volume :=
      (measurable_norm.inv.aestronglyMeasurable).smul (hsec n).measurable_velocity
    refine ⟨(memLp_two_iff_integrable_sq_norm hm).2 (by rw [e]; exact hI), ?_⟩
    unfold l2Norm
    rw [e]
    calc Real.sqrt (∫ y, ‖u n y‖ ^ 2 / ‖y‖ ^ 2) ≤ Real.sqrt (4 * (d.weightMin⁻¹ * R ^ 2)) :=
          Real.sqrt_le_sqrt (hIb.trans (by linarith [hEG n]))
      _ = 2 * Real.sqrt (d.weightMin⁻¹ * R ^ 2) := by
          rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨φ₁, hφ₁, G₀, hG₀m, hG₀c, hGw⟩ := exists_weak_operator_subseq G _ (fun n => (hsec n).measurable_gradient)
    (fun n => (hsec n).gradient_two) hEG
  have hrow : ∀ n i, AEStronglyMeasurable (fun y => H n y (unitVector i)) volume ∧
      Integrable (fun y => entrySq (H n y (unitVector i))) ∧
      ∫ y, entrySq (H n y (unitVector i)) ≤ R ^ 2 := by
    intro n i
    have hm : AEStronglyMeasurable (fun y => H n y (unitVector i)) volume :=
      (hsec n).measurable_second.apply_continuousLinearMap (unitVector i)
    have hle : ∀ y, entrySq (H n y (unitVector i)) ≤ fullSecondSq (H n y) := by
      intro y
      exact Finset.single_le_sum
        (f := fun i' : Fin 3 => ∑ j' : Fin 3, ‖H n y (unitVector i') (unitVector j')‖ ^ 2)
        (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
    have hint : Integrable (fun y => entrySq (H n y (unitVector i))) := by
      have hm2 : AEStronglyMeasurable (fun y => entrySq (H n y (unitVector i))) volume := by
        unfold entrySq
        exact (Finset.aestronglyMeasurable_sum Finset.univ fun j _ =>
          (hm.apply_continuousLinearMap (unitVector j)).norm.pow 2).congr
          (ae_of_all _ fun y => by simp [Finset.sum_apply])
      refine (hsec n).second_two.mono' hm2 (ae_of_all _ fun y => ?_)
      rw [Real.norm_of_nonneg (entrySq_nonneg _)]
      exact hle y
    refine ⟨hm, hint, ?_⟩
    have hfe := secondSymbolEnergy d.order (u n) (G n) (H n) (hsec n)
    have hfull : ∫ y, fullSecondSq (H n y) = ∫ y, ‖secondTrace (H n y)‖ ^ 2 := by
      rw [hfe.2.2.1, hfe.2.2.2]
    exact (integral_mono hint (hsec n).second_two hle).trans (hfull.le.trans (hTr n))
  obtain ⟨φ₂₀, hφ₂₀, K₀, hK₀m, hK₀c, hK₀w⟩ := exists_weak_operator_subseq (fun n y => H (φ₁ n) y (unitVector 0)) _
    (fun n => (hrow _ 0).1) (fun n => (hrow _ 0).2.1) (fun n => (hrow _ 0).2.2)
  obtain ⟨φ₂₁, hφ₂₁, K₁, hK₁m, hK₁c, hK₁w⟩ :=
    exists_weak_operator_subseq (fun n y => H (φ₁ (φ₂₀ n)) y (unitVector 1)) _
    (fun n => (hrow _ 1).1) (fun n => (hrow _ 1).2.1) (fun n => (hrow _ 1).2.2)
  obtain ⟨φ₂₂, hφ₂₂, K₂, hK₂m, hK₂c, hK₂w⟩ :=
    exists_weak_operator_subseq (fun n y => H (φ₁ (φ₂₀ (φ₂₁ n))) y (unitVector 2)) _
    (fun n => (hrow _ 2).1) (fun n => (hrow _ 2).2.1) (fun n => (hrow _ 2).2.2)
  obtain ⟨φ₂, hφ₂, hφ₂e⟩ : ∃ φ₂ : ℕ → ℕ, StrictMono φ₂ ∧ ∀ n, φ₂ n = φ₂₀ (φ₂₁ (φ₂₂ n)) :=
    ⟨_, hφ₂₀.comp (hφ₂₁.comp hφ₂₂), fun n => rfl⟩
  obtain ⟨H₀, hH₀e, hH₀m⟩ : ∃ H₀ : Space → (Space →L[ℝ] Space →L[ℝ] Space),
      (∀ i y, H₀ y (unitVector i) = (![K₀, K₁, K₂] : Fin 3 → Space → (Space →L[ℝ] Space)) i y) ∧
        AEStronglyMeasurable H₀ volume := by
    refine ⟨opOp ![K₀, K₁, K₂], fun i y => opOp_apply _ y i, opOp_meas ?_⟩
    intro i
    match i with
    | 0 => exact hK₀m
    | 1 => exact hK₁m
    | 2 => exact hK₂m
  have hH₀c : ∀ i j, MemLp (fun y => H₀ y (unitVector i) (unitVector j)) 2 volume := by
    intro i j
    simp only [hH₀e]
    match i with
    | 0 => exact hK₀c j
    | 1 => exact hK₁c j
    | 2 => exact hK₂c j
  have hHw2 : ∀ i j : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (H (φ₁ (φ₂ n)) y (unitVector i) (unitVector j)) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (H₀ y (unitVector i) (unitVector j)) (g y))) := by
    intro i j g hg
    simp only [hφ₂e, hH₀e]
    match i with
    | 0 => exact ((hK₀w j g hg).comp hφ₂₁.tendsto_atTop).comp hφ₂₂.tendsto_atTop
    | 1 => exact (hK₁w j g hg).comp hφ₂₂.tendsto_atTop
    | 2 => exact hK₂w j g hg
  obtain ⟨φ₃, hφ₃, w₀, hw₀m, -, hw₀⟩ := exists_weak_subseq (fun n y => ‖y‖⁻¹ • u (φ₁ (φ₂ n)) y) _
    (fun n => (hWm _).1) (fun n => (hWm _).2)
  obtain ⟨φ₄, hφ₄, P₀, hP₀m, -, hP₀⟩ := exists_weak_subseq (fun n => P (φ₁ (φ₂ (φ₃ n)))) B
    (fun n => (hsol _).state.power.1) (fun n => (hB _).1)
  obtain ⟨φ₅, hφ₅, D₀, hD₀m, -, hD₀⟩ := exists_weak_subseq
    (fun n => driftField α (d.rotationRate (p (φ₁ (φ₂ (φ₃ (φ₄ n)))))) (u (φ₁ (φ₂ (φ₃ (φ₄ n)))))
      (G (φ₁ (φ₂ (φ₃ (φ₄ n)))))) B (fun n => (hsol _).state.drift) (fun n => (hB _).2)
  have hψm : StrictMono (fun n => φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n))))) := hφ₁.comp (hφ₂.comp (hφ₃.comp (hφ₄.comp hφ₅)))
  have hHw' : ∀ i j : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (H (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n))))) y (unitVector i) (unitVector j)) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (H₀ y (unitVector i) (unitVector j)) (g y))) := fun i j g hg =>
    (hHw2 i j g hg).comp (hφ₃.comp (hφ₄.comp hφ₅)).tendsto_atTop
  have hGw' : ∀ i : Fin 3, ∀ g : Space → Space, MemLp g 2 volume →
      Tendsto (fun n => ∫ y, inner ℝ (G (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n))))) y (unitVector i)) (g y)) atTop
        (𝓝 (∫ y, inner ℝ (G₀ y (unitVector i)) (g y))) := fun i g hg =>
    (hGw i g hg).comp (hφ₂.comp (hφ₃.comp (hφ₄.comp hφ₅))).tendsto_atTop
  obtain ⟨hst, horth⟩ := hcl α hα1 hα2 d hd (fun n => p (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))))) q (fun n => hp _) hq
    (hpq.comp hψm.tendsto_atTop) (fun n => u (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n))))))
    (fun n => G (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))))) (fun n => H (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n))))))
    (fun n => P (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))))) (fun n => κ (φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))))) R B κ₀
    (fun n => hsol _) (fun n => hsize _) (fun n => hB _) (hκ.comp hψm.tendsto_atTop)
    w₀ G₀ H₀ P₀ D₀ hG₀m hH₀m hG₀c hH₀c hw₀m hP₀m hD₀m hGw' hHw'
    (fun g hg => (hw₀ g hg).comp (hφ₄.comp hφ₅).tendsto_atTop)
    (fun g hg => (hP₀ g hg).comp hφ₅.tendsto_atTop) (fun g hg => hD₀ g hg)
  refine ⟨fun n => φ₁ (φ₂ (φ₃ (φ₄ (φ₅ n)))), hψm, fun y => ‖y‖ • w₀ y, G₀, H₀, P₀, hst, hGw', ?_, horth⟩
  intro g hg
  have e : ∀ K : Space → (Space →L[ℝ] Space →L[ℝ] Space),
      (∀ i j, MemLp (fun y => K y (unitVector i) (unitVector j)) 2 volume) →
      ∫ y, inner ℝ (secondTrace (K y)) (g y) =
        ∑ j : Fin 3, ∫ y, inner ℝ (K y (unitVector j) (unitVector j)) (g y) := by
    intro K hK
    unfold secondTrace
    simp only [sum_inner]
    exact integral_finset_sum _ fun j _ => pair_integrable (hK j j) hg
  simp only [e _ (hHm _), e _ hH₀c]
  exact tendsto_finset_sum _ fun j _ => hHw' j j g hg

open WeakFieldLimit LinearStateClosedInternal in
theorem heldLimitClosure_of (c1 : SecondOrderWeakLimitStatement) (c2 : WeakPowerLimitStatement)
    (c3 : DriftWeakLimitStatement) (c4 : HeldResidualLimitStatement) : HeldLimitClosureStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R B κ₀ hsol hsize hB hκ w₀ G₀ H₀ P₀ D₀ hG₀m hH₀m hG₀c
    hH₀c hw₀m hP₀m hD₀m hGw hHw hWw hPw hDw
  have hsec : ∀ n, IsSecondOrderField d.order (u n) (G n) (H n) := fun n => (hsol n).state.second
  have hwmin := hd.weightMin_pos
  have hE : ∀ n, d.energy (G n) (H n) ≤ R ^ 2 := by
    intro n
    have hE0 : 0 ≤ d.energy (G n) (H n) := energy_nonneg hwmin hd.weight_lower _ _
    have hsq : d.size (G n) (H n) (κ n) ^ 2 = d.energy (G n) (H n) + d.multiplierScale ^ 2 * ∑ i, κ n i ^ 2 := by
      unfold FracCertData.size sizeNorm
      rw [Real.sq_sqrt]
      · rfl
      · exact add_nonneg hE0 (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h2 : d.size (G n) (H n) (κ n) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsize n) 2
    have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ n i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  have hEG : ∀ n, ∫ y, entrySq (G n y) ≤ d.weightMin⁻¹ * R ^ 2 := fun n =>
    (entry_le_energy hwmin hd.weight_measurable hd.weight_lower hd.weight_upper (L := H n) (hsec n).gradient_two).trans
      (mul_le_mul_of_nonneg_left (hE n) (inv_nonneg.2 hwmin.le))
  have hFull : ∀ n, ∫ y, fullSecondSq (H n y) ≤ R ^ 2 := by
    intro n
    have h1 := hE n
    have h2 : 0 ≤ ∫ y, d.weight y * entrySq (G n y) :=
      integral_nonneg fun y => mul_nonneg (hwmin.le.trans (hd.weight_lower y)) (entrySq_nonneg _)
    unfold FracCertData.energy weightedEnergy at h1
    have hfe := secondSymbolEnergy d.order (u n) (G n) (H n) (hsec n)
    rw [hfe.2.2.1, ← hfe.2.2.2]
    linarith
  have hWm : ∀ n, MemLp (fun y => ‖y‖⁻¹ • u n y) 2 volume := by
    intro n
    obtain ⟨hI, -⟩ := inverseSquareBound (u n) (G n) (hsec n).measurable_velocity (hsec n).velocity_six
      (hsec n).gradient_two (hsec n).weak_gradient
    have e : (fun y => ‖‖y‖⁻¹ • u n y‖ ^ 2) = fun y => ‖u n y‖ ^ 2 / ‖y‖ ^ 2 := by
      funext y
      rw [norm_smul, norm_inv, norm_norm, mul_pow, inv_pow, div_eq_inv_mul]
    have hm : AEStronglyMeasurable (fun y => ‖y‖⁻¹ • u n y) volume :=
      (measurable_norm.inv.aestronglyMeasurable).smul (hsec n).measurable_velocity
    exact (memLp_two_iff_integrable_sq_norm hm).2 (by rw [e]; exact hI)
  have hrr : Tendsto (fun n => d.rotationRate (p n)) atTop (𝓝 (d.rotationRate q)) :=
    (hd.rotationRate_continuous q hq).tendsto.comp (tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩)
  have h1 := c1 d.order (max (d.weightMin⁻¹ * R ^ 2) (R ^ 2)) u G H w₀ G₀ H₀ hsec
    (fun n => (hEG n).trans (le_max_left _ _)) (fun n => (hFull n).trans (le_max_right _ _)) hG₀m hH₀m hw₀m
    hG₀c hH₀c hGw hHw hWw
  have h2 := c2 α hα1 hα2 u P w₀ P₀ (fun n => (hsol n).state.power) hWm hw₀m hP₀m hWw hPw
  have h3 := c3 α hα1 hα2 d.order (fun n => d.rotationRate (p n)) (d.rotationRate q) u G H w₀ G₀ H₀ D₀ hrr hsec h1
    (fun n => (hsol n).state.drift) hWm hD₀m hGw hWw hDw
  have hst : d.IsLinearState α q (fun y => ‖y‖ • w₀ y) G₀ H₀ P₀ := ⟨h1, h2, h3⟩
  exact ⟨hst, c4 α hα1 hα2 d hd p q hp hq hpq u G H P κ R B κ₀ hsol hsize hB hκ w₀ G₀ H₀ P₀ D₀ hst hD₀m
    hGw hHw hWw hPw hDw⟩

end SteadyCert

end Breakdown

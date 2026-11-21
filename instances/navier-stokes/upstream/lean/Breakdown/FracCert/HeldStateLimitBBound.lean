import Breakdown.FracCert.HeldStateLimitBParts
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.FracCert.GradientOrthogonal
import Breakdown.FracCert.GradientAdd
import Breakdown.FracCert.QuadraticSquare
import Breakdown.FracCert.LinearStateClosed
import Breakdown.FracCert.HeldUnique
import Breakdown.FracCert.FreeBounds
import Breakdown.FracCert.DriftEnergy
import Breakdown.FracCert.DriftPower
import Breakdown.FracCert.DriftSymbolWeak
import Breakdown.FracCert.FlowDeriv
import Breakdown.FracCert.FlowPairing
import Breakdown.FracCert.PowerSymbol
import Breakdown.FracCert.PowerSymbolRapid
import Breakdown.FracCert.SecondPairRapid
import Breakdown.FracCert.SecondSymbol
import Breakdown.FracCert.InverseSquare

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldBoundInternal

open LinearStateClosedInternal HeldUniqueInternal

theorem freeBoundsProved : FreeBoundsStatement :=
  have wps : WeakPowerSymbolStatement := weakPowerSymbol_of_band secondSymbolEnergy
    (PowerSymbolInternal.bandWeakPower_of rapidWeakPower) (PowerSymbolInternal.bandSecondPair_of rapidSecondPair)
  freeBounds_of secondSymbolEnergy wps driftEnergy
    (driftPower_of secondSymbolEnergy wps (driftPairSymbol_of secondSymbolEnergy driftSymbolWeak
      (flowPairing_of_integral (flowIntegral_of_test (flowTest_of_deriv flowDeriv)))))

theorem norm_add_le' {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Norm (fun y => f y + g y) ≤ l2Norm f + l2Norm g := by
  have e : (fun y => f y + g y) = f + g := rfl
  rw [e, l2Norm_eq (hf.add hg), l2Norm_eq hf, l2Norm_eq hg, MemLp.toLp_add]
  exact norm_add_le _ _

theorem norm_smul' (c : ℝ) (f : Space → Space) : l2Norm (fun y => c • f y) = |c| * l2Norm f := by
  unfold l2Norm
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [integral_const_mul, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem norm_zero' : l2Norm (fun _ : Space => (0 : Space)) = 0 := by
  simp [l2Norm]

theorem norm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (hf : ∀ i, MemLp (f i) 2 volume) :
    MemLp (fun y => ∑ i ∈ s, f i y) 2 volume ∧ l2Norm (fun y => ∑ i ∈ s, f i y) ≤ ∑ i ∈ s, l2Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨MemLp.zero, by simp [l2Norm]⟩
  | insert a s ha ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : (fun y => ∑ i ∈ insert a s, f i y) = fun y => f a y + ∑ i ∈ s, f i y := by
      funext y
      rw [Finset.sum_insert ha]
    rw [e, Finset.sum_insert ha]
    exact ⟨(hf a).add h1, (norm_add_le' (hf a) h1).trans (by linarith)⟩

theorem pair_integrable' {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem gradient_neg' {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq2, hQ2, hQm, hq⟩ := hQ
  refine ⟨fun y => -q y, ?_, ?_, hQm.neg, ?_⟩
  · simpa only [neg_sq] using hq2
  · simpa only [norm_neg] using hQ2
  · intro φ hφ j
    have h := hq φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg]
    linarith

theorem residual_memLp' {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N)
    (hd : IsFracCert α d) {p : Fin k → ℝ} (hp : p ∈ box d.radius) {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space}
    (hst : d.IsLinearState α p v G H P) (κ : Fin k → ℝ) :
    MemLp (d.heldResidual α p v G H P κ) 2 volume := by
  have e : d.heldResidual α p v G H P κ = fun y =>
      driftField α (d.rotationRate p) v G y + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
        + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + v y)
        + ∑ i, (d.multiplier p i + κ i) • d.actuator i y := by
    funext y
    simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField,
      FracCertData.splitField, FracCertData.defect, symProduct, add_smul, Finset.sum_add_distrib,
      add_apply, map_add, smul_smul]
    norm_num
    abel
  rw [e]
  have hs : MemLp (fun y => ∑ i, (d.multiplier p i + κ i) • d.actuator i y) 2 volume :=
    memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i + κ i)
  exact ((((hst.drift.add (hd.profile_drift p hp)).add hst.power.1).add (hd.profile_power p hp).1).add
    (heldQuadraticL2_of quadraticSquareIntegrable α hα1 hα2 d hd p hp v G H hst.second)).add hs

end HeldBoundInternal

open HeldBoundInternal LinearStateClosedInternal in
theorem heldUniformBound_of (hs : DriftPowerSolenoidalStatement) : HeldUniformBoundStatement := by
  intro α hα1 hα2 k N d hd R
  obtain ⟨C, hC⟩ := hd.profile_bounds
  obtain ⟨C₀, hF⟩ := freeBoundsProved α hα1 hα2
  have hwmin := hd.weightMin_pos
  have hμ := hd.multiplierScale_pos
  refine ⟨2 * Real.sqrt (5 / 2 * C ^ 2 * (d.weightMin⁻¹ * R ^ 2)) + d.productConst * R ^ 2
    + ∑ i, R / d.multiplierScale * l2Norm (d.actuator i) + (d.defectBound + 1), ?_⟩
  intro p hp u G H P κ hsol hsize
  have hst := hsol.state
  have hsec := hst.second
  have hS : IsSolenoidalL2 (fun y => driftField α (d.rotationRate p) u G y + P y) :=
    hs α hα1 hα2 (d.rotationRate p) d.order u G H P hsec hst.power hst.drift
  obtain ⟨hP1, hD1, -, -⟩ := hF (d.rotationRate p) d.order u G H P
    (fun y => driftField α (d.rotationRate p) u G y + P y) hsec hst.power hst.drift hS.1
    (Filter.Eventually.of_forall fun y => rfl)
  suffices hSB : l2Norm (fun y => driftField α (d.rotationRate p) u G y + P y) ≤
      2 * Real.sqrt (5 / 2 * C ^ 2 * (d.weightMin⁻¹ * R ^ 2)) + d.productConst * R ^ 2
        + ∑ i, R / d.multiplierScale * l2Norm (d.actuator i) + (d.defectBound + 1) from
    ⟨hP1.trans hSB, hD1.trans hSB⟩
  have hR0 : 0 ≤ R := (Real.sqrt_nonneg _).trans hsize
  have hE0 : 0 ≤ d.energy G H := energy_nonneg hwmin hd.weight_lower G H
  have hE : d.energy G H ≤ R ^ 2 := by
    have hsq : d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
      unfold FracCertData.size sizeNorm
      rw [Real.sq_sqrt]
      · rfl
      · exact add_nonneg hE0 (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h2 : d.size G H κ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hsize 2
    have : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    linarith
  have hEG : ∫ y, entrySq (G y) ≤ d.weightMin⁻¹ * R ^ 2 :=
    (entry_le_energy hwmin hd.weight_measurable hd.weight_lower hd.weight_upper (L := H) hsec.gradient_two).trans
      (mul_le_mul_of_nonneg_left hE (inv_nonneg.2 hwmin.le))
  have hkap : ∀ i, |κ i| ≤ R / d.multiplierScale := by
    intro i
    rw [le_div_iff₀ hμ, mul_comm]
    have hsq : d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
      unfold FracCertData.size sizeNorm
      rw [Real.sq_sqrt]
      · rfl
      · exact add_nonneg hE0 (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
    have h1 : (d.multiplierScale * |κ i|) ^ 2 ≤ d.size G H κ ^ 2 := by
      rw [hsq, mul_pow, sq_abs]
      have : κ i ^ 2 ≤ ∑ j, κ j ^ 2 :=
        Finset.single_le_sum (f := fun j => κ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [sq_nonneg d.multiplierScale]
    exact ((pow_le_pow_iff_left₀ (mul_nonneg hμ.le (abs_nonneg _)) (Real.sqrt_nonneg _) two_ne_zero).1 h1).trans
      hsize
  have hWc : Continuous (d.profile p) := (hd.profile_smooth p hp).continuous
  have hDWc : Continuous (d.gradProfile p) := (hd.profile_smooth p hp).continuous_fderiv one_ne_zero
  obtain ⟨hY1m, hY1b⟩ := sym_bound inverseSquareBound (d.profile p) (d.gradProfile p) hWc hDWc C
    (fun y => ⟨(hC p hp y).1, (hC p hp y).2.1⟩) d.order hsec
  have hY1m' : MemLp (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y) 2 volume :=
    hY1m.const_smul (2 : ℝ)
  have hY1n : l2Norm (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y) ≤
      2 * Real.sqrt (5 / 2 * C ^ 2 * (d.weightMin⁻¹ * R ^ 2)) := by
    rw [norm_smul', abs_of_pos two_pos]
    refine mul_le_mul_of_nonneg_left ?_ two_pos.le
    unfold l2Norm
    refine Real.sqrt_le_sqrt (hY1b.trans ?_)
    exact mul_le_mul_of_nonneg_left hEG (by positivity)
  have hY2m : MemLp (fun y => G y (u y)) 2 volume := quadraticSquareIntegrable d.order u G H hsec
  have hY2n : l2Norm (fun y => G y (u y)) ≤ d.productConst * R ^ 2 := by
    have e : (fun y => G y (u y)) = symProduct u G u G := by
      funext y
      simp only [symProduct]
      rw [← two_smul ℝ (G y (u y)), smul_smul]
      norm_num
    rw [e]
    refine (hd.productConst_bound u G H hsec u G H hsec).trans ?_
    rw [mul_assoc, Real.mul_self_sqrt hE0]
    exact mul_le_mul_of_nonneg_left hE hd.productConst_nonneg
  obtain ⟨hY3m, hY3b⟩ := norm_sum_le' Finset.univ (fun i y => κ i • d.actuator i y)
    (fun i => (hd.actuator_two i).const_smul (κ i))
  have hY3n : l2Norm (fun y => ∑ i, κ i • d.actuator i y) ≤ ∑ i, R / d.multiplierScale * l2Norm (d.actuator i) := by
    refine hY3b.trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_smul']
    exact mul_le_mul_of_nonneg_right (hkap i) (Real.sqrt_nonneg _)
  have hres := residual_memLp' hα1 hα2 d hd hp hst κ
  have hfull : ∀ y, d.heldResidual α p u G H P κ y =
      (driftField α (d.rotationRate p) u G y + P y) +
        ((2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)
          + ∑ i, κ i • d.actuator i y) + d.defect α p y := by
    intro y
    simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField,
      FracCertData.splitField]
    abel
  have hYm : MemLp (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)
      + ∑ i, κ i • d.actuator i y) 2 volume := (hY1m'.add hY2m).add hY3m
  have hdefm : MemLp (d.defect α p) 2 volume := by
    have e : d.defect α p = fun y => d.heldResidual α p u G H P κ y -
        ((driftField α (d.rotationRate p) u G y + P y) +
          ((2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)
            + ∑ i, κ i • d.actuator i y)) := by
      funext y
      rw [hfull y]
      abel
    rw [e]
    exact hres.sub (hS.1.add hYm)
  have hne : {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => d.defect α p y + Q y) 2 volume ∧
      r = l2Norm (fun y => d.defect α p y + Q y)}.Nonempty := by
    refine ⟨_, fun _ => 0, ?_, by simpa using hdefm, rfl⟩
    refine ⟨fun _ => 0, ?_, ?_, aestronglyMeasurable_const, ?_⟩
    · intro K _
      simp
    · intro K _
      simp
    · intro φ _ j
      simp
  have hlt : projectedNorm (d.defect α p) < d.defectBound + 1 := by linarith [hd.defect_norm p hp]
  obtain ⟨r, ⟨Qd, hQdg, hZm, rfl⟩, hrlt⟩ := exists_lt_of_csInf_lt hne hlt
  obtain ⟨Q, hQg, hQ⟩ := hsol.equation
  set S : Space → Space := fun y => driftField α (d.rotationRate p) u G y + P y with hSdef
  set Y : Space → Space := fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)
      + ∑ i, κ i • d.actuator i y with hYdef
  set Z : Space → Space := fun y => d.defect α p y + Qd y with hZdef
  have hT : IsGradientField (fun y => Qd y + -Q y) := gradientAdd Qd (fun y => -Q y) hQdg (gradient_neg' hQg)
  have hTe : (fun y => Qd y + -Q y) =ᵐ[volume] fun y => S y + (Y y + Z y) := by
    filter_upwards [hQ] with y hy
    have h1 := hfull y
    simp only [FracCertData.heldResidual] at h1
    rw [h1] at hy
    rw [eq_neg_of_add_eq_zero_right hy]
    simp only [hSdef, hYdef, hZdef]
    abel
  have hTm : MemLp (fun y => Qd y + -Q y) 2 volume := (hS.1.add (hYm.add hZm)).ae_eq hTe.symm
  have horth := gradientOrthogonal _ S hT hTm hS
  have hWm : MemLp (fun y => Y y + Z y) 2 volume := hYm.add hZm
  have hkey : l2Norm S ^ 2 ≤ l2Norm S * l2Norm (fun y => Y y + Z y) := by
    have e1 : l2Norm S ^ 2 = ∫ y, inner ℝ (S y) (S y) := by
      rw [sq_l2Norm]
      congr 1
      funext y
      rw [real_inner_self_eq_norm_sq]
    have e2 : ∫ y, inner ℝ (S y) (S y) = ∫ y, inner ℝ (S y) (-(Y y + Z y)) := by
      have hA : ∫ y, inner ℝ (S y) (Qd y + -Q y) = (∫ y, inner ℝ (S y) (S y)) + ∫ y, inner ℝ (S y) (Y y + Z y) := by
        calc ∫ y, inner ℝ (S y) (Qd y + -Q y)
            = ∫ y, (inner ℝ (S y) (S y) + inner ℝ (S y) (Y y + Z y)) := by
              refine integral_congr_ae ?_
              filter_upwards [hTe] with y hy
              rw [hy, inner_add_right]
          _ = _ := by
              have h := integral_add (pair_integrable' hS.1 hS.1) (pair_integrable' hS.1 hWm)
              beta_reduce at h
              exact h
      have hB : ∫ y, inner ℝ (S y) (Qd y + -Q y) = 0 := by
        rw [← horth]
        congr 1
        funext y
        exact real_inner_comm _ _
      have hC' : ∫ y, inner ℝ (S y) (-(Y y + Z y)) = -∫ y, inner ℝ (S y) (Y y + Z y) := by
        rw [← integral_neg]
        congr 1
        funext y
        exact inner_neg_right _ _
      linarith
    have h3 : ∫ y, inner ℝ (S y) (-(Y y + Z y)) ≤ l2Norm S * l2Norm (fun y => -(Y y + Z y)) :=
      l2_pair_le hS.1 hWm.neg
    have e3 : l2Norm (fun y => -(Y y + Z y)) = l2Norm (fun y => Y y + Z y) := by
      simp only [l2Norm, norm_neg]
    rw [e1, e2]
    rw [e3] at h3
    exact h3
  have hSle : l2Norm S ≤ l2Norm (fun y => Y y + Z y) := by
    rcases (Real.sqrt_nonneg (∫ y, ‖S y‖ ^ 2)).eq_or_lt with h0 | h0
    · change 0 = l2Norm S at h0
      rw [← h0]
      exact Real.sqrt_nonneg _
    · change 0 < l2Norm S at h0
      nlinarith
  have hYn : l2Norm Y ≤ 2 * Real.sqrt (5 / 2 * C ^ 2 * (d.weightMin⁻¹ * R ^ 2)) + d.productConst * R ^ 2
      + ∑ i, R / d.multiplierScale * l2Norm (d.actuator i) := by
    have a1 : l2Norm (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)) ≤
        l2Norm (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y) + l2Norm (fun y => G y (u y)) :=
      norm_add_le' hY1m' hY2m
    have a2 : l2Norm Y ≤
        l2Norm (fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y)) +
          l2Norm (fun y => ∑ i, κ i • d.actuator i y) :=
      norm_add_le' (f := fun y => (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) u G y + G y (u y))
        (hY1m'.add hY2m) hY3m
    linarith
  have hZn : l2Norm Z ≤ d.defectBound + 1 := hrlt.le
  have a3 : l2Norm (fun y => Y y + Z y) ≤ l2Norm Y + l2Norm Z := norm_add_le' hYm hZm
  linarith

end SteadyCert

end Breakdown

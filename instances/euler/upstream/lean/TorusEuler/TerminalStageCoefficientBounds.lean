import TorusEuler.TerminalFlowTimeCoefficients
import TorusEuler.TerminalReciprocalTimeBounds
import TorusEuler.InductiveStageVelocityJetBounds
import TorusEuler.HierarchyInductiveTransverseBudget

/-! Actual mixed coefficient estimates on a selected parent's smaller slab. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

namespace TerminalMixedJetBound

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Restricting the time slab preserves the pointwise mixed jet bounds.
The derivatives at the endpoints of the smaller slab agree with the
corresponding restricted parent derivatives. -/
theorem restrict_time {a b c d D A : ℝ} {p q : ℕ} {C : ℕ → ℝ}
    {f : ℝ → Vec3 → E} (h : TerminalMixedJetBound a b q p D A C f)
    (hab : a < b) (hcd : c < d) (hsub : Icc c d ⊆ Icc a b)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) :
    TerminalMixedJetBound c d q p D A C f := by
  intro i hi n t ht x
  rw [show slabTimeJet c d i f t = slabTimeJet a b i f t from
    funext (slabTimeJet_eq_of_subset hcd hsub hab hf i ht)]
  exact h i hi n t (hsub ht) x

/-- Old Fourier-band Bernstein bounds fit the mixed label calculus with
one spatial factor of the effective parent parameter `μ^9`. -/
theorem of_parentBernstein {a b μ A : ℝ} {q : ℕ} {C : ℕ → ℝ} {f : ℝ → Vec3 → E}
    (hμ : 1 ≤ μ) (hA : 0 ≤ A) (hC : ∀ n, 0 ≤ C n)
    (h : ∀ i ≤ q, ∀ n, ∀ t ∈ Icc a b, ∀ x,
      ‖iteratedFDeriv ℝ n (slabTimeJet a b i f t) x‖ ≤ C n * A * μ ^ (5 * n)) :
    TerminalMixedJetBound a b q 1 (μ ^ 9) A C f := by
  intro i hi n t ht x
  rw [one_mul, ← pow_mul]
  exact (h i hi n t ht x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hμ (by omega)) (mul_nonneg (hC n) hA))

end TerminalMixedJetBound

namespace InductiveEulerStage.OnSlab

local notation "Time(" T ")" => Icc (0 : ℝ) T

set_option maxHeartbeats 1500000 in
/-- Parent admissibility on the selected slab turns Eulerian bounds
through order `q` into actual label-time bounds on all flow coefficients. -/
theorem exists_terminalStageCoefficientBounds (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) (q : ℕ) :
    ∃ C Ci : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ (∀ n, 0 ≤ Ci n) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T A : ℝ}
        {parent : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (_d : parent.OnSlab hT k), T ≤ 1 → 2 ≤ P.frequency n → 1 ≤ A →
        ∀ {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Time(T) →
          ‖labelWaveVector parent.flow 0 0 k t₀‖ = freq →
          let D := P.frequency n ^ (9 : ℕ)
          let B := terminalFlowTimeAmplitude q D A
          let F := fun t x => fderiv ℝ (parent.flow 0 t) x
          let G := fun t x => fderiv ℝ (parent.flow t 0) (parent.flow 0 t x)
          let M := fun t x => fderiv ℝ (parent.velocity t) (parent.flow 0 t x)
          let κ := fun t x => freq⁻¹ • labelWaveVector parent.flow 0 x k t
          TerminalMixedJetBound 0 T q 1 D A W parent.velocity →
          TerminalMixedJetBound 0 T q 16 D B C F ∧
          TerminalMixedJetBound 0 T q 16 D B C G ∧
          TerminalMixedJetBound 0 T q 16 D B C M ∧
          TerminalMixedJetBound 0 T q 16 D B C κ ∧
          TerminalMixedJetBound 0 T q 16 D
            (terminalReciprocalTimeAmplitude (B * B) (D^4) q) Ci
            (fun t x => (‖κ t x‖ ^ 2)⁻¹) := by
  obtain ⟨R, hR, hBernstein⟩ := exists_velocity_jet_bounds
  obtain ⟨C, hC, hCoefficients⟩ := exists_terminalFlowLinearJetBounds R W hR hW q
  obtain ⟨S, hS, hBase⟩ := exists_parent_coefficientJetBounds R hR
  let H : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  let Cκ := terminalMixedProductCost q H C C
  let Cr := terminalReciprocalTimeCost Cκ S q
  refine ⟨C, Cr, hC, terminalReciprocalTimeCost_nonneg (terminalMixedProductCost_nonneg q H hC hC) hS q, ?_⟩
  intro P n activation T A parent hT k d hT₁ hParent hA freq t₀ hf ht₀ hk D B F G M κ hUJ
  have hμ : 1 ≤ P.frequency n := one_le_two.trans hParent
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hB : 0 ≤ B := by dsimp only [B, terminalFlowTimeAmplitude]; positivity
  let X := parent.flow
  let U := parent.velocity
  have hX := d.deformationOn.flow
  have hU := d.smooth_velocity
  have hper : ∀ t ∈ Time(T), SpatiallyPeriodic (U t) := fun t _ => parent.periodic_velocity t
  have hF (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖F t x‖ ≤ D :=
    (d.raw_coframe_norm_le_frequency_nine hParent ht x).1
  have hG (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : ‖G t x‖ ≤ D :=
    (d.raw_coframe_norm_le_frequency_nine hParent ht x).2
  have hR' (i j : ℕ) (h₁ : 1 ≤ j) (h₂ : j ≤ i) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R i * D ^ j :=
    hBernstein parent hμ i j h₁ h₂ t (d.subset ht) x
  obtain ⟨hFJ,hGJ,hMJ,hκJ⟩ :=
    hCoefficients hT hT₁ hD hA hX hU hper hF hG hR' hUJ k hf ht₀ hk
  refine ⟨hFJ,hGJ,hMJ,hκJ,?_⟩
  have hκreg : ContDiffOn ℝ ∞ (Function.uncurry κ) (Time(T) ×ˢ (univ : Set Vec3)) :=
    (hX.contDiffOn_transportedCovector hT hU hper k).const_smul freq⁻¹
  have hκnz (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) : κ t x ≠ 0 := by
    have h := hX.norm_normalizedLabelWaveVector_bounds hT (hU.of_le (by simp)) hper ht₀ ht x k hD hf hk
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht x) (hG t ht x)
    exact (normalizedWaveNorm_ne_zero_and_inv_sq_le (zero_lt_one.trans_le hD) h.2.1).1
  have hrec : TerminalMixedJetBound 0 T 0 16 D (D^4) S
      (fun t x => (‖κ t x‖ ^ 2)⁻¹) := by
    apply TerminalMixedJetBound.of_zero
    intro j t ht x
    simpa only [κ, inv_sq_norm_inv_smul, ← pow_add, Nat.add_comm (16 * j) 4, mul_assoc] using
      (hBase hT hT₁ hD hX hU hper hF hG hR' k hf ht₀ hk j t ht x).2.2.2.2.2.1
  exact terminalMixedJetBound_inv_norm_sq hT hD₀ hB (pow_nonneg hD₀ _) hC hS hκreg hκnz hκJ hrec

set_option maxHeartbeats 900000 in
/-- The selected parent residual keeps its inverse next-frequency power
under label pullback, using only the available residual time orders. -/
theorem exists_terminalStageResidualPullbackBounds (W Wr : ℕ → ℝ)
    (hW : ∀ n, 0 ≤ W n) (hWr : ∀ n, 0 ≤ Wr n) (q : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation T A : ℝ}
        {parent : InductiveEulerStage P n activation} {hT : 0 < T} {k : Vec3}
        (_d : parent.OnSlab hT k), T ≤ 1 → 2 ≤ P.frequency n → 0 ≤ A →
        let D := P.frequency n ^ (9 : ℕ)
        let R := P.frequency (n+1) ^ (-5 / 2 : ℝ)
        TerminalMixedJetBound 0 T q 1 D A W parent.velocity →
        TerminalMixedJetBound 0 T q 1 D R Wr parent.residual →
        TerminalMixedJetBound 0 T q 6 D (R * (1 + D * A)^q) C
          (fun t x => parent.residual t (parent.flow 0 t x)) := by
  obtain ⟨R, hR, hVel⟩ := exists_velocity_jet_bounds
  obtain ⟨F, hF, hFlow⟩ := exists_forward_flowJetBounds R hR
  obtain ⟨C, hC, hPull⟩ := exists_terminalMaterialPullbackCost (E := Vec3) W Wr F hW hWr hF q
  refine ⟨C,hC,?_⟩
  intro P n activation T A parent hT k d hT₁ hParent hA D B hU hRj
  have hμ : 1 ≤ P.frequency n := one_le_two.trans hParent
  have hD : 1 ≤ D := one_le_pow₀ hμ
  have hX := d.deformationOn.flow
  have hper (t : ℝ) (_ht : t ∈ Time(T)) := parent.periodic_velocity t
  have hFbound (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖fderiv ℝ (parent.flow 0 t) x‖ ≤ D := (d.raw_coframe_norm_le_frequency_nine hParent ht x).1
  have hGbound (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖fderiv ℝ (parent.flow t 0) (parent.flow 0 t x)‖ ≤ D :=
    (d.raw_coframe_norm_le_frequency_nine hParent ht x).2
  have hFlowBound (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Time(T)) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (parent.flow 0 t) x‖ ≤ F j * D ^ (5*j) := by
    refine (hFlow hT hT₁ hD hX d.smooth_velocity hper hFbound hGbound
      (fun i _ k hk₁ hk₂ r hr y => hVel parent hμ i k (by omega) hk₂ r (d.subset hr) y)
      j hj t ht x).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.sub_le _ _)) (hF j)
  have hNext : 0 ≤ P.frequency (n+1) := by
    rw [P.frequency_step n]
    exact pow_nonneg (zero_le_one.trans hμ) _
  exact hPull (f := parent.residual) hT hD (Real.rpow_nonneg hNext _) hA hX d.smooth_velocity
    d.smooth_residual hper hU hRj hFlowBound

end InductiveEulerStage.OnSlab

end

end TorusEuler

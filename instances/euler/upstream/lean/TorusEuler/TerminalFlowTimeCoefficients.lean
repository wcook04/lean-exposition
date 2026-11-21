import TorusEuler.TerminalCoefficientTimeEvolution
import TorusEuler.TerminalMaterialCoefficientBounds
import TorusEuler.ParentCoframeEstimates

/-! The normalized flow coefficients on the actual parent slab. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "End" => (Vec3 →L[ℝ] Vec3)

/-- A fixed polynomial amplitude for the time jets of the material
gradient and the two deformation matrices. -/
def terminalFlowTimeAmplitude (q : ℕ) (D A : ℝ) : ℝ :=
  let grad := A * D * (1 + D * A) ^ q
  let cof := D * grad ^ q
  grad + cof + D * cof

set_option maxHeartbeats 1300000 in
/-- The actual material gradient, forward and inverse deformation, and
normalized transported covector have a common spatial slope for all time
orders through `q`. The label cost and the parent polynomial are selected
before the individual flow and frequencies. -/
theorem exists_terminalFlowLinearJetBounds (R W : ℕ → ℝ)
    (hR : ∀ n, 0 ≤ R n) (hW : ∀ n, 0 ≤ W n) (q : ℕ) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧ ∀ {U : Velocity} {X : ℝ → Velocity} {T D A : ℝ},
      0 < T → T ≤ 1 → 1 ≤ D → 1 ≤ A →
      IsLabelFlowOn U X (Icc 0 T) →
      ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X 0 t) x‖ ≤ D) →
      (∀ t ∈ Icc 0 T, ∀ x, ‖fderiv ℝ (X t 0) (X 0 t x)‖ ≤ D) →
      (∀ n j : ℕ, 1 ≤ j → j ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
        ‖iteratedFDeriv ℝ j (U t) x‖ ≤ R n * D ^ j) →
      TerminalMixedJetBound 0 T q 1 D A W U →
      ∀ (k : Vec3) {freq t₀ : ℝ}, 0 < freq → t₀ ∈ Icc 0 T →
        ‖labelWaveVector X 0 0 k t₀‖ = freq →
        let cap := terminalFlowTimeAmplitude q D A
        let F (t : ℝ) (x : Vec3) := fderiv ℝ (X 0 t) x
        let G (t : ℝ) (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
        let M (t : ℝ) (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
        let κ (t : ℝ) (x : Vec3) := freq⁻¹ • labelWaveVector X 0 x k t
        TerminalMixedJetBound 0 T q 16 D cap C F ∧
        TerminalMixedJetBound 0 T q 16 D cap C G ∧
        TerminalMixedJetBound 0 T q 16 D cap C M ∧
        TerminalMixedJetBound 0 T q 16 D cap C κ := by
  obtain ⟨Xcost, hXcost, hFlow⟩ := exists_forward_flowJetBounds R hR
  obtain ⟨S, hS, hBase⟩ := exists_parent_coefficientJetBounds R hR
  obtain ⟨Mcost, hMcost, hMat⟩ := exists_terminalMaterialPullbackCost (E := End)
    W (fun n => W (n+1)) Xcost hW (fun n => hW (n+1)) hXcost q
  let B : End →L[ℝ] End →L[ℝ] End := ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3
  let B' : End →L[ℝ] End →L[ℝ] End := -B.flip
  let Fcost := terminalLinearODECost B Mcost S q
  let Gcost := terminalLinearODECost B' Mcost S q
  have hFcost (n : ℕ) : 0 ≤ Fcost n := terminalLinearODECost_nonneg B hMcost hS q n
  have hGcost (n : ℕ) : 0 ≤ Gcost n := terminalLinearODECost_nonneg B' hMcost hS q n
  let C (n : ℕ) := Fcost n + Gcost n + Mcost n
  refine ⟨C, fun n => add_nonneg (add_nonneg (hFcost n) (hGcost n)) (hMcost n), ?_⟩
  intro U X T D A hT hT₁ hD hA hX hU hper hF hG hSpatial hTime k freq t₀ hf ht₀ hk cap F G M κ
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hA₀ : 0 ≤ A := zero_le_one.trans hA
  have hZero : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  let AM := A * D * (1 + D * A)^q
  let AF := D * AM^q
  have hAM : 1 ≤ AM :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hA hD)
      (one_le_pow₀ (le_add_of_nonneg_right (mul_nonneg hD₀ hA₀)))
  have hAM₀ : 0 ≤ AM := zero_le_one.trans hAM
  have hAF : 0 ≤ AF := mul_nonneg hD₀ (pow_nonneg hAM₀ _)
  have hcap₀ : 0 ≤ cap := by change 0 ≤ AM + AF + D * AF; positivity
  have hSpace := terminal_contDiffOn_spaceDerivative hT hU
  have hXjets (j : ℕ) (hj : 1 ≤ j) (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) :
      ‖iteratedFDeriv ℝ j (X 0 t) x‖ ≤ Xcost j * D ^ (5 * j) := by
    refine (hFlow hT hT₁ hD hX hU hper hF hG
      (fun n _ i hi hin => hSpatial n i (by omega) hin) j hj t ht x).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.sub_le _ _)) (hXcost j)
  have hMixedGrad : TerminalMixedJetBound 0 T q 1 D (A * D) (fun n => W (n+1))
      (fun t x => fderiv ℝ (U t) x) := by
    simpa only [pow_one] using hTime.spaceDerivative hT hU
  have hM : TerminalMixedJetBound 0 T q 16 D AM Mcost M :=
    (hMat (f := fun t x => fderiv ℝ (U t) x) hT hD (mul_nonneg hA₀ hD₀) hA₀ hX hU hSpace hper hTime hMixedGrad hXjets).mono_slope
      hD hAM₀ hMcost (by decide : 6 ≤ 16)
  have hFreg := hX.contDiffOn_forwardLabelDerivative hT hU hper
  have hGreg := hX.contDiffOn_inverseLabelDerivative hT hU hper
  have hMreg := hX.contDiffOn_materialGradient hT hU hper
  have hF₀ : TerminalMixedJetBound 0 T 0 16 D D S F := by
    apply TerminalMixedJetBound.of_zero
    intro n t ht x
    have h := (hBase hT hT₁ hD hX hU hper hF hG hSpatial k hf ht₀ hk n t ht x).1
    calc
      _ ≤ S n * D ^ (5 * n + 1) := h
      _ ≤ S n * D ^ (16 * n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hS n)
      _ = _ := by rw [pow_add, pow_one]; ring
  have hG₀ : TerminalMixedJetBound 0 T 0 16 D D S G := by
    apply TerminalMixedJetBound.of_zero
    intro n t ht x
    have h := (hBase hT hT₁ hD hX hU hper hF hG hSpatial k hf ht₀ hk n t ht x).2.1
    calc
      _ ≤ S n * D ^ (7 * n + 1) := h
      _ ≤ S n * D ^ (16 * n + 1) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hS n)
      _ = _ := by rw [pow_add, pow_one]; ring
  have hFq : TerminalMixedJetBound 0 T q 16 D AF Fcost F :=
    terminalMixedJetBound_of_linearODE (f := M) (g := F) B hT hD₀ hAM hD₀ hMcost hS hMreg hFreg
      (fun t ht x => ((hX.labelDerivative_evolves hT (hU.of_le (by simp)) hper hZero x).2 t ht).derivWithin
        (uniqueDiffOn_Icc hT t ht)) hF₀ q hM
  have hGq : TerminalMixedJetBound 0 T q 16 D AF Gcost G :=
    terminalMixedJetBound_of_linearODE (f := M) (g := G) B' hT hD₀ hAM hD₀ hMcost hS hMreg hGreg
      (fun t ht x => (hX.terminal_hasDerivWithinAt_inverseDeformation hT hU hper ht x).derivWithin
        (uniqueDiffOn_Icc hT t ht)) hG₀ q hM
  let kNorm := freq⁻¹ • k
  let adj := (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3))
  let L : End →L[ℝ] Vec3 := (ContinuousLinearMap.apply ℝ Vec3 kNorm).comp
    adj.toContinuousLinearEquiv.toContinuousLinearMap
  have hkn : ‖kNorm‖ ≤ D := by
    have h := (hX.norm_normalizedLabelWaveVector_bounds hT (hU.of_le (by simp)) hper ht₀ ht₀ 0 k hD hf hk
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t₀ ht₀ 0) (hG t₀ ht₀ 0)).1
    simpa only [kNorm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hf), div_eq_mul_inv, mul_comm] using h
  have hnormL : ‖L‖ ≤ D := L.opNorm_le_bound hD₀ fun v => by
    change ‖adj v kNorm‖ ≤ D * ‖v‖
    calc
      _ ≤ ‖adj v‖ * ‖kNorm‖ := (adj v).le_opNorm _
      _ ≤ ‖v‖ * D := by rw [adj.norm_map]; exact mul_le_mul_of_nonneg_left hkn (norm_nonneg _)
      _ = _ := mul_comm _ _
  have hκq : TerminalMixedJetBound 0 T q 16 D (D * AF) Gcost κ := by
    have hh := hGq.apply_clm hT hGreg L
    intro i hi n t ht x
    have hκeq (r : ℝ) (y : Vec3) : L (G r y) = κ r y := by
      change (G r y).adjoint (freq⁻¹ • k) = freq⁻¹ • labelWaveVector X 0 y k r
      exact labelWaveVector_smul X 0 r y k freq⁻¹
    refine ((hh.congr (fun r _ y => hκeq r y)) i hi n t ht x).trans ?_
    exact mul_le_mul_of_nonneg_right (by
      rw [show ‖L‖ * Gcost n * AF = Gcost n * (‖L‖ * AF) by ring]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hnormL hAF) (hGcost n))
      (pow_nonneg hD₀ _)
  have hcapF : AF ≤ cap := by change AF ≤ AM + AF + D * AF; linarith [mul_nonneg hD₀ hAF]
  have hcapM : AM ≤ cap := by change AM ≤ AM + AF + D * AF; linarith [mul_nonneg hD₀ hAF]
  have hcapκ : D * AF ≤ cap := by change D * AF ≤ AM + AF + D * AF; linarith
  exact ⟨(hFq.mono_amplitude hD₀ hFcost hcapF).mono_constant hD₀ hcap₀
      (fun n => by dsimp only [C]; linarith [hGcost n, hMcost n]),
    (hGq.mono_amplitude hD₀ hGcost hcapF).mono_constant hD₀ hcap₀
      (fun n => by dsimp only [C]; linarith [hFcost n, hMcost n]),
    (hM.mono_amplitude hD₀ hMcost hcapM).mono_constant hD₀ hcap₀
      (fun n => by dsimp only [C]; linarith [hFcost n, hGcost n]),
    (hκq.mono_amplitude hD₀ hGcost hcapκ).mono_constant hD₀ hcap₀
      (fun n => by dsimp only [C]; linarith [hFcost n, hMcost n])⟩

end

end TorusEuler

import TorusEuler.TerminalPhysicalTimeReadout

/-! Fixed-order constants for absorbing the exact mixed graph readout. -/

open Set
open TorusEuler.HierarchyTwistedProfile
open TorusEuler.HierarchyTwistedProfile.PhysicalApproximationData

namespace TorusEuler

noncomputable section

/-- The full fixed scalar in the mixed graph estimate. Putting the product
in one threshold row keeps the remaining exponent independent of depth. -/
def terminalGraphReadoutCost (q N : ℕ) (L parent M O R W : ℝ) : ℝ :=
  (3 * ((N : ℝ) + 1) + 6) * (1 + (2 : ℝ) ^ (N + q) * parent) ^ q *
    (parent + materialGraphFactor L N * q.factorial * M +
      materialGraphFactor (2 * L) N * q.factorial * O +
      materialGraphFactor (2 * L) N * q.factorial * R +
      materialGraphFactor (2 * L) N * q.factorial * W * Real.exp 3)

/-- The remaining old-parent power in the velocity and residual graph bounds. -/
def terminalGraphReadoutPower (q parentPower profilePower : ℕ) : ℕ :=
  1 + parentPower * q + max parentPower (q + profilePower)

set_option maxHeartbeats 2400000 in
/-- Once the whole fixed-order cost is bounded by the old frequency, the
three scalar graph bounds have a uniform power of the parent frequency. -/
theorem terminalGraphReadoutScalars_le
    {μ T freq next L parent M O R W : ℝ} {N q i m parentPower profilePower depth exponent : ℕ}
    (hμ : 1 ≤ μ) (hT : 0 < T) (hInv : T⁻¹ ≤ μ) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hp : 0 ≤ parent) (hM : 0 ≤ M) (hO : 0 ≤ O) (hR : 0 ≤ R) (hW : 0 ≤ W)
    (hCost : terminalGraphReadoutCost q N L parent M O R W ≤ μ)
    (hi : i ≤ q) (hm : m ≤ N) (hDepth : depth = 6 * exponent) (hNext : next = freq ^ exponent) :
    let η := μ ^ profilePower
    let ext := terminalTimeExtraction T q
    let D := parent * μ ^ parentPower
    let K := (1 + (2 : ℝ) ^ (N+q) * D) ^ i
    let Cmean := materialGraphFactor L N * (ext * (M * η)) * freq ^ (-5/2 : ℝ)
    let Cosc := materialGraphFactor (2*L) N * (ext * (O * η)) * freq ^ (-5/4 : ℝ)
    let Ctail := materialGraphFactor (2*L) N * (ext * (R * η)) * freq ^ hierarchyOscExponent (depth+1)
    let Cswitch := materialGraphFactor (2*L) N * (ext * (W * η)) *
      ((Real.exp 3 * next ^ (-4 : ℝ)) * freq ^ (-5/4 : ℝ))
    let power := terminalGraphReadoutPower q parentPower profilePower
    ((3 * (m+1) : ℝ) * (K * Cmean) ≤ μ ^ power * freq ^ (-5/2 : ℝ)) ∧
    ((3 * (m+1) : ℝ) * (K * (D + Cosc + Cmean)) ≤ μ ^ power) ∧
      6 * (K * (Ctail + Cswitch)) ≤ μ ^ power * next ^ (-4 : ℝ) := by
  intro η ext D K Cmean Cosc Ctail Cswitch power
  let E := max parentPower (q+profilePower)
  let F := (1 + (2 : ℝ) ^ (N+q) * parent) ^ q
  let V := 3 * ((N : ℝ)+1) + 6
  let uM := materialGraphFactor L N * q.factorial * M
  let uO := materialGraphFactor (2*L) N * q.factorial * O
  let uR := materialGraphFactor (2*L) N * q.factorial * R
  let uW := materialGraphFactor (2*L) N * q.factorial * W * Real.exp 3
  let U := parent + uM + uO + uR + uW
  have hμ₀ : 0 ≤ μ := zero_le_one.trans hμ
  have hf₀ := zero_lt_one.trans_le hf
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  have hNext₀ : 0 ≤ next := hNext ▸ pow_nonneg hf₀.le _
  have hγ₀ : 0 ≤ next ^ (-4 : ℝ) := Real.rpow_nonneg hNext₀ _
  have hM₀ : 0 ≤ uM := by dsimp [uM, materialGraphFactor]; positivity
  have hO₀ : 0 ≤ uO := by dsimp [uO, materialGraphFactor]; positivity
  have hR₀ : 0 ≤ uR := by dsimp [uR, materialGraphFactor]; positivity
  have hW₀ : 0 ≤ uW := by dsimp [uW, materialGraphFactor]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hD₀ : 0 ≤ D := by dsimp [D]; positivity
  have hK₀ : 0 ≤ K := by dsimp only [K]; positivity
  have hK : K ≤ F * μ ^ (parentPower*q) :=
    terminalGraphTimeFactor_le_of_parent hμ hp hD₀ hi le_rfl
  have hExt : ext ≤ (q.factorial : ℝ) * μ ^ q :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr hT.le) hInv _) (Nat.cast_nonneg _)
  have hExt₀ : 0 ≤ ext := by dsimp [ext, terminalTimeExtraction]; positivity
  have hm' : (3 * (m+1) : ℝ) ≤ V := by
    have hmR : (m : ℝ) ≤ N := by exact_mod_cast hm
    dsimp only [V]
    linarith only [hmR]
  have h6 : (6 : ℝ) ≤ V := le_add_of_nonneg_left (by positivity)
  have hU₀ : 0 ≤ U := by dsimp only [U]; positivity
  have hPcap (C : ℝ) (hC : 0 ≤ C) : ext * (C * η) ≤ (q.factorial : ℝ) * C * μ ^ E := by
    calc
      _ ≤ ((q.factorial : ℝ) * μ ^ q) * (C * η) :=
        mul_le_mul_of_nonneg_right hExt (by dsimp [η]; positivity)
      _ = (q.factorial : ℝ) * C * μ ^ (q+profilePower) := by dsimp [η]; rw [pow_add]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hμ (le_max_right _ _)) (by positivity)
  have hRateM : Cmean ≤ uM * μ ^ E * freq ^ (-5/2 : ℝ) := by
    dsimp only [Cmean, uM]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hPcap M hM)
      (by unfold materialGraphFactor; positivity)) (Real.rpow_nonneg hf₀.le _)).trans_eq (by ring)
  have hWave (β : ℝ) (hβ : β ≤ 0) : freq ^ β ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hf hβ
  have hPar : D ≤ parent * μ ^ E :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hμ (le_max_left _ _)) hp
  have hOsc : Cosc ≤ uO * μ ^ E := by
    dsimp only [Cosc, uO]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hPcap O hO)
      (by unfold materialGraphFactor; positivity)) (hWave _ (by norm_num))
      (Real.rpow_nonneg hf₀.le _) (by unfold materialGraphFactor; positivity)).trans_eq (by ring)
  have hMean : Cmean ≤ uM * μ ^ E :=
    hRateM.trans (mul_le_of_le_one_right (by positivity) (hWave _ (by norm_num)))
  have hTail : Ctail ≤ uR * μ ^ E * next ^ (-4 : ℝ) := by
    dsimp only [Ctail, uR]
    rw [terminalDepthTail_rpow hf₀ hDepth hNext, ← mul_assoc]
    exact (mul_le_mul_of_nonneg_right
      ((mul_le_mul (mul_le_mul_of_nonneg_left (hPcap R hR)
        (by unfold materialGraphFactor; positivity)) (hWave _ (by norm_num))
        (Real.rpow_nonneg hf₀.le _) (by unfold materialGraphFactor; positivity)).trans_eq (by ring))
      hγ₀)
  have hSwitch : Cswitch ≤ uW * μ ^ E * next ^ (-4 : ℝ) := by
    dsimp only [Cswitch, uW]
    exact (mul_le_mul (mul_le_mul_of_nonneg_left (hPcap W hW)
      (by unfold materialGraphFactor; positivity))
      (mul_le_of_le_one_right (by positivity) (hWave _ (by norm_num)))
      (by positivity) (by unfold materialGraphFactor; positivity)).trans_eq (by ring)
  have hUmean : uM ≤ U := by dsimp only [U]; linarith
  have hUvel : parent + uO + uM ≤ U := by dsimp only [U]; linarith
  have hUres : uR + uW ≤ U := by dsimp only [U]; linarith
  have hVel : D + Cosc + Cmean ≤ U * μ ^ E := by
    refine (add_le_add (add_le_add hPar hOsc) hMean).trans ?_
    simpa only [add_mul] using mul_le_mul_of_nonneg_right hUvel (pow_nonneg hμ₀ _)
  have hMean' : Cmean ≤ U * μ ^ E * freq ^ (-5/2 : ℝ) :=
    hRateM.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hUmean (pow_nonneg hμ₀ _))
      (Real.rpow_nonneg hf₀.le _))
  have hRes : Ctail + Cswitch ≤ U * μ ^ E * next ^ (-4 : ℝ) := by
    refine (add_le_add hTail hSwitch).trans ?_
    simpa only [add_mul] using mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hUres (pow_nonneg hμ₀ _)) hγ₀
  have hFullCost : V * F * U ≤ μ := hCost
  have hAny {c Z δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hV : c ≤ V)
      (hZ₀ : 0 ≤ Z) (hZ : Z ≤ U * μ ^ E * δ) :
      c * (K * Z) ≤ μ ^ power * δ := by
    calc
      _ ≤ V * ((F * μ ^ (parentPower*q)) * (U * μ ^ E * δ)) :=
        mul_le_mul hV (mul_le_mul hK hZ hZ₀ (by positivity))
          (by positivity) (hc.trans hV)
      _ = (V * F * U) * μ ^ (parentPower*q+E) * δ := by rw [pow_add]; ring
      _ ≤ μ * μ ^ (parentPower*q+E) * δ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hFullCost (pow_nonneg hμ₀ _)) hδ
      _ = _ := by
        change μ * μ ^ (parentPower*q+E) * δ = μ ^ (1+parentPower*q+E) * δ
        rw [show 1+parentPower*q+E = (parentPower*q+E)+1 by omega, pow_succ, mul_comm μ]
  have hCmean₀ : 0 ≤ Cmean := by dsimp only [Cmean, η]; unfold materialGraphFactor; positivity
  have hCosc₀ : 0 ≤ Cosc := by dsimp only [Cosc, η]; unfold materialGraphFactor; positivity
  have hCtail₀ : 0 ≤ Ctail := by dsimp only [Ctail, η]; unfold materialGraphFactor; positivity
  have hCswitch₀ : 0 ≤ Cswitch := by dsimp only [Cswitch, η]; unfold materialGraphFactor; positivity
  refine ⟨hAny (by positivity) (Real.rpow_nonneg hf₀.le _) hm' hCmean₀ hMean', ?_, ?_⟩
  · simpa only [mul_one] using hAny (by positivity : 0 ≤ (3 * (m+1) : ℝ)) zero_le_one hm'
      (by positivity) (by simpa only [mul_one] using hVel)
  · exact hAny (by norm_num) hγ₀ h6 (by positivity) hRes

end

end TorusEuler

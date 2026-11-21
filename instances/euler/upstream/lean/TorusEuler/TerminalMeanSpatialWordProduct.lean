import TorusEuler.EndpointPhysicalJetEstimates

/-! Ordered spatial Leibniz words for the time-differentiated mean forcing. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)

section LinearOperations

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {u : Vec3} {f df g dg : HalfHolder A E}

theorem endpointTorusHasSpatialDerivative.add
    (hf : endpointTorusHasSpatialDerivative u f df) (hg : endpointTorusHasSpatialDerivative u g dg) :
    endpointTorusHasSpatialDerivative u (f + g) (df + dg) := by
  intro a s
  simpa only [map_add, Pi.add_def] using (hf a s).add (hg a s)

theorem endpointTorusHasSpatialDerivative.sub
    (hf : endpointTorusHasSpatialDerivative u f df) (hg : endpointTorusHasSpatialDerivative u g dg) :
    endpointTorusHasSpatialDerivative u (f - g) (df - dg) := by
  intro a s
  simpa only [map_sub, Pi.sub_def] using (hf a s).sub (hg a s)

theorem endpointTorusHasSpatialDerivative.nsmul (c : ℕ)
    (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (c • f) (c • df) := by
  intro a s
  simpa only [map_nsmul] using (h a s).fun_const_smul c

theorem endpointTorusHasSpatialDerivative.finset_sum {ι : Type*} (s : Finset ι)
    (f df : ι → HalfHolder A E) (h : ∀ i ∈ s, endpointTorusHasSpatialDerivative u (f i) (df i)) :
    endpointTorusHasSpatialDerivative u (∑ i ∈ s, f i) (∑ i ∈ s, df i) := by
  intro a t
  simpa only [map_sum] using HasDerivAt.fun_sum (u := s) (fun i hi => h i hi a t)

end LinearOperations

/-- The full product rule includes the term with the undifferentiated
coefficient and all the terms with positive coefficient order. -/
def terminalMeanWordProduct {I : Type*} (C : List I → K½) (v : List I → W) (w : List I) : W :=
  (C []).coefficientMul (v w) + endpointMixedCorrection C v w

@[simp] theorem terminalMeanWordProduct_nil {I : Type*} (C : List I → K½) (v : List I → W) :
    terminalMeanWordProduct C v [] = (C []).coefficientMul (v []) := by
  simp [terminalMeanWordProduct, endpointMixedCorrection, endpointMixedCorrectionPairs]

/-- The product words are genuine spatial derivatives of the same
coefficient times velocity, with their original multiplicities. -/
theorem terminalMeanWordProduct_spatialDerivative {I : Type*} {N : ℕ} (u : I → Vec3)
    (C : List I → K½) (v : List I → W)
    (hC : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (C q) (C (i :: q)))
    (hv : ∀ i q, q.length < N → endpointTorusHasSpatialDerivative (u i) (v q) (v (i :: q)))
    (i : I) (w : List I) (hw : w.length < N) :
    endpointTorusHasSpatialDerivative (u i) (terminalMeanWordProduct C v w)
      (terminalMeanWordProduct C v (i :: w)) := by
  let d := ((endpointMixedCorrectionPairs w).map fun p =>
    (C (i :: p.1)).coefficientMul (v p.2) + (C p.1).coefficientMul (v (i :: p.2))).sum
  have hCorrection : endpointTorusHasSpatialDerivative (u i) (endpointMixedCorrection C v w) d :=
    endpointMixedCorrection_hasSpatialDerivative C v u i w
      (fun q hq => hC i q (hq.trans_lt hw)) (fun q hq => hv i q (hq.trans hw))
  have hRow : endpointMixedCorrection C v (i :: w) = (C [i]).coefficientMul (v w) + d :=
    endpointMixedCorrectionPairs_sum_cons i w fun p => (C p.1).coefficientMul (v p.2)
  intro a s
  have h₀ : ([] : List I).length < N := Nat.zero_lt_of_lt hw
  have hProd := (hC i [] h₀ a s).clm_apply (hv i w hw a s)
  rw [terminalMeanWordProduct, terminalMeanWordProduct, hRow]
  simp only [map_add, HalfHolder.eval_coefficientMul]
  convert hProd.add (hCorrection a s) using 1
  · rfl
  · abel

/-- The scaled product estimate charges one factor of two for the
half-Hölder multiplication and one term for each binary Leibniz choice. -/
theorem terminalMeanWordProduct_norm_le {I : Type*} (C : List I → K½) (v : List I → W) (w : List I)
    {ℓ K V : ℝ} (hℓ : 0 ≤ ℓ) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hC : ∀ q : List I, q.length ≤ w.length → ℓ ^ q.length * ‖C q‖ ≤ K)
    (hv : ∀ q : List I, q.length ≤ w.length → ℓ ^ q.length * ‖v q‖ ≤ V) :
    ℓ ^ w.length * ‖terminalMeanWordProduct C v w‖ ≤ (2 : ℝ) ^ (w.length + 1) * K * V := by
  let b := 2 * (K * V)
  have hb : 0 ≤ b := by dsimp only [b]; positivity
  have hPair (r s : List I) (h : r.length + s.length = w.length) :
      ℓ ^ w.length * (2 * ‖C r‖ * ‖v s‖) ≤ b := by
    calc
      _ = 2 * ((ℓ ^ r.length * ‖C r‖) * (ℓ ^ s.length * ‖v s‖)) := by
        rw [← h, pow_add]
        ring
      _ ≤ b := mul_le_mul_of_nonneg_left
        (mul_le_mul (hC r (by omega)) (hv s (by omega)) (by positivity) hK) zero_le_two
  have hScaledCorrection :
      ℓ ^ w.length * ‖endpointMixedCorrection C v w‖ ≤ ((endpointMixedCorrectionPairs w).length : ℝ) * b :=
    calc
      _ ≤ ℓ ^ w.length * ((endpointMixedCorrectionPairs w).map fun p => 2 * ‖C p.1‖ * ‖v p.2‖).sum :=
        mul_le_mul_of_nonneg_left (norm_endpointMixedCorrection_le C v w) (pow_nonneg hℓ _)
      _ ≤ ((endpointMixedCorrectionPairs w).map fun _ => b).sum := by
        rw [← List.sum_map_mul_left]
        exact List.sum_le_sum (fun p hp => hPair p.1 p.2 (endpointMixedCorrectionPairs_mem hp).2.1)
      _ = _ := by rw [List.map_const', List.sum_replicate, nsmul_eq_mul]
  have hCount : ((endpointMixedCorrectionPairs w).length : ℝ) + 1 = (2 : ℝ) ^ w.length := by
    exact_mod_cast endpointMixedCorrectionPairs_length_add_one w
  have hC0 : ‖(C []).coefficientMul (v w)‖ ≤ 2 * ‖C []‖ * ‖v w‖ :=
    (C []).coefficientMul.le_of_opNorm_le (HalfHolder.norm_coefficientMul_le _) _
  calc
    _ ≤ ℓ ^ w.length * (‖(C []).coefficientMul (v w)‖ + ‖endpointMixedCorrection C v w‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hℓ _)
    _ ≤ b + ((endpointMixedCorrectionPairs w).length : ℝ) * b := by
      rw [mul_add]
      exact add_le_add ((mul_le_mul_of_nonneg_left hC0 (pow_nonneg hℓ _)).trans
        (hPair [] w (by simp))) hScaledCorrection
    _ = (2 : ℝ) ^ (w.length + 1) * K * V := by
      rw [pow_succ, ← hCount]
      dsimp only [b]
      ring

/-- Smooth coefficient and velocity curves give smooth product word curves
on the same time set. -/
theorem contDiffOn_terminalMeanWordProduct {I : Type*} {n : ℕ∞ω} {s : Set ℝ}
    (C : List I → ℝ → K½) (v : List I → ℝ → W) (w : List I)
    (hC : ∀ q, q.length ≤ w.length → ContDiffOn ℝ n (C q) s)
    (hv : ∀ q, q.length ≤ w.length → ContDiffOn ℝ n (v q) s) :
    ContDiffOn ℝ n (fun t => terminalMeanWordProduct (fun q => C q t) (fun q => v q t) w) s := by
  exact ((HalfHolder.contDiffOn_coefficientMul (hC [] (Nat.zero_le _))).clm_apply (hv w le_rfl)).add
    (contDiffOn_endpointTemporalSpatialCorrection (fun q t => (C q t).coefficientMul) v w
      (fun q hq => HalfHolder.contDiffOn_coefficientMul (hC q hq)) (fun q hq => hv q hq.le))

/-- The scaled spatial product estimate is uniform on the closed time slab. -/
theorem terminalMeanWordProduct_closedTimeNorm_le {I : Type*} {T : ℝ} (hT : 0 ≤ T)
    (C : List I → ℝ → K½) (v : List I → ℝ → W) (w : List I)
    {ℓ K V : ℝ} (hℓ : 0 < ℓ) (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hCc : ∀ q, q.length ≤ w.length → ContinuousOn (C q) (Icc 0 T))
    (hvc : ∀ q, q.length ≤ w.length → ContinuousOn (v q) (Icc 0 T))
    (hC : ∀ q : List I, q.length ≤ w.length → ℓ ^ q.length * endpointClosedTimeNorm T (C q) ≤ K)
    (hv : ∀ q : List I, q.length ≤ w.length → ℓ ^ q.length * endpointClosedTimeNorm T (v q) ≤ V) :
    ℓ ^ w.length * endpointClosedTimeNorm T
      (fun t => terminalMeanWordProduct (fun q => C q t) (fun q => v q t) w) ≤
      (2 : ℝ) ^ (w.length + 1) * K * V := by
  have hℓw : 0 < ℓ ^ w.length := pow_pos hℓ _
  rw [mul_comm (ℓ ^ w.length), ← le_div_iff₀ hℓw]
  apply endpointClosedTimeNorm_le hT
  intro t ht
  rw [le_div_iff₀ hℓw, mul_comm ‖terminalMeanWordProduct (fun q => C q t) (fun q => v q t) w‖]
  exact terminalMeanWordProduct_norm_le (fun q => C q t) (fun q => v q t) w hℓ.le hK hV
    (fun q hq => (mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm (hCc q hq) ht)
      (pow_nonneg hℓ.le _)).trans (hC q hq))
    (fun q hq => (mul_le_mul_of_nonneg_left (norm_le_endpointClosedTimeNorm (hvc q hq) ht)
      (pow_nonneg hℓ.le _)).trans (hv q hq))

end

end TorusEuler

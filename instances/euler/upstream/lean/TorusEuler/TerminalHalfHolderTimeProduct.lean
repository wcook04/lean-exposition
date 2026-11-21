import TorusEuler.TerminalMeanTimeCalculus

/-! Time derivatives of the actual half-Hölder coefficient products. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "W" => HalfHolder Labels Vec3
local notation "K½" => HalfHolder Labels (Vec3 →L[ℝ] Vec3)
local notation "Time(" T ")" => Icc (0 : ℝ) T

private theorem terminalTimeJet_halfHolder_eval
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Time(T)) (a : Labels)
    {f : ℝ → HalfHolder Labels E} (hf : ContDiffOn ℝ ∞ f Time(T)) (n : ℕ) :
    terminalTimeJet T n (fun r => HalfHolder.eval a (f r)) t =
      HalfHolder.eval a (terminalTimeJet T n f t) :=
  terminalIteratedDerivWithin_clm (uniqueDiffOn_Icc hT) (HalfHolder.eval a) hf n ht

/-- The within-slab time jets of the actual half-Hölder multiplication
satisfy Leibniz's rule, including the two endpoint times. -/
theorem terminalTimeJet_coefficientMul {T : ℝ} (hT : 0 < T)
    {K : ℝ → K½} {v : ℝ → W}
    (hK : ContDiffOn ℝ ∞ K Time(T)) (hv : ContDiffOn ℝ ∞ v Time(T))
    (n : ℕ) (t : ℝ) (ht : t ∈ Time(T)) :
    terminalTimeJet T n (fun r => (K r).coefficientMul (v r)) t =
      ∑ i ∈ Finset.range (n + 1), n.choose i •
        (terminalTimeJet T i K t).coefficientMul (terminalTimeJet T (n - i) v t) := by
  apply HalfHolder.ext
  intro a
  let C (r : ℝ) : Vec3 →L[ℝ] Vec3 := HalfHolder.eval a (K r)
  let u (r : ℝ) : Vec3 := HalfHolder.eval a (v r)
  have hC : ContDiffOn ℝ ∞ C Time(T) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := K½) (F := Vec3 →L[ℝ] Vec3)
      (HalfHolder.eval a)).comp_contDiffOn hK
  have hu : ContDiffOn ℝ ∞ u Time(T) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := W) (F := Vec3)
      (HalfHolder.eval a)).comp_contDiffOn hv
  have hp : ContDiffOn ℝ ∞ (fun r => (K r).coefficientMul (v r)) Time(T) :=
    (HalfHolder.contDiffOn_coefficientMul hK).clm_apply hv
  calc
    _ = terminalTimeJet T n (fun r => C r (u r)) t := by
      rw [← terminalTimeJet_halfHolder_eval hT ht a hp n]
      simp only [HalfHolder.eval_coefficientMul, C, u]
    _ = ∑ i ∈ Finset.range (n + 1), n.choose i •
        terminalTimeJet T i C t (terminalTimeJet T (n - i) u t) :=
      terminalIteratedDerivWithin_clm_apply (uniqueDiffOn_Icc hT) hC hu n ht
    _ = _ := by
      simp only [map_sum, map_nsmul, HalfHolder.eval_coefficientMul, C, u,
        terminalTimeJet_halfHolder_eval hT ht a hK, terminalTimeJet_halfHolder_eval hT ht a hv]

/-- The same coefficient after time differentiation acts by the derivative
of the operator-valued half-Hölder multiplication curve. -/
theorem terminalTimeJet_coefficientMulL {T : ℝ} (hT : 0 < T) {K : ℝ → K½}
    (hK : ContDiffOn ℝ ∞ K Time(T)) (n : ℕ) (t : ℝ) (ht : t ∈ Time(T)) :
    terminalTimeJet T n (fun r => (K r).coefficientMul) t = (terminalTimeJet T n K t).coefficientMul := by
  induction n generalizing K with
  | zero => simp only [terminalTimeJet, iteratedDerivWithin_zero]
  | succ n ih =>
    let L : K½ →L[ℝ] (W →L[ℝ] W) := HalfHolder.coefficientMulL
    have hUpdate : EqOn (derivWithin (fun r => (K r).coefficientMul) Time(T))
        (fun r => (derivWithin K Time(T) r).coefficientMul) Time(T) := by
      intro r hr
      have hKDer := ((hK.differentiableOn (by simp)) r hr).hasDerivWithinAt
      have hLinear := ContinuousLinearMap.hasFDerivAt (𝕜 := ℝ) (E := K½) (F := W →L[ℝ] W)
        L (x := K r)
      have hLin := HasFDerivAt.comp_hasDerivWithinAt (𝕜 := ℝ)
        (F := K½) (E := W →L[ℝ] W) (f := K) r hLinear hKDer
      exact (hLin.derivWithin (uniqueDiffOn_Icc hT r hr))
    simp only [terminalTimeJet, iteratedDerivWithin_succ']
    rw [iteratedDerivWithin_congr hUpdate ht]
    exact ih (hK.derivWithin (uniqueDiffOn_Icc hT) (by simp))

end

end TorusEuler

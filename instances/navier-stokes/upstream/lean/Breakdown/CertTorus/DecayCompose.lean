import Breakdown.CertTorus.DecayStatements

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

theorem farFieldDecay_of_parts (hK : LerayKernelBound) (hKm : LerayKernelMeasurable)
    (hKs : KernelConvSup)
    (hMass : KernelMassBound) (hRad : RadialWeightBound)
    (hInner : KernelMassBound → RadialWeightBound → InnerSplitBound)
    (hOutF : OuterFarBound) (hOutN : OuterNearBound) (hSmall : SmallTimeIntegrable)
    (hOp : InnerSplitBound → OuterFarBound → OuterNearBound → SmallTimeIntegrable →
      OpWeightedBound)
    (hLin : LerayKernelMeasurable → InnerSplitBound → SmallTimeIntegrable → OpLinear)
    (hMeas : LerayKernelMeasurable → OpMeasurable)
    (hTW : TensorWeight)
    (hNeu : OpWeightedBound → OpLinear → OpMeasurable → TensorWeight → NeumannDecay)
    (hCD : LerayKernelMeasurable → KernelMassBound → KernelConvDeriv)
    (hPD : LerayKernelMeasurable → KernelConvSup → KernelConvDeriv → SmallTimeIntegrable →
      ProfileOpDeriv)
    (hRep : ProfileOpDeriv → DerivRepresentation)
    (hD1 : OpWeightedBound → FirstDerivBootstrap)
    (hD2 : OpWeightedBound → SecondDerivBootstrap)
    (hLap : PressureSumSecondPartials) (hDD : PressureSourceDivDiv) (hSrc : PressureSourceBound)
    (hTD : TensorDerivDecay)
    (hMV : HarmonicMeanValue) (hHG : HarmonicMeanValue → HarmonicGradientBound)
    (hTN : TruncatedNewton)
    (hId : HarmonicGradientBound → TruncatedNewton → PressureIdentification)
    (hNear : NewtonNear) (hFI : NewtonFarIdentity) (hFE : NewtonFarEstimate)
    (hFar : NewtonFarIdentity → NewtonFarEstimate → NewtonFar)
    (hCF : ClassFormOfWeights) : FarFieldDecay := by
  have hIn := hInner hMass hRad
  have hOpW := hOp hIn hOutF hOutN hSmall
  have hNeuD := hNeu hOpW (hLin hKm hIn hSmall) (hMeas hKm) hTW
  have hRepD := hRep (hPD hKm hKs (hCD hKm hMass) hSmall)
  have hD1' := hD1 hOpW
  have hD2' := hD2 hOpW
  have hIdD := hId (hHG hMV) hTN
  have hFarD := hFar hFI hFE
  intro W q P R hW
  have hS := hW.toIsSmoothOrbitField
  obtain ⟨C, hC⟩ := hS.deriv_bound
  have hbil : ∀ s y, W s y = profileOp 1 (pairTensor W W) s y := fun s y =>
    (hW.integral_eq s y).trans (profileBilin_eq_profileOp W W s y)
  have hmeas : Measurable (fun p : ℝ × Space => W p.1 p.2) :=
    hS.smooth_field.continuous.measurable
  have hbdd : ∃ C : ℝ, ∀ s y, ‖W s y‖ ≤ C := ⟨C, fun s y => by
    have h := hC 0 (by norm_num) s y
    rwa [norm_iteratedFDeriv_zero] at h⟩
  obtain ⟨A, hA⟩ := hNeuD hK W hmeas hbdd hS.tail hbil
  obtain ⟨K, -, hK0⟩ := hOpW hK 0 (by norm_num) (3 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hT := hTW W W (3 / 4) (3 / 4) A A (by norm_num) (by norm_num) hA hA
  have e0 : (3 / 4 : ℝ) + 3 / 4 = 3 / 2 := by norm_num
  rw [e0] at hT
  have hO := hK0 (pairTensor W W) (A * A) hT
  have e1 : (1 + ((0 : ℕ) : ℝ) / 2) = 1 := by norm_num
  have e2 : min (3 / 2 : ℝ) (((0 : ℕ) : ℝ) + 1) = 1 := by norm_num
  rw [e1, e2] at hO
  have h1 : WeightedBound W 1 (K * (A * A)) := by
    intro s y
    rw [hbil s y]
    exact hO s y
  have h2 : UniformDerivBound W 2 C := fun j hj => hC j (le_trans hj (by norm_num))
  have hRep' := hRepD hK W q P R hW
  obtain ⟨B1, hB1⟩ := hD1' hK W hS.smooth_field ⟨C, h2⟩ ⟨_, h1⟩ (fun s y v => (hRep' s y v).1)
  obtain ⟨B2, hB2⟩ := hD2' hK W hS.smooth_field ⟨C, h2⟩ ⟨_, h1⟩ ⟨B1, hB1⟩
    (fun s y v w => (hRep' s y v).2 w)
  obtain ⟨Cg, hCg⟩ := hSrc W hS.smooth_field B1 hB1
  obtain ⟨Af, hAf⟩ := hTD W hS.smooth_field _ _ _ h1 hB1 hB2
  obtain ⟨Cn, hCn⟩ := hNear
  obtain ⟨Cf, hCf⟩ := hFarD
  refine hCF W q ⟨_, h1⟩ ⟨B1, hB1⟩ ⟨B2, hB2⟩ ⟨Cn * Cg + Cf * Af, fun s y i => ?_⟩
  have hq : ContDiff ℝ ∞ (q s) :=
    hS.smooth_pressure.comp ((contDiff_const (c := s)).prodMk contDiff_id)
  have hid := hIdD (q s) (pressureSource W s) Cg hq (hCg s).1
    (fun y => hLap W q P R hS s y) (hS.pressure_sq s) (hCg s).2 i y
  have hn := hCn (pressureSource W s) Cg (hCg s).1.continuous (hCg s).2 i y
  have hf := hCf (pairTensor W W s) Af (hAf s).1 (hAf s).2 i y
  have hsplit : newtonGradientComp (pressureSource W s) i y =
      (∫ z, FundSol.kernelGrad (y - z) i * (nearCutoff y z * pressureSource W s z)) +
        ∫ z, FundSol.kernelGrad (y - z) i *
          ((1 - nearCutoff y z) * divDivSource (pairTensor W W s) z) := by
    rw [← integral_add hn.1 hf.1]
    unfold newtonGradientComp
    congr 1
    funext z
    rw [← hDD W q P R hS s z]
    ring
  rw [hid, abs_neg, hsplit]
  calc _ ≤ |∫ z, FundSol.kernelGrad (y - z) i * (nearCutoff y z * pressureSource W s z)| +
        |∫ z, FundSol.kernelGrad (y - z) i *
          ((1 - nearCutoff y z) * divDivSource (pairTensor W W s) z)| := abs_add_le _ _
    _ ≤ Cn * Cg / (1 + ‖y‖) ^ 3 + Cf * Af / (1 + ‖y‖) ^ 3 := add_le_add hn.2 hf.2
    _ = (Cn * Cg + Cf * Af) / (1 + ‖y‖) ^ 3 := by ring

end Breakdown.FarField

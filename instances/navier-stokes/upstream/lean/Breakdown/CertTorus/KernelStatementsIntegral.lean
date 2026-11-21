import Breakdown.CertTorus.KernelStatementsIdentify

open MeasureTheory Set Real Filter
open scoped ContDiff

noncomputable section

namespace Breakdown.FarField

open Freq

def similarityHeatPart (W : ℝ → Space → Space) (s T : ℝ) (y : Space) : Space :=
  (Real.sqrt (1 + T))⁻¹ • heatConv T (similarityShift W s T) y

def profileBilinTrunc (a b : ℝ → Space → Space) (T s : ℝ) (y : Space) : Space :=
  -∫ τ in Ioc (0 : ℝ) T,
    (1 + τ)⁻¹ • kernelConv τ (tensorField (similarityShift a s τ) (similarityShift b s τ)) y

def duhamelVelocityForm (W : ℝ → Space → Space) (s' s : ℝ) (y : Space) : Space :=
  dilateField (Real.exp (-(s - s'))) (heatConv (1 - Real.exp (-(s - s'))) (W s')) y +
    ∫ σ in s'..s, dilateField (Real.exp (-(s - σ)))
      (fun x => -kernelConv (1 - Real.exp (-(s - σ))) (tensorField (W σ) (W σ)) x) y

def IntervalIntegralL6 : Prop :=
  ∀ (f : ℝ → L6R) (a b : ℝ), a ≤ b → IntervalIntegrable f volume a b →
    ∀ G : ℝ → Space → Space, Measurable (fun p : ℝ × Space => G p.1 p.2) →
      (∀ σ ∈ Ioo a b, (f σ : Space → Space) =ᵐ[volume] G σ) →
        ((∫ σ in a..b, f σ : L6R) : Space → Space) =ᵐ[volume] fun y => ∫ σ in a..b, G σ y

def DuhamelVelocityAE : Prop :=
  ∀ (w : ℝ → X) (P : ℝ) (R : Space ≃ₗᵢ[ℝ] Space) (W : ℝ → Space → Space) (q : ℝ → Space → ℝ),
    realization.F.IsOrbit (realization.rot R) w P → IsSmoothOrbitField W q P R → IsVelocityOf w W →
      ∀ s' s : ℝ, s' < s → W s =ᵐ[volume] duhamelVelocityForm W s' s

def DuhamelChangeOfVariables : Prop :=
  ∀ W : ℝ → Space → Space, Continuous (fun p : ℝ × Space => W p.1 p.2) → ∀ C : ℝ,
    (∀ s y, ‖W s y‖ ≤ C) → ∀ s T : ℝ, 0 < T → ∀ y : Space,
      duhamelVelocityForm W (s - Real.log (1 + T)) s y =
        similarityHeatPart W s T y + profileBilinTrunc W W T s y

def DuhamelContinuous : Prop :=
  ∀ W : ℝ → Space → Space, Continuous (fun p : ℝ × Space => W p.1 p.2) → ∀ C : ℝ,
    (∀ s y, ‖W s y‖ ≤ C) → ∀ s T : ℝ, 0 < T →
      Continuous (fun y => similarityHeatPart W s T y + profileBilinTrunc W W T s y)

def HeatPartVanishes : Prop :=
  ∀ W : ℝ → Space → Space, Continuous (fun p : ℝ × Space => W p.1 p.2) → ∀ C : ℝ,
    (∀ s y, ‖W s y‖ ≤ C) → ∀ s : ℝ, ∀ y : Space,
      Tendsto (fun T => similarityHeatPart W s T y) atTop (nhds 0)

def TruncTendsto : Prop :=
  ∀ W : ℝ → Space → Space, Continuous (fun p : ℝ × Space => W p.1 p.2) → ∀ C : ℝ,
    (∀ s y, ‖W s y‖ ≤ C) → ∀ s : ℝ, ∀ y : Space,
      Tendsto (fun T => profileBilinTrunc W W T s y) atTop (nhds (profileBilin W W s y))

theorem integralEquationOfOrbit_of_duhamel (hA : DuhamelVelocityAE) (hB : DuhamelChangeOfVariables)
    (hC : DuhamelContinuous) (hD : HeatPartVanishes) (hE : TruncTendsto) :
    IntegralEquationOfOrbit := by
  intro w P R W q hO hS hV s y
  obtain ⟨C, hC0⟩ := hS.deriv_bound
  have hbd : ∀ s y, ‖W s y‖ ≤ C := by
    intro s y
    have h0 := hC0 0 (Nat.zero_le _) s y
    rwa [norm_iteratedFDeriv_zero] at h0
  have hcont : Continuous (fun p : ℝ × Space => W p.1 p.2) := hS.smooth_field.continuous
  have hslice : Continuous (W s) := hcont.comp (continuous_const.prodMk continuous_id)
  have key : ∀ T : ℝ, 0 < T →
      W s y = similarityHeatPart W s T y + profileBilinTrunc W W T s y := by
    intro T hT
    have hlog : 0 < Real.log (1 + T) := Real.log_pos (by linarith)
    have h1 := hA w P R W q hO hS hV (s - Real.log (1 + T)) s (by linarith)
    have h2 : W s =ᵐ[volume] fun y => similarityHeatPart W s T y + profileBilinTrunc W W T s y :=
      h1.trans (Filter.Eventually.of_forall fun y => hB W hcont C hbd s T hT y)
    have h3 := (Continuous.ae_eq_iff_eq volume hslice (hC W hcont C hbd s T hT)).mp h2
    exact congrFun h3 y
  have hlim := (hD W hcont C hbd s y).add (hE W hcont C hbd s y)
  rw [zero_add] at hlim
  have hev : (fun T => similarityHeatPart W s T y + profileBilinTrunc W W T s y) =ᶠ[atTop]
      fun _ => W s y :=
    (eventually_gt_atTop 0).mono fun T hT => (key T hT).symm
  exact tendsto_nhds_unique tendsto_const_nhds (hlim.congr' hev)

theorem integralEquationOfOrbit_of_kernel
    (hHB : HeatKernelBounds) (hHP : HeatKernelPartials) (hOdd : LerayKernelOdd)
    (hSc : KernelScaling) (hI6 : IntervalIntegralL6)
    (nB : HeatKernelBounds → LerayKernelBound)
    (nM : HeatKernelBounds → LerayKernelJointContinuous ∧ LerayKernelMeasurable)
    (nC1 : HeatKernelBounds → HeatKernelPartials → LerayKernelC1)
    (nDiv : HeatKernelBounds → HeatKernelPartials → LerayKernelC1 → LerayKernelDivFree)
    (nL1 : LerayKernelBound → LerayKernelMeasurable → KernelL1Bound)
    (nSup : KernelL1Bound → LerayKernelMeasurable → KernelConvSup)
    (nHT : HeatKernelBounds → HeatKernelPartials → HeatConvTest)
    (nHV : HeatKernelBounds → HeatConvTest → HeatVelocity)
    (nKC : HeatKernelBounds → HeatKernelPartials → KernelContraction)
    (nTD : LerayKernelBound → LerayKernelMeasurable → LerayKernelC1 → LerayKernelDivFree →
      KernelConvTestDecay)
    (nBT : HeatConvTest → KernelContraction → KernelConvTestDecay → LerayKernelOdd →
      LerayKernelBound → LerayKernelMeasurable → BilinTestKernel)
    (nLp : LerayKernelBound → LerayKernelMeasurable → KernelConvL3Pointwise)
    (nBK : BilinTestKernel → KernelConvL3Pointwise → BilinKernel)
    (nA : HeatVelocity → BilinKernel → IntervalIntegralL6 → LerayKernelMeasurable → KernelConvSup →
      DuhamelVelocityAE)
    (nCV : KernelScaling → KernelConvSup → LerayKernelBound → LerayKernelMeasurable →
      DuhamelChangeOfVariables)
    (nCo : HeatKernelBounds → KernelConvSup → LerayKernelBound → LerayKernelMeasurable →
      LerayKernelJointContinuous → DuhamelContinuous)
    (nH0 : HeatKernelBounds → HeatPartVanishes)
    (nTr : KernelConvSup → LerayKernelBound → LerayKernelMeasurable → TruncTendsto) :
    IntegralEquationOfOrbit := by
  have lB := nB hHB
  have lM := (nM hHB).2
  have lJ := (nM hHB).1
  have c1 := nC1 hHB hHP
  have dv := nDiv hHB hHP c1
  have l1 := nL1 lB lM
  have sup := nSup l1 lM
  have ht := nHT hHB hHP
  have hv := nHV hHB ht
  have kc := nKC hHB hHP
  have td := nTD lB lM c1 dv
  have bt := nBT ht kc td hOdd lB lM
  have lp := nLp lB lM
  have bk := nBK bt lp
  exact integralEquationOfOrbit_of_duhamel (nA hv bk hI6 lM sup) (nCV hSc sup lB lM)
    (nCo hHB sup lB lM lJ) (nH0 hHB) (nTr sup lB lM)

end Breakdown.FarField

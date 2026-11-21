import Breakdown.Uniqueness.RegDefs
import Breakdown.Uniqueness.RegPersistAuxDefs
import Breakdown.Uniqueness.RegCurve
import Breakdown.Uniqueness.RegAprioriAuxMildPart1
import Breakdown.Uniqueness.RegPhysAuxBasic
import Breakdown.Frac.StSpace
import Breakdown.Frac.StBilinH1

open scoped ContDiff ENNReal FourierTransform Topology
open MeasureTheory Set Real Filter

noncomputable section

namespace Breakdown.SmoothFlow

open Breakdown.Freq

def powerHeatSymbol (α t : ℝ) (ξ : Space) : ℝ := Real.exp (-(t * (2 * π * ‖ξ‖) ^ (2 * α)))

def IsPowerMildSymbol (α : ℝ) (F : ℝ → Space → CSpace) (a b : ℝ) : Prop :=
  ∀ t ∈ Icc a b, ∀ ξ, F t ξ = ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) • F a ξ +
    ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ

def powerHeatPart (α a : ℝ) (f : Space → CSpace) (t : ℝ) (ξ : Space) : CSpace :=
  ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) • f ξ

def powerMildMap (α a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace) (t : ℝ) (ξ : Space) :
    CSpace :=
  ((powerHeatSymbol α (t - a) ξ : ℝ) : ℂ) • F₀ ξ +
    ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (G s) ξ

def powerMildIntegral (α a : ℝ) (N : ℝ → Space → CSpace) (t : ℝ) (ξ : Space) : CSpace :=
  ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ

def IsPowerSymbolFlow (α : ℝ) (m : ℕ) (F : ℝ → Space → CSpace) (F₀ : Space → CSpace) (s : ℝ) :
    Prop :=
  IsHsCurve m F 0 s ∧ IsPowerMildSymbol α F 0 s ∧
    (∀ t ∈ Icc 0 s, IsSolenoidalSymbol (F t)) ∧ F 0 = F₀

def powerSymbol (α : ℝ) (f : Space → CSpace) (ξ : Space) : CSpace :=
  (((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) : ℂ) • f ξ

def powerTimeDerivSymbol (α : ℝ) (f : Space → CSpace) (ξ : Space) : CSpace :=
  -powerSymbol α f ξ + nonlinSymbol f ξ

def PowerHeatGainStatement (α : ℝ) : Prop :=
  ∀ T : ℝ, ∃ C : ℝ, ∀ τ : ℝ, 0 < τ → τ ≤ T → ∀ ξ : Space,
    ‖ξ‖ ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (1 / 2 : ℝ) * powerHeatSymbol α τ ξ ^ 2 ≤ C * τ ^ (-(3 / (2 * α)))

def PowerHeatPartStatement (α : ℝ) : Prop :=
  (∀ f : Space → CSpace, AEStronglyMeasurable f volume → ∀ a t : ℝ,
    AEStronglyMeasurable (powerHeatPart α a f t) volume) ∧
  (∀ (r : ℝ) (a t : ℝ), a ≤ t → ∀ f : Space → CSpace,
    fracNormSq r (powerHeatPart α a f t) ≤ fracNormSq r f) ∧
  (∀ (m : ℕ) (f : Space → CSpace), AEStronglyMeasurable f volume → hsNormSq m f < ⊤ →
    ∀ a b t₀ : ℝ, t₀ ∈ Icc a b →
      Tendsto (fun t => hsNormSq m (powerHeatPart α a f t - powerHeatPart α a f t₀))
        (𝓝[Icc a b] t₀) (𝓝 0))

def PowerMildGainStatement (α : ℝ) : Prop :=
  ∀ (F : ℝ → Space → CSpace) (a b : ℝ), IsHsCurve 3 F a b → IsPowerMildSymbol α F a b →
    (∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) → ∀ r : ℝ, 0 ≤ r → ∀ B : ℝ,
    (∀ s ∈ Icc a b, fracNormSq r (F s) ≤ ENNReal.ofReal B) →
    ∃ B' : ℝ, ∀ t ∈ Icc a b,
      fracNormSq (r + 1 / 2) (F t - powerHeatPart α a (F a) t) ≤ ENNReal.ofReal B'

def PowerPersistStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (F : ℝ → Space → CSpace) (a b : ℝ), IsHsCurve 3 F a b →
    IsPowerMildSymbol α F a b → (∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) →
    hsNormSq m (F a) < ⊤ → IsHsCurve m F a b

def PowerHeatBasicStatement (α : ℝ) : Prop :=
  (∀ t ξ, 0 ≤ powerHeatSymbol α t ξ) ∧
  (∀ t ξ, Continuous (fun s => powerHeatSymbol α (t - s) ξ)) ∧
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T t : ℝ, T ≤ t → ∀ ξ : Space,
    (1 + ‖ξ‖) * ∫ s in T..t, powerHeatSymbol α (t - s) ξ ≤ (t - T) + C * (t - T) ^ (1 - 1 / (2 * α))

def PowerMildBoundStatement (α : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : ℝ → CSpace) (a b T t M : ℝ) (ξ : Space),
    ContinuousOn φ (Icc a b) → a ≤ T → T ≤ t → t ≤ b → (∀ r ∈ Icc a T, φ r = 0) →
    (∀ r ∈ Icc T t, ‖φ r‖ ≤ M) →
    (1 + ‖ξ‖) * ‖∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • φ s‖ ≤
      M * ((t - T) + C * (t - T) ^ (1 - 1 / (2 * α)))

def PowerMildSubStatement (α : ℝ) : Prop :=
  ∀ (F G : ℝ → Space → CSpace) (a b : ℝ), IsHsCurve 3 F a b → IsHsCurve 3 G a b →
    IsPowerMildSymbol α F a b → IsPowerMildSymbol α G a b → F a = G a →
    ∀ t ∈ Icc a b, ∀ ξ : Space,
      F t ξ - G t ξ = ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) •
        (nonlinSymbol (F s) ξ - nonlinSymbol (G s) ξ)

def PowerMildUniqueStatement (α : ℝ) : Prop :=
  ∀ (F G : ℝ → Space → CSpace) (a b : ℝ), IsHsCurve 3 F a b → IsHsCurve 3 G a b →
    IsPowerMildSymbol α F a b → IsPowerMildSymbol α G a b →
    (∀ t ∈ Icc a b, IsSolenoidalSymbol (F t)) → (∀ t ∈ Icc a b, IsSolenoidalSymbol (G t)) →
    F a = G a → ∀ t ∈ Icc a b, F t = G t

def PowerHeatWeightStatement (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ a t : ℝ, a ≤ t → t ≤ a + 1 → ∀ ξ : Space,
    ∫⁻ s in Ioc a t, ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) * powerHeatSymbol α (t - s) ξ ^ 2) ≤
      ENNReal.ofReal C

def PowerHeatIntegralStatement (α : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (n : ℕ) (a t : ℝ), a ≤ t → t ≤ a + 1 → ∀ N : ℝ → Space → CSpace,
    Measurable (Function.uncurry N) → ∀ K : ℝ≥0∞, (∀ s ∈ Ioc a t, hsNormSq n (N s) ≤ K) →
    hsNormSq (n + 1) (fun ξ => ∫ s in a..t, ((powerHeatSymbol α (t - s) ξ : ℝ) : ℂ) • N s ξ) ≤
      ENNReal.ofReal C * ENNReal.ofReal (t - a) * K

def PowerMildMapBasicStatement (α : ℝ) : Prop :=
  (∀ (a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace), powerMildMap α a F₀ G a = F₀) ∧
  ∀ (a : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace) (t : ℝ), IsSolenoidalSymbol F₀ →
    (∀ s ∈ uIcc a t, ∀ᵐ η ∂volume, G s (-η) = conjVec (G s η)) →
    IsSolenoidalSymbol (powerMildMap α a F₀ G t)

def PowerMildMapEstStatement (α : ℝ) : Prop :=
  (∀ m : ℕ, 3 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (a δ B : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace), 0 < δ → δ ≤ 1 →
      AEStronglyMeasurable F₀ volume → IsHsCurve m G a (a + δ) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (G t) ≤ ENNReal.ofReal B) →
      ∀ t ∈ Icc a (a + δ),
        hsNormSq m (powerMildMap α a F₀ G t) ≤ 2 * hsNormSq m F₀ + ENNReal.ofReal (C * δ * B ^ 2)) ∧
  (∀ m : ℕ, 3 ≤ m → ∃ C : ℝ, 0 < C ∧
    ∀ (a δ B : ℝ) (F₀ : Space → CSpace) (G H : ℝ → Space → CSpace), 0 < δ → δ ≤ 1 →
      AEStronglyMeasurable F₀ volume → hsNormSq m F₀ < ⊤ →
      IsHsCurve m G a (a + δ) → IsHsCurve m H a (a + δ) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (G t) ≤ ENNReal.ofReal B) →
      (∀ t ∈ Icc a (a + δ), hsNormSq m (H t) ≤ ENNReal.ofReal B) →
      ∀ t ∈ Icc a (a + δ),
        hsNormSq m (powerMildMap α a F₀ G t - powerMildMap α a F₀ H t) ≤
          ENNReal.ofReal (C * δ * B) * ⨆ s ∈ Icc a (a + δ), hsNormSq m (G s - H s))

def PowerMildIntegralCurveStatement (α : ℝ) : Prop :=
  ∀ (n : ℕ) (a b : ℝ) (N : ℝ → Space → CSpace) (K : ℝ),
    AEStronglyMeasurable (fun p : Space × ℝ => N p.2 p.1)
      ((volume : Measure Space).prod (volume.restrict (Icc a b))) →
    (∀ s ∈ Icc a b, hsNormSq n (N s) ≤ ENNReal.ofReal K) →
    IsHsCurve (n + 1) (powerMildIntegral α a N) a b

def PowerMildMapCurveStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ (a δ : ℝ) (F₀ : Space → CSpace) (G : ℝ → Space → CSpace), 0 < δ →
    AEStronglyMeasurable F₀ volume → hsNormSq m F₀ < ⊤ → IsHsCurve m G a (a + δ) →
    IsHsCurve m (powerMildMap α a F₀ G) a (a + δ)

def PowerFixedPointStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ R : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (a : ℝ) (F₀ : Space → CSpace), AEStronglyMeasurable F₀ volume → IsSolenoidalSymbol F₀ →
      hsNormSq m F₀ ≤ ENNReal.ofReal R →
      ∃ G : ℝ → Space → CSpace, IsHsCurve m G a (a + δ) ∧
        (∀ t ∈ Icc a (a + δ), G t =ᵐ[volume] powerMildMap α a F₀ G t) ∧
        ∀ t ∈ Icc a (a + δ), ∀ᵐ ξ ∂volume, G t (-ξ) = conjVec (G t ξ)

def PowerLocalStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ R : ℝ, ∃ δ : ℝ, 0 < δ ∧
    ∀ (a : ℝ) (F₀ : Space → CSpace), AEStronglyMeasurable F₀ volume → IsSolenoidalSymbol F₀ →
      hsNormSq m F₀ ≤ ENNReal.ofReal R →
      ∃ F : ℝ → Space → CSpace, F a = F₀ ∧ IsHsCurve m F a (a + δ) ∧
        IsPowerMildSymbol α F a (a + δ) ∧ ∀ t ∈ Icc a (a + δ), IsSolenoidalSymbol (F t)

def PowerConcatStatement (α : ℝ) : Prop :=
  (∀ (F G : ℝ → Space → CSpace) (a b c : ℝ), a ≤ b → b ≤ c → IsHsCurve 3 F a b →
    IsHsCurve 3 G b c → IsPowerMildSymbol α F a b → IsPowerMildSymbol α G b c →
    G b = F b → IsPowerMildSymbol α (fun t => if t ≤ b then F t else G t) a c) ∧
  ∀ (F : ℝ → Space → CSpace) (a b b' : ℝ), b' ≤ b → IsPowerMildSymbol α F a b →
    IsPowerMildSymbol α F a b'

def PowerEnormMildStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∃ c : ℝ, 0 ≤ c ∧
    ∀ (T : ℝ) (F : ℝ → Space → CSpace) (t : ℝ), IsHsCurve m F 0 T →
      IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → t ∈ Icc 0 T →
      ∀ ξ, ‖F t ξ‖ₑ ≤ ‖F 0 ξ‖ₑ + ∫⁻ s in Ioo 0 t,
        ENNReal.ofReal (c * (t - s) ^ (-(1 / (2 * α)))) * convEnormSum (F s) ξ

def PowerHsMildStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∃ C : ℝ,
    ∀ (T : ℝ) (F : ℝ → Space → CSpace), IsHsCurve m F 0 T → IsPowerMildSymbol α F 0 T →
      (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → ∀ t ∈ Icc 0 T,
      hsNormSq m (F t) ^ (1 / 2 : ℝ) ≤ hsNormSq m (F 0) ^ (1 / 2 : ℝ) +
        ENNReal.ofReal C * ∫⁻ s in Ioo 0 t, ENNReal.ofReal ((t - s) ^ (-(1 / (2 * α)))) *
          freqL1Norm (F s) * hsNormSq m (F s) ^ (1 / 2 : ℝ)

def PowerAEMeasStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, IsHsCurve 1 F 0 T →
    IsPowerMildSymbol α F 0 T →
    AEMeasurable (fun p : ℝ × Space => ‖F p.1 p.2‖ₑ) ((volume.restrict (Icc 0 T)).prod volume)

def PowerPointwiseDerivStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, IsPowerMildSymbol α F 0 T → ∀ ξ : Space,
    ContinuousOn (fun s => nonlinSymbol (F s) ξ) (Icc 0 T) → ∀ t ∈ Icc 0 T,
    HasDerivWithinAt (fun τ => F τ ξ) (powerTimeDerivSymbol α (F t) ξ) (Icc 0 T) t

def PowerEnergyInequalityStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, IsHsCurve 1 F 0 T →
    IsPowerMildSymbol α F 0 T → ∀ ξ : Space,
    2 * ∫⁻ s in Icc 0 T, ENNReal.ofReal (‖ξ‖ ^ 2 * (2 * π * ‖ξ‖) ^ (2 * α)) * ‖F s ξ‖ₑ ^ 2 ≤
      ENNReal.ofReal (‖ξ‖ ^ 2) * ‖F 0 ξ‖ₑ ^ 2 +
        2 * ∫⁻ s in Icc 0 T, ENNReal.ofReal (‖ξ‖ ^ 2) * (‖F s ξ‖ₑ * ‖nonlinSymbol (F s) ξ‖ₑ)

def PowerDissipationStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ M T : ℝ, ∃ K : ℝ, ∀ T' ∈ Icc 0 T,
    ∀ F : ℝ → Space → CSpace, IsHsCurve m F 0 T' → IsPowerMildSymbol α F 0 T' →
      (∀ t ∈ Icc 0 T', IsSolenoidalSymbol (F t)) →
      (∀ t ∈ Icc 0 T', homNormSq 1 (F t) ≤ ENNReal.ofReal M) →
      ∫⁻ s in Icc 0 T', homNormSq 2 (F s) ≤ ENNReal.ofReal K

def PowerAprioriStatement (α : ℝ) : Prop :=
  ∀ (m : ℕ), 3 ≤ m → ∀ M T B₀ : ℝ, ∃ B : ℝ, ∀ T' ∈ Icc 0 T,
    ∀ F : ℝ → Space → CSpace, IsHsCurve m F 0 T' → IsPowerMildSymbol α F 0 T' →
      (∀ t ∈ Icc 0 T', IsSolenoidalSymbol (F t)) → hsNormSq m (F 0) ≤ ENNReal.ofReal B₀ →
      (∀ t ∈ Icc 0 T', homNormSq 1 (F t) ≤ ENNReal.ofReal M) →
      ∀ t ∈ Icc 0 T', hsNormSq m (F t) ≤ ENNReal.ofReal B

def PowerWeightCurveStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) →
    (∀ (k : ℕ), ∀ t ∈ Icc 0 T,
      HasDerivWithinAt (fun τ => toWeightL1 k (F τ)) (toWeightL1 k (powerTimeDerivSymbol α (F t)))
        (Icc 0 T) t) ∧
    ∀ (k n : ℕ), ContDiffOn ℝ n (fun τ => toWeightL1 k (F τ)) (Icc 0 T)

def PowerPhysPowerStatement (α : ℝ) : Prop :=
  ∀ f : Space → CSpace, MemLp f 1 (weightL1Measure 3) → ∀ x : Space,
    fractionalPowerAt α (physField f) x = physField (powerSymbol α f) x

def PowerPressureCurveStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → ∀ k n : ℕ,
    ContDiffOn ℝ n (fun τ => toWeightL1 k
      (fun ξ => pressureSymbol (F τ) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ))) (Icc 0 T)

def PowerPhysCurveStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) →
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physField (F z.1) z.2) (Icc 0 T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => physScalar (pressureSymbol (F z.1)) z.2)
      (Icc 0 T ×ˢ univ) ∧
    (∀ t ∈ Ioo 0 T, ∀ x : Space,
      HasDerivAt (fun τ => physField (F τ) x) (physField (powerTimeDerivSymbol α (F t)) x) t) ∧
    (∀ t ∈ Icc 0 T, Integrable (powerTimeDerivSymbol α (F t)) ∧ Integrable (advectionSymbol (F t)) ∧
      Integrable (powerSymbol α (F t)) ∧ Integrable (gradPressureSymbol (F t))) ∧
    (∀ t ∈ Icc 0 T, ∀ x : Space,
      fractionalPowerAt α (physField (F t)) x = physField (powerSymbol α (F t)) x) ∧
    ∀ t ∈ Icc 0 T, ∀ x : Space,
      gradientAt (physScalar (pressureSymbol (F t))) x = physField (gradPressureSymbol (F t)) x

def PowerSolutionOnStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) →
    FracSolutionOn α T (fun t => physField (F t)) (fun t => physScalar (pressureSymbol (F t)))

def PowerHeatXStatement (α : ℝ) : Prop :=
  ∀ (t : ℝ) (x : X), ((fracHeatX α t x : X) : Space → CSpace) =ᵐ[volume]
    fun ξ => ((fracHeatFactor α t ξ : ℝ) : ℂ) • ((x : X) : Space → CSpace) ξ

def PowerSolenoidalStatement (α : ℝ) : Prop :=
  (∀ τ : ℝ, Continuous (fracPhiFactor α τ)) ∧
  (∀ (τ : ℝ) (ξ : Space), fracPhiFactor α τ (-ξ) = fracPhiFactor α τ ξ) ∧
  (∃ C : ℝ, ∀ τ : ℝ, 0 < τ → ∀ ξ : Space, ‖fracPhiFactor α τ ξ‖ ≤ C * (1 + τ⁻¹)) ∧
  ∀ (A : Space → CSpace), MemLp A 1 volume → MemLp A 2 volume → (∀ ξ, A (-ξ) = conjVec (A ξ)) →
    ∀ τ : ℝ, 0 < τ →
    ((fracHeatSolenoidal α τ (toLpOrZero 2 (physField A)) : X) : Space → CSpace) =ᵐ[volume]
      fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • divFreeC ξ (A ξ)

def PowerBilinPhysStatement (α : ℝ) : Prop :=
  ∀ f : Space → CSpace, AEStronglyMeasurable f volume → IsSolenoidalSymbol f →
    (∀ m, hsNormSq m f < ⊤) → ∀ τ : ℝ, 0 < τ →
    ((fracBilinX α τ (embedX (physField f)) (embedX (physField f)) : X) : Space → CSpace)
      =ᵐ[volume] fun ξ => ((fracPhiFactor α τ ξ : ℝ) : ℂ) • nonlinSymbol f ξ

def PowerBilinContinuousStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) →
    (∀ t ∈ Icc 0 T, ContinuousOn
      (fun s => fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))))
      (Ico 0 t)) ∧
    ∃ C : ℝ, ∀ s ∈ Icc 0 T, ∀ τ : ℝ, 0 < τ →
      ‖fracBilinX α τ (embedX (physField (F s))) (embedX (physField (F s)))‖ ≤
        C * τ ^ (-(1 / (2 * α)))

def PowerBilinIntegralStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) → ∀ t ∈ Icc 0 T,
    IntervalIntegrable
      (fun s => fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s))))
      volume 0 t ∧
    (((∫ s in (0 : ℝ)..t,
        fracBilinX α (t - s) (embedX (physField (F s))) (embedX (physField (F s)))) : X) :
          Space → CSpace) =ᵐ[volume]
      fun ξ => ∫ s in (0 : ℝ)..t, ((fracPhiFactor α (t - s) ξ : ℝ) : ℂ) • nonlinSymbol (F s) ξ

def PowerIdentifyStatement (α : ℝ) : Prop :=
  ∀ (T : ℝ), 0 < T → ∀ F : ℝ → Space → CSpace, (∀ m, IsHsCurve m F 0 T) →
    IsPowerMildSymbol α F 0 T → (∀ t ∈ Icc 0 T, IsSolenoidalSymbol (F t)) →
    IsFracMildX α (fun t => embedX (physField (F t))) 0 T

def PowerFlowStatement (α : ℝ) : Prop :=
  (∀ (F : ℝ → Space → CSpace) (F₀ : Space → CSpace) (s : ℝ), IsPowerSymbolFlow α 3 F F₀ s →
    (∀ m, hsNormSq m F₀ < ⊤) → ∀ m, IsHsCurve m F 0 s) ∧
  ∀ (F₀ : Space → CSpace), AEStronglyMeasurable F₀ volume → IsSolenoidalSymbol F₀ →
    hsNormSq 3 F₀ < ⊤ → ∀ T M : ℝ, 0 < T →
    (∀ s ∈ Icc 0 T, ∀ F, IsPowerSymbolFlow α 3 F F₀ s → ∀ t ∈ Icc 0 s,
      homNormSq 1 (F t) ≤ ENNReal.ofReal M) →
    ∃ F, IsPowerSymbolFlow α 3 F F₀ T

end Breakdown.SmoothFlow

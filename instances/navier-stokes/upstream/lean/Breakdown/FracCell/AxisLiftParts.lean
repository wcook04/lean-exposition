import Breakdown.FracCell.OnAxisNorm

open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert Internal.SpectralBlocksMode

def liftVal (g : CellBlock) (χ : ℝ → ℝ) (v : ℕ → ℝ → ℝ) (r z : ℝ) : ℝ :=
  χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * v j z

def liftRad (g : CellBlock) (χ : ℝ → ℝ) (v : ℕ → ℝ → ℝ) (r z : ℝ) : ℝ :=
  deriv (fun t => χ (t / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), t ^ j * v j z) r

def liftHgt (g : CellBlock) (χ : ℝ → ℝ) (v : ℕ → ℝ → ℝ) (r z : ℝ) : ℝ :=
  χ (r / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), r ^ j * deriv (v j) z

def liftCoef (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (s : Fin 2) (c d : Fin 3) (t : Fin 2)
    (r z : ℝ) : ℝ :=
  if t = 0 then
    (if d = 0 then liftRad g χ (u s c) r z
      else if d = 2 then liftHgt g χ (u s c) r z
      else if c = 1 then liftVal g χ (u s 0) r z / r
      else if c = 0 then -(liftVal g χ (u s 1) r z / r) else 0)
  else 0

def liftGrad (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (y : Space) : Space →L[ℝ] Space :=
  ∑ s : Fin 2, Set.indicator (cellSolid g s)
    (fun w => ∑ c : Fin 3, ∑ d : Fin 3, (∑ t : Fin 2, trigMode t (g.mode * angleCoord w)
      * liftCoef g χ u s c d t (radialCoord w) (w 2)) • (innerSL ℝ (frameVector d w)).smulRight (frameVector c w)) y

def LiftGradStatement : Prop :=
  ∀ (g : CellBlock) (χ : ℝ → ℝ) (u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ) (ψ : Space → Space),
    g.innerRadius = 0 → g.mode = 0 → 0 < g.outerRadius → g.lowerHeight < g.upperHeight → 0 ≤ g.lowerHeight →
    χ 1 = 0 → (∃ K, LipschitzWith K χ) → (∀ s c j, ContDiff ℝ 1 (u s c j)) →
    (∀ s c j, u s c j (if s = 0 then g.lowerHeight else -g.upperHeight) = 0 ∧
      u s c j (if s = 0 then g.upperHeight else -g.lowerHeight) = 0) →
    (∀ s c, c ≠ 2 → u s c 0 = 0) →
    (∀ y, ψ y = ∑ s : Fin 2, Set.indicator (cellSolid g s)
      (fun w => ∑ c : Fin 3, (χ (radialCoord w / g.outerRadius)
        * ∑ j ∈ Finset.range (g.degree + 1), radialCoord w ^ j * u s c j (w 2)) • frameVector c w) y) →
    MemLp ψ 2 volume ∧ AEStronglyMeasurable (liftGrad g χ u) volume ∧
      Integrable (fun y => entrySq (liftGrad g χ u y)) ∧ IsWeakGradientOf ψ (liftGrad g χ u)

namespace Internal.AxisLiftParts

theorem val_cont (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {v : ℕ → ℝ → ℝ} (hv : ∀ j, Continuous (v j)) :
    Continuous (fun p : ℝ × ℝ => χ (p.1 / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), p.1 ^ j * v j p.2) := by
  refine (hχ.comp (continuous_fst.div_const _)).mul (continuous_finset_sum _ fun j _ => ?_)
  exact (continuous_fst.pow j).mul ((hv j).comp continuous_snd)

theorem rad_meas (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {v : ℕ → ℝ → ℝ} (hv : ∀ j, Continuous (v j)) :
    Measurable (fun p : ℝ × ℝ => liftRad g χ v p.1 p.2) := by
  have hc : Continuous (Function.uncurry fun (z t : ℝ) =>
      χ (t / g.outerRadius) * ∑ j ∈ Finset.range (g.degree + 1), t ^ j * v j z) :=
    (val_cont g hχ hv).comp continuous_swap
  exact (measurable_deriv_with_param hc).comp measurable_swap

theorem hgt_cont (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {v : ℕ → ℝ → ℝ}
    (hv : ∀ j, ContDiff ℝ 1 (v j)) : Continuous (fun p : ℝ × ℝ => liftHgt g χ v p.1 p.2) :=
  val_cont g hχ (v := fun j => deriv (v j)) fun j => (hv j).continuous_deriv le_rfl

theorem coef_meas (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ}
    (hu : ∀ s c j, ContDiff ℝ 1 (u s c j)) (s : Fin 2) (c d : Fin 3) (t : Fin 2) :
    Measurable (Function.uncurry (liftCoef g χ u s c d t)) := by
  have hv : ∀ c j, Continuous (u s c j) := fun c j => (hu s c j).continuous
  have hval : ∀ c, Measurable (fun p : ℝ × ℝ => liftVal g χ (u s c) p.1 p.2 / p.1) := fun c =>
    ((val_cont g hχ (hv c)).measurable).div measurable_fst
  unfold liftCoef
  split_ifs
  · exact rad_meas g hχ (hv c)
  · exact (hgt_cont g hχ (hu s c)).measurable
  · exact hval 0
  · exact (hval 1).neg
  · exact measurable_const
  · exact measurable_const

end Internal.AxisLiftParts

open Internal.AxisLiftParts in
theorem liftGrad_mode (g : CellBlock) {χ : ℝ → ℝ} (hχ : Continuous χ) {u : Fin 2 → Fin 3 → ℕ → ℝ → ℝ}
    (hu : ∀ s c j, ContDiff ℝ 1 (u s c j)) : ModeGradient g (liftGrad g χ u) :=
  ⟨liftCoef g χ u, fun s c d t => coef_meas g hχ hu s c d t, fun _ => rfl⟩

end Spectral

end CellCert

end Breakdown

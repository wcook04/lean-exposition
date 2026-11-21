import TorusEuler.PaperGenericWaveSwitch
import TorusEuler.PaperGenericSwitchCompletion

/-! Explicit cutoff identities for the completed leading wave. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile.PhysicalLeadingInput

open LocalizedAmplitude LocalizedAmplitude.SeedOn

set_option maxHeartbeats 900000

variable {T t₀ ell D C r h : ℝ} {hT : 0 < T}
  {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {center : ℝ → Vec3}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

/-- In the wrapped label coordinates, the curl completion of the leading wave is
`χ C[A₁]` and the completion switch is `χ' C[A₁]` for the very same seed and coframe. -/
theorem ofPaperCutoff_completed_eval
    (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    {t : ℝ} (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    let L := ofPaperCutoff g w reg χ hX hU hper hodd hAmp
    let A₁ := phaseTwistedPeriodizeCentered k (w.leading h)
    let C₁ := curlOfDerivative ((fderiv ℝ (fun b => wavePotential (K t b) (A₁ t b) s) a).comp
      (g.inverse.val.val.val (t, a, s)))
    (complete hT g.inverse g.covector g.oscillation.covector_independent g.oscillation.covector_ne_zero
      L.output.V).val.val.val (t, a, s) = χ.value t • C₁ ∧
    L.completionSwitch.val.val.val (t, a, s) = χ.derivative t • C₁ := by
  let L := ofPaperCutoff g w reg χ hX hU hper hodd hAmp
  have hMean : profilePhaseAverage hT (genericLeading reg k χ) = 0 := L.output.average_V
  constructor
  · exact complete_smul_wrapped_eval hT g.inverse g.covector (genericLeading reg k χ)
      g.oscillation.covector_independent g.oscillation.covector_ne_zero
      (κ := K) (c := χ.value) (raw := w.leading h) g.covector_value
      hMean ht (genericLeading_eval reg k χ ht) a s
  · exact complete_smul_wrapped_eval hT g.inverse g.covector (genericLeadingSwitch reg k χ)
      g.oscillation.covector_independent g.oscillation.covector_ne_zero
      (κ := K) (c := χ.derivative) (raw := w.leading h) g.covector_value
      (genericLeadingSwitch_average_zero reg χ) ht (genericLeadingSwitch_eval reg k χ ht) a s

/-- The two parts of the activation residual have the pointwise form
`χ' (A₁ + C[A₁])`, with the same wrapped unswitched wave in both terms. -/
theorem ofPaperCutoff_switch_eval
    (g : ParentGeometry hT U X k) (w : SeedOn M K center t₀ T ell D C)
    (reg : w.HierarchyRegularity r h) (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    {t : ℝ} (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    let L := ofPaperCutoff g w reg χ hX hU hper hodd hAmp
    let A₁ := phaseTwistedPeriodizeCentered k (w.leading h)
    let C₁ := curlOfDerivative ((fderiv ℝ (fun b => wavePotential (K t b) (A₁ t b) s) a).comp
      (g.inverse.val.val.val (t, a, s)))
    L.leadingSwitch.val.val.val (t, a, s) + L.completionSwitch.val.val.val (t, a, s) =
      χ.derivative t • (A₁ t a s + C₁) := by
  dsimp only
  have hv := genericLeadingSwitch_eval reg k χ ht a s
  have hc := (ofPaperCutoff_completed_eval g w reg χ hX hU hper hodd hAmp ht a s).2
  rw [hc, smul_add]
  exact congrArg (fun v : Vec3 => v + _) hv

/-- The first wave is unswitched, so both activation profiles vanish everywhere. -/
theorem ofPaperCutoff_first_switches_eq_zero
    (g : ParentGeometry hT U X k) (w : SeedOn M K center 0 T ell D C)
    (reg : w.HierarchyRegularity r h)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ I, Function.Even (w.amplitude t)) :
    let L := ofPaperCutoff g w reg (PaperWaveCutoff.first T) hX hU hper hodd hAmp
    L.leadingSwitch = 0 ∧ L.completionSwitch = 0 := by
  constructor
  · apply HierarchyTwistedProfile.ext
    rintro ⟨t,a,s⟩ hz
    change (genericLeadingSwitch reg k (PaperWaveCutoff.first T)).val.val.val (t, a, s) = 0
    rw [genericLeadingSwitch_eval reg k _ hz.1, PaperWaveCutoff.derivative_first, zero_smul]
  · apply HierarchyTwistedProfile.ext
    rintro ⟨t,a,s⟩ hz
    have hc := (ofPaperCutoff_completed_eval g w reg (PaperWaveCutoff.first T) hX hU hper hodd hAmp hz.1 a s).2
    exact hc.trans (by
      change (PaperWaveCutoff.first T).derivative t • _ = (0 : Vec3)
      rw [PaperWaveCutoff.derivative_first, zero_smul])

end TorusEuler.HierarchyTwistedProfile.PhysicalLeadingInput

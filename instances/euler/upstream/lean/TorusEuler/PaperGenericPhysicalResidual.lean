import TorusEuler.PaperGenericWaveSwitchIdentities
import TorusEuler.HierarchyPhysicalVelocityBounds

/-! The residual estimate of Lemma 5.8 for any smooth cutoff on the closed slab. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

namespace PaperWaveCutoff

variable {t₀ T : ℝ}

/-- The exact supremum of the weighted activation derivative. -/
def derivativeSize (χ : PaperWaveCutoff t₀ T) (γ : ℝ → ℝ) : ℝ :=
  ⨆ t : Icc t₀ T, |χ.derivative t| * γ t

theorem derivativeSize_bounds (χ : PaperWaveCutoff t₀ T) (hT : 0 < T)
    (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T) {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T))
    (hNonneg : ∀ t ∈ Icc t₀ T, 0 ≤ γ t) :
    0 ≤ χ.derivativeSize γ ∧ ∀ t ∈ Icc t₀ T, |χ.derivative t| * γ t ≤ χ.derivativeSize γ := by
  have hD := (χ.derivative_smooth hT).continuousOn.mono (Icc_subset_Icc_left ht₀)
  have hCompact := isCompact_Icc.image_of_continuousOn (hD.abs.mul hγ)
  have hBound : BddAbove (Set.range fun t : Icc t₀ T => |χ.derivative t| * γ t) := by
    apply hCompact.bddAbove.mono
    rintro _ ⟨t, rfl⟩
    exact ⟨t, t.property, rfl⟩
  have hPoint (t : ℝ) (ht : t ∈ Icc t₀ T) : |χ.derivative t| * γ t ≤ χ.derivativeSize γ :=
    le_ciSup hBound (⟨t, ht⟩ : Icc t₀ T)
  exact ⟨(mul_nonneg (abs_nonneg _) (hNonneg t₀ ⟨le_rfl, htT⟩)).trans
    (hPoint t₀ ⟨le_rfl, htT⟩), hPoint⟩

end PaperWaveCutoff

namespace HierarchyTwistedProfile.PhysicalApproximationData

open LocalizedAmplitude

variable {T : ℝ} {k : Vec3} {U : Velocity} {X : ℝ → Velocity} {q : Pressure}
  {depth : ℕ} {hT : 0 < T} {g : ParentGeometry hT U X k}

local notation "I" => Icc (0 : ℝ) T
local notation "J" => Set.prod I (univ : Set Vec3)
local notation "InvLabel" => (fun t => X t 0)
local notation "M" => (fun t a => fderiv ℝ (U t) (X 0 t a))
local notation "K" => (fun t a => labelWaveVector X 0 a k t)

private theorem paperCutoffSwitch_slice_eq
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofPaperCutoff g w reg χ hX hU hper hodd hAmp)
    {t : ℝ} (ht : t ∈ I) (a : Vec3) (s : ℝ) :
    slice (b.leading.leadingSwitch + b.leading.completionSwitch) t a s =
      χ.derivative t • activationPrimary (h := h) w g.inverse t a s := by
  change b.leading.leadingSwitch.val.val.val (t, a, s) +
    b.leading.completionSwitch.val.val.val (t, a, s) = _
  rw [hLeading]
  exact PhysicalLeadingInput.ofPaperCutoff_switch_eval g w reg χ hX hU hper hodd hAmp ht a s

/-- The actual residual is the hierarchy remainder and the exact cutoff derivative
times the unswitched leading velocity plus completion. -/
theorem residual_eq_graph_tail_add_paperCutoff
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h : ℝ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofPaperCutoff g w reg χ hX hU hper hodd hAmp)
    {t : ℝ} (ht : t ∈ I) :
    b.residual t = graphRead InvLabel (b.operators.remainder b.profiles depth) t +
      χ.derivative t • transportedProfile InvLabel k (activationPrimary (h := h) w g.inverse) t := by
  rw [b.residual_eq_graph_tail_add_switch]
  congr 1
  funext x
  exact b.paperCutoffSwitch_slice_eq w reg χ hX hU hper hodd hAmp hLeading ht _ _

/-- Lemma 5.8's residual estimate for any smooth closed-slab cutoff,
using the actual level tail and unswitched two-jet estimate. -/
theorem residual_holder_of_paperCutoff
    (b : PhysicalApproximationData g q depth)
    {t₀ ell D C r h freq L Ctail Cprimary Cstep : ℝ} {a p : ℕ} {center : ℝ → Vec3}
    (w : SeedOn M K center t₀ T ell D C) (reg : w.HierarchyRegularity r h)
    (χ : PaperWaveCutoff t₀ T)
    (hX : IsLabelFlowOn U X I) (hU : ContDiffOn ℝ ∞ (Function.uncurry U) J)
    (hper : ∀ t ∈ I, SpatiallyPeriodic (U t)) (hodd : ∀ t ∈ I, Function.Odd (U t))
    (hAmp : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t))
    (hLeading : b.leading = PhysicalLeadingInput.ofPaperCutoff g w reg χ hX hU hper hodd hAmp)
    (hD : 1 ≤ D) (hf : 1 ≤ freq) (hL : 1 ≤ L) (hCt : 0 ≤ Ctail) (hCp : 0 ≤ Cprimary)
    (hLabel : ell⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ)) (hCarrier : ‖k‖ ≤ D * freq)
    (hCoframe : ∀ t ∈ I, ∀ j ≤ (2 : ℕ), ∀ a,
      ell ^ j * ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ (X t 0) (X 0 t x)) a‖ ≤ L * D)
    (hTail : unweightedSeminorm False ell h 2 hT (b.operators.remainder b.profiles depth) ≤
      Ctail * freq ^ hierarchyOscExponent (depth + 1))
    {γ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T))
    (hPrimary : ∀ t ∈ Icc t₀ T, PhaseJetBound 2
      (γ t * (Cprimary * D ^ p * freq ^ (-5 / 4 : ℝ)))
      (scaledPhaseProfile ell h (activationPrimary (h := h) w g.inverse t)))
    (hγ₀ : ∀ t ∈ Icc t₀ T, 0 ≤ γ t)
    (hTailCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      ((4 : ℝ) ^ (2 : ℕ) * Ctail) * D ^ ((max a 1 + 1) * 2)) ≤ Cstep)
    (hPrimaryCap : 6 * ((((3 : ℝ) * 2 ^ (2 : ℕ) * (2 * L)) ^ (2 : ℕ)) *
      Cprimary * D ^ ((max a 1 + 1) * 2 + p)) ≤ Cstep) :
    ∀ t ∈ I, SpatialHolderHalf 1 (b.residual t) ∧ spatialHolderHalfNorm 1 (b.residual t) ≤
      Cstep * freq ^ (2 : ℝ) * (freq ^ (-2 * (depth : ℝ) / 3) + χ.derivativeSize γ) := by
  obtain ⟨hS, hSwitch⟩ := χ.derivativeSize_bounds hT reg.nonneg_start reg.start_lt_end.le hγ hγ₀
  have hReg (t : ℝ) (ht : t ∈ Icc t₀ T) (hσ : χ.derivative t ≠ 0) :
      ContDiff ℝ ∞ (Function.uncurry (activationPrimary (h := h) w g.inverse t)) := by
    let F := b.leading.leadingSwitch + b.leading.completionSwitch
    have hEq := b.paperCutoffSwitch_slice_eq w reg χ hX hU hper hodd hAmp hLeading
      ⟨reg.nonneg_start.trans ht.1, ht.2⟩
    have he : Function.uncurry (activationPrimary (h := h) w g.inverse t) =
        fun z => (χ.derivative t)⁻¹ • slice F t z.1 z.2 := by
      funext z
      change activationPrimary (h := h) w g.inverse t z.1 z.2 =
        (χ.derivative t)⁻¹ • slice F t z.1 z.2
      rw [hEq, smul_smul, inv_mul_cancel₀ hσ, one_smul]
    rw [he]
    exact (contDiff_slice F ⟨reg.nonneg_start.trans ht.1, ht.2⟩).const_smul (χ.derivative t)⁻¹
  exact b.residual_holder_of_measuredTail_and_primary hX hU hper reg.envelope_pos reg.phase_pos hD
    hf hL hCt hCp hS hLabel hWidth hCarrier hCoframe hTail hReg hPrimary hγ₀ hSwitch
    (fun _ ht hpre => χ.derivative_zero_before hT ht hpre)
    (fun _ ht => b.residual_eq_graph_tail_add_paperCutoff w reg χ hX hU hper hodd hAmp hLeading ht)
    hTailCap hPrimaryCap

end HierarchyTwistedProfile.PhysicalApproximationData

end

end TorusEuler

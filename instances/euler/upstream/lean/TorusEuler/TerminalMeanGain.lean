import TorusEuler.TerminalMeanTime
import TorusEuler.TerminalMeanTimeBounds
import TorusEuler.TerminalMeanTimeReadout
import TorusEuler.TerminalMeanParentInverseCaps
import TorusEuler.TerminalMeanHolderJetBridge

/-! The one-time-derivative gain for the selected physical mean. -/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

local notation "S" => endpointHalfHolderSolenoidal
local notation "Coeff" => Vec3 →L[ℝ] Vec3
local notation "Leray" => endpointStrongSpatialLeray

local instance terminalMeanGainSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance terminalMeanGainSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

set_option maxHeartbeats 5000000 in
/-- The actual selected mean uses time derivatives of the forcing only up to
`q - 1`. All coefficient costs have fixed parent powers, independently of
the retained level or the spatial jet order. -/
theorem selectedMean_timeJetSeminorm_le_of_holderCaps {T D ℓ h Ccoef Csrc Kcost Z : ℝ}
    {k : Vec3} {G M : HierarchyTwistedProfile T k Coeff}
    {κ force : HierarchyTwistedProfile T k Vec3} {hT : 0 < T} {d : MeanCoefficients G M}
    (r : MeanResult hT G M κ force d) (hT₁ : T ≤ 1) (hD : 1 ≤ D) (hℓ : 0 < ℓ)
    (hForce : (twistedHierarchyOperators hT G M κ).average force = force)
    (n q p : ℕ)
    (rec : EndpointPhysicalMeanRecovery hT D d.strain_bound d.deformation d.strain
      (fun t x => force.val.val.val (t,x,0)) r.rawVelocity)
    (inverse : TerminalMeanParentInverseData rec p)
    (hCoef : 0 ≤ Ccoef) (hSrc : 0 ≤ Csrc) (hKcost : 0 ≤ Kcost) (hZ : 0 ≤ Z)
    (hK0 : ∀ w, 1 ≤ w.length → w.length ≤ n → ∀ t ∈ Icc 0 T,
      D ^ p * (ℓ ^ w.length * (2 * ‖Leray‖ * ‖rec.jets.kinetic.curve w t‖)) ≤ Kcost)
    (hBaseK : ∀ w, 1 ≤ w.length → w.length ≤ n →
      D ^ p * (ℓ ^ w.length * endpointPhysicalCoefficientWordNorm T rec.jets.kinetic.curve
        rec.jets.vorticity.curve w) ≤ Kcost)
    (hTimeK : ∀ i ≤ q, ∀ w, w.length ≤ n → ∀ t ∈ Icc 0 T,
      ℓ ^ w.length * ‖terminalTimeJet T i (rec.jets.kinetic.curve w) t‖ ≤ Ccoef ∧
        ℓ ^ w.length * ‖terminalTimeJet T i (rec.jets.vorticity.curve w) t‖ ≤ Ccoef)
    (hTimeF : ∀ jet : EndpointSlabHalfHolderJets T coordinateDirection
        (fun z => d.deformation (z.1, toUnitTorus z.2)),
      ∀ i ≤ q, ∀ w, w.length ≤ n → ∀ t ∈ Icc 0 T,
        ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ Ccoef)
    (hTimeAdj : ∀ jet : EndpointSlabHalfHolderJets T coordinateDirection
        (fun z => (d.deformation (z.1, toUnitTorus z.2)).adjoint),
      ∀ i ≤ q - 1, ∀ w, w.length ≤ n → ∀ t ∈ Icc 0 T,
        ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ Ccoef)
    (hTimeForce : ∀ jet : EndpointSlabHalfHolderJets T coordinateDirection
        (fun z => force.val.val.val (z.1,z.2,0)),
      ∀ i ≤ q - 1, ∀ w, w.length ≤ n → ∀ t ∈ Icc 0 T,
        ℓ ^ w.length * ‖terminalTimeJet T i (jet.curve w) t‖ ≤ Csrc * Z) :
    let K0 := D ^ p * (1 + (2 : ℝ) ^ n * Kcost) ^ n
    let A := max K0 (K0 * ‖Leray‖)
    let B := (2 : ℝ) ^ (n + 1) * ((2 : ℝ) ^ q + (2 : ℝ) ^ q) * Ccoef
    let G0 := (2 : ℝ) ^ (n + 1 + (q - 1)) * Ccoef * (Csrc * Z)
    let C := (2 : ℝ) ^ (n + 1 + q) * Ccoef * ((1 + A * (1 + B)) ^ (q + 1) * G0)
    timeJetSeminorm hT q (unweightedSeminorm False ℓ h n hT) r.output.B ≤
      (((q : ℝ) + 1) * ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ)) * C := by
  intro K0 A B G0 C
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  let f (t : ℝ) (x : Vec3) := force.val.val.val (t,x,0)
  let F (z : ℝ × Vec3) := d.deformation (z.1, toUnitTorus z.2)
  let Fa (z : ℝ × Vec3) := (F z).adjoint
  have hF := d.deformation_smooth
  have hFa : ContDiffOn ℝ ∞ Fa (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    (ContinuousLinearMap.adjoint : Coeff ≃ₗᵢ[ℝ] Coeff).contDiff.comp_contDiffOn hF
  obtain ⟨hf, hfPer, _⟩ := meanSource_properties hT G M κ force hForce
  have hFPer (t : ℝ) (_ : t ∈ Icc 0 T) : SpatiallyPeriodic (fun x => F (t, x)) := by
    intro v x
    dsimp only [F]
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨v, rfl⟩]
  have hFaPer (t : ℝ) (ht : t ∈ Icc 0 T) :
      SpatiallyPeriodic (fun x => Fa (t, x)) := by
    intro v x
    exact congrArg ContinuousLinearMap.adjoint (hFPer t ht v x)
  obtain ⟨Jf⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection
    (fun z => f z.1 z.2) hf hfPer
  obtain ⟨JF⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection F hF hFPer
  obtain ⟨JFa⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection Fa hFa hFaPer
  obtain ⟨Jg, hSourceEq, hTimeEq⟩ := rec.exists_terminalTimeEquation hF hf hfPer
  obtain ⟨w⟩ := rec.words n
  have hG0 : 0 ≤ G0 := by dsimp only [G0]; positivity
  have hK0₀ : 0 ≤ K0 := by dsimp only [K0]; positivity
  have hPull (t : ℝ) (ht : t ∈ Icc 0 T) :
      Jg.curve [] t = (JFa.curve [] t).coefficientMul (Jf.curve [] t) := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [HalfHolder.eval_coefficientMul, Jg.eval_lift [] t ht x, JFa.eval_lift [] t ht x,
      Jf.eval_lift [] t ht x]
    rfl
  have hGcap := terminalMeanProductWords_timeJet_bound hT coordinateDirection n (q - 1)
    JFa.curve Jf.curve Jg.curve (fun s _ => JFa.smooth s) (fun s _ => Jf.smooth s)
    (fun s _ => Jg.smooth s) (fun i s _ => JFa.spatialDerivative i s)
    (fun i s _ => Jf.spatialDerivative i s) (fun i s _ => Jg.spatialDerivative i s)
    (fun t ht => hPull t ht) hℓ.le hCoef (mul_nonneg hSrc hZ) (hTimeAdj JFa) (hTimeForce Jf)
  have hμ : 0 < (D ^ 2)⁻¹ := inv_pos.mpr (pow_pos (zero_lt_one.trans_le hD) _)
  have hInitial := rec.terminalInitialWordBounds hT₁ n w Jg.curve
    (fun s => (Jg.smooth s).continuousOn) hSourceEq hμ inverse.hLK inverse.hLip rec.kinetic_coercive
    inverse.hSup inverse.eS inverse.heS inverse.hAs inverse.eM inverse.heM inverse.hAm inverse.hCap
    hℓ hKcost hG0 hBaseK (fun s hs t ht => by
      simpa only [terminalTimeJet, iteratedDerivWithin_zero] using hGcap 0 (Nat.zero_le _) s hs t ht)
  have hEq (i : ℕ) (_ : i < q) (t : ℝ) (ht : t ∈ Icc 0 T) :
      endpointStrongSpatialProjection
        ((rec.jets.kinetic.curve [] t).coefficientMul (terminalTimeJet T (i + 1) (w.curve []) t).val) =
      endpointStrongSpatialProjection
        ((∑ j ∈ Finset.range (i + 1), i.choose j • (terminalTimeJet T j (rec.jets.vorticity.curve []) t).coefficientMul
          (terminalTimeJet T (i - j) (w.curve []) t).val) + terminalTimeJet T i (Jg.curve []) t -
          ∑ j ∈ Finset.range (i + 1), (i + 1).choose (j + 1) •
            (terminalTimeJet T (j + 1) (rec.jets.kinetic.curve []) t).coefficientMul
              (terminalTimeJet T (i - j) (w.curve []) t).val) := by
    have hEqual (j : ℕ) : terminalTimeJet T j (w.curve []) t = terminalTimeJet T j rec.curve t :=
      iteratedDerivWithin_congr w.base_eq ht
    simpa only [hEqual, terminalTimeJet] using hTimeEq i t ht
  have hV := terminalMeanWords_timeJet_bound hT coordinateDirection n q rec.jets.kinetic.curve
    rec.jets.vorticity.curve Jg.curve w.curve (fun s _ => rec.jets.kinetic.smooth s)
    (fun s _ => rec.jets.vorticity.smooth s) (fun s _ => Jg.smooth s) w.smooth
    (fun i s _ => rec.jets.kinetic.spatialDerivative i s) (fun i s _ => rec.jets.vorticity.spatialDerivative i s)
    (fun i s _ => Jg.spatialDerivative i s) (fun i s hs t ht => w.spatial_derivative s hs i t ht)
    hEq inverse.eS inverse.heS hμ rec.kinetic_coercive hℓ.le inverse.hAsPower hKcost hCoef hG0 hK0₀
    hK0 hTimeK (fun i hi => hGcap i (by omega)) hInitial
  let BoundV := (1 + A * (1 + B)) ^ (q + 1) * G0
  have hA₀ : 0 ≤ A := hK0₀.trans (le_max_left _ _)
  have hB₀ : 0 ≤ B := by dsimp only [B]; positivity
  have hBaseV : 1 ≤ 1 + A * (1 + B) := le_add_of_nonneg_right (by positivity)
  have hBoundV : 0 ≤ BoundV := by dsimp only [BoundV]; positivity
  have hVcap (i : ℕ) (hi : i ≤ q) (s : List (Fin 3)) (hs : s.length ≤ n) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ℓ ^ s.length * ‖terminalTimeJet T i (w.curve s) t‖ ≤ BoundV := by
    have h := hV i hi s hs t ht
    have hAM : max K0 (D ^ p * ‖Leray‖ * (1 + (2 : ℝ) ^ n * Kcost) ^ n) = A := by
      dsimp only [K0, A]
      congr 1
      ring
    rw [hAM] at h
    exact h.trans (mul_le_mul_of_nonneg_right
      (pow_le_pow_right₀ hBaseV (Nat.succ_le_succ hi)) hG0)
  obtain ⟨Jb⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection
    (Function.uncurry r.rawMean) r.rawMean_smooth r.rawMean_periodic
  have hBpull (t : ℝ) (ht : t ∈ Icc 0 T) :
      Jb.curve [] t = (JF.curve [] t).coefficientMul (w.curve [] t).val := by
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [HalfHolder.eval_coefficientMul, Jb.eval_lift [] t ht x, JF.eval_lift [] t ht x]
    change r.rawMean t x = F (t,x) (HalfHolder.eval (toUnitTorus x) (w.curve [] t).val)
    rw [w.base_eq ht, r.rawMean_value t ht x]
    exact congrArg (F (t,x)) (congrArg (fun v : Velocity => v t x) rec.lift_eq)
  let Wv (s : List (Fin 3)) (t : ℝ) := (w.curve s t).val
  have hWV (s : List (Fin 3)) (hs : s.length ≤ n) : ContDiffOn ℝ ∞ (Wv s) (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (w.smooth s hs)
  have hWVcap (i : ℕ) (hi : i ≤ q) (s : List (Fin 3)) (hs : s.length ≤ n) (t : ℝ) (ht : t ∈ Icc 0 T) :
      ℓ ^ s.length * ‖terminalTimeJet T i (Wv s) t‖ ≤ BoundV := by
    have hJ : terminalTimeJet T i (Wv s) t = (terminalTimeJet T i (w.curve s) t).val :=
      terminalIteratedDerivWithin_clm (uniqueDiffOn_Icc hT) endpointHalfHolderSolenoidal.subtypeL
        (w.smooth s hs) i ht
    rw [hJ]
    exact hVcap i hi s hs t ht
  have hBcap := terminalMeanProductWords_timeJet_bound hT coordinateDirection n q JF.curve Wv Jb.curve
    (fun s _ => JF.smooth s) hWV (fun s _ => Jb.smooth s)
    (fun i s _ => JF.spatialDerivative i s)
    (fun i s hs t ht => w.spatial_derivative s hs i t ht)
    (fun i s _ => Jb.spatialDerivative i s) (fun t ht => hBpull t ht)
    hℓ.le hCoef hBoundV (hTimeF JF) hWVcap
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine (selectedMean_timeJetSeminorm_le_of_raw r hT₁ hℓ.le
    (C := ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ) * C)
    (mul_nonneg (Nat.cast_nonneg _) hC) n q (fun i hi => ?_)).trans_eq (by ring)
  exact Jb.slabTimeJet_labelNorm_le_of_wordCap hT r.rawMean_smooth hℓ.le n i hC
    (hBcap i hi)

end
end TorusEuler.HierarchyTwistedProfile

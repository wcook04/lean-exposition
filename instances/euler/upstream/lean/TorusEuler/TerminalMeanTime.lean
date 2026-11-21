import TorusEuler.EndpointPhysicalMeanEstimate
import TorusEuler.TerminalMeanTimeCalculus

/-! The higher time equations for the actual recovered physical mean. -/

open Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "S" => endpointHalfHolderSolenoidal
local notation "Coeff" => Vec3 →L[ℝ] Vec3
local notation "K½" => HalfHolder A Coeff
local notation "Time(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => Set.prod (Time(T)) (univ : Set Vec3)

local instance terminalMeanSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
local instance terminalMeanSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

private theorem terminalMeanCoefficientMul_jet {T t : ℝ} (hT : 0 < T) (ht : t ∈ Time(T))
    {K : ℝ → K½} (hK : ContDiffOn ℝ ∞ K Time(T)) (i : ℕ) :
    terminalTimeJet T i (fun r => (K r).coefficientMul) t =
      (terminalTimeJet T i K t).coefficientMul :=
  terminalIteratedDerivWithin_clm (F := K½) (G := C½ →L[ℝ] C½)
    (uniqueDiffOn_Icc hT) (HalfHolder.coefficientMulL : K½ →L[ℝ] (C½ →L[ℝ] C½)) hK i ht

set_option maxHeartbeats 5500000 in
/-- Differentiating the original projected mean equation gives the instantaneous
kinetic solve at time order `n + 1`. The forcing enters through order `n`
and consists of the actual deformation adjoint applied to the physical force. -/
theorem EndpointPhysicalMeanRecovery.exists_terminalTimeEquation {T D L : ℝ}
    {hT : 0 < T} {F M : ℝ × A → Coeff} {force v : Velocity}
    (rec : EndpointPhysicalMeanRecovery hT D L F M force v)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) Slab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) Slab(T))
    (hper : ∀ t ∈ Time(T), SpatiallyPeriodic (force t)) :
    let pull (z : ℝ × Vec3) := (F (z.1, toUnitTorus z.2)).adjoint (force z.1 z.2)
    ∃ jet : EndpointSlabHalfHolderJets T coordinateDirection pull,
      (∀ w, EqOn (rec.jets.source.curve w) (fun r => -endpointPrimitive (jet.curve w) r) Time(T)) ∧
      ∀ n t, t ∈ Time(T) →
        let K := rec.jets.kinetic.curve []
        let Ω := rec.jets.vorticity.curve []
        endpointStrongSpatialProjection ((K t).coefficientMul (terminalTimeJet T (n + 1) rec.curve t).val) =
          endpointStrongSpatialProjection
            ((∑ i ∈ Finset.range (n + 1), n.choose i •
              (terminalTimeJet T i Ω t).coefficientMul (terminalTimeJet T (n - i) rec.curve t).val) +
              terminalTimeJet T n (jet.curve []) t -
              ∑ i ∈ Finset.range (n + 1), (n + 1).choose (i + 1) •
                (terminalTimeJet T (i + 1) K t).coefficientMul (terminalTimeJet T (n - i) rec.curve t).val) := by
  intro pull
  have hAdj : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => (F (z.1, toUnitTorus z.2)).adjoint) Slab(T) :=
    (ContinuousLinearMap.adjoint : Coeff ≃ₗᵢ[ℝ] Coeff).contDiff.comp_contDiffOn hF
  have hPull : ContDiffOn ℝ ∞ pull Slab(T) := hAdj.clm_apply hforce
  have hPullPer (t : ℝ) (ht : t ∈ Time(T)) : SpatiallyPeriodic (fun x => pull (t, x)) := by
    intro p x
    dsimp only [pull]
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨p, rfl⟩, hper t ht p x]
  obtain ⟨jet⟩ := exists_endpointSlabHalfHolderJets hT coordinateDirection pull hPull hPullPer
  have hSrcEq : EqOn (rec.jets.source.curve [])
      (fun r => -endpointPrimitive (jet.curve []) r) Time(T) :=
    endpointSourceCurve_eq_negPrimitive_of_lift (rec.jets.source.curve []) (jet.curve [])
      (fun r x => pull (r, x)) (jet.smooth []).continuousOn
      (fun r hr x => jet.eval_lift [] r hr x)
      (fun r hr x => rec.jets.source.eval_lift [] r hr x)
  refine ⟨jet, ?_, ?_⟩
  · intro w
    exact endpointSourceWords_eq_negPrimitive hT rec.jets.source.curve jet.curve coordinateDirection w.length
      (fun r _ => (rec.jets.source.smooth r).differentiableOn (by simp))
      (fun r _ => (jet.smooth r).continuousOn)
      (fun i r _ => rec.jets.source.spatialDerivative i r)
      (fun i r _ => jet.spatialDerivative i r) hSrcEq w le_rfl
  intro n t ht K Ω
  obtain ⟨words⟩ := rec.words 0
  have hv : ContDiffOn ℝ ∞ rec.curve Time(T) :=
    (words.smooth [] (by simp)).congr (fun r hr => (words.base_eq hr).symm)
  have hK : ContDiffOn ℝ ∞ K Time(T) := rec.jets.kinetic.smooth []
  have hΩ : ContDiffOn ℝ ∞ Ω Time(T) := rec.jets.vorticity.smooth []
  let v₀ (r : ℝ) : C½ := (rec.curve r).val
  have hv₀ : ContDiffOn ℝ ∞ v₀ Time(T) :=
    endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn hv
  obtain ⟨c, hEq⟩ := rec.projected_integrated
  have hEq' (r : ℝ) (hr : r ∈ Time(T)) :
      endpointStrongSpatialLeray ((K r).coefficientMul (v₀ r)) =
        c.val + endpointStrongSpatialLeray (endpointPrimitive (fun s => (Ω s).coefficientMul (v₀ s)) r) +
          endpointStrongSpatialLeray (endpointPrimitive (jet.curve []) r) := by
    have eq := hEq r hr
    rw [hSrcEq hr, map_neg, sub_neg_eq_add] at eq
    exact congrArg (fun w : S => w.val) eq
  have hHigher := terminalProjectedHigherTimeDerivative (X := C½) (B := C½) hT endpointStrongSpatialLeray c.val
    (fun r => (K r).coefficientMul) (fun r => (Ω r).coefficientMul) v₀ (jet.curve [])
    (HalfHolder.contDiffOn_coefficientMul hK) (HalfHolder.contDiffOn_coefficientMul hΩ) hv₀ (jet.smooth [])
    hEq' n t ht
  have hJetV (i : ℕ) : terminalTimeJet T i v₀ t = (terminalTimeJet T i rec.curve t).val :=
    terminalIteratedDerivWithin_clm (F := S) (G := C½) (uniqueDiffOn_Icc hT)
      endpointHalfHolderSolenoidal.subtypeL hv i ht
  apply Subtype.ext
  change endpointStrongSpatialLeray _ = endpointStrongSpatialLeray _
  simpa only [terminalMeanCoefficientMul_jet hT ht hK, terminalMeanCoefficientMul_jet hT ht hΩ, hJetV]
    using hHigher

end

end TorusEuler

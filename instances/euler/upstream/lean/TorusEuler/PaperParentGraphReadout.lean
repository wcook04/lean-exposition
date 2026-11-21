import TorusEuler.PaperGraphReadout
import TorusEuler.PaperPhysicalParentInputs

/-! Lemma 5.7 with the actual coframe of a physical truncated parent. -/

open Set

namespace TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

open InductiveEulerStage

/-- The graph bounds apply to the actual inverse label flow of every physical
truncated parent. The parent coframe budget depends only on derivative order.
The unit weight gives the full-slab version. -/
theorem exists_paperLemma57_graphReadout {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] :
    ∃ L : ℕ → ℝ, (∀ n, 1 ≤ L n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {p : Pressure} {T D freq t₀ t : ℝ}
        {k : Vec3} {hT : 0 < T} {d : ParentGeometry hT U X k},
        TruncatedHierarchyParent d p D freq → t₀ ∈ Icc 0 T →
        ‖labelWaveVector X 0 0 k t₀‖ = freq →
        ∀ (a : ℕ), 7 ≤ a → ∀ (m : ℕ) (f : HierarchyTwistedProfile T k E)
          {τ : ℝ} (hτ : 0 ≤ τ) (hτT : τ ≤ T), t ∈ Icc τ T → ∀ (γ : ℝ → ℝ)
          (hγ : ContinuousOn γ (Icc τ T)) (hpos : ∀ s ∈ Icc τ T, 0 < γ s),
        let ell := (D ^ a)⁻¹
        let h := freq ^ (-1 / 2 : ℝ)
        let F := graphRead (fun s => X s 0) f t
        let N (n : ℕ) := amplitudeSeminorm False ell h n hT hτ hτT γ hγ hpos f
        let bound (factor : ℕ → ℝ) :=
          (∑ i : Fin m → Fin 3, spatialSupNorm (spatialDerivativeWord (List.ofFn i) F)) ≤
            (3 : ℝ) ^ m * factor m * γ t * N m ∧
          SpatialHolderHalf m F ∧
          spatialHolderHalfNorm m F ≤ (3 * (m + 1) : ℝ) * factor (m + 1) * γ t * N (m + 1)
        bound (fun n => oscillatoryGraphJetCost (L (m + 1)) n * D ^ ((max a 1 + 1) * n) *
          freq ^ ((3 : ℝ) * n / 2)) ∧
        (HierarchyPeriodicProfile.PhaseIndependent f.val.val →
          bound (fun n => meanGraphJetCost (L (m + 1)) n * D ^ ((a + 1) * n))) := by
  obtain ⟨R, C, e, _, hC, hInputs⟩ := exists_physicalParentInputs
  refine ⟨stageCoframeOrderConstant C, stageCoframeOrderConstant_ge_one C hC, ?_⟩
  intro U X p T D freq t₀ t k hT d data ht₀ hCarrier a ha m f τ hτ hτT ht γ hγ hpos
    ell h F N bound
  have inputs : PhysicalParentInputs d D freq a e R C := hInputs data ht₀ hCarrier a ha
  have hD : 1 ≤ D := one_le_two.trans data.scale_ge_two
  have hf := data.frequency_ge_one
  have hh : 0 < h := Real.rpow_pos_of_pos (zero_lt_one.trans_le hf) _
  have htFull : t ∈ Icc 0 T := ⟨hτ.trans ht.1, ht.2⟩
  have hL := stageCoframeOrderConstant_ge_one C hC (m + 1)
  refine ⟨paperLemma57_graphWeighted hT f hτ hτT γ hγ hpos ht inputs.radius_pos hh
    hD hf hL inputs.radius_inverse.le rfl inputs.carrier (inputs.inverse_smooth t htFull)
    (inputs.coframe_readout t htFull) (inputs.coframe_smooth t htFull)
    (inputs.scaled_coframe (m + 1) t htFull), fun hmean => ?_⟩
  exact paperLemma57_graphMeanWeighted hT f hmean hτ hτT γ hγ hpos ht inputs.radius_pos
    hD hL inputs.radius_inverse.le (inputs.inverse_smooth t htFull)
    (inputs.coframe_readout t htFull) (inputs.coframe_smooth t htFull)
    (inputs.scaled_coframe (m + 1) t htFull)

end TorusEuler.HierarchyTwistedProfile.TruncatedHierarchyParent

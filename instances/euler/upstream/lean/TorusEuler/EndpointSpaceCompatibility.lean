import TorusEuler.EndpointSpace
import TorusEuler.HalfHolderSpace
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-! Spatial compatibility for the fixed-time solve in Appendix A.2. -/

open BoundedContinuousFunction MeasureTheory Set
open scoped InnerProductSpace

namespace TorusEuler

local notation "A" => UnitAddTorus (Fin 3)
local notation "H" => Lp Vec3 2 unitTorusMeasure
local notation "C½" => HalfHolder A Vec3

/-- The Hölder representative of a fixed-time field determines an element of Haar (L^2). -/
noncomputable def endpointHalfHolderToL2 : C½ →L[ℝ] H :=
  (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ).comp
    ((ContinuousLinearMap.fst ℝ (A →ᵇ Vec3) (DistinctPairs A →ᵇ Vec3)).comp
      (halfHolderSubspace A Vec3).toSubmodule.subtypeL)

theorem endpointHalfHolderToL2_apply_ae (v : C½) :
    endpointHalfHolderToL2 v =ᵐ[unitTorusMeasure] fun x => HalfHolder.eval x v :=
  BoundedContinuousFunction.coeFn_toLp 2 unitTorusMeasure ℝ v.val.1

theorem endpointHalfHolderToL2_injective : Function.Injective endpointHalfHolderToL2 := by
  intro v w h
  change (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ) v.val.1 =
    (BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ) w.val.1 at h
  have h' : v.val.1 = w.val.1 :=
    BoundedContinuousFunction.toLp_injective unitTorusMeasure h
  exact HalfHolder.ext fun x => congrArg (fun f : A →ᵇ Vec3 => f x) h'

theorem norm_endpointHalfHolderToL2_le : ‖endpointHalfHolderToL2‖ ≤ 1 := by
  let L : (A →ᵇ Vec3) →L[ℝ] H := BoundedContinuousFunction.toLp 2 unitTorusMeasure ℝ
  have hL : ‖L‖ ≤ 1 := by
    have h := BoundedContinuousFunction.toLp_norm_le (p := 2) (𝕜 := ℝ) (E := Vec3) unitTorusMeasure
    rw [measureUnivNNReal, measure_univ, ENNReal.toNNReal_one, NNReal.coe_one, Real.one_rpow] at h
    exact h
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖L v.val.1‖ ≤ 1 * ‖v‖
  refine (L.le_of_opNorm_le hL v.val.1).trans ?_
  change 1 * ‖v.val.1‖ ≤ 1 * ‖v.val‖
  simpa only [one_mul] using norm_fst_le v.val

noncomputable def endpointSpatialDivergenceTest (p : EndpointSmoothPotential) :
    H →L[ℝ] ℝ :=
  innerSL ℝ ((endpointPotentialGradient p).toLp 2 unitTorusMeasure ℝ)

theorem endpointSpatialDivergenceTest_apply (p : EndpointSmoothPotential) (v : H) :
    endpointSpatialDivergenceTest p v =
      ∫ a, ⟪endpointPotentialGradient p a, v a⟫_ℝ ∂unitTorusMeasure := by
  change ⟪(endpointPotentialGradient p).toLp 2 unitTorusMeasure ℝ, v⟫_ℝ = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℝ) unitTorusMeasure
    (endpointPotentialGradient p)] with a ha
  rw [ha]

/-- The fixed-time weak divergence constraint on the spatial Hilbert space. -/
noncomputable def endpointSpatialSolenoidal : Submodule ℝ H :=
  ⨅ p : EndpointSmoothPotential, (endpointSpatialDivergenceTest p).ker

theorem isClosed_endpointSpatialSolenoidal :
    IsClosed (endpointSpatialSolenoidal : Set H) := by
  simp only [endpointSpatialSolenoidal, Submodule.coe_iInf]
  exact isClosed_iInter fun p => (endpointSpatialDivergenceTest p).isClosed_ker

theorem mem_endpointSpatialSolenoidal (v : H) :
    v ∈ endpointSpatialSolenoidal ↔ ∀ p : EndpointSmoothPotential,
      (∫ a, ⟪endpointPotentialGradient p a, v a⟫_ℝ ∂unitTorusMeasure) = 0 := by
  simp only [endpointSpatialSolenoidal, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, endpointSpatialDivergenceTest_apply]

/-- The closed subspace of spatial Hölder fields whose divergence vanishes weakly. -/
noncomputable def endpointHalfHolderSolenoidal : Submodule ℝ C½ :=
  endpointSpatialSolenoidal.comap endpointHalfHolderToL2.toLinearMap

theorem isClosed_endpointHalfHolderSolenoidal :
    IsClosed (endpointHalfHolderSolenoidal : Set C½) :=
  isClosed_endpointSpatialSolenoidal.preimage endpointHalfHolderToL2.continuous

theorem mem_endpointHalfHolderSolenoidal (v : C½) :
    v ∈ endpointHalfHolderSolenoidal ↔ ∀ p : EndpointSmoothPotential,
      (∫ a, ⟪endpointPotentialGradient p a, HalfHolder.eval a v⟫_ℝ ∂unitTorusMeasure) = 0 := by
  change endpointHalfHolderToL2 v ∈ endpointSpatialSolenoidal ↔ _
  rw [mem_endpointSpatialSolenoidal]
  exact forall_congr' fun p => by
    have heq : (fun a => ⟪endpointPotentialGradient p a, endpointHalfHolderToL2 v a⟫_ℝ)
        =ᵐ[unitTorusMeasure] fun a => ⟪endpointPotentialGradient p a, HalfHolder.eval a v⟫_ℝ := by
      filter_upwards [endpointHalfHolderToL2_apply_ae v] with a ha
      exact congrArg (fun w : Vec3 => ⟪endpointPotentialGradient p a, w⟫_ℝ) ha
    rw [integral_congr_ae heq]

/-- Compatibility of the solenoidal Hölder and Hilbert spaces in the fixed-time solve. -/
noncomputable def endpointSolenoidalEmbedding :
    endpointHalfHolderSolenoidal →L[ℝ] endpointSpatialSolenoidal :=
  endpointHalfHolderToL2.restrict fun _ hv => hv

theorem endpointSolenoidalEmbedding_injective : Function.Injective endpointSolenoidalEmbedding := by
  intro v w h
  apply Subtype.ext
  exact endpointHalfHolderToL2_injective (congrArg Subtype.val h)

theorem norm_endpointSolenoidalEmbedding_apply_le (v : endpointHalfHolderSolenoidal) :
    ‖endpointSolenoidalEmbedding v‖ ≤ ‖v‖ := by
  change ‖endpointHalfHolderToL2 v.val‖ ≤ ‖v.val‖
  simpa only [one_mul] using endpointHalfHolderToL2.le_of_opNorm_le
    norm_endpointHalfHolderToL2_le v.val

open Classical in
/-- The spatial (L^2) slice of a joint path, extended by zero on times
where the slice is not square integrable. -/
noncomputable def endpointSpatialSlice {T : ℝ} (v : EndpointTorusL2 T) (t : ℝ) : H :=
  if h : MemLp (fun a => v (t, a)) 2 unitTorusMeasure then h.toLp _ else 0

theorem endpointSpatialSlice_apply_ae {T : ℝ} (v : EndpointTorusL2 T) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
      (endpointSpatialSlice v t : A → Vec3) =ᵐ[unitTorusMeasure] fun a => v (t, a) := by
  classical
  have hv := Lp.memLp v
  have hsq := (memLp_two_iff_integrable_sq_norm hv.aestronglyMeasurable).mp hv
  filter_upwards [hv.aestronglyMeasurable.prodMk_left, hsq.prod_right_ae] with t hmeas hint
  have ht : MemLp (fun a => v (t, a)) 2 unitTorusMeasure :=
    (memLp_two_iff_integrable_sq_norm hmeas).mpr hint
  rw [endpointSpatialSlice, dite_eq_left ht]
  exact ht.coeFn_toLp

/-- A weakly solenoidal joint path is solenoidal for almost every time on
one common full-measure set for all spatial tests. -/
theorem ae_endpointSpatialSlice_solenoidal {T : ℝ} {v : EndpointTorusL2 T}
    (hv : v ∈ endpointTorusSpace T) :
    ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), endpointSpatialSlice v t ∈ endpointSpatialSolenoidal := by
  have htest (p : EndpointSmoothPotential) :
      ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)),
        endpointSpatialDivergenceTest p (endpointSpatialSlice v t) = 0 := by
    have hp := ((mem_endpointTorusSpace_iff_slices T v).mp hv).2 p
    filter_upwards [endpointSpatialSlice_apply_ae v, hp] with t hs ht
    rw [endpointSpatialDivergenceTest_apply]
    have heq : (fun a => ⟪endpointPotentialGradient p a, endpointSpatialSlice v t a⟫_ℝ)
        =ᵐ[unitTorusMeasure] fun a => ⟪endpointPotentialGradient p a, v (t, a)⟫_ℝ := by
      filter_upwards [hs] with a ha
      exact congrArg (fun w : Vec3 => ⟪endpointPotentialGradient p a, w⟫_ℝ) ha
    exact (integral_congr_ae heq).trans ht
  let bad (p : EndpointSmoothPotential) : Set H :=
    {w | endpointSpatialDivergenceTest p w ≠ 0}
  have hopen (p : EndpointSmoothPotential) : IsOpen (bad p) :=
    (isClosed_eq (endpointSpatialDivergenceTest p).continuous continuous_const).isOpen_compl
  let : SecondCountableTopology H :=
    @Lp.SecondCountableTopology A Vec3 _ _ unitTorusMeasure 2 _ ⟨ENNReal.ofNat_ne_top⟩ _ _
  obtain ⟨tests, hcount, hcover⟩ := TopologicalSpace.isOpen_iUnion_countable bad hopen
  have hp : ∀ᵐ t ∂(volume.restrict (Ioc (0 : ℝ) T)), ∀ p ∈ tests,
      endpointSpatialDivergenceTest p (endpointSpatialSlice v t) = 0 :=
    (ae_ball_iff hcount).mpr fun p _ => htest p
  filter_upwards [hp] with t ht
  change endpointSpatialSlice v t ∈ ⨅ p : EndpointSmoothPotential, (endpointSpatialDivergenceTest p).ker
  apply (Submodule.mem_iInf _).mpr
  intro p
  rw [LinearMap.mem_ker]
  by_contra h
  have hu : endpointSpatialSlice v t ∈ ⋃ q, bad q := mem_iUnion.mpr ⟨p, h⟩
  rw [← hcover] at hu
  obtain ⟨q, hq, hz⟩ := mem_iUnion₂.mp hu
  exact hz (ht q hq)

end TorusEuler

import TorusEuler.EndpointMixedEmbedding
import Mathlib.Topology.Order.ProjIcc

/-! Continuous time-dependent spatial Hölder fields as mixed path-space sources. -/

open BoundedContinuousFunction ContinuousLinearMap MeasureTheory Set
open scoped ENNReal

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "timeμ" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (timeμ T)

private theorem endpointTimeLp_norm_le {T C : ℝ} (hT : 0 ≤ T) (hC : 0 ≤ C)
    (v : Paths(T)) (hv : ∀ᵐ t ∂timeμ T, ‖v t‖ ≤ C) : ‖v‖ ≤ Real.sqrt T * C := by
  have h := Lp.norm_le_of_ae_bound hC hv
  have hmeasure : (measureUnivNNReal (timeμ T) : ℝ) = T := by
    rw [measureUnivNNReal, Measure.restrict_apply_univ, Real.volume_Ioc, sub_zero,
      ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_ofReal hT]
  simpa [hmeasure, Real.sqrt_eq_rpow, one_div] using h

/-- A continuous source on the slab has the canonical mixed representative.
Its norm is bounded by the spatial supremum times the square root of the
duration, and the joint embedding has the given spatial slices. -/
theorem exists_endpointMixedSource {T M : ℝ} (hT : 0 ≤ T) (hM : 0 ≤ M)
    (F : ℝ → C½) (hFc : ContinuousOn F (Icc 0 T)) (hF : ∀ t ∈ Icc 0 T, ‖F t‖ ≤ M) :
    ∃ f : HalfHolder A Paths(T),
      ‖f‖ ≤ Real.sqrt T * M ∧
      (∀ a, (fun t => HalfHolder.eval a f t) =ᵐ[timeμ T] fun t => HalfHolder.eval a (F t)) ∧
      (∀ᵐ t ∂timeμ T, endpointSpatialSlice (endpointMixedToJoint T f) t =
        endpointHalfHolderToL2 (F t)) := by
  let clamp := fun t => (projIcc 0 T hT t : ℝ)
  have hclamp : Continuous clamp := continuous_subtype_val.comp continuous_projIcc
  have hclampEq {t : ℝ} (ht : t ∈ Icc 0 T) : clamp t = t :=
    congrArg Subtype.val (projIcc_of_mem hT ht)
  let Fc := F ∘ clamp
  have hFc' : Continuous Fc := hFc.comp_continuous hclamp (fun t => (projIcc 0 T hT t).property)
  have hB (t : ℝ) : ‖Fc t‖ ≤ M := hF (clamp t) (projIcc 0 T hT t).property
  let toBCF : C½ →L[ℝ] (A →ᵇ Vec3) :=
    (fst ℝ (A →ᵇ Vec3) (DistinctPairs A →ᵇ Vec3)).comp
      (halfHolderSubspace A Vec3).toSubmodule.subtypeL
  have hJoint : Continuous (fun q : ℝ × A => HalfHolder.eval q.2 (Fc q.1)) := by
    have hEval : Continuous (fun p : (A →ᵇ Vec3) × A => p.1 p.2) := continuous_eval
    exact hEval.comp ((toBCF.continuous.comp hFc').prodMap continuous_id)
  have hlabel (a : A) : Continuous (fun t => HalfHolder.eval a (Fc t)) :=
    (HalfHolder.eval a).continuous.comp hFc'
  have hEval (a : A) (t : ℝ) : ‖HalfHolder.eval a (Fc t)‖ ≤ M :=
    ((HalfHolder.norm_le_iff hM).mp (hB t)).1 a
  have hDiff (a b : A) (t : ℝ) :
      ‖HalfHolder.eval a (Fc t) - HalfHolder.eval b (Fc t)‖ ≤ M * Real.sqrt (dist a b) :=
    ((HalfHolder.norm_le_iff hM).mp (hB t)).2 a b
  have hmem (a : A) : MemLp (fun t => HalfHolder.eval a (Fc t)) 2 (timeμ T) :=
    (hlabel a).aestronglyMeasurable |> fun h => MemLp.of_bound h M (Filter.Eventually.of_forall (hEval a))
  let v (a : A) : Paths(T) := (hmem a).toLp _
  have hv (a : A) : v a =ᵐ[timeμ T] fun t => HalfHolder.eval a (Fc t) :=
    (hmem a).coeFn_toLp
  have hvB (a : A) : ‖v a‖ ≤ Real.sqrt T * M :=
    endpointTimeLp_norm_le hT hM _ ((hv a).mono fun t ht => by rw [ht]; exact hEval a t)
  have hvD (a b : A) : ‖v a - v b‖ ≤ (Real.sqrt T * M) * Real.sqrt (dist a b) := by
    apply (endpointTimeLp_norm_le (C := M * Real.sqrt (dist a b))
      hT (by positivity) (v a - v b) ?_).trans_eq
    · ring
    · filter_upwards [hv a, hv b, Lp.coeFn_sub (v a) (v b)] with t ha hb hs
      rw [hs, Pi.sub_apply, ha, hb]
      exact hDiff a b t
  have hvc : Continuous v := by
    refine continuous_iff_continuousAt.mpr (fun a => ?_)
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (fun b => hvD b a) ?_
    have h : Continuous (fun b : A => (Real.sqrt T * M) * Real.sqrt (dist b a)) :=
      continuous_const.mul (Real.continuous_sqrt.comp (continuous_id.dist continuous_const))
    simpa only [dist_self, Real.sqrt_zero, mul_zero] using h.continuousAt (x := a).tendsto
  let f : HalfHolder A Paths(T) := HalfHolder.ofBound ⟨v, hvc⟩ hvB hvD
  have hfEval (a : A) : HalfHolder.eval a f = v a := rfl
  refine ⟨f, (HalfHolder.norm_le_iff (by positivity)).mpr ⟨hvB, hvD⟩, ?_, ?_⟩
  · intro a
    rw [hfEval]
    filter_upwards [hv a, ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht hdom
    simpa only [Fc, Function.comp_apply, hclampEq (Ioc_subset_Icc_self hdom)] using ht
  · let u := endpointMixedToJoint T f
    let u0 := (Lp.aestronglyMeasurable u).mk u
    have h0 : (u : ℝ × A → Vec3) =ᵐ[endpointTorusMeasure T] u0 :=
      (Lp.aestronglyMeasurable u).ae_eq_mk
    have hMeas : MeasurableSet {p : ℝ × A | u0 p = HalfHolder.eval p.2 (Fc p.1)} :=
      measurableSet_eq_fun (Lp.aestronglyMeasurable u).measurable_mk hJoint.measurable
    have ha : ∀ᵐ a ∂unitTorusMeasure, ∀ᵐ t ∂timeμ T, u0 (t, a) = HalfHolder.eval a (Fc t) := by
      filter_upwards [ae_endpointTimeSlice_congr h0, endpointMixedToJoint_apply_ae f] with a h0a hfa
      filter_upwards [h0a, hfa, hv a] with t h0t hft hvt
      exact h0t.symm.trans (hft.symm.trans (by simpa only [hfEval] using hvt))
    have h' : u0 =ᵐ[endpointTorusMeasure T] fun q => HalfHolder.eval q.2 (Fc q.1) :=
      (Measure.ae_prod_iff_ae_ae hMeas).mpr ((Measure.ae_ae_comm hMeas).mpr ha)
    filter_upwards [endpointSpatialSlice_apply_ae u, Measure.ae_ae_of_ae_prod (h0.trans h'),
      ae_restrict_mem (μ := volume) measurableSet_Ioc] with t ht heq ht0
    apply Lp.ext
    filter_upwards [ht, heq, endpointHalfHolderToL2_apply_ae (F t)] with a ha hb hc
    exact ha.trans (hb.trans (by
      simpa only [Fc, Function.comp_apply, hclampEq (Ioc_subset_Icc_self ht0)] using hc.symm))

end

end TorusEuler

import TorusEuler.LinearFlowExistence
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.ProjIcc

/-! Smooth dependence of a forced linear ODE in the uniform norm on a closed time slab. -/

open Set MeasureTheory
open scoped ContDiff

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private abbrev Slab (T : ℝ) := Icc (0 : ℝ) T
private abbrev SlabPath (T : ℝ) (E : Type*) [TopologicalSpace E] := C(Slab T, E)

private noncomputable def extendSlabPath {T : ℝ} (hT : 0 ≤ T) (x : SlabPath T E) (t : ℝ) : E :=
  x (projIcc 0 T hT t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
private theorem continuous_extendSlabPath {T : ℝ} (hT : 0 ≤ T) (x : SlabPath T E) :
    Continuous (extendSlabPath hT x) :=
  x.continuous.comp continuous_projIcc

private noncomputable def slabPrimitive {T : ℝ} (hT : 0 ≤ T) :
    SlabPath T E →L[ℝ] SlabPath T E := by
  let J : SlabPath T E →ₗ[ℝ] SlabPath T E :=
    { toFun := fun x =>
        ⟨fun t => ∫ u in 0..(t : ℝ), extendSlabPath hT x u,
          (intervalIntegral.continuous_primitive
            (continuous_extendSlabPath hT x).intervalIntegrable 0).comp continuous_subtype_val⟩
      map_add' := fun x y => by
        ext t
        exact intervalIntegral.integral_add
          ((continuous_extendSlabPath hT x).intervalIntegrable 0 t)
          ((continuous_extendSlabPath hT y).intervalIntegrable 0 t)
      map_smul' := fun c x => by
        ext t
        exact intervalIntegral.integral_smul c (extendSlabPath hT x) }
  exact J.mkContinuous T fun x => ((J x).norm_le (mul_nonneg hT (norm_nonneg x))).2 fun t => by
    change ‖∫ u in 0..(t : ℝ), extendSlabPath hT x u‖ ≤ T * ‖x‖
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := 0) (b := (t : ℝ)) (f := extendSlabPath hT x)
      (fun u _ => x.norm_coe_le_norm (projIcc 0 T hT u))
    rw [sub_zero, abs_of_nonneg t.property.1, mul_comm ‖x‖] at h
    exact h.trans (mul_le_mul_of_nonneg_right t.property.2 (norm_nonneg x))

omit [CompleteSpace E] in
private theorem slabPrimitive_apply {T : ℝ} (hT : 0 ≤ T) (x : SlabPath T E) (t : Slab T) :
    slabPrimitive hT x t = ∫ u in 0..(t : ℝ), extendSlabPath hT x u := rfl

private noncomputable def slabAction {T : ℝ} (A : SlabPath T (E →L[ℝ] E)) :
    SlabPath T E →L[ℝ] SlabPath T E := by
  let L : SlabPath T E →ₗ[ℝ] SlabPath T E :=
    { toFun := fun x => ⟨fun t => A t (x t), A.continuous.clm_apply x.continuous⟩
      map_add' := fun x y => by ext t; exact (A t).map_add (x t) (y t)
      map_smul' := fun c x => by ext t; exact (A t).map_smul c (x t) }
  exact L.mkContinuous ‖A‖ fun x =>
    ((L x).norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg x))).2 fun t =>
      ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t) (x.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))

omit [CompleteSpace E] in
private theorem slabAction_apply {T : ℝ} (A : SlabPath T (E →L[ℝ] E)) (x : SlabPath T E) (t : Slab T) :
    slabAction A x t = A t (x t) := rfl

private noncomputable def slabActionLinear {T : ℝ} :
    SlabPath T (E →L[ℝ] E) →L[ℝ] (SlabPath T E →L[ℝ] SlabPath T E) := by
  let L : SlabPath T (E →L[ℝ] E) →ₗ[ℝ] (SlabPath T E →L[ℝ] SlabPath T E) :=
    { toFun := slabAction
      map_add' := fun A B => by
        ext x t
        simp only [add_apply, slabAction_apply, ContinuousMap.add_apply]
      map_smul' := fun c A => by
        ext x t
        simp only [smul_apply, slabAction_apply, ContinuousMap.smul_apply, RingHom.id_apply] }
  have hL (A : SlabPath T (E →L[ℝ] E)) : ‖L A‖ ≤ 1 * ‖A‖ := by
    change ‖slabAction A‖ ≤ 1 * ‖A‖
    rw [one_mul]
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) fun x => ?_
    exact ((slabAction A x).norm_le (mul_nonneg (norm_nonneg A) (norm_nonneg x))).2 fun t => by
      rw [slabAction_apply]
      exact ((A t).le_opNorm _).trans (mul_le_mul (A.norm_coe_le_norm t) (x.norm_coe_le_norm t)
        (norm_nonneg _) (norm_nonneg _))
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := SlabPath T (E →L[ℝ] E))
    (F := SlabPath T E →L[ℝ] SlabPath T E) (σ := RingHom.id ℝ) L 1 hL

private noncomputable def slabVolterra {T : ℝ} (hT : 0 ≤ T) :
    SlabPath T (E →L[ℝ] E) →L[ℝ] (SlabPath T E →L[ℝ] SlabPath T E) :=
  (ContinuousLinearMap.compL ℝ (SlabPath T E) (SlabPath T E) (SlabPath T E)
    (slabPrimitive hT)).comp slabActionLinear

omit [CompleteSpace E] in
private theorem slabVolterra_apply {T : ℝ} (hT : 0 ≤ T)
    (A : SlabPath T (E →L[ℝ] E)) (x : SlabPath T E) (t : Slab T) :
    slabVolterra hT A x t =
      ∫ u in 0..(t : ℝ), extendSlabPath hT A u (extendSlabPath hT x u) :=
  rfl

private noncomputable def slabVolterraEquation {T : ℝ} (hT : 0 ≤ T)
    (A : SlabPath T (E →L[ℝ] E)) : SlabPath T E →L[ℝ] SlabPath T E :=
  ContinuousLinearMap.id ℝ _ - slabVolterra hT A

omit [CompleteSpace E] in
private theorem continuousOn_slabVolterra_inhom {T : ℝ} (hT : 0 ≤ T)
    (A : SlabPath T (E →L[ℝ] E)) (x : SlabPath T E) :
    Continuous (fun u => extendSlabPath hT A u (extendSlabPath hT x u)) :=
  (continuous_extendSlabPath hT A).clm_apply (continuous_extendSlabPath hT x)

private theorem hasDerivWithinAt_from_slabVolterra {T : ℝ} (hT : 0 ≤ T)
    {A : SlabPath T (E →L[ℝ] E)} {x g : SlabPath T E}
    (heq : slabVolterraEquation hT A x = g) (t : ℝ) (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun u => extendSlabPath hT x u - extendSlabPath hT g u)
      (extendSlabPath hT A t (extendSlabPath hT x t)) (Icc 0 T) t := by
  let f (u : ℝ) := extendSlabPath hT A u (extendSlabPath hT x u)
  have hc : Continuous f := continuousOn_slabVolterra_inhom hT A x
  let _ : Fact (t ∈ Icc (0 : ℝ) T) := ⟨ht⟩
  refine (intervalIntegral.integral_hasDerivWithinAt_right (hc.intervalIntegrable 0 t)
    (hc.aestronglyMeasurable.stronglyMeasurableAtFilter) hc.continuousWithinAt).congr_of_mem ?_ ht
  intro u hu
  let v : Slab T := ⟨u, hu⟩
  have hv := congrArg (fun w : SlabPath T E => w v) heq
  change x v - slabVolterra hT A x v = g v at hv
  rw [slabVolterra_apply] at hv
  rw [extendSlabPath, extendSlabPath, projIcc_of_mem hT hu]
  change x v - g v = ∫ r in 0..u, f r
  rw [← hv]
  abel

private theorem slabVolterraEquation_bijective {T : ℝ} (hT : 0 ≤ T)
    (A : SlabPath T (E →L[ℝ] E)) :
    Function.Bijective (slabVolterraEquation hT A) := by
  constructor
  · intro x y heq
    let z := x - y
    have hz : slabVolterraEquation hT A z = 0 := by
      change slabVolterraEquation hT A (x - y) = 0
      rw [map_sub, heq, sub_self]
    have hz' (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivWithinAt (extendSlabPath hT z)
        (extendSlabPath hT A t (extendSlabPath hT z t)) (Icc 0 T) t := by
      change HasDerivWithinAt (fun u => z (projIcc 0 T hT u))
        (extendSlabPath hT A t (extendSlabPath hT z t)) (Icc 0 T) t
      simpa only [extendSlabPath, ContinuousMap.zero_apply, sub_zero] using
        hasDerivWithinAt_from_slabVolterra hT hz t ht
    have h₀ : extendSlabPath hT z 0 = 0 := by
      have hz0 := congrArg (fun w : SlabPath T E => w (projIcc 0 T hT 0)) hz
      change extendSlabPath hT z 0 - slabVolterra hT A z (projIcc 0 T hT 0) = 0 at hz0
      rw [projIcc_of_mem hT (show (0 : ℝ) ∈ Icc 0 T from ⟨le_rfl, hT⟩),
        slabVolterra_apply, intervalIntegral.integral_same, sub_zero] at hz0
      exact hz0
    have he := linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc ⟨le_rfl, hT⟩
      (continuous_extendSlabPath hT A).continuousOn hz'
      (fun t _ => by simpa only [map_zero] using hasDerivWithinAt_const t (Icc 0 T) (0 : E)) h₀
    ext t
    have hh := he t.property
    rw [extendSlabPath, projIcc_of_mem hT t.property] at hh
    exact sub_eq_zero.mp hh
  · intro g
    let B := extendSlabPath hT A
    let f (t : ℝ) := B t (extendSlabPath hT g t)
    obtain ⟨w, hinit, hw⟩ := linearODE_inhom_exists_Icc ⟨le_rfl, hT⟩
      (continuous_extendSlabPath hT A).continuousOn
      (continuousOn_slabVolterra_inhom hT A g).continuousOn (0 : E)
    let x : SlabPath T E :=
      ⟨fun t => w t + g t,
        ((HasDerivWithinAt.continuousOn hw).domRestrict).add g.continuous⟩
    refine ⟨x, ?_⟩
    ext t
    change w t + g t - slabVolterra hT A x t = g t
    rw [slabVolterra_apply]
    have hEq (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivWithinAt w
        (B u (extendSlabPath hT x u)) (Icc 0 T) u := by
      have h := hw u hu
      have hval : extendSlabPath hT x u = w u + extendSlabPath hT g u := by
        simp only [extendSlabPath, projIcc_of_mem hT hu, x]
        rfl
      rw [hval, map_add]
      exact h
    have hint :
        ∫ u in 0..(t : ℝ), B u (extendSlabPath hT x u) = w t - w 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le t.property.1
        ((HasDerivWithinAt.continuousOn hw).mono (Icc_subset_Icc_right t.property.2))
        (fun u hu => (hEq u ⟨hu.1.le, hu.2.le.trans t.property.2⟩).hasDerivAt
          (Icc_mem_nhds hu.1 (hu.2.trans_le t.property.2)))
        ((continuousOn_slabVolterra_inhom hT A x).intervalIntegrable _ _)
    change w t + g t - (∫ u in 0..(t : ℝ), B u (extendSlabPath hT x u)) = g t
    rw [hint, hinit, sub_zero]
    abel

private noncomputable def slabConst (T : ℝ) : E →L[ℝ] SlabPath T E := by
  let L : E →ₗ[ℝ] SlabPath T E :=
    { toFun := ContinuousMap.const _
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact L.mkContinuous 1 fun x => ((L x).norm_le (by positivity)).2 fun _ => by
    change ‖x‖ ≤ 1 * ‖x‖
    rw [one_mul]

/-- The forced solve is smooth as a map into the Banach space of continuous
paths, provided the coefficients and forcing are smooth maps into the
corresponding uniform path norms. The ODE holds within the closed slab. -/
theorem exists_contDiff_parameterized_linearODE
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {T : ℝ} {n : ℕ∞ω} (hT : 0 ≤ T)
    {A : P → C(Icc (0 : ℝ) T, E →L[ℝ] E)} {f : P → C(Icc (0 : ℝ) T, E)} {x₀ : P → E}
    (hA : ContDiff ℝ n A) (hf : ContDiff ℝ n f) (hx₀ : ContDiff ℝ n x₀) :
    ∃ x : P → C(Icc (0 : ℝ) T, E), ContDiff ℝ n x ∧
      (∀ p, x p ⟨0, le_rfl, hT⟩ = x₀ p) ∧
      ∀ p t (ht : t ∈ Icc 0 T),
        HasDerivWithinAt (fun u => x p (projIcc 0 T hT u))
          (A p ⟨t, ht⟩ (x p ⟨t, ht⟩) + f p ⟨t, ht⟩) (Icc 0 T) t := by
  let L (p : P) := slabVolterraEquation hT (A p)
  let g (p : P) := slabConst T (x₀ p) + slabPrimitive hT (f p)
  let x (p : P) := Ring.inverse (L p) (g p)
  have hL (p : P) : IsUnit (L p) :=
    ContinuousLinearMap.isUnit_iff_bijective.mpr (slabVolterraEquation_bijective hT (A p))
  have heq (p : P) : L p (x p) = g p :=
    congrArg (fun K : SlabPath T E →L[ℝ] SlabPath T E => K (g p))
      (Ring.mul_inverse_cancel (L p) (hL p))
  let V : C(Icc (0 : ℝ) T, E →L[ℝ] E) →L[ℝ]
      (C(Icc (0 : ℝ) T, E) →L[ℝ] C(Icc (0 : ℝ) T, E)) := slabVolterra hT
  have hVc : ContDiff ℝ n V :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (E := SlabPath T (E →L[ℝ] E))
      (F := SlabPath T E →L[ℝ] SlabPath T E) (n := n) V
  have hVdiff : ContDiff ℝ n (fun p => slabVolterra (E := E) hT (A p)) :=
    hVc.comp hA
  have hLdiff : ContDiff ℝ n L := contDiff_const.sub hVdiff
  have hLinvDiff : ContDiff ℝ n (fun p => Ring.inverse (L p)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro p
    have hinv : ContDiffAt ℝ n Ring.inverse (L p) := by
      obtain ⟨u, hu⟩ := hL p
      rw [← hu]
      exact contDiffAt_ringInverse (R := SlabPath T E →L[ℝ] SlabPath T E) (n := n) ℝ u
    exact hinv.comp p hLdiff.contDiffAt
  have hgdiff : ContDiff ℝ n g :=
    ((slabConst (E := E) T).contDiff.comp hx₀).add ((slabPrimitive (E := E) hT).contDiff.comp hf)
  refine ⟨x, hLinvDiff.clm_apply hgdiff, ?_, ?_⟩
  · intro p
    let t₀ : Slab T := ⟨0, le_rfl, hT⟩
    have h := congrArg (fun y : SlabPath T E => y t₀) (heq p)
    change x p t₀ - slabVolterra hT (A p) (x p) t₀ = x₀ p + slabPrimitive hT (f p) t₀ at h
    rw [slabVolterra_apply, slabPrimitive_apply] at h
    simpa only [t₀, intervalIntegral.integral_same, sub_zero, add_zero] using h
  · intro p t ht
    have hg (u : ℝ) (hu : u ∈ Icc 0 T) :
        extendSlabPath hT (g p) u = x₀ p + ∫ d in 0..u, extendSlabPath hT (f p) d := by
      rw [extendSlabPath, projIcc_of_mem hT hu]
      change x₀ p + slabPrimitive hT (f p) ⟨u, hu⟩ = _
      rw [slabPrimitive_apply]
    have hdg : HasDerivWithinAt (extendSlabPath hT (g p))
        (extendSlabPath hT (f p) t) (Icc 0 T) t := by
      have hprim := ((continuous_extendSlabPath hT (f p)).integral_hasStrictDerivAt 0 t).hasDerivAt
      exact (hprim.hasDerivWithinAt.const_add (x₀ p)).congr_of_mem hg ht
    have hd := hasDerivWithinAt_from_slabVolterra hT (heq p) t ht
    have hder : HasDerivWithinAt (extendSlabPath hT (x p))
        (extendSlabPath hT (A p) t (extendSlabPath hT (x p) t) + extendSlabPath hT (f p) t)
        (Icc 0 T) t :=
      (hd.add hdg).congr_of_mem (fun u _ =>
        (sub_add_cancel (extendSlabPath hT (x p) u) (extendSlabPath hT (g p) u)).symm) ht
    change HasDerivWithinAt (fun u => x p (projIcc 0 T hT u))
      (A p (projIcc 0 T hT t) (x p (projIcc 0 T hT t)) + f p (projIcc 0 T hT t))
      (Icc 0 T) t at hder
    rw [projIcc_of_mem hT ht] at hder
    exact hder

omit [CompleteSpace E] in
/-- Evaluation preserves fixed-time smoothness of a path-valued solution. -/
theorem contDiff_slabPath_eval {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {T : ℝ} {n : ℕ∞ω} {x : P → C(Icc (0 : ℝ) T, E)}
    (hx : ContDiff ℝ n x) (t : Icc (0 : ℝ) T) :
    ContDiff ℝ n (fun p => x p t) := by
  let ev : C(Icc (0 : ℝ) T, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  have hEv : ContDiff ℝ n ev := ev.contDiff
  exact hEv.comp hx

omit [CompleteSpace E] in
/-- Each evaluated parameter jet is continuous jointly in closed-slab time,
parameter, and its direction arguments. -/
theorem continuous_iteratedFDeriv_slabPath_eval
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {T : ℝ} {n : ℕ∞ω} {m : ℕ} {x : P → C(Icc (0 : ℝ) T, E)}
    (hx : ContDiff ℝ n x) (hm : (m : ℕ∞ω) ≤ n) :
    Continuous (fun z : (Icc (0 : ℝ) T × P) × (Fin m → P) =>
      iteratedFDeriv ℝ m (fun p => x p z.1.1) z.1.2 z.2) := by
  have hEq (t : Icc (0 : ℝ) T) (p : P) (d : Fin m → P) :
      iteratedFDeriv ℝ m (fun q => x q t) p d = (iteratedFDeriv ℝ m x p d) t := by
    let ev : C(Icc (0 : ℝ) T, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
    have h := ev.iteratedFDeriv_comp_left (x := p) hx.contDiffAt hm
    change iteratedFDeriv ℝ m (⇑ev ∘ x) p d = ev (iteratedFDeriv ℝ m x p d)
    rw [h]
    rfl
  simp only [hEq]
  have hJ : Continuous (fun z : (Icc (0 : ℝ) T × P) × (Fin m → P) =>
      iteratedFDeriv ℝ m x z.1.2) :=
    (ContDiff.continuous_iteratedFDeriv hm hx).comp (continuous_fst.snd)
  have hApply : Continuous (fun z : (Icc (0 : ℝ) T × P) × (Fin m → P) =>
      iteratedFDeriv ℝ m x z.1.2 z.2) :=
    continuous_eval.comp (hJ.prodMk continuous_snd)
  exact continuous_eval.comp (hApply.prodMk (continuous_fst.fst))

omit [CompleteSpace E] in
/-- On a compact set of parameters, the fixed-time Fréchet derivatives are
bounded in operator norm uniformly over the entire closed slab. -/
theorem iteratedFDeriv_slabPath_uniform_on_compact
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {T : ℝ} {n : ℕ∞ω} {m : ℕ} {x : P → C(Icc (0 : ℝ) T, E)} {S : Set P}
    (hx : ContDiff ℝ n x) (hm : (m : ℕ∞ω) ≤ n) (hS : IsCompact S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ S, ∀ t : Icc (0 : ℝ) T,
      ‖iteratedFDeriv ℝ m (fun q => x q t) p‖ ≤ C := by
  obtain ⟨C, hC⟩ := hS.exists_bound_of_continuousOn (ContDiff.continuous_iteratedFDeriv hm hx).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun p hp t => ?_⟩
  let ev : C(Icc (0 : ℝ) T, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ t
  have hev : ‖ev‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro y
    change ‖y t‖ ≤ 1 * ‖y‖
    simpa only [one_mul] using y.norm_coe_le_norm t
  have h := ev.norm_iteratedFDeriv_comp_left (x := p) hx.contDiffAt hm
  exact h.trans (((mul_le_mul_of_nonneg_right hev (norm_nonneg _)).trans
    (by simpa only [one_mul] using hC p hp)).trans (le_max_left _ _))

end TorusEuler

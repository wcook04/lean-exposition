import TorusEuler.EndpointTimeRegularity
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Joint smoothness on preterminal slabs in Proposition 8.1. -/

open Asymptotics BoundedContinuousFunction ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff Topology

namespace TorusEuler

noncomputable section

variable (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The order-(m) spatial jet with the uniform norm on the Euclidean lift. -/
abbrev BoundedSpatialJet (m : ℕ) :=
  E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F

/-- All spatial jets through a fixed finite order. -/
abbrev SpatialJetTuple (m : ℕ) := ∀ i : Fin (m + 1), BoundedSpatialJet E F i

variable {E F}

local instance (m : ℕ) : NormedAddCommGroup (BoundedSpatialJet E F m) :=
  inferInstanceAs (NormedAddCommGroup (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F))
local instance (m : ℕ) : NormedSpace ℝ (BoundedSpatialJet E F m) :=
  inferInstanceAs (NormedSpace ℝ (E →ᵇ ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F))
local instance (m : ℕ) : NormedAddCommGroup (SpatialJetTuple E F m) :=
  inferInstanceAs (NormedAddCommGroup (∀ i : Fin (m + 1), BoundedSpatialJet E F i))
local instance (m : ℕ) : NormedSpace ℝ (SpatialJetTuple E F m) :=
  inferInstanceAs (NormedSpace ℝ (∀ i : Fin (m + 1), BoundedSpatialJet E F i))

/-- The time bootstrap from the integrated momentum equation at each spatial
order. The two entries of the bounded bilinear map are the velocity jet
tuples. The map includes the one spatial derivative and the projection. -/
theorem contDiffOn_spatialJets_time_of_integrated [CompleteSpace F] {S : ℝ} (hS : 0 < S)
    (J : ∀ m, ℝ → BoundedSpatialJet E F m)
    (r : ℕ → ℕ)
    (B : ∀ m, SpatialJetTuple E F (r m) →L[ℝ] SpatialJetTuple E F (r m) →L[ℝ] BoundedSpatialJet E F m)
    (hcont : ∀ m, ContinuousOn (J m) (Icc 0 S))
    (hEq : ∀ m t, t ∈ Icc 0 S →
      J m t = J m 0 + endpointPrimitive (fun s => B m (fun i => J i s) (fun i => J i s)) t) :
    ∀ m, ContDiffOn ℝ ∞ (J m) (Icc 0 S) := by
  have h (n : ℕ) : ∀ m, ContDiffOn ℝ n (J m) (Icc 0 S) := by
    induction n with
    | zero => exact fun m => contDiffOn_zero.mpr (hcont m)
    | succ n hn =>
      intro m
      have hj : ContDiffOn ℝ n (fun s => (fun i => J i s : SpatialJetTuple E F (r m))) (Icc 0 S) :=
        contDiffOn_pi.mpr fun i => hn i
      have hb := ((B m).contDiff.comp_contDiffOn hj).clm_apply hj
      rw [Nat.cast_succ]
      exact (contDiffOn_const.add (contDiffOn_endpointPrimitive_succ hS hb)).congr (hEq m)
  exact fun m => contDiffOn_infty.mpr fun n => h n m

private theorem spatialJet_derivative_time_commutes {S : ℝ} (hS : 0 < S)
    (J : ∀ m, ℝ → BoundedSpatialJet E F m)
    (hJ : ∀ m, ContDiffOn ℝ ∞ (J m) (Icc 0 S))
    (hx : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x,
      HasFDerivAt (fun y => J m t y) ((J (m + 1) t x).curryLeft) x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) S) (m : ℕ) (x : E) :
    HasFDerivAt (fun y => derivWithin (J m) (Icc 0 S) t y)
      ((derivWithin (J (m + 1)) (Icc 0 S) t x).curryLeft) x := by
  classical
  let I := Icc (0 : ℝ) S
  let l := 𝓝[I \ ({t} : Set ℝ)] t
  let q (k : ℕ) (s : ℝ) := if s ∈ I then slope (J k) t s else 0
  let d (k : ℕ) := derivWithin (J k) I t
  let : NeBot l := accPt_principal_iff_nhdsWithin.mp ((uniqueDiffOn_Icc hS t ht).accPt)
  have htend (k : ℕ) : Tendsto (q k) l (𝓝 (d k)) := by
    have hk := ((hJ k).differentiableOn (by simp) t ht).hasDerivWithinAt
    have hslope := hasDerivWithinAt_iff_tendsto_slope.mp hk
    have hself : ∀ᶠ s in l, s ∈ I \ ({t} : Set ℝ) := self_mem_nhdsWithin
    have hmem : ∀ᶠ s in l, s ∈ I := hself.mono fun _ hs => hs.1
    refine hslope.congr' ?_
    exact hmem.mono fun s hs => by simp only [q, hs, ite_true]
  have hu (k : ℕ) : TendstoUniformly (fun s y => q k s y) (fun y => d k y) l :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp (htend k)
  let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
  have hD := curry.isometry.uniformContinuous.comp_tendstoUniformly (hu (m + 1))
  refine hasFDerivAt_of_tendstoUniformly hD (fun s y => ?_) (fun y => (hu m).tendsto_at y) x
  by_cases hs : s ∈ I
  · have hsp := ((hx s hs m y).sub (hx t ht m y)).const_smul ((s - t)⁻¹ : ℝ)
    simp only [q, hs, ite_true, slope, vsub_eq_sub, BoundedContinuousFunction.coe_smul,
      BoundedContinuousFunction.coe_sub, Pi.sub_apply, Function.comp_apply, map_smul]
    exact hsp
  · simp only [q, hs, ite_false, Function.comp_apply]
    change HasFDerivAt (fun _ => 0) (curry 0) y
    rw [show curry 0 = 0 from curry.toLinearEquiv.map_zero]
    exact hasFDerivAt_const _ _

private theorem hasFDerivWithinAt_eval_of_time_and_space
    {I : Set ℝ} {J : ℝ → E →ᵇ F} {t : ℝ} {x : E}
    {d : E →ᵇ F} {D : E →L[ℝ] F}
    (ht : HasDerivWithinAt J d I t)
    (hx : HasFDerivAt (fun y => J t y) D x) :
    HasFDerivWithinAt (fun p : ℝ × E => J p.1 p.2)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (d x)).coprod D) (I ×ˢ univ) (t, x) := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  let l := 𝓝[I ×ˢ (univ : Set E)] (t, x)
  have h₁ : Tendsto Prod.fst l (𝓝[I] t) := by
    change Tendsto Prod.fst (𝓝[I ×ˢ (univ : Set E)] (t, x)) (𝓝[I] t)
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact tendsto_fst
  have h₂ : Tendsto Prod.snd l (𝓝 x) := by
    change Tendsto Prod.snd (𝓝[I ×ˢ (univ : Set E)] (t, x)) (𝓝 x)
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact tendsto_snd
  have hδ : 0 < ε / 3 := by positivity
  have hct : Tendsto (fun y => ‖d y - d x‖) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((d.continuous.continuousAt (x := x)).tendsto.sub
      (tendsto_const_nhds (x := d x))).norm
  filter_upwards [h₁.eventually (isLittleO_iff.mp ht.isLittleO hδ),
    h₂.eventually (isLittleO_iff.mp hx.isLittleO hδ),
    h₂.eventually (hct.eventually (gt_mem_nhds hδ))] with p hp₁ hp₂ hp₃
  let r := J p.1 - J t - (p.1 - t) • d
  have hrem : ‖r p.2‖ ≤ ε / 3 * ‖p.1 - t‖ :=
    (r.norm_coe_le_norm p.2).trans hp₁
  have hcross : ‖(p.1 - t) • (d p.2 - d x)‖ ≤ ε / 3 * ‖p.1 - t‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hp₃.le (norm_nonneg _)
  have hfst : ‖p.1 - t‖ ≤ ‖p - (t, x)‖ := norm_fst_le (p - (t, x))
  have hsnd : ‖p.2 - x‖ ≤ ‖p - (t, x)‖ := norm_snd_le (p - (t, x))
  calc
    _ = ‖r p.2 + (p.1 - t) • (d p.2 - d x) +
        (J t p.2 - J t x - D (p.2 - x))‖ := by
      rw [coprod_apply]
      simp only [r, BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul, Pi.sub_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, Prod.fst_sub, Prod.snd_sub, smul_sub]
      abel_nf
    _ ≤ ‖r p.2‖ + ‖(p.1 - t) • (d p.2 - d x)‖ + ‖J t p.2 - J t x - D (p.2 - x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε / 3 * ‖p.1 - t‖ + ε / 3 * ‖p.1 - t‖ + ε / 3 * ‖p.2 - x‖ :=
      add_le_add (add_le_add hrem hcross) hp₂
    _ ≤ ε / 3 * ‖p - (t, x)‖ + ε / 3 * ‖p - (t, x)‖ + ε / 3 * ‖p - (t, x)‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfst hδ.le)
        (mul_le_mul_of_nonneg_left hfst hδ.le)) (mul_le_mul_of_nonneg_left hsnd hδ.le)
    _ = _ := by ring

/-- A tower of bounded spatial jets that is smooth in the uniform time norm
evaluates to a jointly smooth field on a closed slab. -/
theorem contDiffOn_joint_of_spatialJets_time {S : ℝ} (hS : 0 < S)
    (J : ∀ m, ℝ → BoundedSpatialJet E F m)
    (hJ : ∀ m, ContDiffOn ℝ ∞ (J m) (Icc 0 S))
    (hspace : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x,
      HasFDerivAt (fun y => J m t y) ((J (m + 1) t x).curryLeft) x) :
    ∀ m, ContDiffOn ℝ ∞ (fun p : ℝ × E => J m p.1 p.2) (Icc 0 S ×ˢ univ) := by
  let I := Icc (0 : ℝ) S
  have h (n : ℕ) : ∀ (J : ∀ m, ℝ → BoundedSpatialJet E F m),
      (∀ m, ContDiffOn ℝ ∞ (J m) I) →
      (∀ t ∈ I, ∀ m x, HasFDerivAt (fun y => J m t y) ((J (m + 1) t x).curryLeft) x) →
      ∀ m, ContDiffOn ℝ n (fun p : ℝ × E => J m p.1 p.2) (I ×ˢ univ) := by
    induction n with
    | zero =>
      intro J hT _ m
      apply contDiffOn_zero.mpr
      have hPair := (((hT m).continuousOn.comp continuous_fst.continuousOn mapsTo_fst_prod)).prodMk
        (continuous_snd.continuousOn (s := I ×ˢ (univ : Set E)))
      exact continuous_eval.comp_continuousOn hPair
    | succ n ih =>
      intro J hT hx m
      let dJ (k : ℕ) := derivWithin (J k) I
      have hdT (k : ℕ) : ContDiffOn ℝ ∞ (dJ k) I :=
        (hT k).derivWithin (uniqueDiffOn_Icc hS) (by simp)
      have hdx (t : ℝ) (ht : t ∈ I) (k : ℕ) (x : E) :
          HasFDerivAt (fun y => dJ k t y) ((dJ (k + 1) t x).curryLeft) x :=
        spatialJet_derivative_time_commutes hS J hT hx t ht k x
      let G := ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F
      let A : G →L[ℝ] (ℝ × E) →L[ℝ] G :=
        (ContinuousLinearMap.smulRightL ℝ (ℝ × E) G) (fst ℝ ℝ E)
      let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
      let B : (E →L[ℝ] G) →L[ℝ] (ℝ × E) →L[ℝ] G :=
        (compL ℝ (ℝ × E) E G).flip (snd ℝ ℝ E)
      let D (p : ℝ × E) := A (dJ m p.1 p.2) + B (C (J (m + 1) p.1 p.2))
      have hAc : ContDiff ℝ n A :=
        ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n) (E := G) (F := (ℝ × E) →L[ℝ] G) A
      let BC := B.comp C.toContinuousLinearEquiv.toContinuousLinearMap
      have hBc : ContDiff ℝ n BC := ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := n)
        (E := ContinuousMultilinearMap ℝ (fun _ : Fin (m + 1) => E) F)
        (F := (ℝ × E) →L[ℝ] G) BC
      have hA := hAc.comp_contDiffOn (ih dJ hdT hdx m)
      have hB := hBc.comp_contDiffOn (ih J hT hx (m + 1))
      have hD : ContDiffOn ℝ n D (I ×ˢ univ) := hA.add hB
      have hderiv (p : ℝ × E) (hp : p ∈ I ×ˢ univ) :
          HasFDerivWithinAt (fun z : ℝ × E => J m z.1 z.2) (D p) (I ×ˢ univ) p := by
        refine (hasFDerivWithinAt_eval_of_time_and_space
          (((hT m).differentiableOn (by simp) p.1 hp.1).hasDerivWithinAt) (hx p.1 hp.1 m p.2)).congr_fderiv ?_
        apply ContinuousLinearMap.ext
        intro z
        rfl
      have hI := (uniqueDiffOn_Icc hS).prod (uniqueDiffOn_univ (𝕜 := ℝ) (E := E))
      rw [Nat.cast_succ]
      apply (contDiffOn_succ_iff_fderivWithin hI).mpr
      exact ⟨fun p hp => (hderiv p hp).differentiableWithinAt, by simp,
        hD.congr fun p hp => (hderiv p hp).fderivWithin (hI p hp)⟩
  exact fun m => contDiffOn_infty.mpr fun n => h n J hJ hspace m

private theorem boundedSpatialJets_derivative_of_actual {S : ℝ} {u : ℝ → E → F}
    (J : ∀ m, ℝ → BoundedSpatialJet E F m)
    (hu : ∀ t ∈ Icc (0 : ℝ) S, ContDiff ℝ ∞ (u t))
    (hactual : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x, J m t x = iteratedFDeriv ℝ m (u t) x)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) S) (m : ℕ) (x : E) :
    HasFDerivAt (fun y => J m t y) ((J (m + 1) t x).curryLeft) x := by
  rw [show (fun y => J m t y) = iteratedFDeriv ℝ m (u t) from funext (hactual t ht m),
    hactual t ht (m + 1) x]
  have H := (hu t ht).contDiffOn.ftaylorSeriesWithin (s := univ) uniqueDiffOn_univ
  have hm : (m : ℕ∞ω) < ∞ := by exact_mod_cast (ENat.natCast_lt_top m)
  have hD := (H.fderivWithin m hm x (mem_univ x)).hasFDerivAt (univ_mem : univ ∈ 𝓝 x)
  simpa only [ftaylorSeriesWithin, iteratedFDerivWithin_univ] using hD

/-- Joint regularity from the actual spatial Fréchet jets and their integrated
momentum equations. The finite input order of each bounded momentum map can
include an extra spatial loss. Time derivatives at zero are within the slab. -/
theorem contDiffOn_eulerVelocity_of_integrated_jets [CompleteSpace F] {S : ℝ} (hS : 0 < S)
    {u : ℝ → E → F}
    (J : ∀ m, ℝ → BoundedSpatialJet E F m)
    (r : ℕ → ℕ)
    (B : ∀ m, SpatialJetTuple E F (r m) →L[ℝ] SpatialJetTuple E F (r m) →L[ℝ] BoundedSpatialJet E F m)
    (hu : ∀ t ∈ Icc (0 : ℝ) S, ContDiff ℝ ∞ (u t))
    (hactual : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x, J m t x = iteratedFDeriv ℝ m (u t) x)
    (hcont : ∀ m, ContinuousOn (J m) (Icc 0 S))
    (hEq : ∀ m t, t ∈ Icc 0 S →
      J m t = J m 0 + endpointPrimitive (fun s => B m (fun i => J i s) (fun i => J i s)) t) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ univ) := by
  have hT := contDiffOn_spatialJets_time_of_integrated hS J r B hcont hEq
  let C := continuousMultilinearCurryFin0 ℝ E F
  have hJ0 := contDiffOn_joint_of_spatialJets_time hS J hT
    (boundedSpatialJets_derivative_of_actual J hu hactual) 0
  let C₀ := C.toContinuousLinearEquiv.toContinuousLinearMap
  have hC : ContDiff ℝ ∞ C₀ := ContinuousLinearMap.contDiff (𝕜 := ℝ)
    (E := ContinuousMultilinearMap ℝ (fun _ : Fin 0 => E) F) (F := F) C₀
  refine (hC.comp_contDiffOn hJ0).congr ?_
  rintro ⟨t, x⟩ hp
  change u t x = C (J 0 t x)
  rw [hactual t hp.1 0 x, iteratedFDeriv_zero_eq_comp, Function.comp_apply, C.apply_symm_apply]

private theorem hasFDerivAt_eval_timePrimitive [CompleteSpace F] {S t : ℝ}
    {U : ℝ → E →ᵇ F} {D : ℝ → E →ᵇ (E →L[ℝ] F)}
    (ht : t ∈ Icc (0 : ℝ) S)
    (hU : ContinuousOn U (Icc 0 S)) (hD : ContinuousOn D (Icc 0 S))
    (hx : ∀ s ∈ Icc (0 : ℝ) S, ∀ x, HasFDerivAt (fun y => U s y) (D s x) x) (x : E) :
    HasFDerivAt (fun y => endpointPrimitive U t y) (endpointPrimitive D t x) x := by
  let : NormedAddCommGroup (E →L[ℝ] F) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  let : NormedAddCommGroup (E →ᵇ (E →L[ℝ] F)) := BoundedContinuousFunction.instNormedAddCommGroup
  have hSub : Icc (0 : ℝ) t ⊆ Icc 0 S := Icc_subset_Icc_right ht.2
  have huInt := (hU.mono hSub).intervalIntegrable_of_Icc (μ := volume) ht.1
  have hdInt : IntervalIntegrable D volume 0 t :=
    (hD.mono hSub).intervalIntegrable_of_Icc ht.1
  have hu (y : E) : IntervalIntegrable (fun s => U s y) volume 0 t :=
    (((evalCLM ℝ y).continuous.comp_continuousOn hU).mono hSub).intervalIntegrable_of_Icc ht.1
  have hd : IntervalIntegrable (fun s => D s x) volume 0 t :=
    (((evalCLM ℝ x).continuous.comp_continuousOn hD).mono hSub).intervalIntegrable_of_Icc ht.1
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hD
  have htime : ∀ᵐ s ∂(volume.restrict (uIoc (0 : ℝ) t)), s ∈ Icc 0 S := by
    rw [uIoc_of_le ht.1]
    exact (ae_restrict_mem measurableSet_Ioc).mono fun _ hs => hSub (Ioc_subset_Icc_self hs)
  have hdiffer :=
    hasFDerivAt_integral_of_dominated_of_fderiv_le'' (μ := volume)
      (F := fun y s => U s y) (F' := fun y s => D s y) (bound := fun _ => M)
      (s := univ) (x₀ := x) univ_mem
      (Eventually.of_forall fun y => (hu y).def'.aestronglyMeasurable)
      (hu x) hd.def'.aestronglyMeasurable
      (htime.mono fun s hs y _ => ((D s).norm_coe_le_norm y).trans (hM s hs))
      (intervalIntegrable_const) (htime.mono fun s hs y _ => hx s hs y)
  have hEq (y : E) : (∫ s in (0 : ℝ)..t, U s y) = endpointPrimitive U t y :=
    (evalCLM ℝ y).intervalIntegral_comp_comm huInt
  have hEqD : (∫ s in (0 : ℝ)..t, D s x) = endpointPrimitive D t x :=
    (evalCLM ℝ x).intervalIntegral_comp_comm hdInt
  rw [show (fun y => ∫ s in (0 : ℝ)..t, U s y) = (fun y => endpointPrimitive U t y) from funext hEq,
    hEqD] at hdiffer
  exact hdiffer

private theorem spatialJets_timePrimitive_hasFDerivAt [CompleteSpace F] {S t : ℝ}
    (U : ∀ m, ℝ → BoundedSpatialJet E F m) (hcont : ∀ m, ContinuousOn (U m) (Icc 0 S))
    (hx : ∀ s ∈ Icc (0 : ℝ) S, ∀ m x,
      HasFDerivAt (fun y => U m s y) ((U (m + 1) s x).curryLeft) x)
    (ht : t ∈ Icc (0 : ℝ) S) (m : ℕ) (x : E) :
    HasFDerivAt (fun y => endpointPrimitive (U m) t y)
      ((endpointPrimitive (U (m + 1)) t x).curryLeft) x := by
  let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
  let G := ContinuousMultilinearMap ℝ (fun _ : Fin m => E) F
  let : NormedAddCommGroup (E →L[ℝ] G) :=
    ContinuousLinearMap.toNormedAddCommGroup (σ₁₂ := RingHom.id ℝ)
  let : NormedAddCommGroup (E →ᵇ (E →L[ℝ] G)) := BoundedContinuousFunction.instNormedAddCommGroup
  let CL : BoundedSpatialJet E F (m + 1) →L[ℝ] (E →ᵇ (E →L[ℝ] G)) :=
    ContinuousLinearMap.compLeftContinuousBounded E C.toContinuousLinearEquiv.toContinuousLinearMap
  have hD : ContinuousOn (fun s => CL (U (m + 1) s)) (Icc 0 S) :=
    CL.continuous.comp_continuousOn (hcont (m + 1))
  have hd := hasFDerivAt_eval_timePrimitive ht (hcont m) hD
    (show ∀ s ∈ Icc (0 : ℝ) S, ∀ y, HasFDerivAt (fun z => U m s z) (CL (U (m + 1) s) y) y
      from fun s hs y => hx s hs m y) x
  have hu := ((hcont (m + 1)).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc
    (μ := volume) ht.1
  have heq : endpointPrimitive (fun s => CL (U (m + 1) s)) t =
      CL (endpointPrimitive (U (m + 1)) t) :=
    CL.intervalIntegral_comp_comm hu
  rw [heq] at hd
  exact hd

/-- The integrated equation at order zero yields its spatially differentiated
equations because taking the time primitive preserves the jet relation. -/
theorem integrated_spatialJets_of_zeroth [CompleteSpace F] {S : ℝ} (hS : 0 ≤ S)
    (J U : ∀ m, ℝ → BoundedSpatialJet E F m)
    (hJ : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x,
      HasFDerivAt (fun y => J m t y) ((J (m + 1) t x).curryLeft) x)
    (hU : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x,
      HasFDerivAt (fun y => U m t y) ((U (m + 1) t x).curryLeft) x)
    (hcont : ∀ m, ContinuousOn (U m) (Icc 0 S))
    (hEq : ∀ t ∈ Icc (0 : ℝ) S, J 0 t = J 0 0 + endpointPrimitive (U 0) t) :
    ∀ m t, t ∈ Icc (0 : ℝ) S → J m t = J m 0 + endpointPrimitive (U m) t := by
  intro m
  induction m with
  | zero => exact hEq
  | succ m hm =>
    intro t ht
    have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS⟩
    apply BoundedContinuousFunction.ext
    intro x
    have h := hJ t ht m x
    have hEqF : (fun y => J m t y) = fun y => J m 0 y + endpointPrimitive (U m) t y := by
      funext y
      rw [hm t ht]
      rfl
    rw [hEqF] at h
    have hg := (hJ 0 h0 m x).add (spatialJets_timePrimitive_hasFDerivAt U hcont hU ht m x)
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) F
    apply C.injective
    change (J (m + 1) t x).curryLeft =
        C (J (m + 1) 0 x + endpointPrimitive (U (m + 1)) t x)
    rw [map_add]
    exact h.fderiv.symm.trans hg.fderiv

/-- A single integrated projected momentum equation suffices for joint
smoothness. The transform hypothesis identifies each bounded bilinear
momentum map with the corresponding spatial derivative of the signed
projected momentum \(N\). -/
theorem contDiffOn_eulerVelocity_of_integrated_projected_momentum [CompleteSpace F] {S : ℝ}
    (hS : 0 < S) {u N : ℝ → E → F}
    (J : ∀ m, ℝ → BoundedSpatialJet E F m) (r : ℕ → ℕ)
    (B : ∀ m, SpatialJetTuple E F (r m) →L[ℝ] SpatialJetTuple E F (r m) →L[ℝ] BoundedSpatialJet E F m)
    (hu : ∀ t ∈ Icc (0 : ℝ) S, ContDiff ℝ ∞ (u t))
    (hN : ∀ t ∈ Icc (0 : ℝ) S, ContDiff ℝ ∞ (N t))
    (hactual : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x, J m t x = iteratedFDeriv ℝ m (u t) x)
    (hcont : ∀ m, ContinuousOn (J m) (Icc 0 S))
    (hB : ∀ t ∈ Icc (0 : ℝ) S, ∀ m x,
      B m (fun i => J i t) (fun i => J i t) x = iteratedFDeriv ℝ m (N t) x)
    (hEq : ∀ t ∈ Icc (0 : ℝ) S, ∀ x,
      u t x = u 0 x + endpointPrimitive (fun s => N s x) t) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ univ) := by
  let U (m : ℕ) (t : ℝ) := B m (fun i => J i t) (fun i => J i t)
  have hUc (m : ℕ) : ContinuousOn (U m) (Icc 0 S) := by
    have hj : ContinuousOn (fun s => (fun i => J i s : SpatialJetTuple E F (r m))) (Icc 0 S) :=
      continuousOn_pi.mpr fun i => hcont i
    exact (((B m).continuous.comp_continuousOn hj).clm_apply hj)
  have hJx := boundedSpatialJets_derivative_of_actual J hu hactual
  have hUx := boundedSpatialJets_derivative_of_actual U hN hB
  have hEq0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) S) :
      J 0 t = J 0 0 + endpointPrimitive (U 0) t := by
    let C := continuousMultilinearCurryFin0 ℝ E F
    have hC (v : E → F) (x : E) : C (iteratedFDeriv ℝ 0 v x) = v x := by
      rw [iteratedFDeriv_zero_eq_comp, Function.comp_apply, C.apply_symm_apply]
    apply BoundedContinuousFunction.ext
    intro x
    apply C.injective
    change C (J 0 t x) = C (J 0 0 x + endpointPrimitive (U 0) t x)
    have h0 : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hS.le⟩
    have hInt := ((hUc 0).mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc (μ := volume) ht.1
    have hComm :
        endpointPrimitive (fun s => C (U 0 s x)) t = C (endpointPrimitive (U 0) t x) :=
      (C.toContinuousLinearEquiv.toContinuousLinearMap.comp (evalCLM ℝ x)).intervalIntegral_comp_comm hInt
    have hRepr : (fun s => C (U 0 s x)) =ᵐ[volume.restrict (Ioc (0 : ℝ) S)] fun s => N s x := by
      filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with s hs
      exact (congrArg C (hB s (Ioc_subset_Icc_self hs) 0 x)).trans (hC (N s) x)
    rw [map_add, hactual t ht 0 x, hactual 0 h0 0 x, hC, hC, ← hComm,
      endpointPrimitive_congr_ae hRepr ht]
    exact hEq t ht x
  exact contDiffOn_eulerVelocity_of_integrated_jets hS J r B hu hactual hcont
    (integrated_spatialJets_of_zeroth hS.le J U hJx hUx hUc hEq0)

/-- Joint regularity on every positive closed prefix gives regularity on the
preterminal half-open slab, retaining its initial boundary. -/
theorem contDiffOn_halfOpen_of_closedPrefixes {T : ℝ} {u : ℝ → E → F}
    (h : ∀ S : ℝ, 0 < S → S < T →
      ContDiffOn ℝ ∞ (Function.uncurry u) (Icc 0 S ×ˢ (univ : Set E))) :
    ContDiffOn ℝ ∞ (Function.uncurry u) (Ico 0 T ×ˢ (univ : Set E)) := by
  intro z hz
  obtain ⟨S, hzS, hST⟩ := exists_between hz.1.2
  have hlt : (fun w : ℝ × E => w.1) ⁻¹' Iio S ∈ 𝓝 z :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hzS)
  have hnbh : Icc 0 S ×ˢ (univ : Set E) ∈ 𝓝[Ico 0 T ×ˢ (univ : Set E)] z := by
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hlt] with w hw hws
    exact ⟨⟨hw.1.1, (show w.1 < S from hws).le⟩, hw.2⟩
  exact (h S (hz.1.1.trans_lt hzS) hST z ⟨⟨hz.1.1, hzS.le⟩, hz.2⟩)
    |>.mono_of_mem_nhdsWithin hnbh

end

end TorusEuler

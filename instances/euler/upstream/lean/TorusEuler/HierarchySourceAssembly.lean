import TorusEuler.HierarchyLevelBounds
import TorusEuler.HierarchySourceBounds
import TorusEuler.PhaseProfileEstimates
import TorusEuler.PhaseSource
import TorusEuler.WaveCompletion
import Mathlib.Analysis.Normed.Module.Seminorm.Basic

/-! Phase averaging and the finite summations for the sources of
Theorem 5.6. See (5.25)–(5.28) for the sources and (5.42) for the
phase integration by parts. -/

open scoped InnerProductSpace ContDiff

namespace TorusEuler

section Indices

private theorem mem_hierarchyLevelPairs_iff {P d p : ℕ} {ij : ℕ × ℕ} :
    ij ∈ hierarchyLevelPairs P d p ↔
      (d + 1 ≤ ij.1 ∧ ij.1 ≤ P + 1) ∧ (1 ≤ ij.2 ∧ ij.2 ≤ P + 1) ∧
        ij.1 + ij.2 = p + d := by
  constructor
  · intro hij
    obtain ⟨hbox, hlevel⟩ := Finset.mem_filter.mp hij
    obtain ⟨hi, hj⟩ := Finset.mem_product.mp hbox
    rw [Finset.mem_Icc] at hi hj
    unfold hierarchyAdvectionLevel at hlevel
    exact ⟨hi, hj, by omega⟩
  · rintro ⟨hi, hj, hsum⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr hi, Finset.mem_Icc.mpr hj⟩, ?_⟩
    unfold hierarchyAdvectionLevel
    omega

/-- Integrating a completion interaction by parts moves its advecting
index back by one. This changes the fast diagonal to the slow diagonal
with exactly the same second index. -/
theorem hierarchy_sum_fast_previous {E : Type*} [AddCommMonoid E]
    {P p : ℕ} (hp : p ≤ P) (f : ℕ → ℕ → E) :
    (∑ ij ∈ hierarchyLevelPairs P 1 p, f (ij.1 - 1) ij.2) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p, f ij.1 ij.2 := by
  refine Finset.sum_bij' (fun ij _ => (ij.1 - 1, ij.2))
    (fun ij _ => (ij.1 + 1, ij.2)) ?_ ?_ ?_ ?_ ?_
  · intro ij hij
    rw [mem_hierarchyLevelPairs_iff] at hij ⊢
    dsimp only
    omega
  · intro ij hij
    rw [mem_hierarchyLevelPairs_iff] at hij ⊢
    dsimp only
    omega
  · intro ij hij
    rw [mem_hierarchyLevelPairs_iff] at hij
    exact Prod.ext (by dsimp only; omega) rfl
  · intro ij _
    exact Prod.ext (Nat.add_sub_cancel _ _) rfl
  · intro ij _
    rfl

theorem hierarchyLevelPairs_two_slow {P : ℕ} (hP : 2 ≤ P) :
    hierarchyLevelPairs P 0 2 = {(1, 1)} := by
  ext ⟨i, j⟩
  rw [mem_hierarchyLevelPairs_iff]
  simp only [Finset.mem_singleton, Prod.mk.injEq]
  omega

theorem hierarchyLevelPairs_two_fast {P : ℕ} (hP : 2 ≤ P) :
    hierarchyLevelPairs P 1 2 = {(2, 1)} := by
  ext ⟨i, j⟩
  rw [mem_hierarchyLevelPairs_iff]
  simp only [Finset.mem_singleton, Prod.mk.injEq]
  omega

end Indices

section Phase

/-- The averaged completion term uses a label divergence and no fast
derivative. The longitudinal derivative condition is the component of
the curl completion equation along the phase covector. -/
theorem hierarchy_phaseMean_completion (κ : Vec3) (C Y Ys : ℝ → Vec3) (divV : ℝ → ℝ)
    (hC : Continuous C) (hCper : Function.Periodic C 1) (hCmean : phaseMean C = 0)
    (hYper : Function.Periodic Y 1) (hY : ∀ s, HasDerivAt Y (Ys s) s)
    (hYs : Continuous Ys) (hdivV : Continuous divV)
    (hdiv : ∀ s, HasDerivAt (fun r => ⟪κ, C r⟫_ℝ) (-divV s) s) :
    phaseMean (fun s => ⟪κ, C s⟫_ℝ • Ys s) = phaseMean (fun s => divV s • Y s) := by
  simp only [real_inner_comm (C _) κ]
  exact phaseMean_fastSource κ C Y Ys divV hCper hYper hY hYs hdivV
    (fun s => by rw [real_inner_comm]; exact
      waveCorrection_longitudinal_of_mean_zero hdiv hdivV hC hCmean s)

/-- A phase-independent advector of the fast derivative contributes
only to the oscillatory source. -/
theorem hierarchy_phaseMean_supplementary (κ B : Vec3) (Y Ys : ℝ → Vec3)
    (hYper : Function.Periodic Y 1) (hY : ∀ s, HasDerivAt Y (Ys s) s)
    (hYs : Continuous Ys) :
    phaseMean (fun s => ⟪κ, B⟫_ℝ • Ys s) = 0 := by
  rw [real_inner_comm B κ]
  exact phaseMean_meanFastSource κ B Y Ys hYper hY hYs

/-- A fixed-label linear operation on a centered oscillation has
vanishing phase average. This applies to its advection of a mean. -/
theorem hierarchy_phaseMean_apply_eq_zero {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℝ] F) {f : ℝ → E} (hf : Continuous f) (hm : phaseMean f = 0) :
    phaseMean (fun s => L (f s)) = 0 := by
  rw [phaseMean, L.intervalIntegral_comp_comm (hf.intervalIntegrable 0 1),
    ← phaseMean, hm, map_zero]

/-- Advection by a phase-independent vector commutes with phase
averaging. When the advected field is centered the mixed mean is zero. -/
theorem hierarchy_phaseMean_labelDerivative_eq_zero
    {f : Vec3 → ℝ → Vec3} (hf : ContDiff ℝ ∞ (Function.uncurry f))
    (hm : ∀ a, phaseMean (f a) = 0) (a v : Vec3) :
    phaseMean (fun s => fderiv ℝ (fun b => f b s) a v) = 0 := by
  let J (s : ℝ) := iteratedFDeriv ℝ 1 (fun b => f b s) a
  let L : (Vec3 [×1]→L[ℝ] Vec3) →L[ℝ] Vec3 :=
    (ContinuousLinearMap.apply ℝ Vec3 v).comp
      (continuousMultilinearCurryFin1 ℝ Vec3 Vec3).toContinuousLinearEquiv.toContinuousLinearMap
  have hJ (s : ℝ) : J s =
      (iteratedFDeriv ℝ 1 (Function.uncurry f) (a, s)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ Vec3 ℝ) := by
    let I := ContinuousLinearMap.inl ℝ Vec3 ℝ
    let shift := Function.uncurry f ∘ fun (x : Vec3 × ℝ) => x + (0, s)
    have heq : (fun b => f b s) = shift ∘ I := by
      funext b
      simp [I, shift, Function.uncurry]
    have hshift : ContDiff ℝ ∞ shift := hf.comp (contDiff_id.add contDiff_const)
    dsimp only [J]
    rw [heq, I.iteratedFDeriv_comp_right hshift a (by simp)]
    change ContinuousMultilinearMap.compContinuousLinearMap
      (iteratedFDeriv ℝ 1 (fun x => Function.uncurry f (x + (0, s))) (I a))
      (fun _ => I) = _
    rw [iteratedFDeriv_comp_add_right]
    simp [I]
  have hcont : Continuous J := by
    simp only [J] at hJ
    rw [show J = _ from funext hJ]
    exact (ContinuousMultilinearMap.compContinuousLinearMapL (F := Vec3)
      (fun _ : Fin 1 => ContinuousLinearMap.inl ℝ Vec3 ℝ)).continuous.comp
      ((hf.continuous_iteratedFDeriv (by simp)).comp (continuous_const.prodMk continuous_id))
  have hL (s : ℝ) : L (J s) = fderiv ℝ (fun b => f b s) a v := by
    simp only [J, L, ContinuousLinearMap.comp_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearMap.apply_apply,
      continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]
    rw [show (0 : Fin 1) = Fin.last 0 from rfl, Fin.snoc_last]
  have hcomm := iteratedFDeriv_phaseMean hf 1 a
  have hzero : (fun b => phaseMean (f b)) = fun _ => 0 := funext hm
  rw [hzero] at hcomm
  have hmean : phaseMean J = 0 := hcomm.symm.trans (by simp)
  simp_rw [← hL]
  exact hierarchy_phaseMean_apply_eq_zero L hcont hmean

end Phase

section TimeWeight

variable {T : Type*}

/-- The time weight of a fast product can be put on either profile.
The phase derivative differentiates the fixed-time slice. -/
theorem hierarchy_fastAdvection_timeFactors
    (r q : T → ℝ) (κ z g : T → Vec3 × ℝ → Vec3)
    (hg : ∀ t, Differentiable ℝ (g t)) :
    (fun t x => ⟪κ t x, r t • z t x⟫_ℝ •
      fderiv ℝ (fun y => q t • g t y) x (0, 1)) =
    fun t x => (r t * q t) •
      (⟪κ t x, z t x⟫_ℝ • fderiv ℝ (g t) x (0, 1)) := by
  funext t x
  rw [fderiv_fun_const_smul (hg t x)]
  simp only [inner_smul_right, _root_.smul_apply, smul_smul]
  ring_nf

/-- Time normalization also passes to either profile in each coframe
coordinate of the slow product. -/
theorem hierarchy_slowAdvection_timeFactors
    (r q : T → ℝ) (A : T → Vec3 × ℝ → Vec3 →L[ℝ] Vec3)
    (z g : T → Vec3 × ℝ → Vec3) (i : Fin 3) (hg : ∀ t, Differentiable ℝ (g t)) :
    (fun t x => (A t x (r t • z t x)) i •
      fderiv ℝ (fun y => q t • g t y) x (coordinateDirection i, 0)) =
    fun t x => (r t * q t) •
      ((A t x (z t x)) i • fderiv ℝ (g t) x (coordinateDirection i, 0)) := by
  funext t x
  rw [fderiv_fun_const_smul (hg t x), map_smul]
  change (r t * (A t x (z t x)) i) •
      (q t • fderiv ℝ (g t) x (coordinateDirection i, 0)) = _
  simp only [smul_smul]
  ring_nf

/-- The supplementary fast term carries the time weight on the
differentiated oscillation and uses the unweighted advecting mean. -/
theorem hierarchyFastAdvection_timeWeighted_le
    (ℓ h : ℝ) (hh : h ≠ 0) (n : ℕ) {freq L : ℝ} (γ : T → ℝ)
    {κ z g : T → (Vec3 × ℝ) → Vec3}
    (hκ : ∀ t, ContDiff ℝ ∞ (κ t)) (hz : ∀ t, ContDiff ℝ ∞ (z t))
    (hg : ∀ t, ContDiff ℝ ∞ (g t))
    (hκb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (hierarchyScaledPhaseCoefficient h κ)))
    (hzb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w z))
    (hgb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1),
      BddAbove (hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
        (fun t x => (γ t)⁻¹ • g t x)))
    (hκN : hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (hierarchyScaledPhaseCoefficient h κ) ≤ L * freq ^ (3 / 2 : ℝ)) :
    hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n
      (fun t x => (γ t)⁻¹ • (⟪κ t x, z t x⟫_ℝ • fderiv ℝ (g t) x (0, 1))) ≤
      hierarchyQuadraticConstant (Fin 4) n ^ 2 * (L * freq ^ (3 / 2 : ℝ)) *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n z *
        hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) (n + 1)
          (fun t x => (γ t)⁻¹ • g t x) := by
  have ht := hierarchy_fastAdvection_timeFactors (fun _ => 1) (fun t => (γ t)⁻¹)
    κ z g (fun t => (hg t).differentiable (by simp))
  simp only [one_smul, one_mul] at ht
  rw [← ht]
  exact hierarchyFastAdvection_le ℓ h hh n hκ hz
    (fun t => (hg t).const_smul ((γ t)⁻¹)) hκb hzb hgb hκN

end TimeWeight

section Source

variable {E Q : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup Q] [Module ℝ Q]

/-- The linear part of the retained source includes the removal of the
activation derivative at level two. -/
def HierarchyOperators.relayAtLevel (A : HierarchyOperators E Q)
    (u : HierarchyProfiles E Q) (completionSwitch : E) (p : ℕ) : E :=
  A.material (u.C (p - 1)) + A.labelGrad (u.p (p - 1)) -
    (if p = 2 then completionSwitch else 0)

/-- Averaging the actual retained source gives the three slow sums in
Theorem 5.6. The fast average has already been integrated by parts
in `hcompletion`, while `hmixed` contains the two centered slow terms. -/
theorem HierarchyOperators.average_sourceBeforeMean_eq
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ≤ P) (completionSwitch : E) (divProduct : ℕ → ℕ → E)
    (hrelay : A.average (A.relayAtLevel u completionSwitch p) = 0)
    (hmixed : ∀ i j,
      A.average (A.labelAdv (u.Y i) (u.B j)) = 0 ∧
      A.average (A.labelAdv (u.B i) (u.Y j)) = 0)
    (hmean : ∀ i j, A.average (A.labelAdv (u.B i) (u.B j)) =
      A.labelAdv (u.B i) (u.B j))
    (hcompletion : ∀ i j, A.average (A.phaseAdv (u.C i) (u.Y j)) =
      A.average (divProduct i j)) :
    A.average (A.sourceBeforeMean u P completionSwitch p) =
      ∑ ij ∈ hierarchyLevelPairs P 0 p,
        (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2)) +
          A.average (divProduct ij.1 ij.2) + A.labelAdv (u.B ij.1) (u.B ij.2)) := by
  change A.average (A.relayAtLevel u completionSwitch p +
    (∑ ij ∈ hierarchyLevelPairs P 0 p, A.labelProduct u ij) +
    (∑ ij ∈ hierarchyLevelPairs P 1 p, A.completionPhaseProduct u ij)) = _
  simp only [map_add, map_sum, hrelay, zero_add, HierarchyOperators.completionPhaseProduct,
    hcompletion]
  rw [hierarchy_sum_fast_previous hp (fun i j => A.average (divProduct i j))]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro ij _
  simp only [HierarchyOperators.labelProduct, HierarchyProfiles.Z,
    map_add, LinearMap.add_apply, (hmixed _ _).1, (hmixed _ _).2, hmean, zero_add, add_zero]
  abel

/-- The initial mean forcing contains the parent residual precisely at
level two. There are only two quadratic operators at this level. -/
theorem HierarchyOperators.level_two_meanSource
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P : ℕ} (hP : 2 ≤ P) (completionSwitch parentResidual divProduct : E)
    (hC : u.C 0 = 0) (hB : u.B 1 = 0)
    (hrelay : A.average (A.relayAtLevel u completionSwitch 2) = 0)
    (hcompletion : A.average (A.phaseAdv (u.C 1) (u.V 1)) = A.average divProduct) :
    -A.average (A.sourceBeforeMean u P completionSwitch 2) -
        (if (2 : ℕ) = 2 then parentResidual else 0) =
      -(A.average (A.labelAdv (u.V 1) (u.V 1)) + A.average divProduct + parentResidual) := by
  change -A.average (A.relayAtLevel u completionSwitch 2 +
    (∑ ij ∈ hierarchyLevelPairs P 0 2, A.labelProduct u ij) +
    (∑ ij ∈ hierarchyLevelPairs P 1 2, A.completionPhaseProduct u ij)) - parentResidual = _
  rw [hierarchyLevelPairs_two_slow hP, hierarchyLevelPairs_two_fast hP]
  simp only [Finset.sum_singleton]
  change -A.average (A.relayAtLevel u completionSwitch 2 +
    A.labelAdv (u.Z 1) (u.Z 1) + A.phaseAdv (u.C 1) (u.Y 1)) - parentResidual = _
  have hY : u.Y 1 = u.V 1 := by simp [HierarchyProfiles.Y, hC]
  have hZ : u.Z 1 = u.V 1 := by simp [HierarchyProfiles.Z, hY, hB]
  rw [hY, hZ]
  simp only [map_add, hrelay, zero_add, hcompletion]
  abel

private def centeredProfile (A : HierarchyOperators E Q) : E →ₗ[ℝ] E :=
  LinearMap.id - A.average

private theorem centeredProfile_apply (A : HierarchyOperators E Q) (f : E) :
    centeredProfile A f = f - A.average f := rfl

/-- Phase subtraction discards the mean–mean term before the time weight
is applied. Every remaining product has an oscillatory factor. -/
theorem HierarchyOperators.centered_labelProduct_eq
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q) (i j : ℕ)
    (hmean : A.average (A.labelAdv (u.B i) (u.B j)) =
      A.labelAdv (u.B i) (u.B j)) :
    A.labelProduct u (i, j) - A.average (A.labelProduct u (i, j)) =
      let f := A.labelAdv (u.Y i) (u.Y j) + A.labelAdv (u.Y i) (u.B j) +
        A.labelAdv (u.B i) (u.Y j)
      f - A.average f := by
  simp only [HierarchyOperators.labelProduct, HierarchyProfiles.Z, map_add,
    LinearMap.add_apply, hmean]
  abel

private theorem hierarchy_seminorm_finset_le {I : Type*}
    (N : Seminorm ℝ E) (s : Finset I) (F : I → E) (b : I → ℝ)
    (hb : ∀ i ∈ s, N (F i) ≤ b i) :
    N (∑ i ∈ s, F i) ≤ ∑ i ∈ s, b i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (map_add_le_add N _ _).trans (add_le_add
      (hb _ (Finset.mem_insert_self _ _)) (ih fun j hj => hb _ (Finset.mem_insert_of_mem hj)))

/-- The unweighted source bound in the measured recurrence. Only the
two slow advections and the label-divergence product are charged. -/
theorem HierarchyMeasuredLevels.ofProfiles_meanForcing
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (n : ℕ)
    (completionSwitch parentResidual : E) {freq L K : ℝ} (hf : 0 ≤ freq)
    (unweighted weighted : ℕ → Seminorm ℝ E) (pressureWeighted : ℕ → Q → ℝ)
    (hq : ∀ m a, 0 ≤ pressureWeighted m a) (divProduct : ℕ → ℕ → E)
    (hrelay : A.average (A.relayAtLevel u completionSwitch p) = 0)
    (hmixed : ∀ i j,
      A.average (A.labelAdv (u.Y i) (u.B j)) = 0 ∧
      A.average (A.labelAdv (u.B i) (u.Y j)) = 0)
    (hmean : ∀ i j, A.average (A.labelAdv (u.B i) (u.B j)) =
      A.labelAdv (u.B i) (u.B j))
    (hcompletion : ∀ i j, A.average (A.phaseAdv (u.C i) (u.Y j)) =
      A.average (divProduct i j)) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch parentResidual freq hf
      (fun m => unweighted m) (fun m => weighted m) pressureWeighted
      (fun m => apply_nonneg (unweighted m)) (fun m => apply_nonneg (weighted m)) hq
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      unweighted n (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) ≤
        K * L * (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      unweighted n (A.average (divProduct ij.1 ij.2)) ≤
        K * L * (s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      unweighted n (A.labelAdv (u.B ij.1) (u.B ij.2)) ≤
        K * L * (s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) →
    (p = 2 → unweighted n parentResidual ≤ K * freq ^ hierarchyMeanExponent 2) →
    s.meanSource n p ≤ K * L *
      (∑ ij ∈ hierarchyLevelPairs P 0 p,
        (s.Y (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.osc (n + 1) ij.1 * s.Y (n + 1) ij.2 +
          s.mean (n + 1) ij.1 * s.mean (n + 1) ij.2)) +
      (if p = 2 then K * freq ^ hierarchyMeanExponent 2 else 0) := by
  dsimp only
  intro hYY hdiv hBB hR
  let N := unweighted n
  have hp₁ : p ≠ 1 := by have h := (Finset.mem_Icc.mp hp).1; omega
  change (if p = 1 then 0 else N (-A.average (A.sourceBeforeMean u P completionSwitch p) -
    (if p = 2 then parentResidual else 0))) ≤ _
  rw [ite_eq_right hp₁,
    A.average_sourceBeforeMean_eq u (Finset.mem_Icc.mp hp).2 completionSwitch
      divProduct hrelay hmixed hmean hcompletion, sub_eq_add_neg, ← neg_add, map_neg_eq_map]
  apply (map_add_le_add N _ _).trans
  apply add_le_add
  · rw [Finset.mul_sum]
    apply hierarchy_seminorm_finset_le
    intro ij hij
    calc
      _ ≤ N (A.average (A.labelAdv (u.Y ij.1) (u.Y ij.2))) +
          N (A.average (divProduct ij.1 ij.2)) + N (A.labelAdv (u.B ij.1) (u.B ij.2)) :=
        (map_add_le_add N _ _).trans (add_le_add (map_add_le_add N _ _) le_rfl)
      _ ≤ _ := by
        rw [mul_add, mul_add]
        exact add_le_add (add_le_add (hYY ij hij) (hdiv ij hij)) (hBB ij hij)
  · by_cases h : p = 2
    · simpa [h] using hR h
    · simp [h]

/-- The weighted source bound in the measured recurrence. One
centered slow term and two fast terms occur at each selected pair.
The extra phase-frequency factor applies to the fast terms alone. -/
theorem HierarchyMeasuredLevels.ofProfiles_oscForcing
    (A : HierarchyOperators E Q) (u : HierarchyProfiles E Q)
    {P p : ℕ} (hp : p ∈ Finset.Icc 2 P) (n : ℕ)
    (completionSwitch parentResidual : E) {freq L K : ℝ} (hf : 0 ≤ freq)
    (unweighted weighted : ℕ → Seminorm ℝ E) (pressureWeighted : ℕ → Q → ℝ)
    (hq : ∀ m a, 0 ≤ pressureWeighted m a)
    (hrelayMean : A.average (A.relayAtLevel u completionSwitch p) = 0) :
    let s := HierarchyMeasuredLevels.ofProfiles A u P completionSwitch parentResidual freq hf
      (fun m => unweighted m) (fun m => weighted m) pressureWeighted
      (fun m => apply_nonneg (unweighted m)) (fun m => apply_nonneg (weighted m)) hq
    (weighted n (A.relayAtLevel u completionSwitch p) ≤ K * L *
      (freq ^ (-1 : ℝ) * (s.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)))) →
    (∀ ij ∈ hierarchyLevelPairs P 0 p,
      weighted n (A.labelProduct u ij - A.average (A.labelProduct u ij)) ≤
        K * L * (s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 1 p,
      weighted n (A.completionPhaseProduct u ij - A.average (A.completionPhaseProduct u ij)) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2)) →
    (∀ ij ∈ hierarchyLevelPairs P 1 p,
      weighted n (A.meanPhaseProduct u ij) ≤
        (K * L * freq ^ (3 / 2 : ℝ)) * (s.mean n ij.1 * s.Y (n + 1) ij.2)) →
    s.oscSource n p ≤ K * L *
      (freq ^ (-1 : ℝ) * (s.osc (n + 1) (p - 1) + s.oscSource (n + 1) (p - 1)) +
      (∑ ij ∈ hierarchyLevelPairs P 0 p, s.Z (n + 1) ij.1 * s.Z (n + 1) ij.2) +
      freq ^ (3 / 2 : ℝ) * (∑ ij ∈ hierarchyLevelPairs P 1 p,
        (s.completion n (ij.1 - 1) * s.Y (n + 1) ij.2 +
          s.mean n ij.1 * s.Y (n + 1) ij.2))) := by
  dsimp only
  intro hrelay hslow hfast hmean
  let N := weighted n
  have hp₁ : p ≠ 1 := by have h := (Finset.mem_Icc.mp hp).1; omega
  change (if p = 1 then 0 else N
    (-(A.sourceBeforeMean u P completionSwitch p -
      A.average (A.sourceBeforeMean u P completionSwitch p)) -
      hierarchyAdvectionAtLevel P 1 p (A.meanPhaseProduct u))) ≤ _
  rw [ite_eq_right hp₁, sub_eq_add_neg, ← neg_add, map_neg_eq_map]
  change N ((centeredProfile A)
    (A.relayAtLevel u completionSwitch p +
      (∑ ij ∈ hierarchyLevelPairs P 0 p, A.labelProduct u ij) +
      (∑ ij ∈ hierarchyLevelPairs P 1 p, A.completionPhaseProduct u ij)) +
    (∑ ij ∈ hierarchyLevelPairs P 1 p, A.meanPhaseProduct u ij)) ≤ _
  simp only [map_add, map_sum, centeredProfile_apply, hrelayMean, sub_zero]
  rw [add_assoc (A.relayAtLevel u completionSwitch p + _), ← Finset.sum_add_distrib]
  conv_rhs => rw [mul_add, mul_add]
  apply (map_add_le_add N _ _).trans
  apply add_le_add
  · rw [Finset.mul_sum]
    exact (map_add_le_add N _ _).trans
      (add_le_add hrelay (hierarchy_seminorm_finset_le N _ _ _ hslow))
  · rw [← mul_assoc, Finset.mul_sum]
    apply hierarchy_seminorm_finset_le
    intro ij hij
    rw [mul_add]
    exact (map_add_le_add N _ _).trans (add_le_add (hfast ij hij) (hmean ij hij))

end Source

end TorusEuler

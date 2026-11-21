import TorusEuler.TerminalTimeGraphCalculus
import TorusEuler.TerminalMixedDerivatives
import TorusEuler.TerminalProfileTimeDerivatives
import TorusEuler.HierarchyGraphReadoutBounds
import TorusEuler.PhysicalHierarchyProfileBounds

/-! Mixed Eulerian derivatives of the actual graph on the parent slab. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Velocity} {X : ℝ → Velocity}

local notation "I" => Icc (0 : ℝ) T
local notation "Slab" => Set.prod I (univ : Set Vec3)
local notation "InvFlow" => (fun r => X r 0)

theorem timeJet_phaseIndependent (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hmean : HierarchyPeriodicProfile.PhaseIndependent f.val.val) (i : ℕ) :
    HierarchyPeriodicProfile.PhaseIndependent (timeJet hT i f).val.val := by
  rintro ⟨t,x,s⟩ ⟨ht,-⟩ σ
  rw [timeJet_apply hT i f ht, timeJet_apply hT i f ht]
  exact iteratedDerivWithin_congr (fun r hr =>
    hmean (r,x,s) ⟨hr,mem_univ _⟩ σ) ht

/-- The exact arbitrary-order Leibniz recurrence for converting pure profile
time jets to Eulerian time derivatives on the parent graph. -/
theorem eulerianTimeJet_graphRead_succ (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ r ∈ I, SpatiallyPeriodic (U r))
    (f : HierarchyTwistedProfile T k E) (i : ℕ) {t : ℝ} (ht : t ∈ I) (x : Vec3) :
    iteratedDerivWithin (i + 1) (fun r => graphRead InvFlow f r x) I t =
      iteratedDerivWithin i (fun r => graphRead InvFlow (timeDerivative hT f) r x) I t -
        ∑ l ∈ Finset.range (i + 1), i.choose l •
          fderiv ℝ (fun y => iteratedDerivWithin (i - l) (fun r => graphRead InvFlow f r y) I t) x
            (iteratedDerivWithin l (fun r => U r x) I t) := by
  let F := graphRead InvFlow f
  let F' := graphRead InvFlow (timeDerivative hT f)
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hF : ContDiffOn ℝ ∞ (Function.uncurry F) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k f.val.val hA
  have hF' : ContDiffOn ℝ ∞ (Function.uncurry F') Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k (timeDerivative hT f).val.val hA
  have hD := terminal_contDiffOn_spaceDerivative hT (f := F) hF
  have huread := terminal_contDiffOn_timeSlice hU x
  have hDread : ContDiffOn ℝ ∞ (fun r => fderiv ℝ (F r) x) I :=
    hD.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr,mem_univ x⟩)
  let adv : ℝ → E := fun r => fderiv ℝ (F r) x (U r x)
  have hadv : ContDiffOn ℝ ∞ adv I := hDread.clm_apply huread
  have hderiv : EqOn (derivWithin (fun r => F r x) I) ((fun r => F' r x) - adv) I := by
    intro r hr
    have h := HierarchySmoothProfile.slabTimePartial_graphRead hT f.val.val hX hU hper k hr x
    let z := hierarchyGraphPoint InvFlow k r x
    have hz : z ∈ hierarchyProfileSlab T := ⟨hr,mem_univ _⟩
    have heq :
        (HierarchySmoothProfile.slabTimePartial hT f.val.val).val z =
          (timeDerivative hT f).val.val.val z := by
      rw [HierarchySmoothProfile.slabTimePartial_apply hT f.val.val hz,
        timeDerivative, directionDerivative_apply hT _ _ hz]
    change derivWithin (fun s => F s x) I r + adv r = _ at h
    rw [show HierarchySmoothProfile.graphRead InvFlow k
        (HierarchySmoothProfile.slabTimePartial hT f.val.val) r x = F' r x from heq] at h
    exact eq_sub_of_add_eq h
  rw [iteratedDerivWithin_succ', iteratedDerivWithin_congr hderiv ht,
    iteratedDerivWithin_sub ht (uniqueDiffOn_Icc hT)
      ((terminal_contDiffOn_timeSlice hF' x).of_le (by simp) t ht)
      (hadv.of_le (by simp) t ht)]
  have hAdvJet := iteratedDerivWithin_bilinear (ContinuousLinearMap.apply ℝ E)
    (uniqueDiffOn_Icc hT) ht huread hDread i
  change iteratedDerivWithin i adv I t = _ at hAdvJet
  rw [hAdvJet]
  simp only [ContinuousLinearMap.apply_apply]
  congr 1
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (fun D : Vec3 →L[ℝ] E => i.choose l • D
    (iteratedDerivWithin l (fun r => U r x) I t))
      (terminal_iteratedDerivWithin_fderiv_comm hT (f := F) hF (i-l) ht x)

/-- Time differentiating an actual graph preserves periodicity. -/
theorem spatiallyPeriodic_eulerianTimeJet_graphRead (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ r ∈ I, SpatiallyPeriodic (U r))
    (f : HierarchyTwistedProfile T k E) (i : ℕ) {t : ℝ} (ht : t ∈ I) :
    SpatiallyPeriodic (fun x => iteratedDerivWithin i (fun r => graphRead InvFlow f r x) I t) := by
  exact slabTimeJet_periodic
    (fun _ hr => spatiallyPeriodic_inverseParentGraphRead hT hX hU hper f hr) i ht

end

end TorusEuler.HierarchyTwistedProfile

namespace TorusEuler

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The spatial Leibniz estimate keeps a common geometric rate when derivatives
are distributed between an advection direction and its argument. -/
theorem norm_iteratedFDeriv_advection_le_geometric
    {F : Vec3 → E} {V : Vec3 → Vec3} (hF : ContDiff ℝ ∞ F) (hV : ContDiff ℝ ∞ V)
    {B C D : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) (m : ℕ)
    (hFjet : ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j F x‖ ≤ C * B ^ j)
    (hVjet : ∀ j ≤ m, ∀ x, ‖iteratedFDeriv ℝ j V x‖ ≤ D * B ^ j) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (fun y => fderiv ℝ F y (V y)) x‖ ≤
      (2 : ℝ) ^ m * C * D * B ^ (m + 1) := by
  have hm : (∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ)) = (2 : ℝ) ^ m := by
    exact_mod_cast Nat.sum_range_choose m
  refine (norm_iteratedFDeriv_clm_apply (hF.fderiv_right (by simp)) hV x (n := m) (by simp)).trans ?_
  calc
    _ ≤ ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (C * B ^ (j + 1)) * (D * B ^ (m - j)) := by
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      rw [norm_iteratedFDeriv_fderiv]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hFjet _ (by omega) x) (Nat.cast_nonneg _))
        (hVjet _ (Nat.sub_le _ _) x) (norm_nonneg _) (by positivity)
    _ = _ := by
      conv_lhs =>
        enter [2,j]
        rw [show (m.choose j : ℝ) * (C * B ^ (j + 1)) * (D * B ^ (m - j)) =
          (m.choose j : ℝ) * (C * D) * B ^ ((j + 1) + (m - j)) by rw [pow_add]; ring]
      calc
        _ = ∑ j ∈ Finset.range (m + 1), (m.choose j : ℝ) * (C * D) * B ^ (m + 1) := by
          refine Finset.sum_congr rfl fun j hj => ?_
          have hj' := Finset.mem_range.mp hj
          rw [show j + 1 + (m - j) = m + 1 by omega]
        _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul, hm]; ring

end

end TorusEuler

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {U : Velocity} {X : ℝ → Velocity}

local notation "I" => Icc (0 : ℝ) T
local notation "Slab" => Set.prod I (univ : Set Vec3)
local notation "InvFlow" => (fun r => X r 0)
local notation "EulerianJet(" i "," F ")" =>
  (slabTimeJet 0 T i F)

set_option maxHeartbeats 2500000 in
/-- A pure profile jet with `i` time directions costs at most `i`
additional spatial orders when estimated at fixed Eulerian position. The
spatial rate is any common geometric upper bound for the parent jets and
the material graph jets. -/
theorem norm_iteratedFDeriv_eulerianTimeJet_graphRead_le
    (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ r ∈ I, SpatiallyPeriodic (U r))
    (f : HierarchyTwistedProfile T k E) {N q : ℕ} {B C D : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hparent : ∀ l < q, ∀ m ≤ N, ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (EulerianJet(l,U) t) x‖ ≤ D * B ^ m)
    (hmaterial : ∀ j ≤ q, ∀ m, j + m ≤ N → ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (graphRead InvFlow (timeJet hT j f) t) x‖ ≤ C * B ^ m) :
    ∀ i ≤ q, ∀ m, i + m ≤ N → ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (EulerianJet(i,graphRead InvFlow f) t) x‖ ≤
        (1 + (2 : ℝ) ^ (N + q) * D) ^ i * C * B ^ (m + i) := by
  let J := 1 + (2 : ℝ) ^ (N + q) * D
  have hJ : 1 ≤ J := le_add_of_nonneg_right (by positivity)
  have hB₀ : 0 ≤ B := zero_le_one.trans hB
  let G (j : ℕ) := graphRead InvFlow (timeJet hT j f)
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hG (j : ℕ) : ContDiffOn ℝ ∞ (Function.uncurry (G j)) Slab :=
    HierarchySmoothProfile.contDiffOn_graphRead k (timeJet hT j f).val.val hA
  have hSpace (i j : ℕ) {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (EulerianJet(i,G j) t) :=
    slabTimeJet_slice_smooth hT (hG j) i ht
  have hUSpace (i : ℕ) {t : ℝ} (ht : t ∈ I) : ContDiff ℝ ∞ (EulerianJet(i,U) t) :=
    slabTimeJet_slice_smooth hT hU i ht
  have step (i : ℕ) : ∀ j, i + j ≤ q → ∀ m, i + j + m ≤ N → ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (EulerianJet(i,G j) t) x‖ ≤ J ^ i * C * B ^ (m + i) := by
    induction i using Nat.strong_induction_on with
    | h i ih =>
      cases i with
      | zero =>
        intro j hj m hm t ht x
        simpa only [slabTimeJet_zero, G, pow_zero, one_mul, add_zero] using
          hmaterial j (by omega) m (by omega) t ht x
      | succ i =>
        intro j hj m hm t ht x
        let V := EulerianJet(i,G (j + 1)) t
        let advection (l : ℕ) (y : Vec3) :=
          fderiv ℝ (EulerianJet(i-l,G j) t) y (EulerianJet(l,U) t y)
        let W (y : Vec3) := ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) • advection l y
        have hEq : EulerianJet(i+1,G j) t = V - W := by
          funext y
          simpa only [G, V, W, advection, Pi.sub_apply, ← timeJet_succ, Nat.cast_smul_eq_nsmul] using
            eulerianTimeJet_graphRead_succ hT hX hU hper (timeJet hT j f) i ht y
        have hAdvSmooth (l : ℕ) : ContDiff ℝ ∞ (advection l) :=
          ((hSpace (i-l) j ht).fderiv_right (by simp)).clm_apply (hUSpace l ht)
        have hTerm (l : ℕ) : ContDiff ℝ ∞ (fun y => (i.choose l : ℝ) • advection l y) :=
          (hAdvSmooth l).const_smul (i.choose l : ℝ)
        have hW : ContDiff ℝ ∞ W := ContDiff.sum (fun l _ => hTerm l)
        have hV := ih i (by omega) (j+1) (by omega) m (by omega) t ht x
        have hPow (l : ℕ) (hl : l ≤ i) (d : ℕ) : J ^ (i-l) * C * B ^ (d + (i-l)) ≤
            (J ^ i * C * B ^ i) * B ^ d := by
          calc
            _ ≤ J ^ i * C * B ^ (i + d) :=
              mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hJ (Nat.sub_le _ _)) hC)
                (pow_le_pow_right₀ hB (by omega)) (pow_nonneg hB₀ _) (by positivity)
            _ = _ := by rw [pow_add, ← mul_assoc]
        have hAdvection (l : ℕ) (hl : l ∈ Finset.range (i+1)) :
            ‖iteratedFDeriv ℝ m (advection l) x‖ ≤
              ((2 : ℝ) ^ m * J ^ i * C * D) * B ^ (m + (i + 1)) := by
          have hl' : l ≤ i := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
          have hp : ∀ d ≤ m+1, ∀ y, ‖iteratedFDeriv ℝ d (EulerianJet(i-l,G j) t) y‖ ≤
              (J ^ i * C * B ^ i) * B ^ d := by
            intro d hd y
            exact (ih (i-l) (by omega) j (by omega) d (by omega) t ht y).trans (hPow l hl' d)
          refine (norm_iteratedFDeriv_advection_le_geometric (hSpace (i-l) j ht) (hUSpace l ht)
            hB₀ (by positivity) m hp (fun d hd y => hparent l (by omega) d (by omega) t ht y) x).trans_eq ?_
          rw [show m + (i + 1) = i + (m+1) by omega, pow_add]
          ring
        have hS : (∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ)) = (2 : ℝ) ^ i := by
          exact_mod_cast Nat.sum_range_choose i
        have hWbd : ‖iteratedFDeriv ℝ m W x‖ ≤
            ((2 : ℝ) ^ (m+i) * J ^ i * C * D) * B ^ (m+(i+1)) := by
          unfold W
          rw [iteratedFDeriv_fun_sum_apply
            (f := fun l y => (i.choose l : ℝ) • advection l y)
            (fun l _ => (hTerm l).contDiffAt.of_le (by simp))]
          refine (norm_sum_le _ _).trans ?_
          calc
            _ ≤ ∑ l ∈ Finset.range (i+1), (i.choose l : ℝ) *
              (((2 : ℝ) ^ m * J ^ i * C * D) * B ^ (m+(i+1))) := by
              refine Finset.sum_le_sum fun l hl => ?_
              rw [iteratedFDeriv_const_smul_apply' ((hAdvSmooth l).contDiffAt.of_le (by simp)),
                norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
              exact mul_le_mul_of_nonneg_left (hAdvection l hl) (Nat.cast_nonneg _)
            _ = _ := by rw [← Finset.sum_mul, hS, pow_add]; ring
        rw [hEq, iteratedFDeriv_sub_apply ((hSpace i (j+1) ht).contDiffAt.of_le (by simp))
          (hW.contDiffAt.of_le (by simp))]
        refine (norm_sub_le _ _).trans ((add_le_add hV hWbd).trans ?_)
        have hBin : (2 : ℝ) ^ (m+i) ≤ 2 ^ (N+q) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hMain : J ^ i * C * B ^ (m+i) ≤ J ^ i * C * B ^ (m+(i+1)) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega)) (by positivity)
        have hSecond : ((2 : ℝ) ^ (m+i) * J ^ i * C * D) * B ^ (m+(i+1)) ≤
            ((2 : ℝ) ^ (N+q) * J ^ i * C * D) * B ^ (m+(i+1)) := by gcongr
        refine (add_le_add hMain hSecond).trans_eq ?_
        rw [pow_succ]
        dsimp only [J]
        ring
  intro i hi m hm t ht x
  simpa only [G, timeJet_zero, add_zero] using step i 0 (by omega) m (by omega) t ht x

/-- The extra spatial order gives the full half-Hölder norm at a fixed time. -/
theorem eulerianTimeJet_graphRead_holderHalf_le
    (hT : 0 < T) (hX : IsLabelFlowOn U X I)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) Slab)
    (hper : ∀ r ∈ I, SpatiallyPeriodic (U r))
    (f : HierarchyTwistedProfile T k E) {N q : ℕ} {B C D : ℝ}
    (hB : 1 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hparent : ∀ l < q, ∀ m ≤ N, ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (EulerianJet(l,U) t) x‖ ≤ D * B ^ m)
    (hmaterial : ∀ j ≤ q, ∀ m, j + m ≤ N → ∀ t ∈ I, ∀ x,
      ‖iteratedFDeriv ℝ m (graphRead InvFlow (timeJet hT j f) t) x‖ ≤ C * B ^ m)
    {i m : ℕ} (hi : i ≤ q) (hm : i + m + 1 ≤ N) {t : ℝ} (ht : t ∈ I) :
    let F := EulerianJet(i,graphRead InvFlow f) t
    SpatialHolderHalf m F ∧ spatialHolderHalfNorm m F ≤
      (3 * (m + 1) : ℝ) * ((1 + (2 : ℝ) ^ (N + q) * D) ^ i * C * B ^ (m + 1 + i)) := by
  have hA := hX.contDiffOn_inverseLabelFlow hT hU hper
  have hreg := HierarchySmoothProfile.contDiffOn_graphRead (A := InvFlow) k f.val.val hA
  refine spatialHolderHalfNorm_le_of_uniformJets (slabTimeJet_slice_smooth hT hreg i ht) (by positivity) ?_
  intro j hj x
  refine (norm_iteratedFDeriv_eulerianTimeJet_graphRead_le hT hX hU hper f hB hC hD
    hparent hmaterial i hi j (by omega) t ht x).trans ?_
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hB (by omega)) (by positivity)

end

end TorusEuler.HierarchyTwistedProfile

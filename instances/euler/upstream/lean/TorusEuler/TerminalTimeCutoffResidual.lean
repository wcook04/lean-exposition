import TorusEuler.TerminalTimeCutoffCommutation
import TorusEuler.TerminalTimeCutoffSpatial
import TorusEuler.TerminalTimeGraphCalculus
import TorusEuler.TerminalMixedDerivatives

/-! Leibniz differentiation of the actual closed-slab cutoff residual. -/

open Set UnitAddTorus
open scoped ContDiff

namespace TorusEuler

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

private theorem cutoff_smooth {T Λ : ℝ} {ψ : Vec3 → ℝ} (hT : 0 < T) {V : Velocity}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T))) (g : ℝ → C(Labels, Vec3))
    (hg : ∀ t ∈ Icc 0 T, ∀ x, g t (toUnitTorus x) = V t x) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t => terminalCutoffVector ψ Λ (g t))) (Slab(T)) :=
  contDiffOn_lift_realVectorFourierCutoff_of_coefficients ψ Λ g (fun k _ =>
      contDiffOn_mFourierCoeff_of_truncatedParentLift hT hV (fun t => g t) hg k)

private theorem terminalCutoffVector_nsmul (ψ : Vec3 → ℝ) (Λ : ℝ) (n : ℕ)
    (g : C(Labels, Vec3)) (z : Labels) :
    realVectorFourierCutoff ψ Λ (n • g) z = n • realVectorFourierCutoff ψ Λ g z := by
  simpa only [Finset.sum_const, Finset.card_range] using
    realVectorFourierCutoff_sum (Finset.range n) ψ Λ (fun _ => g) z

private theorem slabTimeJet_comp_clm {T : ℝ} {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (hT : 0 < T) (L : E →L[ℝ] F) {V : ℝ → Vec3 → E}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T))) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) (q : ℕ) :
    slabTimeJet 0 T q (fun r y => L (V r y)) t x = L (slabTimeJet 0 T q V t x) := by
  induction q generalizing t with
  | zero => simp only [slabTimeJet, iteratedDerivWithin_zero]
  | succ q ih =>
    rw [slabTimeJet_succ]
    have hd := L.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_slabTimeJet hT hV q ht x)
    exact (hd.congr_of_mem (fun r hr => ih hr) ht).derivWithin (uniqueDiffOn_Icc hT t ht)

private theorem slabTimeJet_momentumCutoff
    {T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (g : ℕ → ℝ → C(Labels, Vec3))
    (hg : ∀ j t, t ∈ Icc 0 T → ∀ x, g j t (toUnitTorus x) = slabTimeJet 0 T j V t x)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T q
        (fun r y => momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g 0 r) (g 0 r)) (toUnitTorus y)) t x =
      ∑ j ∈ Finset.range (q + 1), q.choose j •
        momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g j t) (g (q - j) t)) (toUnitTorus x) := by
  funext k
  let A : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj k
  let H : ℝ → Vec3 → MomentumTensor := fun r y => momentumTensor (V r y) (V r y)
  let h : ℕ → ℝ → C(Labels, Vec3) := fun j r =>
    ∑ i ∈ Finset.range (j + 1), j.choose i •
      momentumTensorColumn (cutoffMomentumTensor (g i r) (g (j - i) r)) k
  have hH : ContDiffOn ℝ ∞ (Function.uncurry H) (Slab(T)) :=
    (momentumTensor.contDiff.comp_contDiffOn hV).clm_apply hV
  have hHk : ContDiffOn ℝ ∞ (Function.uncurry (fun r y => A (H r y))) (Slab(T)) :=
    A.contDiff.comp_contDiffOn hH
  have hrep (j : ℕ) (r : ℝ) (hr : r ∈ Icc 0 T) (y : Vec3) :
      h j r (toUnitTorus y) = slabTimeJet 0 T j (fun u z => A (H u z)) r y := by
    rw [slabTimeJet_comp_clm hT A hH hr y]
    change _ = A (iteratedDerivWithin j (fun u => momentumTensor (V u y) (V u y)) (Icc 0 T) r)
    rw [iteratedDerivWithin_bilinear momentumTensor (uniqueDiffOn_Icc hT) hr
      (terminal_contDiffOn_timeSlice hV y) (terminal_contDiffOn_timeSlice hV y)]
    simp only [h, map_sum, map_nsmul, ContinuousMap.coe_sum, Finset.sum_apply, ContinuousMap.coe_nsmul,
      Pi.smul_apply, momentumTensorColumn, cutoffMomentumTensor, ContinuousMap.coe_mk, A,
      ContinuousLinearMap.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    rw [hg i r hr y, hg (j - i) r hr y]
  have hzero (r : ℝ) : h 0 r = momentumTensorColumn (cutoffMomentumTensor (g 0 r) (g 0 r)) k := by
    simp [h]
  have hjet :=
    slabTimeJet_realVectorFourierCutoff hT hHk h hrep ψ q ht x (Λ := Λ)
  have hLeft :
      slabTimeJet 0 T q
        (fun r y => momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g 0 r) (g 0 r)) (toUnitTorus y))
          t x k =
        slabTimeJet 0 T q
          (fun r y => realVectorFourierCutoff ψ Λ (h 0 r) (toUnitTorus y)) t x := by
    -- Use continuous coordinate projection on the tensor time curve.
    let F (r : ℝ) (y : Vec3) := momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g 0 r) (g 0 r))
      (toUnitTorus y)
    have hF : ContDiffOn ℝ ∞ (Function.uncurry F) (Slab(T)) := by
      apply contDiffOn_pi.mpr
      intro l
      let lRep (r : ℝ) := momentumTensorColumn (cutoffMomentumTensor (g 0 r) (g 0 r)) l
      let L : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj l
      have hL : ContDiffOn ℝ ∞ (Function.uncurry (fun r y => L (H r y))) (Slab(T)) :=
        L.contDiff.comp_contDiffOn hH
      have hlRep (r : ℝ) (hr : r ∈ Icc 0 T) (y : Vec3) : lRep r (toUnitTorus y) = L (H r y) := by
        simp only [lRep, H, L, ContinuousLinearMap.proj_apply, cutoffMomentumTensor, momentumTensorColumn,
          ContinuousMap.coe_mk, hg 0 r hr y, slabTimeJet, iteratedDerivWithin_zero]
      simpa only [F, Function.uncurry_def, momentumTensorFourierCutoff_apply, lRep, terminalCutoffVector] using
        (cutoff_smooth (ψ := ψ) (Λ := Λ) hT hL lRep hlRep)
    have hA := slabTimeJet_comp_clm hT A hF ht x q
    exact hA.symm.trans (by simp only [F, A, ContinuousLinearMap.proj_apply,
      momentumTensorFourierCutoff_apply, hzero])
  rw [hLeft, hjet]
  unfold h
  rw [realVectorFourierCutoff_sum]
  simp only [terminalCutoffVector_nsmul, Finset.sum_apply, Pi.smul_apply, momentumTensorFourierCutoff_apply]

private theorem terminalCutoffStress_smooth {T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity} (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (g : ℝ → C(Labels, Vec3)) (hg : ∀ t ∈ Icc 0 T, ∀ x, g t (toUnitTorus x) = V t x) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun r => terminalCutoffStress ψ Λ (g r) (g r))) (Slab(T)) := by
  let U : Velocity := fun r => terminalCutoffVector ψ Λ (g r)
  have hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Slab(T)) := cutoff_smooth hT hV g hg
  have hCut : ContDiffOn ℝ ∞
      (fun p : ℝ × Vec3 => momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g p.1) (g p.1))
        (toUnitTorus p.2)) (Slab(T)) := by
    apply contDiffOn_pi.mpr
    intro k
    let L : MomentumTensor →L[ℝ] Vec3 := ContinuousLinearMap.proj k
    let c (r : ℝ) := momentumTensorColumn (cutoffMomentumTensor (g r) (g r)) k
    have h : ContDiffOn ℝ ∞ (Function.uncurry (fun r y => L (momentumTensor (V r y) (V r y))))
        (Slab(T)) :=
      L.contDiff.comp_contDiffOn ((momentumTensor.contDiff.comp_contDiffOn hV).clm_apply hV)
    have hc (r : ℝ) (hr : r ∈ Icc 0 T) (y : Vec3) :
        c r (toUnitTorus y) = L (momentumTensor (V r y) (V r y)) := by
      simp only [c, L, momentumTensorColumn, cutoffMomentumTensor, ContinuousMap.coe_mk,
        ContinuousLinearMap.proj_apply, hg r hr y]
    simpa only [momentumTensorFourierCutoff_apply, Function.uncurry_def, c, terminalCutoffVector] using
      (cutoff_smooth (ψ := ψ) (Λ := Λ) hT h c hc)
  exact ((momentumTensor.contDiff.comp_contDiffOn hU).clm_apply hU).sub hCut

private theorem slabTimeJet_terminalCutoffStress {T Λ : ℝ} {ψ : Vec3 → ℝ} {V : Velocity}
    (hT : 0 < T) (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (g : ℕ → ℝ → C(Labels, Vec3))
    (hg : ∀ j t, t ∈ Icc 0 T → ∀ x, g j t (toUnitTorus x) = slabTimeJet 0 T j V t x)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec3) :
    slabTimeJet 0 T q (fun r => terminalCutoffStress ψ Λ (g 0 r) (g 0 r)) t x =
      ∑ j ∈ Finset.range (q + 1), q.choose j • terminalCutoffStress ψ Λ (g j t) (g (q - j) t) x := by
  let U : Velocity := fun r => terminalCutoffVector ψ Λ (g 0 r)
  let F := fun r => momentumTensor (U r x) (U r x)
  let G := fun r => momentumTensorFourierCutoff ψ Λ (cutoffMomentumTensor (g 0 r) (g 0 r)) (toUnitTorus x)
  have hzero (r : ℝ) (hr : r ∈ Icc 0 T) (y : Vec3) : g 0 r (toUnitTorus y) = V r y := by
    simpa only [slabTimeJet, iteratedDerivWithin_zero] using hg 0 r hr y
  have hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Slab(T)) := cutoff_smooth hT hV (g 0) hzero
  have hUs := terminal_contDiffOn_timeSlice hU x
  have hF : ContDiffOn ℝ ∞ F (Icc 0 T) :=
    (momentumTensor.contDiff.comp_contDiffOn hUs).clm_apply hUs
  have hStress := terminal_contDiffOn_timeSlice (terminalCutoffStress_smooth
    (ψ := ψ) (Λ := Λ) hT hV (g 0) hzero) x
  have hG : ContDiffOn ℝ ∞ G (Icc 0 T) := by
    refine (hF.sub hStress).congr (fun r _ => ?_)
    change G r = F r - (F r - G r)
    abel
  change iteratedDerivWithin q (F - G) (Icc 0 T) t = _
  rw [iteratedDerivWithin_sub ht (uniqueDiffOn_Icc hT)
    ((hF.of_le (by simp)) t ht) ((hG.of_le (by simp)) t ht)]
  have hFq := iteratedDerivWithin_bilinear momentumTensor (uniqueDiffOn_Icc hT) ht hUs hUs q
  change iteratedDerivWithin q F _ _ = _ at hFq
  rw [hFq, show iteratedDerivWithin q G (Icc 0 T) t = _ from
    slabTimeJet_momentumCutoff (ψ := ψ) (Λ := Λ) hT hV g hg q ht x, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hUJet (i : ℕ) : iteratedDerivWithin i (fun r => U r x) (Icc 0 T) t =
      terminalCutoffVector ψ Λ (g i t) x :=
    slabTimeJet_realVectorFourierCutoff hT hV g hg ψ i ht x
  rw [hUJet j, hUJet (q - j), ← nsmul_sub]
  rfl

private theorem truncatedEulerProjectedResidual_eq_cutoffStress (ψ : Vec3 → ℝ) (Λ : ℝ)
    (g r : C(Labels, Vec3)) :
    truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ g r =
      periodicLerayHolderLift
        (terminalCutoffVector ψ Λ r + momentumTensorDivergence ∘ fderiv ℝ (terminalCutoffStress ψ Λ g g)) := by
  unfold truncatedEulerProjectedResidual truncatedParentProjectedResidual
  refine congrArg (fun E : Vec3 → MomentumTensor => periodicLerayHolderLift
    (terminalCutoffVector ψ Λ r + momentumTensorDivergence ∘ fderiv ℝ E)) ?_
  funext x
  simp only [terminalCutoffStress, terminalCutoffVector, cutoffMomentumTensor, momentumTensorFourierCutoff,
    Pi.add_apply, Pi.sub_apply, map_sub, sub_apply, ContinuousMap.coe_mk]
  abel

/-- The time jet of the selected residual is the Leray projection of the
cutoff input residual and the exact differentiated quadratic stress. -/
theorem TruncatedChildStage.slabTimeJet_residual_eq {T Λ : ℝ} {ψ : Vec3 → ℝ} {V RV : Velocity}
    (s : TruncatedChildStage T Λ ψ V RV) (hT : 0 < T)
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Slab(T)))
    (hRV : ContDiffOn ℝ ∞ (Function.uncurry RV) (Slab(T)))
    (g gR : ℕ → ℝ → C(Labels, Vec3))
    (hg : ∀ j t, t ∈ Icc 0 T → ∀ x, g j t (toUnitTorus x) = slabTimeJet 0 T j V t x)
    (hgR : ∀ j t, t ∈ Icc 0 T → ∀ x, gR j t (toUnitTorus x) = slabTimeJet 0 T j RV t x)
    (q : ℕ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    slabTimeJet 0 T q s.residual t = periodicLerayHolderLift
      (terminalCutoffVector ψ Λ (gR q t) +
        momentumTensorDivergence ∘ fderiv ℝ
          (∑ j ∈ Finset.range (q + 1), q.choose j • terminalCutoffStress ψ Λ (g j t) (g (q - j) t))) := by
  let E (r : ℝ) := terminalCutoffStress ψ Λ (g 0 r) (g 0 r)
  let R (r : ℝ) := terminalCutoffVector ψ Λ (gR 0 r)
  let D := momentumTensorDivergence
  let W (r : ℝ) : Vec3 → Vec3 := R r + D ∘ fderiv ℝ (E r)
  have hzero (r : ℝ) (hr : r ∈ Icc 0 T) (x : Vec3) : g 0 r (toUnitTorus x) = V r x := by
    simpa only [slabTimeJet, iteratedDerivWithin_zero] using hg 0 r hr x
  have hRzero (r : ℝ) (hr : r ∈ Icc 0 T) (x : Vec3) : gR 0 r (toUnitTorus x) = RV r x := by
    simpa only [slabTimeJet, iteratedDerivWithin_zero] using hgR 0 r hr x
  have hcoinc (r : ℝ) (hr : r ∈ Icc 0 T) : s.residual r = periodicLerayHolderLift (W r) := by
    have h1 : g 0 r = s.approximateTorus r := by
      ext a
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
      rw [hzero r hr x, s.approximate_rep r hr x]
    have h2 : gR 0 r = s.approximateResidualTorus r := by
      ext a
      obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
      rw [hRzero r hr x, s.approximateResidual_rep r hr x]
    have H := s.residual_cutoff r hr
    change s.residual r = _ at H
    rw [← h1, ← h2, truncatedEulerProjectedResidual_eq_cutoffStress] at H
    exact H
  have hE : ContDiffOn ℝ ∞ (Function.uncurry E) (Slab(T)) := terminalCutoffStress_smooth hT hV (g 0) hzero
  have hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Slab(T)) := cutoff_smooth hT hRV (gR 0) hRzero
  have hD := terminal_contDiffOn_spaceDerivative hT hE
  have hW : ContDiffOn ℝ ∞ (Function.uncurry W) (Slab(T)) :=
    hR.add (D.contDiff.comp_contDiffOn hD)
  have hWper (r : ℝ) (hr : r ∈ Icc 0 T) : SpatiallyPeriodic (W r) := by
    intro n x
    have hz (y : Vec3) : toUnitTorus (y + latticeVector n) = toUnitTorus y :=
      (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩
    have hEper : SpatiallyPeriodic (E r) := fun n x => by
      dsimp only [E, terminalCutoffStress, terminalCutoffVector]
      rw [(toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩]
    have hEx := (hEper.fderiv ((terminal_contDiff_spaceSlice hE hr).differentiable (by simp))) n x
    change R r (x + latticeVector n) + D (fderiv ℝ (E r) (x + latticeVector n)) =
      R r x + D (fderiv ℝ (E r) x)
    rw [hEx]
    simp only [R, terminalCutoffVector, hz]
  have hEJet : slabTimeJet 0 T q E t =
      ∑ j ∈ Finset.range (q + 1), q.choose j • terminalCutoffStress ψ Λ (g j t) (g (q - j) t) :=
    funext fun x => by
      rw [Finset.sum_apply]
      simpa only [Pi.smul_apply] using (slabTimeJet_terminalCutoffStress (ψ := ψ) (Λ := Λ) hT hV g hg q ht x)
  have hJet : slabTimeJet 0 T q W t =
      terminalCutoffVector ψ Λ (gR q t) + D ∘ fderiv ℝ (slabTimeJet 0 T q E t) := by
    funext x
    change iteratedDerivWithin q ((fun r => R r x) +
      fun r => D (fderiv ℝ (E r) x)) (Icc 0 T) t = _
    have hq : (q : ℕ∞ω) ≤ ∞ := by simp
    have hRt := (terminal_contDiffOn_timeSlice hR x).of_le hq t ht
    have hDt := (terminal_contDiffOn_timeSlice (f := fun r y => D (fderiv ℝ (E r) y))
      (D.contDiff.comp_contDiffOn hD) x).of_le hq t ht
    rw [iteratedDerivWithin_add ht (uniqueDiffOn_Icc hT) hRt hDt]
    change slabTimeJet 0 T q R t x + slabTimeJet 0 T q (fun r y => D (fderiv ℝ (E r) y)) t x = _
    have hRjet : slabTimeJet 0 T q R t x = terminalCutoffVector ψ Λ (gR q t) x :=
      slabTimeJet_realVectorFourierCutoff hT hRV gR hgR ψ q ht x
    rw [hRjet, slabTimeJet_comp_clm hT D (V := fun r y => fderiv ℝ (E r) y) hD ht x q,
      terminal_iteratedDerivWithin_fderiv_comm hT hE q ht x]
    rfl
  funext x
  have h := iteratedDerivWithin_congr (g := fun r => periodicLerayHolderLift (W r) x)
    (fun r hr => congrFun (hcoinc r hr) x) ht (n := q)
  exact h.trans ((slabTimeJet_periodicLerayHolderLift hT hW hWper q ht x).trans
    (congrFun (congrArg periodicLerayHolderLift (hJet.trans (by rw [hEJet]))) x))

end

end TorusEuler

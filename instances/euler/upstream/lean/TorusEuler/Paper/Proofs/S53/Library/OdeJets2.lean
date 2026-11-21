import TorusEuler.Paper.Proofs.S53.Library.OdeJets

/-!
# S53 library: membership of the solution jets and the differentiated equation
-/

open Set
open scoped ContDiff


namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

variable {Idx P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace OdeData

variable (D : OdeData Idx P E)

/-- The right-hand side word at the fixed point. -/
def Rw (w : List Idx) (t : ℝ) : E :=
  phaseOperatorWord (fun i _ => D.d i) w (fun y => D.A t y (D.x t y) + D.f t y) D.p

/-- Auxiliary fact `hasDeriv_xj` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem hasDeriv_xj {n : ℕ} {w : List Idx} (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc D.l D.r) :
    HasDerivWithinAt (D.xj n w) (D.Rw w t) (Icc D.l D.r) t := by
  have h := (phaseOperatorWord_linearODE_time_Icc D.d w D.hlr D.hA D.hf D.hx D.hxt).2 D.p t ht
  exact h.congr (fun s hs => D.xj_of_mem hw hs) (D.xj_of_mem hw ht)

/-- Auxiliary fact `continuousOn_Rw` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem continuousOn_Rw (w : List Idx) : ContinuousOn (D.Rw w) (Icc D.l D.r) := by
  have h := (phaseOperatorWord_linearODE_time_Icc D.d w D.hlr D.hA D.hf D.hx D.hxt).1
  exact h.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun t ht => ⟨ht, mem_univ D.p⟩)

/-- Auxiliary fact `derivWithin_xj` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem derivWithin_xj {n : ℕ} {w : List Idx} (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc D.l D.r) :
    derivWithin (D.xj n w) (Icc D.l D.r) t = D.Rw w t :=
  (D.hasDeriv_xj hw ht).derivWithin (uniqueDiffOn_Icc D.hlr t ht)

/-- Auxiliary fact `xj_big` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem xj_big {n : ℕ} {w : List Idx} (hw : ¬ w.length ≤ n) : D.xj n w = fun _ => 0 := by
  funext t; simp [xj, hw]

/-- The solution jets as an element of the space of solutions. -/
def xE (n : ℕ) : Esub Idx E D.slab :=
  ⟨D.xj n, D.xj_symm n, fun w => by
    by_cases hw : w.length ≤ n
    · refine ⟨fun t ht => (D.hasDeriv_xj hw ht).differentiableWithinAt, ?_⟩
      exact (D.continuousOn_Rw w).congr fun t ht => D.derivWithin_xj hw ht
    · rw [xj_big D hw]
      refine ⟨differentiableOn_const _, ?_⟩
      have : derivWithin (fun _ : ℝ => (0 : E)) (Icc D.l D.r) = fun _ => 0 := by
        funext t; simp
      change ContinuousOn (derivWithin (fun _ : ℝ => (0 : E)) (Icc D.slab.l D.slab.r)) _
      rw [show D.slab.l = D.l from rfl, show D.slab.r = D.r from rfl, this]
      exact continuousOn_const⟩

/-- The coefficient jets as an element of the space of coefficients. -/
def aE (n : ℕ) {C : ℝ}
    (hC : ∀ w : List Idx, w.length ≤ n → w ≠ [] → ∀ t ∈ Icc D.l D.r,
      ‖phaseOperatorWord (fun i _ => D.d i) w (D.A t) D.p‖ ≤ C) : Asub Idx E D.slab :=
  ⟨D.aj n, D.aj_symm n, fun w => by
    by_cases hw : w.length ≤ n
    · by_cases hw0 : w = []
      · subst hw0
        have hc : ContinuousOn (fun t => D.A t D.p) (Icc D.l D.r) :=
          D.hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
            (fun t ht => ⟨ht, mem_univ D.p⟩)
        obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
        refine ⟨M, fun t ht => ?_⟩
        rw [D.aj_of_mem hw ht]
        exact hM t ht
      · exact ⟨C, fun t ht => by rw [D.aj_of_mem hw ht]; exact hC w hw hw0 t ht⟩
    · refine ⟨0, fun t ht => ?_⟩
      simp [aj, hw]⟩

/-- The differentiated equation: `L x̃` consists of the jets of the forcing. -/
theorem equation_fst {n : ℕ} {C : ℝ}
    (hC : ∀ w : List Idx, w.length ≤ n → w ≠ [] → ∀ t ∈ Icc D.l D.r,
      ‖phaseOperatorWord (fun i _ => D.d i) w (D.A t) D.p‖ ≤ C)
    {w : List Idx} (hw : w.length ≤ n) {t : ℝ} (ht : t ∈ Icc D.l D.r) :
    (L0 D.slab (D.xE n) + Tmap D.slab (D.aE n hC) (D.xE n)).1.1 w t =
      phaseOperatorWord (fun i _ => D.d i) w (D.f t) D.p := by
  have h1 : (L0 D.slab (D.xE n) + Tmap D.slab (D.aE n hC) (D.xE n)).1.1 w t =
      derivWithin (D.xj n w) (Icc D.l D.r) t -
        lsum w (fun v₁ v₂ => D.aj n v₁ t (D.xj n v₂ t)) := by
    rw [sub_eq_add_neg]
    exact congrArg₂ (· + ·) (L0_fst D.slab (D.xE n) w ht) rfl
  rw [h1, D.derivWithin_xj hw ht]
  have hAu := contDiff_slabSlice D.hA ht
  have hxu := contDiff_slabSlice D.hx ht
  have hfu := contDiff_slabSlice D.hf ht
  have hprod : ContDiff ℝ ∞ (fun q : P => D.A t q (D.x t q)) := hAu.clm_apply hxu
  let eval : (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E := (ContinuousLinearMap.apply ℝ E).flip
  have hb := phaseOperatorWord_bilinear eval (D := fun i (_ : P) => D.d i)
    (fun _ => contDiff_const) hAu hxu w D.p
  unfold Rw
  rw [phaseOperatorWord_add D.d hprod hfu]
  change phaseOperatorWord (fun i _ => D.d i) w (fun q => D.A t q (D.x t q)) D.p + _ - _ = _
  have hb' : phaseOperatorWord (fun i _ => D.d i) w (fun q => D.A t q (D.x t q)) D.p =
      lsum w (fun v₁ v₂ => D.aj n v₁ t (D.xj n v₂ t)) := by
    refine hb.trans ?_
    rw [lsum_eq_splits]
    congr 1
    refine List.map_congr_left fun q hq => ?_
    obtain ⟨_, _, hlen⟩ := hierarchyLeibnizSplits_spec hq
    rw [D.aj_of_mem (by omega) ht, D.xj_of_mem (by omega) ht]
    rfl
  rw [hb']
  abel

end OdeData

end

end TorusEuler.Paper.Lib.S53

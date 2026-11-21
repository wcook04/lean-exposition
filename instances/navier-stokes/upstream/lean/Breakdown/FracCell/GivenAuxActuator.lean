import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxActuatorSmooth
import Breakdown.FracCell.GivenAuxActuatorClass

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

private theorem getD_ge_of_all (tb : ℝ) (L : List ℝ) (hL : ∀ x ∈ L, tb ≤ x) (h1 : tb ≤ 1) (k : ℕ) :
    tb ≤ L.getD k 1 := by
  rw [List.getD_eq_getElem?_getD]
  cases h : L[k]? with
  | none => simpa using h1
  | some v => simpa using hL v (List.mem_of_getElem? h)

private theorem break_le_cell (l : List ℝ) (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0)
    (h1 : l.getLast? = some 1) (tb u : ℝ) (hmem : tb ∈ l) (hpos : 0 < tb) (hlt : tb < 1) (hu : tb ≤ u) :
    tb ≤ l.getD (cellIndex l u) 1 := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem hmem
  cases A with
  | nil =>
    simp at h0
    linarith
  | cons a A' =>
    have ha : a = 0 := by simpa using h0
    subst ha
    obtain ⟨B', rfl⟩ : ∃ B', B = B' ++ [1] := by
      cases B using List.reverseRecOn with
      | nil =>
        rw [show (0 :: A' ++ [tb]) = (0 :: A') ++ [tb] by simp, List.getLast?_concat] at h1
        have : tb = 1 := Option.some.inj h1
        linarith
      | append_singleton B' b _ =>
        have hb : b = 1 := by
          have := h1
          rw [show (0 :: A' ++ tb :: (B' ++ [b])) = (0 :: A' ++ tb :: B') ++ [b] by simp,
            List.getLast?_concat] at this
          exact Option.some.inj this
        exact ⟨B', by rw [hb]⟩
    have hI : ((0 :: A' ++ tb :: (B' ++ [1])).drop 1).dropLast = A' ++ tb :: B' := by
      rw [show (0 :: A' ++ tb :: (B' ++ [1])).drop 1 = (A' ++ tb :: B') ++ [1] by simp]
      exact List.dropLast_concat
    rw [List.pairwise_append] at hs
    obtain ⟨_, hsB, hAB⟩ := hs
    have hAl : ∀ x ∈ A', x < tb := fun x hx => hAB x (by simp [hx]) tb (by simp)
    unfold cellIndex
    rw [hI]
    have hc : (0 :: A').length ≤ ((A' ++ tb :: B').filter (fun b => decide (b ≤ u))).length := by
      have hA : A'.filter (fun b => decide (b ≤ u)) = A' :=
        List.filter_eq_self.2 (fun b hb => by simpa using le_trans (hAl b hb).le hu)
      rw [List.filter_append, List.length_append, hA, List.filter_cons]
      simp [hu]
    rw [List.getD_append_right _ _ _ _ hc]
    apply getD_ge_of_all tb _ _ hlt.le
    intro x hx
    rcases List.mem_cons.1 hx with h | h
    · exact h.ge
    · exact (List.pairwise_cons.1 hsB).1 x h |>.le

private theorem eval_vanish (S : Spline) (hm : IsTensorMesh S.mesh) (tb : ℝ) (hv : S.VanishesFrom tb)
    (hb : tb ∈ S.mesh.tBreaks) (hpos : 0 < tb) (hlt : tb < 1) (odd : Bool) (s x : ℝ) (hs : tb ≤ s) :
    S.eval odd s x = 0 := by
  unfold Spline.eval Spline.evalHalf
  rw [hv _ _ (break_le_cell _ hm.t_sorted hm.t_first hm.t_last tb s hb hpos hlt hs)]
  simp

private theorem deriv_vanish (g : ℝ → ℂ) (tb t : ℝ) (h : ∀ s, tb ≤ s → g s = 0) (ht : tb ≤ t) :
    deriv g t = 0 := by
  by_cases hd : DifferentiableAt ℝ g t
  · have h1 : HasDerivWithinAt g (deriv g t) (Set.Ici t) t := hd.hasDerivAt.hasDerivWithinAt
    have h2 : HasDerivWithinAt g 0 (Set.Ici t) t :=
      (hasDerivWithinAt_const t (Set.Ici t) (0 : ℂ)).congr (fun s hs => h s (le_trans ht hs)) (h t ht)
    exact UniqueDiffWithinAt.eq_deriv _ (uniqueDiffWithinAt_Ici t) h1 h2
  · exact deriv_zero_of_not_differentiableAt hd

private theorem twisted_vanish (P : ChartParams) (n : ℤ) (β : ℝ) (f : ℝ → ℝ → ℂ) (tb t x : ℝ)
    (hf : ∀ s, tb ≤ s → ∀ x', f s x' = 0) (ht : tb ≤ t) : twistedScale P n β f t x = 0 := by
  unfold twistedScale radialScale
  rw [deriv_vanish (fun t' => f t' x) tb t (fun s hs => hf s hs x) ht, hf t ht x]
  simp

private theorem height_vanish (f : ℝ → ℝ → ℂ) (tb t x : ℝ)
    (hf : ∀ s, tb ≤ s → ∀ x', f s x' = 0) (ht : tb ≤ t) : heightDeriv f t x = 0 := by
  unfold heightDeriv
  have : (fun x' => f t x') = fun _ => 0 := funext (hf t ht)
  rw [this]
  simp

private theorem reducedField_vanish_zero (P : ChartParams) (D : FieldData) (β tb t x : ℝ) (ht : tb ≤ t)
    (hs : ∀ s x', tb ≤ s → (D.amp 0).streamAmp.eval true s x' = 0)
    (hw : ∀ s x', tb ≤ s → (D.amp 0).swirlAmp.eval false s x' = 0) (c : Fin 3) :
    reducedField P D 0 β t x c = 0 := by
  have h1 := height_vanish (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') tb t x
    (fun s hs' x' => by simp [hs s x' hs']) ht
  have h2 := twisted_vanish P 0 β (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x')
    tb t x (fun s hs' x' => by simp [hs s x' hs']) ht
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at h1 h2
  unfold reducedField
  fin_cases c <;> simp [h1, h2, hs t x ht, hw t x ht]

private theorem reducedField_vanish_ne (P : ChartParams) (D : FieldData) (n : ℤ) (hn : n ≠ 0) (β tb t x : ℝ)
    (ht : tb ≤ t)
    (hr : ∀ s x', tb ≤ s → (D.amp n).radialAmp.eval false s x' = 0)
    (hp : ∀ s x', tb ≤ s → (D.amp n).polarAmp.eval true s x' = 0) (c : Fin 3) :
    reducedField P D n β t x c = 0 := by
  have h1 := height_vanish (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) *
      (weightPoly (D.lowOrder n) D.highOrder t' * ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n *
        (D.amp n).polarAmp.eval true t' x')) tb t x
    (fun s hs' x' => by simp [hp s x' hs']) ht
  have h2 := twisted_vanish P n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
      ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x')
    tb t x (fun s hs' x' => by simp [hr s x' hs']) ht
  simp only [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] at h1 h2
  unfold reducedField
  fin_cases c <;> simp [hn, h1, h2, hr t x ht, hp t x ht]

private theorem fieldOf_vanish (P : ChartParams) (D : FieldData) (β : ℝ) (y : Space)
    (hall : ∀ n ∈ D.modes, ∀ c, reducedField P D n β (chartT P y) (heightRatio y) c = 0) :
    fieldOf P D β y = 0 := by
  unfold fieldOf ofComponents
  simp +contextual [hall]
  ext j
  simp

theorem fieldOf_eq_zero_of_compact (P : ChartParams) {e : ℕ} {tb : ℝ} {D : FieldData}
    (hc : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) (y : Space) (ht : tb ≤ chartT P y) :
    fieldOf P D β y = 0 := by
  apply fieldOf_vanish
  intro n hn c
  obtain ⟨hvr, hvp, hvs, hvw⟩ := hc.vanish n hn
  obtain ⟨hbr, hbp, hbs, hbw⟩ := hc.tb_break n hn
  by_cases h0 : n = 0
  · subst h0
    exact reducedField_vanish_zero P D β tb _ _ ht
      (fun s x' hs => eval_vanish _ (hc.field.meanStream hn).1.mesh tb hvs hbs hpos hc.tb_lt _ s x' hs)
      (fun s x' hs => eval_vanish _ (hc.field.meanSwirl hn).1.mesh tb hvw hbw hpos hc.tb_lt _ s x' hs) c
  · exact reducedField_vanish_ne P D n h0 β tb _ _ ht
      (fun s x' hs => eval_vanish _ (hc.field.waveRadial n hn h0).mesh tb hvr hbr hpos hc.tb_lt _ s x' hs)
      (fun s x' hs => eval_vanish _ (hc.field.wavePolar n hn h0).mesh tb hvp hbp hpos hc.tb_lt _ s x' hs) c

theorem actuatorSupport_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (region : Set Space) (hreg : ∀ y, chartT P y < A.supportBreak → y ∈ region) (i : Fin k) :
    ∀ y ∉ region, A.actuatorField P i y = 0 := by
  intro y hy
  have ht : A.supportBreak ≤ chartT P y := not_lt.1 (fun h => hy (hreg y h))
  obtain ⟨e, hc⟩ := hA.actuator_shape i
  exact fieldOf_eq_zero_of_compact P hc hA.break_pos _ y ht

private theorem norm_le_of_chart_lt (P : ChartParams) (hP : IsChartParams P) (tb : ℝ) (htb : tb < 1)
    (y : Space) (hy : chartT P y < tb) : ‖y‖ ≤ P.L0 * tb / (1 - tb) := by
  have hL := hP.L0_pos
  have hn : 0 ≤ ‖y‖ := norm_nonneg y
  unfold chartT at hy
  rw [div_lt_iff₀ (by linarith)] at hy
  rw [le_div_iff₀ (by linarith)]
  nlinarith

theorem supportRegion_of (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (region : Set Space) (R : ℝ) (hball : ∀ y : Space, ‖y‖ ≤ R → y ∈ region)
    (hnum : P.L0 * A.supportBreak / (1 - A.supportBreak) ≤ R) :
    ∀ y, chartT P y < A.supportBreak → y ∈ region :=
  fun y hy => hball y (le_trans (norm_le_of_chart_lt P hP _ hA.break_lt y hy) hnum)

theorem fieldOf_hasCompactSupport_of_compact (P : ChartParams) (hP : IsChartParams P) {e : ℕ} {tb : ℝ}
    {D : FieldData} (hc : IsCompactFieldData P e tb D) (hpos : 0 < tb) (β : ℝ) :
    HasCompactSupport (fieldOf P D β) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : Space) (P.L0 * tb / (1 - tb))) (fun y hy =>
    fieldOf_eq_zero_of_compact P hc hpos β y (not_lt.1 (fun h => hy (by
      rw [mem_closedBall_zero_iff]
      exact norm_le_of_chart_lt P hP tb hc.tb_lt y h))))

private theorem weakGradient_of_contDiff_one {v : Space → Space} (hv : ContDiff ℝ 1 v) :
    IsWeakGradientOf v (fun y => fderiv ℝ v y) := by
  intro φ hφ j
  have hφd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hvd : Differentiable ℝ v := hv.differentiable one_ne_zero
  have hφ' : Continuous fun y => fderiv ℝ φ y (unitVector j) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hv' : Continuous fun y => fderiv ℝ v y (unitVector j) :=
    (hv.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hi1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • v y) :=
    (hφ'.smul hv.continuous).integrable_of_hasCompactSupport
      ((hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)).smul_right)
  have hi2 : Integrable (fun y => φ y • fderiv ℝ v y (unitVector j)) :=
    (hφ.1.continuous.smul hv').integrable_of_hasCompactSupport hφ.2.smul_right
  have hi3 : Integrable (fun y => φ y • v y) :=
    (hφ.1.continuous.smul hv.continuous).integrable_of_hasCompactSupport hφ.2.smul_right
  rw [integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable hi1 hi2 hi3 (fun y _ => hφd y) (fun y _ => hvd y),
    neg_neg]

theorem actuator_of_given (P : ChartParams) (hP : IsChartParams P) {k N : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (d : FracCertData k N) (hm : d.order = P.m) (hact : ∀ i, d.actuator i = A.actuatorField P i) :
    (∀ i, MemLp (d.actuator i) 2 volume) ∧ (∀ i, IsClassField d.order (d.actuator i)) := by
  refine ⟨fun i => ?_, fun i => ?_⟩
  · obtain ⟨e, hc⟩ := hA.actuator_shape i
    rw [hact i]
    exact (fieldOf_contDiff_of_compact P hP hc hA.break_pos _).continuous.memLp_of_hasCompactSupport
      (fieldOf_hasCompactSupport_of_compact P hP hc hA.break_pos _)
  · obtain ⟨e, hc⟩ := hA.actuator_shape i
    rw [hact i, hm]
    exact fieldOf_class P hP _ _

theorem actuatorGradient_of_given (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A) (i : Fin k) :
    IsWeakGradientOf (A.actuatorField P i) (fun y => fderiv ℝ (A.actuatorField P i) y) ∧
      AEStronglyMeasurable (fun y => fderiv ℝ (A.actuatorField P i) y) volume ∧
      Integrable (fun y => entrySq (fderiv ℝ (A.actuatorField P i) y)) := by
  obtain ⟨e, hc⟩ := hA.actuator_shape i
  have hv : ContDiff ℝ 1 (A.actuatorField P i) := fieldOf_contDiff_of_compact P hP hc hA.break_pos _
  have hs : HasCompactSupport (A.actuatorField P i) :=
    fieldOf_hasCompactSupport_of_compact P hP hc hA.break_pos _
  have hD : Continuous (fun y => fderiv ℝ (A.actuatorField P i) y) := hv.continuous_fderiv one_ne_zero
  refine ⟨weakGradient_of_contDiff_one hv, hD.aestronglyMeasurable, ?_⟩
  have hE : Continuous (fun y => entrySq (fderiv ℝ (A.actuatorField P i) y)) := by
    unfold entrySq
    exact continuous_finsetSum _ (fun j _ => ((hD.clm_apply continuous_const).norm).pow 2)
  have hsE : HasCompactSupport (fun y => entrySq (fderiv ℝ (A.actuatorField P i) y)) :=
    (hs.fderiv (𝕜 := ℝ)).comp_left (g := entrySq) (by simp [entrySq])
  exact hE.integrable_of_hasCompactSupport hsE

end GivenFields

end CellCert

end Breakdown

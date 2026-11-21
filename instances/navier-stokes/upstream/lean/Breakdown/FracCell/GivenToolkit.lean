import Breakdown.FracCell.GivenChartDefs
import Mathlib.Analysis.Calculus.Rademacher

open scoped ContDiff
open MeasureTheory

noncomputable section

namespace Breakdown

namespace FracInternal

open CellCert.GivenFields SteadyCert

theorem givenTurn_add (m : ℕ) (a b : Space) : turnStep m (a + b) = turnStep m a + turnStep m b := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem givenTurn_smul (m : ℕ) (c : ℝ) (a : Space) : turnStep m (c • a) = c • turnStep m a := by
  ext i
  fin_cases i <;> simp [turnStep] <;> ring

theorem givenMirror_add (a b : Space) : mirror (a + b) = mirror a + mirror b := by
  ext i
  fin_cases i <;> simp [mirror] <;> ring

theorem givenMirror_smul (c : ℝ) (a : Space) : mirror (c • a) = c • mirror a := by
  ext i
  fin_cases i <;> simp [mirror]

def givenTurnLinear (m : ℕ) : Space →ₗ[ℝ] Space where
  toFun := turnStep m
  map_add' := givenTurn_add m
  map_smul' := givenTurn_smul m

def givenMirrorLinear : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' := givenMirror_add
  map_smul' := givenMirror_smul

theorem classField_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (m : ℕ) (f : ι → Space → Space)
    (hf : ∀ i ∈ s, IsClassField m (f i)) : IsClassField m (fun z => ∑ i ∈ s, c i • f i z) := by
  constructor
  · have h : ∀ᵐ y ∂(volume : Measure Space), ∀ i ∈ s, f i (turnStep m y) = turnStep m (f i y) :=
      (Filter.eventually_all_finset s).2 fun i hi => (hf i hi).1
    filter_upwards [h] with y hy
    have e := map_sum (givenTurnLinear m) (fun i => c i • f i y) s
    simp only [givenTurnLinear, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hy i hi, givenTurn_smul]
  · have h : ∀ᵐ y ∂(volume : Measure Space), ∀ i ∈ s, f i (mirror y) = mirror (f i y) :=
      (Filter.eventually_all_finset s).2 fun i hi => (hf i hi).2
    filter_upwards [h] with y hy
    have e := map_sum givenMirrorLinear (fun i => c i • f i y) s
    simp only [givenMirrorLinear, LinearMap.coe_mk, AddHom.coe_mk] at e
    rw [e]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [hy i hi, givenMirror_smul]

theorem fderiv_finset_sum_smul {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Space → Space)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) :
    fderiv ℝ (fun z => ∑ i ∈ s, c i • f i z) = fun y => ∑ i ∈ s, c i • fderiv ℝ (f i) y := by
  funext y
  have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun z => c i • f i z) y := fun i hi => ((hf i hi) y).const_smul (c i)
  rw [fderiv_fun_sum hd]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact fderiv_fun_const_smul ((hf i hi) y) (c i)

theorem divergenceAt_finset_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (f : ι → Space → Space)
    (hf : ∀ i ∈ s, Differentiable ℝ (f i)) (y : Space) :
    divergenceAt (fun z => ∑ i ∈ s, c i • f i z) y = ∑ i ∈ s, c i * divergenceAt (f i) y := by
  unfold divergenceAt
  rw [fderiv_finset_sum_smul s c f hf]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Finset.sum_apply, WithLp.ofLp_sum]

theorem slopeOn_finset_sum {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (s : Finset ι) (c : ι → ℝ) (G : ι → Space → E)
    (hG : ∀ i ∈ s, ∀ R : ℝ, ∃ C : NNReal, LipschitzOnWith C (G i) (Metric.closedBall 0 R)) :
    ∀ R : ℝ, ∃ C : NNReal, LipschitzOnWith C (fun z => ∑ i ∈ s, c i • G i z) (Metric.closedBall 0 R) := by
  classical
  intro R
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using (LipschitzWith.const (0 : E)).lipschitzOnWith⟩
  | insert a s ha ih =>
    obtain ⟨C1, h1⟩ := ih fun i hi => hG i (Finset.mem_insert_of_mem hi)
    obtain ⟨C2, h2⟩ := hG a (Finset.mem_insert_self a s) R
    refine ⟨‖c a‖₊ * C2 + C1, ?_⟩
    simp only [Finset.sum_insert ha]
    exact ((lipschitzWith_smul (c a)).comp_lipschitzOnWith h2).add h1

theorem weakSecond_of_slopeOn {G : Space → (Space →L[ℝ] Space)}
    (hG : ∀ R : ℝ, ∃ C : NNReal, LipschitzOnWith C G (Metric.closedBall 0 R)) :
    IsWeakSecondDerivOf G (fderiv ℝ G) ∧ AEStronglyMeasurable (fderiv ℝ G) volume := by
  have hmeas : Measurable (fderiv ℝ G) := measurable_fderiv ℝ G
  refine ⟨?_, hmeas.aestronglyMeasurable⟩
  have hGc : Continuous G := by
    refine continuous_iff_continuousAt.2 fun y => ?_
    obtain ⟨C, hC⟩ := hG (‖y‖ + 1)
    refine hC.continuousOn.continuousAt (Metric.closedBall_mem_nhds_of_mem ?_)
    rw [mem_ball_zero_iff]
    linarith
  intro φ hφ i j
  obtain ⟨hφs, hφc⟩ := hφ
  obtain ⟨R, hR⟩ := hφc.isCompact.isBounded.subset_ball (0 : Space)
  obtain ⟨C, hC⟩ := hG R
  have hCb : LipschitzOnWith C G (Metric.ball 0 R) := hC.mono Metric.ball_subset_closedBall
  have hφd : Differentiable ℝ φ := hφs.differentiable (by simp)
  have hφz : ∀ y, y ∉ Metric.ball (0 : Space) R → φ y = 0 := fun y hy =>
    image_eq_zero_of_notMem_tsupport fun h => hy (hR h)
  have hφdz : ∀ y, y ∉ Metric.ball (0 : Space) R → fderiv ℝ φ y = 0 := fun y hy => by
    by_contra h
    exact hy (hR (support_fderiv_subset ℝ h))
  obtain ⟨Kφ, hφL⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hφc hφs (by simp)
  have hdiff : ∀ᵐ y ∂(volume : Measure Space), y ∈ Metric.ball (0 : Space) R → DifferentiableAt ℝ G y := by
    filter_upwards [hCb.ae_differentiableWithinAt_of_mem (μ := volume)] with y hy hyb
    exact (hy hyb).differentiableAt (Metric.isOpen_ball.mem_nhds hyb)
  have hunit : ∀ l : Fin 3, ‖unitVector l‖ = 1 := fun l => by simp [unitVector]
  have comp : ∀ k : Fin 3, ∫ y, fderiv ℝ φ y (unitVector j) * (G y (unitVector i)) k =
      -∫ y, φ y * (fderiv ℝ G y (unitVector j) (unitVector i)) k := by
    intro k
    set L : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
      (EuclideanSpace.proj k : Space →L[ℝ] ℝ).comp (ContinuousLinearMap.apply ℝ Space (unitVector i)) with hL
    have hSspp : ∀ A : Space →L[ℝ] Space, L A = (A (unitVector i)) k := fun A => rfl
    have hgL : LipschitzOnWith (‖L‖₊ * C) (fun y => L (G y)) (Metric.closedBall 0 R) :=
      L.lipschitz.comp_lipschitzOnWith hC
    obtain ⟨g, hgSlope, hgEq⟩ := hgL.extend_real
    have key := LipschitzWith.integral_lineDeriv_mul_eq (μ := (volume : Measure Space)) hgSlope hφL hφc (unitVector j)
    have h1 : (fun y => lineDeriv ℝ g y (unitVector j) * φ y) =ᵐ[volume]
        fun y => φ y * (fderiv ℝ G y (unitVector j) (unitVector i)) k := by
      filter_upwards [hdiff] with y hy
      by_cases hyb : y ∈ Metric.ball (0 : Space) R
      · have hGd := hy hyb
        have hev : (fun z => L (G z)) =ᶠ[nhds y] g := by
          filter_upwards [Metric.isOpen_ball.mem_nhds hyb] with z hz
          exact hgEq (Metric.ball_subset_closedBall hz)
        have hF : HasFDerivAt (fun z => L (G z)) (L.comp (fderiv ℝ G y)) y :=
          L.hasFDerivAt.comp y hGd.hasFDerivAt
        have hFg : HasFDerivAt g (L.comp (fderiv ℝ G y)) y := hF.congr_of_eventuallyEq hev.symm
        rw [hFg.differentiableAt.lineDeriv_eq_fderiv, hFg.fderiv]
        simp only [ContinuousLinearMap.coe_comp', Function.comp_apply, hSspp]
        ring
      · simp [hφz y hyb]
    have h2 : ∀ y, lineDeriv ℝ φ y (-unitVector j) * g y = -(fderiv ℝ φ y (unitVector j) * (G y (unitVector i)) k) := by
      intro y
      rw [(hφd y).lineDeriv_eq_fderiv, map_neg]
      by_cases hyb : y ∈ Metric.ball (0 : Space) R
      · rw [← hgEq (Metric.ball_subset_closedBall hyb)]
        show -(fderiv ℝ φ y) (unitVector j) * L (G y) = _
        rw [hSspp]
        ring
      · simp [hφdz y hyb]
    rw [integral_congr_ae h1] at key
    simp only [h2, integral_neg] at key
    rw [key, neg_neg]
  have I1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y (unitVector i)) volume := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact ((hφs.continuous_fderiv (by simp)).clm_apply continuous_const).smul
        (hGc.clm_apply continuous_const)
    · refine hφc.mono' fun y hy => ?_
      by_contra h
      have h0 : fderiv ℝ φ y = 0 := by
        by_contra h1
        exact h (support_fderiv_subset ℝ h1)
      exact hy (by simp [h0])
  have I2 : Integrable (fun y => φ y • fderiv ℝ G y (unitVector j) (unitVector i)) volume := by
    have hφi : Integrable φ volume := hφs.continuous.integrable_of_hasCompactSupport hφc
    refine Integrable.mono' (hφi.norm.const_mul C) ?_ (Filter.Eventually.of_forall fun y => ?_)
    · exact hφs.continuous.aestronglyMeasurable.smul
        (((ContinuousLinearMap.apply ℝ Space (unitVector i)).measurable.comp
          ((ContinuousLinearMap.apply ℝ (Space →L[ℝ] Space) (unitVector j)).measurable.comp hmeas)).aestronglyMeasurable)
    · by_cases hyb : y ∈ Metric.ball (0 : Space) R
      · have hn : ‖fderiv ℝ G y‖ ≤ C := norm_fderiv_le_of_lipschitzOn ℝ (Metric.isOpen_ball.mem_nhds hyb) hCb
        have h3 : ‖fderiv ℝ G y (unitVector j) (unitVector i)‖ ≤ C := by
          calc ‖fderiv ℝ G y (unitVector j) (unitVector i)‖ ≤ ‖fderiv ℝ G y (unitVector j)‖ * ‖unitVector i‖ :=
                (fderiv ℝ G y (unitVector j)).le_opNorm _
            _ ≤ ‖fderiv ℝ G y‖ * ‖unitVector j‖ * ‖unitVector i‖ := by
                gcongr
                exact (fderiv ℝ G y).le_opNorm _
            _ ≤ C := by rw [hunit, hunit]; simpa using hn
        rw [norm_smul]
        calc ‖φ y‖ * ‖fderiv ℝ G y (unitVector j) (unitVector i)‖ ≤ ‖φ y‖ * C := by gcongr
          _ = C * ‖φ y‖ := by ring
      · simp [hφz y hyb]
  ext k
  have e1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm I1
  have e2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm I2
  have hp : ∀ v : Space, (EuclideanSpace.proj k : Space →L[ℝ] ℝ) v = v k := fun v => rfl
  simp only [hp, PiLp.smul_apply, smul_eq_mul] at e1 e2
  rw [PiLp.neg_apply, ← e1, ← e2]
  exact comp k

theorem spline_eval_neg (S : Spline) (odd : Bool) (t x : ℝ) (hx : x ≠ 0) :
    S.eval odd t (-x) = (if odd then -1 else 1) * S.eval odd t x := by
  unfold Spline.eval
  rw [abs_neg]
  rcases lt_or_gt_of_ne hx with h | h
  · have h' : ¬ (-x < 0) := by linarith
    cases odd <;> simp [h, h']
  · have h' : -x < 0 := by linarith
    have h'' : ¬ x < 0 := by linarith
    cases odd <;> simp [h', h'']

theorem heightDeriv_parity {f : ℝ → ℝ → ℂ} {σ : ℂ} (t : ℝ)
    (hf : ∀ x, x ≠ 0 → f t (-x) = σ * f t x) {x : ℝ} (hx : x ≠ 0) :
    heightDeriv f t (-x) = -σ * heightDeriv f t x := by
  unfold heightDeriv
  have hev : (fun x' => f t x') =ᶠ[nhds (-x)] fun x' => σ * f t (-x') := by
    filter_upwards [eventually_ne_nhds (neg_ne_zero.2 hx)] with x' hx'
    have := hf (-x') (neg_ne_zero.2 hx')
    rwa [neg_neg] at this
  rw [hev.deriv_eq, deriv_const_mul_field']
  beta_reduce
  rw [deriv_comp_neg (f := f t), neg_neg]
  ring

theorem radialScale_parity {f : ℝ → ℝ → ℂ} {σ : ℂ} {x : ℝ} (hf : ∀ t', f t' (-x) = σ * f t' x) (t : ℝ) :
    radialScale f t (-x) = σ * radialScale f t x := by
  unfold radialScale
  rw [show (fun t' => f t' (-x)) = fun t' => σ * f t' x from funext hf, deriv_const_mul_field']
  beta_reduce
  ring

theorem twistedScale_parity (P : CellCert.GivenFields.ChartParams) (n : ℤ) (β : ℝ) {f : ℝ → ℝ → ℂ} {σ : ℂ}
    {x : ℝ} (hf : ∀ t', f t' (-x) = σ * f t' x) (t : ℝ) :
    twistedScale P n β f t (-x) = σ * twistedScale P n β f t x := by
  unfold twistedScale
  rw [radialScale_parity hf, hf t]
  ring

theorem reducedField_neg (P : CellCert.GivenFields.ChartParams) (D : CellCert.GivenFields.FieldData)
    (n : ℤ) (β t x : ℝ) (hx : x ≠ 0) :
    reducedField P D n β t (-x) 0 = reducedField P D n β t x 0 ∧
    reducedField P D n β t (-x) 1 = -reducedField P D n β t x 1 ∧
    reducedField P D n β t (-x) 2 = reducedField P D n β t x 2 := by
  unfold reducedField
  split_ifs with hn
  · have hΨ : ∀ t' x', x' ≠ 0 → (D.amp 0).streamAmp.eval true t' (-x') =
        -1 * (D.amp 0).streamAmp.eval true t' x' := fun t' x' h => by
      simpa using spline_eval_neg (D.amp 0).streamAmp true t' x' h
    have hG : ∀ t' x', x' ≠ 0 → (D.amp 0).swirlAmp.eval false t' (-x') =
        (D.amp 0).swirlAmp.eval false t' x' := fun t' x' h => by
      simpa using spline_eval_neg (D.amp 0).swirlAmp false t' x' h
    have h0 : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t (-x) =
        heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (D.amp 0).streamAmp.eval true t' x') t x := by
      rw [heightDeriv_parity (σ := -1) t (fun x' hx' => by rw [hΨ t x' hx', neg_sq]; ring) hx]
      ring
    have h1 : twistedScale P 0 β (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t (-x) =
        -1 * twistedScale P 0 β (fun t' x' => weightPoly 1 D.highOrder t' * (D.amp 0).streamAmp.eval true t' x') t x :=
      twistedScale_parity P 0 β (fun t' => by rw [hΨ t' x hx]; ring) t
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨by rw [h0], ?_, by rw [hG t x hx]⟩
    rw [h1, hΨ t x hx]
    ring
  · have hA : ∀ t' x', x' ≠ 0 → (D.amp n).radialAmp.eval false t' (-x') =
        (D.amp n).radialAmp.eval false t' x' := fun t' x' h => by
      simpa using spline_eval_neg (D.amp n).radialAmp false t' x' h
    have hB : ∀ t' x', x' ≠ 0 → (D.amp n).polarAmp.eval true t' (-x') =
        -1 * (D.amp n).polarAmp.eval true t' x' := fun t' x' h => by
      simpa using spline_eval_neg (D.amp n).polarAmp true t' x' h
    have h1 : twistedScale P n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') t (-x) =
        1 * twistedScale P n β (fun t' x' => weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).radialAmp.eval false t' x') t x :=
      twistedScale_parity P n β (fun t' => by rw [hA t' x hx, neg_sq]; ring) t
    have h2 : heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t (-x) =
        heightDeriv (fun t' x' => ((1 - x' ^ 2 : ℝ) : ℂ) * (weightPoly (D.lowOrder n) D.highOrder t' *
        ((1 - x' ^ 2 : ℝ) : ℂ) ^ D.axisOrder n * (D.amp n).polarAmp.eval true t' x')) t x := by
      rw [heightDeriv_parity (σ := -1) t (fun x' hx' => by rw [hB t x' hx', neg_sq]; ring) hx]
      ring
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons]
    refine ⟨by rw [hA t x hx, neg_sq], by rw [hB t x hx, neg_sq]; ring, ?_⟩
    rw [h1, h2, hA t x hx, neg_sq, one_mul]

theorem ofComponents_apply (w : Fin 3 → ℝ) (k : Fin 3) : (ofComponents w) k = w k := by
  fin_cases k <;> simp [ofComponents]

theorem givenNorm_mirror (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  simp [mirror, Fin.sum_univ_three]

theorem ae_coord_ne_zero (k : Fin 3) : ∀ᵐ y ∂(volume : Measure Space), y k ≠ 0 := by
  have hs : LinearMap.ker (EuclideanSpace.proj k : Space →L[ℝ] ℝ).toLinearMap ≠ ⊤ := by
    intro h
    have : (EuclideanSpace.single k (1 : ℝ) : Space) ∈
        LinearMap.ker (EuclideanSpace.proj k : Space →L[ℝ] ℝ).toLinearMap := by
      rw [h]
      trivial
    simp at this
  have h0 := Measure.addHaar_submodule (volume : Measure Space) _ hs
  rw [ae_iff]
  refine measure_mono_null (fun a ha => ?_) h0
  simp only [ne_eq, Decidable.not_not, Set.mem_setOf_eq] at ha
  simp [LinearMap.mem_ker, ha]

theorem fieldOf_mirror_apply (P : CellCert.GivenFields.ChartParams) (D : CellCert.GivenFields.FieldData)
    (β : ℝ) (y : Space) (hy : y 2 ≠ 0) (k : Fin 3) :
    (fieldOf P D β (mirror y)) k = (if k = 2 then -1 else 1) * (fieldOf P D β y) k := by
  have hn : ‖mirror y‖ = ‖y‖ := givenNorm_mirror y
  have hm0 : (mirror y) 0 = y 0 := by simp [mirror]
  have hm1 : (mirror y) 1 = y 1 := by simp [mirror]
  have hm2 : (mirror y) 2 = -(y 2) := by simp [mirror]
  have hT : chartT P (mirror y) = chartT P y := by simp only [chartT, hn]
  have hdec : decayFactor P (mirror y) = decayFactor P y := by simp only [decayFactor, chartS, hT]
  have hph : ∀ n, modePhase P n β (mirror y) = modePhase P n β y := fun n => by
    simp only [modePhase, angleOf, logPhase, hm0, hm1, hn]
  have hh : heightRatio (mirror y) = -heightRatio y := by
    simp only [heightRatio, hm2, hn]
    ring
  have hq : qOf (mirror y) = qOf y := by simp only [qOf, hh, neg_sq]
  have hx : heightRatio y ≠ 0 := by
    have : ‖y‖ ≠ 0 := by
      intro h
      exact hy (by rw [norm_eq_zero.1 h]; rfl)
    simp only [heightRatio]
    exact div_ne_zero hy this
  have hterm : ∀ n, reducedField P D n β (chartT P y) (-heightRatio y) 0 * (radialVec (mirror y) k : ℂ) +
      reducedField P D n β (chartT P y) (-heightRatio y) 1 * (polarVecQ (mirror y) k : ℂ) +
      reducedField P D n β (chartT P y) (-heightRatio y) 2 * (azimVecQ (mirror y) k : ℂ) =
      ((if k = 2 then -1 else 1 : ℝ) : ℂ) * (reducedField P D n β (chartT P y) (heightRatio y) 0 * (radialVec y k : ℂ) +
      reducedField P D n β (chartT P y) (heightRatio y) 1 * (polarVecQ y k : ℂ) +
      reducedField P D n β (chartT P y) (heightRatio y) 2 * (azimVecQ y k : ℂ)) := by
    intro n
    obtain ⟨h0, h1, h2⟩ := reducedField_neg P D n β (chartT P y) (heightRatio y) hx
    rw [h0, h1, h2]
    fin_cases k <;> simp [radialVec, polarVecQ, azimVecQ, hm0, hm1, hm2, hn, hh, hq] <;> ring
  simp only [fieldOf, ofComponents_apply, hdec, hph, hT, hh]
  rw [Finset.sum_congr rfl (fun n _ => by rw [hterm n])]
  simp only [mul_left_comm _ ((if k = 2 then -1 else 1 : ℝ) : ℂ), ← Finset.mul_sum]
  rw [Complex.re_ofReal_mul]

theorem fieldOf_mirror_ae (P : CellCert.GivenFields.ChartParams) (D : CellCert.GivenFields.FieldData) (β : ℝ) :
    ∀ᵐ y ∂volume, fieldOf P D β (mirror y) = mirror (fieldOf P D β y) := by
  filter_upwards [ae_coord_ne_zero 2] with y hy
  ext k
  rw [fieldOf_mirror_apply P D β y hy k]
  fin_cases k <;> simp [mirror]

theorem givenTurn_coords (m : ℕ) (y : Space) :
    (turnStep m y) 0 = Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 ∧
    (turnStep m y) 1 = Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 ∧
    (turnStep m y) 2 = y 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [turnStep]

theorem givenNorm_turn (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  obtain ⟨h0, h1, h2⟩ := givenTurn_coords m y
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, h0, h1, h2]
  have := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * this

theorem modePhase_turn (P : CellCert.GivenFields.ChartParams) (hm : P.m ≠ 0) (n : ℤ) (β : ℝ) (y : Space)
    (hy : y 0 ≠ 0) : modePhase P n β (turnStep P.m y) = modePhase P n β y := by
  obtain ⟨h0, h1, _⟩ := givenTurn_coords P.m y
  set θ := 2 * Real.pi / P.m with hθ
  have hnorm := givenNorm_turn P.m y
  have hw : (⟨(turnStep P.m y) 0, (turnStep P.m y) 1⟩ : ℂ) =
      ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp [h0, h1, Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im] <;> ring
  have hw0 : (⟨y 0, y 1⟩ : ℂ) ≠ 0 := fun h => hy (by simpa using congrArg Complex.re h)
  have hu0 : ((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    simp [Complex.cos_ofReal_re, Complex.sin_ofReal_re, Complex.cos_ofReal_im, Complex.sin_ofReal_im] at hr hi
    have := Real.sin_sq_add_cos_sq θ
    rw [hr, hi] at this
    norm_num at this
  have hang : (Complex.arg (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨y 0, y 1⟩) : Real.Angle) =
      ((θ + Complex.arg ⟨y 0, y 1⟩ : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hu0 hw0, Real.Angle.coe_add]
    congr 1
    have := Complex.arg_cos_add_sin_mul_I_coe_angle (θ : Real.Angle)
    rwa [Real.Angle.cos_coe, Real.Angle.sin_coe] at this
  obtain ⟨j, hj⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  have hm' : (P.m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hm
  unfold modePhase angleOf logPhase
  rw [hw, hnorm]
  have harg : Complex.arg (((Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I) * ⟨y 0, y 1⟩) =
      Complex.arg ⟨y 0, y 1⟩ + θ + 2 * Real.pi * j := by linarith
  rw [harg]
  have hk : ((n * P.m : ℤ) : ℝ) * θ = 2 * Real.pi * n := by
    rw [hθ]
    push_cast
    field_simp
  have hsplit : ((n * P.m : ℤ) : ℝ) * (Complex.arg ⟨y 0, y 1⟩ + θ + 2 * Real.pi * j) +
      n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)) =
      (((n * P.m : ℤ) : ℝ) * Complex.arg ⟨y 0, y 1⟩ + n * β * ((1 / 2) * Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2))) +
        ((n + n * P.m * j : ℤ) : ℝ) * (2 * Real.pi) := by
    rw [mul_add, mul_add, hk]
    push_cast
    ring
  rw [hsplit, Complex.ofReal_add, mul_add, Complex.exp_add]
  have h1 : Complex.exp (Complex.I * (((n + n * P.m * j : ℤ) : ℝ) * (2 * Real.pi) : ℝ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I (n + n * P.m * j)]
    congr 1
    push_cast
    ring
  rw [h1, mul_one]

theorem givenRe_combo (d : ℝ) (ph : ℤ → ℂ) (S : Finset ℤ) (U V : ℤ → ℂ) (a b : ℝ) :
    ((d : ℂ) * ∑ n ∈ S, ph n * ((a : ℂ) * U n + (b : ℂ) * V n)).re =
      a * ((d : ℂ) * ∑ n ∈ S, ph n * U n).re + b * ((d : ℂ) * ∑ n ∈ S, ph n * V n).re := by
  have h : ∑ n ∈ S, ph n * ((a : ℂ) * U n + (b : ℂ) * V n) =
      (a : ℂ) * ∑ n ∈ S, ph n * U n + (b : ℂ) * ∑ n ∈ S, ph n * V n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h, show (d : ℂ) * ((a : ℂ) * ∑ n ∈ S, ph n * U n + (b : ℂ) * ∑ n ∈ S, ph n * V n) =
      (a : ℂ) * ((d : ℂ) * ∑ n ∈ S, ph n * U n) + (b : ℂ) * ((d : ℂ) * ∑ n ∈ S, ph n * V n) by ring,
    Complex.add_re]
  simp only [Complex.re_ofReal_mul]

theorem fieldOf_turn_apply (P : CellCert.GivenFields.ChartParams) (D : CellCert.GivenFields.FieldData) (β : ℝ)
    (hm : P.m ≠ 0) (y : Space) (hy : y 0 ≠ 0) :
    fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) := by
  obtain ⟨h0, h1, h2⟩ := givenTurn_coords P.m y
  obtain ⟨g0, g1, g2⟩ := givenTurn_coords P.m (fieldOf P D β y)
  have hn := givenNorm_turn P.m y
  have hT : chartT P (turnStep P.m y) = chartT P y := by simp only [chartT, hn]
  have hdec : decayFactor P (turnStep P.m y) = decayFactor P y := by simp only [decayFactor, chartS, hT]
  have hph := fun n => modePhase_turn P hm n β y hy
  have hh : heightRatio (turnStep P.m y) = heightRatio y := by simp only [heightRatio, h2, hn]
  have hq : qOf (turnStep P.m y) = qOf y := by simp only [qOf, hh]
  have r0 : ∀ u0 u1 u2 : ℂ, u0 * (radialVec (turnStep P.m y) 0 : ℂ) + u1 * (polarVecQ (turnStep P.m y) 0 : ℂ) +
      u2 * (azimVecQ (turnStep P.m y) 0 : ℂ) =
      (Real.cos (2 * Real.pi / P.m) : ℂ) * (u0 * (radialVec y 0 : ℂ) + u1 * (polarVecQ y 0 : ℂ) + u2 * (azimVecQ y 0 : ℂ)) +
      ((-Real.sin (2 * Real.pi / P.m) : ℝ) : ℂ) *
        (u0 * (radialVec y 1 : ℂ) + u1 * (polarVecQ y 1 : ℂ) + u2 * (azimVecQ y 1 : ℂ)) := by
    intro u0 u1 u2
    simp only [radialVec, polarVecQ, azimVecQ, h0, h1, hn, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    push_cast
    ring
  have r1 : ∀ u0 u1 u2 : ℂ, u0 * (radialVec (turnStep P.m y) 1 : ℂ) + u1 * (polarVecQ (turnStep P.m y) 1 : ℂ) +
      u2 * (azimVecQ (turnStep P.m y) 1 : ℂ) =
      (Real.sin (2 * Real.pi / P.m) : ℂ) * (u0 * (radialVec y 0 : ℂ) + u1 * (polarVecQ y 0 : ℂ) + u2 * (azimVecQ y 0 : ℂ)) +
      (Real.cos (2 * Real.pi / P.m) : ℂ) *
        (u0 * (radialVec y 1 : ℂ) + u1 * (polarVecQ y 1 : ℂ) + u2 * (azimVecQ y 1 : ℂ)) := by
    intro u0 u1 u2
    simp only [radialVec, polarVecQ, azimVecQ, h0, h1, hn, hh, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons]
    push_cast
    ring
  have r2 : ∀ u0 u1 u2 : ℂ, u0 * (radialVec (turnStep P.m y) 2 : ℂ) + u1 * (polarVecQ (turnStep P.m y) 2 : ℂ) +
      u2 * (azimVecQ (turnStep P.m y) 2 : ℂ) =
      u0 * (radialVec y 2 : ℂ) + u1 * (polarVecQ y 2 : ℂ) + u2 * (azimVecQ y 2 : ℂ) := by
    intro u0 u1 u2
    simp only [radialVec, polarVecQ, azimVecQ, h2, hn, hh, hq, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons]
  ext k
  fin_cases k
  · simp only [Fin.zero_eta, Fin.isValue, g0]
    simp only [fieldOf, ofComponents_apply, hdec, hph, hT, hh, r0]
    rw [givenRe_combo]
    ring
  · simp only [Fin.mk_one, Fin.isValue, g1]
    simp only [fieldOf, ofComponents_apply, hdec, hph, hT, hh, r1]
    rw [givenRe_combo]
  · simp only [Fin.reduceFinMk, Fin.isValue, g2]
    simp only [fieldOf, ofComponents_apply, hdec, hph, hT, hh, r2]

theorem fieldOf_turn_ae (P : CellCert.GivenFields.ChartParams) (D : CellCert.GivenFields.FieldData) (β : ℝ)
    (hm : P.m ≠ 0) : ∀ᵐ y ∂volume, fieldOf P D β (turnStep P.m y) = turnStep P.m (fieldOf P D β y) := by
  filter_upwards [ae_coord_ne_zero 0] with y hy
  exact fieldOf_turn_apply P D β hm y hy


theorem divergenceAt_continuous {f : Space → Space} (hf : ContDiff ℝ 1 f) : Continuous (divergenceAt f) := by
  unfold divergenceAt
  refine continuous_finset_sum _ fun i _ => ?_
  exact (PiLp.continuous_apply 2 _ i).comp ((hf.continuous_fderiv (by norm_num)).clm_apply continuous_const)

theorem divergenceAt_eq_zero_of_ae {f : Space → Space} (hf : ContDiff ℝ 1 f)
    (h : ∀ᵐ y ∂(volume : Measure Space), divergenceAt f y = 0) : ∀ y, divergenceAt f y = 0 := by
  have e : divergenceAt f = fun _ => (0 : ℝ) :=
    (Continuous.ae_eq_iff_eq volume (divergenceAt_continuous hf) continuous_const).1 h
  exact fun y => congrFun e y


theorem cellIndex_eventually (l : List ℝ) (u : ℝ) (hu : u ∉ l) :
    ∀ᶠ u' in nhds u, cellIndex l u' = cellIndex l u := by
  have h : ∀ b ∈ {a | a ∈ l}, ∀ᶠ u' in nhds u, (b ≤ u' ↔ b ≤ u) := by
    intro b hb
    have hbu : b ≠ u := fun e => hu (e ▸ hb)
    rcases lt_or_gt_of_ne hbu with h | h
    · filter_upwards [eventually_gt_nhds h] with u' hu'
      exact ⟨fun _ => h.le, fun _ => hu'.le⟩
    · filter_upwards [eventually_lt_nhds h] with u' hu'
      exact ⟨fun h' => absurd h' (not_le.2 hu'), fun h' => absurd h' (not_le.2 h)⟩
  have hall := (Filter.eventually_all_finite (List.finite_toSet l)).2 h
  filter_upwards [hall] with u' hu'
  unfold cellIndex
  congr 1
  apply List.filter_congr
  intro b hb
  have hbl : b ∈ l := List.mem_of_mem_drop (List.mem_of_mem_dropLast hb)
  simp [hu' b hbl]

theorem mvPoly_eval_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (P : MvPolynomial (Fin 2) ℂ)
    {f g : E → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z => MvPolynomial.eval ![(f z : ℂ), (g z : ℂ)] P) := by
  have hf' : ContDiff ℝ ∞ (fun z => (f z : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
  have hg' : ContDiff ℝ ∞ (fun z => (g z : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    refine hp.mul ?_
    fin_cases i
    · simpa using hf'
    · simpa using hg'

theorem spline_eventually_poly (S : Spline) (odd : Bool) (t x : ℝ) (ht : t ∉ S.mesh.tBreaks)
    (hx : |x| ∉ S.mesh.xBreaks) (hx0 : x ≠ 0) :
    ∃ Q : ℝ × ℝ → ℂ, ContDiff ℝ ∞ Q ∧ ∀ᶠ z in nhds (t, x), S.eval odd z.1 z.2 = Q z := by
  set s : ℝ := if x < 0 then -1 else 1 with hs
  refine ⟨fun z => (if odd && decide (x < 0) then -1 else 1) *
    MvPolynomial.eval ![((z.1 : ℝ) : ℂ), ((s * z.2 : ℝ) : ℂ)]
      (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks |x|)), ?_, ?_⟩
  · exact contDiff_const.mul (mvPoly_eval_contDiff _ contDiff_fst (contDiff_const.mul contDiff_snd))
  · have h1 : ∀ᶠ z in nhds (t, x), cellIndex S.mesh.tBreaks z.1 = cellIndex S.mesh.tBreaks t :=
      (continuous_fst.tendsto (t, x)).eventually (cellIndex_eventually _ _ ht)
    have h2 : ∀ᶠ z in nhds (t, x), cellIndex S.mesh.xBreaks |z.2| = cellIndex S.mesh.xBreaks |x| :=
      ((continuous_abs.comp continuous_snd).tendsto (t, x)).eventually (cellIndex_eventually _ _ hx)
    have h3 : ∀ᶠ z in nhds (t, x), (z.2 < 0 ↔ x < 0) ∧ |z.2| = s * z.2 := by
      rcases lt_or_gt_of_ne hx0 with h | h
      · filter_upwards [(continuous_snd.tendsto (t, x)).eventually (eventually_lt_nhds h)] with z hz
        refine ⟨⟨fun _ => h, fun _ => hz⟩, ?_⟩
        rw [hs, if_pos h, abs_of_neg hz]
        ring
      · filter_upwards [(continuous_snd.tendsto (t, x)).eventually (eventually_gt_nhds h)] with z hz
        refine ⟨⟨fun h' => absurd h' (not_lt.2 hz.le), fun h' => absurd h' (not_lt.2 h.le)⟩, ?_⟩
        rw [hs, if_neg (not_lt.2 h.le), abs_of_pos hz]
        ring
    filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
    unfold Spline.eval Spline.evalHalf
    rw [hz1, hz2, hz3.2]
    simp only [hz3.1]


theorem cone_null (c : ℝ) : volume {y : Space | y 2 = c * ‖y‖} = 0 := by
  by_cases hc : 1 ≤ |c|
  · refine measure_mono_null (fun y hy => ?_) (ae_iff.1 (ae_coord_ne_zero (0 : Fin 3)))
    simp only [Set.mem_setOf_eq] at hy ⊢
    have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three]
    have h2 : y 2 ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [hy]; ring
    have hc2 : 1 ≤ c ^ 2 := by nlinarith [sq_abs c, abs_nonneg c]
    have : y 0 ^ 2 ≤ 0 := by nlinarith [sq_nonneg (y 1), sq_nonneg ‖y‖]
    intro h0
    exact h0 (by nlinarith [sq_nonneg (y 0)])
  · push_neg at hc
    have hc2 : c ^ 2 < 1 := by nlinarith [sq_abs c, abs_nonneg c]
    set k : ℝ := c / Real.sqrt (1 - c ^ 2) with hk
    have hs1 : 0 < Real.sqrt (1 - c ^ 2) := Real.sqrt_pos.2 (by linarith)
    let f : Space → Space := fun u => u + (k * ‖u‖) • (EuclideanSpace.single 2 (1 : ℝ) : Space)
    let P : Set Space := {u | u 2 = 0} \ {0}
    have hP : volume P = 0 := by
      refine measure_mono_null Set.diff_subset ?_
      have := ae_iff.1 (ae_coord_ne_zero (2 : Fin 3))
      simpa using this
    have hdiff : DifferentiableOn ℝ f P := by
      intro u hu
      have hu0 : u ≠ 0 := hu.2
      exact (differentiableAt_id.add (((differentiableAt_id.norm ℝ hu0).const_mul k).smul_const _)).differentiableWithinAt
    have himg := MeasureTheory.addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume hdiff hP
    refine measure_mono_null (fun y hy => ?_) (measure_union_null himg (measure_singleton (0 : Space)))
    simp only [Set.mem_setOf_eq] at hy
    by_cases hy0 : y = 0
    · exact Or.inr hy0
    left
    set u : Space := y - (y 2) • (EuclideanSpace.single 2 (1 : ℝ) : Space) with hu
    have hu0' : u 0 = y 0 := by simp [hu]
    have hu1' : u 1 = y 1 := by simp [hu]
    have hu2' : u 2 = 0 := by simp [hu]
    have hnu : ‖u‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three, hu0', hu1', hu2']
    have hny : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
      simp [Fin.sum_univ_three]
    have hkey : y 2 = k * ‖u‖ := by
      have h2 : y 2 ^ 2 * (1 - c ^ 2) = c ^ 2 * ‖u‖ ^ 2 := by
        rw [hnu]
        have : y 2 ^ 2 = c ^ 2 * ‖y‖ ^ 2 := by rw [hy]; ring
        nlinarith [this, hny]
      have hsq : (k * ‖u‖) ^ 2 = y 2 ^ 2 := by
        have hne : 1 - c ^ 2 ≠ 0 := by linarith
        rw [mul_pow, hk, div_pow, Real.sq_sqrt (by linarith), div_mul_eq_mul_div, div_eq_iff hne]
        linarith [h2]
      have hsign : 0 ≤ y 2 * (k * ‖u‖) := by
        rw [hy, hk, show c * ‖y‖ * (c / Real.sqrt (1 - c ^ 2) * ‖u‖) =
          (c * c) * (‖y‖ * ‖u‖ / Real.sqrt (1 - c ^ 2)) by ring]
        exact mul_nonneg (mul_self_nonneg c) (by positivity)
      have hprod : (y 2 - k * ‖u‖) * (y 2 + k * ‖u‖) = 0 := by
        have : (y 2 - k * ‖u‖) * (y 2 + k * ‖u‖) = y 2 ^ 2 - (k * ‖u‖) ^ 2 := by ring
        rw [this, hsq, sub_self]
      rcases mul_eq_zero.1 hprod with h | h
      · linarith
      · have hb : y 2 = -(k * ‖u‖) := by linarith
        rw [hb] at hsign
        have hb0 : k * ‖u‖ = 0 := by nlinarith [sq_nonneg (k * ‖u‖)]
        rw [hb, hb0, neg_zero]
    refine ⟨u, ⟨hu2', ?_⟩, ?_⟩
    · intro h
      apply hy0
      have hu00 : u = 0 := h
      have : ‖u‖ = 0 := by rw [hu00, norm_zero]
      have hy2 : y 2 = 0 := by rw [hkey, this, mul_zero]
      have e0 : y 0 = 0 := by rw [← hu0', hu00]; rfl
      have e1 : y 1 = 0 := by rw [← hu1', hu00]; rfl
      ext i
      fin_cases i <;> simp [e0, e1, hy2]
    · show u + (k * ‖u‖) • (EuclideanSpace.single 2 (1 : ℝ) : Space) = y
      rw [← hkey, hu]
      abel

theorem ae_chartT_ne (P : CellCert.GivenFields.ChartParams) (hL : 0 < P.L0) (b : ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), chartT P y ≠ b := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (Measure.addHaar_sphere volume (0 : Space) (b * P.L0 / (1 - b)))
  simp only [ne_eq, Decidable.not_not, Set.mem_setOf_eq, chartT] at hy
  have hpos : 0 < ‖y‖ + P.L0 := by positivity
  have h1 : ‖y‖ = b * (‖y‖ + P.L0) := by
    field_simp at hy
    linarith
  have hb : b ≠ 1 := by
    intro e
    rw [e] at h1
    linarith
  have hne : 1 - b ≠ 0 := sub_ne_zero.2 (Ne.symm hb)
  rw [mem_sphere_zero_iff_norm, eq_div_iff hne]
  linarith

theorem ae_heightRatio_abs_ne (b : ℝ) : ∀ᵐ y ∂(volume : Measure Space), |heightRatio y| ≠ b := by
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) (measure_union_null (cone_null b) (cone_null (-b)))
  simp only [ne_eq, Decidable.not_not, Set.mem_setOf_eq, heightRatio] at hy
  by_cases hy0 : ‖y‖ = 0
  · left
    have : y = 0 := norm_eq_zero.1 hy0
    simp [this]
  · rcases abs_eq_abs.1 (show |y 2 / ‖y‖| = |b| from by rw [hy]; exact (abs_of_nonneg (hy ▸ abs_nonneg _)).symm) with h | h
    · rcases abs_cases (y 2 / ‖y‖) with ⟨ha, _⟩ | ⟨ha, _⟩
      · left
        show y 2 = b * ‖y‖
        rw [← hy, ha]
        field_simp
      · right
        show y 2 = -b * ‖y‖
        rw [← hy, ha]
        field_simp
    · rcases abs_cases (y 2 / ‖y‖) with ⟨ha, _⟩ | ⟨ha, _⟩
      · left
        show y 2 = b * ‖y‖
        rw [← hy, ha]
        field_simp
      · right
        show y 2 = -b * ‖y‖
        rw [← hy, ha]
        field_simp

theorem ae_generic (P : CellCert.GivenFields.ChartParams) (hL : 0 < P.L0) (lt lx : List ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), y 0 ≠ 0 ∧ y 1 ≠ 0 ∧ y 2 ≠ 0 ∧ chartT P y ∉ lt ∧ |heightRatio y| ∉ lx := by
  have ht : ∀ᵐ y ∂(volume : Measure Space), ∀ b ∈ {a | a ∈ lt}, chartT P y ≠ b :=
    (Filter.eventually_all_finite (List.finite_toSet lt)).2 fun b _ => ae_chartT_ne P hL b
  have hx : ∀ᵐ y ∂(volume : Measure Space), ∀ b ∈ {a | a ∈ lx}, |heightRatio y| ≠ b :=
    (Filter.eventually_all_finite (List.finite_toSet lx)).2 fun b _ => ae_heightRatio_abs_ne b
  filter_upwards [ae_coord_ne_zero 0, ae_coord_ne_zero 1, ae_coord_ne_zero 2, ht, hx] with y h0 h1 h2 h3 h4
  exact ⟨h0, h1, h2, fun h => h3 _ h rfl, fun h => h4 _ h rfl⟩

end FracInternal

end Breakdown

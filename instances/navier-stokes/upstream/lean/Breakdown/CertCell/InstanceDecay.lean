import Breakdown.CertCell.InstanceChartGlue

open scoped ContDiff Nat
open Polynomial

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.GivenFields

private def glued (S : ChartScalar) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.2 then (S.upper.evalHalf p.1 p.2).re else (S.lower.evalHalf p.1 (-p.2)).re

private theorem glued_contDiffOn (S : ChartScalar) (hS : IsJoinedScalar 2 S) :
    ContDiffOn ℝ 2 (glued S) (Set.Ioo 0 1 ×ˢ Set.univ) :=
  chartScalar_halves_contDiffOn S hS

private theorem breaks_lt_one (l : List ℝ) (hs : l.Pairwise (· < ·)) (h1 : l.getLast? = some 1) :
    ∀ b ∈ (l.drop 1).dropLast, b < 1 := by
  intro b hb
  rw [List.dropLast_drop_eq_drop_dropLast] at hb
  have hb' := List.mem_of_mem_drop hb
  have e := List.dropLast_append_getLast? (l := l) 1 (by rw [h1]; rfl)
  rw [← e, List.pairwise_append] at hs
  exact hs.2.2 b hb' 1 (by simp)

private theorem exists_upper (l : List ℝ) (h : ∀ b ∈ l, b < 1) :
    ∃ m : ℝ, 1 / 2 ≤ m ∧ m < 1 ∧ ∀ b ∈ l, b ≤ m := by
  induction l with
  | nil => exact ⟨1 / 2, le_rfl, by norm_num, by simp⟩
  | cons a l ih =>
    obtain ⟨m, h1, h2, h3⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    refine ⟨max a m, le_max_of_le_right h1, max_lt (h a (by simp)) h2, ?_⟩
    intro b hb
    rcases List.mem_cons.1 hb with rfl | hb
    · exact le_max_left _ _
    · exact le_max_of_le_right (h3 b hb)

private theorem cellIndex_of_ge (l : List ℝ) {t : ℝ} (h : ∀ b ∈ (l.drop 1).dropLast, b ≤ t) :
    cellIndex l t = ((l.drop 1).dropLast).length := by
  unfold cellIndex
  rw [List.filter_eq_self.2]
  intro b hb
  simpa using h b hb

private theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ ((l.drop 1).dropLast).length :=
  List.length_filter_le _ _

private theorem eval_pair (Q : MvPolynomial (Fin 2) ℂ) (t a : ℝ) :
    MvPolynomial.eval ![(t : ℂ), (a : ℂ)] Q =
      (Polynomial.map (MvPolynomial.eval ![(a : ℂ)]) (MvPolynomial.finSuccEquiv ℂ 1 Q)).eval (t : ℂ) :=
  MvPolynomial.eval_eq_eval_mv_eval' ![(a : ℂ)] (t : ℂ) Q

private theorem natDegree_pair (Q : MvPolynomial (Fin 2) ℂ) (a : ℝ) :
    (Polynomial.map (MvPolynomial.eval ![(a : ℂ)]) (MvPolynomial.finSuccEquiv ℂ 1 Q)).natDegree ≤
      MvPolynomial.degreeOf 0 Q :=
  Polynomial.natDegree_map_le.trans (MvPolynomial.natDegree_finSuccEquiv Q).le

private theorem glued_last_cell (S : ChartScalar) (hS : IsJoinedScalar 2 S) :
    ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧ ∃ d : ℕ, ∀ x : ℝ, ∃ q : ℂ[X], q.natDegree ≤ d ∧
      ∀ t, tb ≤ t → glued S (t, x) = (q.eval (t : ℂ)).re := by
  obtain ⟨m, hm1, hm2, hm3⟩ := exists_upper _
    (breaks_lt_one S.upper.mesh.tBreaks hS.upper.mesh.t_sorted hS.upper.mesh.t_last)
  refine ⟨m, by linarith, hm2,
    (∑ j ∈ Finset.range (((S.upper.mesh.xBreaks.drop 1).dropLast).length + 1),
      MvPolynomial.degreeOf 0 (S.upper.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length j)) +
    ∑ j ∈ Finset.range (((S.lower.mesh.xBreaks.drop 1).dropLast).length + 1),
      MvPolynomial.degreeOf 0 (S.lower.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length j),
    fun x => ?_⟩
  have hidx : ∀ t, m ≤ t →
      cellIndex S.upper.mesh.tBreaks t = ((S.upper.mesh.tBreaks.drop 1).dropLast).length :=
    fun t ht => cellIndex_of_ge _ (fun b hb => (hm3 b hb).trans ht)
  have hidx' : ∀ t, m ≤ t →
      cellIndex S.lower.mesh.tBreaks t = ((S.upper.mesh.tBreaks.drop 1).dropLast).length := by
    rw [← hS.same_t]
    exact hidx
  by_cases hx : 0 ≤ x
  · refine ⟨_, (natDegree_pair (S.upper.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length
      (cellIndex S.upper.mesh.xBreaks x)) x).trans ?_, fun t ht => ?_⟩
    · refine le_trans ?_ (Nat.le_add_right _ _)
      exact Finset.single_le_sum
        (f := fun j => MvPolynomial.degreeOf 0 (S.upper.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le (cellIndex_le _ _)))
    · simp only [glued, hx, if_true, Spline.evalHalf, hidx t ht]
      rw [eval_pair]
  · refine ⟨_, (natDegree_pair (S.lower.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length
      (cellIndex S.lower.mesh.xBreaks (-x))) (-x)).trans ?_, fun t ht => ?_⟩
    · refine le_trans ?_ (Nat.le_add_left _ _)
      exact Finset.single_le_sum
        (f := fun j => MvPolynomial.degreeOf 0 (S.lower.piece ((S.upper.mesh.tBreaks.drop 1).dropLast).length j))
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le (cellIndex_le _ _)))
    · simp only [glued, hx, if_false, Spline.evalHalf, hidx' t ht]
      rw [eval_pair]

private def nodeBasis {d : ℕ} (v : Fin (d + 1) → ℝ) (k : Fin (d + 1)) (t : ℝ) : ℝ :=
  ∏ j ∈ Finset.univ.erase k, (v k - v j)⁻¹ * (t - v j)

private theorem nodeBasis_contDiff {d : ℕ} (v : Fin (d + 1) → ℝ) (k : Fin (d + 1)) : ContDiff ℝ 2 (nodeBasis v k) :=
  contDiff_prod fun _ _ => contDiff_const.mul (contDiff_id.sub contDiff_const)

private theorem interp_re {d : ℕ} (v : Fin (d + 1) → ℝ) (hv : Function.Injective v) (q : ℂ[X])
    (hq : q.natDegree ≤ d) (t : ℝ) :
    (q.eval (t : ℂ)).re = ∑ k, nodeBasis v k t * (q.eval (v k : ℂ)).re := by
  have hinj : Set.InjOn (fun k => (v k : ℂ)) (Finset.univ : Finset (Fin (d + 1))) :=
    fun a _ b _ h => hv (Complex.ofReal_injective h)
  have hdeg : q.degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact Polynomial.degree_le_natDegree.trans_lt (by exact_mod_cast Nat.lt_succ_of_le hq)
  have e := congrArg (Polynomial.eval (t : ℂ)) (Lagrange.eq_interpolate hinj hdeg)
  rw [Lagrange.interpolate_apply, Polynomial.eval_finsetSum] at e
  rw [e, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hb : (Lagrange.basis Finset.univ (fun k => (v k : ℂ)) k).eval (t : ℂ) = (nodeBasis v k t : ℂ) := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X, nodeBasis]
    push_cast
    rfl
  rw [Polynomial.eval_mul, Polynomial.eval_C, hb, Complex.re_mul_ofReal, mul_comm]

private theorem glued_far_extension (S : ChartScalar) (hS : IsJoinedScalar 2 S) :
    ∃ tb : ℝ, 0 < tb ∧ tb < 1 ∧ ∃ H : ℝ × ℝ → ℝ, ContDiff ℝ 2 H ∧
      ∀ t x, tb ≤ t → glued S (t, x) = H (t, x) := by
  obtain ⟨tb, h0, h1, d, hq⟩ := glued_last_cell S hS
  have hD : (0 : ℝ) < (d : ℝ) + 2 := by positivity
  have hc : (0 : ℝ) < 1 - tb := by linarith
  let v : Fin (d + 1) → ℝ := fun k => tb + (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((d : ℝ) + 2)
  have hv : Function.Injective v := by
    intro a b hab
    have e1 := add_left_cancel hab
    rw [div_left_inj' hD.ne'] at e1
    have e2 := mul_left_cancel₀ hc.ne' e1
    exact Fin.ext (by exact_mod_cast add_right_cancel e2)
  have hvlo : ∀ k, tb ≤ v k := fun k => le_add_of_nonneg_right (by positivity)
  have hvhi : ∀ k, v k < 1 := by
    intro k
    have hk : (((k : ℕ) : ℝ) + 1) < (d : ℝ) + 2 := by
      have := k.isLt
      have : ((k : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.1 this
      linarith
    have : (1 - tb) * (((k : ℕ) : ℝ) + 1) / ((d : ℝ) + 2) < 1 - tb := by
      rw [div_lt_iff₀ hD]
      nlinarith
    show tb + _ < 1
    linarith
  have hg : ∀ k, ContDiff ℝ 2 (fun x : ℝ => glued S (v k, x)) := fun k =>
    (glued_contDiffOn S hS).comp_contDiff (contDiff_const.prodMk contDiff_id)
      (fun x => ⟨⟨lt_of_lt_of_le h0 (hvlo k), hvhi k⟩, trivial⟩)
  refine ⟨tb, h0, h1, fun p => ∑ k, nodeBasis v k p.1 * glued S (v k, p.2), ?_, ?_⟩
  · exact ContDiff.sum fun k _ => ((nodeBasis_contDiff v k).comp contDiff_fst).mul ((hg k).comp contDiff_snd)
  · intro t x ht
    obtain ⟨q, hqd, hqe⟩ := hq x
    rw [hqe t ht, interp_re v hv q hqd t]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hqe (v k) (hvlo k)]

private def chartPair (y : Space) : ℝ × ℝ := (‖y‖⁻¹, heightRatio y)

private theorem chartPair_contDiffOn : ContDiffOn ℝ 2 chartPair {y : Space | y ≠ 0} := by
  intro y hy
  have hy' : y ≠ 0 := hy
  have hn : ContDiffAt ℝ 2 (fun z : Space => ‖z‖) y := contDiffAt_norm ℝ hy'
  have hn0 : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy'
  have hp : ContDiffAt ℝ 2 (fun z : Space => z 2) y :=
    (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt
  exact ((hn.inv hn0).prodMk (hp.div hn hn0)).contDiffWithinAt

private def scaleFirst (μ : ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (μ • ContinuousLinearMap.fst ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)

private theorem scaleFirst_norm {μ : ℝ} (h0 : 0 ≤ μ) (h1 : μ ≤ 1) : ‖scaleFirst μ‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun p => ?_
  simp only [scaleFirst, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', Prod.norm_def, one_mul, smul_eq_mul,
    norm_mul, Real.norm_eq_abs, abs_of_nonneg h0]
  refine max_le_max ?_ le_rfl
  have := abs_nonneg p.1
  nlinarith

private theorem chartPair_scale {μ : ℝ} (hμ : 0 < μ) :
    chartPair = scaleFirst μ ∘ (chartPair ∘ (μ • ContinuousLinearMap.id ℝ Space)) := by
  funext y
  simp only [Function.comp_apply, scaleFirst, ContinuousLinearMap.prod_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', ContinuousLinearMap.id_apply, chartPair,
    heightRatio, norm_smul, Real.norm_eq_abs, abs_of_pos hμ, smul_eq_mul, PiLp.smul_apply]
  ext
  · simp only
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul]
  · simp only
    rw [mul_div_mul_left _ _ hμ.ne']

private theorem chartPair_bound : ∃ M : ℝ, 1 ≤ M ∧ ∀ y : Space, 1 ≤ ‖y‖ → ∀ i : ℕ, 1 ≤ i → i ≤ 2 →
    ‖iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} y‖ ≤ (M / ‖y‖) ^ i := by
  have hO : IsOpen {z : Space | z ≠ 0} := isOpen_ne
  have hU : UniqueDiffOn ℝ {z : Space | z ≠ 0} := hO.uniqueDiffOn
  have hsub : Metric.sphere (0 : Space) 1 ⊆ {z : Space | z ≠ 0} := by
    intro z hz
    have : ‖z‖ = 1 := by simpa using hz
    exact ne_zero_of_norm_ne_zero (by rw [this]; exact one_ne_zero)
  have hc : ∀ i : ℕ, i ≤ 2 → ∃ C, ∀ z ∈ Metric.sphere (0 : Space) 1,
      ‖iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} z‖ ≤ C := fun i hi =>
    (isCompact_sphere 0 1).exists_bound_of_continuousOn
      ((chartPair_contDiffOn.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hU).mono hsub)
  obtain ⟨C1, hC1⟩ := hc 1 (by norm_num)
  obtain ⟨C2, hC2⟩ := hc 2 le_rfl
  refine ⟨max 1 (max C1 C2), le_max_left _ _, fun y hy i hi1 hi2 => ?_⟩
  set M := max 1 (max C1 C2)
  have hM : 1 ≤ M := le_max_left _ _
  have hsph : ∀ z ∈ Metric.sphere (0 : Space) 1,
      ‖iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} z‖ ≤ M := by
    intro z hz
    interval_cases i
    · exact (hC1 z hz).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hC2 z hz).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hr : 0 < ‖y‖ := lt_of_lt_of_le one_pos hy
  set μ := ‖y‖⁻¹
  have hμ : 0 < μ := inv_pos.2 hr
  have hμ1 : μ ≤ 1 := inv_le_one_of_one_le₀ hy
  set g : Space →L[ℝ] Space := μ • ContinuousLinearMap.id ℝ Space
  have hpre : g ⁻¹' {z : Space | z ≠ 0} = {z : Space | z ≠ 0} := by
    ext z
    simp [g, hμ.ne']
  have hyO : y ∈ {z : Space | z ≠ 0} := ne_zero_of_norm_ne_zero hr.ne'
  have hgy : g y ∈ Metric.sphere (0 : Space) 1 := by
    simp only [g, smul_apply, ContinuousLinearMap.id_apply, mem_sphere_zero_iff_norm,
      norm_smul, Real.norm_eq_abs, abs_of_pos hμ, μ]
    exact inv_mul_cancel₀ hr.ne'
  have hgO : g y ∈ {z : Space | z ≠ 0} := hsub hgy
  have hcd : ContDiffWithinAt ℝ 2 (chartPair ∘ g) {z : Space | z ≠ 0} y := by
    have := chartPair_contDiffOn.comp_continuousLinearMap g
    rw [hpre] at this
    exact this y hyO
  have hright := ContinuousLinearMap.iteratedFDerivWithin_comp_right g chartPair_contDiffOn hU
    (by rw [hpre]; exact hU) hgO (i := i) (by exact_mod_cast hi2)
  rw [hpre] at hright
  have hg : ‖g‖ ≤ μ := by
    simp only [g]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hμ]
    exact mul_le_of_le_one_right hμ.le ContinuousLinearMap.norm_id_le
  have key : iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} y =
      (scaleFirst μ).compContinuousMultilinearMap
        ((iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} (g y)).compContinuousLinearMap fun _ => g) := by
    conv_lhs => rw [chartPair_scale hμ]
    rw [ContinuousLinearMap.iteratedFDerivWithin_comp_left _ hcd hU hyO (by exact_mod_cast hi2), hright]
  rw [key]
  calc ‖(scaleFirst μ).compContinuousMultilinearMap
        ((iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} (g y)).compContinuousLinearMap fun _ => g)‖
      ≤ ‖scaleFirst μ‖ * ‖(iteratedFDerivWithin ℝ i chartPair {z : Space | z ≠ 0} (g y)).compContinuousLinearMap
          fun _ => g‖ := ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
    _ ≤ 1 * (M * μ ^ i) := by
        gcongr
        · exact scaleFirst_norm hμ.le hμ1
        · refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          gcongr
          exact hsph _ hgy
    _ ≤ (M / ‖y‖) ^ i := by
        rw [one_mul, div_eq_mul_inv, mul_pow]
        gcongr
        exact le_self_pow₀ hM (by omega)

private def farPart (L0 : ℝ) (H : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ := H ((1 + L0 * p.1)⁻¹, p.2)

private theorem farPart_contDiffOn {L0 : ℝ} {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ 2 H) :
    ContDiffOn ℝ 2 (farPart L0 H) {p : ℝ × ℝ | 0 < 1 + L0 * p.1} := by
  have h1 : ContDiffOn ℝ 2 (fun p : ℝ × ℝ => 1 + L0 * p.1) {p : ℝ × ℝ | 0 < 1 + L0 * p.1} :=
    (contDiff_const.add (contDiff_const.mul contDiff_fst)).contDiffOn
  exact hH.comp_contDiffOn ((h1.inv fun p hp => ne_of_gt hp).prodMk contDiffOn_snd)

private theorem farPart_bound {L0 : ℝ} (hL : 0 < L0) {H : ℝ × ℝ → ℝ} (hH : ContDiff ℝ 2 H) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1, ∀ i : ℕ, i ≤ 2 →
      ‖iteratedFDerivWithin ℝ i (farPart L0 H) {p : ℝ × ℝ | 0 < 1 + L0 * p.1} p‖ ≤ C := by
  have hV : IsOpen {p : ℝ × ℝ | 0 < 1 + L0 * p.1} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_fst))
  have hsub : Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 ⊆ {p : ℝ × ℝ | 0 < 1 + L0 * p.1} := by
    intro p hp
    have := hp.1.1
    show 0 < 1 + L0 * p.1
    positivity
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1) := isCompact_Icc.prod isCompact_Icc
  have hc : ∀ i : ℕ, i ≤ 2 → ∃ C, ∀ p ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1,
      ‖iteratedFDerivWithin ℝ i (farPart L0 H) {p : ℝ × ℝ | 0 < 1 + L0 * p.1} p‖ ≤ C := fun i hi =>
    hK.exists_bound_of_continuousOn
      (((farPart_contDiffOn hH).continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) hV.uniqueDiffOn).mono hsub)
  obtain ⟨C0, h0⟩ := hc 0 (by norm_num)
  obtain ⟨C1, h1⟩ := hc 1 (by norm_num)
  obtain ⟨C2, h2⟩ := hc 2 le_rfl
  refine ⟨max 0 (max C0 (max C1 C2)), le_max_left _ _, fun p hp i hi => ?_⟩
  interval_cases i
  · exact (h0 p hp).trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact (h1 p hp).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  · exact (h2 p hp).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))

private theorem eval_eq_glued (P : ChartParams) (S : ChartScalar) (hd : S.decay = 0) (y : Space) :
    S.eval P y = glued S (chartT P y, heightRatio y) := by
  have hs : 0 ≤ heightRatio y ↔ 0 ≤ y 2 := by
    by_cases hy : ‖y‖ = 0
    · have : y = 0 := norm_eq_zero.1 hy
      subst this
      simp [heightRatio]
    · have hp : 0 < ‖y‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy)
      rw [heightRatio, le_div_iff₀ hp, zero_mul]
  simp only [ChartScalar.eval, hd, pow_zero, one_mul, glued, hs]

private theorem heightRatio_mem (y : Space) : heightRatio y ∈ Set.Icc (-1 : ℝ) 1 := by
  rw [Set.mem_Icc, ← abs_le, heightRatio, abs_div, abs_norm]
  by_cases hy : ‖y‖ = 0
  · rw [hy, div_zero]
    exact zero_le_one
  · rw [div_le_one (lt_of_le_of_ne (norm_nonneg _) (Ne.symm hy))]
    have := PiLp.norm_apply_le y 2
    simpa [Real.norm_eq_abs] using this

theorem scalarDerivativeDecay (hsm : ScalarSmoothOfJoins) : ScalarDerivativeDecay := by
  intro P S tStar hP hS hcore hd
  have hf : ContDiff ℝ 2 (S.eval P) := hsm P S tStar hP hS hcore hd
  obtain ⟨tb, htb0, htb1, H, hH, hGH⟩ := glued_far_extension S hS
  have hL : 0 < P.L0 := hP.L0_pos
  have hc : 0 < 1 - tb := by linarith
  set R : ℝ := tb * P.L0 / (1 - tb) + 1 with hRdef
  have hR1 : 1 ≤ R := by
    have : 0 ≤ tb * P.L0 / (1 - tb) := by positivity
    linarith
  have hUopen : IsOpen {z : Space | R < ‖z‖} := isOpen_lt continuous_const continuous_norm
  have hVopen : IsOpen {p : ℝ × ℝ | 0 < 1 + P.L0 * p.1} :=
    isOpen_lt continuous_const (continuous_const.add (continuous_const.mul continuous_fst))
  have hUO : {z : Space | R < ‖z‖} ⊆ {z : Space | z ≠ 0} := fun z hz =>
    ne_zero_of_norm_ne_zero (ne_of_gt (lt_of_le_of_lt (zero_le_one.trans hR1) hz))
  have heq : Set.EqOn (S.eval P) (farPart P.L0 H ∘ chartPair) {z : Space | R < ‖z‖} := by
    intro y hy
    have hy' : R < ‖y‖ := hy
    have hr : 0 < ‖y‖ := lt_of_lt_of_le one_pos (hR1.trans hy'.le)
    have ht : tb ≤ chartT P y := by
      rw [chartT, le_div_iff₀ (by positivity)]
      have h1 : tb * P.L0 / (1 - tb) < ‖y‖ := by linarith
      rw [div_lt_iff₀ hc] at h1
      nlinarith
    have hct : chartT P y = (1 + P.L0 * ‖y‖⁻¹)⁻¹ := by
      rw [chartT]
      field_simp
    rw [eval_eq_glued P S hd, hGH _ _ ht, Function.comp_apply, farPart, chartPair, hct]
  obtain ⟨M, hStrain, hMb⟩ := chartPair_bound
  obtain ⟨C, hC0, hCb⟩ := farPart_bound hL hH
  have outer : ∀ y : Space, R < ‖y‖ → ∀ j : ℕ, j ≤ 2 →
      ‖iteratedFDeriv ℝ j (S.eval P) y‖ ≤ j ! * C * (M / ‖y‖) ^ j := by
    intro y hy j hj
    have hyU : y ∈ {z : Space | R < ‖z‖} := hy
    have hy1 : 1 ≤ ‖y‖ := hR1.trans hy.le
    rw [← iteratedFDerivWithin_of_isOpen j hUopen hyU, iteratedFDerivWithin_congr heq hyU]
    have hmem : chartPair y ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1 :=
      ⟨⟨inv_nonneg.2 (norm_nonneg _), inv_le_one_of_one_le₀ hy1⟩, heightRatio_mem y⟩
    refine norm_iteratedFDerivWithin_comp_le (farPart_contDiffOn hH) (chartPair_contDiffOn.mono hUO)
      (by exact_mod_cast hj) hVopen.uniqueDiffOn hUopen.uniqueDiffOn ?_ hyU
      (fun i hi => hCb _ hmem i (hi.trans hj)) (fun i hi1 hi2 => ?_)
    · intro z hz
      show 0 < 1 + P.L0 * ‖z‖⁻¹
      positivity
    · rw [iteratedFDerivWithin_of_isOpen i hUopen hyU,
        ← iteratedFDerivWithin_of_isOpen i isOpen_ne (hUO hyU)]
      exact hMb y hy1 i hi1 (hi2.trans hj)
  have hK : IsCompact (Metric.closedBall (0 : Space) R) := isCompact_closedBall 0 R
  have hin : ∀ j : ℕ, j ≤ 2 → ∃ A, ∀ y ∈ Metric.closedBall (0 : Space) R,
      ‖iteratedFDeriv ℝ j (S.eval P) y‖ ≤ A := fun j hj =>
    hK.exists_bound_of_continuousOn (hf.continuous_iteratedFDeriv (by exact_mod_cast hj)).continuousOn
  obtain ⟨A0, hA0⟩ := hin 0 (by norm_num)
  obtain ⟨A1, hA1⟩ := hin 1 (by norm_num)
  obtain ⟨A2, hA2⟩ := hin 2 le_rfl
  set A := max 0 (max A0 (max A1 A2))
  have hA : ∀ y ∈ Metric.closedBall (0 : Space) R, ∀ j : ℕ, j ≤ 2 → ‖iteratedFDeriv ℝ j (S.eval P) y‖ ≤ A := by
    intro y hy j hj
    interval_cases j
    · exact (hA0 y hy).trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hA1 y hy).trans (((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
    · exact (hA2 y hy).trans (((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _))
  have hA0' : 0 ≤ A := le_max_left _ _
  refine ⟨max ((1 + R) ^ 2 * A) (2 * C * (2 * M) ^ 2), fun y j hj => ?_⟩
  by_cases hy : ‖y‖ ≤ R
  · refine le_trans ?_ (le_max_left _ _)
    have hb := hA y (by simpa using hy) j hj
    have h1 : (1 + ‖y‖) ^ j ≤ (1 + R) ^ 2 := by
      calc (1 + ‖y‖) ^ j ≤ (1 + R) ^ j := by gcongr
        _ ≤ (1 + R) ^ 2 := pow_le_pow_right₀ (by linarith) hj
    exact mul_le_mul h1 hb (norm_nonneg _) (by positivity)
  · refine le_trans ?_ (le_max_right _ _)
    replace hy := not_le.1 hy
    have hy1 : 1 ≤ ‖y‖ := hR1.trans hy.le
    have hr : 0 < ‖y‖ := lt_of_lt_of_le one_pos hy1
    have hb := outer y hy j hj
    have hfac : (j ! : ℝ) ≤ 2 := by
      interval_cases j <;> norm_num [Nat.factorial]
    have hq : (1 + ‖y‖) * (M / ‖y‖) ≤ 2 * M := by
      rw [mul_div_assoc', div_le_iff₀ hr]
      nlinarith
    have hq0 : 0 ≤ (1 + ‖y‖) * (M / ‖y‖) := by positivity
    calc (1 + ‖y‖) ^ j * ‖iteratedFDeriv ℝ j (S.eval P) y‖
        ≤ (1 + ‖y‖) ^ j * (j ! * C * (M / ‖y‖) ^ j) := by gcongr
      _ = (j ! : ℝ) * C * ((1 + ‖y‖) * (M / ‖y‖)) ^ j := by rw [mul_pow]; ring
      _ ≤ 2 * C * (2 * M) ^ 2 := by
          have h2 : ((1 + ‖y‖) * (M / ‖y‖)) ^ j ≤ (2 * M) ^ 2 :=
            (pow_le_pow_left₀ hq0 hq j).trans (pow_le_pow_right₀ (by linarith) hj)
          have h3 : 0 ≤ ((1 + ‖y‖) * (M / ‖y‖)) ^ j := by positivity
          calc (j ! : ℝ) * C * ((1 + ‖y‖) * (M / ‖y‖)) ^ j ≤ 2 * C * ((1 + ‖y‖) * (M / ‖y‖)) ^ j := by
                gcongr
            _ ≤ 2 * C * (2 * M) ^ 2 := by gcongr

end Instance

end CertCell

end Breakdown

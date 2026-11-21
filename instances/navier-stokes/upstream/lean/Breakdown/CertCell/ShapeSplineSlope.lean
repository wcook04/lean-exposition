import Breakdown.CertCell.ShapeStatements

open scoped ContDiff Topology
open Set Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

open CellCert.GivenFields (Spline cellIndex)

def pieceEval (lt lx : List ℝ) (Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (t x : ℝ) : ℂ :=
  MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (Q (cellIndex lt t) (cellIndex lx x))

theorem cellIndex_eventually_right (l : List ℝ) (u : ℝ) :
    ∀ᶠ v in 𝓝[≥] u, cellIndex l v = cellIndex l u := by
  have h : ∀ᶠ v in 𝓝[≥] u, ∀ b ∈ ((l.drop 1).dropLast).toFinset, decide (b ≤ v) = decide (b ≤ u) := by
    rw [Filter.eventually_all_finset]
    intro b _
    by_cases hb : b ≤ u
    · filter_upwards [self_mem_nhdsWithin] with v hv
      have hv' : b ≤ v := le_trans hb hv
      simp [hb, hv']
    · have hlt : ∀ᶠ v in 𝓝[≥] u, v < b := nhdsWithin_le_nhds (eventually_lt_nhds (not_le.mp hb))
      filter_upwards [hlt] with v hv
      have hv' : ¬ b ≤ v := not_le.mpr hv
      simp [hb, hv']
  filter_upwards [h] with v hv
  unfold cellIndex
  congr 1
  apply List.filter_congr
  intro b hb
  exact hv b (List.mem_toFinset.mpr hb)

theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ ((l.drop 1).dropLast).length :=
  List.length_filter_le _ _

theorem polyEval_hasDerivAt_first (P : MvPolynomial (Fin 2) ℂ) (x t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] P)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 P)) t := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const t a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hid : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 t := by
      simpa using (hasDerivAt_id t).ofReal_comp
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have hfun : (fun s : ℝ => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (p * MvPolynomial.X 0)) =
          fun s : ℝ => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] p * (s : ℂ) := by
        funext s
        simp
      have hval : MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 (p * MvPolynomial.X 0)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (t : ℂ) + MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1 := by
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        simp [smul_eq_mul]
        try ring
      rw [hfun, hval]
      exact hp.mul hid
    · have hfun : (fun s : ℝ => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] (p * MvPolynomial.X 1)) =
          fun s : ℝ => MvPolynomial.eval ![(s : ℂ), (x : ℂ)] p * (x : ℂ) := by
        funext s
        simp
      have hval : MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 (p * MvPolynomial.X 1)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 0 p) * (x : ℂ) := by
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        simp [smul_eq_mul]
        try ring
      rw [hfun, hval]
      exact hp.mul_const (x : ℂ)

theorem polyEval_hasDerivAt_second (P : MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] P)
      (MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 P)) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using hasDerivAt_const x a
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    have hid : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ)) 1 x := by
      simpa using (hasDerivAt_id x).ofReal_comp
    obtain rfl | rfl : i = 0 ∨ i = 1 := by fin_cases i <;> simp
    · have hfun : (fun s : ℝ => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (p * MvPolynomial.X 0)) =
          fun s : ℝ => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] p * (t : ℂ) := by
        funext s
        simp
      have hval : MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 (p * MvPolynomial.X 0)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (t : ℂ) := by
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        simp [smul_eq_mul]
        try ring
      rw [hfun, hval]
      exact hp.mul_const (t : ℂ)
    · have hfun : (fun s : ℝ => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] (p * MvPolynomial.X 1)) =
          fun s : ℝ => MvPolynomial.eval ![(t : ℂ), (s : ℂ)] p * (s : ℂ) := by
        funext s
        simp
      have hval : MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 (p * MvPolynomial.X 1)) =
          MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (MvPolynomial.pderiv 1 p) * (x : ℂ) + MvPolynomial.eval ![(t : ℂ), (x : ℂ)] p * 1 := by
        rw [Derivation.leibniz, MvPolynomial.pderiv_X]
        simp [smul_eq_mul]
        try ring
      rw [hfun, hval]
      exact hp.mul hid

theorem pieceEval_right_first (lt lx : List ℝ) (Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (x t : ℝ) :
    HasDerivWithinAt (fun s => pieceEval lt lx Q s x)
      (pieceEval lt lx (fun i j => MvPolynomial.pderiv 0 (Q i j)) t x) (Ici t) t := by
  have h := (polyEval_hasDerivAt_first (Q (cellIndex lt t) (cellIndex lx x)) x t).hasDerivWithinAt
    (s := Ici t)
  refine h.congr_of_eventuallyEq ?_ rfl
  filter_upwards [cellIndex_eventually_right lt t] with s hs
  simp only [pieceEval, hs]

theorem pieceEval_right_second (lt lx : List ℝ) (Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (t x : ℝ) :
    HasDerivWithinAt (fun s => pieceEval lt lx Q t s)
      (pieceEval lt lx (fun i j => MvPolynomial.pderiv 1 (Q i j)) t x) (Ici x) x := by
  have h := (polyEval_hasDerivAt_second (Q (cellIndex lt t) (cellIndex lx x)) t x).hasDerivWithinAt
    (s := Ici x)
  refine h.congr_of_eventuallyEq ?_ rfl
  filter_upwards [cellIndex_eventually_right lx x] with s hs
  simp only [pieceEval, hs]

theorem continuous_pairVec : Continuous fun z : ℝ × ℝ => ![((z.1 : ℝ) : ℂ), ((z.2 : ℝ) : ℂ)] := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · simp only [Fin.zero_eta, Matrix.cons_val_zero]
    exact Complex.continuous_ofReal.comp continuous_fst
  · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    exact Complex.continuous_ofReal.comp continuous_snd

theorem pieceEval_bounded (lt lx : List ℝ) (Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ t x : ℝ, |t| ≤ R → |x| ≤ R → ‖pieceEval lt lx Q t x‖ ≤ M := by
  set K1 := ((lt.drop 1).dropLast).length
  set K2 := ((lx.drop 1).dropLast).length
  let g : ℝ × ℝ → ℝ := fun z => ∑ i ∈ Finset.range (K1 + 1), ∑ j ∈ Finset.range (K2 + 1),
    ‖MvPolynomial.eval ![((z.1 : ℝ) : ℂ), ((z.2 : ℝ) : ℂ)] (Q i j)‖
  have hg : Continuous g := by
    refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
    exact ((MvPolynomial.continuous_eval (Q i j)).comp continuous_pairVec).norm
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_Icc (a := -R) (b := R)) : IsCompact
    (Icc (-R) R ×ˢ Icc (-R) R)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t x ht hx => ?_⟩
  have hmem : (t, x) ∈ Icc (-R) R ×ˢ Icc (-R) R := ⟨abs_le.mp ht, abs_le.mp hx⟩
  have hgC := hC _ hmem
  rw [Real.norm_of_nonneg (by positivity)] at hgC
  have hi : cellIndex lt t ∈ Finset.range (K1 + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (cellIndex_le lt t))
  have hj : cellIndex lx x ∈ Finset.range (K2 + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (cellIndex_le lx x))
  have h1 : ‖pieceEval lt lx Q t x‖ ≤ g (t, x) := by
    refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _) hi)
    exact Finset.single_le_sum (f := fun j => ‖MvPolynomial.eval ![((t : ℝ) : ℂ), ((x : ℝ) : ℂ)]
      (Q (cellIndex lt t) j)‖) (fun j _ => norm_nonneg _) hj
  exact h1.trans (hgC.trans (le_max_left _ _))

theorem slice_diff_le {g g' : ℝ → ℂ} {R M : ℝ} (hc : Continuous g)
    (hd : ∀ s, HasDerivWithinAt g (g' s) (Ici s) s) (hb : ∀ s, |s| ≤ R → ‖g' s‖ ≤ M) :
    ∀ a b : ℝ, |a| ≤ R → |b| ≤ R → ‖g a - g b‖ ≤ M * |a - b| := by
  have key : ∀ a b : ℝ, b ≤ a → |a| ≤ R → |b| ≤ R → ‖g a - g b‖ ≤ M * |a - b| := by
    intro a b hba ha hb'
    have h := norm_image_sub_le_of_norm_deriv_right_le_segment (a := b) (b := a) hc.continuousOn
      (fun s _ => hd s) (fun s hs => hb s (abs_le.mpr ⟨le_trans (abs_le.mp hb').1 hs.1,
        le_trans hs.2.le (abs_le.mp ha).2⟩)) a ⟨hba, le_rfl⟩
    rwa [abs_of_nonneg (sub_nonneg.mpr hba)]
  intro a b ha hb'
  rcases le_total b a with h | h
  · exact key a b h ha hb'
  · rw [norm_sub_rev, abs_sub_comm]
    exact key b a h hb' ha

theorem pieceEval_box (lt lx : List ℝ) (Q : ℕ → ℕ → MvPolynomial (Fin 2) ℂ)
    (hc : Continuous fun z : ℝ × ℝ => pieceEval lt lx Q z.1 z.2) (R : ℝ) :
    ∃ M, 0 ≤ M ∧ ∀ z w : ℝ × ℝ, |z.1| ≤ R → |z.2| ≤ R → |w.1| ≤ R → |w.2| ≤ R →
      ‖pieceEval lt lx Q z.1 z.2 - pieceEval lt lx Q w.1 w.2‖ ≤ M * (|z.1 - w.1| + |z.2 - w.2|) := by
  obtain ⟨M1, hStrain, hb1⟩ := pieceEval_bounded lt lx (fun i j => MvPolynomial.pderiv 0 (Q i j)) R
  obtain ⟨M2, hM2, hb2⟩ := pieceEval_bounded lt lx (fun i j => MvPolynomial.pderiv 1 (Q i j)) R
  refine ⟨M1 + M2, by positivity, fun z w hz1 hz2 hw1 hw2 => ?_⟩
  have c1 : Continuous fun s => pieceEval lt lx Q s z.2 :=
    hc.comp (f := fun s : ℝ => (s, z.2)) (continuous_id.prodMk continuous_const)
  have c2 : Continuous fun s => pieceEval lt lx Q w.1 s :=
    hc.comp (f := fun s : ℝ => (w.1, s)) (continuous_const.prodMk continuous_id)
  have e1 : ‖pieceEval lt lx Q z.1 z.2 - pieceEval lt lx Q w.1 z.2‖ ≤ M1 * |z.1 - w.1| :=
    slice_diff_le c1 (fun s => pieceEval_right_first lt lx Q z.2 s)
      (fun s hs => hb1 s z.2 hs hz2) z.1 w.1 hz1 hw1
  have e2 : ‖pieceEval lt lx Q w.1 z.2 - pieceEval lt lx Q w.1 w.2‖ ≤ M2 * |z.2 - w.2| :=
    slice_diff_le c2 (fun s => pieceEval_right_second lt lx Q w.1 s)
      (fun s hs => hb2 w.1 s hw1 hs) z.2 w.2 hz2 hw2
  have p1 := mul_nonneg hStrain (abs_nonneg (z.2 - w.2))
  have p2 := mul_nonneg hM2 (abs_nonneg (z.1 - w.1))
  calc ‖pieceEval lt lx Q z.1 z.2 - pieceEval lt lx Q w.1 w.2‖
      ≤ ‖pieceEval lt lx Q z.1 z.2 - pieceEval lt lx Q w.1 z.2‖ +
        ‖pieceEval lt lx Q w.1 z.2 - pieceEval lt lx Q w.1 w.2‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ M1 * |z.1 - w.1| + M2 * |z.2 - w.2| := add_le_add e1 e2
    _ ≤ (M1 + M2) * (|z.1 - w.1| + |z.2 - w.2|) := by linarith [add_mul M1 M2 (|z.1 - w.1| + |z.2 - w.2|), mul_add M1 |z.1 - w.1| |z.2 - w.2|, mul_add M2 |z.1 - w.1| |z.2 - w.2|]

theorem opNorm_le_axes (L : ℝ × ℝ →L[ℝ] ℂ) : ‖L‖ ≤ ‖L (1, 0)‖ + ‖L (0, 1)‖ := by
  refine L.opNorm_le_bound (by positivity) fun v => ?_
  have hv : L v = v.1 • L (1, 0) + v.2 • L (0, 1) := by
    rw [← map_smul, ← map_smul, ← map_add]
    congr 1
    ext <;> simp
  have h1 : ‖v.1‖ ≤ ‖v‖ := norm_fst_le v
  have h2 : ‖v.2‖ ≤ ‖v‖ := norm_snd_le v
  have h3 := norm_nonneg (L (1, 0))
  have h4 := norm_nonneg (L (0, 1))
  calc ‖L v‖ ≤ ‖v.1‖ * ‖L (1, 0)‖ + ‖v.2‖ * ‖L (0, 1)‖ := by
        rw [hv, ← norm_smul, ← norm_smul]; exact norm_add_le _ _
    _ ≤ (‖L (1, 0)‖ + ‖L (0, 1)‖) * ‖v‖ := by nlinarith

end Internal

open Internal

theorem joinedSplineGradSlopeBound_of_smooth (hS : JoinedSplineSmooth) : JoinedSplineGradSlopeBound := by
  intro a b S hJ ha hb R
  set F : ℝ × ℝ → ℂ := fun z => S.evalHalf z.1 z.2 with hF
  have hC : ContDiff ℝ 1 F := (hS a b S hJ).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))
  have hdiff : Differentiable ℝ F := hC.differentiable one_ne_zero
  have hcont : Continuous (fderiv ℝ F) := hC.continuous_fderiv one_ne_zero
  have e1 : ∀ z : ℝ × ℝ, fderiv ℝ F z (1, 0) =
      pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) z.1 z.2 := by
    intro z
    have h1 : HasDerivAt (fun s : ℝ => pieceEval S.mesh.tBreaks S.mesh.xBreaks S.piece s z.2)
        (fderiv ℝ F z (1, 0)) z.1 := by
      exact (hdiff z).hasFDerivAt.comp_hasDerivAt z.1
        ((hasDerivAt_id z.1).prodMk (hasDerivAt_const z.1 z.2))
    exact (uniqueDiffWithinAt_Ici z.1).eq_deriv _ h1.hasDerivWithinAt
      (pieceEval_right_first S.mesh.tBreaks S.mesh.xBreaks S.piece z.2 z.1)
  have e2 : ∀ z : ℝ × ℝ, fderiv ℝ F z (0, 1) =
      pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) z.1 z.2 := by
    intro z
    have h1 : HasDerivAt (fun s : ℝ => pieceEval S.mesh.tBreaks S.mesh.xBreaks S.piece z.1 s)
        (fderiv ℝ F z (0, 1)) z.2 := by
      exact (hdiff z).hasFDerivAt.comp_hasDerivAt z.2
        ((hasDerivAt_const z.2 z.1).prodMk (hasDerivAt_id z.2))
    exact (uniqueDiffWithinAt_Ici z.2).eq_deriv _ h1.hasDerivWithinAt
      (pieceEval_right_second S.mesh.tBreaks S.mesh.xBreaks S.piece z.1 z.2)
  have c1 := (hcont.clm_apply (continuous_const (y := ((1 : ℝ), (0 : ℝ))))).congr e1
  have c2 := (hcont.clm_apply (continuous_const (y := ((0 : ℝ), (1 : ℝ))))).congr e2
  obtain ⟨M1, hStrain, hb1⟩ := pieceEval_box _ _ _ c1 R
  obtain ⟨M2, hM2, hb2⟩ := pieceEval_box _ _ _ c2 R
  refine ⟨Real.toNNReal (2 * (M1 + M2)), LipschitzOnWith.of_dist_le' fun z hz w hw => ?_⟩
  have box : ∀ u : ℝ × ℝ, u ∈ Metric.closedBall (0 : ℝ × ℝ) R → |u.1| ≤ R ∧ |u.2| ≤ R := by
    intro u hu
    rw [mem_closedBall_zero_iff] at hu
    exact ⟨(Real.norm_eq_abs u.1 ▸ norm_fst_le u).trans hu, (Real.norm_eq_abs u.2 ▸ norm_snd_le u).trans hu⟩
  obtain ⟨hz1, hz2⟩ := box z hz
  obtain ⟨hw1, hw2⟩ := box w hw
  have d1 : |z.1 - w.1| ≤ ‖z - w‖ := by
    rw [← Real.norm_eq_abs, ← Prod.fst_sub]; exact norm_fst_le _
  have d2 : |z.2 - w.2| ≤ ‖z - w‖ := by
    rw [← Real.norm_eq_abs, ← Prod.snd_sub]; exact norm_snd_le _
  have f1 := hb1 z w hz1 hz2 hw1 hw2
  have f2 := hb2 z w hz1 hz2 hw1 hw2
  rw [dist_eq_norm, dist_eq_norm]
  calc ‖fderiv ℝ F z - fderiv ℝ F w‖
      ≤ ‖(fderiv ℝ F z - fderiv ℝ F w) (1, 0)‖ + ‖(fderiv ℝ F z - fderiv ℝ F w) (0, 1)‖ :=
        opNorm_le_axes _
    _ = ‖pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) z.1 z.2 -
          pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 0 (S.piece i j)) w.1 w.2‖ +
        ‖pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) z.1 z.2 -
          pieceEval S.mesh.tBreaks S.mesh.xBreaks (fun i j => MvPolynomial.pderiv 1 (S.piece i j)) w.1 w.2‖ := by
        rw [FunLike.coe_sub, Pi.sub_apply, Pi.sub_apply, e1, e1, e2, e2]
    _ ≤ M1 * (|z.1 - w.1| + |z.2 - w.2|) + M2 * (|z.1 - w.1| + |z.2 - w.2|) := add_le_add f1 f2
    _ ≤ 2 * (M1 + M2) * ‖z - w‖ := by nlinarith

end GivenShape

end CertCell

end Breakdown

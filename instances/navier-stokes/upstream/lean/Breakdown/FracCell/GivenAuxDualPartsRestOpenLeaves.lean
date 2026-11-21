import Breakdown.FracCell.GivenAuxActuatorOpen
import Breakdown.FracCell.GivenAuxPinSmoothLocal
import Breakdown.FracCell.GivenAuxFarDecayLeaves
import Breakdown.FracCell.GivenAuxDualPartsRestOpenAtomLeaves
import Breakdown.FracCell.PuncturedWeakScalar

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace OpenLeavesInternal

open Filter Set

def pk (Q : MvPolynomial (Fin 2) ℂ) (p : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(p.1 : ℂ), (p.2 : ℂ)] Q

theorem vec_continuous : Continuous (fun p : ℝ × ℝ => (![(p.1 : ℂ), (p.2 : ℂ)] : Fin 2 → ℂ)) := by
  refine continuous_pi fun i => ?_
  fin_cases i
  · exact Complex.continuous_ofReal.comp continuous_fst
  · exact Complex.continuous_ofReal.comp continuous_snd

theorem pk_continuous (Q : MvPolynomial (Fin 2) ℂ) : Continuous (pk Q) :=
  (MvPolynomial.continuous_eval Q).comp vec_continuous

theorem pk_bound (Q : MvPolynomial (Fin 2) ℂ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t u : ℝ, |t| ≤ 1 → |u| ≤ 1 →
    ‖pk Q (t, u)‖ ≤ B := by
  have hK : IsCompact (Metric.closedBall (0 : ℝ × ℝ) 1) := isCompact_closedBall _ _
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (pk_continuous Q).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t u ht hu => ?_⟩
  have hm : (t, u) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le ht hu
  exact (hC _ hm).trans (le_max_left _ _)

theorem eval_atFirst (c : ℂ) (p : MvPolynomial (Fin 2) ℂ) (v : Fin 2 → ℂ) :
    MvPolynomial.eval v (atFirst c p) = MvPolynomial.eval ![c, v 1] p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [atFirst]
  | add p q hp hq => simp only [atFirst, map_add] at *; rw [hp, hq]
  | mul_X p n hp =>
    simp only [atFirst, map_mul] at *
    rw [hp]
    fin_cases n <;> simp

theorem pk_one_eq_zero {R : MvPolynomial (Fin 2) ℂ} (h : atFirst 1 R = 0) (u : ℝ) : pk R (1, u) = 0 := by
  have e := eval_atFirst 1 R ![(0 : ℂ), (u : ℂ)]
  rw [h, map_zero] at e
  simpa [pk] using e.symm

theorem pk_hasDerivAt (Q : MvPolynomial (Fin 2) ℂ) (t u : ℝ) :
    HasDerivAt (fun s : ℝ => pk Q (s, u)) (pk (MvPolynomial.pderiv 0 Q) (t, u)) t := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa [pk] using hasDerivAt_const t c
  | add p q hp hq =>
    have e : (fun s : ℝ => pk (p + q) (s, u)) = fun s => pk p (s, u) + pk q (s, u) := by
      funext s; simp [pk]
    rw [e]
    exact (hp.add hq).congr_deriv (by simp [pk])
  | mul_X p i hp =>
    fin_cases i
    · show HasDerivAt (fun s : ℝ => pk (p * MvPolynomial.X 0) (s, u))
        (pk (MvPolynomial.pderiv 0 (p * MvPolynomial.X 0)) (t, u)) t
      have e : (fun s : ℝ => pk (p * MvPolynomial.X 0) (s, u)) = fun s => pk p (s, u) * ((s : ℝ) : ℂ) := by
        funext s; simp [pk]
      rw [e]
      refine (hp.mul (hasDerivAt_id' t).ofReal_comp).congr_deriv ?_
      rw [Derivation.leibniz, MvPolynomial.pderiv_X]
      simp [pk]
      ring
    · show HasDerivAt (fun s : ℝ => pk (p * MvPolynomial.X 1) (s, u))
        (pk (MvPolynomial.pderiv 0 (p * MvPolynomial.X 1)) (t, u)) t
      have e : (fun s : ℝ => pk (p * MvPolynomial.X 1) (s, u)) = fun s => pk p (s, u) * ((u : ℝ) : ℂ) := by
        funext s; simp [pk]
      rw [e]
      refine (hp.mul_const _).congr_deriv ?_
      rw [Derivation.leibniz, MvPolynomial.pderiv_X]
      simp [pk]
      ring

theorem tail_poly (Q : MvPolynomial (Fin 2) ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ t u : ℝ, |t| ≤ 1 → |u| ≤ 1 →
      ‖pk (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 Q)) (t, u)‖ ≤ B)
    (h0 : atFirst 1 Q = 0) (h1 : atFirst 1 (MvPolynomial.pderiv 0 Q) = 0)
    {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : |u| ≤ 1) :
    ‖pk Q (t, u)‖ ≤ B * (1 - t) ^ 2 ∧ ‖pk (MvPolynomial.pderiv 0 Q) (t, u)‖ ≤ B * (1 - t) := by
  have hd1 : ∀ τ, t ≤ τ → τ ≤ 1 → ‖pk (MvPolynomial.pderiv 0 Q) (τ, u)‖ ≤ B * (1 - τ) := by
    intro τ hτ0 hτ1
    have hm := (convex_Icc τ 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := fun s => pk (MvPolynomial.pderiv 0 Q) (s, u))
      (fun x _ => (pk_hasDerivAt _ x u).hasDerivWithinAt)
      (fun x hx => hB x u (abs_le.2 ⟨by linarith [hx.1], hx.2⟩) hu)
      (left_mem_Icc.2 hτ1) (right_mem_Icc.2 hτ1)
    rw [pk_one_eq_zero h1, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hm
    exact hm
  refine ⟨?_, hd1 t le_rfl ht1⟩
  have hm := (convex_Icc t 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pk Q (s, u)) (C := B * (1 - t))
    (fun x _ => (pk_hasDerivAt _ x u).hasDerivWithinAt)
    (fun x hx => (hd1 x hx.1 hx.2).trans (mul_le_mul_of_nonneg_left (by linarith [hx.1]) hB0))
    (left_mem_Icc.2 ht1) (right_mem_Icc.2 ht1)
  rw [pk_one_eq_zero h0, zero_sub, norm_neg, Real.norm_eq_abs, abs_of_nonneg (by linarith)] at hm
  calc ‖pk Q (t, u)‖ ≤ B * (1 - t) * (1 - t) := hm
    _ = B * (1 - t) ^ 2 := by ring

theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length - 1 - 1 := by
  unfold cellIndex
  calc _ ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
    _ = l.length - 1 - 1 := by simp only [List.length_dropLast, List.length_drop]

theorem interior_lt_one {l : List ℝ} (hs : l.Pairwise (· < ·)) (hl : l.getLast? = some 1) :
    ∀ e ∈ (l.drop 1).dropLast, e < 1 := by
  intro e he
  rw [List.dropLast_drop_eq_drop_dropLast] at he
  have he' := List.mem_of_mem_drop he
  have happ := List.dropLast_append_getLast? (l := l) 1 (by rw [Option.mem_def]; exact hl)
  rw [← happ, List.pairwise_append] at hs
  exact hs.2.2 e he' 1 (by simp)

theorem two_le_length {l : List ℝ} (h0 : l.head? = some 0) (h1 : l.getLast? = some 1) : 2 ≤ l.length := by
  match l, h0, h1 with
  | [], h0, _ => simp at h0
  | [a], h0, h1 =>
    simp at h0 h1
    rw [h0] at h1
    norm_num at h1
  | _ :: _ :: _, _, _ => simp

theorem flux_tail (S : Spline) (hmesh : IsTensorMesh S.mesh)
    (htail : ∀ k < cellCount S.mesh.xBreaks, atFirst 1 (S.piece (atomLastT S) k) = 0 ∧
      atFirst 1 (tDeriv 1 (S.piece (atomLastT S) k)) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ, 0 ≤ t → t < 1 → |u| ≤ 1 →
      ‖pk (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks u)) (t, u)‖ ≤ K * (1 - t) ^ 2 ∧
      ‖pk (MvPolynomial.pderiv 0 (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks u))) (t, u)‖ ≤
        K * (1 - t) := by
  choose B0 hB0 hB using fun ij : ℕ × ℕ => pk_bound (S.piece ij.1 ij.2)
  choose B1 hB10 hB1 using fun ij : ℕ × ℕ => pk_bound (MvPolynomial.pderiv 0 (S.piece ij.1 ij.2))
  choose B2 hB20 hB2 using fun ij : ℕ × ℕ =>
    pk_bound (MvPolynomial.pderiv 0 (MvPolynomial.pderiv 0 (S.piece ij.1 ij.2)))
  set R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1) with hR
  set Bs := ∑ ij ∈ R, (B0 ij + B1 ij + B2 ij) with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun ij _ => by linarith [hB0 ij, hB10 ij, hB20 ij]
  have hle : ∀ ij ∈ R, B0 ij ≤ Bs ∧ B1 ij ≤ Bs ∧ B2 ij ≤ Bs := by
    intro ij h
    have := Finset.single_le_sum (f := fun ij => B0 ij + B1 ij + B2 ij)
      (fun k _ => by linarith [hB0 k, hB10 k, hB20 k]) h
    refine ⟨?_, ?_, ?_⟩ <;> linarith [hB0 ij, hB10 ij, hB20 ij]
  set I := (S.mesh.tBreaks.drop 1).dropLast with hI
  have hlt : ∀ e ∈ I, e < 1 := interior_lt_one hmesh.t_sorted hmesh.t_last
  set fs : Finset ℝ := insert 0 I.toFinset with hfs
  have hne : fs.Nonempty := Finset.insert_nonempty _ _
  set b := fs.max' hne with hb
  have hb1 : b < 1 := by
    rw [hb, Finset.max'_lt_iff]
    intro e he
    rw [hfs, Finset.mem_insert, List.mem_toFinset] at he
    rcases he with h | h
    · rw [h]; norm_num
    · exact hlt e h
  set δ := 1 - b with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  have hlx := two_le_length hmesh.x_first hmesh.x_last
  refine ⟨Bs + Bs / δ ^ 2 + Bs / δ, by positivity, fun t u ht0 ht1 hu => ?_⟩
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1.le
  have hi := cellIndex_le S.mesh.tBreaks t
  have hj := cellIndex_le S.mesh.xBreaks u
  have hmem : (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) ∈ R := by
    rw [hR, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  obtain ⟨l0, l1, l2⟩ := hle _ hmem
  have q0 := hB (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) t u hta hu
  have q1 := hB1 (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) t u hta hu
  have hK1 : Bs ≤ Bs + Bs / δ ^ 2 + Bs / δ := by
    have : 0 ≤ Bs / δ ^ 2 := by positivity
    have : 0 ≤ Bs / δ := by positivity
    linarith
  have hs0 : 0 ≤ 1 - t := by linarith
  by_cases hall : ∀ e ∈ I, e ≤ t
  · have hci : cellIndex S.mesh.tBreaks t = atomLastT S := by
      unfold cellIndex atomLastT cellCount
      rw [List.filter_eq_self.2 (fun e he => by simpa using hall e he)]
      simp only [List.length_dropLast, List.length_drop]
    have hx : cellIndex S.mesh.xBreaks u < cellCount S.mesh.xBreaks := by
      unfold cellCount; omega
    obtain ⟨h0, h1⟩ := htail _ hx
    simp only [tDeriv, Function.iterate_one] at h1
    rw [← hci] at h0 h1
    obtain ⟨r0, r1⟩ := tail_poly _ (hB20 (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u))
      (fun t' u' ht' hu' => hB2 (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) t' u' ht' hu') h0 h1 ht0 ht1.le hu
    refine ⟨r0.trans ?_, r1.trans ?_⟩
    · exact mul_le_mul_of_nonneg_right (l2.trans hK1) (by positivity)
    · exact mul_le_mul_of_nonneg_right (l2.trans hK1) hs0
  · simp only [not_forall, not_le, exists_prop] at hall
    obtain ⟨e, he, hte⟩ := hall
    have heb : e ≤ b := Finset.le_max' _ _ (by rw [hfs]; exact Finset.mem_insert_of_mem (List.mem_toFinset.2 he))
    have hδt : δ ≤ 1 - t := by rw [hδ]; linarith
    have hA : Bs ≤ Bs / δ ^ 2 * (1 - t) ^ 2 := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hδ0.le hδt 2) hBs0
    have hB' : Bs ≤ Bs / δ * (1 - t) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ0]
      exact mul_le_mul_of_nonneg_left hδt hBs0
    have hK2 : Bs / δ ^ 2 ≤ Bs + Bs / δ ^ 2 + Bs / δ := by
      have : 0 ≤ Bs / δ := by positivity
      linarith
    have hK3 : Bs / δ ≤ Bs + Bs / δ ^ 2 + Bs / δ := by
      have : 0 ≤ Bs / δ ^ 2 := by positivity
      linarith
    refine ⟨(q0.trans l0).trans (hA.trans ?_), (q1.trans l1).trans (hB'.trans ?_)⟩
    · exact mul_le_mul_of_nonneg_right hK2 (by positivity)
    · exact mul_le_mul_of_nonneg_right hK3 hs0

theorem norm_smul_pos {s : ℝ} (hs : 0 < s) (y : Space) : ‖s • y‖ = s * ‖y‖ := by
  rw [norm_smul, Real.norm_of_nonneg hs.le]

theorem height_smul {s : ℝ} (hs : 0 < s) (y : Space) : heightRatio (s • y) = heightRatio y := by
  unfold heightRatio
  rw [norm_smul_pos hs]
  simp only [PiLp.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hs.ne'

theorem q_smul {s : ℝ} (hs : 0 < s) (y : Space) : qOf (s • y) = qOf y := by
  unfold qOf; rw [height_smul hs]

theorem angle_smul {s : ℝ} (hs : 0 < s) (y : Space) : angleOf (s • y) = angleOf y := by
  unfold angleOf
  have e : (⟨(s • y) 0, (s • y) 1⟩ : ℂ) = (s : ℂ) * ⟨y 0, y 1⟩ := by
    apply Complex.ext <;> simp
  rw [e, Complex.arg_real_mul _ hs]

def prof (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (y : Space) (ρ : ℝ) : ℂ :=
  (((1 - ρ / (ρ + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) *
    (Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (1 + ρ ^ 2 / P.rc ^ 2)) +
      (M : ℝ) * angleOf y : ℝ))) * ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) *
      S.eval (decide (a = 0)) (ρ / (ρ + P.L0)) (heightRatio y))

theorem ray (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) (y : Space) {s : ℝ} (hs : 0 < s) :
    ((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y) = prof P j a M β S y (s * ‖y‖) := by
  unfold atomTerm prof decayFactor chartS chartT logPhase
  rw [q_smul hs, angle_smul hs, height_smul hs, norm_smul_pos hs]

theorem combo_bound {d d' e e' c σ p p' : ℂ} {r K sv jb : ℝ} (hr : 0 ≤ r) (hd : ‖d‖ ≤ 1) (he : ‖e‖ = 1)
    (hc : ‖c‖ ≤ 1) (hσ : ‖σ‖ ≤ 1) (hd' : r * ‖d'‖ ≤ 1) (he' : r * ‖e'‖ ≤ jb) (hjb : 0 ≤ jb)
    (hp : ‖p‖ ≤ K * sv ^ 2) (hp' : r * ‖p'‖ ≤ K * sv ^ 2) :
    ‖r • (d' * (e * c * (σ * p)) + d * (e' * c * (σ * p) + e * c * (σ * p'))) + (2 : ℝ) • (d * (e * c * (σ * p)))‖ ≤
      (4 + jb) * (K * sv ^ 2) := by
  have hcs : ‖c‖ * ‖σ‖ ≤ 1 := mul_le_one₀ hc (norm_nonneg _) hσ
  have hn := norm_nonneg p
  have hn' := norm_nonneg p'
  have hKs : 0 ≤ K * sv ^ 2 := hn.trans hp
  have a1 : ‖d' * (e * c * (σ * p))‖ ≤ ‖d'‖ * ‖p‖ := by
    simp only [norm_mul, he, one_mul]
    have : ‖c‖ * (‖σ‖ * ‖p‖) ≤ ‖p‖ := by
      rw [← mul_assoc]; exact mul_le_of_le_one_left hn hcs
    exact mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have a2 : ‖e' * c * (σ * p)‖ ≤ ‖e'‖ * ‖p‖ := by
    simp only [norm_mul]
    have : ‖c‖ * (‖σ‖ * ‖p‖) ≤ ‖p‖ := by
      rw [← mul_assoc]; exact mul_le_of_le_one_left hn hcs
    calc ‖e'‖ * ‖c‖ * (‖σ‖ * ‖p‖) = ‖e'‖ * (‖c‖ * (‖σ‖ * ‖p‖)) := by ring
      _ ≤ ‖e'‖ * ‖p‖ := mul_le_mul_of_nonneg_left this (norm_nonneg _)
  have a3 : ‖e * c * (σ * p')‖ ≤ ‖p'‖ := by
    simp only [norm_mul, he, one_mul]
    rw [← mul_assoc]; exact mul_le_of_le_one_left hn' hcs
  have a4 : ‖e * c * (σ * p)‖ ≤ ‖p‖ := by
    simp only [norm_mul, he, one_mul]
    rw [← mul_assoc]; exact mul_le_of_le_one_left hn hcs
  have hX : ‖d' * (e * c * (σ * p)) + d * (e' * c * (σ * p) + e * c * (σ * p'))‖ ≤
      ‖d'‖ * ‖p‖ + (‖e'‖ * ‖p‖ + ‖p'‖) := by
    refine (norm_add_le _ _).trans (add_le_add a1 ?_)
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) hd).trans ((norm_add_le _ _).trans (add_le_add a2 a3)) |>.trans' ?_
    exact le_rfl
  have hY : ‖d * (e * c * (σ * p))‖ ≤ ‖p‖ := by
    rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hd).trans a4
  have b1 : r * (‖d'‖ * ‖p‖) ≤ K * sv ^ 2 := by
    calc r * (‖d'‖ * ‖p‖) = (r * ‖d'‖) * ‖p‖ := by ring
      _ ≤ 1 * (K * sv ^ 2) := mul_le_mul hd' hp hn zero_le_one
      _ = K * sv ^ 2 := one_mul _
  have b2 : r * (‖e'‖ * ‖p‖) ≤ jb * (K * sv ^ 2) := by
    calc r * (‖e'‖ * ‖p‖) = (r * ‖e'‖) * ‖p‖ := by ring
      _ ≤ jb * (K * sv ^ 2) := mul_le_mul he' hp hn hjb
  calc _ ≤ ‖r • (d' * (e * c * (σ * p)) + d * (e' * c * (σ * p) + e * c * (σ * p')))‖ +
        ‖(2 : ℝ) • (d * (e * c * (σ * p)))‖ := norm_add_le _ _
    _ = r * ‖d' * (e * c * (σ * p)) + d * (e' * c * (σ * p) + e * c * (σ * p'))‖ +
        2 * ‖d * (e * c * (σ * p))‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg hr, Real.norm_of_nonneg (by norm_num)]
    _ ≤ r * (‖d'‖ * ‖p‖ + (‖e'‖ * ‖p‖ + ‖p'‖)) + 2 * ‖p‖ := by gcongr
    _ = r * (‖d'‖ * ‖p‖) + r * (‖e'‖ * ‖p‖) + r * ‖p'‖ + 2 * ‖p‖ := by ring
    _ ≤ K * sv ^ 2 + jb * (K * sv ^ 2) + K * sv ^ 2 + 2 * (K * sv ^ 2) := by gcongr
    _ = (4 + jb) * (K * sv ^ 2) := by ring

theorem local_bound (P : ChartParams) (hP : IsChartParams P) (jb θ : ℝ) (c σ : ℂ) (Q : MvPolynomial (Fin 2) ℂ)
    (ux K : ℝ) (hc : ‖c‖ ≤ 1) (hσ : ‖σ‖ ≤ 1) {r : ℝ} (hr : 0 < r)
    (hp : ‖pk Q (r / (r + P.L0), ux)‖ ≤ K * (1 - r / (r + P.L0)) ^ 2)
    (hp' : ‖pk (MvPolynomial.pderiv 0 Q) (r / (r + P.L0), ux)‖ ≤ K * (1 - r / (r + P.L0))) :
    ∃ G' : ℂ, HasDerivAt (fun s : ℝ => s ^ 2 • ((((1 - s * r / (s * r + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * ((jb * ((1 / 2) * Real.log (1 + (s * r) ^ 2 / P.rc ^ 2)) + θ : ℝ))) * c *
        (σ * pk Q (s * r / (s * r + P.L0), ux))))) G' 1 ∧
      ‖G'‖ ≤ (4 + |jb|) * (K * (1 - r / (r + P.L0)) ^ 2) := by
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  have hε := hP.eps_pos
  have hε8 := hP.eps_lt
  set L := P.L0 with hLdef
  have hrL : r + L ≠ 0 := by positivity
  have hrL' : 0 < r + L := by positivity
  set sv := 1 - r / (r + L) with hsvdef
  have hsvL : sv = L / (r + L) := by rw [hsvdef]; field_simp; ring
  have hsv0 : 0 < sv := by rw [hsvL]; positivity
  have hsv1 : sv ≤ 1 := by rw [hsvdef]; have : 0 ≤ r / (r + L) := by positivity
                           linarith
  have hT : HasDerivAt (fun ρ : ℝ => ρ / (ρ + L)) (L / (r + L) ^ 2) r :=
    ((hasDerivAt_id' r).div ((hasDerivAt_id' r).add_const L) hrL).congr_deriv (by ring)
  have hD := (hT.const_sub 1).rpow_const (p := 2 * P.eps) (Or.inl hsv0.ne')
  have hDc := hD.ofReal_comp
  have hL1 : HasDerivAt (fun ρ : ℝ => 1 + ρ ^ 2 / P.rc ^ 2) (2 * r / P.rc ^ 2) r :=
    (((hasDerivAt_pow 2 r).div_const (P.rc ^ 2)).const_add 1).congr_deriv (by norm_num)
  have hpos1 : 1 + r ^ 2 / P.rc ^ 2 ≠ 0 := by positivity
  have hψ := (((hL1.log hpos1).const_mul (1 / 2)).const_mul jb).add_const θ
  have hE := ((hψ.ofReal_comp).const_mul Complex.I).cexp
  have hPk := (pk_hasDerivAt Q (r / (r + L)) ux).scomp r hT
  have hHt := hDc.mul ((hE.mul_const c).mul (hPk.const_mul σ))
  have hHt1 := hHt
  rw [← one_mul r] at hHt1
  have hsq : HasDerivAt (fun s : ℝ => s ^ 2) (2 : ℝ) 1 := by simpa using hasDerivAt_pow 2 (1 : ℝ)
  have hG := hsq.smul (hHt1.scomp 1 (hasDerivAt_mul_const r))
  refine ⟨_, hG, ?_⟩
  simp only [Function.comp_apply, one_mul, one_pow, one_smul]
  have hEn : ∀ x : ℝ, ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := fun x => by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I x
  refine combo_bound hr.le ?_ (hEn _) hc hσ ?_ ?_ (abs_nonneg _) hp ?_
  · rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact Real.rpow_le_one hsv0.le hsv1 (by positivity)
  · rw [Complex.norm_real, Real.norm_eq_abs]
    have hrp : sv ^ (2 * P.eps) ≤ 1 := Real.rpow_le_one hsv0.le hsv1 (by positivity)
    have e : |-(L / (r + L) ^ 2) * (2 * P.eps) * sv ^ (2 * P.eps - 1)| =
        L / (r + L) ^ 2 * (2 * P.eps) * (sv ^ (2 * P.eps) / sv) := by
      rw [Real.rpow_sub_one hsv0.ne', abs_mul, abs_mul, abs_neg, abs_of_nonneg (by positivity),
        abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    rw [e]
    calc r * (L / (r + L) ^ 2 * (2 * P.eps) * (sv ^ (2 * P.eps) / sv))
        ≤ r * (L / (r + L) ^ 2 * (2 * P.eps) * (1 / sv)) := by gcongr
      _ = 2 * P.eps * (r / (r + L)) := by rw [hsvL]; field_simp
      _ ≤ 2 * P.eps * 1 := by
          gcongr
          rw [div_le_one hrL']; linarith
      _ ≤ 1 := by linarith
  · rw [norm_mul, hEn, one_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    have hw : 0 ≤ r ^ 2 / P.rc ^ 2 := by positivity
    have e : r * |1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2))| =
        r ^ 2 / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2) := by
      rw [abs_of_nonneg (by positivity)]
      field_simp
    have h1 : r ^ 2 / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    calc r * (|jb| * |1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2))|)
        = |jb| * (r * |1 / 2 * (2 * r / P.rc ^ 2 / (1 + r ^ 2 / P.rc ^ 2))|) := by ring
      _ ≤ |jb| * 1 := by rw [e]; gcongr
      _ = |jb| := mul_one _
  · rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    have hK : 0 ≤ K * sv := (norm_nonneg _).trans hp'
    calc r * (L / (r + L) ^ 2 * ‖pk (MvPolynomial.pderiv 0 Q) (r / (r + L), ux)‖)
        ≤ r * (L / (r + L) ^ 2 * (K * sv)) := by gcongr
      _ = (r / (r + L)) * (K * sv) * sv := by rw [hsvL]; field_simp
      _ ≤ 1 * (K * sv) * sv := by
          gcongr
          rw [div_le_one hrL']; linarith
      _ = K * sv ^ 2 := by ring

theorem cellIndex_right (l : List ℝ) (u : ℝ) : ∀ᶠ s in 𝓝[≥] u, cellIndex l s = cellIndex l u := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝[≥] u, decide (b ≤ s) = decide (b ≤ u) := by
    intro b _
    rcases le_or_gt b u with hb | hb
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : u ≤ s := hs
      simp [hb, hb.trans hs']
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hb)] with s hs
      simp [not_le.2 hb, not_le.2 hs]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem deriv_norm_le_of_eq {g h : ℝ → ℂ} {u : ℝ} {s : Set ℝ} (hs : UniqueDiffWithinAt ℝ s u)
    {h' : ℂ} (hh : HasDerivAt h h' u) (he : g =ᶠ[𝓝[s] u] h) (hu : g u = h u) :
    ‖deriv g u‖ ≤ ‖h'‖ := by
  by_cases hg : DifferentiableAt ℝ g u
  · have h1 : HasDerivWithinAt h (deriv g u) s u :=
      hg.hasDerivAt.hasDerivWithinAt.congr_of_eventuallyEq he.symm hu.symm
    rw [hs.eq_deriv _ h1 hh.hasDerivWithinAt]
  · rw [deriv_zero_of_not_differentiableAt hg, norm_zero]; exact norm_nonneg _

theorem height_le (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rw [abs_div, abs_norm]
  rcases (norm_nonneg y).eq_or_lt with h | h
  · simp [← h]
  · rw [div_le_one h]; simpa [Real.norm_eq_abs] using PiLp.norm_apply_le y 2

theorem sqrt_q_le (y : Space) (a : ℕ) : ‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_of_nonneg (Real.sqrt_nonneg _)]
  refine pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr ?_)
  unfold qOf
  nlinarith [sq_nonneg (heightRatio y)]

theorem sign_norm_le (b : Bool) : ‖(if b then (-1 : ℂ) else 1)‖ ≤ 1 := by
  split_ifs <;> simp

theorem flux_deriv_bound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ≠ 0 →
      ‖deriv (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1‖ ≤
        C * (1 - ‖y‖ / (‖y‖ + P.L0)) ^ 2 := by
  obtain ⟨K, hK0, hK⟩ := flux_tail S hS.continuous.mesh hS.at_infinity
  refine ⟨(4 + |(j : ℝ) * β|) * K, by positivity, fun y hy => ?_⟩
  have hL := hP.L0_pos
  set r := ‖y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hy
  set t0 := r / (r + P.L0) with ht0
  have ht00 : 0 ≤ t0 := by positivity
  have ht01 : t0 < 1 := by rw [ht0, div_lt_one (by positivity)]; linarith
  set x := heightRatio y with hx
  have hxa : |(|x|)| ≤ 1 := by rw [abs_abs]; exact height_le y
  set Q := S.piece (cellIndex S.mesh.tBreaks t0) (cellIndex S.mesh.xBreaks |x|) with hQ
  set σ : ℂ := if (decide (a = 0) && decide (x < 0)) then -1 else 1 with hσ
  set c : ℂ := ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) with hc
  obtain ⟨q0, q1⟩ := hK t0 |x| ht00 ht01 hxa
  obtain ⟨G', hG, hGb⟩ := local_bound P hP ((j : ℝ) * β) ((M : ℝ) * angleOf y) c σ Q |x| K
    (sqrt_q_le y a) (sign_norm_le _) hr0 q0 q1
  have hev : ∀ τ, cellIndex S.mesh.tBreaks τ = cellIndex S.mesh.tBreaks t0 →
      S.eval (decide (a = 0)) τ x = σ * pk Q (τ, |x|) := by
    intro τ hτ
    simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, hτ]
  have htend : Tendsto (fun s : ℝ => s * r / (s * r + P.L0)) (𝓝[≥] 1) (𝓝[≥] t0) := by
    have hc1 : ContinuousAt (fun s : ℝ => s * r / (s * r + P.L0)) 1 :=
      (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add continuousAt_const)
        (by simp only [one_mul]; positivity)
    have ht : Tendsto (fun s : ℝ => s * r / (s * r + P.L0)) (𝓝 1) (𝓝 t0) := by
      have := hc1.tendsto
      simpa [ht0] using this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (ht.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (1 : ℝ) ≤ s := hs
    show t0 ≤ s * r / (s * r + P.L0)
    rw [ht0, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg hr0.le hL.le) (sub_nonneg.2 hs')]
  have hci := htend.eventually (cellIndex_right S.mesh.tBreaks t0)
  refine (deriv_norm_le_of_eq (uniqueDiffWithinAt_Ici 1) hG ?_ ?_).trans (hGb.trans_eq (by rw [← ht0]; ring))
  · filter_upwards [hci, self_mem_nhdsWithin] with s hs hs1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le one_pos hs1
    rw [ray P j a M β S y hs0]
    simp only [prof]
    rw [hev _ hs]
  · rw [ray P j a M β S y one_pos]
    simp only [prof]
    rw [hev _ (by rw [one_mul])]

theorem cellIndex_nhds (l : List ℝ) {u : ℝ} (hu : u ∉ (l.drop 1).dropLast) :
    ∀ᶠ s in 𝓝 u, cellIndex l s = cellIndex l u := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝 u, decide (b ≤ s) = decide (b ≤ u) := by
    intro b hb
    have hbu : b ≠ u := fun e => hu (e ▸ List.mem_toFinset.1 hb)
    rcases lt_or_gt_of_ne hbu with hb' | hb'
    · filter_upwards [eventually_gt_nhds hb'] with s hs
      simp [hb'.le, hs.le]
    · filter_upwards [eventually_lt_nhds hb'] with s hs
      simp [not_le.2 hb', not_le.2 hs]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem flux_differentiable (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) (y : Space) (hy : y ≠ 0)
    (hgood : ‖y‖ / (‖y‖ + P.L0) ∉ (S.mesh.tBreaks.drop 1).dropLast) :
    DifferentiableAt ℝ (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1 := by
  obtain ⟨K, hK0, hK⟩ := flux_tail S hS.continuous.mesh hS.at_infinity
  have hL := hP.L0_pos
  set r := ‖y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hy
  set t0 := r / (r + P.L0) with ht0
  have ht00 : 0 ≤ t0 := by positivity
  have ht01 : t0 < 1 := by rw [ht0, div_lt_one (by positivity)]; linarith
  set x := heightRatio y with hx
  have hxa : |(|x|)| ≤ 1 := by rw [abs_abs]; exact height_le y
  set Q := S.piece (cellIndex S.mesh.tBreaks t0) (cellIndex S.mesh.xBreaks |x|) with hQ
  set σ : ℂ := if (decide (a = 0) && decide (x < 0)) then -1 else 1 with hσ
  set c : ℂ := ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) with hc
  obtain ⟨q0, q1⟩ := hK t0 |x| ht00 ht01 hxa
  obtain ⟨G', hG, -⟩ := local_bound P hP ((j : ℝ) * β) ((M : ℝ) * angleOf y) c σ Q |x| K
    (sqrt_q_le y a) (sign_norm_le _) hr0 q0 q1
  have hev : ∀ τ, cellIndex S.mesh.tBreaks τ = cellIndex S.mesh.tBreaks t0 →
      S.eval (decide (a = 0)) τ x = σ * pk Q (τ, |x|) := by
    intro τ hτ
    simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, hτ]
  have hc1 : ContinuousAt (fun s : ℝ => s * r / (s * r + P.L0)) 1 :=
    (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add continuousAt_const)
      (by simp only [one_mul]; positivity)
  have ht : Tendsto (fun s : ℝ => s * r / (s * r + P.L0)) (𝓝 1) (𝓝 t0) := by
    have := hc1.tendsto
    simpa [ht0] using this
  have hci := ht.eventually (cellIndex_nhds S.mesh.tBreaks hgood)
  refine hG.differentiableAt.congr_of_eventuallyEq ?_
  filter_upwards [hci, eventually_gt_nhds one_pos] with s hs hs0
  rw [ray P j a M β S y hs0]
  simp only [prof]
  rw [hev _ hs]

theorem evalHalf_measurable (S : Spline) : Measurable (Function.uncurry S.evalHalf) := by
  have hci : ∀ l : List ℝ, Measurable (fun u : ℝ => cellIndex l u) := by
    intro l
    unfold cellIndex
    generalize (l.drop 1).dropLast = l'
    induction l' with
    | nil => simp
    | cons b l ih =>
      have e : (fun u : ℝ => (List.filter (fun c => decide (c ≤ u)) (b :: l)).length) =
          fun u => (if b ≤ u then 1 else 0) + (List.filter (fun c => decide (c ≤ u)) l).length := by
        funext u
        by_cases h : b ≤ u <;> simp [h, add_comm]
      rw [e]
      refine Measurable.add ?_ ih
      exact Measurable.ite measurableSet_Ici measurable_const measurable_const
  let g : ℝ × ℝ → (ℝ × ℝ) × (ℕ × ℕ) := fun p => (p, (cellIndex S.mesh.tBreaks p.1, cellIndex S.mesh.xBreaks p.2))
  let F : (ℝ × ℝ) × (ℕ × ℕ) → ℂ := fun q => pk (S.piece q.2.1 q.2.2) q.1
  have h1 : Measurable g :=
    measurable_id.prodMk (((hci _).comp measurable_fst).prodMk ((hci _).comp measurable_snd))
  have h2 : Measurable F := by
    refine measurable_from_prod_countable_left (fun n => ?_)
    exact (pk_continuous (S.piece n.1 n.2)).measurable
  have e : Function.uncurry S.evalHalf = F ∘ g := by
    funext p
    rfl
  rw [e]
  exact h2.comp h1

theorem eval_measurable (S : Spline) (odd : Bool) : Measurable (Function.uncurry (S.eval odd)) := by
  have ha : Measurable (fun p : ℝ × ℝ => (p.1, |p.2|)) :=
    measurable_fst.prodMk (continuous_abs.measurable.comp measurable_snd)
  have hh : Measurable (Function.uncurry S.evalHalf ∘ fun p : ℝ × ℝ => (p.1, |p.2|)) :=
    (evalHalf_measurable S).comp ha
  have hs : MeasurableSet {p : ℝ × ℝ | (odd && decide (p.2 < 0)) = true} := by
    cases odd
    · simp
    · simpa using measurableSet_lt measurable_snd measurable_const
  have hc : Measurable (fun p : ℝ × ℝ => if (odd && decide (p.2 < 0)) = true then (-1 : ℂ) else 1) :=
    Measurable.ite hs measurable_const measurable_const
  have e : Function.uncurry (S.eval odd) =
      (fun p : ℝ × ℝ => if (odd && decide (p.2 < 0)) = true then (-1 : ℂ) else 1) *
        (Function.uncurry S.evalHalf ∘ fun p : ℝ × ℝ => (p.1, |p.2|)) := by
    funext p
    rfl
  rw [e]
  exact hc.mul hh

theorem atom_measurable (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) :
    Measurable (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) := by
  have hE : Measurable (fun y : Space => S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) := by
    have h1 : Measurable (fun y : Space => (chartT P y, heightRatio y)) := by
      unfold chartT heightRatio; fun_prop
    exact (eval_measurable S _).comp h1
  have hA : Measurable (fun y : Space => angleOf y) := by
    unfold angleOf
    have : Measurable (fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)) := by fun_prop
    have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y : Space => ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) := by
      funext y; exact (Complex.mk_eq_add_mul_I _ _)
    refine Complex.measurable_arg.comp ?_
    rw [e]
    exact this
  have hL : Measurable (fun y : Space => logPhase P y) := by
    unfold logPhase; fun_prop
  have hQ : Measurable (fun y : Space => Real.sqrt (qOf y) ^ a) := by
    unfold qOf heightRatio; fun_prop
  have hD : Measurable (fun y : Space => decayFactor P y) := by
    unfold decayFactor chartS chartT; fun_prop
  unfold atomTerm
  fun_prop

theorem good_ae (P : ChartParams) (hP : IsChartParams P) (I : List ℝ) :
    ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 ∧ ‖y‖ / (‖y‖ + P.L0) ∉ I := by
  have hL := hP.L0_pos
  have h0 : ∀ᵐ y ∂(volume : Measure Space), y ∈ ({0} : Set Space)ᶜ := compl_mem_ae_iff.2 (measure_singleton 0)
  have hb : ∀ b : ℝ, ∀ᵐ y ∂(volume : Measure Space), ‖y‖ / (‖y‖ + P.L0) ≠ b := by
    intro b
    by_cases hb1 : b = 1
    · refine Eventually.of_forall fun y => ?_
      rw [hb1]
      exact ((div_lt_one (by positivity)).2 (by linarith)).ne
    · refine ae_iff.2 (measure_mono_null (t := Metric.sphere (0 : Space) (b * P.L0 / (1 - b)))
        (fun y hy => ?_) (Measure.addHaar_sphere volume 0 _))
      simp only [Set.mem_ofPred_eq, not_not] at hy
      rw [mem_sphere_zero_iff_norm]
      rw [← hy]
      have hpos : ‖y‖ + P.L0 ≠ 0 := by positivity
      have e : 1 - ‖y‖ / (‖y‖ + P.L0) = P.L0 / (‖y‖ + P.L0) := by
        rw [eq_div_iff hpos, sub_mul, div_mul_cancel₀ _ hpos]; ring
      rw [e, div_mul_eq_mul_div, div_div_div_cancel_right₀ hpos, mul_div_assoc, div_self hL.ne', mul_one]
  filter_upwards [h0, (Filter.eventually_all_finset I.toFinset).2 (fun b _ => hb b)] with y hy0 hyb
  exact ⟨hy0, fun hm => hyb _ (List.mem_toFinset.2 hm) rfl⟩

theorem flux_divBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) :
    AEStronglyMeasurable (fun y : Space => ‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) volume ∧
    ∃ C : ℝ, ∀ᵐ y ∂volume, ‖‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1‖ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(2 : ℝ))) := by
  have hL := hP.L0_pos
  refine ⟨?_, ?_⟩
  · have hF : ∀ s : ℝ, Measurable (fun y : Space => s ^ 2 •
        (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) := fun s => by
      have h2 : Measurable (fun y : Space => ((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)) :=
        (atom_measurable P j a M β S).comp (measurable_const_smul s)
      exact (measurable_const (a := (s ^ 2 : ℝ))).smul h2
    refine (measurable_norm.inv).aestronglyMeasurable.smul ?_
    have hseq : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] (1 : ℝ)) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
      · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact Set.mem_compl_singleton_iff.2 (by linarith)
    refine aestronglyMeasurable_of_tendsto_ae atTop
      (f := fun (n : ℕ) (y : Space) => slope (fun s : ℝ => s ^ 2 •
        (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1 (1 + 1 / ((n : ℝ) + 1)))
      (fun n => ?_) ?_
    · simp only [slope_def_module]
      exact (((hF _).sub (hF _)).const_smul _).aestronglyMeasurable
    · filter_upwards [good_ae P hP ((S.mesh.tBreaks.drop 1).dropLast)] with y hy
      have hd := flux_differentiable P hP j a M β S hS y hy.1 hy.2
      exact (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).comp hseq
  · obtain ⟨C, hC0, hC⟩ := flux_deriv_bound P hP j a M β S hS
    refine ⟨C * (max P.L0 1) ^ 2, Eventually.of_forall fun y => ?_⟩
    by_cases hy : y = 0
    · subst hy; simp
    have hr0 : 0 < ‖y‖ := norm_pos_iff.2 hy
    set r := ‖y‖ with hr
    have hsv : 1 - r / (r + P.L0) ≤ max P.L0 1 / (1 + r) := by
      have e : 1 - r / (r + P.L0) = P.L0 / (r + P.L0) := by field_simp; ring
      rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right (le_max_left P.L0 1) hr0.le,
        mul_le_mul_of_nonneg_right (le_max_right P.L0 1) hL.le]
    have hsv0 : 0 ≤ 1 - r / (r + P.L0) := by
      rw [sub_nonneg, div_le_one (by positivity)]; linarith
    rw [norm_smul, norm_inv, norm_norm, Real.rpow_neg (by positivity), Real.rpow_two]
    calc r⁻¹ * ‖deriv (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1‖
        ≤ r⁻¹ * (C * (1 - r / (r + P.L0)) ^ 2) := by gcongr; exact hC y hy
      _ ≤ r⁻¹ * (C * (max P.L0 1 / (1 + r)) ^ 2) := by gcongr
      _ = C * max P.L0 1 ^ 2 * (r⁻¹ * ((1 + r) ^ 2)⁻¹) := by field_simp

theorem invNorm_intOn (R : ℝ) : IntegrableOn (fun y : Space => ‖y‖⁻¹) (Metric.ball 0 R) volume := by
  refine (integrableOn_fun_norm_addHaar (E := Space) volume (f := fun r : ℝ => r⁻¹) (r := R)).2 ?_
  simp only [finrank_euclideanSpace_fin, smul_eq_mul]
  refine IntegrableOn.congr_fun ((continuous_id.integrableOn_Icc (a := 0) (b := R)).mono_set Set.Ioo_subset_Icc_self)
    (fun y hy => ?_) measurableSet_Ioo
  have : y ≠ 0 := hy.1.ne'
  simp only [id]
  field_simp

theorem u_bound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : ∃ B : ℝ, 0 ≤ B ∧ ∀ y : Space,
      ‖((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y‖ ≤ B := by
  obtain ⟨K, hK0, hK⟩ := flux_tail S hS.continuous.mesh hS.at_infinity
  refine ⟨K, hK0, fun y => ?_⟩
  have hL := hP.L0_pos
  have ht0 : 0 ≤ chartT P y := by unfold chartT; positivity
  have ht1 : chartT P y < 1 := by
    unfold chartT; rw [div_lt_one (by positivity)]; linarith
  have hxa : |(|heightRatio y|)| ≤ 1 := by rw [abs_abs]; exact height_le y
  obtain ⟨q0, -⟩ := hK _ _ ht0 ht1 hxa
  have hev : S.eval (decide (a = 0)) (chartT P y) (heightRatio y) =
      (if (decide (a = 0) && decide (heightRatio y < 0)) then (-1 : ℂ) else 1) *
        pk (S.piece (cellIndex S.mesh.tBreaks (chartT P y)) (cellIndex S.mesh.xBreaks |heightRatio y|))
          (chartT P y, |heightRatio y|) := by
    simp only [Spline.eval, Spline.evalHalf, pk]
  have hd : ‖((decayFactor P y : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold decayFactor chartS; positivity)]
    unfold decayFactor chartS
    exact Real.rpow_le_one (by linarith) (by linarith) (by linarith [hP.eps_pos])
  have hE : ‖Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
  have hs1 : (1 - chartT P y) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  unfold atomTerm
  rw [norm_mul, norm_mul, norm_mul, hE, one_mul, hev, norm_mul]
  calc ‖((decayFactor P y : ℝ) : ℂ)‖ * (‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ *
        (‖(if (decide (a = 0) && decide (heightRatio y < 0)) then (-1 : ℂ) else 1)‖ *
          ‖pk (S.piece (cellIndex S.mesh.tBreaks (chartT P y)) (cellIndex S.mesh.xBreaks |heightRatio y|))
            (chartT P y, |heightRatio y|)‖))
      ≤ 1 * (1 * (1 * (K * (1 - chartT P y) ^ 2))) := by
        gcongr
        · exact sqrt_q_le y a
        · exact sign_norm_le _
    _ ≤ K := by nlinarith

theorem deriv_aesm (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : AEStronglyMeasurable (fun y : Space => deriv (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) volume := by
  have hF : ∀ s : ℝ, Measurable (fun y : Space => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) := fun s => by
    have h2 : Measurable (fun y : Space => ((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)) :=
      (atom_measurable P j a M β S).comp (measurable_const_smul s)
    exact (measurable_const (a := (s ^ 2 : ℝ))).smul h2
  have hseq : Tendsto (fun n : ℕ => 1 + 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] (1 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat).const_add (1 : ℝ)
    · have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact Set.mem_compl_singleton_iff.2 (by linarith)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun (n : ℕ) (y : Space) => slope (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1 (1 + 1 / ((n : ℝ) + 1)))
    (fun n => ?_) ?_
  · simp only [slope_def_module]
    exact (((hF _).sub (hF _)).const_smul _).aestronglyMeasurable
  · filter_upwards [good_ae P hP ((S.mesh.tBreaks.drop 1).dropLast)] with y hy
    have hd := flux_differentiable P hP j a M β S hS y hy.1 hy.2
    exact (hasDerivAt_iff_tendsto_slope.1 hd.hasDerivAt).comp hseq

theorem test_bounds (φ : Space → ℝ) (hφ : IsTestScalar φ) : ∃ R Mφ Mφ' : ℝ, 0 < R ∧ 0 ≤ Mφ ∧ 0 ≤ Mφ' ∧
    (∀ y, ‖φ y‖ ≤ Mφ) ∧ (∀ y, ‖fderiv ℝ φ y‖ ≤ Mφ') ∧ (∀ y, R ≤ ‖y‖ → φ y = 0) ∧
      (∀ y, R ≤ ‖y‖ → fderiv ℝ φ y = 0) := by
  obtain ⟨hs, hc⟩ := hφ
  obtain ⟨R0, hR0⟩ := hc.isCompact.isBounded.subset_ball (0 : Space)
  obtain ⟨C, hC⟩ := hs.continuous.bounded_above_of_compact_support hc
  obtain ⟨C', hC'⟩ := (hs.continuous_fderiv (by simp)).bounded_above_of_compact_support (hc.fderiv (𝕜 := ℝ))
  have hout : ∀ y : Space, max R0 1 ≤ ‖y‖ → y ∉ tsupport φ := fun y hy h => by
    have := hR0 h
    rw [Metric.mem_ball, dist_zero_right] at this
    linarith [le_max_left R0 1]
  refine ⟨max R0 1, max C 0, max C' 0, by positivity, le_max_right _ _, le_max_right _ _,
    fun y => (hC y).trans (le_max_left _ _), fun y => (hC' y).trans (le_max_left _ _),
    fun y hy => image_eq_zero_of_notMem_tsupport (hout y hy), fun y hy => ?_⟩
  have h := hout y hy
  exact Function.notMem_support.1 (fun h' => h (support_fderiv_subset ℝ h'))

theorem ind_integrable (R C : ℝ) :
    Integrable (fun y : Space => (Metric.ball (0 : Space) R).indicator (fun y => C * ‖y‖⁻¹) y) volume :=
  (show IntegrableOn (fun y : Space => C * ‖y‖⁻¹) (Metric.ball 0 R) volume from
    (invNorm_intOn R).const_mul C).integrable_indicator measurableSet_ball

theorem j2_deriv (u : Space → ℂ) (hu : Measurable u) {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ y, ‖u y‖ ≤ B)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) :
    HasDerivAt (fun s : ℝ => ∫ z, (φ (s⁻¹ • z) * ‖z‖⁻¹) • u z) (-∫ z, fderiv ℝ φ z (‖z‖⁻¹ • z) • u z) 1 := by
  obtain ⟨R, Mφ, Mφ', hR, hM0, hM0', hM, hM', hz, hz'⟩ := test_bounds φ hφ
  have hd : Differentiable ℝ φ := hφ.1.differentiable (by simp)
  have hcd : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (1 : ℝ))
    (F := fun (s : ℝ) (z : Space) => (φ (s⁻¹ • z) * ‖z‖⁻¹) • u z)
    (F' := fun (s : ℝ) (z : Space) => (fderiv ℝ φ (s⁻¹ • z) ((-(s ^ 2)⁻¹) • z) * ‖z‖⁻¹) • u z)
    (bound := fun z => (Metric.closedBall (0 : Space) (2 * R)).indicator (fun _ => 4 * Mφ' * B) z)
    (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
    (Eventually.of_forall fun s =>
      (((hφ.1.continuous.measurable.comp (measurable_const_smul s⁻¹)).mul measurable_norm.inv).smul hu).aestronglyMeasurable)
    ?_ ?_ ?_
    ((ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) (2 * R)) continuousOn_const).integrable_indicator
      measurableSet_closedBall) ?_
  · have e : ∀ z : Space, (fderiv ℝ φ ((1 : ℝ)⁻¹ • z) ((-((1 : ℝ) ^ 2)⁻¹) • z) * ‖z‖⁻¹) • u z =
        -(fderiv ℝ φ z (‖z‖⁻¹ • z) • u z) := fun z => by
      rw [inv_one, one_smul, one_pow, inv_one, neg_one_smul, map_neg, map_smul, smul_eq_mul, neg_mul, neg_smul,
        mul_comm]
    simp only [e, integral_neg] at hint
    exact hint.2
  · refine Integrable.mono' (ind_integrable R (Mφ * B))
      (((hφ.1.continuous.measurable.comp (measurable_const_smul _)).mul measurable_norm.inv).smul hu).aestronglyMeasurable
      (Eventually.of_forall fun z => ?_)
    simp only [inv_one, one_smul]
    by_cases hzR : ‖z‖ < R
    · rw [Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_zero_right])]
      rw [norm_smul, norm_mul, norm_inv, norm_norm]
      calc ‖φ z‖ * ‖z‖⁻¹ * ‖u z‖ ≤ Mφ * ‖z‖⁻¹ * B := by gcongr; exact hM z; exact hB z
        _ = Mφ * B * ‖z‖⁻¹ := by ring
    · rw [hz z (not_lt.1 hzR)]
      simp only [zero_mul, zero_smul, norm_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) z
  · exact ((((hcd.comp (continuous_const_smul _)).clm_apply (continuous_const_smul _)).measurable.mul
      measurable_norm.inv).smul hu).aestronglyMeasurable
  · refine Eventually.of_forall fun z s hs => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs0 : 0 < s := by linarith
    by_cases hzR : ‖z‖ ≤ 2 * R
    · rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right])]
      have hsq : (s ^ 2)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ (by positivity) (by norm_num)]; nlinarith
      have hzz : ‖z‖ * ‖z‖⁻¹ ≤ 1 := by
        rcases (norm_nonneg z).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [mul_inv_cancel₀ h.ne']
      have h1 : ‖fderiv ℝ φ (s⁻¹ • z) ((-(s ^ 2)⁻¹) • z)‖ * ‖z‖⁻¹ ≤ 4 * Mφ' := by
        calc ‖fderiv ℝ φ (s⁻¹ • z) ((-(s ^ 2)⁻¹) • z)‖ * ‖z‖⁻¹
            ≤ ‖fderiv ℝ φ (s⁻¹ • z)‖ * ‖(-(s ^ 2)⁻¹) • z‖ * ‖z‖⁻¹ := by
              gcongr; exact ContinuousLinearMap.le_opNorm _ _
          _ = ‖fderiv ℝ φ (s⁻¹ • z)‖ * (s ^ 2)⁻¹ * (‖z‖ * ‖z‖⁻¹) := by
              rw [norm_smul, norm_neg, norm_inv, Real.norm_of_nonneg (by positivity)]; ring
          _ ≤ Mφ' * 4 * 1 := by gcongr; exact hM' _
          _ = 4 * Mφ' := by ring
      rw [norm_smul, norm_mul, norm_inv, norm_norm]
      exact mul_le_mul h1 (hB z) (norm_nonneg _) (by positivity)
    · rw [Set.indicator_of_notMem (by rw [Metric.mem_closedBall, dist_zero_right]; exact hzR)]
      have hfar : R ≤ ‖s⁻¹ • z‖ := by
        rw [norm_smul, norm_inv, Real.norm_of_nonneg hs0.le, inv_mul_eq_div, le_div_iff₀ hs0]
        nlinarith
      rw [hz' _ hfar]; simp
  · refine Eventually.of_forall fun z s hs => ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs0 : s ≠ 0 := by intro h; rw [h] at hs; linarith [hs.1]
    exact (((hd _).hasFDerivAt.comp_hasDerivAt s ((hasDerivAt_inv hs0).smul_const z)).mul_const _).smul_const _

theorem flux_weak (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S)
    (hSlope : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal C) (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) (Metric.ball 1 (1 / 2))) :
    ∀ φ : Space → ℝ, IsTestScalar φ →
      Integrable (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) ∧
      ∫ y, fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =
        -∫ y, φ y • (‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
          (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) := by
  intro φ hφ
  obtain ⟨B, hB0, hB⟩ := u_bound P hP j a M β S hS
  obtain ⟨R, Mφ, Mφ', hR, hM0, hM0', hM, hM', hz, hz'⟩ := test_bounds φ hφ
  obtain ⟨C, hC0, hC⟩ := hSlope
  have hum := atom_measurable P j a M β S
  have hcd : Continuous (fderiv ℝ φ) := hφ.1.continuous_fderiv (by simp)
  have hφm : Measurable φ := hφ.1.continuous.measurable
  have hsm : ∀ s : ℝ, Measurable (fun y : Space =>
      ((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)) := fun s =>
    hum.comp (measurable_const_smul s)
  refine ⟨?_, ?_⟩
  · have e : (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) =
        fun y => (‖y‖⁻¹ * fderiv ℝ φ y y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) := by
      funext y; rw [map_smul, smul_eq_mul]
    rw [e]
    refine Integrable.mono' ((ContinuousOn.integrableOn_compact (isCompact_closedBall (0 : Space) R)
      (continuousOn_const (c := Mφ' * B))).integrable_indicator measurableSet_closedBall)
      ((measurable_norm.inv.mul (hcd.clm_apply continuous_id).measurable).smul hum).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    by_cases hyR : ‖y‖ ≤ R
    · rw [Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right])]
      have hzz : ‖y‖⁻¹ * ‖y‖ ≤ 1 := by
        rcases (norm_nonneg y).eq_or_lt with h | h
        · rw [← h]; simp
        · rw [inv_mul_cancel₀ h.ne']
      rw [norm_smul, norm_mul, norm_inv, norm_norm]
      have h1 : ‖fderiv ℝ φ y y‖ ≤ Mφ' * ‖y‖ := (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr; exact hM' y)
      calc ‖y‖⁻¹ * ‖fderiv ℝ φ y y‖ * ‖((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y‖
          ≤ ‖y‖⁻¹ * (Mφ' * ‖y‖) * B := by gcongr; exact hB y
        _ = Mφ' * (‖y‖⁻¹ * ‖y‖) * B := by ring
        _ ≤ Mφ' * 1 * B := by gcongr
        _ = Mφ' * B := by ring
    · rw [hz' y (le_of_lt (not_le.1 hyR))]
      simp only [ContinuousLinearMap.zero_apply, mul_zero, zero_smul, norm_zero]
      exact Set.indicator_nonneg (fun y _ => by positivity) y
  · have h0 : ∀ᵐ y ∂(volume : Measure Space), y ∈ ({0} : Set Space)ᶜ := compl_mem_ae_iff.2 (measure_singleton 0)
    have hJ1 := hasDerivAt_integral_of_dominated_loc_of_lip (μ := volume) (x₀ := (1 : ℝ))
      (F := fun (s : ℝ) (y : Space) => (φ y * ‖y‖⁻¹) • (s ^ 2 •
        (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))))
      (F' := fun y : Space => (φ y * ‖y‖⁻¹) • deriv (fun s : ℝ => s ^ 2 •
        (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1)
      (bound := fun y => (Metric.ball (0 : Space) R).indicator (fun y => Mφ * C * ‖y‖⁻¹) y)
      (Metric.ball_mem_nhds (1 : ℝ) (by norm_num : (0 : ℝ) < 1 / 2))
      (Eventually.of_forall fun s =>
        ((hφm.mul measurable_norm.inv).smul ((measurable_const (a := (s ^ 2 : ℝ))).smul (hsm s))).aestronglyMeasurable)
      ?_ ((hφm.mul measurable_norm.inv).aestronglyMeasurable.smul (deriv_aesm P hP j a M β S hS)) ?_
      (ind_integrable R (Mφ * C)) ?_
    · have hJ2 := j2_deriv (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) hum hB0 hB φ hφ
      have heq : ∀ s : ℝ, 0 < s →
          ∫ y, (φ y * ‖y‖⁻¹) • (s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) =
          ∫ z, (φ (s⁻¹ • z) * ‖z‖⁻¹) • (((decayFactor P z : ℝ) : ℂ) * atomTerm P j a M β S z) := by
        intro s hs
        have hcv := Measure.integral_comp_smul (volume : Measure Space)
          (fun z => (φ (s⁻¹ • z) * ‖z‖⁻¹) • (((decayFactor P z : ℝ) : ℂ) * atomTerm P j a M β S z)) s
        rw [finrank_euclideanSpace_fin] at hcv
        have e : (fun y : Space => (φ y * ‖y‖⁻¹) • (s ^ 2 •
            (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)))) =
            fun y => (s ^ 3) • ((φ (s⁻¹ • s • y) * ‖s • y‖⁻¹) •
              (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) := by
          funext y
          rw [inv_smul_smul₀ hs.ne', norm_smul_pos hs, smul_smul, smul_smul]
          congr 1
          rcases (norm_nonneg y).eq_or_lt with h | h
          · rw [← h]; simp
          · field_simp
        rw [e, integral_smul, hcv, smul_smul, abs_of_pos (by positivity), mul_inv_cancel₀ (by positivity), one_smul]
      have hJ1' : HasDerivAt (fun s : ℝ => ∫ z, (φ (s⁻¹ • z) * ‖z‖⁻¹) •
          (((decayFactor P z : ℝ) : ℂ) * atomTerm P j a M β S z))
          (∫ y, (φ y * ‖y‖⁻¹) • deriv (fun s : ℝ => s ^ 2 •
            (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) 1 := by
        refine hJ1.2.congr_of_eventuallyEq ?_
        filter_upwards [eventually_gt_nhds one_pos] with s hs
        exact (heq s hs).symm
      have hu := hJ1'.unique hJ2
      have e2 : (fun y : Space => φ y • (‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
          (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1)) =
          fun y => (φ y * ‖y‖⁻¹) • deriv (fun s : ℝ => s ^ 2 •
          (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1 :=
        funext fun y => (mul_smul _ _ _).symm
      rw [e2, hu, neg_neg]
    · refine Integrable.mono' (ind_integrable R (Mφ * B))
        ((hφm.mul measurable_norm.inv).smul ((measurable_const (a := ((1 : ℝ) ^ 2 : ℝ))).smul (hsm 1))).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      by_cases hyR : ‖y‖ < R
      · rw [Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_zero_right])]
        simp only [one_pow, one_smul]
        rw [norm_smul, norm_mul, norm_inv, norm_norm]
        calc ‖φ y‖ * ‖y‖⁻¹ * ‖((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y‖ ≤ Mφ * ‖y‖⁻¹ * B := by
              gcongr; exact hM y; exact hB y
          _ = Mφ * B * ‖y‖⁻¹ := by ring
      · rw [hz y (not_lt.1 hyR)]
        simp only [zero_mul, zero_smul, norm_zero]
        exact Set.indicator_nonneg (fun y _ => by positivity) y
    · filter_upwards [h0] with y hy
      have hy' : y ≠ 0 := hy
      refine LipschitzOnWith.of_dist_le_mul fun s hs s' hs' => ?_
      rw [Real.coe_nnabs, dist_eq_norm, ← smul_sub, norm_smul, ← dist_eq_norm]
      have hl := (hC y hy').dist_le_mul s hs s' hs'
      rw [Real.coe_toNNReal _ hC0] at hl
      by_cases hyR : ‖y‖ < R
      · rw [Set.indicator_of_mem (by rwa [Metric.mem_ball, dist_zero_right]),
          abs_of_nonneg (by positivity), norm_mul, norm_inv, norm_norm]
        calc ‖φ y‖ * ‖y‖⁻¹ * dist _ _ ≤ Mφ * ‖y‖⁻¹ * (C * dist s s') := by
              gcongr; exact hM y
          _ = Mφ * C * ‖y‖⁻¹ * dist s s' := by ring
      · rw [hz y (not_lt.1 hyR)]
        simp only [zero_mul, norm_zero]
        positivity
    · filter_upwards [good_ae P hP ((S.mesh.tBreaks.drop 1).dropLast)] with y hy
      exact (flux_differentiable P hP j a M β S hS y hy.1 hy.2).hasDerivAt.const_smul (φ y * ‖y‖⁻¹)

theorem glue_continuous {Z : Type*} [TopologicalSpace Z] (φ : Z → ℝ) (hφ : Continuous φ) :
    ∀ (m : List ℝ), m.Pairwise (· < ·) → ∀ (g : ℕ → Z → ℂ), (∀ k ≤ m.length, Continuous (g k)) →
      (∀ k (hk : k < m.length), ∀ z, φ z = m[k] → g k z = g (k + 1) z) →
      Continuous (fun z => g ((m.filter (fun b => decide (b ≤ φ z))).length) z)
  | [], _, g, hg, _ => by simpa using hg 0 le_rfl
  | b :: m', hm, g, hg, hj => by
    rw [List.pairwise_cons] at hm
    have ih := glue_continuous φ hφ m' hm.2 (fun k => g (k + 1))
      (fun k hk => hg (k + 1) (by simp; omega))
      (fun k hk z hz => hj (k + 1) (by simp; omega) z (by simpa using hz))
    have hnil : ∀ z, φ z ≤ b → m'.filter (fun c => decide (c ≤ φ z)) = [] := by
      intro z hz
      rw [List.filter_eq_nil_iff]
      intro c hc
      have := hm.1 c hc
      simp only [decide_eq_true_eq, not_le]
      linarith
    have e : (fun z => g (((b :: m').filter (fun c => decide (c ≤ φ z))).length) z) =
        fun z => if b ≤ φ z then g ((m'.filter (fun c => decide (c ≤ φ z))).length + 1) z else g 0 z := by
      funext z
      by_cases h : b ≤ φ z
      · simp [h]
      · simp [h, hnil z (le_of_lt (not_le.1 h))]
    rw [e]
    refine Continuous.if_le ih (hg 0 (Nat.zero_le _)) continuous_const hφ ?_
    intro z hz
    simp only [hnil z hz.symm.le, List.length_nil, zero_add]
    exact (hj 0 (by simp) z (by simpa using hz.symm)).symm

theorem interior_get (l : List ℝ) (k : ℕ) (hk : k < ((l.drop 1).dropLast).length) :
    ((l.drop 1).dropLast)[k] = l.getD (k + 1) 0 := by
  have hk' := hk
  simp only [List.length_dropLast, List.length_drop] at hk'
  rw [List.getElem_dropLast, List.getElem_drop, List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

theorem t_continuous (S : Spline) (hS : IsRadialContinuous S) (odd : Bool) (x : ℝ) :
    Continuous (fun t : ℝ => S.eval odd t x) := by
  have hlx := two_le_length hS.mesh.x_first hS.mesh.x_last
  have hj : cellIndex S.mesh.xBreaks |x| < cellCount S.mesh.xBreaks := by
    have := cellIndex_le S.mesh.xBreaks |x|
    unfold cellCount; omega
  set j := cellIndex S.mesh.xBreaks |x| with hjdef
  have hI : ((S.mesh.tBreaks.drop 1).dropLast).Pairwise (· < ·) :=
    hS.mesh.t_sorted.sublist ((List.dropLast_sublist _).trans (List.drop_sublist _ _))
  have hG := glue_continuous (Z := ℝ) id continuous_id _ hI (fun k t => pk (S.piece k j) (t, |x|))
    (fun k _ => (pk_continuous _).comp (continuous_id.prodMk continuous_const)) ?_
  · have e : (fun t : ℝ => S.eval odd t x) = fun t =>
        (if (odd && decide (x < 0)) then (-1 : ℂ) else 1) *
          pk (S.piece ((((S.mesh.tBreaks.drop 1).dropLast).filter (fun b => decide (b ≤ id t))).length) j) (t, |x|) := by
      funext t
      simp only [Spline.eval, Spline.evalHalf, pk, id, hjdef, cellIndex]
    rw [e]
    exact continuous_const.mul hG
  · intro k hk t ht
    have hk' := hk
    simp only [List.length_dropLast, List.length_drop] at hk'
    have h := congrArg (MvPolynomial.eval ![(0 : ℂ), ((|x| : ℝ) : ℂ)])
      (hS.t_joins (k + 1) (by omega) (by unfold cellCount; omega) j hj)
    simp only [eval_atFirst, Nat.add_sub_cancel] at h
    rw [id, interior_get _ _ hk] at ht
    simp only [pk]
    rw [ht]
    simpa using h

theorem ray_right_deriv (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ y : Space, y ≠ 0 → ∀ τ : ℝ, 0 < τ → ∃ D : ℂ,
      HasDerivWithinAt (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)))
        D (Ici τ) τ ∧ ‖D‖ ≤ τ * C0 := by
  obtain ⟨K, hK0, hK⟩ := flux_tail S hS.continuous.mesh hS.at_infinity
  refine ⟨(4 + |(j : ℝ) * β|) * K, by positivity, fun y hy τ hτ => ?_⟩
  have hL := hP.L0_pos
  set r := ‖y‖ with hr
  have hr0 : 0 < r := norm_pos_iff.2 hy
  have hρ : 0 < τ * r := mul_pos hτ hr0
  set t0 := τ * r / (τ * r + P.L0) with ht0
  have ht00 : 0 ≤ t0 := by positivity
  have ht01 : t0 < 1 := by rw [ht0, div_lt_one (by positivity)]; linarith
  set x := heightRatio y with hx
  have hxa : |(|x|)| ≤ 1 := by rw [abs_abs]; exact height_le y
  set Q := S.piece (cellIndex S.mesh.tBreaks t0) (cellIndex S.mesh.xBreaks |x|) with hQ
  set σ : ℂ := if (decide (a = 0) && decide (x < 0)) then -1 else 1 with hσ
  set c : ℂ := ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) with hc
  obtain ⟨q0, q1⟩ := hK t0 |x| ht00 ht01 hxa
  obtain ⟨G', hG, hGb⟩ := local_bound P hP ((j : ℝ) * β) ((M : ℝ) * angleOf y) c σ Q |x| K
    (sqrt_q_le y a) (sign_norm_le _) hρ q0 q1
  have hcomp := (hG.scomp_of_eq τ ((hasDerivAt_id' τ).div_const τ) (div_self hτ.ne').symm).const_smul (τ ^ 2)
  have hHs : HasDerivAt (fun s : ℝ => s ^ 2 • ((((1 - s * r / (s * r + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * (((j : ℝ) * β * ((1 / 2) * Real.log (1 + (s * r) ^ 2 / P.rc ^ 2)) +
        (M : ℝ) * angleOf y : ℝ))) * c * (σ * pk Q (s * r / (s * r + P.L0), |x|)))))
      (τ ^ 2 • ((1 / τ) • G')) τ := by
    refine hcomp.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
    have e1 : s / τ * (τ * r) = s * r := by field_simp
    have e2 : τ ^ 2 * (s / τ) ^ 2 = s ^ 2 := by field_simp
    simp only [Pi.smul_apply, Function.comp_apply, e1, smul_smul, e2]
  have hev : ∀ τ', cellIndex S.mesh.tBreaks τ' = cellIndex S.mesh.tBreaks t0 →
      S.eval (decide (a = 0)) τ' x = σ * pk Q (τ', |x|) := by
    intro τ' hτ'
    simp only [Spline.eval, Spline.evalHalf, pk, hQ, hσ, hτ']
  have htend : Tendsto (fun s : ℝ => s * r / (s * r + P.L0)) (𝓝[≥] τ) (𝓝[≥] t0) := by
    have hc1 : ContinuousAt (fun s : ℝ => s * r / (s * r + P.L0)) τ :=
      (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add continuousAt_const)
        (by show τ * r + P.L0 ≠ 0; positivity)
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (hc1.tendsto.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : τ ≤ s := hs
    show t0 ≤ s * r / (s * r + P.L0)
    rw [ht0, div_le_div_iff₀ (by positivity) (by nlinarith)]
    nlinarith [mul_nonneg (mul_nonneg hr0.le hL.le) (sub_nonneg.2 hs')]
  have hci := htend.eventually (cellIndex_right S.mesh.tBreaks t0)
  refine ⟨_, hHs.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_, ?_⟩
  · filter_upwards [hci, self_mem_nhdsWithin] with s hs hs1
    have hs0 : (0 : ℝ) < s := lt_of_lt_of_le hτ hs1
    rw [ray P j a M β S y hs0]
    simp only [prof]
    rw [hev _ hs]
  · rw [ray P j a M β S y hτ]
    simp only [prof]
    rw [hev _ rfl]
  · rw [norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    have hs1 : (1 - τ * r / (τ * r + P.L0)) ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hGb' : ‖G'‖ ≤ (4 + |(j : ℝ) * β|) * K := by
      refine hGb.trans ?_
      calc (4 + |(j : ℝ) * β|) * (K * (1 - τ * r / (τ * r + P.L0)) ^ 2) ≤ (4 + |(j : ℝ) * β|) * (K * 1) := by
            gcongr
        _ = (4 + |(j : ℝ) * β|) * K := by ring
    calc τ ^ 2 * (1 / τ * ‖G'‖) = τ * ‖G'‖ := by field_simp
      _ ≤ τ * ((4 + |(j : ℝ) * β|) * K) := by gcongr

theorem ray_continuousOn (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) (y : Space) :
    ContinuousOn (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)))
      (Ioi 0) := by
  have hL := hP.L0_pos
  have hrc := hP.rc_pos
  set r := ‖y‖ with hr
  have hcont : ∀ s0 : ℝ, 0 < s0 → ContinuousAt (fun s : ℝ => s ^ 2 • prof P j a M β S y (s * r)) s0 := by
    intro s0 hs0
    have hne : s0 * r + P.L0 ≠ 0 := by positivity
    have hT : ContinuousAt (fun s : ℝ => s * r / (s * r + P.L0)) s0 :=
      (continuousAt_id.mul continuousAt_const).div ((continuousAt_id.mul continuousAt_const).add continuousAt_const) hne
    have hD : ContinuousAt (fun s : ℝ => (((1 - s * r / (s * r + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ)) s0 :=
      Complex.continuous_ofReal.continuousAt.comp ((continuousAt_const.sub hT).rpow_const
        (Or.inr (by linarith [hP.eps_pos])))
    have hlog : ContinuousAt (fun s : ℝ => Real.log (1 + (s * r) ^ 2 / P.rc ^ 2)) s0 :=
      (continuousAt_const.add (((continuousAt_id.mul continuousAt_const).pow 2).div_const _)).log (by show 1 + (s0 * r) ^ 2 / P.rc ^ 2 ≠ 0; positivity)
    have hE : ContinuousAt (fun s : ℝ => Complex.exp (Complex.I * (((j : ℝ) * β *
        ((1 / 2) * Real.log (1 + (s * r) ^ 2 / P.rc ^ 2)) + (M : ℝ) * angleOf y : ℝ) : ℂ))) s0 :=
      Complex.continuous_exp.continuousAt.comp (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          ((continuousAt_const.mul (continuousAt_const.mul hlog)).add continuousAt_const)))
    have hSv : ContinuousAt (fun s : ℝ => S.eval (decide (a = 0)) (s * r / (s * r + P.L0)) (heightRatio y)) s0 :=
      (t_continuous S hS.continuous _ _).continuousAt.comp hT
    exact (continuousAt_id.pow 2).smul (hD.mul ((hE.mul continuousAt_const).mul hSv))
  refine ContinuousOn.congr (f := fun s : ℝ => s ^ 2 • prof P j a M β S y (s * r))
    (fun s hs => (hcont s hs).continuousWithinAt) (fun s hs => ?_)
  simp only []
  rw [ray P j a M β S y hs]

theorem ray_slope (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal C)
      (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y)))
      (Metric.ball 1 (1 / 2)) := by
  obtain ⟨C0, hC0, hrd⟩ := ray_right_deriv P hP j a M β S hS
  refine ⟨2 * C0, by positivity, fun y hy => ?_⟩
  have hex : ∀ τ : ℝ, ∃ D : ℂ, 0 < τ → HasDerivWithinAt (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) D (Ici τ) τ ∧ ‖D‖ ≤ τ * C0 := by
    intro τ
    by_cases hτ : 0 < τ
    · obtain ⟨D, hD⟩ := hrd y hy τ hτ
      exact ⟨D, fun _ => hD⟩
    · exact ⟨0, fun h => absurd h hτ⟩
  choose D hD using hex
  have hco := ray_continuousOn P hP j a M β S hS y
  have key : ∀ u v : ℝ, u ∈ Metric.ball (1 : ℝ) (1 / 2) → v ∈ Metric.ball (1 : ℝ) (1 / 2) → u ≤ v →
      ‖(fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) v -
        (fun s : ℝ => s ^ 2 • (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) u‖ ≤
        2 * C0 * (v - u) := by
    intro u v hu hv huv
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hu hv
    refine norm_image_sub_le_of_norm_deriv_right_le_segment (f' := D)
      (hco.mono fun s hs => show (0 : ℝ) < s by linarith [hs.1])
      (fun s hs => (hD s (by linarith [hs.1])).1)
      (fun s hs => ((hD s (by linarith [hs.1])).2).trans ?_) v (right_mem_Icc.2 huv)
    have : s < 2 := by linarith [hs.2]
    nlinarith
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm, Real.dist_eq]
  rcases le_total u v with h | h
  · rw [norm_sub_rev, abs_of_nonpos (by linarith)]
    have := key u v hu hv h
    linarith
  · rw [abs_of_nonneg (by linarith)]
    exact key v u hv hu h

private theorem far_ofReal {f : Space → ℝ} {a : ℝ} (h : FarDecayInternal.FarDecay f a) :
    FarDecayInternal.FarDecay (fun y => (f y : ℂ)) a := by
  have h' := h.clm Complex.ofRealCLM
  have e : (fun y => Complex.ofRealCLM (f y)) = fun y => (f y : ℂ) := funext fun y => Complex.ofRealCLM_apply _
  rw [e] at h'
  exact h'

private theorem far_re {f : Space → ℂ} {a : ℝ} (h : FarDecayInternal.FarDecay f a) :
    FarDecayInternal.FarDecay (fun y => (f y).re) a := by
  have h' := h.clm Complex.reCLM
  have e : (fun y => Complex.reCLM (f y)) = fun y => (f y).re := funext fun y => Complex.reCLM_apply _
  rw [e] at h'
  exact h'

private theorem single_clm (i : Fin 3) (a : ℝ) :
    (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single i (1 : ℝ)) :
      ℝ →L[ℝ] Space) a = EuclideanSpace.single i a := by
  ext j
  by_cases h : j = i <;> simp [h]

private theorem mode_farDecay (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : FarDecayInternal.FarDecay (modeFieldOf P D β n) 3 := by
  have hR := FarDecayInternal.phased_far P hP D hD β n hn
  have hd := far_ofReal (FarDecayInternal.decay_far P hP)
  have hc : ∀ i : Fin 3, FarDecayInternal.FarDecay (fun y => ((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re) 3 := by
    intro i
    have h0 := (hd.mul ((hR 0).mul (far_ofReal (FarDecayInternal.radial_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have h1 := (hd.mul ((hR 1).mul (far_ofReal (FarDecayInternal.polar_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have h2 := (hd.mul ((hR 2).mul (far_ofReal (FarDecayInternal.azim_far i)))).mono (b := 3) (le_of_eq (by norm_num))
    have hs := far_re ((h0.add h1).add h2)
    have e : (fun y => ((decayFactor P y : ℂ) * (modePhase P n β y *
        (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
          reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
          reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re) =
        fun y => ((decayFactor P y : ℂ) * (modePhase P n β y * reducedField P D n β (chartT P y) (heightRatio y) 0 *
          (radialVec y i : ℂ)) + (decayFactor P y : ℂ) * (modePhase P n β y *
            reducedField P D n β (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ)) +
          (decayFactor P y : ℂ) * (modePhase P n β y *
            reducedField P D n β (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ))).re := by
      funext y
      congr 1
      ring
    rw [e]
    exact hs
  have hL : ∀ i : Fin 3, FarDecayInternal.FarDecay (fun y =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single i (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i))).re)) 3 :=
    fun i => (hc i).clm _
  have hsum := ((hL 0).add (hL 1)).add (hL 2)
  have e : modeFieldOf P D β n = fun y =>
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 0 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 0 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 0 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 0))).re) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 1 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 1 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 1 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 1))).re) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (EuclideanSpace.single 2 (1 : ℝ)) :
        ℝ →L[ℝ] Space) (((decayFactor P y : ℂ) * (modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y 2 +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y 2 +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y 2))).re) := by
    funext y
    simp only [single_clm]
    rfl
  rw [e]
  exact hsum

theorem slope_apply {s : Set Space} {K : NNReal} {G : Space → (Space →L[ℝ] ℂ)} (h : LipschitzOnWith K G s)
    (v : Space) (hv : ‖v‖ ≤ 1) : LipschitzOnWith K (fun z => G z v) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [dist_eq_norm, ← ContinuousLinearMap.sub_apply']
  calc ‖(G x - G y) v‖ ≤ ‖G x - G y‖ * ‖v‖ := (G x - G y).le_opNorm v
    _ ≤ ‖G x - G y‖ * 1 := mul_le_mul_of_nonneg_left hv (norm_nonneg _)
    _ = dist (G x) (G y) := by rw [mul_one, dist_eq_norm]
    _ ≤ K * dist x y := h.dist_le_mul x hx y hy

theorem slope_part {s : Set Space} {K : NNReal} {g : Space → ℂ} (h : LipschitzOnWith K g s)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, |L w| ≤ ‖w‖) : LipschitzOnWith K (fun z => L (g z)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
  rw [Real.dist_eq, ← map_sub]
  exact (hL _).trans ((dist_eq_norm (g x) (g y)).ge.trans (h.dist_le_mul x hx y hy))

theorem fderiv_le_of_ball {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {g : Space → F} {C2 : ℝ}
    {y : Space} (hy : y ≠ 0)
    (h : LipschitzOnWith (Real.toNNReal (C2 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))))) g (Metric.ball y (‖y‖ / 2))) :
    ‖fderiv ℝ g y‖ ≤ max C2 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := by
  refine (norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y (half_pos (norm_pos_iff.2 hy))) h).trans ?_
  rw [Real.coe_toNNReal']
  have hw : 0 ≤ ‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ)) := by positivity
  exact max_le (mul_le_mul_of_nonneg_right (le_max_left _ _) hw) (mul_nonneg (le_max_right _ _) hw)

theorem weight_le (y : Space) : ‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ ‖y‖⁻¹ :=
  mul_le_of_le_one_right (inv_nonneg.2 (norm_nonneg y))
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num))

theorem ae_ne_zero : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
  have h : (volume : Measure Space) {0} = 0 := measure_singleton 0
  filter_upwards [compl_mem_ae_iff.2 h] with y hy
  exact hy

theorem unit_norm (m : Fin 3) : ‖unitVector m‖ = 1 := by simp [unitVector]

theorem part_identity (q : Space → ℂ) {B C2 : ℝ} (hqm : Measurable q) (hqb : ∀ y, ‖q y‖ ≤ B)
    (hqslope : ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal (C2 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))))) q
      (Metric.ball y (‖y‖ / 2)))
    (hann : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K q {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R})
    (hdiff : ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ q y)
    (L : ℂ →L[ℝ] ℝ) (hL : ∀ w, |L w| ≤ ‖w‖) (φ : Space → ℝ) (hφ : IsTestScalar φ) (i : Fin 3) :
    ∫ y, L (fderiv ℝ φ y (unitVector i) • q y) = -∫ y, L (φ y • fderiv ℝ q y (unitVector i)) := by
  have hW := PuncturedWeakInternal.weak_of_punctured (q := fun z => L (q z)) (M := B) (C := max C2 0)
    ((L.continuous.measurable.comp hqm).aestronglyMeasurable)
    (fun y => (hL _).trans (hqb y))
    (fun ε hε R => by
      obtain ⟨K, hK⟩ := hann ε hε R
      exact ⟨K, slope_part hK L hL⟩)
    (by
      filter_upwards [ae_ne_zero] with y hy
      exact (fderiv_le_of_ball hy (slope_part (hqslope y hy) L hL)).trans
        (mul_le_mul_of_nonneg_left (weight_le y) (le_max_right _ _))) φ hφ i
  simp only [PuncturedWeakInternal.inner_gradient] at hW
  have e1 : (fun y => L (fderiv ℝ φ y (unitVector i) • q y)) = fun y => fderiv ℝ φ y (unitVector i) * L (q y) := by
    funext y
    rw [L.map_smul, smul_eq_mul]
  rw [e1, hW]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hdiff] with y hy
  have e2 : fderiv ℝ (fun z => L (q z)) y = L.comp (fderiv ℝ q y) := (L.hasFDerivAt.comp y hy.hasFDerivAt).fderiv
  simp only [e2, ContinuousLinearMap.comp_apply, L.map_smul, smul_eq_mul]

theorem weak_second (f : Space → ℂ) {C C2 : ℝ}
    (hC : ∀ y, ‖fderiv ℝ f y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (hC2 : ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal (C2 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ)))))
      (fderiv ℝ f) (Metric.ball y (‖y‖ / 2)))
    (k : Fin 3) (φ : Space → ℝ) (hφ : IsTestScalar φ) (i : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ f y (unitVector k) =
      -∫ y, φ y • fderiv ℝ (fun z => fderiv ℝ f z (unitVector k)) y (unitVector i) := by
  set q : Space → ℂ := fun z => fderiv ℝ f z (unitVector k) with hq
  have hqslope : ∀ y : Space, y ≠ 0 → LipschitzOnWith (Real.toNNReal (C2 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))))) q
      (Metric.ball y (‖y‖ / 2)) :=
    fun y hy => slope_apply (hC2 y hy) _ (unit_norm k).le
  have hloc : LocallyLipschitzOn {y : Space | y ≠ 0} q := fun y hy =>
    ⟨_, Metric.ball y (‖y‖ / 2),
      mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds y (half_pos (norm_pos_iff.2 hy))), hqslope y hy⟩
  have hann : ∀ ε : ℝ, 0 < ε → ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K q {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
    intro ε hε R
    have hcpt : IsCompact {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} :=
      (isCompact_closedBall (0 : Space) R).of_isClosed_subset
        ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
        (fun y hy => mem_closedBall_zero_iff.2 hy.2)
    exact LocallyLipschitzOn.exists_lipschitzOnWith_of_compact hcpt
      (hloc.mono fun y hy => norm_pos_iff.1 (hε.trans_le hy.1))
  have hw2 : ∀ y : Space, (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ 1 := fun y =>
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
  have hqb : ∀ y, ‖q y‖ ≤ max C 0 := fun y => by
    have h0 : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
    calc ‖q y‖ ≤ ‖fderiv ℝ f y‖ * ‖unitVector k‖ := (fderiv ℝ f y).le_opNorm _
      _ = ‖fderiv ℝ f y‖ := by rw [unit_norm k, mul_one]
      _ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := hC y
      _ ≤ max C 0 * (1 + ‖y‖) ^ (-(2 : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) h0
      _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left (hw2 y) (le_max_right _ _)
      _ = max C 0 := mul_one _
  have hqm : Measurable q := measurable_fderiv_apply_const ℝ f (unitVector k)
  have hdiff : ∀ᵐ y ∂(volume : Measure Space), DifferentiableAt ℝ q y := by
    have h : ∀ n : ℕ, ∀ᵐ y ∂(volume : Measure Space),
        y ∈ {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} → DifferentiableAt ℝ q y := by
      intro n
      obtain ⟨K, hK⟩ := hann (1 / ((n : ℝ) + 1)) (by positivity) ((n : ℝ) + 1)
      have hK' : LipschitzOnWith K q {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} :=
        hK.mono fun y hy => ⟨hy.1.le, hy.2.le⟩
      have hopen : IsOpen {y : Space | 1 / ((n : ℝ) + 1) < ‖y‖ ∧ ‖y‖ < (n : ℝ) + 1} :=
        (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
      filter_upwards [hK'.ae_differentiableWithinAt_of_mem] with y hy hmem
      exact (hy hmem).differentiableAt (hopen.mem_nhds hmem)
    filter_upwards [ae_all_iff.2 h, ae_ne_zero] with y hy hy0
    obtain ⟨n, hn⟩ := exists_nat_gt (max ‖y‖ ‖y‖⁻¹)
    have hp := norm_pos_iff.2 hy0
    refine hy n ⟨?_, by linarith [le_max_left ‖y‖ ‖y‖⁻¹]⟩
    rw [div_lt_iff₀ (by positivity)]
    have h1 : ‖y‖⁻¹ < (n : ℝ) + 1 := by linarith [le_max_right ‖y‖ ‖y‖⁻¹]
    calc (1 : ℝ) = ‖y‖ * ‖y‖⁻¹ := (mul_inv_cancel₀ hp.ne').symm
      _ < ‖y‖ * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left h1 hp
  obtain ⟨R, Mφ, Mφ', hR, hMφ, hMφ', hφb, hφb', hφz, hφz'⟩ := test_bounds φ hφ
  set W : ℝ := Mφ' * max C 0 * R + Mφ * max C2 0 with hW
  have hdom := ind_integrable R W
  have hWn : 0 ≤ W := by positivity
  have hA : Integrable (fun y => fderiv ℝ φ y (unitVector i) • q y) := by
    refine hdom.mono' ((((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).measurable.smul
      hqm).aestronglyMeasurable) ?_
    filter_upwards [ae_ne_zero] with y hy
    have hp := norm_pos_iff.2 hy
    by_cases hyR : ‖y‖ < R
    · rw [Set.indicator_of_mem (by simpa using hyR)]
      rw [norm_smul]
      have h1 : ‖fderiv ℝ φ y (unitVector i)‖ ≤ Mφ' := by
        calc ‖fderiv ℝ φ y (unitVector i)‖ ≤ ‖fderiv ℝ φ y‖ * ‖unitVector i‖ := (fderiv ℝ φ y).le_opNorm _
          _ ≤ Mφ' := by rw [unit_norm i, mul_one]; exact hφb' y
      have h2 : (1 : ℝ) ≤ R * ‖y‖⁻¹ := by
        rw [le_mul_inv_iff₀ hp, one_mul]; exact hyR.le
      calc ‖fderiv ℝ φ y (unitVector i)‖ * ‖q y‖ ≤ Mφ' * max C 0 :=
            mul_le_mul h1 (hqb y) (norm_nonneg _) hMφ'
        _ = Mφ' * max C 0 * 1 := (mul_one _).symm
        _ ≤ Mφ' * max C 0 * (R * ‖y‖⁻¹) := mul_le_mul_of_nonneg_left h2 (by positivity)
        _ ≤ W * ‖y‖⁻¹ := by
            rw [hW, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right (by nlinarith [le_max_right C2 0]) (inv_nonneg.2 (norm_nonneg y))
    · rw [Set.indicator_of_notMem (by simpa using hyR), hφz' y (not_lt.1 hyR)]
      simp
  have hB : Integrable (fun y => φ y • fderiv ℝ q y (unitVector i)) := by
    refine hdom.mono' ((hφ.1.continuous.measurable.smul
      (measurable_fderiv_apply_const ℝ q (unitVector i))).aestronglyMeasurable) ?_
    filter_upwards [ae_ne_zero] with y hy
    by_cases hyR : ‖y‖ < R
    · rw [Set.indicator_of_mem (by simpa using hyR)]
      rw [norm_smul]
      have h1 : ‖fderiv ℝ q y (unitVector i)‖ ≤ max C2 0 * ‖y‖⁻¹ := by
        calc ‖fderiv ℝ q y (unitVector i)‖ ≤ ‖fderiv ℝ q y‖ * ‖unitVector i‖ := (fderiv ℝ q y).le_opNorm _
          _ = ‖fderiv ℝ q y‖ := by rw [unit_norm i, mul_one]
          _ ≤ max C2 0 * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := fderiv_le_of_ball hy (hqslope y hy)
          _ ≤ max C2 0 * ‖y‖⁻¹ := mul_le_mul_of_nonneg_left (weight_le y) (le_max_right _ _)
      calc ‖φ y‖ * ‖fderiv ℝ q y (unitVector i)‖ ≤ Mφ * (max C2 0 * ‖y‖⁻¹) :=
            mul_le_mul (hφb y) h1 (norm_nonneg _) hMφ
        _ ≤ W * ‖y‖⁻¹ := by
            rw [hW, ← mul_assoc]
            exact mul_le_mul_of_nonneg_right
              (le_add_of_nonneg_left (mul_nonneg (mul_nonneg hMφ' (le_max_right C 0)) hR.le))
              (inv_nonneg.2 (norm_nonneg y))
    · rw [Set.indicator_of_notMem (by simpa using hyR), hφz y (not_lt.1 hyR)]
      simp
  have hre := part_identity q hqm hqb hqslope hann hdiff Complex.reCLM
    (fun w => by rw [Complex.reCLM_apply]; exact Complex.abs_re_le_norm w) φ hφ i
  have him := part_identity q hqm hqb hqslope hann hdiff Complex.imCLM
    (fun w => by rw [Complex.imCLM_apply]; exact Complex.abs_im_le_norm w) φ hφ i
  apply Complex.ext
  · have e1 : (∫ y, fderiv ℝ φ y (unitVector i) • q y).re =
        ∫ y, Complex.reCLM (fderiv ℝ φ y (unitVector i) • q y) := by
      rw [Complex.reCLM.integral_comp_comm hA]; rfl
    have e2 : (∫ y, φ y • fderiv ℝ q y (unitVector i)).re =
        ∫ y, Complex.reCLM (φ y • fderiv ℝ q y (unitVector i)) := by
      rw [Complex.reCLM.integral_comp_comm hB]; rfl
    rw [Complex.neg_re, e1, e2]
    exact hre
  · have e1 : (∫ y, fderiv ℝ φ y (unitVector i) • q y).im =
        ∫ y, Complex.imCLM (fderiv ℝ φ y (unitVector i) • q y) := by
      rw [Complex.imCLM.integral_comp_comm hA]; rfl
    have e2 : (∫ y, φ y • fderiv ℝ q y (unitVector i)).im =
        ∫ y, Complex.imCLM (φ y • fderiv ℝ q y (unitVector i)) := by
      rw [Complex.imCLM.integral_comp_comm hB]; rfl
    rw [Complex.neg_im, e1, e2]
    exact him

theorem pk_zero_eq_zero {R : MvPolynomial (Fin 2) ℂ} (h : atFirst 0 R = 0) (u : ℝ) : pk R (0, u) = 0 := by
  have e := eval_atFirst 0 R ![(0 : ℂ), (u : ℂ)]
  rw [h, map_zero] at e
  simpa [pk] using e.symm

theorem origin_poly (Q : MvPolynomial (Fin 2) ℂ) {B : ℝ}
    (hB : ∀ t u : ℝ, |t| ≤ 1 → |u| ≤ 1 → ‖pk (MvPolynomial.pderiv 0 Q) (t, u)‖ ≤ B)
    (h0 : atFirst 0 Q = 0) {t u : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hu : |u| ≤ 1) :
    ‖pk Q (t, u)‖ ≤ B * t := by
  have hm := (convex_Icc 0 t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun s => pk Q (s, u)) (C := B)
    (fun x _ => (pk_hasDerivAt _ x u).hasDerivWithinAt)
    (fun x hx => hB x u (abs_le.2 ⟨by linarith [hx.1], by linarith [hx.2]⟩) hu)
    (left_mem_Icc.2 ht0) (right_mem_Icc.2 ht0)
  rw [pk_zero_eq_zero h0, sub_zero, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at hm
  exact hm

theorem interior_pos {l : List ℝ} (hs : l.Pairwise (· < ·)) (h0 : l.head? = some 0) :
    ∀ e ∈ (l.drop 1).dropLast, 0 < e := by
  intro e he
  match l, hs, h0, he with
  | a :: rest, hs, h0, he =>
    simp only [List.head?_cons, Option.some.injEq] at h0
    subst h0
    simp only [List.drop_succ_cons, List.drop_zero] at he
    exact (List.pairwise_cons.1 hs).1 e (List.dropLast_subset _ he)

theorem origin_bound (S : Spline) (hmesh : IsTensorMesh S.mesh)
    (horig : ∀ k < cellCount S.mesh.xBreaks, atFirst 0 (S.piece 0 k) = 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ t u : ℝ, 0 ≤ t → t ≤ 1 → |u| ≤ 1 →
      ‖pk (S.piece (cellIndex S.mesh.tBreaks t) (cellIndex S.mesh.xBreaks u)) (t, u)‖ ≤ K * t := by
  choose B0 hB0 hB using fun ij : ℕ × ℕ => pk_bound (S.piece ij.1 ij.2)
  choose B1 hB10 hB1 using fun ij : ℕ × ℕ => pk_bound (MvPolynomial.pderiv 0 (S.piece ij.1 ij.2))
  set R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1) with hR
  set Bs := ∑ ij ∈ R, (B0 ij + B1 ij) with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun ij _ => by linarith [hB0 ij, hB10 ij]
  have hle : ∀ ij ∈ R, B0 ij ≤ Bs ∧ B1 ij ≤ Bs := by
    intro ij h
    have := Finset.single_le_sum (f := fun ij => B0 ij + B1 ij)
      (fun k _ => by linarith [hB0 k, hB10 k]) h
    refine ⟨?_, ?_⟩ <;> linarith [hB0 ij, hB10 ij]
  set I := (S.mesh.tBreaks.drop 1).dropLast with hI
  have hpos : ∀ e ∈ I, 0 < e := interior_pos hmesh.t_sorted hmesh.t_first
  set fs : Finset ℝ := insert 1 I.toFinset with hfs
  have hne : fs.Nonempty := Finset.insert_nonempty _ _
  set b := fs.min' hne with hb
  have hb0 : 0 < b := by
    rw [hb, Finset.lt_min'_iff]
    intro e he
    rw [hfs, Finset.mem_insert, List.mem_toFinset] at he
    rcases he with h | h
    · rw [h]; norm_num
    · exact hpos e h
  have hlx := two_le_length hmesh.x_first hmesh.x_last
  refine ⟨Bs + Bs / b, by positivity, fun t u ht0 ht1 hu => ?_⟩
  have hta : |t| ≤ 1 := by rw [abs_of_nonneg ht0]; exact ht1
  have hi := cellIndex_le S.mesh.tBreaks t
  have hj := cellIndex_le S.mesh.xBreaks u
  have hmem : (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) ∈ R := by
    rw [hR, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨by omega, by omega⟩
  obtain ⟨l0, l1⟩ := hle _ hmem
  have q0 := hB (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) t u hta hu
  by_cases hall : ∀ e ∈ I, t < e
  · have hci : cellIndex S.mesh.tBreaks t = 0 := by
      unfold cellIndex
      rw [List.filter_eq_nil_iff.2 (fun e he => by simpa using hall e he)]
      rfl
    have hx : cellIndex S.mesh.xBreaks u < cellCount S.mesh.xBreaks := by
      unfold cellCount; omega
    have h0 := horig _ hx
    rw [← hci] at h0
    have r0 := origin_poly _ (fun t' u' ht' hu' => hB1 (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks u) t' u' ht' hu')
      h0 ht0 ht1 hu
    refine r0.trans (mul_le_mul_of_nonneg_right (l1.trans ?_) ht0)
    have : 0 ≤ Bs / b := by positivity
    linarith
  · simp only [not_forall, not_lt, exists_prop] at hall
    obtain ⟨e, he, hte⟩ := hall
    have heb : b ≤ e := Finset.min'_le _ _ (by rw [hfs]; exact Finset.mem_insert_of_mem (List.mem_toFinset.2 he))
    have hbt : b ≤ t := heb.trans hte
    have hA : Bs ≤ Bs / b * t := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hb0]
      exact mul_le_mul_of_nonneg_left hbt hBs0
    refine (q0.trans l0).trans (hA.trans (mul_le_mul_of_nonneg_right ?_ ht0))
    linarith

theorem origin_continuousAt (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) :
    ContinuousAt (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) 0 := by
  obtain ⟨K, hK0, hK⟩ := origin_bound S hS.spline.mesh hS.at_origin
  have hL := hP.L0_pos
  have hbd : ∀ y : Space, ‖((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y‖ ≤ K * chartT P y := by
    intro y
    have ht0 : 0 ≤ chartT P y := by unfold chartT; positivity
    have ht1 : chartT P y ≤ 1 := by
      unfold chartT; rw [div_le_one (by positivity)]; linarith
    have hxa : |(|heightRatio y|)| ≤ 1 := by rw [abs_abs]; exact height_le y
    have q0 := hK _ _ ht0 ht1 hxa
    have hev : S.eval (decide (a = 0)) (chartT P y) (heightRatio y) =
        (if (decide (a = 0) && decide (heightRatio y < 0)) then (-1 : ℂ) else 1) *
          pk (S.piece (cellIndex S.mesh.tBreaks (chartT P y)) (cellIndex S.mesh.xBreaks |heightRatio y|))
            (chartT P y, |heightRatio y|) := by
      simp only [Spline.eval, Spline.evalHalf, pk]
    have hd : ‖((decayFactor P y : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by unfold decayFactor chartS; positivity)]
      unfold decayFactor chartS
      exact Real.rpow_le_one (by linarith) (by linarith) (by linarith [hP.eps_pos])
    have hE : ‖Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
      rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I _
    unfold atomTerm
    rw [norm_mul, norm_mul, norm_mul, hE, one_mul, hev, norm_mul]
    calc ‖((decayFactor P y : ℝ) : ℂ)‖ * (‖((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)‖ *
          (‖(if (decide (a = 0) && decide (heightRatio y < 0)) then (-1 : ℂ) else 1)‖ *
            ‖pk (S.piece (cellIndex S.mesh.tBreaks (chartT P y)) (cellIndex S.mesh.xBreaks |heightRatio y|))
              (chartT P y, |heightRatio y|)‖))
        ≤ 1 * (1 * (1 * (K * chartT P y))) := by
          gcongr
          · exact sqrt_q_le y a
          · exact sign_norm_le _
      _ = K * chartT P y := by ring
  have hc : Continuous (fun y : Space => K * chartT P y) := by
    unfold chartT
    exact continuous_const.mul (continuous_norm.div (continuous_norm.add continuous_const)
      (fun y => by have := norm_nonneg y; positivity))
  have hz : chartT P 0 = 0 := by simp [chartT]
  have h00 : ((decayFactor P 0 : ℝ) : ℂ) * atomTerm P j a M β S 0 = 0 := by
    have := hbd 0
    rw [hz, mul_zero] at this
    exact norm_le_zero_iff.1 this
  have hlim := hc.tendsto (0 : Space)
  simp only [hz, mul_zero] at hlim
  unfold ContinuousAt
  simp only []
  rw [h00, tendsto_zero_iff_norm_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbd hlim

theorem coord_smooth (i : Fin 3) : ContDiff ℝ 1 (fun y : Space => y i) :=
  (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff

theorem plane_eq (y : Space) : (⟨y 0, y 1⟩ : ℂ) = ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I :=
  Complex.ext (by simp) (by simp)

theorem plane_contDiff : ContDiff ℝ 1 (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) := by
  have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y => ((y 0 : ℝ) : ℂ) + ((y 1 : ℝ) : ℂ) * Complex.I :=
    funext plane_eq
  rw [e]
  exact (Complex.ofRealCLM.contDiff.comp (coord_smooth 0)).add
    ((Complex.ofRealCLM.contDiff.comp (coord_smooth 1)).mul contDiff_const)

theorem exp_arg_zpow (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ)) = (w * ((‖w‖⁻¹ : ℝ) : ℂ)) ^ k := by
  have h1 : Complex.I * (((k : ℝ) * Complex.arg w : ℝ) : ℂ) = (k : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [h1, Complex.exp_int_mul]
  congr 1
  have h2 := Complex.norm_mul_exp_arg_mul_I w
  have h3 : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_ne_zero_iff.2 hw)
  rw [Complex.ofReal_inv, eq_mul_inv_iff_mul_eq₀ h3, mul_comm]
  exact h2

theorem zpow_contDiffAt {g : Space → ℂ} {y : Space} (hg : ContDiffAt ℝ 1 g y) (hy : g y ≠ 0) (k : ℤ) :
    ContDiffAt ℝ 1 (fun z => g z ^ k) y := by
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · simpa using hg.pow m
  · simp only [zpow_neg, zpow_natCast]
    exact (hg.pow m).inv (pow_ne_zero _ hy)

theorem offAxis_contDiffAt (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsAtomSpline (decide (a = 0)) S j) {y : Space} (hw : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
  have hy : y ≠ 0 := fun h => hw (by rw [h]; exact Complex.ext (by simp) (by simp))
  have hL := hP.L0_pos
  have hnorm : ContDiffAt ℝ 1 (fun y : Space => ‖y‖) y := contDiffAt_norm ℝ hy
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hT : ContDiffAt ℝ 1 (chartT P) y := by
    have hd : ‖y‖ + P.L0 ≠ 0 := by have := norm_nonneg y; positivity
    exact hnorm.div (hnorm.add contDiffAt_const) hd
  have hH : ContDiffAt ℝ 1 heightRatio y := (coord_smooth 2).contDiffAt.div hnorm hne
  have hD : ContDiffAt ℝ 1 (decayFactor P) y := by
    have hs : chartS P y ≠ 0 := by
      unfold chartS chartT
      have hd : 0 < ‖y‖ + P.L0 := by have := norm_nonneg y; positivity
      rw [sub_ne_zero]
      intro h
      rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
      linarith
    exact (contDiffAt_const.sub hT).rpow_const_of_ne hs
  have hLog : ContDiff ℝ 1 (logPhase P) := by
    unfold logPhase
    refine contDiff_const.mul (ContDiff.log (contDiff_const.add ((contDiff_norm_sq ℝ).div_const _)) ?_)
    intro z
    have := hP.rc_pos
    positivity
  have hq : qOf y ≠ 0 := by
    have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
      simp [sq_abs]
    have hp : 0 < y 0 ^ 2 + y 1 ^ 2 := by
      by_contra h
      rw [not_lt] at h
      have h0 : y 0 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      have h1 : y 1 = 0 := by nlinarith [sq_nonneg (y 0), sq_nonneg (y 1)]
      exact hw (Complex.ext (by simp [h0]) (by simp [h1]))
    unfold qOf heightRatio
    rw [div_pow, e1]
    have hpos : 0 < y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by positivity
    rw [sub_ne_zero]
    intro h
    rw [eq_comm, div_eq_one_iff_eq hpos.ne'] at h
    linarith
  have hQ : ContDiffAt ℝ 1 (fun y => ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (((contDiffAt_const.sub (hH.pow 2)).sqrt hq).pow a)
  have hV : ContDiffAt ℝ 1 (fun y => S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) y :=
    (spline_eval_contDiff S hS.spline le_rfl le_rfl).contDiffAt.comp y (hT.prodMk hH)
  have hE : ContDiffAt ℝ 1 (fun y => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))) y := by
    have hw' : ∀ᶠ z in 𝓝 y, (⟨z 0, z 1⟩ : ℂ) ≠ 0 := plane_contDiff.continuous.continuousAt.eventually_ne hw
    have heq : (fun z : Space => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ)) *
        ((⟨z 0, z 1⟩ : ℂ) * ((‖(⟨z 0, z 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ)) ^ M) =ᶠ[𝓝 y]
        fun z => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z + (M : ℝ) * angleOf z : ℝ) : ℂ)) := by
      filter_upwards [hw'] with z hz
      rw [← exp_arg_zpow _ hz M, ← Complex.exp_add, ← mul_add]
      congr 2
      push_cast
      simp [angleOf]
    refine ContDiffAt.congr_of_eventuallyEq ?_ heq.symm
    have h1 : ContDiffAt ℝ 1 (fun z : Space => Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P z : ℝ) : ℂ))) y :=
      Complex.contDiff_exp.contDiffAt.comp y (contDiffAt_const.mul
        (Complex.ofRealCLM.contDiff.contDiffAt.comp y (contDiffAt_const.mul hLog.contDiffAt)))
    have hu : ContDiffAt ℝ 1 (fun z : Space => (⟨z 0, z 1⟩ : ℂ) * ((‖(⟨z 0, z 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ)) y :=
      plane_contDiff.contDiffAt.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp y
        (((contDiffAt_norm ℝ hw).comp y plane_contDiff.contDiffAt).inv (norm_ne_zero_iff.2 hw)))
    have hu0 : (⟨y 0, y 1⟩ : ℂ) * ((‖(⟨y 0, y 1⟩ : ℂ)‖⁻¹ : ℝ) : ℂ) ≠ 0 :=
      mul_ne_zero hw (by exact_mod_cast (inv_ne_zero (norm_ne_zero_iff.2 hw)))
    exact h1.mul (zpow_contDiffAt hu hu0 M)
  have hA : ContDiffAt ℝ 1 (atomTerm P j a M β S) y := (hE.mul hQ).mul hV
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp y hD).mul hA

theorem sqrt_q_eq {y : Space} (hy : y ≠ 0) : Real.sqrt (qOf y) = ‖(⟨y 0, y 1⟩ : ℂ)‖ / ‖y‖ := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have e1 : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [sq_abs]
  have e2 : ‖(⟨y 0, y 1⟩ : ℂ)‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    show y 0 * y 0 + y 1 * y 1 = _
    ring
  have hq : qOf y = (‖(⟨y 0, y 1⟩ : ℂ)‖ / ‖y‖) ^ 2 := by
    unfold qOf heightRatio
    rw [div_pow, div_pow, e2, eq_div_iff (by positivity), sub_mul, one_mul, div_mul_cancel₀ _ (by positivity)]
    linarith
  rw [hq, Real.sqrt_sq (by positivity)]

theorem phase_plus (w : ℂ) :
    Complex.exp (Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) = w := by
  have e : Complex.I * ((((1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) = (Complex.arg w : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, mul_comm]
  exact Complex.norm_mul_exp_arg_mul_I w

theorem phase_minus (w : ℂ) :
    Complex.exp (Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ)) * (‖w‖ : ℂ) = (starRingEnd ℂ) w := by
  have e : Complex.I * ((((-1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) = (starRingEnd ℂ) ((Complex.arg w : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [e, Complex.exp_conj, ← Complex.conj_ofReal ‖w‖, ← map_mul, mul_comm, Complex.norm_mul_exp_arg_mul_I]

theorem harmonicZero_contDiffAt (P : ChartParams) (hP : IsChartParams P) (a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S 0) (hM : M.natAbs = a) {y : Space} (hy : y ≠ 0) :
    ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P 0 a M β S y) y := by
  have hL := hP.L0_pos
  have hnorm : ContDiffAt ℝ 1 (fun y : Space => ‖y‖) y := contDiffAt_norm ℝ hy
  have hne : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  have hT : ContDiffAt ℝ 1 (chartT P) y := by
    have hd : ‖y‖ + P.L0 ≠ 0 := by have := norm_nonneg y; positivity
    exact hnorm.div (hnorm.add contDiffAt_const) hd
  have hH : ContDiffAt ℝ 1 heightRatio y := (coord_smooth 2).contDiffAt.div hnorm hne
  have hD : ContDiffAt ℝ 1 (decayFactor P) y := by
    have hs : chartS P y ≠ 0 := by
      unfold chartS chartT
      have hd : 0 < ‖y‖ + P.L0 := by have := norm_nonneg y; positivity
      rw [sub_ne_zero]
      intro h
      rw [eq_comm, div_eq_one_iff_eq hd.ne'] at h
      linarith
    exact (contDiffAt_const.sub hT).rpow_const_of_ne hs
  have hV : ContDiffAt ℝ 1 (fun y => S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) y :=
    (spline_eval_contDiff S hS.spline le_rfl le_rfl).contDiffAt.comp y (hT.prodMk hH)
  have hDc : ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y hD
  have hinv : ContDiffAt ℝ 1 (fun y : Space => ((‖y‖⁻¹ : ℝ) : ℂ)) y :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp y (hnorm.inv hne)
  have hev : ∀ᶠ z in 𝓝 y, z ≠ 0 := eventually_ne_nhds hy
  interval_cases a
  · have hM0 : M = 0 := Int.natAbs_eq_zero.1 hM
    subst hM0
    have e : (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P 0 0 0 β S y) =
        fun y => ((decayFactor P y : ℝ) : ℂ) * S.eval (decide (0 = 0)) (chartT P y) (heightRatio y) := by
      funext z
      simp [atomTerm]
    rw [e]
    exact hDc.mul hV
  · have hM' := Int.natAbs_eq M
    rw [hM] at hM'
    rcases hM' with h1 | h1
    · subst h1
      have e : (fun z => ((decayFactor P z : ℝ) : ℂ) * ((⟨z 0, z 1⟩ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) *
          S.eval (decide (1 = 0)) (chartT P z) (heightRatio z))) =ᶠ[𝓝 y]
          fun z => ((decayFactor P z : ℝ) : ℂ) * atomTerm P 0 1 ((1 : ℕ) : ℤ) β S z := by
        filter_upwards [hev] with z hz
        unfold atomTerm
        rw [sqrt_q_eq hz, pow_one]
        have e2 : (((0 : ℕ) : ℝ) * β * logPhase P z + (((1 : ℕ) : ℤ) : ℝ) * angleOf z : ℝ) =
            (((1 : ℤ) : ℝ) * Complex.arg (⟨z 0, z 1⟩ : ℂ) : ℝ) := by
          simp [angleOf]
        rw [e2]
        have e3 : ((‖(⟨z 0, z 1⟩ : ℂ)‖ / ‖z‖ : ℝ) : ℂ) = (‖(⟨z 0, z 1⟩ : ℂ)‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e3, ← mul_assoc (Complex.exp _), phase_plus]
      refine ContDiffAt.congr_of_eventuallyEq ?_ e.symm
      exact hDc.mul ((plane_contDiff.contDiffAt.mul hinv).mul hV)
    · subst h1
      have e : (fun z => ((decayFactor P z : ℝ) : ℂ) * ((starRingEnd ℂ) (⟨z 0, z 1⟩ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) *
          S.eval (decide (1 = 0)) (chartT P z) (heightRatio z))) =ᶠ[𝓝 y]
          fun z => ((decayFactor P z : ℝ) : ℂ) * atomTerm P 0 1 (-((1 : ℕ) : ℤ)) β S z := by
        filter_upwards [hev] with z hz
        unfold atomTerm
        rw [sqrt_q_eq hz, pow_one]
        have e2 : (((0 : ℕ) : ℝ) * β * logPhase P z + ((-((1 : ℕ) : ℤ) : ℤ) : ℝ) * angleOf z : ℝ) =
            (((-1 : ℤ) : ℝ) * Complex.arg (⟨z 0, z 1⟩ : ℂ) : ℝ) := by
          simp [angleOf]
        rw [e2]
        have e3 : ((‖(⟨z 0, z 1⟩ : ℂ)‖ / ‖z‖ : ℝ) : ℂ) = (‖(⟨z 0, z 1⟩ : ℂ)‖ : ℂ) * ((‖z‖⁻¹ : ℝ) : ℂ) := by
          push_cast
          ring
        rw [e3, ← mul_assoc (Complex.exp _), phase_minus]
      refine ContDiffAt.congr_of_eventuallyEq ?_ e.symm
      have hc : ContDiffAt ℝ 1 (fun z : Space => (starRingEnd ℂ) (⟨z 0, z 1⟩ : ℂ)) y :=
        Complex.conjCLE.contDiff.contDiffAt.comp y plane_contDiff.contDiffAt
      exact hDc.mul ((hc.mul hinv).mul hV)

end OpenLeavesInternal

theorem fieldMode_fderiv_localSlope (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : LocallyLipschitz (fderiv ℝ (modeFieldOf P D β n)) := by
  by_cases h0 : n = 0
  · subst h0
    exact modeFieldOf_fderiv_localSlope_mean P hP hD β hn
  · exact modeFieldOf_fderiv_localSlope_wave P hP hD β n hn h0

theorem fieldMode_farBounds (P : ChartParams) (hP : IsChartParams P) (D : FieldData) (hD : IsFieldData P 3 D)
    (β : ℝ) (n : ℤ) (hn : n ∈ D.modes) : ∃ R C : ℝ, ∀ y : Space, R ≤ ‖y‖ →
      ‖fderiv ℝ (modeFieldOf P D β n) y‖ ≤ C * ‖y‖ ^ (-(4 : ℝ)) ∧
        LipschitzOnWith (Real.toNNReal (C * ‖y‖ ^ (-(5 : ℝ)))) (fderiv ℝ (modeFieldOf P D β n))
          (Metric.ball y 1) := by
  obtain ⟨R, C, h⟩ := (OpenLeavesInternal.mode_farDecay P hP D hD β n hn).bounds
  refine ⟨R, C, fun y hy => ?_⟩
  obtain ⟨_, h2, h3⟩ := h y hy
  have e4 : -((3 : ℝ) + 1) = -(4 : ℝ) := by norm_num
  have e5 : -((3 : ℝ) + 2) = -(5 : ℝ) := by norm_num
  rw [e4] at h2
  rw [e5] at h3
  exact ⟨h2, h3⟩

theorem atomScalar_punctured (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    Continuous (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) ∧
      (∀ y : Space, y ≠ 0 → DifferentiableAt ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y) ∧
      ∃ C : ℝ, ∀ y : Space, y ≠ 0 →
        ‖fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
  obtain ⟨C, hC⟩ := atomScalar_gradBound P hP j a M β S ha hS hM
  have hd : ∀ y : Space, y ≠ 0 → ContDiffAt ℝ 1 (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y := by
    intro y hy
    by_cases hw : (⟨y 0, y 1⟩ : ℂ) = 0
    · have h := Complex.ext_iff.1 hw
      simp only [Complex.zero_re, Complex.zero_im] at h
      by_cases hj : j = 0
      · subst hj
        exact OpenLeavesInternal.harmonicZero_contDiffAt P hP a M β S ha hS (hM rfl) hy
      · exact atomScalar_contDiffAt_axis P hP j a M β S ha hS hM hj y hy h.1 h.2
    · exact OpenLeavesInternal.offAxis_contDiffAt P hP j a M β S hS hw
  refine ⟨continuous_iff_continuousAt.2 fun y => ?_, fun y hy => (hd y hy).differentiableAt one_ne_zero,
    ⟨C, fun y _ => hC y⟩⟩
  by_cases h0 : y = 0
  · subst h0
    exact OpenLeavesInternal.origin_continuousAt P hP j a M β S hS
  · exact (hd y h0).continuousAt

theorem atomScalar_weakSecond (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∀ k : Fin 3, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ i : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector i) • fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) y (unitVector k) =
        -∫ y, φ y • fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y (unitVector i) := by
  intro k φ hφ i
  obtain ⟨C, hC⟩ := atomScalar_gradBound P hP j a M β S ha hS hM
  obtain ⟨C2, hC2⟩ := atomScalar_slopeBound P hP j a M β S ha hS hM
  exact OpenLeavesInternal.weak_second _ hC hC2 k φ hφ i

theorem atomScalar_secondBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (ha : a ≤ 1) (hS : IsAtomSpline (decide (a = 0)) S j) (hM : j = 0 → M.natAbs = a) :
    ∃ C : ℝ, ∀ k : Fin 3, ∀ᵐ y ∂volume,
      ‖fderiv ℝ (fun z => fderiv ℝ (fun y => ((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) z (unitVector k)) y‖ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(3 : ℝ))) := by
  obtain ⟨C, hC⟩ := atomScalar_slopeBound P hP j a M β S ha hS hM
  refine ⟨max C 0, fun k => ?_⟩
  filter_upwards [OpenLeavesInternal.ae_ne_zero] with y hy
  exact OpenLeavesInternal.fderiv_le_of_ball hy
    (OpenLeavesInternal.slope_apply (hC y hy) (unitVector k) (OpenLeavesInternal.unit_norm k).le)

theorem fluxScalar_weak (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) : ∀ φ : Space → ℝ, IsTestScalar φ →
      Integrable (fun y => fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y)) ∧
      ∫ y, fderiv ℝ φ y (‖y‖⁻¹ • y) • (((decayFactor P y : ℝ) : ℂ) * atomTerm P j a M β S y) =
        -∫ y, φ y • (‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
          (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) :=
  OpenLeavesInternal.flux_weak P hP j a M β S hS (OpenLeavesInternal.ray_slope P hP j a M β S hS)

theorem fluxScalar_divBound (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline)
    (hS : IsFluxSpline S) :
    AEStronglyMeasurable (fun y : Space => ‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1) volume ∧
    ∃ C : ℝ, ∀ᵐ y ∂volume, ‖‖y‖⁻¹ • deriv (fun s : ℝ => s ^ 2 •
      (((decayFactor P (s • y) : ℝ) : ℂ) * atomTerm P j a M β S (s • y))) 1‖ ≤ C * (‖y‖⁻¹ * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
  OpenLeavesInternal.flux_divBound P hP j a M β S hS

end GivenFields

end CellCert

end Breakdown

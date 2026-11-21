import Breakdown.Cert.CoerciveSmoothPieceEpsBounds

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEps

theorem edgeSum_le_crude (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g g' : ℤ × ℤ → ℝ) (ι : ℤ × ℤ) {M : ℝ}
    (hM : 0 ≤ M) (hg' : ∀ κ, 0 ≤ g' κ) (hXg : ∀ α ∈ h.harmonics, ∀ κ, X α * g κ ≤ M * g' κ) :
    edgeSum h T X g ι ≤ M * ∑ α ∈ h.harmonics, (g' (ι - α) + g' (ι + α)) := by
  classical
  rw [Finset.mul_sum]
  unfold edgeSum
  split_ifs with h1 h2
  · refine Finset.sum_le_sum fun α hα => ?_
    split_ifs
    · exact mul_nonneg hM (add_nonneg (hg' _) (hg' _))
    · nlinarith [hXg α hα (ι - α), hg' (ι + α)]
  · refine Finset.sum_le_sum fun α hα => ?_
    split_ifs
    · exact mul_nonneg hM (add_nonneg (hg' _) (hg' _))
    · nlinarith [hXg α hα (ι + α), hg' (ι - α)]
  · exact Finset.sum_nonneg fun α _ => mul_nonneg hM (add_nonneg (hg' _) (hg' _))

theorem tsum_edge_le (s : Finset (ℤ × ℤ)) (p g : ℤ × ℤ → ℝ) (hp : ∀ ι, 0 ≤ p ι) (hg : ∀ κ, 0 ≤ g κ) :
    ∑' ι, ENNReal.ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤
      (s.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (p ι ^ 2) + 2 * ∑' ι, ENNReal.ofReal (g ι ^ 2)) := by
  have hpt : ∀ ι, ENNReal.ofReal (p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α))) ≤
      ∑ α ∈ s, (ENNReal.ofReal (p ι ^ 2) + ENNReal.ofReal (g (ι - α) ^ 2) + ENNReal.ofReal (g (ι + α) ^ 2)) := by
    intro ι
    have hr : p ι * ∑ α ∈ s, (g (ι - α) + g (ι + α)) ≤
        ∑ α ∈ s, (p ι ^ 2 + g (ι - α) ^ 2 + g (ι + α) ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun α _ => ?_
      nlinarith [sq_nonneg (p ι - g (ι - α)), sq_nonneg (p ι - g (ι + α)), hp ι, hg (ι - α), hg (ι + α)]
    refine le_trans (ENNReal.ofReal_le_ofReal hr) (le_of_eq ?_)
    rw [ENNReal.ofReal_sum_of_nonneg (fun α _ => by positivity)]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_add (by positivity) (by positivity)]
  refine le_trans (ENNReal.tsum_le_tsum hpt) (le_of_eq ?_)
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  have e1 : ∀ α ∈ s, ∑' ι, (ENNReal.ofReal (p ι ^ 2) + ENNReal.ofReal (g (ι - α) ^ 2)
      + ENNReal.ofReal (g (ι + α) ^ 2)) =
      ∑' ι, ENNReal.ofReal (p ι ^ 2) + 2 * ∑' ι, ENNReal.ofReal (g ι ^ 2) := by
    intro α _
    rw [ENNReal.tsum_add, ENNReal.tsum_add]
    have s1 : ∑' ι, ENNReal.ofReal (g (ι - α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) :=
      (Equiv.subRight α).tsum_eq (fun ι => ENNReal.ofReal (g ι ^ 2))
    have s2 : ∑' ι, ENNReal.ofReal (g (ι + α) ^ 2) = ∑' ι, ENNReal.ofReal (g ι ^ 2) :=
      (Equiv.addRight α).tsum_eq (fun ι => ENNReal.ofReal (g ι ^ 2))
    rw [s1, s2, two_mul, add_assoc]
  rw [Finset.sum_congr rfl e1, Finset.sum_const, nsmul_eq_mul]

theorem ofReal_pieceNorm_sq_le (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → ℝ) :
    ENNReal.ofReal (pieceNorm T x ^ 2) ≤ ∑' κ, ENNReal.ofReal (x κ ^ 2) := by
  unfold pieceNorm
  rw [Real.sq_sqrt (tsum_nonneg fun κ => mul_nonneg (Internal.PieceAbsorb.ind_nonneg _) (sq_nonneg _))]
  by_cases hs : Summable fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * x κ ^ 2
  · rw [ENNReal.ofReal_tsum_of_nonneg (fun κ => mul_nonneg (Internal.PieceAbsorb.ind_nonneg _) (sq_nonneg _)) hs]
    refine ENNReal.tsum_le_tsum fun κ => ENNReal.ofReal_le_ofReal ?_
    have h1 : ModeWeights.ind (PieceWeights.inPiece T κ) ≤ 1 := by
      unfold ModeWeights.ind; split_ifs <;> norm_num
    nlinarith [sq_nonneg (x κ)]
  · rw [tsum_eq_zero_of_not_summable hs, ENNReal.ofReal_zero]
    exact zero_le

theorem pieceNorm_mul (T : Set (ℤ × ℤ)) (x : ℤ × ℤ → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    pieceNorm T (fun κ => c * x κ) = c * pieceNorm T x := by
  unfold pieceNorm
  have e : (fun κ => ModeWeights.ind (PieceWeights.inPiece T κ) * (c * x κ) ^ 2) =
      fun κ => c ^ 2 * (ModeWeights.ind (PieceWeights.inPiece T κ) * x κ ^ 2) := by
    funext κ; ring
  rw [e, tsum_mul_left, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

theorem rest_term_le {w a Bw M e1 e2 e3 e4 s1 s2 s3 s4 : ℝ} (hw : 0 ≤ w) (hwB : w ≤ Bw) (ha : 0 ≤ a)
    (hM : 0 ≤ M) (h1 : e1 ≤ M * s1) (h2 : e2 ≤ M * s2) (h3 : e3 ≤ M * s3) (h4 : e4 ≤ M * s4)
    (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hs3 : 0 ≤ s3) (hs4 : 0 ≤ s4) :
    ENNReal.ofReal (w * a * (e1 + e2 + e3 + e4)) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a * s1) + ENNReal.ofReal (a * s2) + ENNReal.ofReal (a * s3)
        + ENNReal.ofReal (a * s4)) := by
  have hBw : 0 ≤ Bw := le_trans hw hwB
  have hle : w * a * (e1 + e2 + e3 + e4) ≤ (Bw * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by
    have hwa : 0 ≤ w * a := mul_nonneg hw ha
    have hs : e1 + e2 + e3 + e4 ≤ M * (s1 + s2 + s3 + s4) := by linarith
    calc w * a * (e1 + e2 + e3 + e4) ≤ w * a * (M * (s1 + s2 + s3 + s4)) := mul_le_mul_of_nonneg_left hs hwa
      _ = (w * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by ring
      _ ≤ (Bw * M) * (a * s1 + a * s2 + a * s3 + a * s4) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hwB hM) ?_
          have := mul_nonneg ha hs1; have := mul_nonneg ha hs2
          have := mul_nonneg ha hs3; have := mul_nonneg ha hs4
          linarith
  refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
  rw [ENNReal.ofReal_mul (mul_nonneg hBw hM), ENNReal.ofReal_add (by positivity) (mul_nonneg ha hs4),
    ENNReal.ofReal_add (by positivity) (mul_nonneg ha hs3),
    ENNReal.ofReal_add (mul_nonneg ha hs1) (mul_nonneg ha hs2)]

theorem pieceNorm_nonneg' (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) : 0 ≤ pieceNorm T g := Real.sqrt_nonneg _

section Pointwise

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (h : HarmonicBounds) (W v : ℝ → Space → Space)
  (β : Fin nE) {D : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
include hD

theorem decay_le_self (y : Space) (k : ℕ) : D / (1 + ‖y‖) ^ k ≤ D :=
  div_le_self (decay_const_nonneg W hD) (one_le_pow₀ (by linarith [norm_nonneg y]))

theorem rest_pointwise {Bw : ℝ} (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (σ : ℝ) (y : Space) :
    ∑' ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y) ≤
      ENNReal.ofReal (Bw * (729 * D)) *
        ((h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))
          + (h.harmonics.card : ℝ≥0∞) * (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
            + 2 * ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2))) := by
  have hD0 := decay_const_nonneg W hD
  set M : ℝ := 729 * D with hMdef
  have hM : 0 ≤ M := by positivity
  have hBw : 0 ≤ Bw := le_trans (hwt0 0) (hwtB 0)
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  set a1 : ℤ × ℤ → ℝ := fun κ => vortAmp (gradField v) κ σ y with ha1
  set a2 : ℤ × ℤ → ℝ := fun κ => vortGradAmp (secondDerivField v) κ σ y with ha2
  set a3 : ℤ × ℤ → ℝ := fun κ => gradAmp (gradField v) κ σ y with ha3
  set a4 : ℤ × ℤ → ℝ := fun κ => velAmp v κ σ y / (1 + ‖y‖) with ha4
  have p1 : ∀ κ, 0 ≤ a1 κ := fun _ => Real.sqrt_nonneg _
  have p2 : ∀ κ, 0 ≤ a2 κ := fun _ => Real.sqrt_nonneg _
  have p3 : ∀ κ, 0 ≤ a3 κ := fun _ => Real.sqrt_nonneg _
  have p4 : ∀ κ, 0 ≤ a4 κ := fun _ => div_nonneg (Real.sqrt_nonneg _) hr.le
  have S : ∀ (g : ℤ × ℤ → ℝ), (∀ κ, 0 ≤ g κ) → ∀ ι, 0 ≤ ∑ α ∈ h.harmonics, (g (ι - α) + g (ι + α)) :=
    fun g hg ι => Finset.sum_nonneg fun α _ => add_nonneg (hg _) (hg _)
  have E1 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
      ≤ M * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p2 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (velAmp_le W hD α σ y) (by have := div_le_self hD0 (by linarith [norm_nonneg y] : (1 : ℝ) ≤ 1 + ‖y‖); rw [hMdef]; linarith)) (p2 κ)
  have E2 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
      ≤ M * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p1 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (gradAmp_le W hD α σ y) (by have := decay_le_self W hD y 2; rw [hMdef]; linarith)) (p1 κ)
  have E3 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y)
      (fun κ => velAmp v κ σ y) ι ≤ M * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)) := fun ι => by
    refine edgeSum_le_crude h _ _ _ _ ι hM p4 fun α _ κ => ?_
    have hu : 0 ≤ velAmp v κ σ y := Real.sqrt_nonneg _
    have h3 : D / (1 + ‖y‖) ^ 3 ≤ D / (1 + ‖y‖) :=
      div_le_div_of_nonneg_left hD0 hr (le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num))
    calc vortGradAmp (secondDerivField W) α σ y * velAmp v κ σ y
        ≤ (27 * (27 * (D / (1 + ‖y‖) ^ 3))) * velAmp v κ σ y :=
          mul_le_mul_of_nonneg_right (vortGradAmp_le W hD α σ y) hu
      _ ≤ (729 * (D / (1 + ‖y‖))) * velAmp v κ σ y := by nlinarith
      _ = M * a4 κ := by rw [hMdef, ha4]; field_simp
  have E4 : ∀ ι, edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι
      ≤ M * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)) := fun ι =>
    edgeSum_le_crude h _ _ _ _ ι hM p3 fun α _ κ => mul_le_mul_of_nonneg_right
      (le_trans (vortAmp_le W hD α σ y) (by have := decay_le_self W hD y 2; rw [hMdef]; linarith)) (p3 κ)
  have hpt : ∀ ι, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y) ≤
      ENNReal.ofReal (Bw * M) * (ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a2 (ι - α) + a2 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a1 (ι - α) + a1 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a4 (ι - α) + a4 (ι + α)))
        + ENNReal.ofReal (a1 ι * ∑ α ∈ h.harmonics, (a3 (ι - α) + a3 (ι + α)))) := by
    intro ι
    have e : -pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y =
        (m.epsP β).wt y * a1 ι * (edgeSum h (m.epsP β).modes (fun α => velAmp W α σ y) a2 ι
          + edgeSum h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y) a1 ι
          + edgeSum h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y) (fun κ => velAmp v κ σ y) ι
          + edgeSum h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y) a3 ι) := by
      unfold pieceEpsRestMode; ring
    rw [e]
    exact rest_term_le (hwt0 y) (hwtB y) (p1 ι) hM (E1 ι) (E2 ι) (E3 ι) (E4 ι)
      (S a2 p2 ι) (S a1 p1 ι) (S a4 p4 ι) (S a3 p3 ι)
  refine le_trans (ENNReal.tsum_le_tsum hpt) ?_
  rw [ENNReal.tsum_mul_left, show Bw * (729 * D) = Bw * M from rfl]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
  exact add_le_add (add_le_add (add_le_add (tsum_edge_le _ a1 a2 p1 p2) (tsum_edge_le _ a1 a1 p1 p1))
    (tsum_edge_le _ a1 a4 p1 p4)) (tsum_edge_le _ a1 a3 p1 p3)

end Pointwise

theorem block_real {c1 c2 c3 c4 K S1 S2 S3 S4 : ℝ} (h1 : 0 ≤ c1) (h2 : 0 ≤ c2) (h3 : 0 ≤ c3) (h4 : 0 ≤ c4)
    (k1 : c1 ≤ K) (k2 : c2 ≤ K) (k3 : c3 ≤ K) (k4 : c4 ≤ K)
    (s1 : 0 ≤ S1) (s2 : 0 ≤ S2) (s3 : 0 ≤ S3) (s4 : 0 ≤ S4) :
    c1 * S2 * S1 + c2 * S1 ^ 2 + c3 * S4 * S1 + c4 * S3 * S1 ≤ 4 * K * (S1 ^ 2 + S2 ^ 2 + S3 ^ 2 + S4 ^ 2) := by
  have hK : 0 ≤ K := le_trans h1 k1
  have pr : ∀ {c x z : ℝ}, 0 ≤ c → c ≤ K → 0 ≤ x → 0 ≤ z → c * x * z ≤ K * (x ^ 2 + z ^ 2) := by
    intro c x z hc hcK hx hz
    have hxz : x * z ≤ x ^ 2 + z ^ 2 := by nlinarith [sq_nonneg (x - z)]
    calc c * x * z = c * (x * z) := by ring
      _ ≤ K * (x * z) := mul_le_mul_of_nonneg_right hcK (mul_nonneg hx hz)
      _ ≤ K * (x ^ 2 + z ^ 2) := mul_le_mul_of_nonneg_left hxz hK
  have t1 := pr h1 k1 s2 s1
  have t3 := pr h3 k3 s4 s1
  have t4 := pr h4 k4 s3 s1
  have t2 : c2 * S1 ^ 2 ≤ K * S1 ^ 2 := mul_le_mul_of_nonneg_right k2 (sq_nonneg _)
  nlinarith [sq_nonneg S1, sq_nonneg S2, sq_nonneg S3, sq_nonneg S4]

theorem block_pointwise {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (W v : ℝ → Space → Space)
    (β : Fin nE) {D Bw Bd Bg : ℝ} (hD : ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y) (hwtB : ∀ y, (m.epsP β).wt y ≤ Bw)
    (hdec : ∀ y, ‖y‖ * (m.epsP β).wt y ≤ Bd) (hgrad : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ Bg)
    (σ : ℝ) (y : Space) :
    ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y) ≤
      ENNReal.ofReal (4 * (Bw * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + Bg + Bw * (27 * D + |(m.epsP β).frame|)
          + 27 * Bw * D)) *
        (∑' ι, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
          + ∑' ι, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
  have hD0 := decay_const_nonneg W hD
  have hr : 0 < 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hr1 : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have hw := hwt0 y
  have hwB := hwtB y
  have hBw : 0 ≤ Bw := le_trans hw hwB
  have hBd : 0 ≤ Bd := le_trans (mul_nonneg (norm_nonneg y) hw) (hdec y)
  have hg0 : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  have hBg : 0 ≤ Bg := le_trans hg0 (hgrad y)
  set T := (m.epsP β).modes with hT
  set a := (m.epsP β).frame with ha
  set wt := (m.epsP β).wt y with hwtdef
  set S1 := pieceNorm T (fun κ => vortAmp (gradField v) κ σ y) with hS1
  set S2 := pieceNorm T (fun κ => vortGradAmp (secondDerivField v) κ σ y) with hS2
  set S3 := pieceNorm T (fun κ => gradAmp (gradField v) κ σ y) with hS3
  set S4 := pieceNorm T (fun κ => velAmp v κ σ y / (1 + ‖y‖)) with hS4
  have hSv : pieceNorm T (fun κ => velAmp v κ σ y) = (1 + ‖y‖) * S4 := by
    rw [hS4, ← pieceNorm_mul T _ hr.le]
    congr 1
    funext κ
    field_simp
  have fss := frameSpeedSup_le W hD a y
  have vs := vortSup_le W hD y
  have vgs := vortGradSup_le W hD hW y
  have fss0 := frameSpeedSup_nonneg W a y
  have vs0 := vortSup_nonneg W y
  have vgs0 := vortGradSup_nonneg W y
  set K0 := Bw * D + (1 / 2 + 2 * |a|) * Bd + Bg + Bw * (27 * D + |a|) + 27 * Bw * D with hK0
  have d2 : D / (1 + ‖y‖) ^ 2 ≤ D := decay_le_self W hD y 2
  have d3 : D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖) ≤ D := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0), mul_le_mul_of_nonneg_left
      (le_self_pow₀ hr1 (by norm_num : (3 : ℕ) ≠ 0)) hD0]
  have e : -pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y =
      (wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y) * S2 * S1
        + wt * ((1 / 2) * vortSup W y + |a|) * S1 ^ 2
        + (wt * vortGradSup W y * (1 + ‖y‖)) * S4 * S1 + wt * vortSup W y * S3 * S1 := by
    unfold pieceEpsBlock
    rw [hSv]
    ring
  have k1 : wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y ≤ K0 := by
    have := hdec y
    have hA : 0 ≤ 1 / 2 + 2 * |a| := by positivity
    have : wt * frameSpeedSup W a y ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := by
      calc wt * frameSpeedSup W a y ≤ wt * (D + (1 / 2 + 2 * |a|) * ‖y‖) := mul_le_mul_of_nonneg_left fss hw
        _ = wt * D + (1 / 2 + 2 * |a|) * (‖y‖ * wt) := by ring
        _ ≤ Bw * D + (1 / 2 + 2 * |a|) * Bd := add_le_add (mul_le_mul_of_nonneg_right hwB hD0)
            (mul_le_mul_of_nonneg_left (hdec y) hA)
    have := hgrad y
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    have : 0 ≤ 27 * Bw * D := by positivity
    rw [hK0]; linarith
  have k2 : wt * ((1 / 2) * vortSup W y + |a|) ≤ K0 := by
    have h27 : (1 / 2) * vortSup W y + |a| ≤ 27 * D + |a| := by nlinarith
    have : wt * ((1 / 2) * vortSup W y + |a|) ≤ Bw * (27 * D + |a|) :=
      mul_le_mul hwB h27 (by positivity) hBw
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ 27 * Bw * D := by positivity
    rw [hK0]; linarith
  have k3 : wt * vortGradSup W y * (1 + ‖y‖) ≤ K0 := by
    have h1 : vortGradSup W y * (1 + ‖y‖) ≤ 27 * D := by
      calc vortGradSup W y * (1 + ‖y‖) ≤ 27 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) :=
            mul_le_mul_of_nonneg_right vgs hr.le
        _ = 27 * (D / (1 + ‖y‖) ^ 3 * (1 + ‖y‖)) := by ring
        _ ≤ 27 * D := by linarith
    have : wt * vortGradSup W y * (1 + ‖y‖) ≤ 27 * Bw * D := by
      calc wt * vortGradSup W y * (1 + ‖y‖) = wt * (vortGradSup W y * (1 + ‖y‖)) := by ring
        _ ≤ Bw * (27 * D) := mul_le_mul hwB h1 (by positivity) hBw
        _ = 27 * Bw * D := by ring
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    rw [hK0]; linarith
  have k4 : wt * vortSup W y ≤ K0 := by
    have h1 : vortSup W y ≤ 27 * D := by nlinarith
    have : wt * vortSup W y ≤ 27 * Bw * D := by
      calc wt * vortSup W y ≤ Bw * (27 * D) := mul_le_mul hwB h1 vs0 hBw
        _ = 27 * Bw * D := by ring
    have : 0 ≤ Bw * D := by positivity
    have : 0 ≤ (1 / 2 + 2 * |a|) * Bd := by positivity
    have : 0 ≤ Bw * (27 * D + |a|) := by positivity
    rw [hK0]; linarith
  have c1 : 0 ≤ wt * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y :=
    add_nonneg (mul_nonneg hw fss0) hg0
  have c2 : 0 ≤ wt * ((1 / 2) * vortSup W y + |a|) := mul_nonneg hw (by positivity)
  have c3 : 0 ≤ wt * vortGradSup W y * (1 + ‖y‖) := by positivity
  have c4 : 0 ≤ wt * vortSup W y := mul_nonneg hw vs0
  have hb := block_real c1 c2 c3 c4 k1 k2 k3 k4 (show 0 ≤ S1 from pieceNorm_nonneg' _ _)
    (show 0 ≤ S2 from pieceNorm_nonneg' _ _) (show 0 ≤ S3 from pieceNorm_nonneg' _ _)
    (show 0 ≤ S4 from pieceNorm_nonneg' _ _)
  rw [e]
  refine le_trans (ENNReal.ofReal_le_ofReal hb) ?_
  have hK00 : 0 ≤ K0 := le_trans c4 k4
  rw [ENNReal.ofReal_mul (mul_nonneg (by norm_num) hK00),
    ENNReal.ofReal_add (add_nonneg (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3)) (sq_nonneg S4),
    ENNReal.ofReal_add (add_nonneg (sq_nonneg S1) (sq_nonneg S2)) (sq_nonneg S3),
    ENNReal.ofReal_add (sq_nonneg S1) (sq_nonneg S2)]
  refine mul_le_mul_of_nonneg_left ?_ zero_le
  exact add_le_add (add_le_add (add_le_add (ofReal_pieceNorm_sq_le T _) (ofReal_pieceNorm_sq_le T _))
    (ofReal_pieceNorm_sq_le T _)) (ofReal_pieceNorm_sq_le T _)

end Internal.SmoothPieceEps

end Coercive

end Breakdown

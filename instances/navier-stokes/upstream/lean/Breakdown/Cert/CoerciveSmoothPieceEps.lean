import Breakdown.Cert.CoerciveSmoothPieceEpsCoreModes
import Breakdown.Cert.CoerciveSmoothPieceEpsFrequency

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceEps

theorem ind_nonneg (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem edgeSum_nonneg (h : HarmonicBounds) (T : Set (ℤ × ℤ)) (X g : ℤ × ℤ → ℝ) (ι : ℤ × ℤ)
    (hX : ∀ α, 0 ≤ X α) (hg : ∀ κ, 0 ≤ g κ) : 0 ≤ edgeSum h T X g ι := by
  classical
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun α _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX α) (hg _)]
  · exact Finset.sum_nonneg fun α _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX α) (hg _)]
  · exact le_rfl

theorem pieceNorm_nonneg (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) : 0 ≤ pieceNorm T g := Real.sqrt_nonneg _

section Signs

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : Fin nE)

theorem pos_nonneg (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    0 ≤ pieceEpsPos m P G β ι σ y := by
  unfold pieceEpsPos
  exact mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (hwt y)) (abs_nonneg _)) (sq_nonneg _)

theorem rest_nonpos (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceEpsRestMode m h W v G H β ι σ y ≤ 0 := by
  unfold pieceEpsRestMode
  have e1 := edgeSum_nonneg h (m.epsP β).modes (fun α => velAmp W α σ y) (fun κ => vortGradAmp H κ σ y) ι
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e2 := edgeSum_nonneg h (m.epsP β).modes (fun α => gradAmp (gradField W) α σ y)
    (fun κ => vortAmp G κ σ y) ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e3 := edgeSum_nonneg h (m.epsP β).modes (fun α => vortGradAmp (secondDerivField W) α σ y)
    (fun κ => velAmp v κ σ y) ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have e4 := edgeSum_nonneg h (m.epsP β).modes (fun α => vortAmp (gradField W) α σ y)
    (fun κ => gradAmp G κ σ y) ι (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
  have hv : 0 ≤ vortAmp G ι σ y := Real.sqrt_nonneg _
  have := mul_nonneg (mul_nonneg (hwt y) hv) (add_nonneg (add_nonneg (add_nonneg e1 e2) e3) e4)
  linarith

theorem block_nonpos (hwt : ∀ y, 0 ≤ (m.epsP β).wt y) (σ : ℝ) (y : Space) :
    pieceEpsBlock m W v G H β σ y ≤ 0 := by
  unfold pieceEpsBlock
  have n1 := pieceNorm_nonneg (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
  have n2 := pieceNorm_nonneg (m.epsP β).modes (fun κ => vortAmp G κ σ y)
  have n3 := pieceNorm_nonneg (m.epsP β).modes (fun κ => velAmp v κ σ y)
  have n4 := pieceNorm_nonneg (m.epsP β).modes (fun κ => gradAmp G κ σ y)
  have s1 := frameSpeedSup_nonneg W (m.epsP β).frame y
  have s2 := vortSup_nonneg W y
  have s3 := vortGradSup_nonneg W y
  have g0 : 0 ≤ PieceWeights.wtGrad (m.epsP β).wt y := norm_nonneg _
  have w0 := hwt y
  have t1 : 0 ≤ ((m.epsP β).wt y * frameSpeedSup W (m.epsP β).frame y + PieceWeights.wtGrad (m.epsP β).wt y)
      * pieceNorm (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg w0 s1) g0) n1) n2
  have t2 : 0 ≤ (m.epsP β).wt y * ((1 / 2) * vortSup W y + |(m.epsP β).frame|)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) ^ 2 :=
    mul_nonneg (mul_nonneg w0 (add_nonneg (mul_nonneg (by norm_num) s2) (abs_nonneg _))) (sq_nonneg _)
  have t3 : 0 ≤ (m.epsP β).wt y * vortGradSup W y * pieceNorm (m.epsP β).modes (fun κ => velAmp v κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (mul_nonneg w0 s3) n3) n2
  have t4 : 0 ≤ (m.epsP β).wt y * vortSup W y * pieceNorm (m.epsP β).modes (fun κ => gradAmp G κ σ y)
      * pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y) :=
    mul_nonneg (mul_nonneg (mul_nonneg w0 s2) n4) n2
  linarith

end Signs

theorem ennreal_step {A N : ℝ≥0∞} {X : ℝ} (hA : A < ⊤) (hN : N < ⊤) (hI : A.toReal ≤ X + N.toReal) :
    A + ENNReal.ofReal (-X) ≤ ENNReal.ofReal X + N := by
  rcases le_or_gt 0 X with hX | hX
  · rw [ENNReal.ofReal_of_nonpos (by linarith : -X ≤ 0), add_zero]
    calc A = ENNReal.ofReal A.toReal := (ENNReal.ofReal_toReal hA.ne).symm
      _ ≤ ENNReal.ofReal (X + N.toReal) := ENNReal.ofReal_le_ofReal hI
      _ = ENNReal.ofReal X + ENNReal.ofReal N.toReal := ENNReal.ofReal_add hX ENNReal.toReal_nonneg
      _ = ENNReal.ofReal X + N := by rw [ENNReal.ofReal_toReal hN.ne]
  · rw [ENNReal.ofReal_of_nonpos hX.le, zero_add]
    calc A + ENNReal.ofReal (-X) = ENNReal.ofReal A.toReal + ENNReal.ofReal (-X) := by
          rw [ENNReal.ofReal_toReal hA.ne]
      _ = ENNReal.ofReal (A.toReal + -X) := (ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)).symm
      _ ≤ ENNReal.ofReal N.toReal := ENNReal.ofReal_le_ofReal (by linarith)
      _ = N := ENNReal.ofReal_toReal hN.ne

theorem split_of_signs {X : ℝ} {Pos Rest : ℝ → Space → ℤ × ℤ → ℝ} {Blk : ℝ → Space → ℝ}
    (hR : ∀ σ y ι, Rest σ y ι ≤ 0) (hB : ∀ σ y, Blk σ y ≤ 0)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)) < ⊤)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))) < ⊤)
    (hI : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (Pos σ y ι)).toReal ≤
      X + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-Rest σ y ι)) + ENNReal.ofReal (-Blk σ y))).toReal) :
    IsSplitLowerBound X Pos Rest Blk (fun _ _ => 0) := by
  unfold IsSplitLowerBound
  refine ⟨hN, ?_⟩
  have eR : ∀ σ y ι, ENNReal.ofReal (Rest σ y ι) = 0 := fun σ y ι => ENNReal.ofReal_of_nonpos (hR σ y ι)
  have eB : ∀ σ y, ENNReal.ofReal (Blk σ y) = 0 := fun σ y => ENNReal.ofReal_of_nonpos (hB σ y)
  simp only [eR, eB, tsum_zero, add_zero, neg_zero, ENNReal.ofReal_zero]
  exact ennreal_step hA hN hI

private theorem time_series_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (P : ℝ) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
  exact Internal.SmoothPieceEpsFrequency.time_series_finite hPars hDer hSP P v hv

private theorem angular_series_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds)
    (hRotM : ModeRotationHolds) (hSP : SmoothPerturbationIsPerturbationHolds) (P : ℝ) (v : ℝ → Space → Space)
    (hv : IsSmoothPerturbation P v) (wt : Space → ℝ) (hwt0 : ∀ y, 0 ≤ wt y) (hwtc : Continuous wt)
    (hwd : ∃ B, ∀ y, ‖y‖ * wt y ≤ B) (hwb : ∃ B, ∀ y, wt y ≤ B) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
  exact Internal.SmoothPieceEpsFrequency.angular_series_finite hPars hDer hRotM hSP P v hv wt hwt0 hwtc hwd hwb

private theorem frequency_series_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)) < ⊤ := by
  have hP : 0 < P := hm.period_pos
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  obtain ⟨K, hK⟩ := hm.eps_increment β
  have hwtc : Continuous (m.epsP β).wt := hK.continuous
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  set a := (m.epsP β).frame
  set c : ℝ := epsSup * (2 * Real.pi / P) with hc
  have hc0 : 0 ≤ c := mul_nonneg (le_trans (hwt0 0) (hwtB 0)) (by positivity)
  have hpt : ∀ σ y ι, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y) ≤
      ENNReal.ofReal c * ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2)
        + ENNReal.ofReal c * ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ENNReal.ofReal |a| * ENNReal.ofReal ((m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2) := by
    intro σ y ι
    have hx := sq_nonneg (vortAmp (gradField v) ι σ y)
    have hw := hwt0 y
    have hwB := hwtB y
    have hi0 : 0 ≤ ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) := ind_nonneg _
    have hi1 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) ≤ 1 := by
      unfold ModeWeights.ind; split_ifs <;> norm_num
    have hf : |PieceWeights.frameFreq P a ι| ≤ 2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)| := by
      unfold PieceWeights.frameFreq
      refine le_trans (abs_add_le _ _) ?_
      rw [abs_mul, show 2 * Real.pi * (ι.1 : ℝ) / P = 2 * Real.pi / P * ι.1 by ring, abs_mul,
        abs_of_pos (by positivity : 0 < 2 * Real.pi / P)]
    have hn : |(ι.1 : ℝ)| ≤ (ι.1 : ℝ) ^ 2 + 1 := by
      nlinarith [abs_nonneg (ι.1 : ℝ), sq_abs (ι.1 : ℝ), sq_nonneg (|(ι.1 : ℝ)| - 1)]
    have hle : pieceEpsPos m P (gradField v) β ι σ y ≤
        c * ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2) + c * vortAmp (gradField v) ι σ y ^ 2
          + |a| * ((m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2) := by
      unfold pieceEpsPos
      set x := vortAmp (gradField v) ι σ y ^ 2
      set wt := (m.epsP β).wt y
      have h1 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt
          * |PieceWeights.frameFreq P a ι| * x ≤ wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) * x := by
        have := mul_le_mul (mul_le_of_le_one_left hw hi1 |>.trans le_rfl) hf (abs_nonneg _) hw
        have h2 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt ≤ wt :=
          mul_le_of_le_one_left hw hi1
        have h3 : ModeWeights.ind (PieceWeights.inPiece (m.epsP β).modes ι) * wt * |PieceWeights.frameFreq P a ι|
            ≤ wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) :=
          mul_le_mul h2 hf (abs_nonneg _) hw
        exact mul_le_mul_of_nonneg_right h3 hx
      have hpi : 0 ≤ 2 * Real.pi / P := by positivity
      have h4 : wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x ≤ c * ((ι.1 : ℝ) ^ 2 * x) + c * x := by
        have h5 : wt * (2 * Real.pi / P) ≤ c := mul_le_mul_of_nonneg_right hwB hpi
        calc wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x = (wt * (2 * Real.pi / P)) * (|(ι.1 : ℝ)| * x) := by ring
          _ ≤ c * (((ι.1 : ℝ) ^ 2 + 1) * x) := mul_le_mul h5 (mul_le_mul_of_nonneg_right hn hx)
              (mul_nonneg (abs_nonneg _) hx) hc0
          _ = c * ((ι.1 : ℝ) ^ 2 * x) + c * x := by ring
      have e : wt * (2 * Real.pi / P * |(ι.1 : ℝ)| + |a| * |(ι.2 : ℝ)|) * x
          = wt * (2 * Real.pi / P * |(ι.1 : ℝ)|) * x + |a| * (wt * |(ι.2 : ℝ)| * x) := by ring
      linarith
    refine le_trans (ENNReal.ofReal_le_ofReal hle) (le_of_eq ?_)
    have q1 : 0 ≤ (ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι σ y ^ 2 := mul_nonneg (sq_nonneg _) hx
    have q3 : 0 ≤ (m.epsP β).wt y * |(ι.2 : ℝ)| * vortAmp (gradField v) ι σ y ^ 2 :=
      mul_nonneg (mul_nonneg hw (abs_nonneg _)) hx
    rw [ENNReal.ofReal_add (add_nonneg (mul_nonneg hc0 q1) (mul_nonneg hc0 hx)) (mul_nonneg (abs_nonneg _) q3),
      ENNReal.ofReal_add (mul_nonneg hc0 q1) (mul_nonneg hc0 hx), ENNReal.ofReal_mul hc0, ENNReal.ofReal_mul hc0,
      ENNReal.ofReal_mul (abs_nonneg _)]
  have hp := hSP P v hv
  have hG := hp.measurable_gradient
  have m1 : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      (((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2).const_mul _)
  have m2 : ∀ ι, AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable ((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2)
  have hwm : AEMeasurable (fun z : ℝ × Space => (m.epsP β).wt z.2) volume :=
    (hwtc.comp continuous_snd).aemeasurable
  have m3 : ∀ ι, AEMeasurable (fun z : ℝ × Space =>
      ENNReal.ofReal ((m.epsP β).wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2)) volume :=
    fun ι => ENNReal.measurable_ofReal.comp_aemeasurable
      ((hwm.mul_const _).mul ((Internal.PieceAbsorb.aem_vortAmp hG ι).pow_const 2))
  have T1 := time_series_finite hPars hDer hSP P v hv
  have T3 := angular_series_finite hPars hDer hRotM hSP P v hv (m.epsP β).wt hwt0 hwtc ⟨Bd, hBd β⟩
    ⟨epsSup, hwtB⟩
  have T2 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ,
      ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) (amplitudeSeries_finite hPars hSP P v hv)
    exact le_trans le_self_add (le_trans le_self_add le_self_add)
  have key := iterated_add3_lt_top (f1 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((ι.1 : ℝ) ^ 2 * vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (f2 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (f3 := fun z : ℝ × Space => ∑' ι : ℤ × ℤ,
      ENNReal.ofReal ((m.epsP β).wt z.2 * |(ι.2 : ℝ)| * vortAmp (gradField v) ι z.1 z.2 ^ 2))
    (AEMeasurable.tsum m1) (AEMeasurable.tsum m2) (AEMeasurable.tsum m3)
    (c1 := ENNReal.ofReal c) (c2 := ENNReal.ofReal c) (c3 := ENNReal.ofReal |a|)
    ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top T1 T2 T3
  refine lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y => ?_) key
  refine le_trans (ENNReal.tsum_le_tsum (hpt σ y)) (le_of_eq ?_)
  rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

private theorem negative_parts_finite (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y))) < ⊤ := by
  obtain ⟨D, hD⟩ := hWdecay
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  have hwt0 : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hwtB : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)) (hm.eps_sum_le y)
  have hgB : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup := fun y =>
    le_trans (Finset.single_le_sum (f := fun b => PieceWeights.wtGrad (m.epsP b).wt y)
      (fun b _ => norm_nonneg _) (Finset.mem_univ β)) (hm.eps_grad_sum_le y)
  set K : ℝ≥0∞ := ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12)
    + ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + epsGradSup
      + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) with hK
  have hKt : K ≠ ⊤ := by
    rw [hK]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (by norm_num)), ENNReal.ofReal_ne_top⟩
  have hpt : ∀ σ y, ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y)) ≤
      K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) := by
    intro σ y
    have hR := rest_pointwise m h W v β hD hwt0 hwtB σ y
    have hB := block_pointwise m W v β hD hW hwt0 hwtB (fun y => hBd β y) hgB σ y
    set A1 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
    set A2 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
    set A3 := ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
    set A4 := ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)
    have l1 : A1 ≤ A1 + A2 + A3 + A4 := by
      calc A1 ≤ A1 + A2 := le_self_add
        _ ≤ A1 + A2 + A3 := le_self_add
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l2 : A2 ≤ A1 + A2 + A3 + A4 := by
      calc A2 ≤ A1 + A2 := le_add_self
        _ ≤ A1 + A2 + A3 := le_self_add
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l3 : A3 ≤ A1 + A2 + A3 + A4 := by
      calc A3 ≤ A1 + A2 + A3 := le_add_self
        _ ≤ A1 + A2 + A3 + A4 := le_self_add
    have l4 : A4 ≤ A1 + A2 + A3 + A4 := le_add_self
    set A := A1 + A2 + A3 + A4 with hA
    have hR' : ∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y)
        ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A := by
      refine le_trans hR ?_
      calc ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A2)
            + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A1) + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A4)
            + (h.harmonics.card : ℝ≥0∞) * (A1 + 2 * A3))
          ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * (A + 2 * A)
            + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A) + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A)
            + (h.harmonics.card : ℝ≥0∞) * (A + 2 * A)) := by gcongr
        _ = ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A := by ring
    calc _ ≤ ENNReal.ofReal (epsSup * (729 * D)) * ((h.harmonics.card : ℝ≥0∞) * 12) * A
          + ENNReal.ofReal (4 * (epsSup * D + (1 / 2 + 2 * |(m.epsP β).frame|) * Bd + epsGradSup
            + epsSup * (27 * D + |(m.epsP β).frame|) + 27 * epsSup * D)) * A := add_le_add hR' hB
      _ = K * A := by rw [hK]; ring
  calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, K * (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2)) :=
        lintegral_mono fun σ => lintegral_mono fun y => hpt σ y
    _ = K * (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      (∑' ι : ℤ × ℤ, ENNReal.ofReal (vortAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (vortGradAmp (secondDerivField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal (gradAmp (gradField v) ι σ y ^ 2)
        + ∑' ι : ℤ × ℤ, ENNReal.ofReal ((velAmp v ι σ y / (1 + ‖y‖)) ^ 2))) := by
        simp_rw [lintegral_const_mul' K _ hKt]
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.2 hKt) (amplitudeSeries_finite hPars hSP P v hv)

private theorem core_inequality (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B) (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (β : Fin nE)
    (hA : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)) < ⊤) (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y))) < ⊤) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι : ℤ × ℤ, ENNReal.ofReal (pieceEpsPos m P (gradField v) β ι σ y)).toReal ≤
      epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v (smoothRight P W v) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι : ℤ × ℤ, ENNReal.ofReal (-pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y))
        + ENNReal.ofReal (-pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y))).toReal :=
  Internal.SmoothPieceEpsCore.core_inequality_of_setting hPars hDer hRotM hSP hSsp
    ⟨hm, hW, hWp, hWdiv, hWdecay, hwb, hv⟩ β hA hN

end Internal.SmoothPieceEps

open Internal.SmoothPieceEps in
theorem pieceEpsEstimateSmoothHolds_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRotM : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds) (hSsp : WeightedSumSecondPartialsPairingHolds) :
    PieceEpsEstimateSmoothHolds := by
  intro C nE nM m P h w W w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb v hv β
  have hwt : ∀ y, 0 ≤ (m.epsP β).wt y := hm.eps_wt_nonneg β
  have hA := frequency_series_finite hPars hDer hRotM hSP hSsp m P h w W hm hW hWp hWdiv hWdecay hwb v hv β
  have hN := negative_parts_finite hPars hDer hRotM hSP hSsp m P h w W hm hW hWp hWdiv hWdecay hwb v hv β
  exact split_of_signs (fun σ y ι => rest_nonpos m h W v (gradField v) (secondDerivField v) β hwt ι σ y)
    (fun σ y => block_nonpos m W v (gradField v) (secondDerivField v) β hwt σ y) hA hN
    (core_inequality hPars hDer hRotM hSP hSsp m P h w W hm hW hWp hWdiv hWdecay hwb v hv β hA hN)

end Coercive

end Breakdown

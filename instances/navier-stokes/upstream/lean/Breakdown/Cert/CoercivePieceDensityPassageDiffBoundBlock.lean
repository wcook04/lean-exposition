import Breakdown.Cert.CoercivePieceDensityPassageDiffBoundEps

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PiecePassageDiffBoundBlock

open DensityPassageRestBound PiecePassageDiffBoundMu

theorem sqrt_tsum_sub_le {f g : ℤ × ℤ → ℝ} (hf : Summable fun i => f i ^ 2)
    (hg : Summable fun i => g i ^ 2) :
    |Real.sqrt (∑' i, f i ^ 2) - Real.sqrt (∑' i, g i ^ 2)| ≤ Real.sqrt (∑' i, (f i - g i) ^ 2) := by
  have hp : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have mem : ∀ {a : ℤ × ℤ → ℝ}, Summable (fun i => a i ^ 2) → Memℓp a 2 := fun {a} ha => by
    refine (memℓp_gen_iff hp).2 ?_
    simpa [Real.norm_eq_abs, sq_abs] using ha
  have nrm : ∀ (a : ℤ × ℤ → ℝ) (ha : Summable (fun i => a i ^ 2)),
      ‖(⟨a, mem ha⟩ : lp (fun _ : ℤ × ℤ => ℝ) 2)‖ = Real.sqrt (∑' i, a i ^ 2) := fun a ha => by
    rw [lp.norm_eq_tsum_rpow hp, Real.sqrt_eq_rpow]
    simp [Real.norm_eq_abs, sq_abs]
  have hfg : Summable (fun i => (f i - g i) ^ 2) := by
    have := (mem hf).sub (mem hg)
    have h2 := (memℓp_gen_iff hp).1 this
    simpa [Real.norm_eq_abs, sq_abs] using h2
  have e := abs_norm_sub_norm_le (⟨f, mem hf⟩ : lp (fun _ : ℤ × ℤ => ℝ) 2) ⟨g, mem hg⟩
  rw [nrm f hf, nrm g hg] at e
  have e2 : (⟨f, mem hf⟩ : lp (fun _ : ℤ × ℤ => ℝ) 2) - ⟨g, mem hg⟩ = ⟨fun i => f i - g i, mem hfg⟩ := by
    ext i
    simp
    rfl
  rw [e2, nrm _ hfg] at e
  exact e

theorem pieceNorm_eq (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) :
    pieceNorm T g = Real.sqrt (∑' κ, (ModeWeights.ind (PieceWeights.inPiece T κ) * g κ) ^ 2) := by
  unfold pieceNorm
  congr 1
  refine tsum_congr fun κ => ?_
  unfold ModeWeights.ind
  split_ifs <;> ring

theorem pieceNorm_scale (T : Set (ℤ × ℤ)) (g : ℤ × ℤ → ℝ) {c : ℝ} (hc : 0 < c) :
    pieceNorm T g = c * pieceNorm T (fun κ => g κ / c) := by
  unfold pieceNorm
  have e : ∀ κ, ModeWeights.ind (PieceWeights.inPiece T κ) * (g κ / c) ^ 2
      = ModeWeights.ind (PieceWeights.inPiece T κ) * g κ ^ 2 / c ^ 2 := fun κ => by
    field_simp
  simp only [e]
  rw [tsum_div_const, Real.sqrt_div' _ (by positivity : (0 : ℝ) ≤ c ^ 2), Real.sqrt_sq hc.le]
  field_simp

theorem ind_mul_sq_le (p : Prop) (x : ℝ) : (ModeWeights.ind p * x) ^ 2 ≤ x ^ 2 := by
  unfold ModeWeights.ind
  split_ifs <;> simp <;> positivity

theorem summable_of_ofReal {f : ℤ × ℤ → ℝ} (hf0 : ∀ κ, 0 ≤ f κ)
    (hf : ∑' κ, ENNReal.ofReal (f κ) ≠ ⊤) : Summable f := by
  have := ENNReal.summable_toReal hf
  simpa [ENNReal.toReal_ofReal (hf0 _)] using this

theorem tsum_origin (a : ℝ) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (|if ι = 0 then a else 0|) = ENNReal.ofReal |a| := by
  have e : ∀ ι : ℤ × ℤ, ENNReal.ofReal (|if ι = 0 then a else 0|) = if ι = 0 then ENNReal.ofReal |a| else 0 :=
    fun ι => by
      by_cases h0 : ι = 0
      · simp only [if_pos h0]
      · simp only [if_neg h0, abs_zero, ENNReal.ofReal_zero]
  simp only [e]
  exact tsum_ite_eq 0 _

theorem tsum_origin_sub (a b : ℝ) :
    ∑' ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      ENNReal.ofReal |a - b| := by
  have e : ∀ ι : ℤ × ℤ, ENNReal.ofReal (|(if ι = 0 then a else 0) - (if ι = 0 then b else 0)|) =
      if ι = 0 then ENNReal.ofReal |a - b| else 0 := fun ι => by
    by_cases h0 : ι = 0
    · simp only [if_pos h0]
    · simp only [if_neg h0, sub_zero, abs_zero, ENNReal.ofReal_zero]
  simp only [e]
  exact tsum_ite_eq 0 _

theorem amp_norm_facts {A : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ} (hA : IsAmp A)
    (T : Set (ℤ × ℤ)) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (hS : Summable fun κ => ampSqAt v G H κ σ y) :
    Summable (fun κ => (ModeWeights.ind (PieceWeights.inPiece T κ) * A v G H κ σ y) ^ 2) ∧
      pieceNorm T (fun κ => A v G H κ σ y) ^ 2 ≤ ∑' κ, ampSqAt v G H κ σ y ∧
      0 ≤ pieceNorm T (fun κ => A v G H κ σ y) := by
  have hle : ∀ κ, (ModeWeights.ind (PieceWeights.inPiece T κ) * A v G H κ σ y) ^ 2 ≤ ampSqAt v G H κ σ y :=
    fun κ => (ind_mul_sq_le _ _).trans (hA v G H κ σ y).2.1
  have hs : Summable (fun κ => (ModeWeights.ind (PieceWeights.inPiece T κ) * A v G H κ σ y) ^ 2) :=
    Summable.of_nonneg_of_le (fun κ => sq_nonneg _) hle hS
  refine ⟨hs, ?_, Real.sqrt_nonneg _⟩
  rw [pieceNorm_eq, Real.sq_sqrt (tsum_nonneg fun κ => sq_nonneg _)]
  exact hs.tsum_le_tsum hle hS

theorem block_prod_bound {A B : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
    (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}
    (hA : IsAmp A) (hB : IsAmp B) (T : Set (ℤ × ℤ)) (c : ℝ → Space → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hc : ∀ σ y, |c σ y| ≤ M) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => if ι = 0 then c σ y * (pieceNorm T (fun κ => A v G H κ σ y)
      * pieceNorm T (fun κ => B v G H κ σ y)) else 0) v G H := by
  have hK : 0 < 2 * M + 1 := by positivity
  have hKp : ENNReal.ofReal (2 * M + 1) ≠ 0 := (ENNReal.ofReal_pos.2 hK).ne'
  have amp0 : ∀ v G H κ σ y, 0 ≤ ampSqAt v G H κ σ y := fun v G H κ σ y =>
    (sq_nonneg _).trans (hA v G H κ σ y).2.1
  have diff0 : ∀ u Gu Hu κ σ y, 0 ≤ diffSqAt u Gu Hu v G H κ σ y := fun u Gu Hu κ σ y =>
    (sq_nonneg _).trans ((hA v G H κ σ y).2.2 u Gu Hu)
  refine ⟨2 * M + 1, hK.le, fun σ y => ?_, fun t ht u Gu Hu σ y => ?_⟩
  · beta_reduce
    rw [tsum_origin]
    by_cases hS : ampTotal v G H σ y = ⊤
    · rw [hS, ENNReal.mul_top hKp]
      exact le_top
    · have hs := summable_of_ofReal (amp0 v G H · σ y) hS
      obtain ⟨-, pa2, pa0⟩ := amp_norm_facts hA T v G H σ y hs
      obtain ⟨-, pb2, pb0⟩ := amp_norm_facts hB T v G H σ y hs
      have hS0 : 0 ≤ ∑' κ, ampSqAt v G H κ σ y := tsum_nonneg fun κ => amp0 v G H κ σ y
      rw [ampTotal_eq, ← ENNReal.ofReal_tsum_of_nonneg (amp0 v G H · σ y) hs, ← ENNReal.ofReal_mul hK.le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul, abs_of_nonneg (mul_nonneg pa0 pb0)]
      have hpp : pieceNorm T (fun κ => A v G H κ σ y) * pieceNorm T (fun κ => B v G H κ σ y)
          ≤ ∑' κ, ampSqAt v G H κ σ y := by
        nlinarith [sq_nonneg (pieceNorm T (fun κ => A v G H κ σ y) - pieceNorm T (fun κ => B v G H κ σ y))]
      calc |c σ y| * (pieceNorm T (fun κ => A v G H κ σ y) * pieceNorm T (fun κ => B v G H κ σ y))
          ≤ M * ∑' κ, ampSqAt v G H κ σ y := mul_le_mul (hc σ y) hpp (mul_nonneg pa0 pb0) hM
        _ ≤ (2 * M + 1) * ∑' κ, ampSqAt v G H κ σ y := mul_le_mul_of_nonneg_right (by linarith) hS0
  · beta_reduce
    rw [tsum_origin_sub]
    have hK1 : 0 < (2 * M + 1) * (1 + 1 / t) := by positivity
    have hK2 : 0 < (2 * M + 1) * t := by positivity
    by_cases hD : diffTotal u Gu Hu v G H σ y = ⊤
    · rw [hD, ENNReal.mul_top (ENNReal.ofReal_pos.2 hK1).ne']
      exact le_top.trans le_self_add
    by_cases hS : ampTotal v G H σ y = ⊤
    · rw [hS, ENNReal.mul_top (ENNReal.ofReal_pos.2 hK2).ne']
      exact le_top.trans le_add_self
    have hs := summable_of_ofReal (amp0 v G H · σ y) hS
    have hd := summable_of_ofReal (diff0 u Gu Hu · σ y) hD
    have hSd0 : 0 ≤ ∑' κ, diffSqAt u Gu Hu v G H κ σ y := tsum_nonneg fun κ => diff0 u Gu Hu κ σ y
    have hS0 : 0 ≤ ∑' κ, ampSqAt v G H κ σ y := tsum_nonneg fun κ => amp0 v G H κ σ y
    rw [diffTotal_eq, ampTotal_eq, ← ENNReal.ofReal_tsum_of_nonneg (diff0 u Gu Hu · σ y) hd,
      ← ENNReal.ofReal_tsum_of_nonneg (amp0 v G H · σ y) hs]
    refine ennreal_step hK1.le hK2.le hSd0 hS0 ?_
    have famu : ∀ {X : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
        (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}, IsAmp X →
        Summable (fun κ => (ModeWeights.ind (PieceWeights.inPiece T κ) * X u Gu Hu κ σ y) ^ 2) := by
      intro X hX
      refine Summable.of_nonneg_of_le (fun κ => sq_nonneg _) (fun κ => ?_) ((hd.mul_left 2).add (hs.mul_left 2))
      have h1 := (hX v G H κ σ y).2.2 u Gu Hu
      have h2 := (hX v G H κ σ y).2.1
      have h3 := ind_mul_sq_le (PieceWeights.inPiece T κ) (X u Gu Hu κ σ y)
      nlinarith [sq_nonneg (X u Gu Hu κ σ y - 2 * X v G H κ σ y)]
    have normTriangle : ∀ {X : (ℝ → Space → Space) → (ℝ → Space → (Space →L[ℝ] Space)) →
        (ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) → ℤ × ℤ → ℝ → Space → ℝ}, IsAmp X →
        |pieceNorm T (fun κ => X u Gu Hu κ σ y) - pieceNorm T (fun κ => X v G H κ σ y)|
          ≤ Real.sqrt (∑' κ, diffSqAt u Gu Hu v G H κ σ y) := by
      intro X hX
      have hle : ∀ κ, (ModeWeights.ind (PieceWeights.inPiece T κ) * X u Gu Hu κ σ y
          - ModeWeights.ind (PieceWeights.inPiece T κ) * X v G H κ σ y) ^ 2 ≤ diffSqAt u Gu Hu v G H κ σ y :=
        fun κ => by
          rw [← mul_sub]
          exact (ind_mul_sq_le _ _).trans ((hX v G H κ σ y).2.2 u Gu Hu)
      rw [pieceNorm_eq, pieceNorm_eq]
      refine (sqrt_tsum_sub_le (famu hX) (amp_norm_facts hX T v G H σ y hs).1).trans (Real.sqrt_le_sqrt ?_)
      exact (Summable.of_nonneg_of_le (fun κ => sq_nonneg _) hle hd).tsum_le_tsum hle hd
    obtain ⟨-, pa2, pa0⟩ := amp_norm_facts hA T v G H σ y hs
    obtain ⟨-, pb2, pb0⟩ := amp_norm_facts hB T v G H σ y hs
    have pb0' : 0 ≤ pieceNorm T (fun κ => B u Gu Hu κ σ y) := Real.sqrt_nonneg _
    have pd := prod_diff_le pa0 pb0 pb0' (normTriangle hA) (normTriangle hB) ht
    rw [Real.sq_sqrt hSd0] at pd
    rw [← mul_sub, abs_mul]
    have q1 := mul_le_mul (hc σ y) pd (abs_nonneg _) hM
    have ht1 : 0 ≤ 1 + 1 / t := by positivity
    have q2 : M * ((1 + 1 / t) * (∑' κ, diffSqAt u Gu Hu v G H κ σ y + ∑' κ, diffSqAt u Gu Hu v G H κ σ y))
        ≤ (2 * M + 1) * (1 + 1 / t) * ∑' κ, diffSqAt u Gu Hu v G H κ σ y := by
      have := mul_nonneg ht1 hSd0
      nlinarith
    have q3 : M * (t * (pieceNorm T (fun κ => A v G H κ σ y) ^ 2 + pieceNorm T (fun κ => B v G H κ σ y) ^ 2))
        ≤ (2 * M + 1) * t * ∑' κ, ampSqAt v G H κ σ y := by
      have h4 : t * (pieceNorm T (fun κ => A v G H κ σ y) ^ 2 + pieceNorm T (fun κ => B v G H κ σ y) ^ 2)
          ≤ t * (2 * ∑' κ, ampSqAt v G H κ σ y) := mul_le_mul_of_nonneg_left (by linarith) ht.le
      have h5 := mul_le_mul_of_nonneg_left h4 hM
      have h6 : 0 ≤ t * ∑' κ, ampSqAt v G H κ σ y := mul_nonneg ht.le hS0
      nlinarith
    calc |c σ y| * |pieceNorm T (fun κ => A u Gu Hu κ σ y) * pieceNorm T (fun κ => B u Gu Hu κ σ y)
          - pieceNorm T (fun κ => A v G H κ σ y) * pieceNorm T (fun κ => B v G H κ σ y)|
        ≤ M * ((1 + 1 / t) * (∑' κ, diffSqAt u Gu Hu v G H κ σ y + ∑' κ, diffSqAt u Gu Hu v G H κ σ y)
          + t * (pieceNorm T (fun κ => A v G H κ σ y) ^ 2 + pieceNorm T (fun κ => B v G H κ σ y) ^ 2)) := q1
      _ ≤ _ := by rw [mul_add]; linarith

variable {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
  {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}

theorem abs_neg_le {x M : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ M) : |-x| ≤ M := by
  rw [abs_neg, abs_of_nonneg h0]
  exact h1

theorem muBlock_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nM) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G _ ι σ y => if ι = 0 then pieceMuBlock m W v G β σ y else 0) v G H := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 := SmoothPieceEps.decay_const_nonneg W hD
  obtain ⟨B, Bg, hB⟩ := SmoothPieceMuNeg.weight_facts m P h w W hm β
  have hB0 : 0 ≤ B := (hB 0).1.trans (hB 0).2.1
  have hBg0 : 0 ≤ Bg := (mul_nonneg (norm_nonneg _) (by positivity)).trans (hB 0).2.2.2
  set a := (m.muP β).frame
  have hfs : ∀ y : Space, frameSpeedSup W a y ≤ (D + 1 / 2 + 2 * |a|) * (1 + ‖y‖) := fun y => by
    have := SmoothPieceEps.frameSpeedSup_le W hD a y
    nlinarith [norm_nonneg y, abs_nonneg a]
  have hc1 : ∀ (σ : ℝ) (y : Space), |-(((m.muP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y)
      * (1 + ‖y‖))| ≤ 4 * B * (D + 1 / 2 + 2 * |a|) + Bg := fun σ y => by
    obtain ⟨w0, -, w2, w3⟩ := hB y
    have f0 := SmoothPieceEps.frameSpeedSup_nonneg W a y
    have g0 : 0 ≤ PieceWeights.wtGrad (m.muP β).wt y := norm_nonneg _
    have hp : 0 ≤ 1 + ‖y‖ := by positivity
    refine abs_neg_le (by positivity) ?_
    have e1 : (m.muP β).wt y * frameSpeedSup W a y * (1 + ‖y‖)
        ≤ (m.muP β).wt y * ((D + 1 / 2 + 2 * |a|) * (1 + ‖y‖)) * (1 + ‖y‖) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfs y) w0) hp
    have e2 : (m.muP β).wt y * ((D + 1 / 2 + 2 * |a|) * (1 + ‖y‖)) * (1 + ‖y‖)
        = (m.muP β).wt y * (1 + ‖y‖) ^ 2 * (D + 1 / 2 + 2 * |a|) := by ring
    have e3 : (m.muP β).wt y * (1 + ‖y‖) ^ 2 * (D + 1 / 2 + 2 * |a|) ≤ 4 * B * (D + 1 / 2 + 2 * |a|) :=
      mul_le_mul_of_nonneg_right w2 (by positivity)
    nlinarith
  have hc2 : ∀ (σ : ℝ) (y : Space), |-((m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2)| ≤ 4 * B * |a| := fun σ y => by
    obtain ⟨w0, -, w2, -⟩ := hB y
    refine abs_neg_le (by positivity) ?_
    have : (m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2 = (m.muP β).wt y * (1 + ‖y‖) ^ 2 * |a| := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_right w2 (abs_nonneg a)
  have b1 := block_prod_bound isAmp_grad isAmp_vel (m.muP β).modes
    (fun σ y => -(((m.muP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.muP β).wt y) * (1 + ‖y‖)))
    (by positivity) hc1 v G H
  have b2 := block_prod_bound isAmp_vel isAmp_vel (m.muP β).modes
    (fun σ y => -((m.muP β).wt y * |a| * (1 + ‖y‖) ^ 2)) (by positivity) hc2 v G H
  refine isRestBound_congr (b1.add b2) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
    unfold pieceMuBlock
    rw [pieceNorm_scale (m.muP β).modes (fun κ => velAmp v' κ σ y) hp]
    ring
  · simp only [if_neg h0, add_zero]

theorem epsBlock_bound (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2))
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (β : Fin nE) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) :
    IsRestBound (fun v G H ι σ y => if ι = 0 then pieceEpsBlock m W v G H β σ y else 0) v G H := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 := SmoothPieceEps.decay_const_nonneg W hD
  obtain ⟨Bd, hBd⟩ := hm.eps_decay
  have hw0 : ∀ y, 0 ≤ (m.epsP β).wt y := fun y => hm.eps_wt_nonneg β y
  have hwE : ∀ y, (m.epsP β).wt y ≤ epsSup := fun y =>
    (Finset.single_le_sum (f := fun b => (m.epsP b).wt y) (fun b _ => hm.eps_wt_nonneg b y)
      (Finset.mem_univ β)).trans (hm.eps_sum_le y)
  have hgE : ∀ y, PieceWeights.wtGrad (m.epsP β).wt y ≤ epsGradSup := fun y =>
    (Finset.single_le_sum (f := fun b => PieceWeights.wtGrad (m.epsP b).wt y) (fun b _ => norm_nonneg _)
      (Finset.mem_univ β)).trans (hm.eps_grad_sum_le y)
  have hE0 : 0 ≤ epsSup := (hw0 0).trans (hwE 0)
  have hG0 : 0 ≤ epsGradSup := (norm_nonneg _).trans (hgE 0)
  have hBd0 : 0 ≤ Bd := (mul_nonneg (norm_nonneg _) (hw0 0)).trans (hBd β 0)
  have hy1 : ∀ y : Space, 1 ≤ 1 + ‖y‖ := fun y => le_add_of_nonneg_right (norm_nonneg y)
  set a := (m.epsP β).frame
  have hvs : ∀ y : Space, vortSup W y ≤ 27 * D := fun y => by
    have := SmoothPieceEps.vortSup_le W hD y
    have : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ (hy1 y))
    linarith
  have hvs0 : ∀ y, 0 ≤ vortSup W y := fun y => SmoothPieceEps.vortSup_nonneg W y
  have hvg : ∀ y : Space, vortGradSup W y * (1 + ‖y‖) ≤ 27 * D := fun y => by
    have h1 := SmoothPieceEps.vortGradSup_le W hD hW y
    have hp : 0 < 1 + ‖y‖ := by positivity
    have h2 : 27 * (D / (1 + ‖y‖) ^ 3) * (1 + ‖y‖) = 27 * (D / (1 + ‖y‖) ^ 2) := by field_simp
    have h3 : D / (1 + ‖y‖) ^ 2 ≤ D := div_le_self hD0 (one_le_pow₀ (hy1 y))
    nlinarith [mul_le_mul_of_nonneg_right h1 hp.le]
  have hvg0 : ∀ y, 0 ≤ vortGradSup W y := fun y => SmoothPieceEps.vortGradSup_nonneg W y
  have hwfs : ∀ y : Space, (m.epsP β).wt y * frameSpeedSup W a y ≤ epsSup * D + (1 / 2 + 2 * |a|) * Bd :=
    fun y => by
      have h1 := SmoothPieceEps.frameSpeedSup_le W hD a y
      have h2 := mul_le_mul_of_nonneg_left h1 (hw0 y)
      have h3 := hBd β y
      have h4 : (m.epsP β).wt y * D ≤ epsSup * D := mul_le_mul_of_nonneg_right (hwE y) hD0
      have h5 : (m.epsP β).wt y * ((1 / 2 + 2 * |a|) * ‖y‖) ≤ (1 / 2 + 2 * |a|) * Bd := by
        have : (m.epsP β).wt y * ((1 / 2 + 2 * |a|) * ‖y‖) = (1 / 2 + 2 * |a|) * (‖y‖ * (m.epsP β).wt y) := by
          ring
        rw [this]
        exact mul_le_mul_of_nonneg_left h3 (by positivity)
      nlinarith
  have b1 := block_prod_bound isAmp_vortGrad isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * frameSpeedSup W a y + PieceWeights.wtGrad (m.epsP β).wt y))
    (M := epsSup * D + (1 / 2 + 2 * |a|) * Bd + epsGradSup) (by positivity)
    (fun σ y => abs_neg_le (add_nonneg (mul_nonneg (hw0 y) (SmoothPieceEps.frameSpeedSup_nonneg W a y))
      (norm_nonneg _)) (add_le_add (hwfs y) (hgE y))) v G H
  have b2 := block_prod_bound isAmp_vort isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * ((1 / 2) * vortSup W y + |a|)))
    (M := epsSup * ((1 / 2) * (27 * D) + |a|)) (by positivity)
    (fun σ y => abs_neg_le (mul_nonneg (hw0 y) (by have := hvs0 y; positivity))
      (mul_le_mul (hwE y) (by have := hvs y; linarith) (by have := hvs0 y; positivity) hE0)) v G H
  have b3 := block_prod_bound isAmp_vel isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * vortGradSup W y * (1 + ‖y‖)))
    (M := epsSup * (27 * D)) (by positivity)
    (fun σ y => abs_neg_le (by have := hw0 y; have := hvg0 y; positivity) (by
      rw [mul_assoc]; exact mul_le_mul (hwE y) (hvg y) (by have := hvg0 y; positivity) hE0)) v G H
  have b4 := block_prod_bound isAmp_grad isAmp_vort (m.epsP β).modes
    (fun σ y => -((m.epsP β).wt y * vortSup W y))
    (M := epsSup * (27 * D)) (by positivity)
    (fun σ y => abs_neg_le (mul_nonneg (hw0 y) (hvs0 y)) (mul_le_mul (hwE y) (hvs y) (hvs0 y) hE0)) v G H
  refine isRestBound_congr (((b1.add b2).add b3).add b4) fun v' G' H' ι σ y => ?_
  have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
  beta_reduce
  by_cases h0 : ι = 0
  · simp only [if_pos h0]
    unfold pieceEpsBlock
    rw [pieceNorm_scale (m.epsP β).modes (fun κ => velAmp v' κ σ y) hp]
    ring
  · simp only [if_neg h0, add_zero]

end Internal.PiecePassageDiffBoundBlock

end Coercive

end Breakdown

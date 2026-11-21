import Breakdown.Cert.CoercivePieceAbsorbEps
import Breakdown.Cert.CoercivePieceAbsorbMu
import Breakdown.Cert.CoercivePieceAbsorbMeasure

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceAbsorb

theorem le_lintegral_add_iter (f g : ℝ → Space → ℝ≥0∞) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) :=
  (le_lintegral_add _ _).trans (lintegral_mono fun _ => le_lintegral_add _ _)

theorem lintegral_add_iter {f g : ℝ → Space → ℝ≥0∞}
    (hg : AEMeasurable (fun z : ℝ × Space => g z.1 z.2) slabMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y)
      = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  obtain ⟨g', hg'm, hgg'⟩ := hg
  have hae : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y ∂(volume : Measure Space),
      g σ y = g' (σ, y) := Measure.ae_ae_of_ae_prod hgg'
  have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      ∫⁻ y, (f σ y + g σ y) = (∫⁻ y, f σ y) + ∫⁻ y, g' (σ, y) := by
    filter_upwards [hae] with σ hσ
    have hc : (fun y => f σ y + g σ y) =ᵐ[volume] fun y => f σ y + g' (σ, y) :=
      hσ.mono fun y hy => by simp only [hy]
    rw [lintegral_congr_ae hc]
    exact lintegral_add_right (fun y => f σ y) (hg'm.comp measurable_prodMk_left)
  have h2 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, g σ y = ∫⁻ y, g' (σ, y) := by
    filter_upwards [hae] with σ hσ
    exact lintegral_congr_ae hσ
  rw [lintegral_congr_ae h1, lintegral_congr_ae h2]
  exact lintegral_add_right _ hg'm.lintegral_prod_right'

theorem transfer {X : ℝ} {Dp Dn Ap N Jp Jn : ℝ → Space → ℝ≥0∞}
    (hA : AEMeasurable (fun z : ℝ × Space => Ap z.1 z.2 + Jp z.1 z.2) slabMeasure)
    (hJ : AEMeasurable (fun z : ℝ × Space => Jn z.1 z.2) slabMeasure)
    (hpt : ∀ᵐ z ∂slabMeasure, Dp z.1 z.2 + N z.1 z.2 ≤ Ap z.1 z.2 + Dn z.1 z.2)
    (hN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, N σ y) < ⊤)
    (hX : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Ap σ y + Jp σ y)) + ENNReal.ofReal (-X)
      ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (N σ y + Jn σ y)) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Dp σ y + Jp σ y)) + ENNReal.ofReal (-X)
      ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Dn σ y + Jn σ y) := by
  set iP := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Dp σ y + Jp σ y) with hiP
  set iD := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Dn σ y + Jn σ y) with hiD
  set iA := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (Ap σ y + Jp σ y) with hiA
  set iN := ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (N σ y + Jn σ y) with hiN
  by_cases hJt : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, Jn σ y) = ⊤
  · have hD : iD = ⊤ := by
      refine top_le_iff.1 (hJt ▸ ?_)
      exact lintegral_mono fun σ => lintegral_mono fun y => le_add_self
    rw [hD, add_top]
    exact le_top
  have hNJ : iN ≠ ⊤ := by
    rw [hiN, lintegral_add_iter hJ]
    exact ENNReal.add_ne_top.2 ⟨hN.ne, hJt⟩
  have hae := Measure.ae_ae_of_ae_prod hpt
  have step : iP + iN ≤ iD + iA := by
    refine (le_lintegral_add_iter _ _).trans ?_
    rw [hiD, hiA, ← lintegral_add_iter (f := fun σ y => Dn σ y + Jn σ y) hA]
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with σ hσ
    refine lintegral_mono_ae ?_
    filter_upwards [hσ] with y hy
    calc Dp σ y + Jp σ y + (N σ y + Jn σ y) = (Dp σ y + N σ y) + (Jp σ y + Jn σ y) := by ring
      _ ≤ (Ap σ y + Dn σ y) + (Jp σ y + Jn σ y) := add_le_add hy le_rfl
      _ = Dn σ y + Jn σ y + (Ap σ y + Jp σ y) := by ring
  have key : (iP + ENNReal.ofReal (-X)) + iN ≤ (ENNReal.ofReal X + iD) + iN := by
    calc (iP + ENNReal.ofReal (-X)) + iN = (iP + iN) + ENNReal.ofReal (-X) := by ring
      _ ≤ (iD + iA) + ENNReal.ofReal (-X) := add_le_add step le_rfl
      _ = iD + (iA + ENNReal.ofReal (-X)) := by ring
      _ ≤ iD + (ENNReal.ofReal X + iN) := add_le_add le_rfl hX
      _ = (ENNReal.ofReal X + iD) + iN := by ring
  exact (ENNReal.add_le_add_iff_right hNJ).1 key


theorem ofReal_eq_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with hx | hx
  · rw [max_eq_right hx, ENNReal.ofReal_of_nonpos hx, ENNReal.ofReal_zero]
  · rw [max_eq_left hx]

theorem summable_max {f : ℤ × ℤ → ℝ} (hf : Summable f) : Summable fun ι => max (f ι) 0 :=
  Summable.of_nonneg_of_le (fun _ => le_max_right _ _) (fun _ => max_le (le_abs_self _) (abs_nonneg _)) hf.abs

theorem tsum_ofReal_eq {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' ι, ENNReal.ofReal (f ι) = ENNReal.ofReal (∑' ι, max (f ι) 0) := by
  rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => le_max_right _ _) (summable_max hf)]
  exact tsum_congr fun ι => ofReal_eq_max (f ι)

theorem tsum_max_sub {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' ι, max (f ι) 0 - ∑' ι, max (-f ι) 0 = ∑' ι, f ι := by
  rw [← (summable_max hf).tsum_sub (summable_max hf.neg)]
  refine tsum_congr fun ι => ?_
  rcases le_total (f ι) 0 with h | h
  · rw [max_eq_right h, max_eq_left (neg_nonneg.2 h)]
    ring
  · rw [max_eq_left h, max_eq_right (neg_nonpos.2 h)]
    ring

theorem tsum_ofReal_top {f : ℤ × ℤ → ℝ} (hf0 : ∀ ι, 0 ≤ f ι) (hf : ¬ Summable f) :
    ∑' ι, ENNReal.ofReal (f ι) = ⊤ := by
  by_contra hne
  apply hf
  have := ENNReal.summable_toReal hne
  simpa [ENNReal.toReal_ofReal (hf0 _)] using this

theorem ennreal_of_real_sums {d P r : ℤ × ℤ → ℝ} {b : ℝ} (hP : ∀ ι, 0 ≤ P ι)
    (he : Summable fun ι => d ι - P ι) (hr : Summable r)
    (hle : ∑' ι, (d ι - P ι) ≤ ∑' ι, r ι + b) :
    (∑' ι, ENNReal.ofReal (d ι)) + ((∑' ι, ENNReal.ofReal (-r ι)) + ENNReal.ofReal (-b))
      ≤ ((∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (r ι)) + ENNReal.ofReal b)
        + ∑' ι, ENNReal.ofReal (-d ι) := by
  by_cases hPs : Summable P
  swap
  · rw [tsum_ofReal_top hP hPs]
    simp
  have hd : Summable d := by
    have := he.add hPs
    simpa using this
  rw [tsum_ofReal_eq hd, tsum_ofReal_eq hr.neg, tsum_ofReal_eq hPs, tsum_ofReal_eq hr,
    tsum_ofReal_eq hd.neg, ofReal_eq_max (-b), ofReal_eq_max b]
  have h1 := tsum_max_sub hd
  have h2 := tsum_max_sub hr
  have h3 : ∑' ι, max (P ι) 0 = ∑' ι, P ι := tsum_congr fun ι => max_eq_left (hP ι)
  have h4 : ∑' ι, d ι = ∑' ι, (d ι - P ι) + ∑' ι, P ι := by
    rw [← he.tsum_add hPs]
    exact tsum_congr fun ι => by ring
  have h5 : max b 0 - max (-b) 0 = b := by
    rcases le_total b 0 with hb | hb
    · rw [max_eq_right hb, max_eq_left (neg_nonneg.2 hb)]
      ring
    · rw [max_eq_left hb, max_eq_right (neg_nonpos.2 hb)]
      ring
  have n1 : 0 ≤ ∑' ι, max (d ι) 0 := tsum_nonneg fun _ => le_max_right _ _
  have n2 : 0 ≤ ∑' ι, max (-r ι) 0 := tsum_nonneg fun _ => le_max_right _ _
  have n3 : 0 ≤ ∑' ι, max (P ι) 0 := tsum_nonneg fun _ => le_max_right _ _
  have n4 : 0 ≤ ∑' ι, max (r ι) 0 := tsum_nonneg fun _ => le_max_right _ _
  have n5 : 0 ≤ ∑' ι, max (-d ι) 0 := tsum_nonneg fun _ => le_max_right _ _
  have n6 : 0 ≤ max (-b) 0 := le_max_right _ _
  have n7 : 0 ≤ max b 0 := le_max_right _ _
  rw [← ENNReal.ofReal_add n2 n6, ← ENNReal.ofReal_add n1 (add_nonneg n2 n6), ← ENNReal.ofReal_add n3 n4,
    ← ENNReal.ofReal_add (add_nonneg n3 n4) n7, ← ENNReal.ofReal_add (add_nonneg (add_nonneg n3 n4) n7) n5]
  exact ENNReal.ofReal_le_ofReal (by linarith)

section Main

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem pieceBlock_nonpos (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (hM : ∀ β y, 0 ≤ (m.muP β).wt y)
    (σ : ℝ) (y : Space) : pieceBlock m W v G H σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS : 0 ≤ vortGradSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold pieceBlock pieceEpsBlock pieceMuBlock
  refine add_nonpos (Finset.sum_nonpos fun β _ => ?_) (Finset.sum_nonpos fun β _ => ?_)
  · have ha := hE β y
    have h1 := hpn (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
    have h2 := hpn (m.epsP β).modes (fun κ => vortAmp G κ σ y)
    have h3 := hpn (m.epsP β).modes (fun κ => velAmp v κ σ y)
    have h4 := hpn (m.epsP β).modes (fun κ => gradAmp G κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.epsP β).frame)) (hwg (m.epsP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
        (abs_nonneg (m.epsP β).frame))) (sq_nonneg (pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))),
      mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2, mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2]
  · have ha := hM β y
    have h1 := hpn (m.muP β).modes (fun κ => gradAmp G κ σ y)
    have h2 := hpn (m.muP β).modes (fun κ => velAmp v κ σ y)
    nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.muP β).frame)) (hwg (m.muP β).wt)) h1) h2,
      mul_nonneg (mul_nonneg ha (abs_nonneg (m.muP β).frame))
        (sq_nonneg (pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)))]

theorem modeDensity_split (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) :
    m.modeDensity P h w ι y x2 xc x1 xo x0 =
      baseDensity m.convD m.convZ (m.classOf ι) m.c w y x2 xc x1 xo x0
        + ∑ β : Fin nE, pieceEpsDensity m P h β ι y xc xo x1 x0
        + ∑ β : Fin nM, pieceMuDensity m P h β ι y x1 x0 := by
  unfold PieceWeights.modeDensity baseDensity pieceEpsDensity pieceMuDensity PieceWeights.shareHat
    PieceWeights.coefA PieceWeights.coefAA PieceWeights.coefB
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib, ← Finset.sum_mul]
  ring

theorem real_step {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    Summable (fun ι => m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y) ∧
      Summable (fun ι => pieceRest m h w W v G H ι σ y) ∧
      ∑' ι, (m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y)
        ≤ ∑' ι, pieceRest m h w W v G H ι σ y + pieceBlock m W v G H σ y := by
  set bs := fun ι => modeVals v G H ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y) with hbs
  set eD := fun (β : Fin nE) ι => pieceEpsDensity m P h β ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y)
    (gradAmp G ι σ y) (velAmp v ι σ y) - pieceEpsPos m P G β ι σ y with heD
  set mD := fun (β : Fin nM) ι => pieceMuDensity m P h β ι y (gradAmp G ι σ y) (velAmp v ι σ y)
    - pieceMuPos m P v β ι σ y with hmD
  set eR := fun (β : Fin nE) ι => pieceEpsRestMode m h W v G H β ι σ y with heR
  set mR := fun (β : Fin nM) ι => pieceMuRestMode m h W v G β ι σ y with hmR
  have hsplit : ∀ ι, m.modeTerm P h w v G H ι σ y - piecePos m P v G ι σ y
      = bs ι + ∑ β, eD β ι + ∑ β, mD β ι := by
    intro ι
    simp only [hbs, heD, hmD, PieceWeights.modeTerm, piecePos, modeDensity_split, modeVals, secondDerivAmp, vortGradAmp,
      gradAmp, vortAmp, velAmp, Finset.sum_sub_distrib]
    ring
  have hrest : ∀ ι, pieceRest m h w W v G H ι σ y = bs ι + ∑ β, eR β ι + ∑ β, mR β ι := fun ι => rfl
  have hB : pieceBlock m W v G H σ y = ∑ β, pieceEpsBlock m W v G H β σ y + ∑ β, pieceMuBlock m W v G β σ y := rfl
  have hb := base_summable m w v G H σ y hm.finite_classes hg
  have he := fun β => eps_piece_le m P h w W v G H hm β σ y hg
  have hmu := fun β => mu_piece_le m P h w W v G H hm β σ y hg
  have sE : Summable fun ι => ∑ β, eD β ι := summable_sum fun β _ => (he β).1
  have sM : Summable fun ι => ∑ β, mD β ι := summable_sum fun β _ => (hmu β).1
  have sER : Summable fun ι => ∑ β, eR β ι := summable_sum fun β _ => (he β).2.1
  have sMR : Summable fun ι => ∑ β, mR β ι := summable_sum fun β _ => (hmu β).2.1
  simp only [hsplit, hrest, hB]
  refine ⟨(hb.add sE).add sM, (hb.add sER).add sMR, ?_⟩
  rw [(hb.add sE).tsum_add sM, hb.tsum_add sE, (hb.add sER).tsum_add sMR, hb.tsum_add sER,
    Summable.tsum_finsetSum fun β _ => (he β).1, Summable.tsum_finsetSum fun β _ => (hmu β).1, Summable.tsum_finsetSum fun β _ => (he β).2.1,
    Summable.tsum_finsetSum fun β _ => (hmu β).2.1]
  have i1 : ∑ β, ∑' ι, eD β ι ≤ ∑ β, (∑' ι, eR β ι + pieceEpsBlock m W v G H β σ y) :=
    Finset.sum_le_sum fun β _ => (he β).2.2
  have i2 : ∑ β, ∑' ι, mD β ι ≤ ∑ β, (∑' ι, mR β ι + pieceMuBlock m W v G β σ y) :=
    Finset.sum_le_sum fun β _ => (hmu β).2.2
  rw [Finset.sum_add_distrib] at i1 i2
  linarith

theorem pointwise_step {w₀ epsSup epsGradSup ratio : ℝ} (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (σ : ℝ) (y : Space) (hg : IsGoodPoint v G H σ y) :
    (∑' ι, ENNReal.ofReal (m.modeTerm P h w v G H ι σ y))
        + ((∑' ι, ENNReal.ofReal (-pieceRest m h w W v G H ι σ y)) + ENNReal.ofReal (-pieceBlock m W v G H σ y))
      ≤ ((∑' ι, ENNReal.ofReal (piecePos m P v G ι σ y)) + (∑' ι, ENNReal.ofReal (pieceRest m h w W v G H ι σ y))
          + ENNReal.ofReal (pieceBlock m W v G H σ y))
        + ∑' ι, ENNReal.ofReal (-m.modeTerm P h w v G H ι σ y) := by
  obtain ⟨he, hr, hle⟩ := real_step m P h w W v G H hm σ y hg
  refine ennreal_of_real_sums (fun ι => ?_) he hr hle
  unfold piecePos pieceEpsPos pieceMuPos
  refine add_nonneg (Finset.sum_nonneg fun β _ => ?_) (Finset.sum_nonneg fun β _ => ?_)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (hm.eps_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (sub_nonneg.2 hm.cμ_lt_one.le))
      (hm.mu_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)

end Main

end Internal.PieceAbsorb

open Internal.PieceAbsorb in
theorem pieceAbsorbStepHolds_of (hPar : ModeSquareSumHolds) (hSecondDeriv : PerturbationSecondDerivBoundHolds)
    (hL2 : PerturbationLocalSquareIntegrabilityHolds) : PieceAbsorbStepHolds := by
  intro C nE nM m P h w Γ W w₀ epsSup epsGradSup ratio hm hW _hWp _hWdiv _hWdecay _hwb v G H g hv X hX
  obtain ⟨hN, hle⟩ := hX
  have hpt : ∀ᵐ z ∂slabMeasure,
      (∑' ι, ENNReal.ofReal (m.modeTerm P h w v G H ι z.1 z.2))
        + ((∑' ι, ENNReal.ofReal (-pieceRest m h w W v G H ι z.1 z.2))
          + ENNReal.ofReal (-pieceBlock m W v G H z.1 z.2))
      ≤ ((∑' ι, ENNReal.ofReal (piecePos m P v G ι z.1 z.2))
          + (∑' ι, ENNReal.ofReal (pieceRest m h w W v G H ι z.1 z.2))
          + ENNReal.ofReal (pieceBlock m W v G H z.1 z.2))
        + ∑' ι, ENNReal.ofReal (-m.modeTerm P h w v G H ι z.1 z.2) := by
    filter_upwards [ae_goodPoint P v G H hPar hSecondDeriv hL2 hv] with z hz
    exact pointwise_step m P h w W v G H hm z.1 z.2 hz
  exact transfer (aemeasurable_hypothesisSide m P h w W v G H hm hW hv)
    (aemeasurable_stretchNeg P W v G H hW hv) hpt hN hle


end Coercive

end Breakdown

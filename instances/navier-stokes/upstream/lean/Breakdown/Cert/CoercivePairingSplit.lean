import Breakdown.Cert.CoerciveTestDensity
import Breakdown.Cert.CoerciveModeL2

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace PairingSplitInternal

open ModeL2Internal (IsSquareField weightedModeTerm weightedMode_bound)

def periodMeasure : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume

theorem periodMeasure_eq :
    periodMeasure = (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) := by
  rw [periodMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aesm_period {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) periodMeasure := by
  rw [periodMeasure_eq]; exact hF.restrict

theorem lintegral_period (u : ℝ × Space → Space) (hu : AEStronglyMeasurable u periodMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖u (σ, y)‖ ^ 2)
      = ∫⁻ z, ENNReal.ofReal (‖u z‖ ^ 2) ∂periodMeasure := by
  rw [periodMeasure]
  exact (lintegral_prod (fun z => ENNReal.ofReal (‖u z‖ ^ 2))
    ((hu.norm.aemeasurable.pow_const 2).ennreal_ofReal)).symm

theorem sq_integrable {F : ℝ → Space → Space} (hF : IsSquareField F) :
    Integrable (fun z : ℝ × Space => ‖F z.1 z.2‖ ^ 2) periodMeasure := by
  have hμ := aesm_period hF.1
  have hfin : ∫⁻ z, ENNReal.ofReal (‖F z.1 z.2‖ ^ 2) ∂periodMeasure < ⊤ := by
    rw [← lintegral_period (fun z => F z.1 z.2) hμ]; exact hF.2.2
  refine (integrable_toReal_of_lintegral_ne_top (hμ.norm.pow 2).aemeasurable.ennreal_ofReal
    hfin.ne).congr ?_
  exact ae_of_all _ (fun z => ENNReal.toReal_ofReal (sq_nonneg _))

theorem inner_integrable {F G : ℝ → Space → Space} (hF : IsSquareField F) (hG : IsSquareField G) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (G z.1 z.2)) periodMeasure := by
  have hFμ := aesm_period hF.1
  have hGμ := aesm_period hG.1
  refine Integrable.mono' (((sq_integrable hF).add (sq_integrable hG)).div_const 2)
    (hFμ.inner hGμ) (ae_of_all _ fun z => ?_)
  simp only [Pi.add_apply]
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  nlinarith [sq_nonneg (‖F z.1 z.2‖ - ‖G z.1 z.2‖)]

theorem pairing_eq {F G : ℝ → Space → Space} (hF : IsSquareField F) (hG : IsSquareField G) :
    periodPairing F G = ∫ z, inner ℝ (F z.1 z.2) (G z.1 z.2) ∂periodMeasure := by
  rw [periodMeasure, integral_prod _ (inner_integrable hF hG)]
  rfl

theorem normSq_eq {F : ℝ → Space → Space} (hF : IsSquareField F) :
    periodNorm F ^ 2 = ∫ z, ‖F z.1 z.2‖ ^ 2 ∂periodMeasure := by
  have hμ := aesm_period hF.1
  rw [periodNorm, Real.sq_sqrt ENNReal.toReal_nonneg,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun z => sq_nonneg _) (hμ.norm.pow 2),
    ← lintegral_period (fun z => F z.1 z.2) hμ]
  rfl

theorem square_lin {F G : ℝ → Space → Space} (hF : IsSquareField F) (hG : IsSquareField G) (a c : ℝ) :
    IsSquareField (fun σ y => a • F σ y + c • G σ y) := by
  have hFμ := aesm_period hF.1
  have hGμ := aesm_period hG.1
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => a • F z.1 z.2 + c • G z.1 z.2) volume :=
    (hF.1.const_smul a).add (hG.1.const_smul c)
  refine ⟨hm, fun σ y => by simp only [hF.2.1 σ y, hG.2.1 σ y], ?_⟩
  have hmμ := aesm_period (F := fun σ y => a • F σ y + c • G σ y) hm
  have hint : Integrable (fun z : ℝ × Space => ‖a • F z.1 z.2 + c • G z.1 z.2‖ ^ 2) periodMeasure := by
    refine Integrable.mono' ((((sq_integrable hF).const_mul (2 * a ^ 2)).add
      ((sq_integrable hG).const_mul (2 * c ^ 2)))) (hmμ.norm.pow 2) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have h1 := norm_add_le (a • F z.1 z.2) (c • G z.1 z.2)
    rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
    have h2 : 0 ≤ ‖a • F z.1 z.2 + c • G z.1 z.2‖ := norm_nonneg _
    have h3 : 0 ≤ |a| * ‖F z.1 z.2‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have h4 : 0 ≤ |c| * ‖G z.1 z.2‖ := mul_nonneg (abs_nonneg _) (norm_nonneg _)
    have h5 : ‖a • F z.1 z.2 + c • G z.1 z.2‖ ^ 2 ≤ (|a| * ‖F z.1 z.2‖ + |c| * ‖G z.1 z.2‖) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    have h6 : (|a| * ‖F z.1 z.2‖ + |c| * ‖G z.1 z.2‖) ^ 2
        ≤ 2 * a ^ 2 * ‖F z.1 z.2‖ ^ 2 + 2 * c ^ 2 * ‖G z.1 z.2‖ ^ 2 := by
      have ha : |a| ^ 2 = a ^ 2 := sq_abs a
      have hc : |c| ^ 2 = c ^ 2 := sq_abs c
      nlinarith [sq_nonneg (|a| * ‖F z.1 z.2‖ - |c| * ‖G z.1 z.2‖)]
    exact h5.trans h6
  show ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖a • F σ y + c • G σ y‖ ^ 2) < ⊤
  rw [lintegral_period (fun z => a • F z.1 z.2 + c • G z.1 z.2) hmμ]
  exact hint.lintegral_lt_top

theorem square_add {F G : ℝ → Space → Space} (hF : IsSquareField F) (hG : IsSquareField G) :
    IsSquareField (fun σ y => F σ y + G σ y) := by
  have h := square_lin hF hG 1 1
  simpa only [one_smul] using h

theorem pairing_add_left {X Y Z : ℝ → Space → Space} (hX : IsSquareField X) (hY : IsSquareField Y)
    (hZ : IsSquareField Z) :
    periodPairing (fun σ y => X σ y + Y σ y) Z = periodPairing X Z + periodPairing Y Z := by
  rw [pairing_eq (square_add hX hY) hZ, pairing_eq hX hZ, pairing_eq hY hZ,
    ← integral_add (inner_integrable hX hZ) (inner_integrable hY hZ)]
  congr 1
  funext z
  exact inner_add_left _ _ _

theorem pairing_lin_left {X Y Z : ℝ → Space → Space} (hX : IsSquareField X) (hY : IsSquareField Y)
    (hZ : IsSquareField Z) (a c : ℝ) :
    periodPairing (fun σ y => a • X σ y + c • Y σ y) Z = a * periodPairing X Z + c * periodPairing Y Z := by
  rw [pairing_eq (square_lin hX hY a c) hZ, pairing_eq hX hZ, pairing_eq hY hZ,
    ← integral_const_mul, ← integral_const_mul,
    ← integral_add ((inner_integrable hX hZ).const_mul a) ((inner_integrable hY hZ).const_mul c)]
  congr 1
  funext z
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]

theorem normSq_add {X Y : ℝ → Space → Space} (hX : IsSquareField X) (hY : IsSquareField Y) :
    periodNorm (fun σ y => X σ y + Y σ y) ^ 2
      = periodNorm X ^ 2 + 2 * periodPairing X Y + periodNorm Y ^ 2 := by
  rw [normSq_eq (square_add hX hY), normSq_eq hX, normSq_eq hY, pairing_eq hX hY]
  have e : (fun z : ℝ × Space => ‖X z.1 z.2 + Y z.1 z.2‖ ^ 2) = fun z =>
      (‖X z.1 z.2‖ ^ 2 + 2 * inner ℝ (X z.1 z.2) (Y z.1 z.2)) + ‖Y z.1 z.2‖ ^ 2 := by
    funext z; exact norm_add_sq_real _ _
  have i1 : Integrable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2 + 2 * inner ℝ (X z.1 z.2) (Y z.1 z.2))
      periodMeasure := (sq_integrable hX).add ((inner_integrable hX hY).const_mul 2)
  have i2 : Integrable (fun z : ℝ × Space => 2 * inner ℝ (X z.1 z.2) (Y z.1 z.2)) periodMeasure :=
    (inner_integrable hX hY).const_mul 2
  rw [e, integral_add i1 (sq_integrable hY), integral_add (sq_integrable hX) i2, integral_const_mul]

theorem periodNorm_congr {X Y : ℝ → Space → Space}
    (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume)
    (h : ∀ᵐ z : ℝ × Space, X z.1 z.2 = Y z.1 z.2) : periodNorm X = periodNorm Y := by
  have hXμ := aesm_period hX
  have hYμ := aesm_period hY
  have h' : ∀ᵐ z ∂periodMeasure, X z.1 z.2 = Y z.1 z.2 := by
    rw [periodMeasure_eq]; exact ae_restrict_of_ae h
  unfold periodNorm periodLIntegral
  rw [lintegral_period (fun z => X z.1 z.2) hXμ, lintegral_period (fun z => Y z.1 z.2) hYμ]
  have hl : ∫⁻ z, ENNReal.ofReal (‖X z.1 z.2‖ ^ 2) ∂periodMeasure
      = ∫⁻ z, ENNReal.ofReal (‖Y z.1 z.2‖ ^ 2) ∂periodMeasure :=
    lintegral_congr_ae (h'.mono fun z hz => by simp only [hz])
  rw [hl]

theorem square_of_solenoidal {F Q : ℝ → Space → Space} (h : IsSolenoidalPartOf F Q) : IsSquareField Q :=
  ⟨h.1, h.2.1, h.2.2.1⟩

theorem square_of_continuous {X : ℝ → Space → Space} (hc : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (hp : IsTimePeriodic X) (hR : ∃ R, ∀ σ y, R < ‖y‖ → X σ y = 0) : IsSquareField X := by
  obtain ⟨R, hR⟩ := hR
  refine ⟨hc.aestronglyMeasurable, hp, ?_⟩
  have hμ := aesm_period (F := X) hc.aestronglyMeasurable
  show ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖X σ y‖ ^ 2) < ⊤
  rw [lintegral_period (fun z => X z.1 z.2) hμ]
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hcs : Continuous (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2) := hc.norm.pow 2
  have hon : IntegrableOn (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) volume := by
    refine (hcs.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
      (measurableSet_Icc.prod MeasurableSet.univ) ?_
    rintro ⟨σ, y⟩ ⟨⟨hσ, -⟩, hn⟩
    have hy : R < ‖y‖ := by
      by_contra hy
      exact hn ⟨hσ, by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.1 hy⟩
    simp [hR σ y hy]
  have hint : Integrable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2) periodMeasure := by
    rw [periodMeasure_eq]; exact hon
  exact hint.lintegral_lt_top

theorem pairing_test_integrable_split {X Y : ℝ → Space → Space} {Z : ℝ → Space → Space}
    (hX : IsSquareField X) (hY : IsSquareField Y) (hZ : IsSquareField Z) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y + Y σ y) (Z σ y)
      = (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Z σ y))
        + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (Y σ y) (Z σ y) :=
  pairing_add_left hX hY hZ

theorem contDiff_slice {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {V : ℝ → Space → G}
    {m n : WithTop ℕ∞} (hV : ContDiff ℝ m (fun z : ℝ × Space => V z.1 z.2)) (hnm : n + 1 ≤ m) :
    ContDiff ℝ n (fun z : ℝ × Space => fderiv ℝ (V z.1) z.2) :=
  ContDiff.fderiv (f := fun (z : ℝ × Space) (y : Space) => V z.1 y) (g := fun z => z.2)
    (hV.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd hnm

theorem fderiv_eq_zero_far {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space → G} {R : ℝ}
    (hf : ∀ x, R < ‖x‖ → f x = 0) {y : Space} (hy : R < ‖y‖) : fderiv ℝ f y = 0 := by
  have h : f =ᶠ[nhds y] fun _ => 0 :=
    Filter.mem_of_superset ((isOpen_lt continuous_const continuous_norm).mem_nhds hy) fun x hx => hf x hx
  rw [h.fderiv_eq]
  exact fderiv_const_apply 0

theorem gradient_square {q : ℝ → Space → ℝ} (hq : IsPeriodicTestPotential q) :
    IsSquareField (fun σ y => gradientAt (q σ) y) := by
  obtain ⟨hq, hqp, R, hR⟩ := hq
  have d1 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (q z.1) z.2) :=
    contDiff_slice (V := q) (hq.of_le (by norm_cast)) (by norm_num)
  refine square_of_continuous ?_ ?_ ⟨R, fun σ y hy => ?_⟩
  · unfold gradientAt
    exact continuous_finsetSum _ fun i _ =>
      (d1.continuous.clm_apply continuous_const).smul continuous_const
  · intro σ y
    have e : q (σ + 1) = q σ := funext fun x => hqp σ x
    simp only [e]
  · unfold gradientAt
    rw [fderiv_eq_zero_far (hR σ) hy]
    simp

theorem testField_square {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) : IsSquareField ψ :=
  square_of_continuous hψ.1.continuous hψ.2.1 hψ.2.2.1

theorem solenoidal_add {F G Q R : ℝ → Space → Space} (hF : IsSquareField F) (hG : IsSquareField G)
    (h1 : IsSolenoidalPartOf F Q) (h2 : IsSolenoidalPartOf G R) :
    IsSolenoidalPartOf (fun σ y => F σ y + G σ y) (fun σ y => Q σ y + R σ y) := by
  have hQ := square_of_solenoidal h1
  have hR := square_of_solenoidal h2
  have hQR := square_add hQ hR
  refine ⟨hQR.1, hQR.2.1, hQR.2.2, fun q hq => ?_, fun ψ hψ => ?_⟩
  · have hg := gradient_square hq
    rw [pairing_test_integrable_split hQ hR hg, h1.2.2.2.1 q hq, h2.2.2.2.1 q hq, add_zero]
  · have ht := testField_square hψ
    rw [pairing_test_integrable_split hQ hR ht, pairing_test_integrable_split hF hG ht,
      h1.2.2.2.2 ψ hψ, h2.2.2.2.2 ψ hψ]

theorem pairing_eq_solenoidal (hSolMode : SolenoidalModeHolds) {F Q M : ℝ → Space → Space} (hF : IsSquareField F)
    (hQ : IsSolenoidalPartOf F Q) (hM : IsSolenoidalPartOf M M) : periodPairing F M = periodPairing Q M := by
  have hQs := square_of_solenoidal hQ
  have hMs := square_of_solenoidal hM
  obtain ⟨Q₀, hQ₀, -, hiso₀, huniq₀, -⟩ := hSolMode F hF.1 hF.2.1 hF.2.2
  have e0 := huniq₀ Q hQ
  have hX := square_lin hQs hF 2 (-1)
  have hX₀ := square_lin (square_of_solenoidal hQ₀) hF 2 (-1)
  have hiso : periodNorm (fun σ y => (2 : ℝ) • Q σ y + (-1 : ℝ) • F σ y) = periodNorm F := by
    rw [← hiso₀]
    refine periodNorm_congr hX.1 ?_ ?_
    · exact ((square_of_solenoidal hQ₀).1.const_smul (2 : ℝ)).sub hF.1
    · filter_upwards [e0] with z hz
      rw [hz, neg_one_smul, ← sub_eq_add_neg]
  have hFM := square_add hF hMs
  obtain ⟨Q₁, hQ₁, -, hiso₁, huniq₁, -⟩ := hSolMode _ hFM.1 hFM.2.1 hFM.2.2
  have e1 := huniq₁ _ (solenoidal_add hF hMs hQ hM)
  have hXM := square_add hX hMs
  have hiso' : periodNorm (fun σ y => ((2 : ℝ) • Q σ y + (-1 : ℝ) • F σ y) + M σ y)
      = periodNorm (fun σ y => F σ y + M σ y) := by
    rw [← hiso₁]
    refine periodNorm_congr hXM.1 ?_ ?_
    · exact ((square_of_solenoidal hQ₁).1.const_smul (2 : ℝ)).sub hFM.1
    · filter_upwards [e1] with z hz
      rw [← hz]
      module
  have p1 := normSq_add hX hMs
  have p2 := normSq_add hF hMs
  have p3 := pairing_lin_left hQs hF hMs 2 (-1)
  rw [hiso', hiso] at p1
  linarith

theorem solenoidal_self_of_multiplier {C : Type} (m : ModeWeights C) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {M : ℝ → Space → Space} (hM : m.IsMultiplierField v G H M) : IsSolenoidalPartOf M M :=
  ⟨hM.1, hM.2.1, hM.2.2.1, hM.2.2.2.1, fun _ _ => rfl⟩

theorem smoothRight_contDiff (P : ℝ) {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hv : IsPeriodicTestField v) :
    ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2) := by
  have hvs : ContDiff ℝ 3 (fun z : ℝ × Space => v z.1 z.2) := hv.1.of_le (by norm_cast)
  have d1 : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_slice (V := v) hvs (by norm_num)
  have d2 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    contDiff_slice (V := fun s x => fderiv ℝ (v s) x) d1 (by norm_num)
  have dt : ContDiff ℝ 2 (fun z : ℝ × Space => fderiv ℝ (fun s => v s z.2) z.1) :=
    ContDiff.fderiv (f := fun (z : ℝ × Space) (s : ℝ) => v s z.2) (g := fun z => z.1)
      (hvs.comp (contDiff_snd.prodMk contDiff_fst.snd)) contDiff_fst (by norm_num)
  have dW : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    contDiff_slice (V := W) hW (by norm_num)
  have c1 : ContDiff ℝ 1 (fun z : ℝ × Space => (1 / P) • deriv (fun s => v s z.2) z.1) :=
    have dt1 : ContDiff ℝ 1 (fun z : ℝ × Space => deriv (fun s => v s z.2) z.1) :=
      (dt.clm_apply contDiff_const).of_le (by norm_num)
    dt1.const_smul (1 / P)
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hvs.of_le (by norm_num)
  have d11 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) := d1.of_le (by norm_num)
  have hW1 : ContDiff ℝ 1 (fun z : ℝ × Space => W z.1 z.2) := hW.of_le (by norm_num)
  have c2 : ContDiff ℝ 1 (fun z : ℝ × Space => (1 / 2 : ℝ) • v z.1 z.2) := hv1.const_smul (1 / 2 : ℝ)
  have c3 : ContDiff ℝ 1 (fun z : ℝ × Space => (1 / 2 : ℝ) • fderiv ℝ (v z.1) z.2 z.2) :=
    (d11.clm_apply contDiff_snd).const_smul (1 / 2 : ℝ)
  have c4 : ContDiff ℝ 1 (fun z : ℝ × Space => secondDerivTrace (secondDerivField v z.1 z.2)) := by
    unfold secondDerivTrace secondDerivField
    exact ContDiff.sum fun j _ => (d2.clm_apply contDiff_const).clm_apply contDiff_const
  have c5 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2 (W z.1 z.2)) :=
    d11.clm_apply hW1
  have c6 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    dW.clm_apply hv1
  have c := ((((c1.add c2).add c3).sub c4).add c5).add c6
  exact c

theorem smoothRight_periodic (P : ℝ) {W v : ℝ → Space → Space} (hWp : IsTimePeriodic W)
    (hv : IsPeriodicTestField v) : IsTimePeriodic (smoothRight P W v) := by
  intro σ y
  have hvp := hv.2.1
  have ev : v (σ + 1) = v σ := funext fun x => hvp σ x
  have eW : W (σ + 1) = W σ := funext fun x => hWp σ x
  have ed : deriv (fun s => v s y) (σ + 1) = deriv (fun s => v s y) σ := by
    have key := deriv_comp_add_const (f := fun s => v s y) (a := (1 : ℝ)) (x := σ)
    have e : (fun x => v (x + 1) y) = fun s => v s y := funext fun s => hvp s y
    simp only [e] at key
    exact key.symm
  unfold smoothRight secondDerivField
  rw [ed, ev, eW]

theorem smoothRight_far (P : ℝ) (W : ℝ → Space → Space) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) : ∃ R, ∀ σ y, R < ‖y‖ → smoothRight P W v σ y = 0 := by
  obtain ⟨R, hR⟩ := hv.2.2.1
  refine ⟨R, fun σ y hy => ?_⟩
  have h0 : ∀ s, v s y = 0 := fun s => hR s y hy
  have h1 : ∀ s, fderiv ℝ (v s) y = 0 := fun s => fderiv_eq_zero_far (hR s) hy
  have h2 : fderiv ℝ (fun x => fderiv ℝ (v σ) x) y = 0 := by
    refine fderiv_eq_zero_far (f := fun x => fderiv ℝ (v σ) x) (R := R) (fun x hx => ?_) hy
    exact fderiv_eq_zero_far (hR σ) hx
  have hd : deriv (fun s => v s y) σ = 0 := by
    have e : (fun s => v s y) = fun _ => 0 := funext h0
    rw [e]
    exact deriv_const σ 0
  unfold smoothRight secondDerivField secondDerivTrace
  rw [hd, h0 σ, h1 σ, h2]
  simp

theorem smoothRight_square (P : ℝ) {W v : ℝ → Space → Space}
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hv : IsPeriodicTestField v) : IsSquareField (smoothRight P W v) :=
  square_of_continuous (smoothRight_contDiff P hW hv).continuous (smoothRight_periodic P hWp hv)
    (smoothRight_far P W hv)

theorem pairing_comm {X Y : ℝ → Space → Space} (hX : IsSquareField X) (hY : IsSquareField Y) :
    periodPairing X Y = periodPairing Y X := by
  rw [pairing_eq hX hY, pairing_eq hY hX]
  congr 1
  funext z
  exact real_inner_comm _ _

theorem pairing_tendsto {X Q : ℝ → Space → Space} {ψ : ℕ → ℝ → Space → Space} (hX : IsSquareField X)
    (hQ : IsSquareField Q) (hψ : ∀ n, IsSquareField (ψ n))
    (h : Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => periodPairing X (ψ n)) Filter.atTop (nhds (periodPairing X Q)) := by
  have hd : ∀ n, ‖periodPairing X (ψ n) - periodPairing X Q‖
      ≤ periodNorm X * Real.sqrt (periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)).toReal := by
    intro n
    have hs := square_lin (hψ n) hQ 1 (-1)
    have e := pairing_lin_left (hψ n) hQ hX 1 (-1)
    have hb := periodPairing_abs_le hs.1 hX.1 hs.2.2 hX.2.2
    have en : periodNorm (fun σ y => (1 : ℝ) • ψ n σ y + (-1 : ℝ) • Q σ y)
        = Real.sqrt (periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)).toReal := by
      unfold periodNorm
      congr 4
      funext σ y
      simp only [one_smul, neg_one_smul, ← sub_eq_add_neg]
    rw [Real.norm_eq_abs, pairing_comm hX (hψ n), pairing_comm hX hQ]
    have e' : periodPairing (ψ n) X - periodPairing Q X
        = periodPairing (fun σ y => (1 : ℝ) • ψ n σ y + (-1 : ℝ) • Q σ y) X := by
      rw [e]; ring
    rw [e', ← en, mul_comm]
    exact hb
  have hs0 : Filter.Tendsto
      (fun n => Real.sqrt (periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2)).toReal)
      Filter.atTop (nhds 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    have hq := (Real.continuous_sqrt.tendsto _).comp ht
    simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero] using hq
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) hd ?_
  simpa using (tendsto_const_nhds (x := periodNorm X)).mul hs0

def modeSum {C : Type} (m : ModeWeights C) (v ψ : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    ((Complex.I * (m.epsW (m.classOf ι) y : ℂ)
        * cdot (curlOfGrad (modeGrad ι (gradField v) σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re
      + (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

theorem fderiv_apply_const {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {c : Space → (Space →L[ℝ] F)} {x : Space} (hc : DifferentiableAt ℝ c x) (a w : Space) :
    fderiv ℝ (fun y => c y a) x w = fderiv ℝ c x w a := by
  rw [fderiv_clm_apply hc (differentiableAt_const a)]
  simp

theorem proj_apply (a : Space) (i : Fin 3) : (EuclideanSpace.proj i : Space →L[ℝ] ℝ) a = a i := rfl

theorem fderiv_component {h : Space → Space} {x : Space} (hh : DifferentiableAt ℝ h x) (i : Fin 3)
    (w : Space) : fderiv ℝ (fun y => h y i) x w = fderiv ℝ h x w i := by
  have e : HasFDerivAt (fun y => h y i) ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ h x)) x :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x hh.hasFDerivAt
  rw [e.fderiv]
  rfl

theorem differentiableAt_component {h : Space → Space} {x : Space} (hh : DifferentiableAt ℝ h x)
    (i : Fin 3) : DifferentiableAt ℝ (fun y => h y i) x :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp x hh.hasFDerivAt).differentiableAt

theorem trace_deriv_zero {g : Space → (Space →L[ℝ] Space)} (hg : Differentiable ℝ g)
    (h0 : ∀ y, ∑ i : Fin 3, (g y (unitVector i)) i = 0) (x w : Space) :
    ∑ i : Fin 3, (fderiv ℝ g x w (unitVector i)) i = 0 := by
  have hd : ∀ i : Fin 3, DifferentiableAt ℝ (fun y => g y (unitVector i)) x :=
    fun i => (hg x).clm_apply (differentiableAt_const _)
  have hdi : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      DifferentiableAt ℝ (fun y => (g y (unitVector i)) i) x :=
    fun i _ => differentiableAt_component (hd i) i
  have key : fderiv ℝ (fun y => ∑ i : Fin 3, (g y (unitVector i)) i) x w
      = ∑ i : Fin 3, (fderiv ℝ g x w (unitVector i)) i := by
    rw [fderiv_fun_sum hdi, sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_component (hd i) i w, fderiv_apply_const (hg x) (unitVector i) w]
  have hφ : (fun y => ∑ i : Fin 3, (g y (unitVector i)) i) = fun _ => (0 : ℝ) := funext h0
  rw [hφ] at key
  simp only [fderiv_const_apply, zero_apply] at key
  exact key.symm

theorem sumSecondPartials_testField {v : ℝ → Space → Space} (hv : IsPeriodicTestField v) :
    IsPeriodicTestField (fun σ y => -secondDerivTrace (secondDerivField v σ y)) := by
  obtain ⟨hvs, hvp, ⟨R, hR⟩, hdiv⟩ := hv
  have d1 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (v z.1) z.2) :=
    contDiff_slice (V := v) hvs (by exact_mod_cast le_rfl)
  have d2 : ContDiff ℝ ∞ (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (v z.1) x) z.2) :=
    contDiff_slice (V := fun s x => fderiv ℝ (v s) x) d1 (by exact_mod_cast le_rfl)
  refine ⟨?_, ?_, ⟨R, fun σ y hy => ?_⟩, fun σ y => ?_⟩
  · unfold secondDerivTrace secondDerivField
    exact (ContDiff.sum fun j _ => (d2.clm_apply contDiff_const).clm_apply contDiff_const).neg
  · intro σ y
    have ev : v (σ + 1) = v σ := funext fun x => hvp σ x
    simp only [secondDerivField, ev]
  · have h2 : fderiv ℝ (fun x => fderiv ℝ (v σ) x) y = 0 := by
      refine fderiv_eq_zero_far (f := fun x => fderiv ℝ (v σ) x) (R := R) (fun x hx => ?_) hy
      exact fderiv_eq_zero_far (hR σ) hx
    simp [secondDerivTrace, secondDerivField, h2]
  · have hf : ContDiff ℝ ∞ (v σ) := hvs.comp (contDiff_const.prodMk contDiff_id)
    have hD1 : ContDiff ℝ ∞ (fderiv ℝ (v σ)) := hf.fderiv_right (by exact_mod_cast le_rfl)
    have hD2 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (v σ))) := hD1.fderiv_right (by exact_mod_cast le_rfl)
    have hD3 : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ)))) :=
      hD2.fderiv_right (by exact_mod_cast le_rfl)
    have dD1 : Differentiable ℝ (fderiv ℝ (v σ)) := hD1.differentiable (by simp)
    have dD2 : Differentiable ℝ (fderiv ℝ (fderiv ℝ (v σ))) := hD2.differentiable (by simp)
    have s12 : ∀ a b c : Space, fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y a b c
        = fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y b a c := by
      intro a b c
      have hs := ((contDiff_infty.1 hD1 2).contDiffAt (x := y)).isSymmSndFDerivAt (by simp)
      rw [hs a b]
    have s23 : ∀ a b c : Space, fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y a b c
        = fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y a c b := by
      intro a b c
      have e : (fun x => fderiv ℝ (fderiv ℝ (v σ)) x b c) = fun x => fderiv ℝ (fderiv ℝ (v σ)) x c b :=
        funext fun x => ((contDiff_infty.1 hf 2).contDiffAt (x := x)).isSymmSndFDerivAt (by simp) b c
      have l1 := fderiv_apply_const (dD2.clm_apply (differentiable_const b) y) c a
      have l2 := fderiv_apply_const (dD2 y) b a
      have l3 := fderiv_apply_const (dD2.clm_apply (differentiable_const c) y) b a
      have l4 := fderiv_apply_const (dD2 y) c a
      rw [e] at l1
      rw [l1, l2] at l3
      rw [l3, l4] at *
    have hA : ∀ j : Fin 3, ∀ y', ∑ i : Fin 3,
        (fderiv ℝ (fderiv ℝ (v σ)) y' (unitVector j) (unitVector i)) i = 0 :=
      fun j y' => trace_deriv_zero dD1 (fun x => hdiv σ x) y' (unitVector j)
    have hB : ∀ j : Fin 3, ∑ i : Fin 3,
        (fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y (unitVector j) (unitVector j) (unitVector i)) i = 0 := by
      intro j
      have h := trace_deriv_zero (g := fun y' => fderiv ℝ (fderiv ℝ (v σ)) y' (unitVector j))
        (dD2.clm_apply (differentiable_const _)) (hA j) y (unitVector j)
      rwa [fderiv_apply_const (dD2 y)] at h
    have hdu : ∀ i : Fin 3, fderiv ℝ (fun y => -secondDerivTrace (secondDerivField v σ y)) y (unitVector i)
        = -∑ j : Fin 3, fderiv ℝ (fderiv ℝ (fderiv ℝ (v σ))) y (unitVector i) (unitVector j) (unitVector j) := by
      intro i
      have hj : ∀ j ∈ (Finset.univ : Finset (Fin 3)), DifferentiableAt ℝ
          (fun y => fderiv ℝ (fderiv ℝ (v σ)) y (unitVector j) (unitVector j)) y :=
        fun j _ => ((dD2 y).clm_apply (differentiableAt_const _)).clm_apply (differentiableAt_const _)
      have e : (fun y => -secondDerivTrace (secondDerivField v σ y))
          = fun y => -∑ j : Fin 3, fderiv ℝ (fderiv ℝ (v σ)) y (unitVector j) (unitVector j) := rfl
      rw [e, fderiv_fun_neg, neg_apply, fderiv_fun_sum hj, sum_apply]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [fderiv_apply_const (c := fun y => fderiv ℝ (fderiv ℝ (v σ)) y (unitVector j))
        ((dD2 y).clm_apply (differentiableAt_const _)), fderiv_apply_const (dD2 y)]
    have hc : ∀ (a : Fin 3 → Space) (i : Fin 3), (-(∑ j, a j)) i = -∑ j, a j i := by
      intro a i
      rw [← proj_apply, map_neg, map_sum]
      rfl
    unfold divergenceAt
    simp only [hdu, hc]
    rw [Finset.sum_neg_distrib, Finset.sum_comm, neg_eq_zero]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [← hB j]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [s12 (unitVector i), s23 (unitVector j) (unitVector i)]

def epsTerm {C : Type} (m : ModeWeights C) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    (Complex.I * (m.epsW (m.classOf ι) y : ℂ)
      * cdot (curlOfGrad (modeGrad ι (gradField v) σ y)) (curlOfGrad (modeGrad ι (gradField X) σ y))).re

def muTerm {C : Type} (m : ModeWeights C) (v X : ℝ → Space → Space) (ι : ℤ × ℤ) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
    (Complex.I * (m.muW (m.classOf ι) y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι X σ y)).re

theorem curlVec_conj (φ : ℝ) (G : Space →L[ℝ] Space) (i : Fin 3) :
    ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * axialRot (-φ) (G (axialRot φ (unitVector j))) l
      = axialRot (-φ) (curlVec G) i := by
  have h := Real.sin_sq_add_cos_sq φ
  fin_cases i <;>
  simp [axialRot, curlVec, unitVector, Fin.sum_univ_three, alternatingSymbol, map_add, map_smul, Real.cos_neg, Real.sin_neg] <;>
  ring_nf
  linear_combination ((G (EuclideanSpace.single 0 1)) 1 - (G (EuclideanSpace.single 1 1)) 0) * h

theorem modeAverage_sum {β γ : Type*} (s : Finset γ) (ι : ℤ × ℤ) (f : ℝ → ℝ → β → ℝ) (c : γ → ℝ)
    (bs : γ → β) (hf : ∀ k ∈ s, Continuous (fun p : ℝ × ℝ => f p.1 p.2 (bs k)))
    {β' : Type*} (F : ℝ → ℝ → β' → ℝ) (b' : β') (hF : ∀ τ φ, F τ φ b' = ∑ k ∈ s, c k * f τ φ (bs k)) :
    ∑ k ∈ s, (c k : ℂ) * modeAverage ι f (bs k) = modeAverage ι F b' := by
  have hE : Continuous (fun p : ℝ × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
  have hc : ∀ k ∈ s, Continuous (fun p : ℝ × ℝ =>
      (c k : ℂ) * (Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((f p.1 p.2 (bs k) : ℝ) : ℂ))) := fun k hk =>
    continuous_const.mul (hE.mul (Complex.continuous_ofReal.comp (hf k hk)))
  unfold modeAverage
  have e1 : ∀ τ φ, Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((F τ φ b' : ℝ) : ℂ)
      = ∑ k ∈ s, (c k : ℂ) * (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((f τ φ (bs k) : ℝ) : ℂ)) := by
    intro τ φ
    rw [hF, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  simp only [e1]
  have e2 : ∀ τ, ∫ φ in (0 : ℝ)..(2 * Real.pi), ∑ k ∈ s, (c k : ℂ) *
      (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ (bs k) : ℝ) : ℂ))
      = ∑ k ∈ s, (c k : ℂ) * ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ (bs k) : ℝ) : ℂ) := by
    intro τ
    have hi : ∀ k ∈ s, IntervalIntegrable (fun φ => (c k : ℂ) *
        (Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ (bs k) : ℝ) : ℂ)))
        volume 0 (2 * Real.pi) := fun k hk =>
      ((hc k hk).comp (Continuous.prodMk_right τ)).intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum hi]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  simp only [e2]
  rw [intervalIntegral.integral_finsetSum fun k hk => ?_, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [intervalIntegral.integral_const_mul]
    ring
  · refine Continuous.intervalIntegrable ?_ _ _
    refine continuous_const.mul ?_
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((f τ φ (bs k) : ℝ) : ℂ))
      (hE.mul (Complex.continuous_ofReal.comp (hf k hk))) _ _

theorem continuous_axialRot {α : Type*} [TopologicalSpace α] {f : α → ℝ} {g : α → Space}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => axialRot (f a) (g a)) := by
  have c0 : Continuous (fun a => g a 0) := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).continuous.comp hg
  have c1 : Continuous (fun a => g a 1) := (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).continuous.comp hg
  have c2 : Continuous (fun a => g a 2) := (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ).continuous.comp hg
  have cc : Continuous (fun a => Real.cos (f a)) := Real.continuous_cos.comp hf
  have cs : Continuous (fun a => Real.sin (f a)) := Real.continuous_sin.comp hf
  have e1 : Continuous (fun a => (Real.cos (f a) * g a 0 - Real.sin (f a) * g a 1) • unitVector 0) :=
    ((cc.mul c0).sub (cs.mul c1)).smul continuous_const
  have e2 : Continuous (fun a => (Real.sin (f a) * g a 0 + Real.cos (f a) * g a 1) • unitVector 1) :=
    ((cs.mul c0).add (cc.mul c1)).smul continuous_const
  have e3 : Continuous (fun a => g a 2 • unitVector 2) := c2.smul continuous_const
  unfold axialRot
  exact (e1.add e2).add e3

theorem curlOfGrad_modeGrad {X : ℝ → Space → Space} (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2))
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    curlOfGrad (modeGrad ι (gradField X) σ y)
      = modeVel ι (fun s x => curlVec (fderiv ℝ (X s) x)) σ y := by
  have d1 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (X z.1) z.2) :=
    contDiff_slice (V := X) hX (by norm_num)
  have hg : ∀ p : Fin 3 × Fin 3, Continuous (fun q : ℝ × ℝ =>
      axialRot (-q.2) (fderiv ℝ (X (σ + q.1)) (axialRot q.2 y) (axialRot q.2 (unitVector p.1))) p.2) := by
    intro p
    have hr1 : Continuous (fun q : ℝ × ℝ => axialRot q.2 y) :=
      continuous_axialRot continuous_snd continuous_const
    have hr2 : Continuous (fun q : ℝ × ℝ => axialRot q.2 (unitVector p.1)) :=
      continuous_axialRot continuous_snd continuous_const
    have h1 : Continuous (fun q : ℝ × ℝ => fderiv ℝ (X (σ + q.1)) (axialRot q.2 y)) :=
      d1.continuous.comp ((continuous_const.add continuous_fst).prodMk hr1)
    have h2 : Continuous (fun q : ℝ × ℝ =>
        fderiv ℝ (X (σ + q.1)) (axialRot q.2 y) (axialRot q.2 (unitVector p.1))) := h1.clm_apply hr2
    have h3 : Continuous (fun q : ℝ × ℝ =>
        axialRot (-q.2) (fderiv ℝ (X (σ + q.1)) (axialRot q.2 y) (axialRot q.2 (unitVector p.1)))) :=
      continuous_axialRot continuous_snd.neg h2
    exact (EuclideanSpace.proj p.2 : Space →L[ℝ] ℝ).continuous.comp h3
  funext i
  have hF : ∀ τ φ, axialRot (-φ) (curlVec (fderiv ℝ (X (σ + τ)) (axialRot φ y))) i
      = ∑ k ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), alternatingSymbol i k.1 k.2
        * axialRot (-φ) (fderiv ℝ (X (σ + τ)) (axialRot φ y) (axialRot φ (unitVector k.1))) k.2 := by
    intro τ φ
    rw [← curlVec_conj, ← Fintype.sum_prod_type']
  have key := modeAverage_sum (Finset.univ : Finset (Fin 3 × Fin 3)) ι
    (fun τ φ (ij : Fin 3 × Fin 3) =>
      axialRot (-φ) (fderiv ℝ (X (σ + τ)) (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1)
    (fun k => alternatingSymbol i k.1 k.2) (fun k => (k.2, k.1)) (fun k _ => hg k)
    (fun τ φ (j : Fin 3) => axialRot (-φ) (curlVec (fderiv ℝ (X (σ + τ)) (axialRot φ y))) j) i hF
  unfold curlOfGrad modeGrad modeVel gradField
  rw [← Fintype.sum_prod_type']
  exact key

theorem curl_square {X : ℝ → Space → Space} (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2))
    (hXp : IsTimePeriodic X) (hXR : ∃ R, ∀ σ y, R < ‖y‖ → X σ y = 0) :
    IsSquareField (fun σ y => curlVec (fderiv ℝ (X σ) y)) := by
  obtain ⟨R, hR⟩ := hXR
  have d1 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (X z.1) z.2) :=
    contDiff_slice (V := X) hX (by norm_num)
  refine square_of_continuous ?_ ?_ ⟨R, fun σ y hy => ?_⟩
  · unfold curlVec
    exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
      continuous_finsetSum _ fun l _ => continuous_const.mul
        ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp
          (d1.continuous.clm_apply continuous_const))).smul continuous_const
  · intro σ y
    have e : X (σ + 1) = X σ := funext fun x => hXp σ x
    simp only [e]
  · rw [fderiv_eq_zero_far (hR σ) hy]
    simp [curlVec]

theorem epsTerm_bound (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) :
    ∃ K, ∀ X Y : ℝ → Space → Space,
      ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2) → IsTimePeriodic X →
      (∃ R, ∀ σ y, R < ‖y‖ → X σ y = 0) →
      ContDiff ℝ 1 (fun z : ℝ × Space => Y z.1 z.2) → IsTimePeriodic Y →
      (∃ R, ∀ σ y, R < ‖y‖ → Y σ y = 0) →
      Summable (fun ι => epsTerm m v X ι) ∧
        Summable (fun ι => |epsTerm m v X ι - epsTerm m v Y ι|) ∧
        ∑' ι, |epsTerm m v X ι - epsTerm m v Y ι|
          ≤ K * Real.sqrt (periodLIntegral (fun σ y =>
            ‖curlVec (fderiv ℝ (X σ) y) - curlVec (fderiv ℝ (Y σ) y)‖ ^ 2)).toReal := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.1.of_le (by norm_cast)
  have hwm : ∀ ι, Measurable (fun y => m.epsW (m.classOf ι) y) := fun ι => by
    obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
    exact hK.continuous.measurable
  obtain ⟨K, hK⟩ := weightedMode_bound hPars (fun ι y => m.epsW (m.classOf ι) y) hwm
    (fun ι y => hm.epsW_le (m.classOf ι) y) (curl_square hv1 hv.2.1 hv.2.2.1)
  refine ⟨K, fun X Y hX hXp hXR hY hYp hYR => ?_⟩
  have e : ∀ Z : ℝ → Space → Space, ContDiff ℝ 1 (fun z : ℝ × Space => Z z.1 z.2) → ∀ ι,
      epsTerm m v Z ι = weightedModeTerm (fun ι y => m.epsW (m.classOf ι) y)
        (fun s x => curlVec (fderiv ℝ (v s) x)) (fun s x => curlVec (fderiv ℝ (Z s) x)) ι := by
    intro Z hZ ι
    unfold epsTerm weightedModeTerm
    simp only [curlOfGrad_modeGrad hv1, curlOfGrad_modeGrad hZ]
  have h := hK _ _ (curl_square hX hXp hXR) (curl_square hY hYp hYR)
  simp only [e X hX, e Y hY]
  exact h

theorem muTerm_bound (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) :
    ∃ K, ∀ X Y : ℝ → Space → Space, IsSquareField X → IsSquareField Y →
      Summable (fun ι => muTerm m v X ι) ∧
        Summable (fun ι => |muTerm m v X ι - muTerm m v Y ι|) ∧
        ∑' ι, |muTerm m v X ι - muTerm m v Y ι|
          ≤ K * Real.sqrt (periodLIntegral (fun σ y => ‖X σ y - Y σ y‖ ^ 2)).toReal := by
  have hwm : ∀ ι, Measurable (fun y => m.muW (m.classOf ι) y) := fun ι => by
    obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
    exact hK.continuous.measurable
  obtain ⟨B, hB⟩ := hm.muW_decay
  exact weightedMode_bound hPars (fun ι y => m.muW (m.classOf ι) y) hwm
    (fun ι y => (hB (m.classOf ι) y).1) (testField_square hv)

theorem norm_axialRot (φ : ℝ) (y : Space) : ‖axialRot φ y‖ = ‖y‖ := by
  have h := Real.sin_sq_add_cos_sq φ
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp [axialRot, unitVector, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * h

theorem integrable_of_continuous_far {g : ℝ × Space → ℝ} (hc : Continuous g)
    (hR : ∃ R, ∀ σ y, R < ‖y‖ → g (σ, y) = 0) :
    Integrable g ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  obtain ⟨R, hR⟩ := hR
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  have hon : IntegrableOn g (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ) volume := by
    refine (hc.continuousOn.integrableOn_compact hK).of_forall_sdiff_eq_zero
      (measurableSet_Icc.prod MeasurableSet.univ) ?_
    rintro ⟨σ, y⟩ ⟨⟨hσ, -⟩, hn⟩
    have hy : R < ‖y‖ := by
      by_contra hy
      exact hn ⟨hσ, by simpa [Metric.mem_closedBall, dist_zero_right] using not_lt.1 hy⟩
    exact hR σ y hy
  have e := periodMeasure_eq
  unfold periodMeasure at e
  rw [e]
  exact hon

theorem continuous_curl {X : ℝ → Space → Space} (hX : ContDiff ℝ 1 (fun z : ℝ × Space => X z.1 z.2)) :
    Continuous (fun z : ℝ × Space => curlVec (fderiv ℝ (X z.1) z.2)) := by
  have d1 : ContDiff ℝ 0 (fun z : ℝ × Space => fderiv ℝ (X z.1) z.2) :=
    contDiff_slice (V := X) hX (by norm_num)
  unfold curlVec
  exact continuous_finsetSum _ fun i _ => (continuous_finsetSum _ fun j _ =>
    continuous_finsetSum _ fun l _ => continuous_const.mul
      ((EuclideanSpace.proj l : Space →L[ℝ] ℝ).continuous.comp
        (d1.continuous.clm_apply continuous_const))).smul continuous_const

theorem continuous_apply_modeVel {Z : ℝ → Space → Space} (hZ : Continuous (fun z : ℝ × Space => Z z.1 z.2))
    (ι : ℤ × ℤ) (i : Fin 3) : Continuous (fun z : ℝ × Space => modeVel ι Z z.1 z.2 i) := by
  unfold modeVel modeAverage
  refine continuous_const.mul ?_
  have hg : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
      Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-p.2) (Z (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) i : ℝ) : ℂ)) := by
    have hE : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
        Complex.exp (-(((2 * Real.pi * ι.1 * p.1.2 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) := by fun_prop
    have hA : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => axialRot p.2 p.1.1.2) :=
      continuous_axialRot continuous_snd (continuous_snd.comp (continuous_fst.comp continuous_fst))
    have hZc : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ => Z (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2)) :=
      hZ.comp (((continuous_fst.comp (continuous_fst.comp continuous_fst)).add
        (continuous_snd.comp continuous_fst)).prodMk hA)
    have hB : Continuous (fun p : ((ℝ × Space) × ℝ) × ℝ =>
        axialRot (-p.2) (Z (p.1.1.1 + p.1.2) (axialRot p.2 p.1.1.2))) :=
      continuous_axialRot continuous_snd.neg hZc
    exact hE.mul (Complex.continuous_ofReal.comp
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp hB))
  have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (q : (ℝ × Space) × ℝ) (φ : ℝ) =>
      Complex.exp (-(((2 * Real.pi * ι.1 * q.2 + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-φ) (Z (q.1.1 + q.2) (axialRot φ q.1.2)) i : ℝ) : ℂ)) hg 0 (2 * Real.pi)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (μ := volume) (f := fun (z : ℝ × Space) (τ : ℝ) => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-φ) (Z (z.1 + τ) (axialRot φ z.2)) i : ℝ) : ℂ)) h1 0 1

theorem modeIntegrands_integrable {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => (Complex.I * (m.epsW (m.classOf ι) z.2 : ℂ)
        * cdot (curlOfGrad (modeGrad ι (gradField v) z.1 z.2))
          (curlOfGrad (modeGrad ι (gradField ψ) z.1 z.2))).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) ∧
    Integrable (fun z : ℝ × Space => (Complex.I * (m.muW (m.classOf ι) z.2 : ℂ)
        * cdot (modeVel ι v z.1 z.2) (modeVel ι ψ z.1 z.2)).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hv1 : ContDiff ℝ 1 (fun z : ℝ × Space => v z.1 z.2) := hv.1.of_le (by norm_cast)
  have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2) := hψ.1.of_le (by norm_cast)
  obtain ⟨Rv, hRv⟩ := hv.2.2.1
  obtain ⟨Rψ, hRψ⟩ := hψ.2.2.1
  have hcv := continuous_curl hv1
  have hcψ := continuous_curl hψ1
  have hε : Continuous (fun y => m.epsW (m.classOf ι) y) := by
    obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
    exact hK.continuous
  have hμ : Continuous (fun y => m.muW (m.classOf ι) y) := by
    obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
    exact hK.continuous
  have hzero : ∀ {Z : ℝ → Space → Space} {R : ℝ}, (∀ σ y, R < ‖y‖ → Z σ y = 0) →
      ∀ σ y, R < ‖y‖ → modeVel ι Z σ y = 0 := by
    intro Z R hZ σ y hy
    funext i
    unfold modeVel modeAverage
    have e : ∀ τ φ, axialRot (-φ) (Z (σ + τ) (axialRot φ y)) i = 0 := by
      intro τ φ
      rw [hZ _ _ (by rw [norm_axialRot]; exact hy)]
      simp [axialRot]
    simp [e]
  have hfarψ := hzero (fun σ y hy => by
    show curlVec (fderiv ℝ (ψ σ) y) = 0
    rw [fderiv_eq_zero_far (hRψ σ) hy]; simp [curlVec])
  constructor
  · refine integrable_of_continuous_far ?_ ⟨Rψ, fun σ y hy => ?_⟩
    · simp only [curlOfGrad_modeGrad hv1, curlOfGrad_modeGrad hψ1]
      unfold cdot
      refine Complex.continuous_re.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hε.comp continuous_snd))).mul
        (continuous_finsetSum _ fun j _ => (continuous_apply_modeVel hcv ι j).mul
          (Complex.continuous_conj.comp (continuous_apply_modeVel hcψ ι j))))
    · simp only [curlOfGrad_modeGrad hv1, curlOfGrad_modeGrad hψ1]
      rw [hfarψ σ y hy]
      simp [cdot]
  · refine integrable_of_continuous_far ?_ ⟨Rψ, fun σ y hy => ?_⟩
    · unfold cdot
      refine Complex.continuous_re.comp ((continuous_const.mul
        (Complex.continuous_ofReal.comp (hμ.comp continuous_snd))).mul
        (continuous_finsetSum _ fun j _ => (continuous_apply_modeVel hv1.continuous ι j).mul
          (Complex.continuous_conj.comp (continuous_apply_modeVel hψ1.continuous ι j))))
    · rw [hzero hRψ σ y hy]
      simp [cdot]

theorem modeSum_split (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    modeSum m v ψ = ∑' ι, epsTerm m v ψ ι + ∑' ι, muTerm m v ψ ι := by
  obtain ⟨K1, hE⟩ := epsTerm_bound hPars m P b w hm hv
  obtain ⟨K2, hMu⟩ := muTerm_bound hPars m P b w hm hv
  have hψ1 : ContDiff ℝ 1 (fun z : ℝ × Space => ψ z.1 z.2) := hψ.1.of_le (by norm_cast)
  have sE := (hE ψ ψ hψ1 hψ.2.1 hψ.2.2.1 hψ1 hψ.2.1 hψ.2.2.1).1
  have sM := (hMu ψ ψ (testField_square hψ) (testField_square hψ)).1
  rw [← sE.tsum_add sM]
  refine tsum_congr fun ι => ?_
  obtain ⟨iE, iM⟩ := modeIntegrands_integrable m P b w hm hv hψ ι
  unfold epsTerm muTerm
  rw [← integral_prod _ iE, ← integral_prod _ iM, ← integral_add iE iM]
  exact (integral_prod _ (iE.add iM)).symm

theorem sqrt_toReal_tendsto {L : ℕ → ℝ≥0∞} (h : Filter.Tendsto L Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => Real.sqrt (L n).toReal) Filter.atTop (nhds 0) := by
  have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
  have hq := (Real.continuous_sqrt.tendsto _).comp ht
  simpa only [Function.comp_def, ENNReal.toReal_zero, Real.sqrt_zero] using hq

theorem tsum_tendsto_of_bound {a : ℕ → ℤ × ℤ → ℝ} {c : ℤ × ℤ → ℝ} {g : ℕ → ℝ}
    (ha : ∀ n, Summable (a n)) (hc : Summable c) (hd : ∀ n, Summable (fun ι => |a n ι - c ι|))
    (hb : ∀ n, ∑' ι, |a n ι - c ι| ≤ g n) (hg : Filter.Tendsto g Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∑' ι, a n ι) Filter.atTop (nhds (∑' ι, c ι)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hg
  rw [← (ha n).tsum_sub hc]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · simpa only [Real.norm_eq_abs] using hd n
  · simpa only [Real.norm_eq_abs] using hb n

theorem modeSum_tendsto (hPars : ModeSquareSumHolds) {C : Type} (m : ModeWeights C) (P : ℝ)
    (b : FlowBounds C) (w : Space → ℝ) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    (hv : IsPeriodicTestField v) {F Q : ℝ → Space → Space}
    (hF : ContDiff ℝ 1 (fun z : ℝ × Space => F z.1 z.2)) (hFp : IsTimePeriodic F)
    (hFR : ∃ R, ∀ σ y, R < ‖y‖ → F σ y = 0) (hQ : IsSolenoidalPartOf F Q) (ψ : ℕ → ℝ → Space → Space)
    (hψ : ∀ n, IsPeriodicTestField (ψ n))
    (h1 : Filter.Tendsto (fun n => periodLIntegral (fun σ y => ‖ψ n σ y - Q σ y‖ ^ 2))
      Filter.atTop (nhds 0))
    (h2 : Filter.Tendsto (fun n => periodLIntegral (fun σ y =>
        ‖curlVec (fderiv ℝ (ψ n σ) y) - curlVec (fderiv ℝ (F σ) y)‖ ^ 2)) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => modeSum m v (ψ n)) Filter.atTop
      (nhds (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v F
        + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q)) := by
  obtain ⟨K1, hE⟩ := epsTerm_bound hPars m P b w hm hv
  obtain ⟨K2, hMu⟩ := muTerm_bound hPars m P b w hm hv
  have hψ1 : ∀ n, ContDiff ℝ 1 (fun z : ℝ × Space => ψ n z.1 z.2) :=
    fun n => (hψ n).1.of_le (by norm_cast)
  have hQs := square_of_solenoidal hQ
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => testField_square (hψ n)
  have hEn := fun n => hE (ψ n) F (hψ1 n) (hψ n).2.1 (hψ n).2.2.1 hF hFp hFR
  have hMn := fun n => hMu (ψ n) Q (hψs n) hQs
  have tE := tsum_tendsto_of_bound (fun n => (hEn n).1) (hE F F hF hFp hFR hF hFp hFR).1
    (fun n => (hEn n).2.1) (fun n => (hEn n).2.2)
    ((sqrt_toReal_tendsto h2).const_mul K1 |>.congr' (Filter.Eventually.of_forall fun n => rfl)
      |> fun t => by simpa only [mul_zero] using t)
  have tM := tsum_tendsto_of_bound (fun n => (hMn n).1) (hMu Q Q hQs hQs).1
    (fun n => (hMn n).2.1) (fun n => (hMn n).2.2)
    (by simpa only [mul_zero] using (sqrt_toReal_tendsto h1).const_mul K2)
  have t := tE.add tM
  refine t.congr fun n => ?_
  exact (modeSum_split hPars m P b w hm hv (hψ n)).symm

theorem solenoidal_multiplier_pairing (hPars : ModeSquareSumHolds) (hDens : CurlGraphDensityHolds)
    {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C)
    (w : Space → ℝ) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (v : ℝ → Space → Space) (hv : IsPeriodicTestField v)
    (M Q : ℝ → Space → Space) (hM : m.IsMultiplierField v (gradField v) (secondDerivField v) M)
    (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    periodPairing Q M =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)))
        + epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
        + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q := by
  have hFc := smoothRight_contDiff P hW hv
  have hFp := smoothRight_periodic P hWp hv
  have hFR := smoothRight_far P W hv
  obtain ⟨ψ, hψt, hL2, hcurl⟩ := hDens (smoothRight P W v) Q hFc hFp hFR hQ
  have hQs := square_of_solenoidal hQ
  have hMs : IsSquareField M := ⟨hM.1, hM.2.1, hM.2.2.1⟩
  have hψs : ∀ n, IsSquareField (ψ n) := fun n => testField_square (hψt n)
  have hLt := sumSecondPartials_testField hv
  have hLs := testField_square hLt
  have hseq : ∀ n, periodPairing M (ψ n) =
      periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) (ψ n) + modeSum m v (ψ n) :=
    fun n => hM.2.2.2.2 (ψ n) (hψt n)
  have t1 := pairing_tendsto hMs hQs hψs hL2
  have t2 := pairing_tendsto hLs hQs hψs hL2
  have t3 := modeSum_tendsto hPars m P b w hm hv hFc hFp hFR hQ ψ hψt hL2 hcurl
  have t4 := t2.add t3
  have t5 : Filter.Tendsto (fun n => periodPairing M (ψ n)) Filter.atTop
      (nhds (periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q
        + (epsPairing (fun ι y => m.epsW (m.classOf ι) y) v (smoothRight P W v)
          + muPairing (fun ι y => m.muW (m.classOf ι) y) v Q))) := by
    refine t4.congr fun n => ?_
    rw [hseq n]
  have hlim := tendsto_nhds_unique t1 t5
  have hL : periodPairing (fun σ y => -secondDerivTrace (secondDerivField v σ y)) Q =
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y) (-secondDerivTrace (secondDerivField v σ y)) := by
    rw [pairing_comm hLs hQs]
    exact hQ.2.2.2.2 _ hLt
  rw [pairing_comm hQs hMs, hlim, hL]
  ring

end PairingSplitInternal

theorem modePairingSplitHolds_of (hPars : ModeSquareSumHolds) (hSolMode : SolenoidalModeHolds)
    (hDens : CurlGraphDensityHolds) : ModePairingSplitHolds := by
  intro C m P b w W w₀ epsSup epsGradSup ratio hm hb hW hWp hWdiv hWdecay hwb v hv M Q hM hQ
  rw [PairingSplitInternal.pairing_eq_solenoidal hSolMode (PairingSplitInternal.smoothRight_square P hW hWp hv) hQ
    (PairingSplitInternal.solenoidal_self_of_multiplier m hM)]
  exact PairingSplitInternal.solenoidal_multiplier_pairing hPars hDens m P b w W hm hW hWp v hv M Q hM hQ

end Coercive

end Breakdown

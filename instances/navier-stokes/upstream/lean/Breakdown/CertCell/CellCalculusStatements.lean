import Breakdown.CertCell.BridgeCreditStatements
import Breakdown.CertCell.Defs
import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.ResolvedEnergySt
import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.EnergyDefs
import Breakdown.CertCell.TailStatements
import Breakdown.CertCell.CouplingStatements
import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.StatementDefs

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def harmonicMode (ν n : ℤ) : ℤ × ℤ := (n, (n + ν) / 2)

def harmonicCos (ν : ℤ) {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (f : ℝ → Space → β) (y : Space) : β :=
  ∫ τ in Set.Icc (0 : ℝ) 1, Real.cos (2 * Real.pi * ν * τ) • f τ y

def harmonicSin (ν : ℤ) {β : Type*} [NormedAddCommGroup β] [NormedSpace ℝ β]
    (f : ℝ → Space → β) (y : Space) : β :=
  -∫ τ in Set.Icc (0 : ℝ) 1, Real.sin (2 * Real.pi * ν * τ) • f τ y

def HarmonicModeStatement : Prop :=
  ∀ (m : ℕ) (ν n : ℤ), Even (n + ν) →
    labelHarmonic m (harmonicMode ν n) = (ν, n * m) ∧ labelTime (harmonicMode ν n) = ν ∧
      labelTime (labelFlip (harmonicMode ν n)) = ν

def slopeAt (m : ℕ) (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b c : Fin 3) (p : ℝ × ℝ) : ℂ :=
  labelHess m ι H p (a, c, b)

def turnedSlopeAt (m : ℕ) (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (a b : Fin 3) (p : ℝ × ℝ) : ℂ :=
  (p.1 : ℂ) * slopeAt m ι H a b 1 p

def gradArray (m : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    Fin 3 → Fin 3 → ℂ :=
  fun a b => gradAt m ι G a b p

def velArray (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun a => velAt m ι v a p

def slopeSq (m : ℕ) (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ‖slopeAt m ι H a b c p‖ ^ 2

def curlSlopeSq (m : ℕ) (ι : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ c : Fin 3, ‖curlComp (fun a b => slopeAt m ι H a b c p) i‖ ^ 2

structure IsPeriodicSecondOrder (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop where
  measurable_velocity : AEStronglyMeasurable (fun z : ℝ × Space => v z.1 z.2) volume
  measurable_gradient : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume
  measurable_secondDeriv : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume
  periodic_velocity : IsTimePeriodic v
  periodic_gradient : IsTimePeriodic G
  periodic_secondDeriv : IsTimePeriodic H
  weak_gradient : ∀ᵐ σ, IsWeakGradient (v σ) (G σ)
  weak_secondDeriv : ∀ᵐ σ, ∀ j : Fin 3,
    IsWeakGradient (fun y => G σ y (unitVector j)) (fun y => (H σ y).flip (unitVector j))
  divergence_free : ∀ᵐ σ, ∀ᵐ y, ∑ i : Fin 3, (G σ y (unitVector i)) i = 0
  sixth_power_integrated : ∫⁻ σ in Set.Icc (0 : ℝ) 1, (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ ((1 : ℝ) / 6) < ⊤
  gradient_finite : periodLIntegral (fun σ y => matSq (G σ y)) < ⊤
  hessian_finite : periodLIntegral (fun σ y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H σ y (unitVector i) (unitVector j)‖ ^ 2) < ⊤

structure IsPeriodicPressure (Pg : ℝ → Space → Space) : Prop where
  measurable : AEStronglyMeasurable (fun z : ℝ × Space => Pg z.1 z.2) volume
  periodic : IsTimePeriodic Pg
  local_square : ∀ R : ℝ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
    ENNReal.ofReal (‖Pg σ y‖ ^ 2) < ⊤
  harmonic_gradient : ∀ ν : ℤ, IsGradientField (harmonicCos ν Pg) ∧ IsGradientField (harmonicSin ν Pg)

def HarmonicLiftStatement : Prop :=
  ∀ (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsPeriodicSecondOrder v G H →
    ∀ ν : ℤ,
      IsLocalSecondOrderField (harmonicCos ν v) (harmonicCos ν G) (harmonicCos ν H) ∧
      IsLocalSecondOrderField (harmonicSin ν v) (harmonicSin ν G) (harmonicSin ν H) ∧
      ∀ n : ℤ, Even (n + ν) → ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 →
        (∀ a, velAt m (harmonicMode ν n) v a p
            = modeVec m n (harmonicCos ν v) p.1 p.2 a + Complex.I * modeVec m n (harmonicSin ν v) p.1 p.2 a) ∧
        (∀ a b, gradAt m (harmonicMode ν n) G a b p
            = gradMode m n (harmonicCos ν G) a b p + Complex.I * gradMode m n (harmonicSin ν G) a b p) ∧
        (∀ a b c, slopeAt m (harmonicMode ν n) H a b c p
            = modeThird m n (harmonicCos ν H) a b c p + Complex.I * modeThird m n (harmonicSin ν H) a b c p)

def HarmonicPressureLiftStatement : Prop :=
  ∀ (m : ℕ) (Pg : ℝ → Space → Space), IsPeriodicPressure Pg →
    ∀ ν : ℤ, ∀ n : ℤ, Even (n + ν) → ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), 0 < p.1 → ∀ a,
      velAt m (harmonicMode ν n) Pg a p
        = modeVec m n (harmonicCos ν Pg) p.1 p.2 a + Complex.I * modeVec m n (harmonicSin ν Pg) p.1 p.2 a

def cosTuple (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : FieldTuple 0 :=
  (harmonicCos ν v, harmonicCos ν G, harmonicCos ν H, 0, harmonicCos ν Pg)

def sinTuple (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : FieldTuple 0 :=
  (harmonicSin ν v, harmonicSin ν G, harmonicSin ν H, 0, harmonicSin ν Pg)

def harmonicData (L : CellLayout) (ν : ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : L.Datum → ℂ :=
  fun d => L.trueData (cosTuple ν v G H Pg) d + Complex.I * L.trueData (sinTuple ν v G H Pg) d

def modeData (A : CellModeLayouts) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : (A.layout ι).Datum → ℂ :=
  harmonicData (A.layout ι) (labelTime ι) v G H Pg

def HarmonicRelationsStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (modes : Finset ℤ) (L : CellLayout), IsHarmonicLayout m K B modes L →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ ν : ℤ,
        ∀ ρ : L.RelIndex, ∑ d, L.relationRow ρ d * harmonicData L ν v G H Pg d = 0

theorem harmonicRelations_of (h1 : LocalRelationsHoldStatement) (h2 : HarmonicLiftStatement)
    (h3 : HarmonicPressureLiftStatement) : HarmonicRelationsStatement := by
  intro m K B modes L hL v G H Pg hP hPg ν ρ
  obtain ⟨c, S, _, _, hcl⟩ := hL
  obtain ⟨hc, hs, _⟩ := h2 m v G H hP ν
  have hac : IsLocalAdmissible (cosTuple ν v G H Pg) := ⟨hc, (hPg.harmonic_gradient ν).1⟩
  have has : IsLocalAdmissible (sinTuple ν v G H Pg) := ⟨hs, (hPg.harmonic_gradient ν).2⟩
  have e1 := h1 c K S B L hcl _ hac ρ
  have e2 := h1 c K S B L hcl _ has ρ
  unfold harmonicData
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ Complex.I, ← Finset.mul_sum, e1, e2, mul_zero,
    add_zero]

def HarmonicSideDataStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B L.modes L →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ (ν : ℤ) (n : L.modes), Even ((n : ℤ) + ν) →
        (∀ (s : Fin L.segCount) (a : Fin 3) (d : Fin (L.degSide + 2)),
          harmonicData L ν v G H Pg (CellDatum.sideVelocity n s a d)
            = (L.segment s).moment false (fun p => velAt m (harmonicMode ν n) v a p)
                (gradAt m (harmonicMode ν n) G a 0) (gradAt m (harmonicMode ν n) G a 2) (d : ℕ)) ∧
        (∀ (s : Fin L.segCount) (a : Fin 3) (d : Fin (L.degSide + 1)),
          harmonicData L ν v G H Pg (CellDatum.sideGradient n s a d)
            = if (L.segment s).radial then
                (L.segment s).moment true (gradAt m (harmonicMode ν n) G a 0)
                  (slopeAt m (harmonicMode ν n) H a 0 0) (slopeAt m (harmonicMode ν n) H a 0 2) (d : ℕ)
              else (L.segment s).moment true (gradAt m (harmonicMode ν n) G a 2)
                  (slopeAt m (harmonicMode ν n) H a 2 0) (slopeAt m (harmonicMode ν n) H a 2 2) (d : ℕ))

def HarmonicParamStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (modes : Finset ℤ) (L : CellLayout), IsHarmonicLayout m K B modes L →
    ∀ (P : ParamData L.Datum) (sel : Fin P.relCount → L.RelIndex), IsCellParam L P sel →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ ν : ℤ,
        P.param (harmonicData L ν v G H Pg) = harmonicData L ν v G H Pg

theorem harmonicParam_of (h1 : HarmonicRelationsStatement) (h2 : ParamRecoverStatement) :
    HarmonicParamStatement := by
  intro m K B modes L hL P sel hP v G H Pg hv hPg ν
  refine h2 P hP.param (harmonicData L ν v G H Pg) ?_
  funext i
  rw [Pi.zero_apply, Matrix.mulVec, dotProduct, hP.rows i]
  exact h1 m K B modes L hL v G H Pg hv hPg ν (sel i)

def labelStrainEnergy (K : CellBox) (m : ℕ) (ι : ℤ × ℤ) (Q q : ℕ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (K.radialEnergy Q q (gradAt m ι G a b) (slopeAt m ι H a b 0)
      + K.heightEnergy Q q (gradAt m ι G a b) (slopeAt m ι H a b 2)
      + K.angularEnergy Q (turnedSlopeAt m ι H a b))

def labelVorticityEnergy (K : CellBox) (m : ℕ) (ι : ℤ × ℤ) (Q q : ℕ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ i : Fin 3,
    (K.radialEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
        (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
      + K.heightEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
        (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
      + K.angularEnergy Q (fun p => curlComp (fun a b => turnedSlopeAt m ι H a b p) i))

def labelStrainTail (K : CellBox) (m : ℕ) (ι : ℤ × ℤ) (Q : ℕ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3,
    (K.tailGradWeight Q (gradAt m ι G a b) (slopeAt m ι H a b 0) (slopeAt m ι H a b 2)
      + CellBox.angularWeight K ι.1 * K.tailNormSq Q (turnedSlopeAt m ι H a b))

def labelVorticityTail (K : CellBox) (m : ℕ) (ι : ℤ × ℤ) (Q : ℕ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ i : Fin 3,
    (K.tailGradWeight Q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
        (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
        (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
      + CellBox.angularWeight K ι.1 * K.tailNormSq Q (fun p => curlComp (fun a b => turnedSlopeAt m ι H a b p) i))

def LabelModeFactsStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsPeriodicSecondOrder v G H →
    ∀ (ι : ℤ × ℤ) (C : Fin 3 → Fin 3 → ℂ),
      let F : ℝ × ℝ → ℂ := fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m ι G a b p
      let Fc : Fin 3 → ℝ × ℝ → ℂ := fun c p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b c p
      AEStronglyMeasurable F (volume.restrict K.rect) ∧
      IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect ∧
      (∀ c, AEStronglyMeasurable (Fc c) (volume.restrict K.rect) ∧
        IntegrableOn (fun p => p.1 * ‖Fc c p‖ ^ 2) K.rect) ∧
      (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fc 0 p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) ∧
      (∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fc 2 p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p)

def LabelResolvedEnergyStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (Q q : ℕ),
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsPeriodicSecondOrder v G H →
      ∀ ι : ℤ × ℤ, (K.IsAxis → ι.1 = 0) →
        labelStrainEnergy K m ι Q q G H + labelStrainTail K m ι Q G H
            ≤ ∫ p in K.rect, p.1 * slopeSq m ι H p ∧
          labelVorticityEnergy K m ι Q q G H + labelVorticityTail K m ι Q G H
            ≤ ∫ p in K.rect, p.1 * curlSlopeSq m ι H p

theorem labelModeFacts_of (h1 : HarmonicLiftStatement) (h2 : LocalModeSquareIntegrableStatement)
    (h3 : LocalModeRadialPartsStatement) (h4 : LocalModeHeightPartsStatement) : LabelModeFactsStatement := by
  intro K hK m v G H hP ι C
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hrc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hfst : ∀ p ∈ K.rect, 0 ≤ p.1 := fun p hp => hK.r_order.1.trans hp.1.1
  have hlwe : ∀ r, K.lineWeight r = if K.r₁ = 0 then r else 1 := fun r => rfl
  have hlw : ∀ p ∈ K.rect, 0 ≤ K.lineWeight p.1 := by
    intro p hp
    rw [hlwe]
    split_ifs
    · exact hfst p hp
    · exact zero_le_one
  have hlwc : Continuous fun p : ℝ × ℝ => K.lineWeight p.1 := by
    by_cases h0 : K.r₁ = 0
    · rw [show (fun p : ℝ × ℝ => K.lineWeight p.1) = fun p => p.1 from
        funext fun p => by rw [hlwe, if_pos h0]]
      exact continuous_fst
    · rw [show (fun p : ℝ × ℝ => K.lineWeight p.1) = fun _ => 1 from
        funext fun p => by rw [hlwe, if_neg h0]]
      exact continuous_const
  obtain ⟨cw, hcw0, hcw⟩ : ∃ cw : ℝ, 0 ≤ cw ∧ ∀ p ∈ K.rect, K.lineWeight p.1 ≤ cw * p.1 := by
    by_cases h0 : K.r₁ = 0
    · exact ⟨1, zero_le_one, fun p _ => by rw [hlwe, if_pos h0, one_mul]⟩
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
      refine ⟨1 / K.r₁, by positivity, fun p hp => ?_⟩
      rw [hlwe, if_neg h0, div_mul_eq_mul_div, one_mul, le_div_iff₀ hr, one_mul]
      exact hp.1.1
  have key : ∀ (w : ℝ × ℝ → ℝ) (f g : ℝ × ℝ → ℂ) (c : ℝ), Continuous w → (∀ p ∈ K.rect, 0 ≤ w p) →
      AEStronglyMeasurable f (volume.restrict K.rect) → Continuous g →
      IntegrableOn (fun p => w p * ‖f p‖ ^ 2) K.rect → (∀ p ∈ K.rect, ‖g p‖ ≤ c * w p) →
      IntegrableOn (fun p => f p * g p) K.rect := by
    intro w f g c hw hw0 hf hg hfi hb
    have hwi : IntegrableOn w K.rect := hw.continuousOn.integrableOn_compact hrc
    refine Integrable.mono' ((hwi.add hfi).const_mul (|c| / 2)) (hf.mul hg.aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hrm] with p hp
    have h0 := hw0 p hp
    have hc : ‖g p‖ ≤ |c| * w p := (hb p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self c) h0)
    have hf1 : ‖f p‖ ≤ (1 + ‖f p‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖f p‖ - 1)]
    show ‖f p * g p‖ ≤ |c| / 2 * (w p + w p * ‖f p‖ ^ 2)
    rw [norm_mul]
    calc ‖f p‖ * ‖g p‖ ≤ ‖f p‖ * (|c| * w p) := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
      _ = |c| * (w p * ‖f p‖) := by ring
      _ ≤ |c| * (w p * ((1 + ‖f p‖ ^ 2) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hf1 h0) (abs_nonneg c)
      _ = |c| / 2 * (w p + w p * ‖f p‖ ^ 2) := by ring
  have hpd : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → ∀ r z : ℝ,
      HasDerivAt (fun r : ℝ => ψ (r, z)) (fderiv ℝ ψ (r, z) (1, 0)) r := by
    intro ψ hψ r z
    have hd := ((hψ.differentiable one_ne_zero) (r, z)).hasFDerivAt
    exact hd.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r z))
  have hzd : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → ∀ r z : ℝ,
      HasDerivAt (fun z : ℝ => ψ (r, z)) (fderiv ℝ ψ (r, z) (0, 1)) z := by
    intro ψ hψ r z
    have hd := ((hψ.differentiable one_ne_zero) (r, z)).hasFDerivAt
    exact hd.comp_hasDerivAt z ((hasDerivAt_const z r).prodMk (hasDerivAt_id z))
  have hfc : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → ∀ u : ℝ × ℝ, Continuous fun p => fderiv ℝ ψ p u :=
    fun ψ hψ u => (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hbase : ∀ (v' : Space → Space) (G' : Space → (Space →L[ℝ] Space))
      (H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsLocalSecondOrderField v' G' H' →
      ∀ (n : ℤ) (ψ : ℝ × ℝ → ℂ), ContDiff ℝ 1 ψ →
      (∀ c, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * comboThird C m n H' c p * ψ p) K.rect) ∧
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * comboGrad C m n G' p * CellBox.heightDeriv ψ p) K.rect ∧
      ((∀ z, ψ (K.r₁, z) = 0) → IntegrableOn (fun p => comboGrad C m n G' p *
          CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p) K.rect) := by
    intro v' G' H' hs n ψ hψ
    obtain ⟨hGm, hGi, hT⟩ := h2 K hK m v' G' H' hs n C
    have hψc : Continuous ψ := hψ.continuous
    obtain ⟨M, hM⟩ := hrc.exists_bound_of_continuousOn hψc.continuousOn
    obtain ⟨M1, hStrain⟩ := hrc.exists_bound_of_continuousOn (hfc ψ hψ (1, 0)).continuousOn
    obtain ⟨M2, hM2⟩ := hrc.exists_bound_of_continuousOn (hfc ψ hψ (0, 1)).continuousOn
    refine ⟨fun c => ?_, ?_, fun hb => ?_⟩
    · have e : (fun p => (K.lineWeight p.1 : ℂ) * comboThird C m n H' c p * ψ p)
          = fun p => comboThird C m n H' c p * ((K.lineWeight p.1 : ℂ) * ψ p) := by
        funext p
        ring
      rw [e]
      refine key (fun p => p.1) _ _ (cw * M) continuous_fst hfst (hT c).1
        ((Complex.continuous_ofReal.comp hlwc).mul hψc) (hT c).2 (fun p hp => ?_)
      show ‖(K.lineWeight p.1 : ℂ) * ψ p‖ ≤ cw * M * p.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlw p hp)]
      calc K.lineWeight p.1 * ‖ψ p‖ ≤ (cw * p.1) * M :=
            mul_le_mul (hcw p hp) (hM p hp) (norm_nonneg _) (mul_nonneg hcw0 (hfst p hp))
        _ = cw * M * p.1 := by ring
    · have e : (fun p => (K.lineWeight p.1 : ℂ) * comboGrad C m n G' p * CellBox.heightDeriv ψ p)
          = fun p => comboGrad C m n G' p * ((K.lineWeight p.1 : ℂ) * fderiv ℝ ψ p (0, 1)) := by
        funext p
        rw [CellBox.heightDeriv, (hzd ψ hψ p.1 p.2).deriv, Prod.mk.eta]
        ring
      rw [e]
      refine key (fun p => K.lineWeight p.1) _ _ M2 hlwc hlw hGm
        ((Complex.continuous_ofReal.comp hlwc).mul (hfc ψ hψ (0, 1))) hGi (fun p hp => ?_)
      show ‖(K.lineWeight p.1 : ℂ) * fderiv ℝ ψ p (0, 1)‖ ≤ M2 * K.lineWeight p.1
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlw p hp)]
      exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_right (hM2 p hp) (hlw p hp))
    · by_cases h0 : K.r₁ = 0
      · have e : ∀ p : ℝ × ℝ, CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p
            = ψ p + (K.lineWeight p.1 : ℂ) * fderiv ℝ ψ p (1, 0) := by
          intro p
          have h1 : HasDerivAt (fun r : ℝ => (K.lineWeight r : ℂ)) 1 p.1 := by
            have hf : (fun r : ℝ => (K.lineWeight r : ℂ)) = fun r : ℝ => (r : ℂ) := by
              funext r
              rw [hlwe, if_pos h0]
            rw [hf]
            simpa using (hasDerivAt_id p.1).ofReal_comp
          have hd : HasDerivAt (fun r : ℝ => (K.lineWeight r : ℂ) * ψ (r, p.2))
              (1 * ψ (p.1, p.2) + (K.lineWeight p.1 : ℂ) * fderiv ℝ ψ (p.1, p.2) (1, 0)) p.1 :=
            h1.mul (hpd ψ hψ p.1 p.2)
          simp only [CellBox.radialDeriv]
          rw [hd.deriv, one_mul, Prod.mk.eta]
        have e' : (fun p => comboGrad C m n G' p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p)
            = fun p => comboGrad C m n G' p * (ψ p + (K.lineWeight p.1 : ℂ) * fderiv ℝ ψ p (1, 0)) :=
          funext fun p => by rw [e p]
        rw [e']
        refine key (fun p => K.lineWeight p.1) _ _ (2 * M1) hlwc hlw hGm
          (hψc.add ((Complex.continuous_ofReal.comp hlwc).mul (hfc ψ hψ (1, 0)))) hGi (fun p hp => ?_)
        show ‖ψ p + (K.lineWeight p.1 : ℂ) * fderiv ℝ ψ p (1, 0)‖ ≤ 2 * M1 * K.lineWeight p.1
        have hlwp : K.lineWeight p.1 = p.1 := by rw [hlwe, if_pos h0]
        have hbd : ∀ x ∈ Set.Ico (0 : ℝ) p.1, ‖fderiv ℝ ψ (x, p.2) (1, 0)‖ ≤ M1 := by
          intro x hx
          apply hStrain (x, p.2)
          refine ⟨⟨?_, hx.2.le.trans hp.1.2⟩, hp.2⟩
          rw [h0]
          exact hx.1
        have hseg := norm_image_sub_le_of_norm_deriv_le_segment' (a := 0) (b := p.1)
          (f := fun r : ℝ => ψ (r, p.2)) (fun x _ => (hpd ψ hψ x p.2).hasDerivWithinAt) hbd p.1
          ⟨hfst p hp, le_rfl⟩
        have h0z : ψ (0, p.2) = 0 := by
          rw [← h0]
          exact hb p.2
        simp only [h0z, sub_zero, Prod.mk.eta] at hseg
        rw [hlwp]
        calc ‖ψ p + (p.1 : ℂ) * fderiv ℝ ψ p (1, 0)‖ ≤ ‖ψ p‖ + ‖(p.1 : ℂ) * fderiv ℝ ψ p (1, 0)‖ :=
              norm_add_le _ _
          _ ≤ M1 * p.1 + p.1 * M1 := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hfst p hp)]
              exact add_le_add hseg (mul_le_mul_of_nonneg_left (hStrain p hp) (hfst p hp))
          _ = 2 * M1 * p.1 := by ring
      · have hfun : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * ψ p) = ψ := by
          funext p
          rw [hlwe, if_neg h0, Complex.ofReal_one, one_mul]
        rw [hfun]
        have e : (fun p => comboGrad C m n G' p * CellBox.radialDeriv ψ p)
            = fun p => comboGrad C m n G' p * fderiv ℝ ψ p (1, 0) := by
          funext p
          rw [CellBox.radialDeriv, (hpd ψ hψ p.1 p.2).deriv, Prod.mk.eta]
        rw [e]
        refine key (fun p => K.lineWeight p.1) _ _ M1 hlwc hlw hGm (hfc ψ hψ (1, 0)) hGi (fun p hp => ?_)
        show ‖fderiv ℝ ψ p (1, 0)‖ ≤ M1 * K.lineWeight p.1
        rw [hlwe, if_neg h0, mul_one]
        exact hStrain p hp
  have wsi : ∀ {w : ℝ × ℝ → ℝ}, Continuous w → (∀ p ∈ K.rect, 0 ≤ w p) →
      ∀ {f g h : ℝ × ℝ → ℂ}, AEStronglyMeasurable f (volume.restrict K.rect) →
      (∀ᵐ p ∂(volume.restrict K.rect), f p = g p + Complex.I * h p) →
      IntegrableOn (fun p => w p * ‖g p‖ ^ 2) K.rect → IntegrableOn (fun p => w p * ‖h p‖ ^ 2) K.rect →
      IntegrableOn (fun p => w p * ‖f p‖ ^ 2) K.rect := by
    intro w hwc hw f g h hf hfe hg hh
    refine Integrable.mono' ((hg.const_mul 2).add (hh.const_mul 2))
      (hwc.aestronglyMeasurable.mul (hf.norm.pow 2)) ?_
    filter_upwards [hfe, ae_restrict_mem hrm] with p hp hpr
    have hw0 := hw p hpr
    have hsq : ‖g p + Complex.I * h p‖ ^ 2 ≤ 2 * ‖g p‖ ^ 2 + 2 * ‖h p‖ ^ 2 := by
      have hn := norm_add_le (g p) (Complex.I * h p)
      rw [norm_mul, Complex.norm_I, one_mul] at hn
      nlinarith [norm_nonneg (g p + Complex.I * h p), norm_nonneg (g p), norm_nonneg (h p),
        sq_nonneg (‖g p‖ - ‖h p‖)]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw0 (by positivity)), hp]
    have := mul_le_mul_of_nonneg_left hsq hw0
    simp only [Pi.add_apply]
    linarith
  have combine : ∀ {f g fc fs gc gs : ℝ × ℝ → ℂ},
      (∀ᵐ p ∂(volume.restrict K.rect), f p = fc p + Complex.I * fs p) →
      (∀ᵐ p ∂(volume.restrict K.rect), g p = gc p + Complex.I * gs p) →
      IntegrableOn fc K.rect → IntegrableOn fs K.rect → IntegrableOn gc K.rect → IntegrableOn gs K.rect →
      ∫ p in K.rect, fc p = -∫ p in K.rect, gc p → ∫ p in K.rect, fs p = -∫ p in K.rect, gs p →
      ∫ p in K.rect, f p = -∫ p in K.rect, g p := by
    intro f g fc fs gc gs hf hg hfc hfs hgc hgs hc hs
    rw [integral_congr_ae hf, integral_congr_ae hg, integral_add hfc (hfs.const_mul _),
      integral_add hgc (hgs.const_mul _), integral_const_mul, integral_const_mul, hc, hs]
    ring
  obtain ⟨ν, n, hev, rfl⟩ : ∃ ν n : ℤ, Even (n + ν) ∧ ι = harmonicMode ν n := by
    obtain ⟨i, j⟩ := ι
    refine ⟨2 * j - i, i, ⟨j, by ring⟩, ?_⟩
    simp only [harmonicMode, Prod.mk.injEq, true_and]
    omega
  obtain ⟨hc, hs, hprof⟩ := h1 m v G H hP ν
  have hpos : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
    have h0 : volume {p : ℝ × ℝ | p.1 = 0} = 0 := by
      have e : {p : ℝ × ℝ | p.1 = 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
        ext p
        simp
      rw [e, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have hne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
      rw [ae_iff]
      simpa using h0
    filter_upwards [ae_restrict_mem hrm, ae_restrict_of_ae hne] with p hp hp0
    exact lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm hp0)
  have hpt : ∀ᵐ p ∂(volume.restrict K.rect),
      (∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m (harmonicMode ν n) G a b p)
          = comboGrad C m n (harmonicCos ν G) p + Complex.I * comboGrad C m n (harmonicSin ν G) p ∧
        ∀ c, (∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m (harmonicMode ν n) H a b c p)
          = comboThird C m n (harmonicCos ν H) c p + Complex.I * comboThird C m n (harmonicSin ν H) c p := by
    filter_upwards [hpos, ae_restrict_of_ae (hprof n hev)] with p hp hq
    obtain ⟨-, hg, hh⟩ := hq hp
    refine ⟨?_, fun c => ?_⟩
    · rw [comboGrad, comboGrad, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hg]
      ring
    · rw [comboThird, comboThird, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hh]
      ring
  have qc := h2 K hK m _ _ _ hc n C
  have qs := h2 K hK m _ _ _ hs n C
  have hFm : AEStronglyMeasurable (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m (harmonicMode ν n) G a b p)
      (volume.restrict K.rect) :=
    (qc.1.add (aestronglyMeasurable_const.mul qs.1)).congr (hpt.mono fun p hp => hp.1.symm)
  have hTm : ∀ c, AEStronglyMeasurable
      (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m (harmonicMode ν n) H a b c p)
      (volume.restrict K.rect) := fun c =>
    (((qc.2.2 c).1).add (aestronglyMeasurable_const.mul (qs.2.2 c).1)).congr (hpt.mono fun p hp => (hp.2 c).symm)
  dsimp only
  refine ⟨hFm, ?_, fun c => ⟨hTm c, ?_⟩, ?_, ?_⟩
  · exact wsi hlwc hlw hFm (hpt.mono fun p hp => hp.1) qc.2.1 qs.2.1
  · exact wsi continuous_fst hfst (hTm c) (hpt.mono fun p hp => hp.2 c) (qc.2.2 c).2 (qs.2.2 c).2
  · intro ψ hψ e1 e2
    have rc := hbase _ _ _ hc n ψ hψ
    have rs := hbase _ _ _ hs n ψ hψ
    refine combine ?_ ?_ (rc.1 0) (rs.1 0) (rc.2.2 e1) (rs.2.2 e1) (h3 K hK m _ _ _ hc n C ψ hψ e1 e2)
      (h3 K hK m _ _ _ hs n C ψ hψ e1 e2)
    · filter_upwards [hpt] with p hp
      rw [hp.2 0]
      ring
    · filter_upwards [hpt] with p hp
      rw [hp.1]
      ring
  · intro ψ hψ e1 e2
    have rc := hbase _ _ _ hc n ψ hψ
    have rs := hbase _ _ _ hs n ψ hψ
    refine combine ?_ ?_ (rc.1 2) (rs.1 2) rc.2.1 rs.2.1 (h4 K hK m _ _ _ hc n C ψ hψ e1 e2)
      (h4 K hK m _ _ _ hs n C ψ hψ e1 e2)
    · filter_upwards [hpt] with p hp
      rw [hp.2 2]
      ring
    · filter_upwards [hpt] with p hp
      rw [hp.1]
      ring

theorem labelResolvedEnergy_of (h1 : LabelModeFactsStatement) (h2 : ResolvedComponentStatement) :
    LabelResolvedEnergyStatement := by
  intro K hK m Q q v G H hs ι hn
  have hcb : ∀ (C : Fin 3 → Fin 3 → ℂ) (F F0 F1 F2 : ℝ × ℝ → ℂ),
      (∀ p, ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m ι G a b p = F p) →
      (∀ p, ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 0 p = F0 p) →
      (∀ p, ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 1 p = F1 p) →
      (∀ p, ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 2 p = F2 p) →
      (K.radialEnergy Q q F F0 + K.heightEnergy Q q F F2 + K.angularEnergy Q (fun p => (p.1 : ℂ) * F1 p)
          + (K.tailGradWeight Q F F0 F2 + K.angularWeight ι.1 * K.tailNormSq Q (fun p => (p.1 : ℂ) * F1 p))
        ≤ ∫ p in K.rect, p.1 * (‖F0 p‖ ^ 2 + ‖F1 p‖ ^ 2 + ‖F2 p‖ ^ 2)) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖F0 p‖ ^ 2 + ‖F1 p‖ ^ 2 + ‖F2 p‖ ^ 2)) K.rect := by
    intro C F F0 F1 F2 e e0 e1 e2
    obtain ⟨hFm, hFi, hT, hR, hZ⟩ := h1 K hK m v G H hs ι C
    obtain rfl : (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * gradAt m ι G a b p) = F := funext e
    obtain rfl : (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 0 p) = F0 := funext e0
    obtain rfl : (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 1 p) = F1 := funext e1
    obtain rfl : (fun p => ∑ a : Fin 3, ∑ b : Fin 3, C a b * slopeAt m ι H a b 2 p) = F2 := funext e2
    refine ⟨h2 K hK Q q ι.1 hn _ _ _ _ hFm (hT 0).1 (hT 2).1 (hT 1).1 hFi (hT 0).2 (hT 2).2 (hT 1).2 hR hZ, ?_⟩
    refine (((hT 0).2.add (hT 1).2).add (hT 2).2).congr_fun (fun p _ => ?_)
      (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.add_apply]
    ring
  have hu : ∀ (a b : Fin 3) (f : Fin 3 → Fin 3 → ℂ),
      ∑ a' : Fin 3, ∑ b' : Fin 3, (if a' = a ∧ b' = b then (1 : ℂ) else 0) * f a' b' = f a b := by
    intro a b f
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_three]
  have hcs : ∀ (i : Fin 3) (f : Fin 3 → Fin 3 → ℂ),
      ∑ a : Fin 3, ∑ b : Fin 3, (CellCert.permSign i b a : ℂ) * f a b = curlComp f i := by
    intro i f
    unfold curlComp
    rw [Finset.sum_comm]
  have hcm : ∀ (i : Fin 3) (x : ℂ) (f : Fin 3 → Fin 3 → ℂ),
      curlComp (fun a b => x * f a b) i = x * curlComp f i := by
    intro i x f
    simp only [curlComp, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
    ring
  constructor
  · have hb := fun a b => hcb (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0) (gradAt m ι G a b)
      (fun p => slopeAt m ι H a b 0 p) (fun p => slopeAt m ι H a b 1 p) (fun p => slopeAt m ι H a b 2 p)
      (fun p => hu a b (fun a' b' => gradAt m ι G a' b' p)) (fun p => hu a b (fun a' b' => slopeAt m ι H a' b' 0 p))
      (fun p => hu a b (fun a' b' => slopeAt m ι H a' b' 1 p)) (fun p => hu a b (fun a' b' => slopeAt m ι H a' b' 2 p))
    calc _ = ∑ a : Fin 3, ∑ b : Fin 3,
          (K.radialEnergy Q q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 0 p)
            + K.heightEnergy Q q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 2 p)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * slopeAt m ι H a b 1 p)
            + (K.tailGradWeight Q (gradAt m ι G a b) (fun p => slopeAt m ι H a b 0 p)
                (fun p => slopeAt m ι H a b 2 p)
              + K.angularWeight ι.1 * K.tailNormSq Q (fun p => (p.1 : ℂ) * slopeAt m ι H a b 1 p))) := by
          simp only [labelStrainEnergy, labelStrainTail, ← Finset.sum_add_distrib]
          rfl
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => (hb a b).1))
      _ = ∑ a : Fin 3, ∫ p in K.rect, ∑ b : Fin 3, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          Finset.sum_congr rfl (fun a _ => (integral_finsetSum _ (fun b _ => (hb a b).2)).symm)
      _ = ∫ p in K.rect, ∑ a : Fin 3, ∑ b : Fin 3, p.1 * (‖slopeAt m ι H a b 0 p‖ ^ 2
            + ‖slopeAt m ι H a b 1 p‖ ^ 2 + ‖slopeAt m ι H a b 2 p‖ ^ 2) :=
          (integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (hb a b).2))).symm
      _ = ∫ p in K.rect, p.1 * slopeSq m ι H p := by
          congr 1
          funext p
          simp only [slopeSq, Fin.sum_univ_three]
          ring
  · have hb := fun i => hcb (fun a b => (CellCert.permSign i b a : ℂ))
      (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
      (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i) (fun p => curlComp (fun a b => slopeAt m ι H a b 1 p) i)
      (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
      (fun p => hcs i (fun a b => gradAt m ι G a b p)) (fun p => hcs i (fun a b => slopeAt m ι H a b 0 p))
      (fun p => hcs i (fun a b => slopeAt m ι H a b 1 p)) (fun p => hcs i (fun a b => slopeAt m ι H a b 2 p))
    have hang : ∀ i, (fun p : ℝ × ℝ => curlComp (fun a b => turnedSlopeAt m ι H a b p) i)
        = fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i := fun i => by
      funext p; exact hcm i (p.1 : ℂ) (fun a b => slopeAt m ι H a b 1 p)
    calc _ = ∑ i : Fin 3,
          (K.radialEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
              (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
            + K.heightEnergy Q q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
              (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i)
            + (K.tailGradWeight Q (fun p => curlComp (fun a b => gradAt m ι G a b p) i)
                (fun p => curlComp (fun a b => slopeAt m ι H a b 0 p) i)
                (fun p => curlComp (fun a b => slopeAt m ι H a b 2 p) i)
              + K.angularWeight ι.1 * K.tailNormSq Q
                (fun p => (p.1 : ℂ) * curlComp (fun a b => slopeAt m ι H a b 1 p) i))) := by
          simp only [labelVorticityEnergy, labelVorticityTail, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hang i]
      _ ≤ ∑ i : Fin 3, ∫ p in K.rect, p.1 * (‖curlComp (fun a b => slopeAt m ι H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 2 p) i‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => (hb i).1)
      _ = ∫ p in K.rect, ∑ i : Fin 3, p.1 * (‖curlComp (fun a b => slopeAt m ι H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => slopeAt m ι H a b 2 p) i‖ ^ 2) :=
          (integral_finsetSum _ (fun i _ => (hb i).2)).symm
      _ = ∫ p in K.rect, p.1 * curlSlopeSq m ι H p := by
          congr 1
          funext p
          simp only [curlSlopeSq, Fin.sum_univ_three]
          ring

def LeafNormsStatement : Prop :=
  ∀ (m : ℕ) (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ), 0 < p.1 →
    cnormSq (labelVel m ι v p) = vecSq (velArray m ι v p) ∧
      cnormSq (labelGrad m ι G p) = sumSq (gradArray m ι G p) ∧
      cnormSq (curlOfGrad (labelGrad m ι G p)) = curlSq (gradArray m ι G p) ∧
      cnormSq (labelHess m ι H p) = slopeSq m ι H p ∧
      cnormSq (curlGradOfSecondDeriv (labelHess m ι H p)) = curlSlopeSq m ι H p

namespace LeafValues

variable (T : LeafValues)

end LeafValues

def LeafDensityLowerStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (resolved : Finset (ℤ × ℤ)) (coef : ℤ × ℤ → ℝ × ℝ → ModeCoefficients)
    (ch : ModeCharges) (T : LeafValues), IsLeafValues K resolved coef ch T →
    ∀ ι ∈ resolved, ∀ p ∈ K.rect, ∀ (x2 xc : ℝ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
      T.hessFloor ι * x2 ^ 2 + T.curlHessFloor ι * xc ^ 2 + sesqValue (T.localMatrix ι p) (pairVec s v)
          + T.boxPenalty ι s v
        ≤ (coef ι p).value x2 xc (Real.sqrt (sumSq s)) (Real.sqrt (curlSq s)) (Real.sqrt (vecSq v))

def LeafPointwiseStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (resolved : Finset (ℤ × ℤ)) (coef : ℤ × ℤ → ℝ × ℝ → ModeCoefficients)
    (ch : ModeCharges) (T : LeafValues), IsLeafValues K resolved coef ch T →
    ∀ ι ∈ resolved, ∀ p ∈ K.rect, p.1 ≠ 0 → ∀ (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ),
      0 ≤ CellScalars.rHat K p * (coefPairValue (coef ι p) s v - T.boxPenalty ι s v
          - supremumLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) (ch.length ι p) s v
          - T.boxPairPenalty ι s v)
        + T.absorbValue ι s v

def ModelStretchSplitStatement : Prop :=
  ∀ (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)),
    CoerciveWeak.stretchFormWith W HW v G σ y
      = -(∑ i : Fin 3, ∑ j : Fin 3, curlVec (G σ y) i * (strainOf W σ y (unitVector j) i) * curlVec (G σ y) j)
        + ∑ j : Fin 3, (∑ l : Fin 3, v σ y l * vorticityGradOf HW σ y (unitVector l) j) * curlVec (G σ y) j
        + (1 / 2 : ℝ) * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
            alternatingSymbol i l n * vorticityGradOf HW σ y (unitVector l) j * G σ y (unitVector j) i * v σ y n

def cdot3 (x z : Fin 3 → ℂ) : ℂ := ∑ a : Fin 3, x a * (starRingEnd ℂ) (z a)

def rowPairing (K : CellBox) (f : ℝ × ℝ → Fin 3 → ℂ) (φ : Fin 3 → CellPoly) : ℂ :=
  ∫ p in K.rect, (p.1 : ℂ) * cdot3 (f p) (testValue K φ p)

structure RowProfile where
  vel : ℝ × ℝ → Fin 3 → ℂ
  grad : ℝ × ℝ → Fin 3 → Fin 3 → ℂ
  lap : ℝ × ℝ → Fin 3 → ℂ
  presGrad : ℝ × ℝ → Fin 3 → ℂ
  radialSide : Fin 2 → ℝ → Fin 3 → ℂ
  heightSide : Fin 2 → ℝ → Fin 3 → ℂ
  radialPres : Fin 2 → ℝ → ℂ
  heightPres : Fin 2 → ℝ → ℂ

def sideRadius (K : CellBox) (e : Fin 2) : ℝ := if e = 0 then K.r₁ else K.r₂

def sideHeight (K : CellBox) (e : Fin 2) : ℝ := if e = 0 then K.z₁ else K.z₂

def sideSign (e : Fin 2) : ℂ := if e = 0 then -1 else 1

def rowBoundaryGrad (K : CellBox) (R : RowProfile) (φ : Fin 3 → CellPoly) : ℂ :=
  ∑ e : Fin 2, sideSign e *
    ((∫ z in Set.Icc K.z₁ K.z₂, (sideRadius K e : ℂ) * cdot3 (R.radialSide e z) (testValue K φ (sideRadius K e, z)))
      + ∫ r in Set.Icc K.r₁ K.r₂, (r : ℂ) * cdot3 (R.heightSide e r) (testValue K φ (r, sideHeight K e)))

def rowBoundaryPres (K : CellBox) (R : RowProfile) (φ : Fin 3 → CellPoly) : ℂ :=
  ∑ e : Fin 2, sideSign e *
    ((∫ z in Set.Icc K.z₁ K.z₂, (sideRadius K e : ℂ) * R.radialPres e z
        * (starRingEnd ℂ) ((φ 0).eval K (sideRadius K e, z)))
      + ∫ r in Set.Icc K.r₁ K.r₂, (r : ℂ) * R.heightPres e r * (starRingEnd ℂ) ((φ 2).eval K (r, sideHeight K e)))

def rowVolume (K : CellBox) (k freq : ℝ) (R : RowProfile) (φ : Fin 3 → CellPoly) : ℂ :=
  ∫ p in K.rect, (p.1 : ℂ) *
    ((∑ a : Fin 3, ∑ b : Fin 3, R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
      + cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p))

structure IsRowProfile (K : CellBox) (k : ℝ) (R : RowProfile) : Prop where
  measurable : AEStronglyMeasurable R.vel (volume.restrict K.rect) ∧ AEStronglyMeasurable R.grad (volume.restrict K.rect) ∧
    AEStronglyMeasurable R.lap (volume.restrict K.rect) ∧ AEStronglyMeasurable R.presGrad (volume.restrict K.rect)
  integrable : IntegrableOn (fun p => p.1 * (cnormSq (R.vel p) + ∑ a : Fin 3, cnormSq (R.grad p a)
    + cnormSq (R.lap p) + cnormSq (R.presGrad p))) K.rect
  laplacian_parts : ∀ φ : Fin 3 → CellPoly, IsAxisRegularTest K k φ →
    rowPairing K R.lap φ
      = rowBoundaryGrad K R φ - ∫ p in K.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
          R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b)
  pressure_parts : ∀ φ : Fin 3 → CellPoly, IsTestSolenoidal K k φ → IsAxisRegularTest K k φ →
    rowPairing K R.presGrad φ = rowBoundaryPres K R φ

def CellRowFormulaStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (k freq : ℝ) (R : RowProfile), IsRowProfile K k R →
    ∀ (couple drive f : ℝ × ℝ → Fin 3 → ℂ),
      AEStronglyMeasurable couple (volume.restrict K.rect) → AEStronglyMeasurable drive (volume.restrict K.rect) →
      IntegrableOn (fun p => p.1 * (cnormSq (couple p) + cnormSq (drive p))) K.rect →
      (∀ p ∈ K.rect, f p = fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)
          - R.lap p a + couple p a + drive p a + R.presGrad p a) →
      ∀ φ : Fin 3 → CellPoly, IsTestSolenoidal K k φ → IsAxisRegularTest K k φ →
        rowPairing K f φ = rowVolume K k freq R φ - rowBoundaryGrad K R φ + rowBoundaryPres K R φ
          + rowPairing K couple φ + rowPairing K drive φ

def crossVec (u w : Space) : Space :=
  ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * u j * w l) • unitVector i

def couplingField (W : ℝ → Space → Space) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    ℝ → Space → Space :=
  fun σ y => crossVec (curlVec (G σ y)) (W σ y) + crossVec (vorticityOf W σ y) (v σ y)

def LabelRowProfileStatement : Prop :=
  ∀ (K : CellBox), IsCellBox K → ∀ (m : ℕ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
    IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg → ∀ ι : ℤ × ℤ, (K.IsAxis → ι.1 = 0) →
      ∃ R : RowProfile, IsRowProfile K (labelAzimuth m ι : ℝ) R ∧
        (∀ p ∈ K.rect, 0 < p.1 → R.vel p = velArray m ι v p ∧ R.grad p = gradArray m ι G p ∧
          R.lap p = (fun a => ∑ c : Fin 3, slopeAt m ι H a c c p) ∧ R.presGrad p = velArray m ι Pg p)


def RowLowPartStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B L.modes L →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg →
      ∀ (ι : ℤ × ℤ), L.modes = {ι.1} → (K.IsAxis → ι.1 = 0) → ∀ (P : ℝ) (R : RowProfile),
        IsRowProfile K (labelAzimuth m ι : ℝ) R →
        (∀ᵐ p ∂(volume.restrict K.rect), R.vel p = velArray m ι v p ∧ R.grad p = gradArray m ι G p ∧
          R.lap p = (fun a => ∑ c : Fin 3, slopeAt m ι H a c c p) ∧ R.presGrad p = velArray m ι Pg p) →
        ∀ φ : Fin 3 → CellPoly, IsTestSolenoidal K (labelAzimuth m ι : ℝ) φ →
          IsAxisRegularTest K (labelAzimuth m ι : ℝ) φ →
          IsTestOfShape K L.degSide φ → L.degSide + 2 ≤ L.degCoef → IsPressureSegmentation L →
          rowVolume K (labelAzimuth m ι : ℝ) (labelTimeFreq P ι) R φ - rowBoundaryGrad K R φ
              + rowBoundaryPres K R φ
            = ∑ d, ownRowVector L (labelAzimuth m ι : ℝ) (labelTimeFreq P ι) φ d
                * harmonicData L (labelTime ι) v G H Pg d

def lowCoupling (K : CellBox) (Q : ℕ) (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (u : Fin 3 → ℝ × ℝ → ℂ) (p : ℝ × ℝ) : Fin 3 → ℂ :=
  fun i => ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) *
      (curlComp (fun a b => K.proj Q Q (s a b) p) j * Wα p l + Ωα p j * K.proj (Q - 1) (Q - 1) (u l) p)

def RowCouplingLowStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B L.modes L →
    ∀ (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
      (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space),
      IsPeriodicSecondOrder v G H → IsPeriodicPressure Pg →
      ∀ (ι' : ℤ × ℤ), L.modes = {ι'.1} → (K.IsAxis → ι'.1 = 0) →
      ∀ (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ), (∀ a, ∃ c : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * Wα p a * p.1
          = ∑ i ∈ Finset.range (L.degCoef + 1), ∑ j ∈ Finset.range (L.degCoef + 1),
              c i j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) →
        (∀ a, AEStronglyMeasurable (fun p => Ωα p a) (volume.restrict K.rect)) →
        (∃ C : ℝ, ∀ p ∈ K.rect, ∀ a, ‖Ωα p a‖ ≤ C) →
        ∀ φ : Fin 3 → CellPoly,
          rowPairing K (lowCoupling K L.degCoef Wα Ωα (fun a b p => gradAt m ι' G a b p)
              (fun a p => velAt m ι' v a p)) φ
            = ∑ d, couplingRowVector L Wα Ωα φ d * harmonicData L (labelTime ι') v G H Pg d

def pressureSideValue (K : CellBox) (PL PR : ℝ) (S : FaceSegment) (d : ℕ) : ℂ :=
  if S.radial then
    ((if S.level = K.r₁ then PL else PR : ℝ) : ℂ) * ∫ z in Set.Icc S.lo S.hi, ((S.test d z : ℝ) : ℂ)
  else
    ((PR * (∫ r in Set.Icc S.lo S.hi, r * S.test d r)
      + (if S.lo = K.r₁ then (PR - PL) * ∫ r in Set.Icc 0 K.r₁, r * S.test d r else 0) : ℝ) : ℂ)

def classGaugeVector (L : CellLayout) (PL PR : ℝ) : L.Datum → ℂ :=
  Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0)
  (Sum.elim (fun i => pressureSideValue L.box PL PR (L.presSegment i.2.1) (i.2.2 : ℕ))
  (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) (fun _ => 0)))))))

def CellGaugeRowStatement : Prop :=
  ∀ (m : ℕ) (K : CellBox) (B : CellBases) (L : CellLayout), IsHarmonicLayout m K B {0} L →
    L.modes = {0} → ∀ (PL PR : ℝ), (K.IsAxis → PL = 0) → ∀ (freq : ℝ) (φ : Fin 3 → CellPoly),
      IsTestSolenoidal K 0 φ → IsTestOfShape K L.degSide φ → L.degSide + 2 ≤ L.degCoef →
      L.box = K → IsPressureSegmentation L →
      ∑ d, ownRowVector L 0 freq φ d * classGaugeVector L PL PR d = 0

def CellGaugeCouplingStatement : Prop :=
  ∀ (L : CellLayout) (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ) (φ : Fin 3 → CellPoly) (PL PR : ℝ),
    ∑ d, couplingRowVector L Wα Ωα φ d * classGaugeVector L PL PR d = 0

def StreamGaugeStatement : Prop :=
  ∀ (L : CellLayout) (k freq : ℝ) (φ : Fin 3 → CellPoly) (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ) (c : Fin L.cornerCount),
    ownRowVector L k freq φ (CellDatum.cornerStream c) = 0 ∧ couplingRowVector L Wα Ωα φ (CellDatum.cornerStream c) = 0

theorem streamGauge : StreamGaugeStatement := by
  intro L k freq φ Wα Ωα c
  exact ⟨rfl, rfl⟩

def ForestGaugeCoefficientStatement : Prop :=
  ∀ (L : CellLayout) (S : FaceSegment) (PL PR : ℝ) (d : ℕ), 0 < L.box.r₁ → ¬ S.radial →
    S.lo = L.box.r₁ → S.hi = L.box.r₂ → (∫ r in Set.Icc L.box.r₁ L.box.r₂, r * S.test d r) = 0 →
    (∀ r ∈ Set.Ioo 0 L.box.r₁, S.test d r ≠ 0) →
    pressureSideValue L.box PL PR S d = (((PR - PL) * ∫ r in Set.Icc 0 L.box.r₁, r * S.test d r : ℝ) : ℂ) ∧
      (∫ r in Set.Icc 0 L.box.r₁, r * S.test d r) ≠ 0

def IsStrongRightSide {k : ℕ} (W : ℝ → Space → Space) (b : Fin k → ℝ → Space → Space) (κ : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g F Pg : ℝ → Space → Space) : Prop :=
  ∀ᵐ z : ℝ × Space, F z.1 z.2 = g z.1 z.2 - secondDerivTrace (H z.1 z.2) + couplingField W v G z.1 z.2
    + ∑ i, κ i • b i z.1 z.2 + Pg z.1 z.2

def LowSlotFormValueStatement : Prop :=
  ∀ (L : CellLayout) (A : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ) (u : L.Datum → ℂ),
    (∀ i j, Measurable (fun p => A p i j)) → (∃ C : ℝ, ∀ p ∈ L.box.rect, ∀ i j, ‖A p i j‖ ≤ C) →
    IsCellBox L.box →
    quadFormValue (lowSlotForm L A) u
      = ∑ n : L.modes, (∫ p in L.box.rect, ((L.box.lineWeight p.1 * CellScalars.rHat L.box p : ℝ) : ℂ) *
          matrixSesq (A p) (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p))
            (pairVec (lowStrainOf L u n · · p) (lowVelocityOf L u n · p))).re

def cellState {k n : ℕ} (M : CellMesh) (K : Fin M.count) (A : CellModeLayouts) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : Fin n → ℂ) : CellIndex M K A n k → ℂ :=
  Sum.elim (Sum.elim (fun x => modeData A x.1.1 v G H Pg x.2) η)
    (Sum.elim (fun i => ((κ i : ℝ) : ℂ)) (fun i => ((ζ i : ℝ) : ℂ)))

section CellForm

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def cellPos (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ENNReal :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
    + ∫⁻ p in (D.mesh.box K).rect, D.stretchPosMean v G p * ENNReal.ofReal p.1

def cellNeg (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ENNReal :=
  (∑' ι : ℤ × ℤ, ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)))
    + ∫⁻ p in (D.mesh.box K).rect, D.stretchNegMean v G p * ENNReal.ofReal p.1

open Classical in
def offPos (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (q : Fin k → ℝ) (mc : ModeCharges)
    (ec : ℤ × ℤ → TailBand.EntryCharges) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ENNReal :=
  ∑' ι : ℤ × ℤ, if ι ∈ D.mesh.resolved K then 0 else ∫⁻ p in (D.mesh.box K).rect,
    ENNReal.ofReal (TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn mc (ec ι)
      D.azimuthOrder ι v G H p * p.1)

open Classical in
def offNeg (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (q : Fin k → ℝ) (mc : ModeCharges)
    (ec : ℤ × ℤ → TailBand.EntryCharges) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ENNReal :=
  ∑' ι : ℤ × ℤ, if ι ∈ D.mesh.resolved K then 0 else ∫⁻ p in (D.mesh.box K).rect,
    ENNReal.ofReal (-(TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn mc (ec ι)
      D.azimuthOrder ι v G H p * p.1))

def rowShare (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (F : ℝ → Space → Space) : ℝ :=
  ∑ ι ∈ D.mesh.tested K, D.rows.testWeight K ι *
    Coupling.inverseWeightedSq (D.rows.testBlockMatrix D.mesh.box K ι) (D.rows.cellMoment D.mesh.box D.azimuthOrder K ι F)

def pairWeight (κ ζ : Fin k → ℝ) : Fin k ⊕ Fin k → ℝ
  | .inl i => κ i
  | .inr i => 2 * ζ i

def pairShare (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (labels : Finset (ℤ × ℤ))
    (X : Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (κ ζ : Fin k → ℝ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ g : Fin k ⊕ Fin k, pairWeight κ ζ g * ∑ ι ∈ labels,
    (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      gradAt D.azimuthOrder ι G a b p * (starRingEnd ℂ) (X g ι p a b)).re

def pairStrainSlack (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ)) (w : ℤ × ℤ → ℝ)
    (G : ℝ → Space → (Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ S, w ι * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2

def IsCellFormBound (D : CellLayerData k C nE nM) (K : Fin D.mesh.count) (A : CellModeLayouts) {n : ℕ}
    (Ψ : Matrix (CellIndex D.mesh K A n k) (CellIndex D.mesh K A n k) ℂ)
    (mc : ModeCharges) (ec : ℤ × ℤ → TailBand.EntryCharges) (labels : Finset (ℤ × ℤ))
    (X : Fin k ⊕ Fin k → ℤ × ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ)
    (slackLabels : Finset (ℤ × ℤ)) (slackWeight : ℤ × ℤ → ℝ) (kappaCost : ℝ) (cr : (ℝ → Space → Space) → ℝ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F Pg : ℝ → Space → Space), AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
      IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → IsPeriodicPressure Pg →
      (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) →
      IsStrongRightSide D.given D.cert.actuator κ v G H g F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin n → ℂ,
        ENNReal.ofReal (quadFormValue Ψ (cellState D.mesh K A v G H Pg κ ζ η))
            + ENNReal.ofReal (-(rowShare D K F + pairShare D K labels X κ ζ G))
            + ENNReal.ofReal (pairStrainSlack D K slackLabels slackWeight G) + ENNReal.ofReal (cr v)
            + cellNeg D K q v G H + offPos D K q mc ec v G H
          ≤ cellPos D K q v G H + offNeg D K q mc ec v G H
            + ENNReal.ofReal (rowShare D K F + pairShare D K labels X κ ζ G)
            + ENNReal.ofReal (-quadFormValue Ψ (cellState D.mesh K A v G H Pg κ ζ η))
            + ENNReal.ofReal (kappaCost * ∑ i, κ i ^ 2)

end CellForm


section Entry

variable {k : ℕ} {C : Type} {nE nM : ℕ}

abbrev PortVar (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count) : Type :=
  Fin (R.portCount K)

def creditShare (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) : ℝ :=
  ∑ j, ∫ p in (R.creditPatch j).region ∩ (D.mesh.box K).rect,
    (R.creditPatch j).charge p * (cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p))
      + cnormSq (modeVel (-(flipLabel (R.creditPatch j).label)) v 0 (planePoint p))) * p.1

def CellFormBoundsHold (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) : Prop :=
  ∀ K : Fin D.mesh.count, IsCellFormBound D K (R.layouts K) (R.cellForm K) (D.charges (some K))
    (R.entryCharges K) R.pairLabels (R.pairProfile K) (R.pairSlackLabels K) (R.pairSlackWeight K) (R.kappaCost K)
    (creditShare D R K)

end Entry


section Assembly

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def energyBudget (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K,
    ((R.leaves K).hessFloor ι * ((∫ p in (D.mesh.box K).rect, p.1 * slopeSq D.azimuthOrder ι H p)
        - labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
      + (R.leaves K).curlHessFloor ι * ((∫ p in (D.mesh.box K).rect, p.1 * curlSlopeSq D.azimuthOrder ι H p)
        - labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)
      + ∑ n : ((R.layouts K).layout ι).modes,
          (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
            matrixSesq ((R.leaves K).localMatrix ι p)
              (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
                (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))
              (pairVec (lowStrainOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · · p)
                (lowVelocityOf ((R.layouts K).layout ι) (modeData (R.layouts K) ι v G H Pg) n · p))).re)

def tailCredit (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) : ℝ :=
  ∑ ι ∈ D.mesh.resolved K,
    ((R.leaves K).hessFloor ι * labelStrainTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H
      + (R.leaves K).curlHessFloor ι
        * labelVorticityTail (D.mesh.box K) D.azimuthOrder ι ((R.layouts K).layout ι).degCoef G H)

def EnergyLeafBoundStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    CellCalculusConditions D R → ∀ K : Fin D.mesh.count, ∀ q ∈ D.cert.params,
    ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (Pg : ℝ → Space → Space), IsPeriodicPressure Pg → ∀ κ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
      quadFormValue (energyLeafForm D R K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
        ≤ energyBudget D R K v G H Pg

def IsResidualFormBound (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (Ψ : Matrix (CellIndex D.mesh K (R.layouts K) (R.portCount K) k)
      (CellIndex D.mesh K (R.layouts K) (R.portCount K) k) ℂ) : Prop :=
  ∀ q ∈ D.cert.params, ∀ v G H g, IsPerturbation D.cert.symmetries (D.cert.period q) v G H g →
    ∀ (κ : Fin k → ℝ) (F Pg : ℝ → Space → Space), AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
      IsTimePeriodic F → periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → IsPeriodicPressure Pg →
      (∀ᵐ z : ℝ × Space, Pg z.1 (flipPoint z.2) = flipPoint (Pg z.1 z.2)) →
      IsStrongRightSide D.given D.cert.actuator κ v G H g F Pg → ∀ ζ : Fin k → ℝ, ∀ η : Fin (R.portCount K) → ℂ,
        ENNReal.ofReal (quadFormValue Ψ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
              + energyBudget D R K v G H Pg)
            + ENNReal.ofReal (-(rowShare D K F + pairShare D K R.pairLabels (R.pairProfile K) κ ζ G))
            + ENNReal.ofReal (pairStrainSlack D K (R.pairSlackLabels K) (R.pairSlackWeight K) G)
            + ENNReal.ofReal (creditShare D R K v)
            + cellNeg D K q v G H + offPos D K q (D.charges (some K)) (R.entryCharges K) v G H
          ≤ cellPos D K q v G H + offNeg D K q (D.charges (some K)) (R.entryCharges K) v G H
            + ENNReal.ofReal (rowShare D K F + pairShare D K R.pairLabels (R.pairProfile K) κ ζ G)
            + ENNReal.ofReal (-(quadFormValue Ψ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
              + energyBudget D R K v G H Pg))
            + ENNReal.ofReal (R.kappaCost K * ∑ i, κ i ^ 2)

def CellFormAssemblyStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D),
    CellCalculusConditions D R → (∀ K, IsResidualFormBound D R K (R.cellForm K - energyLeafForm D R K)) →
      CellFormBoundsHold D R

theorem cellFormAssembly_of (h : EnergyLeafBoundStatement) : CellFormAssemblyStatement := by
  intro k C nE nM D R hR hres K q hq v G H g hpert κ F Pg hFm hFper hFL2 hPg hflip hF ζ η
  have hE := h D R hR K q hq v G H g hpert Pg hPg κ ζ η
  have hB := hres K q hq v G H g hpert κ F Pg hFm hFper hFL2 hPg hflip hF ζ η
  have hsub : ∀ {X : Type} [Fintype X] (A B : Matrix X X ℂ) (u : X → ℂ),
      quadFormValue (A - B) u = quadFormValue A u - quadFormValue B u := by
    intro X _ A B u
    unfold quadFormValue
    rw [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
  rw [hsub] at hB
  have hle : quadFormValue (R.cellForm K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
      ≤ quadFormValue (R.cellForm K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
          - quadFormValue (energyLeafForm D R K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)
          + energyBudget D R K v G H Pg := by linarith
  have h1 := ENNReal.ofReal_le_ofReal hle
  have h2 := ENNReal.ofReal_le_ofReal (neg_le_neg hle)
  exact (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add h1 le_rfl) le_rfl) le_rfl) le_rfl) le_rfl).trans
    (hB.trans (add_le_add (add_le_add le_rfl h2) le_rfl))

end Assembly

end CellCalculus

end CertCell

end Breakdown

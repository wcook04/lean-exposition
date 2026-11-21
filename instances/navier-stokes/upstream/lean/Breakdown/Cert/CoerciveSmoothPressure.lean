import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoerciveSmoothPieceMuDivergence

open scoped ContDiff ENNReal ComplexConjugate
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPressure

theorem cdot_sub_left (a b c : Fin 3 → ℂ) : cdot (a - b) c = cdot a c - cdot b c := by
  unfold cdot
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.sub_apply, sub_mul]

theorem cdot_add_right (a b c : Fin 3 → ℂ) : cdot a (b + c) = cdot a b + cdot a c := by
  unfold cdot
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.add_apply, map_add, mul_add]

theorem cnormSq_sub_sub (a b c : Fin 3 → ℂ) :
    cnormSq (a - b - c) = cnormSq (a - b) + cnormSq c - 2 * (cdot a c).re + 2 * (cdot b c).re := by
  rw [ModeL2Internal.cnormSq_sub (a - b) c, cdot_sub_left, Complex.sub_re]
  ring

theorem eq_zero_of_cnormSq_eq_zero {x : Fin 3 → ℂ} (h : cnormSq x = 0) : x = 0 := by
  funext i
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun j (_ : j ∈ Finset.univ) => sq_nonneg ‖x j‖)).1 h i
    (Finset.mem_univ i)
  simpa using h1

theorem integrable_inner {X Y : ℝ → Space → Space} (hX : ModeL2Internal.IsSquareField X)
    (hY : ModeL2Internal.IsSquareField Y) :
    Integrable (fun z : ℝ × Space => inner ℝ (X z.1 z.2) (Y z.1 z.2)) ModeL2Internal.slab := by
  have hmX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) ModeL2Internal.slab :=
    hX.1.mono_ac ModeL2Internal.slab_ac
  have hmY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) ModeL2Internal.slab :=
    hY.1.mono_ac ModeL2Internal.slab_ac
  have hnX := ModeL2Internal.integrable_of_periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) (hmX.norm.pow 2)
    (fun _ _ => sq_nonneg _) hX.2.2
  have hnY := ModeL2Internal.integrable_of_periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) (hmY.norm.pow 2)
    (fun _ _ => sq_nonneg _) hY.2.2
  refine (hnX.add hnY).mono' (hmX.inner hmY) (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  have h1 := abs_real_inner_le_norm (X z.1 z.2) (Y z.1 z.2)
  have h2 := norm_nonneg (X z.1 z.2)
  have h3 := norm_nonneg (Y z.1 z.2)
  show _ ≤ ‖X z.1 z.2‖ ^ 2 + ‖Y z.1 z.2‖ ^ 2
  nlinarith [sq_nonneg (‖X z.1 z.2‖ - ‖Y z.1 z.2‖)]

theorem hasSum_re_cdot (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : ModeL2Internal.IsSquareField X) (hY : ModeL2Internal.IsSquareField Y) :
    HasSum (fun ι : ℤ × ℤ => ∫ z, (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂ModeL2Internal.slab)
      (∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab) := by
  have hpol := hPars.2.2.2 X Y hX.1 hY.1 hX.2.1 hY.2.1 hX.2.2 hY.2.2
  have e : (fun ι : ℤ × ℤ => ∫ z, (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂ModeL2Internal.slab)
      = fun ι => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (cdot (modeVel ι X σ y) (modeVel ι Y σ y)).re :=
    funext fun ι => integral_prod _ (ModeL2Internal.integrable_re_cdot_modeVel hPars hX hY ι)
  have e2 : ∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab
      = ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (X σ y) (Y σ y) := integral_prod _ (integrable_inner hX hY)
  rw [e, e2]
  exact hpol

end Internal.SmoothPressure

open Internal.SmoothPressure in
theorem modeVel_add_ae (hPars : ModeSquareSumHolds) {X Y Z : ℝ → Space → Space}
    (hXm : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume) (hXp : IsTimePeriodic X)
    (hX2 : periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤)
    (hYm : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume) (hYp : IsTimePeriodic Y)
    (hY2 : periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) < ⊤)
    (hZm : AEStronglyMeasurable (fun z : ℝ × Space => Z z.1 z.2) volume) (hZp : IsTimePeriodic Z)
    (hZ2 : periodLIntegral (fun σ y => ‖Z σ y‖ ^ 2) < ⊤)
    (h : ∀ᵐ z : ℝ × Space, Z z.1 z.2 = X z.1 z.2 + Y z.1 z.2) (ι : ℤ × ℤ) :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      modeVel ι Z z.1 z.2 = modeVel ι X z.1 z.2 + modeVel ι Y z.1 z.2 := by
  have hX : ModeL2Internal.IsSquareField X := ⟨hXm, hXp, hX2⟩
  have hY : ModeL2Internal.IsSquareField Y := ⟨hYm, hYp, hY2⟩
  have hZ : ModeL2Internal.IsSquareField Z := ⟨hZm, hZp, hZ2⟩
  have hae : ∀ᵐ z ∂ModeL2Internal.slab, Z z.1 z.2 = X z.1 z.2 + Y z.1 z.2 :=
    ModeL2Internal.slab_ac.ae_le h
  have hmZX : AEStronglyMeasurable (fun z : ℝ × Space => ‖Z z.1 z.2 - X z.1 z.2‖ ^ 2) ModeL2Internal.slab :=
    ((hZm.mono_ac ModeL2Internal.slab_ac).sub (hXm.mono_ac ModeL2Internal.slab_ac)).norm.pow 2
  have hmY : AEStronglyMeasurable (fun z : ℝ × Space => ‖Y z.1 z.2‖ ^ 2) ModeL2Internal.slab :=
    (hYm.mono_ac ModeL2Internal.slab_ac).norm.pow 2
  have eZX : (periodLIntegral (fun σ y => ‖Z σ y - X σ y‖ ^ 2)).toReal
      = ∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab := by
    rw [ModeL2Internal.toReal_periodLIntegral (fun σ y => ‖Z σ y - X σ y‖ ^ 2) hmZX (fun _ _ => sq_nonneg _)]
    exact integral_congr_ae (hae.mono fun z hz => by simp only [hz, add_sub_cancel_left])
  have eY : (periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2)).toReal = ∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab :=
    ModeL2Internal.toReal_periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) hmY (fun _ _ => sq_nonneg _)
  have hiXY := integrable_inner hX hY
  have hnY : Integrable (fun z : ℝ × Space => ‖Y z.1 z.2‖ ^ 2) ModeL2Internal.slab :=
    ModeL2Internal.integrable_of_periodLIntegral (fun σ y => ‖Y σ y‖ ^ 2) hmY (fun _ _ => sq_nonneg _) hY2
  have eZY : ∫ z, inner ℝ (Z z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab
      = (∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab) + ∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab := by
    rw [← integral_add hiXY hnY]
    refine integral_congr_ae (hae.mono fun z hz => ?_)
    simp only [hz, inner_add_left, real_inner_self_eq_norm_sq]
  have hs := (((ModeL2Internal.hasSum_cnormSq_modeVel_sub hPars hZ hX).add
    (ModeL2Internal.hasSum_cnormSq_modeVel hPars hY)).sub ((hasSum_re_cdot hPars hZ hY).mul_left 2)).add
    ((hasSum_re_cdot hPars hX hY).mul_left 2)
  rw [eZX, eY, eZY] at hs
  have hval : (∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab) + (∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab)
      - 2 * ((∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab) + ∫ z, ‖Y z.1 z.2‖ ^ 2 ∂ModeL2Internal.slab)
      + 2 * (∫ z, inner ℝ (X z.1 z.2) (Y z.1 z.2) ∂ModeL2Internal.slab) = 0 := by ring
  rw [hval] at hs
  have hcomb : ∀ ι : ℤ × ℤ, Integrable (fun z : ℝ × Space =>
      cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2)
        - 2 * (cdot (modeVel ι Z z.1 z.2) (modeVel ι Y z.1 z.2)).re
        + 2 * (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re) ModeL2Internal.slab := fun ι =>
    (((ModeL2Internal.integrable_cnormSq_modeVel_sub hPars hZ hX ι).add
      (ModeL2Internal.integrable_cnormSq_modeVel hPars hY ι)).sub
      ((ModeL2Internal.integrable_re_cdot_modeVel hPars hZ hY ι).const_mul 2)).add
      ((ModeL2Internal.integrable_re_cdot_modeVel hPars hX hY ι).const_mul 2)
  have hint : ∀ ι : ℤ × ℤ, Integrable (fun z : ℝ × Space =>
      cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2)) ModeL2Internal.slab :=
    fun ι => (hcomb ι).congr (ae_of_all _ fun z => (cnormSq_sub_sub _ _ _).symm)
  have hterm : ∀ ι : ℤ × ℤ, ∫ z, cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2 - modeVel ι Y z.1 z.2)
      ∂ModeL2Internal.slab = (∫ z, cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2) ∂ModeL2Internal.slab)
        + (∫ z, cnormSq (modeVel ι Y z.1 z.2) ∂ModeL2Internal.slab)
        - 2 * (∫ z, (cdot (modeVel ι Z z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂ModeL2Internal.slab)
        + 2 * (∫ z, (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂ModeL2Internal.slab) := by
    intro ι
    have i1 : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2)) ModeL2Internal.slab :=
      ModeL2Internal.integrable_cnormSq_modeVel_sub hPars hZ hX ι
    have i2 : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι Y z.1 z.2)) ModeL2Internal.slab := ModeL2Internal.integrable_cnormSq_modeVel hPars hY ι
    have i3 : Integrable (fun z : ℝ × Space => 2 * (cdot (modeVel ι Z z.1 z.2) (modeVel ι Y z.1 z.2)).re) ModeL2Internal.slab :=
      (ModeL2Internal.integrable_re_cdot_modeVel hPars hZ hY ι).const_mul 2
    have i4 : Integrable (fun z : ℝ × Space => 2 * (cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)).re) ModeL2Internal.slab :=
      (ModeL2Internal.integrable_re_cdot_modeVel hPars hX hY ι).const_mul 2
    have i12 : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2)) ModeL2Internal.slab := i1.add i2
    have i123 : Integrable (fun z : ℝ × Space => cnormSq (modeVel ι Z z.1 z.2 - modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2) - 2 * (cdot (modeVel ι Z z.1 z.2) (modeVel ι Y z.1 z.2)).re) ModeL2Internal.slab := i12.sub i3
    rw [integral_congr_ae (ae_of_all _ fun z => cnormSq_sub_sub _ _ _), integral_add i123 i4, integral_sub i12 i3,
      integral_add i1 i2, integral_const_mul, integral_const_mul]
  rw [← funext hterm] at hs
  have hzero := (hasSum_zero_iff_of_nonneg (fun ι => integral_nonneg fun z =>
    ModeL2Internal.cnormSq_nonneg _)).1 hs
  have h0 := (integral_eq_zero_iff_of_nonneg (fun z => ModeL2Internal.cnormSq_nonneg _) (hint ι)).1
    (congrFun hzero ι)
  refine h0.mono fun z hz => ?_
  have hz' := eq_zero_of_cnormSq_eq_zero hz
  rw [sub_sub, sub_eq_zero] at hz'
  exact hz'

open Internal.SmoothPressure in
theorem modeTerm_add_of_ae (wt : Space → ℝ) (v Q S Y : ℝ → Space → Space) (ι : ℤ × ℤ)
    (hae : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      modeVel ι Q z.1 z.2 = modeVel ι S z.1 z.2 + modeVel ι Y z.1 z.2)
    (hS : Integrable (fun z : ℝ × Space => (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι S z.1 z.2)).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
    (hY : Integrable (fun z : ℝ × Space => (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Y z.1 z.2)).re)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space))) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Q σ y)).re
      = (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι S σ y)).re)
        + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Y σ y)).re := by
  have hpt : ∀ z : ℝ × Space, modeVel ι Q z.1 z.2 = modeVel ι S z.1 z.2 + modeVel ι Y z.1 z.2 →
      (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Q z.1 z.2)).re = (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι S z.1 z.2)).re + (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Y z.1 z.2)).re := by
    intro z hz
    rw [hz, cdot_add_right, mul_add, Complex.add_re]
  have hQ : Integrable (fun z : ℝ × Space => (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Q z.1 z.2)).re) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (hS.add hY).congr (hae.mono fun z hz => (hpt z hz).symm)
  have eQ : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Q σ y)).re = ∫ z, (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Q z.1 z.2)).re ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (integral_prod _ hQ).symm
  have eS : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι S σ y)).re = ∫ z, (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι S z.1 z.2)).re ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (integral_prod _ hS).symm
  have eY : ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (Complex.I * (wt y : ℂ) * cdot (modeVel ι v σ y) (modeVel ι Y σ y)).re = ∫ z, (Complex.I * (wt z.2 : ℂ) * cdot (modeVel ι v z.1 z.2) (modeVel ι Y z.1 z.2)).re ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    (integral_prod _ hY).symm
  rw [eQ, eS, eY, ← integral_add hS hY]
  exact integral_congr_ae (hae.mono fun z hz => hpt z hz)

namespace Internal.SmoothPressure

theorem cnormSq_add_eq (a d : Fin 3 → ℂ) : cnormSq (a + d) = cnormSq (a - d) + 4 * (cdot a d).re := by
  have h1 := ModeL2Internal.cnormSq_sub a (-d)
  rw [sub_neg_eq_add] at h1
  have h2 : cdot a (-d) = -cdot a d := by
    unfold cdot
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.neg_apply, map_neg, mul_neg]
  have h3 : cnormSq (-d) = cnormSq d := by
    unfold cnormSq
    simp
  rw [h1, ModeL2Internal.cnormSq_sub a d, h2, h3, Complex.neg_re]
  ring

theorem pairing_modes_zero (hPars : ModeSquareSumHolds) (hSolenoidal : SolenoidalModeHolds) (F Q' M : ℝ → Space → Space)
    (hF : ModeL2Internal.IsSquareField F) (hQ' : IsSolenoidalPartOf F Q') (hM : ModeL2Internal.IsSquareField M)
    (hMo : ∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) :
    HasSum (fun κ : ℤ × ℤ => ∫ z, (cdot (modeVel κ M z.1 z.2) (modeVel κ (fun σ y => Q' σ y - F σ y) z.1 z.2)).re ∂ModeL2Internal.slab) 0 := by
  have hQs : ModeL2Internal.IsSquareField Q' := ⟨hQ'.1, hQ'.2.1, hQ'.2.2.1⟩
  have hG0 := PairingSplitInternal.square_lin hQs hF 1 (-1)
  have eG : (fun σ y => (1 : ℝ) • Q' σ y + (-1 : ℝ) • F σ y) = (fun σ y => Q' σ y - F σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eG] at hG0
  have hMM : IsSolenoidalPartOf M M := ⟨hM.1, hM.2.1, hM.2.2, hMo, fun _ _ => rfl⟩
  have hpe := PairingSplitInternal.pairing_eq_solenoidal hSolenoidal hF hQ' hMM
  have iF := integrable_inner hF hM
  have iQ := integrable_inner hQs hM
  have hs := hasSum_re_cdot hPars hM hG0
  have e1 : ∫ z, inner ℝ (M z.1 z.2) (Q' z.1 z.2 - F z.1 z.2) ∂ModeL2Internal.slab
      = (∫ z, inner ℝ (Q' z.1 z.2) (M z.1 z.2) ∂ModeL2Internal.slab) - ∫ z, inner ℝ (F z.1 z.2) (M z.1 z.2) ∂ModeL2Internal.slab := by
    rw [← integral_sub iQ iF]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    show inner ℝ (M z.1 z.2) (Q' z.1 z.2 - F z.1 z.2) = inner ℝ (Q' z.1 z.2) (M z.1 z.2) - inner ℝ (F z.1 z.2) (M z.1 z.2)
    rw [inner_sub_right, real_inner_comm (M z.1 z.2), real_inner_comm (M z.1 z.2)]
  have e2 : periodPairing F M = ∫ z, inner ℝ (F z.1 z.2) (M z.1 z.2) ∂ModeL2Internal.slab := (integral_prod _ iF).symm
  have e3 : periodPairing Q' M = ∫ z, inner ℝ (Q' z.1 z.2) (M z.1 z.2) ∂ModeL2Internal.slab := (integral_prod _ iQ).symm
  have hz : ∫ z, inner ℝ (M z.1 z.2) (Q' z.1 z.2 - F z.1 z.2) ∂ModeL2Internal.slab = 0 := by
    rw [e1, ← e2, ← e3, hpe, sub_self]
  rw [hz] at hs
  exact hs

def torusWave (m : ℤ × ℤ) (τ φ : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * m.1 * τ + m.2 * φ : ℝ) : ℂ) * Complex.I)

theorem continuous_torusWave (m : ℤ × ℤ) : Continuous (fun p : ℝ × ℝ => torusWave m p.1 p.2) := by
  unfold torusWave
  fun_prop

theorem norm_torusWave (m : ℤ × ℤ) (τ φ : ℝ) : ‖torusWave m τ φ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem integral_exp_circle (n : ℤ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), Complex.exp (((n * φ : ℝ) : ℂ) * Complex.I)
      = if n = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp
  · have hc : (n : ℂ) * Complex.I ≠ 0 := mul_ne_zero (Int.cast_ne_zero.2 hn) Complex.I_ne_zero
    have e : (fun φ : ℝ => Complex.exp (((n * φ : ℝ) : ℂ) * Complex.I))
        = fun φ : ℝ => Complex.exp ((n : ℂ) * Complex.I * (φ : ℂ)) := by
      funext φ
      congr 1
      push_cast
      ring
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp ((n : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem integral_exp_period (n : ℤ) :
    ∫ τ in (0 : ℝ)..1, Complex.exp (((2 * Real.pi * n * τ : ℝ) : ℂ) * Complex.I)
      = if n = 0 then (1 : ℂ) else 0 := by
  split_ifs with hn
  · subst hn
    simp
  · have hc : 2 * (Real.pi : ℂ) * n * Complex.I ≠ 0 :=
      mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
        (Int.cast_ne_zero.2 hn)) Complex.I_ne_zero
    have e : (fun τ : ℝ => Complex.exp (((2 * Real.pi * n * τ : ℝ) : ℂ) * Complex.I))
        = fun τ : ℝ => Complex.exp (2 * (Real.pi : ℂ) * n * Complex.I * (τ : ℂ)) := by
      funext τ
      congr 1
      push_cast
      ring
    rw [e, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * (Real.pi : ℂ) * n * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I n]
      congr 1
      push_cast
      ring
    rw [h1]
    simp

theorem torusWave_split (m : ℤ × ℤ) (τ φ : ℝ) :
    torusWave m τ φ = torusWave m τ 0 * Complex.exp (((m.2 * φ : ℝ) : ℂ) * Complex.I) := by
  unfold torusWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem torusWave_time (m : ℤ × ℤ) (τ : ℝ) :
    torusWave m τ 0 = Complex.exp (((2 * Real.pi * m.1 * τ : ℝ) : ℂ) * Complex.I) := by
  unfold torusWave
  rw [mul_zero, add_zero]

theorem integral_torusWave_inner (m : ℤ × ℤ) (τ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), torusWave m τ φ
      = torusWave m τ 0 * (if m.2 = 0 then (2 * Real.pi : ℂ) else 0) := by
  rw [intervalIntegral.integral_congr (g := fun φ => torusWave m τ 0 * Complex.exp (((m.2 * φ : ℝ) : ℂ) * Complex.I))
    (fun φ _ => torusWave_split m τ φ), intervalIntegral.integral_const_mul, integral_exp_circle]

theorem integral_torusWave_time (m : ℤ × ℤ) :
    ∫ τ in (0 : ℝ)..1, torusWave m τ 0 = if m.1 = 0 then (1 : ℂ) else 0 := by
  rw [intervalIntegral.integral_congr (g := fun τ => Complex.exp (((2 * Real.pi * m.1 * τ : ℝ) : ℂ) * Complex.I))
    (fun τ _ => torusWave_time m τ)]
  exact integral_exp_period m.1

theorem torusWave_mul_re (ι κ : ℤ × ℤ) (c : ℂ) (τ φ : ℝ) :
    torusWave (-ι) τ φ * (((torusWave κ τ φ * c).re : ℝ) : ℂ)
      = (c * torusWave (κ - ι) τ φ + conj c * torusWave (-κ - ι) τ φ) / 2 := by
  rw [Complex.re_eq_add_conj, map_mul]
  have c1 : conj (torusWave κ τ φ) = torusWave (-κ) τ φ := by
    unfold torusWave
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    congr 1
    simp only [Prod.fst_neg, Prod.snd_neg, Int.cast_neg]
    push_cast
    ring
  have m1 : torusWave (-ι) τ φ * torusWave κ τ φ = torusWave (κ - ι) τ φ := by
    unfold torusWave
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Int.cast_neg, Int.cast_sub]
    push_cast
    ring
  have m2 : torusWave (-ι) τ φ * torusWave (-κ) τ φ = torusWave (-κ - ι) τ φ := by
    unfold torusWave
    rw [← Complex.exp_add]
    congr 1
    simp only [Prod.fst_neg, Prod.snd_neg, Prod.fst_sub, Prod.snd_sub, Int.cast_neg, Int.cast_sub]
    push_cast
    ring
  rw [c1]
  linear_combination (c / 2) * m1 + (conj c / 2) * m2


theorem hasSum_torus_inner (d : ℤ × ℤ → ℂ) (hd : Summable fun κ => ‖d κ‖)
    (h : ∀ τ φ : ℝ, HasSum (fun κ : ℤ × ℤ => (torusWave κ τ φ * d κ).re) 0) (ι : ℤ × ℤ) (τ : ℝ) :
    HasSum (fun κ : ℤ × ℤ => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      torusWave (-ι) τ φ * (((torusWave κ τ φ * d κ).re : ℝ) : ℂ)) 0 := by
  have hh := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := 2 * Real.pi)
    (F := fun κ φ => torusWave (-ι) τ φ * (((torusWave κ τ φ * d κ).re : ℝ) : ℂ)) (f := fun _ => (0 : ℂ))
    (fun κ _ => ‖d κ‖) ?_ ?_ ?_ ?_ ?_
  · rw [intervalIntegral.integral_zero] at hh
    exact hh
  · intro κ
    refine Continuous.aestronglyMeasurable ?_
    have c1 : Continuous (fun φ : ℝ => torusWave (-ι) τ φ) :=
      (continuous_torusWave (-ι)).comp (Continuous.prodMk continuous_const continuous_id)
    have c2 : Continuous (fun φ : ℝ => torusWave κ τ φ) :=
      (continuous_torusWave κ).comp (Continuous.prodMk continuous_const continuous_id)
    exact c1.mul (Complex.continuous_ofReal.comp (Complex.continuous_re.comp (c2.mul continuous_const)))
  · intro κ
    refine ae_of_all _ fun φ _ => ?_
    rw [norm_mul, norm_torusWave, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_torusWave, one_mul]
  · exact ae_of_all _ fun _ _ => hd
  · exact intervalIntegrable_const
  · refine ae_of_all _ fun φ _ => ?_
    have h1 := (Complex.hasSum_ofReal.2 (h τ φ)).mul_left (torusWave (-ι) τ φ)
    rw [Complex.ofReal_zero, mul_zero] at h1
    exact h1

theorem integral_torus_inner_eq (ι κ : ℤ × ℤ) (c : ℂ) (τ : ℝ) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi), torusWave (-ι) τ φ * (((torusWave κ τ φ * c).re : ℝ) : ℂ)
      = (c * (torusWave (κ - ι) τ 0 * (if (κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))
        + conj c * (torusWave (-κ - ι) τ 0 * (if (-κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))) / 2 := by
  have i1 : IntervalIntegrable (fun φ => c * torusWave (κ - ι) τ φ) volume 0 (2 * Real.pi) :=
    (continuous_const.mul ((continuous_torusWave (κ - ι)).comp
      (Continuous.prodMk continuous_const continuous_id))).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun φ => conj c * torusWave (-κ - ι) τ φ) volume 0 (2 * Real.pi) :=
    (continuous_const.mul ((continuous_torusWave (-κ - ι)).comp
      (Continuous.prodMk continuous_const continuous_id))).intervalIntegrable _ _
  rw [intervalIntegral.integral_congr (fun φ _ => torusWave_mul_re ι κ c τ φ), intervalIntegral.integral_div,
    intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_torusWave_inner, integral_torusWave_inner]

theorem torus_coeff_re (d : ℤ × ℤ → ℂ) (hd : Summable fun κ => ‖d κ‖)
    (h : ∀ τ φ : ℝ, HasSum (fun κ : ℤ × ℤ => (torusWave κ τ φ * d κ).re) 0) (ι : ℤ × ℤ) :
    (d ι).re + (d (-ι)).re = 0 := by
  have hin : ∀ τ, HasSum (fun κ : ℤ × ℤ => (d κ * (torusWave (κ - ι) τ 0 * (if (κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))
        + conj (d κ) * (torusWave (-κ - ι) τ 0 * (if (-κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))) / 2) 0 := by
    intro τ
    have h1 := hasSum_torus_inner d hd h ι τ
    simp only [integral_torus_inner_eq] at h1
    exact h1
  have hout := intervalIntegral.hasSum_integral_of_dominated_convergence (μ := volume) (a := 0) (b := 1)
    (F := fun κ τ => (d κ * (torusWave (κ - ι) τ 0 * (if (κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))
        + conj (d κ) * (torusWave (-κ - ι) τ 0 * (if (-κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))) / 2)
    (f := fun _ => (0 : ℂ)) (fun κ _ => ‖d κ‖ * |2 * Real.pi - 0|) ?_ ?_ ?_ ?_ (ae_of_all _ fun τ _ => hin τ)
  rotate_left
  · intro κ
    refine Continuous.aestronglyMeasurable ?_
    have c1 : Continuous (fun τ : ℝ => torusWave (κ - ι) τ 0) :=
      (continuous_torusWave (κ - ι)).comp (Continuous.prodMk continuous_id continuous_const)
    have c2 : Continuous (fun τ : ℝ => torusWave (-κ - ι) τ 0) :=
      (continuous_torusWave (-κ - ι)).comp (Continuous.prodMk continuous_id continuous_const)
    exact ((continuous_const.mul (c1.mul continuous_const)).add (continuous_const.mul (c2.mul continuous_const))).div_const _
  · intro κ
    refine ae_of_all _ fun τ _ => ?_
    rw [← integral_torus_inner_eq]
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun φ _ => ?_
    rw [norm_mul, norm_torusWave, one_mul, Complex.norm_real, Real.norm_eq_abs]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, norm_torusWave, one_mul]
  · exact ae_of_all _ fun _ _ => hd.mul_right _
  · exact intervalIntegrable_const
  rw [intervalIntegral.integral_zero] at hout
  have i1 : ∀ m : ℤ × ℤ, IntervalIntegrable (fun τ => torusWave m τ 0) volume 0 1 := fun m =>
    ((continuous_torusWave m).comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
  have hE : ∀ m : ℤ × ℤ, (if m.1 = 0 then (1 : ℂ) else 0) * (if m.2 = 0 then (2 * Real.pi : ℂ) else 0)
      = if m = 0 then (2 * Real.pi : ℂ) else 0 := by
    intro m
    by_cases h1 : m.1 = 0 <;> by_cases h2 : m.2 = 0 <;> simp [h1, h2, Prod.ext_iff]
  have hval : ∀ κ : ℤ × ℤ, ∫ τ in (0 : ℝ)..1, (d κ * (torusWave (κ - ι) τ 0 * (if (κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))
        + conj (d κ) * (torusWave (-κ - ι) τ 0 * (if (-κ - ι).2 = 0 then (2 * Real.pi : ℂ) else 0))) / 2
      = (if κ = ι then (Real.pi : ℂ) * d ι else 0) + (if κ = -ι then (Real.pi : ℂ) * conj (d (-ι)) else 0) := by
    intro κ
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add (((i1 _).mul_const _).const_mul _)
      (((i1 _).mul_const _).const_mul _), intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const, integral_torusWave_time,
      integral_torusWave_time, hE, hE]
    have s1 : κ - ι = 0 ↔ κ = ι := sub_eq_zero
    have s2 : -κ - ι = 0 ↔ κ = -ι := by
      rw [sub_eq_zero, neg_eq_iff_eq_neg]
    simp only [s1, s2]
    by_cases k1 : κ = ι <;> by_cases k2 : κ = -ι
    · rw [if_pos k1, if_pos k2, if_pos k1, if_pos k2]
      subst k1
      rw [← k2]
      ring
    · rw [if_pos k1, if_neg k2, if_pos k1, if_neg k2]
      subst k1
      ring
    · rw [if_neg k1, if_pos k2, if_neg k1, if_pos k2]
      subst k2
      ring
    · rw [if_neg k1, if_neg k2, if_neg k1, if_neg k2]
      ring
  simp only [hval] at hout
  have hs := (hasSum_ite_eq ι ((Real.pi : ℂ) * d ι)).add (hasSum_ite_eq (-ι) ((Real.pi : ℂ) * conj (d (-ι))))
  have hu := congrArg Complex.re (hout.unique hs)
  simp only [Complex.zero_re, Complex.add_re, Complex.re_ofReal_mul, Complex.conj_re] at hu
  have key : Real.pi * ((d ι).re + (d (-ι)).re) = 0 := by linarith
  exact (mul_eq_zero.1 key).resolve_left Real.pi_ne_zero

theorem axialRot_zero_vec (φ : ℝ) : axialRot φ 0 = 0 := by
  obtain ⟨R, hR⟩ := axialRotationHolds_proof.1 φ
  rw [← hR, map_zero]

theorem modeVel_zero (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : modeVel ι (fun _ _ => (0 : Space)) σ y = 0 := by
  funext i
  unfold modeVel modeAverage
  simp [axialRot_zero_vec]

theorem cdot_mul_left (c : ℂ) (a b : Fin 3 → ℂ) : cdot (fun i => c * a i) b = c * cdot a b := by
  unfold cdot
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem cdot_conj (a b : Fin 3 → ℂ) :
    cdot (fun i => conj (a i)) (fun i => conj (b i)) = conj (cdot a b) := by
  unfold cdot
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]

theorem integrable_cdot_modeVel (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : ModeL2Internal.IsSquareField X) (hY : ModeL2Internal.IsSquareField Y) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2)) ModeL2Internal.slab := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => cdot (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2))
      ModeL2Internal.slab :=
    (ModeL2Internal.aestronglyMeasurable_cdot (fun i => ModeL2Internal.aestronglyMeasurable_modeVel hX.1 ι i)
      (fun i => ModeL2Internal.aestronglyMeasurable_modeVel hY.1 ι i)).mono_ac ModeL2Internal.slab_ac
  refine ((ModeL2Internal.integrable_cnormSq_modeVel hPars hX ι).add
    (ModeL2Internal.integrable_cnormSq_modeVel hPars hY ι)).mono' hm (ae_of_all _ fun z => ?_)
  have h1 := ModeL2Internal.norm_cdot_le (modeVel ι X z.1 z.2) (modeVel ι Y z.1 z.2) one_pos
  have h2 := ModeL2Internal.cnormSq_nonneg (modeVel ι X z.1 z.2)
  have h3 := ModeL2Internal.cnormSq_nonneg (modeVel ι Y z.1 z.2)
  simp only [one_mul, div_one] at h1
  show _ ≤ cnormSq (modeVel ι X z.1 z.2) + cnormSq (modeVel ι Y z.1 z.2)
  linarith

theorem summable_norm_integral_cdot (hPars : ModeSquareSumHolds) {X Y : ℝ → Space → Space}
    (hX : ModeL2Internal.IsSquareField X) (hY : ModeL2Internal.IsSquareField Y) :
    Summable (fun κ : ℤ × ℤ =>
      ‖∫ z, cdot (modeVel κ X z.1 z.2) (modeVel κ Y z.1 z.2) ∂ModeL2Internal.slab‖) := by
  refine Summable.of_nonneg_of_le (fun κ => norm_nonneg _) (fun κ => ?_)
    ((ModeL2Internal.hasSum_cnormSq_modeVel hPars hX).add (ModeL2Internal.hasSum_cnormSq_modeVel hPars hY)).summable
  have iX := ModeL2Internal.integrable_cnormSq_modeVel hPars hX κ
  have iY := ModeL2Internal.integrable_cnormSq_modeVel hPars hY κ
  refine (norm_integral_le_integral_norm _).trans ?_
  rw [← integral_add iX iY]
  refine integral_mono (integrable_cdot_modeVel hPars hX hY κ).norm (iX.add iY) fun z => ?_
  have h1 := ModeL2Internal.norm_cdot_le (modeVel κ X z.1 z.2) (modeVel κ Y z.1 z.2) one_pos
  have h2 := ModeL2Internal.cnormSq_nonneg (modeVel κ X z.1 z.2)
  have h3 := ModeL2Internal.cnormSq_nonneg (modeVel κ Y z.1 z.2)
  simp only [one_mul, div_one] at h1
  show _ ≤ cnormSq (modeVel κ X z.1 z.2) + cnormSq (modeVel κ Y z.1 z.2)
  linarith

theorem mode_orthogonal (hPars : ModeSquareSumHolds) (hSolenoidal : SolenoidalModeHolds) (F Q' : ℝ → Space → Space)
    (hF : ModeL2Internal.IsSquareField F) (hQ' : IsSolenoidalPartOf F Q') (ι : ℤ × ℤ) :
    ∫ z, (cdot (modeVel ι Q' z.1 z.2) (modeVel ι (fun σ y => Q' σ y - F σ y) z.1 z.2)).re ∂ModeL2Internal.slab = 0 := by
  obtain ⟨Q0, hQ0, -, -, huniq, hcov⟩ := hSolenoidal F hF.1 hF.2.1 hF.2.2
  have hQ0s : ModeL2Internal.IsSquareField Q0 := ⟨hQ0.1, hQ0.2.1, hQ0.2.2.1⟩
  have hQs : ModeL2Internal.IsSquareField Q' := ⟨hQ'.1, hQ'.2.1, hQ'.2.2.1⟩
  have hG0 := PairingSplitInternal.square_lin hQs hF 1 (-1)
  have eG : (fun σ y => (1 : ℝ) • Q' σ y + (-1 : ℝ) • F σ y) = (fun σ y => Q' σ y - F σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eG] at hG0
  obtain ⟨d, hd⟩ : ∃ d : ℤ × ℤ → ℂ, ∀ κ, d κ = ∫ z, cdot (modeVel κ Q0 z.1 z.2)
      (modeVel κ (fun σ y => Q' σ y - F σ y) z.1 z.2) ∂ModeL2Internal.slab := ⟨_, fun _ => rfl⟩
  have hre : ∀ κ, (d κ).re = ∫ z, (cdot (modeVel κ Q0 z.1 z.2)
      (modeVel κ (fun σ y => Q' σ y - F σ y) z.1 z.2)).re ∂ModeL2Internal.slab := by
    intro κ
    rw [hd κ]
    have h1 := Complex.reCLM.integral_comp_comm (integrable_cdot_modeVel hPars hQ0s hG0 κ)
    simp only [Complex.reCLM_apply] at h1
    exact h1.symm
  have hsum : Summable fun κ => ‖d κ‖ := by
    simp only [hd]
    exact summable_norm_integral_cdot hPars hQ0s hG0
  have hzero : ∀ τ φ : ℝ, HasSum (fun κ : ℤ × ℤ => (torusWave κ τ φ * d κ).re) 0 := by
    intro τ φ
    have hL := hcov τ φ
    have hM : ModeL2Internal.IsSquareField (fun σ y => axialRot (-φ) (Q0 (σ + τ) (axialRot φ y))) :=
      ⟨hL.1, hL.2.1, hL.2.2.1⟩
    have hp := pairing_modes_zero hPars hSolenoidal F Q' _ hF hQ' hM hL.2.2.2.1
    convert hp using 1
    funext κ
    have hmv : ∀ σ y, modeVel κ (fun σ y => axialRot (-φ) (Q0 (σ + τ) (axialRot φ y))) σ y
        = fun i => torusWave κ τ φ * modeVel κ Q0 σ y i := fun σ y =>
      funext fun i => Internal.SmoothPieceMuDivergence.modeVel_shiftRot κ Q0 hQ0.2.1 τ φ σ y i
    simp only [hmv, cdot_mul_left]
    have h1 := Complex.reCLM.integral_comp_comm
      ((integrable_cdot_modeVel hPars hQ0s hG0 κ).const_mul (torusWave κ τ φ))
    simp only [Complex.reCLM_apply] at h1
    rw [h1, integral_const_mul, hd κ]
  have htor := torus_coeff_re d hsum hzero ι
  have hneg : (d (-ι)).re = (d ι).re := by
    rw [hre, hre]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    have e1 : modeVel (-ι) Q0 z.1 z.2 = fun i => conj (modeVel ι Q0 z.1 z.2 i) :=
      funext fun i => Internal.SmoothPieceMuDivergence.modeVel_neg ι Q0 z.1 z.2 i
    have e2 : modeVel (-ι) (fun σ y => Q' σ y - F σ y) z.1 z.2
        = fun i => conj (modeVel ι (fun σ y => Q' σ y - F σ y) z.1 z.2 i) :=
      funext fun i => Internal.SmoothPieceMuDivergence.modeVel_neg ι _ z.1 z.2 i
    simp only [e1, e2, cdot_conj, Complex.conj_re]
  have hdι : (d ι).re = 0 := by linarith
  have hae := modeVel_add_ae (X := Q0) (Y := fun _ _ => (0 : Space)) (Z := Q') hPars hQ0.1 hQ0.2.1 hQ0.2.2.1
    aestronglyMeasurable_const (fun _ _ => rfl) (by simp [periodLIntegral]) hQ'.1 hQ'.2.1 hQ'.2.2.1
    ((huniq Q' hQ').mono fun z hz => by rw [hz, add_zero]) ι
  rw [hre] at hdι
  rw [← hdι]
  refine integral_congr_ae (hae.mono fun z hz => ?_)
  simp only [hz, modeVel_zero, add_zero]

end Internal.SmoothPressure

open Internal.SmoothPressure in
theorem solenoidal_reflection_modes (hPars : ModeSquareSumHolds) (hSolenoidal : SolenoidalModeHolds)
    (F Q' : ℝ → Space → Space) (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hQ' : IsSolenoidalPartOf F Q') :
    AEStronglyMeasurable (fun z : ℝ × Space => (2 : ℝ) • Q' z.1 z.2 - F z.1 z.2) volume ∧
      IsTimePeriodic (fun σ y => (2 : ℝ) • Q' σ y - F σ y) ∧
      periodLIntegral (fun σ y => ‖(2 : ℝ) • Q' σ y - F σ y‖ ^ 2) < ⊤ ∧
      ∀ ι : ℤ × ℤ, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => (2 : ℝ) • Q' σ y - F σ y) σ y)))
        = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeVel ι F σ y)) := by
  have hFs : ModeL2Internal.IsSquareField F := ⟨hFm, hFp, hF2⟩
  have hQs : ModeL2Internal.IsSquareField Q' := ⟨hQ'.1, hQ'.2.1, hQ'.2.2.1⟩
  have hY0 := PairingSplitInternal.square_lin hQs hFs 2 (-1)
  have eY : (fun σ y => (2 : ℝ) • Q' σ y + (-1 : ℝ) • F σ y) = (fun σ y => (2 : ℝ) • Q' σ y - F σ y) := by
    funext σ y
    rw [neg_one_smul, ← sub_eq_add_neg]
  rw [eY] at hY0
  have hG0 := PairingSplitInternal.square_lin hQs hFs 1 (-1)
  have eG : (fun σ y => (1 : ℝ) • Q' σ y + (-1 : ℝ) • F σ y) = (fun σ y => Q' σ y - F σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eG] at hG0
  refine ⟨hY0.1, hY0.2.1, hY0.2.2, fun ι => ?_⟩
  have a1 := modeVel_add_ae (X := Q') (Y := (fun σ y => Q' σ y - F σ y)) (Z := (fun σ y => (2 : ℝ) • Q' σ y - F σ y)) hPars
    hQs.1 hQs.2.1 hQs.2.2 hG0.1 hG0.2.1 hG0.2.2 hY0.1 hY0.2.1 hY0.2.2
    (ae_of_all _ fun z => by rw [two_smul]; abel) ι
  have a2 := modeVel_add_ae (X := F) (Y := (fun σ y => Q' σ y - F σ y)) (Z := Q') hPars
    hFm hFp hF2 hG0.1 hG0.2.1 hG0.2.2 hQs.1 hQs.2.1 hQs.2.2 (ae_of_all _ fun z => by abel) ι
  have hbase := mode_orthogonal hPars hSolenoidal F Q' hFs hQ' ι
  have iF := ModeL2Internal.integrable_cnormSq_modeVel hPars hFs ι
  have iY := ModeL2Internal.integrable_cnormSq_modeVel hPars hY0 ι
  have iC := ModeL2Internal.integrable_re_cdot_modeVel hPars hQs hG0 ι
  have key : ∫ z, cnormSq (modeVel ι (fun σ y => (2 : ℝ) • Q' σ y - F σ y) z.1 z.2) ∂ModeL2Internal.slab = ∫ z, cnormSq (modeVel ι F z.1 z.2) ∂ModeL2Internal.slab := by
    have e : ∫ z, cnormSq (modeVel ι (fun σ y => (2 : ℝ) • Q' σ y - F σ y) z.1 z.2) ∂ModeL2Internal.slab
        = ∫ z, (cnormSq (modeVel ι F z.1 z.2)
          + 4 * (cdot (modeVel ι Q' z.1 z.2) (modeVel ι (fun σ y => Q' σ y - F σ y) z.1 z.2)).re) ∂ModeL2Internal.slab := by
      refine integral_congr_ae ?_
      filter_upwards [a1, a2] with z h1 h2
      have h3 : modeVel ι F z.1 z.2 = modeVel ι Q' z.1 z.2 - modeVel ι (fun σ y => Q' σ y - F σ y) z.1 z.2 := by
        rw [h2]
        abel
      rw [h1, h3]
      exact cnormSq_add_eq _ _
    rw [e, integral_add iF (iC.const_mul 4), integral_const_mul, hbase, mul_zero, add_zero]
  have mY : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι (fun σ y => (2 : ℝ) • Q' σ y - F σ y) z.1 z.2)) ModeL2Internal.slab :=
    (ModeL2Internal.aestronglyMeasurable_cnormSq
      (fun i => ModeL2Internal.aestronglyMeasurable_modeVel hY0.1 ι i)).mono_ac ModeL2Internal.slab_ac
  have mF : AEStronglyMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι F z.1 z.2)) ModeL2Internal.slab :=
    (ModeL2Internal.aestronglyMeasurable_cnormSq
      (fun i => ModeL2Internal.aestronglyMeasurable_modeVel hFm ι i)).mono_ac ModeL2Internal.slab_ac
  show periodLIntegral (fun σ y => cnormSq (modeVel ι (fun σ y => (2 : ℝ) • Q' σ y - F σ y) σ y))
    = periodLIntegral (fun σ y => cnormSq (modeVel ι F σ y))
  rw [ModeL2Internal.periodLIntegral_eq_slab _ mY, ModeL2Internal.periodLIntegral_eq_slab _ mF,
    ← ofReal_integral_eq_lintegral_ofReal iY (ae_of_all _ fun z => ModeL2Internal.cnormSq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal iF (ae_of_all _ fun z => ModeL2Internal.cnormSq_nonneg _), key]

namespace Internal.SmoothPressure

theorem innerPart_sub_orthogonal (P : ℝ) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v) (q : ℝ → Space → ℝ)
    (hq : IsPeriodicTestPotential q) :
    ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (gradientAt (q σ) y) = 0 := by
  obtain ⟨hqs, -, R, hR⟩ := hq
  have c6 : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    (PairingSplitInternal.contDiff_slice (V := W) hW (by norm_num)).clm_apply (hv.smooth.of_le (by norm_cast))
  have hS : ContDiff ℝ 1 (fun z : ℝ × Space => smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2) - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    ((Internal.SmoothPairingClass.smoothRight_contDiff' hW hv).sub c6).sub c6
  have e : ∀ σ, ∫ y, inner ℝ (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (gradientAt (q σ) y) = 0 := fun σ =>
    Internal.SmoothPieceMuDivergence.orthogonal_of_div_zero
      (Internal.SmoothPairingClass.slice_of_joint
        (V := fun s x => smoothRight P W v s x - fderiv ℝ (W s) x (v s x) - fderiv ℝ (W s) x (v s x)) hS σ)
      (fun x => Internal.SmoothPieceMuDivergence.innerPart_sub_div_zero P W hW hWdiv v hv σ x)
      (Internal.SmoothPairingClass.slice_of_joint hqs σ) (fun y hy => hR σ y hy)
  simp only [e, integral_zero]

end Internal.SmoothPressure

open Internal.SmoothPressure in
theorem solenoidal_split_smooth (hSolenoidal : SolenoidalModeHolds) (P : ℝ) (W : ℝ → Space → Space)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (v : ℝ → Space → Space) (hv : IsSmoothPerturbation P v)
    (Q : ℝ → Space → Space) (hQ : IsSolenoidalPartOf (smoothRight P W v) Q) :
    AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume ∧
      IsTimePeriodic (fun σ y => fderiv ℝ (W σ) y (v σ y)) ∧
      periodLIntegral (fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ ∧
      AEStronglyMeasurable (fun z : ℝ × Space => smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume ∧
      IsTimePeriodic (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) ∧
      periodLIntegral (fun σ y => ‖smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ ∧
      ∃ Q', IsSolenoidalPartOf (fun σ y => fderiv ℝ (W σ) y (v σ y)) Q' ∧ ∀ᵐ z : ℝ × Space, Q z.1 z.2 =
        (smoothRight P W v z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2))
          + ((2 : ℝ) • Q' z.1 z.2 - fderiv ℝ (W z.1) z.2 (v z.1 z.2)) := by
  obtain ⟨D, hD⟩ := hWdecay
  have hD0 := Internal.SmoothPairingClass.decay_nonneg hD
  have dW : ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
    PairingSplitInternal.contDiff_slice (V := W) hW (by norm_num)
  have cF : Continuous (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) :=
    dW.continuous.clm_apply hv.smooth.continuous
  have pF : IsTimePeriodic (fun σ y => fderiv ℝ (W σ) y (v σ y)) := by
    intro σ y
    have ev : v (σ + 1) = v σ := funext fun x => hv.periodic σ x
    have eW : W (σ + 1) = W σ := funext fun x => hWp σ x
    show fderiv ℝ (W (σ + 1)) y (v (σ + 1) y) = _
    rw [ev, eW]
  have bF : ∀ σ y, ‖fderiv ℝ (W σ) y (v σ y)‖ ≤ D * (‖v σ y‖ / (1 + ‖y‖)) := by
    intro σ y
    have h1 : ‖fderiv ℝ (W σ) y‖ ≤ D / (1 + ‖y‖) ^ 2 := by
      have h := hD σ y 1 (by norm_num)
      rwa [norm_iteratedFDeriv_one] at h
    exact ((fderiv ℝ (W σ) y).le_opNorm _).trans ((mul_le_mul_of_nonneg_right h1 (norm_nonneg _)).trans
      (Internal.SmoothPairingClass.div_pow_le_div hD0 (norm_nonneg _) (norm_nonneg y) (by norm_num)))
  have mF := Internal.SmoothPairingClass.memLp_of_bound (h := fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖)
    (g := fun σ y => D * (‖v σ y‖ / (1 + ‖y‖))) cF.norm
    ((Internal.SmoothPairingClass.memLp_weighted hv).const_mul D)
    (fun σ y => by rw [abs_norm]; exact bF σ y)
  have lF : periodLIntegral (fun σ y => ‖fderiv ℝ (W σ) y (v σ y)‖ ^ 2) < ⊤ :=
    Internal.SmoothPairingClass.lt_top_of_memLp_real mF
  have sR := Internal.SmoothPairingClass.smoothRight_square' hW hWp ⟨D, hD⟩ hv
  have sF : ModeL2Internal.IsSquareField (fun σ y => fderiv ℝ (W σ) y (v σ y)) := ⟨cF.aestronglyMeasurable, pF, lF⟩
  have sS0 := PairingSplitInternal.square_lin sR sF 1 (-1)
  have eS : (fun σ y => (1 : ℝ) • smoothRight P W v σ y + (-1 : ℝ) • fderiv ℝ (W σ) y (v σ y))
      = fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eS] at sS0
  have sD0 := PairingSplitInternal.square_lin sS0 sF 1 (-1)
  have eD : (fun σ y => (1 : ℝ) • (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y)) + (-1 : ℝ) • fderiv ℝ (W σ) y (v σ y))
      = fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y) := by
    funext σ y
    rw [one_smul, neg_one_smul, ← sub_eq_add_neg]
  rw [eD] at sD0
  refine ⟨sF.1, sF.2.1, sF.2.2, sS0.1, sS0.2.1, sS0.2.2, ?_⟩
  obtain ⟨Q', hQ', -, -, -, -⟩ := hSolenoidal _ sF.1 sF.2.1 sF.2.2
  refine ⟨Q', hQ', ?_⟩
  have hDD : IsSolenoidalPartOf (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y))
      (fun σ y => smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y)) :=
    ⟨sD0.1, sD0.2.1, sD0.2.2, fun q hq => innerPart_sub_orthogonal P W hW hWdiv v hv q hq, fun _ _ => rfl⟩
  have hFF := PairingSplitInternal.solenoidal_add sF sF hQ' hQ'
  have hsum := PairingSplitInternal.solenoidal_add sD0 (PairingSplitInternal.square_add sF sF) hDD hFF
  have hsum' : IsSolenoidalPartOf (smoothRight P W v)
      (fun σ y => (smoothRight P W v σ y - fderiv ℝ (W σ) y (v σ y) - fderiv ℝ (W σ) y (v σ y)) + (Q' σ y + Q' σ y)) := by
    convert hsum using 1
    funext σ y
    abel
  obtain ⟨Q₀, -, -, -, huniq, -⟩ := hSolenoidal _ sR.1 sR.2.1 sR.2.2
  filter_upwards [huniq Q hQ, huniq _ hsum'] with z h1 h2
  rw [h1, ← h2, two_smul]
  abel

end Coercive

end Breakdown

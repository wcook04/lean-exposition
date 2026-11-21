import Breakdown.FracCell.MeshDataAffineModes

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace MeshGaugeLinearMoment

open SteadyCert Assembly CellAnalysis

private theorem rect_cpt (r₁ r₂ z₁ z₂ : ℝ) : IsCompact (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
  isCompact_Icc.prod isCompact_Icc

private theorem int_aff {s : Set (ℝ × ℝ)} {Iz Ix Iy Iu : ℝ × ℝ → ℂ} {a b K : ℂ}
    (h : ∀ᵐ p ∂(volume.restrict s), Iz p = a * Ix p + b * Iy p + K * Iu p)
    (hx : IntegrableOn Ix s) (hy : IntegrableOn Iy s) (hu : IntegrableOn Iu s) :
    ∫ p in s, Iz p = a * (∫ p in s, Ix p) + b * (∫ p in s, Iy p) + K * (∫ p in s, Iu p) := by
  have h1 : Integrable (fun p => a * Ix p + b * Iy p) (volume.restrict s) := (hx.const_mul a).add (hy.const_mul b)
  rw [integral_congr_ae h, integral_add h1 (hu.const_mul K),
    integral_add (hx.const_mul a) (hy.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul]

private theorem mulc {s : Set (ℝ × ℝ)} (hs : IsCompact s) {F : ℝ × ℝ → ℂ} {W : ℝ × ℝ → ℝ} (hW : Continuous W)
    (hF : IntegrableOn F s) : IntegrableOn (fun p => F p * ((W p : ℝ) : ℂ)) s :=
  hF.mul_continuousOn (Complex.continuous_ofReal.comp hW).continuousOn hs

private theorem presMode_one (m : ℕ) (r z : ℝ) : presMode m 0 (fun _ => 1) r z = 1 := by
  unfold presMode azimuth
  simp
  field_simp

private theorem weighted_radial {c o lo hi : ℝ} {dF : ℝ × ℝ → ℂ} (hc : c ≠ 0) (hmin : 0 ≤ min c o)
    (h1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
  have hs := rect_cpt (min c o) (max c o) lo hi
  by_cases ho : o = 0
  · subst ho
    refine (mulc hs (W := fun _ => 1 / c) continuous_const h1).congr_fun (fun p _ => ?_) hs.measurableSet
    simp only [sub_zero]
    push_cast
    ring
  · have hpos : 0 < min c o := by
      refine lt_of_le_of_ne hmin ?_
      rcases min_choice c o with h | h <;> rw [h]
      · exact Ne.symm hc
      · exact Ne.symm ho
    have hne : ∀ p ∈ Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi, p.1 ≠ 0 :=
      fun p hp => (hpos.trans_le hp.1.1).ne'
    have hg : ContinuousOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) / p.1 : ℝ) : ℂ))
        (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
      refine Complex.continuous_ofReal.comp_continuousOn ?_
      refine ContinuousOn.div ?_ continuous_fst.continuousOn hne
      exact (Continuous.continuousOn (by fun_prop))
    refine (h1.mul_continuousOn hg hs).congr_fun (fun p hp => ?_) hs.measurableSet
    have h0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hne p hp
    push_cast
    field_simp

private theorem radial_lin (c o lo hi : ℝ) (t : ℝ → ℝ) (ht : Continuous t) (hc : c ≠ 0) (hmin : 0 ≤ min c o)
    {Fz Fx Fy U dFz dFx dFy : ℝ × ℝ → ℂ} {a b : ℝ} {K : ℂ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p + K * U p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (iy : IntegrableOn Fy (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (iu : IntegrableOn U (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jx : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dFx p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jy : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dFy p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    radialStripMoment c o lo hi Fz dFz t =
      (a : ℂ) * radialStripMoment c o lo hi Fx dFx t + (b : ℂ) * radialStripMoment c o lo hi Fy dFy t +
        K * radialStripMoment c o lo hi U (fun _ => 0) t := by
  have hs := rect_cpt (min c o) (max c o) lo hi
  have mk : ∀ {F dF : ℝ × ℝ → ℂ}, IntegrableOn F (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
      IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
        (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        ((t p.2 : ℝ) : ℂ)) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
    intro F dF h1 h2
    have h3 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := (h1.const_mul _).add h2
    exact mulc hs (ht.comp continuous_snd) h3
  unfold radialStripMoment
  rw [int_aff (Ix := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fx p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFx p) *
        ((t p.2 : ℝ) : ℂ))
      (Iy := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fy p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFy p) *
        ((t p.2 : ℝ) : ℂ))
      (Iu := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * 0) *
        ((t p.2 : ℝ) : ℂ)) (a := (a : ℂ)) (b := (b : ℂ)) (K := K) ?_
      (mk ix (weighted_radial hc hmin jx)) (mk iy (weighted_radial hc hmin jy)) (mk iu (by simp))]
  · ring
  · filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae hdF] with p h1 h2
    rw [h1, h2]
    ring

private theorem height_lin (c o lo hi : ℝ) (t : ℝ → ℝ) (ht : Continuous t)
    {Fz Fx Fy U dFz dFx dFy : ℝ × ℝ → ℂ} {a b : ℝ} {K : ℂ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p + K * U p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (iy : IntegrableOn Fy (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (iu : IntegrableOn U (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jx : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dFx p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jy : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dFy p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi (fun r => r) Fz dFz t =
      (a : ℂ) * heightStripMoment c o lo hi (fun r => r) Fx dFx t +
        (b : ℂ) * heightStripMoment c o lo hi (fun r => r) Fy dFy t +
        K * heightStripMoment c o lo hi (fun r => r) U (fun _ => 0) t := by
  have hs := rect_cpt lo hi (min c o) (max c o)
  have mk : ∀ {F dF : ℝ × ℝ → ℂ}, IntegrableOn F (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        (((fun r : ℝ => r) p.1 * t p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    intro F dF h1 h2
    have i1 := mulc hs (W := fun p : ℝ × ℝ => 1 / (c - o) * (p.1 * t p.1)) (by fun_prop) h1
    have i2 := mulc hs (W := fun p : ℝ × ℝ => (p.2 - o) / (c - o) * t p.1) (by fun_prop) h2
    refine (i1.add i2).congr_fun (fun p _ => ?_) hs.measurableSet
    simp only [Pi.add_apply]
    push_cast
    ring
  unfold heightStripMoment
  rw [int_aff (Ix := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fx p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFx p) *
        (((fun r : ℝ => r) p.1 * t p.1 : ℝ) : ℂ))
      (Iy := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fy p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFy p) *
        (((fun r : ℝ => r) p.1 * t p.1 : ℝ) : ℂ))
      (Iu := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * 0) *
        (((fun r : ℝ => r) p.1 * t p.1 : ℝ) : ℂ)) (a := (a : ℂ)) (b := (b : ℂ)) (K := K) ?_
      (mk ix jx) (mk iy jy) (mk iu (by simp))]
  · ring
  · filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae hdF] with p h1 h2
    rw [h1, h2]
    ring

private theorem test_cont (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

theorem presMoment_affine (S : FaceSegment) (_hS : IsFaceSegment S)
    (hrad : S.radial → S.level ≠ 0 ∧ 0 ≤ min S.level S.other) (m : ℕ) (Q Q' : Space → Space)
    (hQ : IsGradientField Q) (hQ' : IsGradientField Q') (a b C e e' e'' : ℝ)
    (hC : potentialOf (a • Q + b • Q') =ᵐ[volume] fun y => a * potentialOf Q y + b * potentialOf Q' y + C) (d : ℕ) :
    S.moment true (fun p => presMode m 0 (fun y => potentialOf (a • Q + b • Q') y - e'') p.1 p.2)
        (fun p => modeVec m 0 (a • Q + b • Q') p.1 p.2 0) (fun p => modeVec m 0 (a • Q + b • Q') p.1 p.2 2) d =
      (a : ℂ) * S.moment true (fun p => presMode m 0 (fun y => potentialOf Q y - e) p.1 p.2)
          (fun p => modeVec m 0 Q p.1 p.2 0) (fun p => modeVec m 0 Q p.1 p.2 2) d +
        (b : ℂ) * S.moment true (fun p => presMode m 0 (fun y => potentialOf Q' y - e') p.1 p.2)
          (fun p => modeVec m 0 Q' p.1 p.2 0) (fun p => modeVec m 0 Q' p.1 p.2 2) d +
        ((C - e'' + a * e + b * e' : ℝ) : ℂ) * S.moment true (fun _ => 1) (fun _ => 0) (fun _ => 0) d := by
  have hA := MeshDataAffineModes.gradient_modes_affine m Q Q' hQ hQ' a b C e e' e'' hC 0
  have hF : ∀ᵐ p : ℝ × ℝ ∂volume,
      presMode m 0 (fun y => potentialOf (a • Q + b • Q') y - e'') p.1 p.2 =
        (a : ℂ) * presMode m 0 (fun y => potentialOf Q y - e) p.1 p.2 +
        (b : ℂ) * presMode m 0 (fun y => potentialOf Q' y - e') p.1 p.2 +
        ((C - e'' + a * e + b * e' : ℝ) : ℂ) * (fun _ : ℝ × ℝ => (1 : ℂ)) p := by
    filter_upwards [hA] with p hp
    rw [hp.1, presMode_one]
  have hr0 : ∀ᵐ p : ℝ × ℝ ∂volume, modeVec m 0 (a • Q + b • Q') p.1 p.2 0 =
      (a : ℂ) * modeVec m 0 Q p.1 p.2 0 + (b : ℂ) * modeVec m 0 Q' p.1 p.2 0 := hA.mono (fun p hp => hp.2 0)
  have hz2 : ∀ᵐ p : ℝ × ℝ ∂volume, modeVec m 0 (a • Q + b • Q') p.1 p.2 2 =
      (a : ℂ) * modeVec m 0 Q p.1 p.2 2 + (b : ℂ) * modeVec m 0 Q' p.1 p.2 2 := hA.mono (fun p hp => hp.2 2)
  have iP := fun r₁ r₂ z₁ z₂ => MeshDataAffineModes.gradient_modes_integrable m Q hQ 0 e r₁ r₂ z₁ z₂
  have iP' := fun r₁ r₂ z₁ z₂ => MeshDataAffineModes.gradient_modes_integrable m Q' hQ' 0 e' r₁ r₂ z₁ z₂
  have iU : ∀ r₁ r₂ z₁ z₂ : ℝ, IntegrableOn (fun _ : ℝ × ℝ => (1 : ℂ)) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun r₁ r₂ z₁ z₂ => continuousOn_const.integrableOn_compact (rect_cpt r₁ r₂ z₁ z₂)
  unfold FaceSegment.moment
  by_cases hr : S.radial = true
  · simp only [hr, if_true]
    obtain ⟨hc, hmin⟩ := hrad hr
    exact radial_lin S.level S.other S.lo S.hi (S.test d) (test_cont S d) hc hmin hF hr0
      (iP _ _ _ _).1 (iP' _ _ _ _).1 (iU _ _ _ _) ((iP _ _ _ _).2 0) ((iP' _ _ _ _).2 0)
  · simp only [hr, if_true, Bool.false_eq_true, if_false]
    exact height_lin S.level S.other S.lo S.hi (S.test d) (test_cont S d) hF hz2
      (iP _ _ _ _).1 (iP' _ _ _ _).1 (iU _ _ _ _) ((iP _ _ _ _).2 2) ((iP' _ _ _ _).2 2)

end MeshGaugeLinearMoment

end CellFormula

end CellCert

end Breakdown

import Breakdown.FracCell.MeshMomentLinear
import Breakdown.FracCell.MeshDataAffineModes
import Breakdown.FracCell.MeshGaugeLinearPotential

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula


private theorem setInt_affine {s : Set (ℝ × ℝ)} {Iz Ix Iy Iu : ℝ × ℝ → ℂ} {a b K : ℂ}
    (h : ∀ᵐ p ∂(volume.restrict s), Iz p = a * Ix p + b * Iy p + K * Iu p)
    (hx : IntegrableOn Ix s) (hy : IntegrableOn Iy s) (hu : IntegrableOn Iu s) :
    ∫ p in s, Iz p = a * (∫ p in s, Ix p) + b * (∫ p in s, Iy p) + K * (∫ p in s, Iu p) := by
  have h1 : Integrable (fun p => a * Ix p + b * Iy p) (volume.restrict s) := (hx.const_mul a).add (hy.const_mul b)
  rw [integral_congr_ae h, integral_add h1 (hu.const_mul K),
    integral_add (hx.const_mul a) (hy.const_mul b), integral_const_mul, integral_const_mul,
    integral_const_mul]

private theorem rect_compact (r₁ r₂ z₁ z₂ : ℝ) : IsCompact (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
  isCompact_Icc.prod isCompact_Icc

private theorem radial_aff (c o lo hi : ℝ) (t : ℝ → ℝ) (ht : Continuous t)
    {Fz Fx Fy dFz dFx dFy U : ℝ × ℝ → ℂ} {a b : ℝ} {K : ℂ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p + K * U p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (iy : IntegrableOn Fy (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (iu : IntegrableOn U (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jx : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFx p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jy : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFy p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    radialStripMoment c o lo hi Fz dFz t =
      (a : ℂ) * radialStripMoment c o lo hi Fx dFx t + (b : ℂ) * radialStripMoment c o lo hi Fy dFy t +
        K * radialStripMoment c o lo hi U (fun _ => 0) t := by
  have hs := rect_compact (min c o) (max c o) lo hi
  have hT : ContinuousOn (fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ)) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) :=
    (Complex.continuous_ofReal.comp (ht.comp continuous_snd)).continuousOn
  have mk : ∀ {F dF : ℝ × ℝ → ℂ}, IntegrableOn F (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
      IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
        (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        ((t p.2 : ℝ) : ℂ)) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
    intro F dF h1 h2
    have h3 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := (h1.const_mul _).add h2
    exact h3.mul_continuousOn hT hs
  unfold radialStripMoment
  rw [setInt_affine (Ix := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fx p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFx p) *
        ((t p.2 : ℝ) : ℂ))
      (Iy := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fy p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFy p) *
        ((t p.2 : ℝ) : ℂ))
      (Iu := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * 0) *
        ((t p.2 : ℝ) : ℂ)) (a := (a : ℂ)) (b := (b : ℂ)) (K := K) ?_ (mk ix jx) (mk iy jy)
      (mk iu (by simp))]
  · simp only []
    ring
  · filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae hdF] with p h1 h2
    rw [h1, h2]
    ring

private theorem height_aff (c o lo hi : ℝ) (wt t : ℝ → ℝ) (hw : Continuous wt) (ht : Continuous t)
    {Fz Fx Fy dFz dFx dFy U : ℝ × ℝ → ℂ} {a b : ℝ} {K : ℂ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p + K * U p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (iy : IntegrableOn Fy (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (iu : IntegrableOn U (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jx : IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 : ℝ) : ℂ) * dFx p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jy : IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 : ℝ) : ℂ) * dFy p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi wt Fz dFz t =
      (a : ℂ) * heightStripMoment c o lo hi wt Fx dFx t + (b : ℂ) * heightStripMoment c o lo hi wt Fy dFy t +
        K * heightStripMoment c o lo hi wt U (fun _ => 0) t := by
  have hs := rect_compact lo hi (min c o) (max c o)
  have hT : ContinuousOn (fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) :=
    (Complex.continuous_ofReal.comp ((hw.comp continuous_fst).mul (ht.comp continuous_fst))).continuousOn
  have hB : ContinuousOn (fun p : ℝ × ℝ => ((((p.2 - o) / (c - o)) * t p.1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    apply Continuous.continuousOn
    fun_prop
  have mk : ∀ {F dF : ℝ × ℝ → ℂ}, IntegrableOn F (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
      IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 : ℝ) : ℂ) * dF p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        ((wt p.1 * t p.1 : ℝ) : ℂ)) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := by
    intro F dF h1 h2
    have e1 := (h1.mul_continuousOn hT hs).const_mul ((((1 / (c - o) : ℝ)) : ℂ))
    have e2 := IntegrableOn.continuousOn_mul hB h2 hs
    have e3 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o) : ℝ)) : ℂ) * (F p * ((wt p.1 * t p.1 : ℝ) : ℂ)) +
        ((((p.2 - o) / (c - o)) * t p.1 : ℝ) : ℂ) * (((wt p.1 : ℝ) : ℂ) * dF p))
        (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := e1.add e2
    refine e3.congr_fun (fun p _ => ?_) hs.measurableSet
    push_cast
    ring
  unfold heightStripMoment
  rw [setInt_affine (Ix := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fx p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFx p) *
        ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Iy := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fy p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFy p) *
        ((wt p.1 * t p.1 : ℝ) : ℂ))
      (Iu := fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * U p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * 0) *
        ((wt p.1 * t p.1 : ℝ) : ℂ)) (a := (a : ℂ)) (b := (b : ℂ)) (K := K) ?_ (mk ix jx) (mk iy jy)
      (mk iu (by simp))]
  · simp only []
    ring
  · filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae hdF] with p h1 h2
    rw [h1, h2]
    ring

private theorem corner_aff (cr orr cz oz : ℝ) {Fz Fx Fy Gz Gx Gy Rlz Rx Ry Wz Wx Wy : ℝ × ℝ → ℂ} {a b : ℝ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p)
    (hG : ∀ᵐ p ∂volume, Gz p = a * Gx p + b * Gy p)
    (hR : ∀ᵐ p ∂volume, Rlz p = a * Rx p + b * Ry p)
    (hW : ∀ᵐ p ∂volume, Wz p = a * Wx p + b * Wy p)
    (ifx : IntegrableOn Fx (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (ify : IntegrableOn Fy (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (igx : IntegrableOn Gx (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (igy : IntegrableOn Gy (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (irx : IntegrableOn Rx (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (iry : IntegrableOn Ry (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (iwx : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * Wx p)
      (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)))
    (iwy : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * Wy p)
      (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz))) :
    cornerMoment cr orr cz oz Fz Gz Rlz Wz =
      (a : ℂ) * cornerMoment cr orr cz oz Fx Gx Rx Wx + (b : ℂ) * cornerMoment cr orr cz oz Fy Gy Ry Wy := by
  have hs := rect_compact (min cr orr) (max cr orr) (min cz oz) (max cz oz)
  have mk : ∀ {F G R W : ℝ × ℝ → ℂ},
      IntegrableOn F (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) →
      IntegrableOn G (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) →
      IntegrableOn R (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) →
      IntegrableOn (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * W p)
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) →
      IntegrableOn (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * R p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * G p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * W p)
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) := by
    intro F G R W h1 h3 h2 h4
    have c2 : ContinuousOn (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ))
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) := by
      apply Continuous.continuousOn; fun_prop
    have c3 : ContinuousOn (fun p : ℝ × ℝ => (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ))
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) := by
      apply Continuous.continuousOn; fun_prop
    have c4 : ContinuousOn (fun p : ℝ × ℝ => (((p.2 - oz) / (cz - oz) : ℝ) : ℂ))
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) := by
      apply Continuous.continuousOn; fun_prop
    have e1 := h1.const_mul ((((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ))
    have e2 := IntegrableOn.continuousOn_mul c2 h2 hs
    have e3 := IntegrableOn.continuousOn_mul c3 h3 hs
    have e4 := IntegrableOn.continuousOn_mul c4 h4 hs
    have e5 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (cr - orr) : ℝ)) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * F p
        + (((1 / (cr - orr) : ℝ)) : ℂ) * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * R p
        + (((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * (((1 / (cz - oz) : ℝ)) : ℂ) * G p
        + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * ((((p.1 - orr) / (cr - orr) : ℝ) : ℂ) * W p))
        (Set.Icc (min cr orr) (max cr orr) ×ˢ Set.Icc (min cz oz) (max cz oz)) := ((e1.add e2).add e3).add e4
    refine e5.congr_fun (fun p _ => ?_) hs.measurableSet
    ring
  unfold cornerMoment
  rw [setInt_affine (K := 0) (Iu := fun _ => 0) (a := (a : ℂ)) (b := (b : ℂ)) ?_ (mk ifx igx irx iwx)
    (mk ify igy iry iwy) (by simp)]
  · ring
  · filter_upwards [ae_restrict_of_ae hF, ae_restrict_of_ae hG, ae_restrict_of_ae hR, ae_restrict_of_ae hW]
      with p h1 h2 h3 h4
    rw [h1, h2, h3, h4]
    ring

private theorem lw_cont (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

private theorem coef_aff (B : CellBases) (K : CellBox) (j l : ℕ) {Fz Fx Fy : ℝ × ℝ → ℂ} {a b : ℝ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p)
    (ix : IntegrableOn Fx K.rect) (iy : IntegrableOn Fy K.rect) :
    B.coef K Fz j l = (a : ℂ) * B.coef K Fx j l + (b : ℂ) * B.coef K Fy j l := by
  have hs : IsCompact K.rect := rect_compact _ _ _ _
  have cw : ContinuousOn (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp ((lw_cont K).comp continuous_fst)).continuousOn
  have cp : ContinuousOn (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    apply Continuous.continuousOn
    unfold CellBases.radialPoly CellBases.heightPoly
    fun_prop
  have mk : ∀ {F : ℝ × ℝ → ℂ}, IntegrableOn F K.rect → IntegrableOn (fun p : ℝ × ℝ =>
      ((K.lineWeight p.1 : ℝ) : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect :=
    fun h => (IntegrableOn.continuousOn_mul cw h hs).mul_continuousOn cp hs
  unfold CellBases.coef
  rw [setInt_affine (K := 0) (Iu := fun _ => 0) (a := (a : ℂ)) (b := (b : ℂ)) ?_ (mk ix) (mk iy) (by simp)]
  · ring
  · filter_upwards [ae_restrict_of_ae hF] with p h1
    rw [h1]
    ring

private theorem wcase {c o lo hi : ℝ} {dF : ℝ × ℝ → ℂ} (hc : c ≠ 0) (hmin : 0 ≤ min c o)
    (h1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (h2 : 0 < min c o → IntegrableOn dF (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi) := by
  have hs := rect_compact (min c o) (max c o) lo hi
  by_cases ho : o = 0
  · subst ho
    have h3 : IntegrableOn (fun p : ℝ × ℝ => ((1 / c : ℝ) : ℂ) * ((p.1 : ℂ) * dF p))
      (Set.Icc (min c 0) (max c 0) ×ˢ Set.Icc lo hi) := h1.const_mul _
    refine h3.congr_fun (fun p _ => ?_) hs.measurableSet
    push_cast
    ring
  · have hpos : 0 < min c o := by
      refine lt_of_le_of_ne hmin ?_
      rcases min_choice c o with h | h <;> rw [h]
      · exact Ne.symm hc
      · exact Ne.symm ho
    refine IntegrableOn.continuousOn_mul ?_ (h2 hpos) hs
    apply Continuous.continuousOn
    fun_prop

private theorem unweight {r₁ r₂ z₁ z₂ : ℝ} (h0 : 0 < r₁) {F : ℝ × ℝ → ℂ}
    (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂)) :
    IntegrableOn F (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) := by
  have hs := rect_compact r₁ r₂ z₁ z₂
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((p.1⁻¹ : ℝ) : ℂ)) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    Complex.continuous_ofReal.comp_continuousOn
      (continuous_fst.continuousOn.inv₀ (fun p hp => (h0.trans_le hp.1.1).ne'))
  refine (IntegrableOn.continuousOn_mul hc h hs).congr_fun (fun p hp => ?_) hs.measurableSet
  have hp0 : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (h0.trans_le hp.1.1).ne'
  push_cast
  field_simp

private theorem test_cont (S : FaceSegment) (d : ℕ) : Continuous (S.test d) := by
  unfold FaceSegment.test
  fun_prop

private theorem presMode_one (m : ℕ) (hm : 0 < m) (n : ℤ) (r z : ℝ) :
    presMode m n (fun _ => 1) r z = if n = 0 then 1 else 0 := by
  unfold presMode
  simp only [Complex.ofReal_one, mul_one]
  have hpt : ∀ θ : ℝ, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((-(azimuth m n : ℂ) * Complex.I) * (θ : ℂ)) := fun θ => by
    congr 1; push_cast; ring
  simp_rw [hpt]
  split_ifs with hn
  · subst hn
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [azimuth]
    field_simp
  · have hc0 : (-(azimuth m n : ℂ) * Complex.I) ≠ 0 := by
      refine mul_ne_zero (neg_ne_zero.2 ?_) Complex.I_ne_zero
      unfold azimuth
      push_cast
      exact mul_ne_zero (by exact_mod_cast hn) (by exact_mod_cast hm.ne')
    rw [integral_exp_mul_complex hc0]
    have h2 : Complex.exp ((-(azimuth m n : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have := Complex.exp_int_mul_two_pi_mul_I (-(n * m))
      rw [← this]
      congr 1
      unfold azimuth
      push_cast
      ring
    rw [h2]
    simp

private theorem edge_one (c o : ℝ) (h : o ≠ c) : edgeSign c o * ((max c o - min c o) * (1 / (c - o) : ℝ)) = 1 := by
  unfold edgeSign
  split_ifs with hoc
  · rw [max_eq_left hoc.le, min_eq_right hoc.le]
    have : (c : ℂ) - o ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm h)
    push_cast
    field_simp
  · have hco : c < o := lt_of_le_of_ne (not_lt.1 hoc) (Ne.symm h)
    rw [max_eq_right hco.le, min_eq_left hco.le]
    have : (c : ℂ) - o ≠ 0 := by exact_mod_cast sub_ne_zero.2 (Ne.symm h)
    push_cast
    field_simp
    ring

private theorem radial_unit (S : FaceSegment) (hS : IsFaceSegment S) (d : ℕ) (u : ℂ) :
    radialStripMoment S.level S.other S.lo S.hi (fun _ => u) (fun _ => 0) (S.test d) =
      u * ((∫ z in S.lo..S.hi, S.test d z : ℝ) : ℂ) := by
  unfold radialStripMoment
  have e : ∀ p : ℝ × ℝ, ((((1 / (S.level - S.other) : ℝ)) : ℂ) * (fun _ => u) p +
      (((p.1 - S.other) / (S.level - S.other) : ℝ) : ℂ) * (fun _ => (0 : ℂ)) p) * ((S.test d p.2 : ℝ) : ℂ) =
      (fun _ : ℝ => (((1 / (S.level - S.other) : ℝ)) : ℂ) * u) p.1 * (fun y : ℝ => ((S.test d y : ℝ) : ℂ)) p.2 := by
    intro p; simp
  simp_rw [e]
  have key := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun _ : ℝ => (((1 / (S.level - S.other) : ℝ)) : ℂ) * u) (fun y : ℝ => ((S.test d y : ℝ) : ℂ))
    (Set.Icc (min S.level S.other) (max S.level S.other)) (Set.Icc S.lo S.hi)
  beta_reduce at key
  rw [Measure.volume_eq_prod, key, setIntegral_const,
    Real.volume_real_Icc_of_le (min_le_max), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hS.lo_lt_hi.le, intervalIntegral.integral_ofReal]
  have := edge_one S.level S.other hS.other_ne
  rw [Complex.real_smul]
  push_cast at this ⊢
  linear_combination (u * ((∫ z in S.lo..S.hi, S.test d z : ℝ) : ℂ)) * this

private theorem height_unit (S : FaceSegment) (hS : IsFaceSegment S) (d : ℕ) (u : ℂ) :
    heightStripMoment S.level S.other S.lo S.hi (fun r => r) (fun _ => u) (fun _ => 0) (S.test d) =
      u * ((∫ r in S.lo..S.hi, r * S.test d r : ℝ) : ℂ) := by
  unfold heightStripMoment
  have e : ∀ p : ℝ × ℝ, ((((1 / (S.level - S.other) : ℝ)) : ℂ) * (fun _ => u) p +
      (((p.2 - S.other) / (S.level - S.other) : ℝ) : ℂ) * (fun _ => (0 : ℂ)) p) *
        (((fun r : ℝ => r) p.1 * S.test d p.1 : ℝ) : ℂ) =
      (fun x : ℝ => ((x * S.test d x : ℝ) : ℂ)) p.1 * (fun _ : ℝ => (((1 / (S.level - S.other) : ℝ)) : ℂ) * u) p.2 := by
    intro p; simp only []; ring
  simp_rw [e]
  have key := setIntegral_prod_mul (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (fun x : ℝ => ((x * S.test d x : ℝ) : ℂ)) (fun _ : ℝ => (((1 / (S.level - S.other) : ℝ)) : ℂ) * u)
    (Set.Icc S.lo S.hi) (Set.Icc (min S.level S.other) (max S.level S.other))
  beta_reduce at key
  rw [Measure.volume_eq_prod, key, setIntegral_const,
    Real.volume_real_Icc_of_le (min_le_max), integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hS.lo_lt_hi.le, intervalIntegral.integral_ofReal]
  have := edge_one S.level S.other hS.other_ne
  rw [Complex.real_smul]
  push_cast at this ⊢
  linear_combination (u * ((∫ r in S.lo..S.hi, r * S.test d r : ℝ) : ℂ)) * this

private theorem radial_aff0 (c o lo hi : ℝ) (t : ℝ → ℝ) (ht : Continuous t)
    {Fz Fx Fy dFz dFx dFy : ℝ × ℝ → ℂ} {a b : ℝ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (iy : IntegrableOn Fy (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jx : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFx p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi))
    (jy : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * dFy p)
      (Set.Icc (min c o) (max c o) ×ˢ Set.Icc lo hi)) :
    radialStripMoment c o lo hi Fz dFz t =
      (a : ℂ) * radialStripMoment c o lo hi Fx dFx t + (b : ℂ) * radialStripMoment c o lo hi Fy dFy t := by
  have h := radial_aff c o lo hi t ht (Fz := Fz) (K := 0) (U := fun _ => 0)
    (by filter_upwards [hF] with p h; rw [h]; ring) hdF ix iy (by simp) jx jy
  rw [h]
  ring

private theorem height_aff0 (c o lo hi : ℝ) (wt t : ℝ → ℝ) (hw : Continuous wt) (ht : Continuous t)
    {Fz Fx Fy dFz dFx dFy : ℝ × ℝ → ℂ} {a b : ℝ}
    (hF : ∀ᵐ p ∂volume, Fz p = a * Fx p + b * Fy p)
    (hdF : ∀ᵐ p ∂volume, dFz p = a * dFx p + b * dFy p)
    (ix : IntegrableOn Fx (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (iy : IntegrableOn Fy (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jx : IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 : ℝ) : ℂ) * dFx p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (jy : IntegrableOn (fun p : ℝ × ℝ => ((wt p.1 : ℝ) : ℂ) * dFy p) (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi wt Fz dFz t =
      (a : ℂ) * heightStripMoment c o lo hi wt Fx dFx t + (b : ℂ) * heightStripMoment c o lo hi wt Fy dFy t := by
  have h := height_aff c o lo hi wt t hw ht (Fz := Fz) (K := 0) (U := fun _ => 0)
    (by filter_upwards [hF] with p h; rw [h]; ring) hdF ix iy (by simp) jx jy
  rw [h]
  ring

private theorem cw_mul {s : Set (ℝ × ℝ)} (hs : IsCompact s) {B : ℝ × ℝ → ℝ} (hB : Continuous B)
    {F : ℝ × ℝ → ℂ} (h : IntegrableOn F s) : IntegrableOn (fun p => ((B p : ℝ) : ℂ) * F p) s :=
  IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp hB).continuousOn h hs

private theorem sideTest_cont (L : CellLayout) (e : Fin 4) (d : ℕ) : Continuous (L.sideTest e d) := by
  unfold CellLayout.sideTest CellBases.heightPoly CellBases.radialPoly
  split_ifs
  · fun_prop
  · fun_prop
  · fun_prop

private theorem shiftSum_radial (L : CellLayout) (i : Fin L.presCount × Fin L.degSide)
    (hr : (L.presSegment i.1).radial = true) :
    L.shiftCoefLeft i + L.shiftCoefRight i =
      ∫ z in (L.presSegment i.1).lo..(L.presSegment i.1).hi, (L.presSegment i.1).test i.2 z := by
  unfold CellLayout.shiftCoefLeft CellLayout.shiftCoefRight
  simp only [hr, if_true]
  split_ifs <;> ring

private theorem shiftSum_height (L : CellLayout) (i : Fin L.presCount × Fin L.degSide)
    (hr : ¬ (L.presSegment i.1).radial = true) :
    L.shiftCoefLeft i + L.shiftCoefRight i =
      ∫ r in (L.presSegment i.1).lo..(L.presSegment i.1).hi, r * (L.presSegment i.1).test i.2 r := by
  have key : radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).hi -
      radialWeightIntegral ((L.presSegment i.1).test i.2) (L.presSegment i.1).lo =
      ∫ r in (L.presSegment i.1).lo..(L.presSegment i.1).hi, r * (L.presSegment i.1).test i.2 r := by
    unfold radialWeightIntegral
    exact intervalIntegral.integral_interval_sub_left
      ((continuous_id.mul (test_cont _ _)).intervalIntegrable _ _)
      ((continuous_id.mul (test_cont _ _)).intervalIntegrable _ _)
  rw [← key]
  unfold CellLayout.shiftCoefLeft CellLayout.shiftCoefRight
  simp only [hr, if_false, Bool.false_eq_true]
  split_ifs <;> ring

private def gaugeLevel (m : ℕ) (g : FaceSegment) {k : ℕ} (w : FieldTuple k) : ℝ :=
  (g.moment true (fun p => presMode m 0 (potentialOf w.2.2.2.2) p.1 p.2)
      (fun p => modeVec m 0 w.2.2.2.2 p.1 p.2 0) (fun p => modeVec m 0 w.2.2.2.2 p.1 p.2 2) 0 /
    g.moment true (fun _ => 1) (fun _ => 0) (fun _ => 0) 0).re

private theorem gaugeLevel_eq (L : CellLayout) {k : ℕ} (w : FieldTuple k) {m : ℕ} {g : FaceSegment}
    (hm : L.order = m) (hg : L.gauge = g) : (L.gaugeValue w / L.gaugeUnit).re = gaugeLevel m g w := by
  subst hm hg
  rfl

theorem dataAffine : DataAffineStatement := by
  intro α hα₁ hα₂ k N c hc g x y a b hx hy
  obtain ⟨C0, hC0⟩ := MeshGaugeLinearPotential.potential_affine x.2.2.2.2 y.2.2.2.2 hx.2.1 hy.2.1 a b
  refine ⟨C0 - gaugeLevel c.order g (a • x + b • y) + a * gaugeLevel c.order g x + b * gaugeLevel c.order g y, ?_⟩
  intro L hord hgauge hseg hpseg hrad hprad hcorner d
  have hm : 0 < L.order := by rw [hord]; have := hc.base.order_ge; omega
  have hxs : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := hord ▸ hx.1
  have hys : IsSecondOrderField L.order y.1 y.2.1 y.2.2.1 := hord ▸ hy.1
  have iV : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i : Fin 3) (r₁ r₂ z₁ z₂ : ℝ),
      IntegrableOn (L.velMode n w i) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) := fun w hw n i r₁ r₂ z₁ z₂ =>
    (MeshDataAffineModes.secondOrder_modes_integrable L.order w.1 w.2.1 w.2.2.1 (hord ▸ hw.1) n r₁ r₂ z₁ z₂).1 i
  have iG : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i j : Fin 3) (r₁ r₂ z₁ z₂ : ℝ),
      IntegrableOn (L.gradModeOf n w i j) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) := fun w hw n i j r₁ r₂ z₁ z₂ =>
    (MeshDataAffineModes.secondOrder_modes_integrable L.order w.1 w.2.1 w.2.2.1 (hord ▸ hw.1) n r₁ r₂ z₁ z₂).2.1 i j
  have iH : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i j l : Fin 3) (r₁ r₂ z₁ z₂ : ℝ),
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n w i j l p) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun w hw n i j l r₁ r₂ z₁ z₂ =>
    (MeshDataAffineModes.secondOrder_modes_integrable L.order w.1 w.2.1 w.2.2.1 (hord ▸ hw.1) n r₁ r₂ z₁ z₂).2.2 i j l
  have iH' : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i j l : Fin 3) (r₁ r₂ z₁ z₂ : ℝ), 0 < r₁ →
      IntegrableOn (L.secondModeOf n w i j l) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun w hw n i j l r₁ r₂ z₁ z₂ h => unweight h (iH w hw n i j l r₁ r₂ z₁ z₂)
  have iQ : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i : Fin 3) (r₁ r₂ z₁ z₂ : ℝ),
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.pressureGradMode n w i p) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun w hw n i r₁ r₂ z₁ z₂ =>
    (MeshDataAffineModes.gradient_modes_integrable L.order w.2.2.2.2 hw.2.1 n 0 r₁ r₂ z₁ z₂).2 i
  have iQ' : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (i : Fin 3) (r₁ r₂ z₁ z₂ : ℝ), 0 < r₁ →
      IntegrableOn (L.pressureGradMode n w i) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun w hw n i r₁ r₂ z₁ z₂ h => unweight h (iQ w hw n i r₁ r₂ z₁ z₂)
  have iP : ∀ w : FieldTuple k, IsAdmissible c w → ∀ (n : ℤ) (r₁ r₂ z₁ z₂ : ℝ),
      IntegrableOn (L.pressMode n w) (Set.Icc r₁ r₂ ×ˢ Set.Icc z₁ z₂) :=
    fun w hw n r₁ r₂ z₁ z₂ =>
    (MeshDataAffineModes.gradient_modes_integrable L.order w.2.2.2.2 hw.2.1 n (L.gaugeValue w / L.gaugeUnit).re
      r₁ r₂ z₁ z₂).1
  have hA := fun n : ℤ => MeshDataAffineModes.secondOrder_modes_affine L.order x.1 x.2.1 x.2.2.1 hxs
    y.1 y.2.1 y.2.2.1 hys a b n
  have hV : ∀ (n : ℤ) (i : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume,
      L.velMode n (a • x + b • y) i p = a * L.velMode n x i p + b * L.velMode n y i p := by
    intro n i
    filter_upwards [hA n] with p hp
    exact hp.1 i
  have hG : ∀ (n : ℤ) (i j : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume,
      L.gradModeOf n (a • x + b • y) i j p = a * L.gradModeOf n x i j p + b * L.gradModeOf n y i j p := by
    intro n i j
    filter_upwards [hA n] with p hp
    exact hp.2.1 i j
  have hH : ∀ (n : ℤ) (i j l : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume,
      L.secondModeOf n (a • x + b • y) i j l p = a * L.secondModeOf n x i j l p + b * L.secondModeOf n y i j l p := by
    intro n i j l
    filter_upwards [hA n] with p hp
    exact hp.2.2 i j l
  have hB := fun n : ℤ => MeshDataAffineModes.gradient_modes_affine L.order x.2.2.2.2 y.2.2.2.2 hx.2.1 hy.2.1 a b C0
    (L.gaugeValue x / L.gaugeUnit).re (L.gaugeValue y / L.gaugeUnit).re
    (L.gaugeValue (a • x + b • y) / L.gaugeUnit).re hC0 n
  have hQ : ∀ (n : ℤ) (i : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume,
      L.pressureGradMode n (a • x + b • y) i p = a * L.pressureGradMode n x i p + b * L.pressureGradMode n y i p := by
    intro n i
    filter_upwards [hB n] with p hp
    exact hp.2 i
  have hP : ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume,
      L.pressMode n (a • x + b • y) p = a * L.pressMode n x p + b * L.pressMode n y p +
        (((C0 - gaugeLevel c.order g (a • x + b • y) + a * gaugeLevel c.order g x + b * gaugeLevel c.order g y : ℝ)) : ℂ) *
          (fun _ : ℝ × ℝ => (if n = 0 then (1 : ℂ) else 0)) p := by
    intro n
    filter_upwards [hB n] with p hp
    have e : L.pressMode n (a • x + b • y) p = a * L.pressMode n x p + b * L.pressMode n y p +
        (((C0 - (L.gaugeValue (a • x + b • y) / L.gaugeUnit).re + a * (L.gaugeValue x / L.gaugeUnit).re +
          b * (L.gaugeValue y / L.gaugeUnit).re : ℝ)) : ℂ) * presMode L.order n (fun _ => 1) p.1 p.2 := hp.1
    rw [presMode_one _ hm, gaugeLevel_eq L x hord hgauge, gaugeLevel_eq L y hord hgauge,
      gaugeLevel_eq L (a • x + b • y) hord hgauge] at e
    exact e
  have cpt := rect_compact
  rcases d with i | i | i | i | i | i | i | i
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, mul_zero, Complex.ofReal_zero, add_zero]
    exact coef_aff _ _ _ _ (hG _ _ _) (iG x hx _ _ _ _ _ _ _) (iG y hy _ _ _ _ _ _ _)
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    exact coef_aff _ _ _ _ (hV _ _) (iV x hx _ _ _ _ _ _) (iV y hy _ _ _ _ _ _)
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    unfold FaceSegment.moment
    simp only [Bool.false_eq_true, ↓reduceIte]
    split_ifs with hr
    · exact radial_aff0 _ _ _ _ _ (test_cont _ _) (hV _ _) (hG _ _ _) (iV x hx _ _ _ _ _ _) (iV y hy _ _ _ _ _ _)
        (cw_mul (cpt _ _ _ _) (by fun_prop) (iG x hx _ _ _ _ _ _ _))
        (cw_mul (cpt _ _ _ _) (by fun_prop) (iG y hy _ _ _ _ _ _ _))
    · refine height_aff0 _ _ _ _ _ _ ?_ (test_cont _ _) (hV _ _) (hG _ _ _)
        (iV x hx _ _ _ _ _ _) (iV y hy _ _ _ _ _ _) ?_ ?_
      · exact continuous_const
      · exact cw_mul (cpt _ _ _ _) continuous_const (iG x hx _ _ _ _ _ _ _)
      · exact cw_mul (cpt _ _ _ _) continuous_const (iG y hy _ _ _ _ _ _ _)
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    split_ifs with hr
    · unfold FaceSegment.moment
      simp only [hr, if_true]
      obtain ⟨hl0, hmin⟩ := hrad i.2.1 hr
      exact radial_aff0 _ _ _ _ _ (test_cont _ _) (hG _ _ _) (hH _ _ _ _) (iG x hx _ _ _ _ _ _ _)
        (iG y hy _ _ _ _ _ _ _)
        (wcase hl0 hmin (iH x hx _ _ _ _ _ _ _ _) (fun h => iH' x hx _ _ _ _ _ _ _ _ h))
        (wcase hl0 hmin (iH y hy _ _ _ _ _ _ _ _) (fun h => iH' y hy _ _ _ _ _ _ _ _ h))
    · unfold FaceSegment.moment
      simp only [hr, if_false, Bool.false_eq_true, if_true]
      exact height_aff0 _ _ _ _ (fun r => r) _ continuous_id (test_cont _ _) (hG _ _ _) (hH _ _ _ _)
        (iG x hx _ _ _ _ _ _ _) (iG y hy _ _ _ _ _ _ _) (iH x hx _ _ _ _ _ _ _ _) (iH y hy _ _ _ _ _ _ _ _)
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr]
    unfold FaceSegment.moment
    by_cases hr : (L.presSegment i.2.1).radial = true
    · simp only [hr, if_true]
      obtain ⟨hl0, hmin⟩ := hprad i.2.1 hr
      rw [radial_aff _ _ _ _ _ (test_cont _ _) (hP _) (hQ _ _) (iP x hx _ _ _ _ _) (iP y hy _ _ _ _ _)
        (continuousOn_const.integrableOn_compact (cpt _ _ _ _))
        (wcase hl0 hmin (iQ x hx _ _ _ _ _ _) (fun h => iQ' x hx _ _ _ _ _ _ h))
        (wcase hl0 hmin (iQ y hy _ _ _ _ _ _) (fun h => iQ' y hy _ _ _ _ _ _ h)), radial_unit _ (hpseg _)]
      have hs := shiftSum_radial L (i.2.1, i.2.2) hr
      split_ifs with hn
      · rw [hs]; push_cast; ring
      · push_cast; ring
    · simp only [hr, if_false, Bool.false_eq_true, if_true]
      rw [height_aff _ _ _ _ (fun r => r) _ continuous_id (test_cont _ _) (hP _) (hQ _ _) (iP x hx _ _ _ _ _)
        (iP y hy _ _ _ _ _) (continuousOn_const.integrableOn_compact (cpt _ _ _ _))
        (iQ x hx _ _ _ _ _ _) (iQ y hy _ _ _ _ _ _), height_unit _ (hpseg _)]
      have hs := shiftSum_height L (i.2.1, i.2.2) hr
      split_ifs with hn
      · rw [hs]; push_cast; ring
      · push_cast; ring
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    obtain ⟨h1, h2, h3, h4⟩ := hcorner i.2.1
    exact corner_aff _ _ _ _ (hV _ _) (hG _ _ _) (hG _ _ _) (hH _ _ _ _) (iV x hx _ _ _ _ _ _)
      (iV y hy _ _ _ _ _ _) (iG x hx _ _ _ _ _ _ _) (iG y hy _ _ _ _ _ _ _) (iG x hx _ _ _ _ _ _ _)
      (iG y hy _ _ _ _ _ _ _) (wcase h1 h4 (iH x hx _ _ _ _ _ _ _ _) (fun h => iH' x hx _ _ _ _ _ _ _ _ h))
      (wcase h1 h4 (iH y hy _ _ _ _ _ _ _ _) (fun h => iH' y hy _ _ _ _ _ _ _ _ h))
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    exact height_aff0 _ _ _ _ (fun r => r) (fun _ => 1) continuous_id continuous_const (hV _ _) (hG _ _ _)
      (iV x hx _ _ _ _ _ _) (iV y hy _ _ _ _ _ _)
      (cw_mul (B := fun p => p.1) (cpt _ _ _ _) continuous_fst (iG x hx _ _ _ _ _ _ _))
      (cw_mul (B := fun p => p.1) (cpt _ _ _ _) continuous_fst (iG y hy _ _ _ _ _ _ _))
  · simp only [CellLayout.trueData, constPressureData, Sum.elim_inl, Sum.elim_inr, mul_zero, Complex.ofReal_zero,
      add_zero]
    unfold CellLayout.extraValue
    split_ifs
    all_goals first
      | exact radial_aff0 _ _ _ _ _ (sideTest_cont _ _ _) (hV _ _) (hG _ _ _) (iV x hx _ _ _ _ _ _)
          (iV y hy _ _ _ _ _ _) (cw_mul (cpt _ _ _ _) (by fun_prop) (iG x hx _ _ _ _ _ _ _))
          (cw_mul (cpt _ _ _ _) (by fun_prop) (iG y hy _ _ _ _ _ _ _))
      | (refine height_aff0 _ _ _ _ _ _ ?_ (sideTest_cont _ _ _) (hV _ _) (hG _ _ _)
          (iV x hx _ _ _ _ _ _) (iV y hy _ _ _ _ _ _) ?_ ?_
         · exact continuous_const
         · exact cw_mul (cpt _ _ _ _) continuous_const (iG x hx _ _ _ _ _ _ _)
         · exact cw_mul (cpt _ _ _ _) continuous_const (iG y hy _ _ _ _ _ _ _))

end CellCoordinates

end CellCert

end Breakdown

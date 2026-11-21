import Breakdown.CertCell.BridgeStatements

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal

lemma cornerIntegrand_split (A B h z : ℝ) (hh : h ≠ 0) (F Fr Fz Frz : ℂ) :
    (A : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * F + (A : ℂ) * (((z - h) / (0 - h) : ℝ) : ℂ) * Fz
        + (B : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * Fr + (B : ℂ) * (((z - h) / (0 - h) : ℝ) : ℂ) * Frz
      = (A : ℂ) * (Fz * ((1 - z / h : ℝ) : ℂ) - F / (h : ℂ))
        + (B : ℂ) * (Frz * ((1 - z / h : ℝ) : ℂ) - Fr / (h : ℂ)) := by
  have hc : (h : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hh
  have hc' : (0 : ℂ) - (h : ℂ) ≠ 0 := by rw [zero_sub]; exact neg_ne_zero.mpr hc
  push_cast
  field_simp
  ring

lemma sectionTrace_integral (f fz : ℝ → ℂ) (h : ℝ) (hh : 0 < h) :
    ∫ z in Set.Icc 0 h, (fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ)) = -upperTrace f fz h := by
  unfold upperTrace
  rw [neg_neg, intervalIntegral.integral_of_le hh.le, integral_Icc_eq_integral_Ioc]

lemma sectionTrace_integrable (f fz : ℝ → ℂ) (h : ℝ)
    (hf : IntegrableOn f (Set.Icc 0 h)) (hfz : IntegrableOn fz (Set.Icc 0 h)) :
    IntegrableOn (fun z => fz z * ((1 - z / h : ℝ) : ℂ) - f z / (h : ℂ)) (Set.Icc 0 h) := by
  refine (hfz.mul_continuousOn ?_ isCompact_Icc).sub (hf.div_const _)
  fun_prop

lemma rectangle_iterated (S : Set ℝ) (hS : IsCompact S) (h : ℝ) (hh : 0 < h)
    (F Fr Fz Frz : ℝ × ℝ → ℂ) (A : ℝ) (B : ℝ → ℝ) (hB : Continuous B)
    (iF : IntegrableOn F (S ×ˢ Set.Icc 0 h)) (iFr : IntegrableOn Fr (S ×ˢ Set.Icc 0 h))
    (iFz : IntegrableOn Fz (S ×ˢ Set.Icc 0 h)) (iFrz : IntegrableOn Frz (S ×ˢ Set.Icc 0 h)) :
    ∫ p in S ×ˢ Set.Icc 0 h,
        ((A : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * F p + (A : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ) * Fz p
          + ((B p.1 : ℝ) : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * Fr p
          + ((B p.1 : ℝ) : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ) * Frz p)
      = -∫ r in S, ((A : ℂ) * upperTrace (fun z => F (r, z)) (fun z => Fz (r, z)) h
          + ((B r : ℝ) : ℂ) * upperTrace (fun z => Fr (r, z)) (fun z => Frz (r, z)) h) := by
  have hK : IsCompact (S ×ˢ Set.Icc (0 : ℝ) h) := hS.prod isCompact_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ =>
      (A : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * F p + (A : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ) * Fz p
          + ((B p.1 : ℝ) : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * Fr p
          + ((B p.1 : ℝ) : ℂ) * (((p.2 - h) / (0 - h) : ℝ) : ℂ) * Frz p) (S ×ˢ Set.Icc 0 h) := by
    refine ((IntegrableOn.continuousOn_mul ?_ iF hK).add (IntegrableOn.continuousOn_mul ?_ iFz hK)).add
      (IntegrableOn.continuousOn_mul ?_ iFr hK) |>.add (IntegrableOn.continuousOn_mul ?_ iFrz hK)
    all_goals (apply Continuous.continuousOn; fun_prop)
  have e : (volume.restrict S).prod (volume.restrict (Set.Icc (0 : ℝ) h))
      = (volume : Measure (ℝ × ℝ)).restrict (S ×ˢ Set.Icc 0 h) := by
    rw [Measure.prod_restrict, Measure.volume_eq_prod]
  have sec : ∀ G : ℝ × ℝ → ℂ, IntegrableOn G (S ×ˢ Set.Icc 0 h) →
      ∀ᵐ r ∂(volume.restrict S), IntegrableOn (fun z => G (r, z)) (Set.Icc 0 h) := by
    intro G hG
    have hG' : Integrable G ((volume.restrict S).prod (volume.restrict (Set.Icc (0 : ℝ) h))) := by
      rw [e]; exact hG
    exact hG'.prod_right_ae
  rw [Measure.volume_eq_prod, setIntegral_prod _ hint, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [sec F iF, sec Fr iFr, sec Fz iFz, sec Frz iFrz] with r a b c d
  have hpt : (fun z : ℝ =>
      (A : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * F (r, z) + (A : ℂ) * ((((r, z) : ℝ × ℝ).2 - h) / (0 - h) : ℝ) * Fz (r, z)
          + ((B (r, z).1 : ℝ) : ℂ) * (((1 / (0 - h) : ℝ)) : ℂ) * Fr (r, z)
          + ((B (r, z).1 : ℝ) : ℂ) * ((((r, z) : ℝ × ℝ).2 - h) / (0 - h) : ℝ) * Frz (r, z))
      = fun z => (A : ℂ) * (Fz (r, z) * ((1 - z / h : ℝ) : ℂ) - F (r, z) / (h : ℂ))
        + ((B r : ℝ) : ℂ) * (Frz (r, z) * ((1 - z / h : ℝ) : ℂ) - Fr (r, z) / (h : ℂ)) := by
    funext z
    exact cornerIntegrand_split A (B r) h z hh.ne' _ _ _ _
  simp only [] at hpt ⊢
  rw [hpt, integral_add ((sectionTrace_integrable _ _ h a c).const_mul _)
    ((sectionTrace_integrable _ _ h b d).const_mul _), integral_const_mul, integral_const_mul,
    sectionTrace_integral _ _ h hh, sectionTrace_integral _ _ h hh]
  ring

end Internal

theorem cornerTrace : CornerTraceHolds := by
  intro F Fr Fz Frz cr orr h hne hh iF iFr iFz iFrz
  have hmin : min (0 : ℝ) h = 0 := min_eq_left hh.le
  have hmax : max (0 : ℝ) h = h := max_eq_right hh.le
  have hsign : CellCert.CellFormula.edgeSign 0 h = -1 := by
    unfold CellCert.CellFormula.edgeSign
    rw [if_neg (not_lt.mpr hh.le)]
  have key := Internal.rectangle_iterated (Set.Icc (min cr orr) (max cr orr)) isCompact_Icc h hh
    F Fr Fz Frz (1 / (cr - orr)) (fun r => (r - orr) / (cr - orr)) (by fun_prop) iF iFr iFz iFrz
  unfold CellCert.CellFormula.cornerMoment
  rw [hmin, hmax, hsign]
  rw [key]
  ring

end Bridge

end CertCell

end Breakdown

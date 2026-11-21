import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.StAngularHeightMode
import Breakdown.FracCell.AngularHeightMode
import Breakdown.FracCell.AngularMode

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

namespace StrainFaceHeightTurn

private lemma axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

private lemma strip_turn (c o lo hi : ℝ) (hlo : 0 ≤ lo) (F dF Fa dFa Fb dFb : ℝ × ℝ → ℂ) (lam mu : ℂ)
    (t : ℝ → ℝ) (ht : Continuous t)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * F p = lam * Fa p + mu * Fb p ∧ (p.1 : ℂ) * dF p = lam * dFa p + mu * dFb p)
    (ha : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fa p
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFa p) * ((1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)))
    (hb : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fb p
        + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFb p) * ((1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o))) :
    heightStripMoment c o lo hi (fun r => r) F dF t =
      lam * heightStripMoment c o lo hi (fun _ => 1) Fa dFa t
        + mu * heightStripMoment c o lo hi (fun _ => 1) Fb dFb t := by
  unfold heightStripMoment
  have hSm : MeasurableSet (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hSc : IsCompact (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) := isCompact_Icc.prod isCompact_Icc
  have htc : ContinuousOn (fun p : ℝ × ℝ => ((t p.1 : ℝ) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) :=
    (Complex.continuous_ofReal.comp (ht.comp continuous_fst)).continuousOn
  have ia : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fa p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFa p) * ((((fun _ : ℝ => (1 : ℝ)) p.1 * t p.1 : ℝ)) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) :=
    (ha.mul_continuousOn htc hSc).congr_fun (fun p _ => by push_cast; ring) hSm
  have ib : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * Fb p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFb p) * ((((fun _ : ℝ => (1 : ℝ)) p.1 * t p.1 : ℝ)) : ℂ))
      (Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o)) :=
    (hb.mul_continuousOn htc hSc).congr_fun (fun p _ => by push_cast; ring) hSm
  have hcongr : ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o),
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
        ((((fun r : ℝ => r) p.1 * t p.1 : ℝ)) : ℂ) =
      ∫ p in Set.Icc lo hi ×ˢ Set.Icc (min c o) (max c o),
        (lam * (((((1 / (c - o) : ℝ)) : ℂ) * Fa p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFa p) *
            ((((fun _ : ℝ => (1 : ℝ)) p.1 * t p.1 : ℝ)) : ℂ))
          + mu * (((((1 / (c - o) : ℝ)) : ℂ) * Fb p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dFb p) *
            ((((fun _ : ℝ => (1 : ℝ)) p.1 * t p.1 : ℝ)) : ℂ))) := by
    refine setIntegral_congr_ae hSm ?_
    filter_upwards [hF, axis_null] with p hp hp0 hmem
    have hr : 0 < p.1 := lt_of_le_of_ne (le_trans hlo (Set.mem_prod.mp hmem).1.1) (Ne.symm hp0)
    obtain ⟨h1, h2⟩ := hp hr
    calc ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p) *
          ((((fun r : ℝ => r) p.1 * t p.1 : ℝ)) : ℂ)
        = ((((1 / (c - o) : ℝ)) : ℂ) * ((p.1 : ℂ) * F p)
            + (((p.2 - o) / (c - o) : ℝ) : ℂ) * ((p.1 : ℂ) * dF p)) * ((t p.1 : ℝ) : ℂ) := by
          push_cast
          ring
      _ = _ := by
          rw [h1, h2]
          push_cast
          ring
  rw [hcongr, integral_add (ia.const_mul lam) (ib.const_mul mu), integral_const_mul, integral_const_mul]
  ring

end StrainFaceHeightTurn

open StrainFaceHeightTurn

theorem heightTurn_of (hI : SideStripIntegrableStatement) (hA : AngularModeStatement)
    (hS : AngularHeightModeStatement) : HeightTurnStatement := by
  intro k N c K S B L hL x hx n e a t he ht
  have hsec : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := hL.order_eq ▸ hx.1
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have htc : Continuous t := by
    obtain ⟨q, hq⟩ := ht
    have e1 : t = fun u => q.eval u := funext hq
    rw [e1]
    exact q.continuous
  have hA' := hA L.order x.1 x.2.1 x.2.2.1 hsec n
  have hS' := hS L.order x.1 x.2.1 x.2.2.1 hsec n
  have hI' : ∀ b : Fin 3, _ := fun b => (hI c K S B L hL x hx n e b (fun h => absurd h (by omega))).2 he
  have hlo : 0 ≤ L.box.r₁ := hK.r_order.1
  obtain ⟨co, oo, hface, hside, hint⟩ : ∃ co oo : ℝ,
      (∀ F dF : ℝ × ℝ → ℂ, heightFaceMoment L.box F dF (CellLayout.sideHeightIndex e) t =
        heightStripMoment co oo L.box.r₁ L.box.r₂ (fun r => r) F dF t) ∧
      (∀ b : Fin 3, L.sideVelocityValue n x e b t =
        heightStripMoment co oo L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x b) (L.gradModeOf n x b 2) t) ∧
      (∀ b : Fin 3, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (co - oo) : ℝ)) : ℂ) * L.velMode n x b p
          + (((p.2 - oo) / (co - oo) : ℝ) : ℂ) * L.gradModeOf n x b 2 p) * ((1 : ℝ) : ℂ))
        (Set.Icc L.box.r₁ L.box.r₂ ×ˢ Set.Icc (min co oo) (max co oo))) := by
    have he4 := e.isLt
    have hcase : e = 2 ∨ e = 3 := by
      rcases e with ⟨e, hle⟩
      simp only [Fin.ext_iff, Fin.val_two]
      simp only at he
      omega
    rcases hcase with rfl | rfl
    · have hlev : L.sideLevel 2 = L.box.z₁ := by simp [CellLayout.sideLevel]
      have hoth : L.sideOther 2 = L.box.z₂ := by
        simp only [CellLayout.sideOther, hlev]
        simp
      refine ⟨L.box.z₁, L.box.z₂, fun F dF => ?_, fun b => ?_, fun b => ?_⟩
      · simp [heightFaceMoment, CellLayout.sideHeightIndex]
      · simp [CellLayout.sideVelocityValue, CellLayout.sideHeightIndex]
      · have h := hI' b
        rw [hlev, hoth] at h
        exact h.1
    · have hlev : L.sideLevel 3 = L.box.z₂ := by simp [CellLayout.sideLevel]
      have hoth : L.sideOther 3 = L.box.z₁ := by
        simp only [CellLayout.sideOther, hlev]
        simp
      refine ⟨L.box.z₂, L.box.z₁, fun F dF => ?_, fun b => ?_, fun b => ?_⟩
      · simp [heightFaceMoment, CellLayout.sideHeightIndex]
      · simp [CellLayout.sideVelocityValue, CellLayout.sideHeightIndex]
      · have h := hI' b
        rw [hlev, hoth] at h
        exact h.1
  rw [hface]
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · simp only [CellLayout.turnValue, if_true]
    rw [hside, hside, sub_eq_add_neg, neg_eq_neg_one_mul]
    refine strip_turn co oo L.box.r₁ L.box.r₂ hlo _ _ _ _ _ _ _ _ t htc ?_ (hint 0) (hint 1)
    filter_upwards [hA', hS'] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).1, (hq hr).1]
    constructor <;> ring
  · simp only [CellLayout.turnValue, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
    rw [hside, hside, ← one_mul (heightStripMoment co oo _ _ (fun _ => 1) (L.velMode n x 0) _ t)]
    refine strip_turn co oo L.box.r₁ L.box.r₂ hlo _ _ _ _ _ _ _ _ t htc ?_ (hint 1) (hint 0)
    filter_upwards [hA', hS'] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).2.1, (hq hr).2.1]
    constructor <;> ring
  · simp only [CellLayout.turnValue, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
    rw [hside, ← add_zero (_ * heightStripMoment co oo _ _ (fun _ => 1) (L.velMode n x 2) _ t),
      ← zero_mul (heightStripMoment co oo L.box.r₁ L.box.r₂ (fun _ => 1) (L.velMode n x 0) (L.gradModeOf n x 0 2) t)]
    refine strip_turn co oo L.box.r₁ L.box.r₂ hlo _ _ _ _ _ _ _ _ t htc ?_ (hint 2) (hint 0)
    filter_upwards [hA', hS'] with p hp hq hr
    simp only [CellLayout.velMode, CellLayout.gradModeOf, CellLayout.secondModeOf]
    rw [(hp hr).2.2, (hq hr).2.2]
    constructor <;> ring

theorem heightTurn_of_circle (hI : SideStripIntegrableStatement) (hC : CellEnergy.CircleWeakStatement) :
    HeightTurnStatement :=
  heightTurn_of hI (angularMode hC) (angularHeightMode_of_circle hC)

end CellFormula

end CellCert

end Breakdown

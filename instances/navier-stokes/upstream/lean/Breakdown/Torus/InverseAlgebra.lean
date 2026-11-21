import Breakdown.Torus.StatementsSeqOps

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Periodic

namespace InverseAlgebra.Internal

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem isUnit_one_sub_clm (T : F →L[ℝ] F) (hT : ‖T‖ < 1) : IsUnit (1 - T) :=
  isUnit_one_sub_of_norm_lt_one hT

theorem norm_inverse_one_sub_le (T : F →L[ℝ] F) (q : ℝ) (hT : ‖T‖ ≤ q) (hq : q < 1) :
    ‖Ring.inverse (1 - T)‖ ≤ (1 - q)⁻¹ := by
  have hT1 : ‖T‖ < 1 := hT.trans_lt hq
  rw [← geom_series_eq_inverse T hT1]
  refine (tsum_geometric_le_of_norm_lt_one T hT1).trans ?_
  have h1 : ‖(1 : F →L[ℝ] F)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have h2 : (1 - ‖T‖)⁻¹ ≤ (1 - q)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  linarith

theorem inverse_one_sub_apply_sub (T : F →L[ℝ] F) (hT : ‖T‖ < 1) (x : F) :
    Ring.inverse (1 - T) (x - T x) = x := by
  have h := congrArg (fun f : F →L[ℝ] F => f x)
    (Ring.inverse_mul_cancel (1 - T) (isUnit_one_sub_clm T hT))
  simpa using h

theorem sub_apply_inverse_one_sub (T : F →L[ℝ] F) (hT : ‖T‖ < 1) (y : F) :
    Ring.inverse (1 - T) y - T (Ring.inverse (1 - T) y) = y := by
  have h := congrArg (fun f : F →L[ℝ] F => f y)
    (Ring.mul_inverse_cancel (1 - T) (isUnit_one_sub_clm T hT))
  simpa using h

end InverseAlgebra.Internal

open InverseAlgebra.Internal

theorem rightInversePerturb : RightInversePerturb := by
  intro E F _ _ _ _ _ _ A A' R K hAR hR hK
  have hK0 : 0 ≤ K := (norm_nonneg _).trans hR
  set Q : F →L[ℝ] F := (A' - A).comp R with hQdef
  have hQ : ‖-Q‖ ≤ 1 / 2 := by
    rw [norm_neg]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left hR (norm_nonneg _)).trans hK)
  have hQ1 : ‖-Q‖ < 1 := hQ.trans_lt (by norm_num)
  set U : F →L[ℝ] F := Ring.inverse (1 - -Q) with hUdef
  have hU : ‖U‖ ≤ 2 := by
    calc ‖U‖ ≤ (1 - 1 / 2)⁻¹ := norm_inverse_one_sub_le (-Q) (1 / 2) hQ (by norm_num)
      _ = 2 := by norm_num
  refine ⟨R.comp U, ?_, ?_⟩
  · ext y
    have h1 := sub_apply_inverse_one_sub (-Q) hQ1 y
    have h2 : A (R (U y)) = U y := by
      simpa using DFunLike.congr_fun hAR (U y)
    rw [← hUdef] at h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]
    have h3 : A' (R (U y)) = A (R (U y)) + Q (U y) := by
      simp [hQdef]
    rw [h3, h2]
    simpa [sub_eq_add_neg] using h1
  · calc ‖R.comp U‖ ≤ ‖R‖ * ‖U‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 2 := mul_le_mul hR hU (norm_nonneg _) hK0
      _ = 2 * K := by ring

theorem shellInverseTransfer (hP : RightInversePerturb) : ShellInverseTransfer := by
  intro E Y Yt Z _ _ _ _ _ _ _ _ _ _ _ _ S G B Rr St Gt Bt Rt Rf q Kf δ hq0 hq1 hS hSt hRf hKf
    hδB hδG hδ
  have hS1 : ‖S‖ < 1 := hS.trans_lt hq1
  have hSt1 : ‖St‖ < 1 := hSt.trans_lt hq1
  have hKf0 : 0 ≤ Kf := (norm_nonneg _).trans hKf
  have hδ0 : 0 ≤ δ := (norm_nonneg _).trans hδB
  set Gi : Y →L[ℝ] Y := Ring.inverse (1 - S) with hGi
  set Gti : Yt →L[ℝ] Yt := Ring.inverse (1 - St) with hGti
  set c : ℝ := (1 - q)⁻¹ with hc
  have hc0 : 0 < 1 - q := by linarith
  have hc1 : 1 ≤ c := (one_le_inv₀ hc0).2 (by linarith)
  have hGtin : ‖Gti‖ ≤ c := norm_inverse_one_sub_le St q hSt hq1
  set Cst : ℝ := 1 + Kf * ‖B‖ * (1 + ‖Rr‖) with hCst
  have hCst1 : 1 ≤ Cst := by
    have : 0 ≤ Kf * ‖B‖ * (1 + ‖Rr‖) := by positivity
    linarith
  set Sop : E × Z →L[ℝ] Z := ContinuousLinearMap.snd ℝ E Z -
    (Rr.comp (Gi.comp B)).comp (ContinuousLinearMap.snd ℝ E Z) -
    (Rr.comp (Gi.comp G)).comp (ContinuousLinearMap.fst ℝ E Z) with hSop
  set Stop : E × Z →L[ℝ] Z := ContinuousLinearMap.snd ℝ E Z -
    (Rt.comp (Gti.comp Bt)).comp (ContinuousLinearMap.snd ℝ E Z) -
    (Rt.comp (Gti.comp Gt)).comp (ContinuousLinearMap.fst ℝ E Z) with hStop
  set RS : Z →L[ℝ] E × Z := ((ContinuousLinearMap.fst ℝ E Y).comp (Rf.comp B)).prod
    (ContinuousLinearMap.id ℝ Z + Rr.comp ((ContinuousLinearMap.snd ℝ E Y).comp (Rf.comp B)))
    with hRS
  have hRSinv : Sop.comp RS = ContinuousLinearMap.id ℝ Z := by
    ext ζ
    have hp := DFunLike.congr_fun hRf (B ζ)
    simp only [chainOp, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.id_apply] at hp
    set p := Rf (B ζ) with hpdef
    have hv : p.2 - S p.2 = G p.1 + B (ζ + Rr p.2) := by
      rw [map_add, ← hp]; abel
    have hv2 : p.2 = Gi (G p.1 + B (ζ + Rr p.2)) := by
      rw [← hv, hGi, inverse_one_sub_apply_sub S hS1]
    have hRv : Rr p.2 = Rr (Gi (G p.1)) + Rr (Gi (B ζ)) + Rr (Gi (B (Rr p.2))) := by
      conv_lhs => rw [hv2]
      simp only [map_add]
      abel
    simp only [hSop, hRS, ContinuousLinearMap.comp_apply, sub_apply,
      add_apply, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.id_apply, ← hpdef, map_add]
    rw [← sub_eq_zero]
    rw [← sub_eq_zero] at hRv
    rw [← hRv]
    abel
  have hRSn : ‖RS‖ ≤ Cst := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun ζ => ?_)
    have hp : ‖Rf (B ζ)‖ ≤ Kf * ‖B‖ * ‖ζ‖ := by
      calc ‖Rf (B ζ)‖ ≤ ‖Rf‖ * (‖B‖ * ‖ζ‖) :=
            (Rf.le_opNorm _).trans (mul_le_mul_of_nonneg_left (B.le_opNorm _) (norm_nonneg _))
        _ ≤ Kf * (‖B‖ * ‖ζ‖) := by gcongr
        _ = Kf * ‖B‖ * ‖ζ‖ := by ring
    have hp1 := (norm_fst_le (Rf (B ζ))).trans hp
    have hp2 := (norm_snd_le (Rf (B ζ))).trans hp
    have hX : 0 ≤ Kf * ‖B‖ * ‖ζ‖ := by positivity
    have hR2 : ‖Rr (Rf (B ζ)).2‖ ≤ ‖Rr‖ * (Kf * ‖B‖ * ‖ζ‖) :=
      (Rr.le_opNorm _).trans (mul_le_mul_of_nonneg_left hp2 (norm_nonneg _))
    have hRX : 0 ≤ ‖Rr‖ * (Kf * ‖B‖ * ‖ζ‖) := by positivity
    have hζ := norm_nonneg ζ
    rw [norm_prod_le_iff]
    constructor
    · simp only [hRS, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst']
      nlinarith
    · simp only [hRS, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.coe_snd']
      have := norm_add_le ζ (Rr (Rf (B ζ)).2)
      nlinarith
  have hdiff : ‖Stop - Sop‖ ≤ 2 * δ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (by linarith) (fun x => ?_)
    have hx : (Stop - Sop) x =
        -((Rt.comp (Gti.comp Bt) - Rr.comp (Gi.comp B)) x.2 +
          (Rt.comp (Gti.comp Gt) - Rr.comp (Gi.comp G)) x.1) := by
      simp only [hStop, hSop, sub_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
      abel
    rw [hx, norm_neg]
    have h1 := ((Rt.comp (Gti.comp Bt) - Rr.comp (Gi.comp B)).le_opNorm x.2).trans
      (mul_le_mul hδB (norm_snd_le x) (norm_nonneg _) hδ0)
    have h2 := ((Rt.comp (Gti.comp Gt) - Rr.comp (Gi.comp G)).le_opNorm x.1).trans
      (mul_le_mul hδG (norm_fst_le x) (norm_nonneg _) hδ0)
    linarith [norm_add_le ((Rt.comp (Gti.comp Bt) - Rr.comp (Gi.comp B)) x.2)
      ((Rt.comp (Gti.comp Gt) - Rr.comp (Gi.comp G)) x.1)]
  have hK : ‖Stop - Sop‖ * Cst ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right hdiff (by linarith : (0 : ℝ) ≤ Cst)
    linarith
  obtain ⟨RSt, hRSt, hRStn⟩ := hP (E × Z) Z Sop Stop RS Cst hRSinv hRSn hK
  set W : Yt →L[ℝ] E × Z := RSt.comp (Rt.comp Gti) with hW
  set Rp : Yt →L[ℝ] E × Yt := ((ContinuousLinearMap.fst ℝ E Z).comp W).prod
    (Gti.comp (ContinuousLinearMap.id ℝ Yt + Bt.comp ((ContinuousLinearMap.snd ℝ E Z).comp W) +
      Gt.comp ((ContinuousLinearMap.fst ℝ E Z).comp W))) with hRp
  set a : ℝ := 2 * Cst * ‖Rt‖ * c with ha
  have ha0 : 0 ≤ a := by
    have : 0 ≤ Cst := by linarith
    have : 0 ≤ c := by linarith
    positivity
  refine ⟨Rp, ?_, ?_⟩
  · ext h
    have hw := DFunLike.congr_fun hRSt (Rt (Gti h))
    simp only [hStop, ContinuousLinearMap.comp_apply, sub_apply,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.id_apply] at hw
    have hWh : W h = RSt (Rt (Gti h)) := rfl
    set w := RSt (Rt (Gti h)) with hwdef
    set y : Yt := h + Bt w.2 + Gt w.1 with hy
    have key : Gti y - St (Gti y) = y := by
      rw [hGti]; exact sub_apply_inverse_one_sub St hSt1 y
    have hz : Rt (Gti y) = w.2 := by
      rw [hy, map_add, map_add, map_add, map_add]
      rw [← sub_eq_zero, ← neg_eq_zero]
      rw [← sub_eq_zero] at hw
      rw [← hw]
      abel
    have hRph : Rp h = (w.1, Gti y) := by
      simp only [hRp, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hWh, hy]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, hRph, chainOp,
      sub_apply, ContinuousLinearMap.coe_fst',
      ContinuousLinearMap.coe_snd']
    rw [key, hz, hy]
    abel
  · have hM0 : 0 ≤ c * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) :=
      mul_nonneg (by linarith) (add_nonneg zero_le_one (mul_nonneg (by positivity) ha0))
    have htar : (1 - q)⁻¹ * (1 + (‖Bt‖ + ‖Gt‖ + 1) * 2 * (1 + Kf * ‖B‖ * (1 + ‖Rr‖)) * ‖Rt‖ *
        (1 - q)⁻¹) = c * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) := by
      rw [← hc, ← hCst, ha]; ring
    rw [htar]
    refine ContinuousLinearMap.opNorm_le_bound _ hM0 (fun h => ?_)
    have hWh : W h = RSt (Rt (Gti h)) := rfl
    set w := RSt (Rt (Gti h)) with hwdef
    set y : Yt := h + Bt w.2 + Gt w.1 with hy
    have hRph : Rp h = (w.1, Gti y) := by
      simp only [hRp, ContinuousLinearMap.prod_apply, ContinuousLinearMap.comp_apply,
        add_apply, ContinuousLinearMap.id_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', hWh, hy]
    have hh := norm_nonneg h
    have hwn : ‖w‖ ≤ a * ‖h‖ := by
      calc ‖w‖ ≤ ‖RSt‖ * (‖Rt‖ * (‖Gti‖ * ‖h‖)) :=
            (RSt.le_opNorm _).trans (mul_le_mul_of_nonneg_left ((Rt.le_opNorm _).trans
              (mul_le_mul_of_nonneg_left (Gti.le_opNorm _) (norm_nonneg _))) (norm_nonneg _))
        _ ≤ (2 * Cst) * (‖Rt‖ * (c * ‖h‖)) := by gcongr
        _ = a * ‖h‖ := by rw [ha]; ring
    have hw1 := (norm_fst_le w).trans hwn
    have hw2 := (norm_snd_le w).trans hwn
    have hyn : ‖y‖ ≤ ‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖) := by
      calc ‖y‖ ≤ ‖h‖ + ‖Bt w.2‖ + ‖Gt w.1‖ := norm_add₃_le
        _ ≤ ‖h‖ + ‖Bt‖ * ‖w.2‖ + ‖Gt‖ * ‖w.1‖ := by
            gcongr
            · exact Bt.le_opNorm _
            · exact Gt.le_opNorm _
        _ ≤ ‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖) := by gcongr
    have hvn : ‖Gti y‖ ≤ c * (‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖)) :=
      (Gti.le_opNorm _).trans (mul_le_mul hGtin hyn (norm_nonneg _) (by linarith))
    rw [hRph, norm_prod_le_iff]
    have hBt := norm_nonneg Bt
    have hGt := norm_nonneg Gt
    have hah : 0 ≤ a * ‖h‖ := mul_nonneg ha0 hh
    constructor
    · have h1 : a ≤ c * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) := by
        have hpos : (0 : ℝ) ≤ 1 + (‖Bt‖ + ‖Gt‖ + 1) * a :=
          add_nonneg zero_le_one (mul_nonneg (by positivity) ha0)
        have e : c * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) =
            (c - 1) * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) + (1 + (‖Bt‖ + ‖Gt‖) * a) + a := by ring
        rw [e]
        have := mul_nonneg (sub_nonneg.2 hc1) hpos
        have := mul_nonneg (add_nonneg hBt hGt) ha0
        linarith
      exact hw1.trans (mul_le_mul_of_nonneg_right h1 hh)
    · refine hvn.trans ?_
      have h2 : ‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖) ≤ (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) * ‖h‖ := by
        have e2 : (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) * ‖h‖ =
            (‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖)) + a * ‖h‖ := by ring
        rw [e2]
        linarith
      calc c * (‖h‖ + ‖Bt‖ * (a * ‖h‖) + ‖Gt‖ * (a * ‖h‖))
          ≤ c * ((1 + (‖Bt‖ + ‖Gt‖ + 1) * a) * ‖h‖) :=
            mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = c * (1 + (‖Bt‖ + ‖Gt‖ + 1) * a) * ‖h‖ := by ring

end Breakdown.Periodic

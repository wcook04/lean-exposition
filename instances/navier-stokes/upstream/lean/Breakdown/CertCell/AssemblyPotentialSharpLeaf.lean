import Breakdown.CertCell.AssemblyPotentialSharpPoint
import Breakdown.CertCell.AssemblyPotentialParts

open scoped ComplexConjugate
open Filter Topology Matrix MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open Bridge Bridge.Internal.MeanStretch Coercive.StretchInternal Coercive.Internal.ModeRotation CellCalculus
  CellCert.CellAnalysis

theorem permSign_eq (i j l : Fin 3) : (CellCert.permSign i j l : ℂ) = (alternatingSymbol i j l : ℂ) := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> simp [CellCert.permSign, alternatingSymbol] <;> norm_num

theorem curlComp_eq (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) : curlComp s i = curlOfGrad (fun ab => s ab.1 ab.2) i := by
  unfold curlComp curlOfGrad
  simp only [permSign_eq]

theorem curlSq_strainOfVec (U : Fin 12 → ℂ) : curlSq (strainOfVec U) = cnormSq (curlOfGrad (gradOf U)) := by
  unfold curlSq cnormSq
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [curlComp_eq]
  rfl

theorem sumSq_strainOfVec (U : Fin 12 → ℂ) : sumSq (strainOfVec U) = cnormSq (gradOf U) := by
  unfold sumSq cnormSq
  rw [Fintype.sum_prod_type]
  rfl

theorem vecSq_velOf (U : Fin 12 → ℂ) : vecSq (velOf U) = cnormSq (velOf U) := rfl

theorem supLoss_eq (lam g0 gw ℓ : ℝ) (U : Fin 12 → ℂ) :
    supremumLoss lam g0 gw ℓ (strainOfVec U) (velOf U) = pointLoss lam g0 gw ℓ U := by
  unfold supremumLoss pointLoss CellCert.Exterior.traceFreeConst
  rw [curlSq_strainOfVec, sumSq_strainOfVec, vecSq_velOf]

theorem pairVec_strainOfVec (U : Fin 12 → ℂ) : pairVec (strainOfVec U) (velOf U) = U := by
  funext i
  fin_cases i <;> rfl

theorem gradOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (a b : Fin 3) : gradOf (pairVec s v) (a, b) = s a b := by
  fin_cases a <;> fin_cases b <;> rfl

theorem velOf_pairVec (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (a : Fin 3) : velOf (pairVec s v) a = v a := by
  fin_cases a <;> rfl

theorem quad_withStretch_diff (a : TailBand.PointCoef) (κ s mg wg len cc gc vc x2 xc x1 xo x0 : ℝ) :
    a.quad x2 xc x1 xo x0 - (a.withStretch κ s mg wg len cc gc vc).quad x2 xc x1 xo x0
      = (s + cc) * xo ^ 2 + (κ / 2 * wg * len + gc) * x1 ^ 2 + (κ / 2 * wg / len + vc) * x0 ^ 2 + κ * mg * x1 * x0 := by
  simp only [TailBand.PointCoef.quad, TailBand.PointCoef.withStretch]
  ring

theorem leaf_point (K : CellBox) (res : Finset (ℤ × ℤ)) (coef : ℤ × ℤ → ℝ × ℝ → ModeCoefficients) (ch : ModeCharges)
    (T : LeafValues) (hT : IsLeafValues K res coef ch T) (ι : ℤ × ℤ) (hι : ι ∈ res) (p : ℝ × ℝ) (hp : p ∈ K.rect)
    (hp1 : p.1 ≠ 0) (hlw : 0 < K.lineWeight p.1) (U : Fin 12 → ℂ) :
    p.1 * pointLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) (ch.length ι p) U
        + p.1 * T.boxPairPenalty ι (strainOfVec U) (velOf U) - K.lineWeight p.1 * T.absorbValue ι (strainOfVec U) (velOf U)
      ≤ p.1 * (sesq12 (T.localMatrix ι p) U U).re := by
  have h := hT.pointwise ι hι p hp hp1 (strainOfVec U) (velOf U)
  rw [pairVec_strainOfVec, supLoss_eq] at h
  have e : sesqValue (T.localMatrix ι p) U = (sesq12 (T.localMatrix ι p) U U).re := rfl
  rw [e] at h
  unfold CellScalars.rHat at h
  have h2 := mul_le_mul_of_nonneg_left h hlw.le
  rw [mul_zero] at h2
  have e2 : K.lineWeight p.1 * (p.1 / K.lineWeight p.1 * ((sesq12 (T.localMatrix ι p) U U).re
      - pointLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) (ch.length ι p) U
      - T.boxPairPenalty ι (strainOfVec U) (velOf U)) + T.absorbValue ι (strainOfVec U) (velOf U))
      = p.1 * ((sesq12 (T.localMatrix ι p) U U).re
      - pointLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) (ch.length ι p) U
      - T.boxPairPenalty ι (strainOfVec U) (velOf U)) + K.lineWeight p.1 * T.absorbValue ι (strainOfVec U) (velOf U) := by
    field_simp
  rw [e2] at h2
  nlinarith [h2]

theorem gradOf_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    gradOf (bandProfile D ι v G p) = labelGrad D.azimuthOrder ι G p := by
  funext ab
  unfold bandProfile
  rw [gradOf_pairVec]
  rfl

theorem velOf_bandProfile {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    velOf (bandProfile D ι v G p) = labelVel D.azimuthOrder ι v p := by
  funext a
  unfold bandProfile
  rw [velOf_pairVec]
  rfl

theorem offmode_point {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ)
    (hκ : Real.sqrt (7 / 2) ≤ (R.entryCharges K ι).stretchConst) (hg0 : 0 ≤ (D.charges (some K)).product ι p)
    (hgw : 0 ≤ (D.charges (some K)).gradient ι p) (hℓ : 0 < (D.charges (some K)).length ι p) (hp1 : 0 ≤ p.1) :
    pointLoss ((D.charges (some K)).curl ι p) ((D.charges (some K)).product ι p) ((D.charges (some K)).gradient ι p)
        ((D.charges (some K)).length ι p) (bandProfile D ι v G p) * p.1
      ≤ (D.labelDensity q v G H ι p
        - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
            (R.entryCharges K ι) D.azimuthOrder ι v G H p
        - extraChargeDensity D R K ι v G p) * p.1 := by
  refine mul_le_mul_of_nonneg_right ?_ hp1
  unfold CellLayerData.labelDensity
  rw [TailBand.modeTerm_eq_labelQuad]
  unfold TailBand.offModeDensity TailBand.labelQuad
  rw [quad_withStretch_diff]
  unfold extraChargeDensity modeCurlSq modeStrainSq modeVelSq pointLoss
  rw [gradOf_bandProfile, velOf_bandProfile]
  set ch := D.charges (some K)
  set ec := R.entryCharges K ι
  have hs : ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 = cnormSq (labelGrad D.azimuthOrder ι G p) := by
    unfold cnormSq
    rw [Fintype.sum_prod_type]
    rfl
  have hc : ∑ i : Fin 3, ‖curlComp (gradArray D.azimuthOrder ι G p) i‖ ^ 2
      = cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)) := by
    unfold cnormSq
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [curlComp_eq]
    rfl
  have hv : ∑ a : Fin 3, ‖velAt D.azimuthOrder ι v a p‖ ^ 2 = cnormSq (labelVel D.azimuthOrder ι v p) := rfl
  rw [hs, hc, hv]
  have q1 := Real.sq_sqrt (cnormSq_nonneg' (labelGrad D.azimuthOrder ι G p))
  have qo := Real.sq_sqrt (cnormSq_nonneg' (curlOfGrad (labelGrad D.azimuthOrder ι G p)))
  have q0 := Real.sq_sqrt (cnormSq_nonneg' (labelVel D.azimuthOrder ι v p))
  set x1 := Real.sqrt (cnormSq (labelGrad D.azimuthOrder ι G p))
  set xo := Real.sqrt (cnormSq (curlOfGrad (labelGrad D.azimuthOrder ι G p)))
  set x0 := Real.sqrt (cnormSq (labelVel D.azimuthOrder ι v p))
  rw [← q1, ← qo, ← q0]
  have hx1 : 0 ≤ x1 := Real.sqrt_nonneg _
  have hx0 : 0 ≤ x0 := Real.sqrt_nonneg _
  have hd : 0 ≤ ec.stretchConst - Real.sqrt (7 / 2) := by linarith
  have hA : 0 ≤ ch.product ι p * x1 * x0 + (1 / 2) * ch.gradient ι p * (ch.length ι p * x1 ^ 2 + x0 ^ 2 / ch.length ι p) := by
    positivity
  have key := mul_nonneg hd hA
  have hl0 : ch.length ι p ≠ 0 := hℓ.ne'
  have e : ((ch.curl ι p + ec.curlCharge p) * xo ^ 2
        + (ec.stretchConst / 2 * ch.gradient ι p * ch.length ι p + ec.gradCharge p) * x1 ^ 2
        + (ec.stretchConst / 2 * ch.gradient ι p / ch.length ι p + ec.velCharge p) * x0 ^ 2
        + ec.stretchConst * ch.product ι p * x1 * x0
        - (ec.curlCharge p * xo ^ 2 + ec.gradCharge p * x1 ^ 2 + ec.velCharge p * x0 ^ 2))
      - (ch.curl ι p * xo ^ 2 + Real.sqrt (7 / 2) * ch.product ι p * x1 * x0
        + 1 / 2 * Real.sqrt (7 / 2) * ch.gradient ι p * (ch.length ι p * x1 ^ 2 + x0 ^ 2 / ch.length ι p))
      = (ec.stretchConst - Real.sqrt (7 / 2))
        * (ch.product ι p * x1 * x0 + (1 / 2) * ch.gradient ι p * (ch.length ι p * x1 ^ 2 + x0 ^ 2 / ch.length ι p)) := by
    field_simp
    ring
  linarith [key, e]

theorem star_velOf_single (i : Fin 12) : star (velOf (Pi.single i (1 : ℂ))) = velOf (Pi.single i (1 : ℂ)) := by
  funext a
  simp only [Pi.star_apply, velOf, Pi.single_apply]
  split_ifs <;> simp

theorem star_gradOf_single (i : Fin 12) : star (gradOf (Pi.single i (1 : ℂ))) = gradOf (Pi.single i (1 : ℂ)) := by
  funext ab
  simp only [Pi.star_apply, gradOf, Pi.single_apply]
  split_ifs <;> simp

theorem trueCoupling_eq {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (α : ℤ × ℤ) (p : ℝ × ℝ) :
    trueCoupling D α p = tripleMatrix (labelGrad D.azimuthOrder α (gradField D.given) p)
      (labelHess D.azimuthOrder α D.givenHess p) := by
  ext i j
  unfold trueCoupling tripleMatrix modelTriple
  rw [star_velOf_single, star_gradOf_single]
  rfl

theorem pointLoss_abs_le (lam g0 gw ℓ C : ℝ) (hℓ : 0 < ℓ) (hlam : |lam| ≤ C) (hg0 : 0 ≤ g0) (hg0C : g0 ≤ C)
    (hgw : 0 ≤ gw) (hgwC : gw ≤ C) (U : Fin 12 → ℂ) :
    |pointLoss lam g0 gw ℓ U| ≤ (C * (2 * (∑ i, ∑ j, ‖curlPairMatrix i j‖))
      + Real.sqrt (7 / 2) * C * ((1 / 2) * (2 * (∑ i, ∑ j, ‖gradDiag i j‖) + 2 * (∑ i, ∑ j, ‖velDiag i j‖)))
      + (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * (2 * (∑ i, ∑ j, ‖gradDiag i j‖)) + 2 * (∑ i, ∑ j, ‖velDiag i j‖) / ℓ))
      * cnormSq U := by
  set c1 := 2 * (∑ i, ∑ j, ‖curlPairMatrix i j‖)
  set c2 := 2 * (∑ i, ∑ j, ‖gradDiag i j‖)
  set c3 := 2 * (∑ i, ∑ j, ‖velDiag i j‖)
  have hcu := curl_le U
  have hg := grad_le U
  have hv := vel_le U
  have hX0 := cnormSq_nonneg' U
  have hcn := cnormSq_nonneg' (curlOfGrad (gradOf U))
  have hgn := cnormSq_nonneg' (gradOf U)
  have hvn := cnormSq_nonneg' (velOf U)
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hlam
  have hsq7 : 0 ≤ Real.sqrt (7 / 2) := Real.sqrt_nonneg _
  unfold pointLoss
  have t1 : |lam * cnormSq (curlOfGrad (gradOf U))| ≤ C * c1 * cnormSq U := by
    rw [abs_mul, abs_of_nonneg hcn]
    calc |lam| * cnormSq (curlOfGrad (gradOf U)) ≤ C * (c1 * cnormSq U) := mul_le_mul hlam hcu hcn hC0
      _ = C * c1 * cnormSq U := by ring
  have t2n : 0 ≤ Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U)) := by
    positivity
  have t2 : Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))
      ≤ Real.sqrt (7 / 2) * C * ((1 / 2) * (c2 + c3)) * cnormSq U := by
    have hs := sqrt_mul_le_split (cnormSq (velOf U)) (cnormSq (gradOf U)) 1 hvn hgn one_pos
    have hsq : Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U)) ≤ (1 / 2) * (c2 + c3) * cnormSq U := by
      rw [mul_comm]
      refine hs.trans ?_
      simp only [one_mul, div_one]
      nlinarith
    have h1 : Real.sqrt (7 / 2) * g0 ≤ Real.sqrt (7 / 2) * C := mul_le_mul_of_nonneg_left hg0C hsq7
    calc Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))
        = (Real.sqrt (7 / 2) * g0) * (Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))) := by ring
      _ ≤ (Real.sqrt (7 / 2) * C) * ((1 / 2) * (c2 + c3) * cnormSq U) :=
          mul_le_mul h1 hsq (by positivity) (by positivity)
      _ = _ := by ring
  have t3n : 0 ≤ (1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ) := by positivity
  have t3 : (1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)
      ≤ (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * c2 + c3 / ℓ) * cnormSq U := by
    have i1 : ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ ≤ (ℓ * c2 + c3 / ℓ) * cnormSq U := by
      have := mul_le_mul_of_nonneg_left hg hℓ.le
      have := div_le_div_of_nonneg_right hv hℓ.le
      have e : (ℓ * c2 + c3 / ℓ) * cnormSq U = ℓ * (c2 * cnormSq U) + c3 * cnormSq U / ℓ := by ring
      rw [e]; linarith
    have i2 : (1 / 2) * Real.sqrt (7 / 2) * gw ≤ (1 / 2) * Real.sqrt (7 / 2) * C :=
      mul_le_mul_of_nonneg_left hgwC (by positivity)
    calc (1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)
        ≤ (1 / 2) * Real.sqrt (7 / 2) * C * ((ℓ * c2 + c3 / ℓ) * cnormSq U) :=
          mul_le_mul i2 i1 (by positivity) (by positivity)
      _ = _ := by ring
  calc |lam * cnormSq (curlOfGrad (gradOf U))
        + Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))
        + (1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)|
      ≤ |lam * cnormSq (curlOfGrad (gradOf U))|
        + |Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))|
        + |(1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)| := by
        have a1 := abs_add_le (lam * cnormSq (curlOfGrad (gradOf U))
          + Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U)))
          ((1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ))
        have a2 := abs_add_le (lam * cnormSq (curlOfGrad (gradOf U)))
          (Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U)))
        linarith
    _ ≤ C * c1 * cnormSq U + Real.sqrt (7 / 2) * C * ((1 / 2) * (c2 + c3)) * cnormSq U
        + (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * c2 + c3 / ℓ) * cnormSq U := by
        rw [abs_of_nonneg t2n, abs_of_nonneg t3n]; linarith
    _ = _ := by ring

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown

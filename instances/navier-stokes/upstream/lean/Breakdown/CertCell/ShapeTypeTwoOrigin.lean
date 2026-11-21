import Breakdown.CertCell.ShapeTypeTwoOriginSplit

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline TensorMesh cellCount cellIndex atFirst atSecond tDeriv xDeriv weightPoly
  radialScale heightDeriv heightRatio qOf radialVec polarVecQ azimVecQ)

namespace Internal

namespace TypeTwoNear

def linS (v : Space) (i : Fin 3) : ℝ := ![v 0, v 1, -2 * v 2] i

def radC (v : Space) (i : Fin 3) : ℝ := v i / ‖v‖

def polC (v : Space) (i : Fin 3) : ℝ :=
  ![v 2 / ‖v‖ * v 0 / ‖v‖, v 2 / ‖v‖ * v 1 / ‖v‖, -(1 - (v 2 / ‖v‖) ^ 2)] i

def azC (v : Space) (i : Fin 3) : ℝ := ![-(v 1) / ‖v‖, v 0 / ‖v‖, 0] i

def scaledRem (P : ShapeParams) (A : KeyAmp) (j : ℤ) (gq : Polynomial ℝ) (S1 G1 : Spline) (q : ℝ × Space) :
    Fin 3 → ℂ := fun i =>
  A.axisCoef * ((‖q.2‖ * linS q.2 i / (P.chartLength * (q.1 * ‖q.2‖ + P.chartLength)) : ℝ) : ℂ) +
    ((‖q.2‖ ^ 2 / (q.1 * ‖q.2‖ + P.chartLength) ^ 2 : ℝ) : ℂ) *
      (remComp P A j gq S1 G1 (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength)) (q.2 2 / ‖q.2‖) 0 * (radC q.2 i : ℂ) +
        remComp P A j gq S1 G1 (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength)) (q.2 2 / ‖q.2‖) 1 * (polC q.2 i : ℂ) +
        remComp P A j gq S1 G1 (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength)) (q.2 2 / ‖q.2‖) 2 * (azC q.2 i : ℂ))

def linPart (P : ShapeParams) (α : ℂ) (y : Space) : Fin 3 → ℂ := fun i => -(α / (P.chartLength : ℂ)) * (linS y i : ℂ)

theorem scaled_identity (P : ShapeParams) (hL : 0 < P.chartLength) (κ : FieldKey) (A : KeyAmp) (σ : ℝ)
    (gq : Polynomial ℝ) (S1 G1 : Spline) (T0 : ℝ)
    (hsplit : ∀ t < T0, ∀ x k, reducedComps P κ A t x k = (t : ℂ) * leadComp A.axisCoef x k +
      ((t ^ 2 : ℝ) : ℂ) * remComp P A κ.phaseIndex gq S1 G1 t x k)
    (s : ℝ) (hs : 0 < s) (v : Space) (hv : v ≠ 0) (hτ : s * ‖v‖ / (s * ‖v‖ + P.chartLength) < T0) :
    keyVector P κ A σ (s • v) - keyPhase P κ σ (s • v) • linPart P A.axisCoef (s • v) =
      (s ^ 2) • (keyPhase P κ σ (s • v) • scaledRem P A κ.phaseIndex gq S1 G1 (s, v)) := by
  have hNv : 0 < ‖v‖ := norm_pos_iff.2 hv
  have hN : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
  have hsv : ∀ j, (s • v) j = s * v j := fun j => by rw [PiLp.smul_apply, smul_eq_mul]
  have hT : chartCoord P (s • v) = s * ‖v‖ / (s * ‖v‖ + P.chartLength) := by rw [chartCoord, hN]
  have hH : heightRatio (s • v) = v 2 / ‖v‖ := by
    rw [heightRatio, hsv, hN]
    field_simp
  funext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Complex.real_smul, keyVector, linPart, scaledRem]
  rw [hT, hH]
  simp only [hsplit _ hτ, radialVec, polarVecQ, azimVecQ, qOf, hH, hsv, hN, radC, polC, azC, linS]
  generalize keyPhase P κ σ (s • v) = c
  generalize remComp P A κ.phaseIndex gq S1 G1 (s * ‖v‖ / (s * ‖v‖ + P.chartLength)) (v 2 / ‖v‖) 0 = h0
  generalize remComp P A κ.phaseIndex gq S1 G1 (s * ‖v‖ / (s * ‖v‖ + P.chartLength)) (v 2 / ‖v‖) 1 = h1
  generalize remComp P A κ.phaseIndex gq S1 G1 (s * ‖v‖ / (s * ‖v‖ + P.chartLength)) (v 2 / ‖v‖) 2 = h2
  generalize hNd : ‖v‖ = N at *
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hN' : (N : ℂ) ≠ 0 := by exact_mod_cast hNv.ne'
  have hL' : (P.chartLength : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hD' : (s : ℂ) * (N : ℂ) + (P.chartLength : ℂ) ≠ 0 := by
    have : s * N + P.chartLength ≠ 0 := by positivity
    exact_mod_cast this
  fin_cases i <;>
  · simp only [leadComp, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    push_cast
    field_simp
    ring

theorem origin_quadratic (gp : Polynomial ℝ) (h : gp.eval 0 = 1) :
    ∃ gq : Polynomial ℝ, ∀ t, gp.eval t = 1 + t * gq.eval t := by
  have hd : Polynomial.X ∣ gp - Polynomial.C 1 := by
    rw [Polynomial.X_dvd_iff, Polynomial.coeff_sub, Polynomial.coeff_C_zero, Polynomial.coeff_zero_eq_eval_zero, h,
      sub_self]
  obtain ⟨gq, hgq⟩ := hd
  refine ⟨gq, fun t => ?_⟩
  have := congrArg (Polynomial.eval t) hgq
  simp only [Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X] at this
  linarith

theorem keyPhase_eq (P : ShapeParams) (κ : FieldKey) (σ : ℝ) (h0 : κ.label.1 = 0) :
    keyPhase P κ σ = fun y => Complex.exp ((((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)) : ℝ) : ℂ) * Complex.I) := by
  funext y
  simp only [keyPhase, labelAzimuth, h0, zero_mul, Int.cast_zero, add_zero]

theorem keyPhase_contDiff (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ) (h0 : κ.label.1 = 0) :
    ContDiff ℝ 2 (keyPhase P κ σ) := by
  obtain ⟨δ, hδ, hΦ⟩ := hP.phase.smooth
  rw [keyPhase_eq P κ σ h0]
  have hr : ContDiff ℝ 2 (fun y : Space => 2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)) := by
    refine contDiff_iff_contDiffAt.2 fun y => contDiffAt_const.add (contDiffAt_const.mul ?_)
    have hu : Set.Ioi (-δ) ∈ nhds (‖y‖ ^ 2) := Ioi_mem_nhds (by nlinarith [sq_nonneg ‖y‖])
    exact ((hΦ.contDiffAt hu).of_le (by norm_num)).comp y (contDiff_norm_sq ℝ).contDiffAt
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp hr).mul contDiff_const)

theorem poly_contDiff (f : Polynomial ℝ) : ContDiff ℝ 2 (fun x : ℝ => f.eval x) := by
  simpa using f.contDiff_aeval (𝕜 := ℝ) 2

theorem profQuot_eq (gq : Polynomial ℝ) (e : ℕ) (t : ℝ) :
    profQuot gq e t = ((gq.eval t - (∑ i ∈ Finset.range e, (1 - t) ^ i) -
      t * (∑ i ∈ Finset.range e, (1 - t) ^ i) * gq.eval t : ℝ) : ℂ) := by
  unfold profQuot geomTail
  push_cast
  ring

theorem slopeQuot_contDiffAt (P : ShapeParams) (hP : IsShapeParams P) (q : ℝ × ℝ) (hq : q.1 < 1) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => slopeQuot P p.1) q := by
  obtain ⟨δ, hδ, hΦ⟩ := hP.phase.smooth
  have hΦ' : ContDiffOn ℝ 2 (deriv P.radialPhase) (Set.Ioi (-δ)) := hΦ.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hne : 1 - q.1 ≠ 0 := by linarith
  have hin : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (P.chartLength * p.1 / (1 - p.1)) ^ 2) q :=
    ((contDiffAt_const.mul contDiffAt_fst).div (contDiffAt_const.sub contDiffAt_fst) hne).pow 2
  have hu : Set.Ioi (-δ) ∈ nhds ((P.chartLength * q.1 / (1 - q.1)) ^ 2) :=
    Ioi_mem_nhds (by nlinarith [sq_nonneg (P.chartLength * q.1 / (1 - q.1))])
  have hd : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => deriv P.radialPhase ((P.chartLength * p.1 / (1 - p.1)) ^ 2)) q :=
    ContDiffAt.comp (g := deriv P.radialPhase) q (hΦ'.contDiffAt hu) hin
  unfold slopeQuot
  exact ((contDiffAt_const.mul ((contDiffAt_const.div (contDiffAt_const.sub contDiffAt_fst) hne).pow 2)).mul
    contDiffAt_fst).mul hd

theorem rem_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound) (P : ShapeParams)
    (hP : IsShapeParams P) (A : KeyAmp) (j : ℤ) (gq : Polynomial ℝ) (S1 G1 : Spline)
    (hstream : IsJoinedSpline 2 2 A.stream) (hS1 : IsJoinedSpline 2 2 S1) (hG1 : IsJoinedSpline 2 1 G1)
    (k : Fin 3) (q : ℝ × ℝ) (hq : q.1 < 1) :
    TameAt (fun p : ℝ × ℝ => remComp P A j gq S1 G1 p.1 p.2 k) q := by
  have tX : ∀ f : ℝ × ℝ → ℝ, ContDiffAt ℝ 2 f q → TameAt (fun p => (f p : ℂ)) q := fun f hf =>
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp q hf)
  have tC : ∀ c : ℂ, TameAt (fun _ : ℝ × ℝ => c) q := fun c => tame_of_contDiffAt contDiffAt_const
  have hpe : ContDiff ℝ 2 (fun p : ℝ × ℝ => P.origin.poly.eval p.1) := (poly_contDiff _).comp contDiff_fst
  have hpd : ContDiff ℝ 2 (fun p : ℝ × ℝ => P.origin.poly.derivative.eval p.1) := (poly_contDiff _).comp contDiff_fst
  have hgq : ContDiff ℝ 2 (fun p : ℝ × ℝ => gq.eval p.1) := (poly_contDiff _).comp contDiff_fst
  have hsum : ContDiff ℝ 2 (fun p : ℝ × ℝ => ∑ i ∈ Finset.range A.highOrder, (1 - p.1) ^ i) :=
    ContDiff.sum fun i _ => (contDiff_const.sub contDiff_fst).pow i
  have tw : TameAt (fun p : ℝ × ℝ => wt A.highOrder p.1) q := tX _ (by fun_prop)
  have twd : TameAt (fun p : ℝ × ℝ => wtDeriv A.highOrder p.1) q := tX _ (by fun_prop)
  have tμ : TameAt (fun p : ℝ × ℝ => profQuot gq A.highOrder p.1) q := by
    refine tame_congr (tX (fun p => gq.eval p.1 - (∑ i ∈ Finset.range A.highOrder, (1 - p.1) ^ i) -
      p.1 * (∑ i ∈ Finset.range A.highOrder, (1 - p.1) ^ i) * gq.eval p.1)
      (((hgq.sub hsum).sub ((contDiff_fst.mul hsum).mul hgq)).contDiffAt)) (Filter.Eventually.of_forall fun p => ?_)
    exact profQuot_eq gq A.highOrder p.1
  have tS1 := spline_tame hsm hsl hS1 (by norm_num) (by norm_num) q
  have hS1x := ((splineDerivatives_holds 2 2 S1 hS1).2 (by norm_num)).1
  have tS1x := spline_tame hsm hsl hS1x (by norm_num) (by norm_num) q
  have tG1 := spline_tame hsm hsl hG1 (by norm_num) (by norm_num) q
  have tS := spline_tame hsm hsl hstream (by norm_num) (by norm_num) q
  have hSt := ((splineDerivatives_holds 2 2 A.stream hstream).1 (by norm_num)).1
  have tSt := spline_tame hsm hsl hSt (by norm_num) (by norm_num) q
  have tΨ : TameAt (fun p : ℝ × ℝ => streamFull P A p.1 p.2) q :=
    tame_add (tame_mul (tC A.axisCoef) (tX (fun p => P.origin.poly.eval p.1 * p.2) (hpe.mul contDiff_snd).contDiffAt)) tS
  have tΨt : TameAt (fun p : ℝ × ℝ => streamFullT P A p.1 p.2) q :=
    tame_add (tame_mul (tC A.axisCoef) (tX (fun p => P.origin.poly.derivative.eval p.1 * p.2)
      (hpd.mul contDiff_snd).contDiffAt)) tSt
  have tsq : TameAt (fun p : ℝ × ℝ => (((j : ℝ) * slopeQuot P p.1 : ℝ) : ℂ)) q :=
    tX _ (contDiffAt_const.mul (slopeQuot_contDiffAt P hP q hq))
  fin_cases k
  · have hall := tame_neg (tame_add (tame_mul (tame_mul (tC A.axisCoef) (tX (fun p => 1 - 3 * p.2 ^ 2) (by fun_prop))) tμ)
      (tame_mul tw (tame_add (tame_mul (tX (fun p => -2 * p.2) (by fun_prop)) tS1)
        (tame_mul (tX (fun p => 1 - p.2 ^ 2) (by fun_prop)) tS1x))))
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp only [remComp, Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
  · have hall := tame_neg (tame_add (tame_add (tame_add (tame_sub
      (tame_mul (tame_mul (tame_mul (tC 3) (tC A.axisCoef)) (tX (fun p => p.2) (by fun_prop))) tμ)
      (tame_mul (tame_mul (tame_mul (tC A.axisCoef) (tX (fun p => p.2) (by fun_prop))) tw) (tX _ hpe.contDiffAt)))
      (tame_mul (tame_mul (tX (fun p => 3 - p.1) (by fun_prop)) tw) tS1))
      (tame_mul (tX (fun p => 1 - p.1) (by fun_prop)) (tame_add (tame_mul twd tΨ) (tame_mul tw tΨt))))
      (tame_mul (tame_mul (tC Complex.I) tsq) (tame_mul tw tΨ)))
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp only [remComp, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero]
  · have hall := tame_mul tw tG1
    refine tame_congr hall (Filter.Eventually.of_forall fun p => ?_)
    simp only [remComp, Fin.reduceFinMk, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]

theorem scaledRem_tame (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound) (P : ShapeParams)
    (hP : IsShapeParams P) (A : KeyAmp) (j : ℤ) (gq : Polynomial ℝ) (S1 G1 : Spline)
    (hstream : IsJoinedSpline 2 2 A.stream) (hS1 : IsJoinedSpline 2 2 S1) (hG1 : IsJoinedSpline 2 1 G1)
    (i : Fin 3) (p : ℝ × Space) (hp1 : 0 ≤ p.1) (hp2 : p.2 ≠ 0) :
    TameAt (fun q => scaledRem P A j gq S1 G1 q i) p := by
  have hL := hP.chartLength_pos
  have hn' : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => ‖q.2‖) p := (contDiffAt_norm ℝ hp2).comp p contDiffAt_snd
  have hN0 : ‖p.2‖ ≠ 0 := norm_ne_zero_iff.2 hp2
  have hr : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 * ‖q.2‖) p := contDiffAt_fst.mul hn'
  have hr0 : 0 ≤ p.1 * ‖p.2‖ := mul_nonneg hp1 (norm_nonneg _)
  have hden : p.1 * ‖p.2‖ + P.chartLength ≠ 0 := by positivity
  have hτ : ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength)) p :=
    hr.div (hr.add contDiffAt_const) hden
  have hu : ∀ j : Fin 3, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j) p := fun j =>
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp contDiff_snd).contDiffAt
  have hrat : ∀ j, ContDiffAt ℝ ⊤ (fun q : ℝ × Space => q.2 j / ‖q.2‖) p := fun j => (hu j).div hn' hN0
  have cC : ∀ f : ℝ × Space → ℝ, ContDiffAt ℝ 2 f p → TameAt (fun q => (f q : ℂ)) p := fun f hf =>
    tame_of_contDiffAt (Complex.ofRealCLM.contDiff.contDiffAt.comp p hf)
  have hτ1 : p.1 * ‖p.2‖ / (p.1 * ‖p.2‖ + P.chartLength) < 1 := by
    rw [div_lt_one (by positivity)]
    linarith
  have hH : ∀ k, TameAt (fun q : ℝ × Space =>
      remComp P A j gq S1 G1 (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength)) (q.2 2 / ‖q.2‖) k) p := fun k =>
    tame_comp (g := fun z : ℝ × ℝ => remComp P A j gq S1 G1 z.1 z.2 k)
      (Φ := fun q : ℝ × Space => (q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength), q.2 2 / ‖q.2‖))
      (rem_tame hsm hsl P hP A j gq S1 G1 hstream hS1 hG1 k _ hτ1) (tame_of_contDiffAt ((hτ.prodMk (hrat 2)).of_le le_top))
  have hlin : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖ * linS q.2 i / (P.chartLength * (q.1 * ‖q.2‖ + P.chartLength))) p := by
    have hl : ContDiffAt ℝ 2 (fun q : ℝ × Space => linS q.2 i) p := by
      fin_cases i
      · exact ((hu 0).of_le le_top)
      · exact ((hu 1).of_le le_top)
      · exact (contDiffAt_const.mul (hu 2)).of_le le_top
    exact ((hn'.of_le le_top).mul hl).div (contDiffAt_const.mul ((hr.add contDiffAt_const).of_le le_top))
      (mul_ne_zero hL.ne' hden)
  have hcoef : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖ ^ 2 / (q.1 * ‖q.2‖ + P.chartLength) ^ 2) p :=
    ((hn'.pow 2).div ((hr.add contDiffAt_const).pow 2) (pow_ne_zero 2 hden)).of_le le_top
  have hrad : ContDiffAt ℝ 2 (fun q : ℝ × Space => radC q.2 i) p := (hrat i).of_le le_top
  have hpol : ContDiffAt ℝ 2 (fun q : ℝ × Space => polC q.2 i) p := by
    fin_cases i
    · exact (((hrat 2).mul (hu 0)).div hn' hN0).of_le le_top
    · exact (((hrat 2).mul (hu 1)).div hn' hN0).of_le le_top
    · exact ((contDiffAt_const.sub ((hrat 2).pow 2)).neg).of_le le_top
  have haz : ContDiffAt ℝ 2 (fun q : ℝ × Space => azC q.2 i) p := by
    fin_cases i
    · exact (((hu 1).neg).div hn' hN0).of_le le_top
    · exact (hrat 0).of_le le_top
    · exact contDiffAt_const
  exact tame_add (tame_mul (tame_of_contDiffAt contDiffAt_const) (cC _ hlin))
    (tame_mul (cC _ hcoef) (tame_add (tame_add (tame_mul (hH 0) (cC _ hrad)) (tame_mul (hH 1) (cC _ hpol)))
      (tame_mul (hH 2) (cC _ haz))))

end TypeTwoNear

end Internal

open Internal.TypeTwoNear in
theorem typeTwoKey_near_origin_of (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound)
    (P : ShapeParams) (D : TimeFieldData) (κ : FieldKey) (σ : ℝ) (hP : IsShapeParams P) (hD : IsTimeFieldData D)
    (hκ : κ ∈ D.keys) (h0 : κ.label.1 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) (Metric.ball 0 ρ) ∧
      ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) (Metric.ball 0 ρ) := by
  set A := D.amp κ with hA
  have hL := hP.chartLength_pos
  have hstream : IsJoinedSpline 2 2 A.stream := hD.stream_class κ hκ h0
  have hswirl : IsJoinedSpline 1 1 A.swirl := hD.swirl_class κ hκ h0
  obtain ⟨S1, hS1, cS, hcS, hsS⟩ := first_row_quotient A.stream hstream (hD.stream_origin κ hκ h0)
  obtain ⟨G1, hG1, cG, hcG, hsG⟩ := first_row_quotient A.swirl hswirl (hD.swirl_origin κ hκ h0)
  obtain ⟨gq, hgq⟩ := origin_quadratic P.origin.poly hP.origin.at_zero
  set T0 := min (min cS cG) (min P.origin.edge (1 / 2)) with hT0
  have hT0pos : 0 < T0 := lt_min (lt_min hcS hcG) (lt_min hP.origin.edge_pos (by norm_num))
  have hsS' : ∀ t < T0, ∀ x, A.stream.evalHalf t x = (t : ℂ) * S1.evalHalf t x := fun t ht x =>
    hsS t (lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_left _ _))) x
  have hsG' : ∀ t < T0, ∀ x, A.swirl.evalHalf t x = (t : ℂ) * G1.evalHalf t x := fun t ht x =>
    hsG t (lt_of_lt_of_le ht ((min_le_left _ _).trans (min_le_right _ _))) x
  have hTe : T0 ≤ P.origin.edge := (min_le_right _ _).trans (min_le_left _ _)
  have hT1 : T0 ≤ 1 / 2 := (min_le_right _ _).trans (min_le_right _ _)
  have hsplit : ∀ t < T0, ∀ x k, reducedComps P κ A t x k = (t : ℂ) * leadComp A.axisCoef x k +
      ((t ^ 2 : ℝ) : ℂ) * remComp P A κ.phaseIndex gq S1 G1 t x k := fun t ht x k =>
    reduced_split hsm P κ A h0 hstream gq hgq S1 G1 hS1 T0 hTe hsS' hsG' t ht x k
  have hc : ContDiff ℝ 2 (keyPhase P κ σ) := keyPhase_contDiff P hP κ σ h0
  set h : Space → (Fin 3 → ℂ) := fun y => keyPhase P κ σ y • linPart P A.axisCoef y with hh_def
  have hh : ContDiff ℝ 2 h := by
    refine contDiff_pi.2 fun i => ?_
    have hl : ContDiff ℝ 2 (fun y : Space => linPart P A.axisCoef y i) := by
      have hu : ∀ j : Fin 3, ContDiff ℝ 2 (fun y : Space => y j) := fun j =>
        (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff
      have hs : ContDiff ℝ 2 (fun y : Space => linS y i) := by
        fin_cases i
        · exact hu 0
        · exact hu 1
        · exact contDiff_const.mul (hu 2)
      exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hs)
    exact hc.mul hl
  set g : Space → (Fin 3 → ℂ) := fun y => keyVector P κ A σ y - h y with hg_def
  set Fm : ℝ × Space → (Fin 3 → ℂ) := fun q => keyPhase P κ σ (q.1 • q.2) • scaledRem P A κ.phaseIndex gq S1 G1 q
    with hFm_def
  set F : ℝ × Space → (Fin 3 → ℂ) := fun q => if 0 < q.1 ∧ q.2 ≠ 0 then ((q.1 ^ 2)⁻¹ : ℝ) • g (q.1 • q.2) else Fm q
    with hF_def
  set ρ := P.chartLength * T0 / 4 with hρ_def
  have hρ : 0 < ρ := by positivity
  have hg0 : g 0 = 0 := by
    have hz : ∀ k, reducedComps P κ A (chartCoord P 0) (heightRatio 0) k = 0 := by
      intro k
      have e : chartCoord P 0 = 0 := by simp [chartCoord]
      rw [e, hsplit 0 hT0pos]
      simp
    funext i
    simp only [g, h, keyVector, hz, linPart, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    fin_cases i <;> simp [linS]
  have hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → g (s • v) = (s ^ 2) • F (s, v) := by
    intro s hs v hv
    simp only [F, if_pos (And.intro hs hv), smul_smul]
    rw [show s ^ 2 * (s ^ 2)⁻¹ = 1 by field_simp, one_smul]
  have hF : ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
      ∃ U ∈ nhds p, (∀ q ∈ U, DifferentiableAt ℝ F q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ F) U := by
    intro p hp
    have hp1 : 0 ≤ p.1 := hp.1.1
    have hp3 : 1 / 2 ≤ ‖p.2‖ := by simpa using hp.2.2
    have hpv : p.2 ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at hp3
      norm_num at hp3
    have hev : F =ᶠ[nhds p] Fm := by
      filter_upwards [Metric.ball_mem_nhds p (lt_min (by norm_num : (0 : ℝ) < 1 / 8) hρ)] with q hq
      rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff] at hq
      have hq1 : q.1 < P.chartLength * T0 / 2 := by
        have := hq.1
        rw [Real.dist_eq] at this
        have := (abs_lt.1 (lt_of_lt_of_le this (min_le_right _ _))).2
        have hp1' : p.1 ≤ P.chartLength * T0 / 4 := hp.1.2
        linarith
      have hq2 : ‖q.2‖ < 9 / 8 := by
        have := lt_of_lt_of_le hq.2 (min_le_left _ _)
        rw [dist_eq_norm] at this
        have := norm_le_norm_add_norm_sub' q.2 p.2
        have hp2 : ‖p.2‖ ≤ 1 := by simpa using hp.2.1
        linarith [norm_sub_rev q.2 p.2]
      have hq3 : 3 / 8 < ‖q.2‖ := by
        have := lt_of_lt_of_le hq.2 (min_le_left _ _)
        rw [dist_eq_norm] at this
        have := norm_le_norm_add_norm_sub' p.2 q.2
        linarith [norm_sub_rev q.2 p.2]
      have hqv : q.2 ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hq3
        norm_num at hq3
      by_cases hq0 : 0 < q.1
      · simp only [F, if_pos (And.intro hq0 hqv)]
        have hτ : q.1 * ‖q.2‖ / (q.1 * ‖q.2‖ + P.chartLength) < T0 := by
          have hqn : 0 ≤ q.1 * ‖q.2‖ := mul_nonneg hq0.le (norm_nonneg _)
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        have hid := scaled_identity P hL κ A σ gq S1 G1 T0 hsplit q.1 hq0 q.2 hqv hτ
        simp only [g, h]
        rw [hid, smul_smul, show (q.1 ^ 2)⁻¹ * q.1 ^ 2 = 1 by field_simp, one_smul]
      · simp only [F, if_neg (show ¬(0 < q.1 ∧ q.2 ≠ 0) from fun hh => hq0 hh.1)]
    have hsm2 : ContDiff ℝ 2 (fun q : ℝ × Space => keyPhase P κ σ (q.1 • q.2)) :=
      hc.comp (contDiff_fst.smul contDiff_snd)
    have htame : TameAt Fm p := by
      refine tame_pi fun i => ?_
      have := tame_mul (tame_of_contDiffAt hsm2.contDiffAt)
        (scaledRem_tame hsm hsl P hP A κ.phaseIndex gq S1 G1 hstream hS1 hG1 i p hp1 hpv)
      refine tame_congr this (Filter.Eventually.of_forall fun q => ?_)
      simp only [Fm, Pi.smul_apply, smul_eq_mul]
    exact tame_region (tame_congr htame hev)
  obtain ⟨hgd, K, hK⟩ := scaled_fderiv_slope hρ hg0 hscale hF
  have hhd : Differentiable ℝ h := hh.differentiable (by norm_num)
  obtain ⟨Kh, hKh⟩ : ∃ Kh : NNReal, LipschitzOnWith Kh (fderiv ℝ h) (Metric.closedBall 0 ρ) :=
    ((hh.fderiv_right (m := 1) (by norm_num)).locallyLipschitz).locallyLipschitzOn.exists_lipschitzOnWith_of_compact
      (isCompact_closedBall 0 ρ)
  have hfe : keyVector P κ A σ = fun y => g y + h y := by
    funext y
    simp only [g, sub_add_cancel]
  have hfd : ∀ y ∈ Metric.ball (0 : Space) ρ, fderiv ℝ (keyVector P κ A σ) y = fderiv ℝ g y + fderiv ℝ h y := by
    intro y hy
    rw [hfe]
    exact fderiv_add (hgd y hy) (hhd y)
  have hsum := hK.add (hKh.mono Metric.ball_subset_closedBall)
  have hlip : LipschitzOnWith (K + Kh) (fderiv ℝ (keyVector P κ A σ)) (Metric.ball 0 ρ) := by
    refine LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_
    rw [hfd y hy, hfd z hz]
    exact hsum.dist_le_mul y hy z hz
  refine ⟨ρ, hρ, ?_, K + Kh, hlip⟩
  rw [show (1 : WithTop ℕ∞) = 0 + 1 by norm_num, contDiffOn_succ_iff_fderiv_of_isOpen Metric.isOpen_ball]
  refine ⟨fun y hy => ?_, by simp, contDiffOn_zero.2 hlip.continuousOn⟩
  rw [hfe]
  exact ((hgd y hy).add (hhd y)).differentiableWithinAt

end GivenShape

end CertCell

end Breakdown

import Breakdown.CellReduction.InstFieldPotentialRotation
import Breakdown.CellReduction.InstFieldPotentialAmp
import Breakdown.CellReduction.InstFieldPotentialPrimitive

open scoped ContDiff RealInnerProductSpace Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellReduction

namespace Instantiation

open CertCell CertCell.GivenShape

namespace Internal

namespace FieldPot

open Coercive.RotationInternal

theorem hasFDerivAt_norm_of_ne {y : Space} (hy : y ≠ 0) :
    HasFDerivAt (fun v : Space => ‖v‖) ((‖y‖⁻¹) • innerSL ℝ y) y := by
  have h1 := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  have hne : ‖y‖ ^ 2 ≠ 0 := by positivity
  have h2 := h1.sqrt hne
  simp only [Real.sqrt_sq (norm_nonneg _)] at h2
  refine h2.congr_fderiv ?_
  have hn : ‖y‖ ≠ 0 := norm_ne_zero_iff.2 hy
  ext v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply]
  simp only [smul_eq_mul, nsmul_eq_mul]
  field_simp
  push_cast
  ring

theorem pair_apply (F' : ℝ × ℝ →L[ℝ] ℂ) (a b : ℝ) : F' (a, b) = (a : ℂ) * F' (1, 0) + (b : ℂ) * F' (0, 1) := by
  have : ((a, b) : ℝ × ℝ) = a • ((1 : ℝ), (0 : ℝ)) + b • ((0 : ℝ), (1 : ℝ)) :=
    Prod.ext (by simp) (by simp)
  rw [this, map_add, map_smul, map_smul, Complex.real_smul, Complex.real_smul]

theorem scalar_grad (P : ShapeParams) (hL : 0 < P.chartLength) (j : ℤ) (e : ℕ) (F : ℝ × ℝ → ℂ)
    (F' : ℝ × ℝ →L[ℝ] ℂ) {y : Space} (hy : y ≠ 0) (Φ' p1 : ℝ)
    (hΦ : HasDerivAt P.radialPhase Φ' (‖y‖ ^ 2))
    (hp : HasDerivAt (fun t : ℝ => t ^ 1 * (1 - t) ^ e) p1 (chartCoord P y))
    (hF : HasFDerivAt F F' (chartCoord P y, CellCert.GivenFields.heightRatio y)) :
    ∃ ψ' : Space →L[ℝ] ℂ,
      HasFDerivAt (fun v => Complex.exp ((((j : ℝ) * P.radialPhase (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        CellCert.GivenFields.weightPoly 1 e (chartCoord P v) *
          F (chartCoord P v, CellCert.GivenFields.heightRatio v)) ψ' y ∧
      ∀ v, ψ' v = Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        ((2 * ((j : ℝ) * Φ') : ℝ) * Complex.I * ((chartCoord P y * (1 - chartCoord P y) ^ e : ℝ) : ℂ) *
            F (chartCoord P y, CellCert.GivenFields.heightRatio y) +
          ((p1 : ℂ) * F (chartCoord P y, CellCert.GivenFields.heightRatio y) +
            ((chartCoord P y * (1 - chartCoord P y) ^ e : ℝ) : ℂ) * F' (1, 0)) *
            ((P.chartLength / (‖y‖ + P.chartLength) ^ 2 / ‖y‖ : ℝ) : ℂ) -
          ((chartCoord P y * (1 - chartCoord P y) ^ e : ℝ) : ℂ) * F' (0, 1) * ((y 2 / ‖y‖ ^ 3 : ℝ) : ℂ)) *
          ((⟪y, v⟫ : ℝ) : ℂ) +
        Complex.exp ((((j : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
          ((chartCoord P y * (1 - chartCoord P y) ^ e : ℝ) : ℂ) * F' (0, 1) * ((1 / ‖y‖ : ℝ) : ℂ) * ((v 2 : ℝ) : ℂ) := by
  set L := P.chartLength with hLdef
  set r := ‖y‖ with hrdef
  have hr0 : 0 < r := norm_pos_iff.2 hy
  have hN := hasFDerivAt_norm_of_ne hy
  have hφ : HasDerivAt (fun s : ℝ => s / (s + L)) (L / (r + L) ^ 2) r := by
    have h := (hasDerivAt_id r).div ((hasDerivAt_id r).add_const L) (by positivity)
    refine h.congr_deriv ?_
    simp only [id_eq]
    ring
  have hT : HasFDerivAt (chartCoord P) ((L / (r + L) ^ 2) • ((‖y‖⁻¹) • innerSL ℝ y)) y :=
    (hφ.comp_hasFDerivAt y hN).congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => rfl)
  have hinv := (hasDerivAt_inv hr0.ne').comp_hasFDerivAt y hN
  have hX : HasFDerivAt CellCert.GivenFields.heightRatio
      ((y 2) • ((-(r ^ 2)⁻¹) • ((‖y‖⁻¹) • innerSL ℝ y)) + (‖y‖⁻¹) • (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ)) y :=
    ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).hasFDerivAt.mul hinv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun v => by simp [CellCert.GivenFields.heightRatio, div_eq_mul_inv])
  have hU := (hasStrictFDerivAt_norm_sq y).hasFDerivAt
  rw [two_nsmul] at hU
  have hE0 := (hΦ.const_mul (j : ℝ)).comp_hasFDerivAt y hU
  have hE1 : HasFDerivAt (fun v : Space => Complex.exp ((((j : ℝ) * P.radialPhase (‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I)) _ y :=
    ((Complex.ofRealCLM.hasFDerivAt.comp y hE0).mul_const Complex.I).cexp
  have hP0 := hp.comp_hasFDerivAt y hT
  have hP1 : HasFDerivAt (fun v : Space => CellCert.GivenFields.weightPoly 1 e (chartCoord P v)) _ y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hP0
  have hF1 : HasFDerivAt (fun v : Space => F (chartCoord P v, CellCert.GivenFields.heightRatio v)) _ y :=
    hF.comp y (hT.prodMk hX)
  have hall := (hE1.mul hP1).mul hF1
  refine ⟨_, hall, fun v => ?_⟩
  simp only [ContinuousLinearMap.add_apply, FunLike.coe_smul, Pi.smul_apply,
    ContinuousLinearMap.coe_comp, Function.comp_apply, ContinuousLinearMap.prod_apply, innerSL_apply_apply,
    smul_eq_mul, Complex.ofRealCLM_apply,
    CellCert.GivenFields.weightPoly]
  rw [pair_apply]
  have hp2 : (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) v = v 2 := rfl
  simp only [Pi.mul_apply, hp2, pow_one, ← hrdef]
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hrL : (r : ℂ) + (L : ℂ) ≠ 0 := by exact_mod_cast (by positivity : r + L ≠ 0)
  push_cast
  field_simp
  ring

def ofRealL : Space →L[ℝ] (Fin 3 → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (EuclideanSpace.proj i)

theorem ofRealL_apply (v : Space) (i : Fin 3) : ofRealL v i = ((v i : ℝ) : ℂ) := rfl

def turnL : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := turnVec
      map_add' := fun a b => by apply space_ext <;> simp [turnVec, unit_apply] <;> ring
      map_smul' := fun c a => by apply space_ext <;> simp [turnVec, unit_apply] }

theorem turnL_apply (v : Space) : turnL v = turnVec v := rfl

theorem turnVec_apply (v : Space) : turnVec v 0 = -(v 1) ∧ turnVec v 1 = v 0 ∧ turnVec v 2 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [turnVec, unit_apply]

theorem turnL_norm : ‖turnL‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => ?_
  rw [one_mul, turnL_apply, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  obtain ⟨h0, h1, h2⟩ := turnVec_apply v
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, h0, h1, h2]
  nlinarith [sq_nonneg (v 2)]

theorem inner_unit (y : Space) (i : Fin 3) : ⟪y, unitVector i⟫ = y i := by
  simp [unitVector, PiLp.inner_apply, EuclideanSpace.single_apply]

theorem curl_scalarPair {ψ h : Space → ℂ} {ψ' h' : Space →L[ℝ] ℂ} {y : Space} (hψ : HasFDerivAt ψ ψ' y)
    (hh : HasFDerivAt h h' y) (α β α' β' c : ℂ) (hψv : ∀ v, ψ' v = α * ((⟪y, v⟫ : ℝ) : ℂ) + β * ((v 2 : ℝ) : ℂ))
    (hhv : ∀ v, h' v = α' * ((⟪y, v⟫ : ℝ) : ℂ) + β' * ((v 2 : ℝ) : ℂ)) :
    AdjointDefect.curlAt (fun v => realPartVec (c • (ψ v • ofRealL (turnL v) + h v • ofRealL v))) y =
      realPartVec (c • ![-(α * (y 2 : ℂ) + β) * (y 0 : ℂ) - β' * (y 1 : ℂ),
        -(α * (y 2 : ℂ) + β) * (y 1 : ℂ) + β' * (y 0 : ℂ),
        α * ((y 0 : ℂ) ^ 2 + (y 1 : ℂ) ^ 2) + 2 * ψ y]) := by
  have h1 := hψ.smul ((ofRealL.comp turnL).hasFDerivAt (x := y))
  have h2 := hh.smul (ofRealL.hasFDerivAt (x := y))
  have h3 := (realPartVec.hasFDerivAt.comp y ((h1.add h2).const_smul c))
  have hfun : (fun v => realPartVec (c • (ψ v • ofRealL (turnL v) + h v • ofRealL v))) =
      realPartVec ∘ (c • (ψ • ⇑(ofRealL.comp turnL) + h • ⇑ofRealL)) := rfl
  rw [hfun, AdjointDefect.curlAt, h3.fderiv]
  have ev : ∀ w : Space, ∀ i : Fin 3,
      ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) w) i =
      (c * (ψ y * ((turnL w i : ℝ) : ℂ) + ψ' w * ((turnL y i : ℝ) : ℂ) + (h y * ((w i : ℝ) : ℂ) +
        h' w * ((y i : ℝ) : ℂ)))).re := by
    intro w i
    simp [realPartVec, ofRealL_apply]
    ring
  have rp : ∀ (u : Fin 3 → ℂ) (i : Fin 3), realPartVec u i = (u i).re := fun u i => by simp [realPartVec]
  obtain ⟨t0, t1, t2⟩ := turnVec_apply y
  have tu : ∀ k : Fin 3, turnVec (unitVector k) 0 = -(unitVector k 1) ∧ turnVec (unitVector k) 1 = unitVector k 0 ∧
      turnVec (unitVector k) 2 = 0 := fun k => turnVec_apply _
  have k0 : ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 1)) 2 -
      ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 2)) 1 =
      (c * (-(α * (y 2 : ℂ) + β) * (y 0 : ℂ) - β' * (y 1 : ℂ))).re := by
    rw [ev, ev, ← Complex.sub_re]
    congr 1
    simp only [turnL_apply, t0, t1, t2, (tu 1).1, (tu 1).2.1, (tu 1).2.2, (tu 2).1, (tu 2).2.1, (tu 2).2.2,
      hψv, hhv, inner_unit, unit_apply]
    simp
    ring
  have k1 : ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 2)) 0 -
      ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 0)) 2 =
      (c * (-(α * (y 2 : ℂ) + β) * (y 1 : ℂ) + β' * (y 0 : ℂ))).re := by
    rw [ev, ev, ← Complex.sub_re]
    congr 1
    simp only [turnL_apply, t0, t1, t2, (tu 0).1, (tu 0).2.1, (tu 0).2.2, (tu 2).1, (tu 2).2.1, (tu 2).2.2,
      hψv, hhv, inner_unit, unit_apply]
    simp
    ring
  have k2 : ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 0)) 1 -
      ((realPartVec.comp (c • (ψ y • ofRealL.comp turnL + ψ'.smulRight ((ofRealL.comp turnL) y) +
        (h y • ofRealL + h'.smulRight (ofRealL y))))) (unitVector 1)) 0 =
      (c * (α * ((y 0 : ℂ) ^ 2 + (y 1 : ℂ) ^ 2) + 2 * ψ y)).re := by
    rw [ev, ev, ← Complex.sub_re]
    congr 1
    simp only [turnL_apply, t0, t1, t2, (tu 0).1, (tu 0).2.1, (tu 0).2.2, (tu 1).1, (tu 1).2.1, (tu 1).2.2,
      hψv, hhv, inner_unit, unit_apply]
    simp
    ring
  apply space_ext
  · rw [rp]
    simp only [PiLp.add_apply, PiLp.smul_apply, unit_apply, smul_eq_mul]
    simp only [k0]
    simp
  · rw [rp]
    simp only [PiLp.add_apply, PiLp.smul_apply, unit_apply, smul_eq_mul]
    simp only [k1]
    simp
  · rw [rp]
    simp only [PiLp.add_apply, PiLp.smul_apply, unit_apply, smul_eq_mul]
    simp only [k2]
    simp

def originExt (g : OriginProfile) : ℝ → ℝ := if g.edge < 1 then g.eval else fun t => g.poly.eval t

theorem originExt_eq {g : OriginProfile} (hg : IsOriginProfile g) {t : ℝ} (ht : t < 1) :
    originExt g t = g.eval t := by
  unfold originExt
  split_ifs with h
  · rfl
  · have he : g.edge = 1 := le_antisymm hg.edge_le (not_lt.1 h)
    simp [OriginProfile.eval, he, ht.le]

theorem originExt_smooth {g : OriginProfile} (hg : IsOriginProfile g) : ContDiff ℝ 1 (originExt g) := by
  unfold originExt
  split_ifs with h
  · rw [contDiff_iff_contDiffAt]
    intro t
    rcases lt_or_ge t 1 with ht | ht
    · exact ((shapeParts_closed.origin_profile g hg).1.contDiffAt (Iio_mem_nhds ht)).of_le (by norm_num)
    · have hev : g.eval =ᶠ[𝓝 t] fun _ => g.tail := by
        filter_upwards [Ioi_mem_nhds (h.trans_le ht)] with s hs
        simp [OriginProfile.eval, not_le.2 (show g.edge < s from hs)]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  · refine contDiff_one_iff_deriv.2 ⟨g.poly.differentiable, ?_⟩
    have hd : deriv (fun t => g.poly.eval t) = fun t => (Polynomial.derivative g.poly).eval t :=
      funext fun t => Polynomial.deriv g.poly
    rw [hd]
    exact (Polynomial.derivative g.poly).continuous

def streamF (P : ShapeParams) (A : KeyAmp) (z : ℝ × ℝ) : ℂ :=
  A.axisCoef * ((originExt P.origin z.1 * z.2 : ℝ) : ℂ) + A.stream.evalHalf z.1 z.2

def swirlF (A : KeyAmp) (z : ℝ × ℝ) : ℂ := ∫ u in (-1 : ℝ)..z.2, A.swirl.evalHalf z.1 u

theorem streamF_smooth {P : ShapeParams} (hP : IsShapeParams P) {A : KeyAmp} (hs : IsJoinedSpline 2 2 A.stream) :
    ContDiff ℝ 1 (streamF P A) := by
  have h1 : ContDiff ℝ 1 (fun z : ℝ × ℝ => originExt P.origin z.1 * z.2) :=
    ((originExt_smooth hP.origin).comp contDiff_fst).mul contDiff_snd
  have h2 := (Complex.ofRealCLM.contDiff.comp h1).const_smul A.axisCoef
  have h3 : ContDiff ℝ 1 (fun z : ℝ × ℝ => A.stream.evalHalf z.1 z.2) :=
    (shapeParts_closed.spline_smooth 2 2 A.stream hs).of_le (by norm_num)
  exact h2.add h3

theorem streamF_eq (P : ShapeParams) (hP : IsShapeParams P) (A : KeyAmp) {t : ℝ} (ht : t < 1) (x : ℝ) :
    streamF P A (t, x) = streamValue P A t x := by
  simp [streamF, streamValue, originExt_eq hP.origin ht]

theorem swirlF_smooth (A : KeyAmp) (hs : IsJoinedSpline 1 1 A.swirl) : ContDiff ℝ 1 (swirlF A) :=
  primitiveSmooth_holds (fun z => A.swirl.evalHalf z.1 z.2)
    ((shapeParts_closed.spline_smooth 1 1 A.swirl hs).of_le (by norm_num))

theorem line_second {F : ℝ × ℝ → ℂ} {F' : ℝ × ℝ →L[ℝ] ℂ} {t x : ℝ} (h : HasFDerivAt F F' (t, x)) :
    HasDerivAt (fun x' => F (t, x')) (F' (0, 1)) x := by
  have hl : HasDerivAt (fun x' : ℝ => (t, x')) ((0 : ℝ), (1 : ℝ)) x :=
    (hasDerivAt_const x t).prodMk (hasDerivAt_id x)
  exact h.comp_hasDerivAt x hl

theorem line_first {F : ℝ × ℝ → ℂ} {F' : ℝ × ℝ →L[ℝ] ℂ} {t x : ℝ} (h : HasFDerivAt F F' (t, x)) :
    HasDerivAt (fun t' => F (t', x)) (F' (1, 0)) t := by
  have hl : HasDerivAt (fun t' : ℝ => (t', x)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id t).prodMk (hasDerivAt_const t x)
  exact h.comp_hasDerivAt t hl

theorem swirlF_second (A : KeyAmp) (hs : IsJoinedSpline 1 1 A.swirl) (t x : ℝ) :
    fderiv ℝ (swirlF A) (t, x) ((0 : ℝ), (1 : ℝ)) = A.swirl.evalHalf t x := by
  have hd : HasFDerivAt (swirlF A) (fderiv ℝ (swirlF A) (t, x)) (t, x) :=
    ((swirlF_smooth A hs).differentiable (by norm_num) (t, x)).hasFDerivAt
  have h1 : HasDerivAt (fun x' => swirlF A (t, x')) (fderiv ℝ (swirlF A) (t, x) ((0 : ℝ), (1 : ℝ))) x :=
    line_second hd
  have hcs : Continuous (fun z : ℝ × ℝ => A.swirl.evalHalf z.1 z.2) :=
    (shapeParts_closed.spline_smooth 1 1 A.swirl hs).continuous
  have hc : Continuous (fun u => A.swirl.evalHalf t u) := hcs.comp₂ continuous_const continuous_id'
  have h2 : HasDerivAt (fun u => ∫ v in (-1 : ℝ)..u, A.swirl.evalHalf t v) (A.swirl.evalHalf t x) x :=
    (hc.integral_hasStrictDerivAt (-1) x).hasDerivAt
  have e : (fun x' => swirlF A (t, x')) = fun u => ∫ v in (-1 : ℝ)..u, A.swirl.evalHalf t v := by
    funext u
    simp only [swirlF]
  rw [e] at h1
  exact h1.unique h2

theorem chartCoord_lt_one (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) : chartCoord P y < 1 := by
  unfold chartCoord
  rw [div_lt_one (by positivity)]
  linarith

theorem chartRadius_coord (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    chartRadius P (chartCoord P y) = ‖y‖ := by
  unfold chartRadius chartCoord
  have h1 : ‖y‖ + P.chartLength ≠ 0 := by positivity
  have h2 : P.chartLength ≠ 0 := hL.ne'
  field_simp
  rw [show ‖y‖ + P.chartLength - ‖y‖ = P.chartLength by ring]
  field_simp

theorem keyVector_typeTwo (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (σ : ℝ) (y : Space) (h0 : κ.label.1 = 0) :
    keyVector P κ A σ y = fun i =>
      (Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2) : ℝ) : ℂ) * Complex.I)) *
      (reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 0 *
          (CellCert.GivenFields.radialVec y i : ℂ) +
        reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 1 *
          (CellCert.GivenFields.polarVecQ y i : ℂ) +
        reducedComps P κ A (chartCoord P y) (CellCert.GivenFields.heightRatio y) 2 *
          (CellCert.GivenFields.azimVecQ y i : ℂ)) := by
  funext i
  have hz : (labelAzimuth P.azimuthOrder κ.label : ℝ) = 0 := by simp [labelAzimuth, h0]
  simp only [keyVector, keyPhase, hz, zero_mul, add_zero]
  rw [← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem streamHeight_deriv (P : ShapeParams) (hP : IsShapeParams P) (A : KeyAmp)
    (hs : IsJoinedSpline 2 2 A.stream) {t : ℝ} (ht : t < 1) (x : ℝ) :
    CellCert.GivenFields.heightDeriv (fun t' x' => polarFactor x' * streamValue P A t' x') t x =
      (((-2 * x : ℝ) : ℂ)) * streamF P A (t, x) + (((1 - x ^ 2 : ℝ) : ℂ)) * fderiv ℝ (streamF P A) (t, x) (0, 1) := by
  have hd : HasFDerivAt (streamF P A) (fderiv ℝ (streamF P A) (t, x)) (t, x) :=
    ((streamF_smooth hP hs).differentiable (by norm_num) (t, x)).hasFDerivAt
  have h1 := line_second hd
  have h2 : HasDerivAt (fun x' : ℝ => (((1 - x' ^ 2 : ℝ)) : ℂ)) (((-2 * x : ℝ)) : ℂ) x := by
    have h := ((hasDerivAt_pow 2 x).const_sub 1).ofReal_comp
    convert h using 1
    push_cast
    ring
  have h3 := h2.mul h1
  have e : (fun x' => polarFactor x' * streamValue P A t x') =
      fun x' => (((1 - x' ^ 2 : ℝ)) : ℂ) * streamF P A (t, x') := by
    funext x'
    rw [streamF_eq P hP A ht x']
    rfl
  unfold CellCert.GivenFields.heightDeriv
  rw [e]
  exact h3.deriv

theorem streamRadial_deriv (P : ShapeParams) (hP : IsShapeParams P) (A : KeyAmp)
    (hs : IsJoinedSpline 2 2 A.stream) (e : ℕ) {t : ℝ} (ht : t < 1) (x : ℝ) :
    deriv (fun t' => CellCert.GivenFields.weightPoly 1 e t' * streamValue P A t' x) t =
      ((deriv (fun s : ℝ => s ^ 1 * (1 - s) ^ e) t : ℝ) : ℂ) * streamF P A (t, x) +
        ((t ^ 1 * (1 - t) ^ e : ℝ) : ℂ) * fderiv ℝ (streamF P A) (t, x) (1, 0) := by
  have hd : HasFDerivAt (streamF P A) (fderiv ℝ (streamF P A) (t, x)) (t, x) :=
    ((streamF_smooth hP hs).differentiable (by norm_num) (t, x)).hasFDerivAt
  have h1 := line_first hd
  have hpd : DifferentiableAt ℝ (fun s : ℝ => s ^ 1 * (1 - s) ^ e) t := by fun_prop
  have h2 := hpd.hasDerivAt.ofReal_comp
  have h3 := h2.mul h1
  have hev : (fun t' => CellCert.GivenFields.weightPoly 1 e t' * streamValue P A t' x) =ᶠ[𝓝 t]
      fun t' => (((t' ^ 1 * (1 - t') ^ e : ℝ)) : ℂ) * streamF P A (t', x) := by
    filter_upwards [Iio_mem_nhds ht] with s hs'
    rw [streamF_eq P hP A hs' x]
    rfl
  rw [hev.deriv_eq]
  exact h3.deriv

end FieldPot

end Internal

end Instantiation

end CellReduction

end Breakdown

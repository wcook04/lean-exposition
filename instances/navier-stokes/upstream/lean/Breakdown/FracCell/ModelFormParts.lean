import Breakdown.FracCell.StClauses
import Breakdown.FracCert.LinearSolveCore
import Breakdown.FracCert.InverseSquare
import Breakdown.FracCert.DriftSymbolWeak
import Breakdown.Cert.ExtendedCoerciveSecondDerivSymm

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

open SteadyCert

namespace ModelFormInternal


def curlGradPart (E D : Space →L[ℝ] Space) (v : Space) : ℝ :=
  ∑ i : Fin 3, ∑ l : Fin 3,
    (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j)
      * entry D i l

theorem coord_apply (E : Space →L[ℝ] Space) (w : Space) (i : Fin 3) :
    E w i = ∑ j : Fin 3, entry E i j * w j := by
  have hw : w = ∑ j : Fin 3, w j • unitVector j := by
    ext a
    simp [unitVector, Fin.sum_univ_three]
    fin_cases a <;> simp
  conv_lhs => rw [hw]
  simp [map_sum, map_smul, entry, mul_comm]

theorem norm_sq_coord (x : Space) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_three, sq_abs]

theorem inner_coord (x y : Space) : inner ℝ x y = x 0 * y 0 + x 1 * y 1 + x 2 * y 2 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem sq_identity (E : Space →L[ℝ] Space) (v : Space) :
    ∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j) ^ 2
      = 2 * ‖E v‖ ^ 2 + (1 / 4 : ℝ) * ∑ m : Fin 3, ‖E (crossVec (unitVector m) v)‖ ^ 2
        + inner ℝ v (E (E v)) - (∑ i : Fin 3, entry E i i) * inner ℝ (E v) v := by
  simp only [norm_sq_coord, inner_coord, coord_apply E]
  simp [Fin.sum_univ_three, permSign, crossVec, unitVector]
  ring


theorem cross_sum (v : Space) : ∑ m : Fin 3, ‖crossVec (unitVector m) v‖ ^ 2 = 2 * ‖v‖ ^ 2 := by
  simp only [norm_sq_coord]
  simp [Fin.sum_univ_three, crossVec, unitVector]
  ring

theorem part_sq_le (E : Space →L[ℝ] Space) (v : Space) (htr : ∑ i : Fin 3, entry E i i = 0) :
    ∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign i j q * v q * entry E l j) ^ 2
      ≤ 7 / 2 * (‖E‖ * ‖v‖) ^ 2 := by
  rw [sq_identity, htr, zero_mul, sub_zero]
  have hu : ‖E v‖ ≤ ‖E‖ * ‖v‖ := E.le_opNorm v
  have huu : ‖E (E v)‖ ≤ ‖E‖ * (‖E‖ * ‖v‖) :=
    (E.le_opNorm _).trans (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
  have hin : inner ℝ v (E (E v)) ≤ ‖v‖ * (‖E‖ * (‖E‖ * ‖v‖)) :=
    (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left huu (norm_nonneg _))
  have hm : ∀ m : Fin 3, ‖E (crossVec (unitVector m) v)‖ ^ 2 ≤ ‖E‖ ^ 2 * ‖crossVec (unitVector m) v‖ ^ 2 := by
    intro m
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (E.le_opNorm _) 2
  have hs : ∑ m : Fin 3, ‖E (crossVec (unitVector m) v)‖ ^ 2 ≤ ‖E‖ ^ 2 * (2 * ‖v‖ ^ 2) := by
    rw [← cross_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun m _ => hm m
  have hu2 : ‖E v‖ ^ 2 ≤ (‖E‖ * ‖v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
  nlinarith

theorem entrySq_eq (D : Space →L[ℝ] Space) : entrySq D = ∑ i : Fin 3, ∑ l : Fin 3, entry D i l ^ 2 := by
  simp only [entrySq, norm_sq_coord, entry, Fin.sum_univ_three]
  ring

theorem part_bound (E D : Space →L[ℝ] Space) (v : Space) (htr : ∑ i : Fin 3, entry E i i = 0) :
    |curlGradPart E D v| ≤ Real.sqrt (7 / 2) * (‖E‖ * ‖v‖) * Real.sqrt (entrySq D) := by
  set T : Fin 3 × Fin 3 → ℝ := fun x =>
    -(∑ j : Fin 3, permSign x.1 x.2 j * (E v) j) + (1 / 2 : ℝ) * ∑ j : Fin 3, ∑ q : Fin 3, permSign x.1 j q * v q * entry E x.2 j
  have h1 : curlGradPart E D v = ∑ x : Fin 3 × Fin 3, T x * entry D x.1 x.2 := by
    rw [Fintype.sum_prod_type]; rfl
  have h2 : ∑ x : Fin 3 × Fin 3, T x ^ 2 ≤ 7 / 2 * (‖E‖ * ‖v‖) ^ 2 := by
    rw [Fintype.sum_prod_type]; exact part_sq_le E v htr
  have h3 : entrySq D = ∑ x : Fin 3 × Fin 3, entry D x.1 x.2 ^ 2 := by
    rw [Fintype.sum_prod_type]; exact entrySq_eq D
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ T (fun x => entry D x.1 x.2)
  have hcs' := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun x => -T x) (fun x => entry D x.1 x.2)
  have hs : Real.sqrt (∑ x : Fin 3 × Fin 3, T x ^ 2) ≤ Real.sqrt (7 / 2) * (‖E‖ * ‖v‖) := by
    rw [← Real.sqrt_sq (mul_nonneg (norm_nonneg E) (norm_nonneg v)), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h2
  simp only [neg_sq, neg_mul, Finset.sum_neg_distrib] at hcs'
  rw [h1, h3, abs_le]
  have hD := Real.sqrt_nonneg (∑ x : Fin 3 × Fin 3, entry D x.1 x.2 ^ 2)
  constructor <;> nlinarith [mul_le_mul_of_nonneg_right hs hD]

theorem entryInner_bound (A B : Space →L[ℝ] Space) :
    |entryInner A B| ≤ Real.sqrt (entrySq A) * Real.sqrt (entrySq B) := by
  unfold entryInner entrySq
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine (Finset.sum_le_sum fun i _ => abs_real_inner_le_norm (A (unitVector i)) (B (unitVector i))).trans ?_
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem curl_sq_le (M : Space →L[ℝ] Space) : ‖curlOf M‖ ^ 2 ≤ 2 * entrySq M := by
  rw [entrySq_eq, norm_sq_coord]
  simp [curlOf, Fin.sum_univ_three, permSign, unitVector]
  nlinarith [sq_nonneg (entry M 2 1 + entry M 1 2), sq_nonneg (entry M 0 2 + entry M 2 0),
    sq_nonneg (entry M 1 0 + entry M 0 1)]

theorem pairIntegral_bound {X a b : Space → ℝ} {K : ℝ} (hK : 0 ≤ K) (hX : Integrable X) (ha : AEStronglyMeasurable a volume)
    (hb : AEStronglyMeasurable b volume) (ha0 : ∀ y, 0 ≤ a y) (hb0 : ∀ y, 0 ≤ b y)
    (hia : Integrable (fun y => a y ^ 2)) (hib : Integrable (fun y => b y ^ 2))
    (hle : ∀ᵐ y ∂volume, |X y| ≤ K * (a y * b y)) :
    |∫ y, X y| ≤ K * (Real.sqrt (∫ y, a y ^ 2) * Real.sqrt (∫ y, b y ^ 2)) := by
  have h2 : ENNReal.ofReal 2 = 2 := by norm_num
  have hma : MemLp a 2 volume := (memLp_two_iff_integrable_sq ha).2 hia
  have hmb : MemLp b 2 volume := (memLp_two_iff_integrable_sq hb).2 hib
  have hab : Integrable (fun y => a y * b y) := hma.integrable_mul hmb
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ ha0) (ae_of_all _ hb0) (by rw [h2]; exact hma) (by rw [h2]; exact hmb)
  simp_rw [Real.rpow_two] at hH
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hH
  calc |∫ y, X y| ≤ ∫ y, |X y| := abs_integral_le_integral_abs
    _ ≤ ∫ y, K * (a y * b y) := integral_mono_ae hX.abs (hab.const_mul K) hle
    _ = K * ∫ y, a y * b y := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hH hK


theorem jForm_sub (S1 S2 Gm1 Gm2 D : Space →L[ℝ] Space) (v : Space) :
    jForm S1 Gm1 D v - jForm S2 Gm2 D v =
      -inner ℝ (curlOf D) ((S1 - S2) (curlOf D)) + curlGradPart (Gm1 - Gm2) D v := by
  simp only [jForm, curlGradPart, entry, ContinuousLinearMap.sub_apply, inner_sub_right, PiLp.sub_apply,
    Fin.sum_univ_three]
  ring

theorem pair_integrable {F E : Space → Space} (hF : MemLp F 2 volume) (hE : MemLp E 2 volume) :
    Integrable (fun y => inner ℝ (F y) (E y)) := by
  refine Integrable.mono' (hF.norm.integrable_mul hE.norm) (AEStronglyMeasurable.inner (𝕜 := ℝ) hF.1 hE.1) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

theorem entrySq_sub_le (A B : Space →L[ℝ] Space) : entrySq (A - B) ≤ 2 * entrySq A + 2 * entrySq B := by
  unfold entrySq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [ContinuousLinearMap.sub_apply]
  have h := norm_sub_le (A (unitVector i)) (B (unitVector i))
  nlinarith [norm_nonneg (A (unitVector i) - B (unitVector i)), norm_nonneg (A (unitVector i)),
    norm_nonneg (B (unitVector i)), sq_nonneg (‖A (unitVector i)‖ - ‖B (unitVector i)‖)]

theorem entryInner_pair {G X : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hX : AEStronglyMeasurable X volume) (hGi : Integrable (fun y => entrySq (G y)))
    (hXi : Integrable (fun y => entrySq (X y))) :
    Integrable (fun y => entryInner (G y) (X y)) ∧
      |∫ y, entryInner (G y) (X y)| ≤ Real.sqrt (∫ y, entrySq (G y)) * Real.sqrt (∫ y, entrySq (X y)) := by
  have hm : AEStronglyMeasurable (fun y => entryInner (G y) (X y)) volume := by
    unfold entryInner
    have h := Finset.aestronglyMeasurable_sum (μ := volume) Finset.univ (fun i _ =>
      AEStronglyMeasurable.inner (𝕜 := ℝ) (hG.apply_continuousLinearMap (unitVector i))
        (hX.apply_continuousLinearMap (unitVector i)))
    refine h.congr (ae_of_all _ fun y => ?_)
    simp only [Finset.sum_apply]
  have ha : AEStronglyMeasurable (fun y => Real.sqrt (entrySq (G y))) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hGi.aestronglyMeasurable
  have hb : AEStronglyMeasurable (fun y => Real.sqrt (entrySq (X y))) volume :=
    Real.continuous_sqrt.comp_aestronglyMeasurable hXi.aestronglyMeasurable
  have hia : Integrable (fun y => Real.sqrt (entrySq (G y)) ^ 2) :=
    hGi.congr (ae_of_all _ fun y => (Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _)).symm)
  have hib : Integrable (fun y => Real.sqrt (entrySq (X y)) ^ 2) :=
    hXi.congr (ae_of_all _ fun y => (Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _)).symm)
  have hma : MemLp (fun y => Real.sqrt (entrySq (G y))) 2 volume := (memLp_two_iff_integrable_sq ha).2 hia
  have hmb : MemLp (fun y => Real.sqrt (entrySq (X y))) 2 volume := (memLp_two_iff_integrable_sq hb).2 hib
  have hint : Integrable (fun y => entryInner (G y) (X y)) :=
    (hma.integrable_mul hmb).mono' hm (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs]; exact entryInner_bound _ _)
  refine ⟨hint, ?_⟩
  have h := pairIntegral_bound zero_le_one hint ha hb (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) hia hib
    (ae_of_all _ fun y => by rw [one_mul]; exact entryInner_bound _ _)
  have e1 : ∫ y, Real.sqrt (entrySq (G y)) ^ 2 = ∫ y, entrySq (G y) :=
    integral_congr_ae (ae_of_all _ fun y => Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _))
  have e2 : ∫ y, Real.sqrt (entrySq (X y)) ^ 2 = ∫ y, entrySq (X y) :=
    integral_congr_ae (ae_of_all _ fun y => Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _))
  rw [e1, e2, one_mul] at h
  exact h

theorem formOf_congr {k N : ℕ} (c : FracCellData k N) (α : ℝ) (v : Space → Space) (κ : Fin k → ℝ)
    {G G' : Space → (Space →L[ℝ] Space)} {H H' : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hG : G =ᵐ[volume] G') (hH : H =ᵐ[volume] H') : c.formOf α v G H κ = c.formOf α v G' H' κ := by
  unfold FracCellData.formOf SteadyCert.weightedEnergy
  have e1 : ∫ y, ‖secondTrace (H y)‖ ^ 2 = ∫ y, ‖secondTrace (H' y)‖ ^ 2 :=
    integral_congr_ae (hH.mono fun y hy => by simp only [hy])
  have e2 : ∫ y, c.weight y * entrySq (G y) = ∫ y, c.weight y * entrySq (G' y) :=
    integral_congr_ae (hG.mono fun y hy => by simp only [hy])
  have e3 : ∫ y, fullSecondSq (H y) = ∫ y, fullSecondSq (H' y) :=
    integral_congr_ae (hH.mono fun y hy => by simp only [hy])
  have e4 : ∫ y, curlGradSq (H y) = ∫ y, curlGradSq (H' y) :=
    integral_congr_ae (hH.mono fun y hy => by simp only [hy])
  have e5 : ∫ y, ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G y)‖ ^ 2
        + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G y)) =
      ∫ y, ((1 - 3 / (4 * α) - c.curlWeight) * ‖curlOf (G' y)‖ ^ 2
        + (c.curlWeight - c.coercivity * c.weight y) * entrySq (G' y)) :=
    integral_congr_ae (hG.mono fun y hy => by simp only [hy])
  have e6 : ∫ y, jForm (c.modelStrain y) (c.modelCurlGrad y) (G y) (v y) =
      ∫ y, jForm (c.modelStrain y) (c.modelCurlGrad y) (G' y) (v y) :=
    integral_congr_ae (hG.mono fun y hy => by simp only [hy])
  have e7 : ∀ i, ∫ y, entryInner (G y) (c.modelActuatorGrad i y) = ∫ y, entryInner (G' y) (c.modelActuatorGrad i y) :=
    fun i => integral_congr_ae (hG.mono fun y hy => by simp only [hy])
  rw [e1, e2, e3, e4, e5, e6]
  simp only [e7]


theorem continuous_curlOf : Continuous curlOf := by
  unfold curlOf entry
  fun_prop

theorem continuous_curlGradMatrix : Continuous curlGradMatrix := by
  unfold curlGradMatrix
  fun_prop

theorem continuous_symPart : Continuous symPart := by
  unfold symPart
  exact (continuous_const (y := (1 / 2 : ℝ))).smul (continuous_id.add
    (ContinuousLinearMap.adjoint : (Space →L[ℝ] Space) ≃ₗᵢ⋆[ℝ] (Space →L[ℝ] Space)).continuous)

theorem continuous_part : Continuous (fun x : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) × Space =>
    curlGradPart x.1 x.2.1 x.2.2) := by
  unfold curlGradPart entry
  fun_prop

theorem norm_symPart_le (M : Space →L[ℝ] Space) : ‖symPart M‖ ≤ ‖M‖ := by
  unfold symPart
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  have h := norm_add_le M (ContinuousLinearMap.adjoint M)
  rw [LinearIsometryEquiv.norm_map] at h
  linarith

theorem norm_unitVector (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem abs_permSign_le (i j l : Fin 3) : |permSign i j l| ≤ 1 := by
  unfold permSign
  split_ifs <;> norm_num

theorem norm_curlGradMatrix_le (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖curlGradMatrix H‖ ≤ 81 * ‖H‖ := by
  have hc : ∀ j l : Fin 3, |∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q| ≤ 9 * ‖H‖ := by
    intro j l
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have h1 : ∀ b q : Fin 3, |permSign j b q * H (unitVector l) (unitVector b) q| ≤ ‖H‖ := by
      intro b q
      rw [abs_mul]
      have e1 : |H (unitVector l) (unitVector b) q| ≤ ‖H‖ := by
        have := PiLp.norm_apply_le (H (unitVector l) (unitVector b)) q
        rw [Real.norm_eq_abs] at this
        refine this.trans ?_
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_unitVector, mul_one]
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [norm_unitVector, mul_one]
      nlinarith [abs_permSign_le j b q, abs_nonneg (permSign j b q), abs_nonneg (H (unitVector l) (unitVector b) q)]
    calc ∑ b : Fin 3, |∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q|
        ≤ ∑ b : Fin 3, ∑ q : Fin 3, ‖H‖ :=
          Finset.sum_le_sum fun b _ => (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => h1 b q)
      _ = 9 * ‖H‖ := by simp [Fin.sum_univ_three]; ring
  unfold curlGradMatrix
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖∑ l : Fin 3, (∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q)
        • (innerSL ℝ (unitVector l)).smulRight (unitVector j)‖
      ≤ ∑ j : Fin 3, ∑ l : Fin 3, 9 * ‖H‖ := by
        refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_smul, Real.norm_eq_abs]
        have hn : ‖(innerSL ℝ (unitVector l)).smulRight (unitVector j)‖ ≤ 1 := by
          refine (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans ?_
          rw [innerSL_apply_norm, norm_unitVector, norm_unitVector, one_mul]
        have := hc j l
        nlinarith [norm_nonneg ((innerSL ℝ (unitVector l)).smulRight (unitVector j)), abs_nonneg
          (∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q), norm_nonneg H]
    _ = 81 * ‖H‖ := by simp [Fin.sum_univ_three]; ring

theorem trace_curlGradMatrix (H : Space →L[ℝ] Space →L[ℝ] Space)
    (hH : ∀ i j : Fin 3, H (unitVector i) (unitVector j) = H (unitVector j) (unitVector i)) :
    ∑ i : Fin 3, entry (curlGradMatrix H) i i = 0 := by
  have h10 := hH 1 0
  have h20 := hH 2 0
  have h21 := hH 2 1
  simp only [unitVector] at h10 h20 h21
  simp [entry, curlGradMatrix, Fin.sum_univ_three, permSign, unitVector, EuclideanSpace.inner_single_left,
    h10, h20, h21]
  ring

theorem second_symm {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∀ᵐ y ∂volume, ∀ i j : Fin 3,
      c.centreSecond y (unitVector i) (unitVector j) = c.centreSecond y (unitVector j) (unitVector i) := by
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  have hCc0 : 0 ≤ Cc := by
    have h := (hCc 0).1
    have hp : 0 < (1 + ‖(0 : Space)‖) ^ (-(1 : ℝ)) := by positivity
    nlinarith [norm_nonneg (c.centre 0)]
  have hm := hc.centre_second.2
  have hloc : ∀ i j : Fin 3, LocallyIntegrable (fun y => c.centreSecond y (unitVector i) (unitVector j)) volume := by
    intro i j
    rw [locallyIntegrable_iff]
    intro K hK
    refine Measure.integrableOn_of_bounded (M := Cc) hK.measure_lt_top.ne
      ((hm.apply_continuousLinearMap _).apply_continuousLinearMap _) (ae_of_all _ fun y => ?_)
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_unitVector, mul_one]
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    rw [norm_unitVector, mul_one]
    refine (hCc y).2.2.trans ?_
    have hp : (1 + ‖y‖) ^ (-(3 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    nlinarith
  have hij : ∀ i j : Fin 3, ∀ᵐ y ∂volume,
      c.centreSecond y (unitVector j) (unitVector i) = c.centreSecond y (unitVector i) (unitVector j) := by
    intro i j
    refine ae_eq_of_integral_contDiff_smul_eq (hloc j i) (hloc i j) fun φ hφ hcφ => ?_
    have e1 := hc.centre_second.1 φ ⟨hφ, hcφ⟩ i j
    have e2 := hc.centre_second.1 φ ⟨hφ, hcφ⟩ j i
    have p1 : ∫ y, fderiv ℝ φ y (unitVector j) • c.centreGrad y (unitVector i) =
        -∫ y, fderiv ℝ (fderiv ℝ φ) y (unitVector j) (unitVector i) • c.centre y :=
      CoerciveWeak.Internal.SecondDerivSymm.pairing_eq hφ hcφ hc.centre_smooth j i
    have p2 : ∫ y, fderiv ℝ φ y (unitVector i) • c.centreGrad y (unitVector j) =
        -∫ y, fderiv ℝ (fderiv ℝ φ) y (unitVector i) (unitVector j) • c.centre y :=
      CoerciveWeak.Internal.SecondDerivSymm.pairing_eq hφ hcφ hc.centre_smooth i j
    have s : ∫ y, fderiv ℝ (fderiv ℝ φ) y (unitVector j) (unitVector i) • c.centre y =
        ∫ y, fderiv ℝ (fderiv ℝ φ) y (unitVector i) (unitVector j) • c.centre y := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [(hφ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) (unitVector j) (unitVector i)]
    have q1 : ∫ y, φ y • c.centreSecond y (unitVector j) (unitVector i) =
        -∫ y, fderiv ℝ φ y (unitVector j) • c.centreGrad y (unitVector i) := by rw [e1, neg_neg]
    have q2 : ∫ y, φ y • c.centreSecond y (unitVector i) (unitVector j) =
        -∫ y, fderiv ℝ φ y (unitVector i) • c.centreGrad y (unitVector j) := by rw [e2, neg_neg]
    rw [q1, q2, p1, p2, s]
  have hall : ∀ᵐ y ∂volume, ∀ i j : Fin 3,
      c.centreSecond y (unitVector j) (unitVector i) = c.centreSecond y (unitVector i) (unitVector j) := by
    rw [ae_all_iff]
    intro i
    rw [ae_all_iff]
    exact hij i
  filter_upwards [hall] with y hy i j
  exact hy j i

theorem trace_centre {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∀ᵐ y ∂volume, ∑ i : Fin 3, entry (c.centreCurlGrad y) i i = 0 := by
  filter_upwards [second_symm hc] with y hy
  exact trace_curlGradMatrix _ hy

theorem trace_zero {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∀ᵐ y ∂volume, ∑ i : Fin 3, entry (c.curlGradError y) i i = 0 := by
  filter_upwards [trace_centre hc] with y hy
  have hm := hc.modelCurlGrad_trace y
  have e : ∑ i : Fin 3, entry (c.curlGradError y) i i =
      ∑ i : Fin 3, entry (c.centreCurlGrad y) i i - ∑ i : Fin 3, entry (c.modelCurlGrad y) i i := by
    rw [← Finset.sum_sub_distrib]
    rfl
  rw [e, hy, hm, sub_zero]

theorem jForm_eq (S Gm D : Space →L[ℝ] Space) (v : Space) :
    jForm S Gm D v = -inner ℝ (curlOf D) (S (curlOf D)) + curlGradPart Gm D v := rfl

theorem part_measurable {E D : Space → (Space →L[ℝ] Space)} {w : Space → Space}
    (hE : AEStronglyMeasurable E volume) (hD : AEStronglyMeasurable D volume) (hw : AEStronglyMeasurable w volume) :
    AEStronglyMeasurable (fun y => curlGradPart (E y) (D y) (w y)) volume := by
  have h := continuous_part.comp_aestronglyMeasurable (hE.prodMk (hD.prodMk hw))
  simpa only [Function.comp_def] using h

theorem int_of_bound {X a b : Space → ℝ} {K : ℝ} (hX : AEStronglyMeasurable X volume)
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume)
    (hia : Integrable (fun y => a y ^ 2)) (hib : Integrable (fun y => b y ^ 2))
    (hle : ∀ᵐ y ∂volume, |X y| ≤ K * (a y * b y)) : Integrable X := by
  have hma : MemLp a 2 volume := (memLp_two_iff_integrable_sq ha).2 hia
  have hmb : MemLp b 2 volume := (memLp_two_iff_integrable_sq hb).2 hib
  exact ((hma.integrable_mul hmb).const_mul K).mono' hX (hle.mono fun y hy => by rwa [Real.norm_eq_abs])

theorem centre_nonneg {k N : ℕ} {c : FracCellData k N} {Cc : ℝ}
    (hCc : ∀ y, ‖c.centre y‖ ≤ Cc * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖c.centreGrad y‖ ≤ Cc * (1 + ‖y‖) ^ (-(2 : ℝ)) ∧ ‖c.centreSecond y‖ ≤ Cc * (1 + ‖y‖) ^ (-(3 : ℝ))) :
    0 ≤ Cc := by
  have h := (hCc 0).1
  have hp : 0 < (1 + ‖(0 : Space)‖) ^ (-(1 : ℝ)) := by positivity
  nlinarith [norm_nonneg (c.centre 0)]

theorem rpow_neg_le_one (y : Space) (s : ℝ) (hs : 0 ≤ s) : (1 + ‖y‖) ^ (-s) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by linarith)

theorem quad_integrable {S : Space → (Space →L[ℝ] Space)} {B : ℝ} (hmS : AEStronglyMeasurable S volume)
    (hB0 : 0 ≤ B) (hB : ∀ y, ‖S y‖ ≤ B) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    Integrable (fun y => inner ℝ (curlOf (G y)) (S y (curlOf (G y)))) := by
  have hmω : AEStronglyMeasurable (fun y => curlOf (G y)) volume :=
    continuous_curlOf.comp_aestronglyMeasurable hs.measurable_gradient
  have hm : AEStronglyMeasurable (fun y => inner ℝ (curlOf (G y)) (S y (curlOf (G y)))) volume :=
    AEStronglyMeasurable.inner (𝕜 := ℝ) hmω
      ((continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable (hmS.prodMk hmω))
  refine (hs.gradient_two.const_mul (2 * B)).mono' hm (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs]
  have h1 : ‖S y (curlOf (G y))‖ ≤ B * ‖curlOf (G y)‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right (hB y) (norm_nonneg _))
  calc |inner ℝ (curlOf (G y)) (S y (curlOf (G y)))| ≤ ‖curlOf (G y)‖ * ‖S y (curlOf (G y))‖ :=
        abs_real_inner_le_norm _ _
    _ ≤ ‖curlOf (G y)‖ * (B * ‖curlOf (G y)‖) := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ = B * ‖curlOf (G y)‖ ^ 2 := by ring
    _ ≤ B * (2 * entrySq (G y)) := mul_le_mul_of_nonneg_left (curl_sq_le _) hB0
    _ = 2 * B * entrySq (G y) := by ring

theorem centreStrain_measurable {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    Continuous c.centreStrain :=
  continuous_symPart.comp (hc.centre_smooth.continuous_fderiv one_ne_zero)

theorem centreStrain_bound {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c) :
    ∃ B, 0 ≤ B ∧ (∀ y, ‖c.centreStrain y‖ ≤ B) ∧ ∀ y, ‖c.centreSecond y‖ ≤ B * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
  obtain ⟨Cc, hCc⟩ := hc.centre_bounds
  have hCc0 := centre_nonneg hCc
  refine ⟨Cc, hCc0, fun y => ?_, fun y => (hCc y).2.2⟩
  exact (norm_symPart_le _).trans ((hCc y).2.1.trans (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 2 (by norm_num))))

theorem strain_integrable {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) :
    Integrable (fun y => inner ℝ (curlOf (G y)) (c.strainError y (curlOf (G y)))) := by
  obtain ⟨Cc, hCc0, hCst, -⟩ := centreStrain_bound hc
  obtain ⟨Cm, hCm⟩ := hc.model_bounded
  have hmS : AEStronglyMeasurable (fun y => c.strainError y) volume :=
    (centreStrain_measurable hc).aestronglyMeasurable.sub hc.model_measurable.2.2.1
  refine quad_integrable hmS (by positivity : (0 : ℝ) ≤ Cc + |Cm|) (fun y => ?_) hs
  by_cases hy : y ∈ c.cellRegion
  · show ‖c.centreStrain y - c.modelStrain y‖ ≤ _
    exact (norm_sub_le _ _).trans (add_le_add (hCst y) ((hCm y hy).2.2.1.trans (le_abs_self _)))
  · show ‖c.centreStrain y - c.modelStrain y‖ ≤ _
    rw [(hc.model_outside y hy).1, sub_self, norm_zero]
    positivity

theorem curlGradError_data {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) :
    AEStronglyMeasurable (fun y => ‖c.curlGradError y‖ * ‖v y‖) volume ∧
      Integrable (fun y => (‖c.curlGradError y‖ * ‖v y‖) ^ 2) ∧
      Integrable (fun y => curlGradPart (c.curlGradError y) (G y) (v y)) := by
  obtain ⟨Cc, hCc0, -, hCst⟩ := centreStrain_bound hc
  obtain ⟨Cm, hCm⟩ := hc.model_bounded
  set B := 81 * Cc + |Cm| with hBdef
  have hB0 : 0 ≤ B := by positivity
  have hmE : AEStronglyMeasurable (fun y => c.curlGradError y) volume :=
    (continuous_curlGradMatrix.comp_aestronglyMeasurable hc.centre_second.2).sub hc.model_measurable.2.2.2
  have hzero : ∀ y ∉ c.cellRegion, c.curlGradError y = 0 := by
    intro y hy
    show c.centreCurlGrad y - c.modelCurlGrad y = 0
    rw [(hc.model_outside y hy).2, sub_self]
  have hB : ∀ y, ‖c.curlGradError y‖ ≤ B := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · show ‖c.centreCurlGrad y - c.modelCurlGrad y‖ ≤ _
      refine (norm_sub_le _ _).trans (add_le_add ?_ ((hCm y hy).2.2.2.trans (le_abs_self _)))
      refine (norm_curlGradMatrix_le _).trans ?_
      have h2 := (hCst y).trans (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 3 (by norm_num)))
      linarith
    · rw [hzero y hy, norm_zero]
      exact hB0
  have hmA : AEStronglyMeasurable (fun y => ‖c.curlGradError y‖ * ‖v y‖) volume :=
    hmE.norm.mul hs.measurable_velocity.norm
  have hfin : volume c.cellRegion < ⊤ := hc.cellRegion_bounded.measure_lt_top
  have : IsFiniteMeasure (volume.restrict c.cellRegion) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  have h2 : MemLp v 2 (volume.restrict c.cellRegion) :=
    (hs.velocity_six.restrict _).mono_exponent (by norm_num)
  have hvi : IntegrableOn (fun y => ‖v y‖ ^ 2) c.cellRegion := (memLp_two_iff_integrable_sq_norm h2.1).1 h2
  have hvi' : IntegrableOn (fun y => B ^ 2 * ‖v y‖ ^ 2) c.cellRegion := hvi.const_mul (B ^ 2)
  have hind : Integrable (c.cellRegion.indicator (fun y => B ^ 2 * ‖v y‖ ^ 2)) :=
    hvi'.integrable_indicator hc.cellRegion_measurable
  have hAi : Integrable (fun y => (‖c.curlGradError y‖ * ‖v y‖) ^ 2) := by
    refine hind.mono' (hmA.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases hy : y ∈ c.cellRegion
    · rw [Set.indicator_of_mem hy, mul_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hB y) 2) (by positivity)
    · simp [hy, hzero y hy]
  refine ⟨hmA, hAi, ?_⟩
  have hGi := hs.gradient_two
  refine int_of_bound (K := Real.sqrt (7 / 2)) (b := fun y => Real.sqrt (entrySq (G y)))
    (part_measurable hmE hs.measurable_gradient hs.measurable_velocity)
    hmA (Real.continuous_sqrt.comp_aestronglyMeasurable hGi.aestronglyMeasurable) hAi
    (hGi.congr (ae_of_all _ fun y => (Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _)).symm)) ?_
  filter_upwards [trace_zero hc] with y hy
  rw [← mul_assoc]
  exact part_bound _ _ _ hy

theorem centre_integrable {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFracCell α c)
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField c.order v G H) :
    Integrable (fun y => jForm (c.centreStrain y) (c.centreCurlGrad y) (G y) (v y)) := by
  obtain ⟨Cc, hCc0, hCst, hCH⟩ := centreStrain_bound hc
  have hGi := hs.gradient_two
  have h1 := quad_integrable (centreStrain_measurable hc).aestronglyMeasurable hCc0 hCst hs
  have hmE : AEStronglyMeasurable (fun y => c.centreCurlGrad y) volume :=
    continuous_curlGradMatrix.comp_aestronglyMeasurable hc.centre_second.2
  have hmA : AEStronglyMeasurable (fun y => ‖c.centreCurlGrad y‖ * ‖v y‖) volume :=
    hmE.norm.mul hs.measurable_velocity.norm
  obtain ⟨hIi, -⟩ := inverseSquareBound v G hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  have hAi : Integrable (fun y => (‖c.centreCurlGrad y‖ * ‖v y‖) ^ 2) := by
    refine (hIi.const_mul ((81 * Cc) ^ 2)).mono' (hmA.pow 2) ?_
    filter_upwards [hne] with y hy0
    have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hr : (1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖ ≤ 1 := by
      have e : (1 + ‖y‖) ^ (-(3 : ℝ)) = ((1 + ‖y‖) ^ 3)⁻¹ := by
        rw [Real.rpow_neg (by positivity)]
        norm_cast
      rw [e, inv_mul_le_iff₀ (by positivity), mul_one]
      have h1 : ‖y‖ ≤ 1 + ‖y‖ := by linarith
      have h3 : 1 + ‖y‖ ≤ (1 + ‖y‖) ^ 3 := le_self_pow₀ (by linarith [norm_nonneg y]) (by norm_num)
      linarith
    have hb : ‖c.centreCurlGrad y‖ * ‖y‖ ≤ 81 * Cc := by
      have h := (norm_curlGradMatrix_le (c.centreSecond y)).trans
        (mul_le_mul_of_nonneg_left (hCH y) (by norm_num))
      have h' : ‖c.centreCurlGrad y‖ ≤ 81 * (Cc * (1 + ‖y‖) ^ (-(3 : ℝ))) := h
      calc ‖c.centreCurlGrad y‖ * ‖y‖ ≤ 81 * (Cc * (1 + ‖y‖) ^ (-(3 : ℝ))) * ‖y‖ :=
            mul_le_mul_of_nonneg_right h' hy.le
        _ = 81 * Cc * ((1 + ‖y‖) ^ (-(3 : ℝ)) * ‖y‖) := by ring
        _ ≤ 81 * Cc * 1 := mul_le_mul_of_nonneg_left hr (by positivity)
        _ = 81 * Cc := mul_one _
    have hb' : ‖c.centreCurlGrad y‖ ≤ 81 * Cc / ‖y‖ := by rw [le_div_iff₀ hy]; exact hb
    calc (‖c.centreCurlGrad y‖ * ‖v y‖) ^ 2 = ‖c.centreCurlGrad y‖ ^ 2 * ‖v y‖ ^ 2 := mul_pow _ _ _
      _ ≤ (81 * Cc / ‖y‖) ^ 2 * ‖v y‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hb' 2) (sq_nonneg _)
      _ = (81 * Cc) ^ 2 * (‖v y‖ ^ 2 / ‖y‖ ^ 2) := by rw [div_pow]; ring
  have h2 : Integrable (fun y => curlGradPart (c.centreCurlGrad y) (G y) (v y)) := by
    refine int_of_bound (K := Real.sqrt (7 / 2)) (b := fun y => Real.sqrt (entrySq (G y)))
      (part_measurable hmE hs.measurable_gradient hs.measurable_velocity)
      hmA (Real.continuous_sqrt.comp_aestronglyMeasurable hGi.aestronglyMeasurable) hAi
      (hGi.congr (ae_of_all _ fun y => (Real.sq_sqrt (LinearSolveCore.entrySq_nonneg' _)).symm)) ?_
    filter_upwards [trace_centre hc] with y hy
    rw [← mul_assoc]
    exact part_bound _ _ _ hy
  refine (h1.neg.add h2).congr (ae_of_all _ fun y => ?_)
  simp only [Pi.add_apply, Pi.neg_apply]
  exact (jForm_eq _ _ _ _).symm

end ModelFormInternal

end CellCert

end Breakdown

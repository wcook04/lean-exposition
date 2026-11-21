import Breakdown.FracCell.LayoutRowValuePressure
import Breakdown.FracCell.LowVelocityExpansion
import Breakdown.FracCell.CellDensityModesWeak
import Breakdown.FracCell.LayoutRowVolumeSplit
import Breakdown.FracCell.LayoutRowViscousSides

open MeasureTheory Finset

noncomputable section

namespace Breakdown.FracInternal.LayoutRowVolume

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly CellCert.CellEnergy.TopFormInternal CellCert.CellEnergy.LowVelocityExpansion.Internal
  LayoutRowParts FracInternal.CellDensityModesMirror FracInternal.CellDensityModesWeak
  FracInternal.LayoutRowVolumeSplit

theorem basisVal_eq (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : basisVal B j l p = basisC B j l p := rfl

theorem weight_mul {K : CellBox} {X P : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : ((rHat K p : ℝ) : ℂ) * X p = P p) : (p.1 : ℂ) * X p = (K.lineWeight p.1 : ℂ) * P p := by
  rw [← h]
  by_cases hw : K.lineWeight p.1 = 0
  · have h0 : p.1 = 0 := by
      unfold CellBox.lineWeight at hw
      split_ifs at hw with h1
      · exact hw
      · exact absurd hw one_ne_zero
    have hw0 : K.lineWeight 0 = 0 := h0 ▸ hw
    simp [h0, hw0]
  · unfold rHat
    push_cast
    have hw' : (K.lineWeight p.1 : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp

theorem poly_conj {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') :
    (fun p => (starRingEnd ℂ) (P p)) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun j l => (starRingEnd ℂ) (c j l), fun p => ?_⟩
  show (starRingEnd ℂ) (P p) = _
  rw [hc p]
  simp only [map_sum, map_mul, map_pow, Complex.conj_ofReal]

theorem poly_pairing {K : CellBox} {B : CellBases} (hB : IsCellBases K B) {d : ℕ} {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hX : ∃ P ∈ polyFn d d, ∀ p ∈ K.rect, ((rHat K p : ℝ) : ℂ) * X p = P p) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * F p * X p := by
  obtain ⟨P, hP, hPX⟩ := hX
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  set Q : ℝ × ℝ → ℂ := fun p => (starRingEnd ℂ) (P p) with hQdef
  have hQ : Q ∈ polyFn d d := poly_conj hP
  have e1 : ∀ j l : ℕ, (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) =
      (starRingEnd ℂ) (K.pairOn K.lineWeightFn Q (basisC B j l)) := by
    intro j l
    rw [pair_def, ← integral_conj]
    refine setIntegral_congr_fun hrm fun p hp => ?_
    have h := weight_mul (hPX p hp)
    simp only [hQdef, basisVal_eq, basisC, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination ((CellEnergy.basisFn B j l p : ℝ) : ℂ) * h
  have e2 : (∫ p in K.rect, (p.1 : ℂ) * F p * X p) = K.pairOn K.lineWeightFn F Q := by
    rw [pair_def]
    refine setIntegral_congr_fun hrm fun p hp => ?_
    have h := weight_mul (hPX p hp)
    simp only [hQdef, Complex.conj_conj]
    linear_combination F p * h
  have hrec := poly_recon K hB hQ
  have hQf : Q = fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p := funext hrec
  have hcont : ∀ i ∈ range (d + 1), Continuous (fun p => ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p) := fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)
  rw [e2, hQf, pair_sum_right K _ hF hcont]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sum_right K _ hF (g := fun k p => K.pairOn K.lineWeightFn Q (basisC B j k) * basisC B j k p)
    (fun k _ => continuous_const.mul (basisC_cont B j k))]
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pair_smul_right, e1, coef_eq, coef_eq]

theorem proj_pairing {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (d : ℕ) {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (hX : IntegrableOn X K.rect) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * K.proj d d F p * X p := by
  have hint : ∀ j l : ℕ, IntegrableOn (fun p => (p.1 : ℂ) * basisVal B j l p * X p) K.rect := by
    intro j l
    have hc : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * basisVal B j l p) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul (basisC_cont B j l)
    exact hX.continuousOn_mul hc.continuousOn (rect_compact K)
  have e : ∀ p, (p.1 : ℂ) * K.proj d d F p * X p = ∑ j ∈ range (d + 1), ∑ l ∈ range (d + 1),
      B.coef K F j l * ((p.1 : ℂ) * basisVal B j l p * X p) := by
    intro p
    rw [proj_expand K hB hF d d p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [basisVal_eq]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hint j l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint _ l).const_mul _, integral_const_mul]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring


theorem mirror_sum {ι : Type} (s : Finset ι) (f : ι → Space) : mirror (∑ i ∈ s, f i) = ∑ i ∈ s, mirror (f i) := by
  rw [← mirror_coe]
  exact map_sum _ _ _

theorem mirror_smul (r : ℝ) (u : Space) : mirror (r • u) = r • mirror u := by
  rw [← mirror_coe]; exact map_smul _ _ _

theorem mirror_add (u w : Space) : mirror (u + w) = mirror u + mirror w := by
  rw [← mirror_coe]; exact map_add _ _ _

theorem mirror_sub (u w : Space) : mirror (u - w) = mirror u - mirror w := by
  rw [← mirror_coe]; exact map_sub _ _ _

theorem turn_mirror (u : Space) : axialTurn (mirror u) = mirror (axialTurn u) := by
  ext i; fin_cases i <;> simp [axialTurn, mirror]

theorem cross_mirror_neg (u w : Space) : crossVec (-mirror u) (mirror w) = mirror (crossVec u w) := by
  ext i; rw [mirror_apply]; fin_cases i <;> simp [crossVec, mirror_apply, sgn] <;> ring

theorem curl_conj {M' M : Space →L[ℝ] Space} (h : ∀ u, M' u = mirror (M (mirror u))) :
    curlOf M' = -mirror (curlOf M) := by
  ext i
  rw [PiLp.neg_apply, mirror_apply, curl_apply, curl_apply]
  simp only [entry_conj h, Fin.sum_univ_three, permSign, sgn]
  fin_cases i <;> simp <;> ring

theorem drift_mirror {α t : ℝ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {y : Space}
    (hv : v (mirror y) = mirror (v y)) (hG : ∀ u, G (mirror y) u = mirror (G y (mirror u))) :
    driftField α t v G (mirror y) = mirror (driftField α t v G y) := by
  simp only [driftField, hv, hG, mirror_mirror, turn_mirror, mirror_add, mirror_smul, mirror_sub]

theorem frameUnit_mirror (θ : ℝ) (a : Fin 3) : mirror (frameUnit θ a) = sgn a • frameUnit θ a := by
  fin_cases a <;> ext i <;> fin_cases i <;> simp [frameUnit, radialUnit, angularUnit, axialUnit, mirror, sgn]

theorem cartOfFrame_sgn (θ : ℝ) (w : Fin 3 → ℝ) :
    cartOfFrame θ (fun a => sgn a * w a) = mirror (cartOfFrame θ w) := by
  unfold cartOfFrame
  rw [mirror_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [mirror_smul, frameUnit_mirror, smul_smul, mul_comm]

theorem inner_mirror_right (u w : Space) : inner ℝ u (mirror w) = inner ℝ (mirror u) w := by
  rw [← LayoutRowModes.mirror_inner (mirror u) w, mirror_mirror]

theorem cartOp_sgn (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (u : Space) :
    cartOpOfFrame θ (fun a b => sgn a * sgn b * M a b) u = mirror (cartOpOfFrame θ M (mirror u)) := by
  unfold cartOpOfFrame
  simp only [ContinuousLinearMap.sum_apply, FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply, mirror_sum, mirror_smul, inner_mirror_right, frameUnit_mirror, real_inner_smul_left,
    smul_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  ring

theorem angle_mirror (y : Space) : cylAngle (mirror y) = cylAngle y := by
  simp [cylAngle, mirror_apply, sgn]

theorem sign_mirror {y : Space} (hy : cylHeight y ≠ 0) (a : Fin 3) :
    mirrorSign (mirror y) a = sgn a * mirrorSign y a := by
  have e : cylHeight (mirror y) = -cylHeight y := by simp [cylHeight, mirror]
  unfold mirrorSign
  rw [e]
  rcases lt_or_gt_of_ne hy with h | h
  · have h' : ¬ (-cylHeight y < 0) := by linarith
    fin_cases a <;> simp [sgn, h, h']
  · have h' : -cylHeight y < 0 := by linarith
    have h'' : ¬ (cylHeight y < 0) := by linarith
    fin_cases a <;> simp [sgn, h', h'']

theorem lowV_mirror {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (v : Space → Space)
    {y : Space} (hy : cylHeight y ≠ 0) :
    lowVelocityField c K S v (mirror y) = mirror (lowVelocityField c K S v y) := by
  unfold lowVelocityField
  rw [angle_mirror, CellDensityModesSolid.mirror_radius, CellDensityModesSolid.mirror_height, ← cartOfFrame_sgn]
  congr 1
  funext a
  rw [sign_mirror hy]
  ring

theorem lowG_mirror {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (G : Space → (Space →L[ℝ] Space)) {y : Space} (hy : cylHeight y ≠ 0) (u : Space) :
    lowGradField c K S G (mirror y) u = mirror (lowGradField c K S G y (mirror u)) := by
  unfold lowGradField
  rw [angle_mirror, CellDensityModesSolid.mirror_radius, CellDensityModesSolid.mirror_height, ← cartOp_sgn]
  congr 2
  funext a b
  rw [sign_mirror hy, sign_mirror hy]
  ring

theorem lowTransport_pt {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (α : ℝ)
    (x : FieldTuple k) {y : Space} (hy : cylHeight y ≠ 0) (hv : x.1 (mirror y) = mirror (x.1 y))
    (hG : ∀ u, x.2.1 (mirror y) u = mirror (x.2.1 y (mirror u)))
    (hV : c.modelVelocity (mirror y) = mirror (c.modelVelocity y))
    (hW : c.modelCurl (mirror y) = -mirror (c.modelCurl y)) :
    LayoutRowParts.lowTransport c K S α x (mirror y) = mirror (LayoutRowParts.lowTransport c K S α x y) := by
  unfold LayoutRowParts.lowTransport
  rw [drift_mirror hv hG, curl_conj (lowG_mirror c K S x.2.1 hy), hV, hW, lowV_mirror c K S x.1 hy,
    cross_mirror_neg, cross_mirror_neg, mirror_add, mirror_add]

theorem lowTransport_mirror {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) :
    ∀ᵐ y ∂volume, y ∈ K.solid → inner ℝ (LayoutRowParts.lowTransport c K S α x (mirror y)) (c.row a (mirror y)) =
      inner ℝ (LayoutRowParts.lowTransport c K S α x y) (c.row a y) := by
  have hz : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | y 2 = 0} :=
    measure_eq_zero_iff_ae_notMem.1 CellDensityModesSolid.plane_null
  filter_upwards [gradientMirror c.order x.1 x.2.1 x.2.2.1 hx.1, hx.1.symmetric.2, (hc.base.row_class a).2, hz]
    with y hGH hv hr hy0 hy
  have hy' : cylHeight y ≠ 0 := hy0
  obtain ⟨hV, hW, -⟩ := hD.model_mirror y hy hy'
  rw [lowTransport_pt c K S α x hy' hv hGH.1 hV hW, hr, LayoutRowModes.mirror_inner]

theorem trace_of_mirror {H' H : Space →L[ℝ] Space →L[ℝ] Space} (h : ∀ u u', H' u u' = mirror (H (mirror u) (mirror u'))) :
    secondTrace H' = mirror (secondTrace H) := by
  unfold secondTrace
  rw [mirror_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h, mirror_unit]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_smul, sgn_sq, one_smul]

theorem trace_mirror {K : CellBox} {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {row : Space → Space} (hs : IsSecondOrderField m v G H)
    (hrow : IsClassField m row) :
    ∀ᵐ y ∂volume, y ∈ K.solid → inner ℝ (secondTrace (H (mirror y))) (row (mirror y)) =
      inner ℝ (secondTrace (H y)) (row y) := by
  filter_upwards [gradientMirror m v G H hs, hrow.2] with y hGH hr _
  rw [hr, trace_of_mirror hGH.2, LayoutRowModes.mirror_inner]

theorem frame_entryInner (θ : ℝ) (M K : Space →L[ℝ] Space) :
    entryInner M K = ∑ a : Fin 3, ∑ b : Fin 3, frameMat θ M a b * frameMat θ K a b := by
  simp only [entryInner, inner_eq,
    show ∀ (X : Space →L[ℝ] Space) (a b : Fin 3), X (unitVector b) a = entry X a b from fun _ _ _ => rfl]
  simp only [frameMat, inner_eq, apply_sum M, apply_sum K, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, radialUnit, angularUnit, axialUnit, PiLp.add_apply, EuclideanSpace.single_apply]
  simp
  linear_combination (-entry M 0 0*entry K 0 0*Real.cos θ^2 - entry M 0 0*entry K 0 0*Real.sin θ^2 - entry M 0 0*entry K 0 0 - entry M 0 1*entry K 0 1*Real.cos θ^2 - entry M 0 1*entry K 0 1*Real.sin θ^2 - entry M 0 1*entry K 0 1 - entry M 0 2*entry K 0 2 - entry M 1 0*entry K 1 0*Real.cos θ^2 - entry M 1 0*entry K 1 0*Real.sin θ^2 - entry M 1 0*entry K 1 0 - entry M 1 1*entry K 1 1*Real.cos θ^2 - entry M 1 1*entry K 1 1*Real.sin θ^2 - entry M 1 1*entry K 1 1 - entry M 1 2*entry K 1 2 - entry M 2 0*entry K 2 0 - entry M 2 1*entry K 2 1) * Real.sin_sq_add_cos_sq θ

theorem ii_sum {ι : Type} (s : Finset ι) {g : ι → ℝ → ℝ} {a b : ℝ}
    (h : ∀ i ∈ s, IntervalIntegrable (g i) volume a b) :
    IntervalIntegrable (fun θ => ∑ i ∈ s, g i θ) volume a b := by
  have := IntervalIntegrable.sum s h
  rwa [Finset.sum_fn] at this

theorem re_integral (f : ℝ → ℝ) (w : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 (2 * Real.pi))
    (hw : Continuous w) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), f θ * (w θ).re = (∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ : ℂ) * w θ).re := by
  have hc : IntervalIntegrable (fun θ => (f θ : ℂ) * w θ) volume 0 (2 * Real.pi) :=
    (show IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) from
      ⟨hf.1.ofReal, hf.2.ofReal⟩).mul_continuousOn hw.continuousOn
  rw [← Complex.reCLM_apply, ← Complex.reCLM.intervalIntegral_comp_comm hc]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]

theorem exp_integral_conj (f t : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), (f θ : ℂ) * Complex.exp ((t θ : ℝ) * Complex.I) =
      (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(t θ : ℝ) * Complex.I) * (f θ : ℂ)) := by
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  ring_nf

theorem circle_pairing_mat (m : ℕ) (s : Finset ℤ) (G K : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (W : ℤ → Fin 3 → Fin 3 → ℂ)
    (hexp : ∀ θ a b, frameMat θ (K (cylPoint r θ z)) a b =
      (∑ n ∈ s, W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re)
    (hint : ∀ a b, IntervalIntegrable (fun θ => frameMat θ (G (cylPoint r θ z)) a b) volume 0 (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), entryInner (G (cylPoint r θ z)) (K (cylPoint r θ z)) =
      2 * Real.pi * (∑ n ∈ s, ∑ a : Fin 3, ∑ b : Fin 3,
        modeMat m n G r z a b * (starRingEnd ℂ) (W n a b)).re := by
  have he : ∀ (a b : Fin 3) (n : ℤ),
      Continuous (fun θ : ℝ => W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)) := fun a b n => by
    fun_prop
  have hterm : ∀ (a b : Fin 3) (n : ℤ), IntervalIntegrable (fun θ => frameMat θ (G (cylPoint r θ z)) a b *
      (W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re) volume 0 (2 * Real.pi) := fun a b n =>
    (hint a b).mul_continuousOn (Complex.continuous_re.comp (he a b n)).continuousOn
  have hpt : ∀ θ, entryInner (G (cylPoint r θ z)) (K (cylPoint r θ z)) =
      ∑ a : Fin 3, ∑ b : Fin 3, ∑ n ∈ s, frameMat θ (G (cylPoint r θ z)) a b *
        (W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re := by
    intro θ
    rw [frame_entryInner θ]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hexp θ a b, Complex.re_sum, Finset.mul_sum]
  simp_rw [hpt]
  rw [intervalIntegral.integral_finsetSum fun a _ => ii_sum _ fun b _ => ii_sum s fun n _ => hterm a b n]
  simp_rw [intervalIntegral.integral_finsetSum fun b _ => ii_sum s fun n _ => hterm _ b n]
  simp_rw [intervalIntegral.integral_finsetSum fun n _ => hterm _ _ n]
  have hk : ∀ (a b : Fin 3) (n : ℤ), ∫ θ in (0 : ℝ)..(2 * Real.pi), frameMat θ (G (cylPoint r θ z)) a b *
      (W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)).re =
      (2 * Real.pi * (modeMat m n G r z a b * (starRingEnd ℂ) (W n a b))).re := by
    intro a b n
    rw [re_integral _ _ (hint a b) (he a b n)]
    have h1 : (fun θ : ℝ => (frameMat θ (G (cylPoint r θ z)) a b : ℂ) *
        (W n a b * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I))) =
        fun θ => W n a b * ((frameMat θ (G (cylPoint r θ z)) a b : ℂ) *
          Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)) := by
      funext θ; ring
    rw [h1, intervalIntegral.integral_const_mul,
      exp_integral_conj (fun θ => frameMat θ (G (cylPoint r θ z)) a b) (fun θ => azimuth m n * θ)]
    have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact_mod_cast this.ne'
    have hM : (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (frameMat θ (G (cylPoint r θ z)) a b : ℂ)) = 2 * Real.pi * modeMat m n G r z a b := by
      unfold modeMat
      field_simp
      simp only [mul_comm Complex.I]
    rw [hM]
    have hre : ∀ u w : ℂ, (w * (starRingEnd ℂ) u).re = (u * (starRingEnd ℂ) w).re := by
      intro u w
      simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [map_mul, show (starRingEnd ℂ) (2 * Real.pi : ℂ) = (2 * Real.pi : ℂ) by
      simp [Complex.conj_ofReal, map_ofNat]]
    rw [show W n a b * ((2 * Real.pi : ℂ) * (starRingEnd ℂ) (modeMat m n G r z a b)) =
      ((2 * Real.pi : ℝ) : ℂ) * (W n a b * (starRingEnd ℂ) (modeMat m n G r z a b)) by push_cast; ring]
    rw [show (2 * Real.pi : ℂ) * (modeMat m n G r z a b * (starRingEnd ℂ) (W n a b)) =
      ((2 * Real.pi : ℝ) : ℂ) * (modeMat m n G r z a b * (starRingEnd ℂ) (W n a b)) by push_cast; ring]
    rw [Complex.re_ofReal_mul, Complex.re_ofReal_mul, hre]
  have hr : ∀ X : ℂ, (2 * Real.pi * X).re = 2 * Real.pi * X.re := fun X => by
    rw [show (2 * Real.pi * X : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * X by push_cast; ring, Complex.re_ofReal_mul]
  simp_rw [hk, hr]
  simp only [Complex.re_sum, Finset.mul_sum]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem rim_null_rect (K : CellBox) :
    volume (K.rect \ (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂)) = 0 := by
  have hs : K.rect \ (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) ⊆
      ({K.r₁, K.r₂} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ {K.z₁, K.z₂}) := by
    rintro ⟨r, z⟩ ⟨⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩, hn⟩
    simp only [Set.mem_prod, Set.mem_Ioo, not_and_or, not_lt] at hn
    simp only [Set.mem_union, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, and_true,
      true_and]
    rcases hn with (h | h) | (h | h)
    · exact Or.inl (Or.inl (le_antisymm h hr1))
    · exact Or.inl (Or.inr (le_antisymm hr2 h))
    · exact Or.inr (Or.inl (le_antisymm h hz1))
    · exact Or.inr (Or.inr (le_antisymm hz2 h))
  refine measure_mono_null hs (measure_union_null ?_ ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite {K.r₁, K.r₂}).measure_zero, zero_mul]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite {K.z₁, K.z₂}).measure_zero, mul_zero]

theorem poly_pairing_open {K : CellBox} (hK : IsCellBox K) {B : CellBases} (hB : IsCellBases K B) {d : ℕ} {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hX : ∃ P ∈ polyFn d d, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * X p = P p) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * F p * X p := by
  obtain ⟨P, hP, hPX⟩ := hX
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ K.rect → p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
    refine measure_mono_null ?_ (rim_null_rect K)
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Classical.not_imp] at hq
    exact hq
  have hPX' : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ K.rect → ((rHat K p : ℝ) : ℂ) * X p = P p := by
    filter_upwards [hae] with p hp hpr
    exact hPX p (hp hpr) (lt_of_le_of_lt hK.r_order.1 (hp hpr).1.1).ne'
  set Q : ℝ × ℝ → ℂ := fun p => (starRingEnd ℂ) (P p) with hQdef
  have hQ : Q ∈ polyFn d d := poly_conj hP
  have e1 : ∀ j l : ℕ, (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) =
      (starRingEnd ℂ) (K.pairOn K.lineWeightFn Q (basisC B j l)) := by
    intro j l
    rw [pair_def, ← integral_conj]
    refine setIntegral_congr_ae hrm ?_
    filter_upwards [hPX'] with p hp0 hp
    have h := weight_mul (hp0 hp)
    simp only [hQdef, basisVal_eq, basisC, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination ((CellEnergy.basisFn B j l p : ℝ) : ℂ) * h
  have e2 : (∫ p in K.rect, (p.1 : ℂ) * F p * X p) = K.pairOn K.lineWeightFn F Q := by
    rw [pair_def]
    refine setIntegral_congr_ae hrm ?_
    filter_upwards [hPX'] with p hp0 hp
    have h := weight_mul (hp0 hp)
    simp only [hQdef, Complex.conj_conj]
    linear_combination F p * h
  have hrec := poly_recon K hB hQ
  have hQf : Q = fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p := funext hrec
  have hcont : ∀ i ∈ range (d + 1), Continuous (fun p => ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p) := fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)
  rw [e2, hQf, pair_sum_right K _ hF hcont]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sum_right K _ hF (g := fun k p => K.pairOn K.lineWeightFn Q (basisC B j k) * basisC B j k p)
    (fun k _ => continuous_const.mul (basisC_cont B j k))]
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pair_smul_right, e1, coef_eq, coef_eq]

def openCore (K : CellBox) : Set Space :=
  {y | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < |cylHeight y| ∧ |cylHeight y| < K.z₂}

theorem openCore_open (K : CellBox) : IsOpen (openCore K) := by
  have hR : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hH : Continuous (fun y => |cylHeight y|) := by unfold cylHeight; fun_prop
  exact ((isOpen_lt continuous_const hR).inter ((isOpen_lt hR continuous_const).inter
    ((isOpen_lt continuous_const hH).inter (isOpen_lt hH continuous_const))))

theorem openCore_sub (K : CellBox) : openCore K ⊆ K.solid := fun y hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩

theorem rim_null {K : CellBox} (hK : IsCellBox K) (hfin : volume K.solid < ⊤) :
    volume (K.solid \ openCore K) = 0 := by
  set A := K.solid \ openCore K with hA
  have hAm : MeasurableSet A :=
    (CellDensityModesSolid.solid_closed K).diff (openCore_open K).measurableSet
  have hAs : A ⊆ K.solid := Set.diff_subset
  have hfi : IntegrableOn (A.indicator (fun _ => (1 : ℝ))) K.solid := by
    have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hfin.ne
    exact (integrable_const (1 : ℝ)).indicator hAm
  have hmir : ∀ y, y ∈ A ↔ mirror y ∈ A := by
    intro y
    simp only [hA, Set.mem_diff, CellBox.solid, openCore, Set.mem_setOf_eq, CellDensityModesSolid.mirror_radius,
      CellDensityModesSolid.mirror_height]
  have hm : ∀ᵐ y ∂volume, y ∈ K.solid → A.indicator (fun _ => (1 : ℝ)) (mirror y) = A.indicator (fun _ => (1 : ℝ)) y := by
    refine ae_of_all _ fun y _ => ?_
    by_cases h : y ∈ A
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem ((hmir y).1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h ((hmir y).2 h'))]
  have hsf := CellDensityModesSolid.solid_formula K hK _ hfi hm
  have hzero : (∫ p in K.rect, p.1 * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      A.indicator (fun _ => (1 : ℝ)) (cylPoint p.1 θ p.2)) = 0 := by
    refine setIntegral_eq_zero_of_ae_eq_zero ?_
    have hnull := rim_null_rect K
    have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ K.rect → p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
      refine measure_mono_null ?_ hnull
      intro p hp
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Classical.not_imp] at hp
      exact hp
    filter_upwards [hae] with p hp0 hpr
    have hp := hp0 hpr
    have hr : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hp.1.1
    have hz : 0 < p.2 := lt_of_le_of_lt hK.z_order.1 hp.2.1
    have hin : ∀ θ, cylPoint p.1 θ p.2 ∉ A := by
      intro θ hθ
      refine hθ.2 ?_
      simp only [openCore, Set.mem_setOf_eq, CellDensityModesSolid.cyl_radius hr.le,
        CellDensityModesSolid.cyl_height, abs_of_pos hz]
      exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩
    simp only [Set.indicator_of_notMem (hin _), intervalIntegral.integral_zero, mul_zero]
  rw [hzero, mul_zero] at hsf
  have h1 : (∫ y in K.solid, A.indicator (fun _ => (1 : ℝ)) y) = volume.real A := by
    rw [integral_indicator_const _ hAm, smul_eq_mul, mul_one, Measure.real, Measure.restrict_apply hAm,
      Set.inter_eq_left.2 hAs]
    rfl
  rw [h1] at hsf
  exact (measureReal_eq_zero_iff (measure_mono hAs |>.trans_lt hfin).ne).1 hsf

theorem frameMat_cols (θ : ℝ) (M : Space →L[ℝ] Space) (i j : Fin 3) :
    frameMat θ M i j = ∑ l : Fin 3, (frameUnit θ j) l * frameVec θ (M (unitVector l)) i := by
  have e : frameMat θ M i j = inner ℝ (M (frameUnit θ j)) (frameUnit θ i) := rfl
  rw [e]
  conv_lhs => rw [vec_expand (frameUnit θ j)]
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul, real_inner_smul_left, ModeVelSquareInternal.frameVec_eq]

theorem gradient_circle_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ i j : Fin 3,
      IntervalIntegrable (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) i j) volume 0 (2 * Real.pi) := by
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hcol : ∀ l : Fin 3, ∀ᵐ p ∂(volume.restrict K.rect), ∀ i : Fin 3,
      IntervalIntegrable (fun θ => frameVec θ (x.2.1 (cylPoint p.1 θ p.2) (unitVector l)) i) volume 0
        (2 * Real.pi) := by
    intro l
    have hm : AEStronglyMeasurable (fun y => x.2.1 y (unitVector l)) volume :=
      hx.1.measurable_gradient.apply_continuousLinearMap (unitVector l)
    have hL : MemLp (fun y => x.2.1 y (unitVector l)) 2 volume :=
      memLp_col hx.1.measurable_gradient hx.1.gradient_two l
    have hn : IntegrableOn (fun y => ‖x.2.1 y (unitVector l)‖) K.solid :=
      (show IntegrableOn (fun y => ‖x.2.1 y (unitVector l)‖) (closure c.cellRegion) volume from
        ((hL.locallyIntegrable (by norm_num)).integrableOn_isCompact hT0).norm).mono_set hTT
    have h := LayoutRowPressure.circle_integrable hD.box hm hn
    exact h
  filter_upwards [ae_all_iff.2 hcol] with p hp i j
  have e : (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) i j) = fun θ => ∑ l : Fin 3,
      (frameUnit θ j) l * frameVec θ (x.2.1 (cylPoint p.1 θ p.2) (unitVector l)) i :=
    funext fun θ => frameMat_cols θ _ i j
  rw [e]
  refine ii_sum _ fun l _ => (hp l i).continuousOn_mul ?_
  have hcj : Continuous fun θ : ℝ => (frameUnit θ j) l :=
    (EuclideanSpace.proj (𝕜 := ℝ) l).continuous.comp (ModeVelSquareInternal.frameUnit_cont j)
  exact hcj.continuousOn

theorem solid_isClosed (K : CellBox) : IsClosed K.solid := by
  have hR : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  simp only [CellBox.solid, Set.ofPred_and]
  exact (isClosed_le continuous_const hR).inter ((isClosed_le hR continuous_const).inter
    ((isClosed_le continuous_const hH.abs).inter (isClosed_le hH.abs continuous_const)))

theorem row_deriv_off {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hD : IsCellData α c K S B Cl R) (ha : a ∈ R.rowSet) {y : Space} (hy : y ∉ K.solid) :
    fderiv ℝ (c.row a) y = 0 := by
  have he : c.row a =ᶠ[nhds y] fun _ => 0 :=
    Filter.mem_of_superset ((solid_isClosed K).isOpen_compl.mem_nhds hy) fun z hz => hD.rows_in_cell a ha z hz
  rw [he.fderiv_eq]
  exact fderiv_const_apply 0

theorem vol_height_mirror (y : Space) : cylHeight (mirror y) = -cylHeight y := by
  simp [cylHeight, mirror]

theorem vol_norm_mirror (u : Space) : ‖mirror u‖ = ‖u‖ := by
  rw [← mirror_coe]
  exact LinearSolveCore.mirrorIsometry.norm_map u

theorem core_mirror_iff {K : CellBox} (y : Space) : mirror y ∈ openCore K ↔ y ∈ openCore K := by
  simp only [openCore, Set.mem_setOf_eq, CellDensityModesSolid.mirror_radius, CellDensityModesSolid.mirror_height]

theorem upper_nhds (K : CellBox) {y : Space} (hy : y ∈ openCore K) (hh : 0 < cylHeight y) :
    K.solid ∩ {z | 0 ≤ cylHeight z} ∈ nhds y := by
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  refine Filter.mem_of_superset (((openCore_open K).inter (isOpen_lt continuous_const hH)).mem_nhds ⟨hy, hh⟩) ?_
  exact fun z hz => ⟨openCore_sub K hz.1, show 0 ≤ cylHeight z from le_of_lt hz.2⟩

theorem lower_eq_near {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} {a : Fin N} (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) {y : Space}
    (hy : y ∈ openCore K) (hh : cylHeight y < 0) :
    c.row a =ᶠ[nhds y] fun z => mirror (c.row a (mirror z)) := by
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  exact Filter.mem_of_superset (((openCore_open K).inter (isOpen_lt hH continuous_const)).mem_nhds ⟨hy, hh⟩)
    fun z hz => hR.row_mirror a ha z (openCore_sub K hz.1) hz.2

theorem lower_fderiv {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} {a : Fin N} (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) {y : Space}
    (hy : y ∈ openCore K) (hh : cylHeight y < 0) (u : Space) :
    fderiv ℝ (c.row a) y u = mirror (fderiv ℝ (c.row a) (mirror y) (mirror u)) := by
  set E : Space ≃L[ℝ] Space := LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv with hE
  have hEf : (⇑E : Space → Space) = mirror := mirror_coe
  have hg : (fun z => mirror (c.row a (mirror z))) = ⇑E ∘ (c.row a ∘ ⇑E) := by
    funext z
    rw [hEf]
    rfl
  rw [(lower_eq_near hR ha hy hh).fderiv_eq, hg, E.comp_fderiv, E.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hEf]

theorem upper_bound {k N : ℕ} {c : FracCellData k N} {K : CellBox} {a : Fin N} {L : NNReal}
    (hL : LipschitzOnWith L (c.row a) (K.solid ∩ {y | 0 ≤ cylHeight y})) {y : Space}
    (hy : y ∈ openCore K) (hh : 0 < cylHeight y) : ‖fderiv ℝ (c.row a) y‖ ≤ L :=
  norm_fderiv_le_of_lipschitzOn ℝ (upper_nhds K hy hh) hL

theorem row_norm_bound {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} {a : Fin N} (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) {L : NNReal}
    (hL : LipschitzOnWith L (c.row a) (K.solid ∩ {y | 0 ≤ cylHeight y})) {y : Space}
    (hy : y ∈ openCore K) (hh : cylHeight y ≠ 0) : ‖fderiv ℝ (c.row a) y‖ ≤ L := by
  rcases lt_or_gt_of_ne hh with h | h
  · have hm : 0 < cylHeight (mirror y) := by rw [vol_height_mirror]; linarith
    have hb := upper_bound hL ((core_mirror_iff y).2 hy) hm
    refine ContinuousLinearMap.opNorm_le_bound _ L.coe_nonneg fun u => ?_
    rw [lower_fderiv hR ha hy h u, vol_norm_mirror, ← vol_norm_mirror u]
    exact ContinuousLinearMap.le_of_opNorm_le _ hb _
  · exact upper_bound hL hy h

theorem row_deriv_bound {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) :
    ∃ C, 0 ≤ C ∧ ∀ᵐ y ∂volume, ‖fderiv ℝ (c.row a) y‖ ≤ C := by
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have hnull := rim_null hD.box hfin
  have hz : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | y 2 = 0} :=
    measure_eq_zero_iff_ae_notMem.1 CellDensityModesSolid.plane_null
  refine ⟨L, L.coe_nonneg, ?_⟩
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull, hz] with y hy hy0
  by_cases hs : y ∈ K.solid
  · have hcy : y ∈ openCore K := by
      by_contra h
      exact hy ⟨hs, h⟩
    have hy' : cylHeight y ≠ 0 := hy0
    exact row_norm_bound hR ha hL hcy hy'
  · rw [row_deriv_off hD ha hs, norm_zero]
    exact L.coe_nonneg

theorem gradient_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    Integrable (fun y => entryInner (x.2.1 y) (fderiv ℝ (c.row a) y)) := by
  obtain ⟨C, hC0, hC⟩ := row_deriv_bound hc hD hR ha
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hsm : MeasurableSet K.solid := CellDensityModesSolid.solid_closed K
  have hDm : AEStronglyMeasurable (fderiv ℝ (c.row a)) volume :=
    (measurable_fderiv ℝ (c.row a)).aestronglyMeasurable
  have hterm : ∀ i : Fin 3, Integrable (fun y => inner ℝ (x.2.1 y (unitVector i))
      (fderiv ℝ (c.row a) y (unitVector i))) := by
    intro i
    have hGi : AEStronglyMeasurable (fun y => x.2.1 y (unitVector i)) volume :=
      hx.1.measurable_gradient.apply_continuousLinearMap (unitVector i)
    have hDi : AEStronglyMeasurable (fun y => fderiv ℝ (c.row a) y (unitVector i)) volume :=
      hDm.apply_continuousLinearMap (unitVector i)
    have hL : MemLp (fun y => x.2.1 y (unitVector i)) 2 volume :=
      memLp_col hx.1.measurable_gradient hx.1.gradient_two i
    have hn : IntegrableOn (fun y => ‖x.2.1 y (unitVector i)‖) K.solid :=
      (show IntegrableOn (fun y => ‖x.2.1 y (unitVector i)‖) (closure c.cellRegion) volume from
        ((hL.locallyIntegrable (by norm_num)).integrableOn_isCompact hT0).norm).mono_set hTT
    have hdom : Integrable (K.solid.indicator (fun y => C * ‖unitVector i‖ * ‖x.2.1 y (unitVector i)‖)) :=
      IntegrableOn.integrable_indicator (hn.const_mul (C * ‖unitVector i‖)) hsm
    refine hdom.mono' (hGi.inner hDi) ?_
    filter_upwards [hC] with y hy
    by_cases hs : y ∈ K.solid
    · rw [Set.indicator_of_mem hs]
      calc ‖inner ℝ (x.2.1 y (unitVector i)) (fderiv ℝ (c.row a) y (unitVector i))‖
          ≤ ‖x.2.1 y (unitVector i)‖ * ‖fderiv ℝ (c.row a) y (unitVector i)‖ := norm_inner_le_norm _ _
        _ ≤ ‖x.2.1 y (unitVector i)‖ * (C * ‖unitVector i‖) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul_of_nonneg_right hy (norm_nonneg _))) (norm_nonneg _)
        _ = C * ‖unitVector i‖ * ‖x.2.1 y (unitVector i)‖ := by ring
    · rw [Set.indicator_of_notMem hs, row_deriv_off hD ha hs]
      simp
  have hsum := integrable_finsetSum Finset.univ fun i _ => hterm i
  refine hsum.congr (ae_of_all _ fun y => ?_)
  simp only [entryInner]

theorem gradient_pair_mirror {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    ∀ᵐ y ∂volume, y ∈ K.solid → entryInner (x.2.1 (mirror y)) (fderiv ℝ (c.row a) (mirror y)) =
      entryInner (x.2.1 y) (fderiv ℝ (c.row a) y) := by
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have hz : ∀ᵐ y ∂(volume : Measure Space), y ∉ {y : Space | y 2 = 0} :=
    measure_eq_zero_iff_ae_notMem.1 CellDensityModesSolid.plane_null
  filter_upwards [gradientMirror c.order x.1 x.2.1 x.2.2.1 hx.1,
    measure_eq_zero_iff_ae_notMem.1 (rim_null hD.box hfin), hz] with y hGH hrim hy0 hs
  have hy : y ∈ openCore K := by
    by_contra h
    exact hrim ⟨hs, h⟩
  have hy' : cylHeight y ≠ 0 := hy0
  have hA : ∀ u, fderiv ℝ (c.row a) (mirror y) u = mirror (fderiv ℝ (c.row a) y (mirror u)) := by
    intro u
    rcases lt_or_gt_of_ne hy' with h | h
    · rw [lower_fderiv hR ha hy h (mirror u)]
      simp only [mirror_mirror]
    · have hm : cylHeight (mirror y) < 0 := by rw [vol_height_mirror]; linarith
      rw [lower_fderiv hR ha ((core_mirror_iff y).2 hy) hm u, mirror_mirror]
  exact entryInner_mirror hGH.1 hA

section

open Filter Topology

theorem path_radial (r θ z : ℝ) : HasDerivAt (fun s => cylPoint s θ z) (radialUnit θ) r := by
  have e : (fun s => cylPoint s θ z) = fun s => s • radialUnit θ + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  have h := ((hasDerivAt_id r).smul_const (radialUnit θ)).add_const (EuclideanSpace.single 2 z : Space)
  simpa using h

theorem path_height (r θ z : ℝ) : HasDerivAt (fun s => cylPoint r θ s) axialUnit z := by
  have e : (fun s => cylPoint r θ s) = fun s => s • axialUnit + cylPoint r θ 0 := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, axialUnit]
  rw [e]
  have h := ((hasDerivAt_id z).smul_const axialUnit).add_const (cylPoint r θ 0)
  simpa using h

theorem path_radialUnit (θ : ℝ) : HasDerivAt (fun t => radialUnit t) (angularUnit θ) θ := by
  have e : (fun t => radialUnit t) = fun t => Real.cos t • (EuclideanSpace.single 0 1 : Space)
      + Real.sin t • (EuclideanSpace.single 1 1 : Space) := by
    funext t; ext j; fin_cases j <;> simp [radialUnit]
  rw [e]
  have h := ((Real.hasDerivAt_cos θ).smul_const (EuclideanSpace.single 0 1 : Space)).add
    ((Real.hasDerivAt_sin θ).smul_const (EuclideanSpace.single 1 1 : Space))
  have e2 : angularUnit θ = (-Real.sin θ) • (EuclideanSpace.single 0 1 : Space)
      + Real.cos θ • (EuclideanSpace.single 1 1 : Space) := by
    ext j; fin_cases j <;> simp [angularUnit]
  rw [e2]
  exact h

theorem path_angularUnit (θ : ℝ) : HasDerivAt (fun t => angularUnit t) (-radialUnit θ) θ := by
  have e : (fun t => angularUnit t) = fun t => (-Real.sin t) • (EuclideanSpace.single 0 1 : Space)
      + Real.cos t • (EuclideanSpace.single 1 1 : Space) := by
    funext t; ext j; fin_cases j <;> simp [angularUnit]
  rw [e]
  have h := ((Real.hasDerivAt_sin θ).neg.smul_const (EuclideanSpace.single 0 1 : Space)).add
    ((Real.hasDerivAt_cos θ).smul_const (EuclideanSpace.single 1 1 : Space))
  have e2 : -radialUnit θ = (-Real.cos θ) • (EuclideanSpace.single 0 1 : Space)
      + (-Real.sin θ) • (EuclideanSpace.single 1 1 : Space) := by
    ext j; fin_cases j <;> simp [radialUnit]
  rw [e2]
  exact h

theorem path_angle (r θ z : ℝ) : HasDerivAt (fun t => cylPoint r t z) (r • angularUnit θ) θ := by
  have e : (fun t => cylPoint r t z) = fun t => r • radialUnit t + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  exact ((path_radialUnit θ).const_smul r).add_const _

theorem path_unit (θ : ℝ) (a : Fin 3) :
    HasDerivAt (fun t => frameUnit t a) (![angularUnit θ, -radialUnit θ, 0] a) θ := by
  fin_cases a
  · exact path_radialUnit θ
  · exact path_angularUnit θ
  · exact hasDerivAt_const θ axialUnit

theorem frame_radial_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint s θ z)) a) (frameMat θ D a 0) r := by
  have e : (fun s => frameVec θ (g (cylPoint s θ z)) a) = fun s => inner ℝ (g (cylPoint s θ z)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt r (path_radial r θ z)).inner ℝ (hasDerivAt_const r (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

theorem frame_height_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint r θ s)) a) (frameMat θ D a 2) z := by
  have e : (fun s => frameVec θ (g (cylPoint r θ s)) a) = fun s => inner ℝ (g (cylPoint r θ s)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt z (path_height r θ z)).inner ℝ (hasDerivAt_const z (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

theorem frame_angle_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun t => frameVec t (g (cylPoint r t z)) a)
      (r * frameMat θ D a 1 + ![frameVec θ (g (cylPoint r θ z)) 1, -frameVec θ (g (cylPoint r θ z)) 0, 0] a) θ := by
  have e : (fun t => frameVec t (g (cylPoint r t z)) a) = fun t => inner ℝ (g (cylPoint r t z)) (frameUnit t a) :=
    funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt θ (path_angle r θ z)).inner ℝ (path_unit θ a)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, map_smul, real_inner_smul_left]
  have e1 : frameMat θ D a 1 = inner ℝ (D (angularUnit θ)) (frameUnit θ a) := rfl
  rw [e1, add_comm]
  congr 1
  fin_cases a
  · rfl
  · show inner ℝ (g (cylPoint r θ z)) (-radialUnit θ) = -frameVec θ (g (cylPoint r θ z)) 0
    rw [inner_neg_right]; rfl
  · show inner ℝ (g (cylPoint r θ z)) 0 = 0
    exact inner_zero_right _

theorem frameMat_abs_le (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ M a b| ≤ ‖M‖ := by
  have ha := LowEntry.Internal.unit_norm θ a
  have hb := LowEntry.Internal.unit_norm θ b
  unfold frameMat
  rw [← Real.norm_eq_abs]
  calc ‖inner ℝ (M (![radialUnit θ, angularUnit θ, axialUnit] b)) (![radialUnit θ, angularUnit θ, axialUnit] a)‖
      ≤ ‖M (![radialUnit θ, angularUnit θ, axialUnit] b)‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] a‖ :=
        norm_inner_le_norm _ _
    _ ≤ (‖M‖ * 1) * 1 := by
        gcongr
        exact (M.le_opNorm _).trans (by gcongr)
    _ = ‖M‖ := by ring

theorem param_mode_zero {F F' : ℝ → ℝ → ℝ} {x₀ C k : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 x₀)
    (hFc : ∀ x ∈ s, Continuous (F x)) (hF'c : Continuous (F' x₀)) (hb : ∀ x ∈ s, ∀ t, |F' x t| ≤ C)
    (hd : ∀ x ∈ s, ∀ t, HasDerivAt (fun x => F x t) (F' x t) x)
    (hz : ∀ x ∈ s, ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ) = 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x₀ t : ℂ) = 0 := by
  have hec : Continuous (fun t : ℝ => Complex.exp (-(k * t : ℝ) * Complex.I)) := by fun_prop
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(k * t : ℝ) * Complex.I)‖ = 1 := fun t => by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2 * Real.pi) (bound := fun _ => C)
    (F := fun x t => Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ))
    (F' := fun x t => Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x t : ℂ)) hs
    (Filter.eventually_of_mem hs fun x hx =>
      (hec.mul (Complex.continuous_ofReal.comp (hFc x hx))).aestronglyMeasurable)
    ((hec.mul (Complex.continuous_ofReal.comp (hFc x₀ (mem_of_mem_nhds hs)))).intervalIntegrable _ _)
    ((hec.mul (Complex.continuous_ofReal.comp hF'c)).aestronglyMeasurable)
    (ae_of_all _ fun t _ x hx => by
      rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hb x hx t)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x hx => ((hd x hx t).ofReal_comp).const_mul _)
  have h0 : HasDerivAt (fun x => ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ)) 0 x₀ :=
    (hasDerivAt_const x₀ (0 : ℂ)).congr_of_eventuallyEq (Filter.eventually_of_mem hs fun x hx => hz x hx)
  exact key.2.unique h0

theorem mode_of_deriv {Φ Φ' : ℝ → ℝ} (m : ℕ) (k : ℤ) (hd : ∀ t, HasDerivAt Φ (Φ' t) t) (hc : Continuous Φ')
    (hper : Φ (2 * Real.pi) = Φ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m k * t : ℝ) * Complex.I) * (Φ' t : ℂ) =
      ((azimuth m k : ℂ) * Complex.I) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m k * t : ℝ) * Complex.I) * (Φ t : ℂ) := by
  set w : ℝ := azimuth m k with hw
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I))
      (Complex.exp (-(w * t : ℝ) * Complex.I) * (-((w * 1 : ℝ) : ℂ) * Complex.I)) t := fun t =>
    ((((hasDerivAt_id t).const_mul w).ofReal_comp.neg).mul_const Complex.I).cexp
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (Φ t : ℂ)) (Φ' t : ℂ) t := fun t => (hd t).ofReal_comp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
    (fun t _ => hu t) (fun t _ => hv t)
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I) *
      (-((w * 1 : ℝ) : ℂ) * Complex.I))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hc).intervalIntegrable _ _)
  beta_reduce at hibp
  rw [hibp]
  have h2 : Complex.exp (-(w * (2 * Real.pi) : ℝ) * Complex.I) = 1 := by
    have : -(((w * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I = ((-(k * m) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hw]; unfold azimuth; push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have h0 : Complex.exp (-(w * 0 : ℝ) * Complex.I) = 1 := by simp
  rw [h2, h0, hper]
  have e : (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I) * (-((w * 1 : ℝ) : ℂ) * Complex.I) * (Φ t : ℂ)) =
      fun t => (-((w : ℂ) * Complex.I)) * (Complex.exp (-(w * t : ℝ) * Complex.I) * (Φ t : ℂ)) := by
    funext t; push_cast; ring
  rw [e, intervalIntegral.integral_const_mul]
  ring

private theorem mode_trig_expand (m : ℕ) (hm : 0 < m) (g : ℝ → ℂ) (hg : Continuous g)
    (hper : Function.Periodic g (2 * Real.pi / m)) (s : Finset ℤ)
    (hz : ∀ n ∉ s, (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * g θ = 0) (θ : ℝ) :
    g θ = ∑ n ∈ s, ((1 / (2 * Real.pi) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t) *
        Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : 0 < 2 * Real.pi / m := by positivity
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : Fact (0 < 2 * Real.pi / m) := ⟨hT⟩
  let F : C(AddCircle (2 * Real.pi / m), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hg⟩
  have hF : ∀ x : ℝ, F (x : AddCircle (2 * Real.pi / m)) = g x := fun x => hper.lift_coe x
  have hfo : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 * Real.pi / m)) =
      Complex.exp ((azimuth m n * x : ℝ) * Complex.I) := by
    intro n x
    rw [fourier_coe_apply]
    congr 1
    unfold azimuth
    push_cast
    field_simp
  have hcoef : ∀ n : ℤ, fourierCoeff F n = (1 / (2 * Real.pi) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral F n 0]
    have hh : Function.Periodic (fun t : ℝ => Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t)
        (2 * Real.pi / m) := by
      intro t
      simp only
      rw [hper t]
      congr 1
      have harg : -(((azimuth m n * (t + 2 * Real.pi / m) : ℝ)) : ℂ) * Complex.I =
          -(((azimuth m n * t : ℝ)) : ℂ) * Complex.I + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        unfold azimuth; push_cast; field_simp; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hcont : Continuous (fun t : ℝ => Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t) := by
      fun_prop
    have hsum := hh.intervalIntegral_add_zsmul_eq (m : ℤ) 0 (fun a b => hcont.intervalIntegrable a b)
    rw [zero_add, zero_add, show ((m : ℤ) • (2 * Real.pi / m)) = 2 * Real.pi by
      rw [zsmul_eq_mul]; push_cast; field_simp] at hsum
    rw [hsum]
    have e : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * Real.pi / m)) • F x =
        Complex.exp (-(azimuth m n * x : ℝ) * Complex.I) * g x := by
      intro x
      rw [hF, hfo, smul_eq_mul]
      congr 2
      unfold azimuth
      push_cast
      ring
    simp_rw [e, zero_add]
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    push_cast
    field_simp
  have hsupp : ∀ n ∉ s, fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m)) = 0 := by
    intro n hn
    rw [hcoef, hz n hn, zero_smul]
  have h1 := has_pointwise_sum_fourier_series_of_summable
    (summable_of_ne_finset_zero (s := s) (fun n hn => by rw [hcoef, hz n hn])) (θ : AddCircle (2 * Real.pi / m))
  have h2 : HasSum (fun n => fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m)))
      (∑ n ∈ s, fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m))) :=
    hasSum_sum_of_ne_finset_zero hsupp
  rw [hF] at h1
  rw [h1.unique h2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hcoef, hfo, smul_eq_mul]


theorem row_grad_at {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet)
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (θ : ℝ) (i j : Fin 3) :
    frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i j =
      (∑ n ∈ R.rowModes, rowModeGrad c a n p i j * Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
  have hK := hD.box
  have hr0 : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hr1
  obtain ⟨f, hf, hfeq⟩ := hR.row_smooth a ha (p.1 / 2) (by positivity)
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  set lo : ℝ := max K.r₁ (p.1 / 2) with hlo
  have hRc : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hHc : Continuous cylHeight := by unfold cylHeight; fun_prop
  set V : Set Space := {y | lo < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < cylHeight y ∧ cylHeight y < K.z₂}
    with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const hRc).inter ((isOpen_lt hRc continuous_const).inter
    ((isOpen_lt continuous_const hHc).inter (isOpen_lt hHc continuous_const)))
  have hVcore : ∀ y ∈ V, y ∈ openCore K ∧ 0 < cylHeight y := by
    intro y hy
    have h0 : 0 < cylHeight y := lt_of_le_of_lt hK.z_order.1 hy.2.2.1
    refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2.1, ?_, ?_⟩, h0⟩
    · rw [abs_of_pos h0]; exact hy.2.2.1
    · rw [abs_of_pos h0]; exact hy.2.2.2
  have hVeq : ∀ y ∈ V, c.row a =ᶠ[𝓝 y] f := by
    intro y hy
    refine Filter.eventually_of_mem (hVo.mem_nhds hy) fun w hw => ?_
    obtain ⟨hwc, hw0⟩ := hVcore w hw
    exact hfeq w (openCore_sub K hwc) hw0.le (le_trans (le_max_right _ _) hw.1.le)
  have hder : ∀ y ∈ V, HasFDerivAt (c.row a) (fderiv ℝ (c.row a) y) y := by
    intro y hy
    have h1 : HasFDerivAt f (fderiv ℝ f y) y := (hf.differentiable (by norm_num) y).hasFDerivAt
    rw [(hVeq y hy).fderiv_eq]
    exact h1.congr_of_eventuallyEq (hVeq y hy)
  have hcont : ContinuousOn (fderiv ℝ (c.row a)) V :=
    (hf.continuous_fderiv (by norm_num)).continuousOn.congr fun y hy => (hVeq y hy).fderiv_eq
  have hbd : ∀ y ∈ V, ‖fderiv ℝ (c.row a) y‖ ≤ L := fun y hy =>
    upper_bound hL (hVcore y hy).1 (hVcore y hy).2
  have hmem : ∀ x t z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → cylPoint x t z' ∈ V := by
    intro x t z' h1 h2 h3 h4
    have hx0 : 0 ≤ x := le_trans (le_trans hK.r_order.1 (le_max_left _ _)) h1.le
    show lo < cylRadius (cylPoint x t z') ∧ cylRadius (cylPoint x t z') < K.r₂ ∧
      K.z₁ < cylHeight (cylPoint x t z') ∧ cylHeight (cylPoint x t z') < K.z₂
    rw [CellDensityModesSolid.cyl_radius hx0, CellDensityModesSolid.cyl_height]
    exact ⟨h1, h2, h3, h4⟩
  have hlop : lo < p.1 := max_lt hr1 (by linarith)
  have hpV : ∀ t, cylPoint p.1 t p.2 ∈ V := fun t => hmem _ _ _ hlop hr2 hz1 hz2
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hpath : ∀ x z', Continuous (fun t => cylPoint x t z') := fun x z' =>
    continuous_iff_continuousAt.2 fun t => (path_angle x t z').continuousAt
  have hFc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ b,
      Continuous (fun t => frameVec t (c.row a (cylPoint x t z')) b) := by
    intro x z' h1 h2 h3 h4 b
    have hg : Continuous (fun t => c.row a (cylPoint x t z')) :=
      continuous_iff_continuousAt.2 fun t =>
        (hder _ (hmem x t z' h1 h2 h3 h4)).continuousAt.comp (f := fun t => cylPoint x t z') (path_angle x t z').continuousAt
    have e : (fun t => frameVec t (c.row a (cylPoint x t z')) b) =
        fun t => inner ℝ (c.row a (cylPoint x t z')) (frameUnit t b) :=
      funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
    rw [e]
    exact hg.inner (ModeVelSquareInternal.frameUnit_cont b)
  have hMc : ∀ a' b', Continuous (fun t => frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) a' b') := by
    intro a' b'
    have hD' : Continuous (fun t => fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) :=
      hcont.comp_continuous (hpath p.1 p.2) hpV
    show Continuous fun t => inner ℝ ((fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) (frameUnit t b')) (frameUnit t a')
    exact (hD'.clm_apply (ModeVelSquareInternal.frameUnit_cont b')).inner (ModeVelSquareInternal.frameUnit_cont a')
  have hFper : ∀ q ∈ K.rect, ∀ t b, frameVec (t + 2 * Real.pi / c.order)
      (c.row a (cylPoint q.1 (t + 2 * Real.pi / c.order) q.2)) b = frameVec t (c.row a (cylPoint q.1 t q.2)) b := by
    intro q hq t b
    rw [LayoutRowPressure.row_expansion hc hD hR ha q hq (t + 2 * Real.pi / c.order) b,
      LayoutRowPressure.row_expansion hc hD hR ha q hq t b]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    congr 1
    have hmC : (c.order : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
    have harg : ((azimuth c.order n * (t + 2 * Real.pi / c.order) : ℝ) : ℂ) * Complex.I =
        ((azimuth c.order n * t : ℝ) : ℂ) * Complex.I + (n : ℂ) * (2 * Real.pi * Complex.I) := by
      unfold azimuth; push_cast; field_simp
      try ring
    rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hrect : ∀ x z', K.r₁ < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ((x, z') : ℝ × ℝ) ∈ K.rect :=
    fun x z' h1 h2 h3 h4 => ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  have hang : ∀ t', HasDerivAt (fun t => frameVec t (c.row a (cylPoint p.1 t p.2)) i)
      (p.1 * frameMat t' (fderiv ℝ (c.row a) (cylPoint p.1 t' p.2)) i 1 +
        ![frameVec t' (c.row a (cylPoint p.1 t' p.2)) 1, -frameVec t' (c.row a (cylPoint p.1 t' p.2)) 0, 0] i) t' :=
    fun t' => frame_angle_deriv (hder _ (hpV t')) i
  set T : ℝ := 2 * Real.pi / c.order with hT
  have hper : ∀ t, frameMat (t + T) (fderiv ℝ (c.row a) (cylPoint p.1 (t + T) p.2)) i j =
      frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j := by
    intro t
    fin_cases j
    · have h1 := frame_radial_deriv (hder _ (hpV (t + T))) i
      have h2 := frame_radial_deriv (hder _ (hpV t)) i
      have heq : (fun s => frameVec t (c.row a (cylPoint s t p.2)) i) =ᶠ[𝓝 p.1]
          (fun s => frameVec (t + T) (c.row a (cylPoint s (t + T) p.2)) i) :=
        Filter.eventually_of_mem (Ioo_mem_nhds hr1 hr2) fun s hs =>
          (hFper (s, p.2) (hrect s p.2 hs.1 hs.2 hz1 hz2) t i).symm
      exact (h1.congr_of_eventuallyEq heq).unique h2
    · have hΦ : (fun t' => frameVec (t' + T) (c.row a (cylPoint p.1 (t' + T) p.2)) i) =
          fun t' => frameVec t' (c.row a (cylPoint p.1 t' p.2)) i :=
        funext fun t' => hFper p ⟨⟨hr1.le, hr2.le⟩, ⟨hz1.le, hz2.le⟩⟩ t' i
      have h1 : HasDerivAt (fun t' => frameVec (t' + T) (c.row a (cylPoint p.1 (t' + T) p.2)) i)
          (p.1 * frameMat (t + T) (fderiv ℝ (c.row a) (cylPoint p.1 (t + T) p.2)) i 1 +
            ![frameVec (t + T) (c.row a (cylPoint p.1 (t + T) p.2)) 1,
              -frameVec (t + T) (c.row a (cylPoint p.1 (t + T) p.2)) 0, 0] i) t := by
        have := (hang (t + T)).comp t ((hasDerivAt_id t).add_const T)
        rw [mul_one] at this
        exact this
      rw [hΦ] at h1
      have hu := h1.unique (hang t)
      have hE : ![frameVec (t + T) (c.row a (cylPoint p.1 (t + T) p.2)) 1,
              -frameVec (t + T) (c.row a (cylPoint p.1 (t + T) p.2)) 0, (0 : ℝ)] i =
          ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i := by
        have hq : p ∈ K.rect := ⟨⟨hr1.le, hr2.le⟩, ⟨hz1.le, hz2.le⟩⟩
        rw [hFper p hq t 1, hFper p hq t 0]
      rw [hE] at hu
      have hu' := add_right_cancel hu
      exact mul_left_cancel₀ hr0.ne' hu'
    · have h1 := frame_height_deriv (hder _ (hpV (t + T))) i
      have h2 := frame_height_deriv (hder _ (hpV t)) i
      have heq : (fun s => frameVec t (c.row a (cylPoint p.1 t s)) i) =ᶠ[𝓝 p.2]
          (fun s => frameVec (t + T) (c.row a (cylPoint p.1 (t + T) s)) i) :=
        Filter.eventually_of_mem (Ioo_mem_nhds hz1 hz2) fun s hs =>
          (hFper (p.1, s) (hrect p.1 s hr1 hr2 hs.1 hs.2) t i).symm
      exact (h1.congr_of_eventuallyEq heq).unique h2
  have hq : p ∈ K.rect := ⟨⟨hr1.le, hr2.le⟩, ⟨hz1.le, hz2.le⟩⟩
  have hrm : ∀ n ∉ R.rowModes, ∀ q ∈ K.rect, ∀ b, ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (frameVec t (c.row a (cylPoint q.1 t q.2)) b : ℂ) = 0 := by
    intro n hn q hq' b
    have h : (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (frameVec t (c.row a (cylPoint q.1 t q.2)) b : ℂ) = 0 :=
      congrFun (hD.row_modes a ha n hn q hq') b
    have h2 : (1 / (2 * Real.pi) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact one_div_ne_zero (by exact_mod_cast this.ne')
    exact (mul_eq_zero.1 h).resolve_left h2
  have hec : ∀ n : ℤ, Continuous (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)) :=
    fun n => by fun_prop
  have hz : ∀ n ∉ R.rowModes, (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (fun t => (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j : ℂ)) t = 0 := by
    intro n hn
    suffices H : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j : ℂ) = 0 by
      simp only
      rw [H, mul_zero]
    fin_cases j
    · exact param_mode_zero (F := fun x t => frameVec t (c.row a (cylPoint x t p.2)) i)
        (F' := fun x t => frameMat t (fderiv ℝ (c.row a) (cylPoint x t p.2)) i 0) (C := L)
        (Ioo_mem_nhds hlop hr2)
        (fun x hx => hFc x p.2 hx.1 hx.2 hz1 hz2 i) (hMc i 0)
        (fun x hx t => (frameMat_abs_le _ _ _ _).trans (hbd _ (hmem x t p.2 hx.1 hx.2 hz1 hz2)))
        (fun x hx t => frame_radial_deriv (hder _ (hmem x t p.2 hx.1 hx.2 hz1 hz2)) i)
        (fun x hx => hrm n hn (x, p.2) (hrect x p.2 (lt_of_le_of_lt (le_max_left _ _) hx.1) hx.2 hz1 hz2) i)
    · have hEc : Continuous (fun t => ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1,
          -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i) := by
        fin_cases i
        · exact hFc p.1 p.2 hlop hr2 hz1 hz2 1
        · exact (hFc p.1 p.2 hlop hr2 hz1 hz2 0).neg
        · exact continuous_const
      have h2pi : frameVec (2 * Real.pi) (c.row a (cylPoint p.1 (2 * Real.pi) p.2)) i =
          frameVec 0 (c.row a (cylPoint p.1 0 p.2)) i := by
        have e1 : cylPoint p.1 (2 * Real.pi) p.2 = cylPoint p.1 0 p.2 := by simp [cylPoint]
        rw [e1]
        fin_cases i <;> simp [frameVec, radialUnit, angularUnit]
      have hibp := mode_of_deriv c.order n hang ((continuous_const.mul (hMc i 1)).add hEc) h2pi
      beta_reduce at hibp
      rw [hrm n hn p hq i, mul_zero] at hibp
      have hE0 : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ) = 0 := by
        fin_cases i
        · exact hrm n hn p hq 1
        · refine Eq.trans (intervalIntegral.integral_congr (g := fun t => -(Complex.exp (-(azimuth c.order n * t : ℝ) *
              Complex.I) * (frameVec t (c.row a (cylPoint p.1 t p.2)) 0 : ℂ))) fun t _ => ?_) ?_
          · show _ * (((-frameVec t (c.row a (cylPoint p.1 t p.2)) 0 : ℝ)) : ℂ) = _
            push_cast; ring
          · rw [intervalIntegral.integral_neg, hrm n hn p hq 0, neg_zero]
        · show ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (((0 : ℝ)) : ℂ) = 0
          simp
      have hi1 : IntervalIntegrable (fun t : ℝ => (p.1 : ℂ) * (Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ))) volume 0 (2 * Real.pi) :=
        (continuous_const.mul ((hec n).mul (Complex.continuous_ofReal.comp (hMc i 1)))).intervalIntegrable _ _
      have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ))
          volume 0 (2 * Real.pi) :=
        ((hec n).mul (Complex.continuous_ofReal.comp hEc)).intervalIntegrable _ _
      have hsplit : (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          ((p.1 * frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 +
            ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ)) =
          (p.1 : ℂ) * (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
            (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ)) +
          ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
            ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 hi2]
        congr 1
        funext t
        push_cast
        ring
      rw [hsplit, hE0, add_zero] at hibp
      exact (mul_eq_zero.1 hibp).resolve_left (by exact_mod_cast hr0.ne')
    · exact param_mode_zero (F := fun z' t => frameVec t (c.row a (cylPoint p.1 t z')) i)
        (F' := fun z' t => frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t z')) i 2) (C := L)
        (Ioo_mem_nhds hz1 hz2)
        (fun z' hz => hFc p.1 z' hlop hr2 hz.1 hz.2 i) (hMc i 2)
        (fun z' hz t => (frameMat_abs_le _ _ _ _).trans (hbd _ (hmem p.1 t z' hlop hr2 hz.1 hz.2)))
        (fun z' hz t => frame_height_deriv (hder _ (hmem p.1 t z' hlop hr2 hz.1 hz.2)) i)
        (fun z' hz => hrm n hn (p.1, z') (hrect p.1 z' hr1 hr2 hz.1 hz.2) i)
  have hperC : Function.Periodic (fun t => (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j : ℂ))
      (2 * Real.pi / c.order) := fun t => congrArg (fun x : ℝ => (x : ℂ)) (hper t)
  have key := mode_trig_expand c.order hm _ (Complex.continuous_ofReal.comp (hMc i j)) hperC R.rowModes hz θ
  rw [← Complex.ofReal_re (frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i j)]
  exact congrArg Complex.re key


end

theorem rowGrad_expansion {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ θ (i j : Fin 3),
      frameMat θ (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2)) i j =
        (∑ n ∈ R.rowModes, rowModeGrad c a n p i j * Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
  have hrm := CellDensityModesSolid.rect_meas K
  have hnull := rim_null_rect K
  have hae : ∀ᵐ q ∂(volume : Measure (ℝ × ℝ)), q ∈ K.rect → q ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
    refine measure_mono_null ?_ hnull
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Classical.not_imp] at hq
    exact hq
  rw [ae_restrict_iff' hrm]
  filter_upwards [hae] with q hq hqr θ i j
  exact row_grad_at hc hD hR ha (hq hqr) θ i j

theorem gradient_modes_of {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    LayoutRowParts.gradientPairing c x a = 4 * Real.pi * ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3,
      ∑ b' : Fin 3, gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re := by
  have hz : ∀ y ∉ K.solid, entryInner (x.2.1 y) (fderiv ℝ (c.row a) y) = 0 := fun y hy => by
    rw [row_deriv_off hD ha hy]
    simp [entryInner]
  unfold LayoutRowParts.gradientPairing
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz,
    CellDensityModesSolid.solid_formula K hD.box _ (gradient_integrable hc hD hR hx ha).integrableOn
      (gradient_pair_mirror hc hD hR hx ha)]
  have hrm := CellDensityModesSolid.rect_meas K
  have h2 : (∫ p in K.rect, p.1 * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      entryInner (x.2.1 (cylPoint p.1 θ p.2)) (fderiv ℝ (c.row a) (cylPoint p.1 θ p.2))) =
      ∫ p in K.rect, (2 * Real.pi) * (p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re) := by
    refine setIntegral_congr_ae hrm ?_
    filter_upwards [(ae_restrict_iff' hrm).1 (rowGrad_expansion hc hD hR hx ha),
      (ae_restrict_iff' hrm).1 (gradient_circle_integrable hc hD hR hx ha)] with p h1 h2 hp
    rw [circle_pairing_mat c.order R.rowModes x.2.1 (fderiv ℝ (c.row a)) p.1 p.2
      (fun n i j => rowModeGrad c a n p i j) (h1 hp) (h2 hp)]
    simp only [gradMode]
    ring
  rw [h2, integral_const_mul]
  ring

theorem gradient_modes {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    LayoutRowParts.gradientPairing c x a = 4 * Real.pi * ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
      gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re := by
  exact gradient_modes_of hc hD hR hx ha

theorem frame_expand_vec (θ : ℝ) (w : Space) : w = ∑ b : Fin 3, frameVec θ w b • frameUnit θ b := by
  have hs := Real.sin_sq_add_cos_sq θ
  ext j
  fin_cases j <;>
    simp [frameVec, frameUnit, radialUnit, angularUnit, axialUnit, Fin.sum_univ_three, inner_add_right,
      EuclideanSpace.inner_single_right] <;>
    first
      | linear_combination (-(w 0)) * hs
      | linear_combination (-(w 1)) * hs
      | linear_combination (w 0) * hs
      | linear_combination (w 1) * hs
      | ring

theorem frameVec_apply_clm (θ : ℝ) (M : Space →L[ℝ] Space) (w : Space) (i : Fin 3) :
    frameVec θ (M w) i = ∑ b : Fin 3, frameMat θ M i b * frameVec θ w b := by
  conv_lhs => rw [frame_expand_vec θ w]
  rw [map_sum, ModeVelSquareInternal.frameVec_eq, sum_inner]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, real_inner_smul_left, mul_comm]
  rfl

theorem frameVec_cyl (r θ z : ℝ) (i : Fin 3) : frameVec θ (cylPoint r θ z) i = ![r, 0, z] i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, cylPoint, radialUnit, angularUnit, axialUnit, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_right] <;>
    first
      | linear_combination r * hs
      | ring

theorem frameVec_turn_cyl (r θ z : ℝ) (i : Fin 3) : frameVec θ (axialTurn (cylPoint r θ z)) i = ![0, r, 0] i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, cylPoint, axialTurn, radialUnit, angularUnit, axialUnit, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_right] <;>
    first
      | linear_combination r * hs
      | ring

theorem frameVec_turn (θ : ℝ) (w : Space) (i : Fin 3) :
    frameVec θ (axialTurn w) i = ![-frameVec θ w 1, frameVec θ w 0, 0] i := by
  fin_cases i <;>
    simp [frameVec, axialTurn, radialUnit, angularUnit, axialUnit, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_right] <;>
    ring

theorem frameVec_drift (α a0 r θ z : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (i : Fin 3) :
    frameVec θ (driftField α a0 v G (cylPoint r θ z)) i =
      (1 - 1 / (2 * α)) * frameVec θ (v (cylPoint r θ z)) i
        + (1 / (2 * α)) * ∑ b : Fin 3, frameMat θ (G (cylPoint r θ z)) i b * ![r, 0, z] b
        + a0 * (∑ b : Fin 3, frameMat θ (G (cylPoint r θ z)) i b * ![0, r, 0] b
          - ![-frameVec θ (v (cylPoint r θ z)) 1, frameVec θ (v (cylPoint r θ z)) 0, 0] i) := by
  have hlin : ∀ u w : Space, frameVec θ (u + w) i = frameVec θ u i + frameVec θ w i := fun u w => by
    rw [ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq,
      inner_add_left]
  have hsub : ∀ u w : Space, frameVec θ (u - w) i = frameVec θ u i - frameVec θ w i := fun u w => by
    rw [ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq,
      inner_sub_left]
  have hsm : ∀ (s : ℝ) (u : Space), frameVec θ (s • u) i = s * frameVec θ u i := fun s u => by
    rw [ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq, real_inner_smul_left]
  unfold driftField
  rw [hlin, hlin, hsm, hsm, hsm, hsub, frameVec_apply_clm, frameVec_apply_clm, frameVec_turn]
  simp only [frameVec_cyl, frameVec_turn_cyl]

theorem modeVec_drift (m : ℕ) (n : ℤ) (α a0 : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ)
    (hv : ∀ b, IntervalIntegrable (fun θ => frameVec θ (v (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi))
    (hG : ∀ a b, IntervalIntegrable (fun θ => frameMat θ (G (cylPoint p.1 θ p.2)) a b) volume 0 (2 * Real.pi))
    (i : Fin 3) :
    modeVec m n (driftField α a0 v G) p.1 p.2 i =
      ((1 - 1 / (2 * α) : ℝ) : ℂ) * modeVec m n v p.1 p.2 i
        + ((1 / (2 * α) : ℝ) : ℂ) * ∑ b : Fin 3, gradMode m n G i b p * frameY p b
        + (a0 : ℂ) * (∑ b : Fin 3, gradMode m n G i b p * frameTurnY p b - turnC (modeVec m n v p.1 p.2) i) := by
  have hE : Continuous (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) := by fun_prop
  have hvC : ∀ b, IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (v (cylPoint p.1 θ p.2)) b : ℂ)) volume 0 (2 * Real.pi) := fun b =>
    (show IntervalIntegrable (fun θ => (frameVec θ (v (cylPoint p.1 θ p.2)) b : ℂ)) volume 0 (2 * Real.pi) from
      ⟨(hv b).1.ofReal, (hv b).2.ofReal⟩).continuousOn_mul hE.continuousOn
  have hGC : ∀ b, IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameMat θ (G (cylPoint p.1 θ p.2)) i b : ℂ)) volume 0 (2 * Real.pi) := fun b =>
    (show IntervalIntegrable (fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) i b : ℂ)) volume 0 (2 * Real.pi) from
      ⟨(hG i b).1.ofReal, (hG i b).2.ofReal⟩).continuousOn_mul hE.continuousOn
  set cv : Fin 3 → ℂ := fun b => (((1 - 1 / (2 * α)) * (if b = i then 1 else 0)
    - a0 * ![![0, -1, 0], ![1, 0, 0], ![0, 0, 0]] i b : ℝ) : ℂ) with hcv
  set cg : Fin 3 → ℂ := fun b => (((1 / (2 * α)) * ![p.1, 0, p.2] b + a0 * ![0, p.1, 0] b : ℝ) : ℂ) with hcg
  have hpt : ∀ θ : ℝ, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (driftField α a0 v G (cylPoint p.1 θ p.2)) i : ℂ) =
      (∑ b : Fin 3, cv b * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint p.1 θ p.2)) b : ℂ)))
      + ∑ b : Fin 3, cg b * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameMat θ (G (cylPoint p.1 θ p.2)) i b : ℂ)) := by
    intro θ
    rw [frameVec_drift]
    simp only [hcv, hcg]
    fin_cases i <;> simp [Fin.sum_univ_three] <;> ring
  have hint : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (driftField α a0 v G (cylPoint p.1 θ p.2)) i : ℂ) =
      (∑ b : Fin 3, cv b * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameVec θ (v (cylPoint p.1 θ p.2)) b : ℂ))
      + ∑ b : Fin 3, cg b * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameMat θ (G (cylPoint p.1 θ p.2)) i b : ℂ) := by
    have hsum : ∀ {g : Fin 3 → ℝ → ℂ}, (∀ b, IntervalIntegrable (g b) volume 0 (2 * Real.pi)) →
        IntervalIntegrable (fun θ => ∑ b : Fin 3, g b θ) volume 0 (2 * Real.pi) := fun h => by
      have := IntervalIntegrable.sum Finset.univ fun b _ => h b
      rwa [Finset.sum_fn] at this
    simp_rw [hpt]
    rw [intervalIntegral.integral_add
        (hsum (g := fun b θ => cv b * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameVec θ (v (cylPoint p.1 θ p.2)) b : ℂ))) fun b => (hvC b).const_mul (cv b))
        (hsum (g := fun b θ => cg b * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
          (frameMat θ (G (cylPoint p.1 θ p.2)) i b : ℂ))) fun b => (hGC b).const_mul (cg b)),
      intervalIntegral.integral_finsetSum fun b _ => (hvC b).const_mul (cv b),
      intervalIntegral.integral_finsetSum fun b _ => (hGC b).const_mul (cg b)]
    simp_rw [intervalIntegral.integral_const_mul]
  show (1 / (2 * Real.pi) : ℂ) * _ = _
  rw [hint]
  simp only [modeVec, gradMode, modeMat, hcv, hcg, frameY, frameTurnY, turnC]
  fin_cases i <;> simp [Fin.sum_univ_three] <;> ring

theorem drift_pair_split (m : ℕ) (n : ℤ) (α a0 ν : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (p : ℝ × ℝ)
    (hv : ∀ b, IntervalIntegrable (fun θ => frameVec θ (v (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi))
    (hG : ∀ a b, IntervalIntegrable (fun θ => frameMat θ (G (cylPoint p.1 θ p.2)) a b) volume 0 (2 * Real.pi))
    (X : Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℂ) :
    pairC (modeVec m n (driftField α a0 v G) p.1 p.2) X
        + (ν : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, gradMode m n G a b p * (starRingEnd ℂ) (Y a b) =
      (∑ a : Fin 3, ∑ b : Fin 3, gradMode m n G a b p *
          (((1 / (2 * α) : ℝ) : ℂ) * frameY p b * (starRingEnd ℂ) (X a)
            + (a0 : ℂ) * frameTurnY p b * (starRingEnd ℂ) (X a) + (ν : ℂ) * (starRingEnd ℂ) (Y a b)))
      + ∑ a : Fin 3, modeVec m n v p.1 p.2 a *
          (((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (X a) - (a0 : ℂ) * pairC (turnC (Pi.single a 1)) X) := by
  unfold pairC
  simp_rw [modeVec_drift m n α a0 v G p hv hG]
  simp [Fin.sum_univ_three, turnC, Pi.single_apply]
  ring

theorem frameVec_cross (θ : ℝ) (u w : Space) (i : Fin 3) :
    frameVec θ (crossVec u w) i =
      ![frameVec θ u 1 * frameVec θ w 2 - frameVec θ u 2 * frameVec θ w 1,
        frameVec θ u 2 * frameVec θ w 0 - frameVec θ u 0 * frameVec θ w 2,
        frameVec θ u 0 * frameVec θ w 1 - frameVec θ u 1 * frameVec θ w 0] i := by
  have hs := Real.sin_sq_add_cos_sq θ
  fin_cases i <;>
    simp [frameVec, crossVec, radialUnit, angularUnit, axialUnit, inner_add_right, inner_add_left,
      EuclideanSpace.inner_single_right] <;>
    first
      | ring1
      | linear_combination (u.ofLp 0 * w.ofLp 1 - u.ofLp 1 * w.ofLp 0) * hs
      | linear_combination (-(u.ofLp 0 * w.ofLp 1 - u.ofLp 1 * w.ofLp 0)) * hs
      | linear_combination (u.ofLp 1 * w.ofLp 0 - u.ofLp 0 * w.ofLp 1) * hs

theorem frame_orthonormal (θ : ℝ) (a b : Fin 3) :
    inner ℝ (frameUnit θ a) (frameUnit θ b) = if a = b then 1 else 0 := by
  have hs := Real.sin_sq_add_cos_sq θ
  rw [PiLp.inner_apply]
  fin_cases a <;> fin_cases b <;>
    simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit] <;>
    first
      | ring1
      | linear_combination hs

theorem frameMat_cartOp (θ : ℝ) (M : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) :
    frameMat θ (cartOpOfFrame θ M) a b = M a b := by
  show inner ℝ (cartOpOfFrame θ M (frameUnit θ b)) (frameUnit θ a) = M a b
  unfold cartOpOfFrame
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, frame_orthonormal, smul_eq_mul, sum_inner,
    real_inner_smul_left, inner_smul_left]
  simp [Fin.sum_univ_three]

theorem frameVec_cartOf (θ : ℝ) (w : Fin 3 → ℝ) (a : Fin 3) : frameVec θ (cartOfFrame θ w) a = w a := by
  rw [ModeVelSquareInternal.frameVec_eq]
  unfold cartOfFrame
  simp only [sum_inner, real_inner_smul_left, frame_orthonormal]
  fin_cases a <;> simp [Fin.sum_univ_three]

theorem cylAngle_cyl {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    ∃ k : ℤ, cylAngle (cylPoint r θ z) = θ - k * (2 * Real.pi) := by
  refine ⟨toIocDiv (mul_pos two_pos Real.pi_pos) (-Real.pi) θ, ?_⟩
  have e : (((cylPoint r θ z) 0 : ℝ) : ℂ) + (((cylPoint r θ z) 1 : ℝ) : ℂ) * Complex.I =
      (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I]
    simp [cylPoint]
    push_cast
    ring
  unfold cylAngle
  rw [e, Complex.arg_real_mul _ hr, Complex.arg_exp_mul_I, ← self_sub_toIocDiv_zsmul, zsmul_eq_mul]

theorem frameUnit_shift (θ : ℝ) (k : ℤ) (j : Fin 3) : frameUnit (θ - k * (2 * Real.pi)) j = frameUnit θ j := by
  fin_cases j <;> simp [frameUnit, radialUnit, angularUnit, Real.cos_sub_int_mul_two_pi, Real.sin_sub_int_mul_two_pi]

theorem exp_shift (m : ℕ) (n k : ℤ) (θ : ℝ) :
    Complex.exp ((azimuth m n * (θ - k * (2 * Real.pi)) : ℝ) * Complex.I) =
      Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) := by
  have h : ((azimuth m n * (θ - k * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I =
      ((azimuth m n * θ : ℝ) : ℂ) * Complex.I + ((-(n * m * k)) : ℤ) * (2 * Real.pi * Complex.I) := by
    unfold azimuth; push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem mirrorSign_upper {r θ z : ℝ} (hz : 0 ≤ z) (j : Fin 3) : mirrorSign (cylPoint r θ z) j = 1 := by
  unfold mirrorSign
  rw [CellDensityModesSolid.cyl_height]
  simp [not_lt.2 hz]

theorem lowGrad_frame {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (G : Space → (Space →L[ℝ] Space)) {r θ z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (a b : Fin 3) :
    frameMat θ (lowGradField c K S G (cylPoint r θ z)) a b =
      (∑ n ∈ S.resolved, K.lowStrain c.order n S.degHigh G a b (r, z) *
        Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
  obtain ⟨kk, hk⟩ := cylAngle_cyl hr θ z
  have hcart : ∀ M, cartOpOfFrame (θ - kk * (2 * Real.pi)) M = cartOpOfFrame θ M := by
    intro M; unfold cartOpOfFrame; simp only [frameUnit_shift]
  unfold lowGradField
  rw [hk, hcart, CellDensityModesSolid.cyl_radius hr.le, CellDensityModesSolid.cyl_height, abs_of_nonneg hz,
    frameMat_cartOp]
  simp only [mirrorSign_upper hz, one_mul, exp_shift]

theorem lowVel_frame {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars)
    (v : Space → Space) {r θ z : ℝ} (hr : 0 < r) (hz : 0 ≤ z) (a : Fin 3) :
    frameVec θ (lowVelocityField c K S v (cylPoint r θ z)) a =
      (∑ n ∈ S.resolved, K.lowVelocity c.order n S.degHigh v a (r, z) *
        Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
  obtain ⟨kk, hk⟩ := cylAngle_cyl hr θ z
  have hcart : ∀ w, cartOfFrame (θ - kk * (2 * Real.pi)) w = cartOfFrame θ w := by
    intro w; unfold cartOfFrame; simp only [frameUnit_shift]
  unfold lowVelocityField
  rw [hk, hcart, CellDensityModesSolid.cyl_radius hr.le, CellDensityModesSolid.cyl_height, abs_of_nonneg hz,
    frameVec_cartOf]
  simp only [mirrorSign_upper hz, one_mul, exp_shift]

theorem frameVec_curl (θ : ℝ) (M : Space →L[ℝ] Space) (i : Fin 3) :
    frameVec θ (curlOf M) i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * frameMat θ M l j := by
  have hs := Real.sin_sq_add_cos_sq θ
  have hr : radialUnit θ = Real.cos θ • unitVector 0 + Real.sin θ • unitVector 1 := by
    ext j; fin_cases j <;> simp [radialUnit, unitVector]
  have ha : angularUnit θ = (-Real.sin θ) • unitVector 0 + Real.cos θ • unitVector 1 := by
    ext j; fin_cases j <;> simp [angularUnit, unitVector]
  have hz : axialUnit = unitVector 2 := rfl
  have hframe : ∀ a b : Fin 3, frameMat θ M a b = inner ℝ (M (frameUnit θ b)) (frameUnit θ a) := fun _ _ => rfl
  simp only [hframe]
  rw [ModeVelSquareInternal.frameVec_eq]
  simp only [curlOf, sum_inner, real_inner_smul_left]
  fin_cases i <;>
    simp [Fin.sum_univ_three, permSign, frameUnit, hr, ha, hz, entry, map_add, map_smul, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right, unitVector,
      EuclideanSpace.inner_single_right, EuclideanSpace.inner_single_left] <;>
    ring_nf <;>
    (try simp only [Real.cos_sq']) <;>
    ring_nf

theorem mode_re_mul (mo : ℕ) (m : ℤ) (s : Finset ℤ) (A : ℤ → ℂ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
        ((((∑ n ∈ s, A n * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re * f θ : ℝ)) : ℂ) =
      (1 / 2 : ℂ) * ∑ n ∈ s, (A n * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth mo (m - n) * θ : ℝ) * Complex.I) * (f θ : ℂ))
        + (starRingEnd ℂ) (A n) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Complex.exp (-(azimuth mo (m + n) * θ : ℝ) * Complex.I) * (f θ : ℂ))) := by
  have h1 : ∀ (n : ℤ) (θ : ℝ), Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
      Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I) = Complex.exp (-(azimuth mo (m - n) * θ : ℝ) * Complex.I) := by
    intro n θ
    rw [← Complex.exp_add]
    congr 1
    unfold azimuth
    push_cast
    ring
  have h2 : ∀ (n : ℤ) (θ : ℝ), Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)) =
        Complex.exp (-(azimuth mo (m + n) * θ : ℝ) * Complex.I) := by
    intro n θ
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add]
    congr 1
    unfold azimuth
    push_cast
    ring
  have hpt : ∀ θ : ℝ, Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
      ((((∑ n ∈ s, A n * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re * f θ : ℝ)) : ℂ) =
      (1 / 2 : ℂ) * ∑ n ∈ s, (A n * (Complex.exp (-(azimuth mo (m - n) * θ : ℝ) * Complex.I) * (f θ : ℂ))
        + (starRingEnd ℂ) (A n) * (Complex.exp (-(azimuth mo (m + n) * θ : ℝ) * Complex.I) * (f θ : ℂ))) := by
    intro θ
    rw [Complex.ofReal_mul _ (f θ), Complex.re_eq_add_conj, map_sum]
    simp only [map_mul]
    rw [← Finset.sum_add_distrib, Finset.sum_div, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← h1 n θ, ← h2 n θ]
    ring
  have hE : ∀ k : ℤ, IntervalIntegrable (fun θ : ℝ => Complex.exp (-(azimuth mo k * θ : ℝ) * Complex.I) * (f θ : ℂ))
      volume 0 (2 * Real.pi) := fun k =>
    (show IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) from ⟨hf.1.ofReal, hf.2.ofReal⟩).continuousOn_mul
      (by fun_prop : Continuous (fun θ : ℝ => Complex.exp (-(azimuth mo k * θ : ℝ) * Complex.I))).continuousOn
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum fun n _ =>
    ((hE (m - n)).const_mul (A n)).add ((hE (m + n)).const_mul ((starRingEnd ℂ) (A n)))]
  simp_rw [intervalIntegral.integral_add ((hE _).const_mul _) ((hE _).const_mul _), intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

theorem mode_integral_neg (m : ℕ) (n : ℤ) (g : ℝ → ℝ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m (-n) * θ : ℝ) * Complex.I) * (g θ : ℂ) =
      (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (g θ : ℂ)) := by
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun θ => ?_)
  simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I]
  have e : -(((azimuth m (-n) * θ : ℝ)) : ℂ) * Complex.I = -(((azimuth m n * θ : ℝ)) : ℂ) * -Complex.I := by
    unfold azimuth; push_cast; ring
  rw [e]

theorem modeMat_neg (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m (-n) G r z a b = (starRingEnd ℂ) (modeMat m n G r z a b) := by
  simp only [modeMat]
  rw [mode_integral_neg, map_mul]
  congr 1
  simp [map_ofNat]

theorem modeVec_neg (m : ℕ) (n : ℤ) (v : Space → Space) (r z : ℝ) (a : Fin 3) :
    modeVec m (-n) v r z a = (starRingEnd ℂ) (modeVec m n v r z a) := by
  simp only [modeVec]
  rw [mode_integral_neg, map_mul]
  congr 1
  simp [map_ofNat]

theorem coef_conj_fn (B : CellBases) (K : CellBox) (F : ℝ × ℝ → ℂ) (j l : ℕ) :
    B.coef K (fun q => (starRingEnd ℂ) (F q)) j l = (starRingEnd ℂ) (B.coef K F j l) := by
  unfold CellBases.coef
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun q => ?_)
  simp only [map_mul, Complex.conj_ofReal]

theorem proj_conj_fn {K : CellBox} {B : CellBases} (hB : IsCellBases K B) {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (d d' : ℕ) (p : ℝ × ℝ) :
    K.proj d d' (fun q => (starRingEnd ℂ) (F q)) p = (starRingEnd ℂ) (K.proj d d' F p) := by
  have hF' : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (starRingEnd ℂ) (F p)) K.rect := by
    have h := ContinuousLinearMap.integrable_comp (Complex.conjCLE.toContinuousLinearMap) hF
    refine h.congr (ae_of_all _ fun q => ?_)
    simp [map_mul, Complex.conj_ofReal]
  rw [proj_expand K hB hF' d d' p, proj_expand K hB hF d d' p, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coef_conj_fn, map_mul]
  simp [basisC, Complex.conj_ofReal]

theorem lowStrain_neg {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (m : ℕ) (n : ℤ) (Q : ℕ)
    (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3)
    (hG : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p) K.rect) (p : ℝ × ℝ) :
    K.lowStrain m (-n) Q G a b p = (starRingEnd ℂ) (K.lowStrain m n Q G a b p) := by
  have e : gradMode m (-n) G a b = fun q => (starRingEnd ℂ) (gradMode m n G a b q) :=
    funext fun q => modeMat_neg m n G q.1 q.2 a b
  unfold CellBox.lowStrain
  rw [e]
  exact proj_conj_fn hB hG Q Q p

theorem lowVelocity_neg {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (m : ℕ) (n : ℤ) (Q : ℕ)
    (v : Space → Space) (a : Fin 3)
    (hv : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect) (p : ℝ × ℝ) :
    K.lowVelocity m (-n) Q v a p = (starRingEnd ℂ) (K.lowVelocity m n Q v a p) := by
  have e : (fun q : ℝ × ℝ => modeVec m (-n) v q.1 q.2 a) = fun q => (starRingEnd ℂ) (modeVec m n v q.1 q.2 a) :=
    funext fun q => modeVec_neg m n v q.1 q.2 a
  unfold CellBox.lowVelocity
  rw [e]
  exact proj_conj_fn hB hv (Q - 1) (Q - 1) p

theorem modeVec_add_fn (m : ℕ) (n : ℤ) (u w : Space → Space) (r z : ℝ) (a : Fin 3)
    (hu : IntervalIntegrable (fun θ => frameVec θ (u (cylPoint r θ z)) a) volume 0 (2 * Real.pi))
    (hw : IntervalIntegrable (fun θ => frameVec θ (w (cylPoint r θ z)) a) volume 0 (2 * Real.pi)) :
    modeVec m n (fun y => u y + w y) r z a = modeVec m n u r z a + modeVec m n w r z a := by
  have hE : Continuous (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) := by fun_prop
  have hu' : IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (u (cylPoint r θ z)) a : ℂ)) volume 0 (2 * Real.pi) :=
    (show IntervalIntegrable (fun θ => (frameVec θ (u (cylPoint r θ z)) a : ℂ)) volume 0 (2 * Real.pi) from
      ⟨hu.1.ofReal, hu.2.ofReal⟩).continuousOn_mul hE.continuousOn
  have hw' : IntervalIntegrable (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (w (cylPoint r θ z)) a : ℂ)) volume 0 (2 * Real.pi) :=
    (show IntervalIntegrable (fun θ => (frameVec θ (w (cylPoint r θ z)) a : ℂ)) volume 0 (2 * Real.pi) from
      ⟨hw.1.ofReal, hw.2.ofReal⟩).continuousOn_mul hE.continuousOn
  simp only [modeVec]
  rw [← mul_add, ← intervalIntegral.integral_add hu' hw']
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  show _ * ((frameVec θ (u (cylPoint r θ z) + w (cylPoint r θ z)) a : ℝ) : ℂ) = _
  rw [ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq, ModeVelSquareInternal.frameVec_eq,
    inner_add_left]
  push_cast
  ring

theorem mode_re_mul_integrable (mo : ℕ) (n : ℤ) (s : Finset ℤ) (A : ℤ → ℂ) (f : ℝ → ℝ)
    (hf : IntervalIntegrable f volume 0 (2 * Real.pi)) :
    IntervalIntegrable (fun θ => Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
      ((((∑ k ∈ s, A k * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * f θ : ℝ)) : ℂ)) volume 0 (2 * Real.pi) := by
  have hc : Continuous (fun θ : ℝ => Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
      (((∑ k ∈ s, A k * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re : ℝ) : ℂ)) := by fun_prop
  have h := (show IntervalIntegrable (fun θ => (f θ : ℂ)) volume 0 (2 * Real.pi) from
    ⟨hf.1.ofReal, hf.2.ofReal⟩).continuousOn_mul hc.continuousOn
  refine h.congr fun θ _ => ?_
  push_cast
  ring

theorem mode_cross_re (mo : ℕ) (n : ℤ) (s : Finset ℤ) (X : ℤ → Fin 3 → ℂ) (F : ℝ → Fin 3 → ℝ)
    (hF : ∀ b, IntervalIntegrable (fun θ => F θ b) volume 0 (2 * Real.pi)) (i : Fin 3) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
        ((![(∑ k ∈ s, X k 1 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 2
            - (∑ k ∈ s, X k 2 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 1,
          (∑ k ∈ s, X k 2 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 0
            - (∑ k ∈ s, X k 0 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 2,
          (∑ k ∈ s, X k 0 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 1
            - (∑ k ∈ s, X k 1 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ 0] i : ℝ) : ℂ) =
      (1 / 2 : ℂ) * ∑ k ∈ s,
        (crossC (X k) (fun b => (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (n - k) * θ : ℝ) * Complex.I) * (F θ b : ℂ)) i
          + crossC (fun j => (starRingEnd ℂ) (X k j)) (fun b => (1 / (2 * Real.pi) : ℂ) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo (n + k) * θ : ℝ) * Complex.I) * (F θ b : ℂ)) i) := by
  have key : ∀ a b : Fin 3, (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
        ((((∑ k ∈ s, X k a * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ b
          - (∑ k ∈ s, X k b * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ a : ℝ)) : ℂ) =
      (1 / 2 : ℂ) * ∑ k ∈ s, ((X k a * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (n - k) * θ : ℝ) * Complex.I) * (F θ b : ℂ))
          + (starRingEnd ℂ) (X k a) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (n + k) * θ : ℝ) * Complex.I) * (F θ b : ℂ)))
        - (X k b * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (n - k) * θ : ℝ) * Complex.I) * (F θ a : ℂ))
          + (starRingEnd ℂ) (X k b) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (n + k) * θ : ℝ) * Complex.I) * (F θ a : ℂ)))) := by
    intro a b
    have e : (fun θ : ℝ => Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
        ((((∑ k ∈ s, X k a * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ b
          - (∑ k ∈ s, X k b * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ a : ℝ)) : ℂ)) =
        fun θ => Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
          ((((∑ k ∈ s, X k a * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ b : ℝ)) : ℂ)
        - Complex.exp (-(azimuth mo n * θ : ℝ) * Complex.I) *
          ((((∑ k ∈ s, X k b * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * F θ a : ℝ)) : ℂ) := by
      funext θ
      rw [Complex.ofReal_sub, mul_sub]
    rw [e, intervalIntegral.integral_sub (mode_re_mul_integrable mo n s _ _ (hF b))
      (mode_re_mul_integrable mo n s _ _ (hF a)), mul_sub, mode_re_mul mo n s _ _ (hF b),
      mode_re_mul mo n s _ _ (hF a), ← mul_sub, ← Finset.sum_sub_distrib]
  fin_cases i
  · refine Eq.trans ?_ ((key 1 2).trans ?_)
    · congr 1
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [crossC]
    ring
  · refine Eq.trans ?_ ((key 2 0).trans ?_)
    · congr 1
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [crossC]
    ring
  · refine Eq.trans ?_ ((key 0 1).trans ?_)
    · congr 1
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [crossC]
    ring

theorem mode_cross_gen (mo : ℕ) (m : ℤ) (s : Finset ℤ) (hs : ∀ n, n ∈ s ↔ -n ∈ s) (X : ℤ → Fin 3 → ℂ)
    (hX : ∀ k j, X (-k) j = (starRingEnd ℂ) (X k j)) (A B : ℝ → Space)
    (hA : ∀ θ j, frameVec θ (A θ) j = (∑ k ∈ s, X k j * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re)
    (hB : ∀ b, IntervalIntegrable (fun θ => frameVec θ (B θ) b) volume 0 (2 * Real.pi)) (i : Fin 3) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
        (frameVec θ (crossVec (A θ) (B θ)) i : ℂ) =
      ∑ k ∈ s, crossC (X k) (fun b => (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (m - k) * θ : ℝ) * Complex.I) * (frameVec θ (B θ) b : ℂ)) i := by
  have e : ∀ θ, frameVec θ (crossVec (A θ) (B θ)) i =
      ![(∑ k ∈ s, X k 1 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 2
            - (∑ k ∈ s, X k 2 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 1,
          (∑ k ∈ s, X k 2 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 0
            - (∑ k ∈ s, X k 0 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 2,
          (∑ k ∈ s, X k 0 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 1
            - (∑ k ∈ s, X k 1 * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re * frameVec θ (B θ) 0] i := by
    intro θ
    rw [frameVec_cross, hA, hA, hA]
  simp_rw [e]
  refine (mode_cross_re mo m s X (fun θ b => frameVec θ (B θ) b) hB i).trans ?_
  rw [Finset.sum_add_distrib]
  have hQ : ∑ k ∈ s, crossC (fun j => (starRingEnd ℂ) (X k j)) (fun b => (1 / (2 * Real.pi) : ℂ) *
            ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo (m + k) * θ : ℝ) * Complex.I) *
              (frameVec θ (B θ) b : ℂ)) i =
      ∑ k ∈ s, crossC (X k) (fun b => (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (m - k) * θ : ℝ) * Complex.I) * (frameVec θ (B θ) b : ℂ)) i := by
    refine Finset.sum_equiv (Equiv.neg ℤ) (fun k => hs k) fun k _ => ?_
    have hc : (fun j => (starRingEnd ℂ) (X k j)) = X (-k) := funext fun j => (hX k j).symm
    simp only [Equiv.neg_apply, hc, sub_neg_eq_add]
  rw [hQ]
  ring

theorem crossC_swap (u w : Fin 3 → ℂ) (i : Fin 3) : crossC u w i = -crossC w u i := by
  fin_cases i <;> simp [crossC] <;> ring

theorem frameVec_cross_swap (θ : ℝ) (u w : Space) (i : Fin 3) :
    frameVec θ (crossVec u w) i = -frameVec θ (crossVec w u) i := by
  rw [frameVec_cross, frameVec_cross]
  fin_cases i <;> simp <;> ring

theorem mode_cross_gen_right (mo : ℕ) (m : ℤ) (s : Finset ℤ) (hs : ∀ n, n ∈ s ↔ -n ∈ s) (X : ℤ → Fin 3 → ℂ)
    (hX : ∀ k j, X (-k) j = (starRingEnd ℂ) (X k j)) (A B : ℝ → Space)
    (hA : ∀ θ j, frameVec θ (A θ) j = (∑ k ∈ s, X k j * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re)
    (hB : ∀ b, IntervalIntegrable (fun θ => frameVec θ (B θ) b) volume 0 (2 * Real.pi)) (i : Fin 3) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth mo m * θ : ℝ) * Complex.I) *
        (frameVec θ (crossVec (B θ) (A θ)) i : ℂ) =
      ∑ k ∈ s, crossC (fun b => (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Complex.exp (-(azimuth mo (m - k) * θ : ℝ) * Complex.I) * (frameVec θ (B θ) b : ℂ)) (X k) i := by
  simp_rw [frameVec_cross_swap _ (B _) (A _) i]
  simp only [Complex.ofReal_neg, mul_neg, intervalIntegral.integral_neg]
  rw [mode_cross_gen mo m s hs X hX A B hA hB i, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [crossC_swap, neg_neg]

theorem curl_frame_re (mo : ℕ) (s : Finset ℤ) (θ : ℝ) (M : Space →L[ℝ] Space) (Λ : ℤ → Fin 3 → Fin 3 → ℂ)
    (h : ∀ a b, frameMat θ M a b = (∑ n ∈ s, Λ n a b * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re)
    (i : Fin 3) :
    frameVec θ (curlOf M) i =
      (∑ n ∈ s, curlComp (Λ n) i * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re := by
  rw [frameVec_curl]
  simp only [h, Complex.re_sum]
  have e2 : ∀ n, (curlComp (Λ n) i * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re =
      ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l *
        (Λ n l j * Complex.exp ((azimuth mo n * θ : ℝ) * Complex.I)).re := by
    intro n
    simp only [curlComp, Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    rw [mul_assoc, Complex.re_ofReal_mul]
  simp_rw [e2, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

theorem curlComp_conj (Λ : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (fun a b => (starRingEnd ℂ) (Λ a b)) i = (starRingEnd ℂ) (curlComp Λ i) := by
  simp only [curlComp, map_sum, map_mul, Complex.conj_ofReal]


theorem frameVec_add (θ : ℝ) (u w : Space) (i : Fin 3) : frameVec θ (u + w) i = frameVec θ u i + frameVec θ w i := by
  fin_cases i <;> simp [frameVec, inner_add_left]

theorem cross_integrable (mo : ℕ) (s : Finset ℤ) (X : ℤ → Fin 3 → ℂ) (A B : ℝ → Space)
    (hA : ∀ θ j, frameVec θ (A θ) j = (∑ k ∈ s, X k j * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re)
    (hB : ∀ b, IntervalIntegrable (fun θ => frameVec θ (B θ) b) volume 0 (2 * Real.pi)) (i : Fin 3) :
    IntervalIntegrable (fun θ => frameVec θ (crossVec (A θ) (B θ)) i) volume 0 (2 * Real.pi) := by
  have hc : ∀ j, ContinuousOn (fun θ => frameVec θ (A θ) j) (Set.uIcc 0 (2 * Real.pi)) := by
    intro j
    have e : (fun θ => frameVec θ (A θ) j) =
        fun θ => (∑ k ∈ s, X k j * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re := funext fun θ => hA θ j
    rw [e]
    exact Continuous.continuousOn (by unfold azimuth; fun_prop)
  have e : (fun θ => frameVec θ (crossVec (A θ) (B θ)) i) = fun θ =>
      ![frameVec θ (A θ) 1 * frameVec θ (B θ) 2 - frameVec θ (A θ) 2 * frameVec θ (B θ) 1,
        frameVec θ (A θ) 2 * frameVec θ (B θ) 0 - frameVec θ (A θ) 0 * frameVec θ (B θ) 2,
        frameVec θ (A θ) 0 * frameVec θ (B θ) 1 - frameVec θ (A θ) 1 * frameVec θ (B θ) 0] i :=
    funext fun θ => frameVec_cross θ (A θ) (B θ) i
  rw [e]
  fin_cases i
  · exact ((hB 2).continuousOn_mul (hc 1)).sub ((hB 1).continuousOn_mul (hc 2))
  · exact ((hB 0).continuousOn_mul (hc 2)).sub ((hB 2).continuousOn_mul (hc 0))
  · exact ((hB 1).continuousOn_mul (hc 0)).sub ((hB 0).continuousOn_mul (hc 1))

theorem cross_integrable_right (mo : ℕ) (s : Finset ℤ) (X : ℤ → Fin 3 → ℂ) (A B : ℝ → Space)
    (hA : ∀ θ j, frameVec θ (A θ) j = (∑ k ∈ s, X k j * Complex.exp ((azimuth mo k * θ : ℝ) * Complex.I)).re)
    (hB : ∀ b, IntervalIntegrable (fun θ => frameVec θ (B θ) b) volume 0 (2 * Real.pi)) (i : Fin 3) :
    IntervalIntegrable (fun θ => frameVec θ (crossVec (B θ) (A θ)) i) volume 0 (2 * Real.pi) := by
  have e : (fun θ => frameVec θ (crossVec (B θ) (A θ)) i) = fun θ => -frameVec θ (crossVec (A θ) (B θ)) i :=
    funext fun θ => frameVec_cross_swap θ (B θ) (A θ) i
  rw [e]
  exact (cross_integrable mo s X A B hA hB i).neg

theorem lowTransport_mode {α : ℝ} {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (hsym : ∀ n, n ∈ S.resolved ↔ -n ∈ S.resolved) {r z : ℝ} (hr : 0 < r) (hz : 0 ≤ z)
    (hΛ : ∀ n a b, K.lowStrain c.order (-n) S.degHigh x.2.1 a b (r, z) =
      (starRingEnd ℂ) (K.lowStrain c.order n S.degHigh x.2.1 a b (r, z)))
    (hU : ∀ n a, K.lowVelocity c.order (-n) S.degHigh x.1 a (r, z) =
      (starRingEnd ℂ) (K.lowVelocity c.order n S.degHigh x.1 a (r, z)))
    (hdr : ∀ b, IntervalIntegrable (fun θ => frameVec θ (driftField α c.modelRate x.1 x.2.1 (cylPoint r θ z)) b)
      volume 0 (2 * Real.pi))
    (hV : ∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelVelocity (cylPoint r θ z)) b) volume 0 (2 * Real.pi))
    (hW : ∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelCurl (cylPoint r θ z)) b) volume 0 (2 * Real.pi))
    (m : ℤ) (i : Fin 3) :
    modeVec c.order m (lowTransport c K S α x) r z i =
      modeVec c.order m (driftField α c.modelRate x.1 x.2.1) r z i +
        ∑ n ∈ S.resolved, (crossC (curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (r, z)))
            (modeVec c.order (m - n) c.modelVelocity r z) i
          + crossC (modeVec c.order (m - n) c.modelCurl r z) (K.lowVelocityAt c.order n S.degHigh x.1 (r, z)) i) := by
  obtain ⟨XA, hXA⟩ : ∃ XA : ℤ → Fin 3 → ℂ, XA = fun n => curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (r, z)) :=
    ⟨_, rfl⟩
  obtain ⟨XB, hXB⟩ : ∃ XB : ℤ → Fin 3 → ℂ, XB = fun n => K.lowVelocityAt c.order n S.degHigh x.1 (r, z) := ⟨_, rfl⟩
  have hA : ∀ θ j, frameVec θ (curlOf (lowGradField c K S x.2.1 (cylPoint r θ z))) j =
      (∑ n ∈ S.resolved, XA n j * Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
    intro θ j
    rw [hXA]
    exact curl_frame_re c.order S.resolved θ _ (fun n => K.lowStrainAt c.order n S.degHigh x.2.1 (r, z))
      (fun a b => lowGrad_frame c K S x.2.1 hr hz a b) j
  have hB : ∀ θ j, frameVec θ (lowVelocityField c K S x.1 (cylPoint r θ z)) j =
      (∑ n ∈ S.resolved, XB n j * Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
    intro θ j
    rw [hXB]
    exact lowVel_frame c K S x.1 hr hz j
  have hXA' : ∀ n j, XA (-n) j = (starRingEnd ℂ) (XA n j) := by
    intro n j
    rw [hXA]
    show curlComp (K.lowStrainAt c.order (-n) S.degHigh x.2.1 (r, z)) j =
      (starRingEnd ℂ) (curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (r, z)) j)
    rw [← curlComp_conj]
    have e : K.lowStrainAt c.order (-n) S.degHigh x.2.1 (r, z) =
        fun a b => (starRingEnd ℂ) (K.lowStrainAt c.order n S.degHigh x.2.1 (r, z) a b) :=
      funext fun a => funext fun b => hΛ n a b
    rw [e]
  have hXB' : ∀ n j, XB (-n) j = (starRingEnd ℂ) (XB n j) := by
    intro n j
    rw [hXB]
    exact hU n j
  have h1 := cross_integrable c.order S.resolved XA (fun θ => curlOf (lowGradField c K S x.2.1 (cylPoint r θ z)))
    (fun θ => c.modelVelocity (cylPoint r θ z)) hA hV
  have h2 := cross_integrable_right c.order S.resolved XB (fun θ => lowVelocityField c K S x.1 (cylPoint r θ z))
    (fun θ => c.modelCurl (cylPoint r θ z)) hB hW
  have h12 : ∀ b, IntervalIntegrable (fun θ => frameVec θ (driftField α c.modelRate x.1 x.2.1 (cylPoint r θ z)
      + crossVec (curlOf (lowGradField c K S x.2.1 (cylPoint r θ z))) (c.modelVelocity (cylPoint r θ z))) b)
      volume 0 (2 * Real.pi) := by
    intro b
    simp_rw [frameVec_add]
    exact (hdr b).add (h1 b)
  have e0 : lowTransport c K S α x = fun y => (fun y => driftField α c.modelRate x.1 x.2.1 y
      + crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) y
      + crossVec (c.modelCurl y) (lowVelocityField c K S x.1 y) := rfl
  have s1 : modeVec c.order m (lowTransport c K S α x) r z i =
      modeVec c.order m (fun y => driftField α c.modelRate x.1 x.2.1 y
        + crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) r z i
      + modeVec c.order m (fun y => crossVec (c.modelCurl y) (lowVelocityField c K S x.1 y)) r z i := by
    rw [e0]
    exact modeVec_add_fn c.order m (fun y => driftField α c.modelRate x.1 x.2.1 y
        + crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y))
      (fun y => crossVec (c.modelCurl y) (lowVelocityField c K S x.1 y)) r z i (h12 i) (h2 i)
  have s2 : modeVec c.order m (fun y => driftField α c.modelRate x.1 x.2.1 y
        + crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) r z i =
      modeVec c.order m (driftField α c.modelRate x.1 x.2.1) r z i
      + modeVec c.order m (fun y => crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) r z i :=
    modeVec_add_fn c.order m (driftField α c.modelRate x.1 x.2.1)
      (fun y => crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) r z i (hdr i) (h1 i)
  rw [s1, s2]
  have eA : modeVec c.order m (fun y => crossVec (curlOf (lowGradField c K S x.2.1 y)) (c.modelVelocity y)) r z i =
      ∑ n ∈ S.resolved, crossC (XA n) (modeVec c.order (m - n) c.modelVelocity r z) i := by
    unfold modeVec
    exact mode_cross_gen c.order m S.resolved hsym XA hXA' (fun θ => curlOf (lowGradField c K S x.2.1 (cylPoint r θ z)))
      (fun θ => c.modelVelocity (cylPoint r θ z)) hA hV i
  have eB : modeVec c.order m (fun y => crossVec (c.modelCurl y) (lowVelocityField c K S x.1 y)) r z i =
      ∑ n ∈ S.resolved, crossC (modeVec c.order (m - n) c.modelCurl r z) (XB n) i := by
    unfold modeVec
    exact mode_cross_gen_right c.order m S.resolved hsym XB hXB' (fun θ => lowVelocityField c K S x.1 (cylPoint r θ z))
      (fun θ => c.modelCurl (cylPoint r θ z)) hB hW i
  rw [eA, eB, Finset.sum_add_distrib, add_assoc, hXA, hXB]

theorem cross_pair_expand (Λ : Fin 3 → Fin 3 → ℂ) (U V W X : Fin 3 → ℂ) :
    pairC (fun i => crossC (curlComp Λ) V i + crossC W U i) X =
      (∑ a' : Fin 3, ∑ b' : Fin 3, Λ a' b' * pairC (crossC (fun i => (permSign i b' a' : ℂ)) V) X)
        + ∑ a' : Fin 3, U a' * pairC (crossC W (Pi.single a' 1)) X := by
  simp only [pairC, crossC, curlComp, Fin.sum_univ_three, permSign, Pi.single_apply]
  simp
  ring

theorem pairC_add (A B X : Fin 3 → ℂ) : pairC (fun i => A i + B i) X = pairC A X + pairC B X := by
  simp only [pairC, add_mul, Finset.sum_add_distrib]

theorem pairC_sum (s : Finset ℤ) (A : ℤ → Fin 3 → ℂ) (X : Fin 3 → ℂ) :
    pairC (fun i => ∑ n ∈ s, A n i) X = ∑ n ∈ s, pairC (A n) X := by
  simp only [pairC, Finset.sum_mul]
  exact Finset.sum_comm

theorem volume_pointwise {α : ℝ} {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (hsym : ∀ n, n ∈ S.resolved ↔ -n ∈ S.resolved) {p : ℝ × ℝ} (hr : 0 < p.1) (hz : 0 ≤ p.2)
    (hΛ : ∀ n a b, K.lowStrain c.order (-n) S.degHigh x.2.1 a b p =
      (starRingEnd ℂ) (K.lowStrain c.order n S.degHigh x.2.1 a b p))
    (hU : ∀ n a, K.lowVelocity c.order (-n) S.degHigh x.1 a p =
      (starRingEnd ℂ) (K.lowVelocity c.order n S.degHigh x.1 a p))
    (hdr : ∀ b, IntervalIntegrable (fun θ => frameVec θ (driftField α c.modelRate x.1 x.2.1 (cylPoint p.1 θ p.2)) b)
      volume 0 (2 * Real.pi))
    (hV : ∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelVelocity (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi))
    (hW : ∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelCurl (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi))
    (hv : ∀ b, IntervalIntegrable (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi))
    (hG : ∀ a b, IntervalIntegrable (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b) volume 0 (2 * Real.pi))
    (ν : ℝ) (m : ℤ) (X : Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℂ) :
    pairC (modeVec c.order m (lowTransport c K S α x) p.1 p.2) X
        + (ν : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, gradMode c.order m x.2.1 a b p * (starRingEnd ℂ) (Y a b) =
      (∑ a : Fin 3, ∑ b : Fin 3, gradMode c.order m x.2.1 a b p *
          (((1 / (2 * α) : ℝ) : ℂ) * frameY p b * (starRingEnd ℂ) (X a)
            + (c.modelRate : ℂ) * frameTurnY p b * (starRingEnd ℂ) (X a) + (ν : ℂ) * (starRingEnd ℂ) (Y a b)))
      + ∑ a : Fin 3, modeVec c.order m x.1 p.1 p.2 a *
          (((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (X a) - (c.modelRate : ℂ) * pairC (turnC (Pi.single a 1)) X)
      + ∑ n ∈ S.resolved, ((∑ a' : Fin 3, ∑ b' : Fin 3, K.lowStrain c.order n S.degHigh x.2.1 a' b' p *
            pairC (crossC (fun i => (permSign i b' a' : ℂ)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2)) X)
          + ∑ a' : Fin 3, K.lowVelocity c.order n S.degHigh x.1 a' p *
            pairC (crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2) (Pi.single a' 1)) X) := by
  have hpt : modeVec c.order m (lowTransport c K S α x) p.1 p.2 = fun i =>
      modeVec c.order m (driftField α c.modelRate x.1 x.2.1) p.1 p.2 i +
        ∑ n ∈ S.resolved, (crossC (curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (p.1, p.2)))
            (modeVec c.order (m - n) c.modelVelocity p.1 p.2) i
          + crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2)
              (K.lowVelocityAt c.order n S.degHigh x.1 (p.1, p.2)) i) :=
    funext fun i => lowTransport_mode c K S x hsym hr hz (fun n a b => hΛ n a b) (fun n a => hU n a) hdr hV hW m i
  rw [hpt, pairC_add, pairC_sum, add_right_comm, drift_pair_split c.order m α c.modelRate ν x.1 x.2.1 p hv hG X Y]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  exact cross_pair_expand _ _ _ _ X

theorem volume_mode_conj {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k}
    (hD : IsCellData α c K S B Cl R) (hx : IsAdmissible c x) :
    (∀ n a b p, K.lowStrain c.order (-n) S.degHigh x.2.1 a b p =
      (starRingEnd ℂ) (K.lowStrain c.order n S.degHigh x.2.1 a b p)) ∧
    (∀ n a p, K.lowVelocity c.order (-n) S.degHigh x.1 a p =
      (starRingEnd ℂ) (K.lowVelocity c.order n S.degHigh x.1 a p)) :=
  ⟨fun n a b p => lowStrain_neg hD.bases c.order n S.degHigh x.2.1 a b
      (CellAnalysis.LowEntry.Internal.gradMode_int K hD.box c.order n hx.1.measurable_gradient hx.1.gradient_two a b) p,
    fun n a p => lowVelocity_neg hD.bases c.order n S.degHigh x.1 a
      (CellAnalysis.LowEntry.Internal.modeVec_int K hD.box c.order n hx.1.velocity_six a) p⟩

theorem bounded_solid_integrable {K : CellBox} {F : Space → Space} {C : ℝ}
    (hf : volume K.solid < ⊤) (hF : AEStronglyMeasurable F volume) (hb : ∀ y ∈ K.solid, ‖F y‖ ≤ C) :
    IntegrableOn (fun y => ‖F y‖) K.solid := by
  have hm : MeasurableSet K.solid := CellDensityModesSolid.solid_closed K
  refine Integrable.mono' (integrableOn_const hf.ne) hF.norm.restrict ((ae_restrict_iff' hm).2 (ae_of_all _ fun y hy => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  exact hb y hy

theorem volume_circle_facts {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {x : FieldTuple k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (hx : IsAdmissible c x)
    (ha : a ∈ R.rowSet) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 →
      (∀ b, IntervalIntegrable (fun θ => frameVec θ (driftField α c.modelRate x.1 x.2.1 (cylPoint p.1 θ p.2)) b)
        volume 0 (2 * Real.pi)) ∧
      (∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelVelocity (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi)) ∧
      (∀ b, IntervalIntegrable (fun θ => frameVec θ (c.modelCurl (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi)) ∧
      (∀ b, IntervalIntegrable (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2)) b) volume 0 (2 * Real.pi)) ∧
      (∀ a b, IntervalIntegrable (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)) a b) volume 0 (2 * Real.pi)) := by
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  obtain ⟨hTm, hTi⟩ := lowTransport_on hc hD hx
  have hT := LayoutRowPressure.circle_integrable hD.box hTm hTi
  have hVi := LayoutRowPressure.circle_integrable hD.box hc.model_measurable.1
    (bounded_solid_integrable hTf hc.model_measurable.1 fun y hy => (hCM y (hD.solid_in_region hy)).1)
  have hWi := LayoutRowPressure.circle_integrable hD.box hc.model_measurable.2.1
    (bounded_solid_integrable hTf hc.model_measurable.2.1 fun y hy => (hCM y (hD.solid_in_region hy)).2.1)
  have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hTf.ne
  have hvI : IntegrableOn x.1 K.solid := (hx.1.velocity_six.restrict K.solid).integrable (by norm_num)
  have hvi := LayoutRowPressure.circle_integrable hD.box hx.1.velocity_six.aestronglyMeasurable hvI.norm
  have hGi := gradient_circle_integrable hc hD hR hx ha
  filter_upwards [ae_restrict_mem hrm, hT, hVi, hWi, hvi, hGi] with p hp hT hV hW hv hG hr
  have hz : 0 ≤ p.2 := le_trans hD.box.z_order.1 hp.2.1
  obtain ⟨hΛ, hU⟩ := volume_mode_conj hD hx
  have hA : ∀ θ j, frameVec θ (curlOf (lowGradField c K S x.2.1 (cylPoint p.1 θ p.2))) j =
      (∑ n ∈ S.resolved, curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (p.1, p.2)) j *
        Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := fun θ j =>
    curl_frame_re c.order S.resolved θ _ (fun n => K.lowStrainAt c.order n S.degHigh x.2.1 (p.1, p.2))
      (fun a b => lowGrad_frame c K S x.2.1 hr hz a b) j
  have hB : ∀ θ j, frameVec θ (lowVelocityField c K S x.1 (cylPoint p.1 θ p.2)) j =
      (∑ n ∈ S.resolved, K.lowVelocityAt c.order n S.degHigh x.1 (p.1, p.2) j *
        Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := fun θ j => lowVel_frame c K S x.1 hr hz j
  have h1 := cross_integrable c.order S.resolved (fun n => curlComp (K.lowStrainAt c.order n S.degHigh x.2.1 (p.1, p.2)))
    (fun θ => curlOf (lowGradField c K S x.2.1 (cylPoint p.1 θ p.2))) (fun θ => c.modelVelocity (cylPoint p.1 θ p.2)) hA hV
  have h2 := cross_integrable_right c.order S.resolved (fun n => K.lowVelocityAt c.order n S.degHigh x.1 (p.1, p.2))
    (fun θ => lowVelocityField c K S x.1 (cylPoint p.1 θ p.2)) (fun θ => c.modelCurl (cylPoint p.1 θ p.2)) hB hW
  refine ⟨fun b => ?_, hV, hW, hv, hG⟩
  refine (((hT b).sub (h1 b)).sub (h2 b)).congr fun θ _ => ?_
  rw [show lowTransport c K S α x (cylPoint p.1 θ p.2) = driftField α c.modelRate x.1 x.2.1 (cylPoint p.1 θ p.2)
      + crossVec (curlOf (lowGradField c K S x.2.1 (cylPoint p.1 θ p.2))) (c.modelVelocity (cylPoint p.1 θ p.2))
      + crossVec (c.modelCurl (cylPoint p.1 θ p.2)) (lowVelocityField c K S x.1 (cylPoint p.1 θ p.2)) from rfl,
    frameVec_add, frameVec_add]
  ring

theorem volume_mode_algebra {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    (∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes,
        pairC (modeVec c.order n (lowTransport c K S α x) p.1 p.2) (rowModeVec c a n p)).re)
      + c.splitVisc * (∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re) =
      (strainSum c α L R a x + velocitySum c α L R a x).re := by
  obtain ⟨hI1, hI2⟩ := volume_lhs_integrable hα1 hα2 hc hD hR hL hx ha
  obtain ⟨hΛ, hU⟩ := volume_mode_conj hD hx
  have hsym : ∀ n, n ∈ S.resolved ↔ -n ∈ S.resolved := hD.scalars.resolved_symm
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  rw [← volume_sum_identity hα1 hα2 hc hD hR hL hx ha, ← integral_const_mul, ← integral_add hI1 (hI2.const_mul _)]
  refine setIntegral_congr_ae hrm ?_
  filter_upwards [(ae_restrict_iff' hrm).1 (volume_circle_facts hc hD hR hx ha)] with p hf hp
  by_cases h0 : p.1 = 0
  · simp [h0]
  have hr : 0 < p.1 := lt_of_le_of_ne (le_trans hD.box.r_order.1 hp.1.1) (Ne.symm h0)
  have hz : 0 ≤ p.2 := le_trans hD.box.z_order.1 hp.2.1
  obtain ⟨hdr, hV, hW, hv, hG⟩ := hf hp hr
  have e : ∀ m ∈ R.rowModes, volumeDensity c K S α c.splitVisc x m (rowModeVec c a m p) (rowModeGrad c a m p) p =
      pairC (modeVec c.order m (lowTransport c K S α x) p.1 p.2) (rowModeVec c a m p)
        + (c.splitVisc : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3,
          gradMode c.order m x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a m p a' b') := by
    intro m _
    rw [volume_pointwise c K S x hsym hr hz (fun n a b => hΛ n a b p) (fun n a => hU n a p) hdr hV hW hv hG]
    rfl
  rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ← Finset.mul_sum, Complex.add_re, Complex.re_ofReal_mul]
  ring


theorem volume_identity_holds {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    (l2Pair (transportPart c α x) (c.row a) - l2Pair (highCouplingField c K S x.1 x.2.1) (c.row a)
        + c.splitVisc * LayoutRowParts.gradientPairing c x a) / (4 * Real.pi) =
      (strainSum c α L R a x + velocitySum c α L R a x).re := by
  obtain ⟨hDi, he⟩ := transport_sub_coupling hα1 hα2 hc hD hR hL hx ha
  obtain ⟨hm, hn⟩ := lowTransport_on hc hD hx
  have h := LayoutRowModes.pairing_modes hD.box (hD.rows_in_cell a ha) hDi
    (lowTransport_mirror hc hD hx) c.order R.rowModes (fun p n => rowModeVec c a n p)
    (LayoutRowPressure.row_expansion hc hD hR ha) (LayoutRowPressure.circle_integrable hD.box hm hn)
  rw [he, h, gradient_modes hα1 hα2 hc hD hR hL hx ha, ← volume_mode_algebra hα1 hα2 hc hD hR hL hx ha]
  field_simp

theorem scale_alg {ν A G s q : ℝ} (hq : q ≠ 0) (h : -(ν * A) = ν * G + s) :
    -(ν * (q * A)) / q = ν * (q * G) / q + s := by
  have e1 : -(ν * (q * A)) / q = -(ν * A) := by
    rw [show -(ν * (q * A)) = q * (-(ν * A)) by ring, mul_div_cancel_left₀ _ hq]
  have e2 : ν * (q * G) / q = ν * G := by
    rw [show ν * (q * G) = q * (ν * G) by ring, mul_div_cancel_left₀ _ hq]
  rw [e1, e2, h]

theorem viscous_mode_identity {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1)) :
    -(c.splitVisc * ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes,
        pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)).re) =
      c.splitVisc * (∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re) +
      (gradSideSum c L a x).re := by
  have hM := fun n => LayoutRowViscousSides.mode_parts_identity hα1 hα2 hc hD hR hL hx ha hseg n
  set A : ℤ → ℂ := fun n => ∫ p in K.rect, (p.1 : ℂ) *
    pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p) with hAdef
  set G : ℤ → ℂ := fun n => ∫ p in K.rect, (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3,
    gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b') with hGdef
  set Bd : ℤ → ℂ := fun n => ∑ s : Fin L.segCount, ∑ a' : Fin 3, ∑ d : Fin (L.degSide + 1),
    gradSideRowCoef c L a n s a' d *
      (if (L.segment s).radial then
        (L.segment s).moment true (L.gradModeOf n x a' 0) (L.secondModeOf n x a' 0 0) (L.secondModeOf n x a' 0 2) d
      else (L.segment s).moment true (L.gradModeOf n x a' 2) (L.secondModeOf n x a' 2 0)
        (L.secondModeOf n x a' 2 2) d) with hBd
  have hL1 : ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes,
        pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)).re =
      (∑ n ∈ R.rowModes, A n).re := by
    have e1 : (fun p : ℝ × ℝ => p.1 * (∑ n ∈ R.rowModes,
        pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)).re) =
        fun p => RCLike.re (∑ n ∈ R.rowModes, (p.1 : ℂ) *
          pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)) := by
      funext p
      rw [← Finset.mul_sum]
      exact (Complex.re_ofReal_mul _ _).symm
    rw [e1, integral_re (integrable_finsetSum _ fun n _ => (hM n).1), integral_finsetSum _ fun n _ => (hM n).1]
    rfl
  have hG1 : ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re =
      (∑ n ∈ R.rowModes, G n).re := by
    have e1 : (fun p : ℝ × ℝ => p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re) =
        fun p => RCLike.re (∑ n ∈ R.rowModes, (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3,
          gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) := by
      funext p
      rw [← Finset.mul_sum]
      exact (Complex.re_ofReal_mul _ _).symm
    rw [e1, integral_re (integrable_finsetSum _ fun n _ => (hM n).2.1),
      integral_finsetSum _ fun n _ => (hM n).2.1]
    rfl
  have hR1 : gradSideSum c L a x = ∑ n ∈ L.modes, Bd n := by
    unfold gradSideSum
    rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort L.modes]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fintype.sum_prod_type]
  have hz : ∀ n, (∀ p ∈ K.rect, rowModeVec c a n p = 0) → Bd n = 0 := by
    intro n h
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun a' _ => Finset.sum_eq_zero fun d _ => ?_
    have ht := LayoutRowViscousSides.trace_of_zero hD.box hL.layout (f := fun p => rowModeVec c a n p a')
      (fun p hp => by simp only [h p hp, Pi.zero_apply]) s d
    simp only [gradSideRowCoef, ht, map_zero, mul_zero, zero_mul]
  have hn0 : R.rowModeOf a ∈ L.modes := by
    rw [hL.layout.modes_eq]; exact hD.row_mode_resolved a ha
  have hn1 : -R.rowModeOf a ∈ L.modes := hL.modes_symm _ hn0
  have hA : ∑ n ∈ R.rowModes, Bd n = ∑ n ∈ R.rowModes ∩ L.modes, Bd n := by
    refine (Finset.sum_subset Finset.inter_subset_left fun n hn hnT => ?_).symm
    have hnL : n ∉ L.modes := fun h => hnT (Finset.mem_inter.2 ⟨hn, h⟩)
    exact hz n fun p hp => hD.row_mode_of a ha n (fun h => hnL (h ▸ hn0)) (fun h => hnL (h ▸ hn1)) p hp
  have hB : ∑ n ∈ L.modes, Bd n = ∑ n ∈ R.rowModes ∩ L.modes, Bd n := by
    refine (Finset.sum_subset Finset.inter_subset_right fun n hn hnT => ?_).symm
    have hnR : n ∉ R.rowModes := fun h => hnT (Finset.mem_inter.2 ⟨h, hn⟩)
    exact hz n fun p hp => hD.row_modes a ha n hnR p hp
  have hsum : -((c.splitVisc : ℂ) * ∑ n ∈ R.rowModes, A n) =
      (c.splitVisc : ℂ) * ∑ n ∈ R.rowModes, G n + ∑ n ∈ R.rowModes, Bd n := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun n _ => (hM n).2.2
  have hre := congrArg Complex.re hsum
  rw [Complex.neg_re, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hre
  rw [hL1, hG1, hR1, hB, ← hA]
  exact hre

theorem viscous_identity_holds {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1)) :
    (-(c.splitVisc * l2Pair (fun y => secondTrace (x.2.2.1 y)) (c.row a))) / (4 * Real.pi) =
      c.splitVisc * LayoutRowParts.gradientPairing c x a / (4 * Real.pi) + (gradSideSum c L a x).re := by
  have hSi := (pairings_integrable hα1 hα2 hc hD hR hL hx ha).2.1
  obtain ⟨hm, hn⟩ := secondTrace_on hc hD hx
  have hmir := trace_mirror (K := K) hx.1 (hc.base.row_class a)
  have hexp := LayoutRowPressure.row_expansion hc hD hR ha
  have hint := LayoutRowPressure.circle_integrable hD.box hm hn
  have h := LayoutRowModes.pairing_modes hD.box (hD.rows_in_cell a ha) hSi
    (by filter_upwards [hmir] with y hy hy' using hy hy') c.order R.rowModes (fun p n => rowModeVec c a n p) hexp hint
  have hv := viscous_mode_identity hα1 hα2 hc hD hR hL hx ha hseg
  rw [h, gradient_modes hα1 hα2 hc hD hR hL hx ha]
  exact scale_alg (by positivity) hv

end Breakdown.FracInternal.LayoutRowVolume

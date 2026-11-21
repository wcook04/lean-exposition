import Breakdown.CertCell.TailStatements
import Breakdown.FracCell.RelTrace
import Breakdown.Cert.CoerciveRotation

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

open CellCert.CellAnalysis (cylPoint)
open CellCert.CellFormula.Internal.RelTrace (region cylF lintegral_cyl measurable_cylF)

private theorem exists_measurable_ge {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ g =ᵐ[μ] f := by
  classical
  set S := toMeasurable μ {x | f x ≠ hf.mk f x}
  have hS0 : μ S = 0 := by
    rw [measure_toMeasurable]
    exact ae_iff.mp hf.ae_eq_mk
  refine ⟨S.piecewise (fun _ => ∞) (hf.mk f),
    Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const hf.measurable_mk, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ S
    · simp [Set.piecewise, hx]
    · have hx' : f x = hf.mk f x := by
        by_contra hc
        exact hx (subset_toMeasurable _ _ hc)
      simp only [Set.piecewise, hx, if_false]
      exact hx'.le
  · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS0, hf.ae_eq_mk] with x hx hx'
    simp only [Set.piecewise, hx, if_false]
    exact hx'.symm

private theorem lintegral_period_le (f : ℝ → ℝ≥0∞) (hf : ∀ θ, f (θ + 2 * Real.pi) = f θ) :
    ∫⁻ θ in Ioc 0 (2 * Real.pi), f θ ≤ 2 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ := by
  have hπ := Real.pi_pos
  have hsub : Ioc 0 (2 * Real.pi) ⊆ Ioc (-Real.pi) Real.pi ∪ Ioc Real.pi (3 * Real.pi) := by
    intro x hx
    rcases le_or_gt x Real.pi with h | h
    · exact Or.inl ⟨by linarith [hx.1], h⟩
    · exact Or.inr ⟨h, by linarith [hx.2]⟩
  have hshift : ∫⁻ θ in Ioc Real.pi (3 * Real.pi), f θ = ∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ := by
    have e := (measurePreserving_add_right volume (2 * Real.pi)).setLIntegral_comp_preimage_emb
      (measurableEmbedding_addRight (2 * Real.pi)) f (Ioc Real.pi (3 * Real.pi))
    rw [preimage_add_const_Ioc] at e
    have h1 : Real.pi - 2 * Real.pi = -Real.pi := by ring
    have h2 : 3 * Real.pi - 2 * Real.pi = Real.pi := by ring
    rw [h1, h2] at e
    rw [← e]
    exact setLIntegral_congr_fun (f := fun a => f (a + 2 * Real.pi)) measurableSet_Ioc (fun θ _ => hf θ)
  have hIoo : ∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ = ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ :=
    setLIntegral_congr Ioo_ae_eq_Ioc.symm
  calc ∫⁻ θ in Ioc 0 (2 * Real.pi), f θ
      ≤ ∫⁻ θ in Ioc (-Real.pi) Real.pi ∪ Ioc Real.pi (3 * Real.pi), f θ := lintegral_mono_set hsub
    _ ≤ (∫⁻ θ in Ioc (-Real.pi) Real.pi, f θ) + ∫⁻ θ in Ioc Real.pi (3 * Real.pi), f θ :=
        lintegral_union_le f _ _
    _ = 2 * ∫⁻ θ in Ioo (-Real.pi) Real.pi, f θ := by rw [hshift, hIoo, two_mul]

private theorem cylPoint_add_two_pi (r θ z : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem axialRot_planePoint (p : ℝ × ℝ) (φ : ℝ) :
    axialRot φ (planePoint p) = cylPoint p.1 φ p.2 := by
  ext i
  fin_cases i <;> simp [axialRot, planePoint, cylPoint, unitVector] <;> ring

private theorem measurable_cylPoint :
    Measurable (fun x : (ℝ × ℝ) × ℝ => cylPoint x.1.1 x.2 x.1.2) :=
  measurable_cylF

private theorem cyl_bound (h : Space → ℝ≥0∞) (hh : Measurable h) :
    ∫⁻ p in halfPlane, ENNReal.ofReal p.1 * ∫⁻ φ in Ioc 0 (2 * Real.pi), h (cylPoint p.1 φ p.2)
      ≤ 2 * ∫⁻ y, h y := by
  have hm : Measurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * h (cylF x)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul (hh.comp measurable_cylF)
  have hreg : (volume : Measure ((ℝ × ℝ) × ℝ)).restrict region =
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict]
    rfl
  calc ∫⁻ p in halfPlane, ENNReal.ofReal p.1 * ∫⁻ φ in Ioc 0 (2 * Real.pi), h (cylPoint p.1 φ p.2)
      ≤ ∫⁻ p in halfPlane, ENNReal.ofReal p.1 *
          (2 * ∫⁻ φ in Ioo (-Real.pi) Real.pi, h (cylPoint p.1 φ p.2)) := by
        refine lintegral_mono fun p => ?_
        gcongr
        exact lintegral_period_le _ fun θ => by rw [cylPoint_add_two_pi]
    _ ≤ ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ENNReal.ofReal p.1 *
          (2 * ∫⁻ φ in Ioo (-Real.pi) Real.pi, h (cylPoint p.1 φ p.2)) :=
        lintegral_mono_set fun p hp => ⟨hp.1, mem_univ _⟩
    _ = 2 * ∫⁻ p in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∫⁻ φ in Ioo (-Real.pi) Real.pi,
          ENNReal.ofReal p.1 * h (cylF (p, φ)) := by
        rw [← lintegral_const_mul' _ _ (by norm_num)]
        refine lintegral_congr fun p => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        simp only [cylF]
        ring
    _ = 2 * ∫⁻ x in region, ENNReal.ofReal x.1.1 * h (cylF x) := by
        rw [hreg, lintegral_prod _ hm.aemeasurable]
    _ = 2 * ∫⁻ y, h y := by rw [lintegral_cyl]

private theorem norm_entry_le (A : Space →L[ℝ] Space) (φ : ℝ) (i j : Fin 3) :
    ‖axialRot (-φ) (A (axialRot φ (unitVector j))) i‖ ≤ ‖A‖ := by
  calc ‖axialRot (-φ) (A (axialRot φ (unitVector j))) i‖
      ≤ ‖axialRot (-φ) (A (axialRot φ (unitVector j)))‖ := PiLp.norm_apply_le _ i
    _ = ‖A (axialRot φ (unitVector j))‖ := Coercive.RotationInternal.axialRot_norm _ _
    _ ≤ ‖A‖ * ‖axialRot φ (unitVector j)‖ := A.le_opNorm _
    _ = ‖A‖ := by
        simp [Coercive.RotationInternal.axialRot_norm, unitVector]

private theorem opNorm_le_sum (A : Space →L[ℝ] Space) : ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun x => ?_
  have hx : ∑ i : Fin 3, x i • unitVector i = x := by
    simpa [unitVector] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x
  calc ‖A x‖ = ‖∑ i : Fin 3, x i • A (unitVector i)‖ := by
        conv_lhs => rw [← hx]
        simp only [map_sum, map_smul]
    _ ≤ ∑ i : Fin 3, ‖x i • A (unitVector i)‖ := norm_sum_le _ _
    _ = ∑ i : Fin 3, ‖x i‖ * ‖A (unitVector i)‖ := by simp only [norm_smul]
    _ ≤ ∑ i : Fin 3, ‖x‖ * ‖A (unitVector i)‖ :=
        Finset.sum_le_sum fun i _ => by gcongr; exact PiLp.norm_apply_le x i
    _ = (∑ i : Fin 3, ‖A (unitVector i)‖) * ‖x‖ := by rw [Finset.sum_mul]; simp only [mul_comm]

private theorem norm_sq_le_three_matSq (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have h := opNorm_le_sum A
  have h0 := norm_nonneg A
  unfold matSq
  simp only [Fin.sum_univ_three] at h ⊢
  have h2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖)]

private theorem enorm_modeGrad_le (ξ : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (M : ℝ × Space → ℝ≥0∞) (hM : ∀ z : ℝ × Space, ‖G z.1 z.2‖ₑ ≤ M z) (y : Space)
    (ij : Fin 3 × Fin 3) :
    ‖modeGrad ξ G 0 y ij‖ₑ ≤ ‖(1 / (2 * Real.pi) : ℂ)‖ₑ *
      ∫⁻ τ in Ioc 0 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, axialRot φ y) := by
  unfold modeGrad modeAverage
  rw [enorm_mul]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun τ => ?_)
  rw [intervalIntegral.integral_of_le (by positivity)]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun φ => ?_)
  rw [enorm_mul]
  have h1 : ‖Complex.exp (-(((2 * Real.pi * ξ.1 * τ + ξ.2 * φ : ℝ) : ℂ) * Complex.I))‖ₑ = 1 := by
    rw [← ofReal_norm, ← neg_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I,
      ENNReal.ofReal_one]
  rw [h1, one_mul]
  simp only [zero_add]
  calc ‖((axialRot (-φ) (G τ (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1 : ℝ) : ℂ)‖ₑ
      = ENNReal.ofReal ‖axialRot (-φ) (G τ (axialRot φ y) (axialRot φ (unitVector ij.2))) ij.1‖ := by
        rw [← ofReal_norm, Complex.norm_real]
    _ ≤ ENNReal.ofReal ‖G τ (axialRot φ y)‖ := ENNReal.ofReal_le_ofReal (norm_entry_le _ _ _ _)
    _ = ‖G τ (axialRot φ y)‖ₑ := ofReal_norm _
    _ ≤ M (τ, axialRot φ y) := hM (τ, axialRot φ y)

private theorem sq_lintegral_le {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : AEMeasurable f μ) : (∫⁻ a, f a ∂μ) ^ 2 ≤ μ univ * ∫⁻ a, f a ^ 2 ∂μ := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two hf
    (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, one_mul] at h
  have key : ∀ X : ℝ≥0∞, (X ^ (1 / 2 : ℝ)) ^ 2 = X := fun X => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq : ∫⁻ a, f a ^ (2 : ℝ) ∂μ = ∫⁻ a, f a ^ 2 ∂μ := lintegral_congr fun a => ENNReal.rpow_two (f a)
  calc (∫⁻ a, f a ∂μ) ^ 2 ≤ ((∫⁻ a, f a ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ) * μ univ ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
    _ = μ univ * ∫⁻ a, f a ^ 2 ∂μ := by rw [mul_pow, key, key, hsq, mul_comm]

private theorem labelGrad_bound (mm : ℕ) (ι : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space))
    (M : ℝ × Space → ℝ≥0∞) (hMm : Measurable M) (hM : ∀ z : ℝ × Space, ‖G z.1 z.2‖ₑ ≤ M z)
    (p : ℝ × ℝ) :
    ENNReal.ofReal (cnormSq (labelGrad mm ι G p)) ≤
      9 * ‖(1 / (2 * Real.pi) : ℂ)‖ₑ ^ 2 * (volume (Ioc (0 : ℝ) 1) * volume (Ioc 0 (2 * Real.pi))) *
        ∫⁻ τ in Ioc 0 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2 := by
  set c : ℝ≥0∞ := ‖(1 / (2 * Real.pi) : ℂ)‖ₑ
  set μ : Measure (ℝ × ℝ) :=
    (volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))
  set K : ℝ × ℝ → ℝ≥0∞ := fun x => M (x.1, cylPoint p.1 x.2 p.2)
  have hc : Measurable (fun x : ℝ × ℝ => cylPoint p.1 x.2 p.2) :=
    (measurable_cylPoint.comp (measurable_prodMk_left (x := p))).comp measurable_snd
  have hK : Measurable K := hMm.comp (measurable_fst.prodMk hc)
  have hI : ∫⁻ τ in Ioc 0 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, axialRot φ (planePoint p)) =
      ∫⁻ x, K x ∂μ := by
    rw [lintegral_prod _ hK.aemeasurable]
    simp only [K, axialRot_planePoint]
  have hI2 : ∫⁻ x, K x ^ 2 ∂μ =
      ∫⁻ τ in Ioc 0 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2 := by
    rw [lintegral_prod _ (hK.pow_const 2).aemeasurable]
  have hμ : μ univ = volume (Ioc (0 : ℝ) 1) * volume (Ioc 0 (2 * Real.pi)) := by
    rw [← univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, Measure.restrict_apply_univ]
  have hentry : ∀ ij, ‖labelGrad mm ι G p ij‖ₑ ^ 2 ≤ c ^ 2 * (μ univ * ∫⁻ x, K x ^ 2 ∂μ) := by
    intro ij
    calc ‖labelGrad mm ι G p ij‖ₑ ^ 2 ≤ (c * ∫⁻ x, K x ∂μ) ^ 2 := by
          gcongr
          rw [← hI]
          exact enorm_modeGrad_le _ G M hM _ ij
      _ = c ^ 2 * (∫⁻ x, K x ∂μ) ^ 2 := mul_pow _ _ _
      _ ≤ c ^ 2 * (μ univ * ∫⁻ x, K x ^ 2 ∂μ) := by
          gcongr
          exact sq_lintegral_le μ hK.aemeasurable
  have hsum : ENNReal.ofReal (cnormSq (labelGrad mm ι G p)) =
      ∑ ij, ‖labelGrad mm ι G p ij‖ₑ ^ 2 := by
    unfold cnormSq
    rw [ENNReal.ofReal_sum_of_nonneg (fun ij _ => by positivity)]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rw [hsum]
  calc ∑ ij, ‖labelGrad mm ι G p ij‖ₑ ^ 2
      ≤ ∑ _ij : Fin 3 × Fin 3, c ^ 2 * (μ univ * ∫⁻ x, K x ^ 2 ∂μ) :=
        Finset.sum_le_sum fun ij _ => hentry ij
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, hμ, hI2,
          nsmul_eq_mul]
        push_cast
        ring

theorem labelGradFinite : LabelGradFinite := by
  intro Γ P v G H g hv _ mm ι
  obtain ⟨M, hMm, hle, hae⟩ := exists_measurable_ge
    (hv.measurable_gradient.enorm : AEMeasurable (fun z : ℝ × Space => ‖G z.1 z.2‖ₑ) volume)
  have hM : ∀ z : ℝ × Space, ‖G z.1 z.2‖ₑ ≤ M z := hle
  set C : ℝ≥0∞ := 9 * ‖(1 / (2 * Real.pi) : ℂ)‖ₑ ^ 2 *
    (volume (Ioc (0 : ℝ) 1) * volume (Ioc 0 (2 * Real.pi)))
  have hC : C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top enorm_ne_top))
      (ENNReal.mul_ne_top measure_Ioc_lt_top.ne measure_Ioc_lt_top.ne)
  have hmeas : Measurable (fun q : (ℝ × ℝ) × ℝ => ENNReal.ofReal q.1.1 *
      ∫⁻ φ in Ioc 0 (2 * Real.pi), M (q.2, cylPoint q.1.1 φ q.1.2) ^ 2) := by
    refine (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul ?_
    exact Measurable.lintegral_prod_right'
      (f := fun w : ((ℝ × ℝ) × ℝ) × ℝ => M (w.1.2, cylPoint w.1.1.1 w.2 w.1.1.2) ^ 2)
      ((hMm.comp (measurable_fst.snd.prodMk
        (measurable_cylPoint.comp (measurable_fst.fst.prodMk measurable_snd)))).pow_const 2)
  have hae2 : ∀ᵐ τ : ℝ, ∀ᵐ y : Space, M (τ, y) = ‖G τ y‖ₑ :=
    Measure.ae_ae_of_ae_prod (μ := volume) (ν := volume) hae
  have hfin : ∫⁻ τ in Icc (0 : ℝ) 1, 2 * ∫⁻ y, M (τ, y) ^ 2 < ⊤ := by
    calc ∫⁻ τ in Icc (0 : ℝ) 1, 2 * ∫⁻ y, M (τ, y) ^ 2
        = ∫⁻ τ in Icc (0 : ℝ) 1, 2 * ∫⁻ y, ‖G τ y‖ₑ ^ 2 := by
          refine lintegral_congr_ae ((ae_restrict_of_ae hae2).mono fun τ hτ => ?_)
          dsimp only
          rw [lintegral_congr_ae (hτ.mono fun y hy => by rw [hy])]
      _ ≤ ∫⁻ τ in Icc (0 : ℝ) 1, 2 * ∫⁻ y, ENNReal.ofReal 3 * ENNReal.ofReal (matSq (G τ y)) := by
          refine lintegral_mono fun τ => ?_
          gcongr with y
          rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by norm_num)]
          exact ENNReal.ofReal_le_ofReal (norm_sq_le_three_matSq _)
      _ = 2 * ENNReal.ofReal 3 * periodLIntegral (fun σ y => matSq (G σ y)) := by
          rw [periodLIntegral,
            ← lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top)]
          refine lintegral_congr fun τ => ?_
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
      _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)
          hv.gradient_finite
  calc ∫⁻ p in halfPlane, ENNReal.ofReal (cnormSq (labelGrad mm ι G p) * p.1)
      ≤ ∫⁻ p in halfPlane, C * (ENNReal.ofReal p.1 * ∫⁻ τ in Ioc 0 1,
          ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2) := by
        refine lintegral_mono fun p => ?_
        have hc0 : 0 ≤ cnormSq (labelGrad mm ι G p) := Finset.sum_nonneg fun _ _ => by positivity
        rw [ENNReal.ofReal_mul hc0]
        calc ENNReal.ofReal (cnormSq (labelGrad mm ι G p)) * ENNReal.ofReal p.1
            ≤ (C * ∫⁻ τ in Ioc 0 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2) *
                ENNReal.ofReal p.1 := by
              gcongr
              exact labelGrad_bound mm ι G M hMm hM p
          _ = _ := by ring
    _ = C * ∫⁻ τ in Ioc 0 1, ∫⁻ p in halfPlane, ENNReal.ofReal p.1 *
          ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2 := by
        rw [lintegral_const_mul' _ _ hC]
        congr 1
        refine (lintegral_congr fun p => (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm).trans ?_
        exact lintegral_lintegral_swap
          (f := fun (p : ℝ × ℝ) (τ : ℝ) => ENNReal.ofReal p.1 *
            ∫⁻ φ in Ioc 0 (2 * Real.pi), M (τ, cylPoint p.1 φ p.2) ^ 2) hmeas.aemeasurable
    _ ≤ C * ∫⁻ τ in Ioc 0 1, 2 * ∫⁻ y, M (τ, y) ^ 2 := by
        gcongr with τ
        exact cyl_bound _ ((hMm.comp (measurable_const.prodMk measurable_id)).pow_const 2)
    _ ≤ C * ∫⁻ τ in Icc 0 1, 2 * ∫⁻ y, M (τ, y) ^ 2 := by
        gcongr
        exact Ioc_subset_Icc_self
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hC) hfin

end TailBand

end CertCell

end Breakdown

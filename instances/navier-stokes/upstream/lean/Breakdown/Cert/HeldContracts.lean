import Breakdown.Cert.Nodes
import Breakdown.Cert.TestPairing

open scoped ENNReal Topology
open MeasureTheory Filter Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldContracts

def periodMeasure : Measure (ℝ × Space) :=
  ((volume : Measure ℝ).restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space)

theorem periodMeasure_eq :
    periodMeasure = (volume : Measure (ℝ × Space)).restrict (Icc (0 : ℝ) 1 ×ˢ univ) := by
  rw [periodMeasure, Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem aesm_period {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) periodMeasure := by
  rw [periodMeasure_eq]
  exact hF.restrict

theorem periodLIntegral_eq (F : ℝ → Space → Space)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) =
      eLpNorm (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure ^ 2 := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  have hm : AEMeasurable (fun z : ℝ × Space => ‖F z.1 z.2‖ₑ ^ (2 : ℕ)) periodMeasure :=
    ((aesm_period hF).enorm).pow_const 2
  unfold periodLIntegral
  rw [periodMeasure, lintegral_prod _ hm]
  refine lintegral_congr fun σ => lintegral_congr fun y => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

theorem periodNorm_eq (F : ℝ → Space → Space)
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    periodNorm F = (eLpNorm (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure).toReal := by
  unfold periodNorm
  rw [periodLIntegral_eq F hF, ENNReal.toReal_pow, Real.sqrt_sq ENNReal.toReal_nonneg]

theorem eLpNorm_lt_top {F : ℝ → Space → Space} (hF : IsPeriodicField F) :
    eLpNorm (fun z : ℝ × Space => F z.1 z.2) 2 periodMeasure < ⊤ := by
  have h := hF.2.2
  rw [periodLIntegral_eq F hF.1] at h
  by_contra hc
  rw [not_lt, top_le_iff] at hc
  rw [hc, ENNReal.top_pow two_ne_zero] at h
  exact lt_irrefl _ h

theorem eLpNorm_neg_add_le {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) :
    eLpNorm (fun z : ℝ × Space => -(F₁ z.1 z.2 + F₂ z.1 z.2)) 2 periodMeasure ≤
      eLpNorm (fun z : ℝ × Space => F₁ z.1 z.2) 2 periodMeasure
        + eLpNorm (fun z : ℝ × Space => F₂ z.1 z.2) 2 periodMeasure := by
  have e : (fun z : ℝ × Space => -(F₁ z.1 z.2 + F₂ z.1 z.2)) =
      -((fun z : ℝ × Space => F₁ z.1 z.2) + (fun z : ℝ × Space => F₂ z.1 z.2)) := rfl
  rw [e, eLpNorm_neg]
  exact eLpNorm_add_le (aesm_period h₁.1) (aesm_period h₂.1) (by norm_num)

theorem isPeriodicField_neg_add {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) : IsPeriodicField (fun σ y => -(F₁ σ y + F₂ σ y)) := by
  have hm : AEStronglyMeasurable (fun z : ℝ × Space => -(F₁ z.1 z.2 + F₂ z.1 z.2)) volume :=
    (h₁.1.add h₂.1).neg
  refine ⟨hm, fun σ y => by simp only [h₁.2.1 σ y, h₂.2.1 σ y], ?_⟩
  rw [periodLIntegral_eq _ hm]
  have hlt := lt_of_le_of_lt (eLpNorm_neg_add_le h₁ h₂)
    (ENNReal.add_lt_top.2 ⟨eLpNorm_lt_top h₁, eLpNorm_lt_top h₂⟩)
  exact ENNReal.pow_lt_top hlt

theorem periodNorm_neg_add_le {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) :
    periodNorm (fun σ y => -(F₁ σ y + F₂ σ y)) ≤ periodNorm F₁ + periodNorm F₂ := by
  rw [periodNorm_eq _ (h₁.1.add h₂.1).neg, periodNorm_eq _ h₁.1, periodNorm_eq _ h₂.1,
    ← ENNReal.toReal_add (eLpNorm_lt_top h₁).ne (eLpNorm_lt_top h₂).ne]
  exact ENNReal.toReal_mono
    (ENNReal.add_lt_top.2 ⟨eLpNorm_lt_top h₁, eLpNorm_lt_top h₂⟩).ne (eLpNorm_neg_add_le h₁ h₂)

theorem periodBallNorm_le {F : ℝ → Space → Space} (hF : IsPeriodicField F) (R : ℝ) :
    periodBallNorm R F ≤ periodNorm F := by
  unfold periodBallNorm periodNorm
  refine Real.sqrt_le_sqrt (ENNReal.toReal_mono hF.2.2.ne ?_)
  exact lintegral_mono fun σ => setLIntegral_le_lintegral _ _

theorem periodNorm_nonneg (F : ℝ → Space → Space) : 0 ≤ periodNorm F := Real.sqrt_nonneg _

theorem integral_neg_add_pairing {F₁ F₂ : ℝ → Space → Space} (h₁ : IsPeriodicField F₁)
    (h₂ : IsPeriodicField F₂) {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (-(F₁ z.1 z.2 + F₂ z.1 z.2)) (φ z.1 z.2) =
      -((∫ z : ℝ × Space, inner ℝ (F₁ z.1 z.2) (φ z.1 z.2))
        + ∫ z : ℝ × Space, inner ℝ (F₂ z.1 z.2) (φ z.1 z.2)) := by
  obtain ⟨hs, hc, -⟩ := hφ
  obtain ⟨R, -, hR⟩ := Internal.TestPairing.exists_bound hc
  simp only [inner_neg_left, inner_add_left]
  rw [integral_neg, integral_add (Internal.TestPairing.integrable_pairing h₁ hs hc hR)
    (Internal.TestPairing.integrable_pairing h₂ hs hc hR)]

theorem supGrad_eq_eLpNorm (v : XX) : supGrad v = eLpNorm (gradCLM v) ⊤ volume :=
  (eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL gradPart v)).symm

theorem supGrad_sub_lt_top {u u' : XX} (hu : supGrad u < ⊤) (hu' : supGrad u' < ⊤) :
    supGrad (u - u') < ⊤ := by
  rw [supGrad_eq_eLpNorm] at hu hu' ⊢
  rw [map_sub, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  exact lt_of_le_of_lt (eLpNorm_sub_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) le_top)
    (ENNReal.add_lt_top.2 ⟨hu, hu'⟩)

theorem energyW_nonneg {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) : 0 ≤ energyW w u :=
  add_nonneg (sq_nonneg _) (integral_nonneg fun _ => integral_nonneg fun y =>
    mul_nonneg (hw y) (Finset.sum_nonneg fun _ _ => sq_nonneg _))

theorem sum_sq_nonneg {k : ℕ} (κ : Fin k → ℝ) : 0 ≤ ∑ i, κ i ^ 2 :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem sqrt_energyW_le_sizeZ {k : ℕ} (w : Space → ℝ) (u : XX) (κ : Fin k → ℝ) :
    Real.sqrt (energyW w u) ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_right (sum_sq_nonneg κ))

theorem vecNorm_le_sizeZ {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    vecNorm κ ≤ sizeZ w u κ :=
  Real.sqrt_le_sqrt (le_add_of_nonneg_left (energyW_nonneg hw u))

theorem energyW_le_sq {k : ℕ} {w : Space → ℝ} (hw : ∀ y, 0 ≤ w y) (u : XX) (κ : Fin k → ℝ) :
    energyW w u ≤ sizeZ w u κ ^ 2 := by
  unfold sizeZ
  rw [Real.sq_sqrt (add_nonneg (energyW_nonneg hw u) (sum_sq_nonneg κ))]
  exact le_add_of_nonneg_right (sum_sq_nonneg κ)

theorem sq_bound {s E sE V φ' φ Z m c a K : ℝ} (hm : 0 ≤ m) (hc : 0 ≤ c) (ha : 0 ≤ a)
    (hK : 0 < K) (hZ0 : 0 ≤ Z) (hsE0 : 0 ≤ sE) (_hV0 : 0 ≤ V) (hφ'0 : 0 ≤ φ')
    (hE : E ≤ Z ^ 2) (hsE : sE ≤ Z) (hV : V ≤ Z) (hφ' : φ' ≤ φ) (hZ : Z ≤ K * φ)
    (hs : s ^ 2 ≤ m * E + 2 * c * (φ' + a * V) * sE) :
    s ^ 2 ≤ K ^ 2 * φ ^ 2 * (m + 2 * c * a + 2 * c / K) := by
  have hφ0 : 0 ≤ φ := hφ'0.trans hφ'
  have h1 : m * E ≤ m * Z ^ 2 := mul_le_mul_of_nonneg_left hE hm
  have h2 : (φ' + a * V) * sE ≤ (φ + a * Z) * Z :=
    mul_le_mul (add_le_add hφ' (mul_le_mul_of_nonneg_left hV ha)) hsE hsE0
      (add_nonneg hφ0 (mul_nonneg ha hZ0))
  have hZ2 : Z ^ 2 ≤ (K * φ) ^ 2 := pow_le_pow_left₀ hZ0 hZ 2
  have hφZ : φ * Z ≤ φ * (K * φ) := mul_le_mul_of_nonneg_left hZ hφ0
  have e : K ^ 2 * φ ^ 2 * (m + 2 * c * a + 2 * c / K) =
      m * (K * φ) ^ 2 + 2 * c * (φ * (K * φ) + a * (K * φ) ^ 2) := by
    field_simp
    ring
  rw [e]
  calc s ^ 2 ≤ m * Z ^ 2 + 2 * c * ((φ + a * Z) * Z) := by
        nlinarith [mul_le_mul_of_nonneg_left h2 (mul_nonneg zero_le_two hc)]
    _ = m * Z ^ 2 + 2 * c * (φ * Z + a * Z ^ 2) := by ring
    _ ≤ m * (K * φ) ^ 2 + 2 * c * (φ * (K * φ) + a * (K * φ) ^ 2) := by
        gcongr

theorem mul_eq_mul_div_mul {r a s : ℝ} (hr : 0 < r) : a * s = r * (a / r * s) := by
  field_simp

theorem scaled_le {s ρ r K φ Q Qm : ℝ} (hr : 0 < r) (hρ : 0 ≤ ρ) (hs0 : 0 ≤ s)
    (hKφ : 0 ≤ K * φ) (hs : s ^ 2 ≤ K ^ 2 * φ ^ 2 * Q) (hQ : Q ≤ Qm)
    (hsmall : 4 * ρ ^ 2 * Qm ≤ r ^ 2) : 2 * ρ / r * s ≤ K * φ := by
  have hA : 0 ≤ K ^ 2 * φ ^ 2 := by positivity
  have h1 : (2 * ρ * s) ^ 2 ≤ (K * φ * r) ^ 2 := by
    calc (2 * ρ * s) ^ 2 = 4 * ρ ^ 2 * s ^ 2 := by ring
      _ ≤ 4 * ρ ^ 2 * (K ^ 2 * φ ^ 2 * Qm) := by
          refine mul_le_mul_of_nonneg_left (hs.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left hQ hA
      _ = K ^ 2 * φ ^ 2 * (4 * ρ ^ 2 * Qm) := by ring
      _ ≤ K ^ 2 * φ ^ 2 * r ^ 2 := mul_le_mul_of_nonneg_left hsmall hA
      _ = (K * φ * r) ^ 2 := by ring
  have h2 : 2 * ρ * s ≤ K * φ * r :=
    (pow_le_pow_iff_left₀ (by positivity) (mul_nonneg hKφ hr.le) two_ne_zero).1 h1
  rw [div_mul_eq_mul_div, div_le_iff₀ hr]
  exact h2

theorem bordered_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (g : HH × (Fin k → ℝ)) :
    (bordered d p g).1 = g.1 + convection d p (freeInv (d.period p) g.1) + actuatorH d g.2 := rfl

theorem bordered_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (g : HH × (Fin k → ℝ)) :
    (bordered d p g).2 = pinMap d (freeInv (d.period p) g.1) := rfl

theorem heldRight_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) :
    (heldRight d p u).1 = -(defectH d p) - productH u u := rfl

theorem heldRight_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) :
    (heldRight d p u).2 = targetGap d p := rfl

theorem heldRight_sub_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u u' : XX) :
    (heldRight d p u).1 - (heldRight d p u').1 = -(productH u u - productH u' u') := by
  show (-(defectH d p) - productH u u) - (-(defectH d p) - productH u' u') = _
  abel

theorem bordered_sub {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (g g' : HH × (Fin k → ℝ)) :
    bordered d p (g.1 - g'.1, g.2 - g'.2) = bordered d p g - bordered d p g' :=
  map_sub (bordered d p) g g'

theorem sub_fst_eq {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) {u u' : XX}
    (hsub : productH u u - productH u' u' = productH (u - u') u + productH u' (u - u'))
    {g g' : HH × (Fin k → ℝ)} (hg : bordered d p g = heldRight d p u)
    (hg' : bordered d p g' = heldRight d p u') :
    (bordered d p (g.1 - g'.1, g.2 - g'.2)).1 = -(productH (u - u') u + productH u' (u - u')) :=
  calc (bordered d p (g.1 - g'.1, g.2 - g'.2)).1 = (bordered d p g - bordered d p g').1 :=
        congrArg Prod.fst (bordered_sub d p g g')
    _ = (bordered d p g).1 - (bordered d p g').1 := Prod.fst_sub _ _
    _ = (heldRight d p u).1 - (heldRight d p u').1 := congrArg₂ (fun a b => a.1 - b.1) hg hg'
    _ = -(productH u u - productH u' u') := heldRight_sub_fst d p u u'
    _ = -(productH (u - u') u + productH u' (u - u')) := congrArg Neg.neg hsub

theorem sub_pin_eq {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) {u u' : XX}
    {g g' : HH × (Fin k → ℝ)} (hg : bordered d p g = heldRight d p u)
    (hg' : bordered d p g' = heldRight d p u') :
    pinMap d (freeInv (d.period p) (g.1 - g'.1)) = 0 :=
  calc pinMap d (freeInv (d.period p) (g.1 - g'.1)) = (bordered d p (g.1 - g'.1, g.2 - g'.2)).2 :=
        (bordered_snd d p (g.1 - g'.1, g.2 - g'.2)).symm
    _ = (bordered d p g - bordered d p g').2 := congrArg Prod.snd (bordered_sub d p g g')
    _ = (bordered d p g).2 - (bordered d p g').2 := Prod.snd_sub _ _
    _ = (heldRight d p u).2 - (heldRight d p u').2 := congrArg₂ (fun a b => a.2 - b.2) hg hg'
    _ = targetGap d p - targetGap d p := rfl
    _ = 0 := sub_self _

theorem heldDist_step {k : ℕ} (d : CertificateData k) (P : ℝ) (a b : HH) (α β : Fin k → ℝ) :
    heldDist d (freeInv P a, α) (freeInv P b, β) =
      max (sizeZ d.weightFn (freeInv P (a - b)) (α - β))
        (2 * d.sizeBound / d.supBound * (supGrad (freeInv P (a - b))).toReal) :=
  congrArg (fun v => max (sizeZ d.weightFn v (α - β))
      (2 * d.sizeBound / d.supBound * (supGrad v).toReal)) (map_sub (freeInv P) a b).symm

theorem sizeZ_le_heldDist {k : ℕ} (d : CertificateData k) (x y : XX × (Fin k → ℝ)) :
    sizeZ d.weightFn (x.1 - y.1) (x.2 - y.2) ≤ heldDist d x y := le_max_left _ _

theorem sup_le_heldDist {k : ℕ} (d : CertificateData k) (x y : XX × (Fin k → ℝ)) :
    2 * d.sizeBound / d.supBound * (supGrad (x.1 - y.1)).toReal ≤ heldDist d x y :=
  le_max_right _ _

theorem vecNorm_zero (k : ℕ) : vecNorm (0 : Fin k → ℝ) = 0 := by
  simp [vecNorm]

attribute [local irreducible] freeInv convection actuatorH pinMap productH defectH targetGap energyW
  sizeZ supGrad productField readingOf periodNorm periodBallNorm supBoundFactor testInHH physToHH
  gradCLM secondCLM invariantHH heldDist

theorem forcing_periodic (h4 : ProductBoundHolds) {w : Space → ℝ} {w₀ : ℝ}
    (hw : IsAdmissibleWeight w w₀) {u u' : XX} (hu : supGrad u < ⊤) (ha : supGrad (u - u') < ⊤) :
    IsPeriodicField (fun σ y => -(productField (u - u') u σ y + productField u' (u - u') σ y)) :=
  isPeriodicField_neg_add (h4 w w₀ hw (u - u') u hu).1 (h4 w w₀ hw u' (u - u') ha).1

theorem forcing_norm (h4 : ProductBoundHolds) {w : Space → ℝ} {w₀ : ℝ}
    (hw : IsAdmissibleWeight w w₀) {u u' : XX} (hu : supGrad u < ⊤) (ha : supGrad (u - u') < ⊤)
    {b : ℝ} (hb1 : supBoundFactor w₀ * Real.sqrt (energyW w (u - u')) * (supGrad u).toReal ≤ b)
    (hb2 : supBoundFactor w₀ * Real.sqrt (energyW w u') * (supGrad (u - u')).toReal ≤ b) :
    periodNorm (fun σ y => -(productField (u - u') u σ y + productField u' (u - u') σ y)) ≤ 2 * b :=
  (periodNorm_neg_add_le (h4 w w₀ hw (u - u') u hu).1 (h4 w w₀ hw u' (u - u') ha).1).trans
    ((add_le_add ((h4 w w₀ hw (u - u') u hu).2.1.trans hb1)
      ((h4 w w₀ hw u' (u - u') ha).2.1.trans hb2)).trans_eq (two_mul b).symm)

theorem forcing_normH (h4 : ProductBoundHolds) {w : Space → ℝ} {w₀ : ℝ}
    (hw : IsAdmissibleWeight w w₀) {u u' : XX} (hu : supGrad u < ⊤) (ha : supGrad (u - u') < ⊤)
    {f : HH} (hf : f = -(productH (u - u') u + productH u' (u - u')))
    {b : ℝ} (hb1 : supBoundFactor w₀ * Real.sqrt (energyW w (u - u')) * (supGrad u).toReal ≤ b)
    (hb2 : supBoundFactor w₀ * Real.sqrt (energyW w u') * (supGrad (u - u')).toReal ≤ b) :
    ‖f‖ ≤ 2 * b :=
  calc ‖f‖ = ‖-(productH (u - u') u + productH u' (u - u'))‖ := congrArg norm hf
    _ = ‖productH (u - u') u + productH u' (u - u')‖ := norm_neg _
    _ ≤ ‖productH (u - u') u‖ + ‖productH u' (u - u')‖ := norm_add_le _ _
    _ ≤ b + b := add_le_add ((h4 w w₀ hw (u - u') u hu).2.2.trans hb1)
        ((h4 w w₀ hw u' (u - u') ha).2.2.trans hb2)
    _ = 2 * b := (two_mul b).symm

theorem forcing_pairing (h4 : ProductBoundHolds) (h5 : ProductPairingHolds) {w : Space → ℝ}
    {w₀ : ℝ} (hw : IsAdmissibleWeight w w₀) {u u' : XX} (hu : supGrad u < ⊤)
    (ha : supGrad (u - u') < ⊤) {f : HH} (hf : f = -(productH (u - u') u + productH u' (u - u')))
    (φ : ℝ → Space → Space) (hφ : IsSpaceTimeTestField φ) :
    ∫ z : ℝ × Space, inner ℝ (-(productField (u - u') u z.1 z.2 + productField u' (u - u') z.1 z.2))
      (φ z.1 z.2) = inner ℝ f (testInHH φ) :=
  calc ∫ z : ℝ × Space, inner ℝ (-(productField (u - u') u z.1 z.2 + productField u' (u - u') z.1 z.2))
        (φ z.1 z.2)
      = -((∫ z : ℝ × Space, inner ℝ (productField (u - u') u z.1 z.2) (φ z.1 z.2))
          + ∫ z : ℝ × Space, inner ℝ (productField u' (u - u') z.1 z.2) (φ z.1 z.2)) :=
        integral_neg_add_pairing (h4 w w₀ hw (u - u') u hu).1 (h4 w w₀ hw u' (u - u') ha).1 hφ
    _ = -(inner ℝ (productH (u - u') u) (testInHH φ) + inner ℝ (productH u' (u - u')) (testInHH φ)) :=
        congrArg₂ (fun a b => -(a + b)) (h5 (u - u') u hu φ hφ).symm (h5 u' (u - u') ha φ hφ).symm
    _ = -inner ℝ (productH (u - u') u + productH u' (u - u')) (testInHH φ) :=
        congrArg Neg.neg (inner_add_left _ _ _).symm
    _ = inner ℝ (-(productH (u - u') u + productH u' (u - u'))) (testInHH φ) :=
        (inner_neg_left _ _).symm
    _ = inner ℝ f (testInHH φ) := congrArg (fun g => inner ℝ g (testInHH φ)) hf.symm

theorem coercive_part {k : ℕ} {d : CertificateData k} (hd : IsCertificate d)
    {F : ℝ → Space → Space} (hF : IsPeriodicField F) {Z φb : ℝ} (hFn : periodNorm F ≤ φb)
    {q : Fin k → ℝ} (hq : q = 0)
    (hZ0 : Z ≤ d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F
      + d.coercivePin * vecNorm q) :
    Z ≤ d.coerciveTotal * φb := by
  have h0 : d.coercivePin * vecNorm q = 0 :=
    (congrArg (fun t => d.coercivePin * vecNorm t) hq).trans
      ((congrArg (fun t => d.coercivePin * t) (vecNorm_zero k)).trans (mul_zero _))
  have hZ1 : Z ≤ d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F :=
    hZ0.trans_eq ((congrArg (fun t => d.coerciveL2 * periodNorm F
      + d.coerciveBall * periodBallNorm d.ballRadius F + t) h0).trans (add_zero _))
  have hb := periodBallNorm_le hF d.ballRadius
  have hn := periodNorm_nonneg F
  refine hZ1.trans ?_
  calc d.coerciveL2 * periodNorm F + d.coerciveBall * periodBallNorm d.ballRadius F
      ≤ d.coerciveL2 * periodNorm F + d.coerciveBall * periodNorm F :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hb hd.coerciveBall_nonneg)
    _ = (d.coerciveL2 + d.coerciveBall) * periodNorm F := (add_mul _ _ _).symm
    _ ≤ d.coerciveTotal * periodNorm F := mul_le_mul_of_nonneg_right hd.coerciveTotal_ge hn
    _ ≤ d.coerciveTotal * φb := mul_le_mul_of_nonneg_left hFn hd.coerciveTotal_pos.le

theorem ratio_bound {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) :
    (1 / d.weight + 2 * (d.period p / d.twist) * d.formBound)
        + 2 * (d.period p / d.twist) * d.actuatorBound + 2 * (d.period p / d.twist) / d.coerciveTotal
      ≤ (1 / d.weight + 2 * (d.periodMax / d.twist) * d.formBound)
        + 2 * (d.periodMax / d.twist) * d.actuatorBound + 2 * (d.periodMax / d.twist) / d.coerciveTotal := by
  have hN : (0 : ℝ) < d.twist := Nat.cast_pos.2 hd.twist_pos
  have hcm : 2 * (d.period p / d.twist) ≤ 2 * (d.periodMax / d.twist) :=
    mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right (hd.period_le p hp) hN.le) zero_le_two
  exact add_le_add (add_le_add (add_le_add le_rfl
    (mul_le_mul_of_nonneg_right hcm hd.formBound_nonneg))
    (mul_le_mul_of_nonneg_right hcm hd.actuatorBound_nonneg))
    (div_le_div_of_nonneg_right hcm hd.coerciveTotal_pos.le)

theorem sup_part {k : ℕ} {d : CertificateData k} (hd : IsCertificate d) {p : Fin k → ℝ}
    (hp : p ∈ d.box) {v : XX} {κ : Fin k → ℝ} {f : HH} {φb : ℝ}
    (hS : (supGrad v).toReal ^ 2 ≤
      (1 / d.weight + 2 * (d.period p / d.twist) * d.formBound) * energyW d.weightFn v
        + 2 * (d.period p / d.twist) * (‖f‖ + d.actuatorBound * vecNorm κ)
          * Real.sqrt (energyW d.weightFn v))
    (hf : ‖f‖ ≤ φb) (hZ : sizeZ d.weightFn v κ ≤ d.coerciveTotal * φb) (hφ0 : 0 ≤ φb) :
    2 * d.sizeBound / d.supBound * (supGrad v).toReal ≤ d.coerciveTotal * φb := by
  have hw0 : ∀ z, 0 ≤ d.weightFn z := fun z => hd.weight_pos.le.trans (hd.weightFn_lower z)
  have hK : 0 < d.coerciveTotal := hd.coerciveTotal_pos
  have hN : (0 : ℝ) < d.twist := Nat.cast_pos.2 hd.twist_pos
  have hc : 0 ≤ d.period p / d.twist := (div_pos (hd.period_pos p hp) hN).le
  have hm : 0 ≤ 1 / d.weight + 2 * (d.period p / d.twist) * d.formBound :=
    add_nonneg (one_div_nonneg.2 hd.weight_pos.le)
      (mul_nonneg (mul_nonneg zero_le_two hc) hd.formBound_nonneg)
  have hZ0 : 0 ≤ sizeZ d.weightFn v κ :=
    (Real.sqrt_nonneg _).trans (sqrt_energyW_le_sizeZ d.weightFn v κ)
  have hVpos : 0 ≤ vecNorm κ := Real.sqrt_nonneg _
  have hs2 := sq_bound hm hc hd.actuatorBound_nonneg hK hZ0
    (Real.sqrt_nonneg (energyW d.weightFn v)) hVpos (norm_nonneg f) (energyW_le_sq hw0 v κ)
    (sqrt_energyW_le_sizeZ d.weightFn v κ) (vecNorm_le_sizeZ hw0 v κ) hf hZ hS
  exact scaled_le hd.supBound_pos hd.sizeBound_nonneg ENNReal.toReal_nonneg
    (mul_nonneg hK.le hφ0) hs2 (ratio_bound hd hp) hd.small_second

theorem product_terms {w : Space → ℝ} {w₀ r ρ e : ℝ} (hAg : 0 ≤ supBoundFactor w₀) (hr : 0 < r)
    {u u' : XX} (hEa : Real.sqrt (energyW w (u - u')) ≤ e)
    (hsa : 2 * ρ / r * (supGrad (u - u')).toReal ≤ e)
    (hE' : Real.sqrt (energyW w u') ≤ 2 * ρ) (hsu : (supGrad u).toReal ≤ r) :
    supBoundFactor w₀ * Real.sqrt (energyW w (u - u')) * (supGrad u).toReal ≤ supBoundFactor w₀ * r * e ∧
    supBoundFactor w₀ * Real.sqrt (energyW w u') * (supGrad (u - u')).toReal ≤ supBoundFactor w₀ * r * e := by
  have he0 : 0 ≤ e := (Real.sqrt_nonneg _).trans hEa
  have hkey : Real.sqrt (energyW w u') * (supGrad (u - u')).toReal ≤ r * e :=
    calc Real.sqrt (energyW w u') * (supGrad (u - u')).toReal
        ≤ 2 * ρ * (supGrad (u - u')).toReal :=
          mul_le_mul_of_nonneg_right hE' ENNReal.toReal_nonneg
      _ = r * (2 * ρ / r * (supGrad (u - u')).toReal) := mul_eq_mul_div_mul hr
      _ ≤ r * e := mul_le_mul_of_nonneg_left hsa hr.le
  refine ⟨?_, ?_⟩
  · calc supBoundFactor w₀ * Real.sqrt (energyW w (u - u')) * (supGrad u).toReal
        ≤ supBoundFactor w₀ * e * r :=
          mul_le_mul (mul_le_mul_of_nonneg_left hEa hAg) hsu ENNReal.toReal_nonneg
            (mul_nonneg hAg he0)
      _ = supBoundFactor w₀ * r * e := mul_right_comm _ _ _
  · exact (mul_assoc _ _ _).trans_le
      ((mul_le_mul_of_nonneg_left hkey hAg).trans_eq (mul_assoc _ _ _).symm)

theorem contract_core (h2 : CoerciveBorderedHolds) (h3 : SupBoundHolds)
    (h4 : ProductBoundHolds) (h5 : ProductPairingHolds) (h6 : ProductSubHolds)
    {k : ℕ} (d : CertificateData k) (hd : IsCertificate d) (p : Fin k → ℝ) (hp : p ∈ d.box)
    (x y : XX × (Fin k → ℝ)) (hxG : supGrad x.1 ≤ ENNReal.ofReal d.supBound)
    (hyS : sizeZ d.weightFn y.1 y.2 ≤ 2 * d.sizeBound)
    (hyG : supGrad y.1 ≤ ENNReal.ofReal d.supBound) (gx gy : HH × (Fin k → ℝ))
    (hgx1 : gx.1 ∈ invariantHH d.symmetries) (hgy1 : gy.1 ∈ invariantHH d.symmetries)
    (hgx2 : bordered d p gx = heldRight d p x.1) (hgy2 : bordered d p gy = heldRight d p y.1) :
    heldDist d (freeInv (d.period p) gx.1, gx.2) (freeInv (d.period p) gy.1, gy.2) ≤
      2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound * heldDist d x y := by
  have hw : IsAdmissibleWeight d.weightFn d.weight :=
    ⟨hd.weight_pos, hd.weightFn_measurable, hd.weightFn_lower, d.weightMax, hd.weightFn_upper⟩
  have hAg : 0 ≤ supBoundFactor d.weight := by unfold supBoundFactor; positivity
  have hu : supGrad x.1 < ⊤ := lt_of_le_of_lt hxG ENNReal.ofReal_lt_top
  have hu' : supGrad y.1 < ⊤ := lt_of_le_of_lt hyG ENNReal.ofReal_lt_top
  have ha : supGrad (x.1 - y.1) < ⊤ := supGrad_sub_lt_top hu hu'
  have hg1 : gx.1 - gy.1 ∈ invariantHH d.symmetries := Submodule.sub_mem _ hgx1 hgy1
  have hbg1 : (bordered d p (gx.1 - gy.1, gx.2 - gy.2)).1 =
      -(productH (x.1 - y.1) x.1 + productH y.1 (x.1 - y.1)) :=
    sub_fst_eq d p (h6 x.1 y.1 hu hu').1 hgx2 hgy2
  have hpin : pinMap d (freeInv (d.period p) (gx.1 - gy.1)) = 0 := sub_pin_eq d p hgx2 hgy2
  have hEa : Real.sqrt (energyW d.weightFn (x.1 - y.1)) ≤ heldDist d x y :=
    (sqrt_energyW_le_sizeZ _ _ _).trans (sizeZ_le_heldDist d x y)
  have he0 : 0 ≤ heldDist d x y := (Real.sqrt_nonneg _).trans hEa
  have hE' : Real.sqrt (energyW d.weightFn y.1) ≤ 2 * d.sizeBound :=
    (sqrt_energyW_le_sizeZ _ _ y.2).trans hyS
  have hsu : (supGrad x.1).toReal ≤ d.supBound :=
    ENNReal.toReal_le_of_le_ofReal hd.supBound_pos.le hxG
  have hb := product_terms hAg hd.supBound_pos hEa (sup_le_heldDist d x y) hE' hsu
  have hFper := forcing_periodic h4 hw hu ha
  have hFnorm := forcing_norm h4 hw hu ha hb.1 hb.2
  have hHnorm := forcing_normH h4 hw hu ha hbg1 hb.1 hb.2
  have hZ0 := h2 d hd p hp (gx.1 - gy.1) hg1 (gx.2 - gy.2) _ hFper
    (forcing_pairing h4 h5 hw hu ha hbg1)
  have hφ0 : 0 ≤ 2 * (supBoundFactor d.weight * d.supBound * heldDist d x y) :=
    mul_nonneg zero_le_two (mul_nonneg (mul_nonneg hAg hd.supBound_pos.le) he0)
  have hZ := coercive_part hd hFper hFnorm hpin hZ0
  have hsup := sup_part hd hp (h3 d hd p hp (gx.1 - gy.1) hg1 (gx.2 - gy.2)).2 hHnorm hZ hφ0
  have hfin : d.coerciveTotal * (2 * (supBoundFactor d.weight * d.supBound * heldDist d x y)) =
      2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound * heldDist d x y := by ring
  exact (heldDist_step d (d.period p) gx.1 gy.1 gx.2 gy.2).trans_le
    ((max_le hZ hsup).trans_eq hfin)


end Internal.HeldContracts

theorem heldContractsHolds_of (h1 : BorderedInvertibleHolds) (h2 : CoerciveBorderedHolds)
    (h3 : SupBoundHolds) (h4 : ProductBoundHolds) (h5 : ProductPairingHolds)
    (h6 : ProductSubHolds) (_h7 : DataHolds) (h8 : InvarianceHolds)
    (_h9 : FreeEquivariantHolds) : HeldContractsHolds := by
  intro k d hd p hp
  refine ⟨2 * d.coerciveTotal * supBoundFactor d.weight * d.supBound, hd.small_first, ?_⟩
  intro x hx y hy
  obtain ⟨hxI, -, hxG⟩ := hx
  obtain ⟨hyI, hyS, hyG⟩ := hy
  have hE : ∃ T, BorderedInvSpec d p T := (h1 d hd p hp).1
  have hspec : BorderedInvSpec d p (borderedInv d p) := by
    simp only [borderedInv, dif_pos hE]
    exact hE.choose_spec
  obtain ⟨-, -, hdef⟩ := h8 d hd p hp
  have hconv := (h8 d hd p hp).1
  have hrx : (heldRight d p x.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hdef) (hconv x.1 hxI).2
  have hry : (heldRight d p y.1).1 ∈ invariantHH d.symmetries :=
    Submodule.sub_mem _ (Submodule.neg_mem _ hdef) (hconv y.1 hyI).2
  obtain ⟨hgx1, hgx2⟩ := hspec _ hrx
  obtain ⟨hgy1, hgy2⟩ := hspec _ hry
  exact Internal.HeldContracts.contract_core h2 h3 h4 h5 h6 d hd p hp x y hxG hyS hyG _ _
    hgx1 hgy1 hgx2 hgy2

end Breakdown.Cert

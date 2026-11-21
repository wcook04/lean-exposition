import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyPotentialTailsCross

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert.CellAnalysis

def ProjResidualOrthogonal : Prop :=
  ∀ (Kb : CellBox), IsCellBox Kb → ∀ (B : CellBases), IsCellBases Kb B → ∀ (Q : ℕ) (F : ℝ × ℝ → ℂ),
    AEStronglyMeasurable F (volume.restrict Kb.rect) →
    IntegrableOn (fun p => Kb.lineWeight p.1 * ‖F p‖ ^ 2) Kb.rect →
    ∀ P ∈ polyFn Q Q, Kb.pairOn Kb.lineWeightFn (fun p => F p - Kb.proj Q Q F p) P = 0

end Breakdown.CertCell.Assembly

namespace Breakdown.CertCell.Assembly.Internal.RestrictedPairing

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Breakdown.CertCell.Assembly.Internal.PotentialTails

attribute [local instance] rect_finite

theorem lineWeight_le_scaled (Kb : CellBox) (hK : IsCellBox Kb) {p : ℝ × ℝ} (hp : p ∈ Kb.rect) :
    Kb.lineWeight p.1 ≤ (if Kb.r₁ = 0 then 1 else Kb.r₁⁻¹) * p.1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · rw [one_mul]
  · have h0 : 0 < Kb.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
    rw [inv_mul_eq_div, le_div_iff₀ h0, one_mul]
    exact hp.1.1

theorem pairVec_at_grad (s : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) (a b : Fin 3) :
    pairVec s u ⟨3 * a.val + b.val, by omega⟩ = s a b := by
  unfold pairVec
  rw [dif_pos (by show 3 * a.val + b.val < 9; omega)]
  congr 1
  · ext; simp only; omega
  · ext; simp only; omega

theorem pairVec_at_vel (s : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) (a : Fin 3) :
    pairVec s u ⟨9 + a.val, by omega⟩ = u a := by
  unfold pairVec
  rw [dif_neg (by show ¬ (9 + a.val < 9); omega)]
  congr 1
  ext; simp only; omega

theorem weighted_conj_integrable (Kb : CellBox) (hK : IsCellBox Kb) {T c : ℝ × ℝ → ℂ}
    (hTm : AEStronglyMeasurable T (volume.restrict Kb.rect))
    (hT2 : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T p‖ ^ 2) Kb.rect)
    (hcm : AEStronglyMeasurable c (volume.restrict Kb.rect)) {Cc : ℝ} (hcC : ∀ p ∈ Kb.rect, ‖c p‖ ≤ Cc) :
    IntegrableOn (fun p => (p.1 : ℂ) * (T p * (starRingEnd ℂ) (c p))) Kb.rect := by
  have hs := rect_measurableSet Kb
  have hwc : Continuous fun p : ℝ × ℝ => Kb.lineWeight p.1 := (lineWeight_continuous Kb).comp continuous_fst
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  have hw1 : IntegrableOn (fun p : ℝ × ℝ => Kb.lineWeight p.1) Kb.rect :=
    Integrable.mono' (integrable_const Cw) hwc.aestronglyMeasurable
      (ae_restrict_of_forall_mem hs fun p hp => hCw p hp)
  refine Integrable.mono' (((hw1.add hT2).div_const 2).mul_const (max Kb.r₂ 1 * max Cc 0))
    ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul (hTm.mul hcm.star)) ?_
  refine ae_restrict_of_forall_mem hs fun p hp => ?_
  obtain ⟨h0, h1⟩ := fst_le_lineWeight Kb hK hp
  have hw0 := lineWeight_nonneg Kb hK hp
  have hc : ‖c p‖ ≤ max Cc 0 := le_max_of_le_left (hcC p hp)
  have hT : ‖T p‖ ≤ (1 + ‖T p‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖T p‖ - 1)]
  have hM : 0 ≤ max Kb.r₂ 1 := le_trans zero_le_one (le_max_right _ _)
  have hC0 : 0 ≤ max Cc 0 := le_max_right _ _
  have e : ‖(p.1 : ℂ) * (T p * (starRingEnd ℂ) (c p))‖ = p.1 * (‖T p‖ * ‖c p‖) := by
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  rw [e]
  have hwT : Kb.lineWeight p.1 * ‖T p‖ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hT hw0]
  have hTc : ‖T p‖ * ‖c p‖ ≤ ‖T p‖ * max Cc 0 := mul_le_mul_of_nonneg_left hc (norm_nonneg _)
  show p.1 * (‖T p‖ * ‖c p‖) ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 * (max Kb.r₂ 1 * max Cc 0)
  calc p.1 * (‖T p‖ * ‖c p‖) ≤ (max Kb.r₂ 1 * Kb.lineWeight p.1) * (‖T p‖ * max Cc 0) :=
        mul_le_mul h1 hTc (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (mul_nonneg hM hw0)
    _ = (Kb.lineWeight p.1 * ‖T p‖) * (max Kb.r₂ 1 * max Cc 0) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hwT (mul_nonneg hM hC0)

theorem re_conj_swap (z w : ℂ) : (z * (starRingEnd ℂ) w).re = ((starRingEnd ℂ) z * w).re := by
  rw [← Complex.conj_re, map_mul, Complex.conj_conj, mul_comm]

theorem re_integral_pair_sum (Kb : CellBox) (hK : IsCellBox Kb) (T c : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hTm : ∀ a b, AEStronglyMeasurable (T a b) (volume.restrict Kb.rect))
    (hT2 : ∀ a b, IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T a b p‖ ^ 2) Kb.rect)
    (hcm : ∀ a b, AEStronglyMeasurable (c a b) (volume.restrict Kb.rect))
    (hcC : ∀ a b, ∃ Cc : ℝ, ∀ p ∈ Kb.rect, ‖c a b p‖ ≤ Cc) :
    (∫ p in Kb.rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, T a b p * (starRingEnd ℂ) (c a b p)).re
      = ∫ p in Kb.rect, ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ((starRingEnd ℂ) (T a b p) * c a b p).re := by
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, T a b p * (starRingEnd ℂ) (c a b p))
      = fun p => ∑ a : Fin 3, ∑ b : Fin 3, (p.1 : ℂ) * (T a b p * (starRingEnd ℂ) (c a b p)) := by
    funext p
    simp only [Finset.mul_sum]
  have hint : Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3, T a b p * (starRingEnd ℂ) (c a b p))
      (volume.restrict Kb.rect) := by
    rw [e]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    obtain ⟨Cc, hC⟩ := hcC a b
    exact weighted_conj_integrable Kb hK (hTm a b) (hT2 a b) (hcm a b) hC
  have h := integral_re hint
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1
  funext p
  rw [Complex.re_ofReal_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [re_conj_swap]

theorem cross_sum_integrable (Kb : CellBox) (hK : IsCellBox Kb) (T c : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (hTm : ∀ a b, AEStronglyMeasurable (T a b) (volume.restrict Kb.rect))
    (hT2 : ∀ a b, IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T a b p‖ ^ 2) Kb.rect)
    (hcm : ∀ a b, AEStronglyMeasurable (c a b) (volume.restrict Kb.rect))
    (hcC : ∀ a b, ∃ Cc : ℝ, ∀ p ∈ Kb.rect, ‖c a b p‖ ≤ Cc) :
    IntegrableOn (fun p => ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ((starRingEnd ℂ) (T a b p) * c a b p).re) Kb.rect := by
  refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
  obtain ⟨Cc, hC⟩ := hcC a b
  exact cross_integrable Kb hK (hTm a b) (hT2 a b) (hcm a b) hC

theorem conj_half_mul_re (z w : ℂ) :
    ((starRingEnd ℂ) ((1 / 2 : ℂ) * z) * w).re = (1 / 2) * ((starRingEnd ℂ) w * z).re := by
  simp only [map_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im, map_div₀, map_one, map_ofNat,
    Complex.div_re, Complex.div_im, Complex.one_re, Complex.one_im]
  norm_num
  ring

theorem tailNormSq_nonneg (Kb : CellBox) (hK : IsCellBox Kb) (Qd : ℕ) (F : ℝ × ℝ → ℂ) :
    0 ≤ Kb.tailNormSq Qd F := by
  unfold CellBox.tailNormSq CellBox.normSqOn CellBox.lineWeightFn
  exact setIntegral_nonneg (rect_measurableSet Kb) fun p hp => mul_nonneg (lineWeight_nonneg Kb hK hp) (sq_nonneg _)

section Data

variable {k : ℕ} {C : Type} {nE nM : ℕ}

theorem lowProfile_continuous (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (j : Fin 12) :
    Continuous fun p => lowProfile D R K ι x p j := by
  unfold lowProfile pairVec lowGrad lowVel lowStrainOf lowVelocityOf CellCert.CellEnergy.basisFn
    CellBases.radialPoly CellBases.heightPoly
  split_ifs
  · fun_prop
  · fun_prop

theorem pairWeightOf_cellState (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) :
    pairWeightOf (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) = fun g => ((pairWeight κ ζ g : ℝ) : ℂ) := by
  funext g
  cases g with
  | inl i => simp [pairWeightOf, cellState, pairWeight]
  | inr i => simp [pairWeightOf, cellState, pairWeight]

theorem profile_regular (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (hcc : CellCalculusConditions D R)
    (K : Fin D.mesh.count) (w : Fin k ⊕ Fin k → ℂ) (ι : ℤ × ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (fun p => pairingProfile D R K w ι p a b) (volume.restrict (D.mesh.box K).rect) ∧
      ∃ Cc : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖pairingProfile D R K w ι p a b‖ ≤ Cc := by
  choose hm Cg hCg using fun g => hcc.pair_profile_regular K g ι
  refine ⟨?_, ⟨∑ g, ‖w g‖ * Cg g, fun p hp => ?_⟩⟩
  · unfold pairingProfile
    refine (Finset.aestronglyMeasurable_sum Finset.univ fun g _ => (hm g a b).const_mul (w g)).congr
      (ae_of_all _ fun p => ?_)
    simp only [Finset.sum_apply]
  · unfold pairingProfile
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun g _ => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hCg g p hp a b) (norm_nonneg _)

def ProfileLive (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count) (ι : ℤ × ℤ) : Prop :=
  ∃ g a b, ¬ (fun p => R.pairProfile K g ι p a b) =ᵐ[volume.restrict (D.mesh.box K).rect] 0

theorem profile_ae_zero (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (ι : ℤ × ℤ) (h : ¬ ProfileLive D R K ι) (w : Fin k ⊕ Fin k → ℂ) :
    ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ∀ a b, pairingProfile D R K w ι p a b = 0 := by
  unfold ProfileLive at h
  push Not at h
  have h' : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ∀ g a b, R.pairProfile K g ι p a b = 0 := by
    rw [ae_all_iff]
    intro g
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    filter_upwards [h g a b] with p hp
    simpa using hp
  filter_upwards [h'] with p hp a b
  unfold pairingProfile
  simp [hp]

theorem gradAt_eq_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (a b : Fin 3) (p : ℝ × ℝ) :
    gradAt D.azimuthOrder ι G a b p = bandProfile D ι v G p ⟨3 * a.val + b.val, by omega⟩ := by
  unfold bandProfile
  rw [pairVec_at_grad]
  rfl

theorem grad_regular (D : CellLayerData k C nE nM) (hT : TrueFieldRegular D)
    {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K)) {q : Fin k → ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {gg : ℝ → Space → Space} {κ : Fin k → ℝ} {F Pg : ℝ → Space → Space}
    (ht : IsCellTuple D K q v G H gg κ F Pg) (ι : ℤ × ℤ) (a b : Fin 3) :
    AEStronglyMeasurable (fun p => gradAt D.azimuthOrder ι G a b p) (volume.restrict (D.mesh.box K).rect) ∧
      IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
        (D.mesh.box K).rect ∧
      IntegrableOn (fun p => p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2) (D.mesh.box K).rect := by
  obtain ⟨hm, hi⟩ := (hT.1 K q v G H gg κ F Pg ht).1 ι
  set j : Fin 12 := ⟨3 * a.val + b.val, by omega⟩ with hj
  have he : (fun p => gradAt D.azimuthOrder ι G a b p) = fun p => bandProfile D ι v G p j := by
    funext p
    exact gradAt_eq_bandProfile D ι v G a b p
  have hs := rect_measurableSet (D.mesh.box K)
  have hm' : AEStronglyMeasurable (fun p => gradAt D.azimuthOrder ι G a b p) (volume.restrict (D.mesh.box K).rect) := by
    rw [he]; exact hm j
  have hle : ∀ p ∈ (D.mesh.box K).rect, p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2
      ≤ p.1 * ∑ j', ‖bandProfile D ι v G p j'‖ ^ 2 := by
    intro p hp
    have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    rw [gradAt_eq_bandProfile D ι v G a b p]
    exact mul_le_mul_of_nonneg_left
      (Finset.single_le_sum (f := fun j' => ‖bandProfile D ι v G p j'‖ ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ j)) hp1
  have h3 : IntegrableOn (fun p => p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2) (D.mesh.box K).rect := by
    refine Integrable.mono' hi (continuous_fst.aestronglyMeasurable.mul (hm'.norm.pow 2)) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp1 (sq_nonneg _))]
    exact hle p hp
  refine ⟨hm', ?_, h3⟩
  set c0 : ℝ := if (D.mesh.box K).r₁ = 0 then 1 else (D.mesh.box K).r₁⁻¹ with hc0
  have hc : 0 ≤ c0 := by
    rw [hc0]; split_ifs
    · exact zero_le_one
    · exact inv_nonneg.2 hK.r_order.1
  refine Integrable.mono' (h3.const_mul c0)
    ((((lineWeight_continuous _).comp continuous_fst).aestronglyMeasurable).mul (hm'.norm.pow 2)) ?_
  refine ae_restrict_of_forall_mem hs fun p hp => ?_
  have h0 := lineWeight_nonneg _ hK hp
  have h1 := lineWeight_le_scaled _ hK hp
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  calc (D.mesh.box K).lineWeight p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2
      ≤ (c0 * p.1) * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    _ = c0 * (p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2) := by ring

end Data

end Breakdown.CertCell.Assembly.Internal.RestrictedPairing

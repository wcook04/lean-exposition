import Breakdown.CertCell.AssemblyPairingStageParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RestrictedPairing

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Breakdown.CertCell.Assembly.Internal.PotentialTails

attribute [local instance] rect_finite

section Classes

variable {k : ℕ} {C : Type} {nE nM : ℕ}

def pairCross (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (w : Fin k ⊕ Fin k → ℂ) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) : ℝ :=
  ∫ p in (D.mesh.box K).rect, ∑ a : Fin 3, ∑ b : Fin 3,
    p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * pairingProfile D R K w ι p a b).re

theorem pairCross_dead (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (w : Fin k ⊕ Fin k → ℂ) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (h : ¬ ProfileLive D R K ι) :
    pairCross D R K w G ι = 0 := by
  unfold pairCross
  have hz : (fun p : ℝ × ℝ => ∑ a : Fin 3, ∑ b : Fin 3,
      p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * pairingProfile D R K w ι p a b).re)
      =ᵐ[volume.restrict (D.mesh.box K).rect] fun _ => (0 : ℝ) := by
    filter_upwards [profile_ae_zero D R K ι h w] with p hp
    simp [hp]
  rw [integral_congr_ae hz]
  simp

theorem share_eq (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (hcc : CellCalculusConditions D R)
    (hT : TrueFieldRegular D) {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K)) {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gg : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H gg κ F Pg) (ζ : Fin k → ℝ) :
    pairShare D K R.pairLabels (R.pairProfile K) κ ζ G
      = ∑ ι ∈ R.pairLabels, pairCross D R K (fun g => ((pairWeight κ ζ g : ℝ) : ℂ)) G ι := by
  have hXC : ∀ g ι a b, ∃ Cc : ℝ, ∀ p ∈ (D.mesh.box K).rect, ‖R.pairProfile K g ι p a b‖ ≤ Cc := by
    intro g ι a b
    obtain ⟨Cc, hC⟩ := (hcc.pair_profile_regular K g ι).2
    exact ⟨Cc, fun p hp => hC p hp a b⟩
  have hre : ∀ g ι, (∫ p in (D.mesh.box K).rect, (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
        gradAt D.azimuthOrder ι G a b p * (starRingEnd ℂ) (R.pairProfile K g ι p a b)).re
      = ∫ p in (D.mesh.box K).rect, ∑ a : Fin 3, ∑ b : Fin 3,
        p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * R.pairProfile K g ι p a b).re := fun g ι =>
    re_integral_pair_sum (D.mesh.box K) hK (fun a b p => gradAt D.azimuthOrder ι G a b p)
      (fun a b p => R.pairProfile K g ι p a b) (fun a b => (grad_regular D hT hK ht ι a b).1)
      (fun a b => (grad_regular D hT hK ht ι a b).2.1) (fun a b => (hcc.pair_profile_regular K g ι).1 a b)
      (hXC g ι)
  have hint : ∀ g ι, IntegrableOn (fun p => ∑ a : Fin 3, ∑ b : Fin 3,
        p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * R.pairProfile K g ι p a b).re)
        (D.mesh.box K).rect := fun g ι =>
    cross_sum_integrable (D.mesh.box K) hK (fun a b p => gradAt D.azimuthOrder ι G a b p)
      (fun a b p => R.pairProfile K g ι p a b) (fun a b => (grad_regular D hT hK ht ι a b).1)
      (fun a b => (grad_regular D hT hK ht ι a b).2.1) (fun a b => (hcc.pair_profile_regular K g ι).1 a b)
      (hXC g ι)
  unfold pairShare
  simp only [hre]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [← integral_const_mul]
  rw [← integral_finsetSum _ fun g _ => ((hint g ι).const_mul (pairWeight κ ζ g))]
  unfold pairCross
  congr 1
  funext p
  unfold pairingProfile
  simp only [Finset.mul_sum, Complex.re_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [mul_left_comm ((starRingEnd ℂ) _), Complex.re_ofReal_mul]
  ring

theorem band_term_eq (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop)
    (hC : PairingConditions D R A Q S) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (x : CellVars D R K → ℂ) (hx : S K x)
    (ι : ℤ × ℤ) (hι : ι ∈ D.mesh.band K) :
    (∫ p in (D.mesh.box K).rect, p.1 * (2 * (∑ j, (starRingEnd ℂ)
        (linearField ((A.blocks K).pairingSource ι) x p j) * bandProfile D ι v G p j).re))
      = if ι ∈ R.pairLabels then pairCross D R K (pairWeightOf x) G ι else 0 := by
  split_ifs with hL
  · unfold pairCross
    congr 1
    funext p
    rw [hC.source_eq K ι hι x hx p hL, Complex.re_sum, sum_fin12]
    simp only [bandProfile, pairVec_at_grad, pairVec_at_vel, Pi.zero_apply, map_zero, zero_mul, Complex.zero_re,
      Finset.sum_const_zero, add_zero, conj_half_mul_re, gradArray]
    simp only [Fin.sum_univ_three]
    ring
  · have h0 : ∀ p, linearField ((A.blocks K).pairingSource ι) x p = 0 := hC.source_zero K ι hι hL x hx
    simp [h0]

open Classical in
theorem resolved_bound (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop)
    (hC : PairingConditions D R A Q S) (hT : TrueFieldRegular D)
    (hLT : LowTailSplit D R) (hPO : ProjResidualOrthogonal) {K : Fin D.mesh.count} {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gg : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H gg κ F Pg) (ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) (ι : D.mesh.resolved K) (hL : ι.1 ∈ R.pairLabels) :
    (∫ p in (D.mesh.box K).rect, p.1 * (∑ a : Fin 3, ∑ b : Fin 3,
        lowGrad D R K ι (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) p a b
          * (starRingEnd ℂ) (pairingProfile D R K
            (pairWeightOf (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)) ι.1 p a b)).re)
      ≤ pairCross D R K (pairWeightOf (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)) G ι.1
        + (A.blocks K).pairingStrainCost ι.1 * tailStrainSq D R K ι.1 G
        + (if ProfileLive D R K ι.1 then
            Coupling.quadForm ((Q K).gammaGram ι.1) (pairWeightOf (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η))
              / (4 * (Q K).gammaWeight ι.1) else 0) := by
  have hsplitAe := hLT K q v G H gg κ F Pg ht ζ η ι.1 ι.2
  have hwr := pairWeightOf_cellState D R K v G H Pg κ ζ η
  set x := cellState D.mesh K (R.layouts K) v G H Pg κ ζ η with hx
  set w := pairWeightOf x with hw
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  set Qd := ((R.layouts K).layout ι.1).degCoef with hQd
  have htss : tailStrainSq D R K ι.1 G
      = ∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).tailNormSq Qd (fun p => gradAt D.azimuthOrder ι.1 G a b p) := rfl
  have ht0 : 0 ≤ tailStrainSq D R K ι.1 G := by
    rw [htss]
    exact Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => tailNormSq_nonneg _ hK _ _
  have hcost0 : 0 ≤ (A.blocks K).pairingStrainCost ι.1 * tailStrainSq D R K ι.1 G :=
    mul_nonneg (hC.cost_nonneg K ι.1) ht0
  by_cases hlive : ProfileLive D R K ι.1
  swap
  · rw [if_neg hlive, pairCross_dead D R K w G ι.1 hlive]
    have hz : (fun p : ℝ × ℝ => p.1 * (∑ a : Fin 3, ∑ b : Fin 3,
        lowGrad D R K ι x p a b * (starRingEnd ℂ) (pairingProfile D R K w ι.1 p a b)).re)
        =ᵐ[volume.restrict (D.mesh.box K).rect] fun _ => (0 : ℝ) := by
      filter_upwards [profile_ae_zero D R K ι.1 hlive w] with p hp
      simp [hp]
    rw [integral_congr_ae hz]
    simp only [integral_zero]
    linarith
  rw [if_pos hlive]
  obtain ⟨hgm, hγ, hγc, hΓ⟩ := hC.gamma_resolved K ι.1 ι.2 hL hlive
  have hΓw : ∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).tailNormSq Qd
        (fun p => ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) * pairingProfile D R K w ι.1 p a b)
      ≤ Coupling.quadForm ((Q K).gammaGram ι.1) w := by
    rw [hwr]
    exact hΓ (pairWeight κ ζ)
  have hΓ0 : 0 ≤ Coupling.quadForm ((Q K).gammaGram ι.1) w := by
    rw [hwr]
    exact (hC.gamma_gram K ι.1 hgm).2 (pairWeight κ ζ)
  have hB : IsCellBases (D.mesh.box K) (R.layouts K).bases := by
    obtain ⟨_, _, _, _, hLy⟩ := (hC.cell_conditions.layouts_valid K).layout_valid ι.1 ι.2
    exact hLy.bases_valid
  have hg := fun a b => grad_regular D hT hK ht ι.1 a b
  have hP := fun a b => profile_regular D R hC.cell_conditions K w ι.1 a b
  have h2γ : 0 < 2 * (Q K).gammaWeight ι.1 := by linarith
  have htc : ∀ a b, IntegrableOn (fun p => p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι.1 G a b p
        - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
          * pairingProfile D R K w ι.1 p a b).re) (D.mesh.box K).rect ∧
      -((D.mesh.box K).tailNormSq Qd (fun p => (CellScalars.rHat (D.mesh.box K) p : ℂ) * pairingProfile D R K w ι.1 p a b)
          / (2 * (Q K).gammaWeight ι.1)
        + (2 * (Q K).gammaWeight ι.1) * (D.mesh.box K).tailNormSq Qd (fun p => gradAt D.azimuthOrder ι.1 G a b p))
      ≤ 2 * ∫ p in (D.mesh.box K).rect, p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι.1 G a b p
        - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
          * pairingProfile D R K w ι.1 p a b).re := by
    intro a b
    obtain ⟨Cc, hCc⟩ := (hP a b).2
    exact tail_cross_lower (D.mesh.box K) hK Qd (fun p => gradAt D.azimuthOrder ι.1 G a b p)
      (fun p => pairingProfile D R K w ι.1 p a b) h2γ
      (hPO (D.mesh.box K) hK _ hB Qd _ (hg a b).1 (hg a b).2.1) (hg a b).1 (hg a b).2.1 (hP a b).1 hCc
  have hlowc : ∀ a b, Continuous (fun p => lowGrad D R K ι x p a b) := by
    intro a b
    have h := lowProfile_continuous D R K ι x ⟨3 * a.val + b.val, by omega⟩
    convert h using 1
    funext p
    unfold lowProfile
    rw [pairVec_at_grad]
  have hlowI : IntegrableOn (fun p => ∑ a : Fin 3, ∑ b : Fin 3,
      p.1 * ((starRingEnd ℂ) (lowGrad D R K ι x p a b) * pairingProfile D R K w ι.1 p a b).re) (D.mesh.box K).rect :=
    cross_sum_integrable (D.mesh.box K) hK (fun a b p => lowGrad D R K ι x p a b)
      (fun a b p => pairingProfile D R K w ι.1 p a b) (fun a b => (hlowc a b).aestronglyMeasurable)
      (fun a b => ContinuousOn.integrableOn_compact (rect_isCompact _)
        ((((lineWeight_continuous _).comp continuous_fst).mul ((hlowc a b).norm.pow 2)).continuousOn))
      (fun a b => (hP a b).1) (fun a b => (hP a b).2)
  have htailI : IntegrableOn (fun p => ∑ a : Fin 3, ∑ b : Fin 3,
      p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι.1 G a b p
        - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
          * pairingProfile D R K w ι.1 p a b).re) (D.mesh.box K).rect :=
    integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (htc a b).1
  have hE : (∫ p in (D.mesh.box K).rect, p.1 * (∑ a : Fin 3, ∑ b : Fin 3,
        lowGrad D R K ι x p a b * (starRingEnd ℂ) (pairingProfile D R K w ι.1 p a b)).re)
      = ∫ p in (D.mesh.box K).rect, ∑ a : Fin 3, ∑ b : Fin 3,
        p.1 * ((starRingEnd ℂ) (lowGrad D R K ι x p a b) * pairingProfile D R K w ι.1 p a b).re := by
    congr 1
    funext p
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [re_conj_swap]
  set Tt := ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι.1 G a b p
            - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
              * pairingProfile D R K w ι.1 p a b).re with hTt
  have hsplit : pairCross D R K w G ι.1
      = (∫ p in (D.mesh.box K).rect, ∑ a : Fin 3, ∑ b : Fin 3,
          p.1 * ((starRingEnd ℂ) (lowGrad D R K ι x p a b) * pairingProfile D R K w ι.1 p a b).re) + Tt := by
    have e3 : Tt = ∫ p in (D.mesh.box K).rect, ∑ a : Fin 3, ∑ b : Fin 3,
          p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι.1 G a b p
            - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
              * pairingProfile D R K w ι.1 p a b).re := by
      rw [hTt, integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (htc a b).1)]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun b _ => (htc a b).1]
    rw [e3, ← integral_add hlowI htailI]
    unfold pairCross
    refine integral_congr_ae ?_
    filter_upwards [hsplitAe] with p hp
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hc := congrFun hp ⟨3 * a.val + b.val, by omega⟩
    simp only [trueProfiles, Pi.add_apply, lowAt, dif_pos ι.2, tailProfile, lowProfile, pairVec_at_grad,
      bandProfile, gradArray, Subtype.coe_eta] at hc
    conv_lhs => rw [hc]
    rw [map_add, add_mul, Complex.add_re, mul_add]
  have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
    Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => (htc a b).2
  have hX : (∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).tailNormSq Qd
        (fun p => (CellScalars.rHat (D.mesh.box K) p : ℂ) * pairingProfile D R K w ι.1 p a b)
          / (2 * (Q K).gammaWeight ι.1))
      ≤ Coupling.quadForm ((Q K).gammaGram ι.1) w / (2 * (Q K).gammaWeight ι.1) := by
    simp only [← Finset.sum_div]
    exact div_le_div_of_nonneg_right hΓw h2γ.le
  have hsum' : -(Coupling.quadForm ((Q K).gammaGram ι.1) w / (2 * (Q K).gammaWeight ι.1)
        + (2 * (Q K).gammaWeight ι.1) * tailStrainSq D R K ι.1 G) ≤ 2 * Tt := by
    have e1 : (∑ a : Fin 3, ∑ b : Fin 3,
        -((D.mesh.box K).tailNormSq Qd (fun p => (CellScalars.rHat (D.mesh.box K) p : ℂ) * pairingProfile D R K w ι.1 p a b)
          / (2 * (Q K).gammaWeight ι.1)
        + (2 * (Q K).gammaWeight ι.1) * (D.mesh.box K).tailNormSq Qd (fun p => gradAt D.azimuthOrder ι.1 G a b p)))
        = -((∑ a : Fin 3, ∑ b : Fin 3, (D.mesh.box K).tailNormSq Qd
          (fun p => (CellScalars.rHat (D.mesh.box K) p : ℂ) * pairingProfile D R K w ι.1 p a b)
            / (2 * (Q K).gammaWeight ι.1))
          + (2 * (Q K).gammaWeight ι.1) * tailStrainSq D R K ι.1 G) := by
      rw [htss]
      simp only [Fin.sum_univ_three]
      ring
    have e2 : (∑ a : Fin 3, ∑ b : Fin 3, 2 * ∫ p in (D.mesh.box K).rect, p.1 * ((starRingEnd ℂ)
        (gradAt D.azimuthOrder ι.1 G a b p
          - (D.mesh.box K).proj Qd Qd (fun p' => gradAt D.azimuthOrder ι.1 G a b p') p)
            * pairingProfile D R K w ι.1 p a b).re) = 2 * Tt := by
      rw [hTt]
      simp only [Fin.sum_univ_three]
      ring
    rw [e1, e2] at hsum
    linarith
  have hq : Coupling.quadForm ((Q K).gammaGram ι.1) w / (2 * (Q K).gammaWeight ι.1)
      = 2 * (Coupling.quadForm ((Q K).gammaGram ι.1) w / (4 * (Q K).gammaWeight ι.1)) := by
    field_simp
    ring
  have hct : (Q K).gammaWeight ι.1 * tailStrainSq D R K ι.1 G
      ≤ (A.blocks K).pairingStrainCost ι.1 * tailStrainSq D R K ι.1 G :=
    mul_le_mul_of_nonneg_right hγc ht0
  rw [hE]
  linarith

open Classical in
theorem other_bound (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop)
    (hC : PairingConditions D R A Q S) (hT : TrueFieldRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {gg : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H gg κ F Pg) (w : Fin k ⊕ Fin k → ℂ)
    (wr : Fin k ⊕ Fin k → ℝ) (hw : w = fun g => ((wr g : ℝ) : ℂ))
    (ι : ℤ × ℤ) (hL : ι ∈ R.pairLabels) (hr : ι ∉ D.mesh.resolved K) (hb : ι ∉ D.mesh.band K) :
    -(if ProfileLive D R K ι then ∫ p in (D.mesh.box K).rect, p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p)
        else 0)
      - (if ProfileLive D R K ι then Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0)
      ≤ pairCross D R K w G ι := by
  by_cases hlive : ProfileLive D R K ι
  swap
  · rw [if_neg hlive, if_neg hlive, pairCross_dead D R K w G ι hlive]
    norm_num
  rw [if_pos hlive, if_pos hlive]
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  obtain ⟨hgm, _, hγ, hγl, hBw⟩ := hC.gamma_other K ι hL hr hb hlive
  have hΓ0 : 0 ≤ Coupling.quadForm ((Q K).gammaGram ι) w := by
    rw [hw]
    exact (hC.gamma_gram K ι hgm).2 wr
  have hB : ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖pairingProfile D R K w ι p a b‖ ^ 2
      ≤ Coupling.quadForm ((Q K).gammaGram ι) w := by
    rw [hw]
    exact hBw wr
  have hs := rect_measurableSet (D.mesh.box K)
  have hg := fun a b => grad_regular D hT hK ht ι a b
  have hP := fun a b => profile_regular D R hC.cell_conditions K w ι a b
  set γ := (Q K).gammaWeight ι with hγdef
  set l := (A.blocks K).leakStrain ι with hldef
  have hAI : IntegrableOn (fun p => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
      (D.mesh.box K).rect := by
    have e : (fun p : ℝ × ℝ => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
        = fun p => ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 := by
      funext p; simp only [Finset.mul_sum]
    rw [e]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (hg a b).2.2
  have hBI : IntegrableOn (fun p => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖pairingProfile D R K w ι p a b‖ ^ 2)
      (D.mesh.box K).rect := by
    have e : (fun p : ℝ × ℝ => p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖pairingProfile D R K w ι p a b‖ ^ 2)
        = fun p => ∑ a : Fin 3, ∑ b : Fin 3, p.1 * ‖pairingProfile D R K w ι p a b‖ ^ 2 := by
      funext p; simp only [Finset.mul_sum]
    rw [e]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    obtain ⟨Cc, hCc⟩ := (hP a b).2
    refine Integrable.mono' (integrable_const ((D.mesh.box K).r₂ * (max Cc 0) ^ 2))
      (continuous_fst.aestronglyMeasurable.mul ((hP a b).1.norm.pow 2))
      (ae_restrict_of_forall_mem hs fun p hp => ?_)
    have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hp2 : p.1 ≤ (D.mesh.box K).r₂ := hp.1.2
    have hn : ‖pairingProfile D R K w ι p a b‖ ≤ max Cc 0 := le_max_of_le_left (hCc p hp)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp1 (sq_nonneg _))]
    exact mul_le_mul hp2 (pow_le_pow_left₀ (norm_nonneg _) hn 2) (sq_nonneg _) (le_trans hp1 hp2)
  have hcI := cross_sum_integrable (D.mesh.box K) hK (fun a b p => gradAt D.azimuthOrder ι G a b p)
    (fun a b p => pairingProfile D R K w ι p a b) (fun a b => (hg a b).1) (fun a b => (hg a b).2.1)
    (fun a b => (hP a b).1) (fun a b => (hP a b).2)
  have h2γ : 0 < 2 * γ := by linarith
  have hpt : ∀ p ∈ (D.mesh.box K).rect,
      -γ * (p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
        - (1 / (4 * γ)) * (p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖pairingProfile D R K w ι p a b‖ ^ 2)
      ≤ ∑ a : Fin 3, ∑ b : Fin 3,
        p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * pairingProfile D R K w ι p a b).re := by
    intro p hp
    have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
    have hterm : ∀ a b : Fin 3, -(((2 * γ) * (p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
          + p.1 * ‖pairingProfile D R K w ι p a b‖ ^ 2 / (2 * γ)) / 2)
        ≤ p.1 * ((starRingEnd ℂ) (gradAt D.azimuthOrder ι G a b p) * pairingProfile D R K w ι p a b).re := by
      intro a b
      have h1 := re_conj_mul_le (gradAt D.azimuthOrder ι G a b p) (pairingProfile D R K w ι p a b)
      have h2 := two_mul_le_weighted ‖gradAt D.azimuthOrder ι G a b p‖ ‖pairingProfile D R K w ι p a b‖ (2 * γ) h2γ
      have h3 := (abs_le.1 h1).1
      have h4 : p.1 * (‖gradAt D.azimuthOrder ι G a b p‖ * ‖pairingProfile D R K w ι p a b‖)
          ≤ p.1 * (((2 * γ) * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2
            + ‖pairingProfile D R K w ι p a b‖ ^ 2 / (2 * γ)) / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hp1
      have h5 := mul_le_mul_of_nonneg_left h3 hp1
      calc -(((2 * γ) * (p.1 * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
            + p.1 * ‖pairingProfile D R K w ι p a b‖ ^ 2 / (2 * γ)) / 2)
          = -(p.1 * (((2 * γ) * ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2
            + ‖pairingProfile D R K w ι p a b‖ ^ 2 / (2 * γ)) / 2)) := by ring
        _ ≤ -(p.1 * (‖gradAt D.azimuthOrder ι G a b p‖ * ‖pairingProfile D R K w ι p a b‖)) := neg_le_neg h4
        _ = p.1 * -(‖gradAt D.azimuthOrder ι G a b p‖ * ‖pairingProfile D R K w ι p a b‖) := by ring
        _ ≤ _ := h5
    have hsum := Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) =>
      Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => hterm a b
    refine le_trans (le_of_eq ?_) hsum
    simp only [Fin.sum_univ_three]
    field_simp
    ring
  have hmono := setIntegral_mono_on ((hAI.const_mul (-γ)).sub (hBI.const_mul (1 / (4 * γ)))) hcI hs hpt
  simp only [Pi.sub_apply] at hmono
  rw [integral_sub (hAI.const_mul (-γ)) (hBI.const_mul (1 / (4 * γ))), integral_const_mul,
    integral_const_mul] at hmono
  have hleak : (∫ p in (D.mesh.box K).rect, p.1 * (l * modeStrainSq D ι G p))
      = l * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 := by
    rw [← integral_const_mul]
    congr 1
    funext p
    unfold modeStrainSq
    ring
  have hA0 : 0 ≤ ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 :=
    setIntegral_nonneg hs fun p hp => mul_nonneg (le_trans hK.r_order.1 hp.1.1)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _)
  have h1 : (1 / (4 * γ)) * (∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
      ‖pairingProfile D R K w ι p a b‖ ^ 2) ≤ (1 / (4 * γ)) * Coupling.quadForm ((Q K).gammaGram ι) w :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have h1' : (1 / (4 * γ)) * Coupling.quadForm ((Q K).gammaGram ι) w
      = Coupling.quadForm ((Q K).gammaGram ι) w / (4 * γ) := by ring
  have h2 : γ * (∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3,
      ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2)
      ≤ l * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hγl hA0
  rw [hleak]
  unfold pairCross
  linarith

theorem sum_split_three {M : Type} [AddCommMonoid M] (L res band : Finset (ℤ × ℤ)) (hd : Disjoint res band)
    (f : ℤ × ℤ → M) :
    ∑ ι ∈ L, f ι = ∑ ι ∈ L.filter (· ∈ res), f ι + ∑ ι ∈ L.filter (· ∈ band), f ι
      + ∑ ι ∈ L.filter (fun ι => ι ∉ res ∧ ι ∉ band), f ι := by
  rw [← Finset.sum_filter_add_sum_filter_not L (· ∈ res), add_assoc]
  congr 1
  rw [← Finset.sum_filter_add_sum_filter_not (L.filter (· ∉ res)) (· ∈ band), Finset.filter_filter,
    Finset.filter_filter]
  congr 1
  refine Finset.sum_congr (Finset.filter_congr fun ι _ => ?_) fun _ _ => rfl
  exact ⟨fun h => h.2, fun h => ⟨Finset.disjoint_right.1 hd h, h⟩⟩

open Classical in
theorem stage_cell (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (Q : Fin D.mesh.count → PairingData k) (S : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop)
    (hT : TrueFieldRegular D) (hS : CellStatesIn D R S) (hC : PairingConditions D R A Q S)
    (hLT : LowTailSplit D R) (hPO : ProjResidualOrthogonal) : PairingStage D R A := by
  intro K q v G H gg κ F Pg ht ζ η
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  have hs := rect_measurableSet (D.mesh.box K)
  have hSx := hS K q v G H gg κ F Pg ht ζ η
  have hwx := pairWeightOf_cellState D R K v G H Pg κ ζ η
  have hres := fun (ι : D.mesh.resolved K) (h : ι.1 ∈ R.pairLabels) =>
    resolved_bound D R A Q S hC hT hLT hPO ht ζ η ι h
  set x := cellState D.mesh K (R.layouts K) v G H Pg κ ζ η with hx
  set w := pairWeightOf x with hw
  have hd : Disjoint (D.mesh.resolved K) (D.mesh.band K) := hC.mesh_valid.band_apart K
  have hkept := hC.kept_le K x hSx
  have hband0 : bandLinear D K (A.blocks K).pairingSource x (fun ι => bandProfile D ι v G)
      = ∑ ι ∈ D.mesh.band K, (if ι ∈ R.pairLabels then pairCross D R K w G ι else 0) := by
    unfold bandLinear
    exact Finset.sum_congr rfl fun ι hι => band_term_eq D R A Q S hC K v G x hSx ι hι
  have hband : bandLinear D K (A.blocks K).pairingSource x (fun ι => bandProfile D ι v G)
      = ∑ ι ∈ R.pairLabels.filter (· ∈ D.mesh.band K), pairCross D R K w G ι := by
    rw [hband0, ← Finset.sum_filter]
    congr 1
    ext ι
    simp only [Finset.mem_filter]
    exact and_comm
  have hshare : pairShare D K R.pairLabels (R.pairProfile K) κ ζ G = ∑ ι ∈ R.pairLabels, pairCross D R K w G ι := by
    rw [share_eq D R hC.cell_conditions hT hK ht ζ, ← hwx]
  have hresolved : (∑ ι : D.mesh.resolved K, (if ι.1 ∈ R.pairLabels then ∫ p in (D.mesh.box K).rect, p.1 *
      (∑ a : Fin 3, ∑ b : Fin 3, lowGrad D R K ι x p a b
        * (starRingEnd ℂ) (pairingProfile D R K w ι.1 p a b)).re else 0))
      ≤ ∑ ι ∈ R.pairLabels.filter (· ∈ D.mesh.resolved K), (pairCross D R K w G ι
        + (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
        + (if ProfileLive D R K ι then Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0)) := by
    calc _ ≤ ∑ ι : D.mesh.resolved K, (if ι.1 ∈ R.pairLabels then pairCross D R K w G ι.1
            + (A.blocks K).pairingStrainCost ι.1 * tailStrainSq D R K ι.1 G
            + (if ProfileLive D R K ι.1 then
                Coupling.quadForm ((Q K).gammaGram ι.1) w / (4 * (Q K).gammaWeight ι.1) else 0) else 0) := by
          refine Finset.sum_le_sum fun ι _ => ?_
          by_cases h : ι.1 ∈ R.pairLabels
          · rw [if_pos h, if_pos h]
            exact hres ι h
          · rw [if_neg h, if_neg h]
      _ = ∑ ι ∈ D.mesh.resolved K, (if ι ∈ R.pairLabels then pairCross D R K w G ι
            + (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
            + (if ProfileLive D R K ι then
                Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0) else 0) :=
          Finset.sum_coe_sort (D.mesh.resolved K) (fun ι => if ι ∈ R.pairLabels then pairCross D R K w G ι
            + (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
            + (if ProfileLive D R K ι then
                Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0) else 0)
      _ = _ := by
          rw [← Finset.sum_filter]
          congr 1
          ext ι
          simp only [Finset.mem_filter]
          exact and_comm
  have hother : ∑ ι ∈ R.pairLabels.filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K),
      (-(if ProfileLive D R K ι then
          ∫ p in (D.mesh.box K).rect, p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0)
        - (if ProfileLive D R K ι then Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0))
      ≤ ∑ ι ∈ R.pairLabels.filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K), pairCross D R K w G ι := by
    refine Finset.sum_le_sum fun ι hι => ?_
    obtain ⟨hL, hr, hb⟩ := Finset.mem_filter.1 hι
    exact other_bound D R A Q S hC hT ht w (pairWeight κ ζ) hwx ι hL hr hb
  have hgam0 : ∀ ι ∈ (Q K).gammaModes, 0 ≤ Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) := by
    intro ι hι
    have h0 : 0 ≤ Coupling.quadForm ((Q K).gammaGram ι) w := by
      rw [hwx]
      exact (hC.gamma_gram K ι hι).2 (pairWeight κ ζ)
    have h1 := (hC.gamma_gram K ι hι).1
    positivity
  have hgam : ∑ ι ∈ R.pairLabels.filter (· ∈ D.mesh.resolved K),
        (if ProfileLive D R K ι then Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0)
      + ∑ ι ∈ R.pairLabels.filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K),
        (if ProfileLive D R K ι then Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) else 0)
      ≤ ∑ ι ∈ (Q K).gammaModes, Coupling.quadForm ((Q K).gammaGram ι) w / (4 * (Q K).gammaWeight ι) := by
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    have hdis : Disjoint ((R.pairLabels.filter (· ∈ D.mesh.resolved K)).filter (ProfileLive D R K))
        ((R.pairLabels.filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K)).filter (ProfileLive D R K)) := by
      rw [Finset.disjoint_left]
      intro ι h1 h2
      exact (Finset.mem_filter.1 (Finset.mem_filter.1 h2).1).2.1 (Finset.mem_filter.1 (Finset.mem_filter.1 h1).1).2
    rw [← Finset.sum_union hdis]
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ι hι _ => hgam0 ι hι
    intro ι hι
    rcases Finset.mem_union.1 hι with h | h
    · obtain ⟨h', hlive⟩ := Finset.mem_filter.1 h
      obtain ⟨hL, hr⟩ := Finset.mem_filter.1 h'
      exact (hC.gamma_resolved K ι hr hL hlive).1
    · obtain ⟨h', hlive⟩ := Finset.mem_filter.1 h
      obtain ⟨hL, hr, hb⟩ := Finset.mem_filter.1 h'
      exact (hC.gamma_other K ι hL hr hb hlive).1
  have hcost : ∑ ι ∈ R.pairLabels.filter (· ∈ D.mesh.resolved K), (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G
      ≤ ∑ ι ∈ D.mesh.resolved K, (A.blocks K).pairingStrainCost ι * tailStrainSq D R K ι G := by
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun ι h => (Finset.mem_filter.1 h).2) fun ι _ _ => ?_
    exact mul_nonneg (hC.cost_nonneg K ι)
      (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => tailNormSq_nonneg _ hK _ _)
  have hleak : ∑ ι ∈ R.pairLabels.filter (fun ι => ι ∉ D.mesh.resolved K ∧ ι ∉ D.mesh.band K),
        (if ProfileLive D R K ι then
          ∫ p in (D.mesh.box K).rect, p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0)
      ≤ pairingLeakAmount D K (A.blocks K) G := by
    rw [← Finset.sum_filter]
    unfold pairingLeakAmount
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun ι _ _ => ?_
    · intro ι h
      obtain ⟨h', hlive⟩ := Finset.mem_filter.1 h
      obtain ⟨hL, hr, hb⟩ := Finset.mem_filter.1 h'
      exact (hC.gamma_other K ι hL hr hb hlive).2.1
    · exact setIntegral_nonneg hs fun p hp => mul_nonneg (le_trans hK.r_order.1 hp.1.1)
        (mul_nonneg (hC.leak_nonneg K ι) (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _))
  have hsplit := sum_split_three R.pairLabels (D.mesh.resolved K) (D.mesh.band K) hd (fun ι => pairCross D R K w G ι)
  unfold pairingExact at hkept
  rw [hband, hshare]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hresolved hother
  linarith

end Classes

end Breakdown.CertCell.Assembly.Internal.RestrictedPairing

namespace Breakdown.CertCell.Assembly

theorem pairingStageHolds_of_lowTailSplit (hLT : LowTailSplitHolds) (hPO : ProjResidualOrthogonal) :
    PairingStageHolds := by
  intro k C nE nM D R A Q S hA hT hS hC
  exact Internal.RestrictedPairing.stage_cell D R A Q S hT hS hC (hLT D R hA hT hC.cell_conditions) hPO

end Breakdown.CertCell.Assembly

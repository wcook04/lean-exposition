import Breakdown.CertCell.AssemblyPotentialGroupsChargeAux

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus ChargeAux

variable {k : ℕ} {C : Type} {nE nM : ℕ} {V : Type}

theorem alternatingSymbol_eq_permSign (i j l : Fin 3) :
    (alternatingSymbol i j l : ℂ) = (CellCert.permSign i j l : ℂ) := by
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol, CellCert.permSign]

theorem gradOf_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    gradOf (bandProfile D ι v G p) = fun ab => gradAt D.azimuthOrder ι G ab.1 ab.2 p := by
  funext ab
  rcases ab with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem velOf_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    velOf (bandProfile D ι v G p) = fun a => velAt D.azimuthOrder ι v a p := by
  funext a
  fin_cases a <;> rfl

theorem curl_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    cnormSq (curlOfGrad (gradOf (bandProfile D ι v G p))) = modeCurlSq D ι G p := by
  rw [gradOf_bandProfile]
  unfold cnormSq curlOfGrad modeCurlSq curlComp gradArray
  simp only [alternatingSymbol_eq_permSign]

theorem strain_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    cnormSq (gradOf (bandProfile D ι v G p)) = modeStrainSq D ι G p := by
  rw [gradOf_bandProfile]
  unfold cnormSq modeStrainSq
  rw [Fintype.sum_prod_type]

theorem vel_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    cnormSq (velOf (bandProfile D ι v G p)) = modeVelSq D ι v p := by
  rw [velOf_bandProfile]
  rfl

theorem highPartner_bandProfile {V : Type} (D : CellLayerData k C nE nM) (P : PotentialData V) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    highPartnerCharge P (bandProfile D ι v G p)
      = P.highStrain / P.youngCurl * modeCurlSq D ι G p
        + 3 / (2 * Real.sqrt 2) * P.highGrad * (modeVelSq D ι v p / P.youngStrain + modeStrainSq D ι G p / P.youngVel) := by
  rw [← curl_bandProfile D ι v G p, ← strain_bandProfile D ι v G p, ← vel_bandProfile D ι v G p]
  unfold highPartnerCharge curlSq sumSq vecSq strainOfVec cnormSq curlOfGrad curlComp
  simp only [alternatingSymbol_eq_permSign, Fintype.sum_prod_type]

theorem splitCharge_bandProfile (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (σc cs cv : ℝ) :
    splitCharge σc cs cv (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
      = σc * modeCurlSq D ι G p + cs * modeStrainSq D ι G p + cv * modeVelSq D ι v p := by
  unfold splitCharge
  rw [curl_bandProfile, strain_bandProfile, vel_bandProfile]

theorem profile_sq_split (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∑ j, ‖bandProfile D ι v G p j‖ ^ 2 = modeStrainSq D ι G p + modeVelSq D ι v p := by
  rw [← strain_bandProfile D ι v G p, ← vel_bandProfile D ι v G p, gradOf_velOf_cnormSq]

theorem bandWeight_le (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (w : Fin 12 → ℝ) :
    ∑ j, w j * ‖bandProfile D ι v G p j‖ ^ 2
      ≤ (⨆ j : Fin 9, w ⟨j.val, by omega⟩) * modeStrainSq D ι G p
        + (⨆ j : Fin 3, w ⟨9 + j.val, by omega⟩) * modeVelSq D ι v p := by
  have h9 : ∀ j : Fin 9, w ⟨j.val, by omega⟩ ≤ ⨆ j : Fin 9, w ⟨j.val, by omega⟩ :=
    fun j => le_ciSup (f := fun j : Fin 9 => w ⟨j.val, by omega⟩) (Set.finite_range _).bddAbove j
  have h3 : ∀ j : Fin 3, w ⟨9 + j.val, by omega⟩ ≤ ⨆ j : Fin 3, w ⟨9 + j.val, by omega⟩ :=
    fun j => le_ciSup (f := fun j : Fin 3 => w ⟨9 + j.val, by omega⟩) (Set.finite_range _).bddAbove j
  rw [← strain_bandProfile D ι v G p, ← vel_bandProfile D ι v G p]
  have e : ∑ j, w j * ‖bandProfile D ι v G p j‖ ^ 2
      = ∑ j : Fin 9, w ⟨j.val, by omega⟩ * ‖bandProfile D ι v G p ⟨j.val, by omega⟩‖ ^ 2
        + ∑ j : Fin 3, w ⟨9 + j.val, by omega⟩ * ‖bandProfile D ι v G p ⟨9 + j.val, by omega⟩‖ ^ 2 := by
    exact Fin.sum_univ_add (fun j : Fin (9 + 3) => w j * ‖bandProfile D ι v G p j‖ ^ 2)
  have e9 : cnormSq (gradOf (bandProfile D ι v G p)) = ∑ j : Fin 9, ‖bandProfile D ι v G p ⟨j.val, by omega⟩‖ ^ 2 := by
    unfold cnormSq gradOf
    refine Fintype.sum_equiv (finProdFinEquiv (m := 3) (n := 3)) _ _ (fun ab => ?_)
    congr 3
    simp only [finProdFinEquiv_apply_val]
    ring_nf
  have e3 : cnormSq (velOf (bandProfile D ι v G p)) = ∑ j : Fin 3, ‖bandProfile D ι v G p ⟨9 + j.val, by omega⟩‖ ^ 2 := by
    rfl
  rw [e, e9, e3, Finset.mul_sum, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (h9 j) (by positivity)))
    (Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right (h3 j) (by positivity)))

theorem modeSq_integrable (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (μ : Measure (ℝ × ℝ))
    (hm : ∀ j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) μ)
    (hI : Integrable (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) μ) (hpos : ∀ᵐ p ∂μ, 0 ≤ p.1) :
    Integrable (fun p => p.1 * modeCurlSq D ι G p) μ ∧ Integrable (fun p => p.1 * modeStrainSq D ι G p) μ ∧
      Integrable (fun p => p.1 * modeVelSq D ι v p) μ := by
  have hU : AEMeasurable (fun p => bandProfile D ι v G p) μ := profile_aemeasurable μ _ hm
  have c1 : Continuous (fun U : Fin 12 → ℂ => cnormSq (curlOfGrad (gradOf U))) := by
    unfold cnormSq curlOfGrad gradOf
    fun_prop
  have c2 : Continuous (fun U : Fin 12 → ℂ => cnormSq (gradOf U)) := by
    unfold cnormSq gradOf
    fun_prop
  have c3 : Continuous (fun U : Fin 12 → ℂ => cnormSq (velOf U)) := by
    unfold cnormSq velOf
    fun_prop
  have e1 : (fun p => modeCurlSq D ι G p) = fun p => cnormSq (curlOfGrad (gradOf (bandProfile D ι v G p))) :=
    funext fun p => (curl_bandProfile D ι v G p).symm
  have e2 : (fun p => modeStrainSq D ι G p) = fun p => cnormSq (gradOf (bandProfile D ι v G p)) :=
    funext fun p => (strain_bandProfile D ι v G p).symm
  have e3 : (fun p => modeVelSq D ι v p) = fun p => cnormSq (velOf (bandProfile D ι v G p)) :=
    funext fun p => (vel_bandProfile D ι v G p).symm
  have hsplit := fun p => profile_sq_split D ι v G p
  have hn2 : ∀ p, 0 ≤ modeStrainSq D ι G p := fun p => by
    rw [← strain_bandProfile D ι v G p]
    exact cnormSq_nonneg' _
  have hn3 : ∀ p, 0 ≤ modeVelSq D ι v p := fun p => by
    rw [← vel_bandProfile D ι v G p]
    exact cnormSq_nonneg' _
  have hn1 : ∀ p, 0 ≤ modeCurlSq D ι G p := fun p => by
    rw [← curl_bandProfile D ι v G p]
    exact cnormSq_nonneg' _
  have hc1 : ∀ p, modeCurlSq D ι G p ≤ 27 * modeStrainSq D ι G p := fun p => by
    rw [← curl_bandProfile D ι v G p, ← strain_bandProfile D ι v G p]
    exact curl_cnormSq_le _
  refine ⟨?_, ?_, ?_⟩
  · refine Integrable.mono' (hI.const_mul 27) ?_ ?_
    · rw [show (fun p => p.1 * modeCurlSq D ι G p) = fun p => p.1 * cnormSq (curlOfGrad (gradOf (bandProfile D ι v G p)))
        from funext fun p => by rw [curl_bandProfile]]
      exact (continuous_fst.aemeasurable.mul (c1.measurable.comp_aemeasurable hU)).aestronglyMeasurable
    · filter_upwards [hpos] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (hn1 p)), hsplit p]
      nlinarith [hc1 p, hn2 p, hn3 p]
  · refine Integrable.mono' hI ?_ ?_
    · rw [show (fun p => p.1 * modeStrainSq D ι G p) = fun p => p.1 * cnormSq (gradOf (bandProfile D ι v G p))
        from funext fun p => by rw [strain_bandProfile]]
      exact (continuous_fst.aemeasurable.mul (c2.measurable.comp_aemeasurable hU)).aestronglyMeasurable
    · filter_upwards [hpos] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (hn2 p)), hsplit p]
      nlinarith [hn2 p, hn3 p]
  · refine Integrable.mono' hI ?_ ?_
    · rw [show (fun p => p.1 * modeVelSq D ι v p) = fun p => p.1 * cnormSq (velOf (bandProfile D ι v G p))
        from funext fun p => by rw [vel_bandProfile]]
      exact (continuous_fst.aemeasurable.mul (c3.measurable.comp_aemeasurable hU)).aestronglyMeasurable
    · filter_upwards [hpos] with p hp
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hp (hn3 p)), hsplit p]
      nlinarith [hn2 p, hn3 p]

theorem longPartner_bandProfile {V : Type} (D : CellLayerData k C nE nM) (P : PotentialData V) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    longPartnerCharge P ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
      = longFactor P ι * (P.longStrain * modeCurlSq D ι G p
        + 3 / (2 * Real.sqrt 2) * P.longGrad * P.epsLength * modeStrainSq D ι G p
        + 3 / (2 * Real.sqrt 2) * P.longGrad / P.length * modeVelSq D ι v p) := by
  unfold longPartnerCharge
  rw [splitCharge_bandProfile]

theorem epsPartner_bandProfile {V : Type} (D : CellLayerData k C nE nM) (P : PotentialData V) (ι : ℤ × ℤ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    epsPartnerCharge P (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
      = P.epsStrain * modeCurlSq D ι G p
        + 3 / (2 * Real.sqrt 2) * P.epsGrad * P.epsLength * modeStrainSq D ι G p
        + 3 / (2 * Real.sqrt 2) * P.epsGrad / P.length * modeVelSq D ι v p := by
  unfold epsPartnerCharge
  rw [splitCharge_bandProfile]

theorem modeSq_nonneg (D : CellLayerData k C nE nM) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    0 ≤ modeCurlSq D ι G p ∧ 0 ≤ modeStrainSq D ι G p ∧ 0 ≤ modeVelSq D ι v p := by
  refine ⟨?_, ?_, ?_⟩
  · rw [← curl_bandProfile D ι v G p]
    exact cnormSq_nonneg' _
  · rw [← strain_bandProfile D ι v G p]
    exact cnormSq_nonneg' _
  · rw [← vel_bandProfile D ι v G p]
    exact cnormSq_nonneg' _

theorem bandPointwise (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (hι : ι ∈ D.mesh.band K) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ)
    (hp : p ∈ (D.mesh.box K).rect) :
    p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2
      + p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
      + p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
      + p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p)
      + p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p)
      + p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p)
      ≤ extraChargeDensity D R K ι v G p * p.1 := by
  have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
  obtain ⟨h1, h2, h3⟩ := hP.band_charges K ι hι p hp
  have hw := mul_le_mul_of_nonneg_left (bandWeight_le D ι v G p ((A.blocks K).bandWeight ι)) hp1
  rw [epsPartner_bandProfile, longPartner_bandProfile, highPartner_bandProfile]
  obtain ⟨hn1, hn2, hn3⟩ := modeSq_nonneg D ι v G p
  have k1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hn1 hp1)
  have k2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hn2 hp1)
  have k3 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hn3 hp1)
  unfold extraChargeDensity
  linear_combination k1 + k2 + k3 + hw

theorem mem_deactPartners_iff (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (P : PotentialData (CellVars D R K)) (ι : ℤ × ℤ) (hr : ι ∉ D.mesh.resolved K) (hb : ι ∉ D.mesh.band K) :
    ι ∈ deactPartners D R K P ↔ ∃ ι₀ ∈ D.mesh.resolved K, ι₀ - ι ∈ P.harmonicLabels := by
  unfold deactPartners
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, -⟩
    rw [Finset.mem_product] at hx
    exact ⟨x.1, hx.1, by rw [sub_sub_cancel]; exact hx.2⟩
  · rintro ⟨a, ha, hab⟩
    exact ⟨⟨(a, a - ι), Finset.mem_product.2 ⟨ha, hab⟩, sub_sub_cancel a ι⟩, hr, hb⟩

theorem deactivatedPointwise (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (ι : ℤ × ℤ)
    (hr : ι ∉ D.mesh.resolved K) (hb : ι ∉ D.mesh.band K) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    (if ι ∈ (A.blocks K).leakModes then
        p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p + (A.blocks K).leakVel ι * modeVelSq D ι v p) else 0)
      + (if ι ∈ (A.blocks K).leakModes then p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0)
      + (∑ i, (if ι ∈ (P.potential K).groupPartners i then
          p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
            / (P.potential K).groupBalance i)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0)
      + p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p)
      + creditVelDemand D R K ι p * modeVelSq D ι v p * p.1
      ≤ extraChargeDensity D R K ι v G p * p.1 := by
  have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
  obtain ⟨hn1, hn2, hn3⟩ := modeSq_nonneg D ι v G p
  obtain ⟨hes, heg⟩ := hP.eps_nonneg K
  obtain ⟨hyc, hys, hyv⟩ := hP.young_pos K
  have hℓ := hP.length_pos K
  have hL := hP.eps_length_pos K
  obtain ⟨hlS, hlG, hβ⟩ := hP.long_pos K
  have hlf := longFactor_pos (P.potential K) hβ ι
  obtain ⟨hhS, hhG⟩ := high_nonneg D R A P hP K
  have hg : ∀ i, (if ι ∈ (P.potential K).groupPartners i then
        p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
          / (P.potential K).groupBalance i
      = p.1 * (if ι ∈ (P.potential K).groupPartners i then
        (P.potential K).groupStrain i / (P.potential K).groupBalance i * modeCurlSq D ι G p
          + (P.potential K).groupKappa i / 2 * (P.potential K).length * (P.potential K).groupGrad i
            / (P.potential K).groupBalance i * modeStrainSq D ι G p
          + (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
            / ((P.potential K).length * (P.potential K).groupBalance i) * modeVelSq D ι v p else 0) := by
    intro i
    split_ifs
    · unfold groupCharge
      rw [splitCharge_bandProfile]
      ring
    · ring
  have e : (∑ i, if ι ∈ (P.potential K).groupPartners i then
        (P.potential K).groupStrain i / (P.potential K).groupBalance i * modeCurlSq D ι G p
          + (P.potential K).groupKappa i / 2 * (P.potential K).length * (P.potential K).groupGrad i
            / (P.potential K).groupBalance i * modeStrainSq D ι G p
          + (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
            / ((P.potential K).length * (P.potential K).groupBalance i) * modeVelSq D ι v p else 0)
      = (∑ i, if ι ∈ (P.potential K).groupPartners i then
          (P.potential K).groupStrain i / (P.potential K).groupBalance i else 0) * modeCurlSq D ι G p
        + (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).length
          * (P.potential K).groupGrad i / (P.potential K).groupBalance i else 0) * modeStrainSq D ι G p
        + (∑ i, if ι ∈ (P.potential K).groupPartners i then (P.potential K).groupKappa i / 2 * (P.potential K).groupGrad i
          / ((P.potential K).length * (P.potential K).groupBalance i) else 0) * modeVelSq D ι v p := by
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun i _ => hg i), ← Finset.mul_sum, e, epsPartner_bandProfile, longPartner_bandProfile,
    highPartner_bandProfile]
  obtain ⟨h1, h2, h3⟩ := hP.charges_cover K ι hr hb p hp
  simp only [← mem_deactPartners_iff D R K (P.potential K) ι hr hb] at h1 h2 h3
  have k1 := mul_le_mul_of_nonneg_right h1 (mul_nonneg hn1 hp1)
  have k2 := mul_le_mul_of_nonneg_right h2 (mul_nonneg hn2 hp1)
  have k3 := mul_le_mul_of_nonneg_right h3 (mul_nonneg hn3 hp1)
  have n1 : 0 ≤ ((P.potential K).epsStrain + longFactor (P.potential K) ι * (P.potential K).longStrain
      + (P.potential K).highStrain / (P.potential K).youngCurl) * (modeCurlSq D ι G p * p.1) := by positivity
  have n2 : 0 ≤ 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          * (P.potential K).epsLength + (P.potential K).highGrad / (P.potential K).youngVel)
      * (modeStrainSq D ι G p * p.1) := by positivity
  have n3 : 0 ≤ 3 / (2 * Real.sqrt 2) * (((P.potential K).epsGrad + longFactor (P.potential K) ι * (P.potential K).longGrad)
          / (P.potential K).length + (P.potential K).highGrad / (P.potential K).youngStrain)
      * (modeVelSq D ι v p * p.1) := by positivity
  unfold extraChargeDensity
  split_ifs at k1 k2 k3 ⊢ <;> linear_combination k1 + k2 + k3

theorem allPointwise (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (ι : ℤ × ℤ) (hr : ι ∉ D.mesh.resolved K) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) :
    (if ι ∈ D.mesh.band K then p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2 else 0)
      + (if ι ∈ (A.blocks K).leakModes then
        p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p + (A.blocks K).leakVel ι * modeVelSq D ι v p) else 0)
      + (if ι ∈ (A.blocks K).leakModes then p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0)
      + (∑ i, (if ι ∈ (P.potential K).groupPartners i then
          p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
            / (P.potential K).groupBalance i)
      + (if ι ∈ D.mesh.band K then
          p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ D.mesh.band K then
          p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then
          p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0)
      + (if ι ∈ D.mesh.band K then p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0)
      + (if ι ∈ D.mesh.band K then
          p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p
            + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p) else 0)
      + p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p)
      + creditVelDemand D R K ι p * modeVelSq D ι v p * p.1
      ≤ extraChargeDensity D R K ι v G p * p.1 := by
  by_cases hb : ι ∈ D.mesh.band K
  · have hl : ι ∉ (A.blocks K).leakModes := Finset.disjoint_right.1 (hP.leak_not_band K) hb
    have hpi : ∀ i, ι ∉ (P.potential K).groupPartners i := fun i =>
      Finset.disjoint_right.1 (hP.partners_not_band K i) hb
    have hd : ι ∉ deactPartners D R K (P.potential K) := fun h => (Finset.mem_filter.1 h).2.2 hb
    have hcr : creditVelDemand D R K ι p = 0 := by
      unfold creditVelDemand
      refine Finset.sum_eq_zero (fun j _ => if_neg ?_)
      rintro ⟨h1, _⟩
      exact (hP.credit_deactivated j K ι h1).2 hb
    have key := bandPointwise D R A P hP K ι hb v G p hp
    simp only [hb, hl, hpi, hd, if_true, if_false, zero_div, Finset.sum_const_zero, add_zero, hcr, zero_mul]
    linarith
  · have key := deactivatedPointwise D R A P hP K ι hr hb v G p hp
    simp only [hb, if_false, add_zero, zero_add]
    linarith

theorem ite_setIntegral (c : Prop) [Decidable c] (s : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) :
    (if c then ∫ p in s, f p else 0) = ∫ p in s, (if c then f p else 0) := by
  split_ifs <;> simp

theorem integrable_ite {μ : Measure (ℝ × ℝ)} (c : Prop) [Decidable c] {f : ℝ × ℝ → ℝ} (hf : Integrable f μ) :
    Integrable (fun p => if c then f p else 0) μ := by
  split_ifs
  · exact hf
  · exact integrable_zero _ _ _

theorem labelHarmonic_inj {m : ℕ} (hm : 1 ≤ m) {ι ι' : ℤ × ℤ}
    (h : labelHarmonic m ι = labelHarmonic m ι') : ι = ι' := by
  unfold labelHarmonic labelTime labelAzimuth at h
  obtain ⟨h1, h2⟩ := Prod.mk.inj h
  have hm0 : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have ha : ι.1 = ι'.1 := mul_right_cancel₀ hm0 h2
  have hb : ι.2 = ι'.2 := by omega
  exact Prod.ext ha hb

theorem region_measurable (Q : Bridge.CreditPatch) : MeasurableSet Q.region := by
  unfold Bridge.CreditPatch.region Bridge.patch
  exact measurableSet_Icc.prod measurableSet_Icc

theorem labelHarmonic_neg (m : ℕ) (ι : ℤ × ℤ) : labelHarmonic m (-ι) = -labelHarmonic m ι := by
  refine Prod.ext ?_ ?_ <;> simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg] <;> ring

theorem labelHarmonic_eq_or_neg {m : ℕ} (hm : 1 ≤ m) {ι c F : ℤ × ℤ} (hc : labelHarmonic m c = F) :
    (labelHarmonic m ι = F ∨ labelHarmonic m ι = -F) ↔ (ι = c ∨ ι = -c) := by
  constructor
  · rintro (h | h)
    · exact Or.inl (labelHarmonic_inj hm (h.trans hc.symm))
    · exact Or.inr (labelHarmonic_inj hm (by rw [h, labelHarmonic_neg, hc]))
  · rintro (rfl | rfl)
    · exact Or.inl hc
    · exact Or.inr (by rw [labelHarmonic_neg, hc])

theorem creditDemand_mul (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (ι : ℤ × ℤ) (p : ℝ × ℝ) (h : ℝ) :
    creditVelDemand D R K ι p * h = ∑ j, if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) then
      Set.indicator (R.creditPatch j).region (fun _ => (R.creditPatch j).charge p * h) p else 0 := by
  unfold creditVelDemand
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h1 : (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) <;>
    by_cases h2 : p ∈ (R.creditPatch j).region <;> simp [h1, h2, Set.indicator]

theorem creditTerm_integrable (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (ι : ℤ × ℤ) (j : Fin R.creditCount) (hv : Bridge.IsCreditPatch (R.creditPatch j))
    (hm : Integrable (fun p => modeVelSq D ι v p * p.1) (volume.restrict (D.mesh.box K).rect)) :
    Integrable (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1))
      (volume.restrict (D.mesh.box K).rect) := by
  refine hm.bdd_mul (c := (R.creditPatch j).chargeUpper) hv.charge_measurable.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun p => ?_))
  obtain ⟨h1, h2⟩ := hv.charge_between p
  rw [Real.norm_eq_abs, abs_of_nonneg (le_trans hv.charge_lower_pos.le h1)]
  exact h2

theorem creditIntegrable (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (hpatch : ∀ j, Bridge.IsCreditPatch (R.creditPatch j)) (K : Fin D.mesh.count) (v : ℝ → Space → Space)
    (ι : ℤ × ℤ) (hm : Integrable (fun p => modeVelSq D ι v p * p.1) (volume.restrict (D.mesh.box K).rect)) :
    Integrable (fun p => creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
      (volume.restrict (D.mesh.box K).rect) := by
  have e : (fun p => creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
      = fun p => ∑ j, if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) then
        Set.indicator (R.creditPatch j).region
          (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1)) p else 0 := by
    funext p
    rw [mul_assoc, creditDemand_mul]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · simp only [Set.indicator]
    · rfl
  rw [e]
  refine integrable_finsetSum _ (fun j _ => ?_)
  split_ifs
  · exact (creditTerm_integrable D R K v ι j (hpatch j) hm).indicator (region_measurable _)
  · exact integrable_zero _ _ _

theorem creditAmount_eq (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (hm : 1 ≤ D.azimuthOrder)
    (K : Fin D.mesh.count) (v : ℝ → Space → Space) (T : Finset (ℤ × ℤ)) (c : Fin R.creditCount → ℤ × ℤ)
    (hc : ∀ j, labelHarmonic D.azimuthOrder (c j) = flipLabel (R.creditPatch j).label)
    (hne : ∀ j, (R.creditPatch j).label ≠ 0) (hT : ∀ j, c j ∈ T) (hT' : ∀ j, -c j ∈ T)
    (hI : ∀ ι j, Integrable (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1))
      (volume.restrict (D.mesh.box K).rect)) :
    creditAmount D R K v
      = ∑ ι ∈ T, ∫ p in (D.mesh.box K).rect, creditVelDemand D R K ι p * modeVelSq D ι v p * p.1 := by
  have hJ : ∀ ι j, Integrable (fun p => if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) then
      Set.indicator (R.creditPatch j).region
        (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1)) p else 0)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ι j
    split_ifs
    · exact (hI ι j).indicator (region_measurable _)
    · exact integrable_zero _ _ _
  have e1 : ∀ ι, (∫ p in (D.mesh.box K).rect, creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
      = ∑ j, if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) then ∫ p in (D.mesh.box K).rect,
        Set.indicator (R.creditPatch j).region
          (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1)) p else 0 := by
    intro ι
    have hf : (fun p => creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
        = fun p => ∑ j, if (labelHarmonic D.azimuthOrder ι = flipLabel (R.creditPatch j).label ∨
        labelHarmonic D.azimuthOrder ι = -flipLabel (R.creditPatch j).label) then
          Set.indicator (R.creditPatch j).region
            (fun p => (R.creditPatch j).charge p * (modeVelSq D ι v p * p.1)) p else 0 := by
      funext p
      rw [mul_assoc, creditDemand_mul]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      split_ifs
      · simp only [Set.indicator]
      · rfl
    rw [hf, integral_finsetSum _ (fun j _ => hJ ι j)]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    split_ifs
    · rfl
    · simp
  rw [Finset.sum_congr rfl (fun ι _ => e1 ι), Finset.sum_comm]
  unfold creditAmount creditShare
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hneg : labelHarmonic D.azimuthOrder (-c j) = -flipLabel (R.creditPatch j).label := by
    rw [labelHarmonic_neg, hc j]
  have hcne : c j ≠ -c j := by
    intro h
    apply hne j
    have h0 : c j = 0 := by
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      simp only [Prod.fst_neg, Prod.snd_neg] at h1 h2
      exact Prod.ext (by simp only [Prod.fst_zero]; omega) (by simp only [Prod.snd_zero]; omega)
    have hF := hc j
    rw [h0] at hF
    have hz : flipLabel (R.creditPatch j).label = 0 := by
      rw [← hF]
      simp [labelHarmonic, labelTime, labelAzimuth]
    have z1 := congrArg Prod.fst hz
    have z2 := congrArg Prod.snd hz
    simp only [flipLabel, Prod.fst_zero, Prod.snd_zero, neg_eq_zero] at z1 z2
    exact Prod.ext z1 z2
  have ha : ∀ p, Set.indicator (R.creditPatch j).region
        (fun p => (R.creditPatch j).charge p * (modeVelSq D (c j) v p * p.1)) p
      + Set.indicator (R.creditPatch j).region
        (fun p => (R.creditPatch j).charge p * (modeVelSq D (-c j) v p * p.1)) p
      = Set.indicator (R.creditPatch j).region
        (fun p => (R.creditPatch j).charge p * (cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p))
          + cnormSq (modeVel (-flipLabel (R.creditPatch j).label) v 0 (planePoint p))) * p.1) p := by
    intro p
    have hv : modeVelSq D (c j) v p = cnormSq (modeVel (flipLabel (R.creditPatch j).label) v 0 (planePoint p)) := by
      rw [← hc j]
      rfl
    have hv' : modeVelSq D (-c j) v p
        = cnormSq (modeVel (-flipLabel (R.creditPatch j).label) v 0 (planePoint p)) := by
      rw [← hneg]
      rfl
    by_cases hp : p ∈ (R.creditPatch j).region
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp, hv, hv']
      ring
    · simp [hp]
  rw [Finset.sum_eq_add (c j) (-c j) hcne, if_pos (Or.inl (hc j)), if_pos (Or.inr hneg),
    ← integral_add ((hI _ j).indicator (region_measurable _)) ((hI _ j).indicator (region_measurable _)),
    Set.inter_comm, ← setIntegral_indicator (region_measurable _)]
  · exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => (ha p).symm))
  · intro ι _ hι
    exact if_neg (fun h => ((labelHarmonic_eq_or_neg hm (hc j)).1 h).elim hι.1 hι.2)
  · intro h
    exact absurd (hT j) h
  · intro h
    exact absurd (hT' j) h

theorem sum_eq_sum_ite {β : Type*} [AddCommMonoid β] (S T : Finset (ℤ × ℤ)) (h : S ⊆ T) (f : ℤ × ℤ → β) :
    ∑ ι ∈ S, f ι = ∑ ι ∈ T, if ι ∈ S then f ι else 0 := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.2 h]

theorem perModeCharge (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (hr : ι ∉ D.mesh.resolved K)
    (hi1 : Integrable (fun p => p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2)
      (volume.restrict (D.mesh.box K).rect))
    (hi2 : Integrable (fun p => p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)))
      (volume.restrict (D.mesh.box K).rect))
    (hi5 : Integrable (fun p => p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)))
      (volume.restrict (D.mesh.box K).rect))
    (hi3 : Integrable (fun p => p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p))
      (volume.restrict (D.mesh.box K).rect))
    (hi4 : Integrable (fun p => p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p
      + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p)) (volume.restrict (D.mesh.box K).rect))
    (hl1 : Integrable (fun p => p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p
      + (A.blocks K).leakVel ι * modeVelSq D ι v p)) (volume.restrict (D.mesh.box K).rect))
    (hl2 : Integrable (fun p => p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p))
      (volume.restrict (D.mesh.box K).rect))
    (hgi : ∀ i, Integrable (fun p => p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p))
      (gradOf (bandProfile D ι v G p))) (volume.restrict (D.mesh.box K).rect))
    (hsl : Integrable (fun p => p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p))
      (volume.restrict (D.mesh.box K).rect))
    (hci : Integrable (fun p => creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
      (volume.restrict (D.mesh.box K).rect))
    (hei : Integrable (fun p => extraChargeDensity D R K ι v G p * p.1) (volume.restrict (D.mesh.box K).rect)) :
    (if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2 else 0)
      + (if ι ∈ (A.blocks K).leakModes then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p + (A.blocks K).leakVel ι * modeVelSq D ι v p) else 0)
      + (if ι ∈ (A.blocks K).leakModes then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0)
      + (∑ i, (if ι ∈ (P.potential K).groupPartners i then ∫ p in (D.mesh.box K).rect,
          p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
          else 0) / (P.potential K).groupBalance i)
      + (if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
      + (if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0)
      + (if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0)
      + (if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p
          + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p) else 0)
      + (∫ p in (D.mesh.box K).rect, creditVelDemand D R K ι p * modeVelSq D ι v p * p.1)
      + (∫ p in (D.mesh.box K).rect, p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p))
      ≤ ∫ p in (D.mesh.box K).rect, extraChargeDensity D R K ι v G p * p.1 := by
  have hms : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  simp only [ite_setIntegral]
  have hYi : ∀ i, Integrable (fun p => (if ι ∈ (P.potential K).groupPartners i then
      p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
        / (P.potential K).groupBalance i) (volume.restrict (D.mesh.box K).rect) :=
    fun i => (integrable_ite _ (hgi i)).div_const _
  have eY : (∑ i, (∫ p in (D.mesh.box K).rect, if ι ∈ (P.potential K).groupPartners i then
        p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
          / (P.potential K).groupBalance i)
      = ∫ p in (D.mesh.box K).rect, ∑ i, (if ι ∈ (P.potential K).groupPartners i then
        p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0)
          / (P.potential K).groupBalance i := by
    rw [integral_finsetSum _ (fun i _ => hYi i)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_div]
  rw [eY]
  have j1 := integrable_ite (ι ∈ D.mesh.band K) hi1
  have j2 := integrable_ite (ι ∈ (A.blocks K).leakModes) hl1
  have j3 := integrable_ite (ι ∈ (A.blocks K).leakModes) hl2
  have j4 := integrable_finsetSum Finset.univ (fun i _ => hYi i)
  have j5 := integrable_ite (ι ∈ D.mesh.band K) hi2
  have j6 := integrable_ite (ι ∈ D.mesh.band K) hi5
  have j7 := integrable_ite (ι ∈ deactPartners D R K (P.potential K)) hi2
  have j8 := integrable_ite (ι ∈ deactPartners D R K (P.potential K)) hi5
  have j9 := integrable_ite (ι ∈ deactPartners D R K (P.potential K)) hi3
  have j10 := integrable_ite (ι ∈ D.mesh.band K) hi3
  have j11 := integrable_ite (ι ∈ D.mesh.band K) hi4
  beta_reduce at j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11
  have i2 := j1.add j2
  have i3 := i2.add j3
  have i4 := i3.add j4
  have i5 := i4.add j5
  have i6 := i5.add j6
  have i7 := i6.add j7
  have i8 := i7.add j8
  have i9 := i8.add j9
  have i10 := i9.add j10
  have i11 := i10.add j11
  have i12 := i11.add hci
  have key := setIntegral_mono_on (i12.add hsl) hei hms
    (fun p hp => by have := allPointwise D R A P hP K ι hr v G p hp; simp only [Pi.add_apply]; linarith)
  rw [integral_add' i12 hsl, integral_add' i11 hci, integral_add' i10 j11, integral_add' i9 j10, integral_add' i8 j9, integral_add' i7 j8,
    integral_add' i6 j7, integral_add' i5 j6, integral_add' i4 j5, integral_add' i3 j4, integral_add' i2 j3,
    integral_add' j1 j2] at key
  exact key

end Internal

end Assembly

end CertCell

end Breakdown

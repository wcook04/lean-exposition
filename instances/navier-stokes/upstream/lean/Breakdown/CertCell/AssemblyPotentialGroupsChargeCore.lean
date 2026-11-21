import Breakdown.CertCell.AssemblyPotentialGroupsChargePartsCore

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus ChargeAux

variable {k : ℕ} {C : Type} {nE nM : ℕ} {V : Type}

theorem weighted_abs_le (w a : Fin 12 → ℝ) (ha : ∀ j, 0 ≤ a j) :
    |∑ j, w j * a j| ≤ (∑ j, |w j|) * ∑ j, a j := by
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum (fun j _ => ?_)
  rw [abs_mul, abs_of_nonneg (ha j)]
  exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun i _ => ha i) (Finset.mem_univ j)) (abs_nonneg _)

theorem chargeStage_of (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (hR : AssemblyRegular D R) (hT : TrueFieldRegular D) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) :
    ChargeStage D R A P := by
  choose cl hcl using hP.credit_lattice
  intro K q v G H g κ F Pg ht
  have hreg := hT.1 K q v G H g κ F Pg ht
  have hms : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  have hpos : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), 0 ≤ p.1 :=
    ae_restrict_of_forall_mem hms (rect_fst_nonneg D hP.mesh_valid K)
  have hmode := fun ι => modeSq_integrable D ι v G _ (hreg.1 ι).1 (hreg.1 ι).2 hpos
  obtain ⟨c, hc⟩ := hR.charges.bounded K
  have hextra : ∀ ι, Integrable (fun p => extraChargeDensity D R K ι v G p * p.1)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ι
    obtain ⟨m1, m2, m3⟩ := hmode ι
    obtain ⟨a1, a2, a3, -⟩ := hR.charges.measurable K ι
    have e : (fun p => extraChargeDensity D R K ι v G p * p.1)
        = fun p => (R.entryCharges K ι).curlCharge p * (p.1 * modeCurlSq D ι G p)
          + (R.entryCharges K ι).gradCharge p * (p.1 * modeStrainSq D ι G p)
          + (R.entryCharges K ι).velCharge p * (p.1 * modeVelSq D ι v p) := by
      funext p
      unfold extraChargeDensity
      ring
    rw [e]
    refine ((m1.bdd_mul (c := c) a1 ?_).add (m2.bdd_mul (c := c) a2 ?_)).add (m3.bdd_mul (c := c) a3 ?_)
    · exact ae_restrict_of_forall_mem hms (fun p hp => by rw [Real.norm_eq_abs]; exact (hc ι p hp).1)
    · exact ae_restrict_of_forall_mem hms (fun p hp => by rw [Real.norm_eq_abs]; exact (hc ι p hp).2.1)
    · exact ae_restrict_of_forall_mem hms (fun p hp => by rw [Real.norm_eq_abs]; exact (hc ι p hp).2.2.1)
  set T : Finset (ℤ × ℤ) := D.mesh.band K ∪ (A.blocks K).leakModes
    ∪ Finset.univ.biUnion (fun i => (P.potential K).groupPartners i)
    ∪ (Finset.univ.image cl ∪ Finset.univ.image (fun j => -cl j))
    ∪ deactPartners D R K (P.potential K) ∪ deactSlackLabels D R K with hTdef
  have hbT : D.mesh.band K ⊆ T := fun ι h => by simp [hTdef, h]
  have hlT : (A.blocks K).leakModes ⊆ T := fun ι h => by simp [hTdef, h]
  have hpT : ∀ i, (P.potential K).groupPartners i ⊆ T := fun i ι h => by
    simp only [hTdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact Or.inl (Or.inl (Or.inl (Or.inr ⟨i, h⟩)))
  have hcT : ∀ j, cl j ∈ T := fun j => by simp [hTdef]
  have hcT' : ∀ j, -cl j ∈ T := fun j => by simp [hTdef]
  have hdT : deactPartners D R K (P.potential K) ⊆ T := fun ι h => by simp [hTdef, h]
  have hsT : deactSlackLabels D R K ⊆ T := fun ι h => by simp [hTdef, h]
  have hTres : ∀ ι ∈ T, ι ∉ D.mesh.resolved K := by
    intro ι hι
    simp only [hTdef, Finset.mem_union, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_image] at hι
    rcases hι with ((((hb | hl) | ⟨i, hi⟩) | (⟨j, rfl⟩ | ⟨j, rfl⟩)) | hd) | hs
    · exact fun h => Finset.disjoint_left.1 (hP.mesh_valid.band_apart K) h hb
    · exact hP.leak_unresolved K ι hl
    · exact fun h => Finset.disjoint_left.1 (hP.partners_unresolved K i) hi h
    · exact (hP.credit_deactivated j K (cl j) (Or.inl (hcl j))).1
    · exact (hP.credit_deactivated j K (-cl j) (Or.inr (by rw [labelHarmonic_neg, hcl j]))).1
    · exact (Finset.mem_filter.1 hd).2.1
    · exact (Finset.mem_filter.1 hs).2.1
  have eBQ : bandQuad D K (A.blocks K).bandWeight (fun ι => bandProfile D ι v G)
      = ∑ ι ∈ T, if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * ∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2 else 0 := by
    unfold bandQuad
    exact sum_eq_sum_ite _ T hbT _
  have eRL : rowLeakAmount D K (A.blocks K) v G
      = ∑ ι ∈ T, if ι ∈ (A.blocks K).leakModes then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p + (A.blocks K).leakVel ι * modeVelSq D ι v p) else 0 := by
    unfold rowLeakAmount
    exact sum_eq_sum_ite _ T hlT _
  have ePL : pairingLeakAmount D K (A.blocks K) G
      = ∑ ι ∈ T, if ι ∈ (A.blocks K).leakModes then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p) else 0 := by
    unfold pairingLeakAmount
    exact sum_eq_sum_ite _ T hlT _
  have eGP : groupPartnerAmount D R K (P.potential K) (trueProfiles D v G)
      = ∑ ι ∈ T, ∑ i, (if ι ∈ (P.potential K).groupPartners i then ∫ p in (D.mesh.box K).rect,
          p.1 * groupCharge (P.potential K) i (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))
          else 0) / (P.potential K).groupBalance i := by
    unfold groupPartnerAmount formAmount
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.sum_div, sum_eq_sum_ite _ T (hpT i)]
    rfl
  have eEB : formAmount D K (D.mesh.band K) (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * epsPartnerCharge (P.potential K)
          (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0 := by
    unfold formAmount
    exact sum_eq_sum_ite _ T hbT _
  have eLB : labelFormAmount D K (D.mesh.band K) (longPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0 := by
    unfold labelFormAmount
    exact sum_eq_sum_ite _ T hbT _
  have eED : formAmount D K (deactPartners D R K (P.potential K)) (epsPartnerCharge (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * epsPartnerCharge (P.potential K) (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0 := by
    unfold formAmount
    exact sum_eq_sum_ite _ T hdT _
  have eLD : labelFormAmount D K (deactPartners D R K (P.potential K)) (longPartnerCharge (P.potential K))
        (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)) else 0 := by
    unfold labelFormAmount
    exact sum_eq_sum_ite _ T hdT _
  have eHD : highPartnerAmount D K (P.potential K) (deactPartners D R K (P.potential K)) (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ deactPartners D R K (P.potential K) then ∫ p in (D.mesh.box K).rect,
        p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0 := by
    unfold highPartnerAmount
    exact sum_eq_sum_ite _ T hdT _
  have eHB : highPartnerAmount D K (P.potential K) (D.mesh.band K) (trueProfiles D v G)
      = ∑ ι ∈ T, if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p) else 0 := by
    unfold highPartnerAmount
    exact sum_eq_sum_ite _ T hbT _
  have eBA : bandAllowance D K (A.blocks K).bandCurlAllowance (A.blocks K).bandVelAllowance v G
      = ∑ ι ∈ T, if ι ∈ D.mesh.band K then ∫ p in (D.mesh.box K).rect,
        p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p
          + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p) else 0 := by
    unfold bandAllowance
    exact sum_eq_sum_ite _ T hbT _
  have hm3' : ∀ ι, Integrable (fun p => modeVelSq D ι v p * p.1) (volume.restrict (D.mesh.box K).rect) :=
    fun ι => by
      have := (hmode ι).2.2
      simpa only [mul_comm] using this
  have eCR : creditAmount D R K v
      = ∑ ι ∈ T, ∫ p in (D.mesh.box K).rect, creditVelDemand D R K ι p * modeVelSq D ι v p * p.1 :=
    creditAmount_eq D R hP.azimuth_pos K v T cl hcl hP.credit_label_ne hcT hcT'
      (fun ι j => creditTerm_integrable D R K v ι j (hP.credit_patches j) (hm3' ι))
  have eSL : pairSlackAmount D R K (D.mesh.band K) G + pairSlackAmount D R K (deactSlackLabels D R K) G
      = ∑ ι ∈ T, ∫ p in (D.mesh.box K).rect,
        p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p) := by
    unfold pairSlackAmount pairStrainSlack
    rw [sum_eq_sum_ite _ T (fun ι h => hbT (Finset.mem_inter.1 h).1),
      sum_eq_sum_ite _ T (fun ι h => hsT (Finset.mem_inter.1 h).1), ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun ι hι => ?_)
    have hr := hTres ι hι
    have e : (∫ p in (D.mesh.box K).rect,
        p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p))
        = (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0)
          * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 := by
      rw [← integral_const_mul]
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only [modeStrainSq]
      ring
    rw [e]
    by_cases hs : ι ∈ R.pairSlackLabels K
    · by_cases hb : ι ∈ D.mesh.band K
      · have hd : ι ∉ deactSlackLabels D R K := fun h => (Finset.mem_filter.1 h).2.2 hb
        simp only [Finset.mem_inter, hs, hb, hd, and_true, if_true, if_false, add_zero]
      · have hd : ι ∈ deactSlackLabels D R K := Finset.mem_filter.2 ⟨hs, hr, hb⟩
        simp only [Finset.mem_inter, hs, hb, hd, and_true, if_true, if_false, zero_add]
    · simp only [Finset.mem_inter, hs, and_false, if_false, add_zero, zero_mul]
  rw [add_assoc _ (pairSlackAmount D R K (D.mesh.band K) G), eSL]
  rw [eBQ, eRL, ePL, eGP, eEB, eLB, eED, eLD, eHD, eHB, eBA, eCR, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  obtain ⟨hes, heg⟩ := hP.eps_nonneg K
  obtain ⟨hyc, hys, hyv⟩ := hP.young_pos K
  unfold chargeSurplus
  refine le_trans (Finset.sum_le_sum (fun ι hι => ?_)) (Summable.sum_le_tsum T (fun ι hι => ?_) ?_)
  · rw [if_neg (hTres ι hι)]
    obtain ⟨m1, m2, m3⟩ := hmode ι
    have hsl : Integrable (fun p => p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0)
        * modeStrainSq D ι G p)) (volume.restrict (D.mesh.box K).rect) := by
      have e : (fun p => p.1 * ((if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * modeStrainSq D ι G p))
          = fun p => (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) * (p.1 * modeStrainSq D ι G p) := by
        funext p
        ring
      rw [e]
      exact m2.const_mul _
    refine perModeCharge D R A P hP K v G ι (hTres ι hι) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsl
      (creditIntegrable D R hP.credit_patches K v ι (hm3' ι)) (hextra ι)
    · refine Integrable.mono' ((hreg.1 ι).2.const_mul (∑ j, |(A.blocks K).bandWeight ι j|)) ?_ ?_
      · have hc1 : Continuous (fun U : Fin 12 → ℂ => ∑ j, (A.blocks K).bandWeight ι j * ‖U j‖ ^ 2) := by fun_prop
        exact (continuous_fst.aemeasurable.mul (hc1.measurable.comp_aemeasurable
          (profile_aemeasurable _ _ (hreg.1 ι).1))).aestronglyMeasurable
      · filter_upwards [hpos] with p hp
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hp]
        have := weighted_abs_le ((A.blocks K).bandWeight ι) (fun j => ‖bandProfile D ι v G p j‖ ^ 2)
          (fun j => by positivity)
        calc p.1 * |∑ j, (A.blocks K).bandWeight ι j * ‖bandProfile D ι v G p j‖ ^ 2|
            ≤ p.1 * ((∑ j, |(A.blocks K).bandWeight ι j|) * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) :=
              mul_le_mul_of_nonneg_left this hp
          _ = _ := by ring
    · have hℓ := hP.length_pos K
      have hL := hP.eps_length_pos K
      unfold epsPartnerCharge
      exact chargeY_integrable _ (trueProfiles D v G ι) _ _ _ hes (by positivity) (by positivity) (hreg.1 ι).1
        (hreg.1 ι).2 hpos
    · have hℓ := hP.length_pos K
      have hL := hP.eps_length_pos K
      obtain ⟨hlS, hlG, -⟩ := hP.long_pos K
      have e : (fun p => p.1 * longPartnerCharge (P.potential K) ι (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p)))
          = fun p => longFactor (P.potential K) ι * (p.1 * splitCharge (P.potential K).longStrain
            (3 / (2 * Real.sqrt 2) * (P.potential K).longGrad * (P.potential K).epsLength)
            (3 / (2 * Real.sqrt 2) * (P.potential K).longGrad / (P.potential K).length)
            (velOf (bandProfile D ι v G p)) (gradOf (bandProfile D ι v G p))) := by
        funext p
        unfold longPartnerCharge
        ring
      rw [e]
      exact (chargeY_integrable _ (trueProfiles D v G ι) _ _ _ hlS (by positivity) (by positivity) (hreg.1 ι).1
        (hreg.1 ι).2 hpos).const_mul _
    · have e : (fun p => p.1 * highPartnerCharge (P.potential K) (bandProfile D ι v G p))
          = fun p => (P.potential K).highStrain / (P.potential K).youngCurl * (p.1 * modeCurlSq D ι G p)
            + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain * (p.1 * modeVelSq D ι v p)
            + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel
              * (p.1 * modeStrainSq D ι G p) := by
        funext p
        rw [highPartner_bandProfile]
        ring
      rw [e]
      exact ((m1.const_mul _).add (m3.const_mul _)).add (m2.const_mul _)
    · have e : (fun p => p.1 * ((A.blocks K).bandCurlAllowance ι * modeCurlSq D ι G p
          + (A.blocks K).bandVelAllowance ι * modeVelSq D ι v p))
          = fun p => (A.blocks K).bandCurlAllowance ι * (p.1 * modeCurlSq D ι G p)
            + (A.blocks K).bandVelAllowance ι * (p.1 * modeVelSq D ι v p) := by
        funext p
        ring
      rw [e]
      exact (m1.const_mul _).add (m3.const_mul _)
    · have e : (fun p => p.1 * ((A.blocks K).leakCurl ι * modeCurlSq D ι G p
          + (A.blocks K).leakVel ι * modeVelSq D ι v p))
          = fun p => (A.blocks K).leakCurl ι * (p.1 * modeCurlSq D ι G p)
            + (A.blocks K).leakVel ι * (p.1 * modeVelSq D ι v p) := by
        funext p
        ring
      rw [e]
      exact (m1.const_mul _).add (m3.const_mul _)
    · have e : (fun p => p.1 * ((A.blocks K).leakStrain ι * modeStrainSq D ι G p))
          = fun p => (A.blocks K).leakStrain ι * (p.1 * modeStrainSq D ι G p) := by
        funext p
        ring
      rw [e]
      exact m2.const_mul _
    · intro i
      obtain ⟨h1, h2, h3⟩ := groupCoeffs D R A P hP K i
      unfold groupCharge
      exact chargeY_integrable _ (trueProfiles D v G ι) _ _ _ h1 h2 h3 (hreg.1 ι).1 (hreg.1 ι).2 hpos
  · split_ifs with hres
    · exact le_rfl
    · refine setIntegral_nonneg hms (fun p hp => ?_)
      have hb : ι ∉ D.mesh.band K := fun h => hι (hbT h)
      have hl : ι ∉ (A.blocks K).leakModes := fun h => hι (hlT h)
      have hpi : ∀ i, ι ∉ (P.potential K).groupPartners i := fun i h => hι (hpT i h)
      have hcr : creditVelDemand D R K ι p = 0 := by
        unfold creditVelDemand
        refine Finset.sum_eq_zero (fun j _ => if_neg ?_)
        rintro ⟨h1, _⟩
        rcases (labelHarmonic_eq_or_neg hP.azimuth_pos (hcl j)).1 h1 with h | h
        · exact hι (h ▸ hcT j)
        · exact hι (h ▸ hcT' j)
      have hsl0 : ι ∉ R.pairSlackLabels K := fun h => hι (hsT (Finset.mem_filter.2 ⟨h, hres, hb⟩))
      obtain ⟨h1, h2, h3⟩ := hP.charges_cover K ι hres hb p hp
      have hd : ι ∉ deactPartners D R K (P.potential K) := fun h => hι (hdT h)
      simp only [← mem_deactPartners_iff D R K (P.potential K) ι hres hb, hd, hpi, hl, hsl0, if_false,
        Finset.sum_const_zero, add_zero, hcr] at h1 h2 h3
      have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
      have hlf := longFactor_pos (P.potential K) (hP.long_pos K).2.2 ι
      obtain ⟨hlS, hlG, -⟩ := hP.long_pos K
      obtain ⟨hhS, hhG⟩ := high_nonneg D R A P hP K
      have hℓ := hP.length_pos K
      have hL := hP.eps_length_pos K
      have c1 : 0 ≤ (R.entryCharges K ι).curlCharge p := le_trans (by positivity) h1
      have c2 : 0 ≤ (R.entryCharges K ι).gradCharge p := le_trans (by positivity) h2
      have c3 : 0 ≤ (R.entryCharges K ι).velCharge p := le_trans (by positivity) h3
      have hn1 : 0 ≤ modeCurlSq D ι G p := by
        rw [← curl_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      have hn2 : 0 ≤ modeStrainSq D ι G p := by
        rw [← strain_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      have hn3 : 0 ≤ modeVelSq D ι v p := by
        rw [← vel_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      unfold extraChargeDensity
      positivity
  · have hc0 : 0 ≤ c := le_trans (abs_nonneg _) (hc 0 ((D.mesh.box K).r₁, (D.mesh.box K).z₁) (Set.mem_prod.2 ⟨Set.left_mem_Icc.2
      (hP.mesh_valid.box_valid K).r_order.2.le, Set.left_mem_Icc.2 (hP.mesh_valid.box_valid K).z_order.2.le⟩)).1
    refine Summable.of_norm_bounded (hreg.2.mul_left (28 * c)) (fun ι => ?_)
    have hI0 : 0 ≤ ∫ p in (D.mesh.box K).rect, p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2 :=
      setIntegral_nonneg hms (fun p hp => mul_nonneg (rect_fst_nonneg D hP.mesh_valid K p hp) (by positivity))
    split_ifs
    · rw [norm_zero]
      exact mul_nonneg (by positivity) hI0
    · rw [← integral_const_mul]
      refine norm_integral_le_of_norm_le (((hreg.1 ι).2.const_mul (28 * c))) ?_
      refine ae_restrict_of_forall_mem hms (fun p hp => ?_)
      have hp1 : 0 ≤ p.1 := rect_fst_nonneg D hP.mesh_valid K p hp
      obtain ⟨k1, k2, k3, -⟩ := hc ι p hp
      have hn1 : 0 ≤ modeCurlSq D ι G p := by
        rw [← curl_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      have hn2 : 0 ≤ modeStrainSq D ι G p := by
        rw [← strain_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      have hn3 : 0 ≤ modeVelSq D ι v p := by
        rw [← vel_bandProfile D ι v G p]
        exact cnormSq_nonneg' _
      have hc1 : modeCurlSq D ι G p ≤ 27 * modeStrainSq D ι G p := by
        rw [← curl_bandProfile D ι v G p, ← strain_bandProfile D ι v G p]
        exact curl_cnormSq_le _
      rw [profile_sq_split, Real.norm_eq_abs]
      unfold extraChargeDensity
      have b1 : |(R.entryCharges K ι).curlCharge p * modeCurlSq D ι G p| ≤ c * modeCurlSq D ι G p := by
        rw [abs_mul, abs_of_nonneg hn1]
        exact mul_le_mul_of_nonneg_right k1 hn1
      have b2 : |(R.entryCharges K ι).gradCharge p * modeStrainSq D ι G p| ≤ c * modeStrainSq D ι G p := by
        rw [abs_mul, abs_of_nonneg hn2]
        exact mul_le_mul_of_nonneg_right k2 hn2
      have b3 : |(R.entryCharges K ι).velCharge p * modeVelSq D ι v p| ≤ c * modeVelSq D ι v p := by
        rw [abs_mul, abs_of_nonneg hn3]
        exact mul_le_mul_of_nonneg_right k3 hn3
      have b4 := abs_add_three ((R.entryCharges K ι).curlCharge p * modeCurlSq D ι G p)
        ((R.entryCharges K ι).gradCharge p * modeStrainSq D ι G p) ((R.entryCharges K ι).velCharge p * modeVelSq D ι v p)
      have b5 := mul_le_mul_of_nonneg_left hc1 hc0
      have hE : |(R.entryCharges K ι).curlCharge p * modeCurlSq D ι G p
          + (R.entryCharges K ι).gradCharge p * modeStrainSq D ι G p
          + (R.entryCharges K ι).velCharge p * modeVelSq D ι v p|
          ≤ 28 * c * (modeStrainSq D ι G p + modeVelSq D ι v p) := by
        nlinarith [mul_nonneg hc0 hn2, mul_nonneg hc0 hn3]
      rw [abs_mul, abs_of_nonneg hp1]
      calc |(R.entryCharges K ι).curlCharge p * modeCurlSq D ι G p
            + (R.entryCharges K ι).gradCharge p * modeStrainSq D ι G p
            + (R.entryCharges K ι).velCharge p * modeVelSq D ι v p| * p.1
          ≤ 28 * c * (modeStrainSq D ι G p + modeVelSq D ι v p) * p.1 := mul_le_mul_of_nonneg_right hE hp1
        _ = _ := by ring

end Internal

theorem chargeStageHolds : ChargeStageHolds := by
  intro k C nE nM D R A P states hstates hR hT hP
  exact Internal.chargeStage_of D R A P hR hT hP

end Assembly

end CertCell

end Breakdown

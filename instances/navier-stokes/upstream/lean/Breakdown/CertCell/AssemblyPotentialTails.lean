import Breakdown.CertCell.AssemblyPotentialTailsModes

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.PotentialTails

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

attribute [local instance] rect_finite

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {A : AssemblyEntry D R} {P : CouplingEntries D R}

theorem tail_cross_main {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (x : CellVars D R K → ℂ)
    (hx : states K x) :
    -quadFormValue (P.potential K).portForm x
        - ∑ ι ∈ D.mesh.resolved K, ((P.potential K).strainBalance ι * tailStrainSq D R K ι G
            + (P.potential K).velBalance ι * tailVelSq D R K ι v)
      ≤ 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K)
          (upperProfiles D R K (P.potential K) x) (tailProfiles D R K v G)
        + 2 * leafPair D R K (upperProfiles D R K (P.potential K) x) (tailProfiles D R K v G) := by
  have hK := hP.mesh_valid.box_valid K
  set xu := upperPart D R K (P.potential K) x with hxu
  set β : D.mesh.resolved K → Fin 12 → ℝ := fun b i =>
    if i.val < 9 then (P.potential K).strainBalance b.1 else (P.potential K).velBalance b.1 with hβdef
  set Y : D.mesh.resolved K → Fin 12 → ℝ := fun b i => ∫ p in (D.mesh.box K).rect,
    p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * hvec K (P.potential K) xu b i p).re with hYdef
  set tnh : D.mesh.resolved K → Fin 12 → ℝ := fun b i => (D.mesh.box K).tailNormSq (tailDeg (R := R) K b.1 i)
    (fun p => ((CellScalars.rHat (D.mesh.box K) p : ℝ) : ℂ) * hvec K (P.potential K) xu b i p) with htnh
  set tnF : D.mesh.resolved K → Fin 12 → ℝ := fun b i => (D.mesh.box K).tailNormSq (tailDeg (R := R) K b.1 i)
    (fun p => bandProfile D b.1 v G p i) with htnF
  have hpairs : modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.resolved K)
        (upperProfiles D R K (P.potential K) x) (tailProfiles D R K v G)
      + leafPair D R K (upperProfiles D R K (P.potential K) x) (tailProfiles D R K v G)
      = ∑ b, ∑ i, Y b i := by
    unfold modelPair leafPair
    simp only [sum_resolved (K := K), upperProfiles_val, tailProfiles_val]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun b _ => per_mode_identity hP hreg ht xu b
  have hy : ∀ b i, -(tnh b i / β b i + β b i * tnF b i) ≤ 2 * Y b i := by
    intro b i
    obtain ⟨hFm, hFi⟩ := component_regular hP hreg ht b.1 i
    obtain ⟨hhm, C, hC⟩ := hvec_regular hP ht.param K xu b i
    have hβ : 0 < β b i := by
      obtain ⟨h1, h2⟩ := hP.balance_pos K b.1 b.2
      simp only [hβdef]
      split_ifs
      · exact h1
      · exact h2
    have horth := proj_orth_of_sq _ hK _ (bases_valid_of hP K b.2) (tailDeg (R := R) K b.1 i) _ hFm hFi
    have key := (tail_cross_lower _ hK (tailDeg (R := R) K b.1 i) _ _ hβ horth hFm hFi hhm hC).2
    simp only [hYdef, tailProfile_apply]
    exact key
  have hport : ∑ b, ∑ i, tnh b i / β b i ≤ quadFormValue (P.potential K).portForm x := by
    refine le_trans (le_of_eq ?_) (hP.port_dominates K x hx)
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold couplingTailFull
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : i.val < 9
    · simp only [htnh, hβdef, tailDeg, h, decide_true, if_true, Bool.true_eq_false, if_false, zero_div, add_zero, hvec,
        cM, cL, hxu]
    · simp only [htnh, hβdef, tailDeg, h, decide_false, Bool.false_eq_true, if_false, zero_div, zero_add, hvec, cM,
        cL, hxu]
      rw [if_pos trivial]
  have htail : ∀ b : D.mesh.resolved K, ∑ i, β b i * tnF b i
      = (P.potential K).strainBalance b.1 * tailStrainSq D R K b.1 G
        + (P.potential K).velBalance b.1 * tailVelSq D R K b.1 v := by
    intro b
    rw [sum_fin12]
    have eg : ∀ a c : Fin 3, β b ⟨3 * a.val + c.val, by omega⟩ * tnF b ⟨3 * a.val + c.val, by omega⟩
        = (P.potential K).strainBalance b.1 * (D.mesh.box K).tailNormSq ((R.layouts K).layout b.1).degCoef
            (fun p => gradAt D.azimuthOrder b.1 G a c p) := by
      intro a c
      have hlt : 3 * a.val + c.val < 9 := by omega
      simp only [hβdef, htnF, tailDeg, hlt, if_true]
      congr 2
      funext p
      exact pairVec_grad _ _ a c
    have ev : ∀ a : Fin 3, β b ⟨9 + a.val, by omega⟩ * tnF b ⟨9 + a.val, by omega⟩
        = (P.potential K).velBalance b.1 * (D.mesh.box K).tailNormSq (((R.layouts K).layout b.1).degCoef - 1)
            (fun p => velAt D.azimuthOrder b.1 v a p) := by
      intro a
      have hlt : ¬ (9 + a.val < 9) := by omega
      simp only [hβdef, htnF, tailDeg, hlt, if_false]
      congr 2
      funext p
      exact pairVec_vel _ _ a
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => eg a c,
      Finset.sum_congr rfl fun a _ => ev a]
    unfold tailStrainSq tailVelSq
    simp only [Finset.mul_sum]
  have hsum := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) =>
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hy b i
  have e1 : ∑ b, ∑ i, -(tnh b i / β b i + β b i * tnF b i)
      = -(∑ b, ∑ i, tnh b i / β b i) - ∑ b, ∑ i, β b i * tnF b i := by
    simp only [neg_add, Finset.sum_add_distrib, Finset.sum_neg_distrib]
    ring
  have e2 : ∑ b, ∑ i, 2 * Y b i = 2 * ∑ b, ∑ i, Y b i := by
    simp only [← Finset.mul_sum]
  have e3 : ∑ b, ∑ i, β b i * tnF b i
      = ∑ ι ∈ D.mesh.resolved K, ((P.potential K).strainBalance ι * tailStrainSq D R K ι G
          + (P.potential K).velBalance ι * tailVelSq D R K ι v) := by
    rw [sum_resolved (K := K)]
    exact Finset.sum_congr rfl fun b _ => htail b
  rw [e1, e2, e3] at hsum
  linarith

theorem rHatMax_bound (K : Fin D.mesh.count) (hK : IsCellBox (D.mesh.box K)) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) : p.1 ≤ rHatMax D K * (D.mesh.box K).lineWeight p.1 := by
  unfold rHatMax CellBox.lineWeight
  split_ifs with h
  · have h2 : 0 < (D.mesh.box K).r₂ := by
      have := hK.r_order
      rw [h] at this
      exact this.2
    rw [div_self h2.ne', one_mul]
  · rw [div_one, mul_one]
    exact hp.1.2

theorem strainOfVec_tail (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    strainOfVec (tailProfile D R K ι v G p) = fun a b => gradAt D.azimuthOrder ι G a b p
      - (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
          (fun p' => gradAt D.azimuthOrder ι G a b p') p := by
  funext a b
  unfold strainOfVec gradOf tailProfile
  exact pairVec_grad _ _ a b

theorem velOf_tail (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    velOf (tailProfile D R K ι v G p) = fun a => velAt D.azimuthOrder ι v a p
      - (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1) (((R.layouts K).layout ι).degCoef - 1)
          (fun p' => velAt D.azimuthOrder ι v a p') p := by
  funext a
  unfold velOf tailProfile
  exact pairVec_vel _ _ a

theorem tail_high_main {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) :
    highPartnerAmount D K (P.potential K) (D.mesh.resolved K) (tailProfiles D R K v G)
      ≤ ∑ ι ∈ D.mesh.resolved K, (rHatMax D K * (2 * (P.potential K).highStrain / (P.potential K).youngCurl
            + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel) * tailStrainSq D R K ι G
          + rHatMax D K * (3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain)
            * tailVelSq D R K ι v) := by
  have hK := hP.mesh_valid.box_valid K
  have hs := rect_measurableSet (D.mesh.box K)
  obtain ⟨hyC, hyS, hyV⟩ := hP.young_pos K
  have herr := (hP.cell_conditions.model_split K).errors_nonneg
  have hS0 : 0 ≤ (P.potential K).highStrain := le_trans herr.2.2.2.2.2.2.1 (hP.high_ge K).1
  have hG0 : 0 ≤ (P.potential K).highGrad := le_trans herr.2.2.2.2.2.2.2 (hP.high_ge K).2
  have hk0 : 0 < 3 / (2 * Real.sqrt 2) := by positivity
  have hr0 : 0 ≤ rHatMax D K := by
    unfold rHatMax CellBox.lineWeight
    have h2 : 0 ≤ (D.mesh.box K).r₂ := le_trans hK.r_order.1 hK.r_order.2.le
    split_ifs
    · exact div_nonneg h2 h2
    · exact div_nonneg h2 zero_le_one
  unfold highPartnerAmount
  refine Finset.sum_le_sum fun ι hι => ?_
  have hX : tailProfiles D R K v G ι = fun p => tailProfile D R K ι v G p := by
    funext p
    simp only [tailProfiles, restrictTo, Finset.mem_coe, hι, if_true]
  rw [hX]
  set Q := ((R.layouts K).layout ι).degCoef with hQ
  set sT : Fin 3 → Fin 3 → ℝ × ℝ → ℂ := fun a b p => gradAt D.azimuthOrder ι G a b p
      - (D.mesh.box K).proj Q Q (fun p' => gradAt D.azimuthOrder ι G a b p') p with hsT
  set vT : Fin 3 → ℝ × ℝ → ℂ := fun a p => velAt D.azimuthOrder ι v a p
      - (D.mesh.box K).proj (Q - 1) (Q - 1) (fun p' => velAt D.azimuthOrder ι v a p') p with hvT
  set w : ℝ × ℝ → ℝ := fun p => (D.mesh.box K).lineWeight p.1 with hw
  set cS : ℝ := 2 * (P.potential K).highStrain / (P.potential K).youngCurl
    + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel with hcS
  set cV : ℝ := 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain with hcV
  have hsI : ∀ a b, IntegrableOn (fun p => w p * ‖sT a b p‖ ^ 2) (D.mesh.box K).rect := by
    intro a b
    obtain ⟨hm, hi⟩ := component_regular hP hreg ht ι ⟨3 * a.val + b.val, by omega⟩
    simp only [bandProfile, pairVec_grad, gradArray] at hm hi
    exact (tail_regular _ hK Q _ hm hi).2
  have hvI : ∀ a, IntegrableOn (fun p => w p * ‖vT a p‖ ^ 2) (D.mesh.box K).rect := by
    intro a
    obtain ⟨hm, hi⟩ := component_regular hP hreg ht ι ⟨9 + a.val, by omega⟩
    simp only [bandProfile, pairVec_vel, velArray] at hm hi
    exact (tail_regular _ hK (Q - 1) _ hm hi).2
  have hSI : IntegrableOn (fun p => w p * ∑ a : Fin 3, ∑ b : Fin 3, ‖sT a b p‖ ^ 2) (D.mesh.box K).rect := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hsI a b
  have hVI : IntegrableOn (fun p => w p * ∑ a : Fin 3, ‖vT a p‖ ^ 2) (D.mesh.box K).rect := by
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ fun a _ => hvI a
  have hSeq : ∫ p in (D.mesh.box K).rect, w p * ∑ a : Fin 3, ∑ b : Fin 3, ‖sT a b p‖ ^ 2
      = tailStrainSq D R K ι G := by
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hsI a b]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => hsI a b]
    rfl
  have hVeq : ∫ p in (D.mesh.box K).rect, w p * ∑ a : Fin 3, ‖vT a p‖ ^ 2 = tailVelSq D R K ι v := by
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ fun a _ => hvI a]
    rfl
  have hmono : ∫ p in (D.mesh.box K).rect, p.1 * highPartnerCharge (P.potential K) (tailProfile D R K ι v G p)
      ≤ ∫ p in (D.mesh.box K).rect, (rHatMax D K * cS) * (w p * ∑ a : Fin 3, ∑ b : Fin 3, ‖sT a b p‖ ^ 2)
          + (rHatMax D K * cV) * (w p * ∑ a : Fin 3, ‖vT a p‖ ^ 2) := by
    refine integral_mono_of_nonneg ?_ ((hSI.const_mul _).add (hVI.const_mul _)) ?_
    · refine ae_restrict_of_forall_mem hs fun p hp => ?_
      have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
      unfold highPartnerCharge
      have h1 : 0 ≤ curlSq (strainOfVec (tailProfile D R K ι v G p)) :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ sumSq (strainOfVec (tailProfile D R K ι v G p)) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h3 : 0 ≤ vecSq (velOf (tailProfile D R K ι v G p)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      positivity
    · refine ae_restrict_of_forall_mem hs fun p hp => ?_
      have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
      have hw0 : 0 ≤ w p := lineWeight_nonneg _ hK hp
      have hrb := rHatMax_bound K hK hp
      have hsS : sumSq (strainOfVec (tailProfile D R K ι v G p)) = ∑ a : Fin 3, ∑ b : Fin 3, ‖sT a b p‖ ^ 2 := by
        rw [strainOfVec_tail]
        rfl
      have hvS : vecSq (velOf (tailProfile D R K ι v G p)) = ∑ a : Fin 3, ‖vT a p‖ ^ 2 := by
        rw [velOf_tail]
        rfl
      have hcurl := curlSq_le_two (strainOfVec (tailProfile D R K ι v G p))
      have h1 : 0 ≤ curlSq (strainOfVec (tailProfile D R K ι v G p)) :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h2 : 0 ≤ sumSq (strainOfVec (tailProfile D R K ι v G p)) :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
      have h3 : 0 ≤ vecSq (velOf (tailProfile D R K ι v G p)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
      have hch : highPartnerCharge (P.potential K) (tailProfile D R K ι v G p)
          ≤ cS * sumSq (strainOfVec (tailProfile D R K ι v G p)) + cV * vecSq (velOf (tailProfile D R K ι v G p)) := by
        unfold highPartnerCharge
        have e1 : (P.potential K).highStrain / (P.potential K).youngCurl
            * curlSq (strainOfVec (tailProfile D R K ι v G p))
            ≤ 2 * (P.potential K).highStrain / (P.potential K).youngCurl
              * sumSq (strainOfVec (tailProfile D R K ι v G p)) := by
          have hq : 0 ≤ (P.potential K).highStrain / (P.potential K).youngCurl := div_nonneg hS0 hyC.le
          calc (P.potential K).highStrain / (P.potential K).youngCurl * curlSq (strainOfVec (tailProfile D R K ι v G p))
              ≤ (P.potential K).highStrain / (P.potential K).youngCurl
                  * (2 * sumSq (strainOfVec (tailProfile D R K ι v G p))) :=
                mul_le_mul_of_nonneg_left hcurl hq
            _ = _ := by ring
        rw [hcS, hcV]
        have e2 : 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad
            * (vecSq (velOf (tailProfile D R K ι v G p)) / (P.potential K).youngStrain
              + sumSq (strainOfVec (tailProfile D R K ι v G p)) / (P.potential K).youngVel)
            = 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngVel
                * sumSq (strainOfVec (tailProfile D R K ι v G p))
              + 3 / (2 * Real.sqrt 2) * (P.potential K).highGrad / (P.potential K).youngStrain
                * vecSq (velOf (tailProfile D R K ι v G p)) := by
          field_simp
          ring
        rw [e2]
        nlinarith
      have hch0 : 0 ≤ highPartnerCharge (P.potential K) (tailProfile D R K ι v G p) := by
        unfold highPartnerCharge
        positivity
      have hcS0 : 0 ≤ cS := by rw [hcS]; positivity
      have hcV0 : 0 ≤ cV := by rw [hcV]; positivity
      show p.1 * highPartnerCharge (P.potential K) (tailProfile D R K ι v G p)
        ≤ (rHatMax D K * cS) * (w p * ∑ a : Fin 3, ∑ b : Fin 3, ‖sT a b p‖ ^ 2)
          + (rHatMax D K * cV) * (w p * ∑ a : Fin 3, ‖vT a p‖ ^ 2)
      rw [← hsS, ← hvS]
      calc p.1 * highPartnerCharge (P.potential K) (tailProfile D R K ι v G p)
          ≤ (rHatMax D K * w p) * (cS * sumSq (strainOfVec (tailProfile D R K ι v G p))
              + cV * vecSq (velOf (tailProfile D R K ι v G p))) :=
            mul_le_mul hrb hch hch0 (mul_nonneg hr0 hw0)
        _ = _ := by ring
  rw [integral_add (hSI.const_mul _) (hVI.const_mul _), integral_const_mul, integral_const_mul, hSeq, hVeq] at hmono
  exact hmono

end Breakdown.CertCell.Assembly.Internal.PotentialTails

namespace Breakdown.CertCell.Assembly

theorem tailCrossStage_holds : TailCrossStageHolds := by
  intro k C nE nM D R A P states hstates _ htf hP _ K q v G H g κ F Pg ht ζ η
  exact Internal.PotentialTails.tail_cross_main hP htf.1 ht _ (hstates K q v G H g κ F Pg ht ζ η)

theorem tailHighStage_holds : TailHighStageHolds := by
  intro k C nE nM D R A P states hstates _ htf hP K q v G H g κ F Pg ht
  exact Internal.PotentialTails.tail_high_main hP htf.1 ht

end Breakdown.CertCell.Assembly

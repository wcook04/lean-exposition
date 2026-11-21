import Breakdown.FracCell.ClassProductSplit
import Breakdown.FracCell.ClassCrossRegular
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts

def ClassPointwiseAeStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R →
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ → p.1 ≠ 0 →
      ∀ (F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
        (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ),
      -(∑ n ∈ S.resolved, ∑ i : Fin Cl.count,
          if n ∈ Cl.resolvedPart i then Cl.shareWeight i * Cl.classLoss S.splitLength i p (s n) (v n) else 0)
        - ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
          ∑ i, Cl.classLoss S.splitLength i p (s' n') (v' n') / Cl.shareWeight i)
      ≤ ∑ n ∈ S.resolved, ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
          pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re

namespace SharpYClassCrossAeInternal

private theorem loss_nonneg (Cl : CellClasses) {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin Cl.count) (p : ℝ × ℝ)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (h1 : 0 ≤ Cl.strainDev i p) (h2 : 0 ≤ Cl.gradDev i p) :
    0 ≤ Cl.classLoss ℓ i p s v := by
  unfold CellClasses.classLoss
  have a1 : 0 ≤ curlSq s := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have a2 : 0 ≤ sumSq s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have a3 : 0 ≤ vecSq v := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hT : 0 ≤ Exterior.traceFreeConst := Real.sqrt_nonneg _
  exact add_nonneg (mul_nonneg h1 a1) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hT) h2)
    (add_nonneg (mul_nonneg hℓ.le a2) (div_nonneg a3 hℓ.le)))

private theorem modeMat_neg (m : ℕ) (β : ℤ) (F : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m (-β) F r z a b = (starRingEnd ℂ) (modeMat m β F r z a b) := by
  have h : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  unfold modeMat
  rw [intervalIntegral.integral_of_le h, intervalIntegral.integral_of_le h, map_mul, ← integral_conj]
  congr 1
  · simp [map_ofNat]
  · refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_neg, Complex.conj_I, azimuth]
    congr 2
    push_cast
    ring

private theorem pair_zero {k N : ℕ} (c : FracCellData k N) (n n' : ℤ) (p : ℝ × ℝ)
    (h1 : CellScalars.strainMode c (n - n') p = 0) (h2 : CellScalars.curlGradMode c (n - n') p = 0)
    (h3 : CellScalars.strainMode c (n' - n) p = 0) (h4 : CellScalars.curlGradMode c (n' - n) p = 0)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    pairWave c n n' p s v s' v' + pairWave c n' n p s' v' s v = 0 := by
  simp [pairWave, waveForm, h1, h2, h3, h4, couplingMap, bracketMat, entryPairing]

private theorem cross_vanish {α : ℝ} {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    {n n' : ℤ} (hn : n ∈ S.resolved) (hn'' : n' ∉ S.resolved ∪ S.band) (hex : ∀ i, n - n' ∉ Cl.modes i)
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (hp0 : p.1 ≠ 0)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    pairWave c n n' p s v s' v' + pairWave c n' n p s' v' s v = 0 := by
  have hz : ¬ (∃ q ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, q.1 ≠ 0 ∧ (modeVec c.order (n - n') c.modelVelocity q.1 q.2 ≠ 0 ∨
      modeVec c.order (n - n') c.modelCurl q.1 q.2 ≠ 0 ∨
      modeMat c.order (n - n') c.modelStrain q.1 q.2 ≠ 0 ∨ modeMat c.order (n - n') c.modelCurlGrad q.1 q.2 ≠ 0)) := by
    intro h
    obtain ⟨i, hi⟩ := hd.class_cover n hn n' hn'' h
    exact hex i hi
  have hS0 : modeMat c.order (n - n') c.modelStrain p.1 p.2 = 0 := by
    by_contra h
    exact hz ⟨p, hp, hp0, Or.inr (Or.inr (Or.inl h))⟩
  have hG0 : modeMat c.order (n - n') c.modelCurlGrad p.1 p.2 = 0 := by
    by_contra h
    exact hz ⟨p, hp, hp0, Or.inr (Or.inr (Or.inr h))⟩
  have hneg : n' - n = -(n - n') := by ring
  have hS1 : modeMat c.order (n' - n) c.modelStrain p.1 p.2 = 0 := by
    funext a b
    rw [hneg, modeMat_neg, hS0]
    simp
  have hG1 : modeMat c.order (n' - n) c.modelCurlGrad p.1 p.2 = 0 := by
    funext a b
    rw [hneg, modeMat_neg, hG0]
    simp
  exact pair_zero c n n' p hS0 hG0 hS1 hG1 s v s' v'

private theorem ae_open_box (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
  have h : (Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume]
      (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc.symm Ioo_ae_eq_Icc.symm
  unfold CellBox.rect
  rw [ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc)]
  filter_upwards [h] with p hp hps
  exact cast hp hps

end SharpYClassCrossAeInternal

open SharpYClassCrossAeInternal

theorem classPointwiseAe_of (hY : ClassProductSplitAeStatement) : ClassPointwiseAeStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd
  filter_upwards [hY α h1 h2 c hc K S B Cl R hd] with p hYp hp hp0 F s v s' v'
  set F' := F.filter (fun n' => n' ∉ S.resolved ∪ S.band) with hF'
  set term : ℤ → ℤ → ℝ := fun n n' =>
    (pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re with hterm
  have hR : ∑ n ∈ S.resolved, ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
      pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re
      = ∑ n ∈ S.resolved, ∑ n' ∈ F', term n n' := by
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hF', Finset.sum_filter]
    refine Finset.sum_congr rfl fun n' _ => ?_
    by_cases h : n' ∈ S.resolved ∪ S.band <;> simp [h, hterm]
  have hsplit : ∀ n ∈ S.resolved, ∀ n' ∈ F', term n n' = ∑ i, (if n - n' ∈ Cl.modes i then term n n' else 0) := by
    intro n hn n' hn'
    have hn'' : n' ∉ S.resolved ∪ S.band := (Finset.mem_filter.mp hn').2
    by_cases hex : ∃ i, n - n' ∈ Cl.modes i
    · obtain ⟨i, hi⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [hi]
      · intro j _ hji
        have hdj := hd.class_disjoint j i hji
        rw [if_neg]
        exact fun hj => Finset.disjoint_left.mp hdj hj hi
      · intro h
        exact absurd (Finset.mem_univ i) h
    · push Not at hex
      have h0 : term n n' = 0 := by
        simp only [hterm]
        rw [cross_vanish hd hn hn'' hex hp hp0]
        simp
      rw [h0]
      simp
  have hsum2 : ∑ n ∈ S.resolved, ∑ n' ∈ F', term n n'
      = ∑ i, ∑ n ∈ S.resolved.filter (fun n => n ∈ Cl.resolvedPart i), ∑ n' ∈ F',
          (if n - n' ∈ Cl.modes i then term n n' else 0) := by
    calc _ = ∑ n ∈ S.resolved, ∑ n' ∈ F', ∑ i, (if n - n' ∈ Cl.modes i then term n n' else 0) :=
          Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun n' hn' => hsplit n hn n' hn'
      _ = ∑ n ∈ S.resolved, ∑ i, ∑ n' ∈ F', (if n - n' ∈ Cl.modes i then term n n' else 0) :=
          Finset.sum_congr rfl fun n _ => Finset.sum_comm
      _ = ∑ i, ∑ n ∈ S.resolved, ∑ n' ∈ F', (if n - n' ∈ Cl.modes i then term n n' else 0) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_filter]
          refine Finset.sum_congr rfl fun n hn => ?_
          split_ifs with hr
          · rfl
          · refine Finset.sum_eq_zero fun n' hn' => ?_
            rw [if_neg]
            intro hm
            exact hr (hd.class_resolved_cover i n hn ⟨n', (Finset.mem_filter.mp hn').2, hm⟩)
  have hL : (∑ n ∈ S.resolved, ∑ i : Fin Cl.count, if n ∈ Cl.resolvedPart i then
        Cl.shareWeight i * Cl.classLoss S.splitLength i p (s n) (v n) else 0)
      = ∑ i, Cl.shareWeight i * ∑ n ∈ S.resolved.filter (fun n => n ∈ Cl.resolvedPart i),
          Cl.classLoss S.splitLength i p (s n) (v n) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs <;> simp
  have hF : (∑ n' ∈ F, if n' ∈ S.resolved ∪ S.band then 0 else
        ∑ i, Cl.classLoss S.splitLength i p (s' n') (v' n') / Cl.shareWeight i)
      = ∑ i, (∑ n' ∈ F', Cl.classLoss S.splitLength i p (s' n') (v' n')) / Cl.shareWeight i := by
    simp_rw [Finset.sum_div]
    rw [Finset.sum_comm, hF', Finset.sum_filter]
    refine Finset.sum_congr rfl fun n' _ => ?_
    by_cases h : n' ∈ S.resolved ∪ S.band <;> simp [h]
  rw [hR, hsum2, hL, hF]
  have key : ∀ i : Fin Cl.count,
      -(Cl.shareWeight i * ∑ n ∈ S.resolved.filter (fun n => n ∈ Cl.resolvedPart i),
          Cl.classLoss S.splitLength i p (s n) (v n))
        - (∑ n' ∈ F', Cl.classLoss S.splitLength i p (s' n') (v' n')) / Cl.shareWeight i
      ≤ ∑ n ∈ S.resolved.filter (fun n => n ∈ Cl.resolvedPart i), ∑ n' ∈ F',
          (if n - n' ∈ Cl.modes i then term n n' else 0) :=
    fun i => hYp hp hp0 i _ F' s v s' v'
  have hall := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib] at hall
  linarith

theorem classCross_of_pointwiseAe (hP : ClassPointwiseAeStatement) (hR : ClassCrossRegularStatement)
    (hC : ChargeRegularStatement) : ClassCrossStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hd hax x hx
  obtain ⟨hI, hL⟩ := hR α h1 h2 c hc K S B Cl R hd hax x hx
  obtain ⟨hCI, -, -, hCst, -, -, -⟩ := hC α h1 h2 c hc K S B Cl R hd hax x hx
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hr0 : ∀ p ∈ K.rect, 0 ≤ p.1 := fun p hp => le_trans hd.box.r_order.1 hp.1.1
  have hℓ := hd.scalars.splitLength_pos
  have hw : ∀ i, 0 < Cl.shareWeight i := fun i => (hd.class_weights_pos i).1
  have hloss : ∀ i p s v, 0 ≤ Cl.classLoss S.splitLength i p s v := fun i p s v =>
    loss_nonneg Cl hℓ i p s v (hd.class_devs_nonneg i p).1 (hd.class_devs_nonneg i p).2.1
  have hcd : ∀ n p, 0 ≤ classDensity c K S x Cl n p := by
    intro n p
    unfold classDensity
    split_ifs
    · exact le_rfl
    · exact Finset.sum_nonneg fun i _ => div_nonneg (hloss _ _ _ _) (hw i).le
  have hcdi : ∀ n, 0 ≤ ∫ p in K.rect, p.1 * classDensity c K S x Cl n p := fun n =>
    setIntegral_nonneg hrect fun p hp => mul_nonneg (hr0 p hp) (hcd n p)
  set A : ℝ × ℝ → ℝ := fun p => ∑ n ∈ S.resolved, ∑ i : Fin Cl.count,
    if n ∈ Cl.resolvedPart i then Cl.shareWeight i * Cl.classLoss S.splitLength i p
      (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p) else 0 with hA
  have hAi : ∀ n ∈ S.resolved, ∀ i, IntegrableOn (fun p : ℝ × ℝ => p.1 * (if n ∈ Cl.resolvedPart i then
      Cl.shareWeight i * Cl.classLoss S.splitLength i p (K.lowStrainAt c.order n S.degHigh x.2.1 p)
        (K.lowVelocityAt c.order n S.degHigh x.1 p) else 0)) K.rect := by
    intro n hn i
    split_ifs
    · exact IntegrableOn.congr_fun ((hL n hn i).const_mul (Cl.shareWeight i)) (fun p _ => by ring) hrect
    · simp
  have hAint : IntegrableOn (fun p : ℝ × ℝ => p.1 * A p) K.rect := by
    simp only [hA, Finset.mul_sum]
    exact integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun i _ => hAi n hn i
  have hAval : ∫ p in K.rect, p.1 * A p = CellScalars.classTerm c K S Cl x.1 x.2.1 := by
    unfold CellScalars.classTerm
    simp only [hA, Finset.mul_sum]
    rw [integral_finsetSum _ fun n hn => integrable_finsetSum _ fun i _ => hAi n hn i]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [integral_finsetSum _ fun i _ => hAi n hn i]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs
    · rw [← integral_const_mul]
      congr 1
      funext p
      ring
    · simp
  have hpt : ∀ n ∈ S.resolved, ∀ n' p, classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p =
      (if n' ∈ S.resolved ∪ S.band then 0 else
        pairWave c n n' p (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)
            (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
          + pairWave c n' n p (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
            (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)).re := by
    intro n hn n' p
    unfold classCrossDensity
    have e1 : lowGrad c K S x n p = K.lowStrainAt c.order n S.degHigh x.2.1 p := by simp [lowGrad, hn]
    have e2 : lowVel c K S x n p = K.lowVelocityAt c.order n S.degHigh x.1 p := by simp [lowVel, hn]
    rw [e1, e2]
    by_cases h : n' ∈ S.resolved ∪ S.band
    · rw [if_pos h, if_neg (fun h' : n' ∈ (↑(S.resolved ∪ S.band) : Set ℤ)ᶜ => h' (Finset.mem_coe.mpr h))]
    · rw [if_neg h, if_pos (show n' ∈ (↑(S.resolved ∪ S.band) : Set ℤ)ᶜ from fun h' => h (Finset.mem_coe.mp h'))]
  have hS : ∀ n ∈ S.resolved,
      Summable (fun n' : ℤ => ∫ p in K.rect, p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p) := by
    intro n hn
    refine summable_of_ne_finset_zero (s := Finset.univ.biUnion fun i => (Cl.modes i).image fun β => n - β) ?_
    intro n' hn'
    have hcls : ∀ i, n - n' ∉ Cl.modes i := by
      intro i hi
      apply hn'
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨n - n', hi, by ring⟩⟩
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_open_box K] with p hp
    have h0 : p.1 ≠ 0 := (lt_of_le_of_lt hd.box.r_order.1 hp.1.1).ne'
    rw [hpt n hn n' p]
    by_cases hb : n' ∈ S.resolved ∪ S.band
    · simp [hb]
    · rw [if_neg hb, cross_vanish hd hn hb hcls hp h0]
      simp
  have hbound : ∀ F : Finset ℤ,
      -CellScalars.classTerm c K S Cl x.1 x.2.1 - classSum c K S x Cl
        ≤ ∑ n' ∈ F, ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p := by
    intro F
    have hFi : IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑ n' ∈ F, classDensity c K S x Cl n' p) K.rect := by
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ fun n' _ => hCI n'
    have hXi : IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑ n ∈ S.resolved, ∑ n' ∈ F, classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p)
        K.rect := by
      simp only [Finset.mul_sum]
      exact integrable_finsetSum _ fun n hn => integrable_finsetSum _ fun n' _ => hI n hn n'
    have hsw : ∑ n' ∈ F, ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p
        = ∫ p in K.rect, p.1 * ∑ n ∈ S.resolved, ∑ n' ∈ F, classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]
      rw [integral_finsetSum _ fun n hn => integrable_finsetSum _ fun n' _ => hI n hn n']
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [integral_finsetSum _ fun n' _ => hI n hn n']
    have hmono : ∫ p in K.rect, p.1 * (-A p - ∑ n' ∈ F, classDensity c K S x Cl n' p)
        ≤ ∫ p in K.rect, p.1 * ∑ n ∈ S.resolved, ∑ n' ∈ F, classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p := by
      refine setIntegral_mono_ae_restrict ?_ hXi ?_
      · simp only [mul_sub, mul_neg]
        exact (hAint.neg).sub hFi
      · filter_upwards [ae_open_box K, hP α h1 h2 c hc K S B Cl R hd] with p hp hPp
        have hpos : 0 < p.1 := lt_of_le_of_lt hd.box.r_order.1 hp.1.1
        have h0 : p.1 ≠ 0 := hpos.ne'
        refine mul_le_mul_of_nonneg_left ?_ hpos.le
        have key := hPp hp h0 F
          (fun n => K.lowStrainAt c.order n S.degHigh x.2.1 p) (fun n => K.lowVelocityAt c.order n S.degHigh x.1 p)
          (fun n' => sharpGrad c K S x n' p) (fun n' => sharpVel c K S x n' p)
        have eR : ∑ n ∈ S.resolved, ∑ n' ∈ F, classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p
            = ∑ n ∈ S.resolved, ∑ n' ∈ F, (if n' ∈ S.resolved ∪ S.band then 0 else
              pairWave c n n' p (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)
                  (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
                + pairWave c n' n p (sharpGrad c K S x n' p) (sharpVel c K S x n' p)
                  (K.lowStrainAt c.order n S.degHigh x.2.1 p) (K.lowVelocityAt c.order n S.degHigh x.1 p)).re :=
          Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun n' _ => hpt n hn n' p
        rw [eR]
        exact key
    have hleft : ∫ p in K.rect, p.1 * (-A p - ∑ n' ∈ F, classDensity c K S x Cl n' p)
        = -CellScalars.classTerm c K S Cl x.1 x.2.1 - ∑ n' ∈ F, ∫ p in K.rect, p.1 * classDensity c K S x Cl n' p := by
      simp only [mul_sub, mul_neg]
      have e := integral_sub hAint.neg hFi
      simp only [Pi.neg_apply] at e
      rw [e, integral_neg, hAval]
      simp only [Finset.mul_sum]
      rw [integral_finsetSum _ fun n' _ => hCI n']
    have hpart : ∑ n' ∈ F, ∫ p in K.rect, p.1 * classDensity c K S x Cl n' p ≤ classSum c K S x Cl :=
      hCst.sum_le_tsum F fun n' _ => hcdi n'
    rw [hsw]
    linarith
  have hsum : HasSum (fun n' : ℤ => ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p)
      (∑ n ∈ S.resolved, ∑' n' : ℤ, ∫ p in K.rect, p.1 * classCrossDensity c K S x (↑(S.resolved ∪ S.band))ᶜ n n' p) :=
    hasSum_sum fun n hn => (hS n hn).hasSum
  exact le_hasSum_of_le_sum hsum hbound

theorem classCross_of_ae (hY : ClassProductSplitAeStatement) (hR : ClassCrossRegularStatement)
    (hC : ChargeRegularStatement) : ClassCrossStatement :=
  classCross_of_pointwiseAe (classPointwiseAe_of hY) hR hC

theorem classCross_closed : ClassCrossStatement :=
  classCross_of_ae classProductSplitAe_holds classCrossRegular_holds chargeRegular

end CellAnalysis

end CellCert

end Breakdown

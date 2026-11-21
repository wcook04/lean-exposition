import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.AssemblyPotentialTailsCross
import Breakdown.FracCell.EnergyHeightProj

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.PotentialTails

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

attribute [local instance] rect_finite

theorem conj_modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    (starRingEnd ℂ) (modelTriple S Gω a g a' g')
      = modelTriple (fun i j => (starRingEnd ℂ) (S i j)) (fun i j => (starRingEnd ℂ) (Gω i j))
          (fun i => (starRingEnd ℂ) (a i)) (fun ij => (starRingEnd ℂ) (g ij))
          (fun i => (starRingEnd ℂ) (a' i)) (fun ij => (starRingEnd ℂ) (g' ij)) := by
  unfold modelTriple modelBilin curlOfGrad
  simp only [map_div₀, map_add, map_neg, map_sum, map_mul, Complex.conj_ofReal, map_one, map_ofNat]

theorem modelTriple_swap (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : modelTriple S Gω a g a' g' = modelTriple S Gω a' g' a g := by
  unfold modelTriple
  ring

theorem conj_star_fn {ι : Type} (f : ι → ℂ) : (fun i => (starRingEnd ℂ) ((star f) i)) = f := by
  funext i
  simp [Pi.star_apply]

theorem conj_fn_eq_star {ι : Type} (f : ι → ℂ) : (fun i => (starRingEnd ℂ) (f i)) = star f := by
  funext i
  simp [Pi.star_apply]

theorem planeValue_rect {count : ℕ} (F : CellMatField count) (box : Fin count → CellBox) (K : Fin count)
    (ι : ℤ × ℤ) (a b : Fin 3) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    F.planeValue box K ι a b p = (F.comp K ι a b).eval (box K) p := by
  unfold CellMatField.planeValue labelValueAt
  rw [if_pos hp]

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {A : AssemblyEntry D R} {P : CouplingEntries D R}

theorem rect_snd_nonneg {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) : 0 ≤ p.2 :=
  le_trans ((hP.mesh_valid.box_valid K).z_order.1) hp.2.1

theorem model_sym {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (α : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) (X Y : Fin 12 → ℂ) :
    (sesq12 ((P.potential K).couplingModel α p) X Y).re
      = (sesq12 ((P.potential K).couplingModel (-α) p) Y X).re := by
  have hz := rect_snd_nonneg hP K hp
  obtain ⟨_, _, hSc, hGc⟩ := (hP.cell_conditions.model_split K).model_conj_closed
  have hS : (fun a b => D.model.strain.planeValue D.mesh.box K (-α) a b p)
      = fun a b => (starRingEnd ℂ) (D.model.strain.planeValue D.mesh.box K α a b p) := by
    funext a b
    rw [planeValue_rect _ _ _ _ _ _ hz, planeValue_rect _ _ _ _ _ _ hz, hSc.2 K α a b p]
  have hG : (fun a b => D.model.vorticityGrad.planeValue D.mesh.box K (-α) a b p)
      = fun a b => (starRingEnd ℂ) (D.model.vorticityGrad.planeValue D.mesh.box K α a b p) := by
    funext a b
    rw [planeValue_rect _ _ _ _ _ _ hz, planeValue_rect _ _ _ _ _ _ hz, hGc.2 K α a b p]
  rw [hP.coupling_model K α p hp, hP.coupling_model K (-α) p hp, hS, hG, ← Complex.conj_re,
    conj_modelTriple]
  simp only [conj_star_fn, conj_fn_eq_star]
  rw [modelTriple_swap]

theorem selfAdjoint_sesq_re_symm {L : Matrix (Fin 12) (Fin 12) ℂ} (hL : L.IsHermitian) (X Y : Fin 12 → ℂ) :
    (sesq12 L X Y).re = (sesq12 L Y X).re := by
  rw [← Complex.conj_re (sesq12 L Y X)]
  congr 1
  unfold sesq12
  rw [Finset.sum_comm]
  simp only [map_sum, map_mul, Complex.conj_conj]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hL i) j
  simp only [conjTranspose_apply] at h
  rw [← h]
  simp only [Complex.star_def, Complex.conj_conj]
  ring

theorem cellPoly_eval_continuous (Kb : CellBox) (Pl : CellPoly) : Continuous (fun p => Pl.eval Kb p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem sesq12_single (M : Matrix (Fin 12) (Fin 12) ℂ) (i j : Fin 12) :
    sesq12 M (Pi.single i 1) (Pi.single j 1) = M i j := by
  unfold sesq12
  simp [Pi.single_apply]

theorem modelTriple_continuous {S Gω : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} (hS : ∀ a b, Continuous fun p => S p a b)
    (hG : ∀ a b, Continuous fun p => Gω p a b) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : Continuous fun p => modelTriple (S p) (Gω p) a g a' g' := by
  unfold modelTriple modelBilin curlOfGrad
  fun_prop

theorem coupling_continuousOn {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (α : ℤ × ℤ) (i j : Fin 12) :
    ContinuousOn (fun p => (P.potential K).couplingModel α p i j) (D.mesh.box K).rect := by
  have hc : Continuous fun p => modelTriple
      (fun a b => (D.model.strain.comp K α a b).eval (D.mesh.box K) p)
      (fun a b => (D.model.vorticityGrad.comp K α a b).eval (D.mesh.box K) p)
      (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) :=
    modelTriple_continuous (fun a b => cellPoly_eval_continuous _ _) (fun a b => cellPoly_eval_continuous _ _) _ _ _ _
  refine hc.continuousOn.congr fun p hp => ?_
  have hz := rect_snd_nonneg hP K hp
  show (P.potential K).couplingModel α p i j = _
  rw [← sesq12_single ((P.potential K).couplingModel α p) i j, hP.coupling_model K α p hp]
  simp only [planeValue_rect _ _ _ _ _ _ hz]

theorem lowProfile_continuous (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x : CellVars D R K → ℂ) (j : Fin 12) :
    Continuous fun p => lowProfile D R K ι x p j := by
  unfold lowProfile pairVec lowGrad lowVel lowStrainOf lowVelocityOf CellCert.CellEnergy.basisFn CellBases.radialPoly CellBases.heightPoly
  split_ifs
  · fun_prop
  · fun_prop

theorem lineWeight_le_mul (Kb : CellBox) (hK : IsCellBox Kb) {p : ℝ × ℝ} (hp : p ∈ Kb.rect) :
    Kb.lineWeight p.1 ≤ (if Kb.r₁ = 0 then 1 else Kb.r₁⁻¹) * p.1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · rw [one_mul]
  · have h0 : 0 < Kb.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h)
    rw [inv_mul_eq_div, le_div_iff₀ h0, one_mul]
    exact hp.1.1

theorem proj_orth_of_sq (Kb : CellBox) (hK : IsCellBox Kb) (B : CellBases) (hB : IsCellBases Kb B) (Q : ℕ)
    (F : ℝ × ℝ → ℂ) (hFm : AEStronglyMeasurable F (volume.restrict Kb.rect))
    (hFi : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖F p‖ ^ 2) Kb.rect) :
    ∀ P ∈ polyFn Q Q, Kb.pairOn Kb.lineWeightFn (fun p => F p - Kb.proj Q Q F p) P = 0 := by
  have hs := rect_measurableSet Kb
  have hwc : Continuous fun p : ℝ × ℝ => Kb.lineWeight p.1 := (lineWeight_continuous Kb).comp continuous_fst
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  have hw1 : IntegrableOn (fun p : ℝ × ℝ => Kb.lineWeight p.1) Kb.rect := by
    refine Integrable.mono' (integrable_const Cw) hwc.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hs fun p hp => hCw p hp
  have hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((Kb.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) Kb.rect := by
    intro t s ht hs'
    have hts : Continuous fun p : ℝ × ℝ => t p.1 * s p.2 := (ht.comp continuous_fst).mul (hs'.comp continuous_snd)
    obtain ⟨Ct, hCt⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hts.continuousOn
    refine Integrable.mono' ((hw1.add hFi).div_const 2 |>.mul_const (max Ct 0))
      ((Complex.continuous_ofReal.comp ((hwc.mul (ht.comp continuous_fst)).mul (hs'.comp continuous_snd))).aestronglyMeasurable.mul hFm) ?_
    refine ae_restrict_of_forall_mem hs fun p hp => ?_
    have h0 := lineWeight_nonneg Kb hK hp
    have h1 : |t p.1 * s p.2| ≤ max Ct 0 := le_max_of_le_left (by simpa [Real.norm_eq_abs] using hCt p hp)
    have h2 : ‖F p‖ ≤ (1 + ‖F p‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖F p‖ - 1)]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      show Kb.lineWeight p.1 * t p.1 * s p.2 = Kb.lineWeight p.1 * (t p.1 * s p.2) by ring,
      abs_mul, abs_of_nonneg h0]
    show Kb.lineWeight p.1 * |t p.1 * s p.2| * ‖F p‖ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖F p‖ ^ 2) / 2 * max Ct 0
    have h3 : Kb.lineWeight p.1 * ‖F p‖ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖F p‖ ^ 2) / 2 := by
      nlinarith [mul_le_mul_of_nonneg_left h2 h0]
    calc Kb.lineWeight p.1 * |t p.1 * s p.2| * ‖F p‖ = (Kb.lineWeight p.1 * ‖F p‖) * |t p.1 * s p.2| := by ring
      _ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖F p‖ ^ 2) / 2 * max Ct 0 :=
        mul_le_mul h3 h1 (abs_nonneg _) (by nlinarith [norm_nonneg (F p)])
  intro P hP
  rw [CellCert.CellEnergy.HeightProj.proj_eq_basis Kb B hB Q F hF]
  exact CellCert.CellEnergy.HeightProj.proj_orth Kb B hB Q F hF P hP

def tailDeg (K : Fin D.mesh.count) (ι : ℤ × ℤ) (j : Fin 12) : ℕ :=
  if j.val < 9 then ((R.layouts K).layout ι).degCoef else ((R.layouts K).layout ι).degCoef - 1

theorem tailProfile_apply (K : Fin D.mesh.count) (ι : ℤ × ℤ) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (j : Fin 12) :
    tailProfile D R K ι v G p j = bandProfile D ι v G p j
      - (D.mesh.box K).proj (tailDeg (R := R) K ι j) (tailDeg (R := R) K ι j) (fun p' => bandProfile D ι v G p' j) p := by
  by_cases h : j.val < 9
  · simp only [tailProfile, bandProfile, pairVec, tailDeg, h, dif_pos, if_pos, gradArray]
  · simp only [tailProfile, bandProfile, pairVec, tailDeg, h, dif_neg, if_neg, not_false_eq_true, velArray]

theorem curlComp_zero (s : Fin 3 → Fin 3 → ℂ) : curlComp s 0 = s 2 1 - s 1 2 := by
  simp [curlComp, Fin.sum_univ_three, CellCert.permSign]
  ring

theorem curlComp_one (s : Fin 3 → Fin 3 → ℂ) : curlComp s 1 = s 0 2 - s 2 0 := by
  simp [curlComp, Fin.sum_univ_three, CellCert.permSign]
  ring

theorem curlComp_two (s : Fin 3 → Fin 3 → ℂ) : curlComp s 2 = s 1 0 - s 0 1 := by
  simp [curlComp, Fin.sum_univ_three, CellCert.permSign]
  ring

theorem norm_sub_sq_le (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_sub_le x y
  have h2 : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem curlSq_le_two (s : Fin 3 → Fin 3 → ℂ) : curlSq s ≤ 2 * sumSq s := by
  unfold curlSq sumSq
  simp only [Fin.sum_univ_three]
  rw [curlComp_zero, curlComp_one, curlComp_two]
  have h0 := norm_sub_sq_le (s 2 1) (s 1 2)
  have h1 := norm_sub_sq_le (s 0 2) (s 2 0)
  have h2 := norm_sub_sq_le (s 1 0) (s 0 1)
  nlinarith [sq_nonneg ‖s 0 0‖, sq_nonneg ‖s 1 1‖, sq_nonneg ‖s 2 2‖]

theorem pairVec_grad (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (a b : Fin 3) :
    pairVec s v ⟨3 * a.val + b.val, by omega⟩ = s a b := by
  unfold pairVec
  rw [dif_pos (by show 3 * a.val + b.val < 9; omega)]
  congr 1
  · ext; simp only; omega
  · ext; simp only; omega

theorem pairVec_vel (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (a : Fin 3) :
    pairVec s v ⟨9 + a.val, by omega⟩ = v a := by
  unfold pairVec
  rw [dif_neg (by show ¬ (9 + a.val < 9); omega)]
  congr 1
  ext; simp only; omega


theorem component_regular {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) (j : Fin 12) :
    AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect) ∧
    IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1 * ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect := by
  have hK := hP.mesh_valid.box_valid K
  obtain ⟨hm, hi⟩ := (hreg K q v G H g κ F Pg ht).1 ι
  refine ⟨hm j, ?_⟩
  have hc : 0 ≤ (if (D.mesh.box K).r₁ = 0 then 1 else (D.mesh.box K).r₁⁻¹) := by
    split_ifs
    · exact zero_le_one
    · exact inv_nonneg.2 hK.r_order.1
  refine Integrable.mono' (hi.const_mul (if (D.mesh.box K).r₁ = 0 then 1 else (D.mesh.box K).r₁⁻¹))
    ((((lineWeight_continuous _).comp continuous_fst).aestronglyMeasurable).mul ((hm j).norm.pow 2)) ?_
  refine ae_restrict_of_forall_mem (rect_measurableSet _) fun p hp => ?_
  have h0 := lineWeight_nonneg _ hK hp
  have h1 := lineWeight_le_mul _ hK hp
  have hp1 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have h2 : ‖bandProfile D ι v G p j‖ ^ 2 ≤ ∑ j', ‖bandProfile D ι v G p j'‖ ^ 2 :=
    Finset.single_le_sum (f := fun j' => ‖bandProfile D ι v G p j'‖ ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ j)
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  calc (D.mesh.box K).lineWeight p.1 * ‖bandProfile D ι v G p j‖ ^ 2
      ≤ ((if (D.mesh.box K).r₁ = 0 then 1 else (D.mesh.box K).r₁⁻¹) * p.1)
          * ∑ j', ‖bandProfile D ι v G p j'‖ ^ 2 :=
        mul_le_mul h1 h2 (sq_nonneg _) (mul_nonneg hc hp1)
    _ = (if (D.mesh.box K).r₁ = 0 then 1 else (D.mesh.box K).r₁⁻¹)
          * (p.1 * ∑ j', ‖bandProfile D ι v G p j'‖ ^ 2) := by ring

theorem bases_valid_of {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) {ι : ℤ × ℤ}
    (hι : ι ∈ D.mesh.resolved K) : IsCellBases (D.mesh.box K) (R.layouts K).bases := by
  obtain ⟨c, S, _, _, hL⟩ := (hP.cell_conditions.layouts_valid K).layout_valid ι hι
  exact hL.bases_valid

theorem tail_component_regular {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) (j : Fin 12) :
    AEStronglyMeasurable (fun p => tailProfile D R K ι v G p j) (volume.restrict (D.mesh.box K).rect) ∧
    IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1 * ‖tailProfile D R K ι v G p j‖ ^ 2) (D.mesh.box K).rect := by
  have hK := hP.mesh_valid.box_valid K
  obtain ⟨hm, hi⟩ := component_regular hP hreg ht ι j
  simp only [tailProfile_apply K ι v G _ j]
  exact tail_regular _ hK (tailDeg (R := R) K ι j) _ hm hi

def cM (K : Fin D.mesh.count) (P' : PotentialData (CellVars D R K)) (xu : CellVars D R K → ℂ)
    (a b : D.mesh.resolved K) (i : Fin 12) (p : ℝ × ℝ) : ℂ :=
  ∑ j, P'.couplingModel (b.1 - a.1) p i j * lowProfile D R K a xu p j

def cL (K : Fin D.mesh.count) (xu : CellVars D R K → ℂ) (b : D.mesh.resolved K) (i : Fin 12) (p : ℝ × ℝ) : ℂ :=
  ∑ j, (R.leaves K).localMatrix b.1 p i j * lowProfile D R K b xu p j

def hvec (K : Fin D.mesh.count) (P' : PotentialData (CellVars D R K)) (xu : CellVars D R K → ℂ)
    (b : D.mesh.resolved K) (i : Fin 12) (p : ℝ × ℝ) : ℂ :=
  (∑ a : D.mesh.resolved K, cM K P' xu a b i p) + cL K xu b i p

theorem cM_continuousOn {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (xu : CellVars D R K → ℂ)
    (a b : D.mesh.resolved K) (i : Fin 12) :
    ContinuousOn (cM K (P.potential K) xu a b i) (D.mesh.box K).rect :=
  continuousOn_finsetSum _ fun j _ =>
    (coupling_continuousOn hP K _ i j).mul (lowProfile_continuous K a xu j).continuousOn

theorem bounded_of_continuousOn {f : ℝ × ℝ → ℂ} {Kb : CellBox} (hf : ContinuousOn f Kb.rect) :
    AEStronglyMeasurable f (volume.restrict Kb.rect) ∧ ∃ C, ∀ p ∈ Kb.rect, ‖f p‖ ≤ C :=
  ⟨hf.aestronglyMeasurable (rect_measurableSet Kb), (rect_isCompact Kb).exists_bound_of_continuousOn hf⟩

theorem cL_regular {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) {q : Fin k → ℝ} (hq : q ∈ D.cert.params) (K : Fin D.mesh.count)
    (xu : CellVars D R K → ℂ) (b : D.mesh.resolved K) (i : Fin 12) :
    AEStronglyMeasurable (cL K xu b i) (volume.restrict (D.mesh.box K).rect) ∧
      ∃ C, ∀ p ∈ (D.mesh.box K).rect, ‖cL K xu b i p‖ ≤ C := by
  obtain ⟨hLm, CL, hCL⟩ := (hP.cell_conditions.leaves_valid K q hq).matrix_regular b.1 b.2
  have hU : ∀ j, ∃ C, ∀ p ∈ (D.mesh.box K).rect, ‖lowProfile D R K b xu p j‖ ≤ C := fun j =>
    (rect_isCompact _).exists_bound_of_continuousOn (lowProfile_continuous K b xu j).continuousOn
  choose CU hCU using hU
  refine ⟨?_, ⟨∑ j, max CL 0 * max (CU j) 0, fun p hp => ?_⟩⟩
  · have : Measurable (cL K xu b i) := by
      unfold cL
      exact Finset.measurable_sum _ fun j _ => (hLm i j).mul (lowProfile_continuous K b xu j).measurable
    exact this.aestronglyMeasurable
  · unfold cL
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul]
    exact mul_le_mul (le_max_of_le_left (hCL p hp i j)) (le_max_of_le_left (hCU j p hp)) (norm_nonneg _)
      (le_max_right _ _)

theorem hvec_regular {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) {q : Fin k → ℝ} (hq : q ∈ D.cert.params) (K : Fin D.mesh.count)
    (xu : CellVars D R K → ℂ) (b : D.mesh.resolved K) (i : Fin 12) :
    AEStronglyMeasurable (hvec K (P.potential K) xu b i) (volume.restrict (D.mesh.box K).rect) ∧
      ∃ C, ∀ p ∈ (D.mesh.box K).rect, ‖hvec K (P.potential K) xu b i p‖ ≤ C := by
  have hc : ContinuousOn (fun p => ∑ a : D.mesh.resolved K, cM K (P.potential K) xu a b i p) (D.mesh.box K).rect :=
    continuousOn_finsetSum _ fun a _ => cM_continuousOn hP K xu a b i
  obtain ⟨hm1, C1, hC1⟩ := bounded_of_continuousOn hc
  obtain ⟨hm2, C2, hC2⟩ := cL_regular hP hq K xu b i
  refine ⟨hm1.add hm2, C1 + C2, fun p hp => ?_⟩
  exact le_trans (norm_add_le _ _) (add_le_add (hC1 p hp) (hC2 p hp))

theorem sesq12_re_expand (N : Matrix (Fin 12) (Fin 12) ℂ) (Y X : Fin 12 → ℂ) :
    (sesq12 N Y X).re = ∑ i, ((starRingEnd ℂ) (Y i) * ∑ j, N i j * X j).re := by
  unfold sesq12
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem model_term_eq {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (xu : CellVars D R K → ℂ)
    (T : ℝ × ℝ → Fin 12 → ℂ) (a b : D.mesh.resolved K) {p : ℝ × ℝ} (hp : p ∈ (D.mesh.box K).rect) :
    p.1 * (sesq12 ((P.potential K).couplingModel (a.1 - b.1) p) (lowProfile D R K a xu p) (T p)).re
      = ∑ i, p.1 * ((starRingEnd ℂ) (T p i) * cM K (P.potential K) xu a b i p).re := by
  rw [model_sym hP K (a.1 - b.1) hp, neg_sub, sesq12_re_expand, Finset.mul_sum]
  rfl

theorem leaf_term_eq {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) {q : Fin k → ℝ} (hq : q ∈ D.cert.params) (K : Fin D.mesh.count)
    (xu : CellVars D R K → ℂ) (T : ℝ × ℝ → Fin 12 → ℂ) (b : D.mesh.resolved K) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) :
    p.1 * (sesq12 ((R.leaves K).localMatrix b.1 p) (lowProfile D R K b xu p) (T p)).re
      = ∑ i, p.1 * ((starRingEnd ℂ) (T p i) * cL K xu b i p).re := by
  rw [selfAdjoint_sesq_re_symm ((hP.cell_conditions.leaves_valid K q hq).matrix_hermitian b.1 b.2 p hp), sesq12_re_expand,
    Finset.mul_sum]
  rfl

theorem per_mode_identity {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (xu : CellVars D R K → ℂ)
    (b : D.mesh.resolved K) :
    (∑ a : D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
        p.1 * (sesq12 ((P.potential K).couplingModel (a.1 - b.1) p) (lowProfile D R K a xu p)
          (tailProfile D R K b.1 v G p)).re)
      + ∫ p in (D.mesh.box K).rect,
        p.1 * (sesq12 ((R.leaves K).localMatrix b.1 p) (lowProfile D R K b xu p) (tailProfile D R K b.1 v G p)).re
      = ∑ i, ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * hvec K (P.potential K) xu b i p).re := by
  have hK := hP.mesh_valid.box_valid K
  have hs := rect_measurableSet (D.mesh.box K)
  have hT := fun i => tail_component_regular hP hreg ht b.1 i
  have hMreg := fun a i => bounded_of_continuousOn (cM_continuousOn hP K xu a b i)
  have hLreg := fun i => cL_regular hP ht.param K xu b i
  have hA : ∀ a : D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
      p.1 * (sesq12 ((P.potential K).couplingModel (a.1 - b.1) p) (lowProfile D R K a xu p)
        (tailProfile D R K b.1 v G p)).re
      = ∑ i, ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * cM K (P.potential K) xu a b i p).re := by
    intro a
    rw [setIntegral_congr_fun hs (fun p hp => model_term_eq hP K xu (fun p => tailProfile D R K b.1 v G p) a b hp)]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hm, C, hC⟩ := hMreg a i
    exact cross_integrable _ hK (hT i).1 (hT i).2 hm hC
  have hB : ∫ p in (D.mesh.box K).rect,
      p.1 * (sesq12 ((R.leaves K).localMatrix b.1 p) (lowProfile D R K b xu p) (tailProfile D R K b.1 v G p)).re
      = ∑ i, ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * cL K xu b i p).re := by
    rw [setIntegral_congr_fun hs (fun p hp => leaf_term_eq hP ht.param K xu (fun p => tailProfile D R K b.1 v G p) b hp)]
    refine integral_finsetSum _ fun i _ => ?_
    obtain ⟨hm, C, hC⟩ := hLreg i
    exact cross_integrable _ hK (hT i).1 (hT i).2 hm hC
  have hH : ∀ i, ∫ p in (D.mesh.box K).rect,
      p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * hvec K (P.potential K) xu b i p).re
      = (∑ a : D.mesh.resolved K, ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * cM K (P.potential K) xu a b i p).re)
        + ∫ p in (D.mesh.box K).rect,
          p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * cL K xu b i p).re := by
    intro i
    have hc : ContinuousOn (fun p => ∑ a : D.mesh.resolved K, cM K (P.potential K) xu a b i p) (D.mesh.box K).rect :=
      continuousOn_finsetSum _ fun a _ => cM_continuousOn hP K xu a b i
    obtain ⟨hm1, C1, hC1⟩ := bounded_of_continuousOn hc
    obtain ⟨hm2, C2, hC2⟩ := hLreg i
    have e : (fun p => p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * hvec K (P.potential K) xu b i p).re)
        = fun p => p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i)
            * ∑ a : D.mesh.resolved K, cM K (P.potential K) xu a b i p).re
          + p.1 * ((starRingEnd ℂ) (tailProfile D R K b.1 v G p i) * cL K xu b i p).re := by
      funext p
      simp only [hvec, mul_add, Complex.add_re]
    rw [e, integral_add (cross_integrable _ hK (hT i).1 (hT i).2 hm1 hC1)
      (cross_integrable _ hK (hT i).1 (hT i).2 hm2 hC2)]
    congr 1
    exact cross_sum _ hK Finset.univ (fun a => cM K (P.potential K) xu a b i) (hT i).1 (hT i).2
      (fun a => (hMreg a i).1) (fun a => (hMreg a i).2)
  rw [Finset.sum_congr rfl fun a _ => hA a, hB, Finset.sum_comm, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => (hH i).symm

theorem sum_resolved {K : Fin D.mesh.count} {M : Type} [AddCommMonoid M] (f : ℤ × ℤ → M) :
    ∑ a ∈ D.mesh.resolved K, f a = ∑ a : D.mesh.resolved K, f a.1 :=
  (Finset.sum_coe_sort (D.mesh.resolved K) f).symm

theorem upperProfiles_val (K : Fin D.mesh.count) (P' : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (a : D.mesh.resolved K) :
    upperProfiles D R K P' x a.1 = lowProfile D R K a (upperPart D R K P' x) := by
  funext p
  simp only [upperProfiles, lowAt, dif_pos a.2]

theorem tailProfiles_val (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (b : D.mesh.resolved K) :
    tailProfiles D R K v G b.1 = fun p => tailProfile D R K b.1 v G p := by
  funext p
  simp only [tailProfiles, restrictTo, Finset.mem_coe, b.2, if_true]

end Breakdown.CertCell.Assembly.Internal.PotentialTails

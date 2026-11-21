import Breakdown.CertCell.AssemblyPotentialTailsModes
import Breakdown.FracCell.LowEntry

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

section SplitHelpers

open PotentialTails

attribute [local instance] rect_finite

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}

private def absorbDensity (cA sA vA : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  cA * curlSq (strainOfVec U) + sA * sumSq (strainOfVec U) + vA * vecSq (velOf U)

private def absorbCross (cA sA vA : ℝ) (U V : Fin 12 → ℂ) : ℝ :=
  cA * ∑ i : Fin 3, (curlComp (strainOfVec V) i * (starRingEnd ℂ) (curlComp (strainOfVec U) i)).re
    + sA * ∑ a : Fin 3, ∑ b : Fin 3, (strainOfVec V a b * (starRingEnd ℂ) (strainOfVec U a b)).re
    + vA * ∑ a : Fin 3, (velOf V a * (starRingEnd ℂ) (velOf U a)).re

private theorem norm_add_sq_expand (a b : ℂ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 + 2 * (b * (starRingEnd ℂ) a).re := by
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, Complex.normSq_add]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private theorem strainOfVec_add (U V : Fin 12 → ℂ) (a b : Fin 3) :
    strainOfVec (U + V) a b = strainOfVec U a b + strainOfVec V a b := rfl

private theorem velOf_add (U V : Fin 12 → ℂ) (a : Fin 3) : velOf (U + V) a = velOf U a + velOf V a := rfl

private theorem curlComp_add (s t : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp (fun a b => s a b + t a b) i = curlComp s i + curlComp t i := by
  unfold curlComp
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem absorbDensity_add (cA sA vA : ℝ) (U V : Fin 12 → ℂ) :
    absorbDensity cA sA vA (U + V)
      = absorbDensity cA sA vA U + absorbDensity cA sA vA V + 2 * absorbCross cA sA vA U V := by
  have hs : strainOfVec (U + V) = fun a b => strainOfVec U a b + strainOfVec V a b := rfl
  have hv : velOf (U + V) = fun a => velOf U a + velOf V a := rfl
  have hc : ∀ i, ‖curlComp (strainOfVec (U + V)) i‖ ^ 2 = ‖curlComp (strainOfVec U) i‖ ^ 2
      + ‖curlComp (strainOfVec V) i‖ ^ 2
      + 2 * (curlComp (strainOfVec V) i * (starRingEnd ℂ) (curlComp (strainOfVec U) i)).re := by
    intro i
    rw [hs, curlComp_add, norm_add_sq_expand]
  unfold absorbDensity absorbCross curlSq sumSq vecSq
  simp only [hc]
  rw [hs, hv]
  simp only [norm_add_sq_expand, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

private def NullOn (S : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℝ) : Prop := IntegrableOn f S ∧ ∫ p in S, f p = 0

private theorem nullOn_congr {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (h : ∀ p, f p = g p) (hg : NullOn S g) :
    NullOn S f := by
  have e : f = g := funext h
  rw [e]
  exact hg

private theorem nullOn_add {S : Set (ℝ × ℝ)} {f g : ℝ × ℝ → ℝ} (hf : NullOn S f) (hg : NullOn S g) :
    NullOn S (fun p => f p + g p) :=
  ⟨Integrable.add hf.1 hg.1, by rw [integral_add hf.1 hg.1, hf.2, hg.2, add_zero]⟩

private theorem nullOn_mul {S : Set (ℝ × ℝ)} {f : ℝ × ℝ → ℝ} (c : ℝ) (hf : NullOn S f) :
    NullOn S (fun p => c * f p) :=
  ⟨Integrable.const_mul hf.1 c, by rw [integral_const_mul, hf.2, mul_zero]⟩

private theorem nullOn_sum {S : Set (ℝ × ℝ)} {β : Type} (s : Finset β) (f : β → ℝ × ℝ → ℝ)
    (hf : ∀ i ∈ s, NullOn S (f i)) : NullOn S (fun p => ∑ i ∈ s, f i p) :=
  ⟨integrable_finsetSum s fun i hi => (hf i hi).1, by
    rw [integral_finsetSum s fun i hi => (hf i hi).1]
    exact Finset.sum_eq_zero fun i hi => (hf i hi).2⟩

private theorem weighted_product_integrable (Kb : CellBox) (hK : IsCellBox Kb) {T c : ℝ × ℝ → ℂ}
    (hTm : AEStronglyMeasurable T (volume.restrict Kb.rect))
    (hT2 : IntegrableOn (fun p => Kb.lineWeight p.1 * ‖T p‖ ^ 2) Kb.rect) (hc : Continuous c) :
    IntegrableOn (fun p => ((Kb.lineWeight p.1 : ℝ) : ℂ) * T p * c p) Kb.rect := by
  have hs := rect_measurableSet Kb
  have hwc : Continuous fun p : ℝ × ℝ => Kb.lineWeight p.1 := (lineWeight_continuous Kb).comp continuous_fst
  obtain ⟨Cw, hCw⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hwc.continuousOn
  obtain ⟨Cc, hCc⟩ := (rect_isCompact Kb).exists_bound_of_continuousOn hc.continuousOn
  have hw1 : IntegrableOn (fun p : ℝ × ℝ => Kb.lineWeight p.1) Kb.rect := by
    refine Integrable.mono' (integrable_const Cw) hwc.aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hs fun p hp => hCw p hp
  refine Integrable.mono' (((hw1.add hT2).div_const 2).mul_const (max Cc 0))
    (((Complex.continuous_ofReal.comp hwc).aestronglyMeasurable.mul hTm).mul hc.aestronglyMeasurable) ?_
  refine ae_restrict_of_forall_mem hs fun p hp => ?_
  have h0 := lineWeight_nonneg Kb hK hp
  have h1 : ‖c p‖ ≤ max Cc 0 := le_max_of_le_left (hCc p hp)
  have h2 : ‖T p‖ ≤ (1 + ‖T p‖ ^ 2) / 2 := by nlinarith [sq_nonneg (‖T p‖ - 1)]
  have h3 : Kb.lineWeight p.1 * ‖T p‖ ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]
  show ‖((Kb.lineWeight p.1 : ℝ) : ℂ) * T p * c p‖
    ≤ (Kb.lineWeight p.1 + Kb.lineWeight p.1 * ‖T p‖ ^ 2) / 2 * max Cc 0
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0]
  exact mul_le_mul h3 h1 (norm_nonneg _) (by nlinarith [norm_nonneg (T p)])

private theorem lowProfile_add (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x y : CellVars D R K → ℂ)
    (p : ℝ × ℝ) : lowProfile D R K b (x + y) p = lowProfile D R K b x p + lowProfile D R K b y p := by
  funext j
  simp only [Pi.add_apply]
  unfold lowProfile pairVec lowGrad lowVel lowStrainOf lowVelocityOf restrictData
  split_ifs <;> simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem strain_lowProfile (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x : CellVars D R K → ℂ)
    (p : ℝ × ℝ) (a c : Fin 3) : strainOfVec (lowProfile D R K b x p) a c = lowGrad D R K b x p a c := by
  unfold strainOfVec gradOf lowProfile
  exact pairVec_grad _ _ a c

private theorem vel_lowProfile (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x : CellVars D R K → ℂ)
    (p : ℝ × ℝ) (a : Fin 3) : velOf (lowProfile D R K b x p) a = lowVel D R K b x p a := by
  unfold velOf lowProfile
  exact pairVec_vel _ _ a

private theorem lowGrad_poly (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x : CellVars D R K → ℂ)
    (a c : Fin 3) : (fun p => lowGrad D R K b x p a c)
      ∈ polyFn ((R.layouts K).layout b.1).degCoef ((R.layouts K).layout b.1).degCoef := by
  unfold lowGrad lowStrainOf
  refine LowEntry.Internal.poly_sum _ _ fun n _ => LowEntry.Internal.poly_sum _ _ fun j _ =>
    LowEntry.Internal.poly_sum _ _ fun l _ => LowEntry.Internal.poly_smul _ ?_
  exact LowEntry.Internal.bas_mem _ (Nat.lt_succ_iff.1 j.2) (Nat.lt_succ_iff.1 l.2)

private theorem lowVel_poly (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x : CellVars D R K → ℂ)
    (a : Fin 3) : (fun p => lowVel D R K b x p a)
      ∈ polyFn (((R.layouts K).layout b.1).degCoef - 1) (((R.layouts K).layout b.1).degCoef - 1) := by
  unfold lowVel lowVelocityOf
  refine LowEntry.Internal.poly_sum _ _ fun n _ => LowEntry.Internal.poly_sum _ _ fun j _ =>
    LowEntry.Internal.poly_sum _ _ fun l _ => LowEntry.Internal.poly_smul _ ?_
  exact LowEntry.Internal.bas_mem _ (by have := j.2; omega) (by have := l.2; omega)

private theorem curl_poly {d d' : ℕ} {S : ℝ × ℝ → Fin 3 → Fin 3 → ℂ}
    (hS : ∀ a c, (fun p => S p a c) ∈ polyFn d d') (i : Fin 3) : (fun p => curlComp (S p) i) ∈ polyFn d d' := by
  unfold curlComp
  exact LowEntry.Internal.poly_sum _ _ fun j _ => LowEntry.Internal.poly_sum _ _ fun l _ =>
    LowEntry.Internal.poly_smul _ (hS l j)

private theorem curl_cross_expand (w : ℝ) (t : Fin 3 → Fin 3 → ℂ) (c : ℂ) (i : Fin 3) :
    w * (curlComp t i * (starRingEnd ℂ) c).re
      = ∑ j : Fin 3, ∑ l : Fin 3, w * (t l j * (starRingEnd ℂ) ((CellCert.permSign i j l : ℂ) * c)).re := by
  unfold curlComp
  rw [Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul, Complex.re_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_mul, Complex.conj_ofReal]
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im]
  ring

variable {A : AssemblyEntry D R} {P : CouplingEntries D R}

private theorem tail_term {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K)
    (j : Fin 12) {Q : ℝ × ℝ → ℂ} (hQ : Q ∈ polyFn (tailDeg (R := R) K ι j) (tailDeg (R := R) K ι j)) :
    NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
      (tailProfile D R K ι v G p j * (starRingEnd ℂ) (Q p)).re) := by
  have hK : IsCellBox (D.mesh.box K) := hP.mesh_valid.box_valid K
  obtain ⟨hTm, hT2⟩ := tail_component_regular hP hreg ht ι j
  obtain ⟨hFm, hFi⟩ := component_regular hP hreg ht ι j
  have horth := proj_orth_of_sq (D.mesh.box K) hK _ (bases_valid_of hP K hι) (tailDeg (R := R) K ι j) _ hFm hFi Q hQ
  have hci := weighted_product_integrable (D.mesh.box K) hK hTm hT2
    (Complex.continuous_conj.comp (polyFn_continuous hQ))
  have e : (fun p => (D.mesh.box K).lineWeight p.1 * (tailProfile D R K ι v G p j * (starRingEnd ℂ) (Q p)).re)
      = fun p => (((D.mesh.box K).lineWeight p.1 : ℂ) * tailProfile D R K ι v G p j * (starRingEnd ℂ) (Q p)).re := by
    funext p
    rw [mul_assoc, Complex.re_ofReal_mul]
  have hpair : ∫ p in (D.mesh.box K).rect,
        ((D.mesh.box K).lineWeight p.1 : ℂ) * tailProfile D R K ι v G p j * (starRingEnd ℂ) (Q p)
      = (D.mesh.box K).pairOn (D.mesh.box K).lineWeightFn
          (fun p => bandProfile D ι v G p j - (D.mesh.box K).proj (tailDeg (R := R) K ι j) (tailDeg (R := R) K ι j)
            (fun p' => bandProfile D ι v G p' j) p) Q := by
    unfold CellBox.pairOn CellBox.lineWeightFn
    simp only [tailProfile_apply]
  have hre := integral_re hci
  simp only [RCLike.re_to_complex, Function.comp_apply] at hre
  rw [e]
  refine ⟨hci.re, ?_⟩
  beta_reduce
  rw [hre, hpair, horth, Complex.zero_re]

private theorem absorbDensity_continuous (cA sA vA : ℝ) : Continuous (absorbDensity cA sA vA) := by
  unfold absorbDensity curlSq sumSq vecSq curlComp strainOfVec gradOf velOf
  fun_prop

private theorem absorbDensity_abs_le (cA sA vA : ℝ) (U : Fin 12 → ℂ) :
    |absorbDensity cA sA vA U| ≤ (2 * |cA| + |sA| + |vA|) * ∑ j, ‖U j‖ ^ 2 := by
  have htot : ∑ j, ‖U j‖ ^ 2 = sumSq (strainOfVec U) + vecSq (velOf U) := by
    rw [sum_fin12 (fun j => ‖U j‖ ^ 2)]
    rfl
  have h1 := curlSq_le_two (strainOfVec U)
  have hc : 0 ≤ curlSq (strainOfVec U) := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hs : 0 ≤ sumSq (strainOfVec U) := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have hv : 0 ≤ vecSq (velOf U) := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [htot]
  unfold absorbDensity
  have e1 : |cA * curlSq (strainOfVec U)| ≤ |cA| * (2 * sumSq (strainOfVec U)) := by
    rw [abs_mul, abs_of_nonneg hc]
    exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
  have e2 : |sA * sumSq (strainOfVec U)| = |sA| * sumSq (strainOfVec U) := by rw [abs_mul, abs_of_nonneg hs]
  have e3 : |vA * vecSq (velOf U)| = |vA| * vecSq (velOf U) := by rw [abs_mul, abs_of_nonneg hv]
  calc _ ≤ |cA * curlSq (strainOfVec U)| + |sA * sumSq (strainOfVec U)| + |vA * vecSq (velOf U)| :=
        abs_add_three _ _ _
    _ ≤ _ := by
        rw [e2, e3]
        nlinarith [abs_nonneg cA, abs_nonneg sA, abs_nonneg vA, mul_nonneg (abs_nonneg sA) hv,
          mul_nonneg (abs_nonneg vA) hs, mul_nonneg (abs_nonneg cA) hv]

private theorem tail_density_integrable {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) (ι : ℤ × ℤ) (cA sA vA : ℝ) :
    IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (tailProfile D R K ι v G p))
      (D.mesh.box K).rect := by
  have hK := hP.mesh_valid.box_valid K
  have hreg' := fun j => tail_component_regular hP hreg ht ι j
  have hZm : AEStronglyMeasurable (fun p => tailProfile D R K ι v G p) (volume.restrict (D.mesh.box K).rect) :=
    (aemeasurable_pi_iff.2 fun j => (hreg' j).1.aemeasurable).aestronglyMeasurable
  have hsum : IntegrableOn
      (fun p => ∑ j, (D.mesh.box K).lineWeight p.1 * ‖tailProfile D R K ι v G p j‖ ^ 2) (D.mesh.box K).rect :=
    integrable_finsetSum _ fun j _ => (hreg' j).2
  have hwc : Continuous fun p : ℝ × ℝ => (D.mesh.box K).lineWeight p.1 :=
    (lineWeight_continuous _).comp continuous_fst
  refine Integrable.mono' (hsum.const_mul (2 * |cA| + |sA| + |vA|))
    (hwc.aestronglyMeasurable.mul ((absorbDensity_continuous cA sA vA).comp_aestronglyMeasurable hZm)) ?_
  refine ae_restrict_of_forall_mem (rect_measurableSet _) fun p hp => ?_
  have h0 := lineWeight_nonneg _ hK hp
  have h1 := absorbDensity_abs_le cA sA vA (tailProfile D R K ι v G p)
  show ‖(D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (tailProfile D R K ι v G p)‖
    ≤ (2 * |cA| + |sA| + |vA|) * ∑ j, (D.mesh.box K).lineWeight p.1 * ‖tailProfile D R K ι v G p j‖ ^ 2
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, ← Finset.mul_sum]
  calc _ ≤ (D.mesh.box K).lineWeight p.1 * ((2 * |cA| + |sA| + |vA|) * ∑ j, ‖tailProfile D R K ι v G p j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

private theorem low_density_integrable (K : Fin D.mesh.count) (b : D.mesh.resolved K) (x : CellVars D R K → ℂ)
    (cA sA vA : ℝ) :
    IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (lowProfile D R K b x p))
      (D.mesh.box K).rect :=
  (((lineWeight_continuous _).comp continuous_fst).mul ((absorbDensity_continuous cA sA vA).comp
    (continuous_pi fun j => lowProfile_continuous K b x j))).continuousOn.integrableOn_compact (rect_isCompact _)

private theorem cross_null {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K)
    (xb : CellVars D R K → ℂ) (cA sA vA : ℝ) :
    NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
      (2 * absorbCross cA sA vA (lowProfile D R K ⟨ι, hι⟩ xb p) (tailProfile D R K ι v G p))) := by
  have hsY : ∀ p, strainOfVec (lowProfile D R K ⟨ι, hι⟩ xb p) = fun a c => lowGrad D R K ⟨ι, hι⟩ xb p a c :=
    fun p => funext fun a => funext fun c => strain_lowProfile K ⟨ι, hι⟩ xb p a c
  have hdegS : ∀ a c : Fin 3, tailDeg (R := R) K ι ⟨3 * a.val + c.val, by omega⟩
      = ((R.layouts K).layout ι).degCoef := by
    intro a c
    unfold tailDeg
    rw [if_pos (by show 3 * a.val + c.val < 9; omega)]
  have hdegV : ∀ a : Fin 3, tailDeg (R := R) K ι ⟨9 + a.val, by omega⟩
      = ((R.layouts K).layout ι).degCoef - 1 := by
    intro a
    unfold tailDeg
    rw [if_neg (by show ¬ (9 + a.val < 9); omega)]
  have hstrain : ∀ a c : Fin 3, NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
      (strainOfVec (tailProfile D R K ι v G p) a c
        * (starRingEnd ℂ) (strainOfVec (lowProfile D R K ⟨ι, hι⟩ xb p) a c)).re) := by
    intro a c
    have hQ : (fun p => lowGrad D R K ⟨ι, hι⟩ xb p a c) ∈ polyFn (tailDeg (R := R) K ι ⟨3 * a.val + c.val, by omega⟩)
        (tailDeg (R := R) K ι ⟨3 * a.val + c.val, by omega⟩) := by
      rw [hdegS]
      exact lowGrad_poly K ⟨ι, hι⟩ xb a c
    refine nullOn_congr (fun p => ?_) (tail_term hP hreg ht hι _ hQ)
    rw [strain_lowProfile]
    rfl
  have hvel : ∀ a : Fin 3, NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
      (velOf (tailProfile D R K ι v G p) a * (starRingEnd ℂ) (velOf (lowProfile D R K ⟨ι, hι⟩ xb p) a)).re) := by
    intro a
    have hQ : (fun p => lowVel D R K ⟨ι, hι⟩ xb p a) ∈ polyFn (tailDeg (R := R) K ι ⟨9 + a.val, by omega⟩)
        (tailDeg (R := R) K ι ⟨9 + a.val, by omega⟩) := by
      rw [hdegV]
      exact lowVel_poly K ⟨ι, hι⟩ xb a
    refine nullOn_congr (fun p => ?_) (tail_term hP hreg ht hι _ hQ)
    rw [vel_lowProfile]
    rfl
  have hcurl : ∀ i : Fin 3, NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
      (curlComp (strainOfVec (tailProfile D R K ι v G p)) i
        * (starRingEnd ℂ) (curlComp (strainOfVec (lowProfile D R K ⟨ι, hι⟩ xb p)) i)).re) := by
    intro i
    have hterm : ∀ j l : Fin 3, NullOn (D.mesh.box K).rect (fun p => (D.mesh.box K).lineWeight p.1 *
        (tailProfile D R K ι v G p ⟨3 * l.val + j.val, by omega⟩ * (starRingEnd ℂ)
          ((CellCert.permSign i j l : ℂ) * curlComp (fun a c => lowGrad D R K ⟨ι, hι⟩ xb p a c) i)).re) := by
      intro j l
      have hQ : (fun p => (CellCert.permSign i j l : ℂ) * curlComp (fun a c => lowGrad D R K ⟨ι, hι⟩ xb p a c) i)
          ∈ polyFn (tailDeg (R := R) K ι ⟨3 * l.val + j.val, by omega⟩)
            (tailDeg (R := R) K ι ⟨3 * l.val + j.val, by omega⟩) := by
        rw [hdegS]
        exact LowEntry.Internal.poly_smul _ (curl_poly (fun a c => lowGrad_poly K ⟨ι, hι⟩ xb a c) i)
      exact tail_term hP hreg ht hι _ hQ
    refine nullOn_congr (fun p => ?_)
      (nullOn_sum Finset.univ _ fun j _ => nullOn_sum Finset.univ _ fun l _ => hterm j l)
    rw [hsY p, curl_cross_expand]
    rfl
  refine nullOn_congr (fun p => ?_) (nullOn_mul 2 (nullOn_add (nullOn_add
    (nullOn_mul cA (nullOn_sum Finset.univ _ fun i _ => hcurl i))
    (nullOn_mul sA (nullOn_sum Finset.univ _ fun a _ => nullOn_sum Finset.univ _ fun c _ => hstrain a c)))
    (nullOn_mul vA (nullOn_sum Finset.univ _ fun a _ => hvel a))))
  unfold absorbCross
  simp only [← Finset.mul_sum]
  ring

private theorem mode_identity {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (hreg : CellProfileRegular D)
    {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
    {F Pg : ℝ → Space → Space} (ht : IsCellTuple D K q v G H g κ F Pg) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K)
    (P' : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (hae : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
      trueProfiles D v G ι p = lowAt D R K x ι p + tailProfile D R K ι v G p)
    (cA sA vA : ℝ) :
    ∫ p in (D.mesh.box K).rect, (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (otherProfiles D R K P' x v G ι p)
      = (∫ p in (D.mesh.box K).rect,
          (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (lowAt D R K (bandPart D R K P' x) ι p))
        + ∫ p in (D.mesh.box K).rect,
          (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (tailProfiles D R K v G ι p) := by
  have hlow : ∀ (y : CellVars D R K → ℂ) p, lowAt D R K y ι p = lowProfile D R K ⟨ι, hι⟩ y p :=
    fun y p => by simp only [lowAt, dif_pos hι]
  have htail : ∀ p, tailProfiles D R K v G ι p = tailProfile D R K ι v G p := fun p => by
    simp only [tailProfiles, restrictTo, Finset.mem_coe, hι, if_true]
  have hsplit : ∀ p, lowProfile D R K ⟨ι, hι⟩ x p = lowProfile D R K ⟨ι, hι⟩ (upperPart D R K P' x) p
      + lowProfile D R K ⟨ι, hι⟩ (bandPart D R K P' x) p := by
    intro p
    rw [← lowProfile_add]
    congr 1
    simp only [upperPart, bandPart, sub_add_cancel]
  have hY := low_density_integrable K ⟨ι, hι⟩ (bandPart D R K P' x) cA sA vA
  have hZ := tail_density_integrable hP hreg ht ι cA sA vA
  have hX := cross_null hP hreg ht hι (bandPart D R K P' x) cA sA vA
  simp only [hlow, htail]
  calc ∫ p in (D.mesh.box K).rect,
        (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (otherProfiles D R K P' x v G ι p)
      = ∫ p in (D.mesh.box K).rect,
          (((D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (lowProfile D R K ⟨ι, hι⟩ (bandPart D R K P' x) p)
            + (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (tailProfile D R K ι v G p))
          + (D.mesh.box K).lineWeight p.1 * (2 * absorbCross cA sA vA
              (lowProfile D R K ⟨ι, hι⟩ (bandPart D R K P' x) p) (tailProfile D R K ι v G p))) := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with p hp
        have e : otherProfiles D R K P' x v G ι p
            = lowProfile D R K ⟨ι, hι⟩ (bandPart D R K P' x) p + tailProfile D R K ι v G p := by
          show trueProfiles D v G ι p - upperProfiles D R K P' x ι p = _
          rw [hp, hlow, upperProfiles, hlow, hsplit]
          abel
        rw [e, absorbDensity_add]
        ring
    _ = _ := by
        have hYZ : IntegrableOn (fun p => (D.mesh.box K).lineWeight p.1
            * absorbDensity cA sA vA (lowProfile D R K ⟨ι, hι⟩ (bandPart D R K P' x) p)
            + (D.mesh.box K).lineWeight p.1 * absorbDensity cA sA vA (tailProfile D R K ι v G p))
            (D.mesh.box K).rect := Integrable.add hY hZ
        rw [integral_add hYZ hX.1, integral_add hY hZ, hX.2, add_zero]

end SplitHelpers

theorem absorb_split {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (P : CouplingEntries D R) (hreg : AssemblyRegular D R) (htrue : TrueFieldRegular D)
    {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hchk : PotentialConditions D R A P states) (hLT : LowTailSplit D R) (K : Fin D.mesh.count) (q : Fin k → ℝ)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (κ : Fin k → ℝ)
    (F Pg : ℝ → Space → Space) (ht : IsCellTuple D K q v G H g κ F Pg) (ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) :
    alAmount D R K (otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G)
      = alAmount D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
        + alAmount D R K (tailProfiles D R K v G) := by
  unfold alAmount
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι hι => ?_
  have h := mode_identity hchk htrue.1 ht hι (P.potential K) _ (hLT K q v G H g κ F Pg ht ζ η ι hι)
    ((R.leaves K).curlAbsorb ι) ((R.leaves K).strainAbsorb ι) ((R.leaves K).velocityAbsorb ι)
  unfold absorbDensity at h
  exact h

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown

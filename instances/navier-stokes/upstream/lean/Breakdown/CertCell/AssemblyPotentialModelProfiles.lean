import Breakdown.CertCell.AssemblyPotentialModelOrthogonal

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge


section FrameBounds

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

def rotMat (A : Space →L[ℝ] Space) (φ : ℝ) : Fin 3 → Fin 3 → ℂ :=
  fun a b => ((axialRot (-φ) (A (axialRot φ (unitVector b))) a : ℝ) : ℂ)

theorem opBound_rotMat (hF : FrameFacts) (A : Space →L[ℝ] Space) (φ c : ℝ) (hA : ‖A‖ ≤ c) :
    IsOpBound c (rotMat A φ) := by
  intro u
  have h := hF.rotated_bound A φ u
  have h2 : ‖A‖ ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hA 2
  have h3 : 0 ≤ cnormSq u := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact h.trans (mul_le_mul_of_nonneg_right h2 h3)

theorem norm_half_add_adjoint (A : Space →L[ℝ] Space) :
    ‖(1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)‖ ≤ ‖A‖ := by
  rw [norm_smul]
  have h1 := norm_add_le A (ContinuousLinearMap.adjoint A)
  rw [LinearIsometryEquiv.norm_map] at h1
  have h0 : ‖(1 / 2 : ℝ)‖ = 1 / 2 := by norm_num
  rw [h0]
  linarith

theorem symOpBound_rotMat (hF : FrameFacts) (A : Space →L[ℝ] Space) (φ c : ℝ) (hA : ‖A‖ ≤ c) :
    IsSymOpBound c (rotMat A φ) := by
  intro u
  have e : (fun i => ∑ j : Fin 3, ((rotMat A φ i j + rotMat A φ j i) / 2) * u j)
      = fun i => ∑ j : Fin 3, rotMat ((1 / 2 : ℝ) • (A + ContinuousLinearMap.adjoint A)) φ i j * u j := by
    funext i
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    simp only [rotMat]
    rw [hF.strain A φ i j]
    push_cast
    ring
  rw [e]
  exact opBound_rotMat hF _ φ c ((norm_half_add_adjoint A).trans hA) u

theorem rotMat_sub (A B : Space →L[ℝ] Space) (φ : ℝ) : rotMat (A - B) φ = rotMat A φ - rotMat B φ := by
  funext a b
  simp only [rotMat, ContinuousLinearMap.sub_apply, Pi.sub_apply]
  rw [← Complex.ofReal_sub]
  congr 1
  fin_cases a <;> simp [axialRot] <;> ring

theorem rotMat_entry_le (hF : FrameFacts) (A : Space →L[ℝ] Space) (φ : ℝ) (a b : Fin 3) :
    ‖rotMat A φ a b‖ ≤ ‖A‖ := by
  have h := hF.rotated_bound A φ (Pi.single b 1)
  have e1 : (fun a' => ∑ b' : Fin 3, ((axialRot (-φ) (A (axialRot φ (unitVector b'))) a' : ℝ) : ℂ) *
      (Pi.single b (1 : ℂ) : Fin 3 → ℂ) b') = fun a' => rotMat A φ a' b := by
    funext a'
    simp [rotMat, Pi.single_apply]
  have e2 : cnormSq (Pi.single b (1 : ℂ) : Fin 3 → ℂ) = 1 := by
    unfold cnormSq
    rw [Finset.sum_eq_single b]
    · simp
    · intro x _ hx
      simp [Pi.single_apply, hx]
    · simp
  rw [e1, e2, mul_one] at h
  have h3 : ‖rotMat A φ a b‖ ^ 2 ≤ ‖A‖ ^ 2 :=
    (Finset.single_le_sum (f := fun a' => ‖rotMat A φ a' b‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)).trans h
  nlinarith [norm_nonneg (rotMat A φ a b), norm_nonneg A]

theorem fibGrad_eq_rotMat (F : ℝ → Space → (Space →L[ℝ] Space)) (y : Space) (τ φ : ℝ) (a b : Fin 3) :
    ((fibGrad F y τ φ a b : ℝ) : ℂ) = rotMat (F τ (axialRot φ y)) φ a b := rfl

end FrameBounds

section Pairs

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def truncCoupling (H : Finset (ℤ × ℤ)) (α : ℤ × ℤ) (p : ℝ × ℝ) : Matrix (Fin 12) (Fin 12) ℂ :=
  if α ∈ H then trueCoupling D α p else 0

theorem sesq12_zero_left (M : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) : sesq12 M 0 U = 0 := by
  simp [sesq12]

theorem sesq12_zero_right (M : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) : sesq12 M U 0 = 0 := by
  simp [sesq12]

theorem sesq12_zero_mat (U U' : Fin 12 → ℂ) : sesq12 0 U U' = 0 := by
  simp [sesq12]

theorem trueStretch_eq_modelPair (K : Fin D.mesh.count) (H S T : Finset (ℤ × ℤ))
    (X Z : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (hX : ∀ ι ∉ S, ∀ p, X ι p = 0) (hZ : ∀ ι ∉ T, ∀ p, Z ι p = 0) :
    trueStretch D K H X Z = modelPair D K (truncCoupling D H) S T X Z := by
  classical
  unfold trueStretch modelPair
  rw [tsum_eq_sum (s := S)]
  · refine Finset.sum_congr rfl fun ι _ => ?_
    have e1 : ∑ α ∈ H, ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 (trueCoupling D α p) (X ι p) (Z (ι - α) p)).re
        = ∑ α ∈ H.filter (fun α => ι - α ∈ T),
            ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 (trueCoupling D α p) (X ι p) (Z (ι - α) p)).re := by
      rw [Finset.sum_filter_of_ne]
      intro α _ hne
      by_contra hT
      apply hne
      simp [hZ _ hT, sesq12_zero_right]
    have e2 : ∑ ι' ∈ T, ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 (truncCoupling D H (ι - ι') p) (X ι p) (Z ι' p)).re
        = ∑ ι' ∈ T.filter (fun ι' => ι - ι' ∈ H),
            ∫ p in (D.mesh.box K).rect, p.1 * (sesq12 (truncCoupling D H (ι - ι') p) (X ι p) (Z ι' p)).re := by
      rw [Finset.sum_filter_of_ne]
      intro ι' _ hne
      by_contra hH
      apply hne
      simp [truncCoupling, hH, sesq12_zero_mat]
    rw [e1, e2]
    refine Finset.sum_nbij' (fun α => ι - α) (fun ι' => ι - ι') ?_ ?_ ?_ ?_ ?_
    · intro α hα
      simp only [Finset.mem_filter] at hα ⊢
      refine ⟨hα.2, ?_⟩
      simpa using hα.1
    · intro ι' hι'
      simp only [Finset.mem_filter] at hι' ⊢
      refine ⟨hι'.2, ?_⟩
      simpa using hι'.1
    · intro α _
      simp
    · intro ι' _
      simp
    · intro α hα
      simp only [Finset.mem_filter] at hα
      have : ι - (ι - α) = α := by abel
      simp [truncCoupling, this, hα.1]
  · intro ι hι
    simp [hX ι hι, sesq12_zero_left]

end Pairs


section AssemblyLemmas

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus
open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation Coercive.StretchInternal

theorem lowSpan_continuous {a b : ℕ} {g : ℝ × ℝ → ℂ} (hg : g ∈ lowSpan a b) : Continuous g := by
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, _, j, _, rfl⟩ := hx
    exact monoFn_continuous i j
  | zero => exact continuous_const
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact continuous_const.mul hx

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem lowProfile_add (K : Fin D.mesh.count) (ι : D.mesh.resolved K) (x y : CellVars D R K → ℂ) (p : ℝ × ℝ) :
    lowProfile D R K ι (x + y) p = lowProfile D R K ι x p + lowProfile D R K ι y p := by
  funext j
  simp only [lowProfile, pairVec, lowGrad, lowVel, lowStrainOf, lowVelocityOf, restrictData, Pi.add_apply]
  split_ifs <;> simp only [add_mul, Finset.sum_add_distrib]

theorem lowAt_add (K : Fin D.mesh.count) (x y : CellVars D R K → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    lowAt D R K (x + y) ι p = lowAt D R K x ι p + lowAt D R K y ι p := by
  unfold lowAt
  split_ifs
  · exact lowProfile_add D R K _ x y p
  · simp

theorem lowAt_split (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K)) (x : CellVars D R K → ℂ)
    (ι : ℤ × ℤ) (p : ℝ × ℝ) :
    lowAt D R K x ι p = lowAt D R K (upperPart D R K P x) ι p + lowAt D R K (bandPart D R K P x) ι p := by
  rw [← lowAt_add]
  congr 1
  simp [upperPart, bandPart]

theorem lowAt_mem_lowSpan (hC : CellCalculusConditions D R) (K : Fin D.mesh.count) (x : CellVars D R K → ℂ)
    (ι : ℤ × ℤ) (j : Fin 12) :
    (fun p => lowAt D R K x ι p j) ∈ lowSpan (D.mesh.maxVolumeDeg K) (D.mesh.maxVolumeDeg K) := by
  unfold lowAt
  by_cases hι : ι ∈ D.mesh.resolved K
  · simp only [hι, dif_pos]
    have hdeg : ((R.layouts K).layout ι).degCoef ≤ D.mesh.maxVolumeDeg K := by
      rw [(hC.layouts_valid K).layout_volumeDeg ι hι]
      exact Finset.le_sup (f := D.mesh.volumeDeg K) hι
    have hb : ∀ (a b : ℕ), a ≤ ((R.layouts K).layout ι).degCoef → b ≤ ((R.layouts K).layout ι).degCoef →
        (fun p : ℝ × ℝ => ((CellCert.CellEnergy.basisFn ((R.layouts K).layout ι).bases a b p : ℝ) : ℂ))
          ∈ lowSpan (D.mesh.maxVolumeDeg K) (D.mesh.maxVolumeDeg K) :=
      fun a b ha hb => lowSpan_mono (ha.trans hdeg) (hb.trans hdeg) (basisFn_mem_lowSpan _ a b)
    simp only [lowProfile, pairVec]
    split_ifs with hj
    · simp only [lowGrad, lowStrainOf]
      refine lowSpan_sum _ _ fun n _ => lowSpan_sum _ _ fun a _ => lowSpan_sum _ _ fun b _ =>
        lowSpan_const_mul _ (hb a b (Nat.lt_succ_iff.1 a.2) (Nat.lt_succ_iff.1 b.2))
    · simp only [lowVel, lowVelocityOf]
      refine lowSpan_sum _ _ fun n _ => lowSpan_sum _ _ fun a _ => lowSpan_sum _ _ fun b _ =>
        lowSpan_const_mul _ (hb a b (Nat.le_of_lt a.2) (Nat.le_of_lt b.2))
  · simp only [hι, dif_neg, not_false_eq_true, Pi.zero_apply]
    exact Submodule.zero_mem _

theorem couplingPair_eq_modelPair (K : Fin D.mesh.count) (P : PotentialData (CellVars D R K))
    (x y : CellVars D R K → ℂ) :
    couplingPair D R K P x y
      = modelPair D K P.couplingModel (D.mesh.resolved K) (D.mesh.resolved K) (lowAt D R K x) (lowAt D R K y) := by
  unfold couplingPair modelPair
  rw [← Finset.sum_coe_sort (D.mesh.resolved K)]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [← Finset.sum_coe_sort (D.mesh.resolved K)]
  refine Finset.sum_congr rfl fun ι' _ => ?_
  simp [lowAt, ι.2, ι'.2]

theorem star_velOf_single (i : Fin 12) : star (velOf (Pi.single i (1 : ℂ))) = velOf (Pi.single i 1) := by
  funext a
  simp only [Pi.star_apply, velOf, Pi.single_apply]
  split_ifs <;> simp

theorem star_gradOf_single (i : Fin 12) : star (gradOf (Pi.single i (1 : ℂ))) = gradOf (Pi.single i 1) := by
  funext ab
  simp only [Pi.star_apply, gradOf, Pi.single_apply]
  split_ifs <;> simp

theorem conj_modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    (starRingEnd ℂ) (modelTriple S Gω a g a' g')
      = modelTriple (fun i j => (starRingEnd ℂ) (S i j)) (fun i j => (starRingEnd ℂ) (Gω i j)) (star a) (star g)
          (star a') (star g') := by
  simp only [modelTriple, modelBilin, curlOfGrad, map_div₀, map_add, map_neg, map_sum, map_mul, Complex.conj_ofReal,
    map_one, map_ofNat, Pi.star_apply, RCLike.star_def]

theorem modelTriple_swap (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : modelTriple S Gω a g a' g' = modelTriple S Gω a' g' a g := by
  simp only [modelTriple, add_comm]

theorem tripleMatrix_conj_neg {S Gω S' Gω' : Fin 3 → Fin 3 → ℂ}
    (hS : ∀ a b, S' a b = (starRingEnd ℂ) (S a b)) (hG : ∀ a b, Gω' a b = (starRingEnd ℂ) (Gω a b)) (i j : Fin 12) :
    tripleMatrix S' Gω' i j = (starRingEnd ℂ) (tripleMatrix S Gω j i) := by
  simp only [tripleMatrix]
  rw [conj_modelTriple, star_star, star_star, star_velOf_single, star_gradOf_single, modelTriple_swap]
  congr 1 <;> funext a b <;> simp [hS, hG]

variable {A : AssemblyEntry D R} {P : CouplingEntries D R}

theorem planeValue_neg_of_conj {count : ℕ} (F : CellMatField count) (box : Fin count → CellBox)
    (hF : F.IsConjugateClosed box) (K : Fin count) (α : ℤ × ℤ) (a b : Fin 3) {p : ℝ × ℝ} (hp : 0 ≤ p.2) :
    F.planeValue box K (-α) a b p = (starRingEnd ℂ) (F.planeValue box K α a b p) := by
  simp only [CellMatField.planeValue, labelValueAt, if_pos hp]
  exact hF.2 K α a b p

theorem couplingModel_neg {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (α : ℤ × ℤ) {p : ℝ × ℝ}
    (hp : p ∈ (D.mesh.box K).rect) (i j : Fin 12) :
    (P.potential K).couplingModel (-α) p i j = (starRingEnd ℂ) ((P.potential K).couplingModel α p j i) := by
  have hK := hP.mesh_valid.box_valid K
  have hz : 0 ≤ p.2 := hK.z_order.1.trans (Set.mem_prod.1 hp).2.1
  have hcc := (hP.cell_conditions.model_split K).model_conj_closed
  rw [matrix_eq_tripleMatrix_of_sesq (hP.coupling_model K (-α) p hp),
    matrix_eq_tripleMatrix_of_sesq (hP.coupling_model K α p hp)]
  exact tripleMatrix_conj_neg (fun a b => planeValue_neg_of_conj _ _ hcc.2.2.1 K α a b hz)
    (fun a b => planeValue_neg_of_conj _ _ hcc.2.2.2 K α a b hz) i j

theorem bandLinear_eq {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hP : PotentialConditions D R A P states) (K : Fin D.mesh.count) (x : CellVars D R K → ℂ)
    (hx : states K x) (σ : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (hσ : ∀ ι ∈ D.mesh.band K, IsSqOn D K (σ ι))
    (hMb : ∀ α i j, IsBoundedOnCell D K (fun p => (P.potential K).couplingModel α p i j))
    (hXb : ∀ ι j, IsBoundedOnCell D K (fun p => upperProfiles D R K (P.potential K) x ι p j)) :
    bandLinear D K (A.blocks K).potentialSource x σ
      = 2 * modelPair D K (P.potential K).couplingModel (D.mesh.resolved K) (D.mesh.band K)
          (upperProfiles D R K (P.potential K) x) (restrictTo (D.mesh.band K : Set (ℤ × ℤ)) σ) := by
  have hK := hP.mesh_valid.box_valid K
  unfold bandLinear modelPair
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι' hι' => ?_
  have hpt : ∀ p ∈ (D.mesh.box K).rect,
      p.1 * (2 * (∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι') x p j) * σ ι' p j).re)
      = 2 * ∑ ι ∈ D.mesh.resolved K, p.1 * (sesq12 ((P.potential K).couplingModel (ι - ι') p)
          (upperProfiles D R K (P.potential K) x ι p) (restrictTo (D.mesh.band K : Set (ℤ × ℤ)) σ ι' p)).re := by
    intro p hp
    have e1 : ∀ j, linearField ((A.blocks K).potentialSource ι') x p j
        = ∑ ι ∈ D.mesh.resolved K, ∑ j', (P.potential K).couplingModel (ι' - ι) p j j'
            * upperProfiles D R K (P.potential K) x ι p j' := by
      intro j
      rw [hP.source_eq K ι' hι' x hx p j, ← Finset.sum_coe_sort (D.mesh.resolved K)]
      refine Finset.sum_congr rfl fun ι _ => Finset.sum_congr rfl fun j' _ => ?_
      simp [upperProfiles, lowAt, ι.2]
    have e2 : restrictTo (D.mesh.band K : Set (ℤ × ℤ)) σ ι' p = σ ι' p := by
      simp [restrictTo, hι']
    rw [e2]
    have e3 : ∑ j, (starRingEnd ℂ) (linearField ((A.blocks K).potentialSource ι') x p j) * σ ι' p j
        = ∑ ι ∈ D.mesh.resolved K, sesq12 ((P.potential K).couplingModel (ι - ι') p)
            (upperProfiles D R K (P.potential K) x ι p) (σ ι' p) := by
      simp only [e1, map_sum, map_mul, Finset.sum_mul, sesq12]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ι _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun j _ => ?_
      have hn : ι - ι' = -(ι' - ι) := by abel
      rw [hn, couplingModel_neg D R hP K (ι' - ι) hp j' j]
      ring
    rw [e3, Complex.re_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ι _ => ?_
    ring
  rw [setIntegral_congr_fun (rect_measurableSet _) hpt, integral_const_mul,
    integral_finset_sum _ fun ι _ => integrableOn_sesq_re D hK (fun i j => hMb _ i j) (fun i => hXb ι i) (by
      have e : restrictTo (D.mesh.band K : Set (ℤ × ℤ)) σ ι' = σ ι' := by
        funext p
        simp [restrictTo, hι']
      rw [e]
      exact hσ ι' hι')]

end AssemblyLemmas


section SquareIntegrable

open CellCert.CellAnalysis

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem aesm_of_components {μ : Measure (ℝ × ℝ)} {V : ℝ × ℝ → Fin 12 → ℂ}
    (hV : ∀ j, AEStronglyMeasurable (fun p => V p j) μ) {f : (Fin 12 → ℂ) → ℝ} (hf : Continuous f) :
    AEStronglyMeasurable (fun p => f (V p)) μ :=
  (hf.measurable.comp_aemeasurable (aemeasurable_pi_iff.2 fun j => (hV j).aemeasurable)).aestronglyMeasurable

theorem continuous_sum_normSq : Continuous (fun U : Fin 12 → ℂ => ∑ j, ‖U j‖ ^ 2) := by
  fun_prop

theorem isSqOn_of_bounded {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K)) {V : ℝ × ℝ → Fin 12 → ℂ}
    (hV : ∀ j, IsBoundedOnCell D K (fun p => V p j)) : IsSqOn D K V := by
  refine ⟨fun j => (hV j).1, ?_⟩
  have hc : ∀ j, ∃ c : ℝ, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ‖V p j‖ ≤ c :=
    fun j => boundedOnCell_ae_bound D (hV j)
  choose c hc using hc
  refine Integrable.mul_bdd (c := ∑ j, c j ^ 2) (integrableOn_fst _) ?_ ?_
  · exact aesm_of_components (fun j => (hV j).1) continuous_sum_normSq
  · have h := ae_all_iff.2 hc
    filter_upwards [h] with p hp
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hp j) 2

theorem isSqOn_add_smul {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K)) {V W : ℝ × ℝ → Fin 12 → ℂ}
    (hV : IsSqOn D K V) (hW : IsSqOn D K W) (c : ℂ) : IsSqOn D K (fun p => V p + c • W p) := by
  refine ⟨fun j => ?_, ?_⟩
  · refine ((hV.1 j).add ((hW.1 j).const_mul c)).congr (Filter.Eventually.of_forall fun p => ?_)
    simp
  · refine Integrable.mono' (g := fun p => 2 * (p.1 * ∑ j, ‖V p j‖ ^ 2) + 2 * ‖c‖ ^ 2 * (p.1 * ∑ j, ‖W p j‖ ^ 2))
      ((hV.2.const_mul 2).add (hW.2.const_mul _)) ?_ ?_
    · refine continuous_fst.aestronglyMeasurable.mul ?_
      have hc : ∀ j, AEStronglyMeasurable (fun p => (V p + c • W p) j) (volume.restrict (D.mesh.box K).rect) := by
        intro j
        refine ((hV.1 j).add ((hW.1 j).const_mul c)).congr (Filter.Eventually.of_forall fun p => ?_)
        simp
      exact aesm_of_components hc continuous_sum_normSq
    · refine (ae_restrict_iff' (rect_measurableSet _)).2 (Filter.Eventually.of_forall fun p hp => ?_)
      obtain ⟨h0, _⟩ := rect_fst_bounds hK hp
      have hs : ∀ j, ‖(V p + c • W p) j‖ ^ 2 ≤ 2 * ‖V p j‖ ^ 2 + 2 * ‖c‖ ^ 2 * ‖W p j‖ ^ 2 := by
        intro j
        have h1 := norm_add_le (V p j) (c * W p j)
        rw [norm_mul] at h1
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        nlinarith [norm_nonneg (V p j + c * W p j), norm_nonneg (V p j), norm_nonneg c, norm_nonneg (W p j),
          sq_nonneg (‖V p j‖ - ‖c‖ * ‖W p j‖)]
      have hsum : ∑ j, ‖(V p + c • W p) j‖ ^ 2 ≤ 2 * ∑ j, ‖V p j‖ ^ 2 + 2 * ‖c‖ ^ 2 * ∑ j, ‖W p j‖ ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun j _ => hs j
      have hnn : 0 ≤ p.1 * ∑ j, ‖(V p + c • W p) j‖ ^ 2 :=
        mul_nonneg h0 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      rw [Real.norm_of_nonneg hnn]
      nlinarith [mul_le_mul_of_nonneg_left hsum h0]

theorem isSqOn_congr {K : Fin D.mesh.count} {V W : ℝ × ℝ → Fin 12 → ℂ} (hV : IsSqOn D K V)
    (h : ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), V p = W p) : IsSqOn D K W := by
  refine ⟨fun j => (hV.1 j).congr (h.mono fun p hp => congrFun hp j), ?_⟩
  exact hV.2.congr (h.mono fun p hp => by simp only [hp])

theorem chargeForm_continuous (c₁ c₂ c₃ : ℝ) : Continuous (fun U : Fin 12 → ℂ => chargeForm c₁ c₂ c₃ U) := by
  unfold chargeForm cnormSq curlOfGrad gradOf velOf
  fun_prop

theorem cnormSq_gradOf_le (U : Fin 12 → ℂ) : cnormSq (gradOf U) ≤ ∑ j, ‖U j‖ ^ 2 := by
  simp only [cnormSq, gradOf, Fintype.sum_prod_type, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  nlinarith [sq_nonneg ‖U 9‖, sq_nonneg ‖U 10‖, sq_nonneg ‖U 11‖]

theorem cnormSq_velOf_le (U : Fin 12 → ℂ) : cnormSq (velOf U) ≤ ∑ j, ‖U j‖ ^ 2 := by
  simp only [cnormSq, velOf, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp
  nlinarith [sq_nonneg ‖U 0‖, sq_nonneg ‖U 1‖, sq_nonneg ‖U 2‖, sq_nonneg ‖U 3‖, sq_nonneg ‖U 4‖,
    sq_nonneg ‖U 5‖, sq_nonneg ‖U 6‖, sq_nonneg ‖U 7‖, sq_nonneg ‖U 8‖]

theorem cnormSq_curl_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  have e0 : curlOfGrad g 0 = g (2, 1) - g (1, 2) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have e1 : curlOfGrad g 1 = g (0, 2) - g (2, 0) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have e2 : curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
    simp [curlOfGrad, Fin.sum_univ_three, alternatingSymbol]; norm_num; ring
  have hsub : ∀ x y : ℂ, ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
    intro x y
    have h := norm_sub_le x y
    nlinarith [norm_nonneg (x - y), norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖)]
  simp only [cnormSq, Fin.sum_univ_three, Fintype.sum_prod_type, e0, e1, e2]
  nlinarith [hsub (g (2, 1)) (g (1, 2)), hsub (g (0, 2)) (g (2, 0)), hsub (g (1, 0)) (g (0, 1)),
    sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖, sq_nonneg ‖g (2, 2)‖]

theorem abs_chargeForm_le (c₁ c₂ c₃ : ℝ) (U : Fin 12 → ℂ) :
    |chargeForm c₁ c₂ c₃ U| ≤ (2 * |c₁| + |c₂| + |c₃|) * ∑ j, ‖U j‖ ^ 2 := by
  unfold chargeForm
  have h1 := cnormSq_curl_le (gradOf U)
  have h2 := cnormSq_gradOf_le U
  have h3 := cnormSq_velOf_le U
  have n1 : 0 ≤ cnormSq (curlOfGrad (gradOf U)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have n2 : 0 ≤ cnormSq (gradOf U) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have n3 : 0 ≤ cnormSq (velOf U) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg n1, abs_of_nonneg n2, abs_of_nonneg n3]
  have a1 := abs_nonneg c₁
  have a2 := abs_nonneg c₂
  have a3 := abs_nonneg c₃
  nlinarith [mul_le_mul_of_nonneg_left h1 a1, mul_le_mul_of_nonneg_left h2 a1, mul_le_mul_of_nonneg_left h2 a2,
    mul_le_mul_of_nonneg_left h3 a3]

theorem integrableOn_chargeForm {K : Fin D.mesh.count} (hK : IsCellBox (D.mesh.box K)) {V : ℝ × ℝ → Fin 12 → ℂ}
    (hV : IsSqOn D K V) (c₁ c₂ c₃ : ℝ) :
    IntegrableOn (fun p => p.1 * chargeForm c₁ c₂ c₃ (V p)) (D.mesh.box K).rect := by
  have hm : AEMeasurable (fun p => V p) (volume.restrict (D.mesh.box K).rect) :=
    aemeasurable_pi_iff.2 fun j => (hV.1 j).aemeasurable
  have hcm : AEStronglyMeasurable (fun p => chargeForm c₁ c₂ c₃ (V p)) (volume.restrict (D.mesh.box K).rect) :=
    ((chargeForm_continuous c₁ c₂ c₃).measurable.comp_aemeasurable hm).aestronglyMeasurable
  refine Integrable.mono' (g := fun p => (2 * |c₁| + |c₂| + |c₃|) * (p.1 * ∑ j, ‖V p j‖ ^ 2))
    (hV.2.const_mul _) (continuous_fst.aestronglyMeasurable.mul hcm) ?_
  refine (ae_restrict_iff' (rect_measurableSet _)).2 (Filter.Eventually.of_forall fun p hp => ?_)
  obtain ⟨h0, _⟩ := rect_fst_bounds hK hp
  rw [norm_mul, Real.norm_of_nonneg h0, Real.norm_eq_abs]
  have := mul_le_mul_of_nonneg_left (abs_chargeForm_le c₁ c₂ c₃ (V p)) h0
  nlinarith

end SquareIntegrable

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown

import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.InstanceOrthonormal
import Breakdown.CertCell.InstancePairingFormula

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox radialUnit angularUnit axialUnit)

namespace Internal.RowNormIdentity

open Internal.PairingFormula Internal.RowOrthonormal Coercive.Internal.PassageLimit

variable {rowCount : ℕ}

theorem continuous_single_coord (i : Fin 3) : Continuous fun x : ℝ => (EuclideanSpace.single i x : Space) := by
  have h : (fun x : ℝ => (EuclideanSpace.single i x : Space)) = fun x => x • EuclideanSpace.single i (1 : ℝ) := by
    funext x
    ext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  exact continuous_id.smul continuous_const

theorem continuous_frame (c : Fin 3) : Continuous fun θ : ℝ => frameUnit θ c := by
  fin_cases c
  · show Continuous fun θ : ℝ => radialUnit θ
    unfold radialUnit
    exact ((continuous_single_coord 0).comp Real.continuous_cos).add
      ((continuous_single_coord 1).comp Real.continuous_sin)
  · show Continuous fun θ : ℝ => angularUnit θ
    unfold angularUnit
    exact ((continuous_single_coord 0).comp Real.continuous_sin.neg).add
      ((continuous_single_coord 1).comp Real.continuous_cos)
  · exact continuous_const

theorem generator_measurable (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (a : Fin rowCount) :
    Measurable (fun z : ℝ × Space => R.generatorField M.box m a z.1 z.2) := by
  have e : (fun z : ℝ × Space => R.generatorField M.box m a z.1 z.2) =
      (Prod.snd ⁻¹' (M.box (R.cellOf a)).solid).indicator
        (fun z : ℝ × Space => ∑ c : Fin 3, coefAt R M.box m a z.1 z.2 c • frameUnit (pointAngle z.2) c) := by
    funext z
    rw [generatorField_eq M R m a z.1 z.2]
    by_cases h : z.2 ∈ (M.box (R.cellOf a)).solid
    · simp only [Set.indicator, Set.mem_preimage, h, if_true]
      rfl
    · simp only [Set.indicator, Set.mem_preimage, h, if_false]
  rw [e]
  refine Measurable.indicator (Finset.measurable_sum _ fun c _ => ?_)
    (measurable_snd (measurableSet_solid _))
  exact (measurable_coefAt R M.box m a c).smul
    ((continuous_frame c).measurable.comp (measurable_pointAngle.comp measurable_snd))

theorem generator_square_finite (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (a : Fin rowCount) :
    periodLIntegral (fun σ y => ‖R.generatorField M.box m a σ y‖ ^ 2) < ⊤ := by
  have hA : GenShape M R m a := fun σ y => generatorField_eq M R m a σ y
  have hi := integrable_pairing hA hA
  have hm := generator_measurable M R m a
  have hfm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal
      (inner ℝ (R.generatorField M.box m a z.1 z.2) (R.generatorField M.box m a z.1 z.2)))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    (hm.inner hm).ennreal_ofReal.aemeasurable
  have e : periodLIntegral (fun σ y => ‖R.generatorField M.box m a σ y‖ ^ 2) =
      ∫⁻ z, ENNReal.ofReal
        (inner ℝ (R.generatorField M.box m a z.1 z.2) (R.generatorField M.box m a z.1 z.2))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    rw [lintegral_prod _ hfm]
    unfold periodLIntegral
    simp only [real_inner_self_eq_norm_sq]
  rw [e]
  exact hi.lintegral_lt_top

theorem pairing_combination_right {ι : Type*} [Fintype ι] (F : ℝ → Space → Space) (s : ι → ℝ)
    (g : ι → ℝ → Space → Space)
    (hint : ∀ i, Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (g i z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    periodPairing F (fun σ y => ∑ i, s i • g i σ y) = ∑ i, s i * periodPairing F (g i) := by
  have hpt : ∀ z : ℝ × Space, inner ℝ (F z.1 z.2) (∑ i, s i • g i z.1 z.2) =
      ∑ i, s i * inner ℝ (F z.1 z.2) (g i z.1 z.2) := by
    intro z
    rw [inner_sum]
    simp only [real_inner_smul_right]
  have hI : Integrable (fun z : ℝ × Space => ∑ i, s i * inner ℝ (F z.1 z.2) (g i z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    integrable_finsetSum _ fun i _ => (hint i).const_mul _
  rw [periodPairing_eq_integral (A := F) (B := fun σ y => ∑ i, s i • g i σ y)
      (hI.congr (ae_of_all _ fun z => (hpt z).symm)),
    integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ fun i _ => (hint i).const_mul _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_const_mul, periodPairing_eq_integral (hint i)]

theorem normalizer_square {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ) (hG : G.PosDef) :
    hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) * hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) = G⁻¹ := by
  set S := hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) with hS
  have hST : S.transpose = S := by
    rw [hS, ← hG.isHermitian.cfc_eq]
    have h := (cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) G : IsSelfAdjoint _).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h1 := normalizer_sandwich G hG
  rw [← hS, hST, mul_assoc] at h1
  have h2 : G * S * S = 1 := mul_eq_one_comm.1 h1
  rw [mul_assoc] at h2
  exact (Matrix.inv_eq_right_inv h2).symm

theorem quadratic_identity {n : Type*} [Fintype n] [DecidableEq n] (G : Matrix n n ℝ) (hG : G.PosDef)
    (τ : n → ℝ) (hcomm : G * Matrix.diagonal τ = Matrix.diagonal τ * G) (P : n → ℝ) :
    ∑ a, τ a * (∑ b, hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) a b * P b) ^ 2 =
      ∑ a, ∑ b, τ a * G⁻¹ a b * P a * P b := by
  set S := hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) with hS
  have hSD : S * Matrix.diagonal τ = Matrix.diagonal τ * S := by
    have hc : Commute G (Matrix.diagonal τ) := hcomm
    have h := hc.cfc_real (fun x => (Real.sqrt x)⁻¹)
    rw [hG.isHermitian.cfc_eq] at h
    exact h
  have hST : S.transpose = S := by
    rw [hS, ← hG.isHermitian.cfc_eq]
    have h := (cfc_predicate (fun x : ℝ => (Real.sqrt x)⁻¹) G : IsSelfAdjoint _).star_eq
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hmat : S.transpose * Matrix.diagonal τ * S = Matrix.diagonal τ * G⁻¹ := by
    rw [hST, hSD, mul_assoc, hS, normalizer_square G hG]
  have key : ∀ b c, ∑ a, S a b * τ a * S a c = τ b * G⁻¹ b c := by
    intro b c
    have h := congrFun (congrFun hmat b) c
    rw [Matrix.mul_apply, Matrix.diagonal_mul] at h
    simp only [Matrix.mul_diagonal, Matrix.transpose_apply] at h
    exact h
  calc ∑ a, τ a * (∑ b, S a b * P b) ^ 2
      = ∑ a, ∑ b, ∑ c, S a b * τ a * S a c * P b * P c := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c _ => ?_
        ring
    _ = ∑ b, ∑ c, (∑ a, S a b * τ a * S a c) * P b * P c := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.sum_mul, Finset.sum_mul]
    _ = ∑ a, ∑ b, τ a * G⁻¹ a b * P a * P b := by
        refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
        rw [key b c]

theorem weight_eq_of_entry (hpair : GeneratorPairingMatrixFormula) {M : CellMesh} {R : RowValues M.count rowCount}
    {m : ℕ} {tauMax : ℝ} (hR : IsRowValues M R m tauMax) {a b : Fin rowCount}
    (h : R.fieldPairingMatrix M.box m a b ≠ 0) :
    R.testWeight (R.cellOf a) (R.labelOf a) = R.testWeight (R.cellOf b) (R.labelOf b) := by
  rw [hpair M R m tauMax hR] at h
  by_cases hs : R.SameBlock a b
  · obtain ⟨hc, hl | hl⟩ := hs
    · rw [hc, hl]
    · rw [hc, hl, hR.weight_neg _ _ (hR.row_tested b)]
  · exfalso
    apply h
    simp [RowValues.testPairingMatrix, hs]

end Internal.RowNormIdentity

open Internal.RowNormIdentity Coercive.Internal.PassageLimit

theorem rowNormIdentity (hpair : GeneratorPairingMatrixFormula) : RowNormIdentity := by
  intro rowCount M R m tauMax c hR hc hG F hF hper hF2
  have hint : ∀ b, Integrable
      (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (R.generatorField M.box m b z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := fun b =>
    period_integrable_inner hF (generator_measurable M R m b).aestronglyMeasurable hF2
      (generator_square_finite M R m b)
  have hrow : ∀ a, periodPairing F (R.rowFieldOf M.box m a) =
      ∑ b, R.mix M.box m a b * periodPairing F (R.generatorField M.box m b) := fun a =>
    pairing_combination_right F (R.mix M.box m a) (R.generatorField M.box m) hint
  have hmix : R.mix M.box m = hG.isHermitian.cfc (fun x => (Real.sqrt x)⁻¹) := by
    unfold RowValues.mix
    rw [dif_pos hG.isHermitian]
  have hcomm : R.fieldPairingMatrix M.box m * Matrix.diagonal (fun a => R.testWeight (R.cellOf a) (R.labelOf a)) =
      Matrix.diagonal (fun a => R.testWeight (R.cellOf a) (R.labelOf a)) * R.fieldPairingMatrix M.box m := by
    ext a b
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases h : R.fieldPairingMatrix M.box m a b = 0
    · rw [h, mul_zero, zero_mul]
    · rw [weight_eq_of_entry hpair hR h, mul_comm]
  have key := quadratic_identity (R.fieldPairingMatrix M.box m) hG
    (fun a => R.testWeight (R.cellOf a) (R.labelOf a)) hcomm
    (fun b => periodPairing F (R.generatorField M.box m b))
  have hnn : 0 ≤ ∑ a, R.rowWeightOf c a * periodPairing F (R.rowFieldOf M.box m a) ^ 2 :=
    Finset.sum_nonneg fun a _ =>
      mul_nonneg (div_nonneg (hR.weight_pos _ _ (hR.row_tested a)).le hc.le) (sq_nonneg _)
  unfold rowNorm
  rw [Real.sq_sqrt hnn, Finset.mul_sum]
  rw [← key]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [hrow a, ← hmix]
  unfold RowValues.rowWeightOf
  field_simp

end Breakdown.CertCell.Instance

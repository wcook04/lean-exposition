import Breakdown.CertCell.AssemblyPotentialExpandPairs
import Breakdown.CertCell.TailAngularPlane
import Breakdown.CertCell.ModeConjugate
import Breakdown.CertCell.MeanStretchModeSum
import Breakdown.Cert.CoerciveSmoothPieceEpsBounds

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open CellCert.CellAnalysis CellCert.CellFormula CellCalculus

namespace Internal.StretchPairs

section Coupling

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem labelHarmonic_neg (m : ℕ) (α : ℤ × ℤ) : labelHarmonic m (-α) = -labelHarmonic m α := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_neg, Prod.snd_neg, Prod.neg_mk]
  congr 1 <;> ring

theorem labelGrad_neg (m : ℕ) (α : ℤ × ℤ) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    labelGrad m (-α) G p = fun ab => (starRingEnd ℂ) (labelGrad m α G p ab) := by
  funext ab
  unfold labelGrad modeGrad
  rw [labelHarmonic_neg]
  exact Bridge.modeAverage_neg_eq_conj _ _ _

theorem labelSecond_neg (m : ℕ) (α : ℤ × ℤ) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    labelHess m (-α) H p = fun abc => (starRingEnd ℂ) (labelHess m α H p abc) := by
  funext abc
  unfold labelHess modeSecondDeriv
  rw [labelHarmonic_neg]
  exact Bridge.modeAverage_neg_eq_conj _ _ _

theorem conj_modelTriple (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    (starRingEnd ℂ) (modelTriple S Gω a g a' g')
      = modelTriple (fun x y => (starRingEnd ℂ) (S x y)) (fun x y => (starRingEnd ℂ) (Gω x y))
          (fun x => (starRingEnd ℂ) (a x)) (fun x => (starRingEnd ℂ) (g x))
          (fun x => (starRingEnd ℂ) (a' x)) (fun x => (starRingEnd ℂ) (g' x)) := by
  simp only [modelTriple, modelBilin, curlOfGrad, map_add, map_neg, map_sum, map_mul, map_div₀, map_one,
    map_ofNat, Complex.conj_ofReal]

theorem modelTriple_comm (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : modelTriple S Gω a g a' g' = modelTriple S Gω a' g' a g := by
  unfold modelTriple
  ring

theorem conj_velOf_single (j : Fin 12) : (fun x => (starRingEnd ℂ) (velOf (Pi.single j (1 : ℂ)) x))
    = velOf (Pi.single j 1) := by
  funext x
  simp only [velOf, Pi.single_apply]
  split_ifs <;> simp

theorem conj_gradOf_single (j : Fin 12) : (fun x => (starRingEnd ℂ) (gradOf (Pi.single j (1 : ℂ)) x))
    = gradOf (Pi.single j 1) := by
  funext x
  simp only [gradOf, Pi.single_apply]
  split_ifs <;> simp

theorem star_velOf_single (j : Fin 12) : star (velOf (Pi.single j (1 : ℂ))) = velOf (Pi.single j 1) :=
  conj_velOf_single j

theorem star_gradOf_single (j : Fin 12) : star (gradOf (Pi.single j (1 : ℂ))) = gradOf (Pi.single j 1) :=
  conj_gradOf_single j

theorem curlSecond_conj (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (il : Fin 3 × Fin 3) :
    curlGradOfSecondDeriv (fun x => (starRingEnd ℂ) (h x)) il = (starRingEnd ℂ) (curlGradOfSecondDeriv h il) := by
  simp only [curlGradOfSecondDeriv, map_sum, map_mul, Complex.conj_ofReal]

theorem trueCoupling_symm (α : ℤ × ℤ) (p : ℝ × ℝ) (i j : Fin 12) :
    trueCoupling D α p i j = trueCoupling D α p j i := by
  simp only [trueCoupling, star_velOf_single, star_gradOf_single]
  exact modelTriple_comm _ _ _ _ _ _

theorem trueCoupling_neg (α : ℤ × ℤ) (p : ℝ × ℝ) (i j : Fin 12) :
    trueCoupling D (-α) p i j = (starRingEnd ℂ) (trueCoupling D α p i j) := by
  simp only [trueCoupling, star_velOf_single, star_gradOf_single, conj_modelTriple, conj_velOf_single,
    conj_gradOf_single, labelGrad_neg, labelSecond_neg, curlSecond_conj, map_add, map_div₀, map_ofNat]

theorem sesq12_trueCoupling_neg (α : ℤ × ℤ) (p : ℝ × ℝ) (U V : Fin 12 → ℂ) :
    sesq12 (trueCoupling D (-α) p) V U = (starRingEnd ℂ) (sesq12 (trueCoupling D α p) U V) := by
  simp only [sesq12, trueCoupling_neg, map_sum, map_mul, Complex.conj_conj]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [trueCoupling_symm D α p j i]
  ring

end Coupling

section CouplingRegular

open Coercive.Internal.SmoothPieceEps Coercive.Internal.ModeRotation TailBand.Internal.AngularPlane

def entryFn (i j : Fin 12) (gh : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ)) : ℂ :=
  modelTriple (fun a b => (gh.1 (a, b) + gh.1 (b, a)) / 2) (fun a b => curlGradOfSecondDeriv gh.2 (a, b))
    (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1)))

theorem continuous_entryFn (i j : Fin 12) : Continuous (entryFn i j) := by
  unfold entryFn modelTriple modelBilin curlOfGrad curlGradOfSecondDeriv
  fun_prop

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem trueCoupling_eq (α : ℤ × ℤ) (p : ℝ × ℝ) (i j : Fin 12) :
    trueCoupling D α p i j = entryFn i j (labelGrad D.azimuthOrder α (gradField D.given) p,
      labelHess D.azimuthOrder α D.givenHess p) := rfl

theorem decay_nonneg {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) : 0 ≤ B :=
  (norm_nonneg _).trans ((hW.decay 0 0).1.trans (by rw [norm_zero, add_zero, div_one]))

theorem labelGrad_given_le {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) (m : ℕ) (α : ℤ × ℤ) (p : ℝ × ℝ) (ab : Fin 3 × Fin 3) :
    ‖labelGrad m α (gradField W) p ab‖ ≤ B := by
  have hB := decay_nonneg hW
  unfold labelGrad modeGrad
  refine norm_modeAverage_le (labelHarmonic m α) _ ab fun τ φ => ?_
  simp only [gradField]
  refine le_trans (abs_coord_le _ _) ?_
  rw [Coercive.RotationInternal.axialRot_norm]
  refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
  rw [norm_rot_unit, mul_one]
  refine ((hW.decay (0 + τ) (axialRot φ (planePoint p))).2.1).trans ?_
  exact div_le_self hB (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))

theorem labelSecond_given_le {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) (m : ℕ) (α : ℤ × ℤ) (p : ℝ × ℝ) (abc : Fin 3 × Fin 3 × Fin 3) :
    ‖labelHess m α HW p abc‖ ≤ B := by
  have hB := decay_nonneg hW
  unfold labelHess modeSecondDeriv
  refine norm_modeAverage_le (labelHarmonic m α) _ abc fun τ φ => ?_
  refine le_trans (abs_coord_le _ _) ?_
  rw [Coercive.RotationInternal.axialRot_norm]
  refine le_trans (ContinuousLinearMap.le_opNorm₂ _ _ _) ?_
  rw [norm_rot_unit, norm_rot_unit, mul_one, mul_one]
  refine ((hW.decay (0 + τ) (axialRot φ (planePoint p))).2.2).trans ?_
  exact div_le_self hB (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _)))

theorem labelGiven_meas {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {B : ℝ}
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) (m : ℕ) (α : ℤ × ℤ) :
    AEStronglyMeasurable (labelGrad m α (gradField W)) (volume.restrict halfPlane) ∧
      AEStronglyMeasurable (labelHess m α HW) (volume.restrict halfPlane) := by
  refine ⟨aestronglyMeasurable_of_coord fun ij => ?_, aestronglyMeasurable_of_coord fun ijl => ?_⟩
  · have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
        axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ij.2))) ij.1) := by
      unfold axialRot
      fun_prop
    have hu : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
      (Bridge.Internal.MeanStretch.continuous_gradField hW.smooth).aestronglyMeasurable
    have h := (aestronglyMeasurable_orbitAverage hu (labelHarmonic m α)
      (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ij.2))) ij.1) hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [labelGrad, modeGrad, modeAverage_eq, zero_add]
  · have hΦ : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
      unfold axialRot
      fun_prop
    have h := (aestronglyMeasurable_orbitAverage hW.secondDeriv_measurable (labelHarmonic m α)
      (fun φ x => axialRot (-φ) (x (axialRot φ (unitVector ijl.2.1)) (axialRot φ (unitVector ijl.2.2))) ijl.1)
      hΦ).const_mul (1 / (2 * Real.pi) : ℂ)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [labelHess, modeSecondDeriv, modeAverage_eq, zero_add]

theorem entryFn_bound (B : ℝ) (i j : Fin 12) : ∃ c : ℝ, ∀ gh : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ),
    (∀ ab, ‖gh.1 ab‖ ≤ B) → (∀ abc, ‖gh.2 abc‖ ≤ B) → ‖entryFn i j gh‖ ≤ c := by
  obtain ⟨c, hc⟩ := (isCompact_closedBall (0 : (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 × Fin 3 → ℂ)) B).exists_bound_of_continuousOn
    (continuous_entryFn i j).continuousOn
  refine ⟨c, fun gh h1 h2 => hc gh ?_⟩
  have hB : 0 ≤ B := (norm_nonneg _).trans (h1 (0, 0))
  rw [Metric.mem_closedBall, dist_zero_right, Prod.norm_def]
  exact max_le ((pi_norm_le_iff_of_nonneg hB).2 h1) ((pi_norm_le_iff_of_nonneg hB).2 h2)

theorem trueCoupling_bound (hW : ∃ B, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) (α : ℤ × ℤ) :
    ∃ c : ℝ, ∀ p : ℝ × ℝ, ∀ i j, ‖trueCoupling D α p i j‖ ≤ c := by
  obtain ⟨B, hB⟩ := hW
  choose c hc using fun (i j : Fin 12) => entryFn_bound B i j
  refine ⟨∑ i, ∑ j, |c i j|, fun p i j => ?_⟩
  rw [trueCoupling_eq]
  refine (hc i j _ (labelGrad_given_le hB _ _ p) (labelSecond_given_le hB _ _ p)).trans ?_
  refine (le_abs_self _).trans ?_
  refine le_trans ?_ (Finset.single_le_sum (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg (c i j))
    (Finset.mem_univ i))
  exact Finset.single_le_sum (f := fun j => |c i j|) (fun j _ => abs_nonneg _) (Finset.mem_univ j)

theorem trueCoupling_meas (hW : ∃ B, CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B) (α : ℤ × ℤ)
    (i j : Fin 12) : AEStronglyMeasurable (fun p => trueCoupling D α p i j) (volume.restrict halfPlane) := by
  obtain ⟨B, hB⟩ := hW
  obtain ⟨h1, h2⟩ := labelGiven_meas hB D.azimuthOrder α
  have e : (fun p => trueCoupling D α p i j) = fun p => entryFn i j (labelGrad D.azimuthOrder α (gradField D.given) p,
      labelHess D.azimuthOrder α D.givenHess p) := funext fun p => trueCoupling_eq D α p i j
  rw [e]
  exact (continuous_entryFn i j).comp_aestronglyMeasurable (h1.prodMk h2)

end CouplingRegular

section Expand

theorem curl_smul (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (fun x => c * g x) i = c * curlOfGrad g i := by
  simp only [curlOfGrad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem bilin_smul_left (c : ℂ) (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω (fun x => c * a x) (fun x => c * g x) a' g' = c * modelBilin S Gω a g a' g' := by
  simp only [modelBilin, curl_smul]
  have e1 : ∑ i : Fin 3, ∑ j : Fin 3, c * curlOfGrad g i * S i j * curlOfGrad g' j
      = c * ∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * S i j * curlOfGrad g' j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j : Fin 3, (∑ l : Fin 3, c * a l * Gω j l) * curlOfGrad g' j
      = c * ∑ j : Fin 3, (∑ l : Fin 3, a l * Gω j l) * curlOfGrad g' j := by
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring
  have e3 : ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * Gω j l * (c * g (i, j)) * a' n
      = c * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * Gω j l * g (i, j) * a' n := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun n _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3]
  ring

theorem bilin_smul_right (c : ℂ) (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) :
    modelBilin S Gω a g (fun x => c * a' x) (fun x => c * g' x) = c * modelBilin S Gω a g a' g' := by
  simp only [modelBilin, curl_smul]
  have e1 : ∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * S i j * (c * curlOfGrad g' j)
      = c * ∑ i : Fin 3, ∑ j : Fin 3, curlOfGrad g i * S i j * curlOfGrad g' j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e2 : ∑ j : Fin 3, (∑ l : Fin 3, a l * Gω j l) * (c * curlOfGrad g' j)
      = c * ∑ j : Fin 3, (∑ l : Fin 3, a l * Gω j l) * curlOfGrad g' j := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have e3 : ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * Gω j l * g (i, j) * (c * a' n)
      = c * ∑ i : Fin 3, ∑ l : Fin 3, ∑ n : Fin 3, ∑ j : Fin 3,
        (alternatingSymbol i l n : ℂ) * Gω j l * g (i, j) * a' n := by
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun n _ =>
      Finset.sum_congr rfl fun j _ => by ring
  rw [e1, e2, e3]
  ring

def firstSlot (S Gω : Fin 3 → Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) : (Fin 12 → ℂ) →ₗ[ℂ] ℂ where
  toFun Y := modelTriple S Gω (velOf Y) (gradOf Y) a' g'
  map_add' Y Y' := by
    simp only [modelTriple, modelBilin, curlOfGrad, velOf, gradOf, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring
  map_smul' c Y := by
    have hv : velOf (c • Y) = fun x => c * velOf Y x := rfl
    have hg : gradOf (c • Y) = fun x => c * gradOf Y x := rfl
    simp only [RingHom.id_apply, smul_eq_mul, modelTriple, hv, hg, bilin_smul_left, bilin_smul_right]
    ring

def secondSlot (S Gω : Fin 3 → Fin 3 → ℂ) (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) : (Fin 12 → ℂ) →ₗ[ℂ] ℂ where
  toFun X := modelTriple S Gω a g (velOf X) (gradOf X)
  map_add' X X' := by
    simp only [modelTriple, modelBilin, curlOfGrad, velOf, gradOf, Pi.add_apply, mul_add, add_mul,
      Finset.sum_add_distrib]
    ring
  map_smul' c X := by
    have hv : velOf (c • X) = fun x => c * velOf X x := rfl
    have hg : gradOf (c • X) = fun x => c * gradOf X x := rfl
    simp only [RingHom.id_apply, smul_eq_mul, modelTriple, hv, hg, bilin_smul_left, bilin_smul_right]
    ring

theorem single_eq (j : Fin 12) : (fun k : Fin 12 => if j = k then (1 : ℂ) else 0) = Pi.single j 1 := by
  funext k
  simp [Pi.single_apply, eq_comm]

theorem triple_expand (S Gω : Fin 3 → Fin 3 → ℂ) (X Y : Fin 12 → ℂ) :
    modelTriple S Gω (velOf Y) (gradOf Y) (velOf X) (gradOf X)
      = ∑ i, ∑ j, X i * modelTriple S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
          (velOf (Pi.single i 1)) (gradOf (Pi.single i 1)) * Y j := by
  have h1 := LinearMap.pi_apply_eq_sum_univ (firstSlot S Gω (velOf X) (gradOf X)) Y
  have h2 : ∀ j, modelTriple S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1)) (velOf X) (gradOf X)
      = ∑ i, X i * modelTriple S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
          (velOf (Pi.single i 1)) (gradOf (Pi.single i 1)) := by
    intro j
    have := LinearMap.pi_apply_eq_sum_univ (secondSlot S Gω (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))) X
    simp only [secondSlot, LinearMap.coe_mk, AddHom.coe_mk, single_eq, smul_eq_mul] at this
    exact this
  simp only [firstSlot, LinearMap.coe_mk, AddHom.coe_mk, single_eq, smul_eq_mul] at h1
  rw [h1]
  simp only [h2, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end Expand

section Pointwise

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM)

theorem sesq12_trueCoupling_eq (α : ℤ × ℤ) (p : ℝ × ℝ) (U V : Fin 12 → ℂ) :
    sesq12 (trueCoupling D α p) U V
      = Bridge.stretchTriple (labelGrad D.azimuthOrder α (gradField D.given) p)
          (labelHess D.azimuthOrder α D.givenHess p) (velOf V) (gradOf V) (star (velOf U)) (star (gradOf U)) := by
  have h := triple_expand (fun a b => (labelGrad D.azimuthOrder α (gradField D.given) p (a, b)
      + labelGrad D.azimuthOrder α (gradField D.given) p (b, a)) / 2)
    (fun a b => curlGradOfSecondDeriv (labelHess D.azimuthOrder α D.givenHess p) (a, b)) (star U) V
  have e : Bridge.stretchTriple (labelGrad D.azimuthOrder α (gradField D.given) p)
      (labelHess D.azimuthOrder α D.givenHess p) (velOf V) (gradOf V) (star (velOf U)) (star (gradOf U))
      = modelTriple (fun a b => (labelGrad D.azimuthOrder α (gradField D.given) p (a, b)
      + labelGrad D.azimuthOrder α (gradField D.given) p (b, a)) / 2)
        (fun a b => curlGradOfSecondDeriv (labelHess D.azimuthOrder α D.givenHess p) (a, b))
        (velOf V) (gradOf V) (velOf (star U)) (gradOf (star U)) := rfl
  rw [e, h]
  unfold sesq12
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [trueCoupling, star_velOf_single, star_gradOf_single, Pi.star_apply, Complex.star_def]

theorem velOf_bandProfile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    velOf (bandProfile D ι v G p) = labelVel D.azimuthOrder ι v p := by
  funext a
  fin_cases a <;> rfl

theorem gradOf_bandProfile (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    gradOf (bandProfile D ι v G p) = labelGrad D.azimuthOrder ι G p := by
  funext ab
  obtain ⟨a, b⟩ := ab
  fin_cases a <;> fin_cases b <;> rfl

theorem stretchTriple_zero_left (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ)
    (g' : Fin 3 × Fin 3 → ℂ) : Bridge.stretchTriple gW hW 0 0 a' g' = 0 := by
  simp [Bridge.stretchTriple, Bridge.stretchBilin, curlOfGrad]

theorem stretchTriple_zero_right (gW : Fin 3 × Fin 3 → ℂ) (hW : Fin 3 × Fin 3 × Fin 3 → ℂ) (a : Fin 3 → ℂ)
    (g : Fin 3 × Fin 3 → ℂ) : Bridge.stretchTriple gW hW a g 0 0 = 0 := by
  simp [Bridge.stretchTriple, Bridge.stretchBilin, curlOfGrad]

theorem labelHarmonic_sub (m : ℕ) (ι κ : ℤ × ℤ) : labelHarmonic m (ι - κ) = labelHarmonic m ι - labelHarmonic m κ := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_sub, Prod.snd_sub, Prod.mk_sub_mk]
  congr 1 <;> ring

theorem labelHarmonic_add (m : ℕ) (ι κ : ℤ × ℤ) : labelHarmonic m (ι + κ) = labelHarmonic m ι + labelHarmonic m κ := by
  simp only [labelHarmonic, labelTime, labelAzimuth, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk]
  congr 1 <;> ring

end Pointwise

end Internal.StretchPairs

end Assembly

end CertCell

end Breakdown

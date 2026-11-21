import Breakdown.Cert.Statement
import Breakdown.Cert.SliceFieldsSymbol
import Breakdown.Cert.SliceFieldsIsometry
import Breakdown.Cert.SliceFieldsDivergence
import Breakdown.Cert.SliceFieldsBound
import Breakdown.Weak.VelocityWeakGradient

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Cert

namespace Internal.SliceFields

open Freq

def gradField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (p : Fin 3 → Space → F)
    (y : Space) : Space →L[ℝ] F :=
  ∑ j : Fin 3, (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (p j y)

theorem gradField_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : Fin 3 → Space → F) (y v : Space) : gradField p y v = ∑ j : Fin 3, v j • p j y := by
  simp [gradField]

theorem gradField_unit {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : Fin 3 → Space → F) (y : Space) (i : Fin 3) : gradField p y (unitVector i) = p i y := by
  simp [gradField_apply, unitVector]

theorem memLp_gradField {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {p : Fin 3 → Space → F} (hp : ∀ j, MemLp (p j) 2 volume) : MemLp (gradField p) 2 volume := by
  have h : ∀ j, MemLp (fun y => (EuclideanSpace.proj j : Space →L[ℝ] ℝ).smulRight (p j y)) 2 volume :=
    fun j => (ContinuousLinearMap.smulRightL ℝ Space F (EuclideanSpace.proj j)).comp_memLp' (hp j)
  exact memLp_finsetSum Finset.univ (fun j _ => h j)

def secondDerivField (q : Fin 3 → Fin 3 → Space → Space) (y : Space) : Space →L[ℝ] Space →L[ℝ] Space :=
  gradField (fun i => gradField (q i)) y

theorem secondDerivField_apply (q : Fin 3 → Fin 3 → Space → Space) (y v w : Space) :
    secondDerivField q y v w = ∑ i : Fin 3, ∑ j : Fin 3, (v i * w j) • q i j y := by
  simp only [secondDerivField, gradField_apply, sum_apply,
    smul_apply, Finset.smul_sum, smul_smul]

theorem secondDerivField_unit (q : Fin 3 → Fin 3 → Space → Space) (y : Space) (a b : Fin 3) :
    secondDerivField q y (unitVector a) (unitVector b) = q a b y := by
  rw [secondDerivField, gradField_unit, gradField_unit]

theorem flip_secondDerivField (q : Fin 3 → Fin 3 → Space → Space) (y : Space) (j : Fin 3) :
    (secondDerivField q y).flip (unitVector j) = gradField (fun i => q i j) y := by
  ext1 v
  rw [ContinuousLinearMap.flip_apply, secondDerivField, gradField_apply, gradField_apply,
    sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_apply, gradField_unit]

theorem secondDerivTrace_secondDerivField (q : Fin 3 → Fin 3 → Space → Space) (y : Space) :
    secondDerivTrace (secondDerivField q y) = ∑ j : Fin 3, q j j y := by
  simp only [secondDerivTrace, secondDerivField_unit]

theorem norm_secondDerivField_sq_le (q : Fin 3 → Fin 3 → Space → Space) (y : Space) :
    ‖secondDerivField q y‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖secondDerivField q y (unitVector i) (unitVector j)‖ ^ 2 := by
  simp only [secondDerivField_unit]
  have h0 : 0 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖q i j y‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hb : ‖secondDerivField q y‖ ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖q i j y‖ ^ 2) := by
    refine ContinuousLinearMap.opNorm_le_bound₂ _ (Real.sqrt_nonneg _) fun v w => ?_
    rw [secondDerivField_apply]
    calc _ ≤ ‖v‖ * ‖w‖ * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖q i j y‖ ^ 2) :=
          norm_double_sum_le v w (fun i j => q i j y)
      _ = _ := by ring
  calc ‖secondDerivField q y‖ ^ 2 ≤ Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, ‖q i j y‖ ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ = _ := Real.sq_sqrt h0

theorem integrable_norm_sq_L2R (f : L2R) : Integrable (fun y => ‖(f : Space → Space) y‖ ^ 2) volume :=
  (Lp.memLp f).integrable_norm_pow two_ne_zero

theorem integral_norm_sq_L2R (f : L2R) : ∫ y, ‖(f : Space → Space) y‖ ^ 2 = ‖f‖ ^ 2 :=
  (Internal.SliceFieldsIsometry.l2R_norm_sq f).symm

theorem sum_norm_partialX_sq (z : X) : ∑ i : Fin 3, ‖partialX i z‖ ^ 2 = ‖z‖ ^ 2 := by
  simp only [partialX_eq, norm_toPhys_of_mem_sig _ (derivX _ z).2]
  exact sum_norm_derivX_sq z

theorem sum_partialX_derivX (k : X) :
    (∑ j : Fin 3, partialX j (derivX j k) : L2R) = -toPhys (k : L2C) := by
  simp only [partialX_eq, ← map_sum, ← Submodule.coe_sum, sum_derivX_derivX, Submodule.coe_neg,
    map_neg]

def velGrad (x : X) : Fin 3 → Space → Space := fun j => (partialX j x : Space → Space)

def velSecondDeriv (k : X) : Fin 3 → Fin 3 → Space → Space :=
  fun i j => (partialX i (derivX j k) : Space → Space)

theorem lintegral_sixth_lt_top (x : X) :
    ∫⁻ y, ENNReal.ofReal (‖(velocity x : Space → Space) y‖ ^ 6) < ⊤ := by
  have hm : MemLp (velocity x : Space → Space) ((6 : ℕ) : ℝ≥0∞) volume := by
    exact_mod_cast Lp.memLp (velocity x)
  exact (hm.integrable_norm_pow (by norm_num)).lintegral_lt_top

end Internal.SliceFields

open Freq Internal.SliceFields

theorem slice_fields (x k : Freq.X) (h : Freq.IsHalfSspOf x k) :
    ∃ (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)),
      IsWeakGradient (Freq.velocity x) G ∧
      (∀ j : Fin 3, IsWeakGradient (fun y => G y (unitVector j)) (fun y => (H y).flip (unitVector j))) ∧
      (∀ᵐ y, ∑ i : Fin 3, (G y (unitVector i)) i = 0) ∧
      (∫⁻ y, ENNReal.ofReal (‖(Freq.velocity x : Space → Space) y‖ ^ 6) < ⊤) ∧
      (∀ j : Fin 3, (fun y => G y (unitVector j)) =ᵐ[volume] (Freq.partialX j x : Space → Space)) ∧
      Integrable (fun y => matSq (G y)) ∧ (∫ y, matSq (G y)) = ‖x‖ ^ 2 ∧
      Integrable (fun y => ‖secondDerivTrace (H y)‖ ^ 2) ∧ (∫ y, ‖secondDerivTrace (H y)‖ ^ 2) = ‖k‖ ^ 2 ∧
      (fun y => secondDerivTrace (H y)) =ᵐ[volume] (fun y => -(Freq.toPhys (k : Freq.L2C) : Space → Space) y) ∧
      (∀ y, ‖H y‖ ^ 2 ≤ ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2) ∧
      Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2) ∧
      (∫ y, ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2) = ‖k‖ ^ 2 := by
  have hp : velGrad x = fun j => (partialX j x : Space → Space) := rfl
  have hq : velSecondDeriv k = fun i j => (partialX i (derivX j k) : Space → Space) := rfl
  have htr : (fun y => secondDerivTrace (secondDerivField (velSecondDeriv k) y)) =ᵐ[volume]
      fun y => -(toPhys (k : L2C) : Space → Space) y := by
    filter_upwards [Lp.coeFn_finsetSum Finset.univ (fun j : Fin 3 => partialX j (derivX j k)),
      Lp.coeFn_neg (toPhys (k : L2C))] with y h1 h2
    calc secondDerivTrace (secondDerivField (velSecondDeriv k) y) = ∑ j : Fin 3, (partialX j (derivX j k) : Space → Space) y :=
          secondDerivTrace_secondDerivField (velSecondDeriv k) y
      _ = ((∑ j : Fin 3, partialX j (derivX j k) : L2R) : Space → Space) y := by
          rw [h1, Finset.sum_apply]
      _ = ((-toPhys (k : L2C) : L2R) : Space → Space) y := by rw [sum_partialX_derivX]
      _ = -(toPhys (k : L2C) : Space → Space) y := by rw [h2, Pi.neg_apply]
  have htr2 : (fun y => ‖secondDerivTrace (secondDerivField (velSecondDeriv k) y)‖ ^ 2) =ᵐ[volume]
      fun y => ‖(toPhys (k : L2C) : Space → Space) y‖ ^ 2 := by
    filter_upwards [htr] with y hy
    rw [hy, norm_neg]
  have hmatSq : (fun y => matSq (gradField (velGrad x) y)) = fun y => ∑ i : Fin 3, ‖(velGrad x) i y‖ ^ 2 := by
    funext y
    simp only [matSq, gradField_unit]
  have hsecondDeriv : (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖secondDerivField (velSecondDeriv k) y (unitVector i) (unitVector j)‖ ^ 2) =
      fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖(velSecondDeriv k) i j y‖ ^ 2 := by
    funext y
    simp only [secondDerivField_unit]
  refine ⟨gradField (velGrad x), secondDerivField (velSecondDeriv k), ?_, ?_, ?_, lintegral_sixth_lt_top x, ?_, ?_, ?_, ?_, ?_, htr,
    norm_secondDerivField_sq_le (velSecondDeriv k), ?_, ?_⟩
  · refine ⟨(Lp.memLp (velocity x)).locallyIntegrable (by norm_num),
      (memLp_gradField fun j => Lp.memLp (partialX j x)).locallyIntegrable (by norm_num),
      fun φ hφ i => ?_⟩
    simp only [gradField_unit, hp]
    exact WeakProfile.velocityWeakGradient_holds x φ hφ i
  · intro j
    have hflip : (fun y => (secondDerivField (velSecondDeriv k) y).flip (unitVector j)) = gradField (fun i => (velSecondDeriv k) i j) :=
      funext fun y => flip_secondDerivField (velSecondDeriv k) y j
    have hg : (fun y => gradField (velGrad x) y (unitVector j)) = (velGrad x) j := funext fun y => gradField_unit (velGrad x) y j
    rw [hflip, hg]
    refine ⟨(Lp.memLp (partialX j x)).locallyIntegrable (by norm_num),
      (memLp_gradField fun i => Lp.memLp (partialX i (derivX j k))).locallyIntegrable (by norm_num),
      fun φ hφ i => ?_⟩
    simp only [gradField_unit, hp, hq]
    rw [WeakProfile.velocityWeakGradient_holds (derivX j k) φ hφ i]
    congr 1
    apply integral_congr_ae
    filter_upwards [velocityInverts_holds _ _ (halfSsp_derivX j h)] with y hy
    rw [hy, partialX_eq]
  · simp only [gradField_unit, hp]
    exact partialX_divergence x
  · intro j
    exact ae_of_all _ fun y => gradField_unit (velGrad x) y j
  · rw [hmatSq]
    exact integrable_finsetSum _ fun i _ => integrable_norm_sq_L2R (partialX i x)
  · rw [hmatSq, hp]
    rw [integral_finsetSum _ fun i _ => integrable_norm_sq_L2R (partialX i x)]
    simp only [integral_norm_sq_L2R]
    exact sum_norm_partialX_sq x
  · exact (integrable_norm_sq_L2R (toPhys (k : L2C))).congr htr2.symm
  · rw [integral_congr_ae htr2, integral_norm_sq_L2R, norm_toPhys_of_mem_sig _ k.2]
    rfl
  · rw [hsecondDeriv]
    exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_norm_sq_L2R (partialX i (derivX j k))
  · rw [hsecondDeriv, hq]
    rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      integrable_norm_sq_L2R (partialX i (derivX j k))]
    rw [Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ =>
      integrable_norm_sq_L2R (partialX i (derivX j k))]
    simp only [integral_norm_sq_L2R]
    rw [Finset.sum_comm]
    simp only [sum_norm_partialX_sq]
    exact sum_norm_derivX_sq k

end Breakdown.Cert

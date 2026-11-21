import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.HeldUniqueParts
import Breakdown.Cert.CompactPerturbation

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProductClassStatement : Prop :=
  ∀ (m : ℕ) (W v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), ContDiff ℝ 1 W → IsClassField m W →
    IsSecondOrderField m v G H → IsClassField m (symProduct W (fun z => fderiv ℝ W z) v G)

def LinearKernelStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ v G H P, d.IsLinearState α p v G H P → ∀ κ : Fin k → ℝ,
      (∃ Q : Space → Space, IsGradientField Q ∧ ∀ᵐ y ∂volume, d.fullField α p v G H P κ y = Q y) →
      (∀ i, d.pins G i = 0) →
      (∀ᵐ y ∂volume, driftField α (d.rotationRate p) v G y + P y = 0) ∧ κ = 0

namespace LinearSolveCore


theorem turnStep_apply (m : ℕ) (y : Space) :
    turnStep m y 0 = Real.cos (2 * Real.pi / m) * y 0 - Real.sin (2 * Real.pi / m) * y 1 ∧
    turnStep m y 1 = Real.sin (2 * Real.pi / m) * y 0 + Real.cos (2 * Real.pi / m) * y 1 ∧
    turnStep m y 2 = y 2 := by
  simp [turnStep]

theorem mirror_apply (y : Space) : mirror y 0 = y 0 ∧ mirror y 1 = y 1 ∧ mirror y 2 = -y 2 := by
  simp [mirror]

def turnStepLinear (m : ℕ) : Space →ₗ[ℝ] Space where
  toFun := turnStep m
  map_add' x y := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring

def mirrorLinear : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' x y := by
    ext i
    fin_cases i <;> simp [mirror] <;> ring
  map_smul' c x := by
    ext i
    fin_cases i <;> simp [mirror]

theorem norm_turnStep (m : ℕ) (y : Space) : ‖turnStep m y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  obtain ⟨h0, h1, h2⟩ := turnStep_apply m y
  rw [h0, h1, h2]
  have hc := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  nlinarith [hc]

theorem norm_mirror (y : Space) : ‖mirror y‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  obtain ⟨h0, h1, h2⟩ := mirror_apply y
  rw [h0, h1, h2]
  ring

def turnStepIsometry (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨turnStepLinear m, norm_turnStep m⟩ rfl

def mirrorIsometry : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv ⟨mirrorLinear, norm_mirror⟩ rfl

theorem turnStep_measurePreserving (m : ℕ) : MeasurePreserving (turnStep m) volume volume :=
  (turnStepIsometry m).measurePreserving

theorem mirror_measurePreserving : MeasurePreserving mirror volume volume :=
  mirrorIsometry.measurePreserving



theorem entrySq_nonneg' (L : Space →L[ℝ] Space) : 0 ≤ entrySq L :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem norm_apply_le_entries (L : Space →L[ℝ] Space) (x : Space) :
    ‖L x‖ ≤ ‖x‖ * ∑ i : Fin 3, ‖L (unitVector i)‖ := by
  have hx : x = ∑ i : Fin 3, x i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr x]
    simp [unitVector, EuclideanSpace.basisFun_apply]
  rw [hx, map_sum, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul]
  gcongr
  rw [← hx]
  exact PiLp.norm_apply_le x i

theorem entry_memLp {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (i : Fin 3) :
    MemLp (fun y => G y (unitVector i)) 2 volume := by
  have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume :=
    hs.measurable_gradient.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
  refine hs.gradient_two.mono' (hm.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity)
    (Finset.mem_univ i)

theorem symProduct_memLp (hI : InverseSquareBoundStatement) {m : ℕ} {W v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {C : ℝ}
    (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (hs : IsSecondOrderField m v G H) :
    MemLp (symProduct W (fun z => fderiv ℝ W z) v G) 2 volume := by
  obtain ⟨hIi, -⟩ := hI v G hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient
  have hC : 0 ≤ C := by
    have h := (hb 0).1
    have hp : 0 < (1 + ‖(0 : Space)‖) ^ (-(1 : ℝ)) := by positivity
    nlinarith [norm_nonneg (W 0)]
  have hWc : Continuous W := hW.continuous
  have hDc : Continuous (fun z => fderiv ℝ W z) := hW.continuous_fderiv one_ne_zero
  have hm1 : AEStronglyMeasurable (fun y => G y (W y)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hs.measurable_gradient.prodMk hWc.aestronglyMeasurable)
  have hm2 : AEStronglyMeasurable (fun y => fderiv ℝ W y (v y)) volume :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (hDc.aestronglyMeasurable.prodMk hs.measurable_velocity)
  have hq : MemLp (fun y => ‖v y‖ / ‖y‖) 2 volume := by
    have hm : AEStronglyMeasurable (fun y => ‖v y‖ / ‖y‖) volume :=
      (hs.measurable_velocity.norm.aemeasurable.div continuous_norm.measurable.aemeasurable).aestronglyMeasurable
    refine (memLp_two_iff_integrable_sq_norm hm).mpr ?_
    refine hIi.congr (Filter.Eventually.of_forall fun y => ?_)
    simp [div_pow]
  have hE : MemLp (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖) 2 volume :=
    memLp_finsetSum _ fun i _ => (entry_memLp hs i).norm
  have hg : MemLp (fun y => (1 / 2 : ℝ) * (C * ∑ i : Fin 3, ‖G y (unitVector i)‖ + C * (‖v y‖ / ‖y‖)))
      2 volume :=
    ((hE.const_mul C).add (hq.const_mul C)).const_mul _
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  have hm : AEStronglyMeasurable (symProduct W (fun z => fderiv ℝ W z) v G) volume := by
    unfold symProduct
    exact (hm1.add hm2).const_smul (1 / 2 : ℝ)
  refine hg.of_le hm ?_
  filter_upwards [hne] with y hy0
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw1 : ‖W y‖ ≤ C := by
    have h := (hb y).1
    have hp : (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    nlinarith
  have hw2 : ‖fderiv ℝ W y‖ * ‖y‖ ≤ C := by
    have h := (hb y).2
    have hp : (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖y‖ ≤ 1 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_inv_mul, div_le_one (by positivity)]
      nlinarith [norm_nonneg y]
    nlinarith [norm_nonneg (fderiv ℝ W y)]
  have h1 : ‖G y (W y)‖ ≤ C * ∑ i : Fin 3, ‖G y (unitVector i)‖ :=
    (norm_apply_le_entries (G y) (W y)).trans
      (mul_le_mul_of_nonneg_right hw1 (Finset.sum_nonneg fun i _ => norm_nonneg _))
  have h2 : ‖fderiv ℝ W y (v y)‖ ≤ C * (‖v y‖ / ‖y‖) := by
    refine ((fderiv ℝ W y).le_opNorm (v y)).trans ?_
    rw [mul_div_assoc', le_div_iff₀ hy]
    nlinarith [norm_nonneg (v y)]
  have hsum : 0 ≤ ∑ i : Fin 3, ‖G y (unitVector i)‖ := Finset.sum_nonneg fun i _ => norm_nonneg _
  have hnn : (0 : ℝ) ≤ 1 / 2 * (C * ∑ i : Fin 3, ‖G y (unitVector i)‖ + C * (‖v y‖ / ‖y‖)) :=
    mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hC hsum)
      (mul_nonneg hC (div_nonneg (norm_nonneg _) (norm_nonneg _))))
  show ‖(1 / 2 : ℝ) • (G y (W y) + fderiv ℝ W y (v y))‖ ≤
    ‖(1 / 2 : ℝ) * (C * ∑ i : Fin 3, ‖G y (unitVector i)‖ + C * (‖v y‖ / ‖y‖))‖
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.norm_of_nonneg hnn]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)

abbrev FieldL2 : Type := Lp Space 2 (volume : Measure Space)

theorem gradientAt_continuous {φ : Space → ℝ} (hφ : IsTestScalar φ) : Continuous (gradientAt φ) := by
  unfold gradientAt
  exact continuous_finsetSum _ fun i _ =>
    ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

theorem gradientAt_hasCompactSupport {φ : Space → ℝ} (hφ : IsTestScalar φ) :
    HasCompactSupport (gradientAt φ) := by
  refine (hφ.2.fderiv (𝕜 := ℝ)).mono fun x hx => ?_
  by_contra h
  apply hx
  have h0 : fderiv ℝ φ x = 0 := by simpa using h
  simp [gradientAt, h0]

theorem gradientAt_memLp {φ : Space → ℝ} (hφ : IsTestScalar φ) : MemLp (gradientAt φ) 2 volume :=
  (gradientAt_continuous hφ).memLp_of_hasCompactSupport (gradientAt_hasCompactSupport hφ)

def solPair (φ : {φ : Space → ℝ // IsTestScalar φ}) : FieldL2 →L[ℝ] ℝ :=
  innerSL ℝ ((gradientAt_memLp φ.2).toLp (gradientAt φ.1))

def classDefect (T : Space ≃ₗᵢ[ℝ] Space) : FieldL2 →L[ℝ] FieldL2 :=
  (Lp.compMeasurePreservingₗᵢ ℝ T T.measurePreserving).toContinuousLinearMap -
    (T.toContinuousLinearEquiv : Space →L[ℝ] Space).compLpL 2 volume

def solClass (m : ℕ) : Submodule ℝ FieldL2 :=
  (⨅ φ : {φ : Space → ℝ // IsTestScalar φ}, LinearMap.ker (solPair φ : FieldL2 →ₗ[ℝ] ℝ)) ⊓
    LinearMap.ker (classDefect (turnStepIsometry m) : FieldL2 →ₗ[ℝ] FieldL2) ⊓ LinearMap.ker (classDefect mirrorIsometry : FieldL2 →ₗ[ℝ] FieldL2)

theorem solClass_isClosed (m : ℕ) : IsClosed (solClass m : Set FieldL2) := by
  unfold solClass
  simp only [Submodule.coe_inf, Submodule.coe_iInf]
  exact ((isClosed_iInter fun φ => (solPair φ).isClosed_ker).inter
    (classDefect _).isClosed_ker).inter (classDefect _).isClosed_ker

theorem mem_ker_solPair_iff (φ : {φ : Space → ℝ // IsTestScalar φ}) (f : FieldL2) :
    f ∈ LinearMap.ker (solPair φ : FieldL2 →ₗ[ℝ] ℝ) ↔ ∫ y, inner ℝ (f y) (gradientAt φ.1 y) = 0 := by
  rw [LinearMap.mem_ker]
  change inner ℝ ((gradientAt_memLp φ.2).toLp (gradientAt φ.1)) f = 0 ↔ _
  rw [L2.inner_def]
  have h : ∫ a, inner ℝ (((gradientAt_memLp φ.2).toLp (gradientAt φ.1)) a) (f a) =
      ∫ y, inner ℝ (f y) (gradientAt φ.1 y) := by
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (gradientAt_memLp φ.2)] with y hy
    rw [hy, real_inner_comm]
  rw [h]

theorem mem_ker_classDefect_iff (T : Space ≃ₗᵢ[ℝ] Space) (f : FieldL2) :
    f ∈ LinearMap.ker (classDefect T : FieldL2 →ₗ[ℝ] FieldL2) ↔ ∀ᵐ y ∂volume, f (T y) = T (f y) := by
  rw [LinearMap.mem_ker]
  change (Lp.compMeasurePreservingₗᵢ ℝ T T.measurePreserving) f -
    (T.toContinuousLinearEquiv : Space →L[ℝ] Space).compLpL 2 volume f = 0 ↔ _
  rw [sub_eq_zero, Lp.ext_iff]
  have h1 := Lp.coeFn_compMeasurePreserving f T.measurePreserving
  have h2 := (T.toContinuousLinearEquiv : Space →L[ℝ] Space).coeFn_compLpL f
  constructor
  · intro h
    filter_upwards [h, h1, h2] with y hy hy1 hy2
    have e1 : (Lp.compMeasurePreservingₗᵢ ℝ T T.measurePreserving) f y = f (T y) := hy1
    rw [← e1, hy, hy2]
    rfl
  · intro h
    filter_upwards [h, h1, h2] with y hy hy1 hy2
    have e1 : (Lp.compMeasurePreservingₗᵢ ℝ T T.measurePreserving) f y = f (T y) := hy1
    rw [e1, hy2, hy]
    rfl

theorem mem_solClass_iff (m : ℕ) (f : FieldL2) :
    f ∈ solClass m ↔ IsSolenoidalL2 f ∧ IsClassField m f := by
  simp only [solClass, Submodule.mem_inf, Submodule.mem_iInf, mem_ker_solPair_iff,
    mem_ker_classDefect_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨⟨Lp.memLp f, fun φ hφ => h1 ⟨φ, hφ⟩⟩, h2, h3⟩
  · rintro ⟨⟨-, h1⟩, h2, h3⟩
    exact ⟨⟨fun φ => h1 φ.1 φ.2, h2⟩, h3⟩

instance (m : ℕ) : CompleteSpace (solClass m) := (solClass_isClosed m).completeSpace_coe


theorem weakPower_neg {α : ℝ} {u R : Space → Space} (h : IsWeakFractionalPower α u R) :
    IsWeakFractionalPower α (fun y => -u y) (fun y => -R y) := by
  refine ⟨h.1.neg, fun φ hφ => ?_⟩
  simp only [inner_neg_left, integral_neg, h.2 φ hφ]

theorem drift_sub (α a : ℝ) (v u : Space → Space) (G K : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun y => v y - u y) (fun y => G y - K y) y = driftField α a v G y - driftField α a u K y := by
  have hT : axialTurn (v y - u y) = axialTurn (v y) - axialTurn (u y) := by
    ext i
    fin_cases i <;> simp [axialTurn] <;> ring
  simp only [driftField, FunLike.coe_sub, Pi.sub_apply, hT, smul_sub]
  abel

theorem state_unique (h3 : FreeUniqueStatement) (h7 : SecondOrderLinearStatement)
    (hD : WeakPowerDifferenceStatement)
    {α a : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {m : ℕ} {v u P R : Space → Space}
    {G K : Space → (Space →L[ℝ] Space)} {H L : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (hs' : IsSecondOrderField m u K L)
    (hp : IsWeakFractionalPower α v P) (hp' : IsWeakFractionalPower α u R)
    (hd : MemLp (driftField α a v G) 2 volume) (hd' : MemLp (driftField α a u K) 2 volume)
    (he : ∀ᵐ y ∂volume, driftField α a v G y + P y = driftField α a u K y + R y) :
    (∀ᵐ y ∂volume, v y = u y) ∧ (∀ᵐ y ∂volume, G y = K y) ∧ (∀ᵐ y ∂volume, H y = L y) ∧
      ∀ᵐ y ∂volume, P y = R y := by
  have hsd := h7 m v u G K H L (-1) hs hs'
  have e1 : (fun y => v y + (-1 : ℝ) • u y) = fun y => v y - u y := by
    funext y; rw [neg_one_smul, ← sub_eq_add_neg]
  have e2 : (fun y => G y + (-1 : ℝ) • K y) = fun y => G y - K y := by
    funext y; rw [neg_one_smul, ← sub_eq_add_neg]
  have e3 : (fun y => H y + (-1 : ℝ) • L y) = fun y => H y - L y := by
    funext y; rw [neg_one_smul, ← sub_eq_add_neg]
  rw [e1, e2, e3] at hsd
  have hdd : MemLp (driftField α a (fun y => v y - u y) (fun y => G y - K y)) 2 volume := by
    have h := hd.sub hd'
    refine h.ae_eq (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    exact (drift_sub α a v u G K y).symm
  have hz : ∀ᵐ y ∂volume, driftField α a (fun y => v y - u y) (fun y => G y - K y) y +
      (fun y => P y - R y) y = 0 := by
    filter_upwards [he] with y hy
    show driftField α a (fun y => v y - u y) (fun y => G y - K y) y + (P y - R y) = 0
    rw [drift_sub, show driftField α a v G y - driftField α a u K y + (P y - R y) =
      (driftField α a v G y + P y) - (driftField α a u K y + R y) by abel, hy, sub_self]
  obtain ⟨z1, z2, z3, z4⟩ := h3 α hα1 hα2 a m _ _ _ _ hsd (hD α hα1 hα2 m v G H P u K L R hs hs' hp hp') hdd hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · filter_upwards [z1] with y hy; exact sub_eq_zero.mp hy
  · filter_upwards [z2] with y hy; exact sub_eq_zero.mp hy
  · filter_upwards [z3] with y hy; exact sub_eq_zero.mp hy
  · filter_upwards [z4] with y hy; exact sub_eq_zero.mp hy

theorem weakPower_smul {α : ℝ} {u R : Space → Space} (c : ℝ) (h : IsWeakFractionalPower α u R) :
    IsWeakFractionalPower α (fun y => c • u y) (fun y => c • R y) := by
  refine ⟨h.1.const_smul c, fun φ hφ => ?_⟩
  simp only [real_inner_smul_left, integral_const_mul, h.2 φ hφ]

theorem weakPower_add (hD : WeakPowerDifferenceStatement) (h7 : SecondOrderLinearStatement) {α : ℝ}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) {m : ℕ} {v u P R : Space → Space}
    {G K : Space → (Space →L[ℝ] Space)} {H L : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) (hs' : IsSecondOrderField m u K L)
    (hp : IsWeakFractionalPower α v P) (hp' : IsWeakFractionalPower α u R) :
    IsWeakFractionalPower α (fun y => v y + u y) (fun y => P y + R y) := by
  have hn := h7 m u u K K L L (-2) hs' hs'
  have e1 : (fun y => u y + (-2 : ℝ) • u y) = fun y => -u y := by
    funext y; module
  have e2 : (fun y => K y + (-2 : ℝ) • K y) = fun y => -K y := by
    funext y; module
  have e3 : (fun y => L y + (-2 : ℝ) • L y) = fun y => -L y := by
    funext y; module
  rw [e1, e2, e3] at hn
  have h := hD α hα1 hα2 m v G H P (fun y => -u y) (fun y => -K y) (fun y => -L y) (fun y => -R y) hs hn hp
    (weakPower_neg hp')
  simpa only [sub_neg_eq_add] using h

theorem drift_add_smul (α a c : ℝ) (v u : Space → Space) (G K : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun y => v y + c • u y) (fun y => G y + c • K y) y =
      driftField α a v G y + c • driftField α a u K y := by
  have hT : axialTurn (v y + c • u y) = axialTurn (v y) + c • axialTurn (u y) := by
    ext i
    fin_cases i <;> simp [axialTurn] <;> ring
  simp only [driftField, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, hT]
  module

theorem freeState (h2 : FreeExistsStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ)
    (f : solClass m) :
    ∃ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space))
      (P : Space → Space), IsSecondOrderField m v G H ∧ IsWeakFractionalPower α v P ∧
      MemLp (driftField α a v G) 2 volume ∧ ∀ᵐ y ∂volume, driftField α a v G y + P y = (f : FieldL2) y :=
  h2 α hα1 hα2 a m _ ((mem_solClass_iff m f).mp f.2).1 ((mem_solClass_iff m f).mp f.2).2

theorem state_lin (h3 : FreeUniqueStatement) (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement)
    {α a : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {m : ℕ} {v u w P R S : Space → Space}
    {G K M : Space → (Space →L[ℝ] Space)} {H L N : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (c : ℝ)
    (f g : FieldL2)
    (hs : IsSecondOrderField m v G H) (hs' : IsSecondOrderField m u K L) (hs'' : IsSecondOrderField m w M N)
    (hp : IsWeakFractionalPower α v P) (hp' : IsWeakFractionalPower α u R) (hp'' : IsWeakFractionalPower α w S)
    (hd : MemLp (driftField α a v G) 2 volume) (hd' : MemLp (driftField α a u K) 2 volume)
    (hd'' : MemLp (driftField α a w M) 2 volume)
    (he : ∀ᵐ y ∂volume, driftField α a v G y + P y = f y)
    (he' : ∀ᵐ y ∂volume, driftField α a u K y + R y = g y)
    (he'' : ∀ᵐ y ∂volume, driftField α a w M y + S y = (f + c • g) y) :
    (∀ᵐ y ∂volume, w y = v y + c • u y) ∧ (∀ᵐ y ∂volume, M y = G y + c • K y) := by
  have hsc := h7 m v u G K H L c hs hs'
  have hcu := h7 m u u K K L L (c - 1) hs' hs'
  have e1 : (fun y => u y + (c - 1) • u y) = fun y => c • u y := by funext y; module
  have e2 : (fun y => K y + (c - 1) • K y) = fun y => c • K y := by funext y; module
  have e3 : (fun y => L y + (c - 1) • L y) = fun y => c • L y := by funext y; module
  rw [e1, e2, e3] at hcu
  have hpc : IsWeakFractionalPower α (fun y => v y + c • u y) (fun y => P y + c • R y) :=
    weakPower_add hD h7 hα1 hα2 hs hcu hp (weakPower_smul c hp')
  have hdc : MemLp (driftField α a (fun y => v y + c • u y) (fun y => G y + c • K y)) 2 volume := by
    refine (hd.add (hd'.const_smul c)).ae_eq (Filter.Eventually.of_forall fun y => ?_)
    rw [drift_add_smul]
    rfl
  have hfg := Lp.coeFn_add f (c • g)
  have hcg := Lp.coeFn_smul c g
  have hec : ∀ᵐ y ∂volume, driftField α a w M y + S y =
      driftField α a (fun y => v y + c • u y) (fun y => G y + c • K y) y + (fun y => P y + c • R y) y := by
    filter_upwards [he, he', he'', hfg, hcg] with y h1 h2 h3' h4 h5
    rw [h3', h4, drift_add_smul]
    simp only [Pi.add_apply, Pi.smul_apply] at h5 ⊢
    rw [h5, ← h1, ← h2]
    module
  obtain ⟨z1, z2, -, -⟩ := state_unique h3 h7 hD hα1 hα2 hs'' hsc hp'' hpc hd'' hdc hec
  exact ⟨z1, z2⟩

structure FreeSol (α a : ℝ) (m : ℕ) (F : Space → Space) : Type where
  v : Space → Space
  G : Space → (Space →L[ℝ] Space)
  H : Space → (Space →L[ℝ] Space →L[ℝ] Space)
  P : Space → Space
  second : IsSecondOrderField m v G H
  power : IsWeakFractionalPower α v P
  drift : MemLp (driftField α a v G) 2 volume
  eq : ∀ᵐ y ∂volume, driftField α a v G y + P y = F y

def freeSol (h2 : FreeExistsStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ)
    (f : solClass m) : FreeSol α a m ((f : FieldL2) : Space → Space) :=
  Classical.choice (by
    obtain ⟨v, G, H, P, e1, e2, e3, e4⟩ := freeState h2 hα1 hα2 a m f
    exact ⟨⟨v, G, H, P, e1, e2, e3, e4⟩⟩)

theorem freeSol_lin (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h7 : SecondOrderLinearStatement)
    (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ)
    (f g f' : solClass m) (c : ℝ) (hf' : f' = f + c • g) :
    (∀ᵐ y ∂volume, (freeSol h2 hα1 hα2 a m f').v y =
      (freeSol h2 hα1 hα2 a m f).v y + c • (freeSol h2 hα1 hα2 a m g).v y) ∧
    (∀ᵐ y ∂volume, (freeSol h2 hα1 hα2 a m f').G y =
      (freeSol h2 hα1 hα2 a m f).G y + c • (freeSol h2 hα1 hα2 a m g).G y) := by
  subst hf'
  set s := freeSol h2 hα1 hα2 a m (f + c • g)
  set s1 := freeSol h2 hα1 hα2 a m f
  set s2 := freeSol h2 hα1 hα2 a m g
  exact state_lin h3 h7 hD hα1 hα2 c (f : FieldL2) (g : FieldL2) s1.second s2.second s.second s1.power
    s2.power s.power s1.drift s2.drift s.drift s1.eq s2.eq s.eq

theorem symProduct_add_smul (W : Space → Space) (DW : Space → (Space →L[ℝ] Space)) (v u : Space → Space)
    (G K : Space → (Space →L[ℝ] Space)) (c : ℝ) (y : Space) :
    symProduct W DW (fun y => v y + c • u y) (fun y => G y + c • K y) y =
      symProduct W DW v G y + c • symProduct W DW u K y := by
  simp only [symProduct, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, map_add, map_smul]
  module

theorem freeSol_zero (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h7 : SecondOrderLinearStatement)
    (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) :
    (∀ᵐ y ∂volume, (freeSol h2 hα1 hα2 a m 0).v y = 0) ∧ (∀ᵐ y ∂volume, (freeSol h2 hα1 hα2 a m 0).G y = 0) := by
  have h := freeSol_lin h2 h3 h7 hD hα1 hα2 a m 0 0 0 1 (by simp)
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with y hy
    rw [one_smul] at hy
    exact left_eq_add.mp hy
  · filter_upwards [h.2] with y hy
    rw [one_smul] at hy
    exact left_eq_add.mp hy

def prodMap (hI : InverseSquareBoundStatement) (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement)
    (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4)
    (a : ℝ) (m : ℕ) {W : Space → Space} {C : ℝ} (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    solClass m →ₗ[ℝ] FieldL2 where
  toFun f := (symProduct_memLp hI hW hb (freeSol h2 hα1 hα2 a m f).second).toLp _
  map_add' f g := by
    have h := freeSol_lin h2 h3 h7 hD hα1 hα2 a m f g (f + g) 1 (by rw [one_smul])
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [h.1, h.2] with y h1 h2
    rw [one_smul] at h1 h2
    simp only [Pi.add_apply, symProduct, h1, h2, ContinuousLinearMap.add_apply, map_add]
    module
  map_smul' c f := by
    have h := freeSol_lin h2 h3 h7 hD hα1 hα2 a m 0 f (c • f) c (by rw [zero_add])
    have h0 := freeSol_zero h2 h3 h7 hD hα1 hα2 a m
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [h.1, h.2, h0.1, h0.2] with y h1 h2 h3' h4
    simp only [Pi.smul_apply, symProduct, h1, h2, h3', h4, zero_add, ContinuousLinearMap.smul_apply, map_smul]
    module

theorem symProduct_pointwise {W v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (y : Space) (hy0 : y ≠ 0) :
    ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ≤
      1 / 2 * (C * ∑ i : Fin 3, ‖G y (unitVector i)‖ + C * (‖v y‖ / ‖y‖)) := by
  have hC : 0 ≤ C := by
    have h := (hb 0).1
    have hp : 0 < (1 + ‖(0 : Space)‖) ^ (-(1 : ℝ)) := by positivity
    nlinarith [norm_nonneg (W 0)]
  have hy : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  have hw1 : ‖W y‖ ≤ C := by
    have h := (hb y).1
    have hp : (1 + ‖y‖) ^ (-(1 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)
    nlinarith
  have hw2 : ‖fderiv ℝ W y‖ * ‖y‖ ≤ C := by
    have h := (hb y).2
    have hp : (1 + ‖y‖) ^ (-(2 : ℝ)) * ‖y‖ ≤ 1 := by
      rw [Real.rpow_neg (by positivity), Real.rpow_two, ← div_eq_inv_mul, div_le_one (by positivity)]
      nlinarith [norm_nonneg y]
    nlinarith [norm_nonneg (fderiv ℝ W y)]
  have h1 : ‖G y (W y)‖ ≤ C * ∑ i : Fin 3, ‖G y (unitVector i)‖ :=
    (norm_apply_le_entries (G y) (W y)).trans
      (mul_le_mul_of_nonneg_right hw1 (Finset.sum_nonneg fun i _ => norm_nonneg _))
  have h2 : ‖fderiv ℝ W y (v y)‖ ≤ C * (‖v y‖ / ‖y‖) := by
    refine ((fderiv ℝ W y).le_opNorm (v y)).trans ?_
    rw [mul_div_assoc', le_div_iff₀ hy]
    nlinarith [norm_nonneg (v y)]
  show ‖(1 / 2 : ℝ) • (G y (W y) + fderiv ℝ W y (v y))‖ ≤ _
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add h1 h2)) (by norm_num)

theorem symProduct_sq_bound (hI : InverseSquareBoundStatement) {m : ℕ} {W v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {C : ℝ}
    (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)))
    (hs : IsSecondOrderField m v G H) :
    ∫ y, ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2 ≤ 4 * C ^ 2 * ∫ y, entrySq (G y) := by
  obtain ⟨hIi, hIle⟩ := hI v G hs.measurable_velocity hs.velocity_six hs.gradient_two hs.weak_gradient
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    rw [ae_iff]
    simp
  have hrhs : Integrable (fun y => C ^ 2 * (3 / 2 * entrySq (G y) + 1 / 2 * (‖v y‖ ^ 2 / ‖y‖ ^ 2))) :=
    ((hs.gradient_two.const_mul _).add (hIi.const_mul _)).const_mul _
  have hmono : ∫ y, ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2 ≤
      ∫ y, C ^ 2 * (3 / 2 * entrySq (G y) + 1 / 2 * (‖v y‖ ^ 2 / ‖y‖ ^ 2)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity) hrhs ?_
    filter_upwards [hne] with y hy0
    have hp := symProduct_pointwise (v := v) (G := G) hb y hy0
    have hn := norm_nonneg (symProduct W (fun z => fderiv ℝ W z) v G y)
    have hE : (∑ i : Fin 3, ‖G y (unitVector i)‖) ^ 2 ≤ 3 * entrySq (G y) := by
      simp only [entrySq, Fin.sum_univ_three]
      nlinarith [sq_nonneg (‖G y (unitVector 0)‖ - ‖G y (unitVector 1)‖),
        sq_nonneg (‖G y (unitVector 1)‖ - ‖G y (unitVector 2)‖),
        sq_nonneg (‖G y (unitVector 0)‖ - ‖G y (unitVector 2)‖)]
    have hq : (‖v y‖ / ‖y‖) ^ 2 = ‖v y‖ ^ 2 / ‖y‖ ^ 2 := div_pow _ _ _
    set A := ∑ i : Fin 3, ‖G y (unitVector i)‖
    set B := ‖v y‖ / ‖y‖
    have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => norm_nonneg _
    have hB : 0 ≤ B := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsq : ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2 ≤ (1 / 2 * (C * A + C * B)) ^ 2 :=
      pow_le_pow_left₀ hn hp 2
    rw [← hq]
    nlinarith [sq_nonneg (A - B), sq_nonneg C, mul_nonneg (sq_nonneg C) (sq_nonneg (A - B))]
  have hpos : 0 ≤ ∫ y, entrySq (G y) := integral_nonneg fun y => entrySq_nonneg' (G y)
  calc ∫ y, ‖symProduct W (fun z => fderiv ℝ W z) v G y‖ ^ 2
      ≤ ∫ y, C ^ 2 * (3 / 2 * entrySq (G y) + 1 / 2 * (‖v y‖ ^ 2 / ‖y‖ ^ 2)) := hmono
    _ = C ^ 2 * (3 / 2 * (∫ y, entrySq (G y)) + 1 / 2 * ∫ y, ‖v y‖ ^ 2 / ‖y‖ ^ 2) := by
      rw [integral_const_mul, integral_add (hs.gradient_two.const_mul _) (hIi.const_mul _),
        integral_const_mul, integral_const_mul]
    _ ≤ 4 * C ^ 2 * ∫ y, entrySq (G y) := by
      nlinarith [mul_le_mul_of_nonneg_left hIle (sq_nonneg C), mul_nonneg (sq_nonneg C) hpos]

theorem fieldL2_norm_sq (F : FieldL2) : ‖F‖ ^ 2 = ∫ y, ‖F y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem toLp_norm_sq {F : Space → Space} (hF : MemLp F 2 volume) : ‖hF.toLp F‖ ^ 2 = ∫ y, ‖F y‖ ^ 2 := by
  rw [fieldL2_norm_sq]
  exact integral_congr_ae ((hF.coeFn_toLp).mono fun y hy => by simp only [hy])

def prodCLM (hI : InverseSquareBoundStatement) (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement)
    (h4 : FreeBoundsStatement) (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement) {α : ℝ}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) {W : Space → Space} {C : ℝ} (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    solClass m →L[ℝ] FieldL2 :=
  (prodMap hI h2 h3 h7 hD hα1 hα2 a m hW hb).mkContinuousOfExistsBound (by
    obtain ⟨C₀, hC₀⟩ := h4 α hα1 hα2
    refine ⟨2 * |C| * |C₀|, fun f => ?_⟩
    set s := freeSol h2 hα1 hα2 a m f
    have hB := (hC₀ a m s.v s.G s.H s.P ((f : FieldL2) : Space → Space) s.second s.power s.drift
      (Lp.memLp _) s.eq).2.2.2
    have hsq := symProduct_sq_bound hI hW hb s.second
    have hl : l2Norm ((f : FieldL2) : Space → Space) = ‖f‖ := by
      unfold l2Norm
      rw [← fieldL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rfl
    rw [hl] at hB
    have hE : Real.sqrt (∫ y, entrySq (s.G y)) ≤ |C₀| * ‖f‖ :=
      (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hB.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
    have hE2 : ∫ y, entrySq (s.G y) ≤ (|C₀| * ‖f‖) ^ 2 := by
      have h0 : 0 ≤ ∫ y, entrySq (s.G y) := integral_nonneg fun y => entrySq_nonneg' _
      calc ∫ y, entrySq (s.G y) = Real.sqrt (∫ y, entrySq (s.G y)) ^ 2 := (Real.sq_sqrt h0).symm
        _ ≤ (|C₀| * ‖f‖) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hE 2
    have hN : ‖prodMap hI h2 h3 h7 hD hα1 hα2 a m hW hb f‖ ^ 2 ≤ (2 * |C| * |C₀| * ‖f‖) ^ 2 := by
      show ‖(symProduct_memLp hI hW hb s.second).toLp _‖ ^ 2 ≤ _
      rw [toLp_norm_sq]
      calc _ ≤ 4 * C ^ 2 * ∫ y, entrySq (s.G y) := hsq
        _ ≤ 4 * C ^ 2 * (|C₀| * ‖f‖) ^ 2 := mul_le_mul_of_nonneg_left hE2 (by positivity)
        _ = (2 * |C| * |C₀| * ‖f‖) ^ 2 := by simp only [mul_pow, sq_abs]; ring
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp hN)

def entryMap (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h7 : SecondOrderLinearStatement)
    (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) (j : Fin 3) :
    solClass m →ₗ[ℝ] FieldL2 where
  toFun f := (entry_memLp (freeSol h2 hα1 hα2 a m f).second j).toLp _
  map_add' f g := by
    have h := freeSol_lin h2 h3 h7 hD hα1 hα2 a m f g (f + g) 1 (by rw [one_smul])
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    filter_upwards [h.2] with y h2
    rw [one_smul] at h2
    simp only [Pi.add_apply, h2, ContinuousLinearMap.add_apply]
  map_smul' c f := by
    have h := freeSol_lin h2 h3 h7 hD hα1 hα2 a m 0 f (c • f) c (by rw [zero_add])
    have h0 := freeSol_zero h2 h3 h7 hD hα1 hα2 a m
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    filter_upwards [h.2, h0.2] with y h2 h4
    simp only [Pi.smul_apply, h2, h4, zero_add, ContinuousLinearMap.smul_apply]

def entryCLM (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h4 : FreeBoundsStatement)
    (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α)
    (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) (j : Fin 3) : solClass m →L[ℝ] FieldL2 :=
  (entryMap h2 h3 h7 hD hα1 hα2 a m j).mkContinuousOfExistsBound (by
    obtain ⟨C₀, hC₀⟩ := h4 α hα1 hα2
    refine ⟨|C₀|, fun f => ?_⟩
    set s := freeSol h2 hα1 hα2 a m f
    have hB := (hC₀ a m s.v s.G s.H s.P ((f : FieldL2) : Space → Space) s.second s.power s.drift
      (Lp.memLp _) s.eq).2.2.2
    have hl : l2Norm ((f : FieldL2) : Space → Space) = ‖f‖ := by
      unfold l2Norm
      rw [← fieldL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rfl
    rw [hl] at hB
    have hE : Real.sqrt (∫ y, entrySq (s.G y)) ≤ |C₀| * ‖f‖ :=
      (le_add_of_nonneg_left (Real.sqrt_nonneg _)).trans (hB.trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)))
    have hj : ∫ y, ‖s.G y (unitVector j)‖ ^ 2 ≤ ∫ y, entrySq (s.G y) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
        s.second.gradient_two (Filter.Eventually.of_forall fun y => ?_)
      exact Finset.single_le_sum (f := fun i => ‖s.G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ j)
    have hN : ‖entryMap h2 h3 h7 hD hα1 hα2 a m j f‖ ≤ Real.sqrt (∫ y, entrySq (s.G y)) := by
      show ‖(entry_memLp s.second j).toLp _‖ ≤ _
      rw [← Real.sqrt_sq (norm_nonneg _), toLp_norm_sq]
      exact Real.sqrt_le_sqrt hj
    exact hN.trans hE)

theorem entry_memLp_of {χ : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable χ volume)
    (hi : Integrable (fun y => entrySq (χ y))) (j : Fin 3) : MemLp (fun y => χ y (unitVector j)) 2 volume := by
  have hm' : AEStronglyMeasurable (fun y => χ y (unitVector j)) volume := hm.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hm').mpr ?_
  refine hi.mono' (hm'.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact Finset.single_le_sum (f := fun i => ‖χ y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

def pinCLM (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h4 : FreeBoundsStatement)
    (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α)
    (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) {χ : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable χ volume)
    (hi : Integrable (fun y => entrySq (χ y))) : solClass m →L[ℝ] ℝ :=
  ∑ j : Fin 3, (innerSL ℝ ((entry_memLp_of hm hi j).toLp _)).comp (entryCLM h2 h3 h4 h7 hD hα1 hα2 a m j)

theorem pinCLM_apply (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement) (h4 : FreeBoundsStatement)
    (h7 : SecondOrderLinearStatement) (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α)
    (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ) {χ : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable χ volume)
    (hi : Integrable (fun y => entrySq (χ y))) (f : solClass m) :
    pinCLM h2 h3 h4 h7 hD hα1 hα2 a m hm hi f = pinValue χ (freeSol h2 hα1 hα2 a m f).G := by
  set s := freeSol h2 hα1 hα2 a m f
  have hj : ∀ j : Fin 3, inner ℝ ((entry_memLp_of hm hi j).toLp (fun y => χ y (unitVector j)))
      (entryCLM h2 h3 h4 h7 hD hα1 hα2 a m j f) = ∫ y, inner ℝ (s.G y (unitVector j)) (χ y (unitVector j)) := by
    intro j
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    have e2 : (entryCLM h2 h3 h4 h7 hD hα1 hα2 a m j f : Space → Space) =ᵐ[volume]
        fun y => s.G y (unitVector j) := (entry_memLp s.second j).coeFn_toLp
    filter_upwards [(entry_memLp_of hm hi j).coeFn_toLp, e2] with y hy1 hy2
    rw [hy1, hy2, real_inner_comm]
  have hint : ∀ j ∈ (Finset.univ : Finset (Fin 3)),
      Integrable (fun y => inner ℝ (s.G y (unitVector j)) (χ y (unitVector j))) := by
    intro j _
    have h := L2.integrable_inner (𝕜 := ℝ) ((entry_memLp s.second j).toLp _)
      ((entry_memLp_of hm hi j).toLp _)
    refine h.congr ?_
    filter_upwards [(entry_memLp s.second j).coeFn_toLp, (entry_memLp_of hm hi j).coeFn_toLp] with y h1 h2
    rw [h1, h2]
  unfold pinCLM pinValue entryInner
  rw [integral_finset_sum _ hint]
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, innerSL_apply_apply]
  exact Finset.sum_congr rfl fun j _ => hj j

theorem isCompactOperator_of_seq {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (T : E →L[ℝ] F)
    (h : ∀ x : ℕ → E, (∀ n, ‖x n‖ < 1) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ L : F, Filter.Tendsto (fun n => T (x (φ n))) Filter.atTop (nhds L)) :
    IsCompactOperator T := by
  refine (isCompactOperator_iff_isCompact_closure_image_ball (T : E →ₗ[ℝ] F) zero_lt_one).mpr ?_
  refine IsSeqCompact.isCompact fun u hu => ?_
  have hs : ∀ n, ∃ x : E, ‖x‖ < 1 ∧ dist (u n) (T x) < 1 / ((n : ℝ) + 1) := by
    intro n
    obtain ⟨b, hb, hd⟩ := Metric.mem_closure_iff.mp (hu n) (1 / ((n : ℝ) + 1)) (by positivity)
    obtain ⟨x, hx, rfl⟩ := hb
    exact ⟨x, by simpa using hx, hd⟩
  choose x hx hxd using hs
  obtain ⟨φ, hφ, L, hL⟩ := h x hx
  refine ⟨L, ?_, φ, hφ, ?_⟩
  · refine mem_closure_of_tendsto hL (Filter.Eventually.of_forall fun n => ?_)
    exact ⟨x (φ n), by simpa using hx (φ n), rfl⟩
  · rw [tendsto_iff_dist_tendsto_zero]
    have hε : Filter.Tendsto (fun n => 1 / ((φ n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
    have hL' := tendsto_iff_dist_tendsto_zero.mp hL
    refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (by simpa using hε.add hL')
    exact (dist_triangle _ (T (x (φ n))) L).trans (add_le_add (by simpa using (hxd (φ n)).le) le_rfl)

theorem prodCLM_compact (hI : InverseSquareBoundStatement) (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement)
    (h4 : FreeBoundsStatement) (h5 : ProfileProductCompactStatement) (h7 : SecondOrderLinearStatement)
    (hD : WeakPowerDifferenceStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) (a : ℝ) (m : ℕ)
    {W : Space → Space} {C : ℝ} (hW : ContDiff ℝ 1 W)
    (hb : ∀ y, ‖W y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧ ‖fderiv ℝ W y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) :
    IsCompactOperator (prodCLM hI h2 h3 h4 h7 hD hα1 hα2 a m hW hb) := by
  apply isCompactOperator_of_seq
  intro x hx
  obtain ⟨C₀, hC₀⟩ := h4 α hα1 hα2
  set s := fun n => freeSol h2 hα1 hα2 a m (x n)
  have hbd : ∀ n, (∫ y, entrySq ((s n).G y)) + (∫ y, ‖secondTrace ((s n).H y)‖ ^ 2) ≤ C₀ ^ 2 := by
    intro n
    have hB := (hC₀ a m (s n).v (s n).G (s n).H (s n).P (((x n : solClass m) : FieldL2) : Space → Space)
      (s n).second (s n).power (s n).drift (Lp.memLp _) (s n).eq).2.2.2
    have hl : l2Norm (((x n : solClass m) : FieldL2) : Space → Space) = ‖x n‖ := by
      unfold l2Norm
      rw [← fieldL2_norm_sq, Real.sqrt_sq (norm_nonneg _)]
      rfl
    rw [hl] at hB
    have h0 : 0 ≤ ∫ y, entrySq ((s n).G y) := integral_nonneg fun y => entrySq_nonneg' _
    have h1 : 0 ≤ ∫ y, ‖secondTrace ((s n).H y)‖ ^ 2 := integral_nonneg fun y => by positivity
    have hA := Real.sq_sqrt h0
    have hB' := Real.sq_sqrt h1
    have hs0 := Real.sqrt_nonneg (∫ y, entrySq ((s n).G y))
    have hs1 := Real.sqrt_nonneg (∫ y, ‖secondTrace ((s n).H y)‖ ^ 2)
    have hxn : ‖x n‖ ≤ 1 := (hx n).le
    have hC1 : C₀ * ‖x n‖ ≤ |C₀| := by
      calc C₀ * ‖x n‖ ≤ |C₀| * ‖x n‖ := mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
        _ ≤ |C₀| * 1 := mul_le_mul_of_nonneg_left hxn (abs_nonneg _)
        _ = |C₀| := mul_one _
    have hsum : Real.sqrt (∫ y, entrySq ((s n).G y)) + Real.sqrt (∫ y, ‖secondTrace ((s n).H y)‖ ^ 2) ≤ |C₀| := by
      linarith
    have hsq : (Real.sqrt (∫ y, entrySq ((s n).G y)) + Real.sqrt (∫ y, ‖secondTrace ((s n).H y)‖ ^ 2)) ^ 2 ≤
        |C₀| ^ 2 := pow_le_pow_left₀ (add_nonneg hs0 hs1) hsum 2
    rw [sq_abs] at hsq
    nlinarith [mul_nonneg hs0 hs1]
  obtain ⟨φ, L, hφ, hLm, hLt⟩ := h5 m W C hW hb (fun n => (s n).v) (fun n => (s n).G) (fun n => (s n).H)
    (C₀ ^ 2) (fun n => (s n).second) hbd
  refine ⟨φ, hφ, hLm.toLp L, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : ∀ n, ‖prodCLM hI h2 h3 h4 h7 hD hα1 hα2 a m hW hb (x (φ n)) - hLm.toLp L‖ =
      Real.sqrt (∫ y, ‖symProduct W (fun z => fderiv ℝ W z) (s (φ n)).v (s (φ n)).G y - L y‖ ^ 2) := by
    intro n
    have hsm := symProduct_memLp hI hW hb (s (φ n)).second
    have e1 : prodCLM hI h2 h3 h4 h7 hD hα1 hα2 a m hW hb (x (φ n)) = hsm.toLp _ := rfl
    rw [e1, ← MemLp.toLp_sub, ← toLp_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    rfl
  simp only [he]
  have hc := (Real.continuous_sqrt.tendsto 0).comp hLt
  rw [Real.sqrt_zero] at hc
  exact hc

theorem compact_perturbation {k : ℕ} (m : ℕ) (Bop : solClass m →L[ℝ] FieldL2) (hB : IsCompactOperator Bop)
    (A : (Fin k → ℝ) →L[ℝ] FieldL2) (pinV : solClass m →L[ℝ] (Fin k → ℝ)) :
    IsCompactOperator ((ContinuousLinearMap.inl ℝ (solClass m) (Fin k → ℝ)).comp
        ((solClass m).orthogonalProjection.comp
          (Bop.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) +
            A.comp (ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ)))) +
      (ContinuousLinearMap.inr ℝ (solClass m) (Fin k → ℝ)).comp
        (pinV.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) -
          ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ))) := by
  have hA : IsCompactOperator A := isCompactOperator_of_locallyCompactSpace_rng A
  have h1 : IsCompactOperator (Bop.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) +
      A.comp (ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ))) :=
    (hB.comp_clm _).add (hA.comp_clm _)
  have h2 := h1.clm_comp (solClass m).orthogonalProjection
  have h3 := h2.clm_comp (ContinuousLinearMap.inl ℝ (solClass m) (Fin k → ℝ))
  have h4 : IsCompactOperator (pinV.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) -
      ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ)) :=
    isCompactOperator_of_locallyCompactSpace_dom _
  have h5 := h4.clm_comp (ContinuousLinearMap.inr ℝ (solClass m) (Fin k → ℝ))
  exact h3.add h5

theorem surj_of_inj {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (K : X →L[ℝ] X)
    (hK : IsCompactOperator K) (hinj : ∀ x, x + K x = 0 → x = 0) : ∀ y, ∃ x, x + K x = y := by
  have hi : Function.Injective (((ContinuousLinearEquiv.refl ℝ X : X ≃L[ℝ] X) : X →L[ℝ] X) + K) := by
    intro x x' hxx
    have h0 : (x - x') + K (x - x') = 0 := by
      have hxx' : x + K x = x' + K x' := hxx
      rw [map_sub, show x - x' + (K x - K x') = (x + K x) - (x' + K x') by abel, hxx', sub_self]
    exact sub_eq_zero.mp (hinj _ h0)
  obtain ⟨e, he⟩ := exists_equiv_of_injective_compact_perturbation (ContinuousLinearEquiv.refl ℝ X) K
    (by simpa using hK) hi
  intro y
  refine ⟨e.symm y, ?_⟩
  have h := he (e.symm y)
  rw [ContinuousLinearEquiv.apply_symm_apply] at h
  exact h.symm

theorem class_congr {m : ℕ} {f g : Space → Space} (hf : IsClassField m f) (h : f =ᵐ[volume] g) :
    IsClassField m g := by
  have hT := (turnStep_measurePreserving m).quasiMeasurePreserving.ae_eq h
  have hM := mirror_measurePreserving.quasiMeasurePreserving.ae_eq h
  refine ⟨?_, ?_⟩
  · filter_upwards [hT, hf.1, h] with y h1 h2 h3
    have h1' : f (turnStep m y) = g (turnStep m y) := h1
    rw [← h1', h2, h3]
  · filter_upwards [hM, hf.2, h] with y h1 h2 h3
    have h1' : f (mirror y) = g (mirror y) := h1
    rw [← h1', h2, h3]

theorem sol_congr {f g : Space → Space} (hf : IsSolenoidalL2 f) (h : f =ᵐ[volume] g) : IsSolenoidalL2 g := by
  refine ⟨hf.1.ae_eq h, fun φ hφ => ?_⟩
  rw [← hf.2 φ hφ]
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem proj_split (h6 : SolenoidalSplitStatement) (h9 : GradientOrthogonalStatement) {m : ℕ} (X : FieldL2)
    (hX : IsClassField m X) :
    ∃ Q : Space → Space, IsGradientField Q ∧ MemLp Q 2 volume ∧
      ∀ᵐ y ∂volume, X y = ((solClass m).starProjection X) y + Q y := by
  obtain ⟨X₀, Q, hs, hc, hg, hQ2, he⟩ := h6 m X (Lp.memLp X) hX
  have ht := hs.1.coeFn_toLp
  have hmem : hs.1.toLp X₀ ∈ solClass m :=
    (mem_solClass_iff m _).mpr ⟨sol_congr hs ht.symm, class_congr hc ht.symm⟩
  have hproj : (solClass m).starProjection X = hs.1.toLp X₀ := by
    refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem fun w hw => ?_
    have hw' := ((mem_solClass_iff m w).mp hw).1
    rw [L2.inner_def]
    refine (integral_congr_ae ?_).trans (h9 Q w hg hQ2 hw')
    filter_upwards [Lp.coeFn_sub X (hs.1.toLp X₀), ht, he] with y h1 h2 h3
    rw [h1, Pi.sub_apply, h2, h3, add_sub_cancel_left]
  refine ⟨Q, hg, hQ2, ?_⟩
  rw [hproj]
  filter_upwards [ht, he] with y h1 h2
  rw [h1, h2]

theorem class_comb {m : ℕ} {f g : Space → Space} (hf : IsClassField m f) (hg : IsClassField m g) (c : ℝ) :
    IsClassField m (fun y => f y + c • g y) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with y h1 h2
    show f (turnStep m y) + c • g (turnStep m y) = turnStepLinear m (f y + c • g y)
    rw [map_add, map_smul, h1, h2]
    rfl
  · filter_upwards [hf.2, hg.2] with y h1 h2
    show f (mirror y) + c • g (mirror y) = mirrorLinear (f y + c • g y)
    rw [map_add, map_smul, h1, h2]
    rfl

theorem class_sum {m k : ℕ} {b : Fin k → Space → Space} (hb : ∀ i, IsClassField m (b i)) (κ : Fin k → ℝ) :
    IsClassField m (fun y => ∑ i, κ i • b i y) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_all_iff.mpr fun i => (hb i).1] with y hy
    show ∑ i, κ i • b i (turnStep m y) = turnStepLinear m (∑ i, κ i • b i y)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hy i]
    rfl
  · filter_upwards [ae_all_iff.mpr fun i => (hb i).2] with y hy
    show ∑ i, κ i • b i (mirror y) = mirrorLinear (∑ i, κ i • b i y)
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hy i]
    rfl

theorem gradient_neg' {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq, hQ2, hm, hw⟩ := hQ
  refine ⟨fun y => -q y, ?_, ?_, hm.neg, ?_⟩
  · simpa only [neg_sq] using hq
  · simpa only [norm_neg] using hQ2
  · intro φ hφ j
    have h := hw φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg, neg_neg]
    linarith

def actMap {k : ℕ} (b : Fin k → Space → Space) (hb : ∀ i, MemLp (b i) 2 volume) :
    (Fin k → ℝ) →ₗ[ℝ] FieldL2 where
  toFun κ := (memLp_finsetSum' Finset.univ fun i _ => (hb i).const_smul (κ i)).toLp
    (∑ i, κ i • b i)
  map_add' κ κ' := by
    rw [← MemLp.toLp_add, MemLp.toLp_eq_toLp_iff]
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c κ := by
    rw [RingHom.id_apply, ← MemLp.toLp_const_smul, MemLp.toLp_eq_toLp_iff]
    refine Filter.Eventually.of_forall fun y => ?_
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum]

theorem actMap_ae {k : ℕ} (b : Fin k → Space → Space) (hb : ∀ i, MemLp (b i) 2 volume) (κ : Fin k → ℝ) :
    (actMap b hb κ : Space → Space) =ᵐ[volume] fun y => ∑ i, κ i • b i y := by
  filter_upwards [(memLp_finsetSum' Finset.univ fun i _ => (hb i).const_smul (κ i)).coeFn_toLp] with y hy
  rw [show (actMap b hb κ : Space → Space) y = _ from hy]
  simp only [Finset.sum_apply, Pi.smul_apply]

theorem fullField_split {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (y : Space) :
    d.fullField α p v G H P κ y = (driftField α (d.rotationRate p) v G y + P y) +
      ((∑ i, κ i • d.actuator i y) + (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) v G y) := by
  simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField]
  abel

theorem linearSolve_of_kernel' (h2 : FreeExistsStatement) (h3 : FreeUniqueStatement)
    (h4 : FreeBoundsStatement) (h5 : ProfileProductCompactStatement) (h6 : SolenoidalSplitStatement)
    (h7 : SecondOrderLinearStatement) (h9 : GradientOrthogonalStatement) (h10 : ProductClassStatement)
    (h11 : InverseSquareBoundStatement) (h12 : WeakPowerDifferenceStatement) (hK : LinearKernelStatement) :
    LinearSolveStatement := by
  intro α hα1 hα2 k N d hd p hp F hF hFc z
  have hW : ContDiff ℝ 1 (d.profile p) := hd.profile_smooth p hp
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hb : ∀ y, ‖d.profile p y‖ ≤ C * (1 + ‖y‖) ^ (-(1 : ℝ)) ∧
      ‖fderiv ℝ (d.profile p) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := fun y => ⟨(hC p hp y).1, (hC p hp y).2.1⟩
  set m := d.order with hm
  set a := d.rotationRate p with ha
  set P0 := prodCLM h11 h2 h3 h4 h7 h12 hα1 hα2 a m hW hb with hP0
  have hP0c : IsCompactOperator P0 := prodCLM_compact h11 h2 h3 h4 h5 h7 h12 hα1 hα2 a m hW hb
  set Bop : solClass m →L[ℝ] FieldL2 := (2 : ℝ) • P0 with hBop
  have hBc : IsCompactOperator Bop := by
    rw [hBop]
    exact hP0c.smul (2 : ℝ)
  set A : (Fin k → ℝ) →L[ℝ] FieldL2 := LinearMap.toContinuousLinearMap (actMap d.actuator hd.actuator_two)
    with hA
  set pinV : solClass m →L[ℝ] (Fin k → ℝ) :=
    ContinuousLinearMap.pi fun i => pinCLM h2 h3 h4 h7 h12 hα1 hα2 a m (hd.pin_measurable i).1 (hd.pin_two i).1
    with hpinV
  set Kop := (ContinuousLinearMap.inl ℝ (solClass m) (Fin k → ℝ)).comp
        ((solClass m).orthogonalProjection.comp
          (Bop.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) +
            A.comp (ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ)))) +
      (ContinuousLinearMap.inr ℝ (solClass m) (Fin k → ℝ)).comp
        (pinV.comp (ContinuousLinearMap.fst ℝ (solClass m) (Fin k → ℝ)) -
          ContinuousLinearMap.snd ℝ (solClass m) (Fin k → ℝ)) with hKop
  have hKc := compact_perturbation m Bop hBc A pinV
  have hKapp : ∀ f κ, Kop (f, κ) = ((solClass m).orthogonalProjection (Bop f + A κ), pinV f - κ) := by
    intro f κ
    simp [hKop]
  set sol := fun f => freeSol h2 hα1 hα2 a m f with hsol
  have hX : ∀ f κ, ((Bop f + A κ : FieldL2) : Space → Space) =ᵐ[volume] fun y =>
      (∑ i, κ i • d.actuator i y) + (2 : ℝ) • symProduct (d.profile p) (d.gradProfile p) (sol f).v (sol f).G y := by
    intro f κ
    have e1 : P0 f = (symProduct_memLp h11 hW hb (sol f).second).toLp _ := rfl
    filter_upwards [Lp.coeFn_add (Bop f) (A κ), Lp.coeFn_smul (2 : ℝ) (P0 f),
      (symProduct_memLp h11 hW hb (sol f).second).coeFn_toLp, actMap_ae d.actuator hd.actuator_two κ]
      with y h1 h2' h3' h4'
    rw [h1, Pi.add_apply]
    have eB : (Bop f : Space → Space) y = (2 : ℝ) • (P0 f : Space → Space) y := by
      rw [hBop]; exact h2'
    have eA : (A κ : Space → Space) y = ∑ i, κ i • d.actuator i y := h4'
    rw [eB, eA, e1, h3']
    exact add_comm _ _
  have hXc : ∀ f κ, IsClassField m ((Bop f + A κ : FieldL2) : Space → Space) := fun f κ =>
    class_congr (class_comb (class_sum hd.actuator_class κ)
      (h10 m (d.profile p) (sol f).v (sol f).G (sol f).H hW (hd.profile_class p hp) (sol f).second) 2)
      (hX f κ).symm
  have hpins : ∀ f i, pinV f i = d.pins (sol f).G i := fun f i =>
    pinCLM_apply h2 h3 h4 h7 h12 hα1 hα2 a m (hd.pin_measurable i).1 (hd.pin_two i).1 f
  have hstate : ∀ f, d.IsLinearState α p (sol f).v (sol f).G (sol f).H (sol f).P := fun f =>
    ⟨(sol f).second, (sol f).power, (sol f).drift⟩
  have hinj : ∀ x, x + Kop x = 0 → x = 0 := by
    rintro ⟨f, κ⟩ hx
    rw [hKapp, Prod.mk_add_mk, Prod.mk_eq_zero] at hx
    obtain ⟨hx1, hx2⟩ := hx
    have hpin : pinV f = 0 := by rw [add_sub_cancel] at hx2; exact hx2
    obtain ⟨Q, hQ, -, hXQ⟩ := proj_split h6 h9 (Bop f + A κ) (hXc f κ)
    have hf : (f : FieldL2) = -((solClass m).starProjection (Bop f + A κ)) := by
      have h := congrArg Subtype.val hx1
      simp only [Submodule.coe_add, Submodule.coe_zero] at h
      rw [eq_neg_iff_add_eq_zero]
      exact h
    have hfa : ((f : FieldL2) : Space → Space) =ᵐ[volume]
        fun y => -(((solClass m).starProjection (Bop f + A κ) : FieldL2) : Space → Space) y := by
      rw [hf]; exact Lp.coeFn_neg _
    have hff : ∃ Q' : Space → Space, IsGradientField Q' ∧
        ∀ᵐ y ∂volume, d.fullField α p (sol f).v (sol f).G (sol f).H (sol f).P κ y = Q' y := by
      refine ⟨Q, hQ, ?_⟩
      filter_upwards [(sol f).eq, hfa, hXQ, hX f κ] with y e1 e2 e3 e4
      rw [fullField_split, e1, e2, ← e4, e3]
      abel
    obtain ⟨hz, hκ⟩ := hK α hα1 hα2 d hd p hp _ _ _ _ (hstate f) κ hff
      (fun i => by rw [← hpins f i, hpin]; rfl)
    have hf0 : f = 0 := by
      apply Subtype.ext
      apply Lp.ext
      filter_upwards [(sol f).eq, hz, Lp.coeFn_zero Space 2 (volume : Measure Space)] with y e1 e2 e3
      rw [Submodule.coe_zero, e3, ← e1, e2]
      rfl
    rw [hf0, hκ]
    rfl
  obtain ⟨⟨f, κ⟩, hx⟩ := surj_of_inj Kop hKc hinj ((solClass m).orthogonalProjection (hF.toLp F), z)
  rw [hKapp, Prod.mk_add_mk, Prod.mk.injEq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hpin : pinV f = z := by rw [add_sub_cancel] at hx2; exact hx2
  set X := Bop f + A κ with hXdef
  have hYc : IsClassField m ((hF.toLp F - X : FieldL2) : Space → Space) := by
    have h := class_comb hFc (hXc f κ) (-1)
    refine class_congr h ?_
    filter_upwards [Lp.coeFn_sub (hF.toLp F) X, hF.coeFn_toLp] with y e1 e2
    rw [e1, Pi.sub_apply, e2, neg_one_smul, sub_eq_add_neg]
  obtain ⟨Q, hQ, -, hYQ⟩ := proj_split h6 h9 (hF.toLp F - X) hYc
  have hf : (f : FieldL2) = (solClass m).starProjection (hF.toLp F - X) := by
    have h := congrArg Subtype.val hx1
    simp only [Submodule.coe_add] at h
    rw [map_sub, eq_sub_iff_add_eq]
    exact h
  refine ⟨(sol f).v, (sol f).G, (sol f).H, (sol f).P, κ, hstate f, ⟨fun y => -Q y, gradient_neg' hQ, ?_⟩,
    fun i => by rw [← hpins f i, hpin]⟩
  have hfa : ((f : FieldL2) : Space → Space) =ᵐ[volume]
      (((solClass m).starProjection (hF.toLp F - X) : FieldL2) : Space → Space) := by rw [hf]
  filter_upwards [(sol f).eq, hfa, hYQ, hX f κ, Lp.coeFn_sub (hF.toLp F) X, hF.coeFn_toLp] with y e1 e2 e3 e4 e5 e6
  rw [fullField_split, e1, e2, ← e4]
  rw [e5, Pi.sub_apply, e6] at e3
  rw [show (((solClass m).starProjection (hF.toLp F - X) : FieldL2) : Space → Space) y =
    F y - (X : Space → Space) y - Q y by rw [e3]; abel]
  abel

end LinearSolveCore

end SteadyCert

end Breakdown

import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes

open scoped ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace TailBand

namespace Internal.AngularPlane

open Coercive Coercive.Internal.ModeRotation

theorem rot_entry (ψ : ℝ) (i j : Fin 3) :
    axialRot ψ (unitVector j) i =
      ![![Real.cos ψ, -Real.sin ψ, 0], ![Real.sin ψ, Real.cos ψ, 0], ![0, 0, 1]] i j := by
  fin_cases i <;> fin_cases j <;> simp [axialRot, unitVector]

theorem rot_col_orth (ψ : ℝ) (j k : Fin 3) :
    ∑ i : Fin 3, axialRot ψ (unitVector j) i * axialRot ψ (unitVector k) i = if j = k then 1 else 0 := by
  simp only [rot_entry, Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;> simp <;> nlinarith [Real.sin_sq_add_cos_sq ψ]

theorem rot_row_orth (ψ : ℝ) (j k : Fin 3) :
    ∑ i : Fin 3, axialRot ψ (unitVector i) j * axialRot ψ (unitVector i) k = if j = k then 1 else 0 := by
  simp only [rot_entry, Fin.sum_univ_three]
  fin_cases j <;> fin_cases k <;> simp <;> nlinarith [Real.sin_sq_add_cos_sq ψ]

theorem alt_rot (ψ : ℝ) (i c a : Fin 3) :
    ∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l * axialRot (-ψ) (unitVector j) c
        * axialRot ψ (unitVector a) l =
      ∑ k : Fin 3, axialRot ψ (unitVector k) i * alternatingSymbol k c a := by
  fin_cases i <;> fin_cases c <;> fin_cases a <;>
    simp [axialRot, unitVector, Fin.sum_univ_three, alternatingSymbol] <;> norm_num <;>
    first | ring1 | linear_combination Real.sin_sq_add_cos_sq ψ | linear_combination -Real.sin_sq_add_cos_sq ψ

theorem cnormSq_orth {β : Type*} [Fintype β] [DecidableEq β] (M : β → β → ℝ)
    (hM : ∀ b b', ∑ a, M a b * M a b' = if b = b' then 1 else 0) (x : β → ℂ) :
    cnormSq (fun a => ∑ b, (M a b : ℂ) * x b) = cnormSq x := by
  have hn : ∀ y : ℂ, ‖y‖ ^ 2 = (y * (starRingEnd ℂ) y).re := fun y => by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  unfold cnormSq
  simp_rw [hn, ← Complex.re_sum]
  congr 1
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]
  have e : ∀ b', ∑ a, (M a b : ℂ) * x b * ((M a b' : ℂ) * (starRingEnd ℂ) (x b')) =
      ((∑ a, M a b * M a b' : ℝ) : ℂ) * (x b * (starRingEnd ℂ) (x b')) := by
    intro b'
    push_cast
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    ring
  simp_rw [e, hM]
  rw [Finset.sum_eq_single b (fun b' _ hb' => by rw [if_neg (Ne.symm hb')]; simp) (by simp)]
  simp

def rotTensor (ψ : ℝ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) : Fin 3 × Fin 3 × Fin 3 → ℂ :=
  fun ijl => ∑ abc : Fin 3 × Fin 3 × Fin 3, ((axialRot ψ (unitVector abc.1) ijl.1
    * axialRot (-ψ) (unitVector ijl.2.1) abc.2.1 * axialRot (-ψ) (unitVector ijl.2.2) abc.2.2 : ℝ) : ℂ) * h abc

theorem modeAverage_rotate {β : Type*} [Fintype β] (ι : ℤ × ℤ) (ψ : ℝ) (I J : ℝ → ℝ → β → ℝ)
    (M : β → β → ℝ) (hJp : ∀ τ φ b, J τ (φ + 2 * Real.pi) b = J τ φ b)
    (hJi : ∀ b, Integrable (fun p : ℝ × ℝ => J p.1 p.2 b) boxMeasure)
    (hIJ : ∀ τ φ b, I τ φ b = ∑ b', M b b' * J τ (φ + ψ) b') (b : β) :
    modeAverage ι I b =
      Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * ∑ b', (M b b' : ℂ) * modeAverage ι J b' := by
  have hq : ∀ τ, Function.Periodic (fun φ => ((∑ b', M b b' * J τ φ b' : ℝ) : ℂ)) (2 * Real.pi) := by
    intro τ φ
    simp only [hJp]
  have e := modeAverage_sum ι (M b) (fun b' τ φ => J τ φ b') hJi
  calc modeAverage ι I b
      = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
          expFactor ι τ φ * (fun φ => ((∑ b', M b b' * J τ φ b' : ℝ) : ℂ)) (φ + ψ) := by
        rw [modeAverage_eq]
        simp only [hIJ]
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) *
          ∫ φ in (0 : ℝ)..(2 * Real.pi), expFactor ι τ φ * ((∑ b', M b b' * J τ φ b' : ℝ) : ℂ) := by
        congr 1
        refine intervalIntegral.integral_congr fun τ _ => ?_
        exact integral_shift ι τ ψ _ (hq τ)
    _ = _ := by
        rw [intervalIntegral.integral_const_mul, e]
        simp only [modeAverage_eq, Finset.mul_sum]
        refine Finset.sum_congr rfl fun b' _ => ?_
        ring

theorem integrable_secondDerivComponent (hRot : AxialRotationHolds)
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure)
    (abc : Fin 3 × Fin 3 × Fin 3) :
    Integrable (fun p : ℝ × ℝ => axialRot (-p.2) (H (z.1 + p.1) (axialRot p.2 z.2)
      (axialRot p.2 (unitVector abc.2.1)) (axialRot p.2 (unitVector abc.2.2))) abc.1) boxMeasure := by
  refine hz.norm.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector abc.2.1)) (axialRot q.1.2 (unitVector abc.2.2)))
          abc.1) := by
      unfold axialRot
      fun_prop
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p, H (z.1 + p.1) (axialRot p.2 z.2))) boxMeasure :=
      aestronglyMeasurable_id.prodMk hz.1
    have h2 := hc.comp_aestronglyMeasurable hm
    exact h2
  · refine (PiLp.norm_apply_le _ abc.1).trans ?_
    rw [norm_axialRot hRot]
    have hu : ∀ (m : Fin 3) (φ : ℝ), ‖axialRot φ (unitVector m)‖ = 1 := by
      intro m φ
      rw [norm_axialRot hRot, unitVector, PiLp.norm_single, norm_one]
    calc _ ≤ ‖H (z.1 + p.1) (axialRot p.2 z.2) (axialRot p.2 (unitVector abc.2.1))‖
          * ‖axialRot p.2 (unitVector abc.2.2)‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖H (z.1 + p.1) (axialRot p.2 z.2)‖ * ‖axialRot p.2 (unitVector abc.2.1)‖
          * ‖axialRot p.2 (unitVector abc.2.2)‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ = _ := by rw [hu, hu, mul_one, mul_one]

theorem coord_sum3 (r : Fin 3 → Fin 3 → ℝ) (Y : Fin 3 → Fin 3 → Space) (a : Fin 3) :
    (∑ b, ∑ c, r b c • Y b c) a = ∑ b, ∑ c, r b c * Y b c a := by
  simp

theorem modeSecondDeriv_rotation_of (hRot : AxialRotationHolds)
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (ι : ℤ × ℤ) (ψ : ℝ) {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) boxMeasure) :
    modeSecondDeriv ι H z.1 (axialRot ψ z.2) =
      fun ijl => Complex.exp (((ι.2 * ψ : ℝ) : ℂ) * Complex.I) * rotTensor ψ (modeSecondDeriv ι H z.1 z.2) ijl := by
  funext ijl
  have key := modeAverage_rotate ι ψ
    (fun τ φ (ijl : Fin 3 × Fin 3 × Fin 3) => axialRot (-φ) (H (z.1 + τ) (axialRot φ (axialRot ψ z.2)) (axialRot φ (unitVector ijl.2.1))
      (axialRot φ (unitVector ijl.2.2))) ijl.1)
    (fun τ φ (abc : Fin 3 × Fin 3 × Fin 3) => axialRot (-φ) (H (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector abc.2.1))
      (axialRot φ (unitVector abc.2.2))) abc.1)
    (fun (ijl abc : Fin 3 × Fin 3 × Fin 3) => axialRot ψ (unitVector abc.1) ijl.1
      * axialRot (-ψ) (unitVector ijl.2.1) abc.2.1 * axialRot (-ψ) (unitVector ijl.2.2) abc.2.2) ?_
    (integrable_secondDerivComponent hRot hz) ?_ ijl
  · unfold modeSecondDeriv rotTensor
    beta_reduce at key ⊢
    exact key
  · intro τ φ abc
    simp only [show -(φ + 2 * Real.pi) = -φ - 2 * Real.pi by ring, axialRot_sub_period hRot,
      hRot.2.2.2.1]
  · intro τ φ ijl
    obtain ⟨R, hR⟩ := hRot.1 (-(φ + ψ))
    have hu : ∀ m : Fin 3, axialRot φ (unitVector m) =
        ∑ b : Fin 3, axialRot (-ψ) (unitVector m) b • axialRot (φ + ψ) (unitVector b) := by
      intro m
      rw [← axialRot_eq_sum, ← hRot.2.1]
      congr 1
      ring
    simp only
    rw [← hRot.2.1, axialRot_neg_comp hRot φ ψ, axialRot_apply ψ _ ijl.1, hu, hu, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    simp only [map_sum, map_smul, FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply, ← hR]
    simp only [hR, Finset.smul_sum, smul_smul]
    rw [coord_sum3]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    ring

theorem orth_prod {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (A : α → α → ℝ) (B : β → β → ℝ) (hA : ∀ a a', ∑ i, A i a * A i a' = if a = a' then 1 else 0)
    (hB : ∀ b b', ∑ j, B j b * B j b' = if b = b' then 1 else 0) (p q : α × β) :
    ∑ r : α × β, A r.1 p.1 * B r.2 p.2 * (A r.1 q.1 * B r.2 q.2) = if p = q then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  have e : ∑ i, ∑ j, A (i, j).1 p.1 * B (i, j).2 p.2 * (A (i, j).1 q.1 * B (i, j).2 q.2) =
      (∑ i, A i p.1 * A i q.1) * ∑ j, B j p.2 * B j q.2 := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e, hA, hB]
  by_cases h1 : p.1 = q.1 <;> by_cases h2 : p.2 = q.2 <;> simp [h1, h2, Prod.ext_iff]

theorem cnormSq_phase {β : Type*} [Fintype β] (c : ℂ) (hc : ‖c‖ = 1) (x : β → ℂ) :
    cnormSq (fun b => c * x b) = cnormSq x := by
  unfold cnormSq
  simp [hc]

theorem cnormSq_rotC (ψ : ℝ) (x : Fin 3 → ℂ) : cnormSq (rotC ψ x) = cnormSq x :=
  cnormSq_orth (fun i j => axialRot ψ (unitVector j) i) (rot_col_orth ψ) x

theorem cnormSq_rotCMat (ψ : ℝ) (g : Fin 3 × Fin 3 → ℂ) : cnormSq (rotCMat ψ g) = cnormSq g := by
  have e : rotCMat ψ g = fun ij => ∑ ac : Fin 3 × Fin 3,
      ((axialRot ψ (unitVector ac.1) ij.1 * axialRot (-ψ) (unitVector ij.2) ac.2 : ℝ) : ℂ) * g ac := by
    funext ij
    unfold rotCMat
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    push_cast
    ring
  rw [e]
  exact cnormSq_orth _ (orth_prod (fun i a => axialRot ψ (unitVector a) i)
    (fun j c => axialRot (-ψ) (unitVector j) c) (rot_col_orth ψ) (rot_row_orth (-ψ))) g

theorem cnormSq_rotTensor (ψ : ℝ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) : cnormSq (rotTensor ψ h) = cnormSq h := by
  have e : rotTensor ψ h = fun ijl => ∑ abc : Fin 3 × Fin 3 × Fin 3,
      ((axialRot ψ (unitVector abc.1) ijl.1 * (axialRot (-ψ) (unitVector ijl.2.1) abc.2.1
        * axialRot (-ψ) (unitVector ijl.2.2) abc.2.2) : ℝ) : ℂ) * h abc := by
    funext ijl
    unfold rotTensor
    simp only [mul_assoc]
  rw [e]
  have hB : ∀ p q : Fin 3 × Fin 3, ∑ r : Fin 3 × Fin 3,
      axialRot (-ψ) (unitVector r.1) p.1 * axialRot (-ψ) (unitVector r.2) p.2
        * (axialRot (-ψ) (unitVector r.1) q.1 * axialRot (-ψ) (unitVector r.2) q.2) = if p = q then 1 else 0 :=
    orth_prod (fun j b => axialRot (-ψ) (unitVector j) b) (fun j b => axialRot (-ψ) (unitVector j) b)
      (rot_row_orth (-ψ)) (rot_row_orth (-ψ))
  have hM := orth_prod (fun i a => axialRot ψ (unitVector a) i)
    (fun (jl bc : Fin 3 × Fin 3) => axialRot (-ψ) (unitVector jl.1) bc.1 * axialRot (-ψ) (unitVector jl.2) bc.2)
    (rot_col_orth ψ) hB
  exact cnormSq_orth (fun (ijl abc : Fin 3 × Fin 3 × Fin 3) => axialRot ψ (unitVector abc.1) ijl.1
    * (axialRot (-ψ) (unitVector ijl.2.1) abc.2.1 * axialRot (-ψ) (unitVector ijl.2.2) abc.2.2)) hM h

theorem curlOfGrad_phase (c : ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (fun ij => c * g ij) = fun i => c * curlOfGrad g i := by
  funext i
  unfold curlOfGrad
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem curlGradOfSecondDeriv_phase (c : ℂ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    curlGradOfSecondDeriv (fun ijl => c * h ijl) = fun il => c * curlGradOfSecondDeriv h il := by
  funext il
  unfold curlGradOfSecondDeriv
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem curlOfGrad_rotCMat (ψ : ℝ) (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (rotCMat ψ g) = rotC ψ (curlOfGrad g) := by
  funext i
  calc curlOfGrad (rotCMat ψ g) i
      = ∑ a : Fin 3, ∑ c : Fin 3, ((∑ j : Fin 3, ∑ l : Fin 3, alternatingSymbol i j l
          * axialRot (-ψ) (unitVector j) c * axialRot ψ (unitVector a) l : ℝ) : ℂ) * g (a, c) := by
        unfold curlOfGrad rotCMat
        push_cast
        simp only [Fin.sum_univ_three]
        ring
    _ = ∑ a : Fin 3, ∑ c : Fin 3, ((∑ k : Fin 3, axialRot ψ (unitVector k) i * alternatingSymbol k c a : ℝ) : ℂ)
          * g (a, c) := by
        simp only [alt_rot]
    _ = rotC ψ (curlOfGrad g) i := by
        unfold rotC curlOfGrad
        push_cast
        simp only [Fin.sum_univ_three]
        ring

theorem curlGradOfSecondDeriv_rotTensor (ψ : ℝ) (h : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    curlGradOfSecondDeriv (rotTensor ψ h) = rotCMat ψ (curlGradOfSecondDeriv h) := by
  funext il
  obtain ⟨i, l⟩ := il
  calc curlGradOfSecondDeriv (rotTensor ψ h) (i, l)
      = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ((∑ j : Fin 3, ∑ m : Fin 3, alternatingSymbol i j m
          * axialRot (-ψ) (unitVector j) c * axialRot ψ (unitVector a) m : ℝ) : ℂ)
          * ((axialRot (-ψ) (unitVector l) b : ℝ) : ℂ) * h (a, b, c) := by
        unfold curlGradOfSecondDeriv rotTensor
        push_cast
        simp only [Fintype.sum_prod_type, Fin.sum_univ_three]
        ring
    _ = ∑ a : Fin 3, ∑ b : Fin 3, ∑ c : Fin 3, ((∑ k : Fin 3, axialRot ψ (unitVector k) i
          * alternatingSymbol k c a : ℝ) : ℂ) * ((axialRot (-ψ) (unitVector l) b : ℝ) : ℂ) * h (a, b, c) := by
        simp only [alt_rot]
    _ = rotCMat ψ (curlGradOfSecondDeriv h) (i, l) := by
        unfold rotCMat curlGradOfSecondDeriv
        push_cast
        simp only [Fin.sum_univ_three]
        ring

theorem modeSecondDeriv_shift (ι : ℤ × ℤ) {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hH : IsTimePeriodic H)
    (σ : ℝ) (y : Space) :
    modeSecondDeriv ι H σ y = fun ijl =>
      Complex.exp (((2 * Real.pi * ι.1 * σ : ℝ) : ℂ) * Complex.I) * modeSecondDeriv ι H 0 y ijl := by
  funext ijl
  have h := Coercive.FrequencySeminorm.Internal.modeAverage_shift ι
    (fun t φ (ijl : Fin 3 × Fin 3 × Fin 3) => axialRot (-φ) (H t (axialRot φ y) (axialRot φ (unitVector ijl.2.1))
      (axialRot φ (unitVector ijl.2.2))) ijl.1) (fun t φ b => by simp only [hH t]) σ ijl
  unfold modeSecondDeriv
  simpa only [zero_add] using h

theorem norm_phase (x : ℝ) : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I x

end Internal.AngularPlane

end TailBand

end CertCell

end Breakdown

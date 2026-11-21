import Breakdown.FracCell.SharpYClassCrossSt
import Breakdown.FracCell.SharpCircleMean
import Breakdown.FracCell.ClassRowSq

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.ClassProductSplit

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis SteadyCert Assembly
open Breakdown.CellCert.CellFormula.Internal.RelTrace
open Breakdown.CellCert.CellEnergy.Internal.CircleWeak
open Breakdown.CellCert.CellFormula.FormulaYLinearInternal

def ph (m : ℕ) (k : ℤ) (θ : ℝ) : ℂ := Complex.exp ((azimuth m k * θ : ℝ) * Complex.I)

theorem ph_mul (m : ℕ) (a b : ℤ) (θ : ℝ) : ph m a θ * ph m b θ = ph m (a + b) θ := by
  unfold ph
  rw [← Complex.exp_add]
  congr 1
  simp only [azimuth]
  push_cast
  ring

theorem ph_conj (m : ℕ) (a : ℤ) (θ : ℝ) : (starRingEnd ℂ) (ph m a θ) = ph m (-a) θ := by
  unfold ph
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, azimuth]
  push_cast
  ring

theorem ph_zero (m : ℕ) (θ : ℝ) : ph m 0 θ = 1 := by simp [ph, azimuth]

theorem ph_cont (m : ℕ) (k : ℤ) : Continuous (ph m k) := by
  unfold ph
  fun_prop

theorem tp_cont (m : ℕ) (L : Finset ℤ) (x : ℤ → ℂ) : Continuous fun θ => ∑ n ∈ L, x n * ph m n θ :=
  continuous_finsetSum _ fun n _ => continuous_const.mul (ph_cont m n)

def avg (f : ℝ → ℂ) : ℂ := ∫ θ in Ioo (-Real.pi) Real.pi, ((1 / (2 * Real.pi) : ℝ) : ℂ) * f θ

theorem int_of_cont {f : ℝ → ℂ} (hf : Continuous f) :
    Integrable f (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
  (hf.integrableOn_Icc (a := -Real.pi) (b := Real.pi)).mono_set Ioo_subset_Icc_self

theorem avg_add {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    avg (fun θ => f θ + g θ) = avg f + avg g := by
  unfold avg
  simp only [mul_add]
  exact integral_add ((int_of_cont hf).const_mul _) ((int_of_cont hg).const_mul _)

theorem avg_sub {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    avg (fun θ => f θ - g θ) = avg f - avg g := by
  unfold avg
  simp only [mul_sub]
  exact integral_sub ((int_of_cont hf).const_mul _) ((int_of_cont hg).const_mul _)

theorem avg_mul (c : ℂ) (f : ℝ → ℂ) : avg (fun θ => c * f θ) = c * avg f := by
  unfold avg
  simp only [mul_left_comm _ c]
  exact integral_const_mul _ _

theorem avg_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, Continuous (f i)) :
    avg (fun θ => ∑ i ∈ s, f i θ) = ∑ i ∈ s, avg (f i) := by
  unfold avg
  simp only [Finset.mul_sum]
  exact integral_finsetSum s fun i hi => (int_of_cont (hf i hi)).const_mul _

theorem avg_ph {m : ℕ} (hm : 1 ≤ m) (k : ℤ) : avg (ph m k) = if k = 0 then 1 else 0 := by
  have h := ClassRowSq.orth_circ hm k 0
  have e : ∀ θ : ℝ, (starRingEnd ℂ) (Complex.exp ((azimuth m 0 * θ : ℝ) * Complex.I)) = 1 := by
    intro θ
    simp [azimuth]
  simp only [e, mul_one] at h
  exact h

theorem avg_re_mono {f : ℝ → ℂ} {g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ θ, g θ ≤ (f θ).re) : (avg fun θ => (g θ : ℂ)).re ≤ (avg f).re := by
  have h1 := (int_of_cont (Complex.continuous_ofReal.comp hg)).const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  have h2 := (int_of_cont hf).const_mul (((1 / (2 * Real.pi) : ℝ) : ℂ))
  unfold avg
  have hp : 0 ≤ 1 / (2 * Real.pi) := by positivity
  calc (∫ θ in Ioo (-Real.pi) Real.pi, ((1 / (2 * Real.pi) : ℝ) : ℂ) * (g θ : ℂ)).re
      = ∫ θ in Ioo (-Real.pi) Real.pi, (((1 / (2 * Real.pi) : ℝ) : ℂ) * (g θ : ℂ)).re := by
        exact (integral_re h1).symm
    _ ≤ ∫ θ in Ioo (-Real.pi) Real.pi, (((1 / (2 * Real.pi) : ℝ) : ℂ) * f θ).re := by
        refine integral_mono h1.re h2.re fun θ => ?_
        simp only [Complex.re_ofReal_mul, Complex.ofReal_re]
        exact mul_le_mul_of_nonneg_left (h θ) hp
    _ = (∫ θ in Ioo (-Real.pi) Real.pi, ((1 / (2 * Real.pi) : ℝ) : ℂ) * f θ).re := by
        exact integral_re h2

theorem tri_point (m : ℕ) (L F M : Finset ℤ) (x z y : ℤ → ℂ) (θ : ℝ) :
    (starRingEnd ℂ) (∑ n ∈ L, x n * ph m n θ) * (∑ β ∈ M, z β * ph m β θ) * (∑ n' ∈ F, y n' * ph m n' θ)
      = ∑ n ∈ L, ∑ n' ∈ F, ∑ β ∈ M, ((starRingEnd ℂ) (x n) * z β * y n') * ph m (β + n' - n) θ := by
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul_sum]
  simp only [Finset.sum_mul]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => Finset.sum_congr rfl fun β _ => ?_
  rw [map_mul, ph_conj, show β + n' - n = (-n + β) + n' by ring, ← ph_mul, ← ph_mul]
  ring

theorem avg_tri {m : ℕ} (hm : 1 ≤ m) (L F M : Finset ℤ) (x z y : ℤ → ℂ) :
    avg (fun θ => (starRingEnd ℂ) (∑ n ∈ L, x n * ph m n θ) * (∑ β ∈ M, z β * ph m β θ) *
        (∑ n' ∈ F, y n' * ph m n' θ))
      = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then (starRingEnd ℂ) (x n) * z (n - n') * y n' else 0 := by
  simp only [tri_point]
  rw [avg_sum]
  swap
  · exact fun n _ => continuous_finsetSum _ fun n' _ => continuous_finsetSum _ fun β _ =>
      continuous_const.mul (ph_cont m _)
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [avg_sum]
  swap
  · exact fun n' _ => continuous_finsetSum _ fun β _ => continuous_const.mul (ph_cont m _)
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [avg_sum]
  swap
  · exact fun β _ => continuous_const.mul (ph_cont m _)
  simp only [avg_mul, avg_ph hm, mul_ite, mul_one, mul_zero]
  have e : ∀ β : ℤ, (β + n' - n = 0) ↔ (n - n' = β) := fun β => by omega
  simp only [e]
  rw [Finset.sum_ite_eq]

theorem swap4 {ι κ : Type*} [Fintype ι] [Fintype κ] (L F : Finset ℤ) (g : ι → κ → ℤ → ℤ → ℂ) :
    ∑ a, ∑ b, ∑ n ∈ L, ∑ n' ∈ F, g a b n n' = ∑ n ∈ L, ∑ n' ∈ F, ∑ a, ∑ b, g a b n n' := by
  calc ∑ a, ∑ b, ∑ n ∈ L, ∑ n' ∈ F, g a b n n'
      = ∑ a, ∑ n ∈ L, ∑ b, ∑ n' ∈ F, g a b n n' := Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ n ∈ L, ∑ a, ∑ b, ∑ n' ∈ F, g a b n n' := Finset.sum_comm
    _ = ∑ n ∈ L, ∑ a, ∑ n' ∈ F, ∑ b, g a b n n' :=
        Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ n ∈ L, ∑ n' ∈ F, ∑ a, ∑ b, g a b n n' := Finset.sum_congr rfl fun n _ => Finset.sum_comm

theorem avg_form {m : ℕ} (hm : 1 ≤ m) {ι κ : Type*} [Fintype ι] [Fintype κ] (L F M : Finset ℤ)
    (x : ℤ → ι → ℂ) (z : ℤ → ι → κ → ℂ) (y : ℤ → κ → ℂ) :
    avg (fun θ => ∑ a, ∑ b, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) * (∑ β ∈ M, z β a b * ph m β θ) *
        (∑ n' ∈ F, y n' b * ph m n' θ))
      = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then
          ∑ a, ∑ b, (starRingEnd ℂ) (x n a) * z (n - n') a b * y n' b else 0 := by
  have hc : ∀ a b, Continuous fun θ => (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ M, z β a b * ph m β θ) * (∑ n' ∈ F, y n' b * ph m n' θ) := fun a b =>
    ((Complex.continuous_conj.comp (tp_cont m L _)).mul (tp_cont m M _)).mul (tp_cont m F _)
  rw [avg_sum]
  swap
  · exact fun a _ => continuous_finsetSum _ fun b _ => hc a b
  have inner : ∀ a, (avg fun θ => ∑ b, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ M, z β a b * ph m β θ) * (∑ n' ∈ F, y n' b * ph m n' θ))
      = ∑ b, avg fun θ => (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ M, z β a b * ph m β θ) * (∑ n' ∈ F, y n' b * ph m n' θ) := fun a =>
    avg_sum _ (fun b θ => (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ M, z β a b * ph m β θ) * (∑ n' ∈ F, y n' b * ph m n' θ)) fun b _ => hc a b
  simp only [inner, avg_tri hm]
  rw [swap4]
  refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun n' _ => ?_
  split_ifs <;> simp

theorem avg_sq {m : ℕ} (hm : 1 ≤ m) {ι : Type*} [Fintype ι] (L : Finset ℤ) (x : ℤ → ι → ℂ) :
    avg (fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) * (∑ n ∈ L, x n a * ph m n θ))
      = ∑ n ∈ L, ∑ a, (starRingEnd ℂ) (x n a) * x n a := by
  have hp : ∀ a θ, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) * (∑ n ∈ L, x n a * ph m n θ)
      = (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) * (∑ β ∈ ({0} : Finset ℤ), (1 : ℂ) * ph m β θ) *
        (∑ n ∈ L, x n a * ph m n θ) := by
    intro a θ
    simp [ph_zero]
  simp only [hp]
  have hc : ∀ a, Continuous fun θ => (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ ({0} : Finset ℤ), (1 : ℂ) * ph m β θ) * (∑ n' ∈ L, x n' a * ph m n' θ) := fun a =>
    ((Complex.continuous_conj.comp (tp_cont m L _)).mul (tp_cont m _ _)).mul (tp_cont m L _)
  rw [avg_sum]
  swap
  · exact fun a _ => hc a
  simp only [avg_tri hm, Finset.mem_singleton, sub_eq_zero, mul_one, Finset.sum_ite_eq]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun n hn => Finset.sum_congr rfl fun a _ => by simp [hn]



theorem lin_sum (f : (Fin 3 → Fin 3 → ℂ) → ℂ)
    (hadd : ∀ s t, f (fun a b => s a b + t a b) = f s + f t)
    (hmul : ∀ s (c : ℂ), f (fun a b => s a b * c) = f s * c)
    (M : Finset ℤ) (g : ℤ → Fin 3 → Fin 3 → ℂ) (e : ℤ → ℂ) :
    f (fun a b => ∑ β ∈ M, g β a b * e β) = ∑ β ∈ M, f (g β) * e β := by
  classical
  induction M using Finset.induction_on with
  | empty =>
    have h := hmul (fun _ _ => 0) 0
    simp only [mul_zero] at h
    simpa using h
  | insert β M hβ ih =>
    simp only [Finset.sum_insert hβ]
    rw [hadd (fun a b => g β a b * e β) (fun a b => ∑ x ∈ M, g x a b * e x), ih, hmul]

theorem curl_tp (L : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (e : ℤ → ℂ) (i : Fin 3) :
    curlComp (fun a b => ∑ n ∈ L, s n a b * e n) i = ∑ n ∈ L, curlComp (s n) i * e n :=
  lin_sum (fun s => curlComp s i) (fun s t => by simp only [curlComp, Fin.sum_univ_three]; ring)
    (fun s c => by simp only [curlComp, Fin.sum_univ_three]; ring) L s e

theorem cm_tp (M : Finset ℤ) (g : ℤ → Fin 3 → Fin 3 → ℂ) (e : ℤ → ℂ) (u : Fin 3 → ℂ) (i l : Fin 3) :
    couplingMap (fun a b => ∑ β ∈ M, g β a b * e β) u i l = ∑ β ∈ M, couplingMap (g β) u i l * e β :=
  lin_sum (fun G => couplingMap G u i l)
    (fun s t => by simp only [couplingMap, bracketMat, Fin.sum_univ_three]; ring)
    (fun s c => by simp only [couplingMap, bracketMat, Fin.sum_univ_three]; ring) M g e

theorem cm_vec (G : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (i l : Fin 3) :
    couplingMap G v i l = ∑ c : Fin 3, couplingMap G (Pi.single c 1) i l * v c := by
  simp only [couplingMap, bracketMat, Fin.sum_univ_three, Pi.single_apply]
  simp [Fin.ext_iff]
  try ring

theorem pairing_expand (G : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) (t : Fin 3 → Fin 3 → ℂ) :
    entryPairing (couplingMap G u) t
      = ∑ j : Fin 3 × Fin 3, ∑ c : Fin 3,
          (starRingEnd ℂ) (t j.1 j.2) * couplingMap G (Pi.single c 1) j.1 j.2 * u c := by
  rw [Fintype.sum_prod_type]
  unfold entryPairing
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  rw [cm_vec G u i l, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

theorem strain_expand (Z : Fin 3 → Fin 3 → ℂ) (X Y : Fin 3 → ℂ) :
    ∑ a, (starRingEnd ℂ) (X a) * ∑ b, Z a b * Y b = ∑ a, ∑ b, (starRingEnd ℂ) (X a) * Z a b * Y b := by
  simp only [Finset.mul_sum, mul_assoc]

theorem amgm {t : ℝ} (ht : 0 < t) (a b : ℝ) : 2 * a * b ≤ t * a ^ 2 + b ^ 2 / t := by
  have h : t * a ^ 2 + b ^ 2 / t - 2 * a * b = (t * a - b) ^ 2 / t := by
    field_simp
    ring
  have : 0 ≤ (t * a - b) ^ 2 / t := by positivity
  linarith

theorem curlSq_nonneg (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ curlSq s := by
  unfold curlSq
  positivity

theorem re_ge (z : ℂ) : -‖z‖ ≤ z.re := by
  have := Complex.abs_re_le_norm z
  linarith [neg_abs_le z.re]

theorem strain_le {ΦS : Fin 3 → Fin 3 → ℂ} {dS : ℝ} (hdS : 0 ≤ dS) (hS : OpBound ΦS dS)
    (X Y : Fin 3 → Fin 3 → ℂ) :
    ‖∑ a, (starRingEnd ℂ) (curlComp X a) * ∑ b, ΦS a b * curlComp Y b‖
      ≤ dS * Real.sqrt (curlSq X) * Real.sqrt (curlSq Y) := by
  have h1 := SharpCircleMean.vecInner_le (fun a => (starRingEnd ℂ) (curlComp X a)) (matVec ΦS (fun b => curlComp Y b))
  rw [SharpCircleMean.vecSq_conj] at h1
  have h2 := SharpCircleMean.op_sqrt hdS hS (fun b => curlComp Y b)
  have e1 : vecSq (fun a => curlComp X a) = curlSq X := rfl
  have e2 : vecSq (fun a => curlComp Y a) = curlSq Y := rfl
  rw [e1] at h1
  rw [e2] at h2
  calc _ ≤ Real.sqrt (curlSq X) * Real.sqrt (vecSq (matVec ΦS (fun b => curlComp Y b))) := h1
    _ ≤ Real.sqrt (curlSq X) * (dS * Real.sqrt (curlSq Y)) :=
        mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg _)
    _ = dS * Real.sqrt (curlSq X) * Real.sqrt (curlSq Y) := by ring

theorem point_bound {dS dG w ℓ : ℝ} (hdS : 0 ≤ dS) (hdG : 0 ≤ dG) (hw : 0 < w) (hℓ : 0 < ℓ)
    (ΦS ΦG : Fin 3 → Fin 3 → ℂ) (hS : OpBound ΦS dS) (hG : OpBound ΦG dG) (htr : ∑ a, ΦG a a = 0)
    (σ τ : Fin 3 → Fin 3 → ℂ) (ν ν' : Fin 3 → ℂ) :
    -(w * (dS * curlSq σ + (1 / 2) * Exterior.traceFreeConst * dG * (ℓ * sumSq σ + vecSq ν / ℓ))
        + (dS * curlSq τ + (1 / 2) * Exterior.traceFreeConst * dG * (ℓ * sumSq τ + vecSq ν' / ℓ)) / w)
      ≤ (-(∑ a, (starRingEnd ℂ) (curlComp σ a) * ∑ b, ΦS a b * curlComp τ b)
          - (∑ a, (starRingEnd ℂ) (curlComp τ a) * ∑ b, ΦS a b * curlComp σ b)
          + entryPairing (couplingMap ΦG ν') σ + entryPairing (couplingMap ΦG ν) τ).re := by
  have hA := strain_le hdS hS σ τ
  have hB := strain_le hdS hS τ σ
  have hC := SharpCircleMean.coupling_norm_le hdG hG htr σ ν'
  have hD := SharpCircleMean.coupling_norm_le hdG hG htr τ ν
  have rA := Complex.re_le_norm (∑ a, (starRingEnd ℂ) (curlComp σ a) * ∑ b, ΦS a b * curlComp τ b)
  have rB := Complex.re_le_norm (∑ a, (starRingEnd ℂ) (curlComp τ a) * ∑ b, ΦS a b * curlComp σ b)
  have rC := re_ge (entryPairing (couplingMap ΦG ν') σ)
  have rD := re_ge (entryPairing (couplingMap ΦG ν) τ)
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re]
  set T := Exterior.traceFreeConst
  have hT : 0 ≤ T := Real.sqrt_nonneg _
  set X := Real.sqrt (curlSq σ)
  set Y := Real.sqrt (curlSq τ)
  set Sσ := Real.sqrt (sumSq σ)
  set Sτ := Real.sqrt (sumSq τ)
  set V := Real.sqrt (vecSq ν)
  set V' := Real.sqrt (vecSq ν')
  have eX : curlSq σ = X ^ 2 := (Real.sq_sqrt (curlSq_nonneg σ)).symm
  have eY : curlSq τ = Y ^ 2 := (Real.sq_sqrt (curlSq_nonneg τ)).symm
  have eSσ : sumSq σ = Sσ ^ 2 := (Real.sq_sqrt (SharpCircleMean.sumSq_nonneg σ)).symm
  have eSτ : sumSq τ = Sτ ^ 2 := (Real.sq_sqrt (SharpCircleMean.sumSq_nonneg τ)).symm
  have eV : vecSq ν = V ^ 2 := (Real.sq_sqrt (SharpCircleMean.vecSq_nonneg ν)).symm
  have eV' : vecSq ν' = V' ^ 2 := (Real.sq_sqrt (SharpCircleMean.vecSq_nonneg ν')).symm
  rw [eX, eY, eSσ, eSτ, eV, eV']
  have k1 := mul_le_mul_of_nonneg_left (amgm hw X Y) hdS
  have k2 := mul_le_mul_of_nonneg_left (amgm (mul_pos hw hℓ) Sσ V') (by positivity : 0 ≤ T * dG / 2)
  have k3 := mul_le_mul_of_nonneg_left (amgm (div_pos hℓ hw) Sτ V) (by positivity : 0 ≤ T * dG / 2)
  have key : 2 * dS * X * Y + T * dG * Sσ * V' + T * dG * Sτ * V
      ≤ w * (dS * X ^ 2 + (1 / 2) * T * dG * (ℓ * Sσ ^ 2 + V ^ 2 / ℓ))
        + (dS * Y ^ 2 + (1 / 2) * T * dG * (ℓ * Sτ ^ 2 + V' ^ 2 / ℓ)) / w := by
    have eq : w * (dS * X ^ 2 + (1 / 2) * T * dG * (ℓ * Sσ ^ 2 + V ^ 2 / ℓ))
        + (dS * Y ^ 2 + (1 / 2) * T * dG * (ℓ * Sτ ^ 2 + V' ^ 2 / ℓ)) / w
        = dS * (w * X ^ 2 + Y ^ 2 / w) + T * dG / 2 * (w * ℓ * Sσ ^ 2 + V' ^ 2 / (w * ℓ))
          + T * dG / 2 * (ℓ / w * Sτ ^ 2 + V ^ 2 / (ℓ / w)) := by
      field_simp
      ring
    rw [eq]
    linear_combination k1 + k2 + k3
  have hB' : dS * Y * X = dS * X * Y := by ring
  rw [hB'] at hB
  have hC' : T * dG * Sσ * V' = T * dG * Sσ * V' := rfl
  linarith

theorem avg_neg (f : ℝ → ℂ) : avg (fun θ => -f θ) = -avg f := by
  unfold avg
  simp only [mul_neg]
  exact integral_neg _

theorem nsq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ) z * z := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem curlSq_c (s : Fin 3 → Fin 3 → ℂ) :
    ((curlSq s : ℝ) : ℂ) = ∑ a, (starRingEnd ℂ) (curlComp s a) * curlComp s a := by
  unfold curlSq
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ => nsq _

theorem vecSq_c (v : Fin 3 → ℂ) : ((vecSq v : ℝ) : ℂ) = ∑ a, (starRingEnd ℂ) (v a) * v a := by
  unfold vecSq
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun a _ => nsq _

theorem sumSq_c (s : Fin 3 → Fin 3 → ℂ) :
    ((sumSq s : ℝ) : ℂ) = ∑ j : Fin 3 × Fin 3, (starRingEnd ℂ) (s j.1 j.2) * s j.1 j.2 := by
  unfold sumSq
  rw [Complex.ofReal_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Complex.ofReal_sum]
  exact Finset.sum_congr rfl fun b _ => nsq _

theorem form_cont (m : ℕ) {ι κ : Type*} [Fintype ι] [Fintype κ] (L F M : Finset ℤ)
    (x : ℤ → ι → ℂ) (z : ℤ → ι → κ → ℂ) (y : ℤ → κ → ℂ) :
    Continuous fun θ => ∑ a, ∑ b, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) *
      (∑ β ∈ M, z β a b * ph m β θ) * (∑ n' ∈ F, y n' b * ph m n' θ) :=
  continuous_finsetSum _ fun _ _ => continuous_finsetSum _ fun _ _ =>
    ((Complex.continuous_conj.comp (tp_cont m L _)).mul (tp_cont m M _)).mul (tp_cont m F _)

theorem par_cont (m : ℕ) {ι : Type*} [Fintype ι] (L : Finset ℤ) (x : ℤ → ι → ℂ) :
    Continuous fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ L, x n a * ph m n θ) * (∑ n ∈ L, x n a * ph m n θ) :=
  continuous_finsetSum _ fun _ _ => (Complex.continuous_conj.comp (tp_cont m L _)).mul (tp_cont m L _)

theorem avg_lin6 {f1 f2 f3 f4 f5 f6 : ℝ → ℂ} (h1 : Continuous f1) (h2 : Continuous f2) (h3 : Continuous f3)
    (h4 : Continuous f4) (h5 : Continuous f5) (h6 : Continuous f6) (a1 a2 a3 a4 a5 a6 : ℂ) :
    avg (fun θ => a1 * f1 θ + a2 * f2 θ + a3 * f3 θ + a4 * f4 θ + a5 * f5 θ + a6 * f6 θ)
      = a1 * avg f1 + a2 * avg f2 + a3 * avg f3 + a4 * avg f4 + a5 * avg f5 + a6 * avg f6 := by
  have c1 : Continuous fun θ => a1 * f1 θ := continuous_const.mul h1
  have c2 : Continuous fun θ => a2 * f2 θ := continuous_const.mul h2
  have c3 : Continuous fun θ => a3 * f3 θ := continuous_const.mul h3
  have c4 : Continuous fun θ => a4 * f4 θ := continuous_const.mul h4
  have c5 : Continuous fun θ => a5 * f5 θ := continuous_const.mul h5
  have c6 : Continuous fun θ => a6 * f6 θ := continuous_const.mul h6
  rw [avg_add (f := fun θ => a1 * f1 θ + a2 * f2 θ + a3 * f3 θ + a4 * f4 θ + a5 * f5 θ)
      (g := fun θ => a6 * f6 θ) ((((c1.add c2).add c3).add c4).add c5) c6,
    avg_add (f := fun θ => a1 * f1 θ + a2 * f2 θ + a3 * f3 θ + a4 * f4 θ)
      (g := fun θ => a5 * f5 θ) (((c1.add c2).add c3).add c4) c5,
    avg_add (f := fun θ => a1 * f1 θ + a2 * f2 θ + a3 * f3 θ)
      (g := fun θ => a4 * f4 θ) ((c1.add c2).add c3) c4,
    avg_add (f := fun θ => a1 * f1 θ + a2 * f2 θ) (g := fun θ => a3 * f3 θ) (c1.add c2) c3,
    avg_add (f := fun θ => a1 * f1 θ) (g := fun θ => a2 * f2 θ) c1 c2]
  simp only [avg_mul]

theorem half_re (z : ℂ) : ((1 / 2 : ℂ) * z).re = z.re / 2 := by
  simp [Complex.mul_re]
  ring

theorem wave_re (Sa Sb Ga Gb : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ)
    (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    (waveForm Sa Ga Gb s v s' v' + waveForm Sb Gb Ga s' v' s v).re
      = (-(∑ a, ∑ b, (starRingEnd ℂ) (curlComp s a) * Sa a b * curlComp s' b)
          - (∑ a, ∑ b, (starRingEnd ℂ) (curlComp s' a) * Sb a b * curlComp s b)
          + entryPairing (couplingMap Ga v') s + entryPairing (couplingMap Gb v) s').re := by
  unfold waveForm
  rw [strain_expand, strain_expand, SharpCircleMean.pairing_swap s' (couplingMap Gb v),
    SharpCircleMean.pairing_swap s (couplingMap Ga v')]
  simp only [Complex.add_re, Complex.sub_re, Complex.neg_re, half_re, Complex.conj_re]
  ring

theorem hbase {m : ℕ} (hm : 1 ≤ m) (M : Finset ℤ) (hM : ∀ n, n ∈ M ↔ -n ∈ M)
    (Sm Gm : ℤ → Fin 3 → Fin 3 → ℂ) {dS dG w ℓ : ℝ} (hdS : 0 ≤ dS) (hdG : 0 ≤ dG) (hw : 0 < w) (hℓ : 0 < ℓ)
    (hbS : ∀ θ, OpBound (fun a b => ∑ β ∈ M, Sm β a b * ph m β θ) dS)
    (hbG : ∀ θ, OpBound (fun a b => ∑ β ∈ M, Gm β a b * ph m β θ) dG)
    (htr : ∀ θ, ∑ a, ∑ β ∈ M, Gm β a a * ph m β θ = 0)
    (L F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
    (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ) :
    -(w * ∑ n ∈ L, (dS * curlSq (s n)
        + (1 / 2) * Exterior.traceFreeConst * dG * (ℓ * sumSq (s n) + vecSq (v n) / ℓ)))
      - (∑ n' ∈ F, (dS * curlSq (s' n')
        + (1 / 2) * Exterior.traceFreeConst * dG * (ℓ * sumSq (s' n') + vecSq (v' n') / ℓ))) / w
      ≤ ∑ n ∈ L, ∑ n' ∈ F, (if n - n' ∈ M then
          (waveForm (Sm (n - n')) (Gm (n - n')) (Gm (n' - n)) (s n) (v n) (s' n') (v' n')
            + waveForm (Sm (n' - n)) (Gm (n' - n)) (Gm (n - n')) (s' n') (v' n') (s n) (v n)).re
          else 0) := by
  set T := Exterior.traceFreeConst with hTdef
  set K := (1 / 2) * T * dG with hK
  let σ : ℝ → Fin 3 → Fin 3 → ℂ := fun θ a b => ∑ n ∈ L, s n a b * ph m n θ
  let τ : ℝ → Fin 3 → Fin 3 → ℂ := fun θ a b => ∑ n ∈ F, s' n a b * ph m n θ
  let ν : ℝ → Fin 3 → ℂ := fun θ a => ∑ n ∈ L, v n a * ph m n θ
  let ν' : ℝ → Fin 3 → ℂ := fun θ a => ∑ n ∈ F, v' n a * ph m n θ
  let ΦS : ℝ → Fin 3 → Fin 3 → ℂ := fun θ a b => ∑ β ∈ M, Sm β a b * ph m β θ
  let ΦG : ℝ → Fin 3 → Fin 3 → ℂ := fun θ a b => ∑ β ∈ M, Gm β a b * ph m β θ
  let A : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (curlComp (σ θ) a) * ∑ b, ΦS θ a b * curlComp (τ θ) b
  let B : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (curlComp (τ θ) a) * ∑ b, ΦS θ a b * curlComp (σ θ) b
  let C : ℝ → ℂ := fun θ => entryPairing (couplingMap (ΦG θ) (ν' θ)) (σ θ)
  let D : ℝ → ℂ := fun θ => entryPairing (couplingMap (ΦG θ) (ν θ)) (τ θ)
  let low : ℝ → ℝ := fun θ => w * (dS * curlSq (σ θ) + K * (ℓ * sumSq (σ θ) + vecSq (ν θ) / ℓ))
        + (dS * curlSq (τ θ) + K * (ℓ * sumSq (τ θ) + vecSq (ν' θ) / ℓ)) / w
  have hpt : ∀ θ, -low θ ≤ (-A θ - B θ + C θ + D θ).re := fun θ =>
    point_bound hdS hdG hw hℓ (ΦS θ) (ΦG θ) (hbS θ) (hbG θ) (htr θ) (σ θ) (τ θ) (ν θ) (ν' θ)
  have eA : A = fun θ => ∑ a, ∑ b, (starRingEnd ℂ) (∑ n ∈ L, curlComp (s n) a * ph m n θ) *
      (∑ β ∈ M, Sm β a b * ph m β θ) * (∑ n' ∈ F, curlComp (s' n') b * ph m n' θ) := by
    funext θ
    simp only [A, strain_expand, σ, τ, ΦS, curl_tp]
  have eB : B = fun θ => ∑ a, ∑ b, (starRingEnd ℂ) (∑ n ∈ F, curlComp (s' n) a * ph m n θ) *
      (∑ β ∈ M, Sm β a b * ph m β θ) * (∑ n' ∈ L, curlComp (s n') b * ph m n' θ) := by
    funext θ
    simp only [B, strain_expand, σ, τ, ΦS, curl_tp]
  have eC : C = fun θ => ∑ j : Fin 3 × Fin 3, ∑ c : Fin 3, (starRingEnd ℂ) (∑ n ∈ L, s n j.1 j.2 * ph m n θ) *
      (∑ β ∈ M, couplingMap (Gm β) (Pi.single c 1) j.1 j.2 * ph m β θ) * (∑ n' ∈ F, v' n' c * ph m n' θ) := by
    funext θ
    simp only [C, pairing_expand, ΦG, cm_tp]
    rfl
  have eD : D = fun θ => ∑ j : Fin 3 × Fin 3, ∑ c : Fin 3, (starRingEnd ℂ) (∑ n ∈ F, s' n j.1 j.2 * ph m n θ) *
      (∑ β ∈ M, couplingMap (Gm β) (Pi.single c 1) j.1 j.2 * ph m β θ) * (∑ n' ∈ L, v n' c * ph m n' θ) := by
    funext θ
    simp only [D, pairing_expand, ΦG, cm_tp]
    rfl
  have hAc : Continuous A := by rw [eA]; exact form_cont m L F M _ _ _
  have hBc : Continuous B := by rw [eB]; exact form_cont m F L M _ _ _
  have hCc : Continuous C := by rw [eC]; exact form_cont m L F M _ _ _
  have hDc : Continuous D := by rw [eD]; exact form_cont m F L M _ _ _
  have hP : ∀ n n' : ℤ, (n' - n ∈ M) ↔ (n - n' ∈ M) := fun n n' => by rw [hM (n - n'), neg_sub]
  have aQ : avg (fun θ => -A θ - B θ + C θ + D θ) = -avg A - avg B + avg C + avg D := by
    rw [avg_add (f := fun θ => -A θ - B θ + C θ) (g := D) ((hAc.neg.sub hBc).add hCc) hDc,
      avg_add (f := fun θ => -A θ - B θ) (g := C) (hAc.neg.sub hBc) hCc,
      avg_sub (f := fun θ => -A θ) (g := B) hAc.neg hBc, avg_neg]
  have aA : avg A = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then
      ∑ a, ∑ b, (starRingEnd ℂ) (curlComp (s n) a) * Sm (n - n') a b * curlComp (s' n') b else 0 := by
    rw [eA]
    exact avg_form hm L F M _ _ _
  have aB : avg B = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then
      ∑ a, ∑ b, (starRingEnd ℂ) (curlComp (s' n') a) * Sm (n' - n) a b * curlComp (s n) b else 0 := by
    rw [eB, avg_form hm F L M _ _ _, Finset.sum_comm]
    simp only [hP]
  have aC : avg C = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then
      entryPairing (couplingMap (Gm (n - n')) (v' n')) (s n) else 0 := by
    rw [eC, avg_form hm L F M _ _ _]
    simp only [pairing_expand]
  have aD : avg D = ∑ n ∈ L, ∑ n' ∈ F, if n - n' ∈ M then
      entryPairing (couplingMap (Gm (n' - n)) (v n)) (s' n') else 0 := by
    rw [eD, avg_form hm F L M _ _ _, Finset.sum_comm]
    simp only [hP, pairing_expand]
  let PC : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ L, curlComp (s n) a * ph m n θ) *
    (∑ n ∈ L, curlComp (s n) a * ph m n θ)
  let PS : ℝ → ℂ := fun θ => ∑ j : Fin 3 × Fin 3, (starRingEnd ℂ) (∑ n ∈ L, s n j.1 j.2 * ph m n θ) *
    (∑ n ∈ L, s n j.1 j.2 * ph m n θ)
  let PV : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ L, v n a * ph m n θ) * (∑ n ∈ L, v n a * ph m n θ)
  let PC' : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ F, curlComp (s' n) a * ph m n θ) *
    (∑ n ∈ F, curlComp (s' n) a * ph m n θ)
  let PS' : ℝ → ℂ := fun θ => ∑ j : Fin 3 × Fin 3, (starRingEnd ℂ) (∑ n ∈ F, s' n j.1 j.2 * ph m n θ) *
    (∑ n ∈ F, s' n j.1 j.2 * ph m n θ)
  let PV' : ℝ → ℂ := fun θ => ∑ a, (starRingEnd ℂ) (∑ n ∈ F, v' n a * ph m n θ) * (∑ n ∈ F, v' n a * ph m n θ)
  have hPC : Continuous PC := par_cont m L (fun n a => curlComp (s n) a)
  have hPS : Continuous PS := par_cont m L (fun n (j : Fin 3 × Fin 3) => s n j.1 j.2)
  have hPV : Continuous PV := par_cont m L v
  have hPC' : Continuous PC' := par_cont m F (fun n a => curlComp (s' n) a)
  have hPS' : Continuous PS' := par_cont m F (fun n (j : Fin 3 × Fin 3) => s' n j.1 j.2)
  have hPV' : Continuous PV' := par_cont m F v'
  have aPC : avg PC = ∑ n ∈ L, ((curlSq (s n) : ℝ) : ℂ) := by
    rw [show avg PC = _ from avg_sq hm L (fun n a => curlComp (s n) a)]
    simp only [curlSq_c]
  have aPS : avg PS = ∑ n ∈ L, ((sumSq (s n) : ℝ) : ℂ) := by
    rw [show avg PS = _ from avg_sq hm L (fun n (j : Fin 3 × Fin 3) => s n j.1 j.2)]
    simp only [sumSq_c]
  have aPV : avg PV = ∑ n ∈ L, ((vecSq (v n) : ℝ) : ℂ) := by
    rw [show avg PV = _ from avg_sq hm L v]
    simp only [vecSq_c]
  have aPC' : avg PC' = ∑ n ∈ F, ((curlSq (s' n) : ℝ) : ℂ) := by
    rw [show avg PC' = _ from avg_sq hm F (fun n a => curlComp (s' n) a)]
    simp only [curlSq_c]
  have aPS' : avg PS' = ∑ n ∈ F, ((sumSq (s' n) : ℝ) : ℂ) := by
    rw [show avg PS' = _ from avg_sq hm F (fun n (j : Fin 3 × Fin 3) => s' n j.1 j.2)]
    simp only [sumSq_c]
  have aPV' : avg PV' = ∑ n ∈ F, ((vecSq (v' n) : ℝ) : ℂ) := by
    rw [show avg PV' = _ from avg_sq hm F v']
    simp only [vecSq_c]
  have eL : ∀ θ, ((-low θ : ℝ) : ℂ) = ((-(w * dS) : ℝ) : ℂ) * PC θ + ((-(w * K * ℓ) : ℝ) : ℂ) * PS θ
      + ((-(w * K / ℓ) : ℝ) : ℂ) * PV θ + ((-(dS / w) : ℝ) : ℂ) * PC' θ + ((-(K * ℓ / w) : ℝ) : ℂ) * PS' θ
      + ((-(K / ℓ / w) : ℝ) : ℂ) * PV' θ := by
    intro θ
    have h1 : ((curlSq (σ θ) : ℝ) : ℂ) = PC θ := by
      rw [curlSq_c]
      simp only [σ, curl_tp, PC]
    have h2 : ((sumSq (σ θ) : ℝ) : ℂ) = PS θ := by
      rw [sumSq_c]
    have h3 : ((vecSq (ν θ) : ℝ) : ℂ) = PV θ := by
      rw [vecSq_c]
    have h4 : ((curlSq (τ θ) : ℝ) : ℂ) = PC' θ := by
      rw [curlSq_c]
      simp only [τ, curl_tp, PC']
    have h5 : ((sumSq (τ θ) : ℝ) : ℂ) = PS' θ := by
      rw [sumSq_c]
    have h6 : ((vecSq (ν' θ) : ℝ) : ℂ) = PV' θ := by
      rw [vecSq_c]
    simp only [low]
    push_cast
    rw [h1, h2, h3, h4, h5, h6]
    ring
  have hQc : Continuous fun θ => -A θ - B θ + C θ + D θ := ((hAc.neg.sub hBc).add hCc).add hDc
  have hLc : Continuous fun θ => ((-low θ : ℝ) : ℂ) := by
    simp only [eL]
    exact (((((continuous_const.mul hPC).add (continuous_const.mul hPS)).add (continuous_const.mul hPV)).add
      (continuous_const.mul hPC')).add (continuous_const.mul hPS')).add (continuous_const.mul hPV')
  have hlc : Continuous fun θ => -low θ := by
    have e : (fun θ => -low θ) = fun θ => (((-low θ : ℝ) : ℂ)).re := funext fun θ => (Complex.ofReal_re _).symm
    rw [e]
    exact Complex.continuous_re.comp hLc
  have aL : avg (fun θ => ((-low θ : ℝ) : ℂ))
      = ((-(w * ∑ n ∈ L, (dS * curlSq (s n) + K * (ℓ * sumSq (s n) + vecSq (v n) / ℓ)))
        - (∑ n' ∈ F, (dS * curlSq (s' n') + K * (ℓ * sumSq (s' n') + vecSq (v' n') / ℓ))) / w : ℝ) : ℂ) := by
    rw [show (fun θ => ((-low θ : ℝ) : ℂ)) = _ from funext eL,
      avg_lin6 hPC hPS hPV hPC' hPS' hPV', aPC, aPS, aPV, aPC', aPS', aPV']
    push_cast
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div]
    ring
  have key := avg_re_mono hQc hlc hpt
  rw [aL, aQ, aA, aB, aC, aD, Complex.ofReal_re] at key
  refine key.trans (le_of_eq ?_)
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← Finset.sum_neg_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    Complex.re_sum]
  refine Finset.sum_congr rfl fun n' _ => ?_
  split_ifs with h
  · rw [wave_re]
  · simp

theorem zero_trace_gen (m : ℕ) (β : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ)
    (hint : ∀ i j : Fin 3, IntervalIntegrable (fun θ => ent (G (cylPoint r θ z)) i j) volume 0 (2 * Real.pi))
    (htr : ∀ θ : ℝ, ∑ i : Fin 3, entry (G (cylPoint r θ z)) i i = 0) :
    ∑ a : Fin 3, modeMat m β G r z a a = 0 := by
  have hd : ∀ a : Fin 3, IntervalIntegrable (fun θ => Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) *
      (frameMat θ (G (cylPoint r θ z)) a a : ℂ)) volume 0 (2 * Real.pi) := by
    intro a
    have h0 := SharpCircleMean.diag_int (fun θ => G (cylPoint r θ z)) hint a
    have h1 : IntervalIntegrable (fun θ => (frameMat θ (G (cylPoint r θ z)) a a : ℂ)) volume 0 (2 * Real.pi) :=
      ⟨h0.1.ofReal, h0.2.ofReal⟩
    have hc : Continuous fun θ : ℝ => Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) := by fun_prop
    exact h1.continuousOn_mul hc.continuousOn
  have hz : ∀ θ : ℝ, ∑ a : Fin 3, Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) *
      (frameMat θ (G (cylPoint r θ z)) a a : ℂ) = 0 := by
    intro θ
    rw [← Finset.mul_sum, ← Complex.ofReal_sum]
    simp only [frameMat_diag]
    rw [diag_sum]
    have h := htr θ
    simp only [← SharpCircleMean.ent_eq] at h
    rw [h]
    simp
  unfold modeMat
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum (fun a _ => hd a), funext hz]
  simp

theorem trace_all {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c) {K : CellBox}
    {S : CellScalars} {B : CellBases} {Cl : CellClasses} {slots : ℕ} {R : CellRows N slots k}
    (hd : IsCellData α c K S B Cl R) :
    ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 → p ∈ K.rect →
      ∀ β : ℤ, ∑ a : Fin 3, modeMat c.order β c.modelCurlGrad p.1 p.2 a a = 0 := by
  have hK := hd.box
  have hsub : K.solid ⊆ c.cellRegion := hd.solid_in_region
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hsub).measure_lt_top
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hGm := hc.model_measurable.2.2.2
  have hloc : ∀ i j : Fin 3,
      LocallyIntegrable (K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j)) volume := by
    intro i j
    refine Integrable.locallyIntegrable ?_
    have hc0 : IntegrableOn (fun _ : Space => C) K.solid := by
      refine (integrableOn_const_iff ?_).2 (Or.inr hfin)
      simp
    refine Integrable.mono' (hc0.integrable_indicator (solid_meas K))
      (((continuous_ent i j).comp_aestronglyMeasurable hGm).indicator (solid_meas K)) (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ K.solid
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Real.norm_eq_abs]
      refine (abs_ent_le _ i j).trans (((c.modelCurlGrad y).le_opNorm _).trans ?_)
      have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
      rw [hu, mul_one]
      exact (hC y (hsub hy)).2.2.2
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, norm_zero]
  have hall : ∀ᵐ q : ℝ × ℝ ∂volume, ∀ i j : Fin 3, 0 < q.1 → IntervalIntegrable
      (fun θ => K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j) (cylPoint q.1 θ q.2))
      volume 0 (2 * Real.pi) := by
    rw [ae_all_iff]; intro i
    rw [ae_all_iff]; intro j
    exact sections (hloc i j)
  filter_upwards [ae_restrict_of_ae hall] with p hp hp1 hpK β
  have hint : ∀ i j : Fin 3, IntervalIntegrable (fun θ => ent (c.modelCurlGrad (cylPoint p.1 θ p.2)) i j)
      volume 0 (2 * Real.pi) := by
    intro i j
    have e : (fun θ => K.solid.indicator (fun y => ent (c.modelCurlGrad y) i j) (cylPoint p.1 θ p.2))
        = fun θ => ent (c.modelCurlGrad (cylPoint p.1 θ p.2)) i j := by
      funext θ
      exact Set.indicator_of_mem (cyl_solid K hK hpK θ) _
    rw [← e]
    exact hp i j hp1
  exact zero_trace_gen c.order β c.modelCurlGrad p.1 p.2 hint (fun θ => hd.curlGrad_traceFree p hpK hp1.ne' θ)

theorem classField_trace {m : ℕ} (M : Finset ℤ) (G : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ)
    (h : ∀ β : ℤ, ∑ a : Fin 3, modeMat m β G p.1 p.2 a a = 0) (θ : ℝ) :
    ∑ a, ∑ β ∈ M, modeMat m β G p.1 p.2 a a * ph m β θ = 0 := by
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun β _ => ?_
  rw [← Finset.sum_mul, h β, zero_mul]

end Breakdown.FracInternal.ClassProductSplit

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly Breakdown.FracInternal.ClassProductSplit SharpParts

theorem classProductSplit_of_trace {α : ℝ} {k N : ℕ} {c : FracCellData k N} (hc : IsFormData α c)
    {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses} {slots : ℕ}
    {R : CellRows N slots k} (hd : IsCellData α c K S B Cl R)
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (hp1 : p.1 ≠ 0) (i : Fin Cl.count)
    (htr : ∀ θ : ℝ, ∑ a, classField c.order (Cl.modes i) c.modelCurlGrad p θ a a = 0)
    (L F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
    (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ) :
    -(Cl.shareWeight i * ∑ n ∈ L, Cl.classLoss S.splitLength i p (s n) (v n))
        - (∑ n' ∈ F, Cl.classLoss S.splitLength i p (s' n') (v' n')) / Cl.shareWeight i
      ≤ ∑ n ∈ L, ∑ n' ∈ F, (if n - n' ∈ Cl.modes i then
          (pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re
          else 0) := by
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  have hb := fun θ => hd.class_bounds i p hp hp1 θ
  exact hbase hm (Cl.modes i) (hd.class_modes_symm i)
    (fun β => modeMat c.order β c.modelStrain p.1 p.2) (fun β => modeMat c.order β c.modelCurlGrad p.1 p.2)
    (hd.class_devs_nonneg i p).1 (hd.class_devs_nonneg i p).2.1 (hd.class_weights_pos i).1
    hd.scalars.splitLength_pos (fun θ => (hb θ).1) (fun θ => (hb θ).2.1) htr L F s v s' v'

def ClassProductSplitAeStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R →
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ → p.1 ≠ 0 →
      ∀ (i : Fin Cl.count) (L F : Finset ℤ) (s : ℤ → Fin 3 → Fin 3 → ℂ) (v : ℤ → Fin 3 → ℂ)
        (s' : ℤ → Fin 3 → Fin 3 → ℂ) (v' : ℤ → Fin 3 → ℂ),
      -(Cl.shareWeight i * ∑ n ∈ L, Cl.classLoss S.splitLength i p (s n) (v n))
        - (∑ n' ∈ F, Cl.classLoss S.splitLength i p (s' n') (v' n')) / Cl.shareWeight i
      ≤ ∑ n ∈ L, ∑ n' ∈ F, (if n - n' ∈ Cl.modes i then
          (pairWave c n n' p (s n) (v n) (s' n') (v' n') + pairWave c n' n p (s' n') (v' n') (s n) (v n)).re
          else 0)

theorem classProductSplitAe_holds : ClassProductSplitAeStatement := by
  intro α _ _ k N c hc K S B Cl slots R hd
  filter_upwards [trace_all hc hd] with p hp hpI hp1 i L F s v s' v'
  have hK := hd.box.r_order
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hK.1 hpI.1.1.le) (Ne.symm hp1)
  have hpK : p ∈ K.rect := ⟨⟨hpI.1.1.le, hpI.1.2.le⟩, ⟨hpI.2.1.le, hpI.2.2.le⟩⟩
  exact classProductSplit_of_trace hc hd hpI hp1 i (classField_trace (Cl.modes i) c.modelCurlGrad p (hp hpos hpK))
    L F s v s' v'

end Breakdown.CellCert.CellAnalysis

import Mathlib

noncomputable section

namespace Breakdown.Spectral

structure Complexification (X : Type*) where
  re : X
  im : X

namespace Complexification

variable {X : Type*}

@[ext]
theorem ext {z w : Complexification X} (h₁ : z.re = w.re) (h₂ : z.im = w.im) : z = w := by
  cases z; cases w; simp_all

section Group

variable [AddCommGroup X]

instance : Zero (Complexification X) := ⟨⟨0, 0⟩⟩
instance : Add (Complexification X) := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩
instance : Neg (Complexification X) := ⟨fun z => ⟨-z.re, -z.im⟩⟩
instance : Sub (Complexification X) := ⟨fun z w => ⟨z.re - w.re, z.im - w.im⟩⟩
instance : SMul ℕ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩
instance : SMul ℤ (Complexification X) := ⟨fun n z => ⟨n • z.re, n • z.im⟩⟩

@[simp] theorem zero_re : (0 : Complexification X).re = 0 := rfl
@[simp] theorem zero_im : (0 : Complexification X).im = 0 := rfl
@[simp] theorem add_re (z w : Complexification X) : (z + w).re = z.re + w.re := rfl
@[simp] theorem add_im (z w : Complexification X) : (z + w).im = z.im + w.im := rfl
@[simp] theorem neg_re (z : Complexification X) : (-z).re = -z.re := rfl
@[simp] theorem neg_im (z : Complexification X) : (-z).im = -z.im := rfl
@[simp] theorem sub_re (z w : Complexification X) : (z - w).re = z.re - w.re := rfl
@[simp] theorem sub_im (z w : Complexification X) : (z - w).im = z.im - w.im := rfl

def toProd (z : Complexification X) : X × X := (z.re, z.im)

theorem toProd_injective : Function.Injective (toProd : Complexification X → X × X) := by
  intro z w h
  simp only [toProd, Prod.mk.injEq] at h
  exact ext h.1 h.2

instance : AddCommGroup (Complexification X) :=
  Function.Injective.addCommGroup toProd toProd_injective rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Group

section Module

variable [AddCommGroup X] [Module ℝ X]

instance : SMul ℂ (Complexification X) :=
  ⟨fun c z => ⟨c.re • z.re - c.im • z.im, c.im • z.re + c.re • z.im⟩⟩

@[simp] theorem smul_re (c : ℂ) (z : Complexification X) :
    (c • z).re = c.re • z.re - c.im • z.im := rfl
@[simp] theorem smul_im (c : ℂ) (z : Complexification X) :
    (c • z).im = c.im • z.re + c.re • z.im := rfl

instance : Module ℂ (Complexification X) where
  one_smul z := by ext <;> simp
  mul_smul a b z := by
    ext <;> simp only [smul_re, smul_im, Complex.mul_re, Complex.mul_im] <;> module
  smul_zero c := by ext <;> simp
  smul_add c z w := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im] <;> module
  add_smul a b z := by
    ext <;> simp only [smul_re, smul_im, add_re, add_im, Complex.add_re, Complex.add_im] <;> module
  zero_smul z := by ext <;> simp

theorem real_smul_re (r : ℝ) (z : Complexification X) : (r • z).re = r • z.re := by
  rw [← Complex.coe_smul, smul_re, Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]

theorem real_smul_im (r : ℝ) (z : Complexification X) : (r • z).im = r • z.im := by
  rw [← Complex.coe_smul, smul_im, Complex.ofReal_re, Complex.ofReal_im, zero_smul, zero_add]

end Module

section Inner

variable [NormedAddCommGroup X] [InnerProductSpace ℝ X]

@[instance_reducible] def innerStruct : InnerProductSpace.Core ℂ (Complexification X) where
  inner z w := ((inner ℝ z.re w.re + inner ℝ z.im w.im : ℝ) : ℂ) +
    ((inner ℝ z.re w.im - inner ℝ z.im w.re : ℝ) : ℂ) * Complex.I
  conj_inner_symm x y := by
    apply Complex.ext <;> simp <;>
      linarith [real_inner_comm x.re y.re, real_inner_comm x.im y.im, real_inner_comm x.re y.im,
        real_inner_comm x.im y.re]
  re_inner_nonneg x := by
    simp only [RCLike.re_to_complex, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact add_nonneg real_inner_self_nonneg real_inner_self_nonneg
  add_left x y z := by
    apply Complex.ext <;> simp [inner_add_left] <;> ring
  smul_left x y r := by
    apply Complex.ext <;> simp [inner_add_left, inner_sub_left, real_inner_smul_left] <;> ring
  definite x h := by
    have h1 := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at h1
    rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at h1
    have ha : ‖x.re‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.re‖, sq_nonneg ‖x.im‖]
    have hb : ‖x.im‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖x.re‖, sq_nonneg ‖x.im‖]
    ext
    · simpa using ha
    · simpa using hb

instance : NormedAddCommGroup (Complexification X) :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℂ (Complexification X) _ _ _ innerStruct

instance : InnerProductSpace ℂ (Complexification X) :=
  InnerProductSpace.ofCore innerStruct.toCore

theorem norm_sq_eq (z : Complexification X) : ‖z‖ ^ 2 = ‖z.re‖ ^ 2 + ‖z.im‖ ^ 2 := by
  rw [@norm_sq_eq_re_inner ℂ]
  change RCLike.re (((inner ℝ z.re z.re + inner ℝ z.im z.im : ℝ) : ℂ) +
    ((inner ℝ z.re z.im - inner ℝ z.im z.re : ℝ) : ℂ) * Complex.I) = _
  simp [-Complex.ofReal_pow]

theorem norm_re_le (z : Complexification X) : ‖z.re‖ ≤ ‖z‖ := by
  have h := norm_sq_eq z
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖z.im‖])

theorem norm_im_le (z : Complexification X) : ‖z.im‖ ≤ ‖z‖ := by
  have h := norm_sq_eq z
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith [sq_nonneg ‖z.re‖])

private theorem norm_le_norm_re_add_norm_im (z : Complexification X) :
    ‖z‖ ≤ ‖z.re‖ + ‖z.im‖ := by
  have h := norm_sq_eq z
  exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mp
    (by nlinarith [mul_nonneg (norm_nonneg z.re) (norm_nonneg z.im)])

private theorem norm_mk_zero (x : X) : ‖(⟨x, 0⟩ : Complexification X)‖ = ‖x‖ := by
  have h := norm_sq_eq (⟨x, 0⟩ : Complexification X)
  simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

instance [CompleteSpace X] : CompleteSpace (Complexification X) := by
  refine Metric.complete_of_cauchySeq_tendsto fun u hu => ?_
  have hre : CauchySeq fun n => (u n).re := by
    rw [Metric.cauchySeq_iff'] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    have h2 := norm_re_le (u n - u N)
    rw [sub_re] at h2
    exact lt_of_le_of_lt h2 h1
  have him : CauchySeq fun n => (u n).im := by
    rw [Metric.cauchySeq_iff'] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    refine ⟨N, fun n hn => ?_⟩
    have h1 := hN n hn
    rw [dist_eq_norm] at h1 ⊢
    have h2 := norm_im_le (u n - u N)
    rw [sub_im] at h2
    exact lt_of_le_of_lt h2 h1
  obtain ⟨a, ha⟩ := cauchySeq_tendsto_of_complete hre
  obtain ⟨b, hb⟩ := cauchySeq_tendsto_of_complete him
  refine ⟨⟨a, b⟩, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := tendsto_iff_norm_sub_tendsto_zero.mp ha
  have h2 := tendsto_iff_norm_sub_tendsto_zero.mp hb
  have h3 := h1.add h2
  rw [add_zero] at h3
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) h3
  exact norm_le_norm_re_add_norm_im (u n - ⟨a, b⟩)

def ofReal : X →L[ℝ] Complexification X :=
  LinearMap.mkContinuous
    { toFun := fun x => ⟨x, 0⟩
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun r x => by ext <;> simp [real_smul_re, real_smul_im] } 1
    (fun x => by simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]; exact (norm_mk_zero x).le)

@[simp] theorem ofReal_re (x : X) : (ofReal x : Complexification X).re = x := rfl
@[simp] theorem ofReal_im (x : X) : (ofReal x : Complexification X).im = 0 := rfl

theorem norm_ofReal (x : X) : ‖(ofReal x : Complexification X)‖ = ‖x‖ :=
  norm_mk_zero x

def reCLM : Complexification X →L[ℝ] X :=
  LinearMap.mkContinuous
    { toFun := fun z => z.re
      map_add' := fun z w => rfl
      map_smul' := fun r z => real_smul_re r z } 1
    (fun z => by simp only [LinearMap.coe_mk, AddHom.coe_mk, one_mul]; exact norm_re_le z)

@[simp] theorem reCLM_apply (z : Complexification X) : reCLM z = z.re := rfl

def conj : Complexification X →+ Complexification X where
  toFun z := ⟨z.re, -z.im⟩
  map_zero' := by ext <;> simp
  map_add' z w := by ext <;> simp only [add_re, add_im, neg_add]

@[simp] theorem conj_re (z : Complexification X) : (conj z).re = z.re := rfl
@[simp] theorem conj_im (z : Complexification X) : (conj z).im = -z.im := rfl

theorem norm_conj (z : Complexification X) : ‖conj z‖ = ‖z‖ := by
  have h := norm_sq_eq (conj z)
  rw [conj_re, conj_im, norm_neg, ← norm_sq_eq] at h
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h

theorem conj_ofReal (x : X) : conj (ofReal x : Complexification X) = ofReal x := by
  ext <;> simp

theorem eq_ofReal_of_conj_eq {z : Complexification X} (h : conj z = z) : z = ofReal z.re := by
  have h2 : -z.im = z.im := congrArg Complexification.im h
  have h3 : (2 : ℝ) • z.im = 0 := by
    rw [two_smul]
    nth_rewrite 1 [← h2]
    exact neg_add_cancel _
  ext
  · rfl
  · rw [ofReal_im]
    exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

end Inner

end Complexification

end Breakdown.Spectral

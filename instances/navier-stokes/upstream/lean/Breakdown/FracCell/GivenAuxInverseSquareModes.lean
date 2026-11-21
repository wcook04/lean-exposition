import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenAuxInverseSquareRing
import Breakdown.FracCell.GivenAuxDualParts
import Breakdown.FracCell.GivenAuxAdjointCore
import Breakdown.FracCell.GivenAuxActuatorSmooth
import Breakdown.FracCell.GivenProfileSmoothField
import Breakdown.FracCell.GivenProfileBounds
import Breakdown.FracCell.GivenAuxRingModeWeak

open scoped ContDiff ENNReal Pointwise ComplexConjugate
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

def IsRingScalarTrigSum (S : Finset ℤ) (q : Space → ℝ) : Prop :=
  ∀ ρ z : ℝ, ∃ a : ℤ → ℂ, ∀ θ : ℝ,
    ((q (Reduction.ringPoint ρ θ z) : ℝ) : ℂ) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)

namespace RingModesInternal

open SteadyCert

def IsPolyOff (S : Finset ℤ) (u : Space → ℂ) : Prop :=
  ∀ ρ z : ℝ, ρ ≠ 0 → ∃ a : ℤ → ℂ, ∀ θ : ℝ,
    u (Reduction.ringPoint ρ θ z) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)

def IsInv (h : Space → ℂ) : Prop := ∀ ρ θ z : ℝ, h (Reduction.ringPoint ρ θ z) = h (Reduction.ringPoint ρ 0 z)

theorem ring_two (ρ θ z : ℝ) : (Reduction.ringPoint ρ θ z) 2 = z := by
  simp [Reduction.ringPoint]

theorem ring_zero (ρ θ z : ℝ) : (Reduction.ringPoint ρ θ z) 0 = ρ * Real.cos θ := by
  simp [Reduction.ringPoint]

theorem ring_one (ρ θ z : ℝ) : (Reduction.ringPoint ρ θ z) 1 = ρ * Real.sin θ := by
  simp [Reduction.ringPoint]

theorem ring_norm (ρ θ z : ℝ) : ‖Reduction.ringPoint ρ θ z‖ = Real.sqrt (ρ ^ 2 + z ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three, ring_zero, ring_one, ring_two]
  congr 1
  simp only [Real.norm_eq_abs, sq_abs]
  have h := Real.cos_sq_add_sin_sq θ
  linear_combination ρ ^ 2 * h

theorem ring_axis (θ z : ℝ) : Reduction.ringPoint 0 θ z = Reduction.ringPoint 0 0 z := by
  simp [Reduction.ringPoint]

theorem IsPolyOff.mono {S T : Finset ℤ} (hST : S ⊆ T) {u : Space → ℂ} (hu : IsPolyOff S u) : IsPolyOff T u := by
  classical
  intro ρ z hρ
  obtain ⟨a, h⟩ := hu ρ z hρ
  refine ⟨fun n => if n ∈ S then a n else 0, fun θ => ?_⟩
  rw [h θ, ← Finset.sum_subset hST (fun n _ hn => by simp [hn])]
  exact Finset.sum_congr rfl fun n hn => by simp [hn]

theorem IsPolyOff.add {S T : Finset ℤ} {u v : Space → ℂ} (hu : IsPolyOff S u) (hv : IsPolyOff T v) :
    IsPolyOff (S ∪ T) (fun y => u y + v y) := by
  intro ρ z hρ
  obtain ⟨a, ha⟩ := (hu.mono (Finset.subset_union_left (s₂ := T))) ρ z hρ
  obtain ⟨b, hb⟩ := (hv.mono (Finset.subset_union_right (s₁ := S))) ρ z hρ
  refine ⟨fun n => a n + b n, fun θ => ?_⟩
  simp only [ha θ, hb θ, add_mul, Finset.sum_add_distrib]

theorem IsPolyOff.mul {S T : Finset ℤ} {u v : Space → ℂ} (hu : IsPolyOff S u) (hv : IsPolyOff T v) :
    IsPolyOff (S + T) (fun y => u y * v y) := by
  classical
  intro ρ z hρ
  obtain ⟨a, ha⟩ := hu ρ z hρ
  obtain ⟨b, hb⟩ := hv ρ z hρ
  refine ⟨fun k => ∑ q ∈ (S ×ˢ T).filter (fun q : ℤ × ℤ => q.1 + q.2 = k), a q.1 * b q.2, fun θ => ?_⟩
  show u _ * v _ = _
  rw [ha θ, hb θ, Finset.sum_mul_sum, ← Finset.sum_product']
  rw [← Finset.sum_fiberwise_of_maps_to (s := S ×ˢ T) (t := S + T) (g := fun q : ℤ × ℤ => q.1 + q.2)
    (fun q hq => Finset.add_mem_add (Finset.mem_product.1 hq).1 (Finset.mem_product.1 hq).2)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hk : q.1 + q.2 = k := (Finset.mem_filter.1 hq).2
  rw [← hk]
  push_cast
  rw [add_mul, add_mul, Complex.exp_add]
  ring

theorem IsPolyOff.conj {S : Finset ℤ} {u : Space → ℂ} (hu : IsPolyOff S u) :
    IsPolyOff (S.image (fun n => -n)) (fun y => conj (u y)) := by
  intro ρ z hρ
  obtain ⟨a, ha⟩ := hu ρ z hρ
  refine ⟨fun n => conj (a (-n)), fun θ => ?_⟩
  show conj (u _) = _
  rw [ha θ, map_sum, Finset.sum_image (fun x _ y _ h => neg_injective h)]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [neg_neg, map_mul, ← Complex.exp_conj, map_intCast, Complex.conj_ofReal, Complex.conj_I]
  congr 2
  push_cast
  ring

theorem IsPolyOff.const_mul {S : Finset ℤ} {u : Space → ℂ} (c : ℂ) (hu : IsPolyOff S u) :
    IsPolyOff S (fun y => c * u y) := by
  intro ρ z hρ
  obtain ⟨a, ha⟩ := hu ρ z hρ
  refine ⟨fun n => c * a n, fun θ => ?_⟩
  show c * u _ = _
  rw [ha θ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by ring

theorem IsPolyOff.zero : IsPolyOff ∅ (fun _ => 0) := fun ρ z _ => ⟨fun _ => 0, fun θ => by simp⟩

theorem IsPolyOff.sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ) (hf : ∀ i ∈ s, ∃ S, IsPolyOff S (f i)) :
    ∃ S, IsPolyOff S (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simpa using IsPolyOff.zero⟩
  | insert i s hi ih =>
    obtain ⟨S, hS⟩ := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    obtain ⟨T, hT⟩ := hf i (Finset.mem_insert_self i s)
    exact ⟨T ∪ S, by simpa only [Finset.sum_insert hi] using hT.add hS⟩

theorem IsPolyOff.of_inv {h : Space → ℂ} (hh : IsInv h) : IsPolyOff {0} h := by
  intro ρ z _
  refine ⟨fun _ => h (Reduction.ringPoint ρ 0 z), fun θ => ?_⟩
  simp [hh ρ θ z]

theorem IsPolyOff.ofReal_re {S : Finset ℤ} {u : Space → ℂ} (hu : IsPolyOff S u) :
    IsPolyOff (S ∪ S.image (fun n => -n)) (fun y => (((u y).re : ℝ) : ℂ)) := by
  have h := (hu.add hu.conj).const_mul (1 / 2 : ℂ)
  have e : (fun y => (((u y).re : ℝ) : ℂ)) = fun y => (1 / 2 : ℂ) * (u y + conj (u y)) := by
    funext y
    rw [Complex.re_eq_add_conj]
    ring
  rw [e]
  exact h

theorem IsPolyOff.ofReal_im {S : Finset ℤ} {u : Space → ℂ} (hu : IsPolyOff S u) :
    IsPolyOff (S ∪ S.image (fun n => -n)) (fun y => (((u y).im : ℝ) : ℂ)) := by
  have h := (hu.add (hu.conj.const_mul (-1))).const_mul (1 / (2 * Complex.I))
  have e : (fun y => (((u y).im : ℝ) : ℂ)) = fun y => (1 / (2 * Complex.I)) * (u y + (-1) * conj (u y)) := by
    funext y
    rw [Complex.im_eq_sub_conj]
    ring
  rw [e]
  exact h

theorem IsPolyOff.plane : IsPolyOff {1} (fun y => ((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ)) := by
  intro ρ z _
  refine ⟨fun _ => (ρ : ℂ), fun θ => ?_⟩
  simp only [ring_zero, ring_one, Finset.sum_singleton, Int.cast_one, one_mul]
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

theorem IsPolyOff.angle (M : ℤ) : IsPolyOff {M} (fun y => Complex.exp (Complex.I * ((M : ℝ) * angleOf y : ℝ))) := by
  intro ρ z hρ
  refine ⟨fun _ => ((ρ / |ρ| : ℝ) : ℂ) ^ M, fun θ => ?_⟩
  rw [Finset.sum_singleton]
  set w : ℂ := ⟨(Reduction.ringPoint ρ θ z) 0, (Reduction.ringPoint ρ θ z) 1⟩ with hw
  have hw' : w = (ρ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, hw]
    apply Complex.ext <;> simp [ring_zero, ring_one, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hnorm : ‖w‖ = |ρ| := by
    rw [hw', norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnorm
    exact hρ (abs_eq_zero.1 hnorm.symm)
  have hexp : Complex.exp ((Complex.arg w : ℂ) * Complex.I) = ((ρ / |ρ| : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    have h1 := Complex.norm_mul_exp_arg_mul_I w
    rw [hnorm] at h1
    have habsR : |ρ| ≠ 0 := abs_ne_zero.2 hρ
    have habs : ((|ρ| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast habsR
    refine mul_left_cancel₀ habs ?_
    rw [h1, hw']
    push_cast
    field_simp
  show Complex.exp (Complex.I * ((M : ℝ) * Complex.arg w : ℝ)) = _
  have e1 : Complex.I * (((M : ℝ) * Complex.arg w : ℝ) : ℂ) = (M : ℂ) * ((Complex.arg w : ℂ) * Complex.I) := by
    push_cast
    ring
  rw [e1, Complex.exp_int_mul, hexp, mul_zpow, ← Complex.exp_int_mul]
  congr 2
  ring


open SteadyCert

theorem trig_of_polyOff {S T : Finset ℤ} {F : Space → Space} (hh : IsPolyOff S (Reduction.horizontalPart F))
    (hv : IsPolyOff T (Reduction.verticalPart F)) : IsRingTrigSum (insert 0 (S ∪ T)) F := by
  intro ρ z
  by_cases hρ : ρ = 0
  · subst hρ
    refine ⟨fun n => if n = 0 then Reduction.horizontalPart F (Reduction.ringPoint 0 0 z) else 0,
      fun n => if n = 0 then Reduction.verticalPart F (Reduction.ringPoint 0 0 z) else 0, fun θ => ⟨?_, ?_⟩⟩ <;>
      rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)] <;> simp [ring_axis θ z]
  · have h1 : S ⊆ insert 0 (S ∪ T) := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_left T hx)
    have h2 : T ⊆ insert 0 (S ∪ T) := fun x hx => Finset.mem_insert_of_mem (Finset.mem_union_right S hx)
    obtain ⟨a, ha⟩ := (hh.mono h1) ρ z hρ
    obtain ⟨b, hb⟩ := (hv.mono h2) ρ z hρ
    exact ⟨a, b, fun θ => ⟨ha θ, hb θ⟩⟩

theorem ex_add {u v : Space → ℂ} (hu : ∃ S, IsPolyOff S u) (hv : ∃ S, IsPolyOff S v) :
    ∃ S, IsPolyOff S (fun y => u y + v y) := by
  obtain ⟨S, hS⟩ := hu
  obtain ⟨T, hT⟩ := hv
  exact ⟨_, hS.add hT⟩

theorem ex_mul {u v : Space → ℂ} (hu : ∃ S, IsPolyOff S u) (hv : ∃ S, IsPolyOff S v) :
    ∃ S, IsPolyOff S (fun y => u y * v y) := by
  obtain ⟨S, hS⟩ := hu
  obtain ⟨T, hT⟩ := hv
  exact ⟨_, hS.mul hT⟩

theorem ex_conj {u : Space → ℂ} (hu : ∃ S, IsPolyOff S u) : ∃ S, IsPolyOff S (fun y => conj (u y)) := by
  obtain ⟨S, hS⟩ := hu
  exact ⟨_, hS.conj⟩

theorem ex_re {u : Space → ℂ} (hu : ∃ S, IsPolyOff S u) : ∃ S, IsPolyOff S (fun y => (((u y).re : ℝ) : ℂ)) := by
  obtain ⟨S, hS⟩ := hu
  exact ⟨_, hS.ofReal_re⟩

theorem ex_inv {h : Space → ℂ} (hh : IsInv h) : ∃ S, IsPolyOff S h := ⟨_, IsPolyOff.of_inv hh⟩

theorem ex_angle (M : ℤ) : ∃ S, IsPolyOff S (fun y => Complex.exp (Complex.I * ((M : ℝ) * angleOf y : ℝ))) :=
  ⟨_, IsPolyOff.angle M⟩

theorem ex_sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ) (hf : ∀ i ∈ s, ∃ S, IsPolyOff S (f i)) :
    ∃ S, IsPolyOff S (fun y => ∑ i ∈ s, f i y) := IsPolyOff.sum s f hf

theorem ex_const (c : ℂ) : ∃ S, IsPolyOff S (fun _ => c) := ex_inv (fun _ _ _ => rfl)

theorem ex_coord (i : Fin 3) : ∃ S, IsPolyOff S (fun y => ((y i : ℝ) : ℂ)) := by
  fin_cases i
  · have e : (fun y : Space => ((y 0 : ℝ) : ℂ)) =
        fun y => (((((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ)).re : ℝ) : ℂ) := by
      funext y
      simp
    show ∃ S, IsPolyOff S (fun y : Space => ((y 0 : ℝ) : ℂ))
    rw [e]
    exact ⟨_, IsPolyOff.plane.ofReal_re⟩
  · have e : (fun y : Space => ((y 1 : ℝ) : ℂ)) =
        fun y => (((((y 0 : ℝ) : ℂ) + Complex.I * ((y 1 : ℝ) : ℂ)).im : ℝ) : ℂ) := by
      funext y
      simp
    show ∃ S, IsPolyOff S (fun y : Space => ((y 1 : ℝ) : ℂ))
    rw [e]
    exact ⟨_, IsPolyOff.plane.ofReal_im⟩
  · exact ex_inv (fun ρ θ z => by simp [ring_two])

theorem ex_normInv (f : ℝ → ℝ → ℂ) : ∃ S, IsPolyOff S (fun y => f ‖y‖ (y 2)) :=
  ex_inv (fun ρ θ z => by simp only [ring_norm, ring_two])

theorem ex_atomTerm (P : ChartParams) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) :
    ∃ T, IsPolyOff T (atomTerm P j a M β S) := by
  have e : atomTerm P j a M β S = fun y => Complex.exp (Complex.I * ((M : ℝ) * angleOf y : ℝ)) *
      (Complex.exp (Complex.I * ((j : ℝ) * β * logPhase P y : ℝ)) * ((Real.sqrt (qOf y) ^ a : ℝ) : ℂ) *
        S.eval (decide (a = 0)) (chartT P y) (heightRatio y)) := by
    funext y
    unfold atomTerm
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
    ring
  rw [e]
  refine ex_mul (ex_angle M) ?_
  exact ex_normInv (fun r h => Complex.exp (Complex.I * ((j : ℝ) * β * ((1 / 2) * Real.log (1 + r ^ 2 / P.rc ^ 2)) : ℝ)) *
    ((Real.sqrt (1 - (h / r) ^ 2) ^ a : ℝ) : ℂ) * S.eval (decide (a = 0)) (r / (r + P.L0)) (h / r)) |>.imp
    fun T hT => by simpa [logPhase, qOf, heightRatio, chartT] using hT


theorem ofc (w : Fin 3 → ℝ) (k : Fin 3) : ofComponents w k = w k := by
  fin_cases k <;> simp [ofComponents]

theorem ex_decay (P : ChartParams) : ∃ S, IsPolyOff S (fun y => ((decayFactor P y : ℝ) : ℂ)) :=
  ex_normInv (fun r _ => (((1 - r / (r + P.L0)) ^ (2 * P.eps) : ℝ) : ℂ))

theorem ex_hor_atom (P : ChartParams) (X : AtomData) (β : ℝ) :
    ∃ S, IsPolyOff S (Reduction.horizontalPart (atomOf P X β)) := by
  have e : Reduction.horizontalPart (atomOf P X β) = atomPlane P X β := by
    funext y
    simp only [Reduction.horizontalPart, atomOf, ofc]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [mul_comm Complex.I]
    exact Complex.re_add_im _
  rw [e]
  exact ex_mul (ex_decay P) (ex_add (ex_sum _ _ fun j _ => ex_atomTerm P j 1 _ β _)
    (ex_sum _ _ fun j _ => ex_conj (ex_atomTerm P j 1 _ β _)))

theorem ex_vert_atom (P : ChartParams) (X : AtomData) (β : ℝ) :
    ∃ S, IsPolyOff S (Reduction.verticalPart (atomOf P X β)) := by
  have e : Reduction.verticalPart (atomOf P X β) = fun y => (((atomHeight P X β y).re : ℝ) : ℂ) := by
    funext y
    simp only [Reduction.verticalPart, atomOf, ofc]
    simp
  rw [e]
  exact ex_re (ex_mul (ex_decay P) (ex_sum _ _ fun j _ => ex_mul (ex_const _) (ex_atomTerm P j 0 _ β _)))

theorem ex_modePhase (P : ChartParams) (n : ℤ) (β : ℝ) : ∃ S, IsPolyOff S (modePhase P n β) := by
  have e : modePhase P n β = fun y => Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * angleOf y : ℝ)) *
      Complex.exp (Complex.I * ((n : ℝ) * β * logPhase P y : ℝ)) := by
    funext y
    unfold modePhase
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [e]
  exact ex_mul (ex_angle _) (ex_normInv (fun r _ => Complex.exp (Complex.I *
    ((n : ℝ) * β * ((1 / 2) * Real.log (1 + r ^ 2 / P.rc ^ 2)) : ℝ))))

theorem ex_radial (i : Fin 3) : ∃ S, IsPolyOff S (fun y => ((radialVec y i : ℝ) : ℂ)) := by
  have e : (fun y => ((radialVec y i : ℝ) : ℂ)) = fun y => ((y i : ℝ) : ℂ) * ((1 / ‖y‖ : ℝ) : ℂ) := by
    funext y
    simp [radialVec, div_eq_mul_inv]
  rw [e]
  exact ex_mul (ex_coord i) (ex_normInv (fun r _ => ((1 / r : ℝ) : ℂ)))

theorem ex_polar (i : Fin 3) : ∃ S, IsPolyOff S (fun y => ((polarVecQ y i : ℝ) : ℂ)) := by
  fin_cases i
  · have e : (fun y => ((polarVecQ y 0 : ℝ) : ℂ)) = fun y => ((y 0 : ℝ) : ℂ) * ((heightRatio y / ‖y‖ : ℝ) : ℂ) := by
      funext y
      simp [polarVecQ]
      ring
    show ∃ S, IsPolyOff S (fun y => ((polarVecQ y 0 : ℝ) : ℂ))
    rw [e]
    exact ex_mul (ex_coord 0) (ex_normInv (fun r h => ((h / r / r : ℝ) : ℂ)))
  · have e : (fun y => ((polarVecQ y 1 : ℝ) : ℂ)) = fun y => ((y 1 : ℝ) : ℂ) * ((heightRatio y / ‖y‖ : ℝ) : ℂ) := by
      funext y
      simp [polarVecQ]
      ring
    show ∃ S, IsPolyOff S (fun y => ((polarVecQ y 1 : ℝ) : ℂ))
    rw [e]
    exact ex_mul (ex_coord 1) (ex_normInv (fun r h => ((h / r / r : ℝ) : ℂ)))
  · have e : (fun y => ((polarVecQ y 2 : ℝ) : ℂ)) = fun y => ((-(1 - (y 2 / ‖y‖) ^ 2) : ℝ) : ℂ) := by
      funext y
      simp [polarVecQ, qOf, heightRatio]
    show ∃ S, IsPolyOff S (fun y => ((polarVecQ y 2 : ℝ) : ℂ))
    rw [e]
    exact ex_normInv (fun r h => ((-(1 - (h / r) ^ 2) : ℝ) : ℂ))

theorem ex_azim (i : Fin 3) : ∃ S, IsPolyOff S (fun y => ((azimVecQ y i : ℝ) : ℂ)) := by
  fin_cases i
  · have e : (fun y => ((azimVecQ y 0 : ℝ) : ℂ)) = fun y => ((y 1 : ℝ) : ℂ) * ((-(1 / ‖y‖) : ℝ) : ℂ) := by
      funext y
      simp [azimVecQ]
      ring
    show ∃ S, IsPolyOff S (fun y => ((azimVecQ y 0 : ℝ) : ℂ))
    rw [e]
    exact ex_mul (ex_coord 1) (ex_normInv (fun r _ => ((-(1 / r) : ℝ) : ℂ)))
  · have e : (fun y => ((azimVecQ y 1 : ℝ) : ℂ)) = fun y => ((y 0 : ℝ) : ℂ) * ((1 / ‖y‖ : ℝ) : ℂ) := by
      funext y
      simp [azimVecQ]
      ring
    show ∃ S, IsPolyOff S (fun y => ((azimVecQ y 1 : ℝ) : ℂ))
    rw [e]
    exact ex_mul (ex_coord 0) (ex_normInv (fun r _ => ((1 / r : ℝ) : ℂ)))
  · have e : (fun y => ((azimVecQ y 2 : ℝ) : ℂ)) = fun _ => (0 : ℂ) := by
      funext y
      simp [azimVecQ]
    show ∃ S, IsPolyOff S (fun y => ((azimVecQ y 2 : ℝ) : ℂ))
    rw [e]
    exact ex_const 0

theorem ex_fieldComp (P : ChartParams) (D : FieldData) (β : ℝ) (i : Fin 3) :
    ∃ S, IsPolyOff S (fun y => (decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i)) := by
  have hr : ∀ (n : ℤ) (l : Fin 3), ∃ S, IsPolyOff S (fun y => reducedField P D n β (chartT P y) (heightRatio y) l) :=
    fun n l => ex_normInv (fun r h => reducedField P D n β (r / (r + P.L0)) (h / r) l)
  exact ex_mul (ex_decay P) (ex_sum _ _ fun n _ => ex_mul (ex_modePhase P n β)
    (ex_add (ex_add (ex_mul (hr n 0) (ex_radial i)) (ex_mul (hr n 1) (ex_polar i))) (ex_mul (hr n 2) (ex_azim i))))

theorem scalar_of_polyOff {S : Finset ℤ} {q : Space → ℝ} (h : IsPolyOff S (fun y => ((q y : ℝ) : ℂ))) :
    IsRingScalarTrigSum (insert 0 S) q := by
  intro ρ z
  by_cases hρ : ρ = 0
  · subst hρ
    refine ⟨fun n => if n = 0 then ((q (Reduction.ringPoint 0 0 z) : ℝ) : ℂ) else 0, fun θ => ?_⟩
    rw [Finset.sum_eq_single 0 (by intro b _ hb; simp [hb]) (by simp)]
    simp [ring_axis θ z]
  · obtain ⟨a, ha⟩ := (h.mono (Finset.subset_insert 0 S)) ρ z hρ
    exact ⟨a, ha⟩

theorem cellIndex_le (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  refine (List.length_filter_le _ _).trans ?_
  simp only [List.length_dropLast, List.length_drop]
  omega

theorem spline_bd (S : Spline) (odd : Bool) :
    ∃ B : ℝ, ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 → ‖S.eval odd t x‖ ≤ B := by
  choose B hB0 hB using fun ik : ℕ × ℕ => DualPartsInternal.poly_bound (S.piece ik.1 ik.2)
  refine ⟨∑ ik ∈ Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1), B ik,
    fun t x ht hx => ?_⟩
  have h1 : ‖S.eval odd t x‖ = ‖S.evalHalf t |x|‖ := by
    unfold Spline.eval
    split_ifs <;> simp
  rw [h1]
  unfold Spline.evalHalf
  refine (hB (cellIndex S.mesh.tBreaks t, cellIndex S.mesh.xBreaks |x|) t |x| ht (by rwa [abs_abs])).trans
    (Finset.single_le_sum (f := B) (fun ik _ => hB0 ik) ?_)
  simp only [Finset.mem_product, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (cellIndex_le _ _), Nat.lt_succ_of_le (cellIndex_le _ _)⟩

def IsBdd (u : Space → ℂ) : Prop := ∃ C : ℝ, ∀ y, ‖u y‖ ≤ C

theorem IsBdd.mul {u v : Space → ℂ} (hu : IsBdd u) (hv : IsBdd v) : IsBdd (fun y => u y * v y) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  refine ⟨C * D, fun y => ?_⟩
  rw [norm_mul]
  exact mul_le_mul (hC y) (hD y) (norm_nonneg _) ((norm_nonneg _).trans (hC y))

theorem IsBdd.add {u v : Space → ℂ} (hu : IsBdd u) (hv : IsBdd v) : IsBdd (fun y => u y + v y) := by
  obtain ⟨C, hC⟩ := hu
  obtain ⟨D, hD⟩ := hv
  exact ⟨C + D, fun y => (norm_add_le _ _).trans (add_le_add (hC y) (hD y))⟩

theorem IsBdd.conj {u : Space → ℂ} (hu : IsBdd u) : IsBdd (fun y => conj (u y)) := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun y => by rw [Complex.norm_conj]; exact hC y⟩

theorem IsBdd.const (c : ℂ) : IsBdd (fun _ => c) := ⟨‖c‖, fun _ => le_rfl⟩

theorem IsBdd.sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℂ) (hf : ∀ i ∈ s, IsBdd (f i)) :
    IsBdd (fun y => ∑ i ∈ s, f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun y => by simp⟩
  | insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self i s)).add (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using h

theorem chartT_abs (P : ChartParams) (hP : IsChartParams P) (y : Space) : |chartT P y| ≤ 1 := by
  unfold chartT
  have h0 : 0 < ‖y‖ + P.L0 := by linarith [norm_nonneg y, hP.L0_pos]
  rw [abs_le]
  constructor
  · have : 0 ≤ ‖y‖ / (‖y‖ + P.L0) := div_nonneg (norm_nonneg y) h0.le
    linarith
  · rw [div_le_one h0]
    linarith [hP.L0_pos]

theorem height_abs (y : Space) : |heightRatio y| ≤ 1 := by
  unfold heightRatio
  rcases eq_or_lt_of_le (norm_nonneg y) with h | h
  · rw [← h, div_zero, abs_zero]
    norm_num
  · rw [abs_div, abs_of_pos h, div_le_one h]
    exact (PiLp.norm_apply_le y 2).trans_eq' (Real.norm_eq_abs _).symm

theorem q_bounds (y : Space) : 0 ≤ qOf y ∧ qOf y ≤ 1 := by
  unfold qOf
  have h := height_abs y
  have h2 : heightRatio y ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (heightRatio y)]
  constructor <;> nlinarith [sq_nonneg (heightRatio y)]

theorem bdd_atomTerm (P : ChartParams) (hP : IsChartParams P) (j a : ℕ) (M : ℤ) (β : ℝ) (S : Spline) :
    IsBdd (atomTerm P j a M β S) := by
  obtain ⟨B, hB⟩ := spline_bd S (decide (a = 0))
  refine ⟨1 * 1 * B, fun y => ?_⟩
  unfold atomTerm
  rw [norm_mul, norm_mul]
  have e1 : ‖Complex.exp (Complex.I * (((j : ℝ) * β * logPhase P y + (M : ℝ) * angleOf y : ℝ) : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have e2 : ‖(((Real.sqrt (qOf y) ^ a : ℝ)) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) a)]
    exact pow_le_one₀ (Real.sqrt_nonneg _) (Real.sqrt_le_one.mpr (q_bounds y).2)
  have e3 := hB (chartT P y) (heightRatio y) (chartT_abs P hP y) (height_abs y)
  rw [e1]
  have hB0 : 0 ≤ B := (norm_nonneg _).trans e3
  exact mul_le_mul (mul_le_mul_of_nonneg_left e2 zero_le_one) e3 (norm_nonneg _) (by norm_num)

theorem bdd_decay (P : ChartParams) (hP : IsChartParams P) : IsBdd (fun y => ((decayFactor P y : ℝ) : ℂ)) := by
  refine ⟨1, fun y => ?_⟩
  have ht := chartT_abs P hP y
  have ht0 : 0 ≤ chartT P y := div_nonneg (norm_nonneg y) (by linarith [norm_nonneg y, hP.L0_pos])
  have hs0 : 0 ≤ chartS P y := by unfold chartS; linarith [(abs_le.1 ht).2]
  have hs1 : chartS P y ≤ 1 := by unfold chartS; linarith
  rw [Complex.norm_real, Real.norm_eq_abs, decayFactor, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
  exact Real.rpow_le_one hs0 hs1 (by linarith [hP.eps_pos])

theorem bdd_re {u : Space → ℂ} (hu : IsBdd u) : ∃ C : ℝ, ∀ y, |(u y).re| ≤ C := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun y => (Complex.abs_re_le_norm _).trans (hC y)⟩

theorem bdd_im {u : Space → ℂ} (hu : IsBdd u) : ∃ C : ℝ, ∀ y, |(u y).im| ≤ C := by
  obtain ⟨C, hC⟩ := hu
  exact ⟨C, fun y => (Complex.abs_im_le_norm _).trans (hC y)⟩

theorem ofComponents_norm (w : Fin 3 → ℝ) : ‖ofComponents w‖ ≤ |w 0| + |w 1| + |w 2| := by
  unfold ofComponents
  refine (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ?_ ?_)) ?_) <;>
    simp [PiLp.norm_single]

theorem ofComponents_meas {f g h : Space → ℝ} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) :
    Measurable (fun y => ofComponents ![f y, g y, h y]) := by
  have e : (fun y => ofComponents ![f y, g y, h y]) = fun y => WithLp.toLp 2 (![f y, g y, h y] : Fin 3 → ℝ) := by
    funext y
    ext i
    fin_cases i <;> simp [ofComponents]
  rw [e]
  refine (WithLp.measurable_toLp 2 (Fin 3 → ℝ)).comp ?_
  exact measurable_pi_iff.2 fun i => by fin_cases i <;> simpa

theorem atomOf_meas_bdd (P : ChartParams) (hP : IsChartParams P) (X : AtomData) (β : ℝ) :
    Measurable (atomOf P X β) ∧ ∃ C : ℝ, ∀ y, ‖atomOf P X β y‖ ≤ C := by
  have hd : Measurable (fun y : Space => ((decayFactor P y : ℝ) : ℂ)) := by
    unfold decayFactor chartS chartT
    fun_prop
  have hpm : Measurable (atomPlane P X β) := by
    unfold atomPlane
    exact hd.mul ((Finset.measurable_sum _ fun j _ => DualPartsInternal.atom_measurable P j 1 _ β _).add
      (Finset.measurable_sum _ fun j _ => Complex.continuous_conj.measurable.comp
        (DualPartsInternal.atom_measurable P j 1 _ β _)))
  have hhm : Measurable (atomHeight P X β) := by
    unfold atomHeight
    exact hd.mul (Finset.measurable_sum _ fun j _ => measurable_const.mul
      (DualPartsInternal.atom_measurable P j 0 _ β _))
  have hm : Measurable (atomOf P X β) :=
    ofComponents_meas (Complex.measurable_re.comp hpm) (Complex.measurable_im.comp hpm) (Complex.measurable_re.comp hhm)
  have hpb : IsBdd (atomPlane P X β) :=
    (bdd_decay P hP).mul ((IsBdd.sum _ _ fun j _ => bdd_atomTerm P hP j 1 _ β _).add
      (IsBdd.sum _ _ fun j _ => (bdd_atomTerm P hP j 1 _ β _).conj))
  have hhb : IsBdd (atomHeight P X β) :=
    (bdd_decay P hP).mul (IsBdd.sum _ _ fun j _ => (IsBdd.const _).mul (bdd_atomTerm P hP j 0 _ β _))
  obtain ⟨C1, h1⟩ := bdd_re hpb
  obtain ⟨C2, h2⟩ := bdd_im hpb
  obtain ⟨C3, h3⟩ := bdd_re hhb
  refine ⟨hm, C1 + C2 + C3, fun y => ?_⟩
  exact (ofComponents_norm _).trans (by simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]; linarith [h1 y, h2 y, h3 y])

theorem atomOf_locInt (P : ChartParams) (hP : IsChartParams P) (X : AtomData) (β : ℝ) :
    LocallyIntegrable (atomOf P X β) volume := by
  obtain ⟨hm, C, hC⟩ := atomOf_meas_bdd P hP X β
  exact (memLp_top_of_bound hm.aestronglyMeasurable C (Filter.Eventually.of_forall hC)).locallyIntegrable le_top

theorem radial_meas : Measurable (fun y : Space => ofComponents (radialVec y)) := by
  have hc : ∀ i : Fin 3, Measurable (fun y : Space => radialVec y i) := fun i =>
    (show Continuous (fun y : Space => y i) from (PiLp.continuous_apply 2 _ i)).measurable.div measurable_norm
  have e : (fun y : Space => ofComponents (radialVec y)) = fun y => ofComponents ![radialVec y 0, radialVec y 1, radialVec y 2] := by
    funext y
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [e]
  exact ofComponents_meas (hc 0) (hc 1) (hc 2)

theorem radial_bdd (y : Space) : ‖ofComponents (radialVec y)‖ ≤ 3 := by
  have h : ∀ i : Fin 3, |radialVec y i| ≤ 1 := by
    intro i
    unfold radialVec
    rcases eq_or_lt_of_le (norm_nonneg y) with h | h
    · rw [← h, div_zero, abs_zero]
      norm_num
    · rw [abs_div, abs_of_pos h, div_le_one h]
      exact (PiLp.norm_apply_le y i).trans_eq' (Real.norm_eq_abs _).symm
  linarith [ofComponents_norm (radialVec y), h 0, h 1, h 2]

theorem fluxOf_locInt (P : ChartParams) (hP : IsChartParams P) (F : FluxData) (β : ℝ) :
    LocallyIntegrable (fun y => fluxOf P F β y) volume := by
  obtain ⟨hm, C, hC⟩ := atomOf_meas_bdd P hP F β
  have hcont : Continuous (fun q : Space × Space => (innerSL ℝ q.1).smulRight q.2) :=
    (ContinuousLinearMap.smulRightL ℝ Space Space).continuous₂.comp
      (((innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).continuous.comp continuous_fst).prodMk continuous_snd)
  have hfm : Measurable (fun y => fluxOf P F β y) := by
    have h2 := hcont.measurable.comp (radial_meas.prodMk hm)
    simp only [Function.comp_def] at h2
    unfold fluxOf
    exact h2
  refine (memLp_top_of_bound hfm.aestronglyMeasurable (3 * C) (Filter.Eventually.of_forall fun y => ?_)).locallyIntegrable le_top
  unfold fluxOf
  refine (ContinuousLinearMap.norm_smulRight_apply _ _).le.trans ?_
  rw [innerSL_apply_norm]
  exact mul_le_mul (radial_bdd y) (hC y) (norm_nonneg _) (by norm_num)

theorem angle_meas : Measurable (fun y : Space => angleOf y) := by
  have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y => Complex.equivRealProdCLM.symm (y 0, y 1) := by
    funext y
    apply Complex.ext <;> simp
  unfold angleOf
  rw [show (fun y : Space => Complex.arg (⟨y 0, y 1⟩ : ℂ)) = fun y => Complex.arg ((fun y : Space => (⟨y 0, y 1⟩ : ℂ)) y)
    from rfl, e]
  exact Complex.measurable_arg.comp (Complex.equivRealProdCLM.symm.continuous.comp (by fun_prop)).measurable

theorem modePhase_meas (P : ChartParams) (n : ℤ) (β : ℝ) : Measurable (modePhase P n β) := by
  unfold modePhase logPhase
  have := angle_meas
  fun_prop

theorem bdd_modePhase (P : ChartParams) (n : ℤ) (β : ℝ) : IsBdd (modePhase P n β) :=
  ⟨1, fun y => by unfold modePhase; rw [mul_comm]; exact (Complex.norm_exp_ofReal_mul_I _).le⟩

theorem decay_abs (P : ChartParams) (hP : IsChartParams P) (y : Space) : |decayFactor P y| ≤ 1 := by
  obtain ⟨C, hC⟩ := bdd_decay P hP
  have ht := chartT_abs P hP y
  have ht0 : 0 ≤ chartT P y := div_nonneg (norm_nonneg y) (by linarith [norm_nonneg y, hP.L0_pos])
  have hs0 : 0 ≤ chartS P y := by unfold chartS; linarith [(abs_le.1 ht).2]
  have hs1 : chartS P y ≤ 1 := by unfold chartS; linarith
  rw [decayFactor, abs_of_nonneg (Real.rpow_nonneg hs0 _)]
  exact Real.rpow_le_one hs0 hs1 (by linarith [hP.eps_pos])

theorem shape_meas (P : ChartParams) (low high ax : ℕ) (S : Spline) :
    Measurable (fun y => pressureShape P low high ax S y) := by
  have hT : Measurable (fun y : Space => chartT P y) := by
    unfold chartT
    fun_prop
  have hH : Measurable (fun y : Space => heightRatio y) := by
    unfold heightRatio
    fun_prop
  have hS : Measurable (fun y : Space => chartS P y) := by
    unfold chartS
    exact measurable_const.sub hT
  have hQ : Measurable (fun y : Space => qOf y) := by
    unfold qOf
    exact measurable_const.sub (hH.pow_const 2)
  have h0 := DualPartsInternal.eval_measurable S false
  have h2 := h0.comp (hT.prodMk hH)
  simp only [Function.comp_def, Function.uncurry_apply_pair] at h2
  show Measurable (fun y => ((chartT P y ^ low * chartS P y ^ high * qOf y ^ ax : ℝ) : ℂ) *
    S.eval false (chartT P y) (heightRatio y))
  exact (Complex.measurable_ofReal.comp (((hT.pow_const low).mul (hS.pow_const high)).mul (hQ.pow_const ax))).mul h2

theorem bdd_shape (P : ChartParams) (hP : IsChartParams P) (low high ax : ℕ) (S : Spline) :
    IsBdd (fun y => pressureShape P low high ax S y) := by
  obtain ⟨B, hB⟩ := spline_bd S false
  refine ⟨1 * B, fun y => ?_⟩
  unfold pressureShape
  have ht := chartT_abs P hP y
  have ht0 : 0 ≤ chartT P y := div_nonneg (norm_nonneg y) (by linarith [norm_nonneg y, hP.L0_pos])
  have hs0 : 0 ≤ chartS P y := by unfold chartS; linarith [(abs_le.1 ht).2]
  have hs1 : chartS P y ≤ 1 := by unfold chartS; linarith
  have hq := q_bounds y
  have e3 := hB (chartT P y) (heightRatio y) ht (height_abs y)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hprod : |chartT P y ^ low * chartS P y ^ high * qOf y ^ ax| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (pow_nonneg ht0 _) (pow_nonneg hs0 _)) (pow_nonneg hq.1 _))]
    exact mul_le_one₀ (mul_le_one₀ (pow_le_one₀ ht0 (abs_le.1 ht).2) (pow_nonneg hs0 _) (pow_le_one₀ hs0 hs1))
      (pow_nonneg hq.1 _) (pow_le_one₀ hq.1 hq.2)
  exact mul_le_mul hprod e3 (norm_nonneg _) zero_le_one

theorem pressureOf_locInt (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (β : ℝ) :
    LocallyIntegrable (pressureOf P D β) volume := by
  have hd : Measurable (fun y : Space => decayFactor P y) := by
    unfold decayFactor chartS chartT
    fun_prop
  have hm : Measurable (pressureOf P D β) := by
    unfold pressureOf
    refine Complex.measurable_re.comp (Finset.measurable_sum _ fun n _ => ?_)
    exact (((Complex.measurable_ofReal.comp hd).mul (modePhase_meas P n β)).mul (shape_meas P _ _ _ _)).add
      (((Complex.measurable_ofReal.comp (hd.pow_const 2)).mul (modePhase_meas P n β)).mul (shape_meas P _ _ _ _))
  have hd2 : IsBdd (fun y => ((decayFactor P y ^ 2 : ℝ) : ℂ)) := by
    refine ⟨1, fun y => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (decay_abs P hP y)
  have hb : IsBdd (fun y => ∑ n ∈ D.modes,
      (((decayFactor P y : ℝ) : ℂ) * modePhase P n β y * pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y
        + ((decayFactor P y ^ 2 : ℝ) : ℂ) * modePhase P n β y *
          pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)) :=
    IsBdd.sum _ _ fun n _ => ((((bdd_decay P hP).mul (bdd_modePhase P n β)).mul (bdd_shape P hP _ _ _ _)).add
      ((hd2.mul (bdd_modePhase P n β)).mul (bdd_shape P hP _ _ _ _)))
  obtain ⟨C, hC⟩ := bdd_re hb
  exact (memLp_top_of_bound hm.aestronglyMeasurable C
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hC y)).locallyIntegrable le_top

theorem single_smul (i : Fin 3) (c : ℝ) :
    EuclideanSpace.single i c = c • EuclideanSpace.single i (1 : ℝ) := by
  ext j
  by_cases h : j = i <;> simp [h]

theorem ring_hasDerivAt (ρ z θ : ℝ) :
    HasDerivAt (fun φ => Reduction.ringPoint ρ φ z) (axialTurn (Reduction.ringPoint ρ θ z)) θ := by
  have e : (fun φ => Reduction.ringPoint ρ φ z) = fun φ =>
      (ρ * Real.cos φ) • EuclideanSpace.single (0 : Fin 3) (1 : ℝ) +
        (ρ * Real.sin φ) • EuclideanSpace.single (1 : Fin 3) (1 : ℝ) + z • EuclideanSpace.single (2 : Fin 3) (1 : ℝ) := by
    funext φ
    simp only [Reduction.ringPoint]
    rw [single_smul 0, single_smul 1, single_smul 2]
  rw [e]
  have h := ((((Real.hasDerivAt_cos θ).const_mul ρ).smul_const (EuclideanSpace.single (0 : Fin 3) (1 : ℝ))).add
    (((Real.hasDerivAt_sin θ).const_mul ρ).smul_const (EuclideanSpace.single (1 : Fin 3) (1 : ℝ)))).add_const
      (z • EuclideanSpace.single (2 : Fin 3) (1 : ℝ))
  refine h.congr_deriv ?_
  ext j
  fin_cases j <;> simp [axialTurn, Reduction.ringPoint]

def horCLM : Space →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (EuclideanSpace.proj (0 : Fin 3)) +
    Complex.I • Complex.ofRealCLM.comp (EuclideanSpace.proj (1 : Fin 3))

def vertCLM : Space →L[ℝ] ℂ := Complex.ofRealCLM.comp (EuclideanSpace.proj (2 : Fin 3))

theorem horCLM_apply (v : Space) : horCLM v = (v 0 : ℂ) + Complex.I * (v 1 : ℂ) := by
  simp [horCLM]

theorem vertCLM_apply (v : Space) : vertCLM v = (v 2 : ℂ) := by
  simp [vertCLM]

theorem trigSeries_hasDerivAt (S : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) :
    HasDerivAt (fun φ : ℝ => ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (φ : ℂ) * Complex.I))
      (∑ n ∈ S, a n * ((n : ℂ) * Complex.I) * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) θ := by
  have h : ∀ n ∈ S, HasDerivAt (fun φ : ℝ => a n * Complex.exp ((n : ℂ) * (φ : ℂ) * Complex.I))
      (a n * ((n : ℂ) * Complex.I) * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) θ := by
    intro n _
    have h1 : HasDerivAt (fun φ : ℝ => (n : ℂ) * (φ : ℂ) * Complex.I) ((n : ℂ) * 1 * Complex.I) θ :=
      (((hasDerivAt_id θ).ofReal_comp).const_mul (n : ℂ)).mul_const Complex.I
    have h2 := h1.cexp.const_mul (a n)
    exact h2.congr_deriv (by ring)
  exact HasDerivAt.fun_sum h

theorem trig_turnDeriv {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) (hd : Differentiable ℝ F) :
    IsRingTrigSum S (fun y => fderiv ℝ F y (axialTurn y)) := by
  intro ρ z
  obtain ⟨a, b, h⟩ := hF ρ z
  refine ⟨fun n => a n * ((n : ℂ) * Complex.I), fun n => b n * ((n : ℂ) * Complex.I), fun θ => ⟨?_, ?_⟩⟩
  · have hG : HasDerivAt (fun φ => F (Reduction.ringPoint ρ φ z))
        (fderiv ℝ F (Reduction.ringPoint ρ θ z) (axialTurn (Reduction.ringPoint ρ θ z))) θ :=
      (hd _).hasFDerivAt.comp_hasDerivAt θ (ring_hasDerivAt ρ z θ)
    have hL := horCLM.hasFDerivAt.comp_hasDerivAt θ hG
    have e : (horCLM ∘ fun φ => F (Reduction.ringPoint ρ φ z)) =
        fun φ : ℝ => ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (φ : ℂ) * Complex.I) := by
      funext φ
      rw [← (h φ).1]
      simp only [Function.comp_apply, horCLM_apply, Reduction.horizontalPart]
    rw [e] at hL
    have hu := hL.unique (trigSeries_hasDerivAt S a θ)
    rw [horCLM_apply] at hu
    simp only [Reduction.horizontalPart]
    exact hu
  · have hG : HasDerivAt (fun φ => F (Reduction.ringPoint ρ φ z))
        (fderiv ℝ F (Reduction.ringPoint ρ θ z) (axialTurn (Reduction.ringPoint ρ θ z))) θ :=
      (hd _).hasFDerivAt.comp_hasDerivAt θ (ring_hasDerivAt ρ z θ)
    have hL := vertCLM.hasFDerivAt.comp_hasDerivAt θ hG
    have e : (vertCLM ∘ fun φ => F (Reduction.ringPoint ρ φ z)) =
        fun φ : ℝ => ∑ n ∈ S, b n * Complex.exp ((n : ℂ) * (φ : ℂ) * Complex.I) := by
      funext φ
      rw [← (h φ).2]
      simp only [Function.comp_apply, vertCLM_apply, Reduction.verticalPart]
    rw [e] at hL
    have hu := hL.unique (trigSeries_hasDerivAt S b θ)
    rw [vertCLM_apply] at hu
    simp only [Reduction.verticalPart]
    exact hu

theorem trig_fsum {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (c : ι → ℝ)
    (hf : ∀ i, ∃ S : Finset ℤ, IsRingTrigSum S (f i)) :
    ∃ S : Finset ℤ, IsRingTrigSum S (fun y => ∑ i ∈ s, c i • f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, by simpa using IsRingTrigSum.zero⟩
  | insert i s hi ih =>
    obtain ⟨S, hS⟩ := ih
    obtain ⟨T, hT⟩ := hf i
    refine ⟨T ∪ S, ?_⟩
    have h := ((hT.smul (c i)).mono Finset.subset_union_left).add (hS.mono Finset.subset_union_right)
    simpa only [Finset.sum_insert hi] using h

theorem span_limit (S : Finset ℤ) (g : ℝ → ℝ → ℂ)
    (hg : ∀ s, ∃ a : ℤ → ℂ, ∀ θ, g s θ = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I))
    (q : ℝ → ℂ) (hq : ∀ θ, HasDerivAt (fun s => g s θ) (q θ) 1) :
    ∃ a : ℤ → ℂ, ∀ θ, q θ = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := by
  classical
  set v : S → (ℝ → ℂ) := fun n θ => Complex.exp (((n : ℤ) : ℂ) * (θ : ℂ) * Complex.I) with hv
  set V : Submodule ℂ (ℝ → ℂ) := Submodule.span ℂ (Set.range v) with hV
  have : FiniteDimensional ℂ V := FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  have hcl : IsClosed (V : Set (ℝ → ℂ)) := Submodule.closed_of_finiteDimensional V
  have mem : ∀ s, g s ∈ V := by
    intro s
    obtain ⟨a, ha⟩ := hg s
    have e : g s = ∑ n : S, a n • v n := by
      funext θ
      rw [ha θ, Finset.sum_apply, ← Finset.sum_coe_sort S]
      rfl
    rw [e]
    exact Submodule.sum_mem _ fun n _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  have hslope : ∀ s, (fun θ => slope (fun s => g s θ) 1 s) ∈ V := by
    intro s
    have e : (fun θ => slope (fun s => g s θ) 1 s) = ((s - 1)⁻¹ : ℂ) • (g s - g 1) := by
      funext θ
      simp [slope_def_module, Complex.real_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (mem s) (mem 1))
  have htend : Filter.Tendsto (fun s => fun θ => slope (fun s => g s θ) 1 s) (nhdsWithin 1 {1}ᶜ) (nhds q) :=
    tendsto_pi_nhds.2 fun θ => (hasDerivAt_iff_tendsto_slope.1 (hq θ))
  have hqV : q ∈ V := hcl.mem_of_tendsto htend (Filter.Eventually.of_forall hslope)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hqV
  refine ⟨fun n => if h : n ∈ S then c ⟨n, h⟩ else 0, fun θ => ?_⟩
  rw [← hc, Finset.sum_apply, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [hv]

theorem ring_smul (ρ θ z s : ℝ) : Reduction.ringPoint (s * ρ) θ (s * z) = s • Reduction.ringPoint ρ θ z := by
  ext j
  fin_cases j <;> simp [Reduction.ringPoint] <;> ring

theorem trig_selfDeriv {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) (hd : Differentiable ℝ F) :
    IsRingTrigSum S (fun y => fderiv ℝ F y y) := by
  intro ρ z
  have hpath : ∀ θ, HasDerivAt (fun s : ℝ => F (Reduction.ringPoint (s * ρ) θ (s * z)))
      (fderiv ℝ F (Reduction.ringPoint ρ θ z) (Reduction.ringPoint ρ θ z)) 1 := by
    intro θ
    have h1 : HasDerivAt (fun s : ℝ => s • Reduction.ringPoint ρ θ z) ((1 : ℝ) • Reduction.ringPoint ρ θ z) 1 :=
      (hasDerivAt_id (1 : ℝ)).smul_const _
    rw [one_smul] at h1
    have h2 : HasFDerivAt F (fderiv ℝ F (Reduction.ringPoint ρ θ z)) ((1 : ℝ) • Reduction.ringPoint ρ θ z) := by
      rw [one_smul]
      exact (hd _).hasFDerivAt
    have h3 := h2.comp_hasDerivAt (x := (1 : ℝ)) h1
    simp only [Function.comp_def] at h3
    simp only [ring_smul]
    exact h3
  obtain ⟨a, ha⟩ := span_limit S (fun s θ => Reduction.horizontalPart F (Reduction.ringPoint (s * ρ) θ (s * z)))
    (fun s => by
      obtain ⟨a, b, h⟩ := hF (s * ρ) (s * z)
      exact ⟨a, fun θ => (h θ).1⟩)
    (fun θ => horCLM (fderiv ℝ F (Reduction.ringPoint ρ θ z) (Reduction.ringPoint ρ θ z)))
    (fun θ => by
      have := horCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath θ)
      simp only [Function.comp_def, horCLM_apply] at this
      simp only [horCLM_apply, Reduction.horizontalPart]
      exact this)
  obtain ⟨b, hb⟩ := span_limit S (fun s θ => Reduction.verticalPart F (Reduction.ringPoint (s * ρ) θ (s * z)))
    (fun s => by
      obtain ⟨a, b, h⟩ := hF (s * ρ) (s * z)
      exact ⟨b, fun θ => (h θ).2⟩)
    (fun θ => vertCLM (fderiv ℝ F (Reduction.ringPoint ρ θ z) (Reduction.ringPoint ρ θ z)))
    (fun θ => by
      have := vertCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath θ)
      simp only [Function.comp_def, vertCLM_apply] at this
      simp only [vertCLM_apply, Reduction.verticalPart]
      exact this)
  refine ⟨a, b, fun θ => ⟨?_, ?_⟩⟩
  · rw [← ha θ, horCLM_apply]
    rfl
  · rw [← hb θ, vertCLM_apply]
    rfl


theorem polyOff_congr {S : Finset ℤ} {u v : Space → ℂ} (hu : IsPolyOff S u)
    (h : ∀ ρ θ z : ℝ, ρ ≠ 0 → v (Reduction.ringPoint ρ θ z) = u (Reduction.ringPoint ρ θ z)) : IsPolyOff S v := by
  intro ρ z hρ
  obtain ⟨a, ha⟩ := hu ρ z hρ
  exact ⟨a, fun θ => (h ρ θ z hρ).trans (ha θ)⟩

theorem polyOff_hor {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) :
    IsPolyOff S (Reduction.horizontalPart F) := by
  intro ρ z _
  obtain ⟨a, b, h⟩ := hF ρ z
  exact ⟨a, fun θ => (h θ).1⟩

theorem polyOff_vert {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) :
    IsPolyOff S (Reduction.verticalPart F) := by
  intro ρ z _
  obtain ⟨a, b, h⟩ := hF ρ z
  exact ⟨b, fun θ => (h θ).2⟩

def IsCompPoly (u : Space → ℝ) : Prop := ∃ T, IsPolyOff T (fun y => ((u y : ℝ) : ℂ))

theorem IsCompPoly.add {u v : Space → ℝ} (hu : IsCompPoly u) (hv : IsCompPoly v) : IsCompPoly (fun y => u y + v y) := by
  have e : (fun y => (((u y + v y : ℝ)) : ℂ)) = fun y => ((u y : ℝ) : ℂ) + ((v y : ℝ) : ℂ) := by
    funext y; push_cast; ring
  unfold IsCompPoly; rw [e]; exact ex_add hu hv

theorem IsCompPoly.mul {u v : Space → ℝ} (hu : IsCompPoly u) (hv : IsCompPoly v) : IsCompPoly (fun y => u y * v y) := by
  have e : (fun y => (((u y * v y : ℝ)) : ℂ)) = fun y => ((u y : ℝ) : ℂ) * ((v y : ℝ) : ℂ) := by
    funext y; push_cast; ring
  unfold IsCompPoly; rw [e]; exact ex_mul hu hv

theorem IsCompPoly.const (c : ℝ) : IsCompPoly (fun _ => c) := ex_const _

theorem IsCompPoly.sub {u v : Space → ℝ} (hu : IsCompPoly u) (hv : IsCompPoly v) : IsCompPoly (fun y => u y - v y) := by
  have h := hu.add ((IsCompPoly.const (-1)).mul hv)
  have e : (fun y => u y - v y) = fun y => u y + -1 * v y := by funext y; ring
  rw [e]; exact h

theorem IsCompPoly.sum {ι : Type*} (s : Finset ι) (f : ι → Space → ℝ) (hf : ∀ i ∈ s, IsCompPoly (f i)) :
    IsCompPoly (fun y => ∑ i ∈ s, f i y) := by
  have e : (fun y => ((∑ i ∈ s, f i y : ℝ) : ℂ)) = fun y => ∑ i ∈ s, ((f i y : ℝ) : ℂ) := by
    funext y; push_cast; rfl
  unfold IsCompPoly; rw [e]; exact ex_sum s _ hf

theorem ex_comp {F : Space → Space} (hF : ∃ S, IsRingTrigSum S F) (i : Fin 3) : IsCompPoly (fun y => F y i) := by
  obtain ⟨S, hS⟩ := hF
  fin_cases i
  · have e : (fun y => ((F y 0 : ℝ) : ℂ)) = fun y => (((Reduction.horizontalPart F y).re : ℝ) : ℂ) := by
      funext y; simp [Reduction.horizontalPart]
    show ∃ T, IsPolyOff T (fun y => ((F y 0 : ℝ) : ℂ))
    rw [e]; exact ⟨_, (polyOff_hor hS).ofReal_re⟩
  · have e : (fun y => ((F y 1 : ℝ) : ℂ)) = fun y => (((Reduction.horizontalPart F y).im : ℝ) : ℂ) := by
      funext y; simp [Reduction.horizontalPart]
    show ∃ T, IsPolyOff T (fun y => ((F y 1 : ℝ) : ℂ))
    rw [e]; exact ⟨_, (polyOff_hor hS).ofReal_im⟩
  · exact ⟨_, polyOff_vert hS⟩

theorem trig_heightDeriv {S : Finset ℤ} {F : Space → Space} (hF : IsRingTrigSum S F) (hd : Differentiable ℝ F) :
    IsRingTrigSum S (fun y => fderiv ℝ F y (unitVector 2)) := by
  intro ρ z
  have hcurve : ∀ θ, HasDerivAt (fun s : ℝ => Reduction.ringPoint ρ θ (z + (s - 1))) (unitVector 2) 1 := by
    intro θ
    have e : (fun s : ℝ => Reduction.ringPoint ρ θ (z + (s - 1))) =
        fun s => Reduction.ringPoint ρ θ z + (s - 1) • unitVector 2 := by
      funext s; ext j; fin_cases j <;> simp [Reduction.ringPoint, unitVector]
    rw [e]
    have h1 : HasDerivAt (fun s : ℝ => (s - 1) • unitVector 2) ((1 : ℝ) • unitVector 2) 1 :=
      ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const _
    rw [one_smul] at h1
    exact h1.const_add _
  have hpath : ∀ θ, HasDerivAt (fun s : ℝ => F (Reduction.ringPoint ρ θ (z + (s - 1))))
      (fderiv ℝ F (Reduction.ringPoint ρ θ z) (unitVector 2)) 1 := by
    intro θ
    have h2 : HasFDerivAt F (fderiv ℝ F (Reduction.ringPoint ρ θ z)) (Reduction.ringPoint ρ θ (z + ((1 : ℝ) - 1))) := by
      rw [sub_self, add_zero]; exact (hd _).hasFDerivAt
    have h3 := h2.comp_hasDerivAt (x := (1 : ℝ)) (hcurve θ)
    simp only [Function.comp_def] at h3
    exact h3
  obtain ⟨a, ha⟩ := span_limit S (fun s θ => Reduction.horizontalPart F (Reduction.ringPoint ρ θ (z + (s - 1))))
    (fun s => by
      obtain ⟨a, b, h⟩ := hF ρ (z + (s - 1))
      exact ⟨a, fun θ => (h θ).1⟩)
    (fun θ => horCLM (fderiv ℝ F (Reduction.ringPoint ρ θ z) (unitVector 2)))
    (fun θ => by
      have := horCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath θ)
      simp only [Function.comp_def, horCLM_apply] at this
      simp only [horCLM_apply, Reduction.horizontalPart]
      exact this)
  obtain ⟨b, hb⟩ := span_limit S (fun s θ => Reduction.verticalPart F (Reduction.ringPoint ρ θ (z + (s - 1))))
    (fun s => by
      obtain ⟨a, b, h⟩ := hF ρ (z + (s - 1))
      exact ⟨b, fun θ => (h θ).2⟩)
    (fun θ => vertCLM (fderiv ℝ F (Reduction.ringPoint ρ θ z) (unitVector 2)))
    (fun θ => by
      have := vertCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath θ)
      simp only [Function.comp_def, vertCLM_apply] at this
      simp only [vertCLM_apply, Reduction.verticalPart]
      exact this)
  refine ⟨a, b, fun θ => ⟨?_, ?_⟩⟩
  · rw [← ha θ, horCLM_apply]
    rfl
  · rw [← hb θ, vertCLM_apply]
    rfl

theorem nsq (y : Space) : ‖y‖ ^ 2 - y 2 ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), Fin.sum_univ_three]
  simp only [Real.norm_eq_abs, sq_abs]
  ring

theorem grad_zero (L : Space →L[ℝ] Space) (y : Space) (hq : y 0 ^ 2 + y 1 ^ 2 ≠ 0) (i : Fin 3) :
    L (unitVector 0) i = (1 / (‖y‖ ^ 2 - y 2 ^ 2)) *
      (y 0 * (L y i + -1 * (y 2 * L (unitVector 2) i)) + -1 * (y 1 * L (axialTurn y) i)) := by
  have hv : y 0 • (y - y 2 • unitVector 2) - y 1 • axialTurn y = (y 0 ^ 2 + y 1 ^ 2) • unitVector 0 := by
    ext j; fin_cases j <;> simp [axialTurn, unitVector] <;> ring
  have h1 := congrArg (fun v => L v i) hv
  simp only [map_sub, map_smul, PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] at h1
  rw [nsq, one_div, eq_inv_mul_iff_mul_eq₀ hq]
  linear_combination -h1

theorem grad_one (L : Space →L[ℝ] Space) (y : Space) (hq : y 0 ^ 2 + y 1 ^ 2 ≠ 0) (i : Fin 3) :
    L (unitVector 1) i = (1 / (‖y‖ ^ 2 - y 2 ^ 2)) *
      (y 1 * (L y i + -1 * (y 2 * L (unitVector 2) i)) + y 0 * L (axialTurn y) i) := by
  have hv : y 1 • (y - y 2 • unitVector 2) + y 0 • axialTurn y = (y 0 ^ 2 + y 1 ^ 2) • unitVector 1 := by
    ext j; fin_cases j <;> simp [axialTurn, unitVector] <;> ring
  have h1 := congrArg (fun v => L v i) hv
  simp only [map_sub, map_add, map_smul, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at h1
  rw [nsq, one_div, eq_inv_mul_iff_mul_eq₀ hq]
  linear_combination -h1

theorem ring_q {ρ : ℝ} (hρ : ρ ≠ 0) (θ z : ℝ) :
    (Reduction.ringPoint ρ θ z) 0 ^ 2 + (Reduction.ringPoint ρ θ z) 1 ^ 2 ≠ 0 := by
  rw [ring_zero, ring_one]
  have h := Real.cos_sq_add_sin_sq θ
  have e : (ρ * Real.cos θ) ^ 2 + (ρ * Real.sin θ) ^ 2 = ρ ^ 2 := by linear_combination ρ ^ 2 * h
  rw [e]; exact pow_ne_zero 2 hρ

theorem ex_grad {F : Space → Space} (hF : ∃ S, IsRingTrigSum S F) (hd : Differentiable ℝ F) (j i : Fin 3) :
    IsCompPoly (fun y => fderiv ℝ F y (unitVector j) i) := by
  obtain ⟨S, hS⟩ := hF
  have hy := ex_comp ⟨S, trig_selfDeriv hS hd⟩ i
  have hz := ex_comp ⟨S, trig_heightDeriv hS hd⟩ i
  have ht := ex_comp ⟨S, trig_turnDeriv hS hd⟩ i
  have hinv : IsCompPoly (fun y => 1 / (‖y‖ ^ 2 - y 2 ^ 2)) := ex_normInv (fun r h => ((1 / (r ^ 2 - h ^ 2) : ℝ) : ℂ))
  have hc : ∀ l : Fin 3, IsCompPoly (fun y => y l) := ex_coord
  fin_cases j
  · obtain ⟨T, hT⟩ := hinv.mul (((hc 0).mul (hy.add ((IsCompPoly.const (-1)).mul ((hc 2).mul hz)))).add
      ((IsCompPoly.const (-1)).mul ((hc 1).mul ht)))
    refine ⟨T, polyOff_congr hT fun ρ θ z hρ => ?_⟩
    show (((fderiv ℝ F _ (unitVector 0) i : ℝ)) : ℂ) = _
    rw [grad_zero _ _ (ring_q hρ θ z) i]
  · obtain ⟨T, hT⟩ := hinv.mul (((hc 1).mul (hy.add ((IsCompPoly.const (-1)).mul ((hc 2).mul hz)))).add
      ((hc 0).mul ht))
    refine ⟨T, polyOff_congr hT fun ρ θ z hρ => ?_⟩
    show (((fderiv ℝ F _ (unitVector 1) i : ℝ)) : ℂ) = _
    rw [grad_one _ _ (ring_q hρ θ z) i]
  · exact hz

theorem curl_apply (M : Space →L[ℝ] Space) (i : Fin 3) :
    curlOf M i = ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * M (unitVector j) l := by
  fin_cases i <;> simp [curlOf, entry, unitVector, Fin.sum_univ_three]

theorem adjoint_apply (M : Space →L[ℝ] Space) (v : Space) (i : Fin 3) :
    ContinuousLinearMap.adjoint M v i = ∑ m : Fin 3, v m * M (unitVector i) m := by
  have h : ContinuousLinearMap.adjoint M v i = inner ℝ (ContinuousLinearMap.adjoint M v) (unitVector i) := by
    simp [unitVector, EuclideanSpace.inner_single_right]
  rw [h, ContinuousLinearMap.adjoint_inner_left]
  simp [PiLp.inner_apply, Fin.sum_univ_three]
  ring

theorem compPoly_cross {a b : Space → Space} (ha : ∀ i, IsCompPoly (fun y => a y i)) (hb : ∀ i, IsCompPoly (fun y => b y i)) (i : Fin 3) :
    IsCompPoly (fun y => crossVec (a y) (b y) i) := by
  fin_cases i
  · have e : (fun y => crossVec (a y) (b y) 0) = fun y => a y 1 * b y 2 - a y 2 * b y 1 := by
      funext y; simp [crossVec]
    show IsCompPoly (fun y => crossVec (a y) (b y) 0)
    rw [e]; exact ((ha 1).mul (hb 2)).sub ((ha 2).mul (hb 1))
  · have e : (fun y => crossVec (a y) (b y) 1) = fun y => a y 2 * b y 0 - a y 0 * b y 2 := by
      funext y; simp [crossVec]
    show IsCompPoly (fun y => crossVec (a y) (b y) 1)
    rw [e]; exact ((ha 2).mul (hb 0)).sub ((ha 0).mul (hb 2))
  · have e : (fun y => crossVec (a y) (b y) 2) = fun y => a y 0 * b y 1 - a y 1 * b y 0 := by
      funext y; simp [crossVec]
    show IsCompPoly (fun y => crossVec (a y) (b y) 2)
    rw [e]; exact ((ha 0).mul (hb 1)).sub ((ha 1).mul (hb 0))

theorem trig_convection {W ζ : Space → Space} (hW : ∃ S, IsRingTrigSum S W) (hWd : Differentiable ℝ W)
    (hζ : ∃ S, IsRingTrigSum S ζ) (hζd : Differentiable ℝ ζ) :
    ∃ S, IsRingTrigSum S (fun y => Reduction.convectionAdjointField W (fun z => fderiv ℝ W z) ζ
      (fun z => fderiv ℝ ζ z) y) := by
  have hcurl : ∀ i, IsCompPoly (fun y => curlOf (fderiv ℝ ζ y) i) := by
    intro i
    have e : (fun y => curlOf (fderiv ℝ ζ y) i) =
        fun y => ∑ j : Fin 3, ∑ l : Fin 3, permSign i j l * fderiv ℝ ζ y (unitVector j) l := by
      funext y; exact curl_apply _ i
    rw [e]
    exact IsCompPoly.sum _ _ fun j _ => IsCompPoly.sum _ _ fun l _ => (IsCompPoly.const _).mul (ex_grad hζ hζd j l)
  have hadj : ∀ i, IsCompPoly (fun y => ContinuousLinearMap.adjoint (fderiv ℝ W y) (ζ y) i) := by
    intro i
    have e : (fun y => ContinuousLinearMap.adjoint (fderiv ℝ W y) (ζ y) i) =
        fun y => ∑ m : Fin 3, ζ y m * fderiv ℝ W y (unitVector i) m := by
      funext y; exact adjoint_apply _ _ i
    rw [e]
    exact IsCompPoly.sum _ _ fun m _ => (ex_comp hζ m).mul (ex_grad hW hWd i m)
  have hcomp : ∀ i, IsCompPoly (fun y => Reduction.convectionAdjointField W (fun z => fderiv ℝ W z) ζ
      (fun z => fderiv ℝ ζ z) y i) := by
    intro i
    have e : (fun y => Reduction.convectionAdjointField W (fun z => fderiv ℝ W z) ζ (fun z => fderiv ℝ ζ z) y i) =
        fun y => -1 * crossVec (curlOf (fderiv ℝ ζ y)) (W y) i + 2 * ContinuousLinearMap.adjoint (fderiv ℝ W y) (ζ y) i := by
      funext y; simp [Reduction.convectionAdjointField]
    rw [e]
    exact ((IsCompPoly.const _).mul (compPoly_cross hcurl (ex_comp hW) i)).add ((IsCompPoly.const _).mul (hadj i))
  have hh : ∃ S, IsPolyOff S (Reduction.horizontalPart (fun y => Reduction.convectionAdjointField W
      (fun z => fderiv ℝ W z) ζ (fun z => fderiv ℝ ζ z) y)) :=
    ex_add (hcomp 0) (ex_mul (ex_const _) (hcomp 1))
  obtain ⟨S, hS⟩ := hh
  obtain ⟨T, hT⟩ := hcomp 2
  exact ⟨_, trig_of_polyOff hS hT⟩


theorem polyOff_biUnion {ι : Type*} (s : Finset ι) (T : ι → Finset ℤ) (f : ι → Space → ℂ)
    (hf : ∀ i ∈ s, IsPolyOff (T i) (f i)) : IsPolyOff (s.biUnion T) (fun y => ∑ i ∈ s, f i y) := by
  classical
  intro ρ z hρ
  have h : ∀ i ∈ s, ∃ a : ℤ → ℂ, ∀ θ : ℝ, f i (Reduction.ringPoint ρ θ z) =
      ∑ n ∈ s.biUnion T, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I) := fun i hi =>
    ((hf i hi).mono (Finset.subset_biUnion_of_mem T hi)) ρ z hρ
  choose! a ha using h
  refine ⟨fun n => ∑ i ∈ s, a i n, fun θ => ?_⟩
  show (∑ i ∈ s, f i (Reduction.ringPoint ρ θ z)) = ∑ n ∈ s.biUnion T, (∑ i ∈ s, a i n) * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)
  rw [Finset.sum_congr rfl fun i hi => ha i hi θ, Finset.sum_comm]
  exact Finset.sum_congr rfl fun n _ => by rw [Finset.sum_mul]

theorem of_normInv (f : ℝ → ℝ → ℂ) : IsPolyOff {0} (fun y => f ‖y‖ (y 2)) :=
  IsPolyOff.of_inv (fun ρ θ z => by simp only [ring_norm, ring_two])

theorem modePhase_poly (P : ChartParams) (n : ℤ) (β : ℝ) :
    IsPolyOff (({(n * P.m : ℤ)} + {(0 : ℤ)} : Finset ℤ)) (modePhase P n β) := by
  have e : modePhase P n β = fun y => Complex.exp (Complex.I * (((n * P.m : ℤ) : ℝ) * angleOf y : ℝ)) *
      Complex.exp (Complex.I * ((n : ℝ) * β * logPhase P y : ℝ)) := by
    funext y
    unfold modePhase
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  rw [e]
  exact (IsPolyOff.angle _).mul (of_normInv (fun r _ => Complex.exp (Complex.I *
    ((n : ℝ) * β * ((1 / 2) * Real.log (1 + r ^ 2 / P.rc ^ 2)) : ℝ))))

theorem fieldComp_unif (P : ChartParams) (D : FieldData) (i : Fin 3) :
    ∃ T, ∀ β : ℝ, IsPolyOff T (fun y => (decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * radialVec y i +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * polarVecQ y i +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * azimVecQ y i)) := by
  obtain ⟨Dc, hDc⟩ := ex_decay P
  obtain ⟨R, hR⟩ := ex_radial i
  obtain ⟨Q, hQ⟩ := ex_polar i
  obtain ⟨Z, hZ⟩ := ex_azim i
  refine ⟨_, fun β => hDc.mul (polyOff_biUnion D.modes _ _ fun n _ => (modePhase_poly P n β).mul
    ((((of_normInv (fun r h => reducedField P D n β (r / (r + P.L0)) (h / r) 0)).mul hR).add
      ((of_normInv (fun r h => reducedField P D n β (r / (r + P.L0)) (h / r) 1)).mul hQ)).add
      ((of_normInv (fun r h => reducedField P D n β (r / (r + P.L0)) (h / r) 2)).mul hZ)))⟩

theorem ringTrig_fieldOf_unif (P : ChartParams) (D : FieldData) :
    ∃ S : Finset ℤ, ∀ β : ℝ, IsRingTrigSum S (fieldOf P D β) := by
  obtain ⟨T0, h0⟩ := fieldComp_unif P D 0
  obtain ⟨T1, h1⟩ := fieldComp_unif P D 1
  obtain ⟨T2, h2⟩ := fieldComp_unif P D 2
  refine ⟨insert 0 (((T0 ∪ T0.image (fun n => -n)) ∪ ({0} + (T1 ∪ T1.image (fun n => -n)))) ∪
    (T2 ∪ T2.image (fun n => -n))), fun β => trig_of_polyOff ?_ ?_⟩
  · show IsPolyOff _ (fun y => (((fieldOf P D β y) 0 : ℝ) : ℂ) + Complex.I * (((fieldOf P D β y) 1 : ℝ) : ℂ))
    simp only [fieldOf, ofc]
    exact (h0 β).ofReal_re.add ((IsPolyOff.of_inv (h := fun _ => Complex.I) (fun _ _ _ => rfl)).mul (h1 β).ofReal_re)
  · show IsPolyOff _ (fun y => (((fieldOf P D β y) 2 : ℝ) : ℂ))
    simp only [fieldOf, ofc]
    exact (h2 β).ofReal_re

theorem trig_fsum_unif {ι : Type*} (s : Finset ι) (f : ι → Space → Space) (c : ι → ℝ) {T : Finset ℤ}
    (hf : ∀ i ∈ s, IsRingTrigSum T (f i)) : IsRingTrigSum T (fun y => ∑ i ∈ s, c i • f i y) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using IsRingTrigSum.zero.mono (Finset.empty_subset T)
  | insert i s hi ih =>
    have h := ((hf i (Finset.mem_insert_self i s)).smul (c i)).add (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert hi] using h

theorem profile_unif {k : ℕ} (D : ProfileData k) : ∃ S : Finset ℤ, ∀ q, IsRingTrigSum S (D.profile q) := by
  choose S hS using fun μ => ringTrig_fieldOf_unif D.chart (D.part μ)
  exact ⟨D.index.biUnion S, fun q => trig_fsum_unif D.index _ _ fun μ hμ =>
    (hS μ (D.phase q)).mono (Finset.subset_biUnion_of_mem S hμ)⟩

theorem red_affine (P : ChartParams) (D : FieldData) (n : ℤ) (t x : ℝ) (l : Fin 3) (β : ℝ) :
    reducedField P D n β t x l = reducedField P D n 0 t x l + (β : ℂ) * (reducedField P D n 1 t x l - reducedField P D n 0 t x l) := by
  by_cases h : n = 0
  · subst h
    fin_cases l <;> simp [reducedField, twistedScale]
  · fin_cases l <;> simp [reducedField, twistedScale, h] <;> ring

theorem red_diff (P : ChartParams) (D : FieldData) (n : ℤ) (t x : ℝ) (l : Fin 3) :
    Differentiable ℝ (fun β : ℝ => reducedField P D n β t x l) := by
  have e : (fun β : ℝ => reducedField P D n β t x l) = fun β : ℝ => reducedField P D n 0 t x l +
      Complex.ofRealCLM β * (reducedField P D n 1 t x l - reducedField P D n 0 t x l) := by
    funext β; rw [red_affine P D n t x l β]; rfl
  rw [e]
  exact (Complex.ofRealCLM.differentiable.mul_const _).const_add _

theorem modePhase_diff (P : ChartParams) (n : ℤ) (y : Space) : Differentiable ℝ (fun β : ℝ => modePhase P n β y) := by
  have e : (fun β : ℝ => modePhase P n β y) = fun β : ℝ => Complex.exp (Complex.I *
      Complex.ofRealCLM (((n * P.m : ℤ) : ℝ) * angleOf y + n * β * logPhase P y)) := by
    funext β; rfl
  rw [e]
  have h : Differentiable ℝ (fun β : ℝ => ((n * P.m : ℤ) : ℝ) * angleOf y + n * β * logPhase P y) := by fun_prop
  exact ((Complex.ofRealCLM.differentiable.comp h).const_mul Complex.I).cexp

theorem fieldOf_diffBeta (P : ChartParams) (D : FieldData) (y : Space) :
    Differentiable ℝ (fun β : ℝ => fieldOf P D β y) := by
  rw [differentiable_euclidean]
  intro i
  simp only [fieldOf, ofc]
  have h : Differentiable ℝ (fun β : ℝ => (decayFactor P y : ℂ) * ∑ n ∈ D.modes, modePhase P n β y *
      (reducedField P D n β (chartT P y) (heightRatio y) 0 * (radialVec y i : ℂ) +
        reducedField P D n β (chartT P y) (heightRatio y) 1 * (polarVecQ y i : ℂ) +
        reducedField P D n β (chartT P y) (heightRatio y) 2 * (azimVecQ y i : ℂ))) :=
    (differentiable_const _).fun_mul (Differentiable.fun_sum fun n _ =>
      (modePhase_diff P n y).fun_mul ((((red_diff P D n _ _ 0).mul_const _).fun_add ((red_diff P D n _ _ 1).mul_const _)).fun_add
        ((red_diff P D n _ _ 2).mul_const _)))
  exact fun β => Complex.reCLM.differentiableAt.comp β (h β)

theorem profile_diffq {k : ℕ} (D : ProfileData k) (y : Space) : Differentiable ℝ (fun q : Fin k → ℝ => D.profile q y) := by
  have hmon : ∀ μ : Fin k → ℕ, Differentiable ℝ (fun q : Fin k → ℝ => ProfileData.monomialOf q μ) := by
    intro μ; unfold ProfileData.monomialOf; fun_prop
  have hph : Differentiable ℝ (fun q : Fin k → ℝ => D.phase q) := by
    unfold ProfileData.phase ProfileData.rate; fun_prop
  exact Differentiable.fun_sum fun μ _ => (hmon μ).fun_smul (fun q => (fieldOf_diffBeta D.chart (D.part μ) y (D.phase q)).comp q (hph q))

theorem tangent_ringTrig {k : ℕ} (D : ProfileData k) (i : Fin k) : ∃ S : Finset ℤ, IsRingTrigSum S (D.tangentField i) := by
  obtain ⟨S, hS⟩ := profile_unif D
  refine ⟨S, fun ρ z => ?_⟩
  set c : ℝ → (Fin k → ℝ) := fun s => (s - 1) • (Pi.single i (1 : ℝ) : Fin k → ℝ) with hc
  have hcurve : HasDerivAt c ((Pi.single i (1 : ℝ) : Fin k → ℝ)) 1 := by
    have h1 := ((hasDerivAt_id (1 : ℝ)).sub_const 1).smul_const ((Pi.single i (1 : ℝ) : Fin k → ℝ))
    rw [one_smul] at h1
    exact h1
  have hc1 : c 1 = 0 := by simp [hc]
  have hpath : ∀ y, HasDerivAt (fun s => D.profile (c s) y) (D.tangentField i y) 1 := by
    intro y
    have h2 : HasFDerivAt (fun q => D.profile q y) (fderiv ℝ (fun q => D.profile q y) 0) (c 1) := by
      rw [hc1]; exact (profile_diffq D y).differentiableAt.hasFDerivAt
    exact h2.comp_hasDerivAt (x := (1 : ℝ)) hcurve
  obtain ⟨a, ha⟩ := span_limit S (fun s θ => Reduction.horizontalPart (D.profile (c s)) (Reduction.ringPoint ρ θ z))
    (fun s => by
      obtain ⟨a, b, h⟩ := hS (c s) ρ z
      exact ⟨a, fun θ => (h θ).1⟩)
    (fun θ => horCLM (D.tangentField i (Reduction.ringPoint ρ θ z)))
    (fun θ => by
      have := horCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath (Reduction.ringPoint ρ θ z))
      simp only [Function.comp_def, horCLM_apply] at this
      simp only [horCLM_apply, Reduction.horizontalPart]
      exact this)
  obtain ⟨b, hb⟩ := span_limit S (fun s θ => Reduction.verticalPart (D.profile (c s)) (Reduction.ringPoint ρ θ z))
    (fun s => by
      obtain ⟨a, b, h⟩ := hS (c s) ρ z
      exact ⟨b, fun θ => (h θ).2⟩)
    (fun θ => vertCLM (D.tangentField i (Reduction.ringPoint ρ θ z)))
    (fun θ => by
      have := vertCLM.hasFDerivAt.comp_hasDerivAt (1 : ℝ) (hpath (Reduction.ringPoint ρ θ z))
      simp only [Function.comp_def, vertCLM_apply] at this
      simp only [vertCLM_apply, Reduction.verticalPart]
      exact this)
  refine ⟨a, b, fun θ => ⟨?_, ?_⟩⟩
  · rw [← ha θ, horCLM_apply]
    rfl
  · rw [← hb θ, vertCLM_apply]
    rfl

theorem comp_locInt {L : Space → Space} (hL : LocallyIntegrable L volume) (i : Fin 3) :
    LocallyIntegrable (fun y => L y i) volume := by
  have e : (fun y => L y i) = fun y => inner ℝ (L y) (unitVector i) := by
    funext y
    simp [unitVector, EuclideanSpace.inner_single_right]
  rw [e]
  exact locallyIntegrable_iff.2 fun _ hK => (hL.integrableOn_isCompact hK).inner_const _

theorem rep_of_components {L : Space → Space}
    (h : ∀ i : Fin 3, ∃ g : Space → ℝ, (∀ᵐ y ∂volume, g y = L y i) ∧ ∃ S : Finset ℤ, ∀ ρ z : ℝ, ∃ a : ℤ → ℂ,
      ∀ θ : ℝ, ((g (Reduction.ringPoint ρ θ z) : ℝ) : ℂ) = ∑ n ∈ S, a n * Complex.exp ((n : ℂ) * (θ : ℂ) * Complex.I)) :
    HasRingRep L := by
  choose g hg S hS using h
  have hp : ∀ i, IsPolyOff (S i) (fun y => ((g i y : ℝ) : ℂ)) := fun i ρ z _ => hS i ρ z
  refine ⟨insert 0 ((S 0 ∪ ({0} + S 1)) ∪ S 2), fun y => ofComponents (fun i => g i y), ?_,
    trig_of_polyOff ?_ ?_⟩
  · filter_upwards [hg 0, hg 1, hg 2] with y h0 h1 h2
    ext i
    fin_cases i <;> simp [ofc, h0, h1, h2]
  · show IsPolyOff _ (fun y => ((ofComponents (fun i => g i y) 0 : ℝ) : ℂ) +
      Complex.I * ((ofComponents (fun i => g i y) 1 : ℝ) : ℂ))
    simp only [ofc]
    exact (hp 0).add ((IsPolyOff.of_inv (h := fun _ => Complex.I) (fun _ _ _ => rfl)).mul (hp 1))
  · show IsPolyOff _ (fun y => ((ofComponents (fun i => g i y) 2 : ℝ) : ℂ))
    simp only [ofc]
    exact hp 2

end RingModesInternal

open RingModesInternal

theorem ringRep_of_weakNegTrace {S : Finset ℤ} {X : Space → Space} (hX : IsRingTrigSum S X)
    (hXloc : LocallyIntegrable X volume) {L : Space → Space} (hLloc : LocallyIntegrable L volume)
    (hL : Reduction.IsWeakNegTraceOf X L) : HasRingRep L :=
  rep_of_components fun i => ringModes_unique (comp_locInt hLloc i) (negTrace_ringModes hX hXloc hLloc hL i)

theorem ringRep_of_weakScalarGradient {S : Finset ℤ} {q : Space → ℝ} (hq : IsRingScalarTrigSum S q)
    (hqloc : LocallyIntegrable q volume) {Q : Space → Space} (hQloc : LocallyIntegrable Q volume)
    (hQ : Reduction.IsWeakScalarGradientOf q Q) : HasRingRep Q :=
  rep_of_components fun i => ringModes_unique (comp_locInt hQloc i) (scalarGradient_ringModes hq hqloc hQloc hQ i)

theorem ringRep_of_weakMatrixDivergence {S : Finset ℤ} {Y : Space → (Space →L[ℝ] Space)}
    (hY : ∀ i : Fin 3, IsRingTrigSum S (fun y => Y y (unitVector i)))
    (hYloc : LocallyIntegrable Y volume) {L : Space → Space} (hLloc : LocallyIntegrable L volume)
    (hL : Reduction.IsWeakMatrixDivergenceOf Y L) : HasRingRep L :=
  rep_of_components fun i => ringModes_unique (comp_locInt hLloc i) (matrixDivergence_ringModes hY hYloc hLloc hL i)

theorem ringTrig_fieldOf (P : ChartParams) (D : FieldData) (β : ℝ) : ∃ S : Finset ℤ, IsRingTrigSum S (fieldOf P D β) := by
  have hh : ∃ S, IsPolyOff S (Reduction.horizontalPart (fieldOf P D β)) := by
    show ∃ S, IsPolyOff S (fun y => (((fieldOf P D β y) 0 : ℝ) : ℂ) + Complex.I * (((fieldOf P D β y) 1 : ℝ) : ℂ))
    simp only [fieldOf, ofc]
    exact ex_add (ex_re (ex_fieldComp P D β 0)) (ex_mul (ex_const _) (ex_re (ex_fieldComp P D β 1)))
  have hv : ∃ S, IsPolyOff S (Reduction.verticalPart (fieldOf P D β)) := by
    show ∃ S, IsPolyOff S (fun y => (((fieldOf P D β y) 2 : ℝ) : ℂ))
    simp only [fieldOf, ofc]
    exact ex_re (ex_fieldComp P D β 2)
  obtain ⟨S, hS⟩ := hh
  obtain ⟨T, hT⟩ := hv
  exact ⟨_, trig_of_polyOff hS hT⟩

theorem ringTrig_atomOf (P : ChartParams) (X : AtomData) (β : ℝ) : ∃ S : Finset ℤ, IsRingTrigSum S (atomOf P X β) := by
  obtain ⟨S, hS⟩ := ex_hor_atom P X β
  obtain ⟨T, hT⟩ := ex_vert_atom P X β
  exact ⟨_, trig_of_polyOff hS hT⟩

theorem ringTrig_adjointPressureField (P : ChartParams) {k : ℕ} (A : AuxData k) (j : Fin k) (p : Fin k → ℝ) :
    ∃ S : Finset ℤ, IsRingScalarTrigSum S (A.adjointPressureField P j p) := by
  have e : (fun y => ((A.adjointPressureField P j p y : ℝ) : ℂ)) = fun y =>
      ∑ γ ∈ (A.adjointFamily j).indices, ((multiPow γ p : ℝ) : ℂ) *
        ((pressureOf P (A.adjointPressure j γ) (A.phase p) y : ℝ) : ℂ) := by
    funext y
    simp [AuxData.adjointPressureField]
  have h : ∃ S, IsPolyOff S (fun y => ((A.adjointPressureField P j p y : ℝ) : ℂ)) := by
    rw [e]
    have hshape : ∀ (low high ax : ℕ) (Sp : Spline),
        ∃ S, IsPolyOff S (fun y => pressureShape P low high ax Sp y) := fun low high ax Sp =>
      ex_normInv (fun r h => ((((r / (r + P.L0)) ^ low * (1 - r / (r + P.L0)) ^ high * (1 - (h / r) ^ 2) ^ ax : ℝ)) : ℂ) *
        Sp.eval false (r / (r + P.L0)) (h / r))
    have hd2 : ∃ S, IsPolyOff S (fun y => ((decayFactor P y ^ 2 : ℝ) : ℂ)) :=
      ex_normInv (fun r _ => ((((1 - r / (r + P.L0)) ^ (2 * P.eps)) ^ 2 : ℝ) : ℂ))
    refine ex_sum _ _ fun γ _ => ex_mul (ex_const _) (ex_re (ex_sum _ _ fun n _ => ex_add ?_ ?_))
    · exact ex_mul (ex_mul (ex_decay P) (ex_modePhase P n _)) (hshape _ _ _ _)
    · exact ex_mul (ex_mul hd2 (ex_modePhase P n _)) (hshape _ _ _ _)
  obtain ⟨S, hS⟩ := h
  exact ⟨_, scalar_of_polyOff hS⟩

theorem ringTrig_fluxFieldOf_columns (P : ChartParams) {k : ℕ} (A : AuxData k) (j : Fin k) (p : Fin k → ℝ) :
    ∃ S : Finset ℤ, ∀ i : Fin 3, IsRingTrigSum S (fun y => A.fluxFieldOf P j p y (unitVector i)) := by
  have hcol : ∀ i : Fin 3, ∃ S : Finset ℤ, IsRingTrigSum S (fun y => A.fluxFieldOf P j p y (unitVector i)) := by
    intro i
    have eh : Reduction.horizontalPart (fun y => A.fluxFieldOf P j p y (unitVector i)) = fun y =>
        ∑ γ ∈ (A.adjointFamily j).indices, ((multiPow γ p : ℝ) : ℂ) * (((radialVec y i : ℝ) : ℂ) *
          Reduction.horizontalPart (atomOf P (A.fluxData j γ) (A.phase p)) y) := by
      funext y
      simp [Reduction.horizontalPart, AuxData.fluxFieldOf, fluxOf, ofc, Finset.sum_add_distrib, Finset.mul_sum,
        mul_add, EuclideanSpace.inner_single_right, unitVector]
      exact Finset.sum_congr rfl fun x _ => by ring
    have ev : Reduction.verticalPart (fun y => A.fluxFieldOf P j p y (unitVector i)) = fun y =>
        ∑ γ ∈ (A.adjointFamily j).indices, ((multiPow γ p : ℝ) : ℂ) * (((radialVec y i : ℝ) : ℂ) *
          Reduction.verticalPart (atomOf P (A.fluxData j γ) (A.phase p)) y) := by
      funext y
      simp [Reduction.verticalPart, AuxData.fluxFieldOf, fluxOf, ofc, EuclideanSpace.inner_single_right, unitVector]
    have hh : ∃ S, IsPolyOff S (Reduction.horizontalPart (fun y => A.fluxFieldOf P j p y (unitVector i))) := by
      rw [eh]
      exact ex_sum _ _ fun γ _ => ex_mul (ex_const _) (ex_mul (ex_radial i) (ex_hor_atom P _ _))
    have hv : ∃ S, IsPolyOff S (Reduction.verticalPart (fun y => A.fluxFieldOf P j p y (unitVector i))) := by
      rw [ev]
      exact ex_sum _ _ fun γ _ => ex_mul (ex_const _) (ex_mul (ex_radial i) (ex_vert_atom P _ _))
    obtain ⟨S, hS⟩ := hh
    obtain ⟨T, hT⟩ := hv
    exact ⟨_, trig_of_polyOff hS hT⟩
  choose S hS using hcol
  exact ⟨Finset.univ.biUnion S, fun i => (hS i).mono (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))⟩

theorem differentiable_adjointField (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k)
    (hA : IsAuxData P A) (j : Fin k) (p : Fin k → ℝ) : Differentiable ℝ (A.adjointField P j p) := by
  have h : ContDiff ℝ 1 (fun y => ∑ γ ∈ (A.adjointFamily j).indices,
      multiPow γ p • fieldOf P ((A.adjointFamily j).coef γ) (A.phase p) y) :=
    ContDiff.sum fun γ hγ => (AdjointCoreInternal.field_contDiff P hP _ (hA.adjoint_shape j γ hγ) _).const_smul _
  exact h.differentiable one_ne_zero

theorem ringTrig_adjointField (P : ChartParams) {k : ℕ} (A : AuxData k) (j : Fin k) (p : Fin k → ℝ) :
    ∃ S : Finset ℤ, IsRingTrigSum S (A.adjointField P j p) :=
  trig_fsum (A.adjointFamily j).indices (fun γ => fieldOf P ((A.adjointFamily j).coef γ) (A.phase p))
    (fun γ => multiPow γ p) (fun γ => ringTrig_fieldOf P ((A.adjointFamily j).coef γ) (A.phase p))

theorem locInt_adjointField (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) : LocallyIntegrable (A.adjointField P j p) volume := by
  exact (differentiable_adjointField P hP A hA j p).continuous.locallyIntegrable

theorem locInt_atomFamily (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (F : AtomFamily k)
    (phase : (Fin k → ℝ) → ℝ) (p : Fin k → ℝ) :
    LocallyIntegrable (F.eval P phase p) volume := by
  have h : ∀ γ ∈ F.indices, LocallyIntegrable (fun y => multiPow γ p • atomOf P (F.coef γ) (phase p) y) volume :=
    fun γ _ => (atomOf_locInt P hP (F.coef γ) (phase p)).smul (multiPow γ p)
  exact locallyIntegrable_finsetSum F.indices h

theorem locInt_adjointPressureField (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k)
    (j : Fin k) (p : Fin k → ℝ) :
    LocallyIntegrable (A.adjointPressureField P j p) volume := by
  have h : ∀ γ ∈ (A.adjointFamily j).indices, LocallyIntegrable
      (fun y => multiPow γ p * pressureOf P (A.adjointPressure j γ) (A.phase p) y) volume :=
    fun γ _ => (pressureOf_locInt P hP (A.adjointPressure j γ) (A.phase p)).smul (multiPow γ p)
  exact locallyIntegrable_finsetSum _ h

theorem locInt_pinPotentialField (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k)
    (hA : IsAuxData P A) (l : Fin k) : LocallyIntegrable (A.pinPotentialField P l) volume := by
  obtain ⟨e, he⟩ := hA.pin_shape l
  exact (fieldOf_contDiff_of_compact P hP he hA.break_pos A.phaseBase).continuous.locallyIntegrable

theorem locInt_fluxFieldOf (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k)
    (j : Fin k) (p : Fin k → ℝ) : LocallyIntegrable (A.fluxFieldOf P j p) volume := by
  have h : ∀ γ ∈ (A.adjointFamily j).indices, LocallyIntegrable
      (fun y => multiPow γ p • fluxOf P (A.fluxData j γ) (A.phase p) y) volume :=
    fun γ _ => (fluxOf_locInt P hP (A.fluxData j γ) (A.phase p)).smul (multiPow γ p)
  exact locallyIntegrable_finsetSum _ h

theorem ringRep_fderiv_self (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) :
    HasRingRep (fun y => fderiv ℝ (A.adjointField P j p) y y) := by
  obtain ⟨S, hS⟩ := ringTrig_adjointField P A j p
  exact ⟨S, _, Filter.Eventually.of_forall (fun _ => rfl),
    trig_selfDeriv hS (differentiable_adjointField P hP A hA j p)⟩

theorem ringRep_fderiv_turn (P : ChartParams) (hP : IsChartParams P) {k : ℕ} (A : AuxData k) (hA : IsAuxData P A)
    (j : Fin k) (p : Fin k → ℝ) :
    HasRingRep (fun y => fderiv ℝ (A.adjointField P j p) y (axialTurn y)) := by
  obtain ⟨S, hS⟩ := ringTrig_adjointField P A j p
  exact ⟨S, _, Filter.Eventually.of_forall (fun _ => rfl),
    trig_turnDeriv hS (differentiable_adjointField P hP A hA j p)⟩

theorem ringRep_convectionField {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (A : AuxData k)
    (hA : IsAuxData D.chart A) (j : Fin k) (p : Fin k → ℝ) (W : Space → Space)
    (hW : W = D.profile p ∨ ∃ i, W = D.tangentField i) :
    HasRingRep (fun y => Reduction.convectionAdjointField W (fun z => fderiv ℝ W z) (A.adjointField D.chart j p)
      (fun z => fderiv ℝ (A.adjointField D.chart j p) z) y) := by
  have hWt : (∃ S, IsRingTrigSum S W) ∧ Differentiable ℝ W := by
    rcases hW with rfl | ⟨i, rfl⟩
    · refine ⟨trig_fsum D.index (fun μ => fieldOf D.chart (D.part μ) (D.phase p)) (fun μ => ProfileData.monomialOf p μ)
        (fun μ => ringTrig_fieldOf D.chart (D.part μ) (D.phase p)), ?_⟩
      have h : ContDiff ℝ 1 (fun y => ∑ μ ∈ D.index, ProfileData.monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) y) :=
        ContDiff.sum fun μ hμ => (FracInternal.fieldOf_contDiff hD.chart (hD.parts μ hμ) (D.phase p)).const_smul _
      exact h.differentiable one_ne_zero
    · exact ⟨tangent_ringTrig D i, (shift_regular_of D hD i).1.differentiable one_ne_zero⟩
  obtain ⟨S, hS⟩ := trig_convection hWt.1 hWt.2 (ringTrig_adjointField D.chart A j p)
    (differentiable_adjointField D.chart hD.chart A hA j p)
  exact ⟨S, _, Filter.Eventually.of_forall (fun _ => rfl), hS⟩

end GivenFields

end CellCert

end Breakdown

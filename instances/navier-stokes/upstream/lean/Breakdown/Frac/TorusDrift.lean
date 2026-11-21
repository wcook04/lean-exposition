import Breakdown.Frac.StTorusReduce
import Breakdown.Torus.MovingFrame

open Set Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracDrift.Internal

open MovingFrame.Internal

theorem remainder_shift {f : Space → Space} (hf : ContDiff ℝ ∞ f) (a b x z : Space) :
    secondOrderRemainder (fun w => f (w + a) + b) x z = secondOrderRemainder f (x + a) z := by
  simp only [secondOrderRemainder, fderiv_shift, iteratedFDeriv_shift hf, add_right_comm x z a]
  abel

theorem power_shift (α : ℝ) {f : Space → Space} (hf : ContDiff ℝ ∞ f) (a b x : Space) :
    fractionalPowerAt α (fun w => f (w + a) + b) x = fractionalPowerAt α f (x + a) := by
  simp only [fractionalPowerAt, remainder_shift hf]

theorem power_periodic {α : ℝ} {f : Space → Space} (hf : ContDiff ℝ ∞ f) (hp : IsPeriodic f)
    (i : Fin 3) (w : Space) :
    fractionalPowerAt α f (w + unitVector i) = fractionalPowerAt α f w := by
  rw [← power_shift α hf (unitVector i) 0 w]
  congr 1
  funext z
  rw [add_zero, hp i z]

theorem frac_pressure_shift_pos {α : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (hs : IsFractionalSolution α 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    {t : ℝ} (ht : 0 < t) (i : Fin 3) (x : Space) :
    p t (x + unitVector i) - p t x = p t (unitVector i) - p t 0 := by
  have hper : (fun z => u t (z + unitVector i)) = u t := funext (hu t ht.le i)
  have hgrad : ∀ w, gradientAt (p t) w = -(deriv (fun τ => u τ w) t + advectionAt (u t) w +
      (1 : ℝ) • fractionalPowerAt α (u t) w) := fun w => by
    rw [hs.momentum t ht w, neg_neg]
  have hdt : ∀ w, deriv (fun τ => u τ (w + unitVector i)) t = deriv (fun τ => u τ w) t :=
    fun w => Filter.EventuallyEq.deriv_eq
      (Filter.eventually_of_mem (Ioi_mem_nhds ht) fun τ hτ => hu τ (le_of_lt hτ) i w)
  have hfd : ∀ w, fderiv ℝ (u t) (w + unitVector i) = fderiv ℝ (u t) w := fun w => by
    conv_rhs => rw [← hper]
    rw [fderiv_comp_add_right]
  have hA : ∀ w, fractionalPowerAt α (u t) (w + unitVector i) = fractionalPowerAt α (u t) w :=
    power_periodic (slice_contDiff hs.smooth_velocity ht.le) (hu t ht.le) i
  have hg : ∀ w, gradientAt (p t) (w + unitVector i) = gradientAt (p t) w := fun w => by
    rw [hgrad, hgrad (w := w), hA, hdt]
    simp only [advectionAt, hfd, hu t ht.le i w]
  have hd : Differentiable ℝ (p t) :=
    (slice_contDiff hs.smooth_pressure ht.le).differentiable (by simp)
  have hsh : Differentiable ℝ (fun z => p t (z + unitVector i)) :=
    hd.comp (differentiable_id.add_const _)
  have hφd : Differentiable ℝ (fun z => p t (z + unitVector i) - p t z) := hsh.sub hd
  have hφ : ∀ w, fderiv ℝ (fun z => p t (z + unitVector i) - p t z) w = 0 := fun w => by
    rw [fderiv_fun_sub (hsh w) (hd w), fderiv_comp_add_right, sub_eq_zero]
    exact eq_of_apply_unitVector fun j => by rw [← gradientAt_apply, ← gradientAt_apply, hg]
  have := is_const_of_fderiv_eq_zero hφd hφ x 0
  simp only [zero_add] at this
  exact this

theorem frac_pressure_shift {α : ℝ} {u₀ : Space → Space} {u : ℝ → Space → Space}
    {p : ℝ → Space → ℝ} (hs : IsFractionalSolution α 1 u₀ u p) (hu : ∀ t ≥ 0, IsPeriodic (u t))
    {t : ℝ} (ht : 0 ≤ t) (i : Fin 3) (x : Space) :
    p t (x + unitVector i) = p t x + (p t (unitVector i) - p t 0) := by
  rcases ht.lt_or_eq with ht | rfl
  · linarith [frac_pressure_shift_pos hs hu ht i x]
  · have hc := time_contDiffOn hs.smooth_pressure
    have := eq_zero_of_pos
      (ψ := fun τ => p τ (x + unitVector i) - p τ x - (p τ (unitVector i) - p τ 0))
      (((hc _).continuousOn.sub (hc _).continuousOn).sub
        ((hc _).continuousOn.sub (hc _).continuousOn))
      (fun τ hτ => by linarith [frac_pressure_shift_pos hs hu hτ i x])
    linarith

theorem frac_combine {W : Type*} [AddCommGroup W] (D Fv Fg c A G : W) (m : D + Fv + A = -G) :
    D + -Fg + c + (Fv + Fg) + A = -(G - c) := by
  rw [show D + -Fg + c + (Fv + Fg) + A = (D + Fv + A) + c by abel, m]
  abel

end FracDrift.Internal

open MovingFrame.Internal FracDrift.Internal

theorem fracTorusDrift (α : ℝ) : FracTorusDrift α := by
  intro u₀ u p hs hu
  have hcs : ContDiffOn ℝ ∞ (fun t => linearPart p t) (Ici 0) := by
    unfold linearPart
    exact ContDiffOn.sum fun j _ =>
      ((time_contDiffOn hs.smooth_pressure _).sub (time_contDiffOn hs.smooth_pressure _)).smul
        contDiffOn_const
  obtain ⟨g, hg0, hg', hgs⟩ := antideriv hcs
  obtain ⟨h, hh0, hh', hhs⟩ := antideriv (a := fun t => -g t) hgs.neg
  have hfst : MapsTo (Prod.fst : ℝ × Space → ℝ) (Ici 0 ×ˢ univ) (Ici 0) := fun z hz => hz.1
  have hΦ : ContDiffOn ℝ ∞ (fun z : ℝ × Space => (z.1, z.2 + h z.1)) (Ici 0 ×ˢ univ) :=
    contDiffOn_fst.prodMk (contDiffOn_snd.add (hhs.comp contDiffOn_fst hfst))
  have hmaps : MapsTo (fun z : ℝ × Space => (z.1, z.2 + h z.1)) (Ici 0 ×ˢ univ) (Ici 0 ×ˢ univ) :=
    fun z hz => mk_mem_prod hz.1 (mem_univ _)
  refine ⟨fun t x => u t (x + h t) + g t,
    fun t x => p t (x + h t) - inner ℝ (linearPart p t) (x + h t), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · exact (hs.smooth_velocity.comp hΦ hmaps).add (hgs.comp contDiffOn_fst hfst)
  · exact (hs.smooth_pressure.comp hΦ hmaps).sub ((hcs.comp contDiffOn_fst hfst).inner ℝ
      (contDiffOn_snd.add (hhs.comp contDiffOn_fst hfst)))
  · intro x
    simp only [hh0, hg0, add_zero, hs.initial]
  · intro t ht x
    beta_reduce
    have hD : deriv (fun τ => u τ (x + h τ) + g τ) t = deriv (fun τ => u τ (x + h t)) t +
        fderiv ℝ (u t) (x + h t) (-g t) + linearPart p t :=
      ((along_hasDerivAt hs.smooth_velocity ht x (hh' t ht)).add (hg' t ht)).deriv
    have hA : advectionAt (fun z => u t (z + h t) + g t) x =
        fderiv ℝ (u t) (x + h t) (u t (x + h t)) + fderiv ℝ (u t) (x + h t) (g t) := by
      rw [advectionAt, fderiv_shift, map_add]
    have hL : fractionalPowerAt α (fun z => u t (z + h t) + g t) x =
        fractionalPowerAt α (u t) (x + h t) :=
      power_shift α (slice_contDiff hs.smooth_velocity ht.le) (h t) (g t) x
    have hG : gradientAt (fun z => p t (z + h t) - inner ℝ (linearPart p t) (z + h t)) x =
        gradientAt (p t) (x + h t) - linearPart p t := by
      rw [gradient_shift ((slice_contDiff hs.smooth_pressure ht.le).differentiable (by simp)),
        sum_inner_linearPart]
    rw [hD, hA, hL, hG, map_neg]
    exact frac_combine _ _ _ _ _ _ (hs.momentum t ht (x + h t))
  · intro t ht x
    simp only [divergenceAt, fderiv_shift]
    exact hs.incompressible t ht (x + h t)
  · intro t ht i x
    simp only
    rw [add_right_comm x (unitVector i) (h t), hu t ht i]
  · intro t ht i x
    simp only
    rw [add_right_comm x (unitVector i) (h t), frac_pressure_shift hs hu ht i (x + h t),
      inner_add_right, inner_linearPart]
    ring

end Breakdown.Periodic

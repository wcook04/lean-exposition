import TorusEuler.TerminalMaterialDerivative
import TorusEuler.CoframeDerivativeBounds

/-! Mixed coefficient jets with a fixed spatial power per derivative. -/

open Filter Set
open scoped ContDiff

namespace TorusEuler

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The spatial derivative rate has fixed slope `p` in the spatial order.
The factor `A` is independent of that order. -/
def TerminalMixedJetBound (a b : ℝ) (q p : ℕ) (D A : ℝ) (C : ℕ → ℝ)
    (f : ℝ → Vec3 → E) : Prop :=
  ∀ i ≤ q, ∀ n, ∀ t ∈ Icc a b, ∀ x,
    ‖iteratedFDeriv ℝ n (slabTimeJet a b i f t) x‖ ≤ C n * A * D ^ (p * n)

namespace TerminalMixedJetBound

variable {a b D A A' : ℝ} {p p' q q' : ℕ} {C C' : ℕ → ℝ}
  {f : ℝ → Vec3 → E}

theorem mono_order (h : TerminalMixedJetBound a b q p D A C f) (hq : q' ≤ q) :
    TerminalMixedJetBound a b q' p D A C f :=
  fun i hi => h i (hi.trans hq)

theorem mono_amplitude (h : TerminalMixedJetBound a b q p D A C f)
    (hD : 0 ≤ D) (hC : ∀ n, 0 ≤ C n) (hA : A ≤ A') :
    TerminalMixedJetBound a b q p D A' C f := by
  intro i hi n t ht x
  exact (h i hi n t ht x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA (hC n)) (pow_nonneg hD _))

theorem mono_constant (h : TerminalMixedJetBound a b q p D A C f)
    (hD : 0 ≤ D) (hA : 0 ≤ A) (hC : ∀ n, C n ≤ C' n) :
    TerminalMixedJetBound a b q p D A C' f := by
  intro i hi n t ht x
  exact (h i hi n t ht x).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hC n) hA) (pow_nonneg hD _))

theorem mono_slope (h : TerminalMixedJetBound a b q p D A C f)
    (hD : 1 ≤ D) (hA : 0 ≤ A) (hC : ∀ n, 0 ≤ C n) (hp : p ≤ p') :
    TerminalMixedJetBound a b q p' D A C f := by
  intro i hi n t ht x
  exact (h i hi n t ht x).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (Nat.mul_le_mul_right n hp))
      (mul_nonneg (hC n) hA))

theorem congr (h : TerminalMixedJetBound a b q p D A C f) {g : ℝ → Vec3 → E}
    (hEq : ∀ t ∈ Icc a b, ∀ x, f t x = g t x) :
    TerminalMixedJetBound a b q p D A C g := by
  intro i hi n t ht x
  have hfun : slabTimeJet a b i f t = slabTimeJet a b i g t := by
    funext y
    exact iteratedDerivWithin_congr (fun r hr => hEq r hr y) ht
  rw [← hfun]
  exact h i hi n t ht x

theorem of_zero {g : ℝ → Vec3 → E} (h : ∀ n t, t ∈ Icc a b → ∀ x,
    ‖iteratedFDeriv ℝ n (g t) x‖ ≤ C n * A * D ^ (p * n)) :
    TerminalMixedJetBound a b 0 p D A C g := by
  intro i hi n t ht x
  have hi' : i = 0 := by omega
  simpa only [hi', slabTimeJet_zero] using h n t ht x

theorem spaceDerivative (h : TerminalMixedJetBound a b q p D A C f)
    (hab : a < b) (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3))) :
    TerminalMixedJetBound a b q p D (A * D ^ p) (fun n => C (n + 1))
      (fun t x => fderiv ℝ (f t) x) := by
  intro i hi n t ht x
  have hcomm : slabTimeJet a b i (fun r y => fderiv ℝ (f r) y) t =
      fderiv ℝ (slabTimeJet a b i f t) :=
    funext (terminal_iteratedDerivWithin_fderiv_comm hab hf i ht)
  rw [hcomm, norm_iteratedFDeriv_fderiv]
  have heq : p * (n + 1) = p + p * n := by rw [Nat.mul_succ, Nat.add_comm]
  simpa only [heq, pow_add, mul_assoc] using h i hi (n + 1) t ht x

theorem timeDerivative (h : TerminalMixedJetBound a b (q + 1) p D A C f) :
    TerminalMixedJetBound a b q p D A C
      (fun t x => derivWithin (fun r => f r x) (Icc a b) t) := by
  intro i hi n t ht x
  rw [← slabTimeJet_succ' a b i f]
  exact h (i + 1) (Nat.succ_le_succ hi) n t ht x

theorem add {g : ℝ → Vec3 → E} (hf : TerminalMixedJetBound a b q p D A C f)
    (hg : TerminalMixedJetBound a b q p D A C' g)
    (hab : a < b)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (hgreg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc a b ×ˢ (univ : Set Vec3))) :
    TerminalMixedJetBound a b q p D A (fun n => C n + C' n) (fun t x => f t x + g t x) := by
  intro i hi n t ht x
  have htime : slabTimeJet a b i (fun r y => f r y + g r y) t =
      fun y => slabTimeJet a b i f t y + slabTimeJet a b i g t y := by
    funext y
    exact iteratedDerivWithin_fun_add ht (uniqueDiffOn_Icc hab)
      ((terminal_contDiffOn_timeSlice hfreg y).contDiffWithinAt ht |>.of_le (by simp))
      ((terminal_contDiffOn_timeSlice hgreg y).contDiffWithinAt ht |>.of_le (by simp))
  rw [htime, fun_iteratedFDeriv_add_apply]
  · calc
      _ ≤ ‖iteratedFDeriv ℝ n (slabTimeJet a b i f t) x‖ +
          ‖iteratedFDeriv ℝ n (slabTimeJet a b i g t) x‖ := norm_add_le _ _
      _ ≤ C n * A * D ^ (p * n) + C' n * A * D ^ (p * n) :=
        add_le_add (hf i hi n t ht x) (hg i hi n t ht x)
      _ = _ := by ring
  · exact (slabTimeJet_slice_smooth hab hfreg i ht).contDiffAt.of_le (by simp)
  · exact (slabTimeJet_slice_smooth hab hgreg i ht).contDiffAt.of_le (by simp)

/-- Composition with one bounded linear map commutes with closed-slab time jets. -/
theorem slabTimeJet_apply_clm {g : ℝ → Vec3 → E} (L : E →L[ℝ] F)
    (hab : a < b)
    (hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc a b ×ˢ (univ : Set Vec3)))
    (i : ℕ) {t : ℝ} (ht : t ∈ Icc a b) (x : Vec3) :
    slabTimeJet a b i (fun t y => L (g t y)) t x = L (slabTimeJet a b i g t x) := by
  induction i generalizing t with
  | zero => simp only [slabTimeJet, iteratedDerivWithin_zero]
  | succ i ih =>
    simp only [slabTimeJet_succ]
    refine (derivWithin_congr (fun r hr => ih hr) (ih ht)).trans ?_
    have h := L.hasFDerivAt.comp_hasDerivWithinAt t (hasDerivWithinAt_slabTimeJet hab hg i ht x)
    simpa only [slabTimeJet_succ, Function.comp_apply, Function.comp_def] using h.derivWithin (uniqueDiffOn_Icc hab t ht)

theorem apply_clm (hf : TerminalMixedJetBound a b q p D A C f)
    (hab : a < b)
    (hfreg : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc a b ×ˢ (univ : Set Vec3)))
    (L : E →L[ℝ] F) :
    TerminalMixedJetBound a b q p D A (fun n => ‖L‖ * C n) (fun t x => L (f t x)) := by
  intro i hi n t ht x
  have heq : slabTimeJet a b i (fun t y => L (f t y)) t = L ∘ slabTimeJet a b i f t :=
    funext (slabTimeJet_apply_clm L hab hfreg i ht)
  rw [heq]
  calc
    _ ≤ ‖L‖ * ‖iteratedFDeriv ℝ n (slabTimeJet a b i f t) x‖ :=
      L.norm_iteratedFDeriv_comp_left (slabTimeJet_slice_smooth hab hfreg i ht).contDiffAt (by simp)
    _ ≤ ‖L‖ * (C n * A * D ^ (p * n)) := mul_le_mul_of_nonneg_left (hf i hi n t ht x) (norm_nonneg _)
    _ = _ := by ring

end TerminalMixedJetBound

end

end TorusEuler

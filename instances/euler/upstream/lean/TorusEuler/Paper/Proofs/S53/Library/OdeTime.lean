import TorusEuler.OscillatoryDerivativeEstimates
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux

/-!
# S53 library: time derivative of the parameter words of a linear solve on `[l, r]`

The statement of `phaseOperatorWord_linearODE_time` for a slab `[0, T]` is transported to `[l, r]` by
the translation `t ↦ t + l`.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
/-- The parameter words of a linear solve on `[l, r]` satisfy the differentiated equation in time. -/
theorem phaseOperatorWord_linearODE_time_Icc
    (d : ι → P) (w : List ι) {A : ℝ → P → E →L[ℝ] E} {f x : ℝ → P → E} {l r : ℝ} (hlr : l < r)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ (univ : Set P)))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ (univ : Set P)))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ (univ : Set P)))
    (hxt : ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t) :
    ContinuousOn (fun q : ℝ × P =>
        phaseOperatorWord (fun i _ => d i) w (fun y => A q.1 y (x q.1 y) + f q.1 y) q.2)
      (Icc l r ×ˢ (univ : Set P)) ∧
    ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => phaseOperatorWord (fun i _ => d i) w (x s) p)
        (phaseOperatorWord (fun i _ => d i) w (fun y => A t y (x t y) + f t y) p) (Icc l r) t := by
  let T := r - l
  have hT : 0 < T := sub_pos.mpr hlr
  have hmap : MapsTo (fun u => u + l) (Icc 0 T) (Icc l r) := by
    intro u hu
    exact ⟨by linarith [hu.1], by have := hu.2; dsimp [T] at this; linarith⟩
  have hback : MapsTo (fun u => u + (-l)) (Icc l r) (Icc 0 T) := by
    intro u hu
    exact ⟨by linarith [hu.1], by dsimp [T]; linarith [hu.2]⟩
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × P => (z.1 + l, z.2)) (Icc 0 T ×ˢ univ) :=
    (contDiffOn_fst.add contDiffOn_const).prodMk contDiffOn_snd
  have hmaps : MapsTo (fun z : ℝ × P => (z.1 + l, z.2))
      (Icc 0 T ×ˢ univ) (Icc l r ×ˢ univ) := fun z hz => ⟨hmap hz.1, mem_univ _⟩
  have hA' : ContDiffOn ℝ ∞ (Function.uncurry (fun t => A (t + l))) (Icc 0 T ×ˢ univ) :=
    hA.comp hproj hmaps
  have hf' : ContDiffOn ℝ ∞ (Function.uncurry (fun t => f (t + l))) (Icc 0 T ×ˢ univ) :=
    hf.comp hproj hmaps
  have hx' : ContDiffOn ℝ ∞ (Function.uncurry (fun t => x (t + l))) (Icc 0 T ×ˢ univ) :=
    hx.comp hproj hmaps
  have hxt' (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => x (s + l) p) (A (t + l) p (x (t + l) p) + f (t + l) p)
        (Icc 0 T) t :=
    hasDerivWithinAt_translate (hxt p (t + l) (hmap ht)) hmap
  obtain ⟨hc, hd⟩ := phaseOperatorWord_linearODE_time d w (A := fun t => A (t + l))
    (f := fun t => f (t + l)) (x := fun t => x (t + l)) hT hA' hf' hx' hxt'
  refine ⟨?_, fun p t ht => ?_⟩
  · have h := hc.comp (continuous_fst.sub continuous_const |>.prodMk continuous_snd).continuousOn
      (s := Icc l r ×ˢ (univ : Set P)) (t := Icc 0 T ×ˢ univ)
      (f := fun q : ℝ × P => (q.1 + (-l), q.2)) (fun q hq => ⟨hback hq.1, mem_univ _⟩)
    refine h.congr fun q _ => ?_
    simp
  · have h := hd p (t + (-l)) (hback ht)
    have h2 := hasDerivWithinAt_translate h (I := Icc l r) (J := Icc 0 T) (c := -l) hback
    simpa [neg_add_cancel_right, add_neg_cancel_right] using h2

end

end TorusEuler.Paper.Lib.S53

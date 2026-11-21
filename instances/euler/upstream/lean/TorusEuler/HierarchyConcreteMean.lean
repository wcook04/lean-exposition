import TorusEuler.HierarchyConcreteTransverse

/-! Reading the smooth mean equation as an output of the concrete hierarchy. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

namespace HierarchySmoothProfile

variable {T : ℝ}

local notation "VP" => HierarchySmoothProfile T Vec3
local notation "SP" => HierarchySmoothProfile T ℝ
local notation "VPmap" => HierarchySmoothProfile T (Vec3 →L[ℝ] Vec3)
local notation "J" => hierarchyProfileSlab T

/-- The derivative on the spatial label line is the label component of
the actual joint derivative. -/
theorem profileLabelDerivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a d : Vec3) (s : ℝ) :
    fderivWithin ℝ f.val J (t, a, s) (0, d, 0) =
      fderiv ℝ (fun y => f.val (t, y, s)) a d := by
  let i : Vec3 →L[ℝ] HierarchyProfilePoint :=
    (inr ℝ ℝ (Vec3 × ℝ)).comp (inl ℝ Vec3 ℝ)
  have hx : (t, a, s) ∈ J := ⟨ht, mem_univ _⟩
  have hf := ((smooth f).differentiableOn (by simp) _ hx).hasFDerivWithinAt
  have hi : HasFDerivAt (fun y : Vec3 => (t, y, s)) i a := by
    have ht' : HasFDerivAt (fun _ : Vec3 => t) (0 : Vec3 →L[ℝ] ℝ) a := hasFDerivAt_const _ _
    have hs' : HasFDerivAt (fun _ : Vec3 => s) (0 : Vec3 →L[ℝ] ℝ) a := hasFDerivAt_const _ _
    have h := ht'.prodMk ((hasFDerivAt_id (𝕜 := ℝ) a).prodMk hs')
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro y
    simp [i]
  have hInside (y : Vec3) : (t, y, s) ∈ J := ⟨ht, mem_univ _⟩
  have h := hf.comp_hasFDerivAt a hi (Filter.Eventually.of_forall hInside)
  exact (congrArg (fun B : Vec3 →L[ℝ] E => B d) h.fderiv).symm

theorem phaseDerivative_zero_of_independent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchySmoothProfile T E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ)
    (h : ∀ r : ℝ, f.val (t, a, r) = f.val (t, a, s)) (c : ℝ) :
    fderivWithin ℝ f.val J (t, a, s) (0, 0, c) = 0 := by
  have hc := (hasDerivAt_profilePhase f ht a s).deriv
  rw [show (fun r => f.val (t, a, r)) = (fun _ : ℝ => f.val (t, a, s)) from funext h,
    (hasDerivAt_const (c := f.val (t, a, s)) s).deriv] at hc
  have hc' : ((0, 0, c) : HierarchyProfilePoint) = c • ((0, 0, 1) : HierarchyProfilePoint) := by simp
  rw [hc', map_smul, ← hc, smul_zero]

/-- The coframe label gradient of a scalar profile is the coframe transpose
applied to its ordinary label gradient. -/
theorem labelGradient_eq_adjoint_gradient (hT : 0 < T) (G : VPmap) (q : SP)
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (labelGradient hT G q).val (t, a, s) =
      (G.val (t, a, s)).adjoint (gradient (fun y => q.val (t, y, s)) a) := by
  have hx : (t, a, s) ∈ J := ⟨ht, mem_univ _⟩
  rw [labelGradient_apply hT G q hx]
  have hdiff : DifferentiableAt ℝ (fun y => q.val (t, y, s)) a := by
    have hsl : ContDiff ℝ ∞ (fun y => q.val (t, y, s)) := by
      have hEmbed : ContDiffOn ℝ ∞ (fun y : Vec3 => (t, y, s)) (univ : Set Vec3) :=
        contDiffOn_const.prodMk (contDiffOn_id.prodMk contDiffOn_const)
      have h := (smooth q).comp hEmbed (fun _ _ => ⟨ht, mem_univ _⟩)
      exact contDiffOn_univ.mp h
    exact hsl.differentiable (by simp) a
  have hcoord (i : Fin 3) :
      fderivWithin ℝ q.val J (t, a, s) (0, G.val (t, a, s) (EuclideanSpace.single i 1), 0) =
        ((G.val (t, a, s)).adjoint (gradient (fun y => q.val (t, y, s)) a)) i := by
    rw [profileLabelDerivative q ht a _ s, hdiff.hasGradientAt.hasFDerivAt.fderiv]
    change ⟪gradient (fun y => q.val (t, y, s)) a, G.val (t, a, s) (EuclideanSpace.single i 1)⟫_ℝ = _
    rw [← ContinuousLinearMap.adjoint_inner_left, real_inner_comm, EuclideanSpace.inner_single_left]
    simp
  change (∑ i : Fin 3, fderivWithin ℝ q.val J (t, a, s)
    (0, G.val (t, a, s) (EuclideanSpace.single i 1), 0) • EuclideanSpace.single i 1) = _
  simp only [hcoord]
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, EuclideanSpace.single, Finset.sum_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj.symm]
  · simp

set_option maxHeartbeats 1200000 in
/-- The phase-independent smooth solution of the actual mean equation gives
the corresponding output of the concrete hierarchy. -/
theorem exists_hierarchyConcreteMeanOutput (hT : 0 < T) (G M : VPmap) (κ F : VP)
    (B : ℝ → Vec3 → Vec3) (q : ℝ → Vec3 → ℝ)
    (hB : ContDiffOn ℝ ∞ (Function.uncurry B) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hq : ContDiffOn ℝ ∞ (Function.uncurry q) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (heq : ∀ (t : ℝ) (a : Vec3) (s : ℝ), t ∈ Icc 0 T →
      derivWithin (fun r => B r a) (Icc 0 T) t + M.val (t, a, s) (B t a) +
          (G.val (t, a, s)).adjoint (gradient (q t) a) = F.val (t, a, s)) :
    let A := hierarchyConcreteOperators hT G M κ
    ∃ o : HierarchyMeanOutput A, A.material o.B + A.labelGrad o.q = F ∧
      (∀ (t : ℝ) (a : Vec3) (s : ℝ), t ∈ Icc 0 T →
        o.B.val (t, a, s) = B t a ∧ o.q.val (t, a, s) = q t a) := by
  intro A
  have hproj : ContDiffOn ℝ ∞ (fun z : HierarchyProfilePoint => (z.1, z.2.1)) J :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hmaps : MapsTo (fun z : HierarchyProfilePoint => (z.1, z.2.1)) J
      (Icc 0 T ×ˢ (univ : Set Vec3)) := fun z hz => ⟨hz.1, mem_univ z.2.1⟩
  let Bp := ofSmooth _ (hB.comp hproj hmaps)
  let qp := ofSmooth _ (hq.comp hproj hmaps)
  have hBp (t : ℝ) (a : Vec3) (s : ℝ) (ht : t ∈ Icc 0 T) : Bp.val (t, a, s) = B t a :=
    ofSmooth_apply (hB.comp hproj hmaps) ⟨ht, mem_univ _⟩
  have hqp (t : ℝ) (a : Vec3) (s : ℝ) (ht : t ∈ Icc 0 T) : qp.val (t, a, s) = q t a :=
    ofSmooth_apply (hq.comp hproj hmaps) ⟨ht, mem_univ _⟩
  have hMean : A.average Bp = Bp :=
    profilePhaseAverage_eq_self_of_independent hT Bp
      (fun x hx s => (hBp x.1 x.2.1 s hx.1).trans (hBp x.1 x.2.1 x.2.2 hx.1).symm)
  have hPhase (u : VP) : A.phaseAdv u Bp = 0 := by
    apply ext
    rintro ⟨t, a, s⟩ hx
    change (advect hT (phaseDirections κ) u Bp).val (t, a, s) = 0
    rw [advect_apply hT _ u Bp hx, phaseDirections_apply κ u hx]
    exact phaseDerivative_zero_of_independent Bp hx.1 a s
      (fun r => (hBp t a r hx.1).trans (hBp t a s hx.1).symm) _
  have hGrad : A.phaseGrad qp = 0 := by
    apply ext
    rintro ⟨t, a, s⟩ hx
    change (phaseGradient hT κ qp).val (t, a, s) = 0
    rw [phaseGradient_apply hT κ qp hx, phaseDerivative_zero_of_independent qp hx.1 a s
      (fun r => (hqp t a r hx.1).trans (hqp t a s hx.1).symm), zero_smul]
  refine ⟨⟨Bp, qp, hMean, hPhase, hGrad⟩, ?_, fun t a s ht => ⟨hBp t a s ht, hqp t a s ht⟩⟩
  apply ext
  rintro ⟨t, a, s⟩ hx
  have ht := hx.1
  have hDer := (hasDerivWithinAt_profileTime Bp ht a s).congr
    (fun r hr => (hBp r a s hr).symm) (hBp t a s ht).symm
  have hLabel : (fun y => qp.val (t, y, s)) = q t := funext (fun y => hqp t y s ht)
  change (A.material Bp).val (t, a, s) + (labelGradient hT G qp).val (t, a, s) = F.val (t, a, s)
  rw [hierarchyConcreteOperators_material_apply hT G M κ Bp hx,
    labelGradient_eq_adjoint_gradient hT G qp ht a s, hBp t a s ht, hLabel,
    ← hDer.derivWithin (uniqueDiffOn_Icc hT t ht)]
  exact heq t a s ht

end HierarchySmoothProfile

end

end TorusEuler

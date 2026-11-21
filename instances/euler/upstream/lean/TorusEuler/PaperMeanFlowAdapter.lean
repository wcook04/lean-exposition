import TorusEuler.PaperPhysicalMeanStatements

/-! The physical assumptions of the endpoint inverse for an actual parent flow. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "J(" T ")" => Icc (0 : ℝ) T
local notation "LiftSlab(" T ")" => Set.prod (J(T)) (univ : Set Vec3)

private def paperMeanDescend {E : Type*} (f : ℝ → Vec3 → E) : ℝ × A → E :=
  fun z => f z.1 (toUnitTorus_surjective z.2).choose

private theorem paperMeanDescend_apply {E : Type*} {f : ℝ → Vec3 → E}
    {t : ℝ} (hf : SpatiallyPeriodic (f t)) (a : Vec3) :
    paperMeanDescend f (t, toUnitTorus a) = f t a := by
  obtain ⟨n, hn⟩ := (toUnitTorus_eq_iff _ _).mp (toUnitTorus_surjective (toUnitTorus a)).choose_spec
  change f t (toUnitTorus_surjective (toUnitTorus a)).choose = _
  rw [hn, hf n a]

private theorem paperMean_fderiv_lattice_equivariant {f : Vec3 → Vec3}
    (hf : ∀ (n : Fin 3 → ℤ) a, f (a + latticeVector n) = f a + latticeVector n) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n a
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q a) (funext (hf n))
  simpa only [fderiv_comp_add_right, fderiv_add_const] using h

private theorem paperMean_fderiv_periodic {f : Vec3 → Vec3} (hf : SpatiallyPeriodic f) :
    SpatiallyPeriodic (fderiv ℝ f) := by
  intro n a
  have h := congrArg (fun q : Vec3 → Vec3 => fderiv ℝ q a) (funext (hf n))
  simpa only [fderiv_comp_add_right] using h

/-- The deformation, inverse deformation and velocity gradient of a smooth
periodic parent yield the coefficient object of Theorem 4.2. -/
theorem exists_paperMeanParent_of_flow {T D L : ℝ} {U : Velocity} {X : ℝ → Velocity}
    (hT : 0 < T) (hX : IsLabelFlowOn U X J(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ J(T), SpatiallyPeriodic (U t))
    (hD : ∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (U t) x‖ ≤ L)
    (hsharp : ∀ t ∈ J(T), ∀ a w,
      ⟪endpointHessian (fderiv ℝ (U t) (X 0 t a))
        (derivWithin (fun r => fderiv ℝ (U r) (X 0 r a)) J(T) t) w, w⟫_ℝ ≤ ‖w‖ ^ 2) :
    ∃ p : PaperMeanParent T D L,
      ∀ t ∈ J(T), ∀ a,
        p.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        p.G (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
        p.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a) ∧
        p.Mt (t, toUnitTorus a) = derivWithin (fun r => fderiv ℝ (U r) (X 0 r a)) J(T) t := by
  let F (t : ℝ) (a : Vec3) := fderiv ℝ (X 0 t) a
  let G (t : ℝ) (a : Vec3) := fderiv ℝ (X t 0) (X 0 t a)
  let M (t : ℝ) (a : Vec3) := fderiv ℝ (U t) (X 0 t a)
  let Mt (t : ℝ) (a : Vec3) := derivWithin (fun r => M r a) J(T) t
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) LiftSlab(T) := hU.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hFper (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic (F t) :=
    paperMean_fderiv_lattice_equivariant (hX.add_latticeVector hK hper h0 ht)
  have hGper (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic (G t) := by
    intro n a
    change fderiv ℝ (X t 0) (X 0 t (a + latticeVector n)) = G t a
    rw [hX.add_latticeVector hK hper h0 ht n a,
      paperMean_fderiv_lattice_equivariant (hX.add_latticeVector hK hper ht h0) n (X 0 t a)]
  have hMper (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic (M t) := by
    intro n a
    change fderiv ℝ (U t) (X 0 t (a + latticeVector n)) = M t a
    rw [hX.add_latticeVector hK hper h0 ht n a,
      paperMean_fderiv_periodic (hper t ht) n (X 0 t a)]
  have hMtper (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic (Mt t) := by
    intro n a
    exact derivWithin_congr (fun r hr => hMper r hr n a) (hMper t ht n a)
  have hFsm : ContDiffOn ℝ ∞ (Function.uncurry F) LiftSlab(T) :=
    hX.contDiffOn_forwardLabelDerivative hT hU hper
  have hMsm : ContDiffOn ℝ ∞ (Function.uncurry M) LiftSlab(T) :=
    hX.contDiffOn_materialGradient hT hU hper
  have hMtime (a : Vec3) : ContDiffOn ℝ ∞ (fun r => M r a) J(T) :=
    hMsm.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hr => ⟨hr, mem_univ a⟩)
  have hFd (t : ℝ) (ht : t ∈ J(T)) (a : Vec3) :
      paperMeanDescend F (t, toUnitTorus a) = F t a := paperMeanDescend_apply (hFper t ht) a
  have hGd (t : ℝ) (ht : t ∈ J(T)) (a : Vec3) :
      paperMeanDescend G (t, toUnitTorus a) = G t a := paperMeanDescend_apply (hGper t ht) a
  have hMd (t : ℝ) (ht : t ∈ J(T)) (a : Vec3) :
      paperMeanDescend M (t, toUnitTorus a) = M t a := paperMeanDescend_apply (hMper t ht) a
  have hMtd (t : ℝ) (ht : t ∈ J(T)) (a : Vec3) :
      paperMeanDescend Mt (t, toUnitTorus a) = Mt t a := paperMeanDescend_apply (hMtper t ht) a
  let p : PaperMeanParent T D L :=
    { F := paperMeanDescend F
      G := paperMeanDescend G
      M := paperMeanDescend M
      Mt := paperMeanDescend Mt
      deformation_smooth := hFsm.congr fun x hx => hFd x.1 hx.1 x.2
      gradient_smooth := hMsm.congr fun x hx => hMd x.1 hx.1 x.2
      deformation_ode := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a, hFd t ht a]
        exact ((hX.labelDerivative_evolves hT hU₂ hper h0 a).2 t ht).congr_of_mem
          (fun r hr => hFd r hr a) ht
      gradient_derivative := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hMtd t ht a]
        exact (((hMtime a).differentiableOn (by simp) t ht).hasDerivWithinAt).congr_of_mem
          (fun r hr => hMd r hr a) ht
      gradient_derivative_continuous := by
        intro b
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        exact ((hMtime a).continuousOn_derivWithin (uniqueDiffOn_Icc hT) (by simp)).congr
          (fun r hr => hMtd r hr a)
      left_inverse := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a, hFd t ht a]
        exact (hX.labelDerivative_inverse hT hU₂ hper h0 ht a).1
      right_inverse := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a, hFd t ht a]
        exact (hX.labelDerivative_inverse hT hU₂ hper h0 ht a).2
      inverse_bound := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hGd t ht a]
        exact hD t ht a
      gradient_bound := by
        intro b t ht
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a]
        exact hL t ht (X 0 t a)
      hessian_upper := by
        intro b t ht w
        obtain ⟨a, rfl⟩ := toUnitTorus_surjective b
        rw [hMd t ht a, hMtd t ht a]
        exact hsharp t ht a w }
  exact ⟨p, fun t ht a => ⟨hFd t ht a, hGd t ht a, hMd t ht a, hMtd t ht a⟩⟩


/-- The smooth-force part of Theorem 4.2 for an actual Eulerian parent and
Eulerian force. The label pressure is normalized and the reconstructed
Eulerian fields obey the equation on the closed slab. -/
theorem paper_mean_inverse_smooth_force_of_flow {T D L : ℝ} {U f : Velocity} {X : ℝ → Velocity}
    (hT : 0 < T) (hT₁ : T ≤ 1) (hD₁ : 1 ≤ D) (hL₀ : 0 ≤ L)
    (hX : IsLabelFlowOn U X J(T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) LiftSlab(T))
    (hper : ∀ t ∈ J(T), SpatiallyPeriodic (U t))
    (hdiv : ∀ t ∈ J(T), ∀ x, divergence (U t) x = 0)
    (hD : ∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (U t) x‖ ≤ L)
    (hsharp : ∀ t ∈ J(T), ∀ a w,
      ⟪endpointHessian (fderiv ℝ (U t) (X 0 t a))
        (derivWithin (fun r => fderiv ℝ (U r) (X 0 r a)) J(T) t) w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) LiftSlab(T))
    (hfper : ∀ t ∈ J(T), SpatiallyPeriodic (f t)) :
    let force (t : ℝ) (a : Vec3) := f t (X 0 t a)
    ∃ (p : PaperMeanParent T D L) (s : PaperSmoothMeanSolution p force),
      (∀ t ∈ J(T), ∀ a, p.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        p.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a)) ∧
      (∀ t ∈ J(T), (∫ x in centeredCell, s.pressure t x) = 0) ∧
      let b (t : ℝ) (x : Vec3) := s.mean t (X t 0 x)
      let q (t : ℝ) (x : Vec3) := s.pressure t (X t 0 x)
      ContDiffOn ℝ ∞ (Function.uncurry b) LiftSlab(T) ∧
      ContDiffOn ℝ ∞ (Function.uncurry q) LiftSlab(T) ∧
      (∀ t ∈ J(T), SpatiallyPeriodic (b t) ∧ SpatiallyPeriodic (q t)) ∧
      ∀ t ∈ J(T), ∀ x, divergence (b t) x = 0 ∧
        fderivWithin ℝ (Function.uncurry b) LiftSlab(T) (t, x) (1, U t x) +
          fderiv ℝ (U t) x (b t x) + gradient (q t) x = f t x := by
  intro force
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  obtain ⟨p, hp⟩ := exists_paperMeanParent_of_flow hT hX hU hper hD hL hsharp
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hforce : ContDiffOn ℝ ∞ (Function.uncurry force) LiftSlab(T) := by
    exact hf.comp (contDiffOn_fst.prodMk (hX.contDiffOn_forwardLabelFlow hT hU hper))
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hforceper (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic (force t) := by
    intro n a
    change f t (X 0 t (a + latticeVector n)) = f t (X 0 t a)
    rw [hX.add_latticeVector hK hper h0 ht n a, hfper t ht n]
  obtain ⟨s, hs⟩ := paper_mean_inverse_smooth_force hT hT₁ hD₁ hL₀ p force hforce hforceper
  refine ⟨p, s, (fun t ht a => ⟨(hp t ht a).1, (hp t ht a).2.2.1⟩), hs, ?_⟩
  obtain ⟨hb, hq, hper', hsol⟩ := s.eulerian_equation hT hX hU hper hdiv
    (fun t ht a => (hp t ht a).1) (fun t ht a => (hp t ht a).2.2.1)
  refine ⟨hb, hq, hper', fun t ht x => ?_⟩
  simpa only [force, (hX.inverse hK h0 ht).2 x] using hsol t ht x

end

end TorusEuler

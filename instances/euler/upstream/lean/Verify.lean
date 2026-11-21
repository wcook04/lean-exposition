import TorusEuler
import Lean.Util.CollectAxioms

open Filter MeasureTheory Set TorusEuler
open scoped InnerProductSpace NNReal

-- Expected types are stated apart from the proof files, with all inputs supplied.
example (F : ℝ → ℝ) (a k x : EuclideanSpace ℝ (Fin 3))
    (dF : ℝ) (hF : HasDerivAt F dF ⟪k, x⟫_ℝ) :
    HasFDerivAt (fun y : EuclideanSpace ℝ (Fin 3) => F ⟪k, y⟫_ℝ • a)
      ((dF • innerSL ℝ k).smulRight a) x :=
  TorusEuler.hasFDerivAt_planeWave F a k x dF hF

example (ε τ x s e Y : ℝ) (hx : x = ε * τ ^ 2 / 2)
    (hs : (1 + x ^ 2) * s ^ 2 = 1) (hY : Y = s * (1 + e) - ε * τ * x * s ^ 2 / 2) :
    (x + ε + 2 * ε * τ * Y = x - ε + 2 * ε * s ^ 2 + 2 * ε * τ * s * (1 + e)) ∧
    (-1 + ε * x + 2 * (1 + x ^ 2) * Y ^ 2 + 2 * ε * τ * x * Y =
      1 + 4 * e + 2 * e ^ 2 + ε * x * s ^ 2) :=
  TorusEuler.referenceCouplingNumerators ε τ x s e Y hx hs hY

example {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {κ V : ℝ → E} {t : ℝ} (M : E →L[ℝ] E) (f : E) (p_s : ℝ)
    (hκ : HasDerivAt κ (-(M.adjoint (κ t))) t)
    (hV : HasDerivAt V (f - M (V t) - p_s • κ t) t)
    (hperp : HasDerivAt (fun r => ⟪κ r, V r⟫_ℝ) 0 t) :
    ‖κ t‖ ^ 2 * p_s = ⟪κ t, f⟫_ℝ - 2 * ⟪κ t, M (V t)⟫_ℝ :=
  TorusEuler.transversePressureIdentity M f p_s hκ hV hperp

example : TorusEuler.Theorem11 := TorusEuler.theorem11

example : TorusEuler.AuxiliaryTerminalSmoothness := TorusEuler.auxiliaryTerminalSmoothness

example {T : ℝ} (hT : 0 < T) :
    IsEulerSolution T (fun _ _ => 0) (fun _ _ => 0) ∧ NeBot (nhdsWithin T (Ico 0 T)) :=
  ⟨isEulerSolution_zero hT, terminalTime_neBot hT⟩

example {T : ℝ} (hT : 0 < T) : ¬ IsMaximalEulerSolution T (fun _ _ => 0) (fun _ _ => 0) := by
  intro h
  have hTS : T < T + 1 := lt_add_of_pos_right _ zero_lt_one
  exact h.2 (T + 1) hTS ⟨_, _, isEulerSolution_zero (hT.trans hTS), fun _ _ => rfl⟩

example {T : ℝ} {u : Velocity} {p : Pressure} (h : IsEulerSolution T u p)
    (hcurl : Tendsto (fun t => ‖curl (u t) 0‖) (nhdsWithin T (Ico 0 T)) atTop) :
    IsMaximalEulerSolution T u p :=
  h.isMaximal_of_tendsto_curl_atTop hcurl

example (F : ℝ → ℝ) (a k x : Vec3) (dF : ℝ) (hF : HasDerivAt F dF ⟪k, x⟫_ℝ) :
    curl (fun y => F ⟪k, y⟫_ℝ • a) x =
      dF • WithLp.toLp 2 (crossProduct k.ofLp a.ofLp) :=
  curl_planeWave F a k x dF hF

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (f : ℝ → E) (hf : Continuous f) (hper : Function.Periodic f 1)
    (hmean : phaseMean f = 0) :
    Function.Periodic (phasePrimitive f) 1 ∧ phaseMean (phasePrimitive f) = 0 ∧
      ∀ s, HasDerivAt (phasePrimitive f) (f s) s :=
  ⟨periodic_phasePrimitive hf hper hmean, phaseMean_phasePrimitive hf,
    hasDerivAt_phasePrimitive hf⟩

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : ℝ → E →L[ℝ] E} {x : ℝ → E} {a b : ℝ} (hab : a ≤ b)
    (hA : ContinuousOn A (Icc a b))
    (hx : ∀ t ∈ Icc a b, HasDerivWithinAt x (A t (x t)) (Icc a b) t)
    (h₀ : x a ≠ 0) : x b ≠ 0 :=
  linearODE_ne_zero_of_mem ordConnected_Icc ⟨le_rfl, hab⟩ hA hx h₀ b ⟨hab, le_rfl⟩

example {T : ℝ} {f df : ℝ → Vec3} (hT : 0 ≤ T) (hfT : f T = 0)
    (hc : ContinuousOn df (Icc 0 T))
    (hf : ∀ t ∈ Icc 0 T, HasDerivWithinAt f (df t) (Icc 0 T) t) :
    (∫ t in (0 : ℝ)..T, ‖f t‖ ^ 2) ≤
      T ^ 2 / 2 * (∫ t in (0 : ℝ)..T, ‖df t‖ ^ 2) :=
  terminal_poincare_integral hT hfT hc hf

example {T : ℝ} {F M Mt : ℝ → Vec3 →L[ℝ] Vec3} {z v : ℝ → Vec3}
    (hT : 0 ≤ T) (hT1 : T ≤ 1)
    (hF : ∀ t ∈ Icc 0 T, HasDerivWithinAt F ((M t).comp (F t)) (Icc 0 T) t)
    (hM : ∀ t ∈ Icc 0 T, HasDerivWithinAt M (Mt t) (Icc 0 T) t)
    (hz : ∀ t ∈ Icc 0 T, HasDerivWithinAt z (v t) (Icc 0 T) t)
    (hMt : ContinuousOn Mt (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hz0 : z 0 = 0) (hzT : z T = 0)
    (hupper : ∀ t ∈ Icc 0 T, ∀ x : Vec3, ⟪-((Mt t + (M t).comp (M t)) x), x⟫_ℝ ≤ ‖x‖ ^ 2) :
    (1 / 2 : ℝ) * (∫ t in (0 : ℝ)..T, ‖M t (F t (z t)) + F t (v t)‖ ^ 2) ≤
      ∫ t in (0 : ℝ)..T,
        ⟪(F t).adjoint (F t (v t)), v t⟫_ℝ +
          ⟪(F t).adjoint (((M t).adjoint - M t) (F t (v t))), z t⟫_ℝ :=
  endpointLabelEnergy_coercive hT hT1 hF hM hz hMt hv hz0 hzT hupper

example {N : Matrix (Fin 2) (Fin 2) ℝ} {d : ℝ} (hd : 0 ≤ d)
    (h : ∀ i j, |N i j| ≤ d) :
    ‖MovingAmplitude.pairOperator N‖ ≤ 2 * d :=
  MovingAmplitude.norm_pairOperator_le hd h

example {e : ℝ → Fin 3 → Vec3} {a : ℝ → Vec3} {S t : ℝ}
    (he : Orthonormal ℝ (e t)) (hS : S ≠ 0)
    (ha : a t = (-S⁻¹) • e t 0 + e t 1) :
    MovingAmplitude.U e a S t = 1 ∧ MovingAmplitude.V e a t = 1 :=
  MovingAmplitude.growing_components he hS ha

example {U b : Velocity} {X : ℝ → ℝ → Velocity} {l r : ℝ} {K L J C : ℝ≥0}
    (hlr : l ≤ r)
    (hX : ∀ ε : ℝ, IsLabelFlowOn (fun t x => U t x + ε • b t x) (X ε) (Icc l r))
    (hUlip : ∀ t ∈ Icc l r, LipschitzWith K (U t))
    (hUdiff : ∀ t ∈ Icc l r, Differentiable ℝ (U t))
    (hDlip : ∀ t ∈ Icc l r, LipschitzWith L (fderiv ℝ (U t)))
    (hblip : ∀ t ∈ Icc l r, LipschitzWith J (b t))
    (hbnd : ∀ t ∈ Icc l r, ∀ x, ‖b t x‖ ≤ C)
    (hbc : ContinuousOn (Function.uncurry b) (Icc l r ×ˢ (univ : Set Vec3))) (a : Vec3)
    (hD : ContinuousOn (fun t => fderiv ℝ (U t) (X 0 l t a)) (Icc l r)) :
    ∃ ξ : ℝ → Vec3, ξ l = 0 ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt ξ
        (fderiv ℝ (U t) (X 0 l t a) (ξ t) + b t (X 0 l t a)) (Icc l r) t) ∧
      ∀ t ∈ Icc l r, HasDerivAt (fun ε : ℝ => X ε l t a) (ξ t) 0 :=
  labelFlow_firstVariation hlr hX hUlip hUdiff hDlip hblip hbnd hbc a hD

example {A : Type*} [MetricSpace A] {T : ℝ}
    (w : HalfHolder A (Lp Vec3 2 (volume.restrict (Ioc 0 T)))) :
    let Jw (t : Icc (0 : ℝ) T) : HalfHolder A Vec3 :=
      HalfHolder.map (endpointPrimitiveEvaluation t) w
    Continuous Jw ∧ ∀ s t : Icc (0 : ℝ) T,
      ‖Jw t - Jw s‖ ≤ Real.sqrt |(t : ℝ) - s| * ‖w‖ :=
  continuous_and_norm_sub_le_endpointHalfHolderPrimitive w

run_cmd do
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let decls := (← Lean.getEnv).constants.map₁.fold (init := #[]) fun names name _ =>
    if (`TorusEuler).isPrefixOf name then names.push name else names
  unless decls.contains ``TorusEuler.theorem11 do
    throwError "The unconditional proof of Theorem11 is missing from the imported declarations"
  for decl in decls do
    for ax in ← Lean.collectAxioms decl do
      unless allowed.contains ax do
        throwError "{decl} depends on an unexpected axiom {ax}"
  Lean.logInfo m!"Checked axiom dependencies of {decls.size} TorusEuler declarations"

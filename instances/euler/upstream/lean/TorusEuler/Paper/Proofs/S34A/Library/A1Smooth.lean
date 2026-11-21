import TorusEuler.Paper.Proofs.S34A.Library.A1Words
import TorusEuler.PaperAppendixAInverse

/-! The smooth clause of **Theorem A.1** (package S34A) from Lemma A.2: smooth
coefficients and source give a solution of (4.9) on `[0,1]` whose label velocity is
jointly smooth, and the smoothness of `z`, `c` and `∇φ`. -/

open Filter MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "Path" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "TM" => volume.restrict (Ioc (0 : ℝ) 1)
local notation "I" => Icc (0 : ℝ) 1
local notation "LSlab" => Set.prod (Icc (0 : ℝ) 1) (univ : Set Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "V½" => HalfHolder A Vec3
local notation "KMix" => HalfHolder A (Path →L[ℝ] Path)
local notation "P" => endpointStrongSpatialProjection
local notation "P[" T "]" => endpointStrongMixedLeray T
local notation "W[" T "]" => freezingFixedSpace (P[T])

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1SmoothSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1SmoothSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

/-- From a jointly smooth label velocity of a solution of (4.9) and smooth data, the
displacement `z = Jv`, the constant `c` and the pressure gradient are smooth (last
sentence of Theorem A.1, sections/appA_mean_regularity.tex:245–249). Copy of the private
`paperA1_smoothData_conclusions` (PaperAppendixAInverse.lean:184); glue. -/
theorem smoothData_conclusions
    {K Ω : ℝ → K½} {src : ℝ → V½} (s : PaperMeanIntegratedSolution 1 K Ω src)
    (hΩc : ContinuousOn Ω I) (G : ℝ → V½) (hG : ∀ t ∈ I, paperMeanIntegratedMomentum K Ω src s.velocity t =
      (s.constant : V½) + G t)
    (hJoint : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity s.velocity)) LSlab)
    (hsK : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (K z.1)) LSlab)
    (hsΩ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (Ω z.1)) LSlab)
    (hsL : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (src z.1)) LSlab) :
    ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity (endpointPrimitive s.velocity))) LSlab ∧
    ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) s.constant.val) ∧
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (G z.1)) LSlab := by
  let v := endpointPhysicalLabelVelocity s.velocity
  let omegaField (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2) (Ω z.1)
  let ωv (t : ℝ) (x : Vec3) := omegaField (t, x) (v t x)
  have hωv : ContDiffOn ℝ ∞ (Function.uncurry ωv) LSlab := hsΩ.clm_apply hJoint
  have hPrim := contDiffOn_endpointPhysicalJointPrimitive zero_lt_one hJoint
  have hΩPrim := contDiffOn_endpointPhysicalJointPrimitive zero_lt_one hωv
  let r (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2)
    (paperMeanIntegratedMomentum K Ω src s.velocity z.1)
  have hΩE (t : ℝ) (ht : t ∈ I) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x)
        (endpointPrimitive (fun r => (Ω r).coefficientMul (s.velocity r).val) t) =
        endpointPrimitive (fun r => ωv r x) t := by
    have hCont : ContinuousOn (fun r => (Ω r).coefficientMul (s.velocity r).val) I := by
      exact (HalfHolder.coefficientMulL.continuous.comp_continuousOn hΩc).clm_apply
        (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn s.continuous)
    have hi : IntervalIntegrable (fun r => (Ω r).coefficientMul (s.velocity r).val) volume 0 t :=
      (hCont.mono (Icc_subset_Icc_right ht.2)).intervalIntegrable_of_Icc ht.1
    simpa only [endpointPrimitive, HalfHolder.eval_coefficientMul, ωv, omegaField, v, endpointPhysicalLabelVelocity]
      using ((HalfHolder.eval (toUnitTorus x)).intervalIntegral_comp_comm hi).symm
  have hR : ContDiffOn ℝ ∞ r LSlab := by
    refine (((hsK.clm_apply hJoint).sub hΩPrim).add hsL).congr ?_
    intro z hz
    simp only [r, paperMeanIntegratedMomentum, map_add, map_sub, HalfHolder.eval_coefficientMul, hΩE _ hz.1]
    rfl
  have hc0 : P (paperMeanIntegratedMomentum K Ω src s.velocity 0) = s.constant :=
    s.projected 0 ⟨le_rfl, zero_le_one⟩
  have hcSlice : ContDiff ℝ ∞ (fun x => r (0, x)) :=
    contDiffOn_univ.mp (hR.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨⟨le_rfl, zero_le_one⟩, mem_univ x⟩))
  have hc : ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) s.constant.val) := by
    rw [← hc0]
    let f0 := paperMeanIntegratedMomentum K Ω src s.velocity 0
    change ContDiff ℝ ∞ (fun x => HalfHolder.eval (toUnitTorus x) (endpointStrongSpatialLeray f0))
    rw [← periodicLerayHolderLift_pullback f0]
    apply contDiff_infty.mpr
    intro n
    have hPer : SpatiallyPeriodic (fun x => r (0, x)) := by
      intro k x
      exact congrArg (fun a => HalfHolder.eval a (paperMeanIntegratedMomentum K Ω src s.velocity 0))
        ((toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩)
    exact (spatialHolderHalf_periodicLerayHolderLift hPer
      (spatialHolderHalf_of_contDiff_periodic hcSlice hPer n)).1.1
  refine ⟨?_, hc, ?_⟩
  · refine hPrim.congr ?_
    intro z hz
    let ev := (HalfHolder.eval (toUnitTorus z.2)).comp endpointHalfHolderSolenoidal.subtypeL
    let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
    have hi : IntervalIntegrable s.velocity volume 0 z.1 :=
      (s.continuous.mono (Icc_subset_Icc_right hz.1.2)).intervalIntegrable_of_Icc hz.1.1
    exact (ev.intervalIntegral_comp_comm hi).symm
  · refine (hR.sub (hc.comp contDiff_snd).contDiffOn).congr ?_
    intro z hz
    have h := congrArg (HalfHolder.eval (toUnitTorus z.2)) (hG z.1 hz.1)
    rw [map_add] at h
    dsimp only [r, Function.comp_apply]
    rw [h, add_sub_cancel_left]

set_option maxHeartbeats 8000000 in
/-- The smooth clause of **Theorem A.1** from **Lemma A.2**
(sections/appA_mean_regularity.tex:242–249): for smooth `K`, `Ω`, `L` there is a
solution of (4.9) on `[0,1]` whose label velocity is jointly smooth.

* The coefficients and the source give spatial derivative words (`exists_endpointSlabHalfHolderJets`,
  `exists_endpointMixedCoefficient_jets`, `exists_endpointMixedSource_jets`).
* `hMx` (Lemma A.2, `H = L²(I;ℝ³)`, `B = K - JΩ`, coercivity from (A.2)) gives the mixed
  isomorphism `eM` and the solution `v = eM⁻¹(-P Q L)`; its higher-order clause gives
  `v ∈ C^{k,1/2}_a(L²_t)` for every `k`, because `B` and `P Q L` are.
* `hSp` (Lemma A.2, `H = ℝ³`, `B = K(t)`, coercivity `κ` from (A.1)) gives the fixed-time
  inverses, uniformly bounded and smooth in time.
* The words of `v` solve the differentiated equations (`exists_mixedSolveSpatialJets_of_words`);
  each has a time-smooth representative (`exists_spatialJetTimeRecovery_of_family`), and
  these spatial jets give joint smoothness.

Provenance: a parameterized copy of the A.1 content lemma `exists_paperA1_smoothSolution`
(PaperAppendixAInverse.lean:94). The jets, `hEq`, `Kmix`/`Ωmix`/`Lmix`, the Lipschitz,
bound and coercivity facts and `hMixPos` are unchanged; the private
`appendixCoefficient_caps` is replaced by `endpointHalfHolderCaps_of_lift_gradient`, and
`hLrep`, `hT` are added. The call to `exists_endpointJointVelocity_of_matchedSpatialData`
(which reaches A.2 content) is replaced by the hypotheses `hMx`, `hSp` (Lemma A.2) with
`exists_mixedTimeRecovery_of_family`, `exists_mixedSolveSpatialJets_of_words` and
`exists_spatialJetTimeRecovery_of_family`. -/
theorem exists_smoothSolution_of_freezing {C : ℝ} {p : ℕ} (hC : 0 ≤ C)
    (hSp : ∀ (B : K½) (μ Lip : ℝ), 0 < μ → 0 ≤ Lip →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ Lip * dist a b) →
      (∀ a (w : Vec3), μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      FreezingConclusion endpointStrongSpatialLeray endpointStrongSpatialLeray_idempotent
        C p B μ Lip)
    (hMx : ∀ (B : KMix) (μ Lip : ℝ), 0 < μ → 0 ≤ Lip →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ Lip * dist a b) →
      (∀ a (w : Path), endpointIntegral 1 w = 0 → μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      FreezingConclusion (endpointStrongMixedLeray 1)
        (endpointStrongMixedLeray_idempotent zero_lt_one) C p B μ Lip)
    {K Ω : ℝ → K½} {src : ℝ → V½}
    {κ μ K₀ K₁ Ω₀ Ω₁ : ℝ} (hκ : 0 < κ) (hμ : 0 < μ)
    (hK : EndpointCoefficientC1Bound K K₀ K₁) (hΩ : EndpointCoefficientC1Bound Ω Ω₀ Ω₁)
    (hPos : ∀ t ∈ I, ∀ a v, κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) v, v⟫_ℝ)
    (hEnergy : EndpointSobolevEnergyBound K Ω μ)
    (hsK : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (K z.1)) LSlab)
    (hsΩ : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (Ω z.1)) LSlab)
    (hsL : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (src z.1))
      LSlab) :
    ∃ s : PaperMeanIntegratedSolution 1 K Ω src,
      ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity s.velocity)) LSlab := by
  have hT : (0 : ℝ) < 1 := zero_lt_one
  have hper (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → HalfHolder A E) (t : ℝ) :
      SpatiallyPeriodic (fun x => HalfHolder.eval (toUnitTorus x) (f t)) := by
    intro k x
    change HalfHolder.eval (toUnitTorus (x + latticeVector k)) (f t) = _
    rw [(toUnitTorus_eq_iff _ _).mpr ⟨k, rfl⟩]
  obtain ⟨Jk⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsK
    (fun t _ => hper _ K t)
  obtain ⟨Jω⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsΩ
    (fun t _ => hper _ Ω t)
  obtain ⟨Jl⟩ := exists_endpointSlabHalfHolderJets zero_lt_one coordinateDirection _ hsL
    (fun t _ => hper _ src t)
  have hEq (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
      (f : ℝ → HalfHolder A E)
      (J : EndpointSlabHalfHolderJets 1 coordinateDirection
        (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (f z.1))) :
      EqOn (J.curve []) f I := by
    intro t ht
    apply HalfHolder.ext
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    exact J.eval_lift [] t ht x
  have hKeq := hEq _ K Jk
  have hΩeq := hEq _ Ω Jω
  have hLeq := hEq _ src Jl
  obtain ⟨Kmix, hKa, hKd⟩ := exists_endpointMixedCoefficient_jets Jk
  obtain ⟨Ωmix, hΩa, hΩd⟩ := exists_endpointMixedCoefficient_jets Jω
  obtain ⟨Lmix, hLa, hLd⟩ := exists_endpointMixedSource_jets zero_le_one Jl
  have hLrep (q : List (Fin 3)) : EndpointMixedRepresents (Lmix q) (Jl.curve q) :=
    ae_of_all _ (hLa q)
  have capsK := endpointHalfHolderCaps_of_lift_gradient (T := 1) hK.1 hK.2.1 K
    (fun t x => HalfHolder.eval (toUnitTorus x) (K t)) (fun _ _ _ => rfl)
    (fun t ht => (hK.2.2.2 t ht).1) (fun t ht x => ((hK.2.2.2 t ht).2 x).1)
    (fun t ht x => ((hK.2.2.2 t ht).2 x).2)
  have capsΩ := endpointHalfHolderCaps_of_lift_gradient (T := 1) hΩ.1 hΩ.2.1 Ω
    (fun t x => HalfHolder.eval (toUnitTorus x) (Ω t)) (fun _ _ _ => rfl)
    (fun t ht => (hΩ.2.2.2 t ht).1) (fun t ht x => ((hΩ.2.2.2 t ht).2 x).1)
    (fun t ht x => ((hΩ.2.2.2 t ht).2 x).2)
  have hkL : 0 ≤ 2 * K₁ := mul_nonneg zero_le_two hK.2.1
  have hωL : 0 ≤ 2 * Ω₁ := mul_nonneg zero_le_two hΩ.2.1
  have hKlip t (ht : t ∈ I) a b :
      ‖HalfHolder.eval a (Jk.curve [] t) - HalfHolder.eval b (Jk.curve [] t)‖ ≤
        2 * K₁ * dist a b := by rw [hKeq ht]; exact capsK.2 t ht a b
  have hΩlip t (ht : t ∈ I) a b :
      ‖HalfHolder.eval a (Jω.curve [] t) - HalfHolder.eval b (Jω.curve [] t)‖ ≤
        2 * Ω₁ * dist a b := by rw [hΩeq ht]; exact capsΩ.2 t ht a b
  have hKbound t (ht : t ∈ I) : ‖(Jk.curve [] t).val.1‖ ≤ K₀ + 2 * K₁ := by
    rw [hKeq ht]
    exact (norm_fst_le (K t).val).trans (capsK.1 t ht)
  have hKpos t (ht : t ∈ I) a v :
      κ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (Jk.curve [] t) v, v⟫_ℝ := by
    rw [hKeq ht]
    exact hPos t ht a v
  have hLip := norm_endpointMixedPathCoefficient_sub_le zero_le_one (Kmix []) (Ωmix [])
    (norm_endpointMixedCoefficient_sub_le_of_timeSlices hkL (Kmix []) (Jk.curve [])
      hKlip (hKa []))
    (norm_endpointMixedCoefficient_sub_le_of_timeSlices hωL (Ωmix []) (Jω.curve [])
      hΩlip (hΩa []))
  have hA (kin : ℝ → K½) (c : KMix) (z : ℝ → K½)
      (hz : EqOn z kin I) (a : A) (v : Path)
      (hc : (fun t => HalfHolder.eval a c v t) =ᵐ[TM]
        fun t => HalfHolder.eval a (z t) (v t)) :
      (fun t => HalfHolder.eval a c v t) =ᵐ[TM]
        fun t => HalfHolder.eval a (kin t) (v t) := by
    filter_upwards [hc, ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr hmem
    change HalfHolder.eval a c v r = _ at hr ⊢
    rw [hr, hz (Ioc_subset_Icc_self hmem)]
  have hMixPos a v (hv : endpointIntegral 1 v = 0) :
      μ * ‖v‖ ^ 2 ≤
        ⟪HalfHolder.eval a (endpointMixedPathCoefficient zero_le_one (Kmix []) (Ωmix [])) v,
          v⟫_ℝ := by
    rw [endpointMixedPathCoefficient_inner_eq_sobolevEnergy K Ω _ _ a v hv
      (hA K _ _ hKeq a v (hKa [] a v)) (hA Ω _ _ hΩeq a v (hΩa [] a v))]
    exact hEnergy a v hv
  -- the mixed isomorphism of Lemma A.2 and the base solve
  let B := endpointMixedPathCoefficient zero_le_one (Kmix []) (Ωmix [])
  have hLmix : 0 ≤ 2 * K₁ + 1 * (2 * Ω₁) := add_nonneg hkL (mul_nonneg zero_le_one hωL)
  obtain ⟨eM, heM, -, hHigher⟩ := hMx B μ _ hμ hLmix hLip hMixPos
  let pL : W[1] := ⟨P[1] (Lmix []),
    (mem_freezingFixedSpace P[1] _).mpr (endpointStrongMixedLeray_idempotent hT _)⟩
  let w₁ := eM.symm (-pL)
  let w := w₁.val
  have hFixed : P[1] w = w := (mem_freezingFixedSpace P[1] _).mp w₁.property
  have heMw : (eM w₁).val = -(P[1] (Lmix [])) := by
    rw [show eM w₁ = -pL from eM.apply_symm_apply _]
    rfl
  have hProjected : P[1] (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) w +
      Lmix []) = 0 := by
    have hc : (eM w₁).val = P[1] (B.coefficientMul w) := by
      have := congrArg (fun g : W[1] →L[ℝ] W[1] => (g w₁).val) heM
      simpa using this
    rw [map_add, ← endpointMixedPathCoefficient_coefficientMul hT.le (Kmix []) (Ωmix [])]
    change P[1] (B.coefficientMul w) + _ = 0
    rw [← hc, heMw, neg_add_cancel]
  -- the fixed-time inverses of Lemma A.2
  let Ainv := C * (2 + κ⁻¹ + (K₀ + 2 * K₁) + 2 * K₁) ^ p
  have hAt : ∀ t ∈ I, ∃ e : S ≃L[ℝ] S,
      (∀ v : S, e v = P ((Jk.curve [] t).coefficientMul v.val)) ∧
      ‖(e.symm : S →L[ℝ] S)‖ ≤ Ainv := by
    intro t ht
    obtain ⟨e, he, hb⟩ := exists_solenoidalInverse_of_freezing hC hκ hkL
      (hSp _ κ (2 * K₁) hκ hkL (hKlip t ht) (hKpos t ht))
    refine ⟨e, he, hb.trans ?_⟩
    have h0 : 0 ≤ 2 + κ⁻¹ + ‖(Jk.curve [] t).val.1‖ + 2 * K₁ := by
      have := inv_nonneg.mpr hκ.le
      positivity
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (by linarith [hKbound t ht]) p) hC
  obtain ⟨e, he, hE, hEc⟩ := exists_instantaneousFamily_of_pointwise (Jk.smooth []) hAt
  obtain ⟨Csrc, hBound⟩ := isCompact_Icc.exists_bound_of_continuousOn (Jl.smooth []).continuousOn
  obtain ⟨g, hg, hRecover, hRep, hZero, hEnd, _⟩ :=
    exists_mixedTimeRecovery_of_family hT (Kmix []) (Ωmix []) w (Lmix []) (Jk.curve [])
      (Jl.curve []) hFixed hProjected hκ hKpos e he hE hEc.continuousOn
      (Jl.smooth []).continuousOn (by simpa only using hBound)
      (ae_endpointMixedCoefficient_spatialSlice_of_pathAction (Jk.curve []) (Kmix [])
        (Jk.smooth []).continuousOn (ae_of_all _ (hKa [])) w)
      ((hLrep []).spatialSlice hT.le (Jl.smooth []).continuousOn)
  -- regularity of the mixed solution from the higher-order clause of Lemma A.2
  have hWwords (N : ℕ) : HasSpatialHolderWords N w := by
    have hBk : SpatialHolderHalf (N + 1) (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) B) :=
      (hasSpatialHolderWords_iff_spatialHolderHalf (N + 1) B).mp
        ⟨fun q => endpointMixedPathCoefficient zero_le_one (Kmix q) (Ωmix q), rfl,
          fun i q _ => mixedPathCoefficient_hasSpatialDerivative zero_le_one _ _ _ _ _
            (hKd i q) (hΩd i q)⟩
    have hfk : SpatialHolderHalf (N + 1)
        (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (eM w₁).val) := by
      rw [heMw]
      exact (hasSpatialHolderWords_iff_spatialHolderHalf (N + 1) _).mp
        ⟨fun q => -(P[1] (Lmix q)), rfl, fun i q _ => hasSpatialDerivative_neg
          (strongMixedLeray_hasSpatialDerivative hT _ _ _ (hLd i q))⟩
    have hwk := ((hHigher (N + 1) (by omega) hBk).1 w₁).mpr hfk
    exact hasSpatialHolderWords_of_succ
      ((hasSpatialHolderWords_iff_spatialHolderHalf (N + 1) w).mpr hwk)
  have hgc : ContinuousOn (fun t => (g t).val) I :=
    endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hg
  have hGRep : EndpointMixedRepresents w (fun t => (g t).val) :=
    EndpointMixedRepresents.of_spatialSlice hT.le hgc hRep
  have hFamilies (N : ℕ) : ∃ gN : List (Fin 3) → ℝ → V½,
      EqOn (gN []) (fun t => (g t).val) I ∧
      (∀ q : List (Fin 3), q.length ≤ N → ContDiffOn ℝ ∞ (gN q) I) ∧
      ∀ q : List (Fin 3), q.length < N → ∀ (i : Fin 3), ∀ t ∈ I,
        endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (gN q t)
          (gN (i :: q) t) := by
    obtain ⟨wN, hwN, hNFixed, hNProj, hND⟩ :=
      exists_mixedSolveSpatialJets_of_words hT Kmix Ωmix Lmix w hFixed hProjected hKd hΩd hLd
        N (hWwords N)
    obtain ⟨gN, hgN, hSpace⟩ :=
      exists_spatialJetTimeRecovery_of_family (n := ⊤) (N := N) hT Kmix Ωmix wN Lmix
        coordinateDirection hND Jk.curve Jω.curve Jl.curve
        (fun q _ => Jk.smooth q) (fun q _ => Jω.smooth q) (fun q _ => Jl.smooth q)
        (fun q _ => hLrep q) (fun q _ => ae_of_all _ (hKa q)) (fun q _ => ae_of_all _ (hΩa q))
        hNFixed hNProj hκ hKpos e he hE hEc.continuousOn
    have hcN (q : List (Fin 3)) (hq : q.length ≤ N) :
        ContinuousOn (fun t => (gN q t).val) I :=
      endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn
        (hgN q hq).1.continuousOn
    have hBaseRep : EndpointMixedRepresents w (fun t => (gN [] t).val) := by
      have h := EndpointMixedRepresents.of_spatialSlice hT.le (hcN [] (Nat.zero_le N))
        (hgN [] (Nat.zero_le N)).2.1
      rwa [hwN] at h
    refine ⟨fun q t => (gN q t).val, ?_, ?_, ?_⟩
    · exact EndpointMixedRepresents.eqOn hT (hcN [] (Nat.zero_le N)) hgc hBaseRep hGRep
    · intro q hq
      exact endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (hgN q hq).1
    · intro q hq i t ht
      simpa only [iteratedDerivWithin_zero, coordinateDirection] using
        hSpace 0 (by simp) t ht i q hq
  have hJoint : ContDiffOn ℝ ∞ (Function.uncurry (endpointPhysicalLabelVelocity g)) LSlab := by
    change ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (g z.1).val)
      LSlab
    exact contDiffOn_endpointLift_of_finite_spatialJets hT (f := fun t => (g t).val) hFamilies
  -- the solution of (4.9)
  let c := P ((1 : ℝ)⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨1, hT.le, le_rfl⟩)
    (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) w + Lmix []))
  let Ωw := (Ωmix []).coefficientMul w
  let Ωg (t : ℝ) := (Jω.curve [] t).coefficientMul (g t).val
  have hΩg : ContinuousOn Ωg I :=
    (HalfHolder.contDiffOn_coefficientMul (Jω.smooth [])).continuousOn.clm_apply hgc
  have hΩRep : EndpointMixedRepresents Ωw Ωg := hGRep.coefficientMul (ae_of_all _ (hΩa []))
  have hProj (t : ℝ) (ht : t ∈ I) :
      P (paperMeanIntegratedMomentum K Ω src g t) = c := by
    have h := hRecover ⟨t, ht⟩
    change P ((Jk.curve [] t).coefficientMul (g t).val) =
      c + P (HalfHolder.map (endpointPrimitiveEvaluation ⟨t, ht⟩) Ωw) -
        P (Jl.curve [] t) at h
    rw [endpointMixedPrimitive_eq_endpointPrimitive Ωw hΩg hΩRep ⟨t, ht⟩] at h
    have hprim : endpointPrimitive Ωg t =
        endpointPrimitive (fun r => (Ω r).coefficientMul (g r).val) t := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro r hr
      change (Jω.curve [] r).coefficientMul (g r).val = (Ω r).coefficientMul (g r).val
      rw [hΩeq ⟨hr.1, hr.2.trans ht.2⟩]
    rw [hKeq ht, hLeq ht, hprim] at h
    simp only [paperMeanIntegratedMomentum, map_add, map_sub, h]
    abel
  exact ⟨⟨g, c, hg, hEnd, hProj⟩, hJoint⟩

end

end TorusEuler.Paper.Lib.S34A

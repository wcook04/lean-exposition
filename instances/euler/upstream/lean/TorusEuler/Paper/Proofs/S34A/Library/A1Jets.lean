import TorusEuler.Paper.Proofs.S34A.Library.A1Base
import TorusEuler.EndpointJointHaarRegularity

/-! Glue for the smooth clause of **Theorem A.1** (package S34A): recovery of the time
jets of the spatial derivative words from a supplied instantaneous inverse family. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1JetSolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance a1JetSolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

set_option maxHeartbeats 2400000 in
/-- Time-smooth representatives of the spatial derivative words of the mixed solve,
with both endpoint conditions and the spatial derivative relations of their time jets
(the induction "`J(Ωv)` gains one time derivative from `v`" of
sections/appA_mean_regularity.tex:244–249). Parameterized copy of the glue lemma
`exists_endpointSpatialJetTimeRecovery` (EndpointJointHaarRegularity.lean:581): the
instantaneous inverse family `e` (Lemma A.2, case `H = ℝ³`) is an argument, and the
time recovery is `exists_mixedTimeRecovery_of_family`. -/
theorem exists_spatialJetTimeRecovery_of_family {I : Type*} {T μ Ainv : ℝ} (hT : 0 < T)
    {n : ℕ∞} {N : ℕ}
    (Kmix Ωmix : List I → MixedCoefficient(T)) (w Fmix : List I → Mixed(T)) (u : I → Vec3)
    (hDw : ∀ (i : I) (q : List I), q.length < N →
      endpointTorusHasSpatialDerivative (u i) (w q) (w (i :: q)))
    (K Ω : List I → ℝ → K½) (F : List I → ℝ → C½)
    (hK : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (K q) (Icc 0 T))
    (hΩ : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (Ω q) (Icc 0 T))
    (hF : ∀ q : List I, q.length ≤ N → ContDiffOn ℝ n (F q) (Icc 0 T))
    (hFmix : ∀ q : List I, q.length ≤ N → EndpointMixedRepresents (Fmix q) (F q))
    (hKmix : ∀ q : List I, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun t => HalfHolder.eval a (Kmix q) v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (K q t) (v t))
    (hΩmix : ∀ q : List I, q.length ≤ N → ∀ᵐ a ∂unitTorusMeasure, ∀ v : Paths(T),
      (fun t => HalfHolder.eval a (Ωmix q) v t) =ᵐ[μt T]
        fun t => HalfHolder.eval a (Ω q t) (v t))
    (hFixed : ∀ q : List I, q.length ≤ N → endpointStrongMixedLeray T (w q) = w q)
    (hProjected : ∀ q : List I, q.length ≤ N → endpointStrongMixedLeray T
      (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix q +
        endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (Kmix r) (Ωmix r)) w q) = 0)
    (hμ : 0 < μ)
    (hPos : ∀ t ∈ Icc 0 T, ∀ a v, μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a (K [] t) v, v⟫_ℝ)
    (e : ℝ → S ≃L[ℝ] S)
    (he : ∀ t ∈ Icc 0 T, ∀ v : S,
      e t v = endpointStrongSpatialProjection ((K [] t).coefficientMul v.val))
    (hE : ∀ t ∈ Icc 0 T, ‖((e t).symm : S →L[ℝ] S)‖ ≤ Ainv)
    (hEc : ContinuousOn (fun t => ((e t).symm : S →L[ℝ] S)) (Icc 0 T)) :
    ∃ g : List I → ℝ → S,
      (∀ q : List I, q.length ≤ N →
        ContDiffOn ℝ n (g q) (Icc 0 T) ∧
        (∀ᵐ t ∂μt T, endpointHalfHolderToL2 (g q t).val =
          endpointSpatialSlice (endpointMixedToJoint T (w q)) t) ∧
        endpointPrimitive (g q) 0 = 0 ∧ endpointPrimitive (g q) T = 0) ∧
      ∀ (m : ℕ), (m : ℕ∞) ≤ n → ∀ t ∈ Icc 0 T, ∀ (i : I) (q : List I), q.length < N →
        endpointTorusHasSpatialDerivative (u i)
          (iteratedDerivWithin m (fun r => (g q r).val) (Icc 0 T) t)
          (iteratedDerivWithin m (fun r => (g (i :: q) r).val) (Icc 0 T) t) := by
  classical
  let : CompleteSpace S := isClosed_endpointHalfHolderSolenoidal.completeSpace_coe
  let P := endpointStrongSpatialProjection
  let Kops (q : List I) (t : ℝ) : S →L[ℝ] C½ :=
    (K q t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  let Ωops (q : List I) (t : ℝ) : S →L[ℝ] C½ :=
    (Ω q t).coefficientMul.comp endpointHalfHolderSolenoidal.subtypeL
  have hKops (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (Kops q) (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul (hK q hq)).clm_comp contDiffOn_const
  have hΩops (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (Ωops q) (Icc 0 T) :=
    (HalfHolder.contDiffOn_coefficientMul (hΩ q hq)).clm_comp contDiffOn_const
  have hK0 := hK [] (Nat.zero_le N)
  have heC := contDiffOn_endpointCompressedCoefficient hK0 P he
  let Good (q : List I) (g : ℝ → S) : Prop :=
    ContDiffOn ℝ n g (Icc 0 T) ∧
      (∀ᵐ t ∂μt T, endpointHalfHolderToL2 (g t).val =
        endpointSpatialSlice (endpointMixedToJoint T (w q)) t) ∧
      endpointPrimitive g 0 = 0 ∧ endpointPrimitive g T = 0
  have hMain (m : ℕ) : ∀ q : List I, q.length = m → q.length ≤ N → ∃ g, Good q g := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro q hqm hq
      have hLower (l : List I) (hl : l.length < q.length) : ∃ g, Good l g :=
        ih l.length (by omega) l rfl (by omega)
      let g (l : List I) : ℝ → S :=
        if hl : l.length < q.length then Classical.choose (hLower l hl) else fun _ => 0
      have hg (l : List I) (hl : l.length < q.length) : Good l (g l) := by
        simpa only [g, dite_eq_left hl] using Classical.choose_spec (hLower l hl)
      have hgrep (l : List I) (hl : l.length < q.length) :
          EndpointMixedRepresents (w l) (fun t => (g l t).val) :=
        EndpointMixedRepresents.of_spatialSlice hT.le
          (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn
            (hg l hl).1.continuousOn) (hg l hl).2.1
      let corrK := endpointTemporalSpatialCorrection Kops g q
      let corrΩ := endpointTemporalSpatialCorrection Ωops g q
      have hkc : ContDiffOn ℝ n corrK (Icc 0 T) :=
        contDiffOn_endpointTemporalSpatialCorrection Kops g q
          (fun l hl => hKops l (hl.trans hq)) (fun l hl => (hg l hl).1)
      have hωc : ContDiffOn ℝ n corrΩ (Icc 0 T) :=
        contDiffOn_endpointTemporalSpatialCorrection Ωops g q
          (fun l hl => hΩops l (hl.trans hq)) (fun l hl => (hg l hl).1)
      have hKrep : EndpointMixedRepresents (endpointMixedCorrection Kmix w q) corrK :=
        EndpointMixedRepresents.spatialCorrection Kmix K w g q hgrep
          (fun l hl => hKmix l (hl.trans hq))
      have hΩrep : EndpointMixedRepresents (endpointMixedCorrection Ωmix w q) corrΩ :=
        EndpointMixedRepresents.spatialCorrection Ωmix Ω w g q hgrep
          (fun l hl => hΩmix l (hl.trans hq))
      let F₁ (t : ℝ) := F q t + corrK t - endpointPrimitive corrΩ t
      let Fmix₁ := Fmix q + endpointMixedCorrection Kmix w q -
        endpointMixedIntegration hT.le (endpointMixedCorrection Ωmix w q)
      have hΩPrimitive : ContDiffOn ℝ n (endpointPrimitive corrΩ) (Icc 0 T) := by
        refine contDiffOn_iff_forall_nat_le.mpr fun m hm => ?_
        exact (contDiffOn_endpointPrimitive_succ hT
          (contDiffOn_iff_forall_nat_le.mp hωc m hm)).of_le le_self_add
      have hF₁ : ContDiffOn ℝ n F₁ (Icc 0 T) :=
        ((hF q hq).add hkc).sub hΩPrimitive
      have hF₁rep : EndpointMixedRepresents Fmix₁ F₁ :=
        ((hFmix q hq).add hKrep).sub (hΩrep.integration hT.le hωc.continuousOn)
      have hProjected₁ : endpointStrongMixedLeray T
          (endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix₁) = 0 := by
        have hProj := hProjected q hq
        rw [endpointMixedCorrection_pathCoefficient hT.le Kmix Ωmix w q] at hProj
        convert hProj using 2
        dsimp only [Fmix₁]
        abel
      obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hF₁.continuousOn
      obtain ⟨z, hzc, hzEq, hzRep, hz0, hzT, _⟩ := exists_mixedTimeRecovery_of_family hT
        (Kmix []) (Ωmix []) (w q) Fmix₁ (K []) F₁ (hFixed q hq) hProjected₁
        hμ hPos e he hE hEc hF₁.continuousOn hM₁
        (ae_endpointMixedCoefficient_spatialSlice_of_pathAction (K []) (Kmix [])
          hK0.continuousOn (hKmix [] (Nat.zero_le N)) (w q))
        (hF₁rep.spatialSlice hT.le hF₁.continuousOn)
      let Jz := (Ωmix []).coefficientMul (w q)
      let residual := endpointMixedProductOperator hT.le (Kmix []) (Ωmix []) (w q) + Fmix₁
      let c := P (T⁻¹ • HalfHolder.map (endpointPrimitiveEvaluation ⟨T, hT.le, le_rfl⟩) residual)
      have hΩzC : ContinuousOn (fun t => Ωops [] t (z t)) (Icc 0 T) :=
        (hΩops [] (Nat.zero_le N)).continuousOn.clm_apply hzc
      have hzPath : EndpointMixedRepresents (w q) (fun t => (z t).val) :=
        EndpointMixedRepresents.of_spatialSlice hT.le
          (endpointHalfHolderSolenoidal.subtypeL.continuous.comp_continuousOn hzc) hzRep
      have hΩzPath : EndpointMixedRepresents Jz (fun t => Ωops [] t (z t)) :=
        hzPath.coefficientMul (hΩmix [] (Nat.zero_le N))
      have hzCn : ContDiffOn ℝ n z (Icc 0 T) := by
        refine contDiffOn_iff_forall_nat_le.mpr fun m hm => ?_
        apply contDiffOn_endpointVelocity_of_integrated hT P c
          (contDiffOn_iff_forall_nat_le.mp heC m hm)
          (contDiffOn_iff_forall_nat_le.mp (hΩops [] (Nat.zero_le N)) m hm)
          (contDiffOn_iff_forall_nat_le.mp hF₁ m hm) hzc
        intro t ht
        rw [he t ht, ← endpointMixedPrimitive_eq_endpointPrimitive Jz hΩzC hΩzPath ⟨t, ht⟩]
        exact hzEq ⟨t, ht⟩
      exact ⟨z, hzCn, hzRep, hz0, hzT⟩
  choose g hg using fun q (hq : q.length ≤ N) => hMain q.length q rfl hq
  let G (q : List I) (t : ℝ) := if hq : q.length ≤ N then g q hq t else 0
  have hG (q : List I) (hq : q.length ≤ N) : Good q (G q) := by
    simpa only [G, dite_eq_left hq] using hg q hq
  let V (q : List I) (t : ℝ) : C½ := (G q t).val
  have hV (q : List I) (hq : q.length ≤ N) : ContDiffOn ℝ n (V q) (Icc 0 T) :=
    endpointHalfHolderSolenoidal.subtypeL.contDiff.comp_contDiffOn (hG q hq).1
  have hSpatial := endpointRecoveredSpatialHierarchy hT w V u N hDw
    (fun q hq => (hV q hq).continuousOn) (fun q hq => (hG q hq).2.1)
  refine ⟨G, hG, ?_⟩
  intro m hm t ht i q hq
  exact endpointTorusHasSpatialDerivative_iteratedDerivWithin hT (u i)
    (contDiffOn_iff_forall_nat_le.mp (hV q hq.le) m hm)
    (contDiffOn_iff_forall_nat_le.mp (hV (i :: q) (Nat.succ_le_of_lt hq)) m hm)
    (fun r hr => hSpatial r hr i q hq) m le_rfl t ht

end

end TorusEuler.Paper.Lib.S34A

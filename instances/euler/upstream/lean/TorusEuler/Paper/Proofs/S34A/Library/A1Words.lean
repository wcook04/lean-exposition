import TorusEuler.Paper.Proofs.S34A.Library.A1Jets
import TorusEuler.PaperAppendixAFreezingHolder

/-! Glue for the smooth clause of **Theorem A.1** (package S34A): the spatial derivative
words of a solution of `P Q (B v) = f` that is already known to be `C^{k,1/2}` in space
(by the higher-order assertion of Lemma A.2) satisfy the differentiated equations with
the Leibniz commutators. This only differentiates an identity; the regularity itself
comes from Lemma A.2. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S34A

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "μt" T => volume.restrict (Ioc (0 : ℝ) T)
local notation "Paths(" T ")" => Lp Vec3 2 (μt T)
local notation "Mixed(" T ")" => HalfHolder A Paths(T)
local notation "MixedCoefficient(" T ")" => HalfHolder A (Paths(T) →L[ℝ] Paths(T))
local notation "PathOp(" T ")" => (Paths(T) →L[ℝ] Paths(T))
local notation "P[" T "]" => endpointStrongMixedLeray T

section Derivatives

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Spatial derivatives along a direction are unique. -/
theorem hasSpatialDerivative_unique {u : Vec3} {f df df' : HalfHolder A E}
    (h : endpointTorusHasSpatialDerivative u f df)
    (h' : endpointTorusHasSpatialDerivative u f df') : df = df' := by
  apply HalfHolder.ext
  intro a
  simpa only [zero_smul, toUnitTorus_zero, add_zero] using (h a 0).unique (h' a 0)

/-- Spatial derivatives of a sum. -/
theorem hasSpatialDerivative_add {u : Vec3} {f g df dg : HalfHolder A E}
    (hf : endpointTorusHasSpatialDerivative u f df)
    (hg : endpointTorusHasSpatialDerivative u g dg) :
    endpointTorusHasSpatialDerivative u (f + g) (df + dg) := by
  intro a s
  have h := (hf a s).add (hg a s)
  simp only [map_add]
  exact h

/-- Spatial derivatives of a negative. -/
theorem hasSpatialDerivative_neg {u : Vec3} {f df : HalfHolder A E}
    (hf : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (-f) (-df) := by
  intro a s
  have h := (hf a s).neg
  simp only [map_neg]
  exact h

/-- The product rule for pointwise coefficient multiplication. -/
theorem hasSpatialDerivative_coefficientMul {u : Vec3} {B dB : HalfHolder A (E →L[ℝ] E)}
    {f df : HalfHolder A E}
    (hB : endpointTorusHasSpatialDerivative u B dB)
    (hf : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (B.coefficientMul f)
      (dB.coefficientMul f + B.coefficientMul df) := by
  intro a s
  simpa only [map_add, HalfHolder.eval_coefficientMul] using (hB a s).clm_apply (hf a s)

end Derivatives

/-- The mixed path coefficient `K - JΩ` inherits spatial derivatives (copy of the private
`endpointMixedPathCoefficient_hasSpatialDerivative`, EndpointJointHaarRegularity.lean:458;
glue). -/
theorem mixedPathCoefficient_hasSpatialDerivative {T : ℝ} (hT : 0 ≤ T)
    (u : Vec3) (K Ω dK dΩ : MixedCoefficient(T))
    (hK : endpointTorusHasSpatialDerivative u K dK)
    (hΩ : endpointTorusHasSpatialDerivative u Ω dΩ) :
    endpointTorusHasSpatialDerivative u (endpointMixedPathCoefficient hT K Ω)
      (endpointMixedPathCoefficient hT dK dΩ) := by
  intro a s
  let J := (ContinuousLinearMap.mul ℝ (PathOp(T))) (endpointPrimitiveLp hT)
  have hJ : HasDerivAt (fun r : ℝ =>
      HalfHolder.eval (a + toUnitTorus (r • u)) (HalfHolder.map J Ω))
      (HalfHolder.eval (a + toUnitTorus (s • u)) (HalfHolder.map J dΩ)) s := by
    simpa only [HalfHolder.eval_map, Function.comp_def] using
      J.hasFDerivAt.comp_hasDerivAt s (hΩ a s)
  have h := (hK a s).sub hJ
  change HasDerivAt (fun r : ℝ => HalfHolder.eval (a + toUnitTorus (r • u)) K -
    HalfHolder.eval (a + toUnitTorus (r • u)) (HalfHolder.map J Ω)) _ s at h
  simpa only [endpointMixedPathCoefficient, map_sub, J] using h

/-- The mixed projection `P Q` commutes with spatial derivatives (glue: translation
invariance and the Haar bound of the projection). -/
theorem strongMixedLeray_hasSpatialDerivative {T : ℝ} (hT : 0 < T)
    (u : Vec3) (f df : Mixed(T)) (h : endpointTorusHasSpatialDerivative u f df) :
    endpointTorusHasSpatialDerivative u (P[T] f) (P[T] df) :=
  freezingProjection_preserves_torusDirectionalDerivative_of_haar_bound
    (H := Paths(T)) P[T] 1 zero_le_one
    (fun z => by simpa only [one_mul] using endpointStrongMixedLeray_haar_norm_le hT z)
    u (fun r z => endpointStrongMixedLeray_torusTranslate T (toUnitTorus (r • u)) z) f df h

/-- Coordinate words through order `N + 1` give coordinate words through order `N`. -/
theorem hasSpatialHolderWords_of_succ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {N : ℕ} {f : HalfHolder A E} (h : HasSpatialHolderWords (N + 1) f) :
    HasSpatialHolderWords N f := by
  obtain ⟨w, hw, hd⟩ := h
  exact ⟨w, hw, fun i t ht => hd i t (by omega)⟩

set_option maxHeartbeats 1600000 in
/-- The spatial derivative words of a solution `v` of the projected mixed equation
(TeX proof of Theorem A.1, sections/appA_mean_regularity.tex:242–244), when `v` is known
to have coordinate derivative words through order `N` (from the higher-order assertion
of Lemma A.2): each word is fixed by `P Q` and solves the differentiated projected
equation with the Leibniz commutators `endpointMixedCorrection`. Proof: differentiate
the equation of the previous word along a coordinate direction (product rule,
`P Q` commutes with spatial derivatives) and compare derivatives. This replaces, in the
proof of A.1, the library bootstrap `endpointStrongMixedLeray_allSpatialDerivatives`
(content of Lemma A.2), whose role is taken by Lemma A.2 itself. -/
theorem exists_mixedSolveSpatialJets_of_words {T : ℝ} (hT : 0 < T)
    (K Ω : List (Fin 3) → MixedCoefficient(T)) (F : List (Fin 3) → Mixed(T)) (v : Mixed(T))
    (hv : P[T] v = v)
    (hProjected : P[T] (endpointMixedProductOperator hT.le (K []) (Ω []) v + F []) = 0)
    (hK : ∀ (i : Fin 3) (q : List (Fin 3)),
      endpointTorusHasSpatialDerivative (coordinateDirection i) (K q) (K (i :: q)))
    (hΩ : ∀ (i : Fin 3) (q : List (Fin 3)),
      endpointTorusHasSpatialDerivative (coordinateDirection i) (Ω q) (Ω (i :: q)))
    (hF : ∀ (i : Fin 3) (q : List (Fin 3)),
      endpointTorusHasSpatialDerivative (coordinateDirection i) (F q) (F (i :: q)))
    (N : ℕ) (hWords : HasSpatialHolderWords N v) :
    ∃ w : List (Fin 3) → Mixed(T), w [] = v ∧
      (∀ q : List (Fin 3), q.length ≤ N → P[T] (w q) = w q) ∧
      (∀ q : List (Fin 3), q.length ≤ N → P[T]
        (endpointMixedProductOperator hT.le (K []) (Ω []) (w q) + F q +
          endpointMixedCorrection (fun r => endpointMixedPathCoefficient hT.le (K r) (Ω r)) w q) =
            0) ∧
      (∀ (i : Fin 3) (q : List (Fin 3)), q.length < N →
        endpointTorusHasSpatialDerivative (coordinateDirection i) (w q) (w (i :: q))) := by
  obtain ⟨w, hw0, hD⟩ := hWords
  let B (q : List (Fin 3)) := endpointMixedPathCoefficient hT.le (K q) (Ω q)
  let f (q : List (Fin 3)) := -(P[T] (F q))
  have hB (i : Fin 3) (q : List (Fin 3)) :
      endpointTorusHasSpatialDerivative (coordinateDirection i) (B q) (B (i :: q)) :=
    mixedPathCoefficient_hasSpatialDerivative hT.le _ _ _ _ _ (hK i q) (hΩ i q)
  have hf (i : Fin 3) (q : List (Fin 3)) :
      endpointTorusHasSpatialDerivative (coordinateDirection i) (f q) (f (i :: q)) :=
    hasSpatialDerivative_neg (strongMixedLeray_hasSpatialDerivative hT _ _ _ (hF i q))
  have hMain : ∀ q : List (Fin 3), q.length ≤ N →
      P[T] (w q) = w q ∧
        P[T] ((B []).coefficientMul (w q)) = f q - P[T] (endpointMixedCorrection B w q) := by
    intro q
    induction q with
    | nil =>
      intro _
      refine ⟨by rw [hw0]; exact hv, ?_⟩
      have hp := hProjected
      rw [map_add, ← endpointMixedPathCoefficient_coefficientMul hT.le (K []) (Ω [])] at hp
      simp only [endpointMixedCorrection, endpointMixedCorrectionPairs, List.map_nil,
        List.sum_nil, map_zero, sub_zero, hw0]
      exact eq_neg_of_add_eq_zero_left hp
    | cons i t ih =>
      intro hq
      simp only [List.length_cons] at hq
      obtain ⟨hfix, heq⟩ := ih (by omega)
      have hDt := hD i t (by omega)
      -- the new word is fixed by `P Q`
      have hPD := strongMixedLeray_hasSpatialDerivative hT _ _ _ hDt
      rw [hfix] at hPD
      have hfix' : P[T] (w (i :: t)) = w (i :: t) := hasSpatialDerivative_unique hPD hDt
      refine ⟨hfix', ?_⟩
      -- differentiate the equation of `t`
      let dc := ((endpointMixedCorrectionPairs t).map fun p =>
        (B (i :: p.1)).coefficientMul (w p.2) + (B p.1).coefficientMul (w (i :: p.2))).sum
      have hc : endpointTorusHasSpatialDerivative (coordinateDirection i)
          (endpointMixedCorrection B w t) dc :=
        endpointMixedCorrection_hasSpatialDerivative B w coordinateDirection i t
          (fun s _ => hB i s) (fun s hs => hD i s (by omega))
      have hX := hasSpatialDerivative_add
        (hasSpatialDerivative_coefficientMul (hB i []) hDt) hc
      have hPX := strongMixedLeray_hasSpatialDerivative hT _ _ _ hX
      have hEqt : P[T] ((B []).coefficientMul (w t) + endpointMixedCorrection B w t) = f t := by
        rw [map_add, heq]
        abel
      rw [hEqt] at hPX
      have hd := hasSpatialDerivative_unique hPX (hf i t)
      have hrow : endpointMixedCorrection B w (i :: t) = (B [i]).coefficientMul (w t) + dc :=
        endpointMixedCorrectionPairs_sum_cons i t fun p => (B p.1).coefficientMul (w p.2)
      rw [hrow, ← hd]
      simp only [map_add]
      abel
  refine ⟨w, hw0, fun q hq => (hMain q hq).1, ?_, fun i q hq => hD i q hq⟩
  intro q hq
  apply endpointProjectedMixedResidual_zero_of_spatialHierarchy hT.le K Ω w F q
  exact (hMain q hq).2

end

end TorusEuler.Paper.Lib.S34A

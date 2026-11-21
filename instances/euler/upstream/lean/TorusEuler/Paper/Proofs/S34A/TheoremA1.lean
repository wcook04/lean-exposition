import TorusEuler.Paper.Proofs.S34A.Library.A1Smooth
import TorusEuler.PaperAppendixARecovery

/-! Conditional proof of **Theorem A.1** of the latest manuscript (package S34A), from
**Lemma A.2**. -/

open Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "I" => Icc (0 : ℝ) 1
local notation "Path" => Lp Vec3 2 (volume.restrict (Ioc (0 : ℝ) 1))
local notation "P[" T "]" => endpointStrongMixedLeray T
local notation "W[" T "]" => freezingFixedSpace (P[T])

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance proofA1SolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance proofA1SolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

namespace Lib.S34A

/-- The arithmetic of the constant in (A.3): with `As, Am ≤ C_A (4Q)^{p_A}` (the two
inverses of Lemma A.2) and a coefficient cost at most `8Q`, the recovery budget is at most
`C Q^{2 p_A + 1}`. -/
theorem budget_le_power {Q CA Ps Pm As Am cost : ℝ} {pA : ℕ} (hQ : 1 ≤ Q) (hCA : 0 ≤ CA)
    (hPs : 0 ≤ Ps) (hPm : 0 ≤ Pm) (hAm0 : 0 ≤ Am) (hcost0 : 0 ≤ cost)
    (hAs : As ≤ CA * (4 * Q) ^ pA) (hAm : Am ≤ CA * (4 * Q) ^ pA) (hcost : cost ≤ 8 * Q) :
    As * Ps * (2 + cost * (Am * Pm)) ≤
      (CA * 4 ^ pA * Ps * (2 + 8 * CA * 4 ^ pA * Pm)) * Q ^ (2 * pA + 1) := by
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  rw [mul_pow] at hAs hAm
  have h1 : As * Ps ≤ CA * 4 ^ pA * Ps * Q ^ pA := by
    calc
      _ ≤ (CA * (4 ^ pA * Q ^ pA)) * Ps := mul_le_mul_of_nonneg_right hAs hPs
      _ = _ := by ring
  have h2 : cost * (Am * Pm) ≤ 8 * CA * 4 ^ pA * Pm * Q ^ (pA + 1) := by
    calc
      _ ≤ (8 * Q) * ((CA * (4 ^ pA * Q ^ pA)) * Pm) :=
        mul_le_mul hcost (mul_le_mul_of_nonneg_right hAm hPm) (mul_nonneg hAm0 hPm)
          (by positivity)
      _ = _ := by ring
  have hQp : 1 ≤ Q ^ (pA + 1) := one_le_pow₀ hQ
  have h3 : 2 + cost * (Am * Pm) ≤ (2 + 8 * CA * 4 ^ pA * Pm) * Q ^ (pA + 1) := by
    nlinarith
  calc
    _ ≤ (CA * 4 ^ pA * Ps * Q ^ pA) * ((2 + 8 * CA * 4 ^ pA * Pm) * Q ^ (pA + 1)) :=
      mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _ := by rw [show 2 * pA + 1 = pA + (pA + 1) by ring, pow_add]; ring

end Lib.S34A

set_option maxHeartbeats 8000000 in
/-- Proof of **Theorem A.1** (`cc:holder:linear`, sections/appA_mean_regularity.tex:26–41),
following "Proof of Theorem A.1" at sections/appA_mean_regularity.tex:199–250 with the
reduction at :43–64. The hypothesis `hA_2` (Lemma A.2) is used three times, where the TeX
uses it, except for the spatial higher-order clause in the smooth case (item 3):

1. (:200–207) `hA_2`, case `H = L²(I;ℝ³)`, `R = P Q`, applied to the mixed coefficient
   `B = K - JΩ` (Lipschitz constant `2K₁ + 2Ω₁`, coercivity `μ` from (A.2) through
   `endpointMixedPathCoefficient_inner_eq_sobolevEnergy`, as at appA:53–61) gives the
   isomorphism `eM` and the unique solution `v = eM⁻¹(-P Q L)`, with (A.8).
2. (:223–228) `hA_2`, case `H = ℝ³`, `R = P`, applied to `B = K(t)` with the ellipticity
   `κ` of (A.1), gives the fixed-time inverses `S(t)⁻¹`, uniformly bounded by `C Q^p`;
   continuity in `t` by the resolvent identity (`exists_instantaneousFamily_of_pointwise`).
   With them `Lib.S34A.exists_unitSolve_of_inverses` (a copy, for `T = 1` and with the
   inverses as arguments, of the A.1 own-content lemma
   `paperMeanIntegratedInverse_of_coercivity`; see its docstring) recovers `c`, (A.9), the continuous
   representative with both endpoint conditions, uniqueness and the bound (A.3)
   (`Lib.S34A.budget_le_power`: `C = C_A 4^{p_A} ‖P‖ (2 + 8 C_A 4^{p_A} ‖P Q‖)`,
   `p = 2 p_A + 1`). The pressure gradient comes from `exists_potential` (:238–240).
3. (:242–249) the smooth clause (`Lib.S34A.exists_smoothSolution_of_freezing`): the
   higher-order assertion of `hA_2` in the mixed case gives `v ∈ C^{k,1/2}_a(L²_t)` for every
   `k` (the coefficient `K - JΩ` and the datum `P Q L` are `C^{k,1/2}`), and the fixed-time
   inverses of `hA_2` (case `H = ℝ³`), smooth in time by the resolvent identity, recover
   all time derivatives of every spatial derivative word; uniqueness identifies the smooth
   solution with the one above, and `Lib.S34A.smoothData_conclusions` gives smoothness of
   `z`, `c`, `∇φ`.
   Departure from the TeX: at :244–246 the TeX gets `v ∈ C(I;C^{k,1/2})` and the smoothness
   of `S(t)⁻¹` on `P C^{k,1/2}` from the higher-order clause of Lemma A.2 with `H = ℝ³`. The
   Lean does not use that clause (it is discarded in `exists_solenoidalInverse_of_freezing`).
   It differentiates the projected equation along each spatial derivative word
   (`exists_mixedSolveSpatialJets_of_words`, Leibniz commutator sources) and recovers every
   word with the base-clause inverses on `P C^{0,1/2}`
   (`exists_spatialJetTimeRecovery_of_family`). The reason is the representation: joint
   smoothness is assembled from time-smooth `C^{0,1/2}` curves of all spatial derivative
   words (`contDiffOn_endpointLift_of_finite_spatialJets`), so `C^{0,1/2}` inverses suffice.

The symmetry of `K` and skewness of `Ω` are not needed (as in the TeX proof, where they
only motivate (A.2)). -/
theorem Proof.theorem_A_1_of (hA_2 : Statement.lemma_A_2) : Statement.theorem_A_1 := by
  obtain ⟨CA, pA, hCA, hSp, hMx⟩ := hA_2
  let Ps := ‖endpointStrongSpatialProjection‖
  let Pm := ‖P[1]‖
  have hPs : 0 ≤ Ps := endpointStrongSpatialProjection.opNorm_nonneg
  have hPm : 0 ≤ Pm := (P[1]).opNorm_nonneg
  refine ⟨CA * 4 ^ pA * Ps * (2 + 8 * CA * 4 ^ pA * Pm), 2 * pA + 1, by positivity, ?_⟩
  intro K Ω κ μ K₀ K₁ Ω₀ Ω₁ _ _ hK hΩ hκ hPos hμ hEnergy Q L hL
  have hT : (0 : ℝ) < 1 := zero_lt_one
  have hKc : ContinuousOn K I := hK.2.2.1
  have hΩc : ContinuousOn Ω I := hΩ.2.2.1
  have hK₀ := hK.1
  have hK₁ := hK.2.1
  have hΩ₀ := hΩ.1
  have hΩ₁ := hΩ.2.1
  have hκi := inv_nonneg.mpr hκ.le
  have hμi := inv_nonneg.mpr hμ.le
  have hQ : 1 ≤ Q := by dsimp only [Q]; linarith
  have capsK := endpointHalfHolderCaps_of_lift_gradient (T := 1) hK₀ hK₁ K
    (fun t x => HalfHolder.eval (toUnitTorus x) (K t)) (fun _ _ _ => rfl)
    (fun t ht => (hK.2.2.2 t ht).1) (fun t ht x => ((hK.2.2.2 t ht).2 x).1)
    (fun t ht x => ((hK.2.2.2 t ht).2 x).2)
  have capsΩ := endpointHalfHolderCaps_of_lift_gradient (T := 1) hΩ₀ hΩ₁ Ω
    (fun t x => HalfHolder.eval (toUnitTorus x) (Ω t)) (fun _ _ _ => rfl)
    (fun t ht => (hΩ.2.2.2 t ht).1) (fun t ht x => ((hΩ.2.2.2 t ht).2 x).1)
    (fun t ht x => ((hΩ.2.2.2 t ht).2 x).2)
  have hCK : 0 ≤ K₀ + 2 * K₁ := by positivity
  have hCΩ : 0 ≤ Ω₀ + 2 * Ω₁ := by positivity
  have hLK : 0 ≤ 2 * K₁ := by positivity
  have hLΩ : 0 ≤ 2 * Ω₁ := by positivity
  obtain ⟨Kmix, hKmixN, hKa⟩ := exists_endpointMixedCoefficient_of_timeCurve hCK K hKc capsK.1
  obtain ⟨Ωmix, hΩmixN, hΩa⟩ := exists_endpointMixedCoefficient_of_timeCurve hCΩ Ω hΩc capsΩ.1
  -- step 1: the mixed isomorphism of Lemma A.2 (case `H = L²(I;ℝ³)`)
  let B := endpointMixedPathCoefficient zero_le_one Kmix Ωmix
  have hBLip (a b : A) :
      ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ (2 * K₁ + 1 * (2 * Ω₁)) * dist a b :=
    norm_endpointMixedPathCoefficient_sub_le zero_le_one Kmix Ωmix
      (norm_endpointMixedCoefficient_sub_le_of_timeSlices hLK Kmix K capsK.2 hKa)
      (norm_endpointMixedCoefficient_sub_le_of_timeSlices hLΩ Ωmix Ω capsΩ.2 hΩa) a b
  have hBpos (a : A) (v : Path) (hv : endpointIntegral 1 v = 0) :
      μ * ‖v‖ ^ 2 ≤ ⟪HalfHolder.eval a B v, v⟫_ℝ := by
    rw [endpointMixedPathCoefficient_inner_eq_sobolevEnergy K Ω Kmix Ωmix a v hv
      (hKa a v) (hΩa a v)]
    exact hEnergy a v hv
  have hLmix : 0 ≤ 2 * K₁ + 1 * (2 * Ω₁) := by positivity
  obtain ⟨eM, heM, hbM, -⟩ := hMx B μ _ hμ hLmix hBLip hBpos
  have hBsup : ‖B.val.1‖ ≤ (K₀ + 2 * K₁) + 1 * (Ω₀ + 2 * Ω₁) :=
    norm_endpointMixedPathCoefficient_sup_le zero_le_one Kmix Ωmix hCK hCΩ
      ((HalfHolder.norm_le_iff hCK).mp hKmixN).1 ((HalfHolder.norm_le_iff hCΩ).mp hΩmixN).1
  let Am := CA * (2 + μ⁻¹ + ‖B.val.1‖ + (2 * K₁ + 1 * (2 * Ω₁))) ^ pA
  have hAm₀ : 0 ≤ Am := by positivity
  have hAm : ‖(eM.symm : W[1] →L[ℝ] W[1])‖ ≤ Am :=
    Lib.S34A.norm_symm_le_of_lower_bound eM hAm₀ hbM
  -- step 2: the fixed-time inverses of Lemma A.2 (case `H = ℝ³`)
  let As := CA * (2 + κ⁻¹ + (K₀ + 2 * K₁) + 2 * K₁) ^ pA
  have hAs₀ : 0 ≤ As := by positivity
  have hAt : ∀ t ∈ I, ∃ e : S ≃L[ℝ] S,
      (∀ v : S, e v = endpointStrongSpatialProjection ((K t).coefficientMul v.val)) ∧
      ‖(e.symm : S →L[ℝ] S)‖ ≤ As := by
    intro t ht
    obtain ⟨e, he, hb⟩ := Lib.S34A.exists_solenoidalInverse_of_freezing hCA hκ hLK
      (hSp (K t) κ (2 * K₁) hκ hLK (capsK.2 t ht) (hPos t ht))
    refine ⟨e, he, hb.trans ?_⟩
    have h0 : 0 ≤ 2 + κ⁻¹ + ‖(K t).val.1‖ + 2 * K₁ := by positivity
    have h1 : ‖(K t).val.1‖ ≤ K₀ + 2 * K₁ := (norm_fst_le (K t).val).trans (capsK.1 t ht)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (by linarith) pA) hCA
  obtain ⟨eS, heS, hAs, hEc⟩ :=
    Lib.S34A.exists_instantaneousFamily_of_pointwise (n := 0) (contDiffOn_zero.mpr hKc) hAt
  obtain ⟨s, hStart, hDeriv, hBound, hUnique⟩ :=
    Lib.S34A.exists_unitSolve_of_inverses hκ Kmix Ωmix hKc hΩc hKa hΩa hPos eS heS hAs
      hEc.continuousOn eM heM hAm L hL
  obtain ⟨φ, G, hGc, hG⟩ := s.exists_potential hKc hΩc hL
  -- the constant of (A.3)
  have hBudget : endpointPhysicalInverseBudget zero_le_one Kmix Ωmix As Am ≤
      (CA * 4 ^ pA * Ps * (2 + 8 * CA * 4 ^ pA * Pm)) * Q ^ (2 * pA + 1) := by
    refine (endpointPhysicalInverseBudget_le_of_timeSlices zero_le_one hAs₀ hAm₀ Kmix Ωmix K Ω
      hKc hΩc (ae_of_all _ hKa) (ae_of_all _ hΩa)).trans ?_
    have hKn := endpointClosedTimeNorm_le zero_le_one capsK.1
    have hΩn := endpointClosedTimeNorm_le zero_le_one capsΩ.1
    have hKn₀ := endpointClosedTimeNorm_nonneg zero_le_one K
    have hΩn₀ := endpointClosedTimeNorm_nonneg zero_le_one Ω
    apply Lib.S34A.budget_le_power hQ hCA hPs hPm hAm₀ (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (by dsimp only [Q]; linarith) pA) hCA
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
        (by dsimp only [Q]; linarith) pA) hCA
    · dsimp only [Q]; linarith
  have hLn : 0 ≤ endpointClosedTimeNorm 1 L := endpointClosedTimeNorm_nonneg zero_le_one L
  refine ⟨endpointPrimitive s.velocity, s.velocity, s.constant, φ, G,
    ⟨s.continuous, hDeriv, hStart, s.terminal, hGc,
      fun t ht => ⟨(hG t ht).1, (hG t ht).2.2.1⟩, fun t ht => (hG t ht).2.2.2⟩, ?_, ?_, ?_⟩
  · -- uniqueness (appA:239–240)
    intro z' v' c' φ' G' hs'
    obtain ⟨s', hv', hc', hz'⟩ := paperA1_solution_of_unprojected_equation K Ω L G' z' v' c' φ'
      hs'.initial hs'.terminal hs'.velocity_continuous hs'.displacement_deriv
      (fun t ht => (hs'.potential t ht).1) (fun t ht => (hs'.potential t ht).2) hs'.equation
    obtain ⟨hEq, hc⟩ := hUnique s'
    rw [hv'] at hEq hz'
    rw [hc'] at hc
    have hzEq : EqOn (endpointPrimitive v') (endpointPrimitive s.velocity) I := by
      intro t ht
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      exact fun r hr => hEq ⟨hr.1, hr.2.trans ht.2⟩
    refine ⟨fun t ht => (hz' ht).trans (hzEq ht), hEq, hc, ?_⟩
    intro t ht
    have hEqM : paperMeanIntegratedMomentum K Ω L v' t =
        paperMeanIntegratedMomentum K Ω L s.velocity t := by
      unfold paperMeanIntegratedMomentum
      rw [hEq ht]
      congr 2
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le ht.1]
      intro r hr
      change (Ω r).coefficientMul (v' r).val = (Ω r).coefficientMul (s.velocity r).val
      rw [hEq ⟨hr.1, hr.2.trans ht.2⟩]
    have h := (hs'.equation t ht).symm.trans (hEqM.trans (hG t ht).2.2.2)
    rw [hc] at h
    exact add_left_cancel h
  · -- the bound (A.3)
    calc
      _ ≤ endpointPhysicalInverseBudget zero_le_one Kmix Ωmix As Am *
          endpointClosedTimeNorm 1 L := hBound
      _ ≤ _ := mul_le_mul_of_nonneg_right hBudget hLn
  · -- smooth data (appA:242–249)
    intro hsK hsΩ hsL
    obtain ⟨s', hs'⟩ := Lib.S34A.exists_smoothSolution_of_freezing hCA hSp hMx hκ hμ hK hΩ hPos
      hEnergy hsK hsΩ hsL
    have hEq := (hUnique s').1
    have hJoint : ContDiffOn ℝ ∞
        (Function.uncurry (endpointPhysicalLabelVelocity s.velocity))
        (Set.prod (Icc (0 : ℝ) 1) (univ : Set Vec3)) := by
      exact hs'.congr fun z hz => by
        change HalfHolder.eval (toUnitTorus z.2) (s.velocity z.1).val =
          HalfHolder.eval (toUnitTorus z.2) (s'.velocity z.1).val
        rw [hEq hz.1]
    exact Lib.S34A.smoothData_conclusions s hΩc G (fun t ht => (hG t ht).2.2.2) hJoint hsK hsΩ
      hsL

end

end TorusEuler.Paper

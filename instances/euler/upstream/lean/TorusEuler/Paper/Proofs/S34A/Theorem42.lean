import TorusEuler.Paper.Proofs.S34A.Library.R42Coercive
import TorusEuler.Paper.Proofs.S34A.Library.R42Smooth
import TorusEuler.Paper.Proofs.S34A.Library.A1Inverses
import TorusEuler.PaperMeanFlowAdapter
import TorusEuler.PaperMeanPressureCompatibility

/-! Conditional proof of **Theorem 4.2** of the latest manuscript (package S34A), from
**Lemma 4.1**, **Theorem A.1** and **Lemma A.2**. -/

open MeasureTheory Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder A Vec3
local notation "K½" => HalfHolder A (Vec3 →L[ℝ] Vec3)
local notation "S" => endpointHalfHolderSolenoidal
local notation "P" => endpointStrongSpatialProjection
local notation "J(" T ")" => Icc (0 : ℝ) T
local notation "Slab(" T ")" => Set.prod (Icc (0 : ℝ) T) (univ : Set Vec3)

/-- Normed group structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance proof42SolenoidalNormedGroup : NormedAddCommGroup S := inferInstance
/-- Real normed space structure on the divergence-free subspace `S` (local shortcut for
instance search). -/
local instance proof42SolenoidalNormedSpace : NormedSpace ℝ S := inferInstance

namespace Lib.S34A

/-- Powers of a quantity bounded by `c S⁴` with `S ≥ 1`, absorbed in a larger power. -/
theorem pow_le_of_le_scale {x c Sc : ℝ} {n m : ℕ} (hx : 0 ≤ x) (hc : 0 ≤ c) (hS : 1 ≤ Sc)
    (h : x ≤ c * Sc ^ 4) (hnm : n ≤ m) : x ^ n ≤ c ^ n * Sc ^ (4 * m) := by
  calc
    x ^ n ≤ (c * Sc ^ 4) ^ n := pow_le_pow_left₀ hx h n
    _ = c ^ n * Sc ^ (4 * n) := by rw [mul_pow, ← pow_mul]
    _ ≤ c ^ n * Sc ^ (4 * m) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hS (by omega)) (pow_nonneg hc n)


/-- The body of `Statement.theorem_A_1` for given constants `C`, `p` (so that
`Statement.theorem_A_1 = ∃ C p, 0 ≤ C ∧ A1Body C p`); bookkeeping only. -/
def A1Body (C : ℝ) (p : ℕ) : Prop :=
  ∀ (K Ω : ℝ → K½) (κ μ K₀ K₁ Ω₀ Ω₁ : ℝ),
    (∀ t ∈ J(1), ∀ a, IsSelfAdjoint (HalfHolder.eval a (K t))) →
    (∀ t ∈ J(1), ∀ a, (HalfHolder.eval a (Ω t)).adjoint = -HalfHolder.eval a (Ω t)) →
    EndpointCoefficientC1Bound K K₀ K₁ → EndpointCoefficientC1Bound Ω Ω₀ Ω₁ →
    0 < κ → (∀ t ∈ J(1), ∀ a (w : Vec3), κ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) w, w⟫_ℝ) →
    0 < μ → EndpointSobolevEnergyBound K Ω μ →
    let Q : ℝ := 2 + κ⁻¹ + μ⁻¹ + K₀ + K₁ + Ω₀ + Ω₁
    ∀ L : ℝ → C½, ContinuousOn L J(1) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution 1 K Ω L z v c φ G ∧
        (∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution 1 K Ω L z' v' c' φ' G' →
          EqOn z' z J(1) ∧ EqOn v' v J(1) ∧ c' = c ∧ EqOn G' G J(1)) ∧
        endpointClosedTimeNorm 1 v ≤ C * Q ^ p * endpointClosedTimeNorm 1 L ∧
        (ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (K q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (Ω q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (L q.1)) Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
              Slab(1) ∧
            ContDiff ℝ ∞ (fun x : Vec3 => HalfHolder.eval (toUnitTorus x) (c : C½)) ∧
            ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (G q.1)) Slab(1))

/-- The parent of Section 4 as a `PaperMeanParent` (glue `exists_paperMeanParent_of_flow`;
the Eulerian gradient bound comes from the label bound through the flow inverse). -/
theorem parent42 {T : ℝ} {U : Velocity} {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L : ℝ} (hD : ∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L) :
    ∃ par : PaperMeanParent T D L, ∀ t ∈ J(T), ∀ (a : Vec3),
      par.F (t, toUnitTorus a) = fderiv ℝ (X 0 t) a ∧
        par.G (t, toUnitTorus a) = fderiv ℝ (X t 0) (X 0 t a) ∧
          par.M (t, toUnitTorus a) = fderiv ℝ (U t) (X 0 t a) ∧
            par.Mt (t, toUnitTorus a) =
              derivWithin (fun r => fderiv ℝ (U r) (X 0 r a)) (Icc 0 T) t := by
  have hT := hP.time_pos
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  obtain ⟨Lip, hLip⟩ :=
    exists_lipschitzWith_of_contDiffOn_periodic hT (hP.smooth.of_le (by simp)) hP.periodic
  have hLeul : ∀ t ∈ J(T), ∀ x, ‖fderiv ℝ (U t) x‖ ≤ L := by
    intro t ht x
    have h := hL t ht (X t 0 x)
    rwa [meanGradient, (hP.flow.inverse hLip h0 ht).2 x] at h
  exact exists_paperMeanParent_of_flow hT hP.flow hP.smooth hP.periodic hD hLeul hH

/-- Joint smoothness on the closed slab of the coefficients `K`, `Ω` of (4.1) along the
flow. -/
theorem lifts42 {T : ℝ} {U : Velocity} {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L : ℝ} (hD : ∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanKinetic X q.1 q.2) Slab(T) ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanVorticity U X q.1 q.2) Slab(T) := by
  obtain ⟨par, hpar⟩ := parent42 hP hH hD hL
  have hFs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanDeformation X q.1 q.2) Slab(T) :=
    par.deformation_smooth.congr fun q hq => ((hpar q.1 hq.1 q.2).1).symm
  have hMs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanGradient U X q.1 q.2) Slab(T) :=
    par.gradient_smooth.congr fun q hq => ((hpar q.1 hq.1 q.2).2.2.1).symm
  let Adj : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ[ℝ] (Vec3 →L[ℝ] Vec3) := ContinuousLinearMap.adjoint
  have hFadj : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => (meanDeformation X q.1 q.2).adjoint)
      Slab(T) := Adj.contDiff.comp_contDiffOn hFs
  have hkin : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanKinetic X q.1 q.2) Slab(T) :=
    hFadj.clm_comp hFs
  have hvor : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => meanVorticity U X q.1 q.2) Slab(T) :=
    hFadj.clm_comp (((Adj.contDiff.comp_contDiffOn hMs).sub hMs).clm_comp hFs)
  exact ⟨hkin, hvor⟩


set_option maxHeartbeats 20000000 in
/-- Part 1 of **Theorem 4.2** (sections/06b_mean_inverse.tex:175–184): for every source
`L ∈ C(I; C^{0,1/2})`, the rescaled Theorem A.1 (`hA1`) with coefficients `K(Tτ)`, `TΩ(Tτ)`,
ellipticity `D_-^{-2}` and the coercivity of `sobolevEnergy_of_hardy` (`h4_1`, Lemma 4.1, and
(4.6)) gives the unique solution of (4.9) on `[0,T]`, the bound `C Q^p ‖L‖`, and, for a
source whose rescaled lift is smooth, a smooth displacement. Of the smooth clause of `hA1`
only the smoothness of `z` is kept; the smoothness of `c` and of the gradient `G = ∇φ` is not
used (see `smooth42`). -/
theorem solve42 (h4_1 : Statement.lemma_4_1) {C1 : ℝ} {p1 : ℕ} (hC1 : 0 ≤ C1)
    (hA1 : A1Body C1 p1)
    {T : ℝ} {U : Velocity} {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L K₀ K₁ Ω₀ Ω₁ : ℝ} (hD1 : 1 ≤ D)
    (hD : ∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L)
    (hKv : ∀ t ∈ J(T), ∀ a, ‖meanKinetic X t a‖ ≤ K₀)
    (hKg : ∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (meanKinetic X t) a‖ ≤ K₁)
    (hΩv : ∀ t ∈ J(T), ∀ a, ‖meanVorticity U X t a‖ ≤ Ω₀)
    (hΩg : ∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (meanVorticity U X t) a‖ ≤ Ω₁)
    {K Ω : ℝ → K½}
    (hKe : ∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (K t) = meanKinetic X t a)
    (hΩe : ∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (Ω t) = meanVorticity U X t a) :
    ∀ src : ℝ → C½, ContinuousOn src J(T) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution T K Ω src z v c φ G ∧
        endpointClosedTimeNorm T v ≤
          C1 * (2 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + L) ^ 2))⁻¹ + K₀ + K₁ + Ω₀ + Ω₁) ^ p1 *
            endpointClosedTimeNorm T src ∧
        (∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution T K Ω src z' v' c' φ' G' →
          EqOn z' z J(T) ∧ EqOn v' v J(T) ∧ c' = c ∧ EqOn G' G J(T)) ∧
        (ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (src (T * q.1)))
            Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
            Slab(T)) := by
  intro src hsrc
  have hT := hP.time_pos
  have hT1 := hP.time_le_one
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.smooth.of_le (by simp)
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 h0 0)
  have hK0 : 0 ≤ K₀ := (norm_nonneg _).trans (hKv 0 h0 0)
  have hK1 : 0 ≤ K₁ := (norm_nonneg (fderiv ℝ (meanKinetic X 0) 0)).trans (hKg 0 h0 0)
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩv 0 h0 0)
  have hΩ1 : 0 ≤ Ω₁ := (norm_nonneg (fderiv ℝ (meanVorticity U X 0) 0)).trans (hΩg 0 h0 0)
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  obtain ⟨hkin, hvor⟩ := lifts42 hP hH hD hL
  have hslice {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Vec3 → E}
      (hf : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => f q.1 q.2) Slab(T)) {t : ℝ} (ht : t ∈ J(T)) :
      ContDiff ℝ ∞ (f t) :=
    contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hperK (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic fun x => meanKinetic X t x := by
    intro n x
    show meanKinetic X t (x + latticeVector n) = meanKinetic X t x
    rw [← hKe t ht, ← hKe t ht]
    exact spatiallyPeriodic_lift (K t) n x
  have hperΩ (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic fun x => meanVorticity U X t x := by
    intro n x
    show meanVorticity U X t (x + latticeVector n) = meanVorticity U X t x
    rw [← hΩe t ht, ← hΩe t ht]
    exact spatiallyPeriodic_lift (Ω t) n x
  have hKc : ContDiffOn ℝ ∞ K J(T) :=
    contDiffOn_curve_of_lift hT K _ hkin hperK hKe
  have hΩc : ContDiffOn ℝ ∞ Ω J(T) :=
    contDiffOn_curve_of_lift hT Ω _ hvor hperΩ hΩe
  have hGF (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      (meanDeformationInv X t x).comp (meanDeformation X t x) = ContinuousLinearMap.id ℝ Vec3 :=
    (hP.flow.labelDerivative_inverse hT hU2 hP.periodic h0 ht x).1
  -- the rescaled coefficients of Theorem A.1 (`τ = t/T`)
  have hmap : MapsTo (fun τ : ℝ => T * τ) J(1) J(T) := mapsTo_scale hT (mul_one T)
  let Kt : ℝ → K½ := fun τ => K (T * τ)
  let Ωt : ℝ → K½ := fun τ => T • Ω (T * τ)
  have hKte : ∀ τ ∈ J(1), ∀ x, HalfHolder.eval (toUnitTorus x) (Kt τ) = meanKinetic X (T * τ) x :=
    fun τ hτ x => hKe _ (hmap hτ) x
  have hΩte : ∀ τ ∈ J(1), ∀ x,
      HalfHolder.eval (toUnitTorus x) (Ωt τ) = T • meanVorticity U X (T * τ) x := by
    intro τ hτ x
    simp only [Ωt, map_smul, hΩe _ (hmap hτ) x]
  have hlin : Continuous (fun τ : ℝ => T * τ) := continuous_const.mul continuous_id
  have hsym : ∀ t ∈ J(1), ∀ a, IsSelfAdjoint (HalfHolder.eval a (Kt t)) := by
    intro t ht a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hKte t ht x]
    exact isSelfAdjoint_kineticForm _
  have hskew : ∀ t ∈ J(1), ∀ a,
      (HalfHolder.eval a (Ωt t)).adjoint = -HalfHolder.eval a (Ωt t) := by
    intro t ht a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hΩte t ht x]
    simp only [meanVorticity, map_smul, adjoint_vorticityForm, smul_neg]
  have hKC1 : EndpointCoefficientC1Bound Kt K₀ K₁ := by
    refine ⟨hK0, hK1, hKc.continuousOn.comp hlin.continuousOn hmap, fun t ht => ?_⟩
    intro k
    have hk : k = meanKinetic X (T * t) := funext (hKte t ht)
    rw [hk]
    exact ⟨(hslice hkin (hmap ht)).differentiable (by simp),
      fun x => ⟨hKv _ (hmap ht) x, hKg _ (hmap ht) x⟩⟩
  have hΩC1 : EndpointCoefficientC1Bound Ωt Ω₀ Ω₁ := by
    refine ⟨hΩ0, hΩ1, (hΩc.continuousOn.const_smul T).comp hlin.continuousOn hmap,
      fun t ht => ?_⟩
    intro k
    have hk : k = T • meanVorticity U X (T * t) := funext fun x => hΩte t ht x
    have hd := (hslice hvor (hmap ht)).differentiable (by simp)
    rw [hk]
    refine ⟨hd.const_smul T, fun x => ⟨?_, ?_⟩⟩
    · rw [Pi.smul_apply]
      refine (norm_smul_le T (meanVorticity U X (T * t) x)).trans ?_
      rw [Real.norm_of_nonneg hT.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) hT1).trans (hΩv _ (hmap ht) x)
    · rw [fderiv_const_smul (hd x) T]
      refine (ContinuousLinearMap.opNorm_smul_le T
        (fderiv ℝ (meanVorticity U X (T * t)) x)).trans ?_
      rw [Real.norm_of_nonneg hT.le]
      exact (mul_le_of_le_one_left (norm_nonneg _) hT1).trans (hΩg _ (hmap ht) x)
  have hκ : 0 < (D ^ 2)⁻¹ := by positivity
  have hell : ∀ t ∈ J(1), ∀ a (w : Vec3),
      (D ^ 2)⁻¹ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a (Kt t) w, w⟫_ℝ := by
    intro t ht a w
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hKte t ht x]
    exact kineticForm_elliptic hDpos (hGF _ (hmap ht) x) (hD _ (hmap ht) x) w
  have hμ : 0 < 1 / (2 * D ^ 2 * (1 + L) ^ 2) := by positivity
  -- (A.2) for the rescaled coefficients, from Lemma 4.1 and (4.6)
  have hE := sobolevEnergy_of_hardy h4_1 hP hH hD1 hD hL0 hL Kt Ωt hKte hΩte
  have hTinv : 0 < T⁻¹ := inv_pos.mpr hT
  have hTT : T⁻¹ * T = 1 := inv_mul_cancel₀ hT.ne'
  let Lt : ℝ → C½ := fun τ => src (T * τ)
  have hLt : ContinuousOn Lt J(1) := hsrc.comp hlin.continuousOn hmap
  obtain ⟨z₁, v₁, c, φ₁, G₁, hs₁, hu₁, hb₁, hsm₁⟩ :=
    hA1 Kt Ωt (D ^ 2)⁻¹ _ K₀ K₁ Ω₀ Ω₁ hsym hskew hKC1 hΩC1 hκ hell hμ hE Lt hLt
  have hback (t : ℝ) : T * (T⁻¹ * t) = t := mul_inv_cancel_left₀ hT.ne' t
  have hs := EndpointSystemSolution.congr
    (endpointSystemSolution_scale hTinv hTT hs₁) (K' := K) (Ω' := Ω) (src' := src)
    (fun t _ => by simp only [Kt, hback])
    (fun t _ => by simp only [Ωt, hback, smul_smul, inv_mul_cancel₀ hT.ne', one_smul])
    (fun t _ => by simp only [Lt, hback])
  refine ⟨_, _, c, _, _, hs, ?_, ?_, ?_⟩
  · calc
      _ ≤ endpointClosedTimeNorm 1 v₁ :=
        endpointClosedTimeNorm_scale_le hTinv hTT hT.le hs₁.velocity_continuous
      _ ≤ _ := hb₁
      _ ≤ C1 * (2 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + L) ^ 2))⁻¹ + K₀ + K₁ + Ω₀ + Ω₁) ^
            p1 * endpointClosedTimeNorm T src :=
        mul_le_mul_of_nonneg_left
          (endpointClosedTimeNorm_scale_le hT (mul_one T) zero_le_one hsrc)
          (by positivity)
  · intro z' v' c' φ' G' hs'
    obtain ⟨hz, hv, hc, hG⟩ := hu₁ _ _ _ _ _ (endpointSystemSolution_scale hT
      (mul_one T) hs')
    have ht1 {t : ℝ} (ht : t ∈ J(T)) : T⁻¹ * t ∈ J(1) :=
      mapsTo_scale hTinv hTT ht
    refine ⟨fun t ht => ?_, fun t ht => ?_, hc, fun t ht => ?_⟩
    · have h := hz (ht1 ht)
      simp only [hback] at h
      simp only [← h, inv_inv, smul_smul, mul_inv_cancel₀ hT.ne', one_smul]
    · have h := hv (ht1 ht)
      simpa only [hback] using h
    · have h := hG (ht1 ht)
      simpa only [hback] using h
  · intro hLs
    have hKts : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (Kt q.1))
        Slab(1) := by
      refine (hkin.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun q hq => ⟨hmap hq.1, mem_univ _⟩)).congr fun q hq => ?_
      exact hKte q.1 hq.1 q.2
    have hΩts : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (Ωt q.1))
        Slab(1) := by
      refine ((contDiffOn_const (c := T)).smul (hvor.comp
        ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
        (fun q hq => ⟨hmap hq.1, mem_univ _⟩))).congr fun q hq => ?_
      exact hΩte q.1 hq.1 q.2
    have hz1 := (hsm₁ hKts hΩts hLs).1
    have hmapT : MapsTo (fun q : ℝ × Vec3 => (T⁻¹ * q.1, q.2)) Slab(T) Slab(1) :=
      fun q hq => ⟨mapsTo_scale hTinv hTT hq.1, mem_univ _⟩
    refine ((contDiffOn_const (c := T⁻¹⁻¹)).smul (hz1.comp
      ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn hmapT)).congr ?_
    intro q _
    simp only [Submodule.coe_smul, map_smul]
    rfl

set_option maxHeartbeats 8000000 in
/-- Part 3 of **Theorem 4.2** (sections/06b_mean_inverse.tex:194–200): Lemma A.2 (`hSp`, the
case `H = ℝ³`, `R = P`) with `B = K(t)`, coercivity `D_-^{-2}` (`kineticForm_elliptic`) and
Lipschitz constant `2K₁` bounds the fixed-time inverse `(P K(t))⁻¹ P`. The transport of the
isomorphism of `hSp` to the divergence-free subspace `S` is
`exists_solenoidalInverse_of_freezing` (conjugation by the isometry `spatialFixedIso`,
generic glue; it reads the isomorphism and its bound off `hSp`). -/
theorem fixedTime42 {C2 : ℝ} {p2 : ℕ} (hC2 : 0 ≤ C2)
    (hSp : ∀ (B : K½) (μ Lip : ℝ), 0 < μ → 0 ≤ Lip →
      (∀ a b, ‖HalfHolder.eval a B - HalfHolder.eval b B‖ ≤ Lip * dist a b) →
      (∀ a (w : Vec3), μ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a B w, w⟫_ℝ) →
      FreezingConclusion endpointStrongSpatialLeray endpointStrongSpatialLeray_idempotent
        C2 p2 B μ Lip)
    {T : ℝ} {U : Velocity} {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L K₀ K₁ : ℝ} (hD1 : 1 ≤ D)
    (hD : ∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L)
    (hKv : ∀ t ∈ J(T), ∀ a, ‖meanKinetic X t a‖ ≤ K₀)
    (hKg : ∀ t ∈ J(T), ∀ a, ‖fderiv ℝ (meanKinetic X t) a‖ ≤ K₁)
    {K : ℝ → K½}
    (hKe : ∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (K t) = meanKinetic X t a) :
    ∀ t ∈ J(T), ∃ e : S ≃L[ℝ] S,
      (∀ w : S, e w = P ((K t).coefficientMul (w : C½))) ∧
      ‖(e.symm : S →L[ℝ] S).comp P‖ ≤
        C2 * (2 + D ^ 2 + K₀ + 2 * K₁) ^ p2 * ‖endpointStrongSpatialProjection‖ := by
  have hT := hP.time_pos
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.smooth.of_le (by simp)
  have hK0 : 0 ≤ K₀ := (norm_nonneg _).trans (hKv 0 h0 0)
  have hK1 : 0 ≤ K₁ := (norm_nonneg (fderiv ℝ (meanKinetic X 0) 0)).trans (hKg 0 h0 0)
  have hDpos : 0 < D := zero_lt_one.trans_le hD1
  have hκ : 0 < (D ^ 2)⁻¹ := by positivity
  obtain ⟨hkin, -⟩ := lifts42 hP hH hD hL
  have hGF (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      (meanDeformationInv X t x).comp (meanDeformation X t x) = ContinuousLinearMap.id ℝ Vec3 :=
    (hP.flow.labelDerivative_inverse hT hU2 hP.periodic h0 ht x).1
  have hdiffK (s : ℝ) (hs : s ∈ J(T)) : Differentiable ℝ (meanKinetic X s) :=
    (contDiffOn_univ.mp (hkin.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨hs, mem_univ x⟩))).differentiable (by simp)
  have hCapsK := endpointHalfHolderCaps_of_lift_gradient (T := T) hK0 hK1 K
    (fun s x => meanKinetic X s x) hKe hdiffK hKv hKg
  have hLK : 0 ≤ 2 * K₁ := by positivity
  intro t ht
  have hcoer : ∀ a (w : Vec3), (D ^ 2)⁻¹ * ‖w‖ ^ 2 ≤ ⟪HalfHolder.eval a (K t) w, w⟫_ℝ := by
    intro a w
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hKe t ht x]
    exact kineticForm_elliptic hDpos (hGF t ht x) (hD t ht x) w
  obtain ⟨e, he, hb⟩ := exists_solenoidalInverse_of_freezing hC2 hκ hLK
    (hSp (K t) (D ^ 2)⁻¹ (2 * K₁) hκ hLK (hCapsK.2 t ht) hcoer)
  refine ⟨e, he, ?_⟩
  have hKsup : ‖(K t).val.1‖ ≤ K₀ := by
    apply (BoundedContinuousFunction.norm_le hK0).mpr
    intro a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    change ‖HalfHolder.eval (toUnitTorus x) (K t)‖ ≤ K₀
    rw [hKe t ht x]
    exact hKv t ht x
  have hX0 : 0 ≤ 2 + ((D ^ 2)⁻¹)⁻¹ + ‖(K t).val.1‖ + 2 * K₁ := by positivity
  have hX : 2 + ((D ^ 2)⁻¹)⁻¹ + ‖(K t).val.1‖ + 2 * K₁ ≤ 2 + D ^ 2 + K₀ + 2 * K₁ := by
    rw [inv_inv]
    linarith only [hKsup]
  calc
    ‖(e.symm : S →L[ℝ] S).comp P‖ ≤ ‖(e.symm : S →L[ℝ] S)‖ * ‖endpointStrongSpatialProjection‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (hb.trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hX0 hX p2) hC2)) endpointStrongSpatialProjection.opNorm_nonneg

/-- The time derivative of the integrated force `L = -∫_0^t (D_aX)ᵀ (f∘X)` is
`-(D_aX)ᵀ(f∘X)` (fundamental theorem of calculus; glue for (4.11)). -/
theorem srcDeriv42 {T : ℝ} (hT : 0 < T) (F : ℝ × A → (Vec3 →L[ℝ] Vec3)) (force : Velocity)
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => F (z.1, toUnitTorus z.2)) Slab(T))
    (hforce : ContDiffOn ℝ ∞ (Function.uncurry force) Slab(T)) (src : ℝ → C½)
    (hsrcC : ContDiffOn ℝ ∞ src J(T))
    (hsrcEval : ∀ t ∈ J(T), ∀ x,
      HalfHolder.eval (toUnitTorus x) (src t) = endpointPhysicalForcePrimitive F force (t, x)) :
    ∀ t ∈ J(T), ∀ x, HalfHolder.eval (toUnitTorus x) (derivWithin src J(T) t) =
      -(F (t, toUnitTorus x)).adjoint (force t x) := by
  intro t ht x
  let Adj : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ[ℝ] (Vec3 →L[ℝ] Vec3) := ContinuousLinearMap.adjoint
  have hpull : ContDiffOn ℝ ∞
      (fun q : ℝ × Vec3 => (F (q.1, toUnitTorus q.2)).adjoint (force q.1 q.2)) Slab(T) :=
    (Adj.contDiff.comp_contDiffOn hF).clm_apply hforce
  have hφ : Continuous (fun r : ℝ => (r, x)) := continuous_id.prodMk continuous_const
  have hmaps : MapsTo (fun r : ℝ => (r, x)) J(T) Slab(T) := fun _ hr => ⟨hr, mem_univ x⟩
  have hcv0 := hpull.continuousOn.comp hφ.continuousOn hmaps
  have hcv : ContinuousOn (fun r => (F (r, toUnitTorus x)).adjoint (force r x)) J(T) := hcv0
  have hEval : ∀ r ∈ J(T), HalfHolder.eval (toUnitTorus x) (src r) =
      -endpointPrimitive (fun r => (F (r, toUnitTorus x)).adjoint (force r x)) r := by
    intro r hr
    rw [hsrcEval r hr x]
    rfl
  exact eval_sourceDerivative hT ht (toUnitTorus x) src _ (hsrcC.of_le (by simp)) hcv hEval

set_option maxHeartbeats 20000000 in
/-- Part 2 of **Theorem 4.2** (sections/06b_mean_inverse.tex:185–193), given part 1 in the
form `solve`: for a smooth force the source is smooth, so the displacement of the unique
solution is smooth (the last assertion of Theorem A.1, inside `solve`). The pressure and
(4.11) come from the time derivative of the projected equation `P`(4.9) (`hEq`, built from
`w.projected`), not of (4.9) itself; see the departure below. With (4.2) this gives (4.11)
(`exists_endpointPhysicalMeanFromJointVelocity`, `PaperSmoothMeanSolution.strong_label_equation`),
the Piola identity gives (4.12) (`.eulerian_equation`), and `c = b(0)` (`constant_eq_initial`).
Departure from the TeX: the TeX differentiates the unprojected equation (4.9) and sets
`q = -φ_t` (06b:187–189), which uses the smoothness of `∇φ` given by the last assertion of
Theorem A.1. The Lean does not use that smoothness: `solve` (from `solve42`) keeps only the
smoothness of `z`. The potential `φ` and the gradient `G` of the solution enter only through
the integrated solution `w` (`exists_of_displacement_pressure_equation`), whose projected
equation is `hEq`. Instead `exists_endpointPhysicalMeanFromJointVelocity` differentiates in
time the residual `R(t) = K(t)v(t) - ∫_0^t Ωv + L(t) - c` of `hEq` (a `C¹` curve, since `K`,
`v`, `L` are `C¹`). By `hEq` the weak Leray projection of `R(t)` vanishes at every time, so
that of `∂_t R(t)` vanishes too, and `∂_t R(t)` is a gradient. The pressure is the zero-mean
periodic potential of `-∂_t R(t)` (`exists_endpointPhysicalPulledBackMomentumPressure`),
and its joint smoothness comes from the jointly smooth right side `g - 𝒟v - K v_t` of (4.11)
(`exists_closedSlab_jointContDiff_periodicPressure_of_gradients`). By (4.9), `R(t) = ∇φ(t)`,
so this is the TeX pressure `-φ_t` for the zero-mean `φ`; the Lean does not prove this
identification, because it does not need it. -/
theorem smooth42 {T : ℝ} {U : Velocity} {X : ℝ → Velocity} (hP : MeanParentFlow T U X)
    (hH : ∀ t ∈ J(T), ∀ (a w : Vec3), ⟪meanHsharp T U X t a w, w⟫_ℝ ≤ ‖w‖ ^ 2)
    {D L : ℝ} (hD : ∀ t ∈ J(T), ∀ a, ‖meanDeformationInv X t a‖ ≤ D)
    (hL : ∀ t ∈ J(T), ∀ a, ‖meanGradient U X t a‖ ≤ L)
    {K Ω : ℝ → K½}
    (hKe : ∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (K t) = meanKinetic X t a)
    (hΩe : ∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (Ω t) = meanVorticity U X t a)
    (solve : ∀ src : ℝ → C½, ContinuousOn src J(T) →
      ∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
        EndpointSystemSolution T K Ω src z v c φ G ∧
        (∀ (z' v' : ℝ → S) (c' : S) (φ' : Pressure) (G' : ℝ → C½),
          EndpointSystemSolution T K Ω src z' v' c' φ' G' →
          EqOn z' z J(T) ∧ EqOn v' v J(T) ∧ c' = c ∧ EqOn G' G J(T)) ∧
        (ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (src (T * q.1)))
            Slab(1) →
          ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
            Slab(T))) :
  ∀ f : Velocity, ContDiffOn ℝ ∞ (Function.uncurry f) Slab(T) →
    (∀ t ∈ J(T), SpatiallyPeriodic (f t)) →
    ∀ src : ℝ → C½,
    (∀ t ∈ J(T), ∀ a, HalfHolder.eval (toUnitTorus a) (src t) =
      -∫ s in (0 : ℝ)..t, (meanDeformation X s a).adjoint (f s (X 0 s a))) →
    (∃ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
      EndpointSystemSolution T K Ω src z v c φ G) ∧
    ∀ (z v : ℝ → S) (c : S) (φ : Pressure) (G : ℝ → C½),
      EndpointSystemSolution T K Ω src z v c φ G →
      let vl : ℝ → Vec3 → Vec3 := fun t a => HalfHolder.eval (toUnitTorus a) (v t : C½)
      let b : ℝ → Vec3 → Vec3 := fun t x => meanDeformation X t (X t 0 x) (vl t (X t 0 x))
      ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
        Slab(T) ∧
      (∀ x, b 0 x = HalfHolder.eval (toUnitTorus x) (c : C½)) ∧
      ∃ qLabel : Pressure, ContDiffOn ℝ ∞ (Function.uncurry qLabel) Slab(T) ∧
        (∀ t ∈ J(T), SpatiallyPeriodic (qLabel t) ∧ (∫ x in centeredCell, qLabel t x) = 0) ∧
        (∀ t ∈ J(T), ∀ a,
          meanKinetic X t a (derivWithin (fun r => vl r a) J(T) t) + gradient (qLabel t) a =
            (meanDeformation X t a).adjoint (f t (X 0 t a)) -
              (2 : ℝ) • (meanDeformation X t a).adjoint
                (derivWithin (fun r => meanDeformation X r a) J(T) t (vl t a))) ∧
        let q : ℝ → Vec3 → ℝ := fun t x => qLabel t (X t 0 x)
        ContDiffOn ℝ ∞ (Function.uncurry b) Slab(T) ∧
        ContDiffOn ℝ ∞ (Function.uncurry q) Slab(T) ∧
        (∀ t ∈ J(T), SpatiallyPeriodic (b t) ∧ SpatiallyPeriodic (q t)) ∧
        ∀ t ∈ J(T), ∀ x, divergence (b t) x = 0 ∧
          fderivWithin ℝ (Function.uncurry b) Slab(T) (t, x) (1, U t x) +
            fderiv ℝ (U t) x (b t x) + gradient (q t) x = f t x := by
  have hT := hP.time_pos
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hU2 : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hP.smooth.of_le (by simp)
  obtain ⟨Lip, hLip⟩ :=
    exists_lipschitzWith_of_contDiffOn_periodic hT (hP.smooth.of_le (by simp)) hP.periodic
  obtain ⟨par, hpar⟩ := parent42 hP hH hD hL
  obtain ⟨hkin, hvor⟩ := lifts42 hP hH hD hL
  let Adj : (Vec3 →L[ℝ] Vec3) ≃ₗᵢ[ℝ] (Vec3 →L[ℝ] Vec3) := ContinuousLinearMap.adjoint
  have hperK (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic fun x => meanKinetic X t x := by
    intro n x
    show meanKinetic X t (x + latticeVector n) = meanKinetic X t x
    rw [← hKe t ht, ← hKe t ht]
    exact spatiallyPeriodic_lift (K t) n x
  have hperΩ (t : ℝ) (ht : t ∈ J(T)) : SpatiallyPeriodic fun x => meanVorticity U X t x := by
    intro n x
    show meanVorticity U X t (x + latticeVector n) = meanVorticity U X t x
    rw [← hΩe t ht, ← hΩe t ht]
    exact spatiallyPeriodic_lift (Ω t) n x
  have hKc : ContDiffOn ℝ ∞ K J(T) := contDiffOn_curve_of_lift hT K _ hkin hperK hKe
  have hΩc : ContDiffOn ℝ ∞ Ω J(T) := contDiffOn_curve_of_lift hT Ω _ hvor hperΩ hΩe
  have hmap : MapsTo (fun τ : ℝ => T * τ) J(1) J(T) := mapsTo_scale hT (mul_one T)
  intro f hf hfper src hsrc_eval
  let force : Velocity := fun t a => f t (X 0 t a)
  have hforce : ContDiffOn ℝ ∞ (Function.uncurry force) Slab(T) :=
    hf.comp (contDiffOn_fst.prodMk (hP.flow.contDiffOn_forwardLabelFlow hT hP.smooth hP.periodic))
      (fun z hz => ⟨hz.1, mem_univ _⟩)
  have hforceper : ∀ t ∈ J(T), SpatiallyPeriodic (force t) := fun t ht n a => by
    change f t (X 0 t (a + latticeVector n)) = f t (X 0 t a)
    rw [hP.flow.add_latticeVector hLip hP.periodic h0 ht n a, hfper t ht n]
  obtain ⟨src', hsrc'sm, hsrc'⟩ := par.exists_integratedForce hT force hforce hforceper
  have hsrc_eq : EqOn src src' J(T) := fun t ht => HalfHolder.ext fun a => by
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hsrc_eval t ht x, hsrc' t ht x]
    simp only [endpointPhysicalForcePrimitive, endpointPrimitive]
    congr 1
    apply intervalIntegral.integral_congr
    rw [uIcc_of_le ht.1]
    intro r hr
    simp only [meanDeformation, force, (hpar r ⟨hr.1, hr.2.trans ht.2⟩ x).1]
  have hsrcC : ContDiffOn ℝ ∞ src J(T) := hsrc'sm.congr hsrc_eq
  -- the integrated force is jointly smooth
  let pull (t : ℝ) (x : Vec3) := (par.F (t, toUnitTorus x)).adjoint (force t x)
  have hpull : ContDiffOn ℝ ∞ (Function.uncurry pull) Slab(T) :=
    (Adj.contDiff.comp_contDiffOn par.deformation_smooth).clm_apply hforce
  have hSrcJ : ContDiffOn ℝ ∞ (endpointPhysicalForcePrimitive par.F force) Slab(T) :=
    (contDiffOn_endpointPhysicalJointPrimitive hT hpull).neg
  have hsrcEval (t : ℝ) (ht : t ∈ J(T)) (x : Vec3) :
      HalfHolder.eval (toUnitTorus x) (src t) =
        endpointPhysicalForcePrimitive par.F force (t, x) := by
    rw [hsrc_eq ht, hsrc' t ht x]
  have hLs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (src (T * q.1)))
      Slab(1) := by
    refine (hSrcJ.comp ((contDiff_const.mul contDiff_fst).prodMk contDiff_snd).contDiffOn
      (fun q hq => ⟨hmap hq.1, mem_univ _⟩)).congr fun q hq => ?_
    exact hsrcEval _ (hmap hq.1) q.2
  obtain ⟨z₀, v₀, c₀, φ₀, G₀, hs₀, hu₀, hsm₀⟩ := solve src hsrcC.continuousOn
  refine ⟨⟨z₀, v₀, c₀, φ₀, G₀, hs₀⟩, ?_⟩
  intro z v c φ G hs
  obtain ⟨hzz, -, -, -⟩ := hu₀ z v c φ G hs
  have hzs : ContDiffOn ℝ ∞ (fun q : ℝ × Vec3 => HalfHolder.eval (toUnitTorus q.2) (z q.1 : C½))
      Slab(T) := (hsm₀ hLs).congr fun q hq => by rw [hzz hq.1]
  have hvs := contDiffOn_lift_velocity hT hs.displacement_deriv hzs
  have hvC : ContDiffOn ℝ ∞ v J(T) := contDiffOn_solenoidal_of_lift hT v hvs
  obtain ⟨w, hw1, hw2, -⟩ := PaperMeanIntegratedSolution.exists_of_displacement_pressure_equation
    (K := K) (Ω := Ω) (src := src) hT.le z v c hs.velocity_continuous hs.displacement_deriv
    hs.initial hs.terminal φ G hs.potential hs.equation
  -- the data of `exists_endpointPhysicalMeanFromJointVelocity`
  have hKrep : ∀ t ∈ J(T), ∀ a, HalfHolder.eval a (K t) = kineticForm (par.F (t, a)) := by
    intro t ht a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hKe t ht x, (hpar t ht x).1]
    rfl
  have hΩrep : ∀ t ∈ J(T), ∀ a,
      HalfHolder.eval a (Ω t) = vorticityForm (par.F (t, a)) (par.M (t, a)) := by
    intro t ht a
    obtain ⟨x, rfl⟩ := toUnitTorus_surjective a
    rw [hΩe t ht x, (hpar t ht x).1, (hpar t ht x).2.2.1]
    rfl
  have hSrcDeriv := srcDeriv42 hT par.F force par.deformation_smooth hforce src hsrcC hsrcEval
  have hEq : ∀ t ∈ J(T), P ((K t).coefficientMul (v t).val) =
      c + P (endpointPrimitive (fun r => (Ω r).coefficientMul (v r).val) t) - P (src t) := by
    intro t ht
    have h := w.projected t ht
    rw [hw1, hw2] at h
    unfold paperMeanIntegratedMomentum at h
    rw [map_add, map_sub] at h
    rw [← h]
    abel
  have hStart : endpointPrimitive v 0 = 0 := by
    simp only [endpointPrimitive, intervalIntegral.integral_same]
  have hFinish : endpointPrimitive v T = 0 := by
    have h := w.terminal
    rwa [hw1] at h
  obtain ⟨Z, B, q, hZ, hB, hq, hPer, hZ0, hZT, hMom⟩ :=
    exists_endpointPhysicalMeanFromJointVelocity hT par.F par.G par.M force par.deformation_smooth
      par.gradient_smooth hforce par.deformation_ode par.left_inverse par.right_inverse K Ω src v c
      (hKc.of_le (by simp)) hΩc.continuousOn (hsrcC.of_le (by simp)) (hvC.of_le (by simp)) hvs
      hKrep hΩrep hSrcDeriv hEq hStart hFinish
  let sm : PaperSmoothMeanSolution par force :=
    ⟨endpointPhysicalLabelVelocity v, Z, B, q, hvs, hZ, hB, hq,
      (fun t ht => ⟨spatiallyPeriodic_lift (v t : C½), (hPer t ht).1, (hPer t ht).2.1,
        (hPer t ht).2.2.1⟩), hZ0, hZT,
      (fun t ht x => (hMom t ht x).1), (fun t ht x => (hMom t ht x).2.1),
      (fun t ht x => (hMom t ht x).2.2.1), (fun t ht x => (hMom t ht x).2.2.2)⟩
  have hX00 : X 0 0 = id := funext fun a => hP.flow.initial 0 h0 a
  intro vl b
  have hbb : ∀ t ∈ J(T), b t = fun y => sm.mean t (X t 0 y) := fun t ht => funext fun y => by
    simp only [b, vl, meanDeformation]
    change _ = B t (X t 0 y)
    rw [(hMom t ht _).1, (hpar t ht _).1]
    rfl
  refine ⟨hzs, ?_, q, hq, fun t ht => ⟨(hPer t ht).2.2.1, (hPer t ht).2.2.2⟩, ?_, ?_⟩
  · intro x
    have hK0' : ∀ a, HalfHolder.eval a (K 0) = ContinuousLinearMap.id ℝ Vec3 := by
      intro a
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective a
      rw [hKe 0 h0 y]
      simp only [meanKinetic, meanDeformation, hX00, fderiv_id, kineticForm_identity]
    have hsrc0 : src 0 = 0 := HalfHolder.ext fun a => by
      obtain ⟨y, rfl⟩ := toUnitTorus_surjective a
      rw [hsrc_eval 0 h0 y]
      simp
    have hc := w.constant_eq_initial hT.le hK0' hsrc0
    rw [hw1, hw2] at hc
    have hx : X 0 0 x = x := hP.flow.initial 0 h0 x
    simp only [b, vl, hx, meanDeformation, hX00, fderiv_id, ContinuousLinearMap.id_apply, hc]
  · intro t ht x
    have hsl := sm.strong_label_equation hT ht x
    dsimp only at hsl
    have hkx : par.kinetic t x = meanKinetic X t x := by
      simp only [PaperMeanParent.kinetic, meanKinetic, meanDeformation, (hpar t ht x).1]
    rw [hkx, (hpar t ht x).1, (hpar t ht x).2.2.1] at hsl
    have hdF : derivWithin (fun r => meanDeformation X r x) J(T) t =
        (fderiv ℝ (U t) (X 0 t x)).comp (fderiv ℝ (X 0 t) x) :=
      ((hP.flow.labelDerivative_evolves hT hU2 hP.periodic h0 x).2 t ht).derivWithin
        (uniqueDiffOn_Icc hT t ht)
    rw [hdF]
    exact hsl
  · intro qE
    obtain ⟨hb, hqs, hper', hsol⟩ := sm.eulerian_equation hT hP.flow hP.smooth hP.periodic
      hP.divergence_free (fun t ht a => (hpar t ht a).1) (fun t ht a => (hpar t ht a).2.2.1)
    refine ⟨hb.congr fun r hr => congrFun (hbb r.1 hr.1) r.2, hqs,
      fun t ht => ⟨by rw [hbb t ht]; exact (hper' t ht).1, (hper' t ht).2⟩, fun t ht x => ?_⟩
    obtain ⟨hdiv, hmom⟩ := hsol t ht x
    refine ⟨by rw [hbb t ht]; exact hdiv, ?_⟩
    have hfx : force t (X t 0 x) = f t x := by
      simp only [force]
      rw [(hP.flow.inverse hLip h0 ht).2 x]
    rw [hfx] at hmom
    rw [fderivWithin_congr (fun r hr => congrFun (hbb r.1 hr.1) r.2) (congrFun (hbb t ht) x),
      hbb t ht]
    exact hmom

end Lib.S34A

set_option maxHeartbeats 8000000 in
/-- Proof of **Theorem 4.2** (`cc:uf:mean:inverse`, sections/06b_mean_inverse.tex:143–173),
following the TeX proof at sections/06b_mean_inverse.tex:174–201.

* Rescaling (:175–176): `τ = t/T`, `Z(τ) = z(t)/T`, `Z_τ = v`
  (`Lib.S34A.endpointSystemSolution_scale`), with coefficients `K(Tτ)`, `T Ω(Tτ)` and
  source `L(Tτ)`.
* `hA_1` (Theorem A.1, :176–177) is applied on `[0,1]` to these coefficients
  (`Lib.S34A.solve42`), with ellipticity `D_-^{-2}` (`kineticForm_elliptic`) and coercivity
  constant `1/(2D_-²(1+‖M‖_∞)²)`; the coercivity (A.2) comes from `h4_1` (Lemma 4.1,
  :178–179) and (4.6) through `Lib.S34A.sobolevEnergy_of_hardy`. It gives the unique
  solution; its bound (A.3) with `Q ≤ 16 (D_- + ‖M‖_∞ + …)⁴` (`paperMean_inverse_scale`,
  :180–184) gives (4.10).
* For smooth `f` (:185–193, `Lib.S34A.smooth42`) the source is smooth, and the last assertion
  of `hA_1` gives smoothness of the rescaled displacement, hence of `z`, `v`. Its other
  conclusions (smoothness of `c` and of `∇φ`) are not used. Departure from the TeX (:187–189,
  details in the docstring of `Lib.S34A.smooth42`): the Lean differentiates the projected
  equation `P`(4.9), not (4.9), and takes as pressure the zero-mean potential of the
  differentiated residual, not `-φ_t`. This gives (4.11), and the Piola identity gives (4.12).
* `hA_2` (Lemma A.2 with `H = ℝ³`, `R = P`, `B = K(t)`, coercivity `D_-^{-2}`, :194–200,
  `Lib.S34A.fixedTime42`) bounds the fixed-time inverse by `C(2 + D_-² + ‖K(t)‖_{C¹})^p`,
  which `A` dominates after enlarging `C`, `p`. The isomorphism is moved to `S` by
  `Lib.S34A.exists_solenoidalInverse_of_freezing` (conjugation by an isometry, generic glue).

Constants: `C = C₁ 16^{p₁} + C₂ ‖P‖ 32^{p₂}`, `p = 4 (p₁ + p₂)`, where `C₁, p₁` and `C₂, p₂`
are the constants of Theorem A.1 and Lemma A.2. -/
theorem Proof.theorem_4_2_of (h4_1 : Statement.lemma_4_1) (hA_1 : Statement.theorem_A_1)
    (hA_2 : Statement.lemma_A_2) : Statement.theorem_4_2 := by
  obtain ⟨C1, p1, hC1, hA1⟩ := hA_1
  obtain ⟨C2, p2, hC2, hSp, -⟩ := hA_2
  let Ps := ‖endpointStrongSpatialProjection‖
  have hPs : 0 ≤ Ps := endpointStrongSpatialProjection.opNorm_nonneg
  refine ⟨C1 * 16 ^ p1 + C2 * Ps * 32 ^ p2, 4 * (p1 + p2), by positivity, ?_⟩
  intro T U X hP hH D L K₀ K₁ Ω₀ Ω₁ hD1 hD hL hKv hKg hΩv hΩg K Ω hKe hΩe Acap
  have hT := hP.time_pos
  have h0 : (0 : ℝ) ∈ J(T) := ⟨le_rfl, hT.le⟩
  have hL0 : 0 ≤ L := (norm_nonneg _).trans (hL 0 h0 0)
  have hK0 : 0 ≤ K₀ := (norm_nonneg _).trans (hKv 0 h0 0)
  have hK1 : 0 ≤ K₁ := (norm_nonneg (fderiv ℝ (meanKinetic X 0) 0)).trans (hKg 0 h0 0)
  have hΩ0 : 0 ≤ Ω₀ := (norm_nonneg _).trans (hΩv 0 h0 0)
  have hΩ1 : 0 ≤ Ω₁ := (norm_nonneg (fderiv ℝ (meanVorticity U X 0) 0)).trans (hΩg 0 h0 0)
  -- the scale of (4.10)
  let Sc := D + L + K₀ + K₁ + Ω₀ + Ω₁
  have hSc : 1 ≤ Sc := by dsimp only [Sc]; linarith
  obtain ⟨-, hQ16⟩ := paperMean_inverse_scale hD1 hL0 hK0 hK1 hΩ0 hΩ1
  change 4 + D ^ 2 + 2 * D ^ 2 * (1 + L) ^ 2 + K₀ + K₁ + Ω₀ + Ω₁ ≤ 16 * Sc ^ 4 at hQ16
  have hAcap : Acap = (C1 * 16 ^ p1 + C2 * Ps * 32 ^ p2) * Sc ^ (4 * (p1 + p2)) := rfl
  have hQ : 2 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + L) ^ 2))⁻¹ + K₀ + K₁ + Ω₀ + Ω₁ ≤
      16 * Sc ^ 4 := by
    rw [inv_inv, one_div, inv_inv]
    linarith only [hQ16]
  have hQ0 : 0 ≤ 2 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + L) ^ 2))⁻¹ + K₀ + K₁ + Ω₀ + Ω₁ := by
    positivity
  have hcap1 : C1 * (2 + ((D ^ 2)⁻¹)⁻¹ + (1 / (2 * D ^ 2 * (1 + L) ^ 2))⁻¹ + K₀ + K₁ + Ω₀ +
      Ω₁) ^ p1 ≤ Acap := by
    rw [hAcap]
    have h := Lib.S34A.pow_le_of_le_scale (n := p1) (m := p1 + p2) hQ0 (by norm_num) hSc hQ
      (by omega)
    calc
      _ ≤ C1 * (16 ^ p1 * Sc ^ (4 * (p1 + p2))) := mul_le_mul_of_nonneg_left h hC1
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
          (by positivity)
  have hX0 : 0 ≤ 2 + D ^ 2 + K₀ + 2 * K₁ := by positivity
  have hX : 2 + D ^ 2 + K₀ + 2 * K₁ ≤ 32 * Sc ^ 4 := by
    have h1 : 0 ≤ 2 * D ^ 2 * (1 + L) ^ 2 := by positivity
    linarith only [hQ16, h1, hK0, hK1, hΩ0, hΩ1, sq_nonneg D]
  have hcap2 : C2 * (2 + D ^ 2 + K₀ + 2 * K₁) ^ p2 * Ps ≤ Acap := by
    rw [hAcap]
    have h := Lib.S34A.pow_le_of_le_scale (n := p2) (m := p1 + p2) hX0 (by norm_num) hSc hX
      (by omega)
    calc
      _ ≤ (C2 * (32 ^ p2 * Sc ^ (4 * (p1 + p2)))) * Ps :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h hC2) hPs
      _ = (C2 * Ps * 32 ^ p2) * Sc ^ (4 * (p1 + p2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity))
        (by positivity)
  -- part 1, from Theorem A.1 (rescaled) and Lemma 4.1
  have solve := Lib.S34A.solve42 h4_1 hC1 hA1 hP hH hD1 hD hL hKv hKg hΩv hΩg hKe hΩe
  refine ⟨fun src hsrc => ?_, ?_, fun t ht => ?_⟩
  · obtain ⟨z, v, c, φ, G, hs, hb, hu, -⟩ := solve src hsrc
    exact ⟨z, v, c, φ, G, hs, hb.trans (mul_le_mul_of_nonneg_right hcap1
      (endpointClosedTimeNorm_nonneg hT.le src)), hu⟩
  -- part 2, smooth forces
  · exact Lib.S34A.smooth42 hP hH hD hL hKe hΩe fun src hsrc => by
      obtain ⟨z, v, c, φ, G, hs, -, hu, hsm⟩ := solve src hsrc
      exact ⟨z, v, c, φ, G, hs, hu, hsm⟩
  -- part 3, the fixed-time inverse from Lemma A.2
  · obtain ⟨e, he, hb⟩ := Lib.S34A.fixedTime42 hC2 hSp hP hH hD1 hD hL hKv hKg hKe t ht
    exact ⟨e, he, hb.trans hcap2⟩

end

end TorusEuler.Paper

import Breakdown.FracCert.HeldStateLimitATest

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProfileFreePairingLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Tendsto p atTop (nhds q) → ∀ ζ : Space → Space, IsSolenoidalL2 ζ →
        Tendsto (fun n => ∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (d.profile (p n))
            (d.gradProfile (p n)) y + d.profilePower (p n) y) (ζ y)) atTop
          (nhds (∫ y, inner ℝ (driftField α (d.rotationRate q) (d.profile q) (d.gradProfile q) y
            + d.profilePower q y) (ζ y)))

def ProfileFreeBoundStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∃ C : ℝ, ∀ p ∈ box d.radius,
      ∫ y, ‖driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y + d.profilePower p y‖ ^ 2 ≤ C

def ProfileFreeTestLimitStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ (p : ℕ → Fin k → ℝ) (q : Fin k → ℝ), (∀ n, p n ∈ box d.radius) → q ∈ box d.radius →
      Tendsto p atTop (nhds q) → ∀ ψ : Space → Space, IsTestVectorField ψ →
        Tendsto (fun n => ∫ y, inner ℝ (driftField α (d.rotationRate (p n)) (d.profile (p n))
            (d.gradProfile (p n)) y + d.profilePower (p n) y) (ψ y)) atTop
          (nhds (∫ y, inner ℝ (driftField α (d.rotationRate q) (d.profile q) (d.gradProfile q) y
            + d.profilePower q y) (ψ y)))

theorem profileFreePairingLimit_of (h1 : ProfileFreeBoundStatement) (h2 : ProfileFreeTestLimitStatement) :
    ProfileFreePairingLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq ζ hζ
  obtain ⟨C, hC⟩ := h1 α hα1 hα2 d hd
  exact WeakPairingInternal.tendsto_pair_of_tests
    (fun n => (hd.profile_drift _ (hp n)).add (hd.profile_power _ (hp n)).1) (fun n => hC _ (hp n))
    ((hd.profile_drift q hq).add (hd.profile_power q hq).1)
    (fun ψ hψ => h2 α hα1 hα2 d hd p q hp hq hpq ψ hψ) hζ.1

namespace DefectPairingInternal

theorem decay_le {C : ℝ} {y : Space} (hy : y ≠ 0) (A : Space →L[ℝ] Space) (hA : ‖A‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2)
    (x : Space) : ‖A x‖ ^ 2 ≤ C ^ 2 * (‖x‖ ^ 2 / ‖y‖ ^ 2) := by
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy
  have h1 : ‖A x‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖x‖ :=
    (A.le_opNorm x).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))
  have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : ((1 + ‖y‖)⁻¹) ^ 4 ≤ (‖y‖ ^ 2)⁻¹ := by
    rw [inv_pow]
    refine (inv_le_inv₀ (by positivity) (by positivity)).2 ?_
    nlinarith [sq_nonneg ‖y‖, mul_pos hr hr]
  calc ‖A x‖ ^ 2 ≤ (C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖x‖) ^ 2 := h2
    _ = C ^ 2 * (((1 + ‖y‖)⁻¹) ^ 4 * ‖x‖ ^ 2) := by ring
    _ ≤ C ^ 2 * ((‖y‖ ^ 2)⁻¹ * ‖x‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 (sq_nonneg _)) (sq_nonneg _)
    _ = C ^ 2 * (‖x‖ ^ 2 / ‖y‖ ^ 2) := by rw [div_eq_mul_inv, mul_comm (‖x‖ ^ 2)]

theorem product_limit {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} {d : FracCertData k N}
    (hd : IsFracCert α d) {p : ℕ → Fin k → ℝ} {q : Fin k → ℝ} (hp : ∀ n, p n ∈ box d.radius)
    (hq : q ∈ box d.radius) (hpq : Tendsto p atTop (nhds q)) {ζ : Space → Space} (hζ : MemLp ζ 2 volume) :
    Tendsto (fun n => ∫ y, inner ℝ (d.gradProfile (p n) y (d.profile (p n) y)) (ζ y)) atTop
      (nhds (∫ y, inner ℝ (d.gradProfile q y (d.profile q y)) (ζ y))) := by
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  have hdn := CrossTestInternal.grad_tendsto hd hp hq hpq
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  have hX : ∀ p' ∈ box d.radius, MemLp (fun y => d.gradProfile p' y (d.profile p' y)) 2 volume := by
    intro p' hp'
    exact ActiveEnclosureInternal.decay_apply_memLp ((hd.profile_smooth p' hp').continuous_fderiv one_ne_zero)
      (fun y => (hC p' hp' y).2) (hemb p' hp').1
      ((hemb p' hp').2.1.integrable_norm_pow (p := 6) (by norm_num))
  have hne : ∀ᵐ y ∂(volume : Measure Space), y ≠ 0 := by
    have : (volume : Measure Space) {0} = 0 := measure_singleton 0
    filter_upwards [compl_mem_ae_iff.2 this] with y hy
    simpa using hy
  have hq2 := CrossTestInternal.profile_second_order hα1 hα2 hd hq
  have bound : ∀ n, ∫ y, ‖d.gradProfile (p n) y (d.profile (p n) y) - d.gradProfile q y (d.profile q y)‖ ^ 2 ≤
      (2 * |C| ^ 2 + 8 * C ^ 2) * ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y) := by
    intro n
    have hs := secondOrderLinear d.order _ _ _ _ _ _ (-1)
      (CrossTestInternal.profile_second_order hα1 hα2 hd (hp n)) hq2
    obtain ⟨hI, hIb⟩ := inverseSquareBound _ _ hs.measurable_velocity hs.velocity_six hs.gradient_two
      hs.weak_gradient
    simp only [neg_one_smul, ← sub_eq_add_neg] at hI hIb
    have hsub := CrossTestInternal.entrySq_sub_integrable (hemb _ (hp n)).2.2.1 (hemb _ (hp n)).2.2.2.1
      (hemb q hq).2.2.1 (hemb q hq).2.2.2.1
    have hL := ((hX _ (hp n)).sub (hX q hq)).integrable_norm_pow (p := 2) (by norm_num)
    have hR : Integrable (fun y => 2 * |C| ^ 2 * entrySq (d.gradProfile (p n) y - d.gradProfile q y)
        + 2 * C ^ 2 * (‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2)) volume :=
      (hsub.const_mul _).add (hI.const_mul _)
    calc ∫ y, ‖d.gradProfile (p n) y (d.profile (p n) y) - d.gradProfile q y (d.profile q y)‖ ^ 2
        ≤ ∫ y, (2 * |C| ^ 2 * entrySq (d.gradProfile (p n) y - d.gradProfile q y)
          + 2 * C ^ 2 * (‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2)) := by
          refine integral_mono_ae hL hR ?_
          filter_upwards [hne] with y hy
          have e : d.gradProfile (p n) y (d.profile (p n) y) - d.gradProfile q y (d.profile q y) =
              (d.gradProfile (p n) y - d.gradProfile q y) (d.profile (p n) y)
                + d.gradProfile q y (d.profile (p n) y - d.profile q y) := by
            simp only [sub_apply, map_sub]
            abel
          rw [e]
          have h1 := LinearStateClosedInternal.clm_sq_le (d.gradProfile (p n) y - d.gradProfile q y)
            (d.profile (p n) y)
          have hW : ‖d.profile (p n) y‖ ^ 2 ≤ |C| ^ 2 := pow_le_pow_left₀ (norm_nonneg _)
            (ActiveEnclosureInternal.profile_le (fun y => (hC _ (hp n) y).1) y) 2
          have h2 := decay_le hy (d.gradProfile q y) (hC q hq y).2 (d.profile (p n) y - d.profile q y)
          have h0 : 0 ≤ entrySq (d.gradProfile (p n) y - d.gradProfile q y) :=
            Finset.sum_nonneg fun i _ => sq_nonneg _
          have h3 := norm_add_le ((d.gradProfile (p n) y - d.gradProfile q y) (d.profile (p n) y))
            (d.gradProfile q y (d.profile (p n) y - d.profile q y))
          have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
          nlinarith [sq_nonneg (‖(d.gradProfile (p n) y - d.gradProfile q y) (d.profile (p n) y)‖
            - ‖d.gradProfile q y (d.profile (p n) y - d.profile q y)‖)]
      _ = 2 * |C| ^ 2 * (∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y))
          + 2 * C ^ 2 * ∫ y, ‖d.profile (p n) y - d.profile q y‖ ^ 2 / ‖y‖ ^ 2 := by
          rw [integral_add (hsub.const_mul _) (hI.const_mul _), integral_const_mul, integral_const_mul]
      _ ≤ _ := by nlinarith [sq_nonneg C, sq_nonneg |C|]
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero_norm (fun n => ?_) (a := fun n => Real.sqrt ((2 * |C| ^ 2 + 8 * C ^ 2) *
    ∫ y, entrySq (d.gradProfile (p n) y - d.gradProfile q y)) * Real.sqrt (∫ y, ‖ζ y‖ ^ 2)) ?_
  · rw [norm_norm, Real.norm_eq_abs, ← integral_sub (ActiveEnclosureInternal.pair_integrable (hX _ (hp n)) hζ)
      (ActiveEnclosureInternal.pair_integrable (hX q hq) hζ)]
    have e : (fun y => inner ℝ (d.gradProfile (p n) y (d.profile (p n) y)) (ζ y)
        - inner ℝ (d.gradProfile q y (d.profile q y)) (ζ y)) = fun y =>
        inner ℝ (d.gradProfile (p n) y (d.profile (p n) y) - d.gradProfile q y (d.profile q y)) (ζ y) := by
      funext y
      rw [inner_sub_left]
    rw [e]
    refine (ApplyPairingInternal.abs_pair_le ((hX _ (hp n)).sub (hX q hq)) hζ).trans ?_
    exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (bound n)) (Real.sqrt_nonneg _)
  · have := ((hdn.const_mul (2 * |C| ^ 2 + 8 * C ^ 2)).sqrt).mul_const (Real.sqrt (∫ y, ‖ζ y‖ ^ 2))
    simpa using this

theorem multiplier_limit {α : ℝ} {k N : ℕ} {d : FracCertData k N} (hd : IsFracCert α d)
    {p : ℕ → Fin k → ℝ} {q : Fin k → ℝ} (hp : ∀ n, p n ∈ box d.radius) (hq : q ∈ box d.radius)
    (hpq : Tendsto p atTop (nhds q)) (i : Fin k) :
    Tendsto (fun n => d.multiplier (p n) i) atTop (nhds (d.multiplier q i)) := by
  have h1 : Tendsto p atTop (nhdsWithin q (box d.radius)) :=
    tendsto_nhdsWithin_iff.2 ⟨hpq, Eventually.of_forall hp⟩
  exact ((continuous_apply i).tendsto _).comp ((hd.multiplier_continuous q hq).tendsto.comp h1)

end DefectPairingInternal

theorem defectPairingLimit_of (h : ProfileFreePairingLimitStatement) : DefectPairingLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq ζ hζ
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  have hemb := fun p' (hp' : p' ∈ box d.radius) => profileEmbedData α hα1 hα2 d hd p' hp'
  have split : ∀ p' ∈ box d.radius, ∫ y, inner ℝ (d.defect α p' y) (ζ y) =
      (∫ y, inner ℝ (driftField α (d.rotationRate p') (d.profile p') (d.gradProfile p') y
        + d.profilePower p' y) (ζ y)) + (∫ y, inner ℝ (d.gradProfile p' y (d.profile p' y)) (ζ y))
        + ∑ i, d.multiplier p' i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
    intro p' hp'
    have mF : MemLp (fun y => driftField α (d.rotationRate p') (d.profile p') (d.gradProfile p') y
        + d.profilePower p' y) 2 volume := (hd.profile_drift p' hp').add (hd.profile_power p' hp').1
    have mX : MemLp (fun y => d.gradProfile p' y (d.profile p' y)) 2 volume :=
      ActiveEnclosureInternal.decay_apply_memLp ((hd.profile_smooth p' hp').continuous_fderiv one_ne_zero)
        (fun y => (hC p' hp' y).2) (hemb p' hp').1
        ((hemb p' hp').2.1.integrable_norm_pow (p := 6) (by norm_num))
    have iF := ActiveEnclosureInternal.pair_integrable mF hζ.1
    have iX := ActiveEnclosureInternal.pair_integrable mX hζ.1
    have iS : ∀ i, Integrable (fun y => d.multiplier p' i * inner ℝ (d.actuator i y) (ζ y)) volume :=
      fun i => (ActiveEnclosureInternal.pair_integrable (hd.actuator_two i) hζ.1).const_mul _
    have iSS : Integrable (fun y => ∑ i, d.multiplier p' i * inner ℝ (d.actuator i y) (ζ y)) volume :=
      integrable_finsetSum _ fun i _ => iS i
    have iFX : Integrable (fun y => inner ℝ (driftField α (d.rotationRate p') (d.profile p') (d.gradProfile p') y
        + d.profilePower p' y) (ζ y) + inner ℝ (d.gradProfile p' y (d.profile p' y)) (ζ y)) volume := iF.add iX
    have e : (fun y => inner ℝ (d.defect α p' y) (ζ y)) = fun y =>
        (inner ℝ (driftField α (d.rotationRate p') (d.profile p') (d.gradProfile p') y
          + d.profilePower p' y) (ζ y) + inner ℝ (d.gradProfile p' y (d.profile p' y)) (ζ y))
          + ∑ i, d.multiplier p' i * inner ℝ (d.actuator i y) (ζ y) := by
      funext y
      simp only [FracCertData.defect, inner_add_left, sum_inner, real_inner_smul_left]
    rw [e, integral_add iFX iSS, integral_add iF iX, integral_finsetSum _ fun i _ => iS i]
    simp only [integral_const_mul]
  rw [split q hq]
  refine ((((h α hα1 hα2 d hd p q hp hq hpq ζ hζ).add
    (DefectPairingInternal.product_limit hα1 hα2 hd hp hq hpq hζ.1)).add
    (tendsto_finsetSum _ fun i _ => (DefectPairingInternal.multiplier_limit hd hp hq hpq i).mul_const _))).congr
    (fun n => (split (p n) (hp n)).symm)

end SteadyCert

end Breakdown

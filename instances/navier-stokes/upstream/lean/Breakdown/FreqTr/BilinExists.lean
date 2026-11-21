import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.BilinExists

def triDensity (u v : X) (w : Space → Space) (x : Space) : ℝ :=
  ∑ j : Fin 3, (velocity u : Space → Space) x j * inner ℝ ((partialX j v : Space → Space) x) (w x)

theorem trilinear_eq (u v : X) (w : Space → Space) :
    trilinear u v w = ∫ x, triDensity u v w x := rfl

theorem triDensity_add_left (u u' v : X) (w : Space → Space) :
    triDensity (u + u') v w =ᵐ[volume] triDensity u v w + triDensity u' v w := by
  filter_upwards [Lp.coeFn_add (velocity u) (velocity u')] with x hx
  simp only [triDensity, map_add, hx, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem triDensity_smul_left (c : ℝ) (u v : X) (w : Space → Space) :
    triDensity (c • u) v w =ᵐ[volume] c • triDensity u v w := by
  filter_upwards [Lp.coeFn_smul c (velocity u)] with x hx
  simp only [triDensity, map_smul, hx, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc]

theorem triDensity_add_mid (u v v' : X) (w : Space → Space) :
    triDensity u (v + v') w =ᵐ[volume] triDensity u v w + triDensity u v' w := by
  have h : ∀ᵐ x ∂volume, ∀ j : Fin 3, (partialX j (v + v') : Space → Space) x =
      (partialX j v : Space → Space) x + (partialX j v' : Space → Space) x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_add (partialX j v) (partialX j v')] with x hx
    rw [map_add, hx, Pi.add_apply]
  filter_upwards [h] with x hx
  simp only [triDensity, hx, inner_add_left, mul_add, Finset.sum_add_distrib, Pi.add_apply]

theorem triDensity_smul_mid (c : ℝ) (u v : X) (w : Space → Space) :
    triDensity u (c • v) w =ᵐ[volume] c • triDensity u v w := by
  have h : ∀ᵐ x ∂volume, ∀ j : Fin 3, (partialX j (c • v) : Space → Space) x =
      c • (partialX j v : Space → Space) x := by
    rw [ae_all_iff]
    intro j
    filter_upwards [Lp.coeFn_smul c (partialX j v)] with x hx
    rw [map_smul, hx, Pi.smul_apply]
  filter_upwards [h] with x hx
  simp only [triDensity, hx, real_inner_smul_left, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem triDensity_add_right (u v : X) (w w' : Space → Space) :
    triDensity u v (w + w') = triDensity u v w + triDensity u v w' := by
  funext x
  simp only [triDensity, Pi.add_apply, inner_add_right, mul_add, Finset.sum_add_distrib]

theorem triDensity_smul_right (c : ℝ) (u v : X) (w : Space → Space) :
    triDensity u v (c • w) = c • triDensity u v w := by
  funext x
  simp only [triDensity, Pi.smul_apply, real_inner_smul_right, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem triDensity_congr (u v : X) {w w' : Space → Space} (h : w =ᵐ[volume] w') :
    triDensity u v w =ᵐ[volume] triDensity u v w' := by
  filter_upwards [h] with x hx
  simp only [triDensity, hx]

theorem trilinear_add_left {u u' v : X} {w : Space → Space}
    (hu : Integrable (triDensity u v w) volume) (hu' : Integrable (triDensity u' v w) volume) :
    trilinear (u + u') v w = trilinear u v w + trilinear u' v w :=
  (integral_congr_ae (triDensity_add_left u u' v w)).trans (integral_add hu hu')

theorem trilinear_smul_left (c : ℝ) (u v : X) (w : Space → Space) :
    trilinear (c • u) v w = c * trilinear u v w :=
  (integral_congr_ae (triDensity_smul_left c u v w)).trans (integral_smul c _)

theorem trilinear_add_mid {u v v' : X} {w : Space → Space}
    (hv : Integrable (triDensity u v w) volume) (hv' : Integrable (triDensity u v' w) volume) :
    trilinear u (v + v') w = trilinear u v w + trilinear u v' w :=
  (integral_congr_ae (triDensity_add_mid u v v' w)).trans (integral_add hv hv')

theorem trilinear_smul_mid (c : ℝ) (u v : X) (w : Space → Space) :
    trilinear u (c • v) w = c * trilinear u v w :=
  (integral_congr_ae (triDensity_smul_mid c u v w)).trans (integral_smul c _)

theorem trilinear_congr (u v : X) {w w' : Space → Space} (h : w =ᵐ[volume] w') :
    trilinear u v w = trilinear u v w' :=
  integral_congr_ae (triDensity_congr u v h)

theorem integrable_triDensity_phi (h1 : TrilinearBound) (h2 : PhiBounds) {τ : ℝ} (hτ : 0 < τ)
    (u v ψ : X) : Integrable (triDensity u v (phiX τ ψ : Space → Space)) volume := by
  obtain ⟨C, hC⟩ := h1
  obtain ⟨D, hD⟩ := h2
  exact (hC u v _ (Lp.memLp _) (hD τ hτ ψ).1).1

theorem trilinear_phi_add (h1 : TrilinearBound) (h2 : PhiBounds) {τ : ℝ} (hτ : 0 < τ)
    (u v ψ ψ' : X) :
    trilinear u v (phiX τ (ψ + ψ') : Space → Space) =
      trilinear u v (phiX τ ψ : Space → Space) + trilinear u v (phiX τ ψ' : Space → Space) := by
  have h : (phiX τ (ψ + ψ') : Space → Space) =ᵐ[volume]
      (phiX τ ψ : Space → Space) + (phiX τ ψ' : Space → Space) := by
    rw [map_add]
    exact Lp.coeFn_add _ _
  rw [trilinear_congr u v h, trilinear_eq, triDensity_add_right]
  exact integral_add (integrable_triDensity_phi h1 h2 hτ u v ψ)
    (integrable_triDensity_phi h1 h2 hτ u v ψ')

theorem trilinear_phi_smul (τ c : ℝ) (u v ψ : X) :
    trilinear u v (phiX τ (c • ψ) : Space → Space) = c * trilinear u v (phiX τ ψ : Space → Space) := by
  have h : (phiX τ (c • ψ) : Space → Space) =ᵐ[volume] c • (phiX τ ψ : Space → Space) := by
    rw [map_smul]
    exact Lp.coeFn_smul _ _
  rw [trilinear_congr u v h, trilinear_eq, triDensity_smul_right]
  exact integral_smul c _

theorem bilinForm_symm (τ : ℝ) (u v ψ : X) : bilinForm τ u v ψ = bilinForm τ v u ψ := by
  simp only [bilinForm, add_comm]

theorem bilinForm_add_left (h1 : TrilinearBound) (h2 : PhiBounds) {τ : ℝ} (hτ : 0 < τ)
    (u u' v ψ : X) : bilinForm τ (u + u') v ψ = bilinForm τ u v ψ + bilinForm τ u' v ψ := by
  have hi := integrable_triDensity_phi h1 h2 hτ
  simp only [bilinForm, trilinear_add_left (hi u v ψ) (hi u' v ψ),
    trilinear_add_mid (hi v u ψ) (hi v u' ψ)]
  ring

theorem bilinForm_smul_left (τ c : ℝ) (u v ψ : X) :
    bilinForm τ (c • u) v ψ = c * bilinForm τ u v ψ := by
  simp only [bilinForm, trilinear_smul_left, trilinear_smul_mid]
  ring

theorem bilinForm_add_right (h1 : TrilinearBound) (h2 : PhiBounds) {τ : ℝ} (hτ : 0 < τ)
    (u v ψ ψ' : X) : bilinForm τ u v (ψ + ψ') = bilinForm τ u v ψ + bilinForm τ u v ψ' := by
  simp only [bilinForm, trilinear_phi_add h1 h2 hτ]
  ring

theorem bilinForm_smul_right (τ c : ℝ) (u v ψ : X) :
    bilinForm τ u v (c • ψ) = c * bilinForm τ u v ψ := by
  simp only [bilinForm, trilinear_phi_smul]
  ring

theorem sqrt_phi_le (h2 : PhiBounds) : ∃ D : ℝ, 0 ≤ D ∧ ∀ τ, 0 < τ → ∀ ψ : X,
    Real.sqrt ((eLpNorm (phiX τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (phiX τ ψ : Space → Space) 6 volume).toReal) ≤ D * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖ := by
  obtain ⟨D, hD⟩ := h2
  refine ⟨|D|, abs_nonneg D, fun τ hτ ψ => ?_⟩
  obtain ⟨-, ha, hb⟩ := hD τ hτ ψ
  have ha' : (eLpNorm (phiX τ ψ : Space → Space) 2 volume).toReal ≤
      |D| * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖ := by
    refine ha.trans ?_
    gcongr
    exact le_abs_self D
  have hb' : (eLpNorm (phiX τ ψ : Space → Space) 6 volume).toReal ≤
      |D| * τ ^ (-(1 : ℝ)) * ‖ψ‖ := by
    refine hb.trans ?_
    gcongr
    exact le_abs_self D
  have hpow : τ ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 : ℝ)) = τ ^ (-(3 / 4 : ℝ)) * τ ^ (-(3 / 4 : ℝ)) := by
    rw [← Real.rpow_add hτ, ← Real.rpow_add hτ]
    norm_num
  have hprod : (eLpNorm (phiX τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (phiX τ ψ : Space → Space) 6 volume).toReal ≤ (|D| * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖) ^ 2 := by
    calc _ ≤ (|D| * τ ^ (-(1 / 2 : ℝ)) * ‖ψ‖) * (|D| * τ ^ (-(1 : ℝ)) * ‖ψ‖) :=
          mul_le_mul ha' hb' ENNReal.toReal_nonneg (le_trans ENNReal.toReal_nonneg ha')
      _ = |D| ^ 2 * (τ ^ (-(1 / 2 : ℝ)) * τ ^ (-(1 : ℝ))) * ‖ψ‖ ^ 2 := by ring
      _ = (|D| * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖) ^ 2 := by rw [hpow]; ring
  calc _ ≤ Real.sqrt ((|D| * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖) ^ 2) := Real.sqrt_le_sqrt hprod
    _ = _ := Real.sqrt_sq (by positivity)

theorem bilinForm_bound (h1 : TrilinearBound) (h2 : PhiBounds) : ∃ K : ℝ, 0 ≤ K ∧ ∀ τ, 0 < τ →
    ∀ u v ψ : X, |bilinForm τ u v ψ| ≤ K * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖ * ‖ψ‖ := by
  obtain ⟨D, hD0, hD⟩ := sqrt_phi_le h2
  obtain ⟨C, hC⟩ := h1
  refine ⟨|C| * D, by positivity, fun τ hτ u v ψ => ?_⟩
  have hS := hD τ hτ ψ
  set S := Real.sqrt ((eLpNorm (phiX τ ψ : Space → Space) 2 volume).toReal *
      (eLpNorm (phiX τ ψ : Space → Space) 6 volume).toReal) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hw6 := (h2.choose_spec τ hτ ψ).1
  have t1 : |trilinear u v (phiX τ ψ : Space → Space)| ≤ |C| * ‖u‖ * ‖v‖ * S := by
    refine (hC u v _ (Lp.memLp _) hw6).2.trans ?_
    gcongr
    exact le_abs_self C
  have t2 : |trilinear v u (phiX τ ψ : Space → Space)| ≤ |C| * ‖u‖ * ‖v‖ * S := by
    refine (hC v u _ (Lp.memLp _) hw6).2.trans ?_
    rw [mul_right_comm (|C|) ‖u‖ ‖v‖]
    gcongr
    exact le_abs_self C
  have e : |bilinForm τ u v ψ| = (1 / 2 : ℝ) *
      |trilinear u v (phiX τ ψ : Space → Space) + trilinear v u (phiX τ ψ : Space → Space)| := by
    rw [bilinForm, abs_mul]
    norm_num
  rw [e]
  calc _ ≤ (1 / 2 : ℝ) * (|trilinear u v (phiX τ ψ : Space → Space)| +
        |trilinear v u (phiX τ ψ : Space → Space)|) := by gcongr; exact abs_add_le _ _
    _ ≤ (1 / 2 : ℝ) * (|C| * ‖u‖ * ‖v‖ * S + |C| * ‖u‖ * ‖v‖ * S) := by gcongr
    _ = |C| * ‖u‖ * ‖v‖ * S := by ring
    _ ≤ |C| * ‖u‖ * ‖v‖ * (D * τ ^ (-(3 / 4 : ℝ)) * ‖ψ‖) := by gcongr
    _ = _ := by ring

theorem exists_bilin_of_form {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (β : E → E → E → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hadd1 : ∀ u u' v ψ, β (u + u') v ψ = β u v ψ + β u' v ψ)
    (hsmul1 : ∀ (c : ℝ) u v ψ, β (c • u) v ψ = c * β u v ψ)
    (hadd2 : ∀ u v v' ψ, β u (v + v') ψ = β u v ψ + β u v' ψ)
    (hsmul2 : ∀ (c : ℝ) u v ψ, β u (c • v) ψ = c * β u v ψ)
    (hadd3 : ∀ u v ψ ψ', β u v (ψ + ψ') = β u v ψ + β u v ψ')
    (hsmul3 : ∀ (c : ℝ) u v ψ, β u v (c • ψ) = c * β u v ψ)
    (hbd : ∀ u v ψ, |β u v ψ| ≤ M * ‖u‖ * ‖v‖ * ‖ψ‖) :
    ∃ B : E →L[ℝ] E →L[ℝ] E, ∀ u v, (∀ ψ, inner ℝ (B u v) ψ = β u v ψ) ∧
      ‖B u v‖ ≤ M * ‖u‖ * ‖v‖ := by
  let L : E → E → E →L[ℝ] ℝ := fun u v =>
    LinearMap.mkContinuous
      { toFun := β u v
        map_add' := hadd3 u v
        map_smul' := fun c ψ => by simp only [hsmul3, smul_eq_mul, RingHom.id_apply] }
      (M * ‖u‖ * ‖v‖) (fun ψ => by rw [Real.norm_eq_abs]; exact hbd u v ψ)
  let R : E → E → E := fun u v => (InnerProductSpace.toDual ℝ E).symm (L u v)
  have hR : ∀ u v ψ, inner ℝ (R u v) ψ = β u v ψ := fun u v ψ => by
    simp only [R, InnerProductSpace.toDual_symm_apply]
    rfl
  have hRn : ∀ u v, ‖R u v‖ ≤ M * ‖u‖ * ‖v‖ := fun u v => by
    simp only [R, LinearIsometryEquiv.norm_map]
    exact LinearMap.mkContinuous_norm_le _ (by positivity) _
  let R₂ : E →ₗ[ℝ] E →ₗ[ℝ] E := LinearMap.mk₂ ℝ R
    (fun u u' v => ext_inner_right ℝ fun ψ => by
      rw [inner_add_left, hR, hR, hR, hadd1])
    (fun c u v => ext_inner_right ℝ fun ψ => by
      rw [real_inner_smul_left, hR, hR, hsmul1])
    (fun u v v' => ext_inner_right ℝ fun ψ => by
      rw [inner_add_left, hR, hR, hR, hadd2])
    (fun c u v => ext_inner_right ℝ fun ψ => by
      rw [real_inner_smul_left, hR, hR, hsmul2])
  refine ⟨LinearMap.mkContinuous₂ R₂ M (fun u v => hRn u v), fun u v => ⟨fun ψ => ?_, ?_⟩⟩
  · exact hR u v ψ
  · exact hRn u v

end Internal.BilinExists

open Internal.BilinExists in
theorem bilinExistsBound (h1 : TrilinearBound) (h2 : PhiBounds) :
    BilinExists ∧ BilinBound := by
  obtain ⟨K, hK0, hK⟩ := bilinForm_bound h1 h2
  have hB : ∀ τ, 0 < τ → ∃ B : X →L[ℝ] X →L[ℝ] X, ∀ u v, (∀ ψ, inner ℝ (B u v) ψ = bilinForm τ u v ψ) ∧
      ‖B u v‖ ≤ K * τ ^ (-(3 / 4 : ℝ)) * ‖u‖ * ‖v‖ := fun τ hτ =>
    exists_bilin_of_form (bilinForm τ) (K * τ ^ (-(3 / 4 : ℝ))) (by positivity)
      (bilinForm_add_left h1 h2 hτ) (bilinForm_smul_left τ)
      (fun u v v' ψ => by
        rw [bilinForm_symm, bilinForm_add_left h1 h2 hτ, bilinForm_symm τ v, bilinForm_symm τ v'])
      (fun c u v ψ => by rw [bilinForm_symm, bilinForm_smul_left, bilinForm_symm])
      (bilinForm_add_right h1 h2 hτ) (bilinForm_smul_right τ) (hK τ hτ)
  refine ⟨fun τ hτ => ?_, K, hK0, fun τ hτ u v => ?_⟩
  · obtain ⟨B, hB⟩ := hB τ hτ
    exact ⟨B, fun u v ψ => (hB u v).1 ψ⟩
  · obtain ⟨B, hB⟩ := hB τ hτ
    have h : 0 < τ ∧ ∃ B, BilinSpec τ B := ⟨hτ, B, fun u v ψ => (hB u v).1 ψ⟩
    have hspec : BilinSpec τ (bilinX τ) := by
      unfold bilinX
      rw [dif_pos h]
      exact h.2.choose_spec
    have heq : bilinX τ u v = B u v := ext_inner_right ℝ fun ψ => by
      rw [hspec, (hB u v).1]
    rw [heq]
    exact (hB u v).2

end Breakdown.Freq

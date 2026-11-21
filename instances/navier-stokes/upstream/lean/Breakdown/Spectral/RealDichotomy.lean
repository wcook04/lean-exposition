import Breakdown.Base.Framework
import Breakdown.Spectral.ComplexifyMap
import Breakdown.Spectral.ComplexDichotomy

noncomputable section

namespace Breakdown.Spectral

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

private theorem ofReal_injective_aux :
    Function.Injective (Complexification.ofReal : X →L[ℝ] Complexification X) := by
  intro x y h
  have h' := congrArg Complexification.re h
  simpa using h'

theorem exists_dichotomy (T₀ C : X →L[ℝ] X) (b α β : ℝ) (hb : 0 ≤ b) (hbα : b ≤ α)
    (hαβ : α < β) (hT₀ : ‖T₀‖ ≤ b) (hC : IsCompactOperator C) :
    ∃ (r₁ r₂ K : ℝ) (Pu : X →L[ℝ] X),
      α < r₁ ∧ r₁ < r₂ ∧ r₂ < β ∧ 0 < K ∧
      Pu * Pu = Pu ∧ Pu * (T₀ + C) = (T₀ + C) * Pu ∧
      FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X)) ∧
      (∀ n : ℕ, ‖(T₀ + C) ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n) ∧
      (∀ n : ℕ, ∀ x, ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖((T₀ + C) ^ n) (Pu x)‖) ∧
      (∀ y ∈ LinearMap.range (Pu : X →ₗ[ℝ] X),
        ∃ x ∈ LinearMap.range (Pu : X →ₗ[ℝ] X), (T₀ + C) x = y) := by
  obtain ⟨r₁, r₂, K, Q, B, hr₁, h12, hr₂, hK, hQQ, hQT, hQc, hs, hu, hTB, hBT, hBQ⟩ :=
    exists_dichotomy_complex (Complexification.map T₀) (Complexification.map C) hb hbα hαβ
      ((Complexification.norm_map_le T₀).trans hT₀) (Complexification.isCompactOperator_map hC)
  set Tc : Complexification X →L[ℂ] Complexification X :=
    Complexification.map T₀ + Complexification.map C with hTc
  have h0 : 0 ≤ r₁ := by linarith
  have hpow : ∀ (n : ℕ) (x : X), Complexification.ofReal (((T₀ + C) ^ n) x) =
      (Tc ^ n) (Complexification.ofReal x) := by
    intro n x
    rw [← Complexification.map_ofReal, Complexification.map_pow, Complexification.map_add]
  have hone : ∀ x : X, Complexification.ofReal ((T₀ + C) x) = Tc (Complexification.ofReal x) := by
    intro x
    rw [← Complexification.map_ofReal, Complexification.map_add]
  have hconjT : ∀ y, Complexification.conj (Tc y) = Tc (Complexification.conj y) := by
    intro y
    simp only [hTc, add_apply, map_add, Complexification.conj_map]
  have hQconj : ∀ y, Complexification.conj (Q y) = Q (Complexification.conj y) :=
    map_comm_of_bounds Tc Q B h0 h12 hQT hBT hTB hs hu Complexification.conj
      Complexification.norm_conj hconjT
  set Pu : X →L[ℝ] X := Complexification.reCLM.comp
    (((1 - Q : Complexification X →L[ℂ] Complexification X).restrictScalars ℝ).comp
      Complexification.ofReal) with hPudef
  have hPu : ∀ x : X, Complexification.ofReal (Pu x) = (1 - Q) (Complexification.ofReal x) := by
    intro x
    have hc : Complexification.conj ((1 - Q) (Complexification.ofReal x)) =
        (1 - Q) (Complexification.ofReal x) := by
      rw [sub_apply, one_apply_eq_self, map_sub, hQconj,
        Complexification.conj_ofReal]
    exact (Complexification.eq_ofReal_of_conj_eq hc).symm
  have hPP : (1 - Q) * (1 - Q) = 1 - Q := by
    rw [sub_mul, one_mul, mul_sub, mul_one, hQQ, sub_self, sub_zero]
  have hcommP : Commute (1 - Q) Tc := (Commute.one_left Tc).sub_left hQT
  have hPuPu : Pu * Pu = Pu := by
    ext x
    apply ofReal_injective_aux
    rw [mul_apply_eq_comp, hPu, hPu]
    exact congrArg (fun S => S (Complexification.ofReal x)) hPP
  have hPuT : Pu * (T₀ + C) = (T₀ + C) * Pu := by
    ext x
    apply ofReal_injective_aux
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hPu, hone, hone, hPu]
    exact congrArg (fun S => S (Complexification.ofReal x)) hcommP.eq
  have hQx : ∀ x : X, Complexification.ofReal (x - Pu x) = Q (Complexification.ofReal x) := by
    intro x
    rw [map_sub, hPu, sub_apply, one_apply_eq_self, sub_sub_cancel]
  have hbound1 : ∀ n : ℕ, ‖(T₀ + C) ^ n * (1 - Pu)‖ ≤ K * r₁ ^ n := by
    intro n
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
    have h1 : Complexification.ofReal (((T₀ + C) ^ n * (1 - Pu)) x) =
        (Tc ^ n * Q) (Complexification.ofReal x) := by
      rw [mul_apply_eq_comp, sub_apply,
        one_apply_eq_self, hpow, hQx]
      rfl
    calc ‖((T₀ + C) ^ n * (1 - Pu)) x‖ = ‖(Tc ^ n * Q) (Complexification.ofReal x)‖ := by
          rw [← h1, Complexification.norm_ofReal]
      _ ≤ ‖Tc ^ n * Q‖ * ‖(Complexification.ofReal x : Complexification X)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * r₁ ^ n * ‖x‖ := by
          rw [Complexification.norm_ofReal]
          exact mul_le_mul_of_nonneg_right (hs n) (norm_nonneg x)
  have hBP : ∀ n : ℕ, B n * Tc ^ n = 1 - Q := by
    intro n
    rw [((hBT n).pow_right n).eq, hTB n]
  have hbound2 : ∀ n : ℕ, ∀ x, ‖Pu x‖ ≤ K * r₂⁻¹ ^ n * ‖((T₀ + C) ^ n) (Pu x)‖ := by
    intro n x
    have h1 : Complexification.ofReal (Pu x) =
        B n (Complexification.ofReal (((T₀ + C) ^ n) (Pu x))) := by
      rw [hpow, hPu, ← mul_apply_eq_comp (B n), hBP n]
      exact (congrArg (fun S => S (Complexification.ofReal x)) hPP).symm
    calc ‖Pu x‖ = ‖(Complexification.ofReal (Pu x) : Complexification X)‖ :=
          (Complexification.norm_ofReal _).symm
      _ = ‖B n (Complexification.ofReal (((T₀ + C) ^ n) (Pu x)))‖ := by rw [h1]
      _ ≤ ‖B n‖ * ‖(Complexification.ofReal (((T₀ + C) ^ n) (Pu x)) : Complexification X)‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ K * r₂⁻¹ ^ n * ‖((T₀ + C) ^ n) (Pu x)‖ := by
          rw [Complexification.norm_ofReal]
          exact mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _)
  have hfinC : FiniteDimensional ℂ (LinearMap.range
      ((1 - Q : Complexification X →L[ℂ] Complexification X) :
        Complexification X →ₗ[ℂ] Complexification X)) :=
    finiteDimensional_range_of_isCompactOperator (1 - Q) hPP hQc
  have hfgR : (Submodule.map (Complexification.reCLM : Complexification X →L[ℝ] X).toLinearMap
      ((LinearMap.range ((1 - Q : Complexification X →L[ℂ] Complexification X) :
        Complexification X →ₗ[ℂ] Complexification X)).restrictScalars ℝ)).FG :=
    ((Module.Finite.iff_fg.mp hfinC).restrictScalars (R := ℝ)).map _
  have := Module.Finite.iff_fg.mpr hfgR
  have hle : LinearMap.range (Pu : X →ₗ[ℝ] X) ≤
      Submodule.map (Complexification.reCLM : Complexification X →L[ℝ] X).toLinearMap
      ((LinearMap.range ((1 - Q : Complexification X →L[ℂ] Complexification X) :
        Complexification X →ₗ[ℂ] Complexification X)).restrictScalars ℝ) := by
    intro y hy
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    refine Submodule.mem_map.mpr ⟨(1 - Q) (Complexification.ofReal x), ?_, rfl⟩
    exact (Submodule.restrictScalars_mem _ _ _).mpr (LinearMap.mem_range.mpr ⟨_, rfl⟩)
  have hfin : FiniteDimensional ℝ (LinearMap.range (Pu : X →ₗ[ℝ] X)) :=
    Submodule.finiteDimensional_of_le hle
  have hmaps : ∀ v ∈ LinearMap.range (Pu : X →ₗ[ℝ] X),
      ((T₀ + C : X →L[ℝ] X) : X →ₗ[ℝ] X) v ∈ LinearMap.range (Pu : X →ₗ[ℝ] X) := by
    intro v hv
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
    exact LinearMap.mem_range.mpr ⟨(T₀ + C) z, congrArg (fun S => S z) hPuT⟩
  have hfix : ∀ v ∈ LinearMap.range (Pu : X →ₗ[ℝ] X), Pu v = v := by
    intro v hv
    obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
    exact congrArg (fun S => S z) hPuPu
  set f := ((T₀ + C : X →L[ℝ] X) : X →ₗ[ℝ] X).restrict hmaps with hf
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).mpr ?_
    rintro ⟨v, hv⟩ h
    have h0v : (T₀ + C) v = 0 := congrArg Subtype.val h
    have hb2 := hbound2 1 v
    simp only [pow_one] at hb2
    rw [hfix v hv, h0v, norm_zero, mul_zero] at hb2
    exact Subtype.ext (norm_le_zero_iff.mp hb2)
  have hsurj := LinearMap.injective_iff_surjective.mp hinj
  refine ⟨r₁, r₂, K, Pu, hr₁, h12, hr₂, hK, hPuPu, hPuT, hfin, hbound1, hbound2, ?_⟩
  intro y hy
  obtain ⟨⟨x, hx⟩, hxy⟩ := hsurj ⟨y, hy⟩
  exact ⟨x, hx, congrArg Subtype.val hxy⟩

end Breakdown.Spectral

namespace Breakdown

theorem dichotomyHolds : DichotomyHolds := by
  intro X _ _ _ T₀ C b α β hb hbα hαβ hT₀ hC
  exact Spectral.exists_dichotomy T₀ C b α β hb hbα hαβ hT₀ hC

end Breakdown

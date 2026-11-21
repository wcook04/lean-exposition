import TorusEuler.Paper.Proofs.S5b.Lemma57
import TorusEuler.Paper.Proofs.S5b.T56Ops
import TorusEuler.Paper.Proofs.S5b.Library.Jets

/-!
# Theorem 5.6, glue: the pulled-back parent residual

`‖R_U∘X‖_{[n]} ≤ C_n λ^{-5/2}` (TeX :615-616, "by (5.10)" of the latest text, `cc:uf:hier:eq:parent-residual`, derived at `05b_parent_coefficients.tex:92-100`; the bound (5.6) of
the parent). The residual has frequencies at most `4𝖣` and sup norm at most `λ^{-5/2}` (`S5.Parent`),
so Bernstein's inequality (B.1) of **Lemma B.1** (`hB_1`) gives `|∇^m R_U| ≤ C_m λ^{-5/2} 𝖣^m`,
and the composition clause (5.7) of **Proposition 5.1** (`h5_1`) gives
`|∇^m (R_U∘X)| ≤ C_m λ^{-5/2} 𝖣^{Cm}`; with `ℓ_* ≤ 𝖣^{-C}` the norm (D.1) of the phase independent
profile `R_U∘X` follows.
-/

open Set
open scoped ContDiff

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile Lib.S5b

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-- **Bernstein's inequality in operator norm** (B.1): a real vector field on the torus with
frequencies at most `4Λ` satisfies `‖∇^m g(x)‖ ≤ C_m Λ^m ‖g‖` (the coordinate sums of (B.1) are
converted to operator norms by `exists_sortedWord` and `opNorm_le_coordinateSum`). -/
theorem band_jets (hB : Statement.lemma_B_1) :
    ∃ C' : ℕ → ℝ, (∀ m, 0 ≤ C' m) ∧
      ∀ (g : C(Labels, Vec3)) {Λ : ℝ}, 0 < Λ → RealTorusFourierBand (4 * Λ) g →
        ContDiff ℝ ∞ (fun y => g (toUnitTorus y)) → ∀ (m : ℕ) (x : Vec3),
          ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x‖ ≤ C' m * ‖g‖ * Λ ^ m := by
  obtain ⟨_, Cb, _, _, hCb, _, hBΛ⟩ := hB _ AppendixB.cutoffSymbol_dyadicMultiplierCutoff
  refine ⟨fun m => (3 : ℝ) ^ m * Cb m, fun m => mul_nonneg (by positivity) (hCb m), ?_⟩
  intro g Λ hΛ hband hsm m x
  have hgR : RealNormedTorusFourierBand (4 * Λ) g := realNormedTorusFourierBand_of_vector hband
  obtain ⟨hbdd, hsum⟩ := (hBΛ Λ hΛ).2.2 m Vec3 g hgR
  have hcomp (β : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x
        (fun j => coordinateDirection (β j))‖ ≤ Cb m * Λ ^ m * ‖g‖ := by
    obtain ⟨w, hw, hwx⟩ := exists_sortedWord hsm β
    obtain ⟨β', hβ', hβw⟩ := exists_monotone_of_orderWord hw
    rw [hwx x, ← hβw, ofFnWord_eq_iteratedFDeriv hsm β' x]
    have h1 : ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) x
          (fun j => EuclideanSpace.single (β' j) 1)‖ ≤
        ⨆ y : Vec3, ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) y
          (fun j => EuclideanSpace.single (β' j) 1)‖ :=
      le_ciSup (hbdd β') x
    have h2 : (⨆ y : Vec3, ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) y
          (fun j => EuclideanSpace.single (β' j) 1)‖) ≤
        ∑ γ ∈ Finset.univ.filter (fun γ : Fin m → Fin 3 => Monotone γ), ⨆ y : Vec3,
          ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) y
            (fun j => EuclideanSpace.single (γ j) 1)‖ :=
      Finset.single_le_sum (f := fun γ : Fin m → Fin 3 => ⨆ y : Vec3,
          ‖iteratedFDeriv ℝ m (fun z => g (toUnitTorus z)) y
            (fun j => EuclideanSpace.single (γ j) 1)‖)
        (fun γ _ => (norm_nonneg _).trans (le_ciSup (hbdd γ) 0))
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hβ'⟩)
    exact h1.trans (h2.trans hsum)
  calc ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x‖
      ≤ ∑ β : Fin m → Fin 3, ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x
            (fun j => coordinateDirection (β j))‖ := opNorm_le_coordinateSum _
    _ ≤ ∑ _β : Fin m → Fin 3, Cb m * Λ ^ m * ‖g‖ := Finset.sum_le_sum fun β _ => hcomp β
    _ = (3 : ℝ) ^ m * Cb m * ‖g‖ * Λ ^ m := by simp [Finset.card_univ]; ring

/-- **The pulled-back residual** `‖R_U∘X‖_{[n]} ≤ K_n λ^{-5/2}` when `ℓ_* ≤ 𝖣^{-C}`
(TeX :615-616, (5.10)), from (B.1) (`hB_1`) and (5.7) (`h5_1`). -/
theorem residual_uNorm (h5_1 : Statement.proposition_5_1) (hB_1 : Statement.lemma_B_1) :
    ∃ C : ℕ, ∃ K : ℕ → ℝ, ∀ {T : ℝ} (_hT : 0 < T) {U : Velocity} {X : ℝ → Velocity}
      {pU : Pressure} {k : Vec3} {D lam t₀ ℓ h : ℝ},
      S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ → 0 < ℓ → ℓ ≤ (D ^ C)⁻¹ →
      ∀ (R : HierarchyTwistedProfile T k Vec3),
        (∀ z ∈ hierarchyProfileSlab T,
          R.val.val.val z = momentumResidual (Icc 0 T) U pU z.1 (X 0 z.1 z.2.1)) →
        ∀ n : ℕ, S5.uNorm ℓ h n R ≤ K n * lam ^ (-5 / 2 : ℝ) := by
  obtain ⟨C, K₁, h51⟩ := h5_1
  obtain ⟨C', hC'0, hjet⟩ := band_jets hB_1
  obtain ⟨Kf, hKf⟩ := h51 C'
  refine ⟨C, fun n => ((hierarchyAdmissibleWords (Fin 3) n).card : ℝ) *
    ∑ m ∈ Finset.range (n + 1), max (Kf m) 0, ?_⟩
  intro T hT U X pU k D lam t₀ ℓ h hP hL hℓ hℓD R hR n
  have h51' := @hKf T U X pU k D lam t₀ hT hP hL
  obtain ⟨-, h57, -⟩ := h51'
  have hD : 2 ≤ D := hP.scale_ge_two
  have hD0 : 0 < D := by linarith
  have hlam : 1 ≤ lam := hP.frequency_ge_one
  have hlam0 : 0 < lam := by linarith
  set Af : ℝ := lam ^ (-5 / 2 : ℝ) with hAf
  have hAf0 : 0 ≤ Af := Real.rpow_nonneg hlam0.le _
  have hRs := contDiffOn_closedSlab_momentumResidual hT hP.velocity_smooth hP.pressure_smooth
  set f := momentumResidual (Icc 0 T) U pU with hf
  have hfs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) := slice_contDiff hRs ht
  obtain ⟨r, hr⟩ := hP.residual_band
  have hfjet : ∀ m : ℕ, ∀ t ∈ Icc 0 T, ∀ x, ‖iteratedFDeriv ℝ m (f t) x‖ ≤ C' m * Af * D ^ m := by
    intro m t ht x
    obtain ⟨hrv, hband, hnorm⟩ := hr t ht
    have hlift : (fun y => r t (toUnitTorus y)) = f t := funext hrv
    have := hjet (r t) hD0 hband (by rw [hlift]; exact hfs t ht) m x
    rw [hlift] at this
    refine this.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hnorm (hC'0 m))
      (pow_nonneg hD0.le _)
  have hcomp := h57 f Af hAf0 hfs hfjet
  have hX0 := hP.flow.contDiffOn_forwardLabelFlow hT hP.velocity_smooth hP.velocity_periodic
  let c : Icc 0 T → Vec3 → Vec3 := fun t a => f t (X 0 t a)
  have hcs (t : Icc 0 T) : ContDiff ℝ ∞ (c t) :=
    (hfs t t.2).comp (slice_contDiff (g := fun z : ℝ × Vec3 => X 0 z.1 z.2) hX0 t.2)
  have hslices : Bridge.slices (Icc 0 T) R = coefField c := by
    funext t x
    rw [Bridge.slices_apply]
    have hmem : ((t : ℝ), x.1, x.2) ∈ hierarchyProfileSlab T := Set.mk_mem_prod t.2 (mem_univ _)
    exact hR _ hmem
  have hKp : ∀ m, 0 ≤ max (Kf m) 0 := fun m => le_max_right _ _
  have hBn : 0 ≤ (∑ m ∈ Finset.range (n + 1), max (Kf m) 0) * Af :=
    mul_nonneg (Finset.sum_nonneg fun m _ => hKp m) hAf0
  have hb := coefField_bounds (c := c) hℓ.le h n hBn hcs
    (fun m => ⟨Kf m * Af * D ^ (C * m), fun t a => hcomp m t t.2 a⟩)
    (fun m hm t a => by
      have h1 := hcomp m t t.2 a
      have h2 : ℓ ^ m * D ^ (C * m) ≤ 1 := by
        rw [pow_mul, ← mul_pow]
        exact pow_le_one₀ (mul_nonneg hℓ.le (pow_nonneg hD0.le _))
          ((mul_le_mul_of_nonneg_right hℓD (pow_nonneg hD0.le _)).trans
            (inv_mul_cancel₀ (pow_pos hD0 _).ne').le)
      have h3 : Kf m * Af ≤ (∑ m ∈ Finset.range (n + 1), max (Kf m) 0) * Af := by
        refine mul_le_mul_of_nonneg_right ?_ hAf0
        exact (le_max_left _ _).trans (Finset.single_le_sum (f := fun m => max (Kf m) 0)
          (fun m _ => hKp m) (Finset.mem_range.mpr (by omega)))
      have hKA : 0 ≤ Kf m * Af := by
        have h4 : 0 ≤ Kf m * Af * D ^ (C * m) := (norm_nonneg _).trans h1
        rcases lt_or_ge (Kf m * Af) 0 with hneg | hge
        · have := mul_neg_of_neg_of_pos hneg (pow_pos hD0 (C * m))
          linarith
        · exact hge
      calc ℓ ^ m * ‖iteratedFDeriv ℝ m (c t) a‖ ≤ ℓ ^ m * (Kf m * Af * D ^ (C * m)) :=
            mul_le_mul_of_nonneg_left h1 (pow_nonneg hℓ.le _)
        _ = (ℓ ^ m * D ^ (C * m)) * (Kf m * Af) := by ring
        _ ≤ 1 * (Kf m * Af) := mul_le_mul_of_nonneg_right h2 hKA
        _ ≤ _ := by rw [one_mul]; exact h3)
  rw [Bridge.uNorm_eq_fieldNorm, hslices]
  exact hb.2.trans (le_of_eq (mul_assoc _ _ _).symm)

end

end TorusEuler.Paper.S5b

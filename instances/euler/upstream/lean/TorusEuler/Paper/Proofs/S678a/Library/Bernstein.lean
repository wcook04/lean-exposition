import TorusEuler.Paper.Proofs.S678b.Library.Comparison
import TorusEuler.Paper.Proofs.S678a.Library.Jets
import TorusEuler.Paper.Proofs.S678a.Library.ChildBounds
import TorusEuler.PhysicalWaveStageClosure

/-! # Bernstein bounds for the parent velocity from (B.1) (package S678a)

Own glue of row 7.1 (item 4 of the proof, sections/08b_induction.tex:395-399, the size of the
parent in the `C^{P,1/2}` norm used for (7.12)): the library's
`exists_velocity_bernstein_bounds_through_depth` reads Bernstein's inequality of Lemma B.1 from the
content lemma `exists_bandBernsteinJetBounds`; here the bound is derived from the coordinate form of
(B.1) in `hB_1` (`Lib.S678b.bernstein_coordinate`) at every order, with the symmetry of the
derivatives of a smooth function (`Lib.S678a.exists_sortedWord`) and the operator norm bound by the
coordinate sum (`Lib.S678a.opNorm_le_coordinateSum`). -/

open Set UnitAddTorus
open scoped ContDiff

local notation "Labels" => UnitAddTorus (Fin 3)

namespace TorusEuler.Paper.Lib.S678a

open TorusEuler

noncomputable section

/-- **Bernstein's inequality at every order for a smooth field with frequencies at most `4D`**
(sections/appB_cutoff.tex, (B.1); from `hB_1`): the operator norm of the `m`-th derivative of the
lift of `g` is at most `K_m ‖g‖ D^m`. Replaces the library's `exists_bandBernsteinJetBounds`
(content of Lemma B.1). -/
theorem bernstein_all_orders (hB_1 : Statement.lemma_B_1) :
    ∃ K : ℕ → ℝ, (∀ m, 0 ≤ K m) ∧
      ∀ (g : C(Labels, Vec3)) {D A : ℝ}, 0 < D → ‖g‖ ≤ A →
        RealTorusFourierBand (4 * D) g →
        ContDiff ℝ ∞ (fun x => g (toUnitTorus x)) → ∀ (m : ℕ) (x : Vec3),
          ‖iteratedFDeriv ℝ m (fun y => g (toUnitTorus y)) x‖ ≤ K m * A * D ^ m := by
  obtain ⟨Cb, hCb, hcoord⟩ := Lib.S678b.bernstein_coordinate hB_1
  refine ⟨fun m => (3 : ℝ) ^ m * Cb m, fun m => mul_nonneg (by positivity) (hCb m), ?_⟩
  intro g D A hD hgA hband hsmooth m x
  have hA : 0 ≤ A := (norm_nonneg g).trans hgA
  set f : Vec3 → Vec3 := fun y => g (toUnitTorus y) with hf
  have hword (β : Fin m → Fin 3) :
      ‖iteratedFDeriv ℝ m f x (fun j => coordinateDirection (β j))‖ ≤ Cb m * D ^ m * A := by
    obtain ⟨w, hw, hwβ⟩ := Lib.S678a.exists_sortedWord hsmooth β
    obtain ⟨β', hmono, hβ'⟩ := Lib.S678a.exists_monotone_of_orderWord hw
    rw [hwβ x, ← hβ', Lib.S678a.ofFnWord_eq_iteratedFDeriv hsmooth β' x]
    have h := hcoord m g hD hband β' hmono x
    exact h.trans (mul_le_mul_of_nonneg_left hgA (mul_nonneg (hCb m) (pow_nonneg hD.le _)))
  calc
    ‖iteratedFDeriv ℝ m f x‖ ≤
        ∑ β : Fin m → Fin 3, ‖iteratedFDeriv ℝ m f x (fun i => coordinateDirection (β i))‖ :=
      Lib.S678a.opNorm_le_coordinateSum _
    _ ≤ ∑ _β : Fin m → Fin 3, Cb m * D ^ m * A := Finset.sum_le_sum fun β _ => hword β
    _ = (3 : ℝ) ^ m * Cb m * A * D ^ m := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring

/-- **Uniform jets of the parent velocity** (copy of
`InductiveEulerStage.exists_velocity_bernstein_bounds_through_depth`, from `bernstein_all_orders`
instead of the content lemma): the iterated derivatives of the velocity of a stage of frequency
`μ ≥ 1` of orders `j ≤ N + 1` are at most `C_N μ^{5(N+1)+1}`. -/
theorem exists_velocity_jets (hB_1 : Statement.lemma_B_1) :
    ∃ C : ℕ → ℝ, (∀ N, 0 ≤ C N) ∧
      ∀ {P : InductiveEulerParameters} {n : ℕ} {activation : ℝ}
        (s : InductiveEulerStage P n activation), 1 ≤ P.frequency n →
        ∀ N : ℕ, ∀ t ∈ Icc 0 (P.slab n activation),
          PhaseJetBound (N + 1) (C N * P.frequency n ^ (5 * (N + 1) + 1)) (s.velocity t) := by
  obtain ⟨K, hK, hBernstein⟩ := bernstein_all_orders hB_1
  let C (N : ℕ) := ∑ i ∈ Finset.range (N + 2), K i
  have hC (N : ℕ) : 0 ≤ C N := Finset.sum_nonneg fun i _ => hK i
  refine ⟨C, hC, ?_⟩
  intro P n activation s hFreq N t ht j hj x
  have hpos : 0 < P.frequency n := zero_lt_one.trans_le hFreq
  have hband : RealTorusFourierBand (4 * P.frequency n ^ 5) (s.torusVelocity t) :=
    fun j hj => s.velocity_band t ht j <|
      (show 2 * P.frequency n ^ 5 ≤ 4 * P.frequency n ^ 5 from
        mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg hpos.le _)).trans_lt hj
  have hsmooth : ContDiff ℝ ∞ (s.velocity t) := contDiff_slice' s.smooth_velocity ht
  have hj' : j ∈ Finset.range (N + 2) := Finset.mem_range.mpr (by omega)
  have hCap : K j ≤ C N := Finset.single_le_sum (fun i _ => hK i) hj'
  have h := hBernstein (s.torusVelocity t) (D := P.frequency n ^ 5) (A := P.frequency n)
    (pow_pos hpos _) (s.velocity_bound t ht) hband hsmooth j x
  refine h.trans ?_
  calc
    K j * P.frequency n * (P.frequency n ^ 5) ^ j = K j * P.frequency n ^ (5 * j + 1) := by
      rw [pow_add, pow_one, pow_mul]; ring
    _ ≤ C N * P.frequency n ^ (5 * (N + 1) + 1) :=
      mul_le_mul hCap (pow_le_pow_right₀ hFreq (by omega)) (pow_nonneg hpos.le _) (hC N)

end

end TorusEuler.Paper.Lib.S678a

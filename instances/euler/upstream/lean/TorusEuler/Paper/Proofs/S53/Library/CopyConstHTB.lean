import TorusEuler.HierarchyTransverseBudgets
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTN
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: scaling of the transverse constants

Generated copy (script `s53tools/mkcopy.py`) of the declarations transverseSolveNormConstant_scaled_le of
`TorusEuler/HierarchyTransverseBudgets.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

open TorusEuler.HierarchyTwistedProfile
noncomputable section

variable {T : ℝ} {k : Vec3}
local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Plane" => transversePlane k

variable {U : Velocity} {X : ℝ → Velocity} {hT : 0 < T}

section ScaledLabelJets

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end ScaledLabelJets
/-- The velocity part has degree thirteen in `D`. Its pressure contribution
has degree twenty, while the direct forcing contribution has degree six. -/
theorem transverseSolveNormConstant_scaled_le (n : ℕ) {r D J₀ J R A B : ℝ}
    (hr : r ≤ 1) (hD : 1 ≤ D) (hJ₀ : 0 ≤ J₀) (hJ : 0 ≤ J) (hR : 0 ≤ R)
    (hA : 0 ≤ A) (hB : 0 ≤ B) :
    let C := transverseSolveNormConstant n 1 (Real.exp 1) (Real.exp 1 * J₀) J R A B
    0 ≤ C ∧ transverseSolveNormConstant n r (Real.exp 1 * D ^ 3) (Real.exp 1 * J₀)
      (J * D) (R * D ^ 9) (A * D ^ 7) (B * D ^ 6) ≤ C * D ^ 20 := by
  let e : ℝ := Real.exp 1
  let V₀ := transverseVelocityWordConstant n 1 e (e * J₀) J R
  let V := transverseVelocityWordConstant n r (e * D ^ 3) (e * J₀) (J * D) (R * D ^ 9)
  let count : ℝ := (hierarchyAdmissibleWords (Fin 4) n).card
  have he : 0 ≤ e := (Real.exp_pos 1).le
  have hWord := linearODEWordFactor_nonneg (mul_nonneg he hJ₀) n
  have hV₀ : 0 ≤ V₀ := by
    unfold V₀ transverseVelocityWordConstant
    positivity
  have hVeq : V = r * V₀ * D ^ 13 := by
    unfold V V₀ transverseVelocityWordConstant
    ring
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hV13 : V ≤ V₀ * D ^ 13 := by
    rw [hVeq]
    exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_left hV₀ hr) (pow_nonneg hD₀ 13)
  have hV20 : V ≤ V₀ * D ^ 20 :=
    hV13.trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide : 13 ≤ 20)) hV₀)
  have hVA : (2 : ℝ) ^ n * (A * D ^ 7) * V ≤ (2 : ℝ) ^ n * A * V₀ * D ^ 20 := by
    calc
      _ ≤ (2 : ℝ) ^ n * (A * D ^ 7) * (V₀ * D ^ 13) :=
        mul_le_mul_of_nonneg_left hV13 (by positivity)
      _ = _ := by ring
  have hFB : (2 : ℝ) ^ n * (B * D ^ 6) ≤ (2 : ℝ) ^ n * B * D ^ 20 := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by decide : 6 ≤ 20)) (by positivity)
  change 0 ≤ count * (V₀ + 2 * (count * ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B))) ∧
    count * (V + 2 * (count * ((2 : ℝ) ^ n * (A * D ^ 7) * V + (2 : ℝ) ^ n * (B * D ^ 6)))) ≤
      count * (V₀ + 2 * (count * ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B))) * D ^ 20
  refine ⟨by positivity, ?_⟩
  calc
    _ ≤ count * (V₀ * D ^ 20 + 2 * (count *
        ((2 : ℝ) ^ n * A * V₀ * D ^ 20 + (2 : ℝ) ^ n * B * D ^ 20))) := by
      gcongr
    _ = _ := by ring


end
end TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile


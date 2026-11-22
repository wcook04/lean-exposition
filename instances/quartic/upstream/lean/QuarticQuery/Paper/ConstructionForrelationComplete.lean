module

public import QuarticQuery.Paper.ConstructionForrelationQuantum

/-!
# Lemma 2.1 with a retained physical implementation of its coherent witness

Compiled as part of the `QuarticQuery` library target.
The final continuation equation uses `compile_circ` before any measurement or
reset. It concerns the same finite logical isometry `F` and output map `out`
whose law has the promised accuracy. It holds for every embedded logical state
and every continuation, so the complete workspace remains available.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Forrelation QuarticQuery.Upper

/-- Ledger: lem-2.1.ii. Verbatim coherent physical implementation with a fixed
worst-case bit-query cap: the same finite isometry, label law and correctness
witness are linked to the physical program on every embedded logical state.
The chosen `Inhabited` instance only fixes the parked physical address. -/
theorem construction_lemma_2_1_ii_complete (k : ℕ) (hk : 1 ≤ k) :
    ∃ A : ℝ, 0 < A ∧ ∀ (t : ℕ) (η : ℝ), 0 < η → η < 1 / 2 →
      ∃ (n : ℕ) (L : BitInput (ForrelationCoord k t) → Bool → ℝ)
        (Z : Type) (instZ : Fintype Z),
        let _ := instZ
        ∃ (o : Z) (out : Z → Bool)
          (F : BitInput (ForrelationCoord k t) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
          ((2 * (n * k) : ℕ) : ℝ) ≤ A * (1 + Real.log (1 / η)) ∧
          IsCirc (n * k) F ∧
          (∀ z b, L z b = lawOf (F z (rket o)) out b) ∧
          (∀ z, 0 ≤ L z false ∧ 0 ≤ L z true ∧ L z false + L z true = 1) ∧
          (∀ z b, P k t z = some b → 1 - η ≤ L z b) ∧
          ∃ instI : Inhabited (ForrelationCoord k t),
            let _ := instI
            ∃ (w : ℕ) (emb : Z ↪ Fin (w + 1))
              (K : AdaptiveProgram (ForrelationCoord k t) w →
                AdaptiveProgram (ForrelationCoord k t) w),
              ∀ next, (K next).queryCap ≤ 2 * (n * k) + next.queryCap ∧
                ∀ z ψ b, (K next).outputMass z (clEmb emb ψ) b =
                  next.outputMass z (clEmb emb (F z ψ)) b := by
  classical
  obtain ⟨A, hA, h⟩ := construction_lemma_2_1_ii k hk
  refine ⟨A, hA, fun t η hη0 hη1 => ?_⟩
  obtain ⟨n, L, hcap, hs, hruns, hlaw, hcorrect⟩ := h t η hη0 hη1
  obtain ⟨Z, instZ, o, out, F, hF, hL⟩ := hs
  let _ := instZ
  have hm : 0 < mValue t := by simp only [mValue]; positivity
  let instI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let _ := instI
  let w := Fintype.card Z
  have hcard : Fintype.card Z ≤ Fintype.card (Fin (w + 1)) := by
    simp only [Fintype.card_fin]
    exact Nat.le_succ _
  obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨K, hK⟩ := compile_circ emb hF
  exact ⟨n, L, Z, instZ, o, out, F, hcap, hF, hL, hlaw, hcorrect,
    instI, w, emb, K, hK⟩

/-- Ledger: lem-2.1. Verbatim conjunction of all three parts on the paper's
power-of-four domain. Part (ii) retains one coherent physical witness and
its complete workspace; part (i) uses the existing alternative lower-bound proof. -/
theorem construction_lemma_2_1_complete (k : ℕ) (hk : 2 ≤ k) :
    (∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → Lvalue k t < R (P k t)) ∧
    (∃ A : ℝ, 0 < A ∧ ∀ (t : ℕ) (η : ℝ), 0 < η → η < 1 / 2 →
      ∃ (n : ℕ) (L : BitInput (ForrelationCoord k t) → Bool → ℝ)
        (Z : Type) (instZ : Fintype Z),
        let _ := instZ
        ∃ (o : Z) (out : Z → Bool)
          (F : BitInput (ForrelationCoord k t) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
          ((2 * (n * k) : ℕ) : ℝ) ≤ A * (1 + Real.log (1 / η)) ∧
          IsCirc (n * k) F ∧
          (∀ z b, L z b = lawOf (F z (rket o)) out b) ∧
          (∀ z, 0 ≤ L z false ∧ 0 ≤ L z true ∧ L z false + L z true = 1) ∧
          (∀ z b, P k t z = some b → 1 - η ≤ L z b) ∧
          ∃ instI : Inhabited (ForrelationCoord k t),
            let _ := instI
            ∃ (w : ℕ) (emb : Z ↪ Fin (w + 1))
              (K : AdaptiveProgram (ForrelationCoord k t) w →
                AdaptiveProgram (ForrelationCoord k t) w),
              ∀ next, (K next).queryCap ≤ 2 * (n * k) + next.queryCap ∧
                ∀ z ψ b, (K next).outputMass z (clEmb emb ψ) b =
                  next.outputMass z (clEmb emb (F z ψ)) b) ∧
    (∃ S : ℕ, 0 < S ∧ ∀ t : ℕ, 1 ≤ t → ∃ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) ∧
      (C.size : ℝ) ≤ (S : ℝ) * (mValue t : ℝ) *
        (Real.logb 2 (mValue t : ℝ)) ^ 2) :=
  ⟨construction_lemma_2_1_i k hk,
    construction_lemma_2_1_ii_complete k (by omega),
    construction_lemma_2_1_iii k (by omega)⟩

end QuarticQuery.Paper

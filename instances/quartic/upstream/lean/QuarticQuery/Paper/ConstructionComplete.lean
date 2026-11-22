module

public import QuarticQuery.Paper.ConstructionCoherent
public import QuarticQuery.Upper.Columns

/-!
# Lemma 2.2 with the finite size and physical query bounds together

Compiled as part of the `QuarticQuery` library target.

The size constant `A` is supplied by Lemma 2.1(iii), and stays fixed as `t` varies.
All coherent statements concern the same circuit witnesses. The final conjunct
chooses a finite physical workspace and compiles those witnesses on the ordinary
bit oracle, including for arbitrary superpositions and arbitrary continuations.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Upper

/-- Ledger: lem-2.2. Verbatim mathematical scope at `m = 4^t ≥ 4`, with explicit
finite constants: exact count, `O_k(m log³m)`, exact adaptive tests, arbitrary
superposed indices, and at most `2(log₂ m + 1)` ordinary bit queries.
The circuit-realization and circuit-size premises are the supplied circuit's
properties from Lemma 2.1(iii), not new open hardness assumptions. -/
theorem construction_lemma_2_2_complete {k t : ℕ}
    (C : Circuit (ForrelationCoord k t)) (A : ℕ) (ht : 1 ≤ t)
    (hC : CircuitRealises C (P k t))
    (hS : C.size ≤ A * mValue t * (2 * t) ^ 2) :
    Fintype.card (TestIndex (2 * t) (40 * t) C.size) =
      mValue t + (mValue t - 1) + 40 * t * (C.size + 2) ∧
    Fintype.card (TestIndex (2 * t) (40 * t) C.size) ≤
      (42 + 20 * A) * mValue t * (2 * t) ^ 3 ∧
    (∀ (x : BitInput (Loc k t C)) (i : Column (2 * t)) (s : Address (40 * t)),
      PaperWinsAt (P k t) C (2 * t) (40 * t) x i s ↔
        ∀ e : TestIndex (2 * t) (40 * t) C.size,
          localTest C (2 * t) (40 * t) x i s e = true) ∧
    (∀ (i : Column (2 * t)) (s : Address (40 * t))
        (e : TestIndex (2 * t) (40 * t) C.size),
      (∀ x, (localTestTree C (2 * t) (40 * t) i s e).eval x =
        localTest C (2 * t) (40 * t) x i s e) ∧
      (localTestTree C (2 * t) (40 * t) i s e).depth ≤ 2 * t + 1) ∧
    (∀ (i : Column (2 * t)) (s : Address (40 * t)),
      ∃ (Z : TestIndex (2 * t) (40 * t) C.size → Type)
        (instZ : ∀ e, Fintype (Z e)),
        let _ := instZ
        ∃ (o : ∀ e, Z e) (out : ∀ e, Z e → Bool)
          (F : ∀ e, BitInput (Loc k t C) → Reg (Z e) ≃ₗᵢ[ℂ] Reg (Z e)),
          (∀ e, IsCirc (max 3 (2 * t + 1)) (F e)) ∧
          IsCirc (max 3 (2 * t + 1)) (fun x => sigmaOp fun e => F e x) ∧
          (∀ (x : BitInput (Loc k t C))
              (a : TestIndex (2 * t) (40 * t) C.size → ℂ)
              (e : TestIndex (2 * t) (40 * t) C.size),
            slice e (sigmaOp (fun e => F e x) (constructionIndexStart o a)) =
              a e • F e x (rket (o e))) ∧
          (∀ (x : BitInput (Loc k t C))
              (e : TestIndex (2 * t) (40 * t) C.size) (z : Z e),
            out e z ≠ localTest C (2 * t) (40 * t) x i s e →
              (F e x (rket (o e))).ofLp z = 0) ∧
          ∃ (w : ℕ) (emb : (Σ e, Z e) ↪ Fin (w + 1))
            (P : AdaptiveProgram (Loc k t C) w → AdaptiveProgram (Loc k t C) w),
            ∀ next, (P next).queryCap ≤ 2 * (2 * t + 1) + next.queryCap ∧
              ∀ x ψ b, (P next).outputMass x (clEmb emb ψ) b =
                next.outputMass x
                  (clEmb emb (sigmaOp (fun e => F e x) ψ)) b) := by
  classical
  have hclassical := construction_lemma_2_2_i C (2 * t) (40 * t) hC
  refine ⟨construction_K_count t C.size, construction_K_bound t C.size A ht hS,
    hclassical.1, ?_, ?_⟩
  · intro i s e
    exact ⟨fun x => localTestTree_eval C (2 * t) (40 * t) x i s e,
      construction_test_depth t ht C (40 * t) i s e⟩
  · intro i s
    obtain ⟨Z, instZ, o, out, F, hF, htotal, hact, hcorrect⟩ :=
      construction_lemma_2_2_ii C (2 * t) (40 * t) i s
    let _ := instZ
    let w := Fintype.card (Σ e, Z e)
    have hcard : Fintype.card (Σ e, Z e) ≤ Fintype.card (Fin (w + 1)) := by
      simp only [Fintype.card_fin]
      exact Nat.le_succ _
    obtain ⟨emb⟩ := Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨P, hP⟩ := compile_circ emb htotal
    refine ⟨Z, instZ, o, out, F, hF, htotal, hact, hcorrect, w, emb, P, ?_⟩
    intro next
    refine ⟨?_, (hP next).2⟩
    have hmax : max 3 (2 * t + 1) = 2 * t + 1 := by omega
    simpa only [hmax] using (hP next).1

end QuarticQuery.Paper

module

public import QuarticQuery.Paper.ConstructionComplete
public import QuarticQuery.Paper.ConstructionPointerSupport

/-! Authored direct agreement target for the exact complete declaration.
It shares the maintained vocabulary and is not an independent semantic review.
The intentional challenge hole is not imported by any proof-bearing module. -/

public section
namespace QuarticQuery.Paper
open QuarticQuery.Upper

theorem construction_lemma_2_2_with_support {k t : ℕ}
    (C : Circuit (ForrelationCoord k t)) (A : ℕ) (ht : 1 ≤ t)
    (hC : CircuitRealises C (P k t))
    (hS : C.size ≤ A * mValue t * (2 * t) ^ 2) :
    (∀ (i : Column (2 * t)) (s : Address (40 * t))
        (e : Fin (2 ^ (2 * t) - 1)) (q : Fin (2 * t) ⊕ Column (2 * t)),
      ∃ X Y : BitInput (Loc k t C),
        (∀ p, p ≠ constructionPointerLoc C (2 * t) (40 * t) i s e q →
          X p = Y p) ∧
        localTest C (2 * t) (40 * t) X i s (.inr (.inl e)) ≠
          localTest C (2 * t) (40 * t) Y i s (.inr (.inl e))) ∧
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
  sorry

end QuarticQuery.Paper

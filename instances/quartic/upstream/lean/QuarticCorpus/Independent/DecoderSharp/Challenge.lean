module

public import QuarticQuery.Paper.ReadSpecOneQuery
public import QuarticQuery.Upper.Decode

/-! Authored direct agreement target for round-four return 04's sharp
construction decoder. It imports the maintained compiler and decoder
definitions but not the proof module. The intentional `sorry` is not a proof.
This shares the maintained vocabulary and is not an independent semantic review. -/

public section
namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Forrelation
open Matrix

theorem construction_decoder_sharp (k t : ℕ) (hk : 1 ≤ k)
    (η : ℝ) (hη : 0 < η) :
    ∃ (n : ℕ), n = repetitions k η ∧
      ∃ (Z : Type) (instZ : Fintype Z),
        let _ := instZ
        ∃ (o : Z) (out : Z → Bool)
          (F : BitInput (ForrelationCoord k t) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
          IsCirc (n * k) F ∧
          (∀ z b, bern (decodeProb k t n z) b = lawOf (F z (rket o)) out b) ∧
          (∀ z b, P k t z = some b →
            1 - η ≤ lawOf (F z (rket o)) out b) ∧
          ∃ instI : Inhabited (ForrelationCoord k t),
            let _ := instI
            ∃ (w : ℕ) (e : Z ↪ Fin (w + 1))
              (K : AdaptiveProgram (ForrelationCoord k t) w →
                AdaptiveProgram (ForrelationCoord k t) w),
              ∀ next, (K next).queryCap ≤ n * k + next.queryCap ∧
                ∀ z ψ b, (K next).outputMass z (clEmb e ψ) b =
                  next.outputMass z (clEmb e (F z ψ)) b := by
  sorry

end QuarticQuery.Paper
end

module

public import QuarticQuery.Paper.ConstructionForrelationSharp
public import QuarticQuery.Paper.QuantumTensor
public import QuarticQuery.Upper.PhysicalContinuation

/-! Fresh-copy tensor of the same concrete alternating Walsh witness.
This leaves the threshold decoder witness in `ConstructionForrelationSharp`
separate until its count-label equality is supplied. -/

public section
namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Forrelation Matrix

/-- The very same one-copy `F` from `forr_walsh_state` is tensor-prepared q
times. Its literal tensor vector and retained physical continuation share G. -/
theorem forr_walsh_tensor_physical (k t : ℕ) (hk : 1 ≤ k) :
    ∃ (o : Fin (mValue t))
      (F : BitInput (ForrelationCoord k t) →
        Reg (Fin (mValue t)) ≃ₗᵢ[ℂ] Reg (Fin (mValue t))),
      IsCirc k F ∧
      (∀ z, F z (rket o) = cplx (H t *ᵥ psi z)) ∧
      (∀ z b, bern (Phi k t z ^ 2) b =
        lawOf (F z (rket o)) (fun j => decide (j = o)) b) ∧
      ∀ q : ℕ, ∃ G : BitInput (ForrelationCoord k t) →
          Reg (TensorBasis (Fin (mValue t)) q) ≃ₗᵢ[ℂ]
            Reg (TensorBasis (Fin (mValue t)) q),
        (∀ z, G z = tensorPreparation (fun _ => F z) q) ∧
        IsCirc (q * k) G ∧
        (∀ z, G z (rket (tensorOrigin o q)) =
          tensorVector (fun _ => cplx (H t *ᵥ psi z)) q) ∧
        ∃ instI : Inhabited (ForrelationCoord k t),
          let _ := instI
          ∃ (w : ℕ) (e : TensorBasis (Fin (mValue t)) q ↪ Fin (w + 1))
            (K : AdaptiveProgram (ForrelationCoord k t) w →
              AdaptiveProgram (ForrelationCoord k t) w),
            ∀ next, (K next).queryCap ≤ q * k + next.queryCap ∧
              ∀ z ψ b, (K next).outputMass z (clEmb e ψ) b =
                next.outputMass z (clEmb e (G z ψ)) b := by
  classical
  have hm : 0 < mValue t := by simp [mValue]
  let instI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let _ := instI
  obtain ⟨o, F, hF, hstate, hlaw⟩ :=
    forr_walsh_state (ι := ForrelationCoord k t) hk id
  have hstate' (z : BitInput (ForrelationCoord k t)) :
      F z (rket o) = cplx (H t *ᵥ psi z) := by
    simpa only [id_eq] using hstate z
  have hlaw' (z : BitInput (ForrelationCoord k t)) (b : Bool) :
      bern (Phi k t z ^ 2) b =
        lawOf (F z (rket o)) (fun j => decide (j = o)) b := by
    simpa only [id_eq] using hlaw z b
  refine ⟨o, F, hF, hstate', hlaw', ?_⟩
  intro q
  let G : BitInput (ForrelationCoord k t) →
      Reg (TensorBasis (Fin (mValue t)) q) ≃ₗᵢ[ℂ]
        Reg (TensorBasis (Fin (mValue t)) q) :=
    fun z => tensorPreparation (fun _ => F z) q
  have hG : IsCirc (q * k) G :=
    tensorPreparation_isCirc (fun _ => F) (fun _ => hF) q
  have hGs (z : BitInput (ForrelationCoord k t)) :
      G z (rket (tensorOrigin o q)) =
        tensorVector (fun _ => cplx (H t *ᵥ psi z)) q := by
    change tensorPreparation (fun _ => F z) q (rket (tensorOrigin o q)) = _
    rw [tensorPreparation_state]
    simp only [hstate']
  obtain ⟨w, e, K, hK⟩ := physicalContinuation_of_isCirc hG
  exact ⟨G, (fun _ => rfl), hG, hGs,
    instI, w, e, K, hK⟩

end QuarticQuery.Paper
end

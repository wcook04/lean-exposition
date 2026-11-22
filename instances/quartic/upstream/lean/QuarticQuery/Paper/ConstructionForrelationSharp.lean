module

public import QuarticQuery.Paper.ReadSpecOneQuery
public import QuarticQuery.Upper.Decode

/-! Sharp physical Forrelation witnesses, conditional on native elaboration of
the one-query compiler in `ReadSpecOneQuery`. The logical witnesses and their
all-input laws are the existing `forr_samples` and `decode_samples`. -/

public section
namespace QuarticQuery.Paper

open QuarticQuery.Upper QuarticQuery.Forrelation
open Matrix

variable {ι : Type} {k t : ℕ}

/-! Concrete Walsh word and its final state. -/
theorem forr_walsh_state (hk : 1 ≤ k)
    (loc : ForrelationCoord k t → ι) :
    ∃ (o : Fin (mValue t))
      (F : BitInput ι → Reg (Fin (mValue t)) ≃ₗᵢ[ℂ]
        Reg (Fin (mValue t))),
      IsCirc k F ∧
      (∀ x, F x (rket o) =
        cplx (H t *ᵥ psi fun c => x (loc c))) ∧
      ∀ x b, bern (Phi k t (fun c => x (loc c)) ^ 2) b =
        lawOf (F x (rket o)) (fun j => decide (j = o)) b := by
  classical
  have h0 : 0 < mValue t := by simp [mValue]
  let o : Fin (mValue t) := ⟨0, h0⟩
  obtain ⟨G, hG, hv⟩ := exists_alternate loc (List.ofFn fun h : Fin k => h)
  have hHe : H t *ᵥ Pi.single o 1 = u t := by
    funext i
    simp only [mulVec_single_one, Matrix.col_apply, u, H, Matrix.smul_apply,
      smul_eq_mul, W, Matrix.map_apply, walshZ, Matrix.of_apply]
    have : walshSign t i o = 1 := by simp [walshSign, o]
    simp [this]
  let F : BitInput ι → Reg (Fin (mValue t)) ≃ₗᵢ[ℂ] Reg (Fin (mValue t)) :=
    fun x => (hGate t).trans ((G x).trans (hGate t))
  have hF : IsCirc k F :=
    (((IsCirc.gate (hGate t)).comp hG).post (hGate t)).cast (by simp)
  have hstate : ∀ x : BitInput ι,
      F x (rket o) = cplx (H t *ᵥ psi fun c => x (loc c)) := fun x => by
    simp only [F, LinearIsometryEquiv.trans_apply]
    rw [rket_zero_eq t h0, hGate_cplx, hHe, hv, hGate_cplx]
    congr 3
    simp [List.map_ofFn, Function.comp_def]
  have hamp : ∀ x : BitInput ι,
      (H t *ᵥ psi fun c => x (loc c)) o = Phi k t fun c => x (loc c) :=
      fun x => by
    rw [Phi_eq_matrix_product k t hk]
    change _ = u t ⬝ᵥ psi fun c => x (loc c)
    simp only [mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    have hs : walshSign t o j = 1 := by simp [walshSign, o]
    simp [H, W, walshZ, hs, u]
  let out : Fin (mValue t) → Bool := fun j => decide (j = o)
  have hlaw : ∀ x : BitInput ι,
      lawOf (F x (rket o)) out true = Phi k t (fun c => x (loc c)) ^ 2 := fun x => by
    simp only [lawOf, out, decide_eq_true_eq]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_univ, ite_true, hstate, cplx,
      Complex.norm_real, Real.norm_eq_abs, sq_abs, hamp]
  refine ⟨o, F, hF, hstate, fun x b => ?_⟩
  cases b with
  | true => exact (by simpa [bern] using (hlaw x).symm)
  | false =>
      have hs := sum_lawOf (F x (rket o)) out
      rw [LinearIsometryEquiv.norm_map, norm_rket, Fintype.sum_bool, hlaw] at hs
      simp only [bern, Bool.false_eq_true, ite_false]
      linarith


theorem forr_walsh_physical (k t : ℕ) (hk : 1 ≤ k) :
    ∃ (o : Fin (mValue t))
      (F : BitInput (ForrelationCoord k t) → Reg (Fin (mValue t)) ≃ₗᵢ[ℂ]
        Reg (Fin (mValue t))),
      IsCirc k F ∧
      (∀ z, F z (rket o) = cplx (H t *ᵥ psi z)) ∧
      (∀ z b, bern (Phi k t z ^ 2) b =
        lawOf (F z (rket o)) (fun j => decide (j = o)) b) ∧
      ∃ instI : Inhabited (ForrelationCoord k t),
        let _ := instI
        ∃ (w : ℕ) (e : Fin (mValue t) ↪ Fin (w + 1))
          (K : AdaptiveProgram (ForrelationCoord k t) w →
            AdaptiveProgram (ForrelationCoord k t) w),
          ∀ next, (K next).queryCap ≤ k + next.queryCap ∧
            ∀ z ψ b, (K next).outputMass z (clEmb e ψ) b =
              next.outputMass z (clEmb e (F z ψ)) b := by
  classical
  have hm : 0 < mValue t := by simp [mValue]
  let instI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let _ := instI
  obtain ⟨o, F, hF, hstate, hL⟩ :=
    forr_walsh_state (ι := ForrelationCoord k t) hk id
  let w := mValue t
  have hcard : Fintype.card (Fin (mValue t)) ≤ Fintype.card (Fin (w + 1)) := by
    simp only [Fintype.card_fin]
    exact Nat.le_succ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨K, hK⟩ := compile_circ_one e hF
  exact ⟨o, F, hF, hstate, hL, instI, w, e, K, hK⟩


/-- The existing logical Forrelation witness, compiled to one physical bit
query per abstract read while retaining exactly the same `F` on every state. -/
theorem construction_projection_test_sharp (k t : ℕ) (hk : 1 ≤ k) :
    ∃ (Z : Type) (instZ : Fintype Z),
      let _ := instZ
      ∃ (o : Z) (out : Z → Bool)
        (F : BitInput (ForrelationCoord k t) → Reg Z ≃ₗᵢ[ℂ] Reg Z),
        IsCirc k F ∧
        (∀ z b, bern (Phi k t z ^ 2) b = lawOf (F z (rket o)) out b) ∧
        ∃ instI : Inhabited (ForrelationCoord k t),
          let _ := instI
          ∃ (w : ℕ) (e : Z ↪ Fin (w + 1))
            (K : AdaptiveProgram (ForrelationCoord k t) w →
              AdaptiveProgram (ForrelationCoord k t) w),
            ∀ next, (K next).queryCap ≤ k + next.queryCap ∧
              ∀ z ψ b, (K next).outputMass z (clEmb e ψ) b =
                next.outputMass z (clEmb e (F z ψ)) b := by
  classical
  have hm : 0 < mValue t := by simp [mValue]
  let instI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let _ := instI
  obtain ⟨Z, instZ, o, out, F, hF, hL⟩ := forr_samples hk (id : ForrelationCoord k t → _)
  let _ := instZ
  let w := Fintype.card Z
  have hcard : Fintype.card Z ≤ Fintype.card (Fin (w + 1)) := by
    simp only [Fintype.card_fin]
    exact Nat.le_succ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨K, hK⟩ := compile_circ_one e hF
  exact ⟨Z, instZ, o, out, F, hF, hL, instI, w, e, K, hK⟩

/-- Exact repeated decoder law on all inputs, promised-input accuracy, and a
physical `n*k` cap for the same retained isometry under every continuation. -/
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
  classical
  have hm : 0 < mValue t := by simp [mValue]
  let instI : Inhabited (ForrelationCoord k t) := ⟨(⟨0, hk⟩, ⟨0, hm⟩)⟩
  let _ := instI
  let n := repetitions k η
  obtain ⟨Z, instZ, o, out, F, hF, hL⟩ :=
    decode_samples hk (id : ForrelationCoord k t → _) n
  let _ := instZ
  let w := Fintype.card Z
  have hcard : Fintype.card Z ≤ Fintype.card (Fin (w + 1)) := by
    simp only [Fintype.card_fin]
    exact Nat.le_succ _
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  obtain ⟨K, hK⟩ := compile_circ_one e hF
  refine ⟨n, rfl, Z, instZ, o, out, F, hF, hL, ?_, instI, w, e, K, hK⟩
  intro z b hz
  rw [← hL]
  exact decodeProb_correct hk hη le_rfl z hz

/-- Measured decision-law corollary of the same one-query compiler. -/
theorem P_runs_sharp {k t : ℕ} (hk : 1 ≤ k)
    [Inhabited (ForrelationCoord k t)] {η : ℝ} (hη : 0 < η)
    {n : ℕ} (hn : repetitions k η ≤ n) :
    ∃ L : BitInput (ForrelationCoord k t) → Bool → ℝ,
      Runs (n * k) L ∧
      ∀ z b, P k t z = some b → 1 - η ≤ L z b :=
  ⟨fun z b => bern (decodeProb k t n z) b,
    (decode_samples hk id n).runs_one,
    fun z b hz => decodeProb_correct hk hη hn z hz⟩

end QuarticQuery.Paper
end

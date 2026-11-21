import TorusEuler.Paper.Proofs.S5a.Library.Near519

/-!
# S5a library: Lemma 5.3, scale monotonicity and the library form of the coefficient jets

Design of the proof of Lemma 5.3: the library chain behind
(5.20)-(5.22) is generic in the parent scale `D` and obtains the jets of the coefficients from the
library form of Proposition 5.1 (explicit exponents `D^{5n+1}`, `D^{7n+1}`, ...). The paper has an
absolute but unspecified exponent `C0` in (D.6) (hypothesis `h5_1`). Both are reconciled by the
scale `D' = D^{C0}`: the data of the lemma satisfy every hypothesis of the library chain with `D'` in
place of `D` (`centerWaveOn_mono` and the monotone hypotheses), and the jets of the coefficients are
`≤ K_m D^{C0 (m+1)} ≤ B_m D'^{e}` for every exponent `e ≥ m+1` (`leafBounds_of_h51`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

/-- The conditions `(5.5)` on the centre wave only weaken when the scale `D` is increased. -/
theorem centerWaveOn_mono {M : ℝ → Vec3 →L[ℝ] Vec3} {κ center : ℝ → Vec3} {t₀ T D D' : ℝ}
    (h : CenterWaveOn M κ center t₀ T D) (hD : 0 < D) (hDD' : D ≤ D') :
    CenterWaveOn M κ center t₀ T D' where
  covector := h.covector
  nonzero := h.nonzero
  amplitude := h.amplitude
  stability z hz hperp u v hu hv huv :=
    (h.stability z hz hperp hu hv huv).trans
      (mul_le_mul_of_nonneg_right hDD' (by positivity))
  coupling t ht :=
    le_trans (mul_le_mul_of_nonneg_right (inv_anti₀ hD hDD') (by positivity)) (h.coupling t ht)

/-- The jets of the seven coefficient fields in the form in which the library chain consumes them
(the conclusion of `exists_parent_coefficientJetBounds`), for the data `U, X, k`, the scale `D` and
the frequency `Λ`, with constants `B`. -/
def LeafBounds (B : ℕ → ℝ) (U : Velocity) (X : ℝ → Velocity) (T D : ℝ) (k : Vec3) (Λ : ℝ) :
    Prop :=
  ∀ n : ℕ, ∀ t ∈ Icc 0 T, ∀ a : Vec3,
    ‖iteratedFDeriv ℝ n (fderiv ℝ (X 0 t)) a‖ ≤ B n * D ^ (5 * n + 1) ∧
    ‖iteratedFDeriv ℝ n (fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ B n * D ^ (7 * n + 1) ∧
    ‖iteratedFDeriv ℝ n (fun b => (fderiv ℝ (X t 0) (X 0 t b)).adjoint) a‖ ≤
      B n * D ^ (7 * n + 1) ∧
    ‖iteratedFDeriv ℝ n (fun b => fderiv ℝ (U t) (X 0 t b)) a‖ ≤ B n * D ^ (6 * n + 1) ∧
    ‖iteratedFDeriv ℝ n (fun b => Λ⁻¹ • labelWaveVector X 0 b k t) a‖ ≤
      B n * D ^ (7 * n + 2) ∧
    ‖iteratedFDeriv ℝ n (fun b => Λ ^ 2 / ‖labelWaveVector X 0 b k t‖ ^ 2) a‖ ≤
      B n * D ^ (16 * n + 4) ∧
    ‖iteratedFDeriv ℝ n (fun b => (‖labelWaveVector X 0 b k t‖ ^ 2)⁻¹ •
      InnerProductSpace.rankOne ℝ (labelWaveVector X 0 b k t) (labelWaveVector X 0 b k t)) a‖ ≤
      B n * D ^ (16 * n + 8)

/-- The jets (D.6) of the coefficients of Proposition 5.1 (`h5_1`, with the absolute exponent `C0`)
give the library form `LeafBounds` at the scale `D^{C0}`, with constants independent of the data:
`K_n D^{C0 (n+1)} ≤ max(K_n,0) (D^{C0})^e` for every `e ≥ n+1` since `D ≥ 1`. -/
theorem leafBounds_of_h51 (h5_1 : Statement.proposition_5_1) :
    ∃ C0 : ℕ, ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧
      ∀ {T D lam t₀ : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3},
        0 < T → S5.Parent T U X pU D lam → S5.Launch T X k lam t₀ →
        LeafBounds B U X T (D ^ C0) k lam := by
  obtain ⟨C, K, hK⟩ := h5_1
  obtain ⟨Kf, hKf⟩ := hK (fun _ => 0)
  refine ⟨C, fun n => max (K n) 0, fun n => le_max_right _ _, ?_⟩
  intro T D lam t₀ U X pU k hT hP hL n t ht a
  have hD1 : (1 : ℝ) ≤ D := by linarith [hP.scale_ge_two]
  obtain ⟨hF, hG, hM, hκ, hν, hPκ⟩ := (hKf hT hP hL).1 n t ht a
  have key : ∀ e : ℕ, n + 1 ≤ e → K n * D ^ (C * (n + 1)) ≤ max (K n) 0 * (D ^ C) ^ e := by
    intro e he
    calc K n * D ^ (C * (n + 1)) ≤ max (K n) 0 * D ^ (C * (n + 1)) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max (K n) 0 * D ^ (C * e) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD1 (Nat.mul_le_mul_left _ he))
            (le_max_right _ _)
      _ = _ := by rw [pow_mul]
  refine ⟨hF.trans (key _ (by omega)), hG.trans (key _ (by omega)), ?_,
    hM.trans (key _ (by omega)), hκ.trans (key _ (by omega)), hν.trans (key _ (by omega)),
    hPκ.trans (key _ (by omega))⟩
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  change ‖iteratedFDeriv ℝ n (J ∘ fun b => fderiv ℝ (X t 0) (X 0 t b)) a‖ ≤ _
  rw [J.norm_iteratedFDeriv_comp_left _ a n]
  exact hG.trans (key _ (by omega))

end

end TorusEuler.Paper.Lib.S5a

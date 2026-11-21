import TorusEuler.Paper.S678.Statements
import TorusEuler.Paper.Proofs.S678b.Library.FirstWaveCoupling
import TorusEuler.Paper.Proofs.S678b.Library.FirstWaveExistence

/-! # Proof of Lemma 6.1 (cites Lemma 2.2) -/

open Set

namespace TorusEuler.Paper

/-- Proof of **Lemma 6.1** (`cc:uf:base:lem:first`), following
sections/03a_exact_base.tex:44-67.

* Existence of the first wave (6.3) (the first conjunct; the setting, 03a:19-27). The TeX
  solves the linear seed equation (3.2) at the origin with initial direction `e_2`, scales it
  to the peak `λ^{-3/4}` (03a:23-25), and keeps the seed perpendicular to `κ` "by (2.1)"
  (sections/04_localized_wave.tex:58-59), i.e. by the persistence of transversality in
  Lemma 2.1. Row 6.1 of the ledger does not cite Lemma 2.1, and the library existence lemma
  `firstWaveOrigin_exists` reaches its content (`affineWave_propagation`). So this proof takes
  a step that is not in the TeX: it checks directly the closed-form solution
  `κ(t,0) = λ(e_1 - 2πt e_2)`, `𝐚(t,0) ∝ g(t)(2πt e_1 + e_2) - ρ arctan(2πt) e_3`,
  `g = (1+4π²t²)^{-1}`, of (2.1) and (3.2) over `B_ρ`, which is perpendicular and nonzero by
  inspection, and rescales it to the peak `λ^{-3/4}` (`Lib.S678b.firstWaveOrigin_exists_explicit`,
  Library/FirstWaveExistence.lean).
* First condition (5.5) (03a:45-55): the reflection estimate `|∂_t log|𝐛|| ≤ |B_ρ|` applied to
  `𝐛` and to the seed gives `|𝐛(t)|/γ(t) ≤ e^{2T|B_ρ|}|𝐛(t')|/γ(t') ≤ 2|𝐛(t')|/γ(t')`
  (`FirstWaveOrigin.weighted_forward`, Lemma 6.1's own content).
* Initial strength (03a:56-58): the same estimate on the seed gives
  `e^{-T|B_ρ|}λ^{-3/4} ≤ |𝐚(0,0)| ≤ λ^{-3/4}`; multiply by `|κ(0,0)| = λ`
  (`FirstWaveOrigin.initial_strength`).
* Second condition (5.5) (03a:60-66): "the frame equations (2.2) give
  `|∂_tE_1|, |∂_tE_2| ≤ |B_ρ|`": `h2_2` (Lemma 2.2, applied on `[0,T]` to the pair at the
  origin over the trace-free `B_ρ`) supplies the frame equations (2.2) and the orthonormality
  of the frame inside `Lib.S678b.first_coupling_lower`; with (6.4) (`ν(0) = 2π`,
  `FirstWaveOrigin.initial_couplings`) they give `ν(t,0) ≥ 2π - 2t|B_ρ|^2 ≥ π ≥ 𝖣^{-1}`. -/
theorem Proof.lemma_6_1_of (h2_2 : Statement.lemma_2_2) : Statement.lemma_6_1 := by
  intro ρ T freq hρ hρ₁ hf hT hSmall
  have hf0 : 0 < freq := zero_lt_one.trans_le hf
  have hTilt : |ρ| ≤ 1 := by simpa only [abs_of_pos hρ] using hρ₁
  refine ⟨Lib.S678b.firstWaveOrigin_exists_explicit hT.le hf0, fun w => ⟨?_, ?_, ?_⟩⟩
  · intro D hD b hb _ t' t ht' ht htt
    exact w.weighted_forward hf0 hSmall hD ht' ht htt hb
  · intro D hD t ht
    have hInv : D⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_two.trans_le hD)).2 (one_le_two.trans hD)
    have hPi : (1 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_three]
    exact hInv.trans (hPi.trans (Lib.S678b.first_coupling_lower h2_2 w hf0 hTilt hSmall ht))
  · rw [mul_comm ‖w.amplitude 0‖]
    exact w.initial_strength hf0 hSmall

end TorusEuler.Paper

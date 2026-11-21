import TorusEuler.Paper.S678.Statements
import TorusEuler.PaperParameterAndLaunchStatements

/-! # Proof of Lemma 1.3 (leaf of the spine) -/

open Filter

namespace TorusEuler.Paper

/-- Proof of **Lemma 1.3** (`cc:uf:tower:lem:slow-orders`), following the proof in
Appendix C (sections/appC_parameters.tex:2-25), which cites no numbered result.

The library lemma `paperLemma13_slowOrders` (Lemma 1.3's own content) carries the three
steps of the TeX proof: the current order is admissible in the maximum (1.14), so
`q_j ≤ q_{j+1} ≤ q_j + 1` (appC:3-8); the frequencies tend to infinity, so `q_j → ∞`
(appC:8-10); and `L_{j+1} = 4K_jK_{j+1}K_{j+2} log λ_{j-1} ≤ 4K(q_{j+1}+1)^3 log λ_{j-1}`,
which (1.13) and the choice of `q_{j+1}` bound by `(log λ_{j-1})^2`, giving (1.15)
(appC:12-23). The Lean statement is one-based (`j ≥ 1`); the library lemma is stated at
`j = i + 1`, and the proof performs this index shift. -/
theorem Proof.lemma_1_3 : Statement.lemma_1_3 := by
  intro b B N q freq hb hB hN hq1 hf0 hfreq hmax
  have hFreq : ∀ i, freq (i + 1) = freq i ^ frequencyExponent b (q (i + 1)) := fun i => by
    simpa using hfreq (i + 1) (Nat.succ_pos i)
  have hMax : ∀ i, IsGreatest {s | 1 ≤ s ∧ s ≤ q (i + 1) + 1 ∧ B s ≤ freq i} (q (i + 2)) :=
    fun i => by simpa using hmax (i + 1) (Nat.succ_pos i)
  obtain ⟨hsteps, htend, hlog⟩ := paperLemma13_slowOrders b B freq q hb hq1 (hf0 ▸ hN) hFreq hMax
    (fun s hs => (hB s hs).1) (fun s hs => (hB s hs).2)
  refine ⟨fun j hj => ?_, htend, fun j hj => ?_⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact hsteps i
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    simpa [Schedule.L] using hlog i

end TorusEuler.Paper

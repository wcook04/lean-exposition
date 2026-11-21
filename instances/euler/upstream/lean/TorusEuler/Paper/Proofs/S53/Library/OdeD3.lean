import TorusEuler.Paper.Proofs.S53.Library.OdeSpaces5

/-!
# S53 library: Lemma D.3 on the jet spaces of the linear ODE
-/

open Set


namespace TorusEuler.Paper.Lib.S53

noncomputable section

/-- Lemma D.3 (through `hD3`) applied to the jet spaces: the constant `Cn` depends only on the index
type, the order `n` and the bound `q` of (D.7). -/
theorem jetD3 (hD3 : Statement.lemma_D_3) (Idx : Type) [Fintype Idx] [LinearOrder Idx] (n : ℕ)
    (q : ℝ) :
    ∃ Cn : ℝ, 0 ≤ Cn ∧ ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
      (s : Slab) (K : ℝ) (c : Asub Idx V s), 0 ≤ K →
      (∀ u : Esub Idx V s, pE s Idx V u ≤ K * pF s Idx V (L0 s u + Tmap s c u)) →
      (∀ m, 1 ≤ m → m ≤ n →
        K * ((s.r - s.l) * appendixExactOrderDerivativeNorm (pA s Idx V) (DA s) m c) ≤ q) →
      ∀ (v : Esub Idx V s) (f : Fsub Idx V s), L0 s v + Tmap s c v = f →
        appendixFiniteDerivativeNorm (pE s Idx V) (DE s) n v ≤
          Cn * K * appendixFiniteDerivativeNorm (pF s Idx V) (DF s) n f := by
  obtain ⟨Cn, hCn, h⟩ := hD3 Idx n (fun _ => q)
  refine ⟨Cn, hCn, fun {V} _ _ s K c hK hInv hSlow v f hEq => ?_⟩
  refine h Unit (Asub Idx V s) (Esub Idx V s) (Fsub Idx V s) (DA s) (DE s) (DF s)
    (pA s Idx V) (pE s Idx V) (pF s Idx V) (L0 s) (fun _ => Tmap s) (fun _ => c)
    (fun _ => s.r - s.l) K (L0_comm s) (fun _ i a u => Tmap_leibniz s i a u) (DF_comm s)
    (DA_comm s) (fun _ => sub_nonneg.mpr s.hlr.le) (fun _ a u => pF_Tmap_le s a u) hK
    ?_ ?_ v f ?_
  · intro u
    simpa using hInv u
  · intro m hm hmn
    simpa using hSlow m hm hmn
  · simpa using hEq

end

end TorusEuler.Paper.Lib.S53

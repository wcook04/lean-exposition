import Breakdown.Cert.FixedPointCount

namespace Breakdown
namespace GridSimplex

def vertex {k p : ℕ} (v : Fin k → Fin p) (τ : Equiv.Perm (Fin k)) (j : ℕ) : Fin k → ℕ :=
  fun i => (v i : ℕ) + if (τ i : ℕ) < j then 1 else 0

def IsFull {k p : ℕ} (L : (Fin k → ℕ) → ℕ) (v : Fin k → Fin p) (τ : Equiv.Perm (Fin k)) : Prop :=
  Covers (fun j : Fin (k + 1) => L (vertex v τ (j : ℕ))) k

def IsDoor {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ) (v : Fin (k + 1) → Fin p)
    (τ : Equiv.Perm (Fin (k + 1))) (j : Fin (k + 2)) : Prop :=
  CoversFrom (fun t : Fin (k + 2) => L (vertex v τ (t : ℕ))) j (k + 1)

def OnBoundary {k p : ℕ} (v : Fin (k + 1) → Fin p) (τ : Equiv.Perm (Fin (k + 1)))
    (j : Fin (k + 2)) : Prop :=
  (j = 0 ∧ (v (τ.symm 0) : ℕ) + 1 = p) ∨
    (j = Fin.last (k + 1) ∧ (v (τ.symm (Fin.last k)) : ℕ) = 0)

open Classical in
noncomputable def fullSet {k p : ℕ} (L : (Fin k → ℕ) → ℕ) :
    Finset ((Fin k → Fin p) × Equiv.Perm (Fin k)) :=
  Finset.univ.filter fun s => IsFull L s.1 s.2

open Classical in
noncomputable def doorSet {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ) :
    Finset ((Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2)) :=
  Finset.univ.filter fun s => IsDoor L s.1 s.2.1 s.2.2

open Classical in
noncomputable def boundaryDoorSet {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ) :
    Finset ((Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2)) :=
  (doorSet L).filter fun s => OnBoundary s.1 s.2.1 s.2.2

theorem mem_fullSet {k p : ℕ} (L : (Fin k → ℕ) → ℕ)
    (s : (Fin k → Fin p) × Equiv.Perm (Fin k)) :
    s ∈ fullSet L ↔ IsFull L s.1 s.2 := by
  classical
  simp [fullSet]

theorem mem_doorSet {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2)) :
    s ∈ doorSet L ↔ IsDoor L s.1 s.2.1 s.2.2 := by
  classical
  simp [doorSet]

theorem mem_boundaryDoorSet {k p : ℕ} (L : (Fin (k + 1) → ℕ) → ℕ)
    (s : (Fin (k + 1) → Fin p) × Equiv.Perm (Fin (k + 1)) × Fin (k + 2)) :
    s ∈ boundaryDoorSet L ↔ IsDoor L s.1 s.2.1 s.2.2 ∧ OnBoundary s.1 s.2.1 s.2.2 := by
  classical
  simp [boundaryDoorSet, doorSet]

theorem vertex_le {k p : ℕ} (v : Fin k → Fin p) (τ : Equiv.Perm (Fin k)) (j : ℕ) (i : Fin k) :
    vertex v τ j i ≤ p := by
  have h := (v i).isLt
  unfold vertex
  split_ifs <;> omega

end GridSimplex
end Breakdown

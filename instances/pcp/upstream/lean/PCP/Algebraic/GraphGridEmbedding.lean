/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi

/-!
# Embedding a finite graph in a Cartesian grid

An injective vertex map pushes the original edges onto the grid and leaves every
unused grid vertex isolated. Restricting and extending colorings proves exact
colorability preservation for any nonempty color type. A finite cardinality
bound supplies the embedding; no field structure or running-time claim is needed.
-/

namespace PCP.Algebraic.GraphGridEmbedding

open Function SimpleGraph

section Padding

variable {V W C : Type*}

/-- Copy the edges along an embedding; unused vertices receive no edges. -/
def pad (G : SimpleGraph V) (e : V ↪ W) : SimpleGraph W := G.map e

/-- Every padded edge is an image of an original edge. -/
theorem pad_adj (G : SimpleGraph V) (e : V ↪ W) (x y : W) :
    (pad G e).Adj x y ↔ ∃ u v, G.Adj u v ∧ e u = x ∧ e v = y :=
  SimpleGraph.map_adj e G x y

/-- The embedded vertices induce exactly the original graph. -/
@[simp] theorem pad_adj_image (G : SimpleGraph V) (e : V ↪ W) (u v : V) :
    (pad G e).Adj (e u) (e v) ↔ G.Adj u v :=
  SimpleGraph.map_adj_apply

/-- Every unused padding vertex is isolated. -/
theorem pad_isIsolated (G : SimpleGraph V) (e : V ↪ W) (x : W)
    (hx : x ∉ Set.range e) : (pad G e).IsIsolated x := by
  intro y h
  obtain ⟨u, v, huv, hu, hv⟩ := (pad_adj G e x y).mp h
  exact hx ⟨u, hu⟩

/-- Extend a coloring by assigning the chosen color to unused vertices. -/
noncomputable def extendColoring (G : SimpleGraph V) (e : V ↪ W)
    (c : G.Coloring C) (defaultColor : C) : (pad G e).Coloring C :=
  Coloring.mk (Function.extend e c (fun _ => defaultColor)) (by
    intro x y h
    obtain ⟨u, v, huv, rfl, rfl⟩ := (pad_adj G e x y).mp h
    simpa only [e.injective.extend_apply] using c.valid huv)

/-- Extension preserves every original vertex's color. -/
@[simp] theorem extendColoring_apply_image (G : SimpleGraph V) (e : V ↪ W)
    (c : G.Coloring C) (defaultColor : C) (v : V) :
    extendColoring G e c defaultColor (e v) = c v :=
  e.injective.extend_apply c (fun _ => defaultColor) v

/-- Restrict a padded coloring to the embedded graph. -/
def restrictColoring (G : SimpleGraph V) (e : V ↪ W)
    (c : (pad G e).Coloring C) : G.Coloring C :=
  Coloring.mk (fun v => c (e v)) (fun h => c.valid ((pad_adj_image G e _ _).mpr h))

/-- Padding by isolated vertices preserves colorability for every nonempty color set. -/
theorem nonempty_coloring_pad_iff [Nonempty C] (G : SimpleGraph V) (e : V ↪ W) :
    Nonempty ((pad G e).Coloring C) ↔ Nonempty (G.Coloring C) := by
  constructor
  · rintro ⟨c⟩
    exact ⟨restrictColoring G e c⟩
  · rintro ⟨c⟩
    exact ⟨extendColoring G e c (Classical.choice inferInstance)⟩

/-- The nonzero-color-count specialization; zero colors would not color unused vertices. -/
theorem colorable_pad_iff (G : SimpleGraph V) (e : V ↪ W) (k : ℕ) [NeZero k] :
    (pad G e).Colorable k ↔ G.Colorable k :=
  nonempty_coloring_pad_iff G e

/-- In particular, the padded graph is 3-colorable exactly when the original graph is. -/
theorem threeColorable_pad_iff (G : SimpleGraph V) (e : V ↪ W) :
    (pad G e).Colorable 3 ↔ G.Colorable 3 := colorable_pad_iff G e 3

end Padding

section Grid

variable {V F σ : Type*}

/-- The Cartesian grid with each coordinate in the finite set `H`. -/
abbrev Grid (H : Finset F) (σ : Type*) := σ → H

/-- Grid points embed into the ambient coordinate space by forgetting membership proofs. -/
def gridPointEmbedding (H : Finset F) : Grid H σ ↪ (σ → F) where
  toFun x i := x i
  inj' _ _ h := funext (fun i => Subtype.ext (congrFun h i))

@[simp] theorem gridPointEmbedding_apply (H : Finset F) (x : Grid H σ) (i : σ) :
    gridPointEmbedding H x i = (x i).val := rfl

/-- Every coordinate of an embedded grid point belongs to the grid alphabet. -/
theorem gridPointEmbedding_mem (H : Finset F) (x : Grid H σ) (i : σ) :
    gridPointEmbedding H x i ∈ H := (x i).property

/-- The image is exactly the Cartesian grid in the ambient coordinate space. -/
theorem range_gridPointEmbedding (H : Finset F) :
    Set.range (gridPointEmbedding (σ := σ) H) = {x | ∀ i, x i ∈ H} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ i
    exact (y i).property
  · intro hx
    exact ⟨fun i => ⟨x i, hx i⟩, rfl⟩

variable [Fintype σ] [DecidableEq σ]

/-- The exact Cartesian-grid cardinality, including zero coordinates and empty alphabets. -/
@[simp] theorem card_grid (H : Finset F) :
    Fintype.card (Grid H σ) = H.card ^ Fintype.card σ := by
  simp only [Grid, Fintype.card_fun, Fintype.card_coe]

variable [Fintype V]

omit [DecidableEq σ] in
/-- The exact cardinal condition for fitting a finite vertex set into the grid. -/
theorem nonempty_grid_embedding_iff (H : Finset F) :
    Nonempty (V ↪ Grid H σ) ↔ Fintype.card V ≤ H.card ^ Fintype.card σ := by
  classical
  rw [Function.Embedding.nonempty_iff_card_le, card_grid]

omit [DecidableEq σ] in
/-- A cardinal bound supplies an actual vertex embedding in the grid. -/
noncomputable def gridEmbedding (H : Finset F)
    (h : Fintype.card V ≤ H.card ^ Fintype.card σ) : V ↪ Grid H σ :=
  Classical.choice ((nonempty_grid_embedding_iff H).mpr h)

omit [DecidableEq σ] in
/-- A finite graph fitting in the grid has a padded graph with exactly the same 3-colorability.
No nonemptiness assumption on the graph or grid alphabet is needed. -/
theorem exists_padded_grid_graph (G : SimpleGraph V) (H : Finset F)
    (h : Fintype.card V ≤ H.card ^ Fintype.card σ) :
    ∃ (e : V ↪ Grid H σ) (G' : SimpleGraph (Grid H σ)),
      (∀ u v, G'.Adj (e u) (e v) ↔ G.Adj u v) ∧
      (∀ x, x ∉ Set.range e → G'.IsIsolated x) ∧
      (G'.Colorable 3 ↔ G.Colorable 3) := by
  classical
  let e := gridEmbedding H h
  exact ⟨e, pad G e, pad_adj_image G e, pad_isIsolated G e, threeColorable_pad_iff G e⟩

end Grid

end PCP.Algebraic.GraphGridEmbedding

/-
Copyright (c) 2026 Troy Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Troy Lee
-/
import PCP.Complexity.DerivedSeedFinishCost

/-! # Complete charged runtime of numeric derived-seed materialization -/

namespace PCP.Lang.DerivedSeed

open PCP.Algebraic ThreeColorSeedIndex ThreeColorFullFieldSampling BinaryFieldCode
open LocalCorrection DerivedGrid

attribute [local irreducible] materialize encodePoints edge computed payload finish

def programCost (C : ℕ) (k : Certificate) (t n m h W : ℕ) (x : List Bool) : ℕ :=
  materializeCost (baseDimension k n) m t W +
    pointsCost (baseDimension k n) t h + 2*encodeCost (k.outer.dimension n) t +
    edgeCost C (baseDimension k n) t h n x + fixedConstant (payload k)*(W+1)+5

/-- Uniform concrete runtime, including public edge computation and every stored array. -/
theorem program_cost : ∃ C : ℕ, ∀ (t n m : ℕ) [NeZero t] (k : Certificate)
    (nodes : Fin 5 → OuterBranch.Field t) (ζ : OuterBranch.Field t)
    (h : ℕ) (_hh : h ≤ 2 ^ t) (x : List Bool) (s : DerivedGrid.Sample k t n m)
    (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 300 112),
    Input k (padDerived s) st → Public (n := n) (m := m) nodes ζ h x qs bs st →
    SourceBound W st → ((program k).run st).2 ≤ programCost C k t n m h W x := by
  obtain ⟨C, hC⟩ := edge_cost
  refine ⟨C, ?_⟩
  intro t n m _ k nodes ζ h hh x s qs bs W st hi hp hb
  have hm := materialize_cost k (padDerived s) W st hi hb.input
  have hout := materialize_run k (padDerived s) st hi
  have hu := hp.materialized
  have hub := hb.materialize
  have hcode : Nat.size ((derivedCodec (BinaryMaterializedField.coordinates t)
      (baseDimension k n) m 4 3).equiv (padDerived s)).val ≤ W := hi.seed ▸ hb.input 3
  generalize heq : (materialize.run st).1 = u at *
  have hui := hout.2.2.2.1
  have hud := hout.2.2.2.2
  have hpoints := encodePoints_cost k h hh s u hui.width hui.card hu.count hu.modulus
    hui.empty hout.1
  have ht := (encodePoints_reg u 240 (by decide) (by decide) (by decide)).trans hui.width
  have hh' := (encodePoints_reg u 279 (by decide) (by decide) (by decide)).trans hu.count
  have hn := (encodePoints_reg u 280 (by decide) (by decide) (by decide)).trans hu.dimension
  have hmod := (encodePoints_list u 101 (by decide) (by decide) (by decide)).trans hu.modulus
  have hempty := (encodePoints_list u 100 (by decide) (by decide) (by decide)).trans hui.empty
  have hpoint := (encodePoints_list u 109 (by decide) (by decide) (by decide)).trans hout.1
  have hgraph := (encodePoints_list u 111 (by decide) (by decide) (by decide)).trans hu.graph
  have hedge := hC t n m k h hh x s _ ht hh' hn hmod hempty hpoint hgraph
  have hcomputed : ((computed k).run u).2 ≤
      pointsCost (baseDimension k n) t h+2*encodeCost (k.outer.dimension n) t+
        edgeCost C (baseDimension k n) t h n x+3 := by
    rw [computed, run_seq_snd]
    omega
  have hfinish := payload_cost k W ((computed k).run u).1 hub.computed
    (hud.computed.bound W hcode)
  simp only [program, run_seq_snd, heq, finish]
  unfold programCost
  omega

end PCP.Lang.DerivedSeed

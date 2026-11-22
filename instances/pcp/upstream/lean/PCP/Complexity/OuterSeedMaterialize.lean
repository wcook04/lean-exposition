import PCP.Complexity.OuterSeedWords

/-! # Complete arrays for an actual decoded outer sample -/

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

structure Stored (k : Kind) (s : Sample k t n m) (st : State 180 80) : Prop where
  inner : InnerStored k s st
  primary : PrimaryStored k s st
  left : st.lists 42 = List.ofFn (fun i => (fieldEquiv t (k.vector s.1.1 i)).val)
  right : st.lists 43 = List.ofFn (fun i => (fieldEquiv t (k.vector s.1.2 i)).val)
  direction : st.lists 44 = List.ofFn
    (fun i => (fieldEquiv t (StandardCorrection.vector s.2.2.1.1 i)).val)
  label : st.lists 45 = List.ofFn (fun i => (s.2.2.1.2 i).val)

def materialize (k : Kind) : Stmt 180 80 := .seq (hadamard k)
  (.seq (point 156 164 42) (.seq (point 155 164 43) (.seq direction bits)))

attribute [local irreducible] hadamard point direction bits

theorem materialize_run (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st)
    (hi : InnerStored k s st) :
    Stored k s ((materialize k).run st).1 ∧ Data k s ((materialize k).run st).1 ∧
      Public (n := n) (m := m) k a ζ qs bs ((materialize k).run st).1 ∧
      Frame st ((materialize k).run st).1 := by
  have hh := hadamard_run k s st hp.width hp.empty hd
  have hf := hadamard_frame k st
  have hid := hf.data k s hd
  have hii := hf.inner k s hi
  have hip := hp.of_frame hf.public
  simp only [materialize, run_seq_fst]
  generalize hu : ((hadamard k).run st).1 = u at *
  have hl := point_run (k.vector s.1.1) 156 164 42 u (hid 6) hip.dimension
    (by decide) hip.card hip.empty
  have hlf := point_frame 156 164 42 u
  have hld := hlf.data k s hid
  have hli := hlf.inner (by decide) k s hii
  have hlh := hlf.primary (by decide) k s hh
  have hlp := hip.of_frame (hlf.public (by decide))
  have hlfull := hf.public.trans (hlf.public (by decide))
  generalize hv : ((point 156 164 42).run u).1 = v at *
  have hr := point_run (k.vector s.1.2) 155 164 43 v (hld 5) hlp.dimension
    (by decide) hlp.card hlp.empty
  have hrf := point_frame 155 164 43 v
  have hrd := hrf.data k s hld
  have hri := hrf.inner (by decide) k s hli
  have hrh := hrf.primary (by decide) k s hlh
  have hrp := hlp.of_frame (hrf.public (by decide))
  have hrl := (hrf.lists 42 (by decide) (by decide)).trans hl
  have hrfull := hlfull.trans (hrf.public (by decide))
  generalize hw : ((point 155 164 43).run v).1 = w at *
  have hc := direction_run s.2.2.1.1 w (hrd 3) hrp.base hrp.card hrp.empty
  have hcf := direction_frame w
  have hcd := hcf.data k s hrd
  have hci := hcf.inner (by decide) k s hri
  have hch := hcf.primary (by decide) k s hrh
  have hcp := hrp.of_frame (hcf.public (by decide))
  have hcl := (hcf.lists 42 (by decide) (by decide)).trans hrl
  have hcr := (hcf.lists 43 (by decide) (by decide)).trans hr
  have hcfull := hrfull.trans (hcf.public (by decide))
  generalize hx : (direction.run w).1 = x at *
  have hb := bits_run s.2.2.1.2 x (hcd 2) hcp.width hcp.empty
  have hbf := bits_frame x
  exact ⟨⟨hbf.inner (by decide) k s hci, hbf.primary (by decide) k s hch,
    (hbf.lists 42 (by decide) (by decide)).trans hcl,
    (hbf.lists 43 (by decide) (by decide)).trans hcr,
    (hbf.lists 44 (by decide) (by decide)).trans hc, hb⟩,
    hbf.data k s hcd, hcp.of_frame (hbf.public (by decide)),
    hcfull.trans (hbf.public (by decide))⟩

end PCP.Lang.OuterSeed

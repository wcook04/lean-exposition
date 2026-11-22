import PCP.Complexity.OuterSeedDecodeCost
import PCP.Complexity.OuterSeedInnerCost
import PCP.Complexity.OuterSeedWordCost

/-! # Polynomial charged cost of the complete actual outer sampler materializer -/

namespace PCP.Lang.OuterSeed

open PCP.Algebraic ThreeColorSeedIndex BinaryFieldCode OuterBranch

variable {t n m : ℕ} [NeZero t]

attribute [local irreducible] unpack inner materialize finalize hadamard point direction bits

def materializeConstant : ℕ := hadConstant+pointConstant 156+pointConstant 155+
  directionConstant+bitsConstant+4

theorem materialize_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hd : Data k s st)
    (hb : SourceBound W st) (hs : Nat.size ((seedCodec k t n m).equiv s).val ≤ W) :
    ((materialize k).run st).2 ≤ materializeConstant*(budget t (k.dimension n) m W)^5 := by
  have hh := hadamard_cost k s W st hp.width hp.empty hd hb (hd.bound k s W st hs)
  have hf := hadamard_frame k st
  have hdata := hf.data k s hd
  have hpub := hp.of_frame hf.public
  have hbound := hb.of_frame hf.public
  simp only [materialize,run_seq_snd]
  generalize hu : ((hadamard k).run st).1 = u at *
  have hl := point_cost (m := m) 156 (by decide) 42 (k.dimension n) W u hpub.dimension
    hpub.card hpub.empty hbound (hdata.bound k s W u hs)
  have hlf := point_frame 156 164 42 u
  have hld := hlf.data k s hdata
  have hlp := hpub.of_frame (hlf.public (by decide))
  have hlb := hbound.of_frame (hlf.public (by decide))
  generalize hv : ((point 156 164 42).run u).1 = v at *
  have hr := point_cost (m := m) 155 (by decide) 43 (k.dimension n) W v hlp.dimension
    hlp.card hlp.empty hlb (hld.bound k s W v hs)
  have hrf := point_frame 155 164 43 v
  have hrd := hrf.data k s hld
  have hrp := hlp.of_frame (hrf.public (by decide))
  have hrb := hlb.of_frame (hrf.public (by decide))
  generalize hw : ((point 155 164 43).run v).1 = w at *
  have hc := direction_cost (k.dimension n) W w hrp.base hrp.card hrp.empty hrb
    (hrd.bound k s W w hs)
  have hcf := direction_frame w
  have hcd := hcf.data k s hrd
  have hcp := hrp.of_frame (hcf.public (by decide))
  have hcb := hrb.of_frame (hcf.public (by decide))
  generalize hx : (direction.run w).1 = x at *
  have hcbit := bits_cost (k.dimension n) m W x hcp.width hcp.empty hcb (hcd.bound k s W x hs)
  have hA : 1 ≤ budget t (k.dimension n) m W :=
    (by decide : 1 ≤ 20).trans (budget_basic t (k.dimension n) m W).1
  have h45 : (budget t (k.dimension n) m W)^4 ≤ (budget t (k.dimension n) m W)^5 :=
    Nat.pow_le_pow_right hA (by decide)
  have hl' := hl.trans (Nat.mul_le_mul_left _ h45)
  have hr' := hr.trans (Nat.mul_le_mul_left _ h45)
  have hc' := hc.trans (Nat.mul_le_mul_left _ h45)
  have hb' := hcbit.trans (Nat.mul_le_mul_left _ h45)
  have h1 := Nat.one_le_pow 5 (budget t (k.dimension n) m W) hA
  unfold materializeConstant
  nlinarith only [hh,hl',hr',hc',hb',h1]

set_option maxRecDepth 1024 in
theorem finalize_cost (k : Kind) (W : ℕ) (st : State 180 80)
    (hb : SourceBound W st) (hd : DataBound W st) :
    ((finalize k).run st).2 ≤ fixedConstant (finalize k)*(W+1) := by
  apply fixed_cost (finalize k) (by unfold finalize; cases k <;> decide)
    (by unfold finalize; cases k <;> decide) (by unfold finalize; cases k <;> decide) W st hb hd

def costConstant (k : Kind) : ℕ := unpackConstant k+innerConstant k+materializeConstant+
  fixedConstant (finalize k)+3

/-- Every generated coefficient and coordinate word is charged, with arbitrary initial scratch. -/
theorem program_cost (k : Kind) (a : Fin 5 → Field t) (ζ : Field t)
    (s : Sample k t n m) (qs : List ℕ) (bs : List Bool) (W : ℕ) (st : State 180 80)
    (hp : Public (n := n) (m := m) k a ζ qs bs st) (hb : SourceBound W st)
    (hc : st.regs 171 = ((seedCodec k t n m).equiv s).val) :
    ((program k).run st).2 ≤ costConstant k*(budget t (k.dimension n) m W)^5 := by
  have hu := unpack_run k a ζ s qs bs st hp hc
  have huc := unpack_cost k a ζ s qs bs W st hp hb hc
  have hub := hb.of_frame hu.2.2
  have hcode : Nat.size ((seedCodec k t n m).equiv s).val ≤ W :=
    hc ▸ hb.regs 171 (by decide) (by decide)
  simp only [program,run_seq_snd]
  generalize hx : ((unpack k).run st).1 = u at *
  have hi := inner_run k a ζ s qs bs u hu.2.1 hu.1
  have hic := inner_cost k a ζ s qs bs W u hu.2.1 hu.1 hub (hu.1.bound k s W u hcode)
  have hib := hub.of_frame hi.2.2.2
  generalize hy : ((inner k).run u).1 = v at *
  have hm := materialize_run k a ζ s qs bs v hi.2.1 hi.2.2.1 hi.1
  have hmc := materialize_cost k a ζ s qs bs W v hi.2.1 hi.2.2.1 hib hcode
  have hmb := hib.of_frame hm.2.2.2
  generalize hz : ((materialize k).run v).1 = w at *
  have hf := finalize_cost k W w hmb (hm.2.1.bound k s W w hcode)
  have hA : 1 ≤ budget t (k.dimension n) m W :=
    (by decide : 1 ≤ 20).trans (budget_basic t (k.dimension n) m W).1
  have hu' := huc.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hA (by decide : 4≤5)))
  have hf' := hf.trans (Nat.mul_le_mul_left _ ((budget_basic t (k.dimension n) m W).2.1.trans
    (Nat.le_pow (by decide : 0<5))))
  have h1 := Nat.one_le_pow 5 (budget t (k.dimension n) m W) hA
  unfold costConstant
  nlinarith only [hu',hic,hmc,hf',h1]

end PCP.Lang.OuterSeed

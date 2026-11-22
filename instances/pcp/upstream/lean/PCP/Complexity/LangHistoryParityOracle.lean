import PCP.Complexity.LangHistoryParityCost
import PCP.Algebraic.InterpolationQueryParity

/-!
# Physical history parity and characteristic-two residuals
-/

namespace PCP.Lang.HistoryParity

open PCP.Algebraic

/-- The accumulator is the binary field sum of the actual history reads. -/
theorem parity_oracle (qs xs : List ℕ) (bs : List Bool) (st : State 12 6)
    (hq : st.lists 0 = qs) (hb : st.lists 1 = bs.map Bool.toNat)
    (hx : st.lists 4 = xs) :
    (parity.run st).1.regs 8 =
      ((xs.map (fun a => BinarySeedPadding.boolEquiv
        (QueryTree.answersOracle qs bs a))).sum).val := by
  rw [(parity_run st).1, hq, hb, hx, BinarySeedPadding.bool_sum_cast, ZMod.val_natCast]
  congr 2
  apply List.map_congr_left
  intro a _
  exact QueryHistory.read_bool qs bs a

/-- Acceptance means precisely that the binary field sum is zero. -/
theorem program_oracle (qs xs : List ℕ) (bs : List Bool) (st : State 12 6)
    (hq : st.lists 0 = qs) (hb : st.lists 1 = bs.map Bool.toNat)
    (hx : st.lists 4 = xs) :
    (program.run st).1.regs 11 = (decide
      ((xs.map (fun a => BinarySeedPadding.boolEquiv
        (QueryTree.answersOracle qs bs a))).sum = 0)).toNat := by
  rw [program, run_seq_fst, finish_run, parity_oracle qs xs bs st hq hb hx]
  simp only [ZMod.val_eq_zero]

/-- Exact interpolation acceptance for every physical address embedding and answer history. -/
theorem program_interpolation {F σ : Type*} [Field F] [DecidableEq F]
    [Algebra (ZMod 2) F] {c t r : ℕ} (hr : 1 ≤ r)
    (ρ : F ≃ₗ[ZMod 2] (Fin t → ZMod 2)) (nodes : Fin (c + 1) → F)
    (u v : σ → F) (z : F) (w : Fin t → ZMod 2)
    (index : ((σ → F) × BinaryPolynomialSpace.Coefficients t r) → ℕ)
    (qs : List ℕ) (bs : List Bool) (st : State 12 6)
    (hq : st.lists 0 = qs) (hb : st.lists 1 = bs.map Bool.toNat)
    (hx : st.lists 4 =
      (ComputableBinaryLagrangeConstraint.queries hr ρ nodes u v z w).map index) :
    (program.run st).1.regs 11 = (decide
      (ComputableBinaryLagrangeConstraint.check hr ρ nodes
        (fun x label => BinarySeedPadding.boolEquiv
          (QueryTree.answersOracle qs bs (index (x, label)))) u v z w = 0)).toNat := by
  rw [ComputableBinaryLagrangeConstraint.check_eq_query_sum]
  have h := program_oracle qs _ bs st hq hb hx
  simpa only [List.map_map, Function.comp_def, Prod.mk.eta] using h

end PCP.Lang.HistoryParity

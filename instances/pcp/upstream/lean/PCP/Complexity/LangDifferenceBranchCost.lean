import PCP.Complexity.LangDifferenceBranch
import PCP.Complexity.LangDifferenceQueriesCost

/-!
# Charged bound for the complete physical difference callback
-/

namespace PCP.Lang.DifferenceBranch

open PCP.Algebraic BinaryPolynomialSpace

variable {t : ℕ}

theorem differenceAddress_size (A B C1 C3 x y z W : ℕ)
    (hA : Nat.size A ≤ W) (hB : Nat.size B ≤ W) (h1 : Nat.size C1 ≤ W)
    (h3 : Nat.size C3 ≤ W) (hx : Nat.size x ≤ W) (hy : Nat.size y ≤ W)
    (hz : Nat.size z ≤ W) :
    Nat.size (DifferenceQueries.differenceAddress A B C1 C3 x y z) ≤ 10 * (W + 1) := by
  have := size_mul_le A C3
  have := size_mul_le B C1
  have := size_add_le (A * C3) (B * C1)
  have := size_mul_le A y
  have := size_add_le x (A * y)
  have := size_mul_le C3 (x + A * y)
  have := size_add_le z (C3 * (x + A * y))
  have := size_add_le (A * C3 + B * C1) (z + C3 * (x + A * y))
  unfold DifferenceQueries.differenceAddress
  omega

theorem colorAddress_size (C x z W : ℕ) (hC : Nat.size C ≤ W)
    (hx : Nat.size x ≤ W) (hz : Nat.size z ≤ W) :
    Nat.size (z + C * x) ≤ 10 * (W + 1) := by
  have := size_mul_le C x
  have := size_add_le z (C * x)
  omega

theorem prepare_cost (st : State 80 32) (x y z W : ℕ) (hq : st.lists 24 = [x, y, z])
    (hx : Nat.size x ≤ W) (hy : Nat.size y ≤ W) (hz : Nat.size z ≤ W) :
    (prepare.run st).2 ≤ 6 * W + 10 := by
  simp [prepare, Stmt.run, hq, Function.update, listSize]
  omega

theorem verdict_cost (qs : List ℕ) (bs : List Bool) (x y z W : ℕ) (st : State 80 32)
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hx : st.regs 8 = x) (hy : st.regs 9 = y) (hz : st.regs 10 = z)
    (hqs : listSize qs ≤ W) (hbs : listSize (bs.map Bool.toNat) ≤ W)
    (hxs : Nat.size x ≤ W) (hys : Nat.size y ≤ W) (hzs : Nat.size z ≤ W) :
    (verdict.run st).2 ≤ (3 * QueryHistory.passConstant + 160) * (3 * W + 2) ^ 2 := by
  have hc : DifferenceVerdict.Context qs (bs.map Bool.toNat) x y z
      (st.restrict (Fin.castLE (by decide)) verdictLists) := ⟨hq, hb, hx, hy, hz⟩
  have h := DifferenceVerdict.program_cost qs bs x y z W _ hc hqs hbs hxs hys hzs
  rw [← verdict_result st] at h
  exact h

def programConstant : ℕ := BooleanLabelTransform.queryConstant + WordCodec.passConstant * 3 +
  DifferenceQueries.finishConstant + 2000 * (3 * QueryHistory.passConstant + 160) + 500

/-- The complete physical callback has one uniform degree-eight charged bound. -/
theorem program_cost (w : Fin t → ZMod 2) (qs : List ℕ) (bs : List Bool)
    (st : State 80 32) (W : ℕ) (ht : st.regs 20 = t) (he : st.lists 7 = [])
    (hw : st.lists 17 = List.ofFn (fun i => (w i).val))
    (hq : st.lists 30 = qs) (hb : st.lists 31 = bs.map Bool.toNat)
    (hqs : listSize qs ≤ W) (hbs : listSize (bs.map Bool.toNat) ≤ W)
    (hr : ∀ i : Fin 80, 57 ≤ i.val → i.val ≤ 62 → Nat.size (st.regs i) ≤ W) :
    (program.run st).2 ≤ programConstant * (2 ^ t + W + 8) ^ 8 := by
  have hq0 := Nat.zero_le (2 ^ t)
  have hW0 := Nat.zero_le W
  let p := BooleanCoefficientArithmetic.homogeneousIndex (by decide : 1 ≤ 3) w
  let z := HadamardLabel.code p
  let x := DifferenceQueries.differenceAddress (st.regs 59) (st.regs 60) (st.regs 61)
    (st.regs 62) (st.regs 57) (st.regs 58) z
  let y := z + st.regs 62 * st.regs 57
  let v := z + st.regs 62 * st.regs 58
  let V := 10 * (W + 2 ^ t + 1)
  have hs (i : Fin 80) (hi : 57 ≤ i.val) (hi' : i.val ≤ 62) :
      Nat.size (st.regs i) ≤ W + 2 ^ t := (hr i hi hi').trans (by omega)
  have hsz : Nat.size z ≤ W + 2 ^ t := (HadamardLabel.code_size p).trans (by omega)
  have hx : Nat.size x ≤ V := differenceAddress_size _ _ _ _ _ _ _ _
    (hs 59 (by decide) (by decide)) (hs 60 (by decide) (by decide))
    (hs 61 (by decide) (by decide)) (hs 62 (by decide) (by decide))
    (hs 57 (by decide) (by decide)) (hs 58 (by decide) (by decide)) hsz
  have hy : Nat.size y ≤ V := colorAddress_size _ _ _ _
    (hs 62 (by decide) (by decide)) (hs 57 (by decide) (by decide)) hsz
  have hv : Nat.size v ≤ V := colorAddress_size _ _ _ _
    (hs 62 (by decide) (by decide)) (hs 58 (by decide) (by decide)) hsz
  have hquery : (DifferenceQueries.program.run st).1.lists 24 = [x, y, v] :=
    DifferenceQueries.program_run w st ht he hw
  have hcq := DifferenceQueries.program_cost w st W ht he hw hr
  have huq := (query_program_frame 30 (by decide) st).trans hq
  have hub := (query_program_frame 31 (by decide) st).trans hb
  generalize hu : (DifferenceQueries.program.run st).1 = u at *
  have hp := prepare_run u x y v hquery
  have hpc := prepare_cost u x y v V hquery hx hy hv
  have hpq := (run_lists_frame prepare 30 (by decide) u).trans huq
  have hpb := (run_lists_frame prepare 31 (by decide) u).trans hub
  generalize hv' : (prepare.run u).1 = v' at *
  have hWV : W ≤ V := by dsimp [V]; omega
  have hvc := verdict_cost qs bs x y v V v' hpq hpb hp.1 hp.2.1 hp.2.2
    (hqs.trans hWV) (hbs.trans hWV) hx hy hv
  have hbase : 1 ≤ 2 ^ t + W + 8 := by omega
  have hlin : V ≤ 10 * (2 ^ t + W + 8) := by dsimp [V]; omega
  have hpow : 2 ^ t + W + 8 ≤ (2 ^ t + W + 8) ^ 8 := Nat.le_pow (by decide)
  have hsq : (2 ^ t + W + 8) ^ 2 ≤ (2 ^ t + W + 8) ^ 8 :=
    Nat.pow_le_pow_right hbase (by decide)
  have hsq' : (3 * V + 2) ^ 2 ≤ 1024 * (2 ^ t + W + 8) ^ 8 := by
    have ha : 3 * V + 2 ≤ 32 * (2 ^ t + W + 8) := by omega
    have hh := Nat.pow_le_pow_left ha 2
    nlinarith only [hh, hsq]
  have hvc' := hvc.trans (Nat.mul_le_mul_left _ hsq')
  have hpos : 1 ≤ (2 ^ t + W + 8) ^ 8 := Nat.one_le_pow _ _ (by omega)
  simp only [program, run_seq_snd, hu, hv']
  unfold programConstant
  nlinarith only [hcq, hpc, hvc', hlin, hpow, hpos]

end PCP.Lang.DifferenceBranch

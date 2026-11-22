import PCP.Complexity.LangSplitFirstCost
import PCP.Complexity.LangRenaming

/-!+# Running a concrete program on the first word of a public triple

The suffix containing the random bits and answer history is preserved verbatim.
The wrapped program receives a disjoint, freshly initialized register allocation.
-/

namespace PCP.Lang.RunOnFirst

variable (P : Prog)

def r : Fin 5 → Fin (5 + P.R) := Fin.castAdd P.R
def q : Fin 2 → Fin (2 + P.Q) := Fin.castAdd P.Q
def pr : Fin P.R → Fin (5 + P.R) := Fin.natAdd 5
def pq : Fin P.Q → Fin (2 + P.Q) := Fin.natAdd 2

private theorem right_injective (m n : ℕ) : Function.Injective (@Fin.natAdd n m) := by
  intro a b h
  apply Fin.ext
  have := congrArg Fin.val h
  simpa using this

private theorem left_ne_right {m n : ℕ} (i : Fin m) (j : Fin n) :
    i.castAdd n ≠ Fin.natAdd m j := by
  intro h
  have he := congrArg Fin.val h
  change i.val = m + j.val at he
  have := i.isLt
  omega

def split : Stmt (5 + P.R) (2 + P.Q) := SplitFirst.program.rename (r P) (q P)
def call : Stmt (5 + P.R) (2 + P.Q) := P.body.rename (pr P) (pq P)

def finish : Stmt (5 + P.R) (2 + P.Q) :=
  .seq (.copy (q P 0) (q P 1)) (.seq (.assign (r P 4) (.const 2))
    (.seq (.push (q P 1) (r P 4)) (.seq (.rev (pq P P.outL))
      (.revApp (pq P P.outL) (q P 1)))))

def program : Prog where
  R := 5 + P.R
  Q := 2 + P.Q
  hQ := by omega
  body := .seq (split P) (.seq (.copy (q P 1) (pq P P.inL))
    (.seq (call P) (finish P)))

def initial (l : List ℕ) : State (5 + P.R) (2 + P.Q) :=
  ⟨fun _ => 0, fun L => if L.val = 0 then l else []⟩

theorem init_program (l : List ℕ) : (program P).init l = initial P l := by
  unfold Prog.init initial
  congr 1
  funext L
  simp only [Fin.ext_iff, Prog.inL]

def splitState (l : List ℕ) := ((split P).run (initial P l)).1
def callState (xs ys : List ℕ) := setList (splitState P (xs ++ 2 :: ys)) (pq P P.inL) xs

theorem split_result (xs ys : List ℕ) (hx : ∀ v ∈ xs, v ≠ 2) :
    (splitState P (xs ++ 2 :: ys)).lists (q P 0) = ys ∧
    (splitState P (xs ++ 2 :: ys)).lists (q P 1) = xs := by
  have hr := congrArg Prod.fst (SplitFirst.program.run_rename (r P) (q P)
    (Fin.castAdd_injective _ _) (Fin.castAdd_injective _ _)
    (initial P (xs ++ 2 :: ys)))
  have hp := SplitFirst.program_run xs ys hx
    ((initial P (xs ++ 2 :: ys)).restrict (r P) (q P))
    rfl rfl
  rw [← hr] at hp
  exact hp

theorem call_initial (xs ys : List ℕ) :
    (callState P xs ys).restrict (pr P) (pq P) = P.init xs := by
  have hreg (i : Fin P.R) : (splitState P (xs ++ 2 :: ys)).regs (pr P i) = 0 :=
    SplitFirst.program.run_rename_reg_outside (r P) (q P) (pr P i)
      (fun j => left_ne_right j i) _
  have hlist (L : Fin P.Q) : (splitState P (xs ++ 2 :: ys)).lists (pq P L) = [] := by
    rw [splitState, split, SplitFirst.program.run_rename_list_outside
      (r P) (q P) (pq P L) (fun j => left_ne_right j L)]
    change (if 2 + L.val = 0 then xs ++ 2 :: ys else []) = []
    rw [ite_eq_right (by omega : 2 + L.val ≠ 0)]
  unfold State.restrict callState setList Prog.init
  congr 1
  · funext i
    exact hreg i
  · funext L
    have hi : Function.Injective (pq P) := right_injective 2 P.Q
    simp only [Function.comp_apply, Function.update_apply, hi.eq_iff, hlist]

theorem call_result (xs ys : List ℕ) :
    (((call P).run (callState P xs ys)).1.restrict (pr P) (pq P),
      ((call P).run (callState P xs ys)).2) = P.body.run (P.init xs) := by
  have hp := P.body.run_rename (pr P) (pq P)
    (right_injective 5 P.R) (right_injective 2 P.Q) (callState P xs ys)
  rw [call_initial] at hp
  exact hp

theorem call_suffix (xs ys : List ℕ) (hx : ∀ v ∈ xs, v ≠ 2) :
    ((call P).run (callState P xs ys)).1.lists (q P 0) = ys := by
  rw [call, P.body.run_rename_list_outside (pr P) (pq P) (q P 0)
    (fun j => (left_ne_right (0 : Fin 2) j).symm)]
  have hn : q P 0 ≠ pq P P.inL := left_ne_right (0 : Fin 2) P.inL
  simp only [callState, setList_lists, Function.update_of_ne hn]
  exact (split_result P xs ys hx).1

theorem finish_run (st : State (5 + P.R) (2 + P.Q)) :
    ((finish P).run st).1.lists (q P 1) =
      st.lists (pq P P.outL) ++ 2 :: st.lists (q P 0) := by
  have hright : pq P P.outL ≠ q P 1 := (left_ne_right (1 : Fin 2) P.outL).symm
  simp [finish, Stmt.run, Expr.eval, Function.update, hright, Ne.symm hright]

/-- The actual source program changes only the first separator-delimited word. -/
theorem program_run (xs ys : List ℕ) (hx : ∀ v ∈ xs, v ≠ 2) :
    (program P).run (xs ++ 2 :: ys) = P.run xs ++ 2 :: ys := by
  have hout := congrArg (fun z => z.1.lists P.outL) (call_result P xs ys)
  change ((call P).run (callState P xs ys)).1.lists (pq P P.outL) = P.run xs at hout
  have hs := split_result P xs ys hx
  unfold Prog.run
  rw [init_program]
  change ((finish P).run ((call P).run
    (setList (splitState P (xs ++ 2 :: ys)) (pq P P.inL)
      ((splitState P (xs ++ 2 :: ys)).lists (q P 1)))).1).1.lists (q P 1) = _
  rw [hs.2, finish_run]
  change ((call P).run (callState P xs ys)).1.lists (pq P P.outL) ++
    2 :: ((call P).run (callState P xs ys)).1.lists (q P 0) = _
  rw [hout, call_suffix P xs ys hx]
  rfl

end PCP.Lang.RunOnFirst

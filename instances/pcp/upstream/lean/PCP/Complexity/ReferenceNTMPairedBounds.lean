import PCP.Complexity.ReferenceNTMPairedStream
import PCP.Complexity.ReferenceNTMPrefix
import PCP.Complexity.ArithmeticStreamCost

/-! # Linear register-size bounds for the paired reference simulation -/

namespace PCP.ReferenceNTM.PairedStream

open Complexity PCP.Lang PCP.Lang.ArithmeticStream

variable {k q : ℕ} (tm : NTM k) (eQ : tm.Q ≃ Fin q)

def storageBound (q inputLength witnessLength : ℕ) : ℕ :=
  Nat.size q + 2 * (inputLength + witnessLength + 2) + 3

theorem encode_run_size (x w : List Bool) (phase : Bool) (i : Fin (width k)) :
    Nat.size (encode tm eQ (Cfg.run w (Cfg.init tm x)) phase.toNat
      (4 ^ (x.length + 1)) i) ≤ storageBound q x.length w.length := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [encode, encodeRegs, Fin.snoc_last]
    have h : Nat.size (4 ^ (x.length + 1)) = 2 * (x.length + 1) + 1 := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul, Nat.size_pow]
    rw [h]
    dsimp [storageBound]
    omega
  · refine Fin.lastCases ?_ (fun j => ?_) j
    · cases phase <;> simp [encode, encodeRegs, storageBound]
    · simp only [encode, encodeRegs, Fin.snoc_castSucc]
      have h := Cfg.run_encode_size tm eQ x w j
      dsimp [storageBound]
      omega

theorem encode_load_size (x w u : List Bool) (hu : u <+: x) (i : Fin (width k)) :
    Nat.size (encode tm eQ (Cfg.init tm u) 0 (4 ^ (u.length + 1)) i) ≤
      storageBound q x.length w.length := by
  have h := encode_run_size tm eQ u [] false i
  have hl := hu.length_le
  simp only [Cfg.run, Bool.toNat_false, List.length_nil] at h
  dsimp [storageBound] at h ⊢
  omega

theorem encode_prefix_run_size (x w v : List Bool) (hv : v <+: w) (i : Fin (width k)) :
    Nat.size (encode tm eQ (Cfg.run v (Cfg.init tm x)) 1 (4 ^ (x.length + 1)) i) ≤
      storageBound q x.length w.length := by
  have h := encode_run_size tm eQ x v true i
  have hl := hv.length_le
  simp only [Bool.toNat_true] at h
  dsimp [storageBound] at h ⊢
  omega

/-- The bound holds at every actual prefix consumed by the concrete stream loop. -/
theorem prefix_fold_size (x w : List Bool) (ys zs : List ℕ)
    (h : pair x w = ys ++ zs) (i : Fin (width k)) :
    Nat.size (ys.foldl (next (terms tm eQ)) (initial tm eQ) i) ≤
      storageBound q x.length w.length := by
  rcases pair_prefix_cases x w ys zs h with ⟨u, hu, rfl⟩ | ⟨v, hv, rfl⟩
  · rw [foldl_input]
    exact encode_load_size tm eQ x w u hu i
  · change Nat.size ((pair x v).foldl (next (terms tm eQ)) (initial tm eQ) i) ≤ _
    rw [foldl_pair]
    exact encode_prefix_run_size tm eQ x w v hv i

theorem bit_listSize (x : List Bool) : listSize (x.map Bool.toNat) ≤ 2 * x.length := by
  induction x with
  | nil => simp [listSize]
  | cons b bs ih =>
      have hb : Nat.size b.toNat ≤ 1 := by cases b <;> decide
      simp only [List.map_cons, listSize, List.map_cons, List.sum_cons,
        List.length_cons] at ih ⊢
      omega

theorem pair_listSize (x w : List Bool) :
    listSize (pair x w) ≤ storageBound q x.length w.length := by
  have hx := bit_listSize x
  have hw := bit_listSize w
  simp only [pair, listSize_append]
  have hsep : listSize [2] = 3 := by decide
  rw [hsep]
  dsimp [storageBound]
  omega

/-- Charged execution cost of the actual complete bounded-path checker. -/
theorem program_cost (x w : List Bool) :
    (program tm eQ).cost (pair x w) ≤
      programConstant (initial tm eQ) (terms tm eQ) (verdict tm eQ) *
        (storageBound q x.length w.length + 1) ^ 2 := by
  apply PCP.Lang.ArithmeticStream.program_cost
  · exact pair_listSize x w
  · exact prefix_fold_size tm eQ x w

end PCP.ReferenceNTM.PairedStream

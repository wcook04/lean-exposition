import PCP.Complexity.ReferenceNTMBounds
import Mathlib.Data.List.OfFn

/-!
# Choice-list witnesses for the reference NP machines

The verifier consumes exactly the choice bits supplied by its witness. A
polynomial bound appears only in the witness-length condition; it is not a
clock that the verifier must compute or trust.
-/

namespace PCP.ReferenceNTM.Cfg

open Complexity

variable {k : ℕ}

theorem acceptsInTime_iff_exists_length (tm : NTM k) (x : List Bool) (T : ℕ) :
    tm.AcceptsInTime x T ↔ ∃ w : List Bool, w.length = T ∧ accepts tm x w = true := by
  constructor
  · rintro ⟨choices, hh, ho⟩
    refine ⟨List.ofFn choices, by simp, (accepts_iff tm x _).mpr ?_⟩
    generalize hw : List.ofFn choices = w
    have hl : w.length = T := by rw [← hw, List.length_ofFn]
    subst T
    have hf : (fun i : Fin w.length => w[i.val]'i.isLt) = choices := by
      funext i
      have hi := congrArg (fun xs : List Bool => xs[i.val]?) hw
      simpa [List.getElem?_eq_getElem i.isLt] using hi.symm
    simpa only [hf] using And.intro hh ho
  · rintro ⟨w, rfl, hw⟩
    exact ⟨fun i => w[i.val]'i.isLt, (accepts_iff tm x w).mp hw⟩

/-- Short accepting witnesses can be padded because a halted trace remains frozen. -/
theorem acceptsInTime_iff_exists_le (tm : NTM k) (x : List Bool) (T : ℕ) :
    tm.AcceptsInTime x T ↔ ∃ w : List Bool, w.length ≤ T ∧ accepts tm x w = true := by
  constructor
  · intro h
    obtain ⟨w, hw, ha⟩ := (acceptsInTime_iff_exists_length tm x T).mp h
    exact ⟨w, hw.le, ha⟩
  · rintro ⟨w, hw, ha⟩
    exact ((acceptsInTime_iff_exists_length tm x w.length).mpr ⟨w, rfl, ha⟩).mono hw

/-- This bridge uses the reference's actual timed language semantics. -/
theorem decides_iff_witness (tm : NTM k) (L : Complexity.Language) (T : ℕ → ℕ)
    (h : tm.DecidesInTime L T) (x : List Bool) :
    x ∈ L ↔ ∃ w : List Bool, w.length ≤ T x.length ∧ accepts tm x w = true :=
  (h.2 x).trans (acceptsInTime_iff_exists_le tm x (T x.length))

end PCP.ReferenceNTM.Cfg

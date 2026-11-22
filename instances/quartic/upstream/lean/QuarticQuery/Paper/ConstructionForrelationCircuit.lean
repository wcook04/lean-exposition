module

public import QuarticQuery.Paper.ConstructionForrelationDefinitions

/-!
# Section 2.1: exact circuit output bits and size

Compiled as part of the `QuarticQuery` library target.
The supplied circuit represents arithmetic modulo a power of two and proves
that the final sign tests have the required integer meaning. Its endpoint is
the same exact circuit assertion as Lemma 2.1(iii). An assertion about every
intermediate mathematical integer requires separate range evidence.
-/

public section

namespace QuarticQuery.Paper

open QuarticQuery.Forrelation

/-- Ledger: claim-integer-tests. Verbatim value-output rule for the actual
supplied gate list, including inputs outside the promise. -/
theorem construction_forr_value_output (l t : ℕ)
    (x : BitInput (ForrelationCoord (l + 1) t)) :
    (run x (forrProg l t)).getD (coreSize l t) false =
      decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x ≥
        forrelationDenominator (l + 1) t) := by
  obtain ⟨q, a, b, c, e, hq, ra, rb, rc⟩ := forrCore_spec l t
  obtain ⟨w1, p1, e1, x1, r1⟩ := gate_spec ra (rep_none q) (fun a _ => !a)
  obtain ⟨w2, p2, e2, x2, r2⟩ := gate_spec (rb.mono x1) (rc.mono x1)
    (fun a b => !a && !b)
  obtain ⟨w3, p3, e3, x3, r3⟩ := gate_spec (r1.mono x2) r2 or
  have hp : forrProg l t = p3 := by
    simp only [forrProg, finish, e, e1, e2, e3]
  have hw1 : w1 = some (.inr (coreSize l t)) := by
    rw [← hq]
    exact (Prod.mk.inj e1).1.symm
  have hv : (run x (forrProg l t)).getD (coreSize l t) false =
      !decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0) := by
    rw [hp]
    have h := ((r1.mono x2).mono x3).2 x
    rw [hw1] at h
    exact h
  rw [hv]
  by_cases hy : (2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x ≥
      forrelationDenominator (l + 1) t
  · have hn : ¬ ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0) := by omega
    simp only [hn, hy, decide_true, decide_false, Bool.not_false]
  · have hn : (2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x -
        forrelationDenominator (l + 1) t < 0 := by omega
    simp only [hn, hy, decide_true, decide_false, Bool.not_true]

/-- Ledger: claim-integer-tests. Verbatim rules `b = first comparison` and
`d = disjunction`, for every consistent transcript of the constructed circuit.
This also fixes the value output on undefined inputs. -/
theorem construction_forr_output_bits (l t : ℕ)
    (x : BitInput (ForrelationCoord (l + 1) t))
    (tr : Fin (forrCircuit l t).size → Bool)
    (htr : GateConsistent (forrCircuit l t) x tr) :
    tr (forrCircuit l t).valueOut =
      decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x ≥
        forrelationDenominator (l + 1) t) ∧
    tr (forrCircuit l t).domainOut =
      decide ((2 : ℤ) ^ (5 * (l + 1)) * forrelationNumerator (l + 1) t x ≥
          forrelationDenominator (l + 1) t ∨
        (2 : ℤ) ^ (5 * (l + 1) + 1) * |forrelationNumerator (l + 1) t x| ≤
          forrelationDenominator (l + 1) t) := by
  constructor
  · have h := consistent_unique (forrProg l t)
      ⟨coreSize l t + 2, by rw [forrProg_length]; omega⟩
      ⟨coreSize l t, by rw [forrProg_length]; omega⟩ x tr htr
      (forrCircuit l t).valueOut
    change tr (forrCircuit l t).valueOut =
      (run x (forrProg l t)).getD (coreSize l t) false at h
    exact h.trans (construction_forr_value_output l t x)
  · have hd := ((forrCircuit_realises l t).correct x tr htr).1
    have hp := (construction_integer_tests (l + 1) t x).2.2.1
    have hi := hd.trans hp
    cases h : tr (forrCircuit l t).domainOut <;> simp_all

/-- Ledger: claim-circuit-size. Verbatim linear-in-log width estimate for
the existing modular circuit, with an explicit coefficient depending on `k`. -/
theorem construction_circuit_width (l t : ℕ) (ht : 1 ≤ t) :
    widthTop l t + 1 ≤ (3 * l + 5) * (2 * t) := by
  have hlt : l ≤ l * t := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left l ht
  simp only [widthTop]
  nlinarith

/-- Ledger: claim-circuit-size. Exact size and arithmetic contracts of the
supplied circuit. The arithmetic representation is modular, so this statement
does not assert that every intermediate register equals an unbounded integer. -/
theorem construction_circuit_costs (l t : ℕ) (ht : 1 ≤ t) :
    widthTop l t + 1 ≤ (3 * l + 5) * (2 * t) ∧
    (∀ w : ℕ, whtCost w (2 * t) ≤ (2 * t) * mValue t * (6 * w + 1)) ∧
    (∀ n w : ℕ, layerCost n w l ≤
      1 + (l + 1) * (whtCost w n + 2 ^ n * (6 * w))) ∧
    (∀ x : BitInput (ForrelationCoord (l + 1) t),
      |forrelationNumerator (l + 1) t x| ≤ forrelationDenominator (l + 1) t) ∧
    CircuitRealises (forrCircuit l t) (P (l + 1) t) ∧
    (forrCircuit l t).size ≤
      forrConstant (l + 1) * mValue t * (2 * t) ^ 2 := by
  exact ⟨construction_circuit_width l t ht,
    fun w => whtCost_le w (2 * t), fun n w => layerCost_le n w l,
    fun x => abs_numerator_le l t x, forrCircuit_realises l t,
    forrCircuit_size_le l t ht⟩

/-- Ledger: lem-2.1.iii. Verbatim circuit conclusion, with an explicit positive
constant uniform in `m`; the proof also covers `k = 1`. -/
theorem construction_lemma_2_1_iii (k : ℕ) (hk : 1 ≤ k) :
    ∃ S : ℕ, 0 < S ∧ ∀ t : ℕ, 1 ≤ t → ∃ C : Circuit (ForrelationCoord k t),
      CircuitRealises C (P k t) ∧
      (C.size : ℝ) ≤ (S : ℝ) * (mValue t : ℝ) *
        (Real.logb 2 (mValue t : ℝ)) ^ 2 := by
  refine ⟨forrConstant k, ?_, fun t ht => exists_circuit k t hk ht⟩
  simp only [forrConstant]
  positivity

end QuarticQuery.Paper

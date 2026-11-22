import PCP.Verifier.Definition
import PCP.Complexity.CostModel
import PCP.Complexity.NP
import PCP.Complexity.Machine
import PCP.Complexity.ThreeColorRuntime
import PCP.Algebraic.ThreeColorFinalAssembly

/-!
# The PCP theorem via the algebraic construction in PCP-SOSA27

The forward theorem supplies a concrete polynomial-time bit verifier with
logarithmic randomness, constant queries, perfect completeness and soundness 1/2.
The inner low-degree test uses the generator constraint with `q > 2c`.
`ThreeColorRuntime.polyTimeAlg` certifies the same verifier's implementation.

The reverse direction is stated below for a cost model and specialized to the
concrete machine model in `PCP.ReverseConcrete`. The reference NP equivalence is
proved in `PCP.Complexity.ReferenceNPConverse`.
-/

namespace PCP

/-- `NP ⊆ PCP(O(log n), O(1))`, with one polynomial-time verifier for each language.
All constants and the proof-length polynomial are independent of the input. -/
theorem np_subset_pcp (L : Language) (hL : InNP Machine.PolyTimeRel L) :
    ∃ (V : Verifier) (alg : VerifierAlg) (a b q : ℕ) (p : Polynomial ℕ),
      Machine.PolyTimeAlg alg ∧
      V.ImplementedBy alg ∧
      V.queries = q ∧
      V.CanonicalRandomness a b ∧
      (∀ x : List Bool, V.ReadsBelow x (p.eval x.length)) ∧
      (∀ x : List Bool, L x → V.CompleteAt x) ∧
      (∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) := by
  exact Algebraic.ThreeColorFinalAssembly.of_runtime Lang.ThreeColorRuntime.polyTimeAlg L hL

/-- The reverse inclusion follows by guessing the bounded proof prefix and
checking all logarithmically many random bits. The concrete machine model
satisfies the cost-model closure properties in `PCP.Complexity.StandardModel`. -/
theorem pcp_subset_np (M : CostModel) (L : Language) (V : Verifier) (a b : ℕ) (p : Polynomial ℕ)
    (heff : M.Efficient V)
    (hrand : V.CanonicalRandomness a b)
    (hlen : ∀ x : List Bool, V.ReadsBelow x (p.eval x.length))
    (hcomplete : ∀ x : List Bool, L x → V.CompleteAt x)
    (hsound : ∀ x : List Bool, ¬ L x → V.SoundAt x (1 / 2)) :
    InNP M.PolyTimeRel L := by
  classical
  obtain ⟨alg, halg, himpl⟩ := heff
  refine ⟨{
    witnessBound := p
    check := finiteWitnessCheck V
    check_polyTime := M.polyTimeRel_finiteWitnessCheck V alg a b p halg himpl hrand hlen
    spec := ?_ }⟩
  intro x
  constructor
  · -- Completeness: truncate an accepted proof to its first `p n` bits.
    intro hx
    obtain ⟨π, hπ⟩ := hcomplete x hx
    refine ⟨(List.range (p.eval x.length)).map π, by simp, ?_⟩
    rw [finiteWitnessCheck_eq_true_iff]
    have hcongr : V.accProb x (oracleOfWitness ((List.range (p.eval x.length)).map π))
        = V.accProb x π :=
      V.accProb_congr_of_readsBelow x (hlen x)
        (fun j hj => oracleOfWitness_prefix π _ hj)
    exact (V.accProb_eq_one_iff x _).mp (hcongr.trans hπ)
  · -- Soundness: an accepted witness forces acceptance probability 1, which beats 1/2.
    rintro ⟨w, -, hw⟩
    by_contra hx
    have hone : V.accProb x (oracleOfWitness w) = 1 :=
      (V.accProb_eq_one_iff x _).mpr ((finiteWitnessCheck_eq_true_iff V x w).mp hw)
    have := hsound x hx (oracleOfWitness w)
    rw [hone] at this
    norm_num at this

end PCP

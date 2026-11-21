import Breakdown.Frac.StTorusStepApprox
import Breakdown.Torus.Approximants
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracInternal.TorusApproximants

theorem dilExponent_pos {α : ℝ} (hα : 1 < α) : 0 < dilExponent α := by
  unfold dilExponent
  have h4 : 0 < 4 * α := by linarith
  have h : 3 / (4 * α) < 1 := by
    rw [div_lt_one h4]
    linarith
  linarith

theorem profile_rot {α : ℝ} (hα : 1 < α) (hPP : ScaledProfilePieceStatement)
    (F : ScaledMildFramework Freq.X (dilExponent α))
    (R : Space ≃ₗᵢ[ℝ] Space) {w : ℝ → Freq.X} {P : ℝ} (hC : F.Commutes (Freq.rotX R))
    (hO : F.IsOrbit (Freq.rotX R) w P) {k : ℕ} (hk : 0 < k) (i j : ℕ)
    (t : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    F.profilePiece w P k (k * j + i) t = (⇑(Freq.rotX R))^[j] (F.profilePiece w P k i t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := (hPP Freq.X (dilExponent α) (dilExponent_pos hα) F (Freq.rotX R) hC w P hO k hk
      (k * j + i)).2.2.2.1 t
    rw [show k * (j + 1) + i = k * j + i + k by ring, h, ih, Function.iterate_succ_apply']

end FracInternal.TorusApproximants

theorem fracApproximantExists (α : ℝ) (hα : 1 < α) (hPP : ScaledProfilePieceStatement) :
    FracApproximantExists α := by
  have hTD : Freq.TestDense := Freq.testDense_holds.2
  have hTS : Freq.TestSpanSpec := Freq.testSpan_holds
  have hER : Freq.EmbedRot :=
    Freq.embedRot Freq.fieldOpRealized Freq.rotation_holds Freq.embedMem_holds Freq.gradCompatible
  intro F R a U _P P hC hO _ k hk ε hε
  let f : C(Icc (0 : ℝ) (MildFramework.stepLength P k), Fin k → Freq.X) :=
    ⟨fun t i => F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P k i t,
      continuous_pi fun i => (F.profilePiece (fun s => Freq.embedX (rotatingSlice a U s)) P k i).continuous⟩
  have hS : Dense (Set.pi univ fun _ : Fin k => (Freq.testSpan : Set Freq.X)) :=
    dense_pi _ fun _ _ => hTD
  obtain ⟨m, ρ, x, hxS, hρ, hfx⟩ := Internal.Approximants.exists_finite_approx f hS hε
  have hφ : ∀ l i, ∃ φ, IsTestField φ ∧ Freq.embedX φ = x l i :=
    fun l i => hTS _ (hxS l i (mem_univ _))
  choose φ hφT hφE using hφ
  have hr : ∀ l i, ∃ r, tsupport (φ l i) ⊆ Metric.closedBall 0 r :=
    fun l i => (Metric.isBounded_iff_subset_closedBall 0).1 (hφT l i).2.1.isCompact.isBounded
  choose r hr using hr
  have hle : ∀ (c : Fin m → Fin k → ℝ) l i, |c l i| ≤ ∑ l, ∑ i, |c l i| := by
    intro c l i
    calc |c l i| ≤ ∑ i, |c l i| :=
          Finset.single_le_sum (f := fun i => |c l i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ l, ∑ i, |c l i| :=
          Finset.single_le_sum (f := fun l => ∑ i, |c l i|)
            (fun l _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ l)
  have hb : ∀ l i, tsupport (φ l i) ⊆ Metric.closedBall 0 (1 + ∑ l, ∑ i, |r l i|) := by
    intro l i
    refine (hr l i).trans (Metric.closedBall_subset_closedBall ?_)
    linarith [le_abs_self (r l i), hle r l i]
  have hbpos : 0 < 1 + ∑ l, ∑ i, |r l i| := by positivity
  let idx : ℕ → Fin k := fun n => ⟨n % k, Nat.mod_lt n hk⟩
  have key := fun n l =>
    Internal.Approximants.rot_iterate R hER (hφT l (idx n)) (hb l (idx n)) (n / k)
  let A : Approximant (MildFramework.stepLength P k) (1 + ∑ l, ∑ i, |r l i|) :=
    { terms := m
      field := fun n l => (pushForward R)^[n / k] (φ l (idx n))
      isTest := fun n l => (key n l).1
      support := fun n l => (key n l).2.1
      weight := fun _ l => ρ l
      bound := by
        refine ⟨1 + ∑ l, ∑ i, |‖x l i‖|, fun n l => ⟨?_, ?_⟩⟩
        · rw [(key n l).2.2, Internal.Approximants.iterate_norm, hφE]
          linarith [le_abs_self ‖x l (idx n)‖, hle (fun l i => ‖x l i‖) l (idx n)]
        · have h0 : (0 : ℝ) ≤ ∑ l, ∑ i, |‖x l i‖| :=
            Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
          refine (ContinuousMap.norm_le _ (by linarith)).2 fun t => ?_
          rw [Real.norm_of_nonneg (hρ l t).1]
          linarith [(hρ l t).2] }
  refine ⟨1 + ∑ l, ∑ i, |r l i|, hbpos, A, fun n => ?_⟩
  refine (ContinuousMap.norm_le _ hε.le).2 fun t => ?_
  have hn : k * (n / k) + n % k = n := Nat.div_add_mod n k
  have hp := FracInternal.TorusApproximants.profile_rot hα hPP F R hC hO hk (n % k) (n / k) t
  rw [hn] at hp
  have e1 : A.r3Piece n t =
      ∑ l, ρ l t • Freq.embedX ((pushForward R)^[n / k] (φ l (idx n))) := rfl
  have e2 : ∑ l, ρ l t • Freq.embedX ((pushForward R)^[n / k] (φ l (idx n))) =
      ∑ l, ρ l t • (⇑(Freq.rotX R))^[n / k] (x l (idx n)) := by
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(key n l).2.2, hφE]
  rw [ContinuousMap.sub_apply, e1, e2, hp, Internal.Approximants.iterate_combo,
    Internal.Approximants.iterate_norm]
  refine le_trans (le_of_eq ?_) ((norm_le_pi_norm (∑ l, ρ l t • x l - f t) (idx n)).trans (hfx t))
  congr 1
  simp [Finset.sum_apply, f, idx]

end Breakdown.Periodic

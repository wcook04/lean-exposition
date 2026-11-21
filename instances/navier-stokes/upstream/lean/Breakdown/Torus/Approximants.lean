import Breakdown.Torus.StatementsApproxSteps
import Breakdown.FreqTr.VelocityRotate

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace Internal.Approximants

theorem exists_finite_approx {K E : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : C(K, E)) {S : Set E} (hS : Dense S)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (ρ : Fin m → C(K, ℝ)) (x : Fin m → E), (∀ l, x l ∈ S) ∧
      (∀ l t, 0 ≤ ρ l t ∧ ρ l t ≤ 1) ∧ ∀ t, ‖∑ l, ρ l t • x l - f t‖ ≤ ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  let U : K → Set K := fun s => f ⁻¹' Metric.ball (f s) (ε / 2)
  have hUo : ∀ s, IsOpen (U s) := fun s => Metric.isOpen_ball.preimage f.continuous
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hUo
    (fun t _ => mem_iUnion.2 ⟨t, by simp [U, Metric.mem_ball, hε2]⟩)
  let e := T.equivFin
  let pts : Fin T.card → K := fun l => (e.symm l).1
  have hcov : (univ : Set K) ⊆ ⋃ l, U (pts l) := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := mem_iUnion₂.1 (hT ht)
    exact mem_iUnion.2 ⟨e ⟨s, hs⟩, by simpa [pts] using hts⟩
  obtain ⟨ρ, hρ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ (fun l => U (pts l))
    (fun l => hUo _) hcov
  have hx : ∀ l, ∃ y, y ∈ S ∧ dist (f (pts l)) y < ε / 2 := by
    intro l
    obtain ⟨y, hy1, hy2⟩ := Metric.dense_iff.1 hS (f (pts l)) (ε / 2) hε2
    exact ⟨y, hy2, by rw [dist_comm]; exact hy1⟩
  choose x hxS hxd using hx
  refine ⟨T.card, fun l => ρ l, x, hxS, fun l t => ⟨ρ.nonneg l t, ρ.le_one l t⟩, fun t => ?_⟩
  have h1 : ∑ l, ρ l t = 1 := by
    rw [← finsum_eq_sum_of_fintype]
    exact ρ.sum_eq_one (mem_univ t)
  have h2 : ∑ l, ρ l t • x l - f t = ∑ l, ρ l t • (x l - f t) := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, h1, one_smul]
  rw [h2]
  calc ‖∑ l, ρ l t • (x l - f t)‖ ≤ ∑ l, ‖ρ l t • (x l - f t)‖ := norm_sum_le _ _
    _ ≤ ∑ l, ρ l t * ε := by
        refine Finset.sum_le_sum fun l _ => ?_
        rw [norm_smul, Real.norm_of_nonneg (ρ.nonneg l t)]
        by_cases h0 : ρ l t = 0
        · simp [h0]
        · refine mul_le_mul_of_nonneg_left ?_ (ρ.nonneg l t)
          have hts : t ∈ U (pts l) := hρ l (subset_tsupport _ (Function.mem_support.2 h0))
          have h3 : dist (f t) (f (pts l)) < ε / 2 := hts
          have h4 := hxd l
          rw [← dist_eq_norm]
          linarith [dist_triangle (x l) (f (pts l)) (f t), dist_comm (x l) (f (pts l)),
            dist_comm (f t) (f (pts l))]
    _ = ε := by rw [← Finset.sum_mul, h1, one_mul]

theorem iterate_norm {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (e : E ≃ₗᵢ[ℝ] E)
    (j : ℕ) (y : E) : ‖(⇑e)^[j] y‖ = ‖y‖ := by
  induction j with
  | zero => rfl
  | succ j ih => rw [Function.iterate_succ_apply', LinearIsometryEquiv.norm_map, ih]

theorem iterate_combo {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] (e : E ≃ₗᵢ[ℝ] E)
    (j : ℕ) {m : ℕ} (c : Fin m → ℝ) (y : Fin m → E) (z : E) :
    ∑ l, c l • (⇑e)^[j] (y l) - (⇑e)^[j] z = (⇑e)^[j] (∑ l, c l • y l - z) := by
  induction j with
  | zero => rfl
  | succ j ih => simp only [Function.iterate_succ_apply', ← ih, map_sub, map_sum, map_smul]

theorem rot_iterate (R : Space ≃ₗᵢ[ℝ] Space) (hER : Freq.EmbedRot) {b : ℝ} {φ : Space → Space}
    (hφ : IsTestField φ) (hb : tsupport φ ⊆ Metric.closedBall 0 b) (j : ℕ) :
    IsTestField ((pushForward R)^[j] φ) ∧ tsupport ((pushForward R)^[j] φ) ⊆ Metric.closedBall 0 b ∧
      Freq.embedX ((pushForward R)^[j] φ) = (⇑(Freq.rotX R))^[j] (Freq.embedX φ) := by
  induction j with
  | zero => simp [hφ, hb]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨Freq.Internal.VelocityRotate.test_pushForward R h1, ?_, ?_⟩
    · refine closure_minimal (fun y hy => ?_) Metric.isClosed_closedBall
      have hy' : (pushForward R)^[j] φ (R.symm y) ≠ 0 := by
        intro h
        apply hy
        simp [pushForward, h]
      have := h2 (subset_tsupport _ (Function.mem_support.2 hy'))
      simpa using this
    · rw [← hER R _ (Freq.Internal.VelocityRotate.decay_of_test h1), h3, Function.iterate_succ_apply']

theorem profile_rot (hPP : ProfilePieceStatement) (F : MildFramework Freq.X)
    (R : Space ≃ₗᵢ[ℝ] Space) {w : ℝ → Freq.X} {P : ℝ} (hC : F.Commutes (Freq.rotX R))
    (hO : F.IsOrbit (Freq.rotX R) w P) {k : ℕ} (hk : 0 < k) (i j : ℕ)
    (t : Icc (0 : ℝ) (MildFramework.stepLength P k)) :
    F.profilePiece w P k (k * j + i) t = (⇑(Freq.rotX R))^[j] (F.profilePiece w P k i t) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h := (hPP Freq.X F (Freq.rotX R) hC w P hO k hk (k * j + i)).2.2.2.1 t
    rw [show k * (j + 1) + i = k * j + i + k by ring, h, ih, Function.iterate_succ_apply']

end Internal.Approximants

theorem approximantExists (hTD : Freq.TestDense) (hTS : Freq.TestSpanSpec) (hER : Freq.EmbedRot)
    (_hEL : Freq.EmbedLinear) (_hRot : Freq.RotationAlgebra) (hPP : ProfilePieceStatement) :
    ApproximantExists := by
  intro F R W q C P hC hO _ k hk ε hε
  let f : C(Icc (0 : ℝ) (MildFramework.stepLength P k), Fin k → Freq.X) :=
    ⟨fun t i => F.profilePiece (fun s => Freq.embedX (W s)) P k i t,
      continuous_pi fun i => (F.profilePiece (fun s => Freq.embedX (W s)) P k i).continuous⟩
  have hS : Dense (Set.pi univ fun _ : Fin k => (Freq.testSpan : Set Freq.X)) :=
    dense_pi _ fun _ _ => hTD
  obtain ⟨m, ρ, x, hxS, hρ, hfx⟩ := Internal.Approximants.exists_finite_approx f hS hε
  have hφ : ∀ l i, ∃ φ, IsTestField φ ∧ Freq.embedX φ = x l i :=
    fun l i => hTS _ (hxS l i (mem_univ _))
  choose φ hφT hφE using hφ
  have hr : ∀ l i, ∃ r, tsupport (φ l i) ⊆ Metric.closedBall 0 r :=
    fun l i => (Metric.isBounded_iff_subset_closedBall 0).1 (hφT l i).2.1.isCompact.isBounded
  choose r hr using hr
  have hle : ∀ (a : Fin m → Fin k → ℝ) l i, |a l i| ≤ ∑ l, ∑ i, |a l i| := by
    intro a l i
    calc |a l i| ≤ ∑ i, |a l i| :=
          Finset.single_le_sum (f := fun i => |a l i|) (fun i _ => abs_nonneg _) (Finset.mem_univ i)
      _ ≤ ∑ l, ∑ i, |a l i| :=
          Finset.single_le_sum (f := fun l => ∑ i, |a l i|)
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
  have hp := Internal.Approximants.profile_rot hPP F R hC hO hk (n % k) (n / k) t
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

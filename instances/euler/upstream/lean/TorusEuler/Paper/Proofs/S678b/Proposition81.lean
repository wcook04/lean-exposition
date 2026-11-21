import TorusEuler.Paper.Proofs.S678b.Library.EulerLimit
import TorusEuler.Paper.Proofs.S678b.Library.Limit

/-! # Proof of Proposition 8.1 (cites Lemma 1.3 and display (5.59); setting 7.1) -/

open Filter Set
open scoped Topology

namespace TorusEuler.Paper

open Lib.S678b

/-- Proof of **Proposition 8.1** (`cc:uf:terminal:agreement`), following
sections/09_limit.tex:21-46.

* "Since `t_j ↑ T_∞` and `q_j ↑ ∞`" (09_limit:22-23): `t_j → T_∞` and `T_∞ < S_j` are
  `h71.lifetime`; `q_j → ∞` is Lemma 1.3, used through `h1_3` (`lemma13_schedule h1_3 P`).
* "For `j > j_0` the oscillation `O_j` vanishes on `[0,T]`; (7.4) gives ... the limit in each of
  these norms is `w`" (09_limit:24-31): `h71.oscillation_vanishes`, `h71.increment` (as
  `increment_jet_bound`) and `h71.T1` feed the copied `exists_inductive_periodicEulerSolution`.
* "Integrating (7.5) ... By (T2) the last integral has supremum norm at most
  `Tλ_{j+1}^{-3}`" (09_limit:33-39): (7.5) is the projected residual equation carried by the
  stages (`c.stages.projected_residual`); the residual bound is `h71.T2`.
* "Convergence in `C([0,T];C^{1,1/2})`, the product estimate (5.59) and boundedness of `ℙ` on
  `C^{0,1/2}` give uniform convergence of the projected nonlinear term. Hence
  `∂_t w = -ℙ div(w ⊗ w)`. The right-hand side is continuous in every spatial Hölder norm, so
  differentiating the equation gives joint smoothness" (09_limit:39-44): this is the bounded
  bilinear momentum map `Lib.S678b.periodicProjectedMomentumJets hText_eq_5_59`, whose bound
  is the product estimate (5.59) taken from `hText_eq_5_59` (the copied chain of
  `Library/EulerLimit.lean`).
* "Uniqueness identifies `w` with `u` wherever both exist. Since `w` exists for every
  `T < T_∞`, maximality gives `T_* ≥ T_∞`" (09_limit:44-46):
  `IsEulerSolution.velocity_eq_on_common_interval` (periodic uniqueness) and the maximality
  of the given solution.
The convergence of the data `U_j(0)` in every `C^{m,1/2}` is the case `t = 0` of the
convergence on `[0,T]`. -/
theorem Proof.proposition_8_1_of (h1_3 : Statement.lemma_1_3)
    (hText_eq_5_59 : Statement.Text.eq_5_59) : Statement.proposition_8_1 := by
  intro P c C T h71
  obtain ⟨hT, hActivation, hSlab⟩ := h71.lifetime
  have hInit := two_le_frequency_zero P
  have hOrder := (lemma13_schedule h1_3 P).1
  obtain ⟨u, p, hEuler, hOdd, -, -, hJets⟩ :=
    Lib.S678b.exists_inductive_periodicEulerSolution hText_eq_5_59 (U := c.stages.velocity)
      (O := c.stages.oscillation) (R := c.stages.residual) (freq := P.frequency)
      (q := P.order) (slab := c.stages.slab) (activation := c.stages.activation)
      hT (fun j => (hSlab j).le) hInit (c.stages.frequency_square_gap hInit) hOrder hActivation
      (fun n => (h71.T1 n).1) (fun n t ht => ((h71.T1 n).2 t ht).1)
      (fun n t ht => ((h71.T1 n).2 t ht).2.1) (fun n t ht => ((h71.T1 n).2 t ht).2.2.1)
      (fun n hn t ht => h71.oscillation_vanishes n hn t ht)
      (fun n t ht x => (h71.increment (n + 1) (Nat.succ_pos n) t ht).1 x)
      (increment_jet_bound h71) c.stages.projected_residual
      (fun n t ht x => (h71.T2 n).2.2 t ht x)
  have hAt0 : (0 : ℝ) ∈ Ico 0 T := ⟨le_rfl, hT⟩
  have hPrefix (S : ℝ) (hST : S < T) (m : ℕ) : TendstoUniformlyOn
      (fun j t => spatialHolderHalfNorm m (c.stages.velocity j t - u t))
      (fun _ => 0) atTop (Icc 0 S) := by
    obtain ⟨S', hSS', hS'T⟩ := exists_between (max_lt hST hT)
    exact ((hJets S' ((le_max_right _ _).trans_lt hSS') hS'T m).2).mono
      (Icc_subset_Icc_right ((le_max_left _ _).trans hSS'.le))
  refine ⟨u, p, fun m => (hPrefix 0 hT m).tendsto_at (x := 0) ⟨le_rfl, le_rfl⟩, hOdd 0 hAt0,
    hEuler.incompressible 0 hAt0, hEuler.contDiff_velocity_slice hAt0, hEuler, ?_, hPrefix, hOdd⟩
  intro T₁ v q hMax h0
  have hEq := hMax.1.velocity_eq_on_common_interval hEuler h0
  have hLe : T ≤ T₁ := by
    by_contra! hSmall
    apply hMax.2 T hSmall
    refine ⟨u, p, hEuler, fun t ht => ?_⟩
    exact (hEq t (by simpa only [min_eq_left hSmall.le] using ht)).symm
  exact ⟨hLe, fun _ ht => hEq _ (by simpa only [min_eq_right hLe] using ht)⟩

end TorusEuler.Paper

import PCP.Complexity.ReferenceNTMBounds

/-! # Prefixes of the binary-input, separator, binary-witness stream -/

namespace PCP.ReferenceNTM

/-- Every finite stream prefix is either still loading input or already executing choices. -/
theorem pair_prefix_cases (x w : List Bool) (ys zs : List ℕ)
    (h : x.map Bool.toNat ++ [2] ++ w.map Bool.toNat = ys ++ zs) :
    (∃ u : List Bool, u <+: x ∧ ys = u.map Bool.toNat) ∨
      ∃ v : List Bool, v <+: w ∧ ys = x.map Bool.toNat ++ [2] ++ v.map Bool.toNat := by
  have hs : x.map Bool.toNat ++ (2 :: w.map Bool.toNat) = ys ++ zs := by
    simpa only [List.append_assoc, List.singleton_append] using h
  rcases List.append_eq_append_iff.mp hs with ⟨as, hy, ht⟩ | ⟨bs, hx, _⟩
  · have ha : as <+: 2 :: w.map Bool.toNat := ⟨zs, ht.symm⟩
    rcases List.prefix_cons_iff.mp ha with rfl | ⟨vs, rfl, hv⟩
    · exact Or.inl ⟨x, List.prefix_rfl, by simpa using hy⟩
    · obtain ⟨v, hpre, hv⟩ := List.prefix_map_iff.mp hv
      exact Or.inr ⟨v, hpre, by simp [hy, hv, List.append_assoc]⟩
  · obtain ⟨u, hu, hy⟩ := List.prefix_map_iff.mp (show ys <+: x.map Bool.toNat from ⟨bs, hx.symm⟩)
    exact Or.inl ⟨u, hu, hy⟩

end PCP.ReferenceNTM

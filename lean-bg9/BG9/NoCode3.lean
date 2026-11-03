import BG9.Codes

/-!
# Sanity check: there is no cyclic 3-bit Beckett-Gray code

A code would have length `2^3 = 8`, so it suffices to check all `3^8 = 6561` sequences of length 8.
`allLists k` lists every sequence in `Fin 3` of length `k` (`mem_allLists`), and the kernel checks
each one with `decide +kernel`.
-/

namespace BG

/-- All sequences of length `k` over `Fin 3`. -/
def allLists : Nat → List (List (Fin 3))
  | 0 => [[]]
  | k + 1 => (allLists k).flatMap fun l => [(0 : Fin 3) :: l, 1 :: l, 2 :: l]

theorem mem_allLists : ∀ t : List (Fin 3), t ∈ allLists t.length
  | [] => by simp [allLists]
  | i :: l => by
    simp only [allLists, List.length_cons, List.mem_flatMap]
    refine ⟨l, mem_allLists l, ?_⟩
    have h3 : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
    rcases h3 i with rfl | rfl | rfl <;> simp

/-- No sequence of length 8 over `Fin 3` is a Beckett-Gray code (exhaustive, kernel-checked). -/
theorem none_of_length_8 : ∀ t ∈ allLists 8, ¬ IsBeckettGray 3 t := by
  decide +kernel

/-- There is no cyclic 3-bit Beckett-Gray code. -/
theorem no_code3 (t : List (Fin 3)) : ¬ IsBeckettGray 3 t := by
  intro h
  have hm := mem_allLists t
  rw [h.1] at hm
  exact none_of_length_8 t hm h

end BG

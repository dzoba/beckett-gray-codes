import BG9.NoCode3

/-!
# Main results

* `code9_isBeckettGray`: the sequence of `FOUND-9.txt` is a cyclic 9-bit Beckett-Gray code.
  Proved by `decide +kernel`: the kernel itself reduces the decision procedure to `true`. No compiled
  code is trusted.
* `code9_isBeckettGray_native`: the same statement by `native_decide`, as a cross-check only. It
  trusts the compiler (axiom `Lean.ofReduceBool`) and nothing else depends on it.
* `code9_visits_all`: every one of the 512 words is among `w₀, …, w₅₁₁`.
* Sanity checks of the definition: `code5_isBeckettGray` (a published 5-bit code passes),
  `code9_swapped_not` (corrupted 9-bit code fails, with the failing conditions named), and
  `no_code3` in `BG9/NoCode3.lean` (no 3-bit code exists, as is known).
-/

namespace BG

/-- The cyclic 9-bit Beckett-Gray code of `FOUND-9.txt` satisfies `IsBeckettGray`. -/
theorem code9_isBeckettGray : IsBeckettGray 9 code9 := by
  decide +kernel

/-- Every word of `{0,1}^9` is visited among the first 512 words of the walk of `code9`. -/
theorem code9_visits_all : ∀ w, w < 2 ^ 9 → w ∈ (words code9).take (2 ^ 9) := by
  decide +kernel

/-- Cross-check of `code9_isBeckettGray` by compiled evaluation (trusts the compiler). -/
theorem code9_isBeckettGray_native : IsBeckettGray 9 code9 := by
  native_decide

/-- The published 5-bit code passes. -/
theorem code5_isBeckettGray : IsBeckettGray 5 code5 := by
  decide +kernel

/-- Swapping the first two steps of `code9` gives a sequence that is not a Beckett-Gray code. -/
theorem code9_swapped_not : ¬ IsBeckettGray 9 code9_swapped := by
  decide +kernel

/-- Why it fails: the swapped walk goes `0 → 2 → 3`, so it repeats a word (word 2 is also
visited later) ... -/
theorem code9_swapped_repeats : ¬ ((words code9_swapped).take (2 ^ 9)).Nodup := by
  decide +kernel

/-- ... and it breaks the FIFO rule (its queue starts `[1, 0, …]`, and a later step turns off bit 0
while bit 1 is at the head). -/
theorem code9_swapped_not_fifo :
    ¬ ∀ p ∈ (states code9_swapped).zip code9_swapped,
        p.1.word.testBit p.2 = true → p.1.queue.head? = some p.2.val := by
  decide +kernel

end BG

-- The literal `code9`, printed back as a digit string, for comparison with `FOUND-9.txt`.
#eval String.join (BG.code9.map fun i => toString i.val)

#print axioms BG.code9_isBeckettGray
#print axioms BG.code9_visits_all
#print axioms BG.code9_isBeckettGray_native
#print axioms BG.code5_isBeckettGray
#print axioms BG.code9_swapped_not
#print axioms BG.code9_swapped_repeats
#print axioms BG.code9_swapped_not_fifo
#print axioms BG.no_code3
#print axioms BG.queue_mem_iff

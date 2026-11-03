import BG9.Defs

/-!
# The queue is the set of 1-coordinates

A check that `IsBeckettGray` means what it says. In every state of the walk of any transition sequence,
the queue has no repeated entries and its entries are exactly the coordinates that are 1 in the
current word. So "the head of the queue" in condition 6 really is a 1-coordinate, and since entries
join at the tail when they turn on, it is the one that has been 1 longest.
-/

namespace BG

/-- The queue invariant: no repeats, and the entries are exactly the 1-coordinates of the word. -/
def QueueOK (s : State) : Prop :=
  s.queue.Nodup ∧ ∀ j, j ∈ s.queue ↔ s.word.testBit j = true

theorem queueOK_start : QueueOK start := by
  simp [QueueOK, start]

theorem testBit_flip (w i j : Nat) : (flip w i).testBit j = (w.testBit j ^^ decide (i = j)) := by
  simp [flip, Nat.testBit_xor, Nat.testBit_two_pow]

theorem queueOK_step {s : State} (h : QueueOK s) (i : Nat) : QueueOK (s.step i) := by
  obtain ⟨hnd, hmem⟩ := h
  unfold State.step
  by_cases hb : s.word.testBit i = true
  · simp only [hb, if_true]
    refine ⟨hnd.erase i, fun j => ?_⟩
    rw [hnd.mem_erase_iff, hmem j, testBit_flip]
    by_cases hij : i = j
    · subst hij; simp [hb]
    · simp [hij, Ne.symm hij]
  · have hb' : s.word.testBit i = false := by simpa using hb
    simp only [hb', Bool.false_eq_true, if_false]
    have hi : i ∉ s.queue := fun hq => hb ((hmem i).1 hq)
    refine ⟨?_, fun j => ?_⟩
    · exact List.nodup_append.2 ⟨hnd, by simp, by
        intro a ha b hb'; simp at hb'; subst hb'; intro hab; subst hab; exact hi ha⟩
    · rw [List.mem_append, List.mem_singleton, hmem j, testBit_flip]
      by_cases hij : i = j
      · subst hij; simp [hb]
      · simp [hij, Ne.symm hij]

theorem queueOK_scanl (l : List Nat) {s : State} (h : QueueOK s) :
    ∀ s' ∈ l.scanl (fun s i => s.step i) s, QueueOK s' := by
  induction l generalizing s with
  | nil => simpa using h
  | cons i l ih =>
    intro s' hs'
    simp only [List.scanl_cons, List.mem_cons] at hs'
    rcases hs' with rfl | hs'
    · exact h
    · exact ih (queueOK_step h i) s' hs'

/-- In every state of the walk, the queue lists each 1-coordinate of the word exactly once and
nothing else. -/
theorem queue_mem_iff {n : Nat} (t : List (Fin n)) :
    ∀ s ∈ states t, s.queue.Nodup ∧ ∀ j, j ∈ s.queue ↔ s.word.testBit j = true := by
  intro s hs
  have : states t = (t.map Fin.val).scanl (fun s i => s.step i) start := by
    simp [states, List.scanl_map]
  rw [this] at hs
  exact queueOK_scanl _ queueOK_start s hs

end BG

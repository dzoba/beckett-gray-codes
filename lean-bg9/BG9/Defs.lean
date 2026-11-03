/-!
# Beckett-Gray codes: the definition

A word of `{0,1}^n` is encoded as a natural number `w < 2^n`; coordinate `i` of `w` is
`w.testBit i`, the coefficient of `2^i` in binary. The all-zero word is `0`.

A code is given by its *transition sequence* `t = [t₀, t₁, …, t_{L-1}]`, with `t_k : Fin n` the
coordinate flipped at step `k`. Starting from word `w₀ = 0`, step `k` produces `w_{k+1}` from `w_k` by
flipping coordinate `t_k`.

Alongside the word we carry the *queue* of its 1-coordinates, oldest first. A step that turns a
coordinate on (0 → 1) appends it at the tail. A step that turns a coordinate off (1 → 0) removes it.
So the queue lists the coordinates that are currently 1, ordered by the time they were last turned on
(`queue_mem_iff` in `BG9/Queue.lean` proves the membership half). The Beckett (FIFO) rule says every
1 → 0 step removes the head of the queue: the coordinate that has been 1 longest.
-/

namespace BG

/-- Flip coordinate `i` of the word `w`. -/
def flip (w i : Nat) : Nat := w ^^^ 2 ^ i

/-- Hamming distance on `{0,1}^n`: the number of coordinates `j < n` where `a` and `b` differ. -/
def hamming (n a b : Nat) : Nat :=
  ((List.range n).filter (fun j => a.testBit j != b.testBit j)).length

/-- The state of the walk: the current word and its queue of 1-coordinates, oldest first. -/
structure State where
  word : Nat
  queue : List Nat
  deriving DecidableEq, Repr

/-- One step on coordinate `i`. If coordinate `i` is 1 it turns off and leaves the queue (wherever
it is: the FIFO rule, checked separately in `IsBeckettGray`, demands that it is the head). If it is 0
it turns on and joins the tail of the queue. -/
def State.step (s : State) (i : Nat) : State :=
  if s.word.testBit i then
    { word := flip s.word i, queue := s.queue.erase i }
  else
    { word := flip s.word i, queue := s.queue ++ [i] }

/-- The start of the walk: the all-zero word, with an empty queue. -/
def start : State := { word := 0, queue := [] }

/-- `states t = [s₀, s₁, …, s_L]` with `s₀ = start` and `s_{k+1} = s_k.step t_k`. -/
def states {n : Nat} (t : List (Fin n)) : List State :=
  t.scanl (fun s i => s.step i.val) start

/-- `words t = [w₀, w₁, …, w_L]`, the words visited by the walk (`w₀ = 0`). -/
def words {n : Nat} (t : List (Fin n)) : List Nat :=
  (states t).map State.word

/-- `IsBeckettGray n t`: the transition sequence `t` is a cyclic `n`-bit Beckett-Gray code.

With `w₀ = 0, w₁, …, w_L` the words of the walk (`L = t.length`) and `s_k` its states:

1. it has `2^n` steps, `L = 2^n`;
2. every word lies in `{0,1}^n`, that is `w_k < 2^n`;
3. `w₀, …, w_{2^n - 1}` are pairwise distinct, so by (1) and (2) every word of `{0,1}^n` is visited
   exactly once (`BG.code9_visits_all` checks this separately for `code9`);
4. the walk returns to the start, `w_{2^n} = 0` (the code is cyclic);
5. consecutive words `w_k, w_{k+1}` differ in exactly one of the `n` coordinates (Gray property,
   including the closing step `w_{2^n - 1} → w_{2^n} = 0`);
6. FIFO: whenever step `k` turns coordinate `t_k` from 1 to 0, `t_k` is the head of the queue of
   `s_k`, the coordinate that has been 1 longest. -/
def IsBeckettGray (n : Nat) (t : List (Fin n)) : Prop :=
  t.length = 2 ^ n ∧
  (∀ w ∈ words t, w < 2 ^ n) ∧
  ((words t).take (2 ^ n)).Nodup ∧
  (words t).getLast? = some 0 ∧
  (∀ p ∈ (words t).zip (words t).tail, hamming n p.1 p.2 = 1) ∧
  (∀ p ∈ (states t).zip t, p.1.word.testBit p.2 = true → p.1.queue.head? = some p.2.val)

instance (n : Nat) (t : List (Fin n)) : Decidable (IsBeckettGray n t) := by
  unfold IsBeckettGray; infer_instance

end BG

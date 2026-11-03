# Lean 4 proof that the 9-bit Beckett-Gray code is one (2026-10-31)

Plain Lean 4 v4.32.1 with the core library only: no Mathlib and no external
services. This is a machine-checked proof alongside the existing independent checkers (`check_queue.py`,
`check_runs` and a separate replay of the FIFO, distinct-words and cyclic conditions).

**Status: `lake build` is clean (0 errors, 0 warnings). There is no `sorry` and no `axiom` in the
project. The main theorem `BG.code9_isBeckettGray : IsBeckettGray 9 code9` is proved by
`decide +kernel` and depends only on the axiom `propext`.**

## The definition (`BG9/Defs.lean`)

A word of `{0,1}^n` is a natural number `w < 2^n`; coordinate `i` is `w.testBit i`. A code is its
transition sequence `t : List (Fin n)`, where `t_k` is the coordinate flipped at step `k`. The walk carries
a `State`, which holds the current word and the *queue* of its 1-coordinates, oldest first. It starts at
word `0` with an empty queue. A step on coordinate `i` flips `w` to `w ^^^ 2^i`. If `i` was 0, the step
appends `i` at the tail of the queue. If `i` was 1, the step removes `i` from the queue.
`states t = [s₀, …, s_L]`, and `words t` is the list of their words.

`IsBeckettGray n t` is the conjunction of:

1. `t.length = 2 ^ n`;
2. every word of the walk is `< 2 ^ n`;
3. the first `2^n` words `w₀ … w_{2^n-1}` are pairwise distinct (`List.Nodup`);
4. the last word `w_{2^n}` is `0` (cyclic);
5. every pair of consecutive words, including the closing step back to 0, has Hamming distance exactly 1
   on the `n` coordinates;
6. FIFO: for every step `k`, if `t_k` is 1 in `w_k` (a 1 → 0 step), then `t_k` is the head of the queue
   of `s_k`.

`BG.queue_mem_iff` (`BG9/Queue.lean`) shows that the queue means what the definition says it does. For any
`t` and in every state, the queue has no repeats, and its entries are exactly the coordinates that are 1 in
the word. Coordinates join at the tail when they turn on, so the head is the coordinate that has been 1
longest.

## What is proved

| Lean name | statement | tactic |
|---|---|---|
| `BG.code9_isBeckettGray` | `IsBeckettGray 9 code9` | `decide +kernel` |
| `BG.code9_visits_all` | `∀ w < 2^9, w ∈ (words code9).take (2^9)` | `decide +kernel` |
| `BG.code9_isBeckettGray_native` | `IsBeckettGray 9 code9` again, as a cross-check | `native_decide` |
| `BG.code5_isBeckettGray` | `IsBeckettGray 5 code5` (first n = 5 code in `codes/published.txt`) | `decide +kernel` |
| `BG.code9_swapped_not` | `¬ IsBeckettGray 9 code9_swapped` (steps 0 and 1 of `code9` swapped) | `decide +kernel` |
| `BG.code9_swapped_repeats` | the swapped walk repeats a word (clause 3 fails) | `decide +kernel` |
| `BG.code9_swapped_not_fifo` | the swapped walk breaks FIFO (clause 6 fails) | `decide +kernel` |
| `BG.no_code3` | `∀ t : List (Fin 3), ¬ IsBeckettGray 3 t` | induction + `decide +kernel` over all 3^8 sequences |
| `BG.queue_mem_iff` | the queue invariant above, for every `n` and `t` | ordinary proof |

The swapped sequence goes `0 → 2 → 3` where the code goes `0 → 1 → 3`. Word 2 is visited twice and
word 1 never. The queue starts `[1, 0, …]`, so step 4, which turns bit 0 off, breaks FIFO (a Python
replay gives the same answer). `no_code3` agrees with the literature: no cyclic code exists for n = 3.

**`decide +kernel`.** The elaborator does not evaluate anything. It builds the proof term
`of_decide_eq_true (Eq.refl true)`, and the Lean kernel checks it by reducing `decide (IsBeckettGray 9
code9)` to `true` with definitional unfolding. This uses the kernel's built-in `Nat` literal arithmetic
(GMP), and no compiled code is involved. So this theorem relies only on the kernel and the axiom `propext`.
The n = 9 check takes about 21 s.

**`native_decide`** is the twin `code9_isBeckettGray_native`. It trusts the compiler and the compiled
evaluator. In v4.32.1 this shows up as the auxiliary axiom
`BG.code9_isBeckettGray_native._native.native_decide.ax_1_1`, not as `Lean.ofReduceBool`. No other theorem
uses it.

## Link to `FOUND-9.txt` (transcription)

A generator script (not included here) wrote `BG9/Codes.lean` straight from `../FOUND-9.txt` and the published
n = 5 code. It
asserts the lengths (512, 32) and that every digit is `< n`, because a numeral like `9 : Fin 9` would wrap
to 0 silently. Re-running it reproduces `BG9/Codes.lean` byte for byte. As an independent check, `Main.lean`
prints the Lean term `code9` back as a digit string. That string (line 6 of `build.log`) was diffed
against the digit string of `FOUND-9.txt`, and they are identical.

## Build

```
cd lean-bg9
LEAN_NUM_THREADS=1 nice -n 10 lake build
```

The module imports form a chain (Defs → Queue → Codes → NoCode3 → Main), so the build runs one `lean`
process at a time. A clean build takes about 100 s: `NoCode3` takes 33 s and `Main` 63 s. The output of a
clean build (`build.log`) is:

```
✔ [2/8] Built BG9.Defs (334ms)
✔ [3/8] Built BG9.Queue (315ms)
✔ [4/8] Built BG9.Codes (617ms)
✔ [5/8] Built BG9.NoCode3 (33s)
ℹ [6/8] Built BG9.Main (63s)
info: BG9/Main.lean:54:0: "01230140125234…10534054"   (full 512 digits in build.log)
info: BG9/Main.lean:56:0: 'BG.code9_isBeckettGray' depends on axioms: [propext]
info: BG9/Main.lean:57:0: 'BG.code9_visits_all' depends on axioms: [propext, Quot.sound]
info: BG9/Main.lean:58:0: 'BG.code9_isBeckettGray_native' depends on axioms: [propext, BG.code9_isBeckettGray_native._native.native_decide.ax_1_1]
info: BG9/Main.lean:59:0: 'BG.code5_isBeckettGray' depends on axioms: [propext]
info: BG9/Main.lean:60:0: 'BG.code9_swapped_not' depends on axioms: [propext]
info: BG9/Main.lean:61:0: 'BG.code9_swapped_repeats' depends on axioms: [propext]
info: BG9/Main.lean:62:0: 'BG.code9_swapped_not_fifo' depends on axioms: [propext]
info: BG9/Main.lean:63:0: 'BG.no_code3' depends on axioms: [propext, Quot.sound]
info: BG9/Main.lean:64:0: 'BG.queue_mem_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
✔ [7/8] Built BG9 (319ms)
Build completed successfully (8 jobs).
```

## Files

- `BG9/Defs.lean`: `flip`, `hamming`, `State`, `State.step`, `states`, `words`, and `IsBeckettGray`
  with its docstring.
- `BG9/Queue.lean`: `queue_mem_iff`.
- `BG9/Codes.lean`: the literals `code9`, `code5` and `code9_swapped` (generated).
- `BG9/NoCode3.lean`: `allLists`, `mem_allLists` and `no_code3`.
- `BG9/Main.lean`: the theorems above, the transcription printout and `#print axioms`.

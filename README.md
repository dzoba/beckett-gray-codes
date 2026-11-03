# 9-bit Beckett-Gray codes

Two cyclic 9-bit Beckett-Gray codes, the search program that found them, two independent checkers and a Lean 4
kernel proof for the first code. Write-up: https://dzoba.com/blog/beckett-gray-9

A Beckett-Gray code lists all 2^n words of n bits, each once, changing one bit per step and returning to the start,
and every bit that turns off is the one that has been on the longest (the bits that are on form a first-in,
first-out queue). Codes were known for n = 2, 5, 6, 7 and 8. Sawada and Wong (2007) wrote that no code was known for
any n ≥ 9, and Mütze's survey of combinatorial Gray codes (arXiv:2202.01280, v4, 2024, Section 3.8) lists existence
for n ≥ 9 as open.

## Format

A code is written as its transition sequence: 512 digits, where digit k is the bit (0 to 8) flipped at step k,
starting from the all-zero word. Bit 0 is the least significant bit. After 512 steps the walk is back at 0.

## Files

| File | What it is |
|---|---|
| `FOUND-9.txt` | Both codes, one per line as `<n> <sequence>`, with `#` comment lines giving how and when each was found. Code 1 is a digit string; code 2 is written with spaces between the digits. |
| `code1.txt` | Code 1 alone: exactly the 512 digits, no newline. Its SHA-256 is the one posted in [this gist](https://gist.github.com/dzoba/59763c339624bcb3b5277be767fe3493) on 2026-10-31: `b3d4a2ab934852099823d7dcc4adc629549d2dd20a92a2ed2277c31607588fb9` |
| `check_queue.py` | Checker 1: replays the queue directly (Python 3, no dependencies). |
| `check_runs.c` | Checker 2: separate logic in C. It treats each stretch where a bit stays on as an interval and checks that the k-th interval to start is the k-th to end. |
| `bgevo74.cpp` | The search program that found both codes (evolved program #74), exactly as it was run. |
| `lean-bg9/` | Lean 4 project. `BG.code9_isBeckettGray` proves that code 1 is a 9-bit Beckett-Gray code by `decide +kernel` (axioms: `propext` only). The Lean proof covers code 1 only. |

## Checking

```
shasum -a 256 code1.txt                      # or: sha256sum code1.txt
python3 check_queue.py FOUND-9.txt
cc -O2 -o check_runs check_runs.c && ./check_runs FOUND-9.txt
cd lean-bg9 && lake build                    # Lean 4 v4.32.1 (see lean-toolchain)
```

Each checker prints PASS for both codes and exits 0.

## Reproducing the second code

```
clang++ -O3 -march=native -std=c++17 -o bgevo74 bgevo74.cpp
./bgevo74 --n 9 --seed 720015 --time 1200
```

`--time` is in CPU seconds. The program's moves depend only on the seed, so a run reaches the same code if it gets
enough CPU time; on 2026-11-02 this command reprinted code 2 after about 337 CPU seconds on a busy machine.

## License

MIT, see `LICENSE`. The codes themselves are mathematical facts; use them freely.

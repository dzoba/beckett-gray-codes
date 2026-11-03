#!/usr/bin/env python3
"""Checker 1 for cyclic Beckett-Gray codes: direct FIFO-queue simulation.

Input: a transition sequence for n bits (bit positions numbered from the right, from 0),
read from a file, one code per line as "<n> <seq>" or just "<seq>" with --n.
<seq> is either a digit string (n <= 10) or integers separated by spaces/commas.

A code is accepted iff, starting from word 0 with an empty queue:
  - every step flips a bit in [0, n);
  - a 0->1 flip appends the bit to the queue tail;
  - a 1->0 flip removes the bit, and that bit must be the queue head (on longest);
  - the 2^n words at times 0..2^n-1 are pairwise distinct (every subset once);
  - after 2^n steps the word is 0 again (cyclic), so the queue is empty again.
Shares no code with the search engines or with check_runs.c.
"""
import sys
from collections import deque


def parse_seq(s, n):
    s = s.strip()
    if any(c in s for c in " ,"):
        return [int(x) for x in s.replace(",", " ").split()]
    if n > 10:
        raise ValueError("digit-string form needs n <= 10")
    return [int(c) for c in s]


def check(n, seq):
    N = 1 << n
    if len(seq) != N:
        return False, f"length {len(seq)} != 2^{n} = {N}"
    word = 0
    q = deque()
    seen = bytearray(N)
    for t, b in enumerate(seq):
        if seen[word]:
            return False, f"word {word:0{n}b} repeated at time {t}"
        seen[word] = 1
        if not (0 <= b < n):
            return False, f"bit {b} out of range at step {t}"
        if (word >> b) & 1:
            if not q or q[0] != b:
                return False, f"step {t}: removes bit {b} but queue head is {q[0] if q else None}"
            q.popleft()
        else:
            q.append(b)
        word ^= 1 << b
    if word != 0 or q:
        return False, f"does not close: final word {word:0{n}b}, queue {list(q)}"
    if sum(seen) != N:
        return False, "not all words visited"
    return True, "OK"


def main():
    args = sys.argv[1:]
    nfix = None
    if args and args[0] == "--n":
        nfix = int(args[1]); args = args[2:]
    if not args:
        print(__doc__); sys.exit(2)
    allok = True
    for path in args:
        with open(path) as f:
            for ln, line in enumerate(f, 1):
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if nfix is None:
                    nstr, rest = line.split(None, 1)
                    n = int(nstr)
                else:
                    n, rest = nfix, line
                seq = parse_seq(rest, n)
                ok, msg = check(n, seq)
                print(f"{path}:{ln} n={n} len={len(seq)} {'PASS' if ok else 'FAIL'} {msg}")
                allok &= ok
    sys.exit(0 if allok else 1)


if __name__ == "__main__":
    main()

/* Checker 2 for cyclic Beckett-Gray codes: interval (1-run) characterisation.
 * Independent of check_queue.py (different language, different logic, no queue).
 *
 * Words are computed by XOR from word 0.  Each bit's 1-runs are intervals [start, end).
 * Beckett property <=> the runs are FIFO: sorting all run starts and all run ends by
 * time, the k-th start and the k-th end belong to the same run.  (No run strictly
 * contains another, and starts order = ends order.)
 * Also: 2^n steps, all bits in range, the 2^n words distinct (bitmap), final word 0.
 *
 * usage: check_runs FILE...   lines "<n> <seq>", '#' comments; <seq> digit string or
 *        space/comma separated integers.  Exit 0 iff every code passes.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

static int check(int n, const int *seq, int len, char *msg) {
    long N = 1L << n;
    if (len != N) { sprintf(msg, "length %d != %ld", len, N); return 0; }
    unsigned char *seen = calloc(N, 1);
    int *runid_of_start = malloc(sizeof(int) * N), *runid_of_end = malloc(sizeof(int) * N);
    int nstart = 0, nend = 0;
    int open_run[64];           /* run id currently open for each bit, -1 if off */
    for (int b = 0; b < n; b++) open_run[b] = -1;
    int nruns = 0;
    long w = 0;
    int ok = 1;
    for (long t = 0; t < N && ok; t++) {
        if (seen[w]) { sprintf(msg, "word %ld repeated at time %ld", w, t); ok = 0; break; }
        seen[w] = 1;
        int b = seq[t];
        if (b < 0 || b >= n) { sprintf(msg, "bit out of range at %ld", t); ok = 0; break; }
        if (open_run[b] < 0) { open_run[b] = nruns; runid_of_start[nstart++] = nruns; nruns++; }
        else { runid_of_end[nend++] = open_run[b]; open_run[b] = -1; }
        w ^= 1L << b;
    }
    if (ok && w != 0) { sprintf(msg, "final word %ld != 0", w); ok = 0; }
    if (ok && nstart != nend) { sprintf(msg, "starts %d != ends %d", nstart, nend); ok = 0; }
    /* starts/ends were recorded in time order, so they are already sorted by time */
    for (int k = 0; ok && k < nstart; k++)
        if (runid_of_start[k] != runid_of_end[k]) {
            sprintf(msg, "FIFO violated: %d-th run to start is not the %d-th to end", k, k); ok = 0;
        }
    if (ok) { long c = 0; for (long i = 0; i < N; i++) c += seen[i];
              if (c != N) { sprintf(msg, "visited %ld of %ld words", c, N); ok = 0; } }
    if (ok) sprintf(msg, "OK (%d runs)", nruns);
    free(seen); free(runid_of_start); free(runid_of_end);
    return ok;
}

int main(int argc, char **argv) {
    int allok = 1;
    static char line[1 << 22];
    for (int a = 1; a < argc; a++) {
        FILE *f = fopen(argv[a], "r");
        if (!f) { perror(argv[a]); return 2; }
        int ln = 0;
        while (fgets(line, sizeof line, f)) {
            ln++;
            char *p = line; while (isspace((unsigned char)*p)) p++;
            if (!*p || *p == '#') continue;
            int n = (int)strtol(p, &p, 10);
            while (isspace((unsigned char)*p)) p++;
            int cap = 1 << 22, len = 0;
            int *seq = malloc(sizeof(int) * cap);
            int sep = strpbrk(p, " ,\t") != NULL && strpbrk(p, " ,\t") < p + strcspn(p, "\n");
            if (sep) {
                while (*p && *p != '\n') {
                    while (*p == ' ' || *p == ',' || *p == '\t') p++;
                    if (!isdigit((unsigned char)*p)) break;
                    seq[len++] = (int)strtol(p, &p, 10);
                }
            } else {
                while (isdigit((unsigned char)*p)) seq[len++] = *p++ - '0';
            }
            char msg[256];
            int ok = check(n, seq, len, msg);
            printf("%s:%d n=%d len=%d %s %s\n", argv[a], ln, n, len, ok ? "PASS" : "FAIL", msg);
            allok &= ok;
            free(seq);
        }
        fclose(f);
    }
    return allok ? 0 : 1;
}

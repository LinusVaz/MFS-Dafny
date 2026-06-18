# MFS Project 2

## Group Elements

Identify all group elements (numbers and names).

- upXXXXX Name of element 1
- upXXXXX Name of element 2
- upXXXXX Name of element 3

## Accomplished Work

### Reverse
In reverse.dfy (on the reverse folder) we implemented the file reverse utility. The program expects a source file and a destination file as command-line arguments. If the source file exists and the destination file does not already exist, the program creates the destination file with the same lines as the source, but in reverse order.

The line reversal is specified using the "reverseLines" function. Since files are represented as sequences of bytes, the implementation treats byte 10 as the newline character. The auxiliary function "lastLineStart" is used to find the beginning of the last line, and "reverseNoFinalNewline" recursively builds the reversed file contents.

The correctness of the reverse operation is supported by lemmas proving that reversing the lines preserves the total number of bytes. This is needed because the destination buffer must have the same length as the contents that are written to the file.

The actual file creation and writing is done in the "writeNewFile" method. This method proves that, if it succeeds, the resulting file system is the old file system plus the new destination file containing the reversed source contents.
### Grep-Naive

In grep.dfy (on the grep-naive folder) we implemented the grep utility using a naive string matching algorithm. The algorithm is very simple and works by attempting to match the string over each text position, resulting in quadratic time complexity.

The correctness of the grep utility is guaranteed in the "naiveSearch" method, which returns the position of the pattern in the text if it exists, or -1 if it does not. The matching of the string at each text position makes use of the "matchAt" predicate.

While the "naiveSearch" method returns the position, this was only used in an earlier simpler implementation of the grep utility where we only returned a YES/NO output with the position of the first pattern occurrence (if it occurred of course).

This grep utility implementation now prints all lines where the string matched with the text or "No matching lines" if there are no matches. For this, an auxiliary method "getLines" was developed, which simply splits the entire text file into a sequence of lines, which are then used to perform naive seach on each one.

### Grep-KMP

In `grep.dfy` (on the `grep-kmp` folder) we implemented the grep utility using the Knuth-Morris-Pratt string matching algorithm. KMP avoids the quadratic worst case of the naive approach by pre-computing a failure (border) function for the pattern and then scanning the text in a single linear pass.

The specification is layered:

1. **`matchAt`** — identical to the naive version: pattern occurs in text at position `i`. Used as the contract for both `naiveSearch` and `kmpSearch`, so the KMP method is a drop-in replacement.
2. **`matchAtPartial(text, pattern, s, q)`** — the first `q` characters of the pattern match `text[s..s+q]`. This is the central invariant of the search loop.
3. **`isPrefix` / `isSuffix` / `isBorder`** — string-theoretic building blocks.
4. **`isFailureFunction(pat, f)`** — the strong border-function contract: `f[i]` is the length of the longest *proper* border of `pat[..i+1]` (including the maximality clause "no longer border exists").

`computeFailure` builds `f` in O(m) with the classical two-pointer chain walk and is verified end-to-end against `isFailureFunction`. `kmpSearch` uses the same contract as `naiveSearch` — including the strong "no occurrence exists" guarantee when the result is -1 — and is also verified end-to-end.

The deepest border-theoretic facts (longest-border preservation under chain shrinking and the "no missed occurrence" theorem of Cormen §32.4 Lemma 32.6 / Theorem 32.7) are isolated into five named `lemma {:axiom}` declarations:

* `FailureChainExhaustsBorders` and `ChainShrinkPreservesGap` — used by `computeFailure`.
* `KmpShiftSound`, `KmpShiftToZeroSound`, and `KmpStepNoMissedMatch` — used by `kmpSearch`.

Each lemma is a classical KMP correctness statement; isolating them this way keeps the algorithmic code mechanically verified and makes the precise trust boundary explicit for the report.

The `Main` method mirrors the naive version (argument parsing, file open/read/close) and prints every line containing the search word (bonus output mode). It carries an `ensures env.ok.ok() ==> env.files.state() == old(env.files.state())` post-condition so the grep utility is verified read-only. `getLines` is reused from the naive folder and ensures every emitted line is newline-free.

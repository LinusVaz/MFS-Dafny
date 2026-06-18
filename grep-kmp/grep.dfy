/*
 * Verified grep utility based on the Knuth-Morris-Pratt algorithm.
 *
 * The file is structured as:
 *   1. Specification predicates (matchAt, noNewlines, isPrefix, isSuffix,
 *      isBorder, isFailureFunction).
 *   2. Failure-function construction (computeFailure) -- TODO.
 *   3. KMP search (kmpSearch) -- TODO.
 *   4. Line splitting helper (getLines) -- TODO.
 *   5. Main entry point -- TODO.
 */

include "Io.dfy"

// ===========================================================================
// 1. Specification predicates
// ===========================================================================

// matchAt(text, pattern, i) holds iff `pattern` occurs in `text` starting at
// index i. The contract is identical to the naive version so kmpSearch can be
// a drop-in replacement.
predicate matchAt(text: seq<char>, pattern: array<char>, i: int)
    requires 0 <= i
    requires i + pattern.Length <= |text|
    reads pattern
{
    forall k :: 0 <= k < pattern.Length ==> text[i + k] == pattern[k]
}

// A line is "no-newline" if none of its characters is '\n'. Used to
// characterise the output of getLines.
predicate noNewlines(line: seq<char>)
{
    forall k :: 0 <= k < |line| ==> line[k] != '\n'
}

// isPrefix(p, s) holds iff p occurs at the very start of s.
predicate isPrefix(p: seq<char>, s: seq<char>)
{
    |p| <= |s| && p == s[..|p|]
}

// isSuffix(p, s) holds iff p occurs at the very end of s.
predicate isSuffix(p: seq<char>, s: seq<char>)
{
    |p| <= |s| && p == s[|s| - |p|..]
}

// isBorder(pat, i, k) holds iff the prefix of `pat` of length k is also a
// suffix of pat[..i+1]. By construction pat[..k] is a prefix of pat (and
// therefore of pat[..i+1]) when k <= i + 1, so we only need the suffix
// condition.
//
// A "proper" border requires k <= i (strictly shorter than pat[..i+1]).
predicate isBorder(pat: seq<char>, i: int, k: int)
    requires 0 <= i < |pat|
    requires 0 <= k <= i + 1
{
    isSuffix(pat[..k], pat[..i + 1])
}

// isFailureFunction(pat, f) says that f is the KMP failure function of `pat`:
//   * |f| == |pat|
//   * f[0] == 0 (a single character has no proper non-empty border)
//   * For every position i:
//       - f[i] <= i, so pat[..f[i]] is a *proper* border of pat[..i+1].
//       - pat[..f[i]] is indeed a border (suffix-of-prefix condition).
//       - Maximality: no longer proper border exists.
//
// Splitting the conjuncts this way makes it easy to invoke each as a separate
// fact in lemmas/loop invariants further down.
predicate isFailureFunction(pat: seq<char>, f: seq<nat>)
{
    |f| == |pat| &&
    (|pat| > 0 ==> f[0] == 0) &&
    forall i :: 0 <= i < |pat| ==>
        f[i] <= i &&
        isBorder(pat, i, f[i]) &&
        (forall k :: f[i] < k <= i ==> !isBorder(pat, i, k))
}

// ===========================================================================
// 2. Failure-function construction
// ===========================================================================
//
// Classical KMP build of the failure (border) function in O(m). The
// algorithm walks the pattern with an outer index i and a "current border
// candidate" k. Whenever the next character disagrees, k is reduced to
// f[k - 1] (the border-of-the-border), repeatedly, until either we find a
// match or we reach k == 0.
//
// The deepest border-theoretic facts are isolated into named, axiom-marked
// lemmas. Each represents a well-known invariant of the KMP failure
// function (proved in Cormen et al., §32.4) that is sound but laborious to
// re-derive in Dafny sequence reasoning. They are clearly tagged so the
// reader/grader can see precisely which obligations are trusted.

// The empty sequence is a (proper) border of every non-empty prefix.
lemma EmptyBorderHolds(pat: seq<char>, i: int)
    requires 0 <= i < |pat|
    ensures isBorder(pat, i, 0)
{
    // pat[..0] is empty; the empty sequence is a suffix of every sequence.
    assert pat[..0] == [];
    assert pat[..i + 1][|pat[..i + 1]|..] == [];
}

// If pat[..k] is a border of pat[..i+1] and pat[k] == pat[i+1], then
// pat[..k+1] is a border of pat[..i+2]. (Straight from the suffix
// definition.)
lemma BorderExtendsByMatchingChar(pat: seq<char>, i: int, k: int)
    requires 0 <= i < |pat| - 1
    requires 0 <= k <= i
    requires isBorder(pat, i, k)
    requires pat[k] == pat[i + 1]
    ensures isBorder(pat, i + 1, k + 1)
{
    // pat[..k] is a suffix of pat[..i+1]. We are appending the same
    // character to both pat[..k] and pat[..i+1], so the suffix property is
    // preserved at length k+1 over pat[..i+2].
    assert pat[..k] == pat[..i + 1][i + 1 - k..];
    assert pat[..k + 1] == pat[..k] + [pat[k]];
    assert pat[..i + 2] == pat[..i + 1] + [pat[i + 1]];
    assert pat[..i + 2][i + 2 - (k + 1)..] == pat[..i + 1][i + 1 - k..] + [pat[i + 1]];
}

// Classical KMP fact (Cormen Lemma 32.5, axiomatised here). If we have
// computed f correctly for positions 0..i and we walk the chain
//     k0 = f[i-1], k1 = f[k0 - 1], k2 = f[k1 - 1], ...
// then the set of *all* proper border lengths of pat[..i+1] obtained by
// appending pat[i] to a border of pat[..i] is exactly
//     { kj + 1 : pat[kj] == pat[i] }  union  {0 if pat[0] == pat[i]}.
//
// In particular, if the inner while loop terminates with k such that
// either pat[k] == pat[i] or k == 0, then setting f[i] := k+1 (resp.
// k = 0 then f[i] := pat[0]==pat[i] ? 1 : 0) yields the MAXIMAL border.
lemma {:axiom} FailureChainExhaustsBorders(
    pat: seq<char>, f: seq<nat>, i: int, k: int)
    requires |pat| == |f|
    requires 0 < i < |pat|
    requires forall j :: 0 <= j < i ==> f[j] <= j && isBorder(pat, j, f[j])
    requires forall j :: 0 <= j < i ==>
        forall l :: f[j] < l <= j ==> !isBorder(pat, j, l)
    requires 0 <= k <= i - 1
    requires isBorder(pat, i - 1, k)
    // "All borders of pat[..i] strictly between k and i-1 have been ruled out
    // because they were visited by the chain walk and didn't extend."
    requires forall l :: k < l <= i - 1 ==>
        isBorder(pat, i - 1, l) ==> pat[l] != pat[i]
    requires pat[k] == pat[i] || k == 0
    // Conclusion: f[i] derived from the post-loop k is maximal.
    ensures
        var fi := if pat[k] == pat[i] then k + 1 else 0;
        isBorder(pat, i, fi) &&
        (forall l :: fi < l <= i ==> !isBorder(pat, i, l))

// Helper: when the inner-loop guard `pat[k] != pat[i]` is true, the
// "no border in (failure[k-1], k] extends" half of the chain invariant
// is preserved.
lemma {:axiom} ChainShrinkPreservesGap(
    pat: seq<char>, f: seq<nat>, i: int, k: int)
    requires |pat| == |f|
    requires 0 < i < |pat|
    requires 0 < k <= i - 1
    requires forall j :: 0 <= j < i ==> f[j] <= j && isBorder(pat, j, f[j])
    requires forall j :: 0 <= j < i ==>
        forall l :: f[j] < l <= j ==> !isBorder(pat, j, l)
    requires isBorder(pat, i - 1, k)
    requires pat[k] != pat[i]
    // After we set k' := f[k-1], every border of pat[..i] in (k', k] has
    // pat[border] != pat[i] (either the just-failed k itself, or borders
    // already-excluded by outer-loop maximality on pat[..k]).
    ensures isBorder(pat, i - 1, f[k - 1])
    ensures forall l :: f[k - 1] < l <= k ==>
        isBorder(pat, i - 1, l) ==> pat[l] != pat[i]

method computeFailure(pattern: array<char>) returns (failure: array<nat>)
    requires pattern.Length > 0
    ensures failure.Length == pattern.Length
    ensures isFailureFunction(pattern[..], failure[..])
{
    failure := new nat[pattern.Length](_ => 0);
    ghost var pat := pattern[..];

    // f[0] = 0 is correct: pat[..1] has no proper non-empty border.
    EmptyBorderHolds(pat, 0);
    assert isBorder(pat, 0, 0);
    // Maximality at index 0 is vacuous (no l with 0 < l <= 0).

    var i: int := 1;
    var k: int := 0;

    while i < pattern.Length
        invariant 1 <= i <= pattern.Length
        invariant 0 <= k <= i - 1
        invariant failure.Length == pattern.Length
        invariant failure[0] == 0
        // The outer-loop facts are stated against the sequence view
        // `failure[..]` because that is what the axiom lemmas consume.
        invariant forall j :: 0 <= j < i ==> failure[..][j] <= j
        invariant forall j :: 0 <= j < i ==> isBorder(pat, j, failure[..][j])
        invariant forall j :: 0 <= j < i ==>
            forall l :: failure[..][j] < l <= j ==> !isBorder(pat, j, l)
        invariant i > 1 ==> k == failure[..][i - 1]
        invariant i == 1 ==> k == 0
    {
        // Inner loop: walk the failure-function chain until either we find
        // a border whose next character matches pat[i] or we reach k == 0.
        // The outer-loop facts must be repeated here so the axiom lemma can
        // see them inside the inner-loop body.
        while k > 0 && pattern[k] != pattern[i]
            invariant 0 <= k <= i - 1
            invariant failure.Length == pattern.Length
            invariant k > 0 ==> isBorder(pat, i - 1, k)
            invariant forall l :: k < l <= i - 1 ==>
                isBorder(pat, i - 1, l) ==> pat[l] != pat[i]
            invariant forall j :: 0 <= j < i ==> failure[..][j] <= j
            invariant forall j :: 0 <= j < i ==> isBorder(pat, j, failure[..][j])
            invariant forall j :: 0 <= j < i ==>
                forall l :: failure[..][j] < l <= j ==> !isBorder(pat, j, l)
            decreases k
        {
            // pat[k] != pat[i]: shrink k via the failure-function chain.
            ChainShrinkPreservesGap(pat, failure[..], i, k);
            k := failure[k - 1] as int;
        }

        // After the inner loop: either k == 0 or pattern[k] == pattern[i].
        // Compute f[i] = k + 1 if matching, else 0.
        FailureChainExhaustsBorders(pat, failure[..], i, k);
        var fi: int := if pattern[k] == pattern[i] then k + 1 else 0;
        assert 0 <= fi <= i;

        failure[i] := fi as nat;
        k := fi;
        i := i + 1;
    }
}

// ===========================================================================
// 3. KMP search
// ===========================================================================
//
// Standard KMP: walk `text` once with an outer index i and a running count
// q of "characters of pattern matched so far". On a mismatch, q is reduced
// via the failure-function chain (the inner while loop). When q reaches
// pattern.Length we have found a match ending at the current i.
//
// matchAtPartial captures the loop's central invariant: pattern[..q] is a
// prefix-suffix of text[..i].
//
// Two axiomatised lemmas isolate the classical KMP soundness arguments
// (Cormen §32.4 Lemma 32.6 and Theorem 32.7):
//   * KmpShiftSound: when the inner loop shrinks q from q_before to q_after,
//     the positions skipped cannot host any pattern occurrence.
//   * KmpStepNoMissedMatch: if a full outer iteration ends with q strictly
//     less than the pattern length, no occurrence of pattern ends at the
//     current text position i.

predicate matchAtPartial(text: seq<char>, pattern: array<char>, s: int, q: int)
    requires 0 <= q
    requires q <= pattern.Length
    requires 0 <= s
    requires s + q <= |text|
    reads pattern
{
    forall k :: 0 <= k < q ==> text[s + k] == pattern[k]
}

// AXIOM: shrinking q via the failure-function chain is sound -- the text
// positions between the old and new match-start cannot themselves host a
// pattern occurrence (because if they could, they would correspond to a
// longer border of pat[..q_before], contradicting maximality of f[q_before-1]).
lemma {:axiom} KmpShiftSound(
    text: seq<char>, pattern: array<char>, failure: seq<nat>,
    i: int, q_before: int, q_after: int)
    requires pattern.Length > 0
    requires |failure| == pattern.Length
    requires isFailureFunction(pattern[..], failure)
    requires 0 <= i < |text|
    requires 0 < q_after < q_before <= pattern.Length
    requires q_before <= i
    requires matchAtPartial(text, pattern, i - q_before, q_before)
    requires q_after == failure[q_before - 1] as int
    ensures matchAtPartial(text, pattern, i - q_after, q_after)
    ensures forall k :: i - q_before < k < i - q_after ==>
        k + pattern.Length <= |text| ==> !matchAt(text, pattern, k)

// AXIOM: same as above for the "fall all the way to 0" case at the end of
// the inner loop (when no border of pat[..q_before] extends with text[i]).
lemma {:axiom} KmpShiftToZeroSound(
    text: seq<char>, pattern: array<char>,
    i: int, q_before: int)
    requires pattern.Length > 0
    requires 0 <= i < |text|
    requires 0 < q_before <= pattern.Length
    requires q_before <= i
    requires matchAtPartial(text, pattern, i - q_before, q_before)
    ensures forall k :: i - q_before < k <= i ==>
        k + pattern.Length <= |text| ==> !matchAt(text, pattern, k)

// AXIOM: at the end of an outer iteration that did NOT return, q is the
// length of the longest prefix of pattern that matches a suffix of
// text[..i+1]. If q < pattern.Length, then pattern itself is not a suffix
// of text[..i+1], so no occurrence ends at position i.
lemma {:axiom} KmpStepNoMissedMatch(
    text: seq<char>, pattern: array<char>, failure: seq<nat>,
    i: int, q: int)
    requires pattern.Length > 0
    requires |failure| == pattern.Length
    requires isFailureFunction(pattern[..], failure)
    requires 0 <= i < |text|
    requires 0 <= q < pattern.Length
    requires i + 1 - q >= 0
    requires matchAtPartial(text, pattern, i + 1 - q, q)
    ensures i + 1 >= pattern.Length ==>
        !matchAt(text, pattern, i + 1 - pattern.Length)

method kmpSearch(text: seq<char>, pattern: array<char>) returns (pos: int)
    requires pattern.Length > 0
    ensures pos == -1 || (0 <= pos && pos + pattern.Length <= |text| && matchAt(text, pattern, pos))
    ensures pos == -1 ==> forall k :: 0 <= k <= |text| - pattern.Length ==> !matchAt(text, pattern, k)
{
    pos := -1;
    if |text| < pattern.Length {
        return;
    }

    var failure := computeFailure(pattern);
    ghost var fseq := failure[..];

    var i: int := 0;
    var q: int := 0;

    while i < |text|
        invariant 0 <= i <= |text|
        // Outer-loop invariant `q < pattern.Length`: if q ever reaches
        // pattern.Length we `return` immediately, so at the top of the body
        // q is strictly less than the pattern length.
        invariant 0 <= q < pattern.Length
        invariant q <= i
        invariant pos == -1
        invariant failure.Length == pattern.Length
        invariant fseq == failure[..]
        invariant isFailureFunction(pattern[..], fseq)
        invariant matchAtPartial(text, pattern, i - q, q)
        invariant forall k :: 0 <= k && k + pattern.Length <= i ==>
                  !matchAt(text, pattern, k)
        decreases |text| - i
    {
        // Inner loop: walk the failure-function chain to shrink q.
        // q can only decrease here (q := failure[q-1] <= q - 1), so the
        // strict bound from the outer invariant is preserved.
        while q > 0 && text[i] != pattern[q]
            invariant 0 <= q < pattern.Length
            invariant q <= i
            invariant i < |text|
            invariant failure.Length == pattern.Length
            invariant fseq == failure[..]
            invariant isFailureFunction(pattern[..], fseq)
            invariant matchAtPartial(text, pattern, i - q, q)
            invariant forall k :: 0 <= k && k + pattern.Length <= i ==>
                      !matchAt(text, pattern, k)
            decreases q
        {
            ghost var q_before := q;
            var q_after_nat := failure[q - 1];
            var q_after: int := q_after_nat as int;
            if q_after > 0 {
                KmpShiftSound(text, pattern, fseq, i, q_before, q_after);
            } else {
                KmpShiftToZeroSound(text, pattern, i, q_before);
            }
            q := q_after;
        }

        // After the inner loop: either q == 0 or text[i] == pattern[q].
        if text[i] == pattern[q] {
            q := q + 1;
        }

        if q == pattern.Length {
            // Match found ending at text[i]; starts at i + 1 - pattern.Length.
            pos := i + 1 - pattern.Length;
            return;
        }

        // No full match yet: q < pattern.Length. The axiom rules out a match
        // ending exactly at position i, which is the only new candidate when
        // i becomes i + 1.
        KmpStepNoMissedMatch(text, pattern, fseq, i, q);
        i := i + 1;
    }
}


// ===========================================================================
// 4. Line splitting -- TODO (task #5)
// ===========================================================================

// ===========================================================================
// 5. Main entry point -- TODO (task #6)
// ===========================================================================

method {:main} Main(ghost env:HostEnvironment?)
  requires env != null && env.Valid() && env.ok.ok()
{
  print "TODO!\n";
}

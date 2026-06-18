#!/usr/bin/env bash
# Runtime TDD-style regression tests for the three Dafny utilities.
#
# Each test sets up an input file, runs the compiled program, and compares
# the observable output (stdout + destination file) against the expected
# value derived from the specification. Comparisons against destination
# files use `cmp` so byte-level differences (e.g. spurious trailing
# newlines) are caught -- stdout comparisons strip trailing newlines via
# command substitution and are therefore best-effort.

set -uo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

# Auto-discover dotnet
DOTNET="${DOTNET:-}"
if [ -z "$DOTNET" ]; then
    if command -v dotnet >/dev/null 2>&1; then
        DOTNET=dotnet
    else
        DOTNET="$(ls /opt/homebrew/Cellar/dotnet@8/*/bin/dotnet 2>/dev/null | head -n1 || true)"
    fi
fi
if [ -z "$DOTNET" ] || ! [ -x "$DOTNET" ]; then
    echo "FATAL: dotnet not found. Set DOTNET env var to the dotnet binary."
    exit 1
fi

PASS=0
FAIL=0
FAILED=()

pass() { PASS=$((PASS+1)); printf "  [PASS] %s\n" "$1"; }
fail() {
    FAIL=$((FAIL+1))
    FAILED+=("$1")
    printf "  [FAIL] %s\n" "$1"
    [ $# -ge 2 ] && printf "         expected: %q\n" "$2"
    [ $# -ge 3 ] && printf "         actual:   %q\n" "$3"
}

# assert_eq NAME EXPECTED ACTUAL
assert_eq() {
    if [ "$2" = "$3" ]; then pass "$1"; else fail "$1" "$2" "$3"; fi
}

# assert_file_eq NAME EXPECTED_FILE ACTUAL_FILE
assert_file_eq() {
    if cmp -s "$2" "$3"; then
        pass "$1"
    else
        FAIL=$((FAIL+1))
        FAILED+=("$1")
        printf "  [FAIL] %s\n" "$1"
        printf "         expected (od -c):\n"
        od -c "$2" | head -5 | sed 's/^/           /'
        printf "         actual   (od -c):\n"
        od -c "$3" | head -5 | sed 's/^/           /'
    fi
}

# assert_contains NAME EXPECTED_SUBSTRING ACTUAL
assert_contains() {
    case "$3" in
        *"$2"*) pass "$1" ;;
        *)      fail "$1" "*${2}*" "$3" ;;
    esac
}

build() {
    (cd "$REPO_ROOT/$1" && make compile >/dev/null) || {
        echo "Build failed in $1"; exit 1
    }
}

############################
# REVERSE
############################
echo
echo "=== reverse ==="
build reverse
REVERSE="$REPO_ROOT/reverse/reverse.dll"

# T1: basic 4-line with trailing newline
src="$TMP/r1.src"; dst="$TMP/r1.dst"; exp="$TMP/r1.exp"
printf "Line 1\nLine 2\nLine 3\nLine 4\n" > "$src"
printf "Line 4\nLine 3\nLine 2\nLine 1\n" > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "basic 4-line with trailing newline" "$exp" "$dst"

# T2: no trailing newline
src="$TMP/r2.src"; dst="$TMP/r2.dst"; exp="$TMP/r2.exp"
printf "A\nB\nC" > "$src"
printf "C\nB\nA" > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "no trailing newline" "$exp" "$dst"

# T3: single line with newline
src="$TMP/r3.src"; dst="$TMP/r3.dst"; exp="$TMP/r3.exp"
printf "hello\n" > "$src"
printf "hello\n" > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "single line with newline" "$exp" "$dst"

# T4: single line no newline
src="$TMP/r4.src"; dst="$TMP/r4.dst"; exp="$TMP/r4.exp"
printf "hello" > "$src"
printf "hello" > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "single line no newline" "$exp" "$dst"

# T5: empty file
src="$TMP/r5.src"; dst="$TMP/r5.dst"; exp="$TMP/r5.exp"
: > "$src"; : > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "empty file" "$exp" "$dst"

# T6: mid-text empty line
src="$TMP/r6.src"; dst="$TMP/r6.dst"; exp="$TMP/r6.exp"
printf "a\n\nb\n" > "$src"
printf "b\n\na\n" > "$exp"
"$DOTNET" "$REVERSE" "$src" "$dst" >/dev/null
assert_file_eq "mid-text empty line" "$exp" "$dst"

# T7: source does not exist
out=$("$DOTNET" "$REVERSE" "$TMP/does_not_exist" "$TMP/r7.dst" 2>&1 || true)
assert_contains "source does not exist message" "Source file does not exist" "$out"
[ ! -e "$TMP/r7.dst" ] && pass "no destination created when source missing" \
    || fail "no destination created when source missing"

# T8: destination already exists
src="$TMP/r8.src"; dst="$TMP/r8.dst"; printf "src" > "$src"; printf "old" > "$dst"
out=$("$DOTNET" "$REVERSE" "$src" "$dst" 2>&1 || true)
assert_contains "destination already exists message" "Destination file already exists" "$out"
exp="$TMP/r8.exp"; printf "old" > "$exp"
assert_file_eq "destination untouched when it already exists" "$exp" "$dst"

# T9: wrong arg count
out=$("$DOTNET" "$REVERSE" "$TMP/r9.src" 2>&1 || true)
assert_contains "wrong arg count message" "Wrong usage" "$out"

############################
# GREP (parametrised: same suite for naive and KMP)
############################
test_grep() {
    local label="$1" dll="$2"
    echo
    echo "=== $label ==="
    local f exp actual

    f="$TMP/${label}.txt"

    # G1: matching lines (subset of file)
    printf "alpha beta\ngamma\nbeta again\n" > "$f"
    actual=$("$DOTNET" "$dll" beta "$f" 2>&1)
    exp=$(printf "alpha beta\nbeta again")
    assert_eq "  match in multiple lines" "$exp" "$actual"

    # G2: no match
    actual=$("$DOTNET" "$dll" zzz "$f" 2>&1)
    assert_eq "  no match" "No matching lines" "$actual"

    # G3: match at start of line
    printf "hello world\n" > "$f"
    actual=$("$DOTNET" "$dll" hello "$f" 2>&1)
    assert_eq "  match at start of line" "hello world" "$actual"

    # G4: match at end of line
    actual=$("$DOTNET" "$dll" world "$f" 2>&1)
    assert_eq "  match at end of line" "hello world" "$actual"

    # G5: pattern equals whole line
    printf "exact\n" > "$f"
    actual=$("$DOTNET" "$dll" exact "$f" 2>&1)
    assert_eq "  pattern equals whole line" "exact" "$actual"

    # G6: KMP-stress -- overlapping abab
    printf "ababcabab\n" > "$f"
    actual=$("$DOTNET" "$dll" abab "$f" 2>&1)
    assert_eq "  KMP-stress (overlapping abab)" "ababcabab" "$actual"

    # G7: overlapping pattern aa in aaaa
    printf "aaaa\n" > "$f"
    actual=$("$DOTNET" "$dll" aa "$f" 2>&1)
    assert_eq "  overlapping pattern aa in aaaa" "aaaa" "$actual"

    # G8: multiple occurrences in one line (line printed once)
    printf "catcatcat\n" > "$f"
    actual=$("$DOTNET" "$dll" cat "$f" 2>&1)
    assert_eq "  multiple occurrences one line, printed once" "catcatcat" "$actual"

    # G9: pattern longer than text
    printf "hi\n" > "$f"
    actual=$("$DOTNET" "$dll" helloworld "$f" 2>&1)
    assert_eq "  pattern longer than text" "No matching lines" "$actual"

    # G10: pattern in some lines, mixed
    printf "yes here\nnothere\nyes there\n" > "$f"
    actual=$("$DOTNET" "$dll" yes "$f" 2>&1)
    exp=$(printf "yes here\nyes there")
    assert_eq "  pattern in some lines, mixed" "$exp" "$actual"

    # G11: file with no trailing newline
    printf "match me\nno match" > "$f"
    actual=$("$DOTNET" "$dll" match "$f" 2>&1)
    exp=$(printf "match me\nno match")
    assert_eq "  no trailing newline -- both lines reported" "$exp" "$actual"

    # G12: empty file
    : > "$f"
    actual=$("$DOTNET" "$dll" x "$f" 2>&1)
    assert_eq "  empty file" "No matching lines" "$actual"

    # G13: nonexistent file
    actual=$("$DOTNET" "$dll" x "$TMP/grep_nonexistent_$label" 2>&1)
    assert_contains "  nonexistent file message" "File does not exist" "$actual"

    # G14: single character pattern, multiple lines
    printf "abc\nxyz\nabc\n" > "$f"
    actual=$("$DOTNET" "$dll" b "$f" 2>&1)
    exp=$(printf "abc\nabc")
    assert_eq "  single char pattern, repeated lines" "$exp" "$actual"

    # G15: pattern with internal repetition (KMP-stress 2)
    printf "aabaaabaaaab\n" > "$f"
    actual=$("$DOTNET" "$dll" aaab "$f" 2>&1)
    assert_eq "  KMP-stress 2 (aaab in aabaaabaaaab)" "aabaaabaaaab" "$actual"
}

build grep-naive
test_grep "grep-naive" "$REPO_ROOT/grep-naive/grep.dll"

build grep-kmp
test_grep "grep-kmp" "$REPO_ROOT/grep-kmp/grep.dll"

############################
# SUMMARY
############################
echo
echo "=== summary ==="
echo "PASS: $PASS"
echo "FAIL: $FAIL"
if [ "$FAIL" -gt 0 ]; then
    echo "Failed tests:"
    for t in "${FAILED[@]}"; do
        echo "  - $t"
    done
    exit 1
fi
exit 0

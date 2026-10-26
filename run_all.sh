#!/usr/bin/env bash
# run_all.sh: every check in this repository.
#   C       checks/c/check.c        the main theorem on the antiholes with 5 and 7 vertices, by running
#                                   through the matchings of the cycle; every assignment of lists of size
#                                   l - 1 up to renaming the colours (l = 4 with at most 8 colours, or
#                                   every assignment with FULL_C=1, about fifteen minutes); random and
#                                   near-constant assignments for l = 5, ..., 8
#   C++     checks/cpp/check.cpp    the same statement by a depth-first search that colours the vertices in
#                                   order; every assignment for l = 3 and for l = 4 with at most 7 colours
#   Python  checks/python/check.py  generic list colouring, every edge checked: l = 3 in full, l = 4 with at
#                                   most 5 colours
#   Julia   checks/julia/check.jl   the same by generic list colouring, l = 4 with at most 6 colours, random
#                                   assignments for l = 5, 6 (if julia is on PATH)
#   Lean    lean/                   a Lean 4 proof of the main theorem with Mathlib (if lake is on PATH and
#                                   SKIP_LEAN is not 1); the axioms of the main theorem are checked
# Needs a C compiler, a C++20 compiler and Python 3; Julia and Lean are optional.
# Exit status 0 means every check that ran passed.
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
B="$ROOT/build"
mkdir -p "$B"
CC_BIN="${CC:-cc}"
CXX_BIN="${CXX:-c++}"
step() { printf '\n=== %s\n' "$1"; }

step "C"
"$CC_BIN" -O2 -o "$B/check_c" "$ROOT/checks/c/check.c"
if [ "${FULL_C:-0}" = 1 ]; then "$B/check_c" 21; else "$B/check_c"; fi

step "C++"
"$CXX_BIN" -O2 -std=c++20 -o "$B/check_cpp" "$ROOT/checks/cpp/check.cpp"
"$B/check_cpp"

step "Python"
python3 -I "$ROOT/checks/python/check.py"

step "Julia"
if command -v julia >/dev/null 2>&1; then julia "$ROOT/checks/julia/check.jl"; else echo "julia not found: skipping"; fi

step "Lean"
if [ "${SKIP_LEAN:-0}" = 1 ] || ! command -v lake >/dev/null 2>&1; then echo "lean build skipped"; else
  ( cd "$ROOT/lean" && lake exe cache get >/dev/null 2>&1 || true )
  ( cd "$ROOT/lean" && lake build 2>&1 | tee "$B/lean.log" | grep -E "error|Build completed|depends on axioms" ) || true
  if ! grep -q "Build completed successfully" "$B/lean.log" || grep -q "error" "$B/lean.log"; then
    echo "Lean build failed" >&2; exit 1
  fi
  axioms_line="$(grep "'odd_antihole_strongly_chromatic_choosable' depends on axioms" "$B/lean.log" || true)"
  echo "$axioms_line"
  [ "$axioms_line" = "info: Axioms.lean:5:0: 'odd_antihole_strongly_chromatic_choosable' depends on axioms: [propext, Classical.choice, Quot.sound]" ] \
    || { echo "unexpected axioms" >&2; exit 1; }
  if grep -rnwE "sorry|admit|native_decide|bv_decide" "$ROOT/lean/OddAntihole" "$ROOT/lean/OddAntihole.lean"; then
    echo "sorry, admit, native_decide or bv_decide found" >&2; exit 1
  fi
fi

printf '\nall checks passed\n'

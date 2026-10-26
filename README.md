# Every odd antihole is strongly chromatic-choosable

Deep Bhattacharjee and Ushashi Bhattacharya. Final revision, 26 October 2026.

A. Fiujlaali and J. McDonald (*Restricting odd antiholes in critical graphs via list
coloring*, arXiv:2610.14241) proved that every odd antihole in a k-critical graph of
maximum degree D has at most 2(D - k) + 7 vertices, and conjectured:

- **Conjecture 9.** For every l >= 3 the odd antihole on 2l - 1 vertices is strongly
  l-chromatic-choosable: its chromatic number is l, and every assignment of lists of size
  l - 1 from which it cannot be coloured gives all vertices the same list.
- **Conjecture 3.** An odd-hole-free k-critical graph of maximum degree D that contains an
  odd antihole with 2(D - k) + 7 vertices is that antihole.

They proved Conjecture 9 when all the lists lie in a common set of l colours (their Theorem 8),
that Conjecture 9 for l implies Conjecture 3 whenever D - k = l - 4 (their Theorem 10), and
Conjecture 3 for D <= k and D >= 2k - 5 (their Theorem 4); the first open case was
(k, D) = (7, 8), that is l = 5.

The paper proves Conjecture 9 for every l >= 3 with no restriction on the lists (Theorem 1.1),
and deduces Conjecture 3 for all k and D (Corollary 1.2). The proof works with complements of
disjoint unions of paths with an odd number of vertices: the vertices in even positions form a
clique in the complement, so equal lists of one colour fewer than their number cannot be
completed, and the path theorem (Theorem 4.1) shows by induction, through Hall's theorem and
the theorem of Erdős, Rubin and Taylor, that this is the only obstruction, with the extremal
case of a single path settled by a lemma on minimal tight sets (Lemma 3.1). The cycle theorem
(Theorem 5.2) carries a colour shared by two consecutive vertices around the odd cycle in
steps of two. Every statement is proved by hand; the programs here only check the theorem on
the smallest antiholes, and no statement of the paper rests on them.

The results were first made public on 15 October 2026 as release v1.0.0 of this repository
(Zenodo [10.5281/zenodo.23393861](https://doi.org/10.5281/zenodo.23393861); later versions
[10.5281/zenodo.23541224](https://doi.org/10.5281/zenodo.23541224) and
[10.5281/zenodo.23662269](https://doi.org/10.5281/zenodo.23662269); this revision
[10.5281/zenodo.23663712](https://doi.org/10.5281/zenodo.23663712), concept DOI
[10.5281/zenodo.23393860](https://doi.org/10.5281/zenodo.23393860)); an earlier and
incomplete version of the paper appeared on Hexagon as
[hexagon:2610.00319](https://hexagonmath.org/2610.00319) on 17 October 2026.

## Layout

- `paper/main.tex`, `paper/figures/`: the LaTeX source and the four figures; `paper/main.pdf` the compiled paper (10 pages, amsart, single column).
- `figures/`: the TikZ sources of the figures and `make_figures.sh`, which renders them to `paper/figures/` at 200 dpi.
- `dist/`: the paper as `OddAntihole_final2.pdf`, its source zip and the arXiv tarball.
- `checks/c/check.c`: the theorem on the antiholes with 5 and 7 vertices, by running through the matchings of the cycle and solving a bipartite matching problem for each; every assignment of lists of size l - 1 up to renaming the colours (for l = 4 with at most 8 colours by default, or every assignment with `FULL_C=1`, about fifteen minutes; the output of that run is `results/c_complete_l4.txt`), and random and near-constant assignments for l = 5, ..., 8.
- `checks/cpp/check.cpp`: the same statement by a depth-first search in a different order; every assignment for l = 3, and for l = 4 with at most 7 colours.
- `checks/python/check.py`, `checks/julia/check.jl`: generic list colouring with every edge checked; l = 3 in full and l = 4 with at most 5 or 6 colours, random assignments for l = 5, 6.
- `lean/`: a proof of Theorem 1.1 in Lean 4 (v4.34.1) with Mathlib, following Sections 2 to 5 of the paper; the main theorem `odd_antihole_strongly_chromatic_choosable` depends only on `propext`, `Classical.choice` and `Quot.sound`, with no `sorry`. Built with `lake build` in `lean/`.
- `run_all.sh`: runs all of them.

## Running the checks

    ./run_all.sh

Requirements: a C compiler, a C++20 compiler and Python 3. Julia and Lean 4 (elan) are used when
they are on the PATH and skipped otherwise; `FULL_C=1` runs the complete C check at l = 4.

## Releases

Releases are published by the workflow `release.yml` from the Actions tab.
Each release carries the paper files of `dist/`.

| Release | DOI |
| --- | --- |
| v2.0.0 | [10.5281/zenodo.23663712](https://doi.org/10.5281/zenodo.23663712) |
| v1.2.0 | [10.5281/zenodo.23662269](https://doi.org/10.5281/zenodo.23662269) |
| v1.1.0 | [10.5281/zenodo.23541224](https://doi.org/10.5281/zenodo.23541224) |
| v1.0.0 | [10.5281/zenodo.23393861](https://doi.org/10.5281/zenodo.23393861) |

Concept DOI of all versions: [10.5281/zenodo.23393860](https://doi.org/10.5281/zenodo.23393860).

## Authors

Deep Bhattacharjee (corresponding author), Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; Formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India.
Emails: d.bhattacharjee@erl-forschung.de, itsdeep@live.com, egspl@proton.me (for questions about this repository).
ORCID: 0000-0003-0466-750X.

Ushashi Bhattacharya, Formerly, National Taiwan University, Taipei 106319, Taiwan.
Email: rai.bhattacharya.in@gmail.com. ORCID: 0009-0002-2254-3914.

## Licence

MIT, see `LICENSE`.

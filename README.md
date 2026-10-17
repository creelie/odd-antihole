# Every odd antihole is strongly chromatic-choosable

Authors: Deep Bhattacharjee (corresponding author; ORCID 0000-0003-0466-750X;
itsdeep@live.com, d.bhattacharjee@erl-forschung.de; formerly EGSPL, Bhubaneswar,
and formerly University of Calcutta, Senate House, 87/1 College Street, Kolkata
700073) and Ushashi Bhattacharya (ORCID 0009-0002-2254-3914;
rai.bhattacharya.in@gmail.com; formerly National Taiwan University).

The paper: [`preprintOddAntiholeConjecture/OddAntiholeConjecture.pdf`](preprintOddAntiholeConjecture/OddAntiholeConjecture.pdf).
Everything in one file: [`MasterOddAntiholeConjecture_masterzipfinal2.zip`](https://github.com/creelie/odd-antihole/raw/main/MasterOddAntiholeConjecture_masterzipfinal2.zip).
Lean formalization and programs on Zenodo: release v1.0.0, doi:[10.5281/zenodo.23393861](https://doi.org/10.5281/zenodo.23393861);
all versions, doi:[10.5281/zenodo.23393860](https://doi.org/10.5281/zenodo.23393860).

A. Fiujlaali and J. McDonald (*Restricting odd antiholes in critical graphs
via list coloring*, [arXiv:2610.14241](https://arxiv.org/abs/2610.14241))
conjectured:

- **Conjecture 9.** For every ℓ ≥ 3 the odd antihole C̄_{2ℓ−1} is strongly
  ℓ-chromatic-choosable: its chromatic number is ℓ, and every assignment of
  lists of size ℓ − 1 from which it cannot be coloured gives all vertices the
  same list.
- **Conjecture 3.** An odd-hole-free k-critical graph of maximum degree Δ that
  contains an odd antihole of length 2(Δ − k) + 7 is that antihole.

They proved that Conjecture 9 for ℓ implies Conjecture 3 whenever
Δ − k = ℓ − 4 (their Theorem 10), and Conjecture 3 for Δ ≤ k and Δ ≥ 2k − 5
(their Theorem 4); the first open case was (k, Δ) = (7, 8), that is ℓ = 5.

**Theorem.** For every ℓ ≥ 3, the odd antihole C̄_{2ℓ−1} is strongly
ℓ-chromatic-choosable. More precisely, if every list has at least ℓ − 1 colours
and C̄_{2ℓ−1} cannot be coloured from the lists, then all lists are one set of
ℓ − 1 colours.

**Corollary.** Conjecture 3 holds for all k and Δ.

The proof (Sections 2 to 5 of the paper) works with complements of disjoint
unions of odd paths. If such a union has s outer vertices (the vertices in even
positions of each path), they form a clique in the complement, so constant
lists of size s − 1 on them cannot be completed. The path theorem (Theorem 4.1)
shows that, with lists of size at least s − 1, this is the only obstruction. Its
proof is an induction driven by Hall's theorem and the Erdős–Rubin–Taylor
theorem on complete multipartite graphs with parts of size at most two, with the
extremal case of a single path with 2k colours settled by a separate lemma on
minimal tight sets (Lemma 3.1). The cycle theorem (Theorem 5.2) then follows:
if two consecutive vertices of the cycle share a colour c, the path theorem
applied to the rest of the cycle with c removed carries c and the lists around
the cycle in steps of two. Section 6 gives the deduction of Conjecture 3, which
is the argument of Fiujlaali and McDonald.

For ℓ ≥ 4 the antihole is not edge-critical (removing the edge between v_0 and
v_3 leaves the chromatic number at ℓ), so it is not strongly critical in the
sense of Stiebitz, Tuza and Voigt: the theorem gives an infinite family of
strongly chromatic-choosable graphs that are not strongly critical.

## What is checked by Lean

The Lean 4 project in `lean/` (Lean v4.34.1, Mathlib v4.34.1) proves the
theorem, with no axioms beyond `propext`, `Classical.choice` and `Quot.sound`
and with no `sorry`, `native_decide` or `bv_decide`:

```lean
def oddAntihole (m : ℕ) : SimpleGraph (Fin (2 * m + 1)) :=
  (SimpleGraph.cycleGraph (2 * m + 1))ᶜ

def ListColorable {V : Type*} (G : SimpleGraph V) {β : Type*} (L : V → Finset β) : Prop :=
  ∃ f : V → β, (∀ v, f v ∈ L v) ∧ ∀ u v, G.Adj u v → f u ≠ f v

def StronglyChromaticChoosable {V : Type*} (G : SimpleGraph V) (ℓ : ℕ) : Prop :=
  G.chromaticNumber = ℓ ∧
    ∀ (β : Type u) [DecidableEq β] (L : V → Finset β), (∀ v, (L v).card = ℓ - 1) →
      ¬ ListColorable G L → ∀ u v, L u = L v

theorem odd_antihole_strongly_chromatic_choosable (ℓ : ℕ) (hℓ : 3 ≤ ℓ) :
    StronglyChromaticChoosable.{u} (oddAntihole (ℓ - 1)) ℓ
```

All the lemmas of Sections 2 to 5 of the paper are formalized: Hall's theorem
in the form used (`hall_sdr`), the Erdős–Rubin–Taylor lemma (`ert`), the key
lemma on a single path (`star`, with `cross`, `side` and `walk` for its steps),
the path theorem (`gpath`), the cycle theorem (`cycle_main`) and the chromatic
number (`antihole_chromaticNumber`). The deduction of Conjecture 3 (Section 6
of the paper) is not formalized.

## Contents

| Path | Contents |
|---|---|
| `preprintOddAntiholeConjecture/` | the paper as a PDF, the only file in the folder |
| `paper/` | LaTeX source (`main.tex`, `amsart`), the figures as PNG and the compiled `main.pdf` |
| `figures/` | TikZ sources of the four schematic figures and `make_figures.sh`, which writes them to `paper/figures/` |
| `lean/OddAntihole/Basic.lean` | colourings of complements, Hall's theorem, the Erdős–Rubin–Taylor lemma |
| `lean/OddAntihole/Paths.lean` | odd linear forests, deficiency, the end-pair step |
| `lean/OddAntihole/KeyLemma.lean` | the key lemma on a single path (minimal tight sets) |
| `lean/OddAntihole/PathTheorem.lean` | the path theorem |
| `lean/OddAntihole/Cycle.lean` | the cycle theorem |
| `lean/OddAntihole/Main.lean` | the odd antihole, its chromatic number and the main theorem |
| `lean/Axioms.lean` | prints the axioms of the main theorem |
| `checks/` | independent checks in Python, Julia, C and C++: every assignment of lists of size ℓ − 1 for ℓ = 3 and (in C, with the argument 21) ℓ = 4, up to renaming the colours, and random assignments for ℓ = 5 to 8 |
| `results/c_complete_l4.txt` | output of the complete C check: 7,897,749,769 assignments at ℓ = 4, no failures |
| `scripts/run_all.sh` | builds the Lean project, checks the axioms and runs the four checks |
| `scripts/build_paper.sh` | builds the files in `dist/`, the preprint folder and the master zip |
| `journal/JOURNAL.md` | target journal (Journal of Graph Theory), format rules and AI policy |
| `AI_PROVENANCE_OddAntiholeConjecture.md` | what the AI tool did and what the authors checked |
| `dist/` | `OddAntiholeConjecture_final2.pdf`, the LaTeX source zip `_final2-tex.zip` (with the figures as PNG) and the arXiv tarball `_final2-arxiv.tar.gz` |
| `MasterOddAntiholeConjecture_masterzipfinal2.zip` | every file of the repository with `dist/` and the preprint folder |
| `.github/workflows/` | `verify.yml` (Lean, the four checks and the paper on every pull request) and `release.yml` (runs the checks and publishes a release) |

## Running the checks

```sh
bash scripts/run_all.sh                       # Lean and the four checks
SKIP_LEAN=1 bash scripts/run_all.sh           # the four checks only
SKIP_LEAN=1 CHECKS=c FULL_C=1 bash scripts/run_all.sh   # every assignment at ℓ = 4 (about fifteen minutes)
cd lean && lake exe cache get && lake build   # Lean only; prints the axioms of the main theorem
```

Tools: elan (the toolchain is pinned in `lean/lean-toolchain`), Python 3,
Julia, a C compiler, a C++20 compiler, and pdflatex for the paper.

## License

MIT (see `LICENSE`).

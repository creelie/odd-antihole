**Every odd antihole is strongly chromatic-choosable**, by Deep Bhattacharjee (corresponding author) and Ushashi Bhattacharya.

A. Fiujlaali and J. McDonald ([arXiv:2610.14241](https://arxiv.org/abs/2610.14241), Conjecture 9) conjectured that for every ℓ ≥ 3 the odd antihole C̄_{2ℓ−1} is strongly ℓ-chromatic-choosable. They showed that this implies their Conjecture 3 on odd antiholes in odd-hole-free critical graphs (their Theorem 10). The paper proves Conjecture 9 for every ℓ, and with it Conjecture 3.

**Theorem.** For every ℓ ≥ 3, if every list has at least ℓ − 1 colours and C̄_{2ℓ−1} cannot be coloured from the lists, then all lists are one set of ℓ − 1 colours; and χ(C̄_{2ℓ−1}) = ℓ.

**Corollary.** An odd-hole-free k-critical graph of maximum degree Δ that contains an odd antihole of length 2(Δ − k) + 7 is that antihole.

| Step | Content |
|---|---|
| Lemmas 2.1, 2.2 | Hall's theorem for complements; the Erdős–Rubin–Taylor lemma for parts of size at most two |
| Lemma 3.1 | a single path with 2k colours in all, Hall on proper subsets: consecutive lists are disjoint |
| Theorem 4.1 | odd linear forests with s outer vertices and lists of size at least s − 1: the complement fails to be colourable only when the outer lists are one set of s − 1 colours |
| Proposition 5.1, Theorem 5.2 | χ(C̄_{2m+1}) = m + 1; odd cycles: a non-colourable assignment has all lists equal |
| Section 6 | the deduction of Conjecture 3 (the argument of Fiujlaali and McDonald) |

Lean 4 with Mathlib proves the theorem (`odd_antihole_strongly_chromatic_choosable`) and every lemma of Sections 2 to 5; it depends only on the axioms propext, Classical.choice and Quot.sound, with no `sorry`, `native_decide` or `bv_decide`. Section 6 is proved by hand. Independent checks in C, C++, Julia and Python; the C check examines every assignment of lists of size ℓ − 1, up to renaming the colours, for ℓ = 3 (4,900) and ℓ = 4 (7,897,749,769), and finds no exception.

Version 1.1.0 is the journal version for Journal of Graph Theory: it cites this release instead of a DOI and leaves out the footnotes unrelated to the proof. The paper is also in `paper/paper1/` and its LaTeX source zip in `paper/paper2/`.

Files:
- `OddAntiholeConjecture_final2.pdf`: the paper
- `OddAntiholeConjecture_final2-tex.zip`: LaTeX source (`main.tex`, figures as PNG)
- `OddAntiholeConjecture_final2-arxiv.tar.gz`: the same source, ready for arXiv

The repository also holds `preprintOddAntiholeConjecture/OddAntiholeConjecture.pdf` and `MasterOddAntiholeConjecture_masterzipfinal2.zip`, which holds every file of the repository. Run `scripts/run_all.sh` to repeat the checks and `scripts/build_paper.sh` to rebuild the files above.

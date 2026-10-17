# AI provenance: Every odd antihole is strongly chromatic-choosable

Authors: Deep Bhattacharjee (corresponding author, ORCID 0000-0003-0466-750X;
formerly EGSPL, Bhubaneswar, Odisha 751030, India, and formerly University of
Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal,
India) and Ushashi Bhattacharya (ORCID 0009-0002-2254-3914; formerly National
Taiwan University, Taipei 106319, Taiwan).

- Paper: https://github.com/creelie/odd-antihole/blob/main/preprintOddAntiholeConjecture/OddAntiholeConjecture.pdf
- Lean formalisation and code: Zenodo, release v1.0.0, https://doi.org/10.5281/zenodo.23393861 (all versions: https://doi.org/10.5281/zenodo.23393860)
- Repository: https://github.com/creelie/odd-antihole

## Result

Conjecture 9 of A. Fiujlaali and J. McDonald (arXiv:2610.14241) states that for
every ℓ ≥ 3 the odd antihole C̄_{2ℓ−1} is strongly ℓ-chromatic-choosable: the
only assignments of lists of size ℓ − 1 from which it cannot be coloured give
every vertex the same list. The case ℓ = 3 is classical; the consequence of
the case ℓ = 4 for Conjecture 3 (the case Δ = k) was known, and ℓ = 5 was the
first case with new consequences.
The paper proves the conjecture for every ℓ. With Theorem 10 of Fiujlaali and
McDonald it proves their Conjecture 3: an odd-hole-free k-critical graph of
maximum degree Δ containing an odd antihole of length 2(Δ − k) + 7 is that
antihole.

## Who did what

Deep Bhattacharjee chose the problem, directed the work, set the format and
the target journal, and ran the computations. Claude (Anthropic), used through
Claude Code under his direction, produced the following:

- the proofs of the lemmas and theorems of Sections 2 to 5;
- the Lean 4 formalisation;
- the checking programs in C, C++, Python and Julia;
- the figures;
- the LaTeX text of the paper, its footnotes and its reference list (every
  reference, the three self-citations included, was checked against the
  publisher's or Crossref's record);
- this file and the submission notes.

No other AI system took part. Section 6 reproduces the argument of Fiujlaali
and McDonald (their Theorem 10) and credits it to them.

## How the result is checked

- **Lean 4.34.1 with Mathlib.** The main theorem
  `odd_antihole_strongly_chromatic_choosable` states that for every ℓ ≥ 3 the
  complement of the cycle graph on 2ℓ − 1 vertices has chromatic number ℓ and
  that every assignment of (ℓ − 1)-element lists, with colours from any type,
  from which it cannot be coloured is constant. It depends only on the standard
  axioms propext, Classical.choice and Quot.sound. There is no `sorry`,
  `admit`, `native_decide`, `bv_decide` or added axiom.
- **Independent programs.** Programs in C, C++, Python and Julia decide list
  colourability of the antihole by running through the matchings of the cycle.
  The C program examined every assignment of lists of size ℓ − 1, up to
  renaming the colours, for ℓ = 3 (4,900 assignments) and ℓ = 4
  (7,897,749,769 assignments): the constant assignment is the only one from
  which the antihole cannot be coloured. All four programs also check random
  assignments for ℓ up to 8.
- **Release workflow.** It builds the Lean proof, checks its axioms and runs
  the programs before publishing.

## What is not claimed

The deduction of Conjecture 3 in Section 6 is proved by hand and is not
formalised in Lean. The authors checked on 15 October 2026, and again on
17 October 2026, that the conjecture appears as open in version 1 of the
preprint of Fiujlaali and McDonald (9 October 2026), and found no other proof
on arXiv, on GitHub or on the web. No statement of the paper rests on a
floating-point computation, and nothing beyond Conjectures 9 and 3 of
Fiujlaali and McDonald is claimed.

# Hexagon submission fields

Title: Every odd antihole is strongly chromatic-choosable

Abstract: We prove the complete Fiujlaali-McDonald conjecture on odd antiholes unconditionally: for every l >= 3 the only assignments of (l-1)-element lists from which the odd antihole on 2l-1 vertices cannot be coloured are the constant ones. Consequently, an odd-hole-free k-critical graph of maximum degree D containing an odd antihole of length 2(D-k)+7 is that antihole.

Primary subject: math.CO (Combinatorics)
Cross-list subjects: none
Tags: list colouring, odd antihole, chromatic-choosability, critical graph, odd hole
MSC2020: 05C15 Coloring of graphs and hypergraphs; 05C17 Perfect graphs; 05C38 Paths and cycles; 68V15 Theorem proving (automated and interactive theorem provers, deduction, resolution, etc.)

Contributor 1 (submitting): Deep Bhattacharjee; ORCID 0000-0003-0466-750X; affiliation: Formerly, Electro-Gravitational Space Propulsion Laboratory (EGSPL), Bhubaneswar, Odisha 751030, India; formerly, University of Calcutta, Senate House, 87/1 College Street, Kolkata 700073, West Bengal, India; itsdeep@live.com (second address d.bhattacharjee@erl-forschung.de)
Contributor 2: Ushashi Bhattacharya; ORCID 0009-0002-2254-3914; affiliation: Formerly, National Taiwan University, Taipei 106319, Taiwan; rai.bhattacharya.in@gmail.com

Text of the contribution: A mix of human-written and AI-generated.
Human understanding: "All parts" only after both authors have read every proof; otherwise "Some parts, but not all".

Provenance statement: The proofs, the text, the figures, the Lean 4 formalization and the C, C++, Python, Julia and shell programs were carried out by Deep Bhattacharjee with the help of AI assistance (Claude, Anthropic) in the Claude Code environment. The paper proves Conjecture 9 of A. Fiujlaali and J. McDonald (arXiv:2610.14241): for every l >= 3 the odd antihole on 2l-1 vertices is strongly l-chromatic-choosable; with their Theorem 10 this proves their Conjecture 3. The proof works with complements of disjoint unions of odd paths, by an induction driven by Hall's theorem and the Erdos-Rubin-Taylor theorem, with the extremal case settled by a lemma on minimal tight sets, and then closes the cycle. The main theorem is proved in Lean 4 with Mathlib (odd_antihole_strongly_chromatic_choosable, with every lemma of Sections 2 to 5), depending only on the axioms propext, Classical.choice and Quot.sound, with no sorry, native_decide or added axiom; programs in C, C++, Python and Julia check list colourability independently, and the C program examined every assignment up to renaming the colours for l = 3 and l = 4. No statement rests on a floating-point computation. The deduction of Conjecture 3 (Section 6) follows Fiujlaali and McDonald, is proved by hand and is not formalized. Both authors approved the final version.

Tools used: Anthropic - Claude (Claude Code); Lean community - Lean 4 (v4.34.1) with Mathlib; C; C++; Python; Julia; shell.
arXiv identifier: none (not posted on arXiv).
Formalization: https://github.com/creelie/odd-antihole/blob/main/lean/OddAntihole.lean (archived at Zenodo, release v1.0.0: https://doi.org/10.5281/zenodo.23393861)

Source files or ZIP: OddAntiholeConjecture_final2-tex.zip (the folder OddAntiholeConjecture_final2-tex/ with main.tex and figures/ as PNG; seven entries; compiles with latexmk -pdf main.tex, no BibTeX pass, all fonts embedded). Do not upload the master zip or the Lean files here.
AI provenance files: AI_PROVENANCE_OddAntiholeConjecture.md
License: CC BY 4.0

Data availability (in the paper): LaTeX source, the Lean 4 formalization and the programs archived at Zenodo under doi:10.5281/zenodo.23393861 (release v1.0.0; all versions 10.5281/zenodo.23393860); repository https://github.com/creelie/odd-antihole; the folder preprintOddAntiholeConjecture holds the PDF only.
AI disclosure (in the paper, Data and code availability): Deep Bhattacharjee carried out the computations and the Lean, Julia, C, C++, Python and shell verifications, and the proofs and the text were drafted, with AI assistance (Claude, Anthropic); both authors approved the final version. No separate AI declaration.
Funding: none. Competing interests: none.
Device folder: D:\Hexagon\11 OddAntiholeConjecture.

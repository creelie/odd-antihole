Deep Bhattacharjee and Ushashi Bhattacharya, *Every odd antihole is strongly chromatic-choosable*. Final revision, single column, 11 pages.

The paper proves Conjecture 9 of A. Fiujlaali and J. McDonald, *Restricting odd antiholes in
critical graphs via list coloring* (arXiv:2610.14241): for every l >= 3 the odd antihole on
2l - 1 vertices is strongly l-chromatic-choosable, so its chromatic number is l and every
assignment of lists of size l - 1 from which it cannot be coloured gives all vertices the same
list. It deduces their Conjecture 3: an odd-hole-free k-critical graph of maximum degree D that
contains an odd antihole with 2(D - k) + 7 vertices is that antihole. Every statement is proved
by hand. A Lean 4 proof of the main theorem and programs in C, C++, Python and Julia that check
it on the smallest antiholes are in the repository; this release builds the Lean proof and runs
the C and C++ checks before publishing. No statement of the paper rests on them.

The results were first made public on 15 October 2026 as release v1.0.0 of this repository; an
earlier and incomplete version of the paper appeared on Hexagon as hexagon:2610.00319.

Files: the paper (`OddAntihole_final2.pdf`), its LaTeX source with the figures
(`OddAntihole_final2-tex.zip`) and the arXiv tarball (`OddAntihole_final2-arxiv.tar.gz`).

Contact: d.bhattacharjee@erl-forschung.de, itsdeep@live.com; for this repository egspl@proton.me.

# Target journal: Journal of Graph Theory

| Item | Details |
|---|---|
| Journal | Journal of Graph Theory (JGT) |
| Publisher | Wiley |
| ISSN | 0364-9024 (print), 1097-0118 (electronic) |
| Author guidelines | https://onlinelibrary.wiley.com/page/journal/10970118/homepage/forauthors.html |
| Submission | through the Wiley Authors submission portal linked from the author guidelines; status under "My Submissions" at submission.wiley.com |
| Preprints | the guidelines allow submission of manuscripts posted on a non-commercial preprint server |
| Class file | the paper uses plain `amsart`; Wiley typesets accepted papers itself |

## Scope fit

JGT publishes research in graph theory. The paper proves Conjecture 9 of
A. Fiujlaali and J. McDonald, *Restricting odd antiholes in critical graphs via
list coloring*, arXiv:2610.14241 (2026): every odd antihole C̄_{2ℓ−1} is
strongly ℓ-chromatic-choosable. With their Theorem 10 this proves their
Conjecture 3 on odd antiholes in odd-hole-free critical graphs. Related work in
the journal: J. A. Noel, B. A. Reed and H. Wu, *A proof of a conjecture of
Ohba*, JGT 79 (2015); K. Ohba, *On chromatic-choosable graphs*, JGT 40 (2002);
A. Bernshteyn, H. Kaul, J. A. Mudrock and G. Sharma, *On strongly and robustly
critical graphs*, JGT 112 (2026).

MSC 2020: primary 05C15; secondary 05C17, 05C38.

## Length and format

- 11 pages in `amsart`, with four schematic figures; built with no overfull or
  underfull boxes and no undefined references.
- A two-sentence abstract; MSC codes, keywords and the corresponding author in
  the first-page footnotes, as `amsart` places them.
- Two authors: Deep Bhattacharjee (corresponding author) and Ushashi
  Bhattacharya, with addresses, e-mail addresses and ORCID iDs.
- The source is a single file `main.tex` with the references in the source
  (`thebibliography`), so no `.bib` or `.bbl` file is needed.
  `dist/OddAntiholeConjecture_final2-tex.zip` (7 entries) and the arXiv
  tarball contain this file and the figures as PNG.
- Declarations at the end: "Acknowledgements" (use of AI), "Competing
  interests: None", "Funding: None" and "Data availability" (who computed
  what, the Zenodo DOI of the Lean formalization and the link to the PDF in
  `preprintOddAntiholeConjecture/`).
- Wiley's pages returned HTTP 403 to the session that prepared this file, so
  the details above come from search results quoting those pages; read the
  author guidelines once more before submitting.

## Policy on AI assistance

- Wiley's guidance on generative AI in publishing does not allow an AI tool to
  be an author, since it cannot take responsibility for the work, and asks
  authors who use such tools to disclose the use in the manuscript (in the
  methods or acknowledgements); the authors remain responsible for the content.
- The paper's "Acknowledgements" name Claude (Anthropic), used through Claude
  Code, and say how it was used; "Data availability" repeats it, and
  `AI_PROVENANCE_OddAntiholeConjecture.md` gives the details. If the submission
  form has a field for AI provenance, upload that file.
- Every lemma of Sections 2 to 5 and the main theorem are checked by the Lean 4
  kernel (Section 7 of the paper); the deduction of Conjecture 3 in Section 6
  is proved by hand and follows Fiujlaali and McDonald.

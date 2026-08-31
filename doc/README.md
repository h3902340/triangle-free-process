# The proofs, typeset

`R3k-proofs.pdf` — a 26-page guided tour of the proofs behind
*Improving R(3,k) in just two bites*, written for a non-specialist:
everything from the definition of a graph up to the paper's Theorem 1.2,
with the mathematics typeset properly.

Sections 1-6 are elementary and self-contained. Sections 7-8 set up the
exchange rate between a construction and a Ramsey constant. Section 9 proves Shearer's theorem in full and states the
Davies-Jenssen-Perkins-Roberts conjectures. Sections 10-15 are the paper. Section 16 is the intuition on one page — the takeaway for
the talk. Section 17 says exactly what is proved in full, what is only
stated, and which framing is mine rather than the authors'.

## Rebuilding

    cd doc && npm install katex playwright-core
    node build.js          # writes R3k-proofs.pdf

`build.js` renders `content.md` (markdown with LaTeX in `$...$`) through
KaTeX and prints it with headless Chromium. No TeX installation required.

# simplex-fv

Formal-verification notes and reference material for the **Simplex** consensus
protocol.

## Source

Benjamin Y. Chan, Rafael Pass —
*Simplex Consensus: A Simple and Fast Consensus Protocol*

- IACR ePrint: <https://eprint.iacr.org/2023/463> (version dated 2023-06-01)
- Published at Theory of Cryptography Conference (TCC) 2023
- Intro site: <https://simplex.blog/>

Victor Shoup's *Sing a Song of Simplex* ([ePrint 2023/1916](https://eprint.iacr.org/2023/1916),
DISC 2024) is a related latency optimization of the same protocol and is
**out of scope** for these notes.

> The source PDF is **not** committed to this repository. Download it from the
> link above and place it at `2023-463.pdf` if you want the local copy that the
> notes reference (SHA-256
> `d832a015b91d208f53384826ca080c7e8288b58a0cd71da208abd2030b82da84`).

## Contents

- `notes/paper-statements.md` — every numbered Theorem and Lemma from the paper,
  each with its proof as it appears in §3, plus a glossary of recurring notation
  and data structures. The paper numbers items as `<section>.<index>`
  (Theorem 2.1, 3.1–3.4; Lemma 3.1–3.7). It defines **no** numbered Definitions,
  Propositions, or Corollaries — the model lives in unnumbered §2 prose.
- `notes/_segments/` — the same statements split into one file per item
  (`theorem_*`, `lemma_*`, named by the paper's `section.index` label), each
  containing the statement text and its proof with source line references.

The protocol pseudocode (the §2.1 player steps), Figures 1–2, the §2.2 proof
outline, and the §3.4 communication-complexity discussion beyond Lemma 3.7 are
intentionally omitted — they are protocol description and commentary rather than
statements to formalize.

## Goal

Build toward a machine-checked formalization of the Simplex consistency
(safety) and liveness results, using these extracted statements as the
specification target. The Lean 4 approach is recorded in
[`docs/formalization-strategy.md`](docs/formalization-strategy.md).
</content>
</invoke>

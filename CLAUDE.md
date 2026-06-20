# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this repository is

A formal-verification project for the **Simplex** consensus protocol (Chan & Pass,
*Simplex Consensus: A Simple and Fast Consensus Protocol*, TCC 2023 — IACR ePrint
2023/463). The end goal is a machine-checked Lean 4 formalization of Simplex's
consistency (safety) and liveness results.

**Current state: Lean scaffold up, first statement proved.** The Lake/Mathlib
project is bootstrapped (`lakefile.toml`, `lean-toolchain`, `Simplex/*.lean`) and
**Lemma 3.1 (signature unforgeability)** is formalized — see Issue #1. The
extracted paper statements (the specification target) and the formalization
strategy remain the reference material; the remaining 11 statements (Issues #2–14)
are not yet formalized.

## Layout

- The per-statement paper notes — every numbered Theorem and Lemma (Theorem 2.1,
  3.1–3.4; Lemma 3.1–3.7 — **12 statements**, no numbered
  Definitions/Propositions/Corollaries), each with its proof and a notation
  glossary, plus a one-file-per-statement segment split — are the specification
  target. They are **maintained separately, outside this repository**, and are no
  longer version-controlled here.
- `README.md` (the "Formalization strategy" section) — the authoritative design
  document: proof discipline, the five formalization barriers and the decision for
  each, the dependency DAG (rendered as a Mermaid graph), and the planned Lean
  module layout. **Read this before writing any Lean.**
- `2023-463.pdf` — the source paper. **Not committed** (gitignored, copyrighted);
  download from ePrint and place at this path if you want the local copy the
  notes line-reference.

## Commands

The project uses **Lake + Mathlib** (both pinned to `v4.29.1` — keep
`lean-toolchain` equal to the Mathlib tag's toolchain or the cache won't match):

```bash
lake exe cache get        # fetch prebuilt Mathlib (after a fresh clone / toolchain change)
lake build                # build all modules
lake build Simplex.Safety # build a single module
lake update               # re-resolve deps + rewrite lake-manifest.json (only when bumping)
```

Axiom check — verify a theorem rests only on intended axioms and **no `sorryAx`**:

```bash
printf 'import Simplex.Safety\n#print axioms Simplex.lemma_3_1\n' | lake env lean --stdin
```

Reference project layout to mirror: [`Koukyosyumei/PoL`](https://github.com/Koukyosyumei/PoL)
(Lake, Mathlib, `Consensus/` module structure).

## Architecture (the formalization plan)

### Proof discipline — non-negotiable

- **Never use `sorry`.** It taints every downstream proof.
- **`axiom`** is reserved for genuinely idealized facts: cryptography
  (`SignatureUnforgeable`, `CollisionResistant`) and — temporarily — the
  leader-randomness probability bounds. Each declared axiom gets a source comment
  and the `needs-axiom` label.
- **Hypothesis threading** is the default for everything deterministic: take the
  crypto/randomness facts as explicit premises so the theorem is fully proved as
  "premise ⇒ conclusion" with no local axiom.

### Safety, liveness, and complexity — one DAG (no cycles)

The 12 statements split by the paper's three guarantees (matching the GitHub
labels `safety` / `liveness` / `complexity`):

- **Safety (consistency):** Lemma 3.1–3.3, Theorem 3.1. The entire safety argument
  is one quorum-intersection lemma applied twice. Prove quorum intersection
  directly over `Finset` cardinalities, parameterized by `n`, `f`, `3*f < n` —
  **do not hardcode `n = 3f+1`**; use the `⌈2n/3⌉` threshold (`(2*n+2)/3` in `Nat`)
  and handle integer rounding explicitly.
- **Liveness & confirmation time:** Lemma 3.4–3.6, Theorem 3.2–3.4. Timing
  inequalities over `GST`, `δ`, `∆` (with `δ < ∆`), plus elementary independent-
  coin bounds on leader rotation — **no Chernoff machinery.**
- **Communication complexity:** Lemma 3.7 (≤ 4 multicasts/iteration/honest
  process), independent of the safety and liveness lines.
- **Theorem 2.1** is the capstone summary; it closes as the conjunction of the
  safety, liveness, and complexity conclusions.

The full dependency graph lives in the README "Formalization strategy" section
(rendered as Mermaid). Statements can be closed in topological order.

### Phase 1 vs Phase 2

A statement issue closes at **Phase 1** once its deterministic core is proved and
any probability fact is in place as an axiom/premise. The measure-theoretic proofs
of the coin bounds (Theorems 3.3/3.4) are **Phase 2** follow-ups (`phase2` label)
that never block dependents.

### Lean modules

The layout mirrors `Koukyosyumei/PoL` and `goldfish-fv`: foundational modules at
the root of `Simplex/`, and each result category as a directory of one-file-per-
statement modules (`Lemma3_2.lean`, `Theorem3_1.lean`, …) re-exported by a
same-named barrel module. Root `Simplex.lean` imports the foundation, the three
category barrels, and `Capstone`.

Foundation:

- `Simplex/Basic.lean` — core types: `Process`, opaque `Message`/`Block`/`Log`,
  the `⌈2n/3⌉` `quorumThreshold`, the abstract `Execution` structure, opaque
  `ValidExecution`, and the `SignatureUnforgeable` predicate.
- `Simplex/Protocol.lean` — the abstract `ChainView` interface (block/log
  structure, `Notarized`/`Finalized`, the honest signing rules, `CollisionResistant`,
  and the structural `Laws` bundle). Protocol mechanics are **modeled abstractly,
  not implemented operationally**.
- `Simplex/Axioms.lean` — declared crypto axioms (`signature_unforgeable`,
  `collision_resistant`) and the leader-randomness axioms. **An unguarded axiom
  over the abstract `Execution` would prove `False`** (its fields are
  unconstrained) — each crypto axiom is guarded by `ValidExecution`.

Result categories (`Simplex/<Category>.lean` barrel + `Simplex/<Category>/`):

- `Simplex/Safety/` — `QuorumIntersection`, `Lemma3_1`–`Lemma3_3`, `Theorem3_1`.
- `Simplex/Liveness/` — `Basic` (the `TimingView` model), `Lemma3_4`–`Lemma3_6`
  (with the `confirm_by` bridge in `Lemma3_5`), `Theorem3_2`–`Theorem3_4`.
- `Simplex/Complexity/` — `Lemma3_7`.

Capstone:

- `Simplex/Capstone.lean` — `theorem_2_1`, the conjunction of the safety,
  liveness, and complexity conclusions.

## Conventions

- **Each of the 12 statements maps to a GitHub issue**, labeled by result category
  (`safety`/`liveness`/`complexity`), `type:lemma`/`type:theorem`, and
  `needs-axiom`/`phase2` where relevant (issues #1–14; #13–14 are the Phase 2
  axiom-discharge tasks). The README "Formalization strategy" section is the
  cross-cutting reference those issues link back to.
- The notes are **verbatim PyMuPDF extractions** from a two-column PDF. A known
  artifact: subscripts/superscripts and primed indices line-break at column
  boundaries (e.g. `b'_{h'}` appears as `b′` then `h′`). Read split tokens as one
  symbol — **do not "fix" the extraction**; `(line N)` references point at the raw
  PyMuPDF line numbering.
- Victor Shoup's *Sing a Song of Simplex* (ePrint 2023/1916) is a related but
  **out-of-scope** optimization.

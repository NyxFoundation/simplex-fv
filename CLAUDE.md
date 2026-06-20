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
- `docs/formalization-strategy.md` — the authoritative design document: proof
  discipline, the five formalization barriers and the decision for each, the
  dependency DAG, and the planned Lean module layout. **Read this before writing
  any Lean.**
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

The full adjacency list lives in `docs/formalization-strategy.md`. Statements can
be closed in topological order.

### Phase 1 vs Phase 2

A statement issue closes at **Phase 1** once its deterministic core is proved and
any probability fact is in place as an axiom/premise. The measure-theoretic proofs
of the coin bounds (Theorems 3.3/3.4) are **Phase 2** follow-ups (`phase2` label)
that never block dependents.

### Lean modules

Existing (root `Simplex.lean` imports all of these):

- `Simplex/Basic.lean` — currently a **minimal** abstract model seeded for
  Lemma 3.1: `Process`, opaque `Message`, an abstract `Execution` structure,
  opaque `ValidExecution`, and the `SignatureUnforgeable` predicate. To be
  extended (later issues) with the full core types: `Block (h, parent, txs)`,
  genesis `b_0`, dummy `⊥_h`, prefix order `⪯`, `linearize`, the `n`/`f`
  parameters, notarization/finalization as `≥ ⌈2n/3⌉`-signature sets, timing params.
- `Simplex/Axioms.lean` — declared crypto axioms. Has `signature_unforgeable`
  (guarded by `ValidExecution`); to gain `CollisionResistant` and the
  leader-randomness facts. **An unguarded axiom over the abstract `Execution`
  would prove `False`** (its fields are unconstrained) — guard each crypto axiom
  by `ValidExecution`.
- `Simplex/Safety.lean` — safety (consistency) statements; currently `lemma_3_1`.

Planned (not yet created):

- `Simplex/Protocol.lean` — abstract interface (structure/typeclass of hypotheses)
  for the iteration loop, voting/timer rules, the leader oracle `L_h`, and
  message-delivery assumptions. Protocol steps are **modeled abstractly, not
  implemented operationally** (an executable state machine can replace the
  interface later without changing theorem statements).

## Conventions

- **Each of the 12 statements maps to a GitHub issue**, labeled by result category
  (`safety`/`liveness`/`complexity`), `type:lemma`/`type:theorem`, and
  `needs-axiom`/`phase2` where relevant (issues #1–14; #13–14 are the Phase 2
  axiom-discharge tasks). The strategy doc is the cross-cutting reference those
  issues link back to.
- The notes are **verbatim PyMuPDF extractions** from a two-column PDF. A known
  artifact: subscripts/superscripts and primed indices line-break at column
  boundaries (e.g. `b'_{h'}` appears as `b′` then `h′`). Read split tokens as one
  symbol — **do not "fix" the extraction**; `(line N)` references point at the raw
  PyMuPDF line numbering.
- Victor Shoup's *Sing a Song of Simplex* (ePrint 2023/1916) is a related but
  **out-of-scope** optimization.

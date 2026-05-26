---
title: Simplex Lean 4 Formalization Strategy
last_updated: 2026-05-26
tags:
  - lean4
  - formal-verification
  - simplex
  - consensus
---

# Simplex Lean 4 Formalization Strategy

This document records *how* the Simplex consensus protocol (IACR ePrint
2023/463) is being formalized in Lean 4, the technical barriers we hit, and the
explicit policy decision for each. The 12 numbered statements of the paper
(Theorem 2.1, 3.1–3.4; Lemma 3.1–3.7) are each tracked by a GitHub issue; this
file is the cross-cutting reference those issues link back to.

The statement texts and proofs live in [`notes/paper-statements.md`](../notes/paper-statements.md)
and the per-statement segments in [`notes/_segments/`](../notes/_segments/).

Simplex is deliberately simple: a partially-synchronous BFT protocol whose
entire safety argument is one quorum-intersection lemma applied twice, and whose
liveness argument is a short timing analysis plus a coin-flipping bound on leader
rotation. There is **no VRF lottery, no Chernoff concentration, and no
ebb-and-flow / sleepy model** — so the probabilistic surface is far smaller than
in protocols like Goldfish.

## Proof discipline: `sorry` vs `axiom` vs hypothesis threading

These three are **not** interchangeable. The project uses the latter two and
never the first.

| Mechanism | Meaning | Soundness | Use in this project |
|---|---|---|---|
| `sorry` | Placeholder for an omitted proof; compiles but Lean warns and every downstream proof is tainted. | ✗ Not a proof; technical debt. | **Never.** |
| `axiom` | A proposition *declared* true without proof — a deliberate, explicit assumption. | ✓ Sound relative to the assumption being a genuine external/idealized fact. | For idealized cryptography (signature unforgeability, collision resistance) and for the leader-randomness probability facts (temporarily). |
| Hypothesis threading | The probabilistic / external fact is taken as an explicit *premise* of the theorem. | ✓ The theorem is fully proved: "premise ⇒ conclusion". | Default for all deterministic safety and timing reasoning. |

Concretely, a deterministic theorem takes the cryptographic and randomness facts
as hypotheses and is then proved with **no `sorry` and no local axiom**:

```lean
theorem simplex_consistency
    (huf : SignatureUnforgeable exec)   -- conclusion of Lemma 3.1, threaded in
    (hcr : CollisionResistant H) :
    ∀ {log log'}, Output exec log → Output exec log' → log ⪯ log' ∨ log' ⪯ log := by
  ...  -- fully discharged via the quorum-intersection lemmas (3.2, 3.3)
```

The probabilistic facts ("a forgery occurs only with negligible probability",
"`k = ω(log λ)` consecutive corrupt leaders is negligible", "`E[X] ≤ 1/2`") are
isolated into the relevant statements, declared as `axiom` for now, and proved
later in a dedicated Phase 2 issue.

## Barriers and decisions

### 1. Idealized cryptography (signatures, hashes)

Simplex assumes a bare PKI + unforgeable digital signatures and a publicly known
**collision-resistant hash** `H` (parent-chain linking). Lemma 3.1 is *literally*
"by a direct reduction to the unforgeability of the signature scheme", and
Theorem 3.1's prefix conclusion is closed by collision resistance of `H`.

Game-based cryptographic reductions are research-level work and out of scope.

**Decision.** Axiomatize idealized interfaces: `SignatureUnforgeable` (no honest
process sees a valid `⟨m⟩_i` unless `i` signed `m`) and `CollisionResistant`
(equal hashes ⇒ equal pre-images, on the reachable block space). Declare each as
an `axiom` with a source comment in a central module (label `needs-axiom`). The
deterministic statements take these as hypotheses and are fully proved.

### 2. Random leader election and probabilistic liveness

Leaders are picked by a public hash, `L_h := H*(h) mod n` (random oracle / CRS),
so each iteration's leader is honest with independent probability `(n−f)/n ≥ 2/3`.
Two liveness statements depend on this:

- **Theorem 3.3 (worst-case):** the probability of `k` consecutive corrupt
  leaders is `< (m(λ)−k+1)/2^k`, negligible once `k = ω(log λ)`.
- **Theorem 3.4 (expected):** with `X` the offset to the next honest leader,
  `E[X] ≤ 1/2` (a geometric-tail expectation).

These are elementary independent-coin bounds — **no Chernoff machinery**, unlike
Goldfish.

**Decision.** Model the per-iteration leader as an abstract oracle whose only
exposed property is "honest with independent probability `≥ (n−f)/n`". Thread the
two probability facts above as hypotheses (or small local `axiom`s) into
Theorems 3.3 and 3.4; the deterministic "honest leader ⇒ progress" core
(Lemmas 3.4–3.6) is fully proved. A statement issue closes at **Phase 1** once
the axiom/premise is in place; the measure-theoretic proof of the coin bounds is
a separate **Phase 2** follow-up issue (label `phase2`) and never blocks
dependents.

### 3. Quorum intersection (the safety core)

Both safety lemmas reduce to: among `n` processes with `< n/3` corrupt, two sets
of `≥ 2n/3` signers cannot be "good" for two conflicting messages, because an
honest process signs at most one. This is pure finite combinatorics.

**Decision.** Prove it directly over `Finset` cardinalities, **without baking in
`n = 3f + 1`**. Parameterize by `n`, `f`, and the hypothesis `3 * f < n`, with
the quorum threshold expressed as `⌈2n/3⌉` (handle the integer rounding
explicitly via `Nat`/`ceil`, not by assuming divisibility). The reusable lemma is

```lean
-- any two ⌈2n/3⌉-quorums share an honest process
lemma quorum_intersect_honest
    {n f : ℕ} (hf : 3 * f < n)
    (Q₁ Q₂ : Finset (Fin n)) (honest : Finset (Fin n))
    (h₁ : (2 * n + 2) / 3 ≤ Q₁.card) (h₂ : (2 * n + 2) / 3 ≤ Q₂.card)
    (hc : honestᶜ.card ≤ f) :
    ∃ p ∈ Q₁ ∩ Q₂, p ∈ honest := by ...
```

No axiom; this is the deterministic heart of Lemmas 3.2 and 3.3.

### 4. Protocol mechanics (iterations, timers, notarize/finalize, dummy blocks)

The notes omit the player-step pseudocode, but the statements need the iteration
loop, the `3∆` timer `T_h`, notarization/finalization (`≥ 2n/3` votes), and the
dummy block `⊥_h`.

**Decision (MVP).** Do not implement the steps operationally. Provide the voting,
timer, notarization, and finalization behaviour as an **abstract interface (a
structure / typeclass of hypotheses)** and derive the theorems from it. An
executable state-machine model can replace the interface later without changing
the theorem statements.

### 5. Partial-synchrony timing model

Lemmas 3.4–3.6 and Theorems 3.2–3.3 are timing arguments over `GST`, the actual
delay `δ`, and the timeout parameter `∆` (`δ < ∆`), with claims of the form
"every honest process has entered iteration `h` by time `t + …`".

**Decision.** Model time as `ℝ≥0` (or `ℕ` rounds) with `GST`, `δ`, `∆` as
parameters and the message-delivery / timer rules as abstract hypotheses
(`δ`-bounded delivery after `GST`, timer fires after `3∆`). The timing lemmas are
then ordinary inequality reasoning, fully proved.

## Track structure and dependency graph

Three layers. Track A (safety) is self-contained given the crypto axioms; Track B
(liveness/timing) depends on the timing model and leader randomness; Track C is a
single complexity lemma.

- **Track A — consistency (safety):** Lemma 3.1–3.3, Theorem 3.1. Quorum
  intersection ⇒ no two conflicting blocks notarized ⇒ prefix agreement.
- **Track B — liveness & confirmation time:** Lemma 3.4–3.6, Theorem 3.2–3.4.
  Synchronized iterations + honest/faulty-leader effects ⇒ optimistic `5δ`,
  worst-case `4δ + ω(log λ)·(3∆+δ)`, expected `3.5δ + 1.5∆`.
- **Track C — communication complexity:** Lemma 3.7 (≤ 4 multicasts per
  iteration per honest process). Independent of A and B.
- **Theorem 2.1** is the paper's summary statement; it has no separate proof and
  closes once Tracks A–C close (it is the conjunction of their conclusions).

Dependency adjacency list (`X ← {…}` means X's proof depends on …; `[crypto]`
and `[rand]` are the axioms/premises of Barriers 1 and 2):

```
Thm2.1 ← {Thm3.1, Thm3.2, Thm3.3, Thm3.4, Lem3.7}   (summary; conjunction)

Lem3.1 ← {[crypto: sig-unforgeability]}             (axiom; cryptographic)
Lem3.2 ← {Lem3.1}                                   (quorum intersection)
Lem3.3 ← {Lem3.1}                                   (quorum intersection)
Thm3.1 ← {Lem3.2, Lem3.3, [crypto: collision-res]}  (Consistency)

Lem3.4 ← {}                                          (Synchronized Iterations; timing)
Lem3.5 ← {Lem3.4, Lem3.3}                            (Honest Leaders)
Lem3.6 ← {Lem3.4}                                    (Faulty Leaders)
Thm3.2 ← {Lem3.4, Lem3.5}                            (Optimistic 5δ)
Thm3.3 ← {Lem3.4, Lem3.5, Lem3.6, [rand: k-corrupt-run]}
Thm3.4 ← {Lem3.5, Lem3.6, [rand: E[X] ≤ 1/2]}

Lem3.7 ← {}                                          (message complexity)
```

There is **no cyclic dependency** (contrast Goldfish's healing induction): the
graph is a DAG, so statements can be closed in topological order.

## Non-issue prerequisites (Lean scaffolding)

The following are **not** tracked by per-statement issues; they are prerequisite
scaffolding assumed by every statement issue. They will be introduced together
(separately from the statement issues) and live at these paths:

| Path | Contents |
|---|---|
| `lakefile.toml`, `lean-toolchain` | Lake build config; pin a Lean toolchain and depend on Mathlib. |
| `Simplex/Basic.lean` | Core types: `Block` `(h, parent, txs)`, genesis `b_0`, dummy `⊥_h`, blockchains with the prefix partial order `⪯`, `linearize`, the `n`/`f`/`3*f < n` parameters, notarization/finalization as `≥ ⌈2n/3⌉`-signature sets, and the timing parameters `GST`/`δ`/`∆`. |
| `Simplex/Protocol.lean` | Abstract interface: the iteration loop, voting/timer rules, the leader oracle `L_h`, and message-delivery assumptions as a structure / typeclass of hypotheses (Barriers 4–5). |
| `Simplex/Axioms.lean` | Declared axioms: idealized cryptography — `SignatureUnforgeable`, `CollisionResistant` (Barrier 1) — and the leader-randomness probability facts for Theorems 3.3/3.4 (Barrier 2), each with a source comment. |

Reference pattern for project layout: [`Koukyosyumei/PoL`](https://github.com/Koukyosyumei/PoL)
(Apache-2.0, Lake, `Consensus/` module layout).

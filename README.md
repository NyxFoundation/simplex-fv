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

The per-statement paper notes (every numbered Theorem and Lemma — Theorem 2.1,
3.1–3.4; Lemma 3.1–3.7 — each with its proof, a notation glossary, and
one-file-per-item segments) are **maintained separately, outside this
repository**, and are no longer version-controlled here. The paper defines **no**
numbered Definitions, Propositions, or Corollaries — the model lives in unnumbered
§2 prose.

The protocol pseudocode (the §2.1 player steps), Figures 1–2, the §2.2 proof
outline, and the §3.4 communication-complexity discussion beyond Lemma 3.7 are
intentionally omitted — they are protocol description and commentary rather than
statements to formalize.

## Goal

Build toward a machine-checked formalization of the Simplex consistency
(safety) and liveness results, using the extracted statements as the
specification target. The Lean 4 approach is recorded in the
[Formalization strategy](#formalization-strategy) section below.

## Formalization strategy

This section records *how* the Simplex consensus protocol (IACR ePrint 2023/463)
is being formalized in Lean 4, the technical barriers we hit, and the explicit
policy decision for each. The 12 numbered statements of the paper (Theorem 2.1,
3.1–3.4; Lemma 3.1–3.7) are each tracked by a GitHub issue; this section is the
cross-cutting reference those issues link back to.

Simplex is deliberately simple: a partially-synchronous BFT protocol whose entire
safety argument is one quorum-intersection lemma applied twice, and whose liveness
argument is a short timing analysis plus a coin-flipping bound on leader rotation.
There is **no VRF lottery, no Chernoff concentration, and no ebb-and-flow / sleepy
model** — so the probabilistic surface is far smaller than in protocols like
Goldfish.

### Proof discipline: `sorry` vs `axiom` vs hypothesis threading

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

### Barriers and decisions

#### 1. Idealized cryptography (signatures, hashes)

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

#### 2. Random leader election and probabilistic liveness

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

#### 3. Quorum intersection (the safety core)

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

#### 4. Protocol mechanics (iterations, timers, notarize/finalize, dummy blocks)

The notes omit the player-step pseudocode, but the statements need the iteration
loop, the `3∆` timer `T_h`, notarization/finalization (`≥ 2n/3` votes), and the
dummy block `⊥_h`.

**Decision (MVP).** Do not implement the steps operationally. Provide the voting,
timer, notarization, and finalization behaviour as an **abstract interface (a
structure / typeclass of hypotheses)** and derive the theorems from it. An
executable state-machine model can replace the interface later without changing
the theorem statements.

#### 5. Partial-synchrony timing model

Lemmas 3.4–3.6 and Theorems 3.2–3.3 are timing arguments over `GST`, the actual
delay `δ`, and the timeout parameter `∆` (`δ < ∆`), with claims of the form
"every honest process has entered iteration `h` by time `t + …`".

**Decision.** Model time as `ℝ≥0` (or `ℕ` rounds) with `GST`, `δ`, `∆` as
parameters and the message-delivery / timer rules as abstract hypotheses
(`δ`-bounded delivery after `GST`, timer fires after `3∆`). The timing lemmas are
then ordinary inequality reasoning, fully proved.

### Result categories and dependency graph

Three categories, matching the GitHub labels `safety` / `liveness` / `complexity`.
The safety line is self-contained given the crypto axioms; the liveness line
depends on the timing model and leader randomness; complexity is a single lemma.

- **Safety (consistency):** Lemma 3.1–3.3, Theorem 3.1. Quorum
  intersection ⇒ no two conflicting blocks notarized ⇒ prefix agreement.
- **Liveness & confirmation time:** Lemma 3.4–3.6, Theorem 3.2–3.4.
  Synchronized iterations + honest/faulty-leader effects ⇒ optimistic `5δ`,
  worst-case `4δ + ω(log λ)·(3∆+δ)`, expected `3.5δ + 1.5∆`.
- **Communication complexity:** Lemma 3.7 (≤ 4 multicasts per
  iteration per honest process). Independent of the safety and liveness lines.
- **Theorem 2.1** is the paper's summary statement; it has no separate proof and
  closes once the safety, liveness, and complexity statements close (it is the
  conjunction of their conclusions).

In the graph below, an edge `A --> B` reads "**A's proof depends on B**". The
`[crypto]` and `[rand]` nodes are the axioms / premises of Barriers 1 and 2. The
graph is a **DAG** — there is no cyclic dependency (contrast Goldfish's healing
induction) — so statements can be closed in topological order.

```mermaid
flowchart TD
    %% edge A --> B reads "A's proof depends on B"
    subgraph SAFETY["Safety (consistency)"]
        L31["Lemma 3.1"]
        L32["Lemma 3.2"]
        L33["Lemma 3.3"]
        T31["Theorem 3.1 — Consistency"]
    end

    subgraph LIVENESS["Liveness &amp; confirmation time"]
        L34["Lemma 3.4 — Sync. iterations"]
        L35["Lemma 3.5 — Honest leaders"]
        L36["Lemma 3.6 — Faulty leaders"]
        T32["Theorem 3.2 — Optimistic 5δ"]
        T33["Theorem 3.3 — Worst case"]
        T34["Theorem 3.4 — Expected"]
    end

    subgraph COMPLEXITY["Communication complexity"]
        L37["Lemma 3.7 — ≤ 4 multicasts"]
    end

    subgraph AXIOMS["Axioms / premises — Barriers 1–2"]
        CSIG["[crypto] sig-unforgeability"]
        CCR["[crypto] collision-resistance"]
        RK["[rand] k-corrupt-run"]
        RE["[rand] E[X] ≤ 1/2"]
    end

    T21["Theorem 2.1 — summary (conjunction)"]

    T21 --> T31
    T21 --> T32
    T21 --> T33
    T21 --> T34
    T21 --> L37

    L31 --> CSIG
    L32 --> L31
    L33 --> L31
    T31 --> L32
    T31 --> L33
    T31 --> CCR

    L35 --> L34
    L35 --> L33
    L36 --> L34
    T32 --> L34
    T32 --> L35
    T33 --> L34
    T33 --> L35
    T33 --> L36
    T33 --> RK
    T34 --> L35
    T34 --> L36
    T34 --> RE
```

`Lemma 3.4` and `Lemma 3.7` are leaves (no in-graph dependencies).

### Lean scaffolding (non-issue prerequisites)

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

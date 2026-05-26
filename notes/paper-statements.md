# Simplex Consensus — paper statements and proofs (reference)

> **Source.** Benjamin Y. Chan, Rafael Pass — *Simplex Consensus: A Simple and
> Fast Consensus Protocol.* Theory of Cryptography (TCC) 2023.
> IACR ePrint 2023/463 (version dated 2023-06-01). Intro site:
> <https://simplex.blog/>.
>
> Local PDF: `2023-463.pdf` (26 pp, not committed — see README).
> SHA-256 `d832a015b91d208f53384826ca080c7e8288b58a0cd71da208abd2030b82da84`.
> Text extracted with **PyMuPDF 1.27.1** (MuPDF 1.27.1).
>
> This file lists every numbered statement in the paper, with each proof as it
> appears in §3. The paper numbers statements as `<section>.<index>`: it has
> **5 Theorems (2.1, 3.1–3.4) and 7 Lemmas (3.1–3.7)**.
> **There are no numbered Definitions, Propositions, or Corollaries** — the
> model and data structures are given as unnumbered prose in §2 and summarised
> in the Notation glossary below.
>
> Algorithms / protocol pseudocode (§2.1, the numbered player steps), Figures 1–2
> (event timelines), the §2.2 proof outline, and the §3.4 communication-complexity
> discussion beyond Lemma 3.7 are intentionally omitted — they are protocol
> description and commentary rather than statements to formalize.
>
> PDF-extraction caveat — the text below is preserved verbatim, with one known
> artifact inherited from the two-column PDF: subscripts/superscripts and
> primed/height indices are line-broken at column boundaries, e.g. `b'_{h'}` is
> written across two lines as `b′` then `h′`, and `ch^{id}_r` style
> indices wrap similarly. Read each split token as one symbol. Standalone
> page-number lines interleaved by pagination have been removed; the `(line N)`
> references point at the raw PyMuPDF line numbering.

## Notation

A glossary of the recurring symbols and data structures defined in §2, so each
statement below can be read without flipping back to the paper.

| Symbol | Meaning |
|---|---|
| `n` | Total number of processes (validators), indexed by `[n]`. |
| `f` | Number of Byzantine (statically corrupted) processes; Simplex tolerates `f < n/3`. |
| `∆` | Protocol timeout parameter; the per-iteration timer `T_h` fires after `3∆`. The protocol is parametrised by `∆`, not `δ`. |
| `δ` | Actual message-delivery delay after GST (`δ < ∆`); the execution is `δ`-bounded partially synchronous. |
| `GST` | Global Stabilisation Time — after `GST`, all messages between honest processes are delivered within `δ`. |
| `λ` | Cryptographic security parameter. "w.o.p." / "with overwhelming probability" means except with probability negligible in `λ`. |
| `h` | Iteration (= block height); processes run sequential iterations `h = 1, 2, 3, …` and may be in different iterations at the same time. |
| `L_h` | Leader of iteration `h`, chosen by the random leader-election oracle `L_h := H*(h) mod n` (`H*` a random oracle / CRS-PRF). Honest with probability `(n−f)/n ≥ 2/3`. |
| `b = (h, parent, txs)` | A block: height `h`, parent-chain hash `parent`, and transactions `txs`. |
| `b_0` | The genesis block `(0, ∅, ∅)`. |
| `⊥_h` | The dummy block of height `h`, `(h, ⊥, ⊥)`; inserted when no agreement is reached in iteration `h`. |
| `H(·)` | Publicly known collision-resistant hash; a blockchain links each `b_i` to `H(b_0,…,b_{i−1})`. |
| `⟨m⟩_p` | Message `m` signed by process `p` (tuple `(m, σ)` with `σ` a valid signature under `p`'s key). |
| `⟨vote, h, b⟩_p` | A vote by `p` for block `b` at height `h`. |
| `⟨finalize, h⟩_p` | A finalize vote by `p` for height `h`. |
| `⟨propose, h, b_0,…,b_h, S⟩_p` | A leader proposal: blockchain of height `h` with notarized parent `(b_0,…,b_{h−1}, S)` and `b_h ≠ ⊥_h`. |
| Notarization | A set of `≥ 2n/3` `⟨vote, h, b⟩` signatures from distinct processes; a *notarized block/blockchain* carries one notarization per block. |
| Finalization | A set of `≥ 2n/3` `⟨finalize, h⟩` signatures from distinct processes; a block is *finalized* if notarized **and** accompanied by a finalization for its height. |
| `T_h` | Local timer started on entering iteration `h`, set to fire after `3∆`; on firing, `p` votes `⟨vote, h, ⊥_h⟩`. |
| `linearize(b_0,…,b_h)` | Concatenates the per-block transaction sequences in order into the output ledger. |
| `LOG`, `LOG'` | Output ledgers (sequences of transactions); `LOG ⪯ LOG'` means `LOG` is a prefix of `LOG'`. |
| `B`, `Z`, PPT | The adversary `A`, environment `Z`; both probabilistic polynomial-time. |

Confirmation-time results (Theorems 2.1, 3.2–3.4): optimistic confirmation `5δ`
(optimistic block time `2δ`), worst-case `4δ + ω(log λ)·(3∆+δ)`, expected
view-based liveness `3.5δ + 1.5∆`, with `O(n)` multicast complexity.

## Theorems

### Theorem 2.1 — §2.1 — Partially-synchronous Consensus

**Statement.** (line 440)

```
Theorem 2.1 (Partially-synchronous Consensus). Assuming collision-resistant hash functions,
digital signatures, a PRF, a bare PKI, and a CRS, there is a partially-synchronous blockchain
protocol for f < n/3 static corruptions that has O(n) multicast complexity, optimistic confirmation
time of 5δ, worst-case confirmation time of 4δ+ω(log λ)·(3∆+δ), and expected view-based liveness
of 3.5δ + 1.5∆.
```

**Proof.** (no proof at this location; Theorem 2.1 is the paper's summary statement, established by Theorems 3.1-3.4 in Sec. 3)

### Theorem 3.1 — §3.2 — Consistency

**Statement.** (line 637)

```
Theorem 3.1 (Consistency). Suppose that two sequences of transactions, denote LOG and LOG′,
are both output output in honest view. Then either LOG ⪯LOG′ or LOG′ ⪯LOG (with overwhelming
probability in λ).
```

**Proof.** (line 640)

```
Proof. Immediately, there must be two blockchains denoted b0, b1, . . . , bh and b0, b′
1, . . . , b′
h′, such
that both are finalized in honest view, where LOG ←linearize(b0, b1, . . . , bh) and LOG′ ←linearize(b0, b′
1, . . . , b′
h′).
Without loss of generality, we assume that h ≤h′.
It suffices to show that bh = b′
h and moreover that bh ̸= ⊥h.
In plainer English, the two
chains should contain the same block at height h, and moreover this block is not the dummy block.
Then by collision-resistant property of the hash function H(·), the parent chains are the same
b0, b1, . . . , bh−1 = b0, b′
1, . . . , b′
h−1, and thus LOG ⪯LOG′.
To prove that bh = b′
h, first observe that both b′
h′ and bh are finalized in honest view, and thus
both b′
h′ and bh are notarized in honest view. Because b′
h′ is notarized in honest view, then some
honest process must have voted for it in iteration h′ which implies that b′
h is also notarized in honest
view. By Lemma 3.3, observing that bh is finalized in honest view, it must be that bh ̸= ⊥h, and
likewise b′
h ̸= ⊥h (except with negligible probability in λ). Finally, we apply Lemma 3.2, which
says that since bh and b′
h are both notarized and not the dummy block, it must be that bh = b′
h
(except with negligible probability), concluding the proof.
```

### Theorem 3.2 — §3.3 — Optimistic Confirmation Time

**Statement.** (line 760)

```
Theorem 3.2 (Optimistic Confirmation Time). Simplex has an optimistic confirmation time of
5δ.
```

**Proof.** (line 762)

```
Proof. Suppose that there is a set of transactions txs in the view of every honest player by time
t, where t > GST, where txs is not yet in the output of any honest player. Let h be the highest
iteration that any honest player is in at time t. There are two cases. If Lh has not entered iteration
h yet by time t, then by Lemma 3.4, it will enter iteration h by time t+δ, at which point it proposes
a blockchain that contains txs; applying Lemma 3.5 then completes the proof. In the second case,
by time t, Lh has already started iteration h, and by Lemma 3.5 every honest process will be in
iteration h + 1 by time t + 2δ, and see a finalized block from Lh+1 by t + 5δ.
```

### Theorem 3.3 — §3.3 — Worst-Case Confirmation Time

**Statement.** (line 800)

```
Theorem 3.3 (Worst-Case Confirmation Time). Simplex has worst-case confirmation time of
(4δ + ω(log λ) · (3∆+ δ)).
```

**Proof.** (line 802)

```
Proof. Suppose that there is a set of transactions txs in the view of every honest player by time
t, where t > GST, where txs is not yet in the output of any honest player. Let h be the highest
iteration that any honest player is in at time t. By Lemma 3.4 every every honest process must have
entered iteration h by time t+δ. Now, suppose that at least one iteration i ∈{h+1, . . . , h+k} has
an honest leader Li, for some choice of k ∈N. Then, applying Lemmas 3.5 and 3.6, every honest
process will see a finalized block containing txs by time t + 4δ + k(3∆+ δ).
It remains to analyze the probability that, in a random execution, there is a sequence of k
iterations in a row h, h + 1, . . . , h + k −1 s.t. for every i ∈[k], Lh+i−1 is corrupt. First, observe
that the attacker (and the environment) is PPT, and so there is a polynomial function m(·) s.t.
any execution of the protocol on a security parameter 1λ must contain at most m(λ) number of
iterations. Fix any λ ∈N. Recall that, for all i ∈[m(λ)], Li is selected using a random oracle, and
is thus corrupt with independent probability f/n ≤1/3. (Recall that we instantiated the leader
election oracle to be either Li := H∗(i) mod n or Li := H∗(σi) mod n, where H∗is a random
oracle and σi is a unique threshold signature on i.)
To help, we analyze the probability that in a sequence of m(λ) unbiased coin flips, there is
a consecutive sequence of at least k tails. There are at most (m(λ) −k + 1) · 2m(λ)−k possible
sequences with at least k consecutive tails, out of 2m(λ) total; thus the probability is less than
(m(λ)−k+1)
2k
. Immediately, the probability there are k corrupt leaders in a row is < (m(λ)−k+1)
2k
, since
the probability a leader is corrupt is less than the probability an unbiased coin is tails. Observing
that (m(λ)−k+1)
2k
is a negligible function in λ when k = ω(log λ), the theorem follows.
```

### Theorem 3.4 — §3.3 — Expected View-Based Liveness

**Statement.** (line 833)

```
Theorem 3.4 (Expected View-Based Liveness). Simplex has expected 3.5δ + 1.5∆view-based live-
ness.
```

**Proof.** (line 835)

```
Proof. Fix any iteration h ∈N. Suppose that there is a set of transactions txs in the view of every
honest player before they enter iteration h, and moreover suppose that every honest player entered
iteration h by some time t > GST. Recall that for each iteration i, we defined the leader to be Li :=
H∗(i) mod n, where H∗is a random oracle (chosen independently of GST and h). Immediately,
for each i ∈N, Li must be an honest player with independent probability (n −f)/n ≥2/3. Denote
X the number s.t. Lh+X is honest but, when X > 0, Li is faulty ∀i where h ≤i < h + X. Here
X is a random variable, and immediately E[X] ≤3/2 −1 = 1/2. Observe that, importantly, Lh+X
will propose a blockchain that contains txs.
It remains to upper bound the time at which some honest process enters iteration h + X. By
Lemma 3.6, every honest process will have entered iteration h+X by time t+X ·(3∆+δ). Applying
Lemma 3.5, we conclude that every honest process will see a finalized block proposed by Lh+X by
time t + 3δ + (X) · (3∆+ δ). Moreover, this block contains txs if not already in a previous block.
Taking the expectation of the time elapsed since t, the theorem statement follows.
```

## Lemmas

### Lemma 3.1 — §3.2 — signature unforgeability

**Statement.** (line 595)

```
Lemma 3.1. With overwhelming probability in λ, for any honest process i, no honest process will
see a valid signature of the form ⟨m⟩i in honest view unless process i previously signed m.
```

**Proof.** (line 597)

```
Proof. This is by a direct reduction to the unforgeability of the signature scheme.
```

### Lemma 3.2 — §3.2 — quorum intersection — two non-dummy blocks

**Statement.** (line 602)

```
Lemma 3.2. Let h ∈N. Let bh and b′
h be two distinct blocks s.t. neither are equal to the dummy
block ⊥h. It cannot be that both bh and b′
h are both notarized in honest view (except with negligible
probability in λ).
```

**Proof.** (line 607)

```
Proof. Consider a random execution and let bh and b′
h be any two blocks of height h in the execution
transcript, s.t. bh ̸= b′
h and moreover bh ̸= ⊥h and b′
h ̸= ⊥h. We call a tuple (i, m) “good” if
m ∈{(vote, h, bh), (vote, h, b′
h)} and there exists a valid signature ⟨m⟩i in the view of some honest
player. By the construction of the protocol, each honest process signs at most one of (vote, h, bh)
and (vote, h, b′
h). On the other hand, each corrupted player can sign both messages. Applying
Lemma 3.1, then there are at most (n−f)+f ·2 = n+f < 4n/3 good tuples with all but negligible
probability in the security parameter. Now assume for the sake of contradiction that there are both
notarizations for bh and b′
h in honest view. Then there are ≥2n/3 signatures for ⟨vote, h, bh⟩and
likewise ≥2n/3 signatures for ⟨vote, h, b′
h⟩in honest view; thus there are ≥4n/3 good tuples in
honest view, which is a contradiction.
```

### Lemma 3.3 — §3.2 — quorum intersection — finalize vs. dummy

**Statement.** (line 626)

```
Lemma 3.3. If there is a finalization for height h in honest view, ⊥h cannot be notarized in honest
view (except with negligible probability in λ).
```

**Proof.** (line 628)

```
Proof. We call a tuple (i, m) “good” if m ∈{(finalize, h), (vote, h, ⊥h)} and there exists a valid
signature ⟨m⟩i in the view of some honest player. By the construction of the protocol, each honest
process signs at most one of ⟨finalize, h⟩or ⟨vote, h, ⊥h⟩, whereas each corrupted player can sign
either message. Applying Lemma 3.1, there are thus at most (n −f) + f · 2 = n + f < 4n/3 good
tuples (with all but negligible probability in λ). But now assume for the sake of contradiction
that bh is finalized and ⊥h is also notarized. Since bh is finalized, there are ≥2n/3 signatures
for ⟨finalize, h⟩in honest view, and likewise since ⊥h is notarized, there are ≥2n/3 signatures for
⟨vote, h, ⊥h⟩in honest view; thus there are ≥4n/3 good tuples, which is a contradiction.
```

### Lemma 3.4 — §3.3 — Synchronized Iterations

**Statement.** (line 713)

```
Lemma 3.4 (Synchronized Iterations). If some honest process has entered iteration h by time t,
then every honest process has entered iteration h by time max(GST, t + δ).
```

**Proof.** (line 715)

```
Proof. By the assumption that some honest process p has entered iteration h by time t, we know
that process p must have seen a notarized blockchain of height h −1 at or before time t. By the
protocol design, p will multicast their view of this notarized blockchain immediately before entering
iteration h. Subsequently, every honest process will have seen a notarized blockchain of height h−1,
and thus also a notarized blockchain for every height h′ ≤h−1, by time max(GST, t+δ). Thus, by
time max(GST, t+δ), every honest process that is not yet in an iteration ≥h will have incremented
its iteration number until it is in iteration h.
```

### Lemma 3.5 — §3.3 — The Effect of Honest Leaders

**Statement.** (line 723)

```
Lemma 3.5 (The Effect of Honest Leaders). Let h be any iteration with an honest leader Lh.
Suppose that Lh entered iteration h by some time t > GST. Then, with all but negligible probability,
every honest process will have entered iteration h+1 by time t+2δ. Moreover, every honest process
will see a finalized block at height h, proposed by Lh, by time t + 3δ.
```

**Proof.** (line 727)

```
We break the proof down into two subclaims.
Subclaim 3.1. Every honest player will see a notarized blockchain of height h, and thus enter
iteration h + 1, by time t + 2δ (except with negligible probability).
Proof. Recall that Lh enters iteration h by time t. Thus, Lh must multicast a proposal for a new
non-dummy block bh by time t. Thus, by time t+δ (observing that t > GST), every honest process
must have seen a valid proposal from the leader for bh. There are now two cases:
• Case 1. Every honest process p casts a vote ⟨vote, h, bh⟩p by time t + δ. Subsequently every
honest process will see a notarization for bh and thus a notarized blockchain of height h by
time t + 2δ, if not earlier, and enter iteration h + 1, as required.
• Case 2. There is some honest process p that did not multicast a vote ⟨vote, h, bh⟩p by time
t + δ. However, by Lemma 3.4, every honest process should have entered iteration h by time
t+δ, so the only way this could happen is if p entered iteration h+1 before time t+δ. Then,
every honest process will have entered iteration h+1 (and thus seen a notarized blockchain of
height h) by time t + 2δ, again by Lemma 3.4. (This case may have occured if, for instance,
p saw a notarization for Lh’s proposed block without seeing the proposal itself.)
Subclaim 3.2. Every honest player p will multicast ⟨finalize, h⟩p by time t + 2δ, and thus see a
finalized block of height h by time t + 3δ (except with negligible probability).
Proof. By Subclaim 3.1, every honest player sees a notarized blockchain of height h (thus finishing
iteration h) by time t + 2δ. We will show below that no honest player’s timer for iteration h can
fire before time ≤t+2δ. Then, when each honest player p finishes iteration h, they must multicast
a ⟨finalize, h⟩p message, as their timer cannot have fired yet, showing the claim.
Let t′ ≤t be the time at which the first honest process enters iteration h. By Lemma 3.4,
all honest processes—including the leader Lh—will have entered iteration h by max(GST, t′ + δ),
implying that t ≤t′ + δ (since t is strictly greater than GST). The earliest an honest timer can fire
is at or after t′ + 3∆> t′ + 3δ ≥t + 2δ time (noting that ∆> δ), as desired.
Finishing the Proof of Lemma 3.5. It remains to show that this finalized block is proposed by the
leader. Recall that by Subclaim 3.2, every honest player p will have seen a finalized block bh of
height h by time t + 3δ. Applying Lemma 3.3, we know that bh ̸= ⊥h. Thus, bh must be proposed
by Lh, because for it to be notarized, some honest player must have voted for it.
The lemma
follows.
```

### Lemma 3.6 — §3.3 — The Effect of Faulty Leaders

**Statement.** (line 770)

```
Lemma 3.6 (The Effect of Faulty Leaders). Suppose every honest process has entered iteration h
by time t, for some t > GST. Then every honest process will have entered iteration h + 1 by time
t + 3∆+ δ.
```

**Proof.** (line 792)

```
Proof. There are two cases. First, suppose that for every honest process, its timer in iteration h fires;
then every honest process p will cast a vote ⟨vote, h, ⊥h⟩p at some time ≤t + 3∆, and subsequently
this vote will be in the view of every honest process by time max(GST, t + 3∆+ δ) = t + 3∆+ δ.
These votes comprise a notarization for ⊥h and thus every honest process will see a notarized
blockchain of height h by time t + 3∆+ δ (if not earlier) and subsequently enter iteration h + 1 as
required. The second case is if an iteration h timer does not fire for some honest process p. Then it
must be that p entered iteration h + 1 at a time before its timer could fire, i.e. before time t + 3∆,
and applying Lemma 3.4 yields the claim.
```

### Lemma 3.7 — §3.4 — message complexity

**Statement.** (line 853)

```
Lemma 3.7. In each iteration h, each honest process will multicast at most 4 messages.
```

**Proof.** (line 854)

```
Proof. For each iteration h ∈N, an honest process p will multicast at most one propose message, at
most one vote message for a non-⊥block, at most one of ⟨vote, h, ⊥h⟩p and ⟨finalize, h⟩p, and will
relay their view of a notarized blockchain of height h at most once.
```

import Simplex.Protocol
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Simplex

/-- Idealized digital signatures (EUF-CMA), declared as an axiom.
    Sound relative to the signature scheme being unforgeable; the negligible
    forgery probability of Lemma 3.1 is abstracted away here. Guarded by
    `ValidExecution` so it constrains only real protocol executions (without the
    guard, an adversarial `Execution` value would let this axiom prove `False`).
    Source: Chan & Pass, Simplex Consensus, Lemma 3.1 — "by a direct reduction
    to the unforgeability of the signature scheme". -/
axiom signature_unforgeable {n : Nat} (e : Execution n) :
    ValidExecution e → SignatureUnforgeable e

/-- Idealized collision-resistant hash `H`, declared as an axiom. Sound relative
    to `H` being collision resistant; the negligible-collision probability of
    Theorem 3.1 is abstracted away here. Guarded by `ValidExecution` so it
    constrains only real protocol executions (without the guard, an adversarial
    `ChainView`/`Execution` with `LogPrefix := fun _ _ => False` would let this
    axiom prove `False`). Source: Chan & Pass, Simplex Consensus, Theorem 3.1 —
    "by the collision-resistant property of the hash function `H(·)`". -/
axiom collision_resistant {n : Nat} (cv : ChainView n) (e : Execution n) :
    ValidExecution e → cv.CollisionResistant e

/-- **Phase 1 leader-rotation tail bound (Theorem 3.3, `needs-axiom`).** In a random
    execution with at most `m` iterations, the probability of `k` consecutive corrupt
    leaders is `consecutiveCorruptProb m k`. Each leader `L_i := H*(i) mod n` is
    corrupt with independent probability `f/n ≤ 1/3 < 1/2` (random oracle), so the
    consecutive-tails counting argument gives the bound `< (m − k + 1)/2^k`, which is
    negligible once `k = ω(log λ)`. Declared as an axiom for Phase 1; Phase 2 (#13)
    replaces it with the elementary `Mathlib.Probability` proof. Source: Chan & Pass,
    Simplex Consensus, Theorem 3.3. -/
axiom consecutiveCorruptProb : Nat → Nat → ℝ

axiom consecutiveCorruptProb_bound (m k : Nat) :
    consecutiveCorruptProb m k ≤ ((m : ℝ) - (k : ℝ) + 1) / 2 ^ k

/-- **Phase 1 expected leader-offset bound (Theorem 3.4, `needs-axiom`).** The offset
    `X` to the next honest leader — each leader honest with independent probability
    `(n − f)/n ≥ 2/3` — is geometric, so its expectation satisfies
    `E[X] ≤ 3/2 − 1 = 1/2`. `expectedLeaderOffset` is `E[X]`; the axioms bound it in
    `[0, 1/2]`. Declared for Phase 1; Phase 2 (#14) replaces these with the
    geometric-distribution expectation computed in `Mathlib.Probability`. Source:
    Chan & Pass, Simplex Consensus, Theorem 3.4. -/
axiom expectedLeaderOffset : ℝ

axiom expectedLeaderOffset_nonneg : 0 ≤ expectedLeaderOffset

axiom expectedLeaderOffset_le : expectedLeaderOffset ≤ 1 / 2

end Simplex

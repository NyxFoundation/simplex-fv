import Simplex.Protocol

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

end Simplex

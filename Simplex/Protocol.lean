import Simplex.Basic
import Mathlib.Data.Finset.Card

set_option autoImplicit false

namespace Simplex

/-- **Abstract chain/message interface for the safety theorems** (Barrier 4: the
    protocol mechanics are modeled as an interface, not implemented operationally).
    Bundles the block/log structure and the message encodings that the
    quorum-counting lemmas (3.2, 3.3) and the consistency theorem (3.1) range over.
    A concrete operational model can later *construct* a `ChainView` without
    changing any theorem statement. -/
structure ChainView (n : Nat) where
  /-- Height of a block; the genesis `b_0` is height 0. -/
  height      : Block → Nat
  /-- The dummy block `⊥_h` at each height. -/
  dummyBlock  : Nat → Block
  /-- Ancestor of a block at a given height (its height-`k` prefix block). -/
  blockAt     : Block → Nat → Block
  /-- `linearize` of the chain ending at a block. -/
  logOf       : Block → Log
  /-- The vote message `⟨vote, h, b⟩` for block `b`. -/
  voteMsg     : Block → Message
  /-- The finalize message `⟨finalize, h⟩`. -/
  finalizeMsg : Nat → Message

namespace ChainView

variable {n : Nat}

/-- `b` is **notarized in honest view**: a `⌈2n/3⌉`-quorum each of whose members
    has a valid `⟨vote, ·, b⟩` seen in honest view. -/
def Notarized (cv : ChainView n) (e : Execution n) (b : Block) : Prop :=
  ∃ Q : Finset (Process n),
    quorumThreshold n ≤ Q.card ∧ ∀ p ∈ Q, e.SeenByHonest p (cv.voteMsg b)

/-- Height `h` is **finalized in honest view**: a `⌈2n/3⌉`-quorum each of whose
    members has a valid `⟨finalize, h⟩` seen in honest view. -/
def Finalized (cv : ChainView n) (e : Execution n) (h : Nat) : Prop :=
  ∃ Q : Finset (Process n),
    quorumThreshold n ≤ Q.card ∧ ∀ p ∈ Q, e.SeenByHonest p (cv.finalizeMsg h)

/-- Protocol single-vote rule: an honest process signs at most one vote among
    distinct blocks at a common height (it votes once per iteration). -/
def HonestSingleVote (cv : ChainView n) (e : Execution n) : Prop :=
  ∀ (p : Process n) (b b' : Block), e.Honest p →
    cv.height b = cv.height b' → b ≠ b' →
    e.Signed p (cv.voteMsg b) → e.Signed p (cv.voteMsg b') → False

/-- Protocol rule: an honest process signs at most one of `⟨finalize, h⟩` and the
    dummy vote `⟨vote, h, ⊥_h⟩` (finalizing a height precludes voting for its
    dummy block, and vice versa). -/
def HonestFinalizeNotDummyVote (cv : ChainView n) (e : Execution n) : Prop :=
  ∀ (p : Process n) (h : Nat), e.Honest p →
    e.Signed p (cv.finalizeMsg h) → e.Signed p (cv.voteMsg (cv.dummyBlock h)) → False

/-- **Idealized collision resistance**, exposed at the granularity Theorem 3.1 uses
    it: if two chains share the same non-dummy block at the common (shorter) height,
    their parent chains coincide, so the shorter linearized log is a prefix of the
    longer. Models "equal `H`-hashes ⇒ equal parent chains" on the reachable block
    space (the hash/`linearize` machinery is abstracted, mirroring how
    `SignatureUnforgeable` abstracts the temporal/probabilistic content of
    Lemma 3.1). Declared as an axiom in `Simplex/Axioms.lean`. -/
def CollisionResistant (cv : ChainView n) (_e : Execution n) : Prop :=
  ∀ (top top' : Block),
    cv.height top ≤ cv.height top' →
    cv.blockAt top (cv.height top) = cv.blockAt top' (cv.height top) →
    cv.blockAt top (cv.height top) ≠ cv.dummyBlock (cv.height top) →
    LogPrefix (cv.logOf top) (cv.logOf top')

/-- Deterministic structural laws of the chain interface, threaded as a hypothesis
    bundle (provable in any concrete operational model):
    - `blockAt_self`: a block is its own height-`h` ancestor;
    - `height_blockAt`: the height-`k` ancestor has height `k`;
    - `prefix_notarized`: every ancestor of a notarized chain is notarized
      (the paper's "`b'_{h'}` notarized ⇒ `b'_h` notarized");
    - `honest_single_vote` / `honest_fin_dummy`: the honest signing rules above. -/
structure Laws (cv : ChainView n) (e : Execution n) : Prop where
  blockAt_self       : ∀ b, cv.blockAt b (cv.height b) = b
  height_blockAt     : ∀ b k, k ≤ cv.height b → cv.height (cv.blockAt b k) = k
  prefix_notarized   : ∀ b k, k ≤ cv.height b → cv.Notarized e b → cv.Notarized e (cv.blockAt b k)
  honest_single_vote : cv.HonestSingleVote e
  honest_fin_dummy   : cv.HonestFinalizeNotDummyVote e

end ChainView

end Simplex

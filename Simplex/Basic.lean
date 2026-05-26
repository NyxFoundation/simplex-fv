set_option autoImplicit false

namespace Simplex

/-- A validator/process; there are `n` of them. -/
abbrev Process (n : Nat) := Fin n

/-- Abstract message space (votes, finalize, propose). Refined in later issues. -/
opaque Message : Type

/-- An execution transcript, with the predicates Lemma 3.1 ranges over.
    All fields are abstract for this MVP (Barrier 4: abstract interface). -/
structure Execution (n : Nat) where
  Honest       : Process n → Prop            -- process is honest (not Byzantine)
  Signed       : Process n → Message → Prop  -- process actually signed the message
  -- `SeenByHonest i m` existentially aggregates over honest observers: a valid
  -- ⟨m⟩_i appears in *some* honest process's view. This matches the "some honest
  -- view" usage in Lemmas 3.2/3.3. (Lemma 3.1's "no honest process will see"
  -- collapses to the same predicate; if a later proof needs the specific
  -- observer, refine to `Seen : Process n → Process n → Message → Prop`.)
  SeenByHonest : Process n → Message → Prop

/-- Marks executions actually produced by the protocol. Opaque (no constructor),
    so adversarial structures like `⟨fun _ => True, fun _ _ => False, fun _ _ => True⟩`
    cannot be shown valid — this is what keeps the axiom in `Simplex.Axioms` from
    proving `False`. A concrete operational model can later *define* it. -/
opaque ValidExecution {n : Nat} (e : Execution n) : Prop

/-- Idealized unforgeability as a *predicate* on an execution (Lemma 3.1's
    deterministic conclusion). Exposed as a `def` so later theorems can also
    thread it as a hypothesis (cf. `simplex_consistency (huf : …)`). -/
def SignatureUnforgeable {n : Nat} (e : Execution n) : Prop :=
  ∀ (i : Process n) (m : Message), e.Honest i → e.SeenByHonest i m → e.Signed i m

end Simplex

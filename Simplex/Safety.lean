import Simplex.Axioms

set_option autoImplicit false

namespace Simplex

/-- Lemma 3.1: in a valid execution, a signature attributed to an honest process
    `i` and seen in honest view exists only if `i` actually signed it. Immediate
    from the unforgeability axiom (mirrors the paper's one-line reduction).

    Phase 1 scope: this is the *deterministic* consequence of the crypto axiom;
    the paper's "with overwhelming probability" and the temporal "previously" are
    abstracted into the axiom, not proved here. -/
theorem lemma_3_1 {n : Nat} (e : Execution n) (i : Process n) (m : Message)
    (hvalid : ValidExecution e) (hi : e.Honest i) (hseen : e.SeenByHonest i m) :
    e.Signed i m :=
  signature_unforgeable e hvalid i m hi hseen

end Simplex

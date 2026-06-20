import Simplex.Safety.QuorumIntersection
import Simplex.Safety.Lemma3_1

set_option autoImplicit false

namespace Simplex

/-- **Lemma 3.3.** If there is a finalization for height `h` in honest view, the
    dummy block `⊥_h` cannot also be notarized in honest view. Here `mFin` is the
    finalize message `⟨finalize, h⟩` and `mVote` is the dummy vote `⟨vote, h, ⊥_h⟩`;
    a finalization (resp. notarization) is a `⌈2n/3⌉`-quorum each of whose members
    has a valid signature on `mFin` (resp. `mVote`) seen in honest view.

    Same quorum-intersection argument as Lemma 3.2, applied to the two messages an
    honest process signs at most one of: the finalize and the dummy vote. The two
    quorums intersect in an honest process (`quorum_intersect_honest`); Lemma 3.1
    (`signature_unforgeable`, threaded via `hvalid`) lifts "seen in honest view" to
    "actually signed", so that process signed *both* — contradicting the protocol
    rule (`hSignAtMostOne`) that an honest process signs at most one of
    `⟨finalize, h⟩` and `⟨vote, h, ⊥_h⟩`. The paper's counting bound
    `(n−f) + 2f = n + f < 4n/3` is exactly this intersection argument. No `sorry`,
    no local axiom; the only axiom reached is the crypto one behind Lemma 3.1. -/
theorem lemma_3_3 {n f : Nat} (e : Execution n) (mFin mVote : Message)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f)
    -- Protocol rule (abstract): an honest process signs at most one of
    -- `⟨finalize, h⟩` and `⟨vote, h, ⊥_h⟩`.
    (hSignAtMostOne : ∀ p, e.Honest p → e.Signed p mFin → e.Signed p mVote → False)
    -- `h` finalized and `⊥_h` notarized, both in honest view.
    (Q Q' : Finset (Process n))
    (hQcard : quorumThreshold n ≤ Q.card) (hQ'card : quorumThreshold n ≤ Q'.card)
    (hQseen : ∀ p ∈ Q, e.SeenByHonest p mFin) (hQ'seen : ∀ p ∈ Q', e.SeenByHonest p mVote) :
    False := by
  obtain ⟨p, hpInter, hpHonest⟩ :=
    quorum_intersect_honest hf Q Q' honest hQcard hQ'card hcorrupt
  have hpH : e.Honest p := (hHonest p).1 hpHonest
  rw [Finset.mem_inter] at hpInter
  -- Lemma 3.1 lifts "seen in honest view" to "actually signed", for both messages.
  have hsigFin : e.Signed p mFin :=
    lemma_3_1 e p mFin hvalid hpH (hQseen p hpInter.1)
  have hsigVote : e.Signed p mVote :=
    lemma_3_1 e p mVote hvalid hpH (hQ'seen p hpInter.2)
  exact hSignAtMostOne p hpH hsigFin hsigVote

/-- **Block-level Lemma 3.3.** If height `h` is finalized in honest view, the dummy
    `⊥_h` is not notarized in honest view. Unfolds the finalize/vote quorums and
    applies `lemma_3_3` with the honest finalize-vs-dummy-vote rule. -/
theorem finalized_dummy_not_notarized {n f : Nat} (cv : ChainView n) (e : Execution n)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f) (hfv : cv.HonestFinalizeNotDummyVote e)
    {h : Nat} (hfin : cv.Finalized e h) (hnot : cv.Notarized e (cv.dummyBlock h)) : False := by
  obtain ⟨Q, hQc, hQs⟩ := hfin
  obtain ⟨Q', hQ'c, hQ's⟩ := hnot
  exact lemma_3_3 e (cv.finalizeMsg h) (cv.voteMsg (cv.dummyBlock h)) hvalid hf honest hHonest
    hcorrupt (fun p hp s s' => hfv p h hp s s') Q Q' hQc hQ'c hQs hQ's

end Simplex

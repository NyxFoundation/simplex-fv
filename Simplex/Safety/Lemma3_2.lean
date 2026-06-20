import Simplex.Safety.QuorumIntersection
import Simplex.Safety.Lemma3_1

set_option autoImplicit false

namespace Simplex

/-- **Lemma 3.2.** Two distinct non-dummy blocks at the same height cannot both be
    notarized in honest view. Here `m`, `m'` are the two distinct vote messages
    `⟨vote, h, bₕ⟩` and `⟨vote, h, b'ₕ⟩`; a notarization is a `⌈2n/3⌉`-quorum each
    of whose members has a valid signature on the vote *seen in honest view*.

    The proof mirrors the paper's counting argument: the two notarization quorums
    intersect in an honest process (`quorum_intersect_honest`); Lemma 3.1
    (`signature_unforgeable`, threaded via `hvalid`) turns "seen in honest view"
    into "actually signed", so that honest process signed *both* votes —
    contradicting the protocol rule that an honest process signs at most one of
    two distinct non-dummy votes per height (`hSignAtMostOne`). No `sorry`, no
    local axiom; the only axiom reached is the crypto one behind Lemma 3.1. -/
theorem lemma_3_2 {n f : Nat} (e : Execution n) (m m' : Message)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f)
    -- Protocol rule (abstract): an honest process signs at most one of
    -- the two distinct non-dummy votes `m`, `m'` at this height.
    (hSignAtMostOne : ∀ p, e.Honest p → e.Signed p m → e.Signed p m' → False)
    -- Both blocks notarized in honest view.
    (Q Q' : Finset (Process n))
    (hQcard : quorumThreshold n ≤ Q.card) (hQ'card : quorumThreshold n ≤ Q'.card)
    (hQseen : ∀ p ∈ Q, e.SeenByHonest p m) (hQ'seen : ∀ p ∈ Q', e.SeenByHonest p m') :
    False := by
  obtain ⟨p, hpInter, hpHonest⟩ :=
    quorum_intersect_honest hf Q Q' honest hQcard hQ'card hcorrupt
  have hpH : e.Honest p := (hHonest p).1 hpHonest
  rw [Finset.mem_inter] at hpInter
  -- Lemma 3.1 lifts "seen in honest view" to "actually signed", for both votes.
  have hsig : e.Signed p m :=
    lemma_3_1 e p m hvalid hpH (hQseen p hpInter.1)
  have hsig' : e.Signed p m' :=
    lemma_3_1 e p m' hvalid hpH (hQ'seen p hpInter.2)
  exact hSignAtMostOne p hpH hsig hsig'

/-- **Block-level Lemma 3.2.** Two distinct blocks notarized in honest view at the
    same height are impossible. Unfolds the `ChainView` notarizations to their vote
    quorums and applies `lemma_3_2` with the honest single-vote rule. -/
theorem notarized_height_unique {n f : Nat} (cv : ChainView n) (e : Execution n)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f) (hsv : cv.HonestSingleVote e)
    {b b' : Block} (hheight : cv.height b = cv.height b') (hne : b ≠ b')
    (hnb : cv.Notarized e b) (hnb' : cv.Notarized e b') : False := by
  obtain ⟨Q, hQc, hQs⟩ := hnb
  obtain ⟨Q', hQ'c, hQ's⟩ := hnb'
  exact lemma_3_2 e (cv.voteMsg b) (cv.voteMsg b') hvalid hf honest hHonest hcorrupt
    (fun p hp s s' => hsv p b b' hp hheight hne s s') Q Q' hQc hQ'c hQs hQ's

end Simplex

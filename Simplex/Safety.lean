import Simplex.Axioms
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

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

/-- **Quorum intersection (the deterministic safety core).** With fewer than
    `n/3` corrupt processes (`3*f < n`), any two `⌈2n/3⌉`-quorums share an honest
    process. Pure finite combinatorics over `Finset` cardinalities — no axiom, no
    crypto. Reused by both safety lemmas (3.2 and 3.3).

    Proof: if the intersection contained no honest process it would sit inside the
    corrupt set, so `|Q₁ ∩ Q₂| ≤ f`; but inclusion–exclusion with `|Q₁ ∪ Q₂| ≤ n`
    forces `|Q₁ ∩ Q₂| ≥ 2⌈2n/3⌉ − n > f`, a contradiction (the threshold
    arithmetic, including the `⌈·⌉` rounding, is discharged by `omega`). -/
theorem quorum_intersect_honest {n f : Nat} (hf : 3 * f < n)
    (Q₁ Q₂ honest : Finset (Process n))
    (h₁ : quorumThreshold n ≤ Q₁.card) (h₂ : quorumThreshold n ≤ Q₂.card)
    (hc : honestᶜ.card ≤ f) :
    ∃ p, p ∈ Q₁ ∩ Q₂ ∧ p ∈ honest := by
  by_contra hcon
  push Not at hcon
  -- No honest process in the intersection ⇒ the intersection is corrupt.
  have hsub : Q₁ ∩ Q₂ ⊆ honestᶜ := by
    intro p hp
    exact Finset.mem_compl.2 (hcon p hp)
  have hinter : (Q₁ ∩ Q₂).card ≤ f :=
    le_trans (Finset.card_le_card hsub) hc
  -- The union fits inside the `n` processes.
  have hunion : (Q₁ ∪ Q₂).card ≤ n := by
    have : (Q₁ ∪ Q₂).card ≤ (Finset.univ : Finset (Process n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [Finset.card_fin] using this
  -- Inclusion–exclusion, then close by threshold arithmetic.
  have hie : (Q₁ ∪ Q₂).card + (Q₁ ∩ Q₂).card = Q₁.card + Q₂.card :=
    Finset.card_union_add_card_inter Q₁ Q₂
  simp only [quorumThreshold] at h₁ h₂
  omega

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
    -- Protocol rule (Barrier 4, abstract): an honest process signs at most one of
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
    -- Protocol rule (Barrier 4, abstract): an honest process signs at most one of
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

/-- **Theorem 3.1 (Consistency), `h ≤ h'` direction.** Given two chains finalized
    in honest view — `top` at height `h` and `top'` at height `h'` with `h ≤ h'` —
    the linearized log of the shorter is a prefix of that of the longer.

    Proof (mirrors the paper): the height-`h` block of the second chain,
    `blockAt top' h`, is notarized because it is an ancestor of the notarized
    `top'` (`prefix_notarized`). Lemma 3.3 (`finalized_dummy_not_notarized`),
    applied to the finalization at `h`, rules out both `top` and `blockAt top' h`
    being the dummy `⊥_h`. Lemma 3.2 (`notarized_height_unique`) then forces the
    two notarized non-dummy height-`h` blocks to be equal. Finally collision
    resistance (`collision_resistant`, the `Simplex/Axioms.lean` crypto axiom)
    turns "same non-dummy block at the common height" into the prefix conclusion.
    No `sorry`; the axioms reached are the two crypto ones (Lemmas 3.1's
    `signature_unforgeable` and this collision resistance). -/
theorem theorem_3_1 {n f : Nat} (cv : ChainView n) (e : Execution n)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f) (laws : cv.Laws e)
    (top top' : Block) (hle : cv.height top ≤ cv.height top')
    (hfin : cv.Finalized e (cv.height top))
    (hnotar : cv.Notarized e top) (hnotar' : cv.Notarized e top') :
    LogPrefix (cv.logOf top) (cv.logOf top') := by
  -- The height-`h` ancestor of the second chain is notarized (prefix of `top'`).
  have hb'h_notar : cv.Notarized e (cv.blockAt top' (cv.height top)) :=
    laws.prefix_notarized top' (cv.height top) hle hnotar'
  have hself : cv.blockAt top (cv.height top) = top := laws.blockAt_self top
  -- `b_h ≠ ⊥_h`: else `⊥_h` would be notarized, contradicting finalization at `h`.
  have hbh_nd : top ≠ cv.dummyBlock (cv.height top) := fun hdum =>
    finalized_dummy_not_notarized cv e hvalid hf honest hHonest hcorrupt
      laws.honest_fin_dummy hfin (hdum ▸ hnotar)
  -- `b'_h ≠ ⊥_h`, likewise.
  have hb'h_nd : cv.blockAt top' (cv.height top) ≠ cv.dummyBlock (cv.height top) := fun hdum =>
    finalized_dummy_not_notarized cv e hvalid hf honest hHonest hcorrupt
      laws.honest_fin_dummy hfin (hdum ▸ hb'h_notar)
  -- `b_h = b'_h`: both notarized at height `h` and non-dummy (Lemma 3.2).
  have heq : top = cv.blockAt top' (cv.height top) := by
    by_contra hne
    exact notarized_height_unique cv e hvalid hf honest hHonest hcorrupt
      laws.honest_single_vote (laws.height_blockAt top' (cv.height top) hle).symm hne
      hnotar hb'h_notar
  -- Collision resistance: same non-dummy block at the common height ⇒ prefix.
  apply collision_resistant cv e hvalid top top' hle
  · rw [hself]; exact heq
  · rw [hself]; exact hbh_nd

/-- **Theorem 3.1 (Consistency).** Any two logs output in honest view (each the
    linearization of a chain finalized and notarized in honest view) are
    prefix-comparable. The `h ≤ h'` case analysis discharges to `theorem_3_1`. -/
theorem theorem_3_1_consistency {n f : Nat} (cv : ChainView n) (e : Execution n)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f) (laws : cv.Laws e)
    (top top' : Block)
    (hfin : cv.Finalized e (cv.height top)) (hfin' : cv.Finalized e (cv.height top'))
    (hnotar : cv.Notarized e top) (hnotar' : cv.Notarized e top') :
    LogPrefix (cv.logOf top) (cv.logOf top') ∨ LogPrefix (cv.logOf top') (cv.logOf top) := by
  rcases le_total (cv.height top) (cv.height top') with hle | hle
  · exact Or.inl (theorem_3_1 cv e hvalid hf honest hHonest hcorrupt laws
      top top' hle hfin hnotar hnotar')
  · exact Or.inr (theorem_3_1 cv e hvalid hf honest hHonest hcorrupt laws
      top' top hle hfin' hnotar' hnotar)

end Simplex

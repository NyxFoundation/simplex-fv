import Simplex.Safety.Lemma3_2
import Simplex.Safety.Lemma3_3
import Simplex.Axioms

set_option autoImplicit false

namespace Simplex

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

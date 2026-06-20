import Simplex.Safety
import Simplex.Liveness
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

/-- **The honest-leader round scenario** for Lemma 3.5 (protocol and timing
    mechanics as an abstract interface). Bundles the timing model `tv`, the
    chain view `cv`, the honest leader `L` of iteration `h`, the block `b` it
    proposes at height `h`, and the protocol-behaviour laws the proof needs. The
    novel timing content of the lemma (the `t+2δ` / `t+3δ` bounds and the
    `3Δ > 3δ` timer argument) is *derived*; the per-step protocol behaviours
    (proposal/vote/notarization/finalize timing, leader-proposal) are the abstract
    laws below. -/
structure HonestLeaderRound (n : Nat) where
  tv      : TimingView n
  e       : Execution n
  cv      : ChainView n
  hvalid  : ValidExecution e
  -- quorum parameters (for Lemma 3.3 / `finalized_dummy_not_notarized`)
  f       : Nat
  honest  : Finset (Process n)
  hf      : 3 * f < n
  hHonest : ∀ p, p ∈ honest ↔ e.Honest p
  hcorrupt : honestᶜ.card ≤ f
  hfin_dummy : cv.HonestFinalizeNotDummyVote e
  -- timing model laws (synchronized iterations, Lemma 3.4)
  tvLaws  : tv.Laws e
  -- round data
  h       : Nat
  t       : ℝ
  t'      : ℝ
  L       : Process n
  b       : Block
  /-- `q` has seen a finalized block at height `k` by time `s`. -/
  SawFinalized : Process n → Nat → ℝ → Prop
  /-- block `c` was proposed by process `p`. -/
  ProposedBy   : Block → Process n → Prop
  -- standing facts
  hL_honest : e.Honest L
  ht_gst    : tv.GST < t
  hδ        : 0 ≤ tv.δ
  hbheight  : cv.height b = h
  /-- Lemma 3.4 consequence: with `t' ≤ t` the first honest entry into iteration
      `h` and `t > GST`, the honest leader entered `h` by `max(GST, t'+δ) = t'+δ`,
      hence `t ≤ t' + δ`. -/
  ht_le     : t ≤ t' + tv.δ
  /-- **Subclaim 3.1.** Either every honest process has seen a notarized height-`h`
      chain by `t+2δ` (Case 1: all vote on the leader's proposal), or some honest
      process already entered iteration `h+1` by `t+δ` (Case 2: it advanced early). -/
  hcase : (∀ q, e.Honest q → tv.SawNotar q h (t + 2 * tv.δ)) ∨
          (∃ p, e.Honest p ∧ tv.EnteredBy p (h + 1) (t + tv.δ))
  /-- **Subclaim 3.2** (delivery part): once every honest process has finished
      iteration `h` by `t+2δ` and no honest timer can fire before then
      (`t+2δ ≤ t'+3Δ`), each multicasts `⟨finalize, h⟩` and every honest process
      sees a finalized block at height `h` by `t+3δ`. -/
  hfinalize : (∀ r, e.Honest r → tv.EnteredBy r (h + 1) (t + 2 * tv.δ)) →
              t + 2 * tv.δ ≤ t' + 3 * tv.Δ →
              ∀ q, e.Honest q → SawFinalized q h (t + 3 * tv.δ)
  /-- Bridge: a finalized block seen in honest view at height `h` is a finalization
      for height `h` (a `⌈2n/3⌉`-quorum of `⟨finalize, h⟩`), and the block `b` is
      notarized in honest view. -/
  hcv_finalized : (∀ q, e.Honest q → SawFinalized q h (t + 3 * tv.δ)) → cv.Finalized e h
  hcv_notarized : cv.Notarized e b
  /-- A notarized non-dummy block must have been proposed by the leader (some honest
      process voted for it, and honest processes vote only for the leader's proposal). -/
  hproposed : cv.Notarized e b → b ≠ cv.dummyBlock h → ProposedBy b L

namespace HonestLeaderRound

variable {n : Nat} (R : HonestLeaderRound n)

/-- **Subclaim 3.1 (conclusion).** Every honest process has entered iteration `h+1`
    by time `t+2δ`. Case 1 is immediate from `saw_entered`; Case 2 propagates one
    early entrant to all honest processes via Lemma 3.4 (`lemma_3_4`), the
    `max(GST, ·)` collapsing because `t > GST`. -/
theorem all_entered (q : Process n) (hq : R.e.Honest q) :
    R.tv.EnteredBy q (R.h + 1) (R.t + 2 * R.tv.δ) := by
  rcases R.hcase with hall | ⟨p, hp, hpenter⟩
  · exact R.tvLaws.saw_entered q R.h (R.t + 2 * R.tv.δ) hq (hall q hq)
  · have hstep := lemma_3_4 R.tv R.e R.tvLaws R.h (R.t + R.tv.δ) p hp hpenter q hq
    have hge : R.tv.GST ≤ R.t + R.tv.δ + R.tv.δ := by linarith [R.ht_gst, R.hδ]
    rw [max_eq_right hge] at hstep
    have heq : R.t + R.tv.δ + R.tv.δ = R.t + 2 * R.tv.δ := by ring
    rw [heq] at hstep
    exact hstep

/-- The timer bound of Subclaim 3.2: no honest timer for iteration `h` can fire
    before every honest process finishes iteration `h` (by `t+2δ`). Derived from
    `t ≤ t'+δ` (Lemma 3.4) and `δ < Δ`: `t+2δ ≤ t'+3δ ≤ t'+3Δ`. -/
theorem timer_bound : R.t + 2 * R.tv.δ ≤ R.t' + 3 * R.tv.Δ := by
  linarith [R.ht_le, R.tv.δ_lt_Δ]

/-- **Subclaim 3.2 (conclusion).** Every honest process sees a finalized block at
    height `h` by time `t+3δ`: every honest process finished iteration `h` by `t+2δ`
    (`all_entered`) before any timer can fire (`timer_bound`), so each multicasts
    `⟨finalize, h⟩` and the finalization is delivered by `t+3δ` (`hfinalize`). -/
theorem all_finalized (q : Process n) (hq : R.e.Honest q) :
    R.SawFinalized q R.h (R.t + 3 * R.tv.δ) :=
  R.hfinalize (fun r hr => R.all_entered r hr) R.timer_bound q hq

/-- The finalized block `b` at height `h` is not the dummy `⊥_h`. Lemma 3.3
    (`finalized_dummy_not_notarized`): height `h` is finalized in honest view
    (`hcv_finalized` applied to `all_finalized`), so a notarized `⊥_h` is
    impossible — but `b` is notarized, hence `b ≠ ⊥_h`. -/
theorem block_not_dummy : R.b ≠ R.cv.dummyBlock R.h := by
  have hCvFin : R.cv.Finalized R.e R.h :=
    R.hcv_finalized (fun q hq => R.all_finalized q hq)
  intro hdum
  exact finalized_dummy_not_notarized R.cv R.e R.hvalid R.hf R.honest R.hHonest R.hcorrupt
    R.hfin_dummy hCvFin (hdum ▸ R.hcv_notarized)

/-- **Lemma 3.5 (The Effect of Honest Leaders).** With an honest leader `L` of
    iteration `h` that entered `h` by some time `t > GST`:
    (a) every honest process has entered iteration `h+1` by `t+2δ`;
    (b) every honest process sees a finalized block at height `h` by `t+3δ`, and
        that block is not the dummy `⊥_h` and was proposed by the leader `L`.
    Combines `all_entered`, `all_finalized`, `block_not_dummy`, and the
    leader-proposal law `hproposed`. Uses Lemma 3.4 (synchronization) and Lemma 3.3
    (dummy not notarized); no `sorry`. -/
theorem lemma_3_5 :
    (∀ q, R.e.Honest q → R.tv.EnteredBy q (R.h + 1) (R.t + 2 * R.tv.δ)) ∧
    (∀ q, R.e.Honest q → R.SawFinalized q R.h (R.t + 3 * R.tv.δ)) ∧
    R.b ≠ R.cv.dummyBlock R.h ∧ R.ProposedBy R.b R.L :=
  ⟨fun q hq => R.all_entered q hq,
   fun q hq => R.all_finalized q hq,
   R.block_not_dummy,
   R.hproposed R.hcv_notarized R.block_not_dummy⟩

end HonestLeaderRound

end Simplex

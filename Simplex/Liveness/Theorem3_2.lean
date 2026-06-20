import Simplex.Liveness.Lemma3_5
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

variable {n : Nat}

/-- **Theorem 3.2 (Optimistic Confirmation Time).** Simplex has optimistic
    confirmation time `5δ`: if `txs` is in every honest view by `t > GST` and the
    decisive honest leader entered its iteration by `t + 2δ`, every honest process
    confirms `txs` by `t + 5δ`.

    The paper's two cases both bound the leader's entry by `t + 2δ` (Case 1: `L_h`
    enters by `t+δ` via Lemma 3.4; Case 2: `L_{h+1}` is reached by `t+2δ` via Lemma
    3.5), so this single hypothesis `hB` packages the worst of the two. With Lemma 3.5
    contributing the trailing `3δ` (`confirm_by`), the bound is `t + 2δ + 3δ = t + 5δ`.
    Deterministic; no `sorry`. -/
theorem theorem_3_2 (R : HonestLeaderRound n) (C : Process n → ℝ → Prop)
    (mono : ∀ q s s', s ≤ s' → C q s → C q s')
    (bridge : ∀ q, R.e.Honest q →
        R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ))
    (t : ℝ) (hB : R.t ≤ t + 2 * R.tv.δ) (q : Process n) (hq : R.e.Honest q) :
    C q (t + 5 * R.tv.δ) := by
  have h := confirm_by R C mono bridge (t + 2 * R.tv.δ) hB q hq
  have heq : t + 2 * R.tv.δ + 3 * R.tv.δ = t + 5 * R.tv.δ := by ring
  rwa [heq] at h

end Simplex

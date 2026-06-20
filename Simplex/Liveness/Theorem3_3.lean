import Simplex.Liveness.Lemma3_5
import Simplex.Axioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

variable {n : Nat}

/-- **Theorem 3.3 (Worst-Case Confirmation Time), deterministic core.** If `txs` is in
    every honest view by `t > GST` and at least one of iterations `h+1, …, h+k` has an
    honest leader — so the decisive honest leader entered its iteration by
    `t + δ + k·(3∆+δ)` (Lemma 3.4 for the initial `+δ`, then `faulty_iterations_advance`
    iterating Lemma 3.6 for the `k·(3∆+δ)`) — then every honest process confirms `txs`
    by `t + 4δ + k·(3∆+δ)`.

    Lemma 3.5 contributes the trailing `3δ` (`confirm_by`); the headline worst-case
    time `4δ + ω(log λ)·(3∆+δ)` is this bound with `k = ω(log λ)`, the choice of `k`
    for which the probability of `k` consecutive corrupt leaders is negligible
    (`consecutiveCorruptProb_bound`, the leader-rotation axiom). Deterministic
    core; no `sorry`. -/
theorem theorem_3_3_time (R : HonestLeaderRound n) (C : Process n → ℝ → Prop)
    (mono : ∀ q s s', s ≤ s' → C q s → C q s')
    (bridge : ∀ q, R.e.Honest q →
        R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ))
    (t : ℝ) (k : Nat)
    (hB : R.t ≤ t + R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ))
    (q : Process n) (hq : R.e.Honest q) :
    C q (t + 4 * R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ)) := by
  have h := confirm_by R C mono bridge (t + R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ)) hB q hq
  have heq : t + R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ) + 3 * R.tv.δ
           = t + 4 * R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ) := by ring
  rwa [heq] at h

/-- **The probability part of Theorem 3.3.** The probability that all of the next `k`
    leaders are corrupt is bounded by `(m − k + 1)/2^k` (negligible for
    `k = ω(log λ)`), so the honest-leader hypothesis of `theorem_3_3_time` holds with
    overwhelming probability. This is the `consecutiveCorruptProb_bound` axiom. -/
theorem theorem_3_3_negligible (m k : Nat) :
    consecutiveCorruptProb m k ≤ ((m : ℝ) - (k : ℝ) + 1) / 2 ^ k :=
  consecutiveCorruptProb_bound m k

end Simplex

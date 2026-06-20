import Simplex.HonestLeader
import Simplex.Axioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

variable {n : Nat}

/-- **Confirmation from a finalizing honest-leader round.** If the honest leader of
    the decisive iteration `h` entered it by time `B`, then every honest process has
    confirmed `txs` (output a finalized block containing it) by `B + 3δ`.

    `C q s` reads "process `q` has confirmed `txs` by time `s`"; `mono` is its
    monotonicity in time, and `bridge` says that the finalized height-`h` block Lemma
    3.5 delivers (`R.all_finalized`) is a confirmation of `txs` — i.e. the honest
    leader's proposed block contains `txs`. The `3δ` is exactly Lemma 3.5's
    finalize-by-`t+3δ` bound applied at the leader's entry time `R.t`. -/
theorem confirm_by (R : HonestLeaderRound n) (C : Process n → ℝ → Prop)
    (mono : ∀ q s s', s ≤ s' → C q s → C q s')
    (bridge : ∀ q, R.e.Honest q →
        R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ))
    (B : ℝ) (hB : R.t ≤ B) (q : Process n) (hq : R.e.Honest q) :
    C q (B + 3 * R.tv.δ) :=
  mono q _ _ (by linarith) (bridge q hq (R.all_finalized q hq))

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

/-- **Theorem 3.4 (Expected View-Based Liveness), deterministic core.** With leader
    offset `X` (the number of iterations until the next honest leader), the decisive
    honest leader is reached by `t + X·(3∆+δ)` (`faulty_iterations_advance` iterating
    Lemma 3.6), so by Lemma 3.5 (`confirm_by`) every honest process confirms `txs` by
    `t + 3δ + X·(3∆+δ)`. Deterministic in `X`; no `sorry`. -/
theorem theorem_3_4_time (R : HonestLeaderRound n) (C : Process n → ℝ → Prop)
    (mono : ∀ q s s', s ≤ s' → C q s → C q s')
    (bridge : ∀ q, R.e.Honest q →
        R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ))
    (t : ℝ) (X : Nat)
    (hB : R.t ≤ t + (X : ℝ) * (3 * R.tv.Δ + R.tv.δ))
    (q : Process n) (hq : R.e.Honest q) :
    C q (t + 3 * R.tv.δ + (X : ℝ) * (3 * R.tv.Δ + R.tv.δ)) := by
  have h := confirm_by R C mono bridge (t + (X : ℝ) * (3 * R.tv.Δ + R.tv.δ)) hB q hq
  have heq : t + (X : ℝ) * (3 * R.tv.Δ + R.tv.δ) + 3 * R.tv.δ
           = t + 3 * R.tv.δ + (X : ℝ) * (3 * R.tv.Δ + R.tv.δ) := by ring
  rwa [heq] at h

/-- **Theorem 3.4 (Expected View-Based Liveness), expectation.** Taking expectations
    over the leader offset `X` in `theorem_3_4_time` and using `E[X] ≤ 1/2`
    (`expectedLeaderOffset_le`, the leader-offset axiom), the expected
    confirmation time after `t` is at most `3.5δ + 1.5∆`:
    `E[3δ + X·(3∆+δ)] = 3δ + E[X]·(3∆+δ) ≤ 3δ + ½·(3∆+δ) = 3.5δ + 1.5∆`. -/
theorem theorem_3_4_expected (δ Δ : ℝ) (hδ : 0 ≤ δ) (hΔ : 0 ≤ Δ) :
    3 * δ + expectedLeaderOffset * (3 * Δ + δ) ≤ 3.5 * δ + 1.5 * Δ := by
  have hkey : expectedLeaderOffset * (3 * Δ + δ) ≤ (1 / 2) * (3 * Δ + δ) :=
    mul_le_mul_of_nonneg_right expectedLeaderOffset_le (by linarith)
  have hexp : (1 / 2) * (3 * Δ + δ) = 1.5 * Δ + 0.5 * δ := by ring
  linarith [hkey, hexp]

end Simplex

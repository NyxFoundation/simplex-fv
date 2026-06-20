import Simplex.Liveness.Lemma3_5
import Simplex.Axioms
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

variable {n : Nat}

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

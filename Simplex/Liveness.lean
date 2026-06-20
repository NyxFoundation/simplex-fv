import Simplex.Timing
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace Simplex

/-- **Lemma 3.4 (Synchronized Iterations).** If some honest process `p` has entered
    iteration `h+1` by time `t`, then every honest process has entered iteration
    `h+1` by time `max(GST, t+δ)`. (Iterations are ≥ 1, so "iteration `h`" with
    `h ≥ 1` is written `h+1`, and "a notarized blockchain of height `h−1`" becomes
    "a notarized blockchain of height `h`".)

    Proof (the paper's): `p` having entered iteration `h+1` means it saw a notarized
    height-`h` chain by `t` (`entered_saw`); `p` multicasts that view, so by
    `δ`-bounded delivery after GST every honest process has seen a notarized
    height-`h` chain by `max(GST, t+δ)` (`relay`); seeing it, each honest process
    enters iteration `h+1` by then (`saw_entered`). Deterministic; no axiom, no
    `sorry`. -/
theorem lemma_3_4 {n : Nat} (tv : TimingView n) (e : Execution n) (laws : tv.Laws e)
    (h : Nat) (t : ℝ) (p : Process n) (hp : e.Honest p)
    (hentered : tv.EnteredBy p (h + 1) t)
    (q : Process n) (hq : e.Honest q) :
    tv.EnteredBy q (h + 1) (max tv.GST (t + tv.δ)) :=
  laws.saw_entered q h _ hq
    (laws.relay p q h t hp hq (laws.entered_saw p h t hp hentered))

/-- **Lemma 3.6 (The Effect of Faulty Leaders).** If every honest process has entered
    iteration `h` by some time `t > GST`, then every honest process will have entered
    iteration `h+1` by time `t + 3∆ + δ`.

    Proof (the paper's two cases, with the delivery/notarization content of Case 1
    folded into the case hypothesis `hcase`, mirroring how Lemma 3.5's subclaims are
    threaded):
    - **Case 1** — every honest timer in iteration `h` fires: each honest process
      casts `⟨vote, h, ⊥_h⟩` by `≤ t+3∆`, which is in every honest view by
      `max(GST, t+3∆+δ) = t+3∆+δ`; these votes notarize `⊥_h`, so every honest
      process has seen a notarized height-`h` chain by `t+3∆+δ`
      (`tv.SawNotar q h (t+3∆+δ)`) and enters `h+1` by then (`saw_entered`).
    - **Case 2** — some honest `p`'s iteration-`h` timer does not fire: then `p`
      entered `h+1` before its timer could fire, i.e. by `t+3∆`; Lemma 3.4
      (`lemma_3_4`) propagates this to every honest process by `max(GST, t+3∆+δ)`,
      which collapses to `t+3∆+δ` because `t > GST` and `δ, ∆ ≥ 0`.
    Deterministic; no axiom, no `sorry`. -/
theorem lemma_3_6 {n : Nat} (tv : TimingView n) (e : Execution n) (laws : tv.Laws e)
    (h : Nat) (t : ℝ) (hGST : tv.GST < t) (hΔ : 0 ≤ tv.Δ) (hδ : 0 ≤ tv.δ)
    (hcase : (∀ q, e.Honest q → tv.SawNotar q h (t + 3 * tv.Δ + tv.δ)) ∨
             (∃ p, e.Honest p ∧ tv.EnteredBy p (h + 1) (t + 3 * tv.Δ)))
    (q : Process n) (hq : e.Honest q) :
    tv.EnteredBy q (h + 1) (t + 3 * tv.Δ + tv.δ) := by
  rcases hcase with hall | ⟨p, hp, hpenter⟩
  · exact laws.saw_entered q h _ hq (hall q hq)
  · have hstep := lemma_3_4 tv e laws h (t + 3 * tv.Δ) p hp hpenter q hq
    have hle : tv.GST ≤ t + 3 * tv.Δ + tv.δ := by linarith
    rwa [max_eq_right hle] at hstep

/-- **Iterating Lemma 3.6 over `k` faulty-leader iterations.** If every honest process
    is in iteration `h` by time `t > GST`, and at each of the next `k` iterations the
    Lemma 3.6 case split holds (`advance`), then every honest process has entered
    iteration `h+k` by time `t + k·(3∆+δ)`. Pure induction on `k`, each step invoking
    `lemma_3_6`; this is the deterministic backbone of Theorem 3.3's
    `4δ + k·(3∆+δ)` worst-case bound. -/
theorem faulty_iterations_advance {n : Nat} (tv : TimingView n) (e : Execution n)
    (laws : tv.Laws e) (hΔ : 0 ≤ tv.Δ) (hδ : 0 ≤ tv.δ) (h : Nat) (t : ℝ)
    (hGST : tv.GST < t)
    (advance : ∀ (j : Nat) (s : ℝ), tv.GST < s →
        (∀ q, e.Honest q → tv.EnteredBy q (h + j) s) →
        (∀ q, e.Honest q → tv.SawNotar q (h + j) (s + 3 * tv.Δ + tv.δ)) ∨
        (∃ p, e.Honest p ∧ tv.EnteredBy p (h + j + 1) (s + 3 * tv.Δ))) :
    ∀ (k : Nat), (∀ q, e.Honest q → tv.EnteredBy q h t) →
      ∀ q, e.Honest q → tv.EnteredBy q (h + k) (t + (k : ℝ) * (3 * tv.Δ + tv.δ)) := by
  intro k
  induction k with
  | zero => intro hbase q hq; simpa using hbase q hq
  | succ k ih =>
    intro hbase q hq
    have hk := ih hbase
    have hnn : (0 : ℝ) ≤ (k : ℝ) * (3 * tv.Δ + tv.δ) :=
      mul_nonneg (Nat.cast_nonneg k) (by linarith)
    have hsk : tv.GST < t + (k : ℝ) * (3 * tv.Δ + tv.δ) := by linarith
    have hc := advance k (t + (k : ℝ) * (3 * tv.Δ + tv.δ)) hsk hk
    have hstep := lemma_3_6 tv e laws (h + k) (t + (k : ℝ) * (3 * tv.Δ + tv.δ)) hsk hΔ hδ hc q hq
    have heq : t + (k : ℝ) * (3 * tv.Δ + tv.δ) + 3 * tv.Δ + tv.δ
             = t + ((k + 1 : Nat) : ℝ) * (3 * tv.Δ + tv.δ) := by
      rw [Nat.cast_succ]; ring
    rwa [heq] at hstep

end Simplex

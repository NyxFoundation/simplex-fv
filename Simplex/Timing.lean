import Simplex.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

namespace Simplex

/-- **Abstract partial-synchrony timing model** for the liveness line (Barrier 5).
    Time is `ℝ`; `GST`, `δ`, `Δ` are the network parameters with `δ < Δ` (the
    standing partial-synchrony assumption, in force after GST). `EnteredBy p h t`
    and `SawNotar p k t` are the protocol's timing predicates, modeled abstractly —
    an operational state machine can later *construct* a `TimingView` without
    changing any theorem statement. -/
structure TimingView (n : Nat) where
  GST : ℝ
  δ   : ℝ
  Δ   : ℝ
  δ_lt_Δ : δ < Δ
  /-- `p` has entered iteration `h` by time `t`. -/
  EnteredBy : Process n → Nat → ℝ → Prop
  /-- `p` has seen a notarized blockchain of height `k` by time `t`. -/
  SawNotar  : Process n → Nat → ℝ → Prop

namespace TimingView

variable {n : Nat}

/-- Deterministic protocol/delivery laws for the timing model (Barrier 5), threaded
    as a hypothesis bundle (provable in a concrete operational model):
    - `entered_saw`: an honest process enters iteration `h+1` only after seeing a
      notarized height-`h` chain (the paper's "must have seen a notarized
      blockchain of height `h−1`");
    - `relay`: `δ`-bounded delivery after GST — on entering an iteration an honest
      process multicasts its notarized view, so every honest process has seen a
      notarized height-`k` chain by `max(GST, t+δ)`;
    - `saw_entered`: seeing a notarized height-`h` chain makes an honest process
      enter iteration `h+1` by then (it increments its iteration number until it
      reaches that iteration). -/
structure Laws (tv : TimingView n) (e : Execution n) : Prop where
  entered_saw : ∀ p h t, e.Honest p → tv.EnteredBy p (h + 1) t → tv.SawNotar p h t
  relay       : ∀ p q k t, e.Honest p → e.Honest q → tv.SawNotar p k t →
                  tv.SawNotar q k (max tv.GST (t + tv.δ))
  saw_entered : ∀ q h t, e.Honest q → tv.SawNotar q h t → tv.EnteredBy q (h + 1) t

end TimingView

end Simplex

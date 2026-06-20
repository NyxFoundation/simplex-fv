import Simplex.Liveness.Basic
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

end Simplex

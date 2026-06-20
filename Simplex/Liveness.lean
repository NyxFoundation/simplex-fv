import Simplex.Liveness.Basic
import Simplex.Liveness.Lemma3_4
import Simplex.Liveness.Lemma3_5
import Simplex.Liveness.Lemma3_6
import Simplex.Liveness.Theorem3_2
import Simplex.Liveness.Theorem3_3
import Simplex.Liveness.Theorem3_4

/-!
# Liveness and confirmation time

Timing inequalities over `GST`, `δ`, `Δ` (with `δ < Δ`) plus elementary
leader-rotation bounds.

* `Simplex.Liveness.Basic` — the abstract partial-synchrony timing model.
* `Simplex.Liveness.Lemma3_4` — synchronized iterations.
* `Simplex.Liveness.Lemma3_5` — the honest-leader round and the `confirm_by` bridge.
* `Simplex.Liveness.Lemma3_6` — the effect of faulty leaders (and its `k`-fold iteration).
* `Simplex.Liveness.Theorem3_2` — optimistic confirmation time `5δ`.
* `Simplex.Liveness.Theorem3_3` — worst-case confirmation time `4δ + k·(3∆+δ)`.
* `Simplex.Liveness.Theorem3_4` — expected confirmation time `3.5δ + 1.5∆`.
-/

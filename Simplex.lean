import Simplex.Basic
import Simplex.Protocol
import Simplex.Axioms
import Simplex.Safety
import Simplex.Liveness
import Simplex.Complexity
import Simplex.Capstone

/-!
# Simplex

Machine-checked formalization of the *Simplex* consensus protocol
(Chan & Pass, IACR ePrint 2023/463). See `README.md` for the proof discipline
(`axiom` / hypothesis threading, never `sorry`) and the dependency graph.

* `Simplex.Basic` — core types: processes, blocks, messages, the `⌈2n/3⌉` quorum
  threshold, the abstract `Execution`.
* `Simplex.Protocol` — the abstract `ChainView` interface (notarization/finalization).
* `Simplex.Axioms` — idealized crypto and leader-randomness axioms.
* `Simplex.Safety` — consistency: Lemma 3.1–3.3 and Theorem 3.1.
* `Simplex.Liveness` — confirmation time: Lemma 3.4–3.6 and Theorem 3.2–3.4.
* `Simplex.Complexity` — communication complexity: Lemma 3.7.
* `Simplex.Capstone` — Theorem 2.1, the conjunction of the three guarantees.
-/

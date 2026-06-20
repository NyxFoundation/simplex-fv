import Simplex.Safety.QuorumIntersection
import Simplex.Safety.Lemma3_1
import Simplex.Safety.Lemma3_2
import Simplex.Safety.Lemma3_3
import Simplex.Safety.Theorem3_1

/-!
# Safety (consistency)

The entire safety argument is one quorum-intersection lemma applied twice.

* `Simplex.Safety.QuorumIntersection` — any two `⌈2n/3⌉`-quorums share an honest
  process (pure `Finset` combinatorics, no axiom).
* `Simplex.Safety.Lemma3_1` — signatures seen in honest view were actually signed.
* `Simplex.Safety.Lemma3_2` — no two distinct non-dummy blocks notarized at one height.
* `Simplex.Safety.Lemma3_3` — a finalized height has no notarized dummy block.
* `Simplex.Safety.Theorem3_1` — consistency: honest outputs are prefix-comparable.
-/

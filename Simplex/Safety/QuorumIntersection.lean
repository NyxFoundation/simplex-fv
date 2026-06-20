import Simplex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace Simplex

/-- **Quorum intersection (the deterministic safety core).** With fewer than
    `n/3` corrupt processes (`3*f < n`), any two `⌈2n/3⌉`-quorums share an honest
    process. Pure finite combinatorics over `Finset` cardinalities — no axiom, no
    crypto. Reused by both safety lemmas (3.2 and 3.3).

    Proof: if the intersection contained no honest process it would sit inside the
    corrupt set, so `|Q₁ ∩ Q₂| ≤ f`; but inclusion–exclusion with `|Q₁ ∪ Q₂| ≤ n`
    forces `|Q₁ ∩ Q₂| ≥ 2⌈2n/3⌉ − n > f`, a contradiction (the threshold
    arithmetic, including the `⌈·⌉` rounding, is discharged by `omega`). -/
theorem quorum_intersect_honest {n f : Nat} (hf : 3 * f < n)
    (Q₁ Q₂ honest : Finset (Process n))
    (h₁ : quorumThreshold n ≤ Q₁.card) (h₂ : quorumThreshold n ≤ Q₂.card)
    (hc : honestᶜ.card ≤ f) :
    ∃ p, p ∈ Q₁ ∩ Q₂ ∧ p ∈ honest := by
  by_contra hcon
  push Not at hcon
  -- No honest process in the intersection ⇒ the intersection is corrupt.
  have hsub : Q₁ ∩ Q₂ ⊆ honestᶜ := by
    intro p hp
    exact Finset.mem_compl.2 (hcon p hp)
  have hinter : (Q₁ ∩ Q₂).card ≤ f :=
    le_trans (Finset.card_le_card hsub) hc
  -- The union fits inside the `n` processes.
  have hunion : (Q₁ ∪ Q₂).card ≤ n := by
    have : (Q₁ ∪ Q₂).card ≤ (Finset.univ : Finset (Process n)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    simpa [Finset.card_fin] using this
  -- Inclusion–exclusion, then close by threshold arithmetic.
  have hie : (Q₁ ∪ Q₂).card + (Q₁ ∩ Q₂).card = Q₁.card + Q₂.card :=
    Finset.card_union_add_card_inter Q₁ Q₂
  simp only [quorumThreshold] at h₁ h₂
  omega

end Simplex

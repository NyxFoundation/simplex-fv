import Simplex.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace Simplex

/-- **Abstract per-iteration multicast model for Lemma 3.7** (Barrier 4: the protocol
    mechanics are an interface, not implemented operationally). `multicast p h` is the
    finite set of messages an honest process `p` multicasts during iteration `h`, and
    `category` classifies each message into one of the four per-iteration kinds:

    - `0` — the propose message;
    - `1` — the vote for a non-`⊥` block;
    - `2` — one of `⟨vote, h, ⊥_h⟩` / `⟨finalize, h⟩`;
    - `3` — the relay of a notarized height-`h` blockchain.

    A concrete operational model can later *construct* a `MessageComplexity` without
    changing the theorem statement. -/
structure MessageComplexity (n : Nat) where
  /-- Messages honest process `p` multicasts during iteration `h`. -/
  multicast : Process n → Nat → Finset Message
  /-- Classifies each message into one of the four per-iteration categories. -/
  category  : Message → Fin 4

namespace MessageComplexity

variable {n : Nat}

/-- Protocol multicast law (Barrier 4, abstract): in each iteration an honest process
    multicasts **at most one** message in each of the four categories — at most one
    propose, at most one non-`⊥` vote, at most one of the dummy-vote/finalize pair,
    and at most one notarized-chain relay (the paper's per-iteration enumeration). -/
structure Laws (mc : MessageComplexity n) (e : Execution n) : Prop where
  at_most_one : ∀ (p : Process n) (h : Nat) (c : Fin 4), e.Honest p →
    ((mc.multicast p h).filter (fun m => mc.category m = c)).card ≤ 1

/-- **Lemma 3.7 (Message complexity).** In each iteration `h`, an honest process
    multicasts at most 4 messages. The multicast set partitions, by `category`, into
    the four fibers each of cardinality `≤ 1` (`at_most_one`); summing the four
    bounds over `Fin 4` gives `≤ 4`. Deterministic; no axiom, no `sorry`. -/
theorem lemma_3_7 (mc : MessageComplexity n) (e : Execution n) (laws : mc.Laws e)
    (p : Process n) (h : Nat) (hp : e.Honest p) :
    (mc.multicast p h).card ≤ 4 := by
  have hpart := Finset.card_eq_sum_card_fiberwise
    (s := mc.multicast p h) (t := (Finset.univ : Finset (Fin 4)))
    (f := mc.category) (fun x _ => Finset.mem_univ (mc.category x))
  rw [hpart]
  calc ∑ c : Fin 4, ((mc.multicast p h).filter (fun m => mc.category m = c)).card
      ≤ ∑ _c : Fin 4, 1 := Finset.sum_le_sum (fun c _ => laws.at_most_one p h c hp)
    _ = 4 := by simp

end MessageComplexity

end Simplex

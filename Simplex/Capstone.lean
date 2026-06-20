import Simplex.Safety
import Simplex.Confirmation
import Simplex.Complexity

set_option autoImplicit false

namespace Simplex

/-- **Theorem 2.1 (Partially-synchronous Consensus).** The paper's capstone summary:
    assuming the crypto building blocks (collision-resistant hashes, signatures, a PRF,
    a bare PKI, and a CRS — the project-wide axioms in `Simplex/Axioms.lean`), Simplex
    is a partially-synchronous protocol for `f < n/3` static corruptions
    (`hf : 3*f < n`) enjoying, over one valid execution `e`, all four guarantees at
    once. It has **no separate proof**: it is exactly the conjunction of

    1. **safety** — consistency (Theorem 3.1, `theorem_3_1_consistency`): any two honest
       outputs are prefix-comparable;
    2. **optimistic liveness** — `5δ` confirmation (Theorem 3.2, `theorem_3_2`);
    3. **worst-case liveness** — `4δ + k·(3∆+δ)` confirmation with `k = ω(log λ)`
       (Theorem 3.3 deterministic core, `theorem_3_3_time`);
    4. **expected liveness** — `3.5δ + 1.5∆` (Theorem 3.4, `theorem_3_4_expected`);
    5. **`O(n)` multicast complexity** — `≤ 4` multicasts per honest process per
       iteration (Lemma 3.7, `MessageComplexity.lemma_3_7`).

    The safety context (`cv`, `e`, the quorum/honesty parameters, `cv.Laws`) is shared;
    the liveness guarantees quantify over their own honest-leader-round scenarios `R`
    and the complexity guarantee over the multicast model `mc` for the same `e`. No
    `sorry`; the axioms reached are the crypto ones (`signature_unforgeable`,
    `collision_resistant`) and the leader-randomness ones
    (`consecutiveCorruptProb_bound`, `expectedLeaderOffset_le`). -/
theorem theorem_2_1 {n f : Nat} (cv : ChainView n) (e : Execution n)
    (hvalid : ValidExecution e) (hf : 3 * f < n)
    (honest : Finset (Process n)) (hHonest : ∀ p, p ∈ honest ↔ e.Honest p)
    (hcorrupt : honestᶜ.card ≤ f) (cvLaws : cv.Laws e) :
    -- 1. Safety: consistency of honest outputs.
    (∀ (top top' : Block),
        cv.Finalized e (cv.height top) → cv.Finalized e (cv.height top') →
        cv.Notarized e top → cv.Notarized e top' →
        LogPrefix (cv.logOf top) (cv.logOf top') ∨ LogPrefix (cv.logOf top') (cv.logOf top))
    -- 2. Optimistic confirmation time 5δ.
    ∧ (∀ (R : HonestLeaderRound n) (C : Process n → ℝ → Prop),
        (∀ q s s', s ≤ s' → C q s → C q s') →
        (∀ q, R.e.Honest q →
            R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ)) →
        ∀ (t : ℝ), R.t ≤ t + 2 * R.tv.δ → ∀ q, R.e.Honest q → C q (t + 5 * R.tv.δ))
    -- 3. Worst-case confirmation time 4δ + k·(3∆+δ).
    ∧ (∀ (R : HonestLeaderRound n) (C : Process n → ℝ → Prop),
        (∀ q s s', s ≤ s' → C q s → C q s') →
        (∀ q, R.e.Honest q →
            R.SawFinalized q R.h (R.t + 3 * R.tv.δ) → C q (R.t + 3 * R.tv.δ)) →
        ∀ (t : ℝ) (k : Nat), R.t ≤ t + R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ) →
        ∀ q, R.e.Honest q → C q (t + 4 * R.tv.δ + (k : ℝ) * (3 * R.tv.Δ + R.tv.δ)))
    -- 4. Expected view-based liveness 3.5δ + 1.5∆.
    ∧ (∀ (δ Δ : ℝ), 0 ≤ δ → 0 ≤ Δ →
        3 * δ + expectedLeaderOffset * (3 * Δ + δ) ≤ 3.5 * δ + 1.5 * Δ)
    -- 5. Communication complexity ≤ 4 multicasts / honest process / iteration.
    ∧ (∀ (mc : MessageComplexity n), mc.Laws e → ∀ (p : Process n) (h : Nat),
        e.Honest p → (mc.multicast p h).card ≤ 4) :=
  ⟨ fun top top' hfin hfin' hnotar hnotar' =>
      theorem_3_1_consistency cv e hvalid hf honest hHonest hcorrupt cvLaws
        top top' hfin hfin' hnotar hnotar',
    fun R C mono bridge t hB q hq => theorem_3_2 R C mono bridge t hB q hq,
    fun R C mono bridge t k hB q hq => theorem_3_3_time R C mono bridge t k hB q hq,
    fun δ Δ hδ hΔ => theorem_3_4_expected δ Δ hδ hΔ,
    fun mc mcLaws p h hp => MessageComplexity.lemma_3_7 mc e mcLaws p h hp ⟩

end Simplex

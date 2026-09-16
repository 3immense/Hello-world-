import Std

/-!
JSP-000301

Formalization of the known counterexample to the assertion that whenever two
consecutive positive integers are powerful, at least one of them is a square.

Witnesses: 12167 and 12168.

This file intentionally uses only Lean's bundled `Std` library. The finite
checks are kernel-evaluated with `decide +kernel`; there are no `sorry`,
`admit`, custom axioms, or `native_decide` calls.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

namespace JSP000301

/-- Elementary divisor characterization of primality. -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A positive natural number is powerful iff the square of every prime divisor divides it. -/
def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, Prime p → p ∣ n → p * p ∣ n

/-- A natural number is a perfect square. -/
def Square (n : Nat) : Prop := ∃ k : Nat, n = k * k

/-- It is enough to check candidate prime divisors up to `n`, since every
positive divisor of `n` is at most `n`. -/
theorem powerful_of_bounded_check (n : Nat) (hn : 0 < n)
    (hcheck : ∀ p : Fin (n + 1),
      Prime p.val → p.val ∣ n → p.val * p.val ∣ n) : Powerful n := by
  constructor
  · exact hn
  · intro p hp hpn
    have hle : p ≤ n := Nat.le_of_dvd hn hpn
    exact hcheck ⟨p, by omega⟩ hp hpn

/-- `12167 = 23^3` is powerful. Lean checks every possible prime divisor. -/
theorem powerful_12167 : Powerful 12167 := by
  apply powerful_of_bounded_check 12167 (by decide)
  decide +kernel

/-- `12168 = 2^3 * 3^2 * 13^2` is powerful. -/
theorem powerful_12168 : Powerful 12168 := by
  apply powerful_of_bounded_check 12168 (by decide)
  decide +kernel

/-- No number strictly between `110^2 = 12100` and `111^2 = 12321` can be a perfect square. -/
theorem not_square_between_110_111 (n : Nat)
    (hlo : 12100 < n) (hhi : n < 12321) : ¬ Square n := by
  rintro ⟨k, hk⟩
  by_cases hk110 : k ≤ 110
  · have hsquare : k * k ≤ 110 * 110 := Nat.mul_le_mul hk110 hk110
    omega
  · have hk111 : 111 ≤ k := by omega
    have hsquare : 111 * 111 ≤ k * k := Nat.mul_le_mul hk111 hk111
    omega

/-- The explicit pair `(12167,12168)` is a counterexample. -/
theorem counterexample :
    ∃ n : Nat,
      Powerful n ∧ Powerful (n + 1) ∧ ¬ Square n ∧ ¬ Square (n + 1) := by
  refine ⟨12167, powerful_12167, ?_, ?_, ?_⟩
  · simpa using powerful_12168
  · exact not_square_between_110_111 12167 (by decide) (by decide)
  · simpa using not_square_between_110_111 12168 (by decide) (by decide)

/-- Therefore the universal assertion in JSP-000301 is false. -/
theorem original_claim_false :
    ¬ (∀ n : Nat,
      Powerful n → Powerful (n + 1) → Square n ∨ Square (n + 1)) := by
  intro h
  obtain ⟨n, hn, hn1, hns, hn1s⟩ := counterexample
  rcases h n hn hn1 with hs | hs
  · exact hns hs
  · exact hn1s hs

#print axioms counterexample
#print axioms original_claim_false

end JSP000301

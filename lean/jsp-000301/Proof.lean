import Std

/-!
JSP-000301

Formalization of the known counterexample to the assertion that whenever two
consecutive positive integers are powerful, at least one of them is a square.
Witnesses: 12167 and 12168.

Only Lean's bundled `Std` library is used. Finite certificates are checked by
Lean's kernel via `decide +kernel`. There are no `sorry`, `admit`, custom axioms,
or `native_decide` calls.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JSP000301

/-- Elementary divisor characterization of a prime natural number. -/
def Prime (p : Nat) : Prop :=
  2 ≤ p ∧ ∀ d : Nat, d ∣ p → d = 1 ∨ d = p

/-- A positive integer is powerful if the square of each prime divisor divides it. -/
def Powerful (n : Nat) : Prop :=
  0 < n ∧ ∀ p : Nat, Prime p → p ∣ n → p * p ∣ n

/-- A natural number is a perfect square. -/
def Square (n : Nat) : Prop := ∃ k : Nat, n = k * k

/-- Every divisor of 12167 is among 1, 23, 529, 12167.
The pair `(a,b)` encodes `128*a+b`; 96*128 > 12167. -/
theorem divisors_12167 :
    ∀ a : Fin 96, ∀ b : Fin 128,
      let d := 128 * a.val + b.val
      d ∣ 12167 → d = 1 ∨ d = 23 ∨ d = 529 ∨ d = 12167 := by
  decide +kernel

/-- For every divisor `d` of 12168 in the same finite range, either `d²` divides
12168 already, or `d` has a proper divisor below 14. The latter alternative is
incompatible with `d` being prime. -/
theorem divisors_12168 :
    ∀ a : Fin 96, ∀ b : Fin 128,
      let d := 128 * a.val + b.val
      d ∣ 12168 → (d * d ∣ 12168) ∨
      (∃ q : Fin 14, q.val ∣ d ∧ q.val ≠ 1 ∧ q.val ≠ d) := by
  decide +kernel

theorem powerful_12167 : Powerful 12167 := by
  constructor
  · decide
  intro p hp hdiv
  have hbound : p < 12168 := by
    have := Nat.le_of_dvd (by decide : 0 < 12167) hdiv
    omega
  have ha : p / 128 < 96 := by omega
  have hb : p % 128 < 128 := Nat.mod_lt p (by decide)
  have heq : 128 * (p / 128) + p % 128 = p := by omega
  have hc := divisors_12167 ⟨p / 128, ha⟩ ⟨p % 128, hb⟩
  simp only at hc
  rw [heq] at hc
  have cases := hc hdiv
  rcases cases with h | h | h | h
  · have := hp.1; omega
  · subst p; decide
  · subst p
    have := hp.2 23 (by decide)
    omega
  · subst p
    have := hp.2 23 (by decide)
    omega

theorem powerful_12168 : Powerful 12168 := by
  constructor
  · decide
  intro p hp hdiv
  have hbound : p < 12169 := by
    have := Nat.le_of_dvd (by decide : 0 < 12168) hdiv
    omega
  have ha : p / 128 < 96 := by omega
  have hb : p % 128 < 128 := Nat.mod_lt p (by decide)
  have heq : 128 * (p / 128) + p % 128 = p := by omega
  have hc := divisors_12168 ⟨p / 128, ha⟩ ⟨p % 128, hb⟩
  simp only at hc
  rw [heq] at hc
  rcases hc hdiv with h | ⟨q, hq, h1, hne⟩
  · exact h
  · rcases hp.2 q.val hq with h | h
    · exact False.elim (h1 h)
    · exact False.elim (hne h)

/-- No number strictly between 110² and 111² is a square. -/
theorem not_square_between (n : Nat) (lo : 12100 < n) (hi : n < 12321) :
    ¬ Square n := by
  rintro ⟨k, hk⟩
  by_cases h : k ≤ 110
  · have := Nat.mul_self_le_mul_self h
    omega
  · have h' : 111 ≤ k := by omega
    have := Nat.mul_self_le_mul_self h'
    omega

/-- The explicit pair `(12167,12168)` disproves the catalog assertion. -/
theorem counterexample :
    ∃ n : Nat, Powerful n ∧ Powerful (n + 1) ∧ ¬ Square n ∧ ¬ Square (n + 1) := by
  exact ⟨12167, powerful_12167, powerful_12168,
    not_square_between 12167 (by decide) (by decide),
    not_square_between 12168 (by decide) (by decide)⟩

theorem original_claim_false :
    ¬ (∀ n : Nat, Powerful n → Powerful (n + 1) → Square n ∨ Square (n + 1)) := by
  intro h
  obtain ⟨n, hn, hn1, hns, hn1s⟩ := counterexample
  rcases h n hn hn1 with hs | hs
  · exact hns hs
  · exact hn1s hs

#print axioms counterexample
#print axioms original_claim_false

end JSP000301

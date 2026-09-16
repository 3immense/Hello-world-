import Mathlib

/-!
JSP-000301

Formalization of the known counterexample to the assertion that whenever two
consecutive positive integers are powerful, at least one of them is a square.
Witnesses: 12167 and 12168.

Statement-fidelity choices:
* primality uses Mathlib's `Nat.Prime` directly;
* squareness uses Mathlib's `IsSquare` directly;
* `Powerful` is the only problem-specific predicate, defined by the standard
  divisor characterization `p ∣ n -> p^2 ∣ n` for every prime `p`;
* `powerful_iff_factorization_exponents` proves that this definition is exactly
  equivalent, for positive `n`, to every prime divisor occurring with
  factorization exponent at least two.

Finite arithmetic certificates are checked by Lean's kernel via `decide +kernel`.
There are no `sorry`, `admit`, custom axioms, `native_decide`, or unsafe declarations.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace JSP000301

/-- Standard definition of a positive powerful (squarefull) natural number:
every prime divisor divides to at least the second power. -/
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n

/-- Definition audit: for positive `n`, `Powerful n` is equivalent to saying
that every prime divisor has factorization exponent at least two. -/
theorem powerful_iff_factorization_exponents {n : ℕ} (hn : 0 < n) :
    Powerful n ↔ ∀ p : ℕ, p.Prime → p ∣ n → 2 ≤ n.factorization p := by
  constructor
  · rintro ⟨_, hpow⟩ p hp hpn
    exact (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hn)).mp (hpow p hp hpn)
  · intro hfac
    refine ⟨hn, ?_⟩
    intro p hp hpn
    exact (hp.pow_dvd_iff_le_factorization (Nat.ne_of_gt hn)).mpr (hfac p hp hpn)

/-- Every divisor of 12167 is among 1, 23, 529, 12167.
The pair `(a,b)` encodes `128*a+b`; 96*128 > 12167. -/
theorem divisors_12167 :
    ∀ a : Fin 96, ∀ b : Fin 128,
      let d := 128 * a.val + b.val
      d ∣ 12167 → d = 1 ∨ d = 23 ∨ d = 529 ∨ d = 12167 := by
  decide +kernel

/-- For every divisor `d` of 12168 in the same finite range, either `d^2`
divides 12168 already, or `d` has a proper divisor below 14. A prime divisor
cannot satisfy the latter alternative. -/
theorem divisors_12168 :
    ∀ a : Fin 96, ∀ b : Fin 128,
      let d := 128 * a.val + b.val
      d ∣ 12168 → (d ^ 2 ∣ 12168) ∨
      (∃ q : Fin 14, q.val ∣ d ∧ q.val ≠ 1 ∧ q.val ≠ d) := by
  decide +kernel

theorem powerful_12167 : Powerful 12167 := by
  constructor
  · norm_num
  intro p hp hdiv
  have hbound : p < 12168 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 12167) hdiv
    omega
  have ha : p / 128 < 96 := by omega
  have hb : p % 128 < 128 := Nat.mod_lt p (by norm_num)
  have heq : 128 * (p / 128) + p % 128 = p := by omega
  have hc := divisors_12167 ⟨p / 128, ha⟩ ⟨p % 128, hb⟩
  simp only at hc
  rw [heq] at hc
  rcases hc hdiv with h | h | h | h
  · have hp2 := hp.two_le
    omega
  · subst p
    norm_num
  · subst p
    exact False.elim ((Nat.not_prime_of_dvd_of_ne (by norm_num : 23 ∣ 529)
      (by norm_num) (by norm_num)) hp)
  · subst p
    exact False.elim ((Nat.not_prime_of_dvd_of_ne (by norm_num : 23 ∣ 12167)
      (by norm_num) (by norm_num)) hp)

theorem powerful_12168 : Powerful 12168 := by
  constructor
  · norm_num
  intro p hp hdiv
  have hbound : p < 12169 := by
    have hle := Nat.le_of_dvd (by norm_num : 0 < 12168) hdiv
    omega
  have ha : p / 128 < 96 := by omega
  have hb : p % 128 < 128 := Nat.mod_lt p (by norm_num)
  have heq : 128 * (p / 128) + p % 128 = p := by omega
  have hc := divisors_12168 ⟨p / 128, ha⟩ ⟨p % 128, hb⟩
  simp only at hc
  rw [heq] at hc
  rcases hc hdiv with h | ⟨q, hq, hq1, hqp⟩
  · exact h
  · rcases hp.eq_one_or_self_of_dvd q.val hq with h | h
    · exact False.elim (hq1 h)
    · exact False.elim (hqp h)

/-- No natural number strictly between 110^2 and 111^2 is a square. -/
theorem not_isSquare_between (n : ℕ) (lo : 12100 < n) (hi : n < 12321) :
    ¬ IsSquare n := by
  rintro ⟨k, hk⟩
  by_cases h : k ≤ 110
  · have hsquare : k * k ≤ 110 * 110 := Nat.mul_le_mul h h
    omega
  · have h' : 111 ≤ k := by omega
    have hsquare : 111 * 111 ≤ k * k := Nat.mul_le_mul h' h'
    omega

/-- Exact formalization of the catalog's counterexample statement. -/
theorem counterexample :
    ∃ n : ℕ,
      Powerful n ∧ Powerful (n + 1) ∧ ¬ IsSquare n ∧ ¬ IsSquare (n + 1) := by
  exact ⟨12167, powerful_12167, powerful_12168,
    not_isSquare_between 12167 (by norm_num) (by norm_num),
    not_isSquare_between 12168 (by norm_num) (by norm_num)⟩

/-- Exact negation of the universal yes/no assertion in JSP-000301. -/
theorem original_claim_false :
    ¬ (∀ n : ℕ,
      Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1)) := by
  intro h
  obtain ⟨n, hn, hn1, hns, hn1s⟩ := counterexample
  rcases h n hn hn1 with hs | hs
  · exact hns hs
  · exact hn1s hs

#print axioms powerful_iff_factorization_exponents
#print axioms counterexample
#print axioms original_claim_false

end JSP000301

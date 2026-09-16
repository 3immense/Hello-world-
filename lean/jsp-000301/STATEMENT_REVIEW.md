# JSP-000301 statement fidelity review

## English

### Natural-language source

The formal target is the yes/no assertion recorded as JSP-000301 in the official
problem bank:

> If two consecutive positive integers are powerful, must at least one be a
> perfect square?

The recorded counterexample is 12167 and 12168.

Source: `TheJustinSunPrize/awards`, `problems/catalog-0301-0400.md`, entry
`JSP-000301`.

### Formal statement

The final Lean theorem is:

```lean
theorem original_claim_false :
    ¬ (∀ n : ℕ,
      Powerful n → Powerful (n + 1) → IsSquare n ∨ IsSquare (n + 1))
```

This is the direct negation of the universal yes/no assertion. Positivity is
included in `Powerful`, so the quantification over `n : ℕ` does not introduce
zero as an unintended powerful integer.

### Definitions reviewed

#### `Nat.Prime` — from library

`Nat.Prime` is Mathlib's standard predicate for natural-number primality. No
local replacement definition is used.

#### `IsSquare` — from library

`IsSquare n` is Mathlib's standard multiplicative square predicate
`∃ r, n = r * r`. No local replacement definition is used.

#### `Powerful` — problem-specific definition

```lean
def Powerful (n : ℕ) : Prop :=
  0 < n ∧ ∀ p : ℕ, p.Prime → p ∣ n → p ^ 2 ∣ n
```

This is the standard divisor characterization of a positive powerful/squarefull
integer: every prime divisor occurs with multiplicity at least two.

The Lean theorem

```lean
powerful_iff_factorization_exponents
```

proves, using Mathlib's `Nat.Prime.pow_dvd_iff_le_factorization`, that for
positive `n` this definition is equivalent to

```lean
∀ p : ℕ, p.Prime → p ∣ n → 2 ≤ n.factorization p
```

Thus the problem-specific predicate is tied to Mathlib's prime factorization
infrastructure rather than relying only on an informal definition review.

### Counterexample fidelity

The proof uses exactly the counterexample recorded by the official catalog:

- `12167 = 23^3`;
- `12168 = 2^3 * 3^2 * 13^2`;
- they are consecutive;
- both satisfy `Powerful`;
- both lie strictly between `110^2 = 12100` and `111^2 = 12321`, hence neither
  satisfies `IsSquare`.

The formalization proves only the scoped JSP-000301 yes/no question. It does not
claim to formalize the separate counting question associated with Erdős problem
#365.

### Library pin

The project pins:

- Lean: `v4.34.0`;
- Mathlib tag: `v4.34.0`;
- Mathlib commit: `5ed2965256430c3649e86755f9576b54eca72435`.

### Review boundary

This document is contributor-supplied statement-comparison evidence. It is not
an official equivalence attestation. The Justin Sun Prize repository's own
schema requires authorized statement signatories and substantive independent
review for an official verification record; those roles must not be fabricated
by the contributor.

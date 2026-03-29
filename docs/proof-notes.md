# Proof Notes: Erdős–Turán Sidon Set Construction

This document gives an extended commentary on the Lean 4 proof in
`ErdosTuranSidon/Basic.lean`, explaining each tactic choice and the
mathematical content behind it.

---

## Overview

The proof of `erdosTuranSet_sidon` is a formalization of a standard argument
from additive combinatorics. What makes it non-trivial to machine-check is the
need to coordinate three different arithmetic "layers":

1. **Natural number arithmetic** — element membership, bounds, injectivity
2. **Integer arithmetic** — signed differences of indices (since `i₁ - i₃` can
   be negative over ℕ)
3. **Modular arithmetic (`ZMod p`)** — the prime-field argument

Lean 4 requires being explicit about which layer you are working in at each
point, and coercions between layers are not always automatic.

---

## `erdosTuranFn_injective`

```lean
lemma erdosTuranFn_injective (p : ℕ) (hp : p ≥ 3) :
    ∀ i < p, ∀ j < p, erdosTuranFn p i = erdosTuranFn p j → i = j
```

**Mathematical content.** If `2pi + (i² mod p) = 2pj + (j² mod p)` then
reducing mod `p` gives `i² ≡ j² (mod p)`, and reducing mod `2p` (using that
the residues are in `[0, p)`) gives `i = j`.

**Tactic explanation.** The proof applies `congr_arg (· % p)` to extract the
congruence, then uses `norm_num` with `Nat.mod_eq_of_lt` (since `i, j < p`) to
simplify, and `aesop` to close the goal. This is a case where the modular
arithmetic is simple enough that `norm_num` + `aesop` suffices.

---

## `erdosTuranSet_card`

```lean
lemma erdosTuranSet_card (p : ℕ) (hp : p ≥ 3) :
    (erdosTuranSet p).card = p
```

**Mathematical content.** The set `E_p` is the image of `{0, …, p-1}` under
an injective function, so its cardinality equals `p`.

**Tactic explanation.** `Finset.card_image_of_injOn` reduces the goal to
injectivity on the domain, which is exactly `erdosTuranFn_injective`. The
`|>.trans (by simp)` chain handles the `card (range p) = p` computation.

---

## `erdosTuranSet_bound`

```lean
lemma erdosTuranSet_bound (p : ℕ) (n : ℕ) (hn : n ∈ erdosTuranSet p) :
    n < 2 * p ^ 2
```

**Mathematical content.** For `i < p`, we have
`2pi + (i² mod p) < 2pi + p ≤ 2p(p-1) + p = 2p² - p < 2p²`.

**Tactic explanation.** After extracting the index `i` via `Finset.mem_image`,
`nlinarith` handles the nonlinear arithmetic with the hints `i < p` and
`i² mod p < p` (the latter via `Nat.mod_lt`).

---

## `erdosTuranSet_sidon` — main proof

```lean
set_option maxHeartbeats 800000 in
lemma erdosTuranSet_sidon (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    IsSidonSet (↑(erdosTuranSet p) : Set ℕ)
```

### Index extraction

```lean
obtain ⟨i1, hi1⟩ : ∃ i1 < p, a = 2 * p * i1 + (i1 ^ 2 % p) := by
  unfold erdosTuranSet at ha; aesop
```

Each of the four hypotheses `a ∈ E_p`, `b ∈ E_p`, etc. is unfolded to extract
a witness index `i₁, i₂, i₃, i₄ ∈ [0, p)` together with the explicit formula.
`aesop` handles the `Finset.mem_image` unfolding.

### Step 1: `i₁ + i₂ = i₃ + i₄`

```lean
have h_eq : 2 * p * (i1 + i2 - i3 - i4 : ℤ) =
    (i3 ^ 2 % p + i4 ^ 2 % p) - (i1 ^ 2 % p + i2 ^ 2 % p) := by linarith
```

Working over `ℤ` (to allow signed differences), we observe that `a + b = c + d`
forces the right-hand side — the difference of residues — to equal a multiple
of `2p`. But residues are in `[0, p)`, so the RHS is strictly between `-2p`
and `2p`. Hence the multiple is zero, giving `i₁ + i₂ = i₃ + i₄`.

The `by_contra` + `nlinarith` block makes this precise: if the sum-of-indices
were unequal, the multiple of `2p` would have absolute value `≥ 2p`, which
contradicts the residue bounds supplied as `nlinarith` hints via
`Int.emod_nonneg` and `Int.emod_lt_of_pos`.

Note: the proof works over `ℤ` because `ℕ` subtraction is truncated and
cannot represent the argument cleanly.

### Step 2: Quadratic congruence

```lean
have h_mod : 2 * (i1 - i3 : ℤ) * (i3 - i2 : ℤ) ≡ 0 [ZMOD p]
```

From Step 1 we know `i₄ = i₁ + i₂ - i₃`. Substituting into the residue
equality `i₁² + i₂² ≡ i₃² + i₄² (mod p)` and factoring:

```
i₁² + i₂² - i₃² - (i₁ + i₂ - i₃)²
= i₁² + i₂² - i₃² - i₁² - i₂² - i₃² - 2i₁i₂ + 2i₁i₃ + 2i₂i₃
= 2i₃(i₁ + i₂ - i₃) - 2i₁i₂
= 2(i₁ - i₃)(i₃ - i₂)
```

So `2(i₁ - i₃)(i₃ - i₂) ≡ 0 (mod p)`.

In Lean, this is proved by establishing the modular congruence of squares
via `Nat.ModEq` and then converting to `Int.dvd` via
`Int.modEq_zero_iff_dvd`.

### Step 3: Prime field argument

```lean
by_cases h_cases : (i1 - i3 : ℤ) ≡ 0 [ZMOD p] ∨ (i3 - i2 : ℤ) ≡ 0 [ZMOD p]
```

Since `p` is an odd prime and `2 ≢ 0 (mod p)`, the product
`(i₁ - i₃)(i₃ - i₂) ≡ 0 (mod p)` implies one factor is zero mod `p`.
The two cases are handled separately.

**Case: `i₁ ≡ i₃ (mod p)`.** Since `0 ≤ i₁, i₃ < p`, this means `i₁ = i₃`
(the only multiple of `p` in `(-p, p)` is `0`). Then `i₂ = i₄` from Step 1,
giving the first Sidon alternative `a = c, b = d`.

**Case: `i₃ ≡ i₂ (mod p)`.** Similarly gives `i₂ = i₃`, then `i₁ = i₄`,
giving the second alternative `a = d, b = c`.

The `rcases lt_trichotomy k 0` splits are needed because `Int.modEq_zero_iff_dvd`
gives `p ∣ (difference)` as `∃ k, difference = p * k`, and `k` could be
negative, zero, or positive; only `k = 0` is consistent with the index bounds.

**The `h_cases = False` branch.** When neither factor is zero mod `p`, the
proof uses:

```lean
haveI := Fact.mk hp
simp_all +decide [← ZMod.intCast_eq_intCast_iff]
rcases p with (_ | _ | _ | p) <;> cases h_mod <;> contradiction
```

`Fact.mk hp` makes `p` a prime available as a type class instance for `ZMod`
theorems. The `ZMod.intCast_eq_intCast_iff` rewrite converts the `¬ ≡ 0`
hypotheses into statements about `ZMod p`. The structural case split on `p`
(matching `0 | 1 | 2 | p+3`) discharges `p < 3` before the general odd-prime
reasoning, which then derives a contradiction from `h_mod` (the product being
zero) and the two non-zero-factor hypotheses.

---

## On `maxHeartbeats 800000`

The `nlinarith` calls in Step 1 need to reason about eight bounds
simultaneously (lower and upper bounds on four modular remainders). `nlinarith`
works by summing products of hypotheses to find a contradiction, and the search
space grows with the number of hypotheses. The increased heartbeat limit is
expected and does not indicate a fragile proof — the same argument would work
at lower limits with more manual unfolding of the bounds.

# Erdős–Turán Sidon Set Construction — Lean 4 Formalization

A machine-checked proof of the classical Erdős–Turán construction of finite Sidon sets from quadratic residues, formalized in Lean 4 with Mathlib4.

## The Result

A Sidon set (or B₂ set) is a set of natural numbers in which all pairwise sums `a + b` are distinct — equivalently, the equation `a + b = c + d` has no solutions with `{a, b} ≠ {c, d}` as multisets.

The central theorem of this repository is:

> **Theorem** (`erdosTuranSet_sidon`). For every prime `p ≥ 3`, the set
>
> $$E_p = \{ \, 2pi + (i^2 \bmod p) \mid 0 \le i < p \, \}$$
>
> is a Sidon set of size `p` contained in `[0, 2p²)`.

This formalizes the algebraic construction introduced by Erdős and Turán in their 1941 paper *On a problem of Sidon in additive number theory*, establishing that Sidon sets of size `~√N` exist inside `[1, N]`.

## Why is this interesting?

Constructing dense Sidon sets is a hard problem. The double-counting upper bound gives `|A ∩ [1,N]| ≤ (1 + o(1))√N`; achieving this up to constants requires real algebraic input. The Erdős–Turán construction is the canonical example, using quadratic residues modulo a prime to spread elements so that sums cannot collide. The result is a standard reference in additive combinatorics (Tao–Vu, O'Bryant's bibliography), yet no Lean 4 formalization appears to exist in Mathlib as of this writing.

The proof is also non-trivial to machine-check: it requires reasoning simultaneously about natural number arithmetic, integer congruences (`ZMod`), and Mathlib's prime API, with a case analysis on divisibility by an odd prime.

## The Proof Idea

Each element `a ∈ E_p` is written as `a = 2p·i + rᵢ` where `rᵢ = i² mod p ∈ [0, p)`. Suppose `a + b = c + d`, i.e. the four elements come from indices `i₁, i₂, i₃, i₄`.

**Step 1 — Sum of indices.** The "coarse" `2p`-multiples force:

$$i_1 + i_2 = i_3 + i_4$$

since the residues `rᵢ` are bounded in `[0, p)` and cannot compensate a full multiple of `2p`.

**Step 2 — Quadratic congruence.** Substituting back, the residue parts satisfy:

$$i_1^2 + i_2^2 \equiv i_3^2 + i_4^2 \quad (\bmod\ p)$$

Combined with Step 1, this rewrites (setting `i₄ = i₁ + i₂ - i₃`) to:

$$2(i_1 - i_3)(i_3 - i_2) \equiv 0 \quad (\bmod\ p)$$

**Step 3 — Prime field.** Since `p` is an odd prime, `ℤ/pℤ` is a field. So one factor is zero mod `p`. Since all indices lie in `[0, p)`, their differences have absolute value `< p`, so "zero mod p" means literally zero. This gives `i₁ = i₃` or `i₂ = i₃`, and in either case `{i₁, i₂} = {i₃, i₄}`, hence `{a, b} = {c, d}`.

## Repository Structure

```
erdos-turan-sidon/
├── ErdosTuranSidon/
│   └── Basic.lean         ← The full formalization
├── docs/
│   └── proof-notes.md     ← Extended proof commentary
├── lakefile.lean
├── lean-toolchain
└── README.md
```

The entire formalization lives in `ErdosTuranSidon/Basic.lean`. There are no auxiliary files and no `sorry`.

## Building

**Prerequisites:** [elan](https://github.com/leanprover/elan) (the Lean version manager) and an internet connection for Mathlib's cache.

```bash
# Clone
git clone https://github.com/YOUR_USERNAME/erdos-turan-sidon
cd erdos-turan-sidon

# Download prebuilt Mathlib cache (saves hours of compilation)
lake exe cache get

# Build
lake build
```

Successful compilation with no errors or warnings confirms the proof.

## Lean 4 Proof Structure

The formalization consists of three definitions and four lemmas.

### Definitions

```lean
-- A set A is Sidon if a + b = c + d ⟹ {a,b} = {c,d} as multisets
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

-- The Erdős–Turán map: i ↦ 2pi + (i² mod p)
def erdosTuranFn (p : ℕ) (i : ℕ) : ℕ := 2 * p * i + (i ^ 2 % p)

-- The set E_p = image of {0,...,p-1} under erdosTuranFn p
def erdosTuranSet (p : ℕ) : Finset ℕ := (Finset.range p).image (erdosTuranFn p)
```

### Supporting lemmas

| Lemma | Statement |
|---|---|
| `erdosTuranFn_injective` | `i ↦ 2pi + (i² mod p)` is injective on `[0, p)` |
| `erdosTuranSet_card` | `\|E_p\| = p` |
| `erdosTuranSet_bound` | Every element of `E_p` is `< 2p²` |

### Main theorem

```lean
set_option maxHeartbeats 800000 in
lemma erdosTuranSet_sidon (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    IsSidonSet (↑(erdosTuranSet p) : Set ℕ)
```

The most delicate formalization step is the prime-field argument in Step 3, which uses `ZMod.intCast_eq_intCast_iff` together with a structural case split `rcases p with (_ | _ | _ | p)` to discharge the degenerate cases `p < 3` before the prime-field reasoning applies.

The `maxHeartbeats 800000` annotation reflects the cost of `nlinarith` bounding integer differences in absolute value; this is expected and not a sign of a fragile proof.


## Related work

**Mathlib4** does not appear to contain a formalization of the Erdős–Turán Sidon construction or Sidon sets in general. The closest existing Mathlib content is `Mathlib.Data.ZMod.Basic` (the `ZMod` API used in the proof) and `Mathlib.Combinatorics.Additive.SalemSpencer` (Salem–Spencer/Roth theory), but Sidon sets are not covered.

**Classical reference:** P. Erdős and P. Turán, *On a problem of Sidon in additive number theory, and on some related problems*, J. London Math. Soc. **16** (1941), 212–215.

**Survey:** K. O'Bryant, *A complete annotated bibliography of work related to Sidon sets*, Electron. J. Combin. DS11 (2004).

## Contributing

Issues and pull requests are welcome.

## License

Apache 2.0 — the same license as Mathlib4.

import Mathlib

/-!
# Erdős–Turán Sidon Set Construction

## Main result

For any prime `p ≥ 3`, the set

    E_p = { 2pi + (i² mod p) : 0 ≤ i < p }

is a **Sidon set** (also called a B₂ set): all pairwise sums `a + b` with
`a, b ∈ E_p` are distinct.

This is a Lean 4 + Mathlib4 formalization of the classical Erdős–Turán (1941)
construction of dense finite Sidon sets from quadratic residues modulo a prime.

-/

open Classical Finset

noncomputable section

/-! ## Definition -/

/-- A set `A` is a *Sidon set* (B₂ set) if whenever `a + b = c + d` with
    `a, b, c, d ∈ A`, we have `{a, b} = {c, d}` as multisets. -/
def IsSidonSet (A : Set ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A,
    a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The Erdős–Turán map: `i ↦ 2pi + (i² mod p)`. -/
def erdosTuranFn (p : ℕ) (i : ℕ) : ℕ :=
  2 * p * i + (i ^ 2 % p)

/-- The Erdős–Turán Sidon set for prime `p`: image of `{0, …, p-1}` under
    `erdosTuranFn p`. -/
def erdosTuranSet (p : ℕ) : Finset ℕ :=
  (Finset.range p).image (erdosTuranFn p)

/-! ## Supporting lemmas -/

/-- `erdosTuranFn p` is injective on `{0, …, p-1}`. -/
lemma erdosTuranFn_injective (p : ℕ) (hp : p ≥ 3) :
    ∀ i < p, ∀ j < p, erdosTuranFn p i = erdosTuranFn p j → i = j := by
  unfold erdosTuranFn
  intro i hi j hj h
  have := congr_arg (· % p) h
  norm_num [Nat.add_mod, Nat.mul_mod, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  aesop

/-- The Erdős–Turán set has exactly `p` elements. -/
lemma erdosTuranSet_card (p : ℕ) (hp : p ≥ 3) :
    (erdosTuranSet p).card = p := by
  exact Finset.card_image_of_injOn (fun x hx y hy hxy =>
    erdosTuranFn_injective p hp x (Finset.mem_range.mp hx) y
      (Finset.mem_range.mp hy) hxy) |>.trans (by simp)

/-- Elements of the Erdős–Turán set are bounded above by `2p²`. -/
lemma erdosTuranSet_bound (p : ℕ) (n : ℕ) (hn : n ∈ erdosTuranSet p) :
    n < 2 * p ^ 2 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hn
  unfold erdosTuranFn
  nlinarith [Finset.mem_range.mp hi,
    Nat.mod_lt (i ^ 2) (show p > 0 from Nat.pos_of_ne_zero (by aesop_cat))]

/-! ## Main theorem -/

/-- **Erdős–Turán Sidon construction** (Lean 4 + Mathlib4 formalization).

    For any prime `p ≥ 3`, the set `E_p = {2pi + (i² mod p) : 0 ≤ i < p}`
    is a Sidon set of size `p` contained in `[0, 2p²)`.

    This formalizes the classical 1941 construction of Erdős and Turán. -/
set_option maxHeartbeats 800000 in
lemma erdosTuranSet_sidon (p : ℕ) (hp : Nat.Prime p) (hp3 : p ≥ 3) :
    IsSidonSet (↑(erdosTuranSet p) : Set ℕ) := by
  intro a ha b hb c hc d hd habc
  -- Extract index witnesses: each element is `2pi + (i² mod p)` for some `i < p`.
  obtain ⟨i1, hi1⟩ : ∃ i1 < p, a = 2 * p * i1 + (i1 ^ 2 % p) := by
    unfold erdosTuranSet at ha; aesop
  obtain ⟨i2, hi2⟩ : ∃ i2 < p, b = 2 * p * i2 + (i2 ^ 2 % p) := by
    unfold erdosTuranSet at hb; aesop
  obtain ⟨i3, hi3⟩ : ∃ i3 < p, c = 2 * p * i3 + (i3 ^ 2 % p) := by
    unfold erdosTuranSet at hc; aesop
  obtain ⟨i4, hi4⟩ : ∃ i4 < p, d = 2 * p * i4 + (i4 ^ 2 % p) := by
    unfold erdosTuranSet at hd; aesop
  -- Step 1: The sum equation forces i1 + i2 = i3 + i4 (compare `2p`-multiples).
  have h_eq : i1 + i2 = i3 + i4 ∧
      i1 ^ 2 % p + i2 ^ 2 % p = i3 ^ 2 % p + i4 ^ 2 % p := by
    have h_eq : 2 * p * (i1 + i2 - i3 - i4 : ℤ) =
        (i3 ^ 2 % p + i4 ^ 2 % p) - (i1 ^ 2 % p + i2 ^ 2 % p) := by linarith
    have h_sum_eq : i1 + i2 = i3 + i4 := by
      by_contra h_contra
      exact h_contra <| by
        nlinarith only [h_eq,
          Int.emod_nonneg (i1 ^ 2) (by linarith : (p : ℤ) ≠ 0),
          Int.emod_lt_of_pos (i1 ^ 2) (by linarith : (p : ℤ) > 0),
          Int.emod_nonneg (i2 ^ 2) (by linarith : (p : ℤ) ≠ 0),
          Int.emod_lt_of_pos (i2 ^ 2) (by linarith : (p : ℤ) > 0),
          Int.emod_nonneg (i3 ^ 2) (by linarith : (p : ℤ) ≠ 0),
          Int.emod_lt_of_pos (i3 ^ 2) (by linarith : (p : ℤ) > 0),
          Int.emod_nonneg (i4 ^ 2) (by linarith : (p : ℤ) ≠ 0),
          Int.emod_lt_of_pos (i4 ^ 2) (by linarith : (p : ℤ) > 0)]
    grind
  -- Step 2: The quadratic residue condition gives 2(i1 - i3)(i3 - i2) ≡ 0 (mod p).
  have h_mod : 2 * (i1 - i3 : ℤ) * (i3 - i2 : ℤ) ≡ 0 [ZMOD p] := by
    have h_mod : (i1 ^ 2 + i2 ^ 2 : ℤ) ≡ (i3 ^ 2 + i4 ^ 2 : ℤ) [ZMOD p] := by
      norm_cast; simp +decide [*, Nat.ModEq, Nat.add_mod]
    rw [Int.modEq_zero_iff_dvd]
    obtain ⟨k, hk⟩ := h_mod.symm.dvd
    exact ⟨k, by nlinarith only [hk, h_eq.1]⟩
  -- Step 3: Since p is an odd prime, one factor is zero mod p, giving {i1,i2} = {i3,i4}.
  by_cases h_cases : (i1 - i3 : ℤ) ≡ 0 [ZMOD p] ∨ (i3 - i2 : ℤ) ≡ 0 [ZMOD p]
  · rcases h_cases with h | h <;>
      rw [Int.modEq_zero_iff_dvd] at h <;>
      rcases h with ⟨k, hk⟩ <;>
      simp_all +decide [sub_eq_iff_eq_add]
    · rcases lt_trichotomy k 0 with hk' | rfl | hk' <;> first | nlinarith | aesop
    · rcases lt_trichotomy k 0 with hk' | rfl | hk'
      · nlinarith
      · grind
      · nlinarith
  · haveI := Fact.mk hp
    simp_all +decide [← ZMod.intCast_eq_intCast_iff]
    rcases p with (_ | _ | _ | p) <;> cases h_mod <;> contradiction

end

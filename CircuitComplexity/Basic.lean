/-
Boolean functions on n variables.
Truth table representation and counting.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Basic

namespace CircuitComplexity

/-- Boolean function on `n` input variables. -/
abbrev BoolFn (n : ℕ) := (Fin n → Bool) → Bool

-- Fintype instance for BoolFn needs DecidableEq (Fin n → Bool),
-- which requires classical reasoning for function extensionality.
open Classical in
noncomputable instance (n : ℕ) : Fintype (BoolFn n) := Pi.instFintype

/-- Truth table: evaluate f at each input encoded as a binary index.
    Entry `i` holds `f(bit₀(i), bit₁(i), ..., bitₙ₋₁(i))`. -/
def BoolFn.truthTable {n : ℕ} (f : BoolFn n) : Fin (2 ^ n) → Bool :=
  fun i => f (fun j => i.val.testBit j.val)

/-- Decode a truth table index to explicit input bits. -/
def decodeBits (n : ℕ) (i : Fin (2 ^ n)) : Fin n → Bool :=
  fun j => i.val.testBit j.val

/-- |BoolFn n| = 2^(2^n). -/
theorem card_boolFn (n : ℕ) : Fintype.card (BoolFn n) = 2 ^ 2 ^ n := by
  classical
  simp only [BoolFn, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]

end CircuitComplexity

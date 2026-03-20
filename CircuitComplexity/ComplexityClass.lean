/-
Circuit families and the complexity class P/poly.
-/
import CircuitComplexity.Circuit
import Mathlib.Tactic.Linarith

namespace CircuitComplexity

/-- A circuit family: one circuit per input length. -/
structure CircuitFamily where
  circuit : (n : ℕ) → Circuit n

/-- A circuit family computes a function sequence. -/
def CircuitFamily.computes (C : CircuitFamily) (f : (n : ℕ) → BoolFn n) : Prop :=
  ∀ n, (C.circuit n).computes (f n)

/-- Polynomial bound: ∃ c d, ∀ n, s(n) ≤ c · n^d + c. -/
def PolyBounded (s : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, s n ≤ c * n ^ d + c

/-- P/poly: computed by a polynomial-size circuit family. -/
def InPPoly (f : (n : ℕ) → BoolFn n) : Prop :=
  ∃ C : CircuitFamily, C.computes f ∧ PolyBounded (fun n => (C.circuit n).size)

/-- Polynomial in the truth table length 2^n.
    The constructivity bound in Razborov-Rudich. -/
def PolyInExp (s : ℕ → ℕ) : Prop :=
  ∃ c d : ℕ, ∀ n, s n ≤ c * (2 ^ n) ^ d + c

-- Closure properties of PolyBounded

theorem polyBounded_const (k : ℕ) : PolyBounded (fun _ => k) :=
  ⟨k, 0, fun _ => by simp⟩

theorem polyBounded_add {s t : ℕ → ℕ} (hs : PolyBounded s) (ht : PolyBounded t) :
    PolyBounded (fun n => s n + t n) := by
  obtain ⟨c₁, d₁, h₁⟩ := hs
  obtain ⟨c₂, d₂, h₂⟩ := ht
  -- Use max(s(0)+t(0), c₁+c₂) to absorb the n=0 edge case
  refine ⟨max (s 0 + t 0) (c₁ + c₂), max d₁ d₂, fun n => ?_⟩
  have h1 := h₁ n
  have h2 := h₂ n
  by_cases hn : n = 0
  · subst hn
    linarith [le_max_left (s 0 + t 0) (c₁ + c₂),
              Nat.zero_le (max (s 0 + t 0) (c₁ + c₂) * 0 ^ max d₁ d₂)]
  · have hn1 : 0 < n := Nat.pos_of_ne_zero hn
    have hd1 : n ^ d₁ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn1 (le_max_left d₁ d₂)
    have hd2 : n ^ d₂ ≤ n ^ max d₁ d₂ := Nat.pow_le_pow_right hn1 (le_max_right d₁ d₂)
    have hmax : c₁ + c₂ ≤ max (s 0 + t 0) (c₁ + c₂) := le_max_right _ _
    nlinarith [Nat.mul_le_mul_left c₁ hd1, Nat.mul_le_mul_left c₂ hd2,
               Nat.mul_le_mul_right (n ^ max d₁ d₂) hmax]

end CircuitComplexity

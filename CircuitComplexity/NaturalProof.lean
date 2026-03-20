/-
Natural combinatorial properties (Razborov-Rudich 1997).

A property of Boolean functions is *natural* if it is:
  1. Constructive: decidable in poly(2^n) time on truth tables
  2. Large: satisfied by ≥ 1/poly(n) fraction of all functions

A natural property is *useful against C* if having the property
implies not being in C.
-/
import CircuitComplexity.ComplexityClass

namespace CircuitComplexity

/-- A combinatorial property of Boolean functions, one per input length.
    Bundled with decidability for truth table checking. -/
structure CombProperty where
  prop : (n : ℕ) → BoolFn n → Prop
  decidable : (n : ℕ) → DecidablePred (prop n)

/-- Constructivity: decidable by a poly(2^n)-size circuit on truth tables.
    The checker circuit at parameter n takes 2^n input bits (the truth table)
    and outputs whether the function satisfies the property. -/
def CombProperty.constructive (P : CombProperty) : Prop :=
  ∃ D : (n : ℕ) → Circuit (2 ^ n),
    PolyInExp (fun n => (D n).size) ∧
    ∀ n (f : BoolFn n),
      letI := P.decidable n
      (D n).eval (f.truthTable) = decide (P.prop n f)

/-- Largeness: ≥ 1/q(n) fraction of all n-variable functions satisfy P.
    Stated as: |{f | P(f)}| · q(n) ≥ |BoolFn n|. -/
noncomputable def CombProperty.large (P : CombProperty) : Prop :=
  ∃ q : ℕ → ℕ, PolyBounded q ∧ ∀ n,
    letI := P.decidable n
    Fintype.card (BoolFn n) ≤
      (Finset.univ.filter (P.prop n)).card * q n

/-- Usefulness against P/poly: for any polynomial size bound,
    functions with circuits that small eventually fall outside P.
    This per-bound formulation gives a uniform cutoff for all seeds
    of a PRF generator sharing the same circuit size polynomial. -/
def CombProperty.usefulAgainstPPoly (P : CombProperty) : Prop :=
  ∀ c d : ℕ, ∃ N, ∀ n, n ≥ N → ∀ (f : BoolFn n) (circ : Circuit n),
    circ.computes f → circ.size ≤ c * n ^ d + c → ¬P.prop n f

/-- A natural property: constructive and large. -/
structure NaturalProperty extends CombProperty where
  isConstructive : toCombProperty.constructive
  isLarge : toCombProperty.large

end CircuitComplexity

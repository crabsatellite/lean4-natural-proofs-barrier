/-
Pseudorandom function generators and the PRF hypothesis.

We formalize the *consequence* of PRF security needed for the
natural proofs barrier, avoiding measure theory.
-/
import CircuitComplexity.NaturalProof

namespace CircuitComplexity

/-- A PRF generator maps seeds to Boolean functions via poly-size circuits. -/
structure PRFGenerator where
  /-- Seed length as a function of the security parameter. -/
  seedLen : ℕ → ℕ
  /-- Map seed to Boolean function. -/
  generate : (n : ℕ) → (Fin (seedLen n) → Bool) → BoolFn n
  /-- Each generated function has a polynomial-size circuit.
      The bound c · n^d + c is uniform over all seeds. -/
  polySize : ∃ c d : ℕ, ∀ n (seed : Fin (seedLen n) → Bool),
    ∃ circ : Circuit n, circ.computes (generate n seed) ∧
      circ.size ≤ c * n ^ d + c

/-- PRF hypothesis (consequence form).

    If a combinatorial property is both constructive and large,
    it cannot reject *all* PRF outputs — otherwise the property
    itself would be a polynomial-size distinguisher with
    non-negligible advantage, contradicting PRF security.

    The "∀ N, ∃ n ≥ N" quantification ensures the existence
    holds at arbitrarily large input lengths, matching the
    asymptotic nature of usefulness. -/
def PRFHypothesis : Prop :=
  ∃ G : PRFGenerator,
    ∀ (P : CombProperty),
      P.constructive → P.large →
      ∀ N : ℕ, ∃ n, n ≥ N ∧ ∃ seed : Fin (G.seedLen n) → Bool,
        P.prop n (G.generate n seed)

end CircuitComplexity

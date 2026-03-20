/-
The Natural Proofs Barrier (Razborov-Rudich 1997).

Main theorem: under the PRF hypothesis, no natural combinatorial
property is useful against P/poly.
-/
import CircuitComplexity.PRF

namespace CircuitComplexity

/-- **Natural Proofs Barrier.**
    If pseudorandom function generators exist (PRFHypothesis),
    then no natural property is useful against P/poly.

    Proof sketch:
    1. PRFHypothesis gives a generator G with uniform poly-size bound (c_G, d_G).
    2. Usefulness against that bound gives a cutoff N.
    3. PRFHypothesis (constructive + large) yields n ≥ N and a seed
       whose output satisfies P — contradicting usefulness at n ≥ N
       since G's output has a circuit of size ≤ c_G · n^d_G + c_G. -/
theorem natural_proof_barrier (h : PRFHypothesis) :
    ∀ P : NaturalProperty, ¬P.toCombProperty.usefulAgainstPPoly := by
  intro P hU
  -- Extract PRF generator
  obtain ⟨G, hG⟩ := h
  -- Uniform polynomial bound on circuit sizes of G's output
  obtain ⟨c_G, d_G, heff⟩ := G.polySize
  -- Usefulness at the (c_G, d_G) bound gives cutoff N
  obtain ⟨N, hN⟩ := hU c_G d_G
  -- PRF hypothesis: P is constructive and large, so some G output satisfies P
  obtain ⟨n, hn, seed, hsat⟩ := hG P.toCombProperty P.isConstructive P.isLarge N
  -- G(n, seed) has a small circuit
  obtain ⟨circ, hcomp, hsize⟩ := heff n seed
  -- But usefulness says small-circuit functions don't satisfy P at n ≥ N
  exact hN n hn (G.generate n seed) circ hcomp hsize hsat

end CircuitComplexity

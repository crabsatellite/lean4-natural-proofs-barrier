# Conditional natural-property obstruction in Lean 4

This repository contains a conditional formula-model obstruction and finite
counting infrastructure. It preserves the original Lean definitions and proofs;
the scope statement and accompanying paper were corrected on 12 November 2026.

## Exact scope

- The main theorem consumes PRFHypothesis: a postulated polynomial-size family
  hits every constructive, inverse-polynomially dense property at arbitrarily
  large input lengths. The reduction from cryptographic hardness to that
  premise is not formalized here.
- Circuit is an inductive tree. Circuit.size counts repeated subexpressions
  repeatedly, so the model is Boolean formulas, without shared gates.
  Historical identifiers containing PPoly retain that local meaning.
- CombProperty.large requires inverse-polynomial density in the number of
  variables n, a stronger condition than the classical inverse-polynomial
  density in truth-table length 2^n.
- Shannon.lean proves bounded-formula finiteness and an existence implication
  conditional on a strict cardinality inequality. It does not supply a
  quantitative circuit-count estimate or an asymptotic most-functions bound.

Consequently, the earlier description as a complete or first formalization
of the classical natural-proofs barrier was too broad. Zero sorry obligations
in a conditional theorem do not discharge its stated hypothesis or establish
correspondence with a different circuit model.

## Classical Theorem 4.1 and acknowledgement

For a separate development that reports the classical theorem from an explicit
generator hardness assumption, including the GGM and hybrid reduction, see
[zzyzek/NaturalProof-Lean, pinned revision](https://github.com/zzyzek/NaturalProof-Lean/tree/8c1df29730a2f34d3513b693a5bac5d33abe1520).
Its statement and definitions were inspected for this comparison; it was not
independently rebuilt here. Its metadata reports self-assessed mathematical
review and kernel/comparator checks. The cryptographic hardness remains an
assumption.

I thank its maintainer, publicly identified as zzyzek, for the
[published comparison](https://github.com/zzyzek/NaturalProof-Lean/blob/8c1df29730a2f34d3513b693a5bac5d33abe1520/README.md#other-formalizations)
that prompted the scope clarification. Readers seeking that fuller reduction
should consult that project; this repository is not being expanded into a
duplicate implementation.

## Files and reproducibility

The seven source modules remain in CircuitComplexity/.
The exact main conditional theorem is in NaturalProofBarrier.lean,
with its premise in PRF.lean. Toolchain and Mathlib dependency identity are
retained in lean-toolchain and lake-manifest.json.

Build with the pinned toolchain and lake build. A build checks the Lean
statements under their displayed definitions and assumptions.

## Paper

The corrected source is paper/main.tex.
[Stable paper archive and version history](https://doi.org/10.5281/zenodo.19132830).
The March 2026 first edition remains part of the version history; the scope
clarification applies to its broader abstract and completion claims.

## License

Apache 2.0 for the existing software. See LICENSE.
The paper retains its Zenodo CC BY 4.0 license.

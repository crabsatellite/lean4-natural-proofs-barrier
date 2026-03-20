# Natural Proofs Barrier in Lean 4

First machine-verified formalization of the natural proofs barrier
(Razborov--Rudich 1997) in any proof assistant.

**Status**: Complete. Zero `sorry` obligations. Builds under Lean v4.29.0-rc6 + Mathlib.

## Theorem

> If pseudorandom function generators exist, then no natural
> combinatorial property is useful against P/poly.

## Files

| File | Contents |
|------|----------|
| `Basic.lean` | Boolean functions, truth tables, cardinality |
| `Circuit.lean` | Circuits (AND/OR/NOT), evaluation, size, Shannon decomposition |
| `ComplexityClass.lean` | Circuit families, `PolyBounded`, `PolyInExp`, P/poly |
| `NaturalProof.lean` | Combinatorial properties: constructive, large, useful |
| `PRF.lean` | PRF generators, PRF hypothesis (consequence form) |
| `NaturalProofBarrier.lean` | Main theorem: `natural_proof_barrier` |
| `Shannon.lean` | Shannon counting bound: most functions need large circuits |

## Building

```
# Install Lean 4 via elan
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh

# Build
lake build
```

## Paper

See `paper/main.tex` for the accompanying manuscript.

## License

Apache 2.0. See [LICENSE](LICENSE).

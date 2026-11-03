# Third-party sources and attribution

The following adapted sources retain their original copyright notices and
licenses.

## Algebraic combinatorics

Five files under `AlgebraicCombinatorics/` are adapted from
[facebookresearch/algebraic-combinatorics](https://github.com/facebookresearch/algebraic-combinatorics)
at commit `b6022318e986a0c20764569208ba8ebbe1c04dbf`:

- `SymmetricFunctions/NPartition.lean`
- `SymmetricFunctions/MonomialSymmetric.lean`
- `SymmetricFunctions/LittlewoodRichardson.lean`
- `Determinants/LGV2.lean`
- `SymmetricFunctions/PieriJacobiTrudi.lean`

Copyright (c) Meta Platforms, Inc. and affiliates. These files are distributed
under **Creative Commons Attribution–NonCommercial 4.0 International**, whose
full text is in
[`third-party-licenses/algebraic-combinatorics-CC-BY-NC-4.0.txt`](third-party-licenses/algebraic-combinatorics-CC-BY-NC-4.0.txt).
The upstream source formalizes material from Darij Grinberg's *Algebraic
Combinatorics*; the source comments identify its definitions and results.

Changes include compatibility adaptations for Lean/mathlib 4.35.0
(polynomial APIs, coercions, list indices, and finite sums/products), and
documentation updates. The selection keeps proved upstream declarations:
`LGV2.lean` ends after `LGV.lgv_nonpermutable`; `PieriJacobiTrudi.lean`
omits `pieri_horizontal`, `pieri_vertical`, and `jacobiTrudi_e`, and removes
the unused `OmegaInvolution` import.

## Desnanot–Jacobi identity

`CoefficientOne/DesnanotJacobi.lean` adapts Slava Naprienko's
[`dj.lean`](https://github.com/slavanaprienko/lean-formalization/blob/b0812ef8b8597be0b0159aeae4b167b415c6f1d3/dj.lean),
commit `b0812ef8b8597be0b0159aeae4b167b415c6f1d3`.
Copyright (c) 2026 Slava Naprienko; **Apache License 2.0**. The full license is in
[`third-party-licenses/desnanot-jacobi-APACHE-2.0.txt`](third-party-licenses/desnanot-jacobi-APACHE-2.0.txt).
Adaptations consist of namespacing the declarations under
`CoefficientOne.DesnanotJacobi`, compatibility qualification of
`Matrix.smul_apply`, and documentation updates.

## Lean and mathlib

The Lean 4.35.0 toolchain is installed separately. Mathlib 4.35.0 sources are
included in [`../mathlib`](../mathlib), at commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`, with their copyright notices and
[license](../mathlib/LICENSE).

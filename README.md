# An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits

Lean sources accompanying [the manuscript](paper/main.pdf).
The paper's results are indexed in [RESULTS.md](RESULTS.md).

Install Lean/Lake **4.35.0** and Python **3.10 or later**, then run from this directory:

```sh
python verify.py
```

This compiles the included m-set and spectral-theorem proof libraries and checks
their declarations for axioms. The only permitted axioms are `propext`,
`Classical.choice`, and `Quot.sound`; `sorryAx` is rejected. Generated files stay
under `.lake/` and are not needed to reproduce the check.

The main entry point is [MsetsPaper.lean](MsetsPaper.lean). `MsetsLower/` provides
probability and bandit foundations used by `MsetsPaper/`.
`vendor/coefficient-one/` contains the spectral theorem and its proof dependencies.
All library sources are included; no private repository is needed.

Mathlib is pinned to `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0).
Its dependency revisions are recorded in the included Lake manifests.
ProofWidgets uses the included display JavaScript instead of invoking npm;
its original configuration is retained as `lakefile.lean.upstream`.
Dependency licenses and the spectral library's third-party attribution are
retained alongside their sources.

Lean checks the formal statements and proofs. Correspondence with the manuscript
requires comparing its statements, definitions and assumptions with the Lean source.
The computational bounds use the paper's exact-real arithmetic model.

# anchor-calculus

Replication package. Paper DOI: [10.5281/zenodo.23086699](https://doi.org/10.5281/zenodo.23086699) (v1.1, version chain concept 10.5281/zenodo.23084466; v1.0 = 10.5281/zenodo.23084467).

**File ↔ section map**

| Lean file | Paper section |
|---|---|
| AnchorOperations.lean | §3 axioms Op-0~5 + Theorems 1–8 (§8 composite order lattice instance: Theorems 4a/4b) |
| AnchorMeasure.lean | §5 continuous allocation geometry (ledger_main) |

**Replication**: `cd lean && lake build` (toolchain pinned v4.33.1) reproduces the zero-sorry claims. Accommodation-test sources are literature references (paper §6). `replication/` holds the constraint-order round (preregistered script + results) backing the v1.1 §8 composite-order lattice instance.

## License

Code (`lean/`): MIT. Docs: CC-BY-4.0.

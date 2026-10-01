# anchor-calculus

Replication package. Paper DOI: **PENDING** (backfilled after publish).

**File ↔ section map**

| Lean file | Paper section |
|---|---|
| AnchorOperations.lean | §3 axioms Op-0~5 + Theorems 1–8 |
| AnchorMeasure.lean | §5 continuous allocation geometry (ledger_main) |

**Replication**: `cd lean && lake build` (toolchain pinned v4.33.1) reproduces the zero-sorry claims. Accommodation-test sources are literature references (paper §8).


## License

Code (`lean/`): MIT. Docs: CC-BY-4.0.

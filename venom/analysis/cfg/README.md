# CFG Analysis

Consumer API: `Ancestors cfgAnalysis`

## Structure

```
cfgAnalysisScript.sml        — public API (re-exports defs + props)
cfgAnalysisPropsScript.sml   — correctness theorem statements
defs/cfgDefsScript.sml       — definitions
proofs/                      — correctness proofs + helpers
```

`defs/` is a separate directory because Holmake disallows circular `INCLUDES`.
`proofs/` needs the definitions, and the parent needs `proofs/`, so definitions
must live in a sibling subdir to avoid a loop.

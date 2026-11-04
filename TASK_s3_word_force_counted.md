# TASK: Counted memory forcing for word body literals

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Locations: lowering/bodyLiteralForceMemoryScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem compile_literal_word_body_sim_mem:
  !ctx func cenv cx env ty ann l es.
    expr_sim_pre cenv cx env (Literal ann l) es /\ is_word_type ann ==>
    expr_sim_mem ctx func cenv cx ty (Literal ann l) es
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

Prove this existing root under canonical counted memory judgments. Preserve its
old successful proof and private tactic as a comment. Build the target with its
strict kernel gate intact. No definitions, admissions or stronger assumptions.

## Build

`holbuild -j2 build bodyLiteralForceMemoryTheory`

The old proof has not been built under the counted join. Independent exact-schema
audit: PROVABLE, including arbitrary external ty and all well-typed word literals.

## Background

The raw value root in bodyLiteralMemory is owner checked at51d5d7ce6. Its genuine
mode-T body_literal_word_mem_prefix is public, without a simp attribute, for this
actual consumer. Do not duplicate its path, post or compiler-shape facts.

## Domain Constraints

Edit only bodyLiteralForceMemoryScript.sml and necessary direct imports. Keep
bodyLiteralMemory and executable/source definitions read-only. No new helper
family, axiom, admission, timeout override, TRY/ORELSE search, holbuild run/repl,
checkpoint/cache bypass or force rebuild. Keep complete posts, locals/allocas,
allocation history/frontier and arbitrary source gas tails.

## Available Resources

- lowering/bodyLiteralMemoryScript.sml: checked actual mode-T prefix.
- lowering/exprSimMemoryValuesScript.sml: canonical expression introduction.
- lowering/exprSimMemDefsScript.sml, exprSimHypsDefsScript.sml.
- lowering/exprSimPropsScript.sml and gasSummaryScript.sml.

## Notes

This independent job does not own body induction or other consumers.

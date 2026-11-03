# TASK: Repair the signed multiplication mismatch helper

## Meta
Status: planned; independent truth audit PROVABLE
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem mul_sdiv_mismatch[local]:
  ∀(a:bytes32) b ty.
    b ≠ 0w ∧
    ¬(INT_MIN (:256) ≤ w2i a * w2i b ∧ w2i a * w2i b ≤ INT_MAX (:256)) ∧
    is_signed_type ty ∧ in_type_range ty (math_val ty a) ∧ type_bits ty ≤ 256 ∧
    safe_sdiv (a * b) b = a ⇒
    type_bits ty = 256 ∧ a = n2w (2 ** 255) ∧ b = n2w (2 ** 256 − 1)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

All existing schemas, definitions, ML tactics, other proof bodies and files
are frozen at 766399319. Change only this root's proof and necessary consumed
local helpers in lowering/arithmeticPropsScript.sml. Retain the existing proof
until replacing it. This task covers one independent root.

## Completion Criteria

1. The unchanged root builds at the default step limit without new admissions.
2. All other schemas, definitions, proof bodies, ML tactics and files stay unchanged.
3. Report the named-target result and any later failure without expanding scope.
   The owner performs one cached default checkpoint-free check after return.

## Build

```sh
holbuild -j4 build arithmeticPropsTheory
```

## Background

The existing signed multiplication proof was factored into this local lemma
to expose its individual tactics to the step timer. A downstream owner check
timed out in its final simplifier. A narrower rewrite set reaches its final
arithmetic step, which fails. The complete statement parses and all earlier
theorems were reached successfully in the latest focused build. No arithmetic
definition, type classification or assumption may change.

## Domain Constraints

- Preserve the complete frozen schema and every other existing proof.
- No new cheat, axiom, hypothesis, restricted subset or opaque fact.
- Default 2.5s limit; never raise it, disable checks or catch timeouts.
- No TRY/ORELSE/FIRST around search; select goals explicitly.
- Use holbuild only; no interactive HOL, Holmake, run/repl or explicit theory loads.
- Reuse existing facts before adding necessary consumed local helpers.
- Report later failures without expanding scope or resuming a completed task.
- Commit only substantive source edits; leave Alan working files untracked.
  End commits with `Bot: sol (OpenAI GPT-6.1 Sol)`.

## Available Resources

- `lowering/arithmeticPropsScript.sml`: frozen root, safe_sdiv_mul_overflow, typed arithmetic and word bounds.
- `lowering/defs/exprLoweringScript.sml`: source compiler arithmetic operations.
- `lowering/defs/compileEnvScript.sml`: compilation type helpers.
- `venom/defs/venomExecSemanticsScript.sml`: safe_sdiv and instruction execution.
- `syntax/vyperASTScript.sml`: all Vyper base and type constructors.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: proof-control conventions.

## Notes

Independent source audit found the complete unchanged statement PROVABLE,
including width zero, width one, DecimalT and every other type constructor.
This is a truth audit, not a kernel proof.

The owner compares all frozen schemas and every byte outside the permitted
proof/helper area. This prerequisite does not complete the downstream gas
oracle consumer proof.

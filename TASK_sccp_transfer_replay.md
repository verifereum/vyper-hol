# TASK: Repair the observed SCCP transfer replay timeout

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem sccp_transfer_sound:
  !fn. transfer_sound (\lat. const_sound lat.sl_vals)
         sccp_transfer_inst fn
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

The entire existing theorem is the frozen root, not merely the first failing
fragment. All executable definitions and every other existing theorem statement
and proof body are frozen at 71a288d37. Only this root's proof and necessary new
local helper lemmas in its defining script may change. Shared ML tactics are
frozen. Do not repair an unrelated prerequisite: report its exact failure.

## Completion Criteria

1. The existing root and necessary local helpers build at the default step limit
   with no new admissions or CHEAT warnings.
2. The exact frozen schema remains unchanged; all branches are proved.
3. Remove inherited search tactics wrapped in TRY, ORELSE or FIRST from this
   root's replacement. Select the relevant goals explicitly.
4. Keep every other existing proof, statement, definition and file unchanged.
5. Report the actual build outcome and any newly reached failure. Owner forced
   default/CI replay and oracle-tag checks are separate follow-up checks, not
   operations required from your build interface.

## Build

```sh
holbuild -j2 build sccpSoundTheory
```

## Background

Forced default replay of a preserved-pass batch stopped in this ancestor at
line 542, `rpt (BasicProvers.TOP_CASE_TAC >> gvs[])`, with a 2.5s TacticTimeout.
The theorem was reached and parsed. Its complete current schema was independently
audited PROVABLE across all transfer branches, opcodes, malformed arities, GAS
and INVOKE. No additional invariant or executable change is authorized.

## Domain Constraints

- Preserve all statements and executable definitions byte for byte.
- No new cheats, axioms, opacity, supported subsets or stronger hypotheses.
- Keep the default 2.5s step limit. Never catch search timeouts or disable checks.
- Use holbuild; no interactive HOL, Holmake, or explicit theory load calls.
- Reuse existing results before adding necessary local helpers. Do not add
  speculative infrastructure, diagnostic theories or broad test families.
- Other Alan tasks in this tree are complete or stopped. Do not resume them or
  edit their task/control/state files.

## Available Resources

- `venom/passes/sccp/proofs/sccpSoundScript.sml`: root and existing soundness helpers.
- `venom/passes/sccp/defs/sccpDefsScript.sml`: lattice and transfer definitions.
- `venom/simulation/defs/analysisSimDefsScript.sml`: transfer_sound definition.
- `venom/defs/venomExecSemanticsScript.sml`: current instruction semantics.
- `venom/defs/venomStateScript.sml`: state and variable operations.
- `venom/proofs/venomInstProofsScript.sml` and adjacent proof scripts: instruction facts.
- `venom/passes/shared/proofs/`: existing frame and simulation dependencies.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: project proof-control conventions.

## Notes

The existing failing proof is retained. The latest known file-history revision
9c806c1e0 has the same root proof and is not a checked replacement. The rest of
the same-list batch has not passed its complete forced replay; build only the
named ancestor here. Do not infer completion from an unrelated cached target.

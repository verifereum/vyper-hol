# TASK: Repair the observed read-output shape replay timeout

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem read_outputs_singleton[local]:
  (ef_read0 inst.inst_opcode \/ ef_read1 inst.inst_opcode \/
   inst.inst_opcode = SHA3) /\ inst_wf inst ==>
  ?out. inst.inst_outputs = [out]
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

Only this root's proof and necessary consumed local helpers in its defining
script may change. All other existing statements, definitions, proof bodies,
shared ML tactics and files are frozen at the commit containing this task.
Do not repair other newly reached read helpers or unrelated prerequisites;
report their exact failure instead. Do not resume other completed Alan tasks.

## Completion Criteria

1. Prove the complete unchanged root at the default step limit, with no new
   admissions or CHEAT warnings.
2. Keep every other existing statement, definition, proof and file unchanged.
3. Report the actual named-target build outcome and any newly reached failure.
   Owner forced default/CI replay and public dependency checks are separate
   follow-ups, not operations required from your build interface.

## Build

```sh
holbuild -j2 build regularReadEmitSimTheory
```

## Background

The current integration/GAS combined tree's forced default replay stopped at
line 14 in the broad `gvs[ef_read0_def, ef_read1_def, inst_wf_def,
LENGTH_EQ_NUM_compute]` with a 2.5s TacticTimeout. The complete schema was
independently audited PROVABLE for every admitted opcode and arbitrary operands
under its exact premises, including GAS. No extra assumption or definition edit
is authorized. The existing proof is retained for replacement.

## Domain Constraints

- Preserve the frozen schema and every executable definition.
- No new cheats, axioms, hypotheses, restricted subsets or opcode exclusions.
- Default 2.5s step limit; never raise it, disable checks or catch timeouts.
- No TRY/ORELSE/FIRST around search; select goals explicitly.
- Use holbuild; no interactive HOL, Holmake, run/repl or explicit theory loads.
- Reuse existing facts before adding necessary local helpers. No speculative
  infrastructure, test families or diagnostic theories.

## Available Resources

- `venom/codegen/proofs/regularReadEmitSimScript.sml`: root and consumers.
- `venom/codegen/proofs/opcodeClassScript.sml`: ef_read0 and ef_read1.
- `venom/defs/venomWfScript.sml`: inst_wf.
- `venom/defs/venomInstScript.sml`: opcodes and instruction record.
- `venom/codegen/proofs/instSimHelpersScript.sml`: existing shape helpers.
- `docs/HOL4_PROOF_CONTROL_LESSONS.md`: project proof-control conventions.

## Notes

The GAS frame and entry-dispatch targets have not reached a fresh owner
certificate on this combined tree. Check only the named ancestor here.

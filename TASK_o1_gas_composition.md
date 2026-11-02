# TASK: Compose O1 stages with reconstructed input gas oracles

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/compiler

## Theorem Statement (FROZEN)

```sml
Theorem o1_pipeline_stage_facts:
  run_venom_pipeline mem_ok calling_ok post_ok rpolicy o1_pipeline_spec unit =
    SOME out /\
  o1_source_unit_ok unit /\ unit_label_refs_ok unit /\
  unit_entry_no_params unit /\ unit_first_block_no_phi unit ==>
  o1_ctx_shape out.po_unit.cu_context /\
  entry_fn_first out.po_unit.cu_context /\
  !D vs_out. dead_wf D /\ o1_run_state_ok vs_out ==>
    ?vs_in. gas_variant vs_in vs_out /\
      (o1_src_inv unit.cu_context vs_in ==>
       ctx_sim D unit.cu_context out.po_unit.cu_context vs_in vs_out /\
       o1_lowered_inv out.po_unit.cu_context vs_out)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Save `o1_pipeline_stage_facts` without new admissions.
- Repair its proof and the O1 composition helpers under the approved real gas_variant and guarded stage contract definitions.
- Preserve structural facts, fixed dead-byte parameter D, and all existing source/program/shape preconditions.
- Replace false same-state simulation claims with the approved guarded input-oracle form. Keep useful existing proof code and report every changed helper statement.
- Build `o1PipelineComposeTheory`.
- If the frozen statement is false, provide a concrete counterexample, without adding a premise.

## Build

`holbuild -j2 build o1PipelineComposeTheory`

## Background

GAS consumes vs_gas_readings. A pass that reorders or drops reads must choose an input oracle for each output oracle. A memory invariant may depend on gas-dependent reachability, so it belongs to the chosen input, not the output's initial oracle. The approved gas-stage definition chooses the input unconditionally, then guards the simulation and output invariant with the input invariant. At the source boundary the current S3 producer supplies memory safety at the chosen raw input: its premises do not inspect target readings. This checks premise closure of an existing admitted producer, not a substantive proof of S3.

The updated definitions in o1PassContractScript.sml are frozen for this task. gas_variant relates states equal outside vs_gas_readings. o1_stage_contract_gas has no I C vs_out antecedent and concludes `?vs_in. gas_variant vs_in vs_out /\ (I C vs_in ==> ctx_sim ... /\ I' C' vs_out)`.

Existing preserving-pass contracts remain same-state. The existing DFT contract supplies the oracle-changing row. Do not prove or weaken DFT's contract in this task; its owner supplies that proof separately. Existing admissions in the contract theory are dependencies, not new permissions to add admissions.

## Domain Constraints

- No new cheat, admission, axiom, no-GAS restriction or stronger source/stage premise.
- Preserve existing proofs; never replace an existing proof with cheat.
- Do not change executable compiler, semantics, source language, D/dead_result_rel definitions, invariant definitions or pass schedules.
- Scope edits to o1PassContract proof lemmas and o1PipelineCompose proofs. The two approved definition changes are already made and must remain unchanged.
- The false generic gas-to-same-state implication cannot be retained by assuming gas_variant is equality. Replace it with correct adapters/composition facts within the approved boundary.
- Do not edit o1ContractTheorems, DFT files, o1PipelineCorrect, e2e/source result definitions or final call theorem statements. Those consumers will be migrated on the checked composition result separately.
- The compositor may instantiate the existing DFT row, without changing that row's contract or its owner files.
- Keep the default 2.5-second tactic timeout. No TRY/ORELSE around proof search, no timeout override.
- Alan working files are not deliverables.

## Available Resources

- `venom/compiler/o1PassContractScript.sml`
- `venom/compiler/o1PipelineComposeScript.sml`
- `venom/compiler/o1ContractTheoremsScript.sml`
- `venom/compiler/o1ComposeSupportScript.sml`
- `venom/compiler/o1ScheduleDecompScript.sml`
- `venom/compiler/unitMemInvScript.sml`
- `venom/compiler/unitTransformDefsScript.sml`
- `venom/compiler/contextRawReachableScript.sml`
- `venom/compiler/ctxLookupAgreeScript.sml`
- `venom/defs/venomStateScript.sml`

## Notes

The shared definition boundary was approved by argon after actual DFT scheduling, current S3 producer and dead-byte composition checks. Source semantics and the final call theorem stay unchanged here. The owner independently checks frozen statements and forces replay after Alan returns.

# TASK: Replay the existing non-alloca allocation-map preservation proof

## Meta
Status: ready for proof
Priority: P1
Created: 2026-11-03
Location: project root

## Theorem Statement (FROZEN)

```sml
Theorem step_inst_base_allocas[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    v.vs_allocas = s.vs_allocas
Theorem remap_preserved_no_pointer_ops[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Theorem remap_preserved_mem_ops[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    allocas_in_memory s1 /\ allocas_in_memory s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    inst.inst_opcode <> ISTORE /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
           ?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Theorem immutable_op_scalar_preserved[local]:
  !inst s v. is_immutable_op inst.inst_opcode /\
             step_inst_base inst s = OK v ==>
             v.vs_block_ctx = s.vs_block_ctx /\
             (v.vs_halted <=> s.vs_halted) /\
             v.vs_call_ctx = s.vs_call_ctx /\
             v.vs_labels = s.vs_labels /\
             v.vs_accounts = s.vs_accounts /\
             v.vs_transient = s.vs_transient /\
             v.vs_params = s.vs_params /\
             v.vs_prev_hashes = s.vs_prev_hashes /\
             v.vs_code = s.vs_code /\
             v.vs_data_section = s.vs_data_section /\
             v.vs_returndata = s.vs_returndata /\
             v.vs_current_bb = s.vs_current_bb /\
             v.vs_logs = s.vs_logs /\
             v.vs_inst_idx = s.vs_inst_idx /\
             v.vs_prev_bb = s.vs_prev_bb /\
             v.vs_fmp = s.vs_fmp /\
             v.vs_call_entry_fmp = s.vs_call_entry_fmp /\
             v.vs_initial_fmp = s.vs_initial_fmp /\
             v.vs_return_pc_token = s.vs_return_pc_token /\
             v.vs_tx_ctx = s.vs_tx_ctx
Theorem immutable_op_preserves_remap[local]:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    inst.inst_opcode <> ISTORE /\ s1.vs_memory = s2.vs_memory /\
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    pointer_confined fn roots /\
    FINITE roots /\ roots SUBSET alloca_roots fn /\
    ssa_form fn /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Theorem pp_single_output[local]:
  !inst s v.
    is_pointer_preserving_op inst.inst_opcode /\
    inst.inst_opcode <> PHI /\
    step_inst_base inst s = OK v ==>
    ?out. inst.inst_outputs = [out]
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing step_inst_base_allocas proof without changing its statement.
- Repair the existing remap_preserved_no_pointer_ops proof so full replay continues.
- Repair the encountered remap_preserved_mem_ops[log] proof while preserving the full theorem statement and other opcode resumes.
- Repair the existing immutable_op_scalar_preserved and immutable_op_preserves_remap proof bodies without changing either statement.
- Repair the encountered pp_single_output proof body without changing its statement.
- Build allocaRemapProofsTheory at the default tactic limit.
- Preserve all other existing proofs, definitions and statements.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

A forced default replay at eaf96a2fa timed out at the classification gvs after opcode case splitting, with 101 goals. An independent read-only audit found this exact statement PROVABLE under current GAS-popping semantics and checked all relevant allocation-field producers. The existing proof remains intact.

## Domain Constraints

- The five previously authorized repairs now pass incrementally at 420c9d0a8. Preserve all these completed repairs and helpers. Edit only pp_single_output and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml. A needed declarative Ancestors entry is allowed if it introduces no dependency cycle. Preserve the completed allocation-map proof repair.
- All existing definitions and statements, including local declarations, are frozen. No new definitions, axioms, admissions, strengthened premises, opcode exclusions or supported-subset changes.
- Preserve all completed gas, CFG and DRET proofs.
- Default 2.5-second tactic limit; no timeout override and no TRY/ORELSE/FIRST around search.
- Report another prerequisite failure before expanding scope.
- Commit substantive source changes only; no generated TASK/PLAN/DOSSIER records.
- End commit messages with Bot: sol (OpenAI GPT-6.1 Sol).

## Available Resources

- `venom/passes/shared/proofs/allocaRemapProofsScript.sml`
- `venom/props/venomMemPropsScript.sml` (step_inst_base_preserves_allocas)
- `venom/proofs/venomMemProofsScript.sml`
- `venom/defs/venomInstScript.sml`
- `venom/defs/venomExecSemanticsScript.sml`
- `venom/defs/venomStateScript.sml`
- `venom/passes/shared/defs/allocaRemapDefsScript.sml`
- `venom/passes/shared/defs/passResidualFrameScript.sml`
- `venom/passes/shared/defs/pointerConfinedDefsScript.sml`
- `venom/passes/shared/proofs/allocaRemapSSAScript.sml`
- `venom/passes/shared/proofs/passSharedTransferScript.sml`
- `venom/passes/shared/proofs/passSharedFieldScript.sml`

- `venom/analysis/shared/defs/memLocDefsScript.sml`

## Notes

This exact statement parsed in the forced failing build. The owner separately checks frozen schemas, forced default/CI replay and dependency tags after return.

The first root now passes incrementally as 24293f5fd, but full replay stopped in the second exact existing root while discharging a GAS-readings agreement premise of the scalar bridge. An independent audit of the complete second statement, its residual frame, GAS step and SSA/pointer producers found PROVABLE under the current definitions. No new invariant or assumption is authorized or needed. This amendment permits only that second proof and necessary helper theorems; all old schemas and completed proofs remain frozen.

The incremental default-limit replay at ffd26407e passes both previously authorized roots, then stops in the distinct LOG resume at its initial full-dispatch simplification (2.5s). An independent read-only audit of the exact full remap_preserved_mem_ops statement and LOG producer/semantics found PROVABLE: existing pointer/read bounds and residual-frame equality suffice, including all gas fields. This scope extension permits only the LOG resume and necessary local helpers; no statements, definitions or completed proof bodies may change. Report any further prerequisite before expansion.

Independent read-only audit at a6abad420 finds both exact immutable-operation statements PROVABLE against their real producers and residual frame. Existing is_immutable_op contains only ILOAD/ISTORE; neither statement admits GAS. The first proof timed out at its ILOAD case dispatch. The second has the existing ISTORE exclusion and memory equality and failed at a stale reconstruction tactic with pending-deletion agreement still open. No new hypotheses or definitions are needed or authorized. This amendment permits only those two proof bodies and necessary local helpers; all completed earlier proofs and all existing schemas remain frozen.

Default replay at420c9d0a8 passes the two immutable repairs and stops at pp_single_output while unfolding the full dispatcher in its ADD branch. An independent read-only audit found this exact full statement PROVABLE: existing classification reduces it to ADD/SUB/ASSIGN and successful execution forces one output. No well-formedness, gas, SSA or stage premise is needed or authorized. Only this proof and necessary local helpers are newly in scope; preserve all other proofs/statements/definitions.

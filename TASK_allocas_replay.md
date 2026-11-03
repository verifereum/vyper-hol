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
Theorem inst_ids_fresh_after_step[local]:
  !fn bb inst s1 v.
    wf_function fn /\
    MEM bb fn.fn_blocks /\
    get_instruction bb s1.vs_inst_idx = SOME inst /\
    step_inst_base inst s1 = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (!i. s1.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
         (EL i bb.bb_instructions).inst_id NOTIN FDOM s1.vs_allocas) ==>
    !i. SUC s1.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
        (EL i bb.bb_instructions).inst_id NOTIN FDOM v.vs_allocas
Theorem exec_alloca_preserves_remap:
  !fn roots remap inst s1 s2 alloc_size out.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    wf_function fn /\
    alloca_inv s1 /\ alloca_inv s2 /\
    LENGTH s1.vs_memory <= s1.vs_alloca_next /\
    LENGTH s2.vs_memory <= s2.vs_alloca_next /\
    inst.inst_id NOTIN FDOM s1.vs_allocas /\
    fn_alloca_id_of_var fn out = SOME inst.inst_id /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [out] /\
    out IN roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\
    FLOOKUP s1.vs_allocas inst.inst_id = NONE /\
    FLOOKUP s2.vs_allocas inst.inst_id = NONE /\
    s1.vs_alloca_next + w2n alloc_size < dimword (:256) /\
    s2.vs_alloca_next + w2n alloc_size < dimword (:256) /\
    0 < w2n alloc_size ==>
    let base1 = s1.vs_alloca_next in
    let base2 = s2.vs_alloca_next in
    let sz = w2n alloc_size in
    let s1' = update_var out (n2w base1)
                (s1 with <| vs_allocas :=
                   s1.vs_allocas |+ (inst.inst_id, (base1, sz));
                   vs_alloca_next := base1 + sz |>) in
    let s2' = update_var out (n2w base2)
                (s2 with <| vs_allocas :=
                   s2.vs_allocas |+ (inst.inst_id, (base2, sz));
                   vs_alloca_next := base2 + sz |>) in
      exec_alloca inst s1 alloc_size = OK s1' /\
      exec_alloca inst s2 alloc_size = OK s2' /\
      alloca_remap_rel fn roots
        (remap |+ (inst.inst_id, base2)) s1' s2'
Theorem exec_pure3_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_pure3 f inst s1 = Error err ==>
    ?err'. exec_pure3 f inst s2 = Error err'
Theorem step_inst_base_error_transfer[local]:
  !fn roots remap inst s1 s2 err.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = Error err ==>
    ?err'. step_inst_base inst s2 = Error err'
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- Repair the existing step_inst_base_allocas proof without changing its statement.
- Repair the existing remap_preserved_no_pointer_ops proof so full replay continues.
- Repair the encountered remap_preserved_mem_ops[log] proof while preserving the full theorem statement and other opcode resumes.
- Repair the existing immutable_op_scalar_preserved and immutable_op_preserves_remap proof bodies without changing either statement.
- Repair the encountered pp_single_output proof body without changing its statement.
- Repair the encountered inst_ids_fresh_after_step proof without changing its statement.
- Repair the encountered exec_alloca_preserves_remap[sizes] and remap_preserved_mem_ops[mstore8] proof resumes without changing their statements or other resumes.
- Repair the encountered exec_pure3_error_transfer proof without changing its statement.
- Repair only the encountered SHA3 resume of step_inst_base_error_transfer, keeping its full statement and other resumes unchanged.
- Repair encountered default-limit tactic failures in the existing remap_preserved_mem_ops resumes (currently CODECOPY), keeping its full statement and completed repairs unchanged.
- Repair encountered default-limit tactic failures in step_inst_base_error_transfer resumes (currently EXTCODECOPY), keeping its full statement and completed SHA3 repair unchanged.
- Build allocaRemapProofsTheory at the default tactic limit.
- Preserve all other existing proofs, definitions and statements.

## Build

`holbuild -j2 build allocaRemapProofsTheory`

## Background

A forced default replay at eaf96a2fa timed out at the classification gvs after opcode case splitting, with 101 goals. An independent read-only audit found this exact statement PROVABLE under current GAS-popping semantics and checked all relevant allocation-field producers. The existing proof remains intact.

## Domain Constraints

- The prior six repairs, allocation-size resume and pure3 error transfer now pass incrementally at e7674da9c. Preserve all these completed repairs and helpers. Edit only inst_ids_fresh_after_step, encountered timed-out proof steps anywhere within remap_preserved_mem_ops or step_inst_base_error_transfer, including common pre-suspend prefixes (current memory classification prefix), and necessary local helper theorems in venom/passes/shared/proofs/allocaRemapProofsScript.sml. Preserve the completed LOG/MSTORE8 memory resumes, exec_pure3_error_transfer, the completed SHA3 error-transfer resume, shared exec_err_tac/error_inline_tac, and every error-transfer proof/resume that has no encountered timeout. A needed declarative Ancestors entry is allowed if it introduces no dependency cycle.
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

The next actual default-replay failure is the ALLOCA branch of inst_ids_fresh_after_step, at the broad FULL_CASE_TAC loop. Independent read-only audit of its full exact statement and producers found PROVABLE: wf_function provides instruction-ID distinctness; current-index freshness excludes a preexisting current allocation site; successful ALLOCA can add only the current ID; the existing allocation-map preservation theorem covers all other allowed opcodes, including GAS. No missing assumption or definition amendment is authorized. Only this proof and necessary local helpers are newly in scope; preserve the prior six repairs and all existing schemas.

Default replay now encounters two earlier actual prerequisite timeouts before reaching the authorized freshness proof: exec_alloca_preserves_remap[sizes] at its broad fs[] (one unchanged replay passed), and remap_preserved_mem_ops[mstore8] at full dispatcher expansion. Independent read-only audit of both complete exact theorem statements and these real obligations found PROVABLE from existing allocation-map correspondence, fresh-site/no-wrap/zero-region facts, pointer confinement, one-byte bounds and residual-frame transport. The scope now permits only these two resumes plus the already authorized freshness proof/local helpers; all completed repairs, other resumes, statements and definitions remain frozen. No new premise, invariant, opcode exclusion or supported-subset restriction is authorized.

Incremental replay at 5613bd390 bounded the allocation-size resume but stopped earlier than the pending MSTORE8/freshness obligations in exec_pure3_error_transfer: the shared exec_err_tac expansion exceeds the default tactic limit. A fresh independent audit of the exact complete statement and exec_pure3/eval_operand definitions found PROVABLE: only arity errors or failed operand evaluation can produce Error; the existing NONE-transfer premise suffices. No GAS reading or state-changing error branch is involved. This amendment permits only that additional proof and necessary local helpers. Keep the existing generic tactic and other error-transfer proofs frozen. No statement, definition or premise change is authorized.

Default replay at 9e4fb772a passes the pure3 repair and next stops in step_inst_base_error_transfer[SHA3] at error_inline_tac. Independent audit of the complete theorem against every admitted opcode/error producer found PROVABLE: structural errors and undefined operands transfer from the existing relation; PARAM/FMP_PARAM bounds use equal parameters; SHA3 has no memory-bound Error branch. This extension permits only the SHA3 resume and necessary local helpers, not shared tactics or other resumes. Preserve all previous repairs and every schema/definition. No additional assumption is authorized.

Replay at f426dcedc passes the SHA3 error transfer and unchanged MSTORE8 memory resume, but a subsequent validation stops in remap_preserved_mem_ops[codecopy]. A fresh independent audit covered the complete frozen memory-operation theorem and ALL its existing opcode resumes and found PROVABLE, including CODECOPY, MCOPY, ILOAD and LOG. Existing pointer confinement/single-occurrence ensures source and size operands are scalar, the residual frame preserves source code/data/returndata, and the existing remap/safe-access/allocas-in-memory premises support destination transport and equal memory growth. This scope extension permits bounded proof-only repair of encountered timeouts within this already audited memory-operation root. Current actual failure is CODECOPY. Preserve completed LOG/MSTORE8 repairs; no speculative cleanup, schemas, definitions, new premises or shared-tactic edits. Other theorem failures must still be reported before expanding scope.

Default replay at e7674da9c passes the new CODECOPY/DLOADBYTES success boundaries and their existing memory-operation resumes, then encounters step_inst_base_error_transfer[EXTCODECOPY] at error_inline_tac. The prior fresh independent audit covered this complete frozen root and every admitted opcode error producer, explicitly including EXTCODECOPY, and found PROVABLE. This amendment permits bounded proof-only repair of actual encountered timeouts within that already audited error-transfer root. Preserve completed SHA3/pure3 and all nonfailing resumes, plus shared tactics. Any different root still requires separate audit before scope expansion. No statement, definition, premise, opcode exclusion or timeout amendment is authorized.

The already-audited memory-operation root now has an actual timeout in its common classification prefix before the opcode resumes. This prefix is part of the SAME complete frozen theorem already independently audited against every producer. Permission covers bounded repair of this actual common-prefix timeout as well as encountered resume timeouts. The same interpretation applies to the already-audited error-transfer root. Preserve completed repairs; no speculative cleanup or other root edits. No new theorem schema, definition, premise or invariant is authorized.

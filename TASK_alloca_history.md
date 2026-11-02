# TASK: Preserve allocation history through actual execution

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Locations: venom/proofs/allocaHistoryScript.sml, lowering/allocaHistoryFragmentScript.sml

## Theorem Statement (FROZEN)

Both definitions and nine public statements below are frozen. Replace scaffold proofs.

```sml
(* Allocation order within a block survives reuse of its allocation sites.
   The instruction cursor records which sites must already exist. *)
Theory allocaHistory
Ancestors
  venomInst venomWf venomState venomExecSemantics venomExecProps
  venomMemDefs venomMemProofs finite_map list arithmetic

Definition alloca_block_order_def:
  alloca_block_order bb (sites : (num, num # num) fmap) <=>
    !i j earlier later b sz.
      i < j /\ get_instruction bb i = SOME earlier /\
      get_instruction bb j = SOME later /\
      earlier.inst_opcode = ALLOCA /\ later.inst_opcode = ALLOCA /\
      FLOOKUP sites later.inst_id = SOME (b,sz) ==>
      ?a n. FLOOKUP sites earlier.inst_id = SOME (a,n) /\ a + n <= b
End

Definition alloca_history_def:
  alloca_history func s <=>
    (!bb. MEM bb func.fn_blocks ==> alloca_block_order bb s.vs_allocas) /\
    (!bb k inst.
      lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      k < s.vs_inst_idx /\ get_instruction bb k = SOME inst /\
      inst.inst_opcode = ALLOCA ==>
      IS_SOME (FLOOKUP s.vs_allocas inst.inst_id))
End

Theorem alloca_history_empty:
  !func s. s.vs_allocas = FEMPTY /\ s.vs_inst_idx = 0 ==>
    alloca_history func s
Proof
  cheat
QED

Theorem alloca_history_frame:
  !func s t.
    alloca_history func s /\ t.vs_allocas = s.vs_allocas /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx ==>
    alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_jump:
  !func s t.
    alloca_history func s /\ t.vs_allocas = s.vs_allocas /\
    t.vs_inst_idx = 0 ==> alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_pair:
  !func s bb i j earlier later b sz.
    alloca_history func s /\ MEM bb func.fn_blocks /\ i < j /\
    get_instruction bb i = SOME earlier /\
    get_instruction bb j = SOME later /\
    earlier.inst_opcode = ALLOCA /\ later.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas later.inst_id = SOME (b,sz) ==>
    ?a n. FLOOKUP s.vs_allocas earlier.inst_id = SOME (a,n) /\ a + n <= b
Proof
  cheat
QED

Theorem alloca_history_step:
  !func s bb inst fuel ctx t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK t ==>
    alloca_history func
      (if is_terminator inst.inst_opcode then t
       else t with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  cheat
QED

Theorem alloca_history_exec_block:
  !func s bb fuel ctx t ret.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    (exec_block fuel ctx bb s = OK t \/
     exec_block fuel ctx bb s = IntRet ret t) ==>
    alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_run_blocks:
  !func s fuel ctx t ret.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    run_blocks fuel ctx func s = IntRet ret t ==> alloca_history func t
Proof
  cheat
QED

Theorem alloca_history_callee_entry:
  !func args s t. setup_callee func args s = SOME t ==>
    alloca_history func t
Proof
  cheat
QED


(* A straight-line helper retains its raw cursor; use the actual code
   slice to recover allocation history at its normalized landing. *)
Theory allocaHistoryFragment
Ancestors
  allocaHistory exprLoweringProps instIdxIndep venomWf venomInst venomState
  venomExecSemantics venomMemDefs venomMemProofs list arithmetic

Theorem alloca_history_run_inst_seq:
  !func bb s insts rest t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = insts ++ rest /\
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts /\
    run_inst_seq insts s = OK t ==>
    alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  cheat
QED

```

Do not modify these statements. Prove them as-is, or produce a counterexample.

## Completion Criteria

1. Both theories build with all nine scaffold cheats removed.
2. Preserve both definitions and all public statements exactly.
3. No new admissions, axioms, timeout overrides or executable-definition changes.
4. Commit proof sources and essential helper registration only; no harness/logs/dossiers/task files.

## Build

`holbuild -j2 build allocaHistoryTheory allocaHistoryFragmentTheory`

## Background

Concat output is followed by 64-byte scratch in the same block. Its full-word stores
can extend past output into scratch. Plain disjointness loses this order on reuse.
History is derived at actual entry, never added as a source/runtime-unit premise.

INVOKE restores caller metadata on success. Callee entry has empty allocation map
and cursor zero. Caller history is not a postcondition on callee Halt/Abort/Error.
Nested callee IntRet is consumed by INVOKE into OK/Error; a direct IntRet retains
this function's frame. run_blocks never returns OK, so its theorem covers IntRet.
Zero-sized allocations and cached reuse are included.

run_inst_seq is a lowering helper, defined in exprLoweringProps, and does not
advance the instruction cursor. The separate lowering adapter normalizes the final
cursor using the actual nonterminator code slice. Keep the generic history theory
independent of lowering.

## Domain Constraints

- Edit only the two proof sources, ancestors and essential helper registration.
- No S1/S3/compiler/semantics/existing-statement changes or stronger premises.
- No exclusions, timeout overrides or TRY/ORELSE around search; default 2.5s.
- No let in theorem statements.

## Available Resources

- venom/proofs/venomMemProofsScript.sml: allocation field/invariant preservation.
- venom/defs/venomExecSemanticsScript.sml: allocator, calls, PHIs, actual execution.
- venom/simulation/proofs/instIdxIndepScript.sml: step_inst_inst_idx_indep.
- lowering/exprLoweringPropsScript.sml: run_inst_seq definition and stepping.
- lowering/abiAllocationHistoryScript.sml: size provenance, a different property.
- lowering/allocaFrontierBoundScript.sml: INVOKE restoration helpers.
- venom/defs/venomWfScript.sml: fn_inst_ids_distinct.

## Notes

All nine statements independently audited PROVABLE before launch. Owner performs
forced CI-flag replay, export inspection and kernel dependency checks after completion.


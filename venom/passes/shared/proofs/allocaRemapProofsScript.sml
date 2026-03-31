(*
 * Alloca Remapping Proofs
 *
 * Key theorem: execution under pointer_confined is insensitive to
 * concrete alloca base addresses. If two states are related by
 * alloca_remap_rel (same non-pointer vars, corresponding memory
 * content), then executing the same instruction/block/function
 * preserves the relation.
 *
 * TOP-LEVEL:
 *   eval_operand_remap        — non-pointer operand agreement
 *   mload_remap               — MLOAD through remapped pointer
 *   mstore_remap              — MSTORE through remapped pointer
 *   step_inst_preserves_remap — step_inst preserves alloca_remap_rel
 *   run_block_preserves_remap — run_block preserves alloca_remap_rel
 *
 * Proof strategy (per instruction type under pointer_confined):
 *   - Non-pointer operands: values agree by clause 1 → same computation
 *   - Pointer operands (only in iao_ofst position): different addresses
 *     but memory content at those addresses agrees by clause 3 →
 *     MLOAD/MSTORE/MCOPY produce corresponding results
 *   - ALLOCA: produces new pointer at next_alloca_offset, which may
 *     differ. Remap extended with new mapping. Memory extended with
 *     zeroes in both states → content trivially agrees.
 *   - Pointer-preserving ops (ADD/SUB/ASSIGN/PHI): output is pointer-
 *     derived, may differ, but stays in pv → clause 1 unaffected.
 *   - Terminators: operands are non-pointer (by pointer_confined) →
 *     agree → same control flow.
 *)

Theory allocaRemapProofs
Ancestors
  allocaRemapDefs venomExecSemantics venomEffects venomInst
  venomInstProps passSharedTransfer

(* ===== Operand Agreement ===== *)

(* Non-pointer operands evaluate identically under alloca_remap_rel.
   Pointer operands may differ but are only used as addresses. *)
Theorem eval_operand_non_pointer_remap:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 /\
    (!v. op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  cheat
QED

(* ===== Memory Operation Lemmas ===== *)

(* MLOAD through corresponding pointers yields the same value.
   If addr1 is in alloca region (orig_off, sz) and addr2 is the
   remapped address, and the alloca region is at least 32 bytes
   from the address, then mload addr1 s1 = mload addr2 s2. *)
Theorem mload_alloca_remap:
  !remap s1 s2 aid orig_off sz new_off addr1_off.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    addr1_off + 32 <= sz ==>
    mload (orig_off + addr1_off) s1 = mload (new_off + addr1_off) s2
Proof
  cheat
QED

(* MSTORE through corresponding pointers preserves alloca_mem_agrees.
   Writing the same value at corresponding addresses in two states
   keeps the memory correspondence invariant. *)
Theorem mstore_preserves_alloca_mem_agrees:
  !remap s1 s2 aid orig_off sz new_off addr1_off val.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    addr1_off + 32 <= sz ==>
    alloca_mem_agrees remap
      (mstore (orig_off + addr1_off) val s1)
      (mstore (new_off + addr1_off) val s2)
Proof
  cheat
QED

(* MSTORE8 through corresponding pointers preserves alloca_mem_agrees. *)
Theorem mstore8_preserves_alloca_mem_agrees:
  !remap s1 s2 aid orig_off sz new_off addr1_off val.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    addr1_off < sz ==>
    alloca_mem_agrees remap
      (mstore8 (orig_off + addr1_off) val s1)
      (mstore8 (new_off + addr1_off) val s2)
Proof
  cheat
QED

(* ===== Instruction-Level Preservation ===== *)

(* step_inst_base preserves alloca_remap_rel for non-ALLOCA instructions
   when pointer_confined holds.
   Key insight: pointer_confined ensures pointer operands are only in
   iao_ofst positions of memory ops, or in pointer-preserving ops.
   Non-pointer operands agree. So the instruction either:
   - Computes the same scalar result (non-pointer output)
   - Accesses corresponding memory (pointer in address position)
   - Propagates a pointer value (ADD/SUB/ASSIGN/PHI, output in pv) *)
Theorem step_inst_base_preserves_remap:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (* inst is in fn *)
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  cheat
QED

(* ALLOCA preserves the relation with an extended remap.
   Both states execute ALLOCA: s1 gets base1 = next_alloca_offset s1,
   s2 gets base2 = next_alloca_offset s2. These may differ.
   The remap is extended: remap' = remap |+ (inst_id, base2).
   New region is zero-initialized in both → alloca_mem_agrees trivially. *)
Theorem exec_alloca_preserves_remap:
  !fn roots remap inst s1 s2 alloc_size.
    alloca_remap_rel fn roots remap s1 s2 /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [out] /\
    out IN roots ==>
    let v1 = exec_alloca inst s1 alloc_size in
    let v2 = exec_alloca inst s2 alloc_size in
    ?base1 base2.
      v1 = OK (update_var out (n2w base1)
                (s1 with vs_allocas :=
                   s1.vs_allocas |+ (inst.inst_id, (base1, w2n alloc_size)))) /\
      v2 = OK (update_var out (n2w base2)
                (s2 with vs_allocas :=
                   s2.vs_allocas |+ (inst.inst_id, (base2, w2n alloc_size)))) /\
      alloca_remap_rel fn roots
        (remap |+ (inst.inst_id, base2))
        (update_var out (n2w base1)
          (s1 with vs_allocas :=
             s1.vs_allocas |+ (inst.inst_id, (base1, w2n alloc_size))))
        (update_var out (n2w base2)
          (s2 with vs_allocas :=
             s2.vs_allocas |+ (inst.inst_id, (base2, w2n alloc_size))))
Proof
  cheat
QED

(* ===== Block/Function-Level Preservation ===== *)

(* Terminators: operands are non-pointer (by pointer_confined),
   so they agree → same control flow decision → same next block. *)
Theorem terminator_same_target_remap:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    is_terminator inst.inst_opcode /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    (* Terminator operands agree, so eval_operand produces same result,
       hence the same branch/halt/revert decision.
       Note: terminators don't modify state beyond control flow,
       so the relation is preserved trivially. *)
    (!op. MEM op inst.inst_operands ==> eval_operand op s1 = eval_operand op s2)
Proof
  cheat
QED

(* run_block preserves alloca_remap_rel.
   By induction on block instructions, using step_inst_base_preserves_remap
   for each non-terminator, and terminator_same_target_remap at the end. *)
Theorem run_block_preserves_remap:
  !fn roots remap bb fuel ctx s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks ==>
    ?remap'.
      (* remap' extends remap with any new alloca mappings *)
      FDOM remap SUBSET FDOM remap' /\
      (!aid. aid IN FDOM remap ==> FLOOKUP remap' aid = FLOOKUP remap aid) /\
      lift_result
        (alloca_remap_rel fn roots remap')
        (alloca_remap_rel fn roots remap')
        (run_block fuel ctx bb s1)
        (run_block fuel ctx bb s2)
Proof
  cheat
QED

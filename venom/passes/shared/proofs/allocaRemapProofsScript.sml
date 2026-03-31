(*
 * Alloca Remapping Proofs
 *
 * Key theorem: execution under pointer_confined is insensitive to
 * concrete alloca base addresses. If two states are related by
 * alloca_remap_rel (same non-pointer vars, corresponding memory,
 * non-overlapping regions), then executing the same instruction/block
 * preserves the relation.
 *
 * TOP-LEVEL:
 *   eval_operand_remap           — non-pointer operand agreement
 *   mem_byte_at_remap            — byte access through remapped pointers
 *   mload_alloca_remap           — MLOAD through remapped pointer
 *   mstore_preserves_remap       — MSTORE preserves alloca_mem_agrees +
 *                                  non-alloca memory agreement
 *   mstore8_preserves_remap      — MSTORE8 preserves same
 *   step_inst_base_preserves_remap — per-instruction preservation
 *   exec_alloca_preserves_remap  — ALLOCA extends remap
 *   terminator_remap             — terminators: same control flow +
 *                                  observable result equiv for RETURN/REVERT
 *   run_block_preserves_remap    — block-level preservation
 *
 * Proof strategy (per instruction type under pointer_confined):
 *   - Non-pointer operands: values agree by clause 1 → same computation
 *   - Pointer operands (only in iao_ofst position): different addresses
 *     but memory content at those addresses agrees by clause 3 →
 *     MLOAD/MSTORE/MCOPY produce corresponding results
 *   - ALLOCA: new region zero-initialized in both → agrees trivially.
 *     Non-overlapping preserved (new region appended past existing).
 *   - Pointer-preserving ops (ADD/SUB/ASSIGN/PHI): output in pv,
 *     may differ, clause 1 unaffected for non-pv vars.
 *   - Terminators: JMP/JNZ/STOP operands are non-pointer → agree →
 *     same control flow. RETURN/REVERT have pointer in offset position
 *     but read corresponding memory → same return/revert data.
 *)

Theory allocaRemapProofs
Ancestors
  allocaRemapDefs venomExecSemantics venomEffects venomInst
  venomInstProps passSharedTransfer

(* ===== Operand Agreement ===== *)

(* Non-pointer operands evaluate identically under alloca_remap_rel. *)
Theorem eval_operand_non_pointer_remap:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 /\
    (!v. op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  cheat
QED

(* ===== Memory Byte Lemmas ===== *)

(* Byte access through corresponding alloca pointers yields same byte. *)
Theorem mem_byte_at_alloca_remap:
  !remap s1 s2 aid orig_off sz new_off i.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    i < sz ==>
    mem_byte_at s1.vs_memory (orig_off + i) =
    mem_byte_at s2.vs_memory (new_off + i)
Proof
  cheat
QED

(* Byte access OUTSIDE alloca regions yields same byte. *)
Theorem mem_byte_at_non_alloca_remap:
  !fn roots remap s1 s2 i.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~in_alloca_region s1 i ==>
    mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i
Proof
  cheat
QED

(* ===== Memory Operation Lemmas ===== *)

(* MLOAD through corresponding alloca pointers yields the same value.
   Requires the 32-byte read to stay within the alloca region. *)
Theorem mload_alloca_remap:
  !remap s1 s2 aid orig_off sz new_off rel_off.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + 32 <= sz ==>
    mload (orig_off + rel_off) s1 = mload (new_off + rel_off) s2
Proof
  cheat
QED

(* MSTORE within an alloca region preserves:
   - alloca_mem_agrees (same value written at corresponding offsets)
   - non-alloca memory agreement (write is within region, doesn't touch outside)
   - allocas_non_overlapping (regions unchanged) *)
Theorem mstore_preserves_remap_mem:
  !fn roots remap s1 s2 aid orig_off sz new_off rel_off val.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + 32 <= sz ==>
    let s1' = mstore (orig_off + rel_off) val s1 in
    let s2' = mstore (new_off + rel_off) val s2 in
      alloca_mem_agrees remap s1' s2' /\
      (!i. ~in_alloca_region s1 i ==>
           mem_byte_at s1'.vs_memory i = mem_byte_at s2'.vs_memory i) /\
      allocas_non_overlapping s1' /\
      allocas_non_overlapping s2'
Proof
  cheat
QED

(* MSTORE8 within an alloca region preserves the same properties. *)
Theorem mstore8_preserves_remap_mem:
  !fn roots remap s1 s2 aid orig_off sz new_off rel_off val.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off < sz ==>
    let s1' = mstore8 (orig_off + rel_off) val s1 in
    let s2' = mstore8 (new_off + rel_off) val s2 in
      alloca_mem_agrees remap s1' s2' /\
      (!i. ~in_alloca_region s1 i ==>
           mem_byte_at s1'.vs_memory i = mem_byte_at s2'.vs_memory i) /\
      allocas_non_overlapping s1' /\
      allocas_non_overlapping s2'
Proof
  cheat
QED

(* read_memory through corresponding alloca pointers yields same bytes.
   Used by MCOPY, RETURN, REVERT, SHA3, LOG, CREATE, etc.
   Requires the read to stay within the alloca region. *)
Theorem read_memory_alloca_remap:
  !remap s1 s2 aid orig_off sz new_off rel_off n.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + n <= sz ==>
    read_memory (orig_off + rel_off) n s1 =
    read_memory (new_off + rel_off) n s2
Proof
  cheat
QED

(* ===== Instruction-Level Preservation ===== *)

(* step_inst_base preserves alloca_remap_rel for non-ALLOCA,
   non-terminator, non-ext-call instructions under pointer_confined.
   Cases:
   - Effect-free (ADD, MUL, EQ, etc.): non-pointer operands agree →
     same result → update_var preserves clause 1. Pointer-preserving
     ops (ADD/SUB/ASSIGN/PHI): output in pv, allowed to differ.
   - Memory read (MLOAD, ILOAD): pointer in iao_ofst, data loaded
     agrees by mload_alloca_remap. Output is non-pointer (not in
     pointer_derived_vars since MLOAD is not pointer-preserving).
   - Memory write (MSTORE, MSTORE8, ISTORE, MCOPY, etc.): pointer in
     iao_ofst, same value written at corresponding addresses. Memory
     correspondence preserved by mstore_preserves_remap_mem.
   - Storage/transient (SLOAD, SSTORE, TLOAD, TSTORE): no pointer
     operands (not mem ops, not pointer-preserving). Operands agree →
     same result.
   - PHI: resolve_phi uses vs_prev_bb (agrees). Output in pv.
   - PARAM: uses vs_params (agrees). Output non-pointer. *)
Theorem step_inst_base_preserves_remap:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  cheat
QED

(* ALLOCA preserves the relation with an extended remap.
   Both states execute ALLOCA, getting base1/base2 from next_alloca_offset
   (may differ). New region is zero-initialized → alloca_mem_agrees
   trivially. Non-overlapping preserved: new region is appended past
   all existing regions (next_alloca_offset >= off+sz for all existing). *)
Theorem exec_alloca_preserves_remap:
  !fn roots remap inst s1 s2 alloc_size out.
    alloca_remap_rel fn roots remap s1 s2 /\
    inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [out] /\
    out IN roots ==>
    let base1 = next_alloca_offset s1 in
    let base2 = next_alloca_offset s2 in
    let sz = w2n alloc_size in
    let s1' = update_var out (n2w base1)
                (s1 with vs_allocas :=
                   s1.vs_allocas |+ (inst.inst_id, (base1, sz))) in
    let s2' = update_var out (n2w base2)
                (s2 with vs_allocas :=
                   s2.vs_allocas |+ (inst.inst_id, (base2, sz))) in
      exec_alloca inst s1 alloc_size = OK s1' /\
      exec_alloca inst s2 alloc_size = OK s2' /\
      alloca_remap_rel fn roots
        (remap |+ (inst.inst_id, base2)) s1' s2'
Proof
  cheat
QED

(* ===== Terminator Handling ===== *)

(* JMP/JNZ/STOP/DJMP: operands are non-pointer (by pointer_confined —
   these are terminators with no mem_read_ops/mem_write_ops and are
   not pointer-preserving), so operands agree → same control flow. *)
Theorem terminator_control_flow_remap:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> RETURN /\
    inst.inst_opcode <> REVERT /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2)
Proof
  cheat
QED

(* RETURN/REVERT: offset operand may be pointer-derived (it's the
   iao_ofst of mem_read_ops). The offset values differ, but the
   memory content at corresponding addresses agrees → same return/
   revert data. Size operand is non-pointer → agrees → same length.
   Result: the halted/reverted state has identical observable output
   (returndata, accounts, logs, etc.) *)
Theorem return_revert_remap:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    (* Size operand agrees (non-pointer) *)
    (!sz_op. MEM sz_op inst.inst_operands /\
             (!v. sz_op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
             eval_operand sz_op s1 = eval_operand sz_op s2) /\
    (* Memory content read by RETURN/REVERT agrees:
       offset may be pointer-derived but reads corresponding memory *)
    (case inst.inst_operands of
       [off_op; sz_op] =>
         !off1 off2 n.
           eval_operand off_op s1 = SOME off1 /\
           eval_operand off_op s2 = SOME off2 /\
           eval_operand sz_op s1 = SOME n ==>
           read_memory (w2n off1) (w2n n) s1 =
           read_memory (w2n off2) (w2n n) s2
     | _ => T)
Proof
  cheat
QED

(* ===== Block/Function-Level Preservation ===== *)

(* run_block preserves alloca_remap_rel.
   By induction on block instructions:
   - Non-terminators: step_inst_base_preserves_remap (or exec_alloca)
   - JMP/JNZ/STOP/DJMP: terminator_control_flow_remap → same next block
   - RETURN/REVERT: return_revert_remap → equivalent halt/revert result
   remap' extends remap with any new alloca mappings from the block. *)
Theorem run_block_preserves_remap:
  !fn roots remap bb fuel ctx s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks ==>
    ?remap'.
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

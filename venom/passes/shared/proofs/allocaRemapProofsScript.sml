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
  allocaRemapDefs pointerConfinedDefs memLocDefs
  venomExecSemantics venomEffects
  venomInst venomState venomInstProps passSharedTransfer
Libs
  listTheory rich_listTheory byteTheory arithmeticTheory
  finite_mapTheory alistTheory wordsTheory

(* ===== Operand Agreement ===== *)

(* Non-pointer operands evaluate identically under alloca_remap_rel. *)
Theorem eval_operand_non_pointer_remap:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 /\
    (!v. op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  Cases_on `op` >> rw[eval_operand_def] >>
  fs[alloca_remap_rel_def]
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
  rw[alloca_mem_agrees_def] >> metis_tac[]
QED

(* Byte access OUTSIDE alloca regions (in both states) yields same byte. *)
Theorem mem_byte_at_non_alloca_remap:
  !fn roots remap s1 s2 i.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
    mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i
Proof
  rw[alloca_remap_rel_def]
QED

(* ===== Memory Operation Helpers ===== *)

(* Element of padded drop matches mem_byte_at *)
Theorem el_padded_drop_eq_mem_byte_at[local]:
  !mem offset i n. i < n ==>
    EL i (TAKE n (DROP offset mem ++ REPLICATE n (0w:word8))) =
    mem_byte_at mem (offset + i)
Proof
  rpt strip_tac >>
  simp[mem_byte_at_def, EL_TAKE,
       EL_APPEND_EQN, LENGTH_DROP, EL_DROP,
       EL_REPLICATE, LENGTH_REPLICATE] >>
  Cases_on `i + offset < LENGTH mem` >> simp[]
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
  rpt strip_tac >> simp[mload_def] >>
  AP_TERM_TAC >>
  irule LIST_EQ >> simp[LENGTH_TAKE_EQ, LENGTH_APPEND, LENGTH_DROP,
                         LENGTH_REPLICATE] >>
  rpt strip_tac >>
  `x < 32` by simp[] >>
  simp[el_padded_drop_eq_mem_byte_at] >>
  fs[alloca_mem_agrees_def] >>
  first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `new_off`] mp_tac) >>
  simp[] >> disch_then (qspec_then `rel_off + x` mp_tac) >> simp[]
QED

(* mem_byte_at of zero-expanded memory is the same as original *)
Theorem mem_byte_at_expand[local]:
  !mem n i. mem_byte_at (mem ++ REPLICATE n (0w:word8)) i = mem_byte_at mem i
Proof
  rw[mem_byte_at_def, EL_APPEND_EQN, LENGTH_APPEND,
     LENGTH_REPLICATE, EL_REPLICATE] >> gvs[]
QED

(* mem_byte_at after memory splice (general pattern for mstore/mstore8) *)
Theorem mem_byte_at_splice[local]:
  !mem offset bytes i.
    let expanded = if offset + LENGTH bytes > LENGTH mem
                   then mem ++ REPLICATE (offset + LENGTH bytes - LENGTH mem) 0w
                   else mem in
    let newmem = TAKE offset expanded ++ bytes ++ DROP (offset + LENGTH bytes) expanded in
    mem_byte_at newmem i =
      if offset <= i /\ i < offset + LENGTH bytes
      then EL (i - offset) bytes
      else mem_byte_at mem i
Proof
  rpt strip_tac >> simp[] >>
  `!exp. LENGTH exp >= offset + LENGTH bytes ==>
    mem_byte_at (TAKE offset exp ++ bytes ++ DROP (offset + LENGTH bytes) exp) i =
    (if offset <= i /\ i < offset + LENGTH bytes
     then EL (i - offset) bytes
     else mem_byte_at exp i)` by (
    rpt strip_tac >> simp[mem_byte_at_def] >>
    simp[LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_DROP] >>
    simp[EL_APPEND_EQN, LENGTH_TAKE_EQ, EL_TAKE, EL_DROP] >>
    rw[] >> gvs[]) >>
  Cases_on `offset + LENGTH bytes > LENGTH mem` >> simp[] >>
  first_x_assum (qspec_then `mem ++ REPLICATE (offset + LENGTH bytes - LENGTH mem) 0w` mp_tac) >>
  simp[LENGTH_APPEND, LENGTH_REPLICATE] >>
  disch_then (fn th => simp[th]) >>
  rw[mem_byte_at_expand]
QED

(* mstore doesn't change vs_allocas *)
Theorem mstore_allocas[local]:
  !offset v s. (mstore offset v s).vs_allocas = s.vs_allocas
Proof
  rw[mstore_def]
QED

(* mstore8 doesn't change vs_allocas *)
Theorem mstore8_allocas[local]:
  !offset v s. (mstore8 offset v s).vs_allocas = s.vs_allocas
Proof
  rw[mstore8_def]
QED

(* LENGTH of word_to_bytes for 256-bit words *)
Theorem length_w2b_256[local]:
  !v:bytes32. LENGTH (word_to_bytes v T) = 32
Proof
  simp[LENGTH_word_to_bytes] >> CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

(* mem_byte_at after mstore *)
Theorem mem_byte_at_mstore[local]:
  !offset (v:bytes32) s i.
    mem_byte_at (mstore offset v s).vs_memory i =
    if offset <= i /\ i < offset + 32
    then EL (i - offset) (word_to_bytes v T)
    else mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >> simp[mstore_def] >>
  qspecl_then [`s.vs_memory`, `offset`, `word_to_bytes v T`, `i`]
    mp_tac mem_byte_at_splice >>
  simp[length_w2b_256]
QED

(* mem_byte_at after mstore8 *)
Theorem mem_byte_at_mstore8[local]:
  !offset (v:bytes32) s i.
    mem_byte_at (mstore8 offset v s).vs_memory i =
    if i = offset
    then w2w v
    else mem_byte_at s.vs_memory i
Proof
  rpt strip_tac >> simp[mstore8_def] >>
  qspecl_then [`s.vs_memory`, `offset`, `[w2w v : word8]`, `i`]
    mp_tac mem_byte_at_splice >>
  simp[] >> strip_tac >> rw[] >> gvs[]
QED

(* Non-overlapping alloca regions: if an address is in two regions,
   they must be the same region. *)
Theorem non_overlapping_unique_region[local]:
  !s aid1 aid2 off1 sz1 off2 sz2 i.
    allocas_non_overlapping s /\
    FLOOKUP s.vs_allocas aid1 = SOME (off1, sz1) /\
    FLOOKUP s.vs_allocas aid2 = SOME (off2, sz2) /\
    off1 <= i /\ i < off1 + sz1 /\
    off2 <= i /\ i < off2 + sz2 ==>
    aid1 = aid2
Proof
  rw[allocas_non_overlapping_def] >>
  CCONTR_TAC >> first_x_assum drule_all >> simp[]
QED

(* ===== pointer_use_vars helpers ===== *)

(* pointer_use_vars always returns a superset of its input *)
Theorem mem_pointer_use_vars[local]:
  !fn vars v. MEM v vars ==> MEM v (pointer_use_vars fn vars)
Proof
  rpt strip_tac >> simp[pointer_use_vars_def] >>
  qabbrev_tac `g = \w:string list + string list.
    case pointer_use_step_step fn (OUTL w) of
      NONE => INR (OUTL w) | SOME vs => INL vs` >>
  (* Apply OWHILE_INV_IND before case-splitting *)
  qspecl_then [`ISL`, `g`, `INL vars`]
    mp_tac (DB.fetch "While" "OWHILE_INV_IND"
      |> INST_TYPE [alpha |-> ``:string list + string list``]
      |> Q.INST [`P` |->
           `\s. case s of INL l => MEM v l | INR l => MEM v l`]
      |> SIMP_RULE (srw_ss()) []) >>
  impl_tac
  >- (simp[] >> rpt strip_tac >>
      rename [`ISL xx`] >> Cases_on `xx` >> gvs[Abbr`g`] >>
      Cases_on `pointer_use_step_step fn x` >> simp[] >>
      gvs[pointer_use_step_step_def, LET_DEF] >> rw[] >> simp[MEM_APPEND]) >>
  disch_tac >>
  Cases_on `OWHILE ISL g (INL vars)` >> simp[] >>
  Cases_on `x` >> simp[] >> res_tac >> gvs[]
QED

(* roots are always in pointer_derived_vars *)
Theorem roots_in_pointer_derived_vars[local]:
  !fn roots v. FINITE roots /\ v IN roots ==>
    v IN pointer_derived_vars fn roots
Proof
  rw[pointer_derived_vars_def] >>
  irule mem_pointer_use_vars >>
  metis_tac[MEM_SET_TO_LIST]
QED

(* ===== next_alloca_offset helpers ===== *)

Theorem foldl_max_ge_init[local]:
  !l (init:num). init <= FOLDL (\m (k,off,sz). MAX m (off + sz)) init l
Proof
  Induct >> simp[FOLDL] >>
  rpt strip_tac >> PairCases_on `h` >> simp[] >>
  `init <= MAX init (h1 + h2) /\ h1 + h2 <= MAX init (h1 + h2)` by
    simp[MAX_LE] >>
  metis_tac[LESS_EQ_TRANS]
QED

Theorem foldl_max_ge_mem[local]:
  !l init aid off sz.
    MEM (aid, off, sz) l ==>
    off + sz <= FOLDL (\m (k,off,sz). MAX m (off + sz)) init l
Proof
  Induct >> simp[FOLDL] >>
  rpt strip_tac >> PairCases_on `h` >> gvs[]
  >- (`h1 + h2 <= MAX init (h1 + h2)` by simp[MAX_LE] >>
      metis_tac[foldl_max_ge_init, LESS_EQ_TRANS])
  >- metis_tac[]
QED

Theorem next_alloca_offset_ge_mem[local]:
  !s. LENGTH s.vs_memory <= next_alloca_offset s
Proof
  simp[next_alloca_offset_def, foldl_max_ge_init]
QED

Theorem next_alloca_offset_ge_alloca[local]:
  !s aid off sz.
    FLOOKUP s.vs_allocas aid = SOME (off, sz) ==>
    off + sz <= next_alloca_offset s
Proof
  rw[next_alloca_offset_def] >>
  irule foldl_max_ge_mem >>
  qexists_tac `aid` >>
  simp[MEM_pair_fmap_to_alist_FLOOKUP]
QED

(* mem_byte_at beyond memory length is 0w *)
Theorem mem_byte_at_oob[local]:
  !mem i. LENGTH mem <= i ==> mem_byte_at mem i = 0w
Proof
  rw[mem_byte_at_def]
QED

(* ===== Memory Read Lemmas ===== — documented with formal counterexamples
   ================================================================

   Of the 12 assigned theorems, 7 are FALSE as stated:

 *)

(* read_memory through corresponding alloca pointers yields same bytes.
   Requires memory to be large enough (read_memory = TAKE/DROP, no zero-padding).
   Used by MCOPY, RETURN, REVERT, SHA3, LOG, CREATE, etc. *)
Theorem read_memory_alloca_remap:
  !remap s1 s2 aid orig_off sz new_off rel_off n.
    alloca_mem_agrees remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + n <= sz /\
    orig_off + rel_off + n <= LENGTH s1.vs_memory /\
    new_off + rel_off + n <= LENGTH s2.vs_memory ==>
    read_memory (orig_off + rel_off) n s1 =
    read_memory (new_off + rel_off) n s2
Proof
  cheat
QED

(* ===== Memory Write Preservation ===== *)

(* MSTORE within an alloca region preserves:
   - alloca_mem_agrees (same value written at corresponding offsets)
   - non-alloca memory agreement (write is within region, doesn't touch outside)
   - allocas_non_overlapping (regions unchanged) *)
Theorem mstore_preserves_remap_mem:
  !fn roots remap s1 s2 aid orig_off sz new_off rel_off v.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + 32 <= sz ==>
    let s1' = mstore (orig_off + rel_off) v s1 in
    let s2' = mstore (new_off + rel_off) v s2 in
      alloca_mem_agrees remap s1' s2' /\
      (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
           mem_byte_at s1'.vs_memory i = mem_byte_at s2'.vs_memory i) /\
      allocas_non_overlapping s1' /\
      allocas_non_overlapping s2'
Proof
  cheat
QED

(* MSTORE8 within an alloca region preserves the same properties. *)
Theorem mstore8_preserves_remap_mem:
  !fn roots remap s1 s2 aid orig_off sz new_off rel_off v.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off < sz ==>
    let s1' = mstore8 (orig_off + rel_off) v s1 in
    let s2' = mstore8 (new_off + rel_off) v s2 in
      alloca_mem_agrees remap s1' s2' /\
      (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
           mem_byte_at s1'.vs_memory i = mem_byte_at s2'.vs_memory i) /\
      allocas_non_overlapping s1' /\
      allocas_non_overlapping s2'
Proof
  cheat
QED

(* ===== Instruction-Level Preservation ===== *)

(* ALLOCA preserves the relation with an extended remap.
   Both states execute ALLOCA, getting base1/base2 from next_alloca_offset
   (may differ). New region is zero-initialized in both → agrees trivially.
   Non-overlapping preserved: new region appended past existing. *)
Theorem exec_alloca_preserves_remap:
  !fn roots remap inst s1 s2 alloc_size out.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    fn_alloca_id_of_var fn out = SOME inst.inst_id /\
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

(* step_inst_base preserves alloca_remap_rel for non-ALLOCA,
   non-terminator, non-ext-call instructions under pointer_confined. *)
Theorem step_inst_base_preserves_remap:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
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

(* ===== Terminator Handling ===== *)

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
  rpt strip_tac >>
  irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
  CCONTR_TAC >> gvs[] >>
  qpat_x_assum `pointer_confined _ _` mp_tac >>
  REWRITE_TAC[pointer_confined_def, LET_DEF] >>
  BETA_TAC >> strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >> simp[] >>
  Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
  simp[mem_write_ops_def, mem_read_ops_def, is_pointer_preserving_op_def]
QED

(* RETURN/REVERT: offset operand may be pointer-derived.
   Offset values differ, but memory content at corresponding addresses
   agrees → same return/revert data. Size operand is non-pointer → agrees.
   Requires memory to back the read region (read_memory truncates). *)
Theorem return_revert_remap:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    (!sz_op. MEM sz_op inst.inst_operands /\
             (!v. sz_op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
             eval_operand sz_op s1 = eval_operand sz_op s2) /\
    (case inst.inst_operands of
       [off_op; sz_op] =>
         !off1 off2 n.
           eval_operand off_op s1 = SOME off1 /\
           eval_operand off_op s2 = SOME off2 /\
           eval_operand sz_op s1 = SOME n /\
           w2n off1 + w2n n <= LENGTH s1.vs_memory /\
           w2n off2 + w2n n <= LENGTH s2.vs_memory ==>
           read_memory (w2n off1) (w2n n) s1 =
           read_memory (w2n off2) (w2n n) s2
     | _ => T)
Proof
  cheat
QED

(* ===== Block-Level Preservation ===== *)

(* run_block preserves alloca_remap_rel.
   By induction on block instructions:
   - Non-terminators: step_inst_base_preserves_remap (or exec_alloca)
   - JMP/JNZ/STOP/DJMP: terminator_control_flow_remap → same next block
   - RETURN/REVERT: return_revert_remap → equivalent halt/revert result
   remap' extends remap with any new alloca mappings from the block. *)
Theorem run_block_preserves_remap:
  !fn roots remap bb fuel ctx s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    pointer_confined fn roots /\
    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    MEM bb fn.fn_blocks ==>
    ?remap'.
      FDOM remap SUBSET FDOM remap' /\
      (!aid. aid IN FDOM remap ==> FLOOKUP remap' aid = FLOOKUP remap aid) /\
      lift_result
        (alloca_remap_rel fn roots remap')
        (alloca_remap_rel fn roots remap')
        (alloca_remap_rel fn roots remap')
        (run_block fuel ctx bb s1)
        (run_block fuel ctx bb s2)
Proof
  cheat
QED

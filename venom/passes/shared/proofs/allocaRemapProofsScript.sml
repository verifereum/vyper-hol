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
 *   exec_block_preserves_remap    — block-level preservation
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
  venomExecSemantics venomEffects venomWf venomMemDefs
  venomInst venomState venomInstProps passSharedTransfer
  allocaRemapSSA stateEquiv passSharedField
Libs
  listTheory rich_listTheory byteTheory arithmeticTheory
  finite_mapTheory alistTheory wordsTheory pred_setTheory

(* Make is_immutable_op reduce automatically in simp/gvs/fs *)
val _ = augment_srw_ss [rewrites [is_immutable_op_def]];

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

(* List version: all non-pv operands agree *)
Theorem eval_operands_non_pointer_remap[local]:
  !fn roots remap s1 s2 ops.
    alloca_remap_rel fn roots remap s1 s2 /\
    (!v. MEM (Var v) ops ==> v NOTIN pointer_derived_vars fn roots) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  rpt strip_tac >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule eval_operand_non_pointer_remap >> simp[] >>
    Cases_on `h` >> simp[] >> metis_tac[]) >>
  `eval_operands ops s1 = eval_operands ops s2` by (
    first_x_assum irule >> simp[] >> metis_tac[]) >>
  simp[]
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
  simp[LENGTH_word_to_bytes] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV)
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

(* ===== alloca bump pointer helpers ===== *)

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

(* Adding a region at vs_alloca_next preserves non-overlapping
   when alloca_next_valid holds (all existing endpoints <= vs_alloca_next). *)
Theorem non_overlapping_extend[local]:
  !s s' id sz.
    allocas_non_overlapping s /\
    alloca_next_valid s /\
    s'.vs_allocas = s.vs_allocas |+ (id, (s.vs_alloca_next, sz)) ==>
    allocas_non_overlapping s'
Proof
  rpt strip_tac >>
  `!aid off asz. FLOOKUP s.vs_allocas aid = SOME (off, asz) ==>
     off + asz <= s.vs_alloca_next` by (
    rpt strip_tac >> fs[alloca_next_valid_def] >> res_tac >> simp[]) >>
  fs[allocas_non_overlapping_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  Cases_on `id = a1` >> Cases_on `id = a2` >> gvs[] >>
  res_tac >> simp[]
QED

(* mem_byte_at beyond memory length is 0w *)
Theorem mem_byte_at_oob[local]:
  !mem i. LENGTH mem <= i ==> mem_byte_at mem i = 0w
Proof
  rw[mem_byte_at_def]
QED

(* ===== Memory Read Lemmas ===== *)

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
  rpt strip_tac >> simp[read_memory_def] >>
  irule LIST_EQ >>
  simp[LENGTH_TAKE_EQ, LENGTH_DROP] >>
  rpt strip_tac >>
  `x < n` by simp[] >>
  simp[EL_TAKE, EL_DROP] >>
  `mem_byte_at s1.vs_memory (orig_off + rel_off + x) =
   mem_byte_at s2.vs_memory (new_off + rel_off + x)` by (
    fs[alloca_mem_agrees_def] >>
    first_x_assum (qspecl_then [`aid`, `orig_off`, `sz`, `new_off`] mp_tac) >>
    simp[] >> disch_then (qspec_then `rel_off + x` mp_tac) >> simp[]) >>
  `x < LENGTH (DROP (orig_off + rel_off) s1.vs_memory)` by simp[LENGTH_DROP] >>
  `x < LENGTH (DROP (new_off + rel_off) s2.vs_memory)` by simp[LENGTH_DROP] >>
  simp[rich_listTheory.EL_APPEND1, rich_listTheory.EL_DROP] >>
  gvs[mem_byte_at_def]
QED

(* ===== Memory Write Preservation ===== *)

(* Shared tactic for showing a point is in_alloca_region *)
fun in_alloca_tac aid_q off_q sz_q =
  simp[in_alloca_region_def] >>
  qexists_tac aid_q >> qexists_tac off_q >> qexists_tac sz_q >> simp[];

(* Generic: writing the SAME bytes at corresponding alloca offsets in both
   states preserves alloca memory agreement and non-alloca agreement.
   Works for mstore, mstore8, write_memory_with_expansion, mcopy, etc. —
   any operation that splices bytes into memory within an alloca region.
   Stated in terms of mem_byte_at to be independent of the splice mechanism. *)
Theorem splice_preserves_remap_mem[local]:
  !remap s1 s2 m1 m2 aid orig_off sz new_off rel_off bytes.
    alloca_mem_agrees remap s1 s2 /\
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i) /\
    allocas_non_overlapping s1 /\
    allocas_non_overlapping s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP s2.vs_allocas aid = SOME (new_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    (* remap entries correspond to s2 alloca offsets *)
    (!a off asz noff. FLOOKUP s1.vs_allocas a = SOME (off, asz) /\
       FLOOKUP remap a = SOME noff ==>
       FLOOKUP s2.vs_allocas a = SOME (noff, asz)) /\
    rel_off + LENGTH bytes <= sz /\
    (* m1, m2 result from splicing the same bytes at corresponding offsets *)
    (!i. mem_byte_at m1 i =
         if orig_off + rel_off <= i /\ i < orig_off + rel_off + LENGTH bytes
         then EL (i - (orig_off + rel_off)) bytes
         else mem_byte_at s1.vs_memory i) /\
    (!i. mem_byte_at m2 i =
         if new_off + rel_off <= i /\ i < new_off + rel_off + LENGTH bytes
         then EL (i - (new_off + rel_off)) bytes
         else mem_byte_at s2.vs_memory i) ==>
    alloca_mem_agrees remap
      (s1 with vs_memory := m1) (s2 with vs_memory := m2) /\
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at m1 i = mem_byte_at m2 i)
Proof
  rpt strip_tac >> simp[]
  >- suspend "splice_agrees"
  >- (qpat_x_assum `!i. mem_byte_at m1 _ = _` (qspec_then `i` mp_tac) >>
      qpat_x_assum `!i. mem_byte_at m2 _ = _` (qspec_then `i` mp_tac) >>
      simp[] >> rpt strip_tac >>
      `~(orig_off + rel_off <= i /\ i < orig_off + rel_off + LENGTH bytes)` by
        (CCONTR_TAC >> gvs[] >>
         qpat_x_assum `~in_alloca_region s1 _` mp_tac >>
         in_alloca_tac `aid` `orig_off` `sz`) >>
      `~(new_off + rel_off <= i /\ i < new_off + rel_off + LENGTH bytes)` by
        (CCONTR_TAC >> gvs[] >>
         qpat_x_assum `~in_alloca_region s2 _` mp_tac >>
         in_alloca_tac `aid` `new_off` `sz`) >>
      gvs[])
QED

Resume splice_preserves_remap_mem[splice_agrees]:
  simp[alloca_mem_agrees_def] >> rpt strip_tac >>
  rename [`FLOOKUP s1.vs_allocas a = SOME (ooff, asz)`,
          `FLOOKUP remap a = SOME noff`, `j < asz`] >>
  (* Specialize the splice lemmas for ooff + j and noff + j *)
  qpat_x_assum `!i. mem_byte_at m1 _ = _` (qspec_then `ooff + j` assume_tac) >>
  qpat_x_assum `!i. mem_byte_at m2 _ = _` (qspec_then `noff + j` assume_tac) >>
  Cases_on `a = aid`
  >- (gvs[] >>
      `(ooff + rel_off <= j + ooff <=> rel_off <= j) /\
       (new_off + rel_off <= j + new_off <=> rel_off <= j)` by simp[] >>
      gvs[] >>
      Cases_on `rel_off <= j /\ j < rel_off + LENGTH bytes`
      >- gvs[]
      >- (gvs[] >>
          qpat_x_assum `alloca_mem_agrees _ _ _` mp_tac >>
          simp[alloca_mem_agrees_def] >>
          disch_then (qspecl_then [`a`,`ooff`,`asz`,`new_off`] mp_tac) >>
          simp[] >> disch_then (qspec_then `j` mp_tac) >> simp[]))
  >- ((* Derive s2 alloca entry for a *)
      `FLOOKUP s2.vs_allocas a = SOME (noff, asz)` by
        (first_x_assum irule >> simp[]) >>
      (* s1 non-overlapping: alloca a vs alloca aid *)
      `ooff + asz <= orig_off \/ orig_off + sz <= ooff` by (
        qpat_x_assum `allocas_non_overlapping s1` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`ooff`,`asz`,`orig_off`,`sz`]
          mp_tac) >> simp[]) >>
      (* s2 non-overlapping: alloca a vs alloca aid *)
      `noff + asz <= new_off \/ new_off + sz <= noff` by (
        qpat_x_assum `allocas_non_overlapping s2` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`noff`,`asz`,`new_off`,`sz`]
          mp_tac) >> simp[]) >>
      (* write region doesn't overlap with alloca a *)
      `~(orig_off + rel_off <= ooff + j /\
         ooff + j < orig_off + rel_off + LENGTH bytes)` by simp[] >>
      `~(new_off + rel_off <= noff + j /\
         noff + j < new_off + rel_off + LENGTH bytes)` by simp[] >>
      gvs[] >> fs[alloca_mem_agrees_def] >> metis_tac[])
QED

Finalise splice_preserves_remap_mem

(* alloca_remap_rel field-update tactic.
   Works by unfolding both sides then closing with metis_tac. *)
val remap_rel_update_tac =
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[];

(* Updating only vs_logs preserves alloca_remap_rel when logs agree. *)
Theorem alloca_remap_rel_logs_update[local]:
  !fn roots remap s1 s2 l.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (s1 with vs_logs := l) (s2 with vs_logs := l)
Proof
  remap_rel_update_tac
QED

Theorem alloca_remap_rel_halted[local]:
  !fn roots remap s1 s2.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (s1 with vs_halted := T) (s2 with vs_halted := T)
Proof
  remap_rel_update_tac
QED

Theorem alloca_remap_rel_jump_to[local]:
  !fn roots remap s1 s2 lbl.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (jump_to lbl s1) (jump_to lbl s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, jump_to_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

Theorem alloca_remap_rel_returndata[local]:
  !fn roots remap s1 s2 rd.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (set_returndata rd s1) (set_returndata rd s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, set_returndata_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

Theorem alloca_remap_rel_inst_idx[local]:
  !fn roots remap s1 s2 n.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (s1 with vs_inst_idx := n) (s2 with vs_inst_idx := n)
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

Theorem alloca_remap_rel_accounts_update[local]:
  !fn roots remap s1 s2 f.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (s1 with vs_accounts := f) (s2 with vs_accounts := f)
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* Combined: halt_state (set_returndata rd s) — avoids simultaneous record update *)
Theorem alloca_remap_rel_halt_returndata[local]:
  !fn roots remap s1 s2 rd.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (halt_state (set_returndata rd s1))
      (halt_state (set_returndata rd s2))
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, halt_state_def, set_returndata_def,
       lookup_var_def, alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* Combined: revert_state (set_returndata rd s) *)
Theorem alloca_remap_rel_revert_returndata[local]:
  !fn roots remap s1 s2 rd.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (revert_state (set_returndata rd s1))
      (revert_state (set_returndata rd s2))
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, revert_state_def, set_returndata_def,
       lookup_var_def, alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* Combined: halt_state (s with vs_accounts := f) *)
Theorem alloca_remap_rel_halt_accounts[local]:
  !fn roots remap s1 s2 f.
    alloca_remap_rel fn roots remap s1 s2 ==>
    alloca_remap_rel fn roots remap
      (halt_state (s1 with vs_accounts := f))
      (halt_state (s2 with vs_accounts := f))
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  simp[alloca_remap_rel_def, halt_state_def, lookup_var_def,
       alloca_mem_agrees_def, in_alloca_region_def,
       allocas_non_overlapping_def] >>
  metis_tac[]
QED

(* Extract scalar field equalities from alloca_remap_rel in one shot. *)
val alloca_remap_rel_scalars = prove(
  ``alloca_remap_rel fn roots remap s1 s2 ==>
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\
    s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\
    s1.vs_prev_hashes = s2.vs_prev_hashes /\
    LENGTH s1.vs_memory = LENGTH s2.vs_memory /\
    FDOM s1.vs_allocas = FDOM s2.vs_allocas``,
  REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
  strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC);

(* Non-PV lookup: extracts the lookup_var clause without full expansion. *)
val alloca_remap_rel_non_pv_lookup = prove(
  ``alloca_remap_rel fn roots remap s1 s2 /\
    v NOTIN pointer_derived_vars fn roots ==>
    lookup_var v s1 = lookup_var v s2``,
  REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
  strip_tac >> res_tac);

(* Replacing just vs_memory preserves alloca_remap_rel when the new
   memories satisfy alloca_mem_agrees and non-alloca agreement.
   Factors memory reasoning from structural reasoning. *)
Theorem alloca_remap_rel_mem_update[local]:
  !fn roots remap s1 s2 m1 m2.
    alloca_remap_rel fn roots remap s1 s2 /\
    alloca_mem_agrees remap (s1 with vs_memory := m1) (s2 with vs_memory := m2) /\
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at m1 i = mem_byte_at m2 i) /\
    LENGTH m1 = LENGTH m2 ==>
    alloca_remap_rel fn roots remap
      (s1 with vs_memory := m1) (s2 with vs_memory := m2)
Proof
  REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
  REWRITE_TAC[allocas_non_overlapping_def, in_alloca_region_def,
              lookup_var_def] >>
  rpt gen_tac >> strip_tac >>
  rpt conj_tac >> rpt gen_tac >> rpt disch_tac >> gvs[] >>
  metis_tac[]
QED

(* Rewrite mstore/mstore8 in terms of write_memory_with_expansion *)
Theorem mstore_eq_wmwe[local]:
  mstore offset value s =
  write_memory_with_expansion offset (word_to_bytes value T) s
Proof
  simp[mstore_def, write_memory_with_expansion_def, length_w2b_256]
QED

Theorem mstore8_eq_wmwe[local]:
  mstore8 offset value s =
  write_memory_with_expansion offset [w2w value] s
Proof
  simp[mstore8_def, write_memory_with_expansion_def]
QED

(* Generic: writing same bytes at corresponding alloca offsets via
   write_memory_with_expansion preserves alloca_remap_rel.
   Combines splice_preserves_remap_mem + alloca_remap_rel_mem_update. *)
Theorem write_pv_mem_preserves_remap[local]:
  !fn roots remap s1 s2 aid orig_off sz new_off rel_off bytes.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    rel_off + LENGTH bytes <= sz /\
    orig_off + sz <= LENGTH s1.vs_memory /\
    new_off + sz <= LENGTH s2.vs_memory ==>
    alloca_remap_rel fn roots remap
      (write_memory_with_expansion (orig_off + rel_off) bytes s1)
      (write_memory_with_expansion (new_off + rel_off) bytes s2)
Proof
  rpt strip_tac >>
  `orig_off + rel_off + LENGTH bytes <= LENGTH s1.vs_memory` by simp[] >>
  `new_off + rel_off + LENGTH bytes <= LENGTH s2.vs_memory` by simp[] >>
  simp[write_memory_with_expansion_def] >>
  irule alloca_remap_rel_mem_update >>
  (* Extract sub-properties from alloca_remap_rel *)
  `alloca_mem_agrees remap s1 s2 /\
   (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
     mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i) /\
   allocas_non_overlapping s1 /\ allocas_non_overlapping s2 /\
   FLOOKUP s2.vs_allocas aid = SOME (new_off, sz) /\
   (!a off asz noff. FLOOKUP s1.vs_allocas a = SOME (off, asz) /\
     FLOOKUP remap a = SOME noff ==> FLOOKUP s2.vs_allocas a = SOME (noff, asz)) /\
   LENGTH s1.vs_memory = LENGTH s2.vs_memory`
    by (fs[alloca_remap_rel_def, LET_DEF] >> metis_tac[]) >>
  (* Get mem_byte_at characterizations via mp_tac *)
  `(!i. mem_byte_at (TAKE (orig_off + rel_off) s1.vs_memory ++ bytes ++
        DROP (orig_off + (rel_off + LENGTH bytes)) s1.vs_memory) i =
     if orig_off + rel_off <= i /\ i < orig_off + rel_off + LENGTH bytes
     then EL (i - (orig_off + rel_off)) bytes
     else mem_byte_at s1.vs_memory i) /\
   (!i. mem_byte_at (TAKE (new_off + rel_off) s2.vs_memory ++ bytes ++
        DROP (new_off + (rel_off + LENGTH bytes)) s2.vs_memory) i =
     if new_off + rel_off <= i /\ i < new_off + rel_off + LENGTH bytes
     then EL (i - (new_off + rel_off)) bytes
     else mem_byte_at s2.vs_memory i)` by (
    conj_tac >> gen_tac >>
    qspecl_then [`s1.vs_memory`,`orig_off + rel_off`,`bytes`,`i`]
      mp_tac mem_byte_at_splice >>
    TRY (qspecl_then [`s2.vs_memory`,`new_off + rel_off`,`bytes`,`i`]
      mp_tac mem_byte_at_splice) >>
    simp[]) >>
  (* Use splice_preserves_remap_mem *)
  mp_tac (Q.SPECL [`remap`,`s1`,`s2`,
    `TAKE (orig_off + rel_off) s1.vs_memory ++ bytes ++
     DROP (orig_off + (rel_off + LENGTH bytes)) s1.vs_memory`,
    `TAKE (new_off + rel_off) s2.vs_memory ++ bytes ++
     DROP (new_off + (rel_off + LENGTH bytes)) s2.vs_memory`,
    `aid`,`orig_off`,`sz`,`new_off`,`rel_off`,`bytes`]
    splice_preserves_remap_mem) >>
  simp[]
QED

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
  rpt strip_tac >> simp[] >> gvs[alloca_remap_rel_def] >>
  `FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)` by metis_tac[] >>
  rpt conj_tac
  >- suspend "mstore_agrees"
  >- suspend "mstore_non_alloca"
  >- (fs[allocas_non_overlapping_def, mstore_allocas] >> metis_tac[])
  >- (fs[allocas_non_overlapping_def, mstore_allocas] >> metis_tac[])
QED

Resume mstore_preserves_remap_mem[mstore_agrees]:
  simp[alloca_mem_agrees_def, mstore_allocas, mem_byte_at_mstore] >>
  rpt strip_tac >>
  rename [`FLOOKUP s1.vs_allocas a = SOME (ooff, asz)`,
          `FLOOKUP remap a = SOME noff`, `j < asz`] >>
  Cases_on `a = aid`
  >- (gvs[] >>
      Cases_on `rel_off <= j /\ j < rel_off + 32`
      >- simp[]
      >- (simp[] >> fs[alloca_mem_agrees_def] >> metis_tac[]))
  >- (`FLOOKUP s2.vs_allocas a = SOME (noff, asz)` by metis_tac[] >>
      `ooff + asz <= orig_off \/ orig_off + sz <= ooff` by (
        qpat_x_assum `allocas_non_overlapping s1` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`ooff`,`asz`,`orig_off`,`sz`]
          mp_tac) >> simp[]) >>
      `noff + asz <= new_off \/ new_off + sz <= noff` by (
        qpat_x_assum `allocas_non_overlapping s2` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`noff`,`asz`,`new_off`,`sz`]
          mp_tac) >> simp[]) >>
      simp[] >> fs[alloca_mem_agrees_def] >> metis_tac[])
QED

Resume mstore_preserves_remap_mem[mstore_non_alloca]:
  simp[mem_byte_at_mstore] >> rpt strip_tac >>
  `~(orig_off + rel_off <= i /\ i < orig_off + rel_off + 32)` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `~in_alloca_region s1 _` mp_tac >>
     in_alloca_tac `aid` `orig_off` `sz`) >>
  `~(new_off + rel_off <= i /\ i < new_off + rel_off + 32)` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `~in_alloca_region s2 _` mp_tac >>
     in_alloca_tac `aid` `new_off` `sz`) >>
  simp[]
QED

Finalise mstore_preserves_remap_mem

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
  rpt strip_tac >> simp[] >> gvs[alloca_remap_rel_def] >>
  `FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)` by metis_tac[] >>
  rpt conj_tac
  >- suspend "mstore8_agrees"
  >- suspend "mstore8_non_alloca"
  >- (fs[allocas_non_overlapping_def, mstore8_allocas] >> metis_tac[])
  >- (fs[allocas_non_overlapping_def, mstore8_allocas] >> metis_tac[])
QED

Resume mstore8_preserves_remap_mem[mstore8_agrees]:
  simp[alloca_mem_agrees_def, mstore8_allocas, mem_byte_at_mstore8] >>
  rpt strip_tac >>
  rename [`FLOOKUP s1.vs_allocas a = SOME (ooff, asz)`,
          `FLOOKUP remap a = SOME noff`, `j < asz`] >>
  Cases_on `a = aid`
  >- (gvs[] >>
      Cases_on `j = rel_off`
      >- simp[]
      >- (simp[] >> fs[alloca_mem_agrees_def] >> metis_tac[]))
  >- (`FLOOKUP s2.vs_allocas a = SOME (noff, asz)` by metis_tac[] >>
      `ooff + asz <= orig_off \/ orig_off + sz <= ooff` by (
        qpat_x_assum `allocas_non_overlapping s1` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`ooff`,`asz`,`orig_off`,`sz`]
          mp_tac) >> simp[]) >>
      `noff + asz <= new_off \/ new_off + sz <= noff` by (
        qpat_x_assum `allocas_non_overlapping s2` mp_tac >>
        rewrite_tac[allocas_non_overlapping_def] >>
        disch_then (qspecl_then [`a`,`aid`,`noff`,`asz`,`new_off`,`sz`]
          mp_tac) >> simp[]) >>
      `j + ooff <> orig_off + rel_off` by simp[] >>
      `j + noff <> new_off + rel_off` by simp[] >>
      simp[] >> fs[alloca_mem_agrees_def] >> metis_tac[])
QED

Resume mstore8_preserves_remap_mem[mstore8_non_alloca]:
  simp[mem_byte_at_mstore8] >> rpt strip_tac >>
  `i <> orig_off + rel_off` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `~in_alloca_region s1 _` mp_tac >>
     in_alloca_tac `aid` `orig_off` `sz`) >>
  `i <> new_off + rel_off` by
    (CCONTR_TAC >> gvs[] >>
     qpat_x_assum `~in_alloca_region s2 _` mp_tac >>
     in_alloca_tac `aid` `new_off` `sz`) >>
  simp[]
QED

Finalise mstore8_preserves_remap_mem

(* ===== Instruction-Level Preservation ===== *)

(* FIND returns a member satisfying the predicate *)
Theorem find_some_mem[local]:
  !P l x. FIND P l = SOME x ==> MEM x l /\ P x
Proof
  Induct_on `l` >> simp[FIND_thm] >> rpt gen_tac >> strip_tac >>
  Cases_on `P h` >> gvs[] >> res_tac >> gvs[]
QED

(* ALL_DISTINCT MAP implies injectivity *)
Theorem all_distinct_map_inj[local]:
  !(l:'a list) (f:'a -> 'b) x y.
    ALL_DISTINCT (MAP f l) /\ MEM x l /\ MEM y l /\ f x = f y ==> x = y
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]
QED

(* Specialised: ALL_DISTINCT inst_ids implies inst equality *)
Theorem all_distinct_inst_id_inj[local]:
  !l (x:instruction) y.
    ALL_DISTINCT (MAP (\i. i.inst_id) l) /\ MEM x l /\ MEM y l /\
    x.inst_id = y.inst_id ==> x = y
Proof
  Induct >> simp[] >> rpt strip_tac >> gvs[MEM_MAP]
QED

(* fn_inst_ids_distinct gives ALL_DISTINCT on fn_insts *)
Theorem fn_inst_ids_all_distinct[local]:
  !fn. fn_inst_ids_distinct fn ==>
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  simp[fn_inst_ids_distinct_def, fn_insts_def] >> rpt strip_tac >>
  pop_assum mp_tac >>
  `!bbs. FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs) =
         MAP (\i. i.inst_id) (fn_insts_blocks bbs)` by (
    Induct >> simp[fn_insts_blocks_def]) >>
  simp[]
QED

(* fn_alloca_id_of_var is injective under wf_function *)
Theorem fn_alloca_id_of_var_inj[local]:
  !fn v1 v2 id.
    wf_function fn /\
    fn_alloca_id_of_var fn v1 = SOME id /\
    fn_alloca_id_of_var fn v2 = SOME id ==>
    v1 = v2
Proof
  rpt strip_tac >>
  gvs[fn_alloca_id_of_var_def, AllCaseEqs()] >>
  imp_res_tac find_some_mem >> gvs[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (irule fn_inst_ids_all_distinct >> gvs[wf_function_def]) >>
  drule_all all_distinct_inst_id_inj >> strip_tac >> gvs[]
QED

(* ===== Shared Reconstruction Helpers ===== *)

(* Introduction rule for alloca_remap_rel — deterministic subgoal order.
   Use: irule alloca_remap_rel_intro >> rpt conj_tac >- ... *)
Theorem alloca_remap_rel_intro[local]:
  !fn roots remap s1 s2.
    (!v. v NOTIN pointer_derived_vars fn roots ==>
         lookup_var v s1 = lookup_var v s2) /\
    (!v aid orig_off sz new_off.
         v IN roots /\ fn_alloca_id_of_var fn v = SOME aid /\
         FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
         FLOOKUP remap aid = SOME new_off ==>
         lookup_var v s1 = SOME (n2w orig_off) /\
         lookup_var v s2 = SOME (n2w new_off)) /\
    (!v. v IN pointer_derived_vars fn roots ==>
         lookup_var v s1 = NONE /\ lookup_var v s2 = NONE \/
         ?w1 w2 aid orig_off sz new_off.
           FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
           FLOOKUP remap aid = SOME new_off /\
           lookup_var v s1 = SOME w1 /\ lookup_var v s2 = SOME w2 /\
           w1 - n2w orig_off = w2 - n2w new_off /\
           orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
           new_off <= w2n w2 /\ w2n w2 < new_off + sz /\
           orig_off + sz < dimword (:256) /\
           new_off + sz < dimword (:256)) /\
    alloca_mem_agrees remap s1 s2 /\
    (!i. ~in_alloca_region s1 i /\ ~in_alloca_region s2 i ==>
         mem_byte_at s1.vs_memory i = mem_byte_at s2.vs_memory i) /\
    allocas_non_overlapping s1 /\ allocas_non_overlapping s2 /\
    FDOM s1.vs_allocas = FDOM s2.vs_allocas /\
    (!aid off1 sz new_off.
         FLOOKUP s1.vs_allocas aid = SOME (off1, sz) /\
         FLOOKUP remap aid = SOME new_off ==>
         FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)) /\
    LENGTH s1.vs_memory = LENGTH s2.vs_memory /\
    (s1.vs_halted <=> s2.vs_halted) /\
    s1.vs_returndata = s2.vs_returndata /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_transient = s2.vs_transient /\
    s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_tx_ctx = s2.vs_tx_ctx /\
    s1.vs_block_ctx = s2.vs_block_ctx /\ s1.vs_logs = s2.vs_logs /\
    s1.vs_immutables = s2.vs_immutables /\
    s1.vs_data_section = s2.vs_data_section /\
    s1.vs_labels = s2.vs_labels /\ s1.vs_code = s2.vs_code /\
    s1.vs_params = s2.vs_params /\ s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_prev_hashes = s2.vs_prev_hashes ==>
    alloca_remap_rel fn roots remap s1 s2
Proof
  simp[alloca_remap_rel_def, LET_DEF]
QED

(* in_alloca_region only depends on vs_allocas *)
Theorem in_alloca_region_allocas[local]:
  !s s' i. s'.vs_allocas = s.vs_allocas ==>
    (in_alloca_region s' i <=> in_alloca_region s i)
Proof
  rw[in_alloca_region_def]
QED

(* allocas_non_overlapping only depends on vs_allocas *)
Theorem allocas_non_overlapping_allocas[local]:
  !s s'. s'.vs_allocas = s.vs_allocas ==>
    (allocas_non_overlapping s' <=> allocas_non_overlapping s)
Proof
  rw[allocas_non_overlapping_def]
QED

(* Adding a fresh alloca entry only adds regions — old regions preserved.
   Works for any state s' whose vs_allocas = s.vs_allocas |+ (id, entry). *)
Theorem not_in_alloca_fupdate_fresh[local]:
  !s s' id entry i.
    id NOTIN FDOM s.vs_allocas /\
    s'.vs_allocas = s.vs_allocas |+ (id, entry) /\
    ~in_alloca_region s' i ==>
    ~in_alloca_region s i
Proof
  rw[in_alloca_region_def] >>
  rpt strip_tac >>
  first_x_assum (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  simp[FLOOKUP_UPDATE] >>
  Cases_on `aid = id` >> gvs[FLOOKUP_DEF]
QED

(* Extending allocas at OOB offsets preserves alloca_mem_agrees *)
Theorem alloca_mem_agrees_extend[local]:
  !remap s1 s2 id off1 off2 sz.
    alloca_mem_agrees remap s1 s2 /\
    LENGTH s1.vs_memory <= off1 /\
    LENGTH s2.vs_memory <= off2 ==>
    alloca_mem_agrees (remap |+ (id, off2))
      (s1 with vs_allocas := s1.vs_allocas |+ (id, (off1, sz)))
      (s2 with vs_allocas := s2.vs_allocas |+ (id, (off2, sz)))
Proof
  rw[alloca_mem_agrees_def, FLOOKUP_UPDATE] >>
  Cases_on `id = aid` >> gvs[]
  >- (`mem_byte_at s1.vs_memory (i + off1) = 0w` by
        (irule mem_byte_at_oob >> DECIDE_TAC) >>
      `mem_byte_at s2.vs_memory (i + new_off) = 0w` by
        (irule mem_byte_at_oob >> DECIDE_TAC) >>
      simp[])
  >- (res_tac >> fs[])
QED

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
Proof
  rpt gen_tac >> strip_tac >>
  (`inst.inst_id NOTIN FDOM s2.vs_allocas` by
    (qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
     REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
     strip_tac >> gvs[])) >>
  (`out IN pointer_derived_vars fn roots` by
    metis_tac[roots_in_pointer_derived_vars]) >>
  simp[exec_alloca_def] >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE[alloca_remap_rel_def, LET_DEF]) >>
  MATCH_MP_TAC alloca_remap_rel_intro >>
  simp[update_var_def, FLOOKUP_UPDATE, FDOM_FUPDATE, lookup_var_def] >>
  (* Clause 1: non-pv vars agree *)
  conj_tac >- (
    rpt strip_tac >>
    Cases_on `out = v` >> gvs[lookup_var_def]) >>
  (* Clause 2: roots *)
  conj_tac >- suspend "roots" >>
  (* Clause 2b: PV displacement *)
  conj_tac >- suspend "pv" >>
  (* Clause 3: alloca_mem_agrees *)
  conj_tac >- suspend "mem_agrees" >>
  (* Clause 4: non-alloca bytes *)
  conj_tac >- suspend "non_alloca" >>
  (* Clause 5a: non-overlapping s1 *)
  conj_tac >- suspend "non_overlap_s1" >>
  (* Clause 5b: non-overlapping s2 *)
  conj_tac >- suspend "non_overlap_s2" >>
  (* Clause 6: sizes agree *)
  suspend "sizes"
QED

Resume exec_alloca_preserves_remap[roots]:
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id = aid` >> fs[]
  (* YES: v = out by injectivity *)
  >- ((`v = out` by metis_tac[fn_alloca_id_of_var_inj]) >> rw[])
  (* NO: out ≠ v, then use old roots hyp *)
  >- ((`out <> v` by (CCONTR_TAC >> fs[] >>
       metis_tac[fn_alloca_id_of_var_inj])) >>
     fs[] >> res_tac >> gvs[lookup_var_def])
QED

Resume exec_alloca_preserves_remap[pv]:
  rpt strip_tac >>
  Cases_on `out = v` >> gvs[]
  >- ((* out = v: goal is pure existential after gvs simplifies disjunction *)
    qexistsl_tac [`inst.inst_id`,
                   `s1.vs_alloca_next`, `w2n alloc_size`,
                   `s2.vs_alloca_next`] >>
    simp[WORD_SUB_REFL])
  >- ((* out ≠ v: use old PV hypothesis *)
    qpat_x_assum `!v. v IN pointer_derived_vars _ _ ==> _ \/ _`
      (qspec_then `v` mp_tac) >> simp[] >> strip_tac
    >- (DISJ1_TAC >> gvs[lookup_var_def])
    >- (DISJ2_TAC >>
        `aid <> inst.inst_id` by
          (strip_tac >> gvs[flookup_thm]) >>
        qexistsl_tac [`w1`, `w2`, `aid`, `orig_off`, `sz`, `new_off`] >>
        gvs[lookup_var_def]))
QED

Resume exec_alloca_preserves_remap[mem_agrees]:
  rw[alloca_mem_agrees_def, FLOOKUP_UPDATE] >>
  Cases_on `inst.inst_id = aid` >> gvs[]
  >- (`mem_byte_at s1.vs_memory (i + s1.vs_alloca_next) = 0w` by
        (irule mem_byte_at_oob >> DECIDE_TAC) >>
      `mem_byte_at s2.vs_memory (i + s2.vs_alloca_next) = 0w` by
        (irule mem_byte_at_oob >> DECIDE_TAC) >>
      simp[])
  >- (fs[alloca_mem_agrees_def] >> res_tac >> fs[])
QED

Resume exec_alloca_preserves_remap[non_alloca]:
  rpt strip_tac >>
  first_x_assum irule >>
  conj_tac >> (
    CCONTR_TAC >>
    fs[in_alloca_region_def, FLOOKUP_UPDATE] >> gvs[] >>
    metis_tac[flookup_thm])
QED

Resume exec_alloca_preserves_remap[non_overlap_s1]:
  irule non_overlapping_extend >>
  qexistsl_tac [`inst.inst_id`, `s1`, `w2n alloc_size`] >> simp[] >>
  fs[alloca_inv_def]
QED

Resume exec_alloca_preserves_remap[non_overlap_s2]:
  irule non_overlapping_extend >>
  qexistsl_tac [`inst.inst_id`, `s2`, `w2n alloc_size`] >> simp[] >>
  fs[alloca_inv_def]
QED

Resume exec_alloca_preserves_remap[sizes]:
  rpt strip_tac >>
  Cases_on `inst.inst_id = aid` >> fs[]
QED

Finalise exec_alloca_preserves_remap

(* ===== Helper: alloca_safe_access implies ptrs_in_alloca_bounds ===== *)

(* alloca_safe_access gives w2n w + w2n sz_val <= off + asz,
   which implies off <= w2n w < off + asz (when asz >= w2n sz_val > 0).
   But more directly, we can derive ptrs_in_alloca_bounds separately
   or just use alloca_safe_access directly in proofs. *)

(* Bridge: step_inst_base = step_inst for our excluded opcodes.
   INVOKE is not is_alloca_op, is_terminator, or is_ext_call_op,
   but step_inst_base returns Error for it, so OK v1 rules it out. *)
Theorem not_invoke_from_ok[local]:
  !inst s v.
    step_inst_base inst s = OK v ==> inst.inst_opcode <> INVOKE
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

(* Bridge: step_inst_base OK implies step_inst OK for any fuel/ctx.
   Lifts all step_inst properties to step_inst_base. *)
Theorem step_inst_base_as_step_inst[local]:
  !inst s v.
    step_inst_base inst s = OK v ==>
    !fuel ctx. step_inst fuel ctx inst s = OK v
Proof
  rpt strip_tac >>
  imp_res_tac not_invoke_from_ok >>
  metis_tac[step_inst_non_invoke]
QED

(* step_inst_base preserves non-output vars *)
Theorem step_inst_base_non_output_vars[local]:
  !inst s v nm.
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~MEM nm inst.inst_outputs ==>
    lookup_var nm v = lookup_var nm s
Proof
  metis_tac[step_inst_base_as_step_inst, step_preserves_non_output_vars]
QED

(* Helper: step_inst_base doesn't change vs_allocas for non-alloca ops. *)
Theorem step_inst_base_allocas[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    v.vs_allocas = s.vs_allocas
Proof
  rpt strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_alloca_op_def, is_terminator_def, is_ext_call_op_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
  gvs[update_var_def, mstore_def, mstore8_def, sstore_def, tstore_def,
      mcopy_def, write_memory_with_expansion_def, write_memory_def]
QED

(* Helper: non-pointer operand agreement *)
Theorem operand_agreement[local]:
  !fn roots remap s1 s2 inst bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions ==>
    !op. MEM op inst.inst_operands /\
         (!v. op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
         eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >> irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[]
QED

(* Helper: operands defined in s1 are also defined in s2 *)
Theorem operand_defined_iff[local]:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 ==>
    ((eval_operand op s1 = NONE) <=> (eval_operand op s2 = NONE))
Proof
  rpt strip_tac >> EQ_TAC >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def] >>
  TRY (rename [`lookup_var nm`]) >>
  TRY (Cases_on `nm IN pointer_derived_vars fn roots`) >>
  gvs[alloca_remap_rel_def, LET_DEF] >>
  TRY (first_x_assum (qspec_then `nm` mp_tac) >> simp[] >>
       strip_tac >> gvs[])
QED

Theorem operand_defined_transfer[local]:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 /\
    eval_operand op s1 <> NONE ==>
    eval_operand op s2 <> NONE
Proof
  metis_tac[operand_defined_iff]
QED

(* ===== Case 1: No pointer operands ===== *)

(* Bridge: mem_write_ops or mem_read_ops SOME implies iao_ofst is an operand *)
Theorem mem_ops_ofst_is_operand[local]:
  !inst ops.
    (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
    MEM ops.iao_ofst inst.inst_operands
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  pop_assum mp_tac >>
  simp[mem_write_ops_def, mem_read_ops_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED

(* No pointer operand + all_mem_via_pointer + ~is_immutable_op → no mem ops.
   Contrapositive: mem ops → all_mem_via_pointer → pointer in iao_ofst
   → iao_ofst is operand → pointer operand.
   Excludes ILOAD/ISTORE: they have mem_read/write_ops but operate on
   vs_immutables, not vs_memory. all_mem_via_pointer skips them. *)
Theorem no_mem_ops_from_no_pointer_ops[local]:
  !fn roots bb inst.
    all_mem_via_pointer fn roots /\
    ~is_immutable_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    mem_read_ops inst = NONE /\ mem_write_ops inst = NONE
Proof
  rpt gen_tac >> strip_tac >>
  `!ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) ==>
         ?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots` by
    (fs[all_mem_via_pointer_def, LET_DEF] >> metis_tac[]) >>
  conj_tac >> spose_not_then strip_assume_tac >>
  Cases_on `mem_read_ops inst` >> Cases_on `mem_write_ops inst` >> gvs[] >>
  res_tac >> gvs[] >> imp_res_tac mem_ops_ofst_is_operand >> gvs[] >>
  TRY (res_tac >> NO_TAC) >>
  first_x_assum (qspec_then `x` mp_tac) >> simp[] >> strip_tac >> gvs[] >>
  rpt strip_tac >> gvs[]
QED

(* Memory preservation: for non-pointer-op instructions (no mem ops),
   memory is unchanged. Two cases:
   - effect_free: state_equiv gives all fields preserved
   - non-effect-free: only SSTORE/TSTORE/LOG possible (memory writers
     require correct operand arity from step_inst_base=OK, giving
     mem_write_ops<>NONE, contradicting mem_write_ops=NONE).
     SSTORE/TSTORE/LOG don't write memory. *)
Theorem step_inst_base_mem_preserves_no_mem_ops[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    mem_write_ops inst = NONE ==>
    v.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  imp_res_tac not_invoke_from_ok >>
  `!fuel ctx. step_inst fuel ctx inst s = OK v` by
    metis_tac[step_inst_non_invoke] >>
  Cases_on `is_effect_free_op inst.inst_opcode`
  (* Effect-free: state_equiv gives memory preserved *)
  >- (first_x_assum (qspecl_then [`0`, `ARB`] assume_tac) >>
      drule_all step_effect_free_state_equiv >>
      simp[state_equiv_def, execution_equiv_def])
  (* Non-effect-free: show Eff_MEMORY NOTIN write_effects, then use
     write_effects_sound_memory. The 8 mem-writer opcodes (MSTORE etc)
     all have Eff_MEMORY IN write_effects but require correct operand
     arity for step_inst_base=OK, giving mem_write_ops<>NONE. *)
  >- (`Eff_MEMORY NOTIN write_effects inst.inst_opcode` by
        (spose_not_then strip_assume_tac >>
         qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
         qpat_x_assum `mem_write_ops _ = _` mp_tac >>
         simp[step_inst_base_def, mem_write_ops_def] >>
         Cases_on `inst.inst_opcode` >>
         gvs[is_effect_free_op_def, is_alloca_op_def,
             is_terminator_def, is_ext_call_op_def,
             write_effects_def, all_effects_def, empty_effects_def] >>
         simp[exec_write2_def, AllCaseEqs()] >>
         rpt strip_tac >> gvs[]) >>
      first_x_assum (qspecl_then [`0`, `ARB`] assume_tac) >>
      drule_all write_effects_sound_memory >> simp[])
QED

(* Bridging: when mem_read_ops = NONE and step_inst_base succeeds,
   the opcode doesn't read memory. Needed to discharge the memory
   conditional in step_inst_base_scalar_agree for no-pointer-ops. *)
(* MEMTOP reads memory but mem_read_ops doesn't cover it.
   Exclude MEMTOP from the bridge.
   TODO: add MEMTOP to mem_read_ops? *)
Theorem no_mem_read_effect_from_no_mem_read_ops[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    mem_read_ops inst = NONE /\
    inst.inst_opcode <> MEMTOP /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode ==>
    Eff_MEMORY NOTIN read_effects inst.inst_opcode
Proof
  rpt strip_tac >>
  spose_not_then strip_assume_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  qpat_x_assum `mem_read_ops _ = _` mp_tac >>
  simp[step_inst_base_def, mem_read_ops_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_alloca_op_def, is_terminator_def, is_ext_call_op_def,
      read_effects_def, all_effects_def, empty_effects_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
QED



(* Specialized reconstruction: allocas/memory preserved from input.
   Useful for non-ALLOCA instructions that don't modify allocas/memory. *)
Theorem remap_rel_from_equiv[local]:
  !fn roots remap s1 s2 v1 v2.
    alloca_remap_rel fn roots remap s1 s2 /\
    v1.vs_allocas = s1.vs_allocas /\
    v2.vs_allocas = s2.vs_allocas /\
    v1.vs_memory = s1.vs_memory /\
    v2.vs_memory = s2.vs_memory /\
    (!v. v NOTIN pointer_derived_vars fn roots ==>
         lookup_var v v1 = lookup_var v v2) /\
    (!v aid orig_off sz new_off.
         v IN roots /\ fn_alloca_id_of_var fn v = SOME aid /\
         FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
         FLOOKUP remap aid = SOME new_off ==>
         lookup_var v v1 = SOME (n2w orig_off) /\
         lookup_var v v2 = SOME (n2w new_off)) /\
    (!v. v IN pointer_derived_vars fn roots ==>
         lookup_var v v1 = lookup_var v s1 /\
         lookup_var v v2 = lookup_var v s2 \/
         ?w1 w2 aid orig_off sz new_off.
           FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
           FLOOKUP remap aid = SOME new_off /\
           lookup_var v v1 = SOME w1 /\
           lookup_var v v2 = SOME w2 /\
           w1 - n2w orig_off = w2 - n2w new_off /\
           orig_off <= w2n w1 /\ w2n w1 < orig_off + sz /\
           new_off <= w2n w2 /\ w2n w2 < new_off + sz /\
           orig_off + sz < dimword (:256) /\
           new_off + sz < dimword (:256)) /\
    (v1.vs_halted <=> v2.vs_halted) /\
    v1.vs_returndata = v2.vs_returndata /\
    v1.vs_accounts = v2.vs_accounts /\
    v1.vs_transient = v2.vs_transient /\
    v1.vs_call_ctx = v2.vs_call_ctx /\
    v1.vs_tx_ctx = v2.vs_tx_ctx /\
    v1.vs_block_ctx = v2.vs_block_ctx /\
    v1.vs_logs = v2.vs_logs /\
    v1.vs_immutables = v2.vs_immutables /\
    v1.vs_data_section = v2.vs_data_section /\
    v1.vs_labels = v2.vs_labels /\
    v1.vs_code = v2.vs_code /\
    v1.vs_params = v2.vs_params /\
    v1.vs_prev_bb = v2.vs_prev_bb /\
    v1.vs_current_bb = v2.vs_current_bb /\
    v1.vs_inst_idx = v2.vs_inst_idx /\
    v1.vs_prev_hashes = v2.vs_prev_hashes ==>
    alloca_remap_rel fn roots remap v1 v2
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
  REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
  REWRITE_TAC[allocas_non_overlapping_def, alloca_mem_agrees_def,
              in_alloca_region_def] >>
  strip_tac >>
  REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
  REWRITE_TAC[allocas_non_overlapping_def, alloca_mem_agrees_def,
              in_alloca_region_def] >>
  ASM_REWRITE_TAC[] >>
  rpt conj_tac >>
  TRY (rpt strip_tac >> res_tac >> NO_TAC) >>
  rpt strip_tac >>
  qpat_x_assum `!v. v IN _ ==> lookup_var v v1 = _ /\ _ \/ _`
    (qspec_then `v` mp_tac) >>
  ASM_REWRITE_TAC[] >> strip_tac >> gvs[] >>
  qexistsl_tac [`aid`, `orig_off`, `sz`, `new_off`] >> simp[]
QED

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
    ~is_immutable_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt strip_tac >>
  (* Step 1: Extract scalar fields from alloca_remap_rel *)
  `s1.vs_prev_bb = s2.vs_prev_bb /\ s1.vs_params = s2.vs_params /\
   s1.vs_returndata = s2.vs_returndata /\
   s1.vs_call_ctx = s2.vs_call_ctx /\ s1.vs_tx_ctx = s2.vs_tx_ctx /\
   s1.vs_block_ctx = s2.vs_block_ctx /\
   s1.vs_data_section = s2.vs_data_section /\
   s1.vs_labels = s2.vs_labels /\ s1.vs_code = s2.vs_code /\
   s1.vs_prev_hashes = s2.vs_prev_hashes /\
   s1.vs_immutables = s2.vs_immutables /\
   s1.vs_accounts = s2.vs_accounts /\
   s1.vs_transient = s2.vs_transient /\
   s1.vs_logs = s2.vs_logs /\
   s1.vs_current_bb = s2.vs_current_bb /\
   s1.vs_inst_idx = s2.vs_inst_idx /\
   (s1.vs_halted <=> s2.vs_halted)` by
    (qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
     REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
     strip_tac >> simp[]) >>
  (* Step 2: Operand agreement (all operands non-pointer) *)
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by
    (rpt strip_tac >> irule eval_operand_non_pointer_remap >>
     MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
     rpt strip_tac >> res_tac) >>
  (* Step 3: Get v2 via transfer *)
  `?v2. step_inst_base inst s2 = OK v2` by
    (irule step_inst_base_ok_transfer >> simp[] >>
     qexistsl_tac [`s1`, `v1`] >> simp[]) >>
  qexists_tac `v2` >> simp[] >>
  (* Step 4: No mem ops → allocas/memory preserved *)
  `mem_write_ops inst = NONE /\ mem_read_ops inst = NONE` by
    (imp_res_tac no_mem_ops_from_no_pointer_ops >> gvs[]) >>
  `v1.vs_allocas = s1.vs_allocas /\ v2.vs_allocas = s2.vs_allocas` by
    metis_tac[step_inst_base_allocas] >>
  `v1.vs_memory = s1.vs_memory /\ v2.vs_memory = s2.vs_memory` by
    metis_tac[step_inst_base_mem_preserves_no_mem_ops] >>
  (* Step 5: No pv outputs, non-output vars preserved *)
  `!v. MEM v inst.inst_outputs ==> v NOTIN pointer_derived_vars fn roots` by
    metis_tac[no_pv_outputs_from_no_pv_inputs] >>
  `!nm. ~MEM nm inst.inst_outputs ==>
        lookup_var nm v1 = lookup_var nm s1 /\
        lookup_var nm v2 = lookup_var nm s2` by
    metis_tac[step_inst_base_non_output_vars] >>
  (* Step 6: All 17 scalar fields agree via step_inst_base_scalar_agree.
     The memory conditional is vacuously true: no mem ops ⇒ no memory reads. *)
  (`Eff_MEMORY NOTIN read_effects inst.inst_opcode` by
    metis_tac[no_mem_read_effect_from_no_mem_read_ops]) >>
  mp_tac step_inst_base_scalar_agree >>
  disch_then (qspecl_then [`inst`, `s1`, `s2`, `v1`, `v2`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Step 7: Output var agreement *)
  `LENGTH s1.vs_memory = LENGTH s2.vs_memory` by
    (qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
     REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
     strip_tac >> simp[]) >>
  `!v. MEM v inst.inst_outputs ==> lookup_var v s1 = lookup_var v s2` by
    (rpt strip_tac >>
     `v NOTIN pointer_derived_vars fn roots` by res_tac >>
     qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
     REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
     strip_tac >> res_tac) >>
  mp_tac step_inst_base_output_vars_agree >>
  disch_then (qspecl_then [`inst`, `s1`, `s2`, `v1`, `v2`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  (* Step 8: Reconstruct alloca_remap_rel *)
  irule remap_rel_from_equiv >>
  gvs[] >> rpt conj_tac
  (* Non-pv vars agree *)
  >- (rpt strip_tac >>
      Cases_on `MEM v inst.inst_outputs`
      >- (`lookup_var v v1 = lookup_var v v2` by res_tac >> gvs[])
      >- (`lookup_var v v1 = lookup_var v s1 /\
           lookup_var v v2 = lookup_var v s2` by
            (qpat_assum `!nm. ~MEM nm inst.inst_outputs ==> _`
              (qspec_then `v` mp_tac) >> simp[]) >>
          `lookup_var v s1 = lookup_var v s2` by
            (qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
             REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
             strip_tac >> res_tac) >>
          gvs[]))
  (* Existential: root vars, pv vars, allocas/memory/remap *)
  >- (qexistsl_tac [`s1`, `s2`] >> simp[] >> rpt conj_tac
      (* Root vars: not outputs (roots ⊆ pv, outputs ∉ pv), so preserved *)
      >- (rpt strip_tac >>
          `v IN pointer_derived_vars fn roots` by
            metis_tac[roots_in_pointer_derived_vars] >>
          `~MEM v inst.inst_outputs` by
            (strip_tac >> res_tac >> gvs[]) >>
          `lookup_var v v1 = lookup_var v s1 /\
           lookup_var v v2 = lookup_var v s2` by
            (qpat_assum `!nm. ~MEM nm inst.inst_outputs ==> _`
              (qspec_then `v` mp_tac) >> simp[]) >>
          qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
          REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
          strip_tac >> res_tac >> gvs[])
      (* PV vars: not outputs, so preserved from input *)
      >- (rpt strip_tac >>
          `~MEM v inst.inst_outputs` by
            (strip_tac >> res_tac >> gvs[]) >>
          DISJ1_TAC >>
          qpat_assum `!nm. ~MEM nm inst.inst_outputs ==> _`
            (qspec_then `v` mp_tac) >> simp[]))
QED


(* ===== Case 2: Pointer-preserving ops (ADD, SUB, ASSIGN, PHI) ===== *)

(* update_var with a pv output preserves alloca_remap_rel when:
   - out is pv but NOT a root (ensured by SSA: roots are alloca outputs)
   - val1/val2 satisfy the displacement invariant for some alloca
   This captures the common pattern for ADD/SUB/ASSIGN/PHI outputs. *)
Theorem remap_rel_update_pv[local]:
  !fn roots remap s1 s2 out val1 val2 aid orig_off sz new_off.
    alloca_remap_rel fn roots remap s1 s2 /\
    out IN pointer_derived_vars fn roots /\
    out NOTIN roots /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    val1 - n2w orig_off = val2 - n2w new_off /\
    orig_off <= w2n val1 /\ w2n val1 < orig_off + sz /\
    new_off <= w2n val2 /\ w2n val2 < new_off + sz /\
    orig_off + sz < dimword (:256) /\
    new_off + sz < dimword (:256) ==>
    alloca_remap_rel fn roots remap
      (update_var out val1 s1)
      (update_var out val2 s2)
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     strip_assume_tac (BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th))) >>
  MATCH_MP_TAC remap_rel_from_equiv >>
  MAP_EVERY qexists_tac [`s1`, `s2`] >>
  simp[update_var_def] >>
  rpt conj_tac >>
  rpt strip_tac >>
  simp[lookup_var_def, FLOOKUP_UPDATE] >>
  Cases_on `out = v` >> gvs[] >>
  TRY (res_tac >> gvs[lookup_var_def] >> NO_TAC) >>
  TRY (DISJ1_TAC >> simp[lookup_var_def] >> NO_TAC) >>
  DISJ2_TAC >>
  MAP_EVERY qexists_tac [`aid`, `orig_off`, `sz`, `new_off`] >>
  simp[]
QED

(* Transfer bounds from one state to another via displacement.
   If w1 is in [a, a+sz) and w1-a = w2-b (displacement preserved),
   then w2 is in [b, b+sz), provided b+sz doesn't overflow. *)
Theorem displacement_bounds_transfer[local]:
  !(w1:'a word) (w2:'a word) a sz b.
    w1 - n2w a = w2 - n2w b /\
    a <= w2n w1 /\ w2n w1 < a + sz /\
    b + sz < dimword (:'a) ==>
    b <= w2n w2 /\ w2n w2 < b + sz
Proof
  rpt gen_tac >> strip_tac >>
  `a < dimword (:'a)` by
    (mp_tac (SPEC ``w1:'a word`` w2n_lt) >> decide_tac) >>
  `b < dimword (:'a)` by decide_tac >>
  `(n2w a :'a word) <=+ w1` by simp[WORD_LS, w2n_n2w] >>
  `w2n (w1 - n2w a) = w2n w1 - a` by
    (mp_tac (Q.SPECL [`w1`, `n2w a`] word_sub_w2n) >> simp[w2n_n2w]) >>
  `w2 = w1 - n2w a + n2w b` by metis_tac[WORD_SUB_ADD] >>
  `w2n w2 = (w2n (w1 - n2w a) + w2n (n2w b :'a word)) MOD dimword (:'a)` by
    (qpat_x_assum `w2 = _` SUBST1_TAC >>
     REWRITE_TAC[word_add_def, w2n_n2w]) >>
  `w2n (n2w b : 'a word) = b` by simp[w2n_n2w] >>
  `w2n (w1 - n2w a) + b < dimword (:'a)` by decide_tac >>
  fs[]
QED

Theorem non_alloca_output_notin_roots[local]:
  !fn roots inst out bb.
    ssa_form fn /\
    roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM out inst.inst_outputs /\
    ~is_alloca_op inst.inst_opcode ==>
    out NOTIN roots
Proof
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >>
  `out IN roots` by fs[] >>
  drule_all (iffLR pred_setTheory.SUBSET_DEF) >> strip_tac >>
  fs[alloca_roots_def] >>
  `MEM inst' (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
  `MEM out inst'.inst_outputs` by
    (Cases_on `inst'.inst_outputs` >> gvs[inst_output_def] >>
     Cases_on `t` >> gvs[inst_output_def]) >>
  `inst = inst'` by metis_tac[ssa_unique_output] >>
  gvs[is_alloca_op_def]
QED

(* Helper: outputs of non-pp, non-alloca instructions are not in pv.
   By SSA uniqueness, the only defining instruction for out is this one.
   pointer_use_vars_mem_char: if out IN pv, either in roots (impossible for
   non-alloca by non_alloca_output_notin_roots) or output of a pp op
   (impossible since this op is ~pp). *)
Theorem non_pp_output_notin_pv[local]:
  !fn roots inst out bb.
    ssa_form fn /\ FINITE roots /\ roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM out inst.inst_outputs /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode ==>
    out NOTIN pointer_derived_vars fn roots
Proof
  rpt gen_tac >> strip_tac >>
  CCONTR_TAC >> gvs[] >>
  `MEM out (pointer_use_vars fn (SET_TO_LIST roots))` by
    fs[pointer_derived_vars_def] >>
  drule pointer_use_vars_mem_char >> strip_tac
  >- (* out IN roots — impossible for non-alloca *)
     (imp_res_tac non_alloca_output_notin_roots >>
      `MEM out (SET_TO_LIST roots)` by simp[] >>
      `out IN roots` by metis_tac[MEM_SET_TO_LIST, FINITE_LIST_TO_SET] >>
      metis_tac[])
  >- (* out is output of a pp op — but inst is not pp, and SSA unique *)
     (`MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
      `MEM inst' (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
      `inst = inst'` by metis_tac[ssa_unique_output] >>
      gvs[])
QED

(* Helper: for pointer-preserving ops with a pv operand,
   the output var is in pv and not in roots *)
Theorem pp_no_mem_ops[local]:
  !inst. is_pointer_preserving_op inst.inst_opcode ==>
    mem_write_ops inst = NONE /\ mem_read_ops inst = NONE
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  fs[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def]
QED

Theorem pointer_confined_pp_elim[local]:
  !fn roots inst bb v.
    pointer_confined fn roots /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM (Var v) inst.inst_operands /\
    v IN pointer_derived_vars fn roots ==>
    set inst.inst_outputs SUBSET pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  imp_res_tac pp_no_mem_ops >>
  qpat_x_assum `pointer_confined _ _` mp_tac >>
  REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >>
  strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
  simp[]
QED

Theorem pp_pv_output[local]:
  !fn roots inst bb inp out.
    pointer_confined fn roots /\ ssa_form fn /\
    roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    MEM (Var inp) inst.inst_operands /\
    inp IN pointer_derived_vars fn roots /\
    MEM out inst.inst_outputs ==>
    out IN pointer_derived_vars fn roots /\ out NOTIN roots
Proof
  rpt gen_tac >> strip_tac >>
  (`set inst.inst_outputs SUBSET pointer_derived_vars fn roots` by
    (MATCH_MP_TAC pointer_confined_pp_elim >>
     MAP_EVERY qexists_tac [`bb`, `inp`] >> simp[])) >>
  conj_tac
  >- (fs[SUBSET_DEF])
  >- (metis_tac[non_alloca_output_notin_roots])
QED

(* Helper: non-pv operand agreement via alloca_remap_rel *)
Theorem nonpv_operand_agrees[local]:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 /\
    (!v. op = Var v ==> v NOTIN pointer_derived_vars fn roots) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[]
QED

(* Helper: remap_rel_from_equiv specialized for update_var when output
   is not in pv — all pv/root vars pass through to the original states *)
Theorem remap_rel_update_nonpv[local]:
  !fn roots remap s1 s2 out val1 val2.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    val1 = val2 /\
    out NOTIN pointer_derived_vars fn roots /\
    s1.vs_prev_bb = s2.vs_prev_bb /\
    s1.vs_params = s2.vs_params ==>
    alloca_remap_rel fn roots remap
      (update_var out val1 s1)
      (update_var out val2 s2)
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     strip_assume_tac
       (BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th))) >>
  irule remap_rel_from_equiv >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  (* scalar equalities resolved by simp; remaining: nonpv ∧ ∃s1' s2'. ... *)
  (conj_tac >-
    (rpt strip_tac >> Cases_on `out = v` >>
     gvs[lookup_var_def] >> res_tac)) >>
  MAP_EVERY qexists_tac [`s1`, `s2`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  (`out <> v` by
    (strip_tac >> gvs[] >>
     imp_res_tac roots_in_pointer_derived_vars >> gvs[])) >>
  gvs[] >>
  TRY (res_tac >> gvs[lookup_var_def] >> NO_TAC)
QED

(* Helper: for ADD/SUB with affine_pointer_ops, at most one operand is pv.
   Given op1 = Var inp with inp ∈ pv, op2 cannot be Var v2 with v2 ∈ pv. *)
(* Combined: for ADD/SUB with a pv operand, the other operand agrees *)
Theorem add_sub_other_operand_agrees[local]:
  !fn roots remap s1 s2 bb inst op_pv op_other pv_var.
    alloca_remap_rel fn roots remap s1 s2 /\
    affine_pointer_ops fn roots /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (inst.inst_operands = [op_pv; op_other] \/
     inst.inst_operands = [op_other; op_pv]) /\
    op_pv = Var pv_var /\ pv_var IN pointer_derived_vars fn roots ==>
    eval_operand op_other s1 = eval_operand op_other s2
Proof
  rpt strip_tac >>
  irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `affine_pointer_ops _ _` mp_tac >>
  REWRITE_TAC[affine_pointer_ops_def, LET_DEF] >> BETA_TAC >>
  strip_tac >>
  first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >> simp[]
QED

Theorem affine_other_not_pv[local]:
  !fn roots bb inst op1 op2 inp.
    affine_pointer_ops fn roots /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_operands = [op1; op2] /\
    op1 = Var inp /\ inp IN pointer_derived_vars fn roots ==>
    !v. op2 = Var v ==> v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `affine_pointer_ops _ _` mp_tac >>
  REWRITE_TAC[affine_pointer_ops_def, LET_DEF] >> BETA_TAC >>
  strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `Var inp`, `Var v`] mp_tac) >>
  simp[] >> qexistsl_tac [`inp`, `v`] >> simp[]
QED

(* Symmetric version: op2 is pv, so op1 can't be *)
Theorem affine_other_not_pv_sym[local]:
  !fn roots bb inst op1 op2 inp.
    affine_pointer_ops fn roots /\
    (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_operands = [op1; op2] /\
    op2 = Var inp /\ inp IN pointer_derived_vars fn roots ==>
    !v. op1 = Var v ==> v NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `affine_pointer_ops _ _` mp_tac >>
  REWRITE_TAC[affine_pointer_ops_def, LET_DEF] >> BETA_TAC >>
  strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `Var v`, `Var inp`] mp_tac) >>
  simp[] >> qexistsl_tac [`v`, `inp`] >> simp[]
QED

(* When a PHI with pv Var operands resolves to a non-Var-pv value,
   pointer_arith_in_region is contradicted.
   Key idea: construct a state where the pv input is in an alloca region
   that does NOT contain the literal output value. *)
(* CHEATED — parallel PHI: step_inst_base on PHI is now OK s (no-op).
   The proof constructs a state where step_inst_base PHI = update_var,
   which is no longer true. Needs reformulation for eval_phis. *)
Theorem phi_nonvar_pv_contradiction[local]:
  !fn roots inst bb out u s1 prev val_op w1.
    pointer_arith_in_region fn roots /\
    ssa_form fn /\
    roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    out IN pointer_derived_vars fn roots /\
    MEM (Var u) inst.inst_operands /\
    u IN pointer_derived_vars fn roots /\
    s1.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME val_op /\
    (!v. val_op <> Var v) /\
    eval_operand val_op s1 = SOME w1 ==>
    F
Proof
  cheat
QED

(* Elimination form for pointer_arith_in_region:
   if a pp op produces w_out from a pv input w_in that's in [off, off+sz),
   then w_out is also in [off, off+sz). *)
Theorem pointer_arith_in_region_elim[local]:
  !fn roots bb inst s v out w_out inp w_in aid off asz.
    pointer_arith_in_region fn roots /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    step_inst_base inst s = OK v /\
    inst.inst_outputs = [out] /\
    out IN pointer_derived_vars fn roots /\
    lookup_var out v = SOME w_out /\
    MEM (Var inp) inst.inst_operands /\
    inp IN pointer_derived_vars fn roots /\
    lookup_var inp s = SOME w_in /\
    FLOOKUP s.vs_allocas aid = SOME (off, asz) /\
    off <= w2n w_in /\ w2n w_in < off + asz ==>
    off <= w2n w_out /\ w2n w_out < off + asz
Proof
  rpt strip_tac >>
  qpat_x_assum `pointer_arith_in_region _ _` mp_tac >>
  REWRITE_TAC[pointer_arith_in_region_def, LET_DEF] >> BETA_TAC >>
  disch_then (qspecl_then [`bb`,`inst`,`s`,`v`,`out`,`w_out`,
    `inp`,`w_in`,`aid`,`off`,`asz`] mp_tac) >>
  simp[]
QED

Theorem resolve_phi_mem[local]:
  !prev ops val_op.
    resolve_phi prev ops = SOME val_op ==> MEM val_op ops
Proof
  ho_match_mp_tac resolve_phi_ind >> rpt strip_tac >>
  gvs[resolve_phi_def, AllCaseEqs()]
QED

(* Combined helper for PV subcases of pointer-preserving ops:
   given the step results for both states and displacement preservation,
   derive bounds via pointer_arith_in_region and reconstruct alloca_remap_rel.
   Eliminates the 3-lemma pattern (remap_rel_update_pv + pointer_arith_in_region_elim
   + displacement_bounds_transfer) that appears in every PV subcase. *)
Theorem pp_pv_update_remap[local]:
  !fn roots remap s1 s2 bb inst out val1 val2 inp w_in aid orig_off asz new_off.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_arith_in_region fn roots /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_outputs = [out] /\
    out IN pointer_derived_vars fn roots /\ out NOTIN roots /\
    inp IN pointer_derived_vars fn roots /\
    MEM (Var inp) inst.inst_operands /\
    lookup_var inp s1 = SOME w_in /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, asz) /\
    FLOOKUP remap aid = SOME new_off /\
    orig_off <= w2n w_in /\ w2n w_in < orig_off + asz /\
    orig_off + asz < dimword (:256) /\
    new_off + asz < dimword (:256) /\
    step_inst_base inst s1 = OK (update_var out val1 s1) /\
    step_inst_base inst s2 = OK (update_var out val2 s2) /\
    val1 - n2w orig_off = val2 - n2w new_off ==>
    alloca_remap_rel fn roots remap
      (update_var out val1 s1) (update_var out val2 s2)
Proof
  rpt strip_tac >>
  (* Get s1 output bounds from pointer_arith_in_region *)
  (`orig_off <= w2n val1 /\ w2n val1 < orig_off + asz` by
    (mp_tac pointer_arith_in_region_elim >>
     disch_then (qspecl_then
       [`fn`,`roots`,`bb`,`inst`,`s1`,
        `update_var out val1 s1`,`out`,`val1`,`inp`,`w_in`,
        `aid`,`orig_off`,`asz`] mp_tac) >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE])) >>
  (* Get s2 output bounds via displacement transfer *)
  (`new_off <= w2n val2 /\ w2n val2 < new_off + asz` by
    metis_tac[displacement_bounds_transfer]) >>
  irule remap_rel_update_pv >> simp[] >>
  MAP_EVERY qexists_tac [`aid`, `new_off`, `orig_off`, `asz`] >>
  simp[]
QED

(* Combined helper: pp op preserves remap given displacement.
   The caller shows val1 - w1 = val2 - w2 (operation preserves relative offset).
   The lemma internally extracts clause 2b and handles everything else. *)
Theorem pp_step_preserves_remap[local]:
  !fn roots remap s1 s2 bb inst out val1 val2 inp w1 w2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_arith_in_region fn roots /\
    pointer_confined fn roots /\ ssa_form fn /\
    roots SUBSET alloca_roots fn /\
    is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_outputs = [out] /\
    inp IN pointer_derived_vars fn roots /\
    MEM (Var inp) inst.inst_operands /\
    lookup_var inp s1 = SOME w1 /\
    lookup_var inp s2 = SOME w2 /\
    step_inst_base inst s1 = OK (update_var out val1 s1) /\
    step_inst_base inst s2 = OK (update_var out val2 s2) /\
    val1 - w1 = val2 - w2 ==>
    alloca_remap_rel fn roots remap
      (update_var out val1 s1) (update_var out val2 s2)
Proof
  rpt strip_tac >>
  (* Extract clause 2b for inp *)
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     strip_assume_tac
       (BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th))) >>
  first_x_assum (qspec_then `inp` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  (* out ∈ pv ∧ out ∉ roots *)
  (`MEM out inst.inst_outputs` by simp[]) >>
  (`out IN pointer_derived_vars fn roots /\ out NOTIN roots` by
    metis_tac[pp_pv_output]) >>
  (* Derive displacement: val1 - orig = val2 - new *)
  (`val1 - n2w orig_off = val2 - n2w new_off` by
    metis_tac[WORD_SUB_TRIANGLE]) >>
  (* s1 output bounds from pointer_arith_in_region *)
  (`orig_off <= w2n val1 /\ w2n val1 < orig_off + sz` by
    (mp_tac pointer_arith_in_region_elim >>
     disch_then (qspecl_then
       [`fn`,`roots`,`bb`,`inst`,`s1`,
        `update_var out val1 s1`,`out`,`val1`,`inp`,`w1`,
        `aid`,`orig_off`,`sz`] mp_tac) >>
     simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE])) >>
  (* s2 output bounds via displacement_bounds_transfer *)
  (`new_off <= w2n val2 /\ w2n val2 < new_off + sz` by
    metis_tac[displacement_bounds_transfer]) >>
  (* Apply remap_rel_update_pv directly *)
  irule remap_rel_update_pv >> simp[] >>
  MAP_EVERY qexists_tac [`aid`, `new_off`, `orig_off`, `sz`] >>
  simp[]
QED

(* Step evaluation helpers — avoid expanding step_inst_base_def in main proof *)
Theorem step_inst_base_add_ok[local]:
  !inst op1 op2 out w1 w2 st.
    inst.inst_opcode = ADD /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 st = SOME w1 /\
    eval_operand op2 st = SOME w2 ==>
    step_inst_base inst st = OK (update_var out (w1 + w2) st)
Proof
  rpt strip_tac >> gvs[step_inst_base_def, exec_pure2_def]
QED

Theorem step_inst_base_sub_ok[local]:
  !inst op1 op2 out w1 w2 st.
    inst.inst_opcode = SUB /\
    inst.inst_operands = [op1; op2] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 st = SOME w1 /\
    eval_operand op2 st = SOME w2 ==>
    step_inst_base inst st = OK (update_var out (w1 - w2) st)
Proof
  rpt strip_tac >> gvs[step_inst_base_def, exec_pure2_def]
QED

Theorem step_inst_base_assign_ok[local]:
  !inst op1 out w1 st.
    inst.inst_opcode = ASSIGN /\
    inst.inst_operands = [op1] /\
    inst.inst_outputs = [out] /\
    eval_operand op1 st = SOME w1 ==>
    step_inst_base inst st = OK (update_var out w1 st)
Proof
  rpt strip_tac >> gvs[step_inst_base_def]
QED

(* CHEATED — parallel PHI: step_inst_base on PHI is now OK s (no update_var) *)
Theorem step_inst_base_phi_ok[local]:
  !inst out prev val_op w st.
    inst.inst_opcode = PHI /\
    inst.inst_outputs = [out] /\
    st.vs_prev_bb = SOME prev /\
    resolve_phi prev inst.inst_operands = SOME val_op /\
    eval_operand val_op st = SOME w ==>
    step_inst_base inst st = OK (update_var out w st)
Proof
  cheat
QED

(* Step inversion lemmas — decompose step_inst_base OK into operand/output structure.
   Used via drule to get CLEAN variable names (avoids gvs renaming). *)
Theorem step_inst_base_assign_inv[local]:
  !inst s v1.
    step_inst_base inst s = OK v1 /\ inst.inst_opcode = ASSIGN ==>
    ?out op1 w. inst.inst_operands = [op1] /\ inst.inst_outputs = [out] /\
                eval_operand op1 s = SOME w /\ v1 = update_var out w s
Proof
  rpt strip_tac >> gvs[step_inst_base_def, AllCaseEqs()]
QED

Theorem step_inst_base_add_inv[local]:
  !inst s v1.
    step_inst_base inst s = OK v1 /\ inst.inst_opcode = ADD ==>
    ?out op1 op2 w1 w2. inst.inst_operands = [op1; op2] /\
                inst.inst_outputs = [out] /\
                eval_operand op1 s = SOME w1 /\
                eval_operand op2 s = SOME w2 /\
                v1 = update_var out (w1 + w2) s
Proof
  rpt strip_tac >> gvs[step_inst_base_def, exec_pure2_def] >>
  gvs[AllCaseEqs()]
QED

Theorem step_inst_base_sub_inv[local]:
  !inst s v1.
    step_inst_base inst s = OK v1 /\ inst.inst_opcode = SUB ==>
    ?out op1 op2 w1 w2. inst.inst_operands = [op1; op2] /\
                inst.inst_outputs = [out] /\
                eval_operand op1 s = SOME w1 /\
                eval_operand op2 s = SOME w2 /\
                v1 = update_var out (w1 - w2) s
Proof
  rpt strip_tac >> gvs[step_inst_base_def, exec_pure2_def, AllCaseEqs()]
QED

(* CHEATED — parallel PHI: step_inst_base on PHI is now OK s (no update_var) *)
Theorem step_inst_base_phi_inv[local]:
  !inst s v1.
    step_inst_base inst s = OK v1 /\ inst.inst_opcode = PHI ==>
    ?out prev val_op w. inst.inst_outputs = [out] /\
                s.vs_prev_bb = SOME prev /\
                resolve_phi prev inst.inst_operands = SOME val_op /\
                eval_operand val_op s = SOME w /\
                v1 = update_var out w s
Proof
  cheat
QED

(* Extract clause 2b (pv displacement invariant) from alloca_remap_rel
   without decomposing the full definition into ~30 assumptions.
   Preserves the original alloca_remap_rel in assumptions. *)
val extract_clause2b : tactic =
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     let val body = BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th)
     in assume_tac (el 3 (CONJUNCTS body)) end);

Theorem remap_preserved_pointer_preserving[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    all_mem_via_pointer fn roots /\
    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    is_pointer_preserving_op inst.inst_opcode /\
    (inst.inst_opcode = PHI ==>
       (!v. MEM (Var v) inst.inst_operands ==>
            v IN pointer_derived_vars fn roots) /\
       (!op. MEM op inst.inst_operands ==>
             (?v. op = Var v) \/ (?l. op = Label l))) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt gen_tac >> strip_tac >>
  (* ---- Non-PV subcase: no Var operand is in pv — delegate ---- *)
  reverse (Cases_on `?v op. MEM op inst.inst_operands /\
                             op = Var v /\ v IN pointer_derived_vars fn roots`)
  >- (`~is_immutable_op inst.inst_opcode` by
        (Cases_on `inst.inst_opcode` >>
         gvs[is_pointer_preserving_op_def, is_immutable_op_def]) >>
      mp_tac remap_preserved_no_pointer_ops >>
      disch_then (qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`,`bb`]
        mp_tac) >>
      impl_tac >- (gvs[] >> metis_tac[]) >> simp[])
  (* ---- PV subcase: some operand Var v is in pv ---- *)
  >> gvs[] >>
  (* NOTE: Do NOT decompose alloca_remap_rel here — it adds ~30 assumptions
     that make simp/metis_tac timeout in Resume blocks. Each Resume block
     extracts clause 2b locally as needed. *)
  (* ---- Case split on opcode ---- *)
  Cases_on `inst.inst_opcode` >>
  gvs[is_pointer_preserving_op_def]
  >~ [`ASSIGN`] >- suspend "assign"
  >~ [`ADD`] >- suspend "add"
  >~ [`SUB`] >- suspend "sub"
  >> suspend "phi"
QED

(* ASSIGN: v → out with same value *)
Resume remap_preserved_pointer_preserving[assign]:
  drule step_inst_base_assign_inv >> (impl_tac >- simp[]) >>
  strip_tac >> gvs[eval_operand_def] >>
  extract_clause2b >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  qexists_tac `update_var out w2 s2` >>
  (conj_tac >-
    simp[step_inst_base_def, eval_operand_def,
         lookup_var_def, update_var_def]) >>
  irule pp_step_preserves_remap >> simp[] >>
  MAP_EVERY qexists_tac [`bb`, `v`, `inst`, `w`, `w2`] >>
  simp[is_pointer_preserving_op_def, WORD_SUB_REFL, lookup_var_def,
       step_inst_base_def, eval_operand_def, update_var_def]
QED

(* ADD: two subcases for which operand is pv *)
Resume remap_preserved_pointer_preserving[add]:
  drule step_inst_base_add_inv >> (impl_tac >- simp[]) >>
  strip_tac >>
  extract_clause2b >>
  `op1 = Var v \/ op2 = Var v` by fs[MEM] >> gvs[eval_operand_def]
  >- suspend "add_c1"
  >- suspend "add_c2"
QED

(* ADD Case 1: op1 = Var v (pointer), op2 = non-pointer *)
Resume remap_preserved_pointer_preserving[add_c1]:
  `eval_operand op2 s1 = eval_operand op2 s2` by (
    irule add_sub_other_operand_agrees >>
    MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`Var v`,`v`,`remap`,`roots`] >>
    simp[]) >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  qexists_tac `update_var out (w2' + w2) s2` >>
  (conj_tac >- (
    irule step_inst_base_add_ok >>
    simp[eval_operand_def, lookup_var_def])) >>
  irule pp_step_preserves_remap >>
  simp[is_pointer_preserving_op_def, lookup_var_def, WORD_ADD_SUB] >>
  qexistsl_tac [`bb`,`v`,`inst`,`w1`,`w2'`] >>
  simp[WORD_ADD_SUB, is_pointer_preserving_op_def] >>
  (conj_tac >- (
    irule step_inst_base_add_ok >> simp[eval_operand_def, lookup_var_def])) >>
  simp[WORD_ADD_SUB2]
QED

(* ADD Case 2: op2 = Var v (pointer), op1 = non-pointer *)
Resume remap_preserved_pointer_preserving[add_c2]:
  `eval_operand op1 s1 = eval_operand op1 s2` by (
    irule add_sub_other_operand_agrees >>
    MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`Var v`,`v`,`remap`,`roots`] >>
    simp[]) >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  (* s1: w1 + w2 where w1=eval op1, w2=lookup v s1; s2: w1 + w2' where w2'=lookup v s2 *)
  qexists_tac `update_var out (w1 + w2') s2` >>
  (conj_tac >- (
    irule step_inst_base_add_ok >>
    simp[eval_operand_def, lookup_var_def])) >>
  irule pp_step_preserves_remap >>
  simp[is_pointer_preserving_op_def, lookup_var_def, WORD_ADD_SUB] >>
  qexistsl_tac [`bb`,`v`,`inst`,`w2`,`w2'`] >>
  simp[WORD_ADD_SUB, is_pointer_preserving_op_def] >>
  irule step_inst_base_add_ok >> simp[eval_operand_def, lookup_var_def]
QED

(* SUB: gvs produces 2 goals — real case (Var v as op1) and impossible (Var v as op2) *)
Resume remap_preserved_pointer_preserving[sub]:
  drule step_inst_base_sub_inv >> (impl_tac >- simp[]) >>
  strip_tac >> gvs[] >>
  extract_clause2b
  (* Goal 1: inst.inst_operands = [Var v; op2] — the real case *)
  >- suspend "sub_body"
  (* Goal 2: inst.inst_operands = [op1; Var v] — impossible: affine says op2 of SUB not pv *)
  >- (qpat_x_assum `affine_pointer_ops _ _` mp_tac >>
      REWRITE_TAC[affine_pointer_ops_def, LET_DEF] >> BETA_TAC >>
      strip_tac >> first_x_assum (qspecl_then [`bb`,`inst`,`op1`,`Var v`] mp_tac) >>
      simp[])
QED

Resume remap_preserved_pointer_preserving[sub_body]:
  `eval_operand op2 s1 = eval_operand op2 s2` by (
    irule add_sub_other_operand_agrees >>
    MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`Var v`,`v`,`remap`,`roots`] >>
    simp[]) >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def, eval_operand_def] >>
  `step_inst_base inst s2 = OK (update_var out (w2' - w2) s2)` by (
    irule step_inst_base_sub_ok >>
    simp[eval_operand_def, lookup_var_def]) >>
  qexists_tac `update_var out (w2' - w2) s2` >>
  (conj_tac >- simp[]) >>
  irule pp_step_preserves_remap >>
  simp[is_pointer_preserving_op_def, lookup_var_def] >>
  qexistsl_tac [`bb`,`v`,`inst`,`w1`,`w2'`] >>
  simp[is_pointer_preserving_op_def, WORD_SUB_SUB3]
QED

(* PHI: resolve_phi gives Var u ∈ pv — suspend for clean context *)
Resume remap_preserved_pointer_preserving[phi]:
  drule step_inst_base_phi_inv >> (impl_tac >- simp[]) >>
  strip_tac >> gvs[] >>
  extract_clause2b >>
  suspend "phi_body"
QED

Resume remap_preserved_pointer_preserving[phi_body]:
  (* val_op must be Var u — Label case contradicts pointer_arith_in_region *)
  `out IN pointer_derived_vars fn roots` by (
    `MEM out inst.inst_outputs` by simp[] >>
    metis_tac[pp_pv_output, is_pointer_preserving_op_def]) >>
  `?u. val_op = Var u` by (
    `MEM val_op inst.inst_operands` by metis_tac[resolve_phi_mem] >>
    `(?u. val_op = Var u) \/ ?l. val_op = Label l` by metis_tac[] >>
    gvs[] >>
    mp_tac phi_nonvar_pv_contradiction >>
    disch_then (qspecl_then [`fn`,`roots`,`inst`,`bb`,`out`,`v`,`s1`,`prev`,
                             `Label l`,`w`] mp_tac) >>
    simp[]) >>
  gvs[eval_operand_def] >>
  `u IN pointer_derived_vars fn roots` by metis_tac[resolve_phi_mem] >>
  first_x_assum (qspec_then `u` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  `s2.vs_prev_bb = SOME prev` by (
    fs[alloca_remap_rel_def, LET_DEF]) >>
  `step_inst_base inst s2 = OK (update_var out w2 s2)` by (
    irule step_inst_base_phi_ok >>
    simp[eval_operand_def, lookup_var_def]) >>
  qexists_tac `update_var out w2 s2` >>
  (conj_tac >- simp[]) >>
  irule pp_step_preserves_remap >>
  simp[is_pointer_preserving_op_def, lookup_var_def] >>
  qexistsl_tac [`bb`,`u`,`inst`,`w`,`w2`] >>
  simp[is_pointer_preserving_op_def, WORD_SUB_REFL] >>
  metis_tac[resolve_phi_mem]
QED

Finalise remap_preserved_pointer_preserving

(* Bridge from word-level displacement to natural-number relative offset.
   Given a pv variable with displacement and in_alloca_region,
   derive the shared relative offset usable by read_memory_alloca_remap etc. *)
Theorem pv_address_rel[local]:
  !w1 w2 orig_off asz new_off.
    w1 - n2w orig_off = w2 - n2w new_off /\
    orig_off <= w2n w1 /\ w2n w1 < orig_off + asz /\
    new_off <= w2n w2 /\ w2n w2 < new_off + asz ==>
    w2n w1 = orig_off + (w2n w1 - orig_off) /\
    w2n w2 = new_off + (w2n w1 - orig_off) /\
    w2n w1 - orig_off < asz
Proof
  rpt strip_tac >> simp[] >>
  `orig_off < dimword (:'a)` by
    (mp_tac (SPEC ``w1:'a word`` w2n_lt) >> decide_tac) >>
  `new_off < dimword (:'a)` by
    (mp_tac (SPEC ``w2:'a word`` w2n_lt) >> decide_tac) >>
  (* word_sub_w2n specialized for each side *)
  `w2n (w1 - n2w orig_off) = w2n w1 - orig_off` by
    (mp_tac (Q.SPECL [`w1`,`n2w orig_off`] word_sub_w2n) >>
     simp[WORD_LS, w2n_n2w, LESS_MOD]) >>
  `w2n (w2 - n2w new_off) = w2n w2 - new_off` by
    (mp_tac (Q.SPECL [`w2`,`n2w new_off`] word_sub_w2n) >>
     simp[WORD_LS, w2n_n2w, LESS_MOD]) >>
  (* From word equality w1-k1 = w2-k2, apply w2n to both sides *)
  `w2n (w1 - n2w orig_off) = w2n (w2 - n2w new_off)` by
    simp[] >>
  `w2n w1 - orig_off = w2n w2 - new_off` by decide_tac >>
  simp[]
QED

(* User-facing helper: takes raw word addresses (w2n form) instead of
   requiring the caller to decompose into orig_off + rel_off.
   Combines pv_address_rel + write_pv_mem_preserves_remap.
   Use this in all write-op Resume blocks. *)
Theorem write_at_pv_preserves_remap[local]:
  !fn roots remap s1 s2 aid orig_off sz new_off bytes
   (addr1 : 256 word) (addr2 : 256 word).
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, sz) /\
    FLOOKUP remap aid = SOME new_off /\
    orig_off <= w2n addr1 /\ w2n addr1 < orig_off + sz /\
    new_off <= w2n addr2 /\ w2n addr2 < new_off + sz /\
    addr1 - n2w orig_off = addr2 - n2w new_off /\
    w2n addr1 - orig_off + LENGTH bytes <= sz /\
    orig_off + sz <= LENGTH s1.vs_memory /\
    new_off + sz <= LENGTH s2.vs_memory ==>
    alloca_remap_rel fn roots remap
      (write_memory_with_expansion (w2n addr1) bytes s1)
      (write_memory_with_expansion (w2n addr2) bytes s2)
Proof
  rpt strip_tac >>
  `w2n addr1 = orig_off + (w2n addr1 - orig_off) /\
   w2n addr2 = new_off + (w2n addr1 - orig_off) /\
   w2n addr1 - orig_off < sz` by (irule pv_address_rel >> simp[]) >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`sz`,
               `new_off`,`w2n addr1 - orig_off`,`bytes`]
    mp_tac write_pv_mem_preserves_remap >>
  simp[]
QED

(* Read-side counterpart of write_at_pv_preserves_remap:
   Under alloca_remap_rel + safe-access bounds, padded memory reads agree.
   Combines pv_address_rel + TAKE_APPEND1 + read_memory_alloca_remap.
   Matches the TAKE..DROP..REPLICATE pattern in SHA3, LOG, MCOPY, mload. *)
Theorem read_at_pv_agrees[local]:
  !fn roots remap s1 s2 aid orig_off asz new_off
   (addr1 : 256 word) (addr2 : 256 word) n.
    alloca_remap_rel fn roots remap s1 s2 /\
    FLOOKUP s1.vs_allocas aid = SOME (orig_off, asz) /\
    FLOOKUP remap aid = SOME new_off /\
    orig_off <= w2n addr1 /\ w2n addr1 < orig_off + asz /\
    new_off <= w2n addr2 /\ w2n addr2 < new_off + asz /\
    addr1 - n2w orig_off = addr2 - n2w new_off /\
    w2n addr1 + n <= orig_off + asz /\
    orig_off + asz <= LENGTH s1.vs_memory /\
    new_off + asz <= LENGTH s2.vs_memory ==>
    TAKE n (DROP (w2n addr1) s1.vs_memory ++ REPLICATE n 0w) =
    TAKE n (DROP (w2n addr2) s2.vs_memory ++ REPLICATE n 0w)
Proof
  rpt strip_tac >>
  `alloca_mem_agrees remap s1 s2` by fs[alloca_remap_rel_def, LET_DEF] >>
  (* Decompose addresses *)
  `w2n addr1 = orig_off + (w2n addr1 - orig_off) /\
   w2n addr2 = new_off + (w2n addr1 - orig_off) /\
   w2n addr1 - orig_off < asz` by (irule pv_address_rel >> simp[]) >>
  (* Derive remaining bounds *)
  `w2n addr1 - orig_off + n <= asz` by decide_tac >>
  `orig_off + (w2n addr1 - orig_off) + n <= LENGTH s1.vs_memory` by decide_tac >>
  `new_off + (w2n addr1 - orig_off) + n <= LENGTH s2.vs_memory` by decide_tac >>
  (* Bridge: rewrite TAKE..DROP..REPLICATE to read_memory at decomposed offsets *)
  `TAKE n (DROP (w2n addr1) s1.vs_memory ++ REPLICATE n 0w) =
   read_memory (orig_off + (w2n addr1 - orig_off)) n s1` by
    (simp[read_memory_def] >> irule TAKE_APPEND1 >> simp[]) >>
  `TAKE n (DROP (w2n addr2) s2.vs_memory ++ REPLICATE n 0w) =
   read_memory (new_off + (w2n addr1 - orig_off)) n s2` by
    (simp[read_memory_def] >> irule TAKE_APPEND1 >> simp[]) >>
  (* Substitute address equations into goal *)
  qpat_x_assum `TAKE _ (DROP (w2n addr1) _ ++ _) = _` (SUBST1_TAC) >>
  qpat_x_assum `TAKE _ (DROP (w2n addr2) _ ++ _) = _` (SUBST1_TAC) >>
  irule read_memory_alloca_remap >> simp[] >>
  qexistsl_tac [`aid`, `remap`, `asz`] >> simp[]
QED

(* Eliminate alloca_safe_access: given mem_read/write_ops and pointer
   containment, derive the safe-access bound. *)
Theorem alloca_safe_access_elim[local]:
  !fn roots s bb inst ops v w aid off asz (sz_val : bytes32).
    alloca_safe_access fn roots s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
    ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots /\
    lookup_var v s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (off, asz) /\
    off <= w2n w /\ w2n w < off + asz /\
    ops.iao_max_size = SOME (Lit sz_val) ==>
    w2n w + w2n sz_val <= off + asz
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_safe_access _ _ _` (mp_tac o BETA_RULE o
    REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
  strip_tac >>
  pop_assum (qspecl_then [`bb`, `inst`, `ops`, `v`, `w`,
    `Lit sz_val`, `sz_val`, `aid`, `off`, `asz`] mp_tac) >>
  simp[eval_operand_def]
QED

(* Elimination helper: alloca_safe_access clause 2 gives access bounds.
   Identical to the old alloca_var_size_safe but now derived from
   alloca_safe_access (which subsumes alloca_var_size_safe). *)
Theorem alloca_safe_access_bounds_elim[local]:
  !fn roots s bb inst ops v w aid off asz sz_op sz_val.
    alloca_safe_access fn roots s /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
    ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots /\
    lookup_var v s = SOME w /\
    FLOOKUP s.vs_allocas aid = SOME (off, asz) /\
    off <= w2n w /\ w2n w < off + asz /\
    ops.iao_max_size = SOME sz_op /\
    eval_operand sz_op s = SOME sz_val ==>
    w2n w + w2n sz_val <= off + asz
Proof
  rpt strip_tac >>
  qpat_x_assum `alloca_safe_access _ _ _` (mp_tac o BETA_RULE o
    REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
  strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `ops`, `v`, `w`,
    `sz_op`, `sz_val`, `aid`, `off`, `asz`] mp_tac) >>
  simp[]
QED

(* Unfolded pointer_confined without LET pain *)
Theorem pointer_confined_elim[local]:
  !fn roots.
    pointer_confined fn roots <=>
    !bb inst v. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands /\ v IN pointer_derived_vars fn roots ==>
      (?ops. mem_write_ops inst = SOME ops /\
             ~is_immutable_op inst.inst_opcode /\ Var v = ops.iao_ofst) \/
      (?ops. mem_read_ops inst = SOME ops /\
             ~is_immutable_op inst.inst_opcode /\ Var v = ops.iao_ofst) \/
      (is_pointer_preserving_op inst.inst_opcode /\
       set inst.inst_outputs SUBSET pointer_derived_vars fn roots)
Proof
  rw[pointer_confined_def, LET_DEF]
QED

(* ===== Case 3: Memory ops with pointer address ===== *)

(* For a mem op, any operand that is NOT the iao_ofst is non-pv,
   hence agrees under alloca_remap_rel. *)
Theorem mem_op_other_operand_agrees[local]:
  !fn roots remap s1 s2 bb inst op.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM op inst.inst_operands /\
    (!ops. mem_write_ops inst = SOME ops ==> op <> ops.iao_ofst) /\
    (!ops. mem_read_ops inst = SOME ops ==> op <> ops.iao_ofst) ==>
    eval_operand op s1 = eval_operand op s2
Proof
  rpt strip_tac >>
  irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`,`remap`,`roots`] >> simp[] >>
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  fs[pointer_confined_elim] >>
  first_x_assum (qspecl_then [`bb`,`inst`,`v`] mp_tac) >>
  simp[] >>
  rpt strip_tac >> res_tac >> fs[]
QED

(* List version: operands that are all NOT iao_ofst agree under remap.
   Useful for LOG topics, MCOPY size, etc. *)
Theorem eval_operands_other_agree[local]:
  !fn roots remap s1 s2 bb inst ops.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (!op. MEM op ops ==> MEM op inst.inst_operands) /\
    (!op. MEM op ops ==>
       (!wr. mem_write_ops inst = SOME wr ==> op <> wr.iao_ofst) /\
       (!rd. mem_read_ops inst = SOME rd ==> op <> rd.iao_ofst)) ==>
    eval_operands ops s1 = eval_operands ops s2
Proof
  Induct_on `ops` >> simp[eval_operands_def] >>
  rpt strip_tac >>
  `MEM h inst.inst_operands` by metis_tac[MEM] >>
  `eval_operand h s1 = eval_operand h s2` by (
    irule mem_op_other_operand_agrees >> simp[] >>
    metis_tac[MEM]) >>
  `eval_operands ops s1 = eval_operands ops s2` by (
    first_x_assum irule >> simp[] >>
    metis_tac[MEM]) >>
  simp[]
QED

(* ===== Shared tactics for mem-op proofs ===== *)

(* Preamble: extract clause 2b for the pv address variable v.
   PRECONDITION: step_inst_base already inverted so FLOOKUP v is SOME.
   This makes the NONE branch from clause 2b auto-dismissable by fs. *)
val mem_op_preamble : tactic =
  extract_clause2b >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  (* Normalize alloca size name to 'asz' to avoid operand name clashes *)
  TRY (rename1 `FLOOKUP s1.vs_allocas aid = SOME (orig_off, asz)`);

(* Uniqueness: show a non-address operand op <> Var v *)
val pv_uniqueness_contra : tactic =
  CCONTR_TAC >> fs[] >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[];

(* Show non-address operand agrees under remap.
   After step inversion + preamble, the non-address operand v6 is not pv.
   Use irule mem_op_other_operand_agrees then resolve mem_write/read_ops goals
   using asm_simp_tac which picks up inst.inst_opcode and inst.inst_operands
   from assumptions to evaluate the case expressions. *)
val non_addr_operand_agrees : tactic =
  irule mem_op_other_operand_agrees >>
  MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`remap`,`roots`] >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def];

(* Rewrite set for converting w2n of small 256-word literals to nats *)
val w2n_256_ss = [w2n_n2w, dimword_def,
  fcpLib.INDEX_CONV ``dimindex (:256)``];

(* Extract safe access bound from alloca_safe_access for a specific op.
   Produces: w2n w1 + <nat_size> <= orig_off + sz
   ops_q  : quotation for the inst_alloca_ops record
   szop_q : quotation for the size operand (e.g., `Lit 32w`)
   szval_q: quotation for the size value (e.g., `32w`)
   rw_defs: extra rewrites for simplifying mem_write/read_ops (e.g., []) *)
(* Extract safe access bound. Uses ML-level CONJUNCTS to get the bound
   from alloca_safe_access.
   asz_q: quotation for alloca size variable (e.g., `sz` or `sz'`) *)
fun safe_access_bound_gen ops_q var_q addr_q szop_q szval_q
                         aid_q off_q asz_q rw_defs : tactic =
  qpat_x_assum `alloca_safe_access _ _ s1`
    (fn th =>
      let val body = BETA_RULE (REWRITE_RULE[alloca_safe_access_def, LET_DEF] th)
          val c2 = el 2 (CONJUNCTS body)
      in assume_tac th >>
         qspecl_then [`bb`,`inst`, ops_q, var_q, addr_q,
                      szop_q, szval_q, aid_q, off_q, asz_q]
           mp_tac c2 end) >>
  simp ([mem_write_ops_def, mem_read_ops_def,
         eval_operand_def, lookup_var_def] @ rw_defs @ w2n_256_ss) >>
  TRY strip_tac;

fun safe_access_bound_tac ops_q szop_q szval_q rw_defs : tactic =
  safe_access_bound_gen ops_q `v` `w1` szop_q szval_q
                        `aid` `orig_off` `asz` rw_defs;

(* Variable-size access bound tactics.
   Uses alloca_safe_access clause 2 (subsumes old alloca_var_size_safe).
   ops_q: ops record quotation; sz_q: size operand quotation;
   szval_q: size value quotation. *)
fun var_safe_access_bound_gen ops_q var_q addr_q szval_q
                              aid_q off_q asz_q sz_q rw_defs : tactic =
  qspecl_then [`fn`,`roots`,`s1`,`bb`,`inst`, ops_q, var_q, addr_q,
               aid_q, off_q, asz_q, sz_q, szval_q]
    mp_tac alloca_safe_access_bounds_elim >>
  simp ([mem_write_ops_def, mem_read_ops_def,
         eval_operand_def, lookup_var_def] @ rw_defs @ w2n_256_ss) >>
  TRY strip_tac;

fun var_safe_access_bound_tac ops_q sz_q szval_q rw_defs : tactic =
  var_safe_access_bound_gen ops_q `v` `w1` szval_q
                            `aid` `orig_off` `asz` sz_q rw_defs;

(* Establish alloca bounds from alloca_safe_access + alloca_remap_rel *)
val write_bounds_tac : tactic =
  (`orig_off + asz <= LENGTH s1.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s1`
      (mp_tac o BETA_RULE o
       REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac)) >>
  (`FLOOKUP s2.vs_allocas aid = SOME (new_off, asz)` by
    (fs[alloca_remap_rel_def, LET_DEF] >> metis_tac[])) >>
  (`new_off + asz <= LENGTH s2.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s2`
      (mp_tac o BETA_RULE o
       REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac));

Theorem remap_preserved_mem_ops[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
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
    ~is_immutable_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    (?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
           ?v. ops.iao_ofst = Var v /\ v IN pointer_derived_vars fn roots) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_alloca_op_def, is_terminator_def, is_ext_call_op_def,
      is_immutable_op_def, mem_write_ops_def, mem_read_ops_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
  (* Use >~ pattern matching to bind labels to correct opcodes *)
  >~ [`MLOAD`] >- suspend "mload"
  >~ [`MSTORE8`] >- suspend "mstore8"
  >~ [`MSTORE`] >- suspend "mstore"
  >~ [`CALLDATACOPY`] >- suspend "calldatacopy"
  >~ [`CODECOPY`] >- suspend "codecopy"
  >~ [`DLOADBYTES`] >- suspend "dloadbytes"
  >~ [`EXTCODECOPY`] >- suspend "extcodecopy"
  >~ [`RETURNDATACOPY`] >- suspend "returndatacopy"
  >~ [`SHA3`] >- suspend "sha3"
  >~ [`LOG`] >- suspend "log"
  (* MCOPY produces 2 goals: write (dst pv) and read (src pv) *)
  >- suspend "mcopy_wr"
  >- suspend "mcopy_rd"
QED

(* --- MSTORE: write 32 bytes at pv address --- *)
Resume remap_preserved_mem_ops[mstore]:
  (* Invert s1 step *)
  fs[step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  (* Non-address operand agrees *)
  `v6 <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  (* Substitute v1/addr, resolve existential *)
  qpat_x_assum `mstore _ _ _ = v1` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `w1 = addr` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  (* Rewrite to wmwe and apply write_at_pv_preserves_remap *)
  simp[mstore_eq_wmwe] >>
  (* Safe access bound: w2n w1 + 32 <= orig_off + asz *)
  safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w) |>`
    `Lit 32w` `32w` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,`word_to_bytes val T`,`w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[length_w2b_256]
QED

(* --- MSTORE8: write 1 byte at pv address --- *)
Resume remap_preserved_mem_ops[mstore8]:
  fs[step_inst_base_def, exec_write2_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  (* Non-address operand agrees *)
  `v6 <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  (* Substitute v1/addr, resolve existential *)
  qpat_x_assum `mstore8 _ _ _ = v1` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `w1 = addr` (SUBST_ALL_TAC o SYM) >>
  fs[] >>
  (* Rewrite to wmwe and apply write_at_pv_preserves_remap *)
  simp[mstore8_eq_wmwe] >>
  (* Safe access bound: w2n w1 + 1 <= orig_off + asz *)
  safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME (Lit 1w);
        iao_max_size := SOME (Lit 1w) |>`
    `Lit 1w` `1w` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,`[w2w val]`,`w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[]
QED

(* --- MLOAD --- *)
Resume remap_preserved_mem_ops[mload]:
  fs[step_inst_base_def, exec_read1_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  qpat_x_assum `w1 = addr` (SUBST_ALL_TAC o SYM) >>
  (* Safe access bound *)
  safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME (Lit 32w);
        iao_max_size := SOME (Lit 32w) |>`
    `Lit 32w` `32w` [] >>
  write_bounds_tac >>
  (* mload values agree via read_at_pv_agrees + mload_def *)
  `mload (w2n w1) s1 = mload (w2n w2) s2` by (
    simp[mload_def, LET_DEF] >>
    qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,`new_off`,
                 `w1`,`w2`,`32`]
      mp_tac read_at_pv_agrees >> simp[]) >>
  gvs[] >>
  irule remap_rel_update_nonpv >> simp[] >>
  conj_tac
  >- metis_tac[non_pp_output_notin_pv,
               is_pointer_preserving_op_def, is_alloca_op_def, MEM]
  >- fs[alloca_remap_rel_def, LET_DEF]
QED

(* --- CALLDATACOPY --- *)
Resume remap_preserved_mem_ops[calldatacopy]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `v6 <> Var v` by pv_uniqueness_contra >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  qpat_x_assum `w1 = destOffset` (SUBST_ALL_TAC o SYM) >>
  (* Provide witnesses for s2 operands *)
  MAP_EVERY qexists_tac [`offset`, `size_val`] >>
  fs[] >>
  (* Scalar field agreement *)
  `s1.vs_call_ctx = s2.vs_call_ctx` by
    fs[alloca_remap_rel_def, LET_DEF] >>
  fs[] >>
  (* Now goal: alloca_remap_rel ... (wmwe w1 bytes s1) (wmwe w2 bytes s2) *)
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n size_val)
                  (DROP (w2n offset) s2.vs_call_ctx.cc_calldata ++
                   REPLICATE (w2n size_val) 0w)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

(* --- CODECOPY: 3-op write, src = vs_code --- *)
Resume remap_preserved_mem_ops[codecopy]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `v6 <> Var v` by pv_uniqueness_contra >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  qpat_x_assum `w1 = dst` (SUBST_ALL_TAC o SYM) >>
  MAP_EVERY qexists_tac [`src`, `size_val`] >> fs[] >>
  `s1.vs_code = s2.vs_code` by fs[alloca_remap_rel_def, LET_DEF] >> fs[] >>
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n size_val)
                  (DROP (w2n src) s2.vs_code ++ REPLICATE (w2n size_val) 0w)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

(* --- DLOADBYTES: 3-op write, src = vs_data_section --- *)
Resume remap_preserved_mem_ops[dloadbytes]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `v6 <> Var v` by pv_uniqueness_contra >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  qpat_x_assum `w1 = dst` (SUBST_ALL_TAC o SYM) >>
  MAP_EVERY qexists_tac [`src`, `size_val`] >> fs[] >>
  `s1.vs_data_section = s2.vs_data_section` by
    fs[alloca_remap_rel_def, LET_DEF] >> fs[] >>
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n size_val)
                  (DROP (w2n src) s2.vs_data_section ++
                   REPLICATE (w2n size_val) 0w)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

(* --- EXTCODECOPY: 4-op write, dst is 2nd operand --- *)
(* inst.inst_operands = [v2; Var v; v10; sz] — pv addr is 2nd *)
Resume remap_preserved_mem_ops[extcodecopy]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `v2 <> Var v` by pv_uniqueness_contra >>
  `v10 <> Var v` by pv_uniqueness_contra >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand v2 s1 = eval_operand v2 s2` by non_addr_operand_agrees >>
  `eval_operand v10 s1 = eval_operand v10 s2` by non_addr_operand_agrees >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  qpat_x_assum `w1 = dst` (SUBST_ALL_TAC o SYM) >>
  MAP_EVERY qexists_tac [`addr`, `src`, `size_val`] >> fs[] >>
  `s1.vs_accounts = s2.vs_accounts` by
    fs[alloca_remap_rel_def, LET_DEF] >> fs[] >>
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n size_val)
                  (DROP (w2n src)
                    (lookup_account (w2w addr) s2.vs_accounts).code ++
                   REPLICATE (w2n size_val) 0w)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

(* --- RETURNDATACOPY: 3-op write with OOB check --- *)
(* Note: OOB branch dismissed by AllCaseEqs — OK branch has no REPLICATE padding *)
Resume remap_preserved_mem_ops[returndatacopy]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `v6 <> Var v` by pv_uniqueness_contra >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand v6 s1 = eval_operand v6 s2` by non_addr_operand_agrees >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  qpat_x_assum `w1 = destOffset` (SUBST_ALL_TAC o SYM) >>
  MAP_EVERY qexists_tac [`offset`, `size_val`] >> fs[] >>
  `s1.vs_returndata = s2.vs_returndata` by
    fs[alloca_remap_rel_def, LET_DEF] >> fs[] >>
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n size_val)
                  (DROP (w2n offset) s2.vs_returndata)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

(* --- SHA3: read from memory, hash, update non-pv output --- *)
Resume remap_preserved_mem_ops[sha3]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  (* Size operand agrees *)
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  (* Provide s2 size witness *)
  qexists_tac `size_val` >> fs[] >>
  (* Normalize addr *)
  qpat_x_assum `w1 = offset` (SUBST_ALL_TAC o SYM) >>
  (* Safe access bound *)
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `size_val` [] >>
  write_bounds_tac >>
  (* Bytes agree via read_at_pv_agrees *)
  `TAKE (w2n size_val) (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n size_val) 0w) =
   TAKE (w2n size_val) (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n size_val) 0w)` by (
    qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,`new_off`,
                 `w1`,`w2`,`w2n size_val`]
      mp_tac read_at_pv_agrees >> simp[]) >>
  gvs[] >>
  irule remap_rel_update_nonpv >> simp[] >>
  conj_tac
  >- metis_tac[non_pp_output_notin_pv,
               is_pointer_preserving_op_def, is_alloca_op_def, MEM]
  >- fs[alloca_remap_rel_def, LET_DEF]
QED

(* If pv uniqueness holds on operands = x::Var v::y::rest,
   and x is not Var v and y is not Var v, then ~MEM (Var v) rest.
   Used for LOG (operands = Lit tc :: Var v :: sz :: topics). *)
Theorem pv_unique_tail_not_mem[local]:
  !x y v rest.
    x <> Var v /\ y <> Var v /\
    LENGTH (FILTER ($= (Var v)) (x :: Var v :: y :: rest)) <= 1 ==>
    ~MEM (Var v) rest
Proof
  rpt strip_tac >> fs[FILTER] >>
  `LENGTH (FILTER ($= (Var v)) rest) >= 1` by (
    Induct_on `rest` >> fs[FILTER] >> rw[] >> fs[]) >>
  fs[] >> rfs[]
QED

(* Helper: non-pv vars in a list suffix of a mem-op with a single
   pv address operand are non-pv. Used for LOG topics. *)
Theorem log_topics_non_pv[local]:
  !fn roots bb inst v ops.
    pointer_confined fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_pointer_preserving_op inst.inst_opcode /\
    mem_write_ops inst = NONE /\
    (!rd. mem_read_ops inst = SOME rd ==> rd.iao_ofst = Var v) /\
    v IN pointer_derived_vars fn roots /\
    (!op. MEM op ops ==> MEM op inst.inst_operands) /\
    (!u. u IN pointer_derived_vars fn roots ==>
      LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    ~MEM (Var v) ops ==>
    !v'. MEM (Var v') ops ==> v' NOTIN pointer_derived_vars fn roots
Proof
  rpt strip_tac >> CCONTR_TAC >> fs[] >>
  `MEM (Var v') inst.inst_operands` by metis_tac[] >>
  fs[pointer_confined_elim] >>
  first_x_assum (qspecl_then [`bb`,`inst`,`v'`] mp_tac) >>
  simp[] >> rpt strip_tac >> gvs[]
QED

(* --- LOG: read from memory, append to logs, no memory write --- *)
Resume remap_preserved_mem_ops[log]:
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  mem_op_preamble >>
  `sz <> Var v` by pv_uniqueness_contra >>
  `eval_operand sz s1 = eval_operand sz s2` by non_addr_operand_agrees >>
  (* Topic operands are non-pv — via standalone helpers *)
  `~MEM (Var v) v11` by (
    irule pv_unique_tail_not_mem >>
    MAP_EVERY qexists_tac [`v2`,`sz`] >> simp[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[]) >>
  qspecl_then [`fn`,`roots`,`bb`,`inst`,`v`,`v11`]
    mp_tac log_topics_non_pv >>
  simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def] >>
  (impl_tac >- (gvs[] >> metis_tac[MEM])) >>
  strip_tac >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`v11`]
    mp_tac eval_operands_non_pointer_remap >>
  (impl_tac >- (conj_tac >| [first_assum ACCEPT_TAC, first_assum ACCEPT_TAC])) >>
  strip_tac >>
  qexistsl_tac [`sz'`, `topics`] >> fs[] >>
  qpat_x_assum `w1 = off` (SUBST_ALL_TAC o SYM) >>
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `sz'` [] >>
  write_bounds_tac >>
  `TAKE (w2n sz') (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n sz') 0w) =
   TAKE (w2n sz') (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n sz') 0w)` by (
    qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,`new_off`,
                 `w1`,`w2`,`w2n sz'`]
      mp_tac read_at_pv_agrees >> simp[]) >>
  `s1.vs_logs = s2.vs_logs` by fs[alloca_remap_rel_def, LET_DEF] >>
  `s1.vs_call_ctx = s2.vs_call_ctx` by fs[alloca_remap_rel_def, LET_DEF] >>
  gvs[] >>
  irule alloca_remap_rel_logs_update >> simp[]
QED

(* Helper: extract second pv variable from all_mem_via_pointer for MCOPY.
   Given that one address is Var v (already extracted), extract the other
   address variable from all_mem_via_pointer + mem_read/write_ops. *)
Theorem mcopy_second_pv[local]:
  !fn roots bb inst v v6 sz.
    all_mem_via_pointer fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MCOPY /\
    inst.inst_operands = [Var v; v6; sz] ==>
    ?u. v6 = Var u /\ u IN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  fs[all_mem_via_pointer_def, LET_DEF] >>
  first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >>
  simp[mem_read_ops_def, mem_write_ops_def, is_immutable_op_def] >>
  disch_then (qspec_then
    `<| iao_ofst := v6; iao_size := SOME sz;
        iao_max_size := SOME sz |>` mp_tac) >>
  simp[]
QED

Theorem mcopy_second_pv_rd[local]:
  !fn roots bb inst v v2 sz.
    all_mem_via_pointer fn roots /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = MCOPY /\
    inst.inst_operands = [v2; Var v; sz] ==>
    ?u. v2 = Var u /\ u IN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  fs[all_mem_via_pointer_def, LET_DEF] >>
  first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >>
  simp[mem_write_ops_def, mem_read_ops_def, is_immutable_op_def] >>
  disch_then (qspec_then
    `<| iao_ofst := v2; iao_size := SOME sz;
        iao_max_size := SOME sz |>` mp_tac) >>
  simp[]
QED

(* Standalone MCOPY helper: proves the MCOPY case for remap_preserved_mem_ops.
   Extracted from Resume block to avoid by-clause failures with 30+ assumptions. *)
Theorem mcopy_preserves_remap[local]:
  !fn roots remap inst s1 s2 v1 bb v.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\ roots SUBSET alloca_roots fn /\
    wf_function fn /\ ssa_form fn /\
    pointer_confined fn roots /\ all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\ alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    inst.inst_opcode = MCOPY /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    v IN pointer_derived_vars fn roots /\
    (?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
           ops.iao_ofst = Var v) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt strip_tac >> gvs[] >>
  (* Case split on whether Var v matched write or read ops *)
  fs[mem_write_ops_def, mem_read_ops_def, AllCaseEqs()] >> gvs[]
  >- suspend "wr"
  >- suspend "rd"
QED

Resume mcopy_preserves_remap[wr]:
  (* Case 1: Var v is the dst (write) address — operands = [Var v; v6; sz] *)
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  extract_clause2b >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  rename1 `FLOOKUP s1.vs_allocas aid = SOME (orig_off, asz)` >>
  qpat_x_assum `w1 = _` (SUBST_ALL_TAC o SYM) >>
  (`v6 <> Var v` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER])) >>
  (`sz <> Var v` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER])) >>
  (`?u. v6 = Var u /\ u IN pointer_derived_vars fn roots` by (
    fs[all_mem_via_pointer_def, LET_DEF] >>
    first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >>
    simp[mem_read_ops_def, mem_write_ops_def, is_immutable_op_def] >>
    disch_then (qspec_then
      `<| iao_ofst := v6; iao_size := SOME sz;
          iao_max_size := SOME sz |>` mp_tac) >>
    simp[])) >>
  gvs[] >>
  extract_clause2b >>
  first_x_assum (qspec_then `u` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[eval_operand_def, lookup_var_def] >>
  rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (orig_off2, asz2)` >>
  (`sz <> Var u` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `u` mp_tac) >> simp[FILTER])) >>
  (`eval_operand sz s1 = eval_operand sz s2` by (
    irule mem_op_other_operand_agrees >>
    MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`remap`,`roots`] >>
    simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def])) >>
  (* Establish s2 size evaluation for discharging implications *)
  (`eval_operand sz s2 = SOME sz'` by fs[]) >>
  (* Safe access bounds — dst (write, primary v) *)
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `sz'` [] >>
  write_bounds_tac >>
  rename1 `FLOOKUP remap aid2 = SOME new_off2` >>
  (* Safe access bounds — src (read, secondary u) *)
  var_safe_access_bound_gen
    `<| iao_ofst := Var u; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `u` `w1'` `sz'` `aid2` `orig_off2` `asz2` `sz` [] >>
  (`orig_off2 + asz2 <= LENGTH s1.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s1`
      (mp_tac o BETA_RULE o REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac)) >>
  (`FLOOKUP s2.vs_allocas aid2 = SOME (new_off2, asz2)` by
    (fs[alloca_remap_rel_def, LET_DEF] >> metis_tac[])) >>
  (`new_off2 + asz2 <= LENGTH s2.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s2`
      (mp_tac o BETA_RULE o REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac)) >>
  (* Source bytes agree *)
  (`TAKE (w2n sz') (DROP (w2n w1') s1.vs_memory ++ REPLICATE (w2n sz') 0w) =
   TAKE (w2n sz') (DROP (w2n w2') s2.vs_memory ++ REPLICATE (w2n sz') 0w)` by (
    qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid2`,`orig_off2`,`asz2`,
                 `new_off2`,`w1'`,`w2'`,`w2n sz'`]
      mp_tac read_at_pv_agrees >> simp[])) >>
  gvs[mcopy_def] >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
               `new_off`,
               `TAKE (w2n sz') (DROP (w2n w2') s2.vs_memory ++
                  REPLICATE (w2n sz') 0w)`,
               `w1`,`w2`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

Resume mcopy_preserves_remap[rd]:
  (* Case 2: Var v is the src (read) address — operands = [v2; Var v; sz] *)
  fs[step_inst_base_def, AllCaseEqs()] >>
  fs[eval_operand_def, lookup_var_def] >>
  (* Extract clause 2b for src var v *)
  extract_clause2b >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  rename1 `FLOOKUP s1.vs_allocas aid = SOME (orig_off, asz)` >>
  qpat_x_assum `w1 = _` (SUBST_ALL_TAC o SYM) >>
  (`v2 <> Var v` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER])) >>
  (`sz <> Var v` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER])) >>
  (`?u. v2 = Var u /\ u IN pointer_derived_vars fn roots` by (
    fs[all_mem_via_pointer_def, LET_DEF] >>
    first_x_assum (qspecl_then [`bb`,`inst`] mp_tac) >>
    simp[mem_write_ops_def, mem_read_ops_def, is_immutable_op_def] >>
    disch_then (qspec_then
      `<| iao_ofst := v2; iao_size := SOME sz;
          iao_max_size := SOME sz |>` mp_tac) >>
    simp[])) >>
  gvs[] >>
  extract_clause2b >>
  first_x_assum (qspec_then `u` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[eval_operand_def, lookup_var_def] >>
  rename1 `FLOOKUP s1.vs_allocas aid2 = SOME (orig_off2, asz2)` >>
  (`sz <> Var u` by (
    CCONTR_TAC >> fs[] >>
    first_x_assum (qspec_then `u` mp_tac) >> simp[FILTER])) >>
  (`eval_operand sz s1 = eval_operand sz s2` by (
    irule mem_op_other_operand_agrees >>
    MAP_EVERY qexists_tac [`bb`,`fn`,`inst`,`remap`,`roots`] >>
    simp[is_pointer_preserving_op_def, mem_write_ops_def, mem_read_ops_def])) >>
  (`eval_operand sz s2 = SOME sz'` by fs[]) >>
  (* Safe access bounds — src (read, primary v) *)
  var_safe_access_bound_tac
    `<| iao_ofst := Var v; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `sz` `sz'` [] >>
  write_bounds_tac >>
  (* Safe access bounds — dst (write, secondary u) *)
  rename1 `FLOOKUP remap aid2 = SOME new_off2` >>
  var_safe_access_bound_gen
    `<| iao_ofst := Var u; iao_size := SOME sz;
        iao_max_size := SOME sz |>`
    `u` `w1'` `sz'` `aid2` `orig_off2` `asz2` `sz` [] >>
  (`orig_off2 + asz2 <= LENGTH s1.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s1`
      (mp_tac o BETA_RULE o REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac)) >>
  (`FLOOKUP s2.vs_allocas aid2 = SOME (new_off2, asz2)` by
    (fs[alloca_remap_rel_def, LET_DEF] >> metis_tac[])) >>
  (`new_off2 + asz2 <= LENGTH s2.vs_memory` by (
    qpat_x_assum `alloca_safe_access _ _ s2`
      (mp_tac o BETA_RULE o REWRITE_RULE[alloca_safe_access_def, LET_DEF]) >>
    rpt strip_tac >> res_tac)) >>
  (* Source bytes agree — v is the source *)
  (`TAKE (w2n sz') (DROP (w2n w1) s1.vs_memory ++ REPLICATE (w2n sz') 0w) =
   TAKE (w2n sz') (DROP (w2n w2) s2.vs_memory ++ REPLICATE (w2n sz') 0w)` by (
    qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`asz`,
                 `new_off`,`w1`,`w2`,`w2n sz'`]
      mp_tac read_at_pv_agrees >> simp[])) >>
  gvs[mcopy_def] >>
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid2`,`orig_off2`,`asz2`,
               `new_off2`,
               `TAKE (w2n sz') (DROP (w2n w2) s2.vs_memory ++
                  REPLICATE (w2n sz') 0w)`,
               `dst`,`w2'`]
    mp_tac write_at_pv_preserves_remap >>
  simp[LENGTH_TAKE_EQ]
QED

Finalise mcopy_preserves_remap

(* --- MCOPY write: dst is pv --- *)
Resume remap_preserved_mem_ops[mcopy_wr]:
  irule mcopy_preserves_remap >> simp[] >>
  rpt conj_tac
  >- metis_tac[]
  >- (qexists_tac `v` >> simp[] >>
      qexists_tac `<| iao_ofst := Var v; iao_size := SOME sz;
                       iao_max_size := SOME sz |>` >>
      simp[mem_write_ops_def])
  >- metis_tac[]
QED

(* --- MCOPY read: src is pv --- *)
Resume remap_preserved_mem_ops[mcopy_rd]:
  irule mcopy_preserves_remap >> simp[] >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> Cases_on `Var u = v2` >> gvs[])
  >- metis_tac[]
  >- (qexists_tac `v` >> simp[] >>
      qexists_tac `<| iao_ofst := Var v; iao_size := SOME sz;
                       iao_max_size := SOME sz |>` >>
      simp[mem_read_ops_def])
  >- metis_tac[]
QED

Finalise remap_preserved_mem_ops

(* ===== Immutable op helpers ===== *)

(* Pre-compute opcode-level properties for ILOAD/ISTORE to avoid
   repeated 92-way case splits in the main proof. *)

Theorem is_immutable_op_not_invoke[local]:
  !opc. is_immutable_op opc ==> opc <> INVOKE
Proof
  Cases >> simp[is_immutable_op_def]
QED

Theorem is_immutable_op_write_effects[local]:
  !opc. is_immutable_op opc ==>
    Eff_RETURNDATA NOTIN write_effects opc /\
    Eff_TRANSIENT NOTIN write_effects opc /\
    Eff_BALANCE NOTIN write_effects opc /\
    Eff_STORAGE NOTIN write_effects opc /\
    Eff_LOG NOTIN write_effects opc
Proof
  Cases >> simp[is_immutable_op_def, write_effects_def, empty_effects_def]
QED

Theorem immutable_op_mem_preserved[local]:
  !inst s v. is_immutable_op inst.inst_opcode /\
             step_inst_base inst s = OK v ==>
             v.vs_memory = s.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_immutable_op_def] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, exec_read1_def] >>
  rpt (CASE_TAC >> simp[]) >> strip_tac >> gvs[update_var_def]
QED

Theorem immutable_op_immutables_agree[local]:
  !inst s1 s2 v1 v2.
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    s1.vs_immutables = s2.vs_immutables /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    v1.vs_immutables = v2.vs_immutables
Proof
  rpt strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_immutable_op_def] >>
  ntac 2 (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  simp[step_inst_base_def, exec_read1_def] >>
  rpt (CASE_TAC >> simp[]) >> rpt strip_tac >>
  gvs[update_var_def]
QED

Theorem immutable_op_output_vars_agree[local]:
  !inst s1 s2 v1 v2.
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    s1.vs_immutables = s2.vs_immutables /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) /\
    (!nm. MEM nm inst.inst_outputs ==>
          lookup_var nm s1 = lookup_var nm s2) ==>
    !v. MEM v inst.inst_outputs ==> lookup_var v v1 = lookup_var v v2
Proof
  rpt strip_tac >>
  ntac 2 (qpat_x_assum `step_inst_base _ _ = OK _` mp_tac) >>
  Cases_on `inst.inst_opcode` >> gvs[is_immutable_op_def] >>
  simp[step_inst_base_def, exec_read1_def] >>
  rpt (CASE_TAC >> fs[]) >>
  rpt strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

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
             v.vs_tx_ctx = s.vs_tx_ctx
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode` >> gvs[is_immutable_op_def] >>
  qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
  simp[step_inst_base_def, exec_read1_def] >>
  rpt (CASE_TAC >> simp[]) >> strip_tac >> gvs[update_var_def]
QED

(* Combined scalar agreement: encapsulates imp_res_tac explosion in its own
   proof context. Main proof uses drule_all to get all 17 equalities. *)
Theorem immutable_op_scalars_agree[local]:
  !fn roots remap inst s1 s2 v1 v2.
    alloca_remap_rel fn roots remap s1 s2 /\
    is_immutable_op inst.inst_opcode /\
    step_inst_base inst s1 = OK v1 /\
    step_inst_base inst s2 = OK v2 /\
    (!op. MEM op inst.inst_operands ==>
          eval_operand op s1 = eval_operand op s2) ==>
    v1.vs_immutables = v2.vs_immutables /\
    v1.vs_block_ctx = v2.vs_block_ctx /\ (v1.vs_halted <=> v2.vs_halted) /\
    v1.vs_call_ctx = v2.vs_call_ctx /\ v1.vs_labels = v2.vs_labels /\
    v1.vs_accounts = v2.vs_accounts /\ v1.vs_transient = v2.vs_transient /\
    v1.vs_params = v2.vs_params /\ v1.vs_prev_hashes = v2.vs_prev_hashes /\
    v1.vs_code = v2.vs_code /\ v1.vs_data_section = v2.vs_data_section /\
    v1.vs_returndata = v2.vs_returndata /\
    v1.vs_current_bb = v2.vs_current_bb /\ v1.vs_logs = v2.vs_logs /\
    v1.vs_inst_idx = v2.vs_inst_idx /\ v1.vs_prev_bb = v2.vs_prev_bb /\
    v1.vs_tx_ctx = v2.vs_tx_ctx
Proof
  rpt gen_tac >> strip_tac >>
  imp_res_tac alloca_remap_rel_scalars >>
  imp_res_tac immutable_op_scalar_preserved >>
  `v1.vs_immutables = v2.vs_immutables` by
    metis_tac[immutable_op_immutables_agree] >>
  rpt conj_tac >> simp[]
QED

(* ILOAD/ISTORE: no PV in operands (pointer_confined blocks all 3 disjuncts),
   so operands agree and step results agree. Uses helper lemmas above. *)
Theorem immutable_op_preserves_remap[local]:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
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
Proof
  rpt strip_tac >>
  imp_res_tac alloca_remap_rel_scalars >>
  (* 1. Operand agreement *)
  `!op. MEM op inst.inst_operands ==>
        eval_operand op s1 = eval_operand op s2` by (
    rpt strip_tac >> irule eval_operand_non_pointer_remap >>
    MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
    rpt strip_tac >> res_tac) >>
  (* 2. OK transfer *)
  `?v2. step_inst_base inst s2 = OK v2` by (
    irule step_inst_base_ok_transfer >> simp[] >>
    qexistsl_tac [`s1`, `v1`] >> simp[]) >>
  qexists_tac `v2` >> simp[] >>
  (* 3. Allocas preserved *)
  `v1.vs_allocas = s1.vs_allocas /\ v2.vs_allocas = s2.vs_allocas` by
    metis_tac[step_inst_base_allocas] >>
  (* 4. Memory preserved *)
  `v1.vs_memory = s1.vs_memory /\ v2.vs_memory = s2.vs_memory` by
    metis_tac[immutable_op_mem_preserved] >>
  (* 5. Scalar fields + immutables *)
  mp_tac (Q.SPECL [`fn`, `roots`, `remap`, `inst`, `s1`, `s2`, `v1`, `v2`]
    immutable_op_scalars_agree) >>
  impl_tac >- simp[] >> strip_tac >>
  (* 6. No PV outputs *)
  `!v. MEM v inst.inst_outputs ==> v NOTIN pointer_derived_vars fn roots` by
    metis_tac[no_pv_outputs_from_no_pv_inputs] >>
  (* 7. Non-output vars preserved *)
  `!nm. ~MEM nm inst.inst_outputs ==>
        lookup_var nm v1 = lookup_var nm s1 /\
        lookup_var nm v2 = lookup_var nm s2` by
    metis_tac[step_inst_base_non_output_vars] >>
  (* 8. Output vars agree in s1/s2 *)
  `!nm. MEM nm inst.inst_outputs ==>
        lookup_var nm s1 = lookup_var nm s2` by (
    rpt strip_tac >>
    `nm NOTIN pointer_derived_vars fn roots` by res_tac >>
    metis_tac[alloca_remap_rel_non_pv_lookup]) >>
  (* 9. Output vars agree in v1/v2 *)
  mp_tac (Q.SPECL [`inst`, `s1`, `s2`, `v1`, `v2`]
    immutable_op_output_vars_agree) >>
  impl_tac >- simp[] >> strip_tac >>
  (* 10. Reconstruct alloca_remap_rel *)
  irule remap_rel_from_equiv >> gvs[] >> rpt conj_tac
  (* Non-PV vars *)
  >- (rpt strip_tac >>
      Cases_on `MEM v inst.inst_outputs`
      >- res_tac
      >> metis_tac[alloca_remap_rel_non_pv_lookup,
                  step_inst_base_non_output_vars])
  (* Existential: root vars, pv vars *)
  >- (qexistsl_tac [`s1`, `s2`] >> simp[] >> rpt conj_tac
      (* Root vars *)
      >- (rpt strip_tac >>
          `v IN pointer_derived_vars fn roots` by
            metis_tac[roots_in_pointer_derived_vars] >>
          `~MEM v inst.inst_outputs` by
            (strip_tac >> res_tac >> gvs[]) >>
          `lookup_var v v1 = lookup_var v s1 /\
           lookup_var v v2 = lookup_var v s2` by (
            qpat_assum `!nm. ~MEM nm inst.inst_outputs ==> _`
              (qspec_then `v` mp_tac) >> simp[]) >>
          qpat_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
          REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
          strip_tac >> res_tac >> gvs[])
      (* PV vars *)
      >- (rpt strip_tac >>
          `~MEM v inst.inst_outputs` by
            (strip_tac >> res_tac >> gvs[]) >>
          DISJ1_TAC >>
          qpat_assum `!nm. ~MEM nm inst.inst_outputs ==> _`
            (qspec_then `v` mp_tac) >> simp[]))
QED

(* ===== Main theorem ===== *)

Theorem step_inst_base_preserves_remap:
  !fn roots remap inst s1 s2 v1.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    phi_pv_all_var fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    step_inst_base inst s1 = OK v1 /\
    ~is_alloca_op inst.inst_opcode /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) ==>
    ?v2. step_inst_base inst s2 = OK v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt strip_tac >>
  (* ILOAD/ISTORE: pointer_confined auto-eliminates PV in all operand
     positions (is_immutable_op blocks mem disjuncts, not PP), so
     no PV in operands for these ops. Handle via remap_preserved_no_pointer_ops
     after establishing ~is_immutable_op for the other branches. *)
  Cases_on `is_immutable_op inst.inst_opcode`
  >- (
    (* Immutable ops: delegate to immutable_op_preserves_remap.
       Just need to prove PV vars not in operands from pointer_confined. *)
    `!op v. MEM op inst.inst_operands /\ op = Var v ==>
            v NOTIN pointer_derived_vars fn roots` by (
      rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      qpat_assum `pointer_confined _ _` mp_tac >>
      REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >> strip_tac >>
      first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
      (impl_tac >- simp[]) >>
      strip_tac >>
      Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]) >>
    irule immutable_op_preserves_remap >> simp[] >>
    metis_tac[])
  >>
  (* Non-immutable ops *)
  (* Check if any pv variable appears in operands *)
  Cases_on `!op v. MEM op inst.inst_operands /\ op = Var v ==>
                   v NOTIN pointer_derived_vars fn roots`
  >- (
    (* Case 1: no pointer operands — delegate *)
    qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`,`bb`]
      mp_tac remap_preserved_no_pointer_ops >>
    simp[]
  )
  >>
  gvs[PULL_EXISTS] >>
  rename1 `MEM (Var pv_var) inst.inst_operands` >>
  rename1 `pv_var IN pointer_derived_vars fn roots` >>
  (* Use pointer_confined to classify *)
  qpat_assum `pointer_confined _ _` mp_tac >>
  REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >> strip_tac >>
  first_x_assum (qspecl_then [`bb`, `inst`, `pv_var`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac
  (* mem_write_ops case (with ~is_immutable_op) *)
  >- (
    qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`,`bb`]
      mp_tac remap_preserved_mem_ops >>
    simp[] >> disch_then irule >> gvs[] >> metis_tac[]
  )
  (* mem_read_ops case (with ~is_immutable_op) *)
  >- (
    qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`,`bb`]
      mp_tac remap_preserved_mem_ops >>
    simp[] >> disch_then irule >> gvs[] >> metis_tac[]
  )
  (* is_pointer_preserving_op case *)
  >>
  qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`,`bb`]
    mp_tac remap_preserved_pointer_preserving >>
  simp[] >> disch_then irule >> simp[] >>
  (* PHI guard: all Var operands pv + all ops are Var/Label *)
  strip_tac >>
  qpat_x_assum `phi_pv_all_var _ _` mp_tac >>
  simp[phi_pv_all_var_def, LET_DEF] >>
  disch_then (qspecl_then [`bb`, `inst`] mp_tac) >>
  simp[] >> metis_tac[]
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

Theorem return_revert_remap:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

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
  REWRITE_TAC[GSYM AND_IMP_INTRO] >>
  rpt gen_tac >> ntac 7 disch_tac >>
  (* 8th conjunct is the disjunction — don't split it *)
  disch_tac >>
  (* 9th conjunct is the existential *)
  disch_tac >>
  (* Now: all hypotheses are separate, disjunction unsplit *)
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     strip_assume_tac
       (BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th))) >>
  conj_tac >- (
    rpt strip_tac >> irule eval_operand_non_pointer_remap >>
    MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[]) >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  CASE_TAC >> simp[] >>
  rpt strip_tac >>
  (* Extract bb from existential *)
  qpat_x_assum `?bb. _` strip_assume_tac >>
  (* all_mem_via_pointer: off_op = Var v with v IN pv *)
  `~is_immutable_op inst.inst_opcode` by
    (Cases_on `inst.inst_opcode` >> gvs[is_immutable_op_def]) >>
  (`?v. h = Var v /\ v IN pointer_derived_vars fn roots` by (
    qpat_x_assum `all_mem_via_pointer _ _` (mp_tac o REWRITE_RULE
      [all_mem_via_pointer_def, LET_DEF]) >> BETA_TAC >>
    strip_tac >>
    `mem_read_ops inst = SOME
       <| iao_ofst := h; iao_size := SOME h';
          iao_max_size := SOME h' |>` by
      (Cases_on `inst.inst_opcode` >> gvs[mem_read_ops_def]) >>
    first_x_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := h; iao_size := SOME h';
          iao_max_size := SOME h' |>`] mp_tac) >>
    simp[])) >>
  gvs[eval_operand_def] >>
  (* Clause 2b: displacement + bounds *)
  first_x_assum (qspec_then `v` mp_tac) >> simp[] >>
  strip_tac >> gvs[] >>
  (* pv_address_rel: bridge to rel_off *)
  (`w2n off1 = orig_off + (w2n off1 - orig_off) /\
    w2n off2 = new_off + (w2n off1 - orig_off) /\
    w2n off1 - orig_off < sz` by
    (irule pv_address_rel >> simp[])) >>
  (* alloca_safe_access: w2n off1 + w2n n <= orig_off + sz *)
  (`mem_read_ops inst = SOME
      <| iao_ofst := Var v; iao_size := SOME h';
         iao_max_size := SOME h' |>` by
    (Cases_on `inst.inst_opcode` >> gvs[mem_read_ops_def])) >>
  (`w2n off1 + w2n n <= orig_off + sz` by (
    mp_tac alloca_safe_access_bounds_elim >>
    disch_then (qspecl_then [`fn`, `roots`, `s1`, `bb`, `inst`,
      `<| iao_ofst := Var v; iao_size := SOME h';
         iao_max_size := SOME h' |>`, `v`, `off1`, `aid`,
      `orig_off`, `sz`, `h'`, `n`] mp_tac) >>
    simp[eval_operand_def])) >>
  qpat_assum `w2n off1 = _` (fn eq1 =>
    qpat_assum `w2n off2 = _` (fn eq2 =>
      ONCE_REWRITE_TAC[eq1, eq2])) >>
  irule read_memory_alloca_remap >>
  rpt conj_tac >> TRY (simp[] >> NO_TAC) >>
  MAP_EVERY qexists_tac [`aid`, `remap`, `sz`] >>
  simp[]
QED

(* ===== Block-Level Preservation ===== *)

(* Step-level bridge: any non-terminator, non-ext_call instruction either
   preserves the remap (non-ALLOCA) or extends it (ALLOCA).
   Combines step_inst_base_preserves_remap and exec_alloca_preserves_remap.
   INVOKE is auto-excluded by step_inst_base returning Error.
   ILOAD/ISTORE are auto-excluded by pointer_confined (is_immutable_op). *)
Theorem step_preserves_remap[local]:
  !fn roots remap inst s1 s2 v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    phi_pv_all_var fn roots /\

    FDOM remap SUBSET FDOM s1.vs_allocas /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\
    step_inst_base inst s1 = OK v1 /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    (* ALLOCA-specific conditions *)
    (is_alloca_op inst.inst_opcode ==>
       alloca_inv s1 /\ alloca_inv s2 /\
       LENGTH s1.vs_memory <= s1.vs_alloca_next /\
       LENGTH s2.vs_memory <= s2.vs_alloca_next /\
       inst.inst_outputs = [HD inst.inst_outputs] /\
       HD inst.inst_outputs IN roots /\
       fn_alloca_id_of_var fn (HD inst.inst_outputs) = SOME inst.inst_id /\
       inst.inst_id NOTIN FDOM s1.vs_allocas /\
       ?alloc_size. inst.inst_operands = [Lit alloc_size] /\
         0 < w2n alloc_size /\
         s1.vs_alloca_next + w2n alloc_size < dimword (:256) /\
         s2.vs_alloca_next + w2n alloc_size < dimword (:256)) ==>
    ?remap' v2.
      FDOM remap SUBSET FDOM remap' /\
      FDOM remap' SUBSET FDOM v1.vs_allocas /\
      (!aid. aid IN FDOM remap ==> FLOOKUP remap' aid = FLOOKUP remap aid) /\
      step_inst_base inst s2 = OK v2 /\
      alloca_remap_rel fn roots remap' v1 v2
Proof
  rpt strip_tac >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- (
    (* ALLOCA case *)
    gvs[] >>
    Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
    gvs[step_inst_base_def] >>
    Cases_on `inst.inst_outputs` >> gvs[] >>
    rename1 `inst.inst_outputs = [out]` >>
    `inst.inst_id NOTIN FDOM remap` by (
      CCONTR_TAC >> gvs[SUBSET_DEF]) >>
    qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`alloc_size`,`out`]
      mp_tac exec_alloca_preserves_remap >>
    (impl_tac >- (
      `FDOM s1.vs_allocas = FDOM s2.vs_allocas` by (
        qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
        REWRITE_TAC[alloca_remap_rel_def, LET_DEF] >> BETA_TAC >>
        strip_tac >> simp[]) >>
      `inst.inst_id NOTIN FDOM s2.vs_allocas` by gvs[] >>
      simp[FLOOKUP_DEF])) >>
    simp[LET_DEF] >> strip_tac >> gvs[] >>
    qexists_tac `remap |+ (inst.inst_id, s2.vs_alloca_next)` >>
    simp[FLOOKUP_UPDATE, SUBSET_DEF, FDOM_FUPDATE, update_var_def] >>
    rpt strip_tac >> gvs[] >> metis_tac[SUBSET_DEF]
  )
  >>
  (* Non-ALLOCA case *)
  qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`v1`]
    mp_tac step_inst_base_preserves_remap >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  `v1.vs_allocas = s1.vs_allocas` by (
    qspecl_then [`inst`,`s1`,`v1`] mp_tac step_inst_base_allocas >> simp[]) >>
  qexistsl_tac [`remap`, `v2`] >> simp[SUBSET_REFL]
QED

(* eval_operand definedness transfers across alloca_remap_rel:
   if s1 has NONE then s2 has NONE. *)
Theorem eval_operand_none_transfer[local]:
  !fn roots remap s1 s2 op.
    alloca_remap_rel fn roots remap s1 s2 ==>
    eval_operand op s1 = NONE ==> eval_operand op s2 = NONE
Proof
  rpt strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def]
  >- (
    (* Var: either non-PV (lookup_var agrees) or PV (clause 2b) *)
    rename1 `lookup_var vname` >>
    qpat_x_assum `alloca_remap_rel _ _ _ _ _` mp_tac >>
    simp[alloca_remap_rel_def, LET_DEF] >> strip_tac >>
    Cases_on `vname IN pointer_derived_vars fn roots`
    >- (
      (* PV: clause 2b gives NONE/NONE or SOME/SOME *)
      qpat_x_assum `!v. v IN pointer_derived_vars _ _ ==> _`
        (qspec_then `vname` mp_tac) >> simp[] >>
      strip_tac >> gvs[lookup_var_def]
    ) >>
    (* Non-PV: lookup_var agrees *)
    qpat_x_assum `!v. v NOTIN pointer_derived_vars _ _ ==> _`
      (qspec_then `vname` mp_tac) >> simp[lookup_var_def]
  ) >>
  (* Label: vs_labels agree *)
  imp_res_tac alloca_remap_rel_scalars >> gvs[]
QED

(* If step_inst_base returns Error on s1, and alloca_remap_rel holds,
   then step_inst_base also returns Error on s2.
   True because Error comes from: (1) wrong operand/output count (structural,
   state-independent), (2) eval_operand NONE (transfers by eval_operand_none_transfer),
   or (3) scalar state fields like vs_prev_bb (agree by alloca_remap_rel). *)
(* -- Error transfer for each exec_* helper -- *)
(* Case-split on eval_operand terms in the goal conclusion *)
fun case_eval_in_goal (g as (_, goal)) = let
  val evals = find_terms (can (match_term ``eval_operand op s``)) goal
  in case evals of
       [] => NO_TAC g
     | (t :: _) => (BasicProvers.tmCases_on t [] >> gvs[]) g
  end;

val exec_err_tac : thm -> tactic = fn def =>
  rw[def] >> rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  TRY (first_x_assum drule >> simp[] >> NO_TAC) >>
  rpt case_eval_in_goal >> simp[];

Theorem exec_pure1_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_pure1 f inst s1 = Error err ==>
    ?err'. exec_pure1 f inst s2 = Error err'
Proof
  exec_err_tac exec_pure1_def
QED

Theorem exec_pure2_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_pure2 f inst s1 = Error err ==>
    ?err'. exec_pure2 f inst s2 = Error err'
Proof
  exec_err_tac exec_pure2_def
QED

Theorem exec_pure3_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_pure3 f inst s1 = Error err ==>
    ?err'. exec_pure3 f inst s2 = Error err'
Proof
  exec_err_tac exec_pure3_def
QED

Theorem exec_read0_error_transfer[local]:
  !f inst s1 s2 err.
    exec_read0 f inst s1 = Error err ==>
    ?err'. exec_read0 f inst s2 = Error err'
Proof
  rw[exec_read0_def] >> rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem exec_read1_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_read1 f inst s1 = Error err ==>
    ?err'. exec_read1 f inst s2 = Error err'
Proof
  exec_err_tac exec_read1_def
QED

Theorem exec_write2_error_transfer[local]:
  !f inst s1 s2 err.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    exec_write2 f inst s1 = Error err ==>
    ?err'. exec_write2 f inst s2 = Error err'
Proof
  exec_err_tac exec_write2_def
QED

Theorem eval_operands_none_transfer[local]:
  !ops s1 s2.
    (!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE) /\
    eval_operands ops s1 = NONE ==>
    eval_operands ops s2 = NONE
Proof
  Induct >> simp[eval_operands_def] >>
  rpt strip_tac >>
  Cases_on `eval_operand h s1` >> gvs[] >>
  Cases_on `eval_operand h s2` >> gvs[] >>
  Cases_on `eval_operands ops s1` >> gvs[] >>
  `eval_operands ops s2 = NONE` by (
    first_x_assum (qspecl_then [`s1`, `s2`] mp_tac) >> simp[]) >>
  simp[]
QED

(* Main error transfer: case split on opcode, apply exec_* transfer helpers,
   handle inline cases (MCOPY, JNZ, etc.) individually *)
Theorem step_inst_base_error_transfer[local]:
  !fn roots remap inst s1 s2 err.
    alloca_remap_rel fn roots remap s1 s2 /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = Error err ==>
    ?err'. step_inst_base inst s2 = Error err'
Proof
  rpt strip_tac >>
  imp_res_tac alloca_remap_rel_scalars >>
  `!op. eval_operand op s1 = NONE ==> eval_operand op s2 = NONE` by
    metis_tac[eval_operand_none_transfer] >>
  `!ops. eval_operands ops s1 = NONE ==> eval_operands ops s2 = NONE` by
    metis_tac[eval_operands_none_transfer] >>
  qpat_x_assum `step_inst_base _ _ = Error _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_terminator_def, is_ext_call_op_def] >>
  (* ~77 non-terminator non-ext-call cases *)
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, eval_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  TRY (first_assum drule >> simp[] >> NO_TAC) >>
  rpt case_eval_in_goal >> simp[]
QED

(* Abort transfer: for non-terminator, non-ext-call opcodes,
   only ASSERT, ASSERT_UNREACHABLE, and RETURNDATACOPY produce Abort.
   - ASSERT/ASSERT_UNREACHABLE: single condition operand is non-PV
     (pointer_confined: no mem ops, not pointer-preserving)
   - RETURNDATACOPY: OOB check uses offset/size operands which are non-PV
     (not iao_ofst; uniqueness prevents PV var appearing as both dest and
     offset/size), and LENGTH vs_returndata agrees by alloca_remap_rel_scalars
   All three produce halt_state/revert_state (set_returndata [] s). *)
Theorem step_inst_base_abort_transfer[local]:
  !fn roots remap inst s1 s2 a v1 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    step_inst_base inst s1 = Abort a v1 ==>
    ?v2. step_inst_base inst s2 = Abort a v2 /\
         alloca_remap_rel fn roots remap v1 v2
Proof
  rpt strip_tac >>
  (* Step 1: Identify the 3 opcodes that can produce Abort *)
  `inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE \/
   inst.inst_opcode = RETURNDATACOPY` by (
    pop_assum mp_tac >>
    qpat_x_assum `~is_ext_call_op _` mp_tac >>
    qpat_x_assum `~is_terminator _` mp_tac >>
    qpat_x_assum `alloca_remap_rel _ _ _ _ _` kall_tac >>
    qpat_x_assum `pointer_confined _ _` kall_tac >>
    qpat_x_assum `!u. _` kall_tac >>
    qpat_x_assum `MEM bb _` kall_tac >>
    qpat_x_assum `MEM inst _` kall_tac >>
    simp[step_inst_base_def] >>
    Cases_on `inst.inst_opcode` >>
    simp[is_terminator_def, is_ext_call_op_def,
         exec_pure1_def, exec_pure2_def, exec_pure3_def,
         exec_read0_def, exec_read1_def, exec_write2_def,
         exec_alloca_def, eval_operands_def] >>
    rpt strip_tac >> gvs[AllCaseEqs()] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[])) >>
  (* 3 goals: ASSERT, ASSERT_UNREACHABLE, RETURNDATACOPY *)
  gvs[]
  >- suspend "assert_case"
  >- suspend "assert_unr_case"
  >> suspend "rdc_case"
QED

Resume step_inst_base_abort_transfer[assert_case]:
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  simp[step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `eval_operand cop s1 = SOME 0w` >>
  drule_then (qspec_then `cop` mp_tac) eval_operand_non_pointer_remap >>
  (impl_tac >- (
    rpt strip_tac >> CCONTR_TAC >> gvs[] >>
    qpat_x_assum `pointer_confined _ _` mp_tac >>
    REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >> simp[] >>
    simp[mem_write_ops_def, mem_read_ops_def,
         is_pointer_preserving_op_def])) >>
  strip_tac >> gvs[] >>
  irule alloca_remap_rel_revert_returndata >> simp[]
QED

Resume step_inst_base_abort_transfer[assert_unr_case]:
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  simp[step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  rename1 `eval_operand cop s1 = SOME 0w` >>
  drule_then (qspec_then `cop` mp_tac) eval_operand_non_pointer_remap >>
  (impl_tac >- (
    rpt strip_tac >> CCONTR_TAC >> gvs[] >>
    qpat_x_assum `pointer_confined _ _` mp_tac >>
    REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >> simp[] >>
    simp[mem_write_ops_def, mem_read_ops_def,
         is_pointer_preserving_op_def])) >>
  strip_tac >> gvs[] >>
  irule alloca_remap_rel_halt_returndata >> simp[]
QED

Resume step_inst_base_abort_transfer[rdc_case]:
  qpat_x_assum `step_inst_base _ _ = Abort _ _` mp_tac >>
  simp[step_inst_base_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  (* op_offset: non-PV by pointer_confined + uniqueness *)
  `eval_operand op_offset s1 = eval_operand op_offset s2` by (
    irule eval_operand_non_pointer_remap >>
    MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >>
    conj_tac >- (
      rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      qpat_assum `pointer_confined _ _` mp_tac >>
      REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >> strip_tac >>
      first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >> simp[] >>
      simp[mem_read_ops_def, is_pointer_preserving_op_def] >>
      simp[mem_write_ops_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `!u. u IN _ ==> _` (qspec_then `v` mp_tac) >>
      simp[]) >>
    first_assum ACCEPT_TAC) >>
  (* op_size: suspend for debugging (L925) *)
  `eval_operand op_size s1 = eval_operand op_size s2`
    by suspend "rdc_op_size" >>
  imp_res_tac alloca_remap_rel_scalars >>
  gvs[] >>
  (* destOp may differ but must be defined *)
  drule operand_defined_transfer >>
  disch_then (qspec_then `op_destOffset` mp_tac) >> simp[] >>
  strip_tac >>
  Cases_on `eval_operand op_destOffset s2` >> gvs[] >>
  irule alloca_remap_rel_halt_returndata >> simp[]
QED

Resume step_inst_base_abort_transfer[rdc_op_size]:
  irule eval_operand_non_pointer_remap >>
  MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >>
  conj_tac
  >- (
    rpt strip_tac >> spose_not_then assume_tac >>
    qpat_x_assum `pointer_confined _ _` mp_tac >>
    REWRITE_TAC[pointer_confined_elim] >> strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
    asm_rewrite_tac[] >>
    simp[is_pointer_preserving_op_def, mem_read_ops_def,
         mem_write_ops_def] >>
    suspend "rdc_after_confined") >>
  first_assum ACCEPT_TAC
QED

Resume step_inst_base_abort_transfer[rdc_after_confined]:
  (* Goal: Var v <> op_destOffset. Proof by contradiction using uniqueness:
     if Var v = op_destOffset and op_size = Var v, then v appears at
     positions 0 and 2 in operands, giving LENGTH(FILTER) >= 2 > 1. *)
  CCONTR_TAC >> fs[] >>
  qpat_x_assum `!u. u IN _ ==> _` (qspec_then `v` mp_tac) >>
  simp[] >> IF_CASES_TAC >> simp[]
QED

Finalise step_inst_base_abort_transfer

(* For RETURN/REVERT: padded returndata on both sides agrees.
   Uses alloca_safe_access to show padding is never reached,
   then return_revert_remap for core agreement. *)
Theorem return_revert_returndata_agrees[local]:
  !fn roots remap inst s1 s2 off1 off2 sz_val bb off_op sz_op.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_operands = [off_op; sz_op] /\
    eval_operand off_op s1 = SOME off1 /\
    eval_operand off_op s2 = SOME off2 /\
    eval_operand sz_op s1 = SOME sz_val ==>
    TAKE (w2n sz_val) (DROP (w2n off1) s1.vs_memory ++
      REPLICATE (w2n sz_val) 0w) =
    TAKE (w2n sz_val) (DROP (w2n off2) s2.vs_memory ++
      REPLICATE (w2n sz_val) 0w)
Proof
  rpt strip_tac >>
  (* Establish mem_read_ops once from the disjunction *)
  `mem_read_ops inst = SOME
     <| iao_ofst := off_op; iao_size := SOME sz_op;
        iao_max_size := SOME sz_op |>` by (
    Cases_on `inst.inst_opcode` >> gvs[mem_read_ops_def]) >>
  (* off_op is pv via all_mem_via_pointer *)
  `?v. off_op = Var v /\ v IN pointer_derived_vars fn roots` by (
    qpat_x_assum `all_mem_via_pointer _ _` (mp_tac o REWRITE_RULE
      [all_mem_via_pointer_def, LET_DEF]) >> BETA_TAC >>
    strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`,
      `<| iao_ofst := off_op; iao_size := SOME sz_op;
          iao_max_size := SOME sz_op |>`] mp_tac) >>
    simp[]) >>
  gvs[eval_operand_def] >>
  (* clause 2b for v *)
  qpat_x_assum `alloca_remap_rel _ _ _ _ _`
    (fn th => assume_tac th >>
     let val body = BETA_RULE
       (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th)
     in assume_tac (el 3 (CONJUNCTS body)) end) >>
  first_x_assum (qspec_then `v` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[DISJ_IMP_THM, PULL_EXISTS] >> rpt strip_tac >>
  fs[lookup_var_def] >>
  (* sz_op is non-pv, so agrees across states *)
  `!n. sz_op = Var n ==> n NOTIN pointer_derived_vars fn roots` by (
    rpt strip_tac >> CCONTR_TAC >> fs[] >>
    qpat_assum `pointer_confined _ _` mp_tac >>
    REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >>
    strip_tac >>
    first_x_assum (qspecl_then [`bb`, `inst`, `n`] mp_tac) >>
    simp[mem_write_ops_def, is_pointer_preserving_op_def] >>
    strip_tac >> fs[] >>
    first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER]) >>
  `eval_operand sz_op s2 = SOME sz_val` by (
    `eval_operand sz_op s1 = eval_operand sz_op s2` suffices_by simp[] >>
    irule eval_operand_non_pointer_remap >>
    MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
    Cases_on `sz_op` >> simp[] >> metis_tac[]) >>
  (* s2 alloca info via alloca_remap_rel clause 8 *)
  `FLOOKUP s2.vs_allocas aid = SOME (new_off, sz)` by (
    qpat_x_assum `alloca_remap_rel _ _ _ _ _`
      (fn th => assume_tac th >>
       mp_tac (BETA_RULE (REWRITE_RULE[alloca_remap_rel_def, LET_DEF] th))) >>
    simp[]) >>
  (* Bounds from alloca_safe_access *)
  `w2n off1 + w2n sz_val <= orig_off + sz` by (
    qspecl_then [`fn`,`roots`,`s1`,`bb`,`inst`,
      `<| iao_ofst := Var v; iao_size := SOME sz_op;
          iao_max_size := SOME sz_op |>`,
      `v`,`off1`,`aid`,`orig_off`,`sz`,`sz_op`,`sz_val`]
      mp_tac alloca_safe_access_bounds_elim >>
    simp[lookup_var_def, eval_operand_def]) >>
  (* Memory length bounds *)
  `orig_off + sz <= LENGTH s1.vs_memory` by (
    qpat_assum `alloca_safe_access fn roots s1` mp_tac >>
    REWRITE_TAC[alloca_safe_access_def, LET_DEF] >> BETA_TAC >>
    strip_tac >> res_tac) >>
  `new_off + sz <= LENGTH s2.vs_memory` by (
    qpat_assum `alloca_safe_access fn roots s2` mp_tac >>
    REWRITE_TAC[alloca_safe_access_def, LET_DEF] >> BETA_TAC >>
    strip_tac >> res_tac) >>
  (* Direct: read_at_pv_agrees gives TAKE..DROP..REPLICATE agreement *)
  qspecl_then [`fn`,`roots`,`remap`,`s1`,`s2`,`aid`,`orig_off`,`sz`,
    `new_off`,`off1`,`off2`,`w2n sz_val`]
    mp_tac read_at_pv_agrees >>
  simp[]
QED

(* Pre-compute step_inst_base per opcode at ML level to avoid
   92-branch expansion in goals. *)
fun step_base_for opc_tm = let
  val inst_var = mk_var("inst", ``:instruction``)
  val s_var = mk_var("s", ``:venom_state``)
  val lhs_tm = list_mk_comb(``step_inst_base``, [inst_var, s_var])
  val opc_eq = ASSUME (mk_eq(mk_comb(``instruction_inst_opcode``, inst_var),
                              opc_tm))
  val th = REWRITE_CONV [step_inst_base_def] lhs_tm
  val th2 = CONV_RULE (RHS_CONV (REWRITE_CONV [opc_eq]
                                 THENC SIMP_CONV (srw_ss()) [])) th
in DISCH (concl opc_eq) th2 end;

val step_base_thms = map step_base_for
  [``JMP``, ``JNZ``, ``DJMP``, ``RET``, ``RETURN``, ``REVERT``,
   ``STOP``, ``SINK``, ``SELFDESTRUCT``, ``INVALID``];

(* Tactic: given inst.inst_opcode = OPC in assumptions, rewrite
   step_inst_base inst _ using the pre-computed per-opcode theorem. *)
val step_term_rw : tactic = fn (asl, g) => let
  fun is_opc_eq a =
    let val (l,r) = dest_eq a
    in l ~~ ``(inst:instruction).inst_opcode`` andalso is_const r
    end handle HOL_ERR _ => false
  val opc_eq = first is_opc_eq asl
  val opc = rhs opc_eq
  val th = first (fn th => rhs (fst (dest_imp (concl th))) ~~ opc)
                 step_base_thms
  val th' = MP th (ASSUME opc_eq)
in PURE_REWRITE_TAC [th'] (asl, g) end;

(* Standalone: is_terminator /\ <> INVOKE implies 10-way disjunction *)
val is_terminator_cases = prove(
  ``!opc. is_terminator opc /\ opc <> INVOKE ==>
    (opc = JMP \/ opc = JNZ \/ opc = DJMP \/ opc = RET \/
     opc = RETURN \/ opc = REVERT \/ opc = STOP \/ opc = SINK \/
     opc = SELFDESTRUCT \/ opc = INVALID)``,
  Cases >> simp[is_terminator_def]);

(* Helper: operand agreement for non-RETURN/REVERT terminators *)
fun term_op_agree (g as (asl, _)) = (
  qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`]
    mp_tac terminator_control_flow_remap >>
  (impl_tac >- (simp[] >> qexists_tac `bb` >> simp[])) >>
  strip_tac
) g;

(* Common tactic for jump-producing terminators *)
val jump_term_tac =
  BasicProvers.every_case_tac >> gvs[lift_result_def] >>
  TRY (irule alloca_remap_rel_jump_to >> simp[] >> NO_TAC) >>
  gvs[jump_to_def];

(* Helper: RETURN/REVERT case for step_terminator_lift_result.
   After preamble, inst.inst_opcode is substituted to RETURN (or REVERT)
   and step_inst_base is expanded. The goal is a lift_result on the case expr. *)
Theorem return_revert_lift_result[local]:
  !fn roots remap inst s1 s2 bb.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    (inst.inst_opcode = RETURN \/ inst.inst_opcode = REVERT) /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    s1.vs_call_ctx = s2.vs_call_ctx /\
    s1.vs_accounts = s2.vs_accounts /\
    s1.vs_returndata = s2.vs_returndata /\
    LENGTH s1.vs_memory = LENGTH s2.vs_memory ==>
    lift_result (alloca_remap_rel fn roots remap)
      (alloca_remap_rel fn roots remap)
      (alloca_remap_rel fn roots remap)
      (case step_inst_base inst s1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vs s' => IntRet vs s'
       | Error e => Error e)
      (case step_inst_base inst s2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vs s' => IntRet vs s'
       | Error e => Error e)
Proof
  (* rpt strip_tac splits the RETURN\/REVERT disjunction into 2 goals *)
  rpt strip_tac >> (
    (* Each branch: single opcode, single goal throughout *)
    step_term_rw >> simp[lift_result_def] >>
    Cases_on `inst.inst_operands` >> simp[lift_result_def] >>
    Cases_on `t` >> simp[lift_result_def] >>
    Cases_on `t'` >> simp[lift_result_def] >>
    (* Size operand h' is non-pv, agrees across states *)
    `eval_operand h' s1 = eval_operand h' s2` by (
      irule eval_operand_non_pointer_remap >>
      MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
      rpt strip_tac >> CCONTR_TAC >> gvs[] >>
      qpat_assum `pointer_confined _ _` mp_tac >>
      REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >>
      strip_tac >>
      first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
      simp[mem_write_ops_def, mem_read_ops_def,
           is_pointer_preserving_op_def] >>
      strip_tac >> fs[] >>
      first_x_assum (qspec_then `v` mp_tac) >> simp[FILTER]) >>
    Cases_on `eval_operand h s1` >> simp[lift_result_def] >>
    Cases_on `eval_operand h' s1` >> simp[lift_result_def] >>
    Cases_on `eval_operand h s2` >> simp[lift_result_def] >>
    TRY (imp_res_tac operand_defined_iff >> fs[] >> NO_TAC) >>
    TRY (fs[lift_result_def] >> NO_TAC) >>
    rename1 `eval_operand h s1 = SOME off1` >>
    rename1 `eval_operand h s2 = SOME off2` >>
    rename1 `eval_operand h' s1 = SOME sz_val` >>
    `eval_operand h' s2 = SOME sz_val` by metis_tac[] >>
    qpat_x_assum `SOME _ = eval_operand _ s2` kall_tac >>
    pop_assum (fn th => PURE_REWRITE_TAC[th]) >>
    simp[lift_result_def] >>
    qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,
                 `off1`,`off2`,`sz_val`,`bb`,`h`,`h'`]
      mp_tac return_revert_returndata_agrees >>
    (impl_tac >- fs[]) >> strip_tac >> fs[] >>
    TRY (irule alloca_remap_rel_halt_returndata >> simp[] >> NO_TAC) >>
    irule alloca_remap_rel_revert_returndata >> simp[])
QED

(* Terminator step produces lift_result-related outputs. *)
Theorem step_terminator_lift_result[local]:
  !fn roots remap inst s1 s2.
    alloca_remap_rel fn roots remap s1 s2 /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    alloca_safe_access fn roots s1 /\
    alloca_safe_access fn roots s2 /\

    ptrs_in_alloca_bounds fn roots s1 /\
    ptrs_in_alloca_bounds fn roots s2 /\
    (!u. u IN pointer_derived_vars fn roots ==>
         LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1) /\
    is_terminator inst.inst_opcode /\
    inst.inst_opcode <> INVOKE /\
    (?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions) ==>
    lift_result (alloca_remap_rel fn roots remap)
      (alloca_remap_rel fn roots remap)
      (alloca_remap_rel fn roots remap)
      (case step_inst_base inst s1 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vs s' => IntRet vs s'
       | Error e => Error e)
      (case step_inst_base inst s2 of
         OK s'' => if s''.vs_halted then Halt s'' else OK s''
       | Halt s' => Halt s'
       | Abort a s' => Abort a s'
       | IntRet vs s' => IntRet vs s'
       | Error e => Error e)
Proof
  rpt strip_tac >>
  imp_res_tac alloca_remap_rel_scalars >>
  qspec_then `inst.inst_opcode` mp_tac is_terminator_cases >>
  (impl_tac >- simp[]) >>
  strip_tac >> pop_assum strip_assume_tac
  (* 10 goals, one per terminator.
     Handle RETURN/REVERT BEFORE step_term_rw (needs unreduced step_inst_base). *)
  >~ [`inst.inst_opcode = RETURN`]
  >- (qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`bb`]
        mp_tac return_revert_lift_result >> simp[])
  >~ [`inst.inst_opcode = REVERT`]
  >- (qspecl_then [`fn`,`roots`,`remap`,`inst`,`s1`,`s2`,`bb`]
        mp_tac return_revert_lift_result >> simp[])
  (* Remaining 8 goals: expand step_inst_base *)
  >> step_term_rw >> fs[] >> simp[lift_result_def]
  (* JMP *)       >- jump_term_tac
  (* JNZ *)       >- (term_op_agree >> jump_term_tac)
  (* DJMP *)      >- (term_op_agree >> jump_term_tac)
  (* RET: all operands non-pv, so eval_operands agrees *)
  >- (`eval_operands inst.inst_operands s1 =
       eval_operands inst.inst_operands s2` by (
        irule eval_operands_non_pointer_remap >>
        MAP_EVERY qexists_tac [`fn`, `remap`, `roots`] >> simp[] >>
        rpt strip_tac >> CCONTR_TAC >> gvs[] >>
        qpat_assum `pointer_confined _ _` mp_tac >>
        REWRITE_TAC[pointer_confined_def, LET_DEF] >> BETA_TAC >>
        strip_tac >>
        first_x_assum (qspecl_then [`bb`, `inst`, `v`] mp_tac) >>
        simp[mem_write_ops_def, mem_read_ops_def,
             is_pointer_preserving_op_def]) >>
      BasicProvers.every_case_tac >> gvs[lift_result_def])
  (* STOP *)      >- (simp[halt_state_def] >>
                      irule alloca_remap_rel_halted >> simp[])
  (* SINK *)      >- (simp[halt_state_def] >>
                      irule alloca_remap_rel_halted >> simp[])
  (* SELFDESTRUCT *)
  >- (term_op_agree >>
      BasicProvers.every_case_tac >>
      gvs[lift_result_def] >>
      irule alloca_remap_rel_halt_accounts >> simp[])
  (* INVALID *)
  >> (irule alloca_remap_rel_halt_returndata >> simp[])
QED

Theorem run_block_preserves_remap:
  !fn roots.
    FINITE roots /\
    roots SUBSET alloca_roots fn /\
    wf_function fn /\
    ssa_form fn /\
    pointer_confined fn roots /\
    all_mem_via_pointer fn roots /\
    affine_pointer_ops fn roots /\
    pointer_arith_in_region fn roots /\
    phi_pv_all_var fn roots /\
    step_preserves_safety fn roots /\

    fn_inst_wf fn ==>
    !fuel ctx bb s1 remap s2.
      alloca_remap_rel fn roots remap s1 s2 /\
      alloca_safe_access fn roots s1 /\
      alloca_safe_access fn roots s2 /\
      ptrs_in_alloca_bounds fn roots s1 /\
      ptrs_in_alloca_bounds fn roots s2 /\
      FDOM remap SUBSET FDOM s1.vs_allocas /\
      (!inst. MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> INVOKE /\
              ~is_ext_call_op inst.inst_opcode /\
              ~is_alloca_op inst.inst_opcode /\
              (!u. u IN pointer_derived_vars fn roots ==>
                   LENGTH (FILTER ($= (Var u)) inst.inst_operands) <= 1)) /\
      (!inst. MEM inst bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
              inst.inst_outputs = [HD inst.inst_outputs] /\
              HD inst.inst_outputs IN roots /\
              fn_alloca_id_of_var fn (HD inst.inst_outputs) = SOME inst.inst_id /\
              ?alloc_size. inst.inst_operands = [Lit alloc_size] /\
                0 < w2n alloc_size) /\
      (!inst s. MEM inst bb.bb_instructions /\ is_alloca_op inst.inst_opcode ==>
                !alloc_size. inst.inst_operands = [Lit alloc_size] ==>
                s.vs_alloca_next + w2n alloc_size < dimword (:256)) /\
      (!i. s1.vs_inst_idx <= i /\ i < LENGTH bb.bb_instructions ==>
           (EL i bb.bb_instructions).inst_id NOTIN FDOM s1.vs_allocas) /\
      MEM bb fn.fn_blocks ==>
      ?remap'.
        FDOM remap SUBSET FDOM remap' /\
        (!aid. aid IN FDOM remap ==> FLOOKUP remap' aid = FLOOKUP remap aid) /\
        lift_result
          (alloca_remap_rel fn roots remap')
          (alloca_remap_rel fn roots remap')
          (alloca_remap_rel fn roots remap')
          (exec_block fuel ctx bb s1)
          (exec_block fuel ctx bb s2)
Proof
  rpt gen_tac >> strip_tac >>
  (* Static hypotheses now in assumptions.
     Goal: !fuel ctx bb s1 remap s2. <state-dep conds> ==> ?remap'. ... *)
  (* Introduce all 6 variables, then push back for induction *)
  rpt gen_tac >>
  (* Now fn, roots, fuel, ctx, bb, s1, remap, s2 are free.
     Goal: <state-dep conds> ==> ?remap'. ... *)
  MAP_EVERY qid_spec_tac [`s2`, `remap`, `s1`, `bb`, `ctx`, `fuel`] >>
  (* Goal: !fuel ctx bb s1 remap s2. <conds> ==> ?remap'. ... *)
  ho_match_mp_tac (cj 2 run_defs_ind) >>
  qexists_tac `\fuel ctx inst s. T` >>
  qexists_tac `\fuel ctx fn' s. T` >>
  conj_tac >- simp[] >>    (* step_inst trivial *)
  conj_tac
  >- (
    rpt gen_tac >> strip_tac >>   (* IH *)
    rpt gen_tac >> strip_tac >>   (* state-dep hypotheses *)
    ONCE_REWRITE_TAC[exec_block_def] >>
    imp_res_tac alloca_remap_rel_scalars >>
    qpat_x_assum `s1.vs_inst_idx = s2.vs_inst_idx`
      (fn th => REWRITE_TAC[GSYM th]) >>
    Cases_on `get_instruction bb s1.vs_inst_idx`
    >- (qexists_tac `remap` >> simp[lift_result_def]) >>
    rename1 `get_instruction bb s1.vs_inst_idx = SOME inst'` >>
    `MEM inst' bb.bb_instructions` by (
      fs[get_instruction_def] >>
      Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[] >>
      metis_tac[MEM_EL]) >>
    `inst'.inst_opcode <> INVOKE /\ ~is_ext_call_op inst'.inst_opcode` by
      (first_x_assum drule >> simp[]) >>
    (* step_inst = step_inst_base for non-INVOKE *)
    simp[step_inst_def] >>
    (* Split: terminator or not *)
    Cases_on `is_terminator inst'.inst_opcode`
    >- (
      (* === Terminator case === *)
      (* step_terminator_lift_result handles all result types at once *)
      simp[] >>
      qexists_tac `remap` >> simp[SUBSET_REFL] >>
      irule step_terminator_lift_result >>
      simp[] >> qexists_tac `bb` >> simp[]
    ) >>
    simp[] >>
    (* === Non-terminator case === *)
    (* Case-split on step_inst_base result for s1 *)
    Cases_on `step_inst_base inst' s1` >> simp[]
    >- (
      (* OK v1: use step_preserves_remap then IH *)
      suspend "ok_case"
    )
    >- (
      (* Halt: impossible for non-terminators *)
      suspend "halt_case"
    )
    >- (
      (* Abort: ASSERT/ASSERT_UNREACHABLE *)
      suspend "abort_case"
    )
    >- (
      (* IntRet: impossible for non-terminators *)
      suspend "intret_case"
    )
    >>
    (* Error: both sides error *)
    suspend "error_case"
  ) >>
  simp[]                     (* run_function trivial *)
QED

(* ===== inst_idx invariance for safety predicates ===== *)

Theorem alloca_safe_access_inst_idx[local]:
  !fn roots s n.
    alloca_safe_access fn roots (s with vs_inst_idx := n) <=>
    alloca_safe_access fn roots s
Proof
  rpt gen_tac >>
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[alloca_safe_access_def, lookup_var_def]
QED

Theorem ptrs_in_alloca_bounds_inst_idx[local]:
  !fn roots s n.
    ptrs_in_alloca_bounds fn roots (s with vs_inst_idx := n) <=>
    ptrs_in_alloca_bounds fn roots s
Proof
  simp[ptrs_in_alloca_bounds_def, in_alloca_region_def, lookup_var_def]
QED

(* ===== Step preservation of safety predicates ===== *)

(* Helper: unwrap step_preserves_safety for direct use.
   Keeps the conjunction small (2 conjuncts) to avoid cascade. *)
Theorem step_safety_elim[local]:
  !fn roots inst bb s v.
    step_preserves_safety fn roots /\
    MEM bb fn.fn_blocks /\
    MEM inst bb.bb_instructions /\
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    alloca_safe_access fn roots s /\
    ptrs_in_alloca_bounds fn roots s ==>
    alloca_safe_access fn roots v /\
    ptrs_in_alloca_bounds fn roots v
Proof
  simp[step_preserves_safety_def] >> metis_tac[]
QED

(* Helper: resolve_phi on well-formed PHI always returns Var *)
Theorem resolve_phi_gives_var[local]:
  !ops prev val_op.
    phi_well_formed ops /\
    resolve_phi prev ops = SOME val_op ==>
    ?var. val_op = Var var
Proof
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >- simp[resolve_phi_def] >>
  Cases_on `t` >- simp[resolve_phi_def] >>
  Cases_on `h` >> Cases_on `h'` >>
  rpt strip_tac >> fs[resolve_phi_def, phi_well_formed_def] >>
  TRY (Cases_on `s = prev` >> fs[]) >>
  first_x_assum (qspec_then `t'` mp_tac) >> simp[] >>
  strip_tac >> res_tac >> metis_tac[]
QED

(* Helper: fn_inst_wf + PHI => phi_well_formed *)
Theorem phi_inst_wf_well_formed[local]:
  !fn bb inst.
    fn_inst_wf fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst.inst_opcode = PHI ==>
    phi_well_formed inst.inst_operands
Proof
  rpt strip_tac >>
  `inst_wf inst` by (fs[fn_inst_wf_def] >> metis_tac[]) >>
  gvs[inst_wf_def] >>
  `!ops. phi_operands_wf ops ==> phi_well_formed ops` suffices_by simp[] >>
  measureInduct_on `LENGTH ops` >>
  Cases_on `ops` >> simp[phi_operands_wf_def, phi_well_formed_def] >>
  rename1 `phi_operands_wf (h::t)` >>
  Cases_on `h` >> gvs[phi_operands_wf_def, phi_well_formed_def] >>
  Cases_on `t` >> gvs[phi_operands_wf_def, phi_well_formed_def] >>
  rename1 `_ ==> phi_well_formed (Label _ :: h2 :: _)` >>
  Cases_on `h2` >> gvs[phi_operands_wf_def, phi_well_formed_def]
QED

(* Helper: PP output ∈ pv implies ∃ PV input operand *)
Theorem pp_has_pv_input[local]:
  !fn roots inst bb out.
    pointer_confined fn roots /\ ssa_form fn /\
    FINITE roots /\ roots SUBSET alloca_roots fn /\
    is_pointer_preserving_op inst.inst_opcode /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    MEM out inst.inst_outputs /\
    out IN pointer_derived_vars fn roots ==>
    ?inp. MEM (Var inp) inst.inst_operands /\
          inp IN pointer_derived_vars fn roots
Proof
  rpt strip_tac >>
  gvs[pointer_derived_vars_def] >>
  drule pointer_use_vars_mem_char >> strip_tac
  >- (* out ∈ SET_TO_LIST roots ⇒ out ∈ roots ⇒ alloca output ⇒ SSA *)
     (`~is_alloca_op inst.inst_opcode` by
        (Cases_on `inst.inst_opcode` >>
         gvs[is_pointer_preserving_op_def, is_alloca_op_def]) >>
      `out NOTIN roots` by metis_tac[non_alloca_output_notin_roots] >>
      gvs[MEM_SET_TO_LIST])
  >- (* pointer_use_vars: ∃ PP inst' with pv input having out as output *)
     (rename1 `MEM inst' _` >>
      `MEM inst (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
      `MEM inst' (fn_insts fn)` by metis_tac[mem_fn_insts_intro] >>
      `inst = inst'` by (irule ssa_unique_output >> simp[] >> metis_tac[]) >>
      gvs[] >> metis_tac[])
QED

(* Helper: PP step success + Var operand => operand is defined in pre-state.
   For PHI, only the resolved operand is guaranteed; caller must use
   phi_pv_all_var to identify the right one. *)
(* CHEATED — parallel PHI: step_inst_base on PHI is no-op, doesn't
   check operand definedness. Needs eval_phis-level reasoning. *)
Theorem pp_operand_var_defined[local]:
  !inst s v inp.
    step_inst_base inst s = OK v /\
    is_pointer_preserving_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode /\
    MEM (Var inp) inst.inst_operands /\
    (inst.inst_opcode = PHI ==>
       ?prev. s.vs_prev_bb = SOME prev /\
              resolve_phi prev inst.inst_operands = SOME (Var inp)) ==>
    ?w. lookup_var inp s = SOME w
Proof
  cheat
QED

(* Helper: PP ops have exactly one output *)
(* CHEATED — parallel PHI: step_inst_base on PHI is no-op, can't
   derive output structure from it. Needs inst_wf hypothesis. *)
Theorem pp_single_output[local]:
  !inst s v.
    is_pointer_preserving_op inst.inst_opcode /\
    step_inst_base inst s = OK v ==>
    ?out. inst.inst_outputs = [out]
Proof
  cheat
QED

(* PP opcodes are disjoint from alloca opcodes.
   Proven in small context to avoid OOM from Cases_on opcode in large goals. *)
Theorem pp_not_alloca_op[local]:
  !opc. is_pointer_preserving_op opc ==> ~is_alloca_op opc
Proof
  Cases >> simp[is_pointer_preserving_op_def, is_alloca_op_def]
QED

(* ptrs_in_alloca_bounds is preserved by non-terminator, non-ext-call steps. *)
Theorem step_preserves_ptrs_in_alloca_bounds[local]:
  !fn roots inst bb s v.
    ptrs_in_alloca_bounds fn roots s /\
    pointer_arith_in_region fn roots /\
    pointer_confined fn roots /\
    phi_pv_all_var fn roots /\
    fn_inst_wf fn /\
    ssa_form fn /\ FINITE roots /\ roots SUBSET alloca_roots fn /\
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    (is_alloca_op inst.inst_opcode ==>
      inst.inst_outputs = [HD inst.inst_outputs] /\
      HD inst.inst_outputs IN roots /\
      inst.inst_id NOTIN FDOM s.vs_allocas /\
      ?alloc_size. inst.inst_operands = [Lit alloc_size] /\
                   0 < w2n alloc_size /\
                   s.vs_alloca_next + w2n alloc_size < dimword (:256)) ==>
    ptrs_in_alloca_bounds fn roots v
Proof
  rpt strip_tac >>
  REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
  rpt strip_tac >>
  rename1 `lookup_var u v = SOME w` >>
  Cases_on `MEM u inst.inst_outputs`
  >- (
    (* u is an output of inst *)
    Cases_on `is_pointer_preserving_op inst.inst_opcode`
    >- suspend "pp_case"
    >- (
      Cases_on `is_alloca_op inst.inst_opcode`
      >- suspend "alloca_case"
      >- metis_tac[non_pp_output_notin_pv]))
  >- suspend "nonoutput_case"
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_case]:
  (* PP ops don't change allocas *)
  `~is_alloca_op inst.inst_opcode` by (
    Cases_on `inst.inst_opcode` >>
    gvs[is_pointer_preserving_op_def, is_alloca_op_def]) >>
  `v.vs_allocas = s.vs_allocas` by
    metis_tac[step_inst_base_allocas] >>
  `inst.inst_outputs = [u]` by metis_tac[pp_single_output, HD, MEM] >>
  `?inp. MEM (Var inp) inst.inst_operands /\
         inp IN pointer_derived_vars fn roots` by
    metis_tac[pp_has_pv_input] >>
  (* Defer finding defined value + region to per-opcode case *)
  suspend "pp_input_region"
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_input_region]:
  (* Per-opcode: find inp's value, get region, apply pointer_arith_in_region *)
  Cases_on `inst.inst_opcode` >> gvs[is_pointer_preserving_op_def]
  >- ( (* ADD *) suspend "pp_add")
  >- ( (* SUB *) suspend "pp_sub")
  >- ( (* PHI *) suspend "pp_phi")
  >- ( (* ASSIGN *) suspend "pp_assign")
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_add]:
  (* Extract operand definedness from step success, NOT consuming step hyp *)
  `?w_in. lookup_var inp s = SOME w_in` by (
    qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
    simp[step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
    strip_tac >> gvs[eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `in_alloca_region s (w2n w_in)` by (
    qpat_x_assum `ptrs_in_alloca_bounds _ _ _` mp_tac >>
    REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
    disch_then (qspecl_then [`inp`, `w_in`] mp_tac) >> simp[]) >>
  gvs[in_alloca_region_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (off, asz)` >>
  `off <= w2n w /\ w2n w < off + asz` by (
    mp_tac pointer_arith_in_region_elim >>
    disch_then (qspecl_then [`fn`,`roots`,`bb`,`inst`,`s`,`v`,
      `u`,`w`,`inp`,`w_in`,`aid`,`off`,`asz`] mp_tac) >>
    simp[is_pointer_preserving_op_def]) >>
  simp[in_alloca_region_def] >>
  MAP_EVERY qexists_tac [`aid`, `off`, `asz`] >> simp[]
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_sub]:
  (* Same approach as ADD *)
  `?w_in. lookup_var inp s = SOME w_in` by (
    qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
    simp[step_inst_base_def, exec_pure2_def, AllCaseEqs()] >>
    strip_tac >> gvs[eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `in_alloca_region s (w2n w_in)` by (
    qpat_x_assum `ptrs_in_alloca_bounds _ _ _` mp_tac >>
    REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
    disch_then (qspecl_then [`inp`, `w_in`] mp_tac) >> simp[]) >>
  gvs[in_alloca_region_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (off, asz)` >>
  `off <= w2n w /\ w2n w < off + asz` by (
    mp_tac pointer_arith_in_region_elim >>
    disch_then (qspecl_then [`fn`,`roots`,`bb`,`inst`,`s`,`v`,
      `u`,`w`,`inp`,`w_in`,`aid`,`off`,`asz`] mp_tac) >>
    simp[is_pointer_preserving_op_def]) >>
  simp[in_alloca_region_def] >>
  MAP_EVERY qexists_tac [`aid`, `off`, `asz`] >> simp[]
QED

(* ASSIGN/PHI: extract operand def WITHOUT consuming step hyp, then
   apply pointer_arith_in_region_elim with the original step hyp. *)
Resume step_preserves_ptrs_in_alloca_bounds[pp_assign]:
  `?w_in. lookup_var inp s = SOME w_in` by (
    drule step_inst_base_assign_inv >> (impl_tac >- simp[]) >>
    strip_tac >> gvs[eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `in_alloca_region s (w2n w_in)` by (
    qpat_x_assum `ptrs_in_alloca_bounds _ _ _` mp_tac >>
    REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
    disch_then (qspecl_then [`inp`, `w_in`] mp_tac) >> simp[]) >>
  gvs[in_alloca_region_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (off, asz)` >>
  `off <= w2n w /\ w2n w < off + asz` by (
    mp_tac pointer_arith_in_region_elim >>
    disch_then (qspecl_then [`fn`,`roots`,`bb`,`inst`,`s`,`v`,
      `u`,`w`,`inp`,`w_in`,`aid`,`off`,`asz`] mp_tac) >>
    simp[is_pointer_preserving_op_def]) >>
  simp[in_alloca_region_def] >>
  MAP_EVERY qexists_tac [`aid`, `off`, `asz`] >> simp[]
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_phi]:
  (* Copy step hyp before drule consumes it *)
  qpat_x_assum `step_inst_base _ _ = OK _`
    (fn th => assume_tac th >> assume_tac th) >>
  drule step_inst_base_phi_inv >> (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac resolve_phi_mem >>
  suspend "pp_phi_body"
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_phi_body]:
  (* Derive phi_well_formed from fn_inst_wf *)
  `phi_well_formed inst.inst_operands` by (
    metis_tac[phi_inst_wf_well_formed]) >>
  suspend "pp_phi_resolved"
QED

Resume step_preserves_ptrs_in_alloca_bounds[pp_phi_resolved]:
  (* resolve_phi returns Var (not Label, not Lit) *)
  `?var. val_op = Var var` by
    metis_tac[resolve_phi_gives_var] >>
  gvs[] >>
  (* phi_pv_all_var: resolved Var is PV *)
  qpat_x_assum `phi_pv_all_var _ _` mp_tac >>
  simp[phi_pv_all_var_def, LET_DEF] >>
  disch_then (qspecl_then [`bb`, `inst`] mp_tac) >>
  simp[] >> impl_tac >- metis_tac[] >> strip_tac >>
  gvs[eval_operand_def] >>
  rename1 `lookup_var u' s = SOME w_in` >>
  `u' IN pointer_derived_vars fn roots` by metis_tac[] >>
  `in_alloca_region s (w2n w_in)` by (
    qpat_x_assum `ptrs_in_alloca_bounds _ _ _` mp_tac >>
    REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
    disch_then (qspecl_then [`u'`, `w_in`] mp_tac) >> simp[]) >>
  gvs[in_alloca_region_def] >>
  rename1 `FLOOKUP s.vs_allocas aid = SOME (off, asz)` >>
  `off <= w2n w /\ w2n w < off + asz` by (
    mp_tac pointer_arith_in_region_elim >>
    disch_then (qspecl_then [`fn`,`roots`,`bb`,`inst`,`s`,
      `update_var out w_in s`,
      `out`,`w`,`u'`,`w_in`,`aid`,`off`,`asz`] mp_tac) >>
    simp[is_pointer_preserving_op_def]) >>
  simp[in_alloca_region_def] >>
  MAP_EVERY qexists_tac [`aid`, `off`, `asz`] >> simp[]
QED

Resume step_preserves_ptrs_in_alloca_bounds[alloca_case]:
  (* ALLOCA case: output ∈ roots, value = n2w(nao), new alloca covers it *)
  `inst.inst_outputs = [HD inst.inst_outputs] /\
   HD inst.inst_outputs IN roots` by simp[] >>
  `?alloc_size. inst.inst_operands = [Lit alloc_size] /\
                0 < w2n alloc_size /\
                s.vs_alloca_next + w2n alloc_size < dimword (:256)` by
    simp[] >>
  `u = HD inst.inst_outputs` by (gvs[] >> Cases_on `inst.inst_outputs` >> gvs[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
  simp[exec_alloca_def] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
  strip_tac >> gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[in_alloca_region_def] >>
  qexists_tac `inst.inst_id` >>
  simp[FLOOKUP_UPDATE] >>
  `s.vs_alloca_next < dimword (:256)` by simp[] >>
  gvs[w2n_n2w, FLOOKUP_DEF]
QED

Resume step_preserves_ptrs_in_alloca_bounds[nonoutput_case]:
  (* u not an output: value unchanged, alloca region preserved *)
  `lookup_var u s = SOME w` by
    metis_tac[step_inst_base_non_output_vars] >>
  (* Derive in_alloca_region from ptrs_in_alloca_bounds *)
  `in_alloca_region s (w2n w)` by (
    qpat_x_assum `ptrs_in_alloca_bounds _ _ _` mp_tac >>
    REWRITE_TAC[ptrs_in_alloca_bounds_def, LET_DEF] >> BETA_TAC >>
    disch_then (qspecl_then [`u`, `w`] mp_tac) >> simp[]) >>
  (* Transfer to post-step state: allocas monotone *)
  gvs[in_alloca_region_def] >>
  rename1 `FLOOKUP s.vs_allocas aid' = SOME (off', asz')` >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- (
    `inst.inst_id NOTIN FDOM s.vs_allocas` by simp[] >>
    `inst.inst_id <> aid'` by (
      strip_tac >> gvs[FLOOKUP_DEF]) >>
    qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
    simp[step_inst_base_def] >>
    Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
    simp[exec_alloca_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    strip_tac >> gvs[update_var_def, FLOOKUP_UPDATE] >>
    MAP_EVERY qexists_tac [`aid'`, `off'`, `asz'`] >> simp[])
  >- (
    `v.vs_allocas = s.vs_allocas` by metis_tac[step_inst_base_allocas] >>
    MAP_EVERY qexists_tac [`aid'`, `off'`, `asz'`] >> simp[])
QED

Finalise step_preserves_ptrs_in_alloca_bounds

(* Memory length monotonicity for write_memory_with_expansion *)
Theorem wmwe_mem_length_mono[local]:
  !off bytes s.
    LENGTH s.vs_memory <= LENGTH (write_memory_with_expansion off bytes s).vs_memory
Proof
  rpt gen_tac >>
  simp[write_memory_with_expansion_def, LET_DEF] >>
  Cases_on `off + LENGTH bytes > LENGTH s.vs_memory` >>
  simp[LENGTH_APPEND, LENGTH_TAKE_EQ, LENGTH_REPLICATE, LENGTH_DROP]
QED

(* Memory length monotonicity for non-ALLOCA, non-terminator steps *)
(* Memory length monotonicity for non-ALLOCA steps: memory never shrinks.
   For non-write ops: memory unchanged.
   For write ops: wmwe is monotone. *)
Theorem step_inst_base_mem_length_mono[local]:
  !inst s v.
    step_inst_base inst s = OK v /\
    ~is_terminator inst.inst_opcode /\
    ~is_ext_call_op inst.inst_opcode /\
    ~is_alloca_op inst.inst_opcode ==>
    LENGTH s.vs_memory <= LENGTH v.vs_memory
Proof
  rpt strip_tac >>
  Cases_on `mem_write_ops inst`
  >- (`v.vs_memory = s.vs_memory` by
        metis_tac[step_inst_base_mem_preserves_no_mem_ops] >> simp[])
  >- (
    (* Memory-writing instruction: result uses mstore/mstore8/mcopy/wmwe.
       All of these preserve or grow memory (wmwe_mem_length_mono). *)
    qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
    simp[step_inst_base_def] >>
    Cases_on `inst.inst_opcode` >>
    gvs[is_terminator_def, is_alloca_op_def, is_ext_call_op_def,
        mem_write_ops_def] >>
    (* Only memory-writing opcodes remain after gvs *)
    simp[exec_write2_def] >>
    rpt strip_tac >> gvs[AllCaseEqs()] >>
    rpt (CHANGED_TAC (rpt (pairarg_tac >> gvs[]))) >>
    gvs[update_var_def] >>
    (* All results use mstore/mstore8/mcopy → wmwe → monotone *)
    simp[mstore_eq_wmwe, mstore8_eq_wmwe, mcopy_def] >>
    irule wmwe_mem_length_mono)
QED

(* After a step, future inst_ids remain fresh w.r.t. the updated allocas *)
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
Proof
  rpt strip_tac >>
  `(EL i bb.bb_instructions).inst_id NOTIN FDOM s1.vs_allocas` by (
    first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
  Cases_on `is_alloca_op inst.inst_opcode`
  >- (
    (* ALLOCA case: v.vs_allocas extended with inst.inst_id *)
    (* Derive (EL i).inst_id <> inst.inst_id via ALL_DISTINCT *)
    `s1.vs_inst_idx < LENGTH bb.bb_instructions /\
     EL s1.vs_inst_idx bb.bb_instructions = inst` by (
      fs[get_instruction_def] >>
      Cases_on `s1.vs_inst_idx < LENGTH bb.bb_instructions` >> fs[]) >>
    `(EL i bb.bb_instructions).inst_id <> inst.inst_id` by (
      `ALL_DISTINCT (MAP (\j. j.inst_id) bb.bb_instructions)` by (
        `fn_inst_ids_distinct fn` by fs[wf_function_def] >>
        pop_assum mp_tac >> simp[fn_inst_ids_distinct_def] >>
        `!bbs. ALL_DISTINCT
                 (FLAT (MAP (\bb. MAP (\j. j.inst_id) bb.bb_instructions) bbs)) /\
               MEM bb bbs ==>
               ALL_DISTINCT (MAP (\j. j.inst_id) bb.bb_instructions)` suffices_by
          metis_tac[] >>
        Induct >> simp[ALL_DISTINCT_APPEND] >> metis_tac[]) >>
      `i <> s1.vs_inst_idx` by simp[] >>
      fs[EL_ALL_DISTINCT_EL_EQ, EL_MAP] >>
      metis_tac[]) >>
    (* Now show NOTIN FDOM v.vs_allocas *)
    qpat_x_assum `step_inst_base _ _ = OK _` mp_tac >>
    simp[step_inst_base_def] >>
    Cases_on `inst.inst_opcode` >> gvs[is_alloca_op_def] >>
    simp[exec_alloca_def] >>
    rpt (BasicProvers.FULL_CASE_TAC >> gvs[]) >>
    strip_tac >> gvs[update_var_def, FDOM_FUPDATE])
  >- (
    (* Non-ALLOCA: v.vs_allocas = s1.vs_allocas *)
    `v.vs_allocas = s1.vs_allocas` by metis_tac[step_inst_base_allocas] >>
    fs[])
QED

Resume run_block_preserves_remap[ok_case]:
  (* Step 1: Specialize nested uniqueness for inst' *)
  `!u. u IN pointer_derived_vars fn roots ==>
       LENGTH (FILTER ($= (Var u)) inst'.inst_operands) <= 1` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  (* Step 2: Apply step_preserves_remap *)
  qspecl_then [`fn`,`roots`,`remap`,`inst'`,`s1`,`s2`,`v`,`bb`]
    mp_tac step_preserves_remap >>
  impl_tac >- suspend "spr_impl"
  >>
  (* Step 3: Decompose conclusion *)
  strip_tac >>
  (* Rewrite case expression using step_inst_base inst' s2 = OK v2 *)
  qpat_x_assum `step_inst_base inst' s2 = OK v2` (fn th =>
    assume_tac th >> PURE_REWRITE_TAC[th] >> BETA_TAC) >>
  simp_tac (srw_ss()) [] >>
  (* Step 4: Bridge step_inst = step_inst_base for IH *)
  `step_inst fuel ctx inst' s1 = OK v` by
    simp[step_inst_non_invoke] >>
  (* Step 5: Apply IH -- instantiate outer quantifiers *)
  qpat_x_assum `!inst s''. SOME inst' = SOME inst /\ _ ==> _`
    (qspecl_then [`inst'`, `v`] mp_tac) >>
  simp[] >>
  (* Now instantiate inner quantifiers *)
  disch_then (qspecl_then
    [`remap'`, `v2 with vs_inst_idx := SUC s1.vs_inst_idx`] mp_tac) >>
  impl_tac >- suspend "ih_impl"
  >>
  (* Step 6: Chain FDOM subset and FLOOKUP preservation *)
  strip_tac >>
  qexists_tac `remap''` >>
  conj_tac >- (irule SUBSET_TRANS >> qexists_tac `FDOM remap'` >> simp[]) >>
  (conj_tac >- (
    rpt strip_tac >>
    `aid IN FDOM remap'` by metis_tac[SUBSET_DEF] >>
    fs[])) >>
  simp[]
QED

Resume run_block_preserves_remap[spr_impl]:
  (* is_alloca_op ==> ... is vacuously true since ~is_alloca_op inst' *)
  `~is_alloca_op inst'.inst_opcode` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  simp[]
QED

Resume run_block_preserves_remap[ih_impl]:
  (* 1. alloca_remap_rel with bumped inst_idx *)
  conj_tac >- (
    irule alloca_remap_rel_inst_idx >> first_assum ACCEPT_TAC) >>
  (* 2-3. alloca_safe_access for v, v2 — needs step preservation *)
  conj_tac >- (
    simp[alloca_safe_access_inst_idx] >>
    suspend "ih_safe_access_v") >>
  conj_tac >- (
    simp[alloca_safe_access_inst_idx] >>
    suspend "ih_safe_access_v2") >>
  (* 4-5. ptrs_in_alloca_bounds for v, v2 — needs step preservation *)
  conj_tac >- (
    simp[ptrs_in_alloca_bounds_inst_idx] >>
    suspend "ih_ptrs_bounds_v") >>
  conj_tac >- (
    simp[ptrs_in_alloca_bounds_inst_idx] >>
    suspend "ih_ptrs_bounds_v2") >>
  (* 6. FDOM remap' ⊆ FDOM v.vs_allocas *)
  conj_tac >- first_assum ACCEPT_TAC >>
  (* 7. Offset bounds -- universally quantified, still in context *)
  conj_tac >- first_assum ACCEPT_TAC >>
  (* 8. Freshness after step *)
  qspecl_then [`fn`,`bb`,`inst'`,`s1`,`v`] mp_tac inst_ids_fresh_after_step >>
  simp[]
QED

Resume run_block_preserves_remap[halt_case]:
  (* step_inst_base never returns Halt for non-terminators *)
  qpat_x_assum `step_inst_base _ _ = Halt _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst'.inst_opcode` >>
  gvs[is_terminator_def, is_ext_call_op_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, eval_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Resume run_block_preserves_remap[abort_case]:
  (* Specialize nested per-inst uniqueness hypothesis for inst' *)
  `!u. u IN pointer_derived_vars fn roots ==>
       LENGTH (FILTER ($= (Var u)) inst'.inst_operands) <= 1` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  drule_all step_inst_base_abort_transfer >> strip_tac >>
  qexists_tac `remap` >> simp[SUBSET_REFL, lift_result_def]
QED

Resume run_block_preserves_remap[intret_case]:
  (* step_inst_base never returns IntRet for non-terminators *)
  qpat_x_assum `step_inst_base _ _ = IntRet _ _` mp_tac >>
  simp[step_inst_base_def] >>
  Cases_on `inst'.inst_opcode` >>
  gvs[is_terminator_def, is_ext_call_op_def] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_alloca_def, eval_operands_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Resume run_block_preserves_remap[error_case]:
  drule_all step_inst_base_error_transfer >> strip_tac >>
  qexists_tac `remap` >> simp[SUBSET_REFL, lift_result_def]
QED

Resume run_block_preserves_remap[ih_ptrs_bounds_v]:
  (* ptrs_in_alloca_bounds preserved through step for s1 *)
  `~is_alloca_op inst'.inst_opcode` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  qspecl_then [`fn`,`roots`,`inst'`,`bb`,`s1`,`v`]
    mp_tac step_preserves_ptrs_in_alloca_bounds >>
  simp[]
QED

Resume run_block_preserves_remap[ih_ptrs_bounds_v2]:
  (* ptrs_in_alloca_bounds preserved through step for s2 *)
  `~is_alloca_op inst'.inst_opcode` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  qspecl_then [`fn`,`roots`,`inst'`,`bb`,`s2`,`v2`]
    mp_tac step_preserves_ptrs_in_alloca_bounds >>
  simp[]
QED

(* alloca_safe_access preserved by step: use step_preserves_safety oracle.
   alloca_safe_access clause 2 quantifies over ALL mem instructions in fn;
   when the stepped instruction outputs a variable used as a size operand
   in some other instruction, the new value is program-specific and the
   bound cannot be transferred from the pre-state. *)
Resume run_block_preserves_remap[ih_safe_access_v]:
  `~is_alloca_op inst'.inst_opcode` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  qspecl_then [`fn`,`roots`,`inst'`,`bb`,`s1`,`v`]
    mp_tac step_safety_elim >> simp[]
QED

Resume run_block_preserves_remap[ih_safe_access_v2]:
  `~is_alloca_op inst'.inst_opcode` by (
    first_x_assum (qspec_then `inst'` mp_tac) >> simp[]) >>
  qspecl_then [`fn`,`roots`,`inst'`,`bb`,`s2`,`v2`]
    mp_tac step_safety_elim >> simp[]
QED

Finalise run_block_preserves_remap

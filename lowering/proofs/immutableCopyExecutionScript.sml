Theory immutableCopyExecution
Ancestors
  bytestringCopyExecution fragExec stmtSimStoreCopy
  fragGasPath fragGasMode fragGasSeq placeCopyControlPath immutableWordExecution immutableMemoryFrame emitHelperProps
  context compileEnv emitHelper exprLoweringProps venomState venomExecSemantics venomInst
  mmCopyEquiv venomMemProps mmInterval
Libs
  stepInstBaseLib

(* The offset helper either folds a literal or emits a single ADD.  Its
   semantic frame is the interface needed to keep the copy's root operands
   stable while allocating address temporaries. *)
Theorem immutable_byte_offset_execution:
  compile_lit_byte_offset op off st = (result,st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand result s' = SOME (a + n2w off) /\
    fresh_vars_wrt st' s' /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p s' = SOME w) /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables
Proof
  Cases_on `off = 0`
  >- (simp[compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, wordsTheory.WORD_ADD_0]) >>
  Cases_on `op` >>
  simp[compile_lit_byte_offset_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def] >> rpt strip_tac >> gvs[]
  >- (qexists_tac `s` >>
      gvs[emitted_insts_def, run_inst_seq_def, eval_operand_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a + n2w off) s` >>
  simp[mk_inst_def] >>
  simp[emitted_insts_def, run_inst_seq_def, listTheory.DROP_APPEND,
       step_inst_base_opcode_eqs, exec_pure2_def,
       eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  (conj_tac >- gvs[fresh_vars_wrt_def]) >>
  rpt strip_tac >> Cases_on `p` >>
  gvs[eval_operand_def, lookup_var_def, update_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  IF_CASES_TAC >> gvs[fresh_vars_wrt_def, finite_mapTheory.FLOOKUP_DEF]
QED

(* Common loop invariant: generated writes only extend the variable domain,
   and never alter an operand which was already defined at entry. *)
Definition immutable_operand_frame_def:
  immutable_operand_frame st s st' s' <=>
    fresh_vars_wrt st' s' /\
    (!p w. eval_operand p s = SOME w ==> eval_operand p s' = SOME w)
End

Theorem immutable_operand_frame_refl:
  fresh_vars_wrt st s ==> immutable_operand_frame st s st s
Proof
  simp[immutable_operand_frame_def]
QED

Theorem immutable_operand_frame_trans:
  immutable_operand_frame st s st1 s1 /\
  immutable_operand_frame st1 s1 st2 s2 ==>
  immutable_operand_frame st s st2 s2
Proof
  simp[immutable_operand_frame_def] >> metis_tac[]
QED

Theorem immutable_fresh_update_frame:
  fresh_vars_wrt st s /\ st'.cs_next_var = st.cs_next_var + 1 ==>
  immutable_operand_frame st s st'
    (update_var (STRING #"%" (toString st.cs_next_var)) v s)
Proof
  simp[immutable_operand_frame_def] >> strip_tac >> conj_tac
  >- (irule fresh_vars_wrt_advance >> qexistsl_tac [`st.cs_next_var`,`st`] >> simp[]) >>
  rpt strip_tac >> irule eval_operand_update_fresh >> simp[] >>
  qexists_tac `st` >> simp[]
QED

Theorem immutable_byte_offset_extends:
  compile_lit_byte_offset op off st = (result,st') ==>
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var
Proof
  Cases_on `off = 0`
  >- simp[compile_lit_byte_offset_def, comp_return_def,
          emitted_insts_def, same_blocks_def] >>
  Cases_on `op` >> simp[compile_lit_byte_offset_def, comp_return_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
    fresh_var_def, emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def, same_blocks_def, listTheory.DROP_APPEND]
QED

(* Shared read boundary for MLOAD, ILOAD and DLOAD. *)
Theorem immutable_emit_read_frame:
  (opc = MLOAD \/ opc = ILOAD \/ opc = DLOAD) /\
  emit_op opc [op] st = (result,st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand result s' = SOME
      (if opc = DLOAD then word_of_bytes T (0w:bytes32)
         (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
       else mload (w2n a) s) /\
    immutable_operand_frame st s st' s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\
    s'.vs_memory = s.vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule emitted_insts_emit_op_local >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var))
    (if opc = DLOAD then word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
     else mload (w2n a) s) s` >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  (conj_tac
   >- (gvs[] >> simp[mk_inst_def] >>
       simp[run_inst_seq_def, step_inst_base_opcode_eqs,
                    exec_read1_def, update_var_def])) >>
  rewrite_tac[GSYM update_var_def] >>
  irule immutable_fresh_update_frame >> simp[]
QED

Theorem immutable_emit_store_frame:
  (opc = MSTORE \/ opc = ISTORE) /\
  emit_void opc [dst;value] st = ((),st') /\
  eval_operand dst s = SOME a /\ eval_operand value s = SOME v /\
  fresh_vars_wrt st s ==>
  run_inst_seq (emitted_insts st st') s =
    OK (if opc = ISTORE then istore (w2n a) v s else mstore (w2n a) v s) /\
  immutable_operand_frame st s st'
    (if opc = ISTORE then istore (w2n a) v s else mstore (w2n a) v s) /\
  st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
  same_blocks st st'
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  simp[mk_inst_def] >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, same_blocks_def,
       run_inst_seq_def, step_inst_base_opcode_eqs, exec_write2_def,
       immutable_operand_frame_def, fresh_vars_wrt_def, istore_def, mstore_def] >>
  rpt strip_tac >> gvs[fresh_vars_wrt_def] >>
  Cases_on `p` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem immutable_two_updates_frame:
  fresh_vars_wrt st s /\ st'.cs_next_var = st.cs_next_var + 2 ==>
  immutable_operand_frame st s st'
    (update_var (STRING #"%" (toString (st.cs_next_var + 1))) v
      (update_var (STRING #"%" (toString st.cs_next_var)) a s))
Proof
  strip_tac >>
  irule immutable_operand_frame_trans >>
  qexistsl_tac [`update_var (STRING #"%" (toString st.cs_next_var)) a s`,
               `st with cs_next_var := st.cs_next_var + 1`] >>
  conj_asm1_tac
  >- (irule immutable_fresh_update_frame >> simp[]) >>
  qmatch_goalsub_abbrev_tac `immutable_operand_frame mid _ _ _` >>
  `mid.cs_next_var = st.cs_next_var + 1` by simp[Abbr `mid`] >>
  qpat_x_assum `mid.cs_next_var = _` (SUBST1_TAC o SYM) >>
  irule immutable_fresh_update_frame >>
  gvs[immutable_operand_frame_def, Abbr `mid`]
QED

Theorem immutable_ctor_load_frame:
  compile_imm_load_word T (SOME region) off st = (result,st') /\
  eval_operand off s = SOME a /\ eval_operand region s = SOME 0w /\
  fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand result s' = SOME (mload (w2n a) s) /\
    immutable_operand_frame st s st' s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\ s'.vs_memory = s.vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule compile_imm_load_word_ctor_result >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString (st.cs_next_var + 1)))
    (mload (w2n a) s) (update_var (STRING #"%" (toString st.cs_next_var)) a s)` >>
  conj_tac
  >- (drule compile_imm_load_word_ctor_execution >> simp[]) >>
  conj_tac
  >- simp[eval_operand_def, lookup_var_def, update_var_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac >- (irule immutable_two_updates_frame >> simp[]) >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, update_var_def] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, same_blocks_def] >> strip_tac >> gvs[]
QED

Theorem immutable_load_frame:
  compile_imm_load_word ctor (SOME region) off st = (result,st') /\
  eval_operand off s = SOME a /\ (ctor ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    eval_operand result s' = SOME
      (if ctor then mload (w2n a) s else word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    immutable_operand_frame st s st' s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\ s'.vs_memory = s.vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables
Proof
  Cases_on `ctor` >> simp[]
  >- (strip_tac >> irule immutable_ctor_load_frame >> simp[] >> metis_tac[]) >>
  simp[compile_imm_load_word_def] >> strip_tac >>
  irule (SRULE [] (Q.INST [`opc` |-> `DLOAD`]
    (SPEC_ALL immutable_emit_read_frame))) >> simp[] >>
  qexists_tac `off` >> simp[]
QED

Theorem immutable_frame_istore:
  immutable_operand_frame st s st' s' ==>
  immutable_operand_frame st s st' (istore at v s')
Proof
  simp[immutable_operand_frame_def, immutable_word_istore_operand_frame] >>
  strip_tac >> simp[] >>
  gvs[fresh_vars_wrt_def, istore_def, mstore_def]
QED

Theorem immutable_ctor_store_frame:
  compile_imm_store_word (SOME region) off value st = ((),st') /\
  eval_operand region s = SOME 0w /\ eval_operand off s = SOME a /\
  eval_operand value s = SOME v /\ fresh_vars_wrt st s ==>
  ?s'. run_inst_seq (emitted_insts st st') s = OK s' /\
    immutable_operand_frame st s st' s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\
    s'.vs_memory = (mstore (w2n a) v s).vs_memory /\
    s'.vs_data_section = s.vs_data_section /\
    s'.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  strip_tac >> drule compile_imm_store_word_result >> strip_tac >>
  `immutable_operand_frame st s st'
    (update_var (STRING #"%" (toString st.cs_next_var)) a s)` by
    (irule immutable_fresh_update_frame >> simp[]) >>
  `eval_operand value (update_var (STRING #"%" (toString st.cs_next_var)) a s) = SOME v` by
    fs[immutable_operand_frame_def] >>
  qexists_tac `istore (w2n a) v
    (update_var (STRING #"%" (toString st.cs_next_var)) a s)` >>
  conj_tac
  >- (drule compile_imm_store_word_execution >> simp[]) >>
  conj_tac >- (irule immutable_frame_istore >> simp[]) >>
  simp[emitted_insts_def, listTheory.DROP_APPEND, immutable_word_store_frame,
       istore_def, update_var_def, mstore_def] >>
  qpat_x_assum `compile_imm_store_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_store_word_def, emit_op_def, emit_void_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
       emit_def, same_blocks_def] >> strip_tac >> gvs[]
QED

(* Endpoint composition only: no pre/postcondition or compiler Hoare logic.
   Memory and immutable-map effects remain in the per-operation theorem. *)
Definition immutable_execution_frame_def:
  immutable_execution_frame st s st' s' <=>
    run_inst_seq (emitted_insts st st') s = OK s' /\
    st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
    same_blocks st st' /\ immutable_operand_frame st s st' s' /\
    s'.vs_data_section = s.vs_data_section
End

Theorem immutable_execution_frame_trans:
  immutable_execution_frame st s st1 s1 /\
  immutable_execution_frame st1 s1 st2 s2 ==>
  immutable_execution_frame st s st2 s2
Proof
  simp[immutable_execution_frame_def] >> strip_tac >>
  `emitted_insts st st2 = emitted_insts st st1 ++ emitted_insts st1 st2` by
    (irule emitted_insts_append >> simp[]) >>
  conj_tac
  >- (qpat_assum `run_inst_seq (emitted_insts st st1) s = _`
        (mp_then Any mp_tac run_inst_seq_append) >> simp[]) >>
  conj_tac >- simp[listTheory.APPEND_ASSOC] >>
  conj_tac >- gvs[same_blocks_def] >> simp[] >>
  irule immutable_operand_frame_trans >> metis_tac[]
QED

Theorem immutable_comp_bind_cases:
  (do x <- f; g x od) st = (r,st') <=>
  ?x st1. f st = (x,st1) /\ g x st1 = (r,st')
Proof
  Cases_on `f st` >> simp[comp_bind_def]
QED

Definition immutable_copy_one_def:
  immutable_copy_one ctor imm src dst off =
    do src_op <- compile_lit_byte_offset src off;
       value <- compile_imm_load_word ctor imm src_op;
       dst_op <- compile_lit_byte_offset dst off;
       emit_void MSTORE [dst_op;value]
    od
End

Definition immutable_store_one_def:
  immutable_store_one imm src dst off =
    do src_op <- compile_lit_byte_offset src off;
       value <- emit_op MLOAD [src_op];
       dst_op <- compile_lit_byte_offset dst off;
       compile_imm_store_word imm dst_op value
    od
End

Theorem immutable_copy_suc:
  compile_imm_copy_to_memory ctor imm src dst (SUC n) off =
    do immutable_copy_one ctor imm src dst off;
       compile_imm_copy_to_memory ctor imm src dst n (off+32)
    od
Proof
  simp[compile_imm_copy_to_memory_def, immutable_copy_one_def,
       comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem immutable_store_suc:
  compile_imm_store_words imm src dst (SUC n) off =
    do immutable_store_one imm src dst off;
       compile_imm_store_words imm src dst n (off+32)
    od
Proof
  simp[compile_imm_store_words_def, immutable_store_one_def,
       comp_ignore_bind_def, comp_bind_assoc]
QED

Theorem immutable_offset_frame:
  compile_lit_byte_offset op off st = (result,st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    eval_operand result s' = SOME (a+n2w off) /\
    s'.vs_memory = s.vs_memory /\ s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all immutable_byte_offset_execution >> strip_tac >>
  drule immutable_byte_offset_extends >> strip_tac >>
  qexists_tac `s'` >> fs[immutable_execution_frame_def, immutable_operand_frame_def]
QED

Theorem immutable_load_execution_frame:
  compile_imm_load_word ctor (SOME region) op st = (result,st') /\
  eval_operand op s = SOME a /\ (ctor ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    eval_operand result s' = SOME
      (if ctor then mload (w2n a) s else word_of_bytes T (0w:bytes32)
        (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))) /\
    s'.vs_memory = s.vs_memory /\ s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all immutable_load_frame >> strip_tac >>
  qexists_tac `s'` >> fs[immutable_execution_frame_def]
QED

Theorem immutable_memory_load_frame:
  emit_op MLOAD [op] st = (result,st') /\
  eval_operand op s = SOME a /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    eval_operand result s' = SOME (mload (w2n a) s) /\
    s'.vs_memory = s.vs_memory /\ s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  mp_tac (SRULE [] (Q.INST [`opc` |-> `MLOAD`]
    (SPEC_ALL immutable_emit_read_frame))) >>
  simp[] >> strip_tac >> qexists_tac `s'` >>
  fs[immutable_execution_frame_def]
QED

Theorem immutable_memory_store_frame:
  emit_void MSTORE [dst;value] st = ((),st') /\
  eval_operand dst s = SOME a /\ eval_operand value s = SOME v /\
  fresh_vars_wrt st s ==>
  immutable_execution_frame st s st' (mstore (w2n a) v s)
Proof
  strip_tac >>
  mp_tac (SRULE [] (Q.INST [`opc` |-> `MSTORE`]
    (SPEC_ALL immutable_emit_store_frame))) >>
  simp[] >> strip_tac >>
  fs[immutable_execution_frame_def, mstore_def]
QED

Theorem immutable_store_execution_frame:
  compile_imm_store_word (SOME region) op value st = ((),st') /\
  eval_operand region s = SOME 0w /\ eval_operand op s = SOME a /\
  eval_operand value s = SOME v /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (mstore (w2n a) v s).vs_memory /\
    s'.vs_immutables = s.vs_immutables |+ (w2n a,v)
Proof
  strip_tac >> drule_all immutable_ctor_store_frame >> strip_tac >>
  qexists_tac `s'` >> fs[immutable_execution_frame_def]
QED

Definition immutable_copy_read_def:
  immutable_copy_read memory_source (a:bytes32) s =
    if memory_source then mload (w2n a) s
    else word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n a) s.vs_data_section ++ REPLICATE 32 0w))
End

Theorem immutable_transfer_load_frame:
  (if store then emit_op MLOAD [op]
   else compile_imm_load_word ctor (SOME region) op) st = (result,st') /\
  eval_operand op s = SOME a /\ (ctor ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    eval_operand result s' = SOME (immutable_copy_read (store \/ ctor) a s) /\
    s'.vs_memory = s.vs_memory /\ s'.vs_immutables = s.vs_immutables
Proof
  Cases_on `store` >> simp[immutable_copy_read_def]
  >- (strip_tac >> drule_all immutable_memory_load_frame >> simp[]) >>
  strip_tac >> drule_all immutable_load_execution_frame >> simp[]
QED

Theorem immutable_transfer_store_frame:
  (if store then compile_imm_store_word (SOME region) op value
   else emit_void MSTORE [op;value]) st = ((),st') /\
  eval_operand op s = SOME a /\ eval_operand value s = SOME v /\
  (store ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (mstore (w2n a) v s).vs_memory /\
    s'.vs_immutables =
      (if store then s.vs_immutables |+ (w2n a,v) else s.vs_immutables)
Proof
  Cases_on `store` >> simp[]
  >- (strip_tac >> drule_all immutable_store_execution_frame >> simp[]) >>
  strip_tac >> drule_all immutable_memory_store_frame >> strip_tac >>
  qexists_tac `mstore (w2n a) v s` >> simp[mstore_def]
QED

(* A common prefix avoids duplicating the same four-stage freshness argument
   for reading a staged immutable and for writing one. *)
Definition immutable_transfer_one_def:
  immutable_transfer_one store ctor region src dst off =
    do src_op <- compile_lit_byte_offset src off;
       value <- (if store then emit_op MLOAD [src_op]
                 else compile_imm_load_word ctor (SOME region) src_op);
       dst_op <- compile_lit_byte_offset dst off;
       (if store then compile_imm_store_word (SOME region) dst_op value
        else emit_void MSTORE [dst_op;value])
    od
End

Theorem immutable_transfer_one_copy:
  immutable_copy_one ctor (SOME region) src dst off =
    immutable_transfer_one F ctor region src dst off
Proof
  simp[immutable_copy_one_def, immutable_transfer_one_def]
QED

Theorem immutable_transfer_one_store:
  immutable_store_one (SOME region) src dst off =
    immutable_transfer_one T ctor region src dst off
Proof
  simp[immutable_store_one_def, immutable_transfer_one_def]
QED

Definition immutable_word_transfer_def:
  immutable_word_transfer store ctor a (b:bytes32) off s =
    let value = immutable_copy_read (store \/ ctor) (a+n2w off) s in
    if store then istore (w2n (b+n2w off)) value s
    else mstore (w2n (b+n2w off)) value s
End

Theorem immutable_execution_frame_operands:
  immutable_execution_frame st s st' s' ==>
  fresh_vars_wrt st' s' /\ s'.vs_data_section = s.vs_data_section /\
  (!p w. eval_operand p s = SOME w ==> eval_operand p s' = SOME w)
Proof
  simp[immutable_execution_frame_def, immutable_operand_frame_def]
QED

Theorem immutable_copy_read_cong:
  s1.vs_memory = s.vs_memory /\ s1.vs_data_section = s.vs_data_section ==>
  immutable_copy_read mode a s1 = immutable_copy_read mode a s
Proof
  simp[immutable_copy_read_def, mload_def]
QED

Theorem immutable_mstore_memory_cong:
  s1.vs_memory = s.vs_memory ==>
  (mstore at v s1).vs_memory = (mstore at v s).vs_memory
Proof
  simp[mstore_def]
QED

Theorem immutable_word_transfer_fields:
  (immutable_word_transfer store ctor a b off s).vs_memory =
    (mstore (w2n (b+n2w off))
      (immutable_copy_read (store \/ ctor) (a+n2w off) s) s).vs_memory /\
  (immutable_word_transfer store ctor a b off s).vs_immutables =
    (if store then s.vs_immutables |+ (w2n (b+n2w off),
       immutable_copy_read (store \/ ctor) (a+n2w off) s)
     else s.vs_immutables)
Proof
  Cases_on `store` >> simp[immutable_word_transfer_def, istore_def, mstore_def]
QED

Theorem immutable_transfer_one_execution:
  immutable_transfer_one store ctor region src dst off st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_word_transfer store ctor a b off s).vs_memory /\
    s'.vs_immutables = (immutable_word_transfer store ctor a b off s).vs_immutables
Proof
  simp[immutable_transfer_one_def, immutable_comp_bind_cases] >> strip_tac >>
  rename1 `compile_lit_byte_offset src off st = (src_addr,c1)` >>
  rename1 `(if store then emit_op MLOAD [src_addr] else _) c1 = (value,c2)` >>
  rename1 `compile_lit_byte_offset dst off c2 = (dst_addr,c3)` >>
  drule_all immutable_offset_frame >> strip_tac >>
  rename1 `immutable_execution_frame st s c1 s1` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `ctor ==> eval_operand region s1 = SOME 0w` by metis_tac[] >>
  drule_all immutable_transfer_load_frame >> strip_tac >>
  rename1 `immutable_execution_frame c1 s1 c2 s2` >>
  `immutable_execution_frame st s c2 s2` by
    (irule immutable_execution_frame_trans >> metis_tac[]) >>
  qpat_x_assum `immutable_execution_frame c1 _ _ _` kall_tac >>
  qpat_x_assum `immutable_execution_frame st _ c1 _` kall_tac >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand dst s2 = SOME b` by metis_tac[] >>
  drule_all immutable_offset_frame >> strip_tac >>
  rename1 `immutable_execution_frame c2 s2 c3 s3` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand value s3 = SOME (immutable_copy_read (store \/ ctor)
     (a+n2w off) s1)` by metis_tac[] >>
  `store ==> eval_operand region s3 = SOME 0w` by metis_tac[] >>
  drule_all immutable_transfer_store_frame >> strip_tac >>
  rename1 `immutable_execution_frame c3 s3 st' s4` >>
  qexists_tac `s4` >> conj_tac
  >- (irule immutable_execution_frame_trans >>
      qexistsl_tac [`s2`,`c2`] >> simp[] >>
      irule immutable_execution_frame_trans >> metis_tac[]) >>
  `immutable_copy_read (store \/ ctor) (a+n2w off) s1 =
    immutable_copy_read (store \/ ctor) (a+n2w off) s` by
    (irule immutable_copy_read_cong >> simp[]) >>
  gvs[immutable_word_transfer_fields, immutable_mstore_memory_cong]
QED

(* Sequential semantics, including forward-copy overlap and word arithmetic.
   No snapshot/disjointness assertion is hidden in this definition. *)
Definition immutable_transfers_def:
  immutable_transfers store ctor a b 0 off s = s /\
  immutable_transfers store ctor a b (SUC n) off s =
    immutable_transfers store ctor a b n (off+32)
      (immutable_word_transfer store ctor a b off s)
End

Theorem immutable_transfer_data:
  (immutable_word_transfer store ctor a b off s).vs_data_section = s.vs_data_section
Proof
  Cases_on `store` >> simp[immutable_word_transfer_def, istore_def, mstore_def]
QED

Theorem immutable_transfers_data:
  !n off s. (immutable_transfers store ctor a b n off s).vs_data_section =
    s.vs_data_section
Proof
  Induct >> simp[immutable_transfers_def, immutable_transfer_data]
QED

Theorem immutable_word_transfer_cong:
  s1.vs_memory = s.vs_memory /\ s1.vs_data_section = s.vs_data_section /\
  s1.vs_immutables = s.vs_immutables ==>
  (immutable_word_transfer store ctor a b off s1).vs_memory =
    (immutable_word_transfer store ctor a b off s).vs_memory /\
  (immutable_word_transfer store ctor a b off s1).vs_data_section =
    (immutable_word_transfer store ctor a b off s).vs_data_section /\
  (immutable_word_transfer store ctor a b off s1).vs_immutables =
    (immutable_word_transfer store ctor a b off s).vs_immutables
Proof
  strip_tac >>
  `immutable_copy_read (store \/ ctor) (a+n2w off) s1 =
    immutable_copy_read (store \/ ctor) (a+n2w off) s` by
    (irule immutable_copy_read_cong >> simp[]) >>
  simp[immutable_word_transfer_fields, immutable_transfer_data,
       immutable_mstore_memory_cong]
QED

Theorem immutable_transfers_cong:
  !n off s1 s.
  s1.vs_memory = s.vs_memory /\ s1.vs_data_section = s.vs_data_section /\
  s1.vs_immutables = s.vs_immutables ==>
  (immutable_transfers store ctor a b n off s1).vs_memory =
    (immutable_transfers store ctor a b n off s).vs_memory /\
  (immutable_transfers store ctor a b n off s1).vs_immutables =
    (immutable_transfers store ctor a b n off s).vs_immutables
Proof
  Induct >> simp[immutable_transfers_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum irule >>
  drule_all immutable_word_transfer_cong >> simp[]
QED

Theorem immutable_compile_transfer_suc:
  (if store then compile_imm_store_words (SOME region) src dst (SUC n) off
   else compile_imm_copy_to_memory ctor (SOME region) src dst (SUC n) off) =
  do immutable_transfer_one store ctor region src dst off;
     (if store then compile_imm_store_words (SOME region) src dst n (off+32)
      else compile_imm_copy_to_memory ctor (SOME region) src dst n (off+32))
  od
Proof
  Cases_on `store` >>
  simp[immutable_copy_suc, immutable_store_suc,
       immutable_transfer_one_def, immutable_copy_one_def, immutable_store_one_def]
QED

Theorem immutable_compile_transfers_execution:
  !n off st st' s.
  (if store then compile_imm_store_words (SOME region) src dst n off
   else compile_imm_copy_to_memory ctor (SOME region) src dst n off) st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\
  fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers store ctor a b n off s).vs_memory /\
    s'.vs_immutables = (immutable_transfers store ctor a b n off s).vs_immutables
Proof
  Induct
  >- (rpt gen_tac >>
      simp[compile_imm_store_words_def, compile_imm_copy_to_memory_def,
           comp_return_def, immutable_transfers_def] >>
      Cases_on `store` >> simp[] >> strip_tac >> gvs[] >>
      qexists_tac `s` >> simp[immutable_execution_frame_def,
        immutable_operand_frame_refl, emitted_insts_def, run_inst_seq_def,
        same_blocks_def]) >>
  rpt gen_tac >>
  simp[immutable_compile_transfer_suc, comp_ignore_bind_def, immutable_comp_bind_cases] >>
  strip_tac >> rename1 `immutable_transfer_one store ctor region src dst off st = (u,c1)` >>
  Cases_on `u` >>
  drule_all immutable_transfer_one_execution >> strip_tac >>
  rename1 `immutable_execution_frame st s c1 s1` >>
  drule immutable_execution_frame_operands >> strip_tac >>
  `eval_operand src s1 = SOME a /\ eval_operand dst s1 = SOME b /\
   ((store \/ ctor) ==> eval_operand region s1 = SOME 0w)` by metis_tac[] >>
  qpat_x_assum `!off st st' s. _` drule_all >> strip_tac >>
  rename1 `immutable_execution_frame c1 s1 st' s2` >>
  qexists_tac `s2` >> conj_tac
  >- (irule immutable_execution_frame_trans >> metis_tac[]) >>
  `s1.vs_data_section = (immutable_word_transfer store ctor a b off s).vs_data_section` by
    simp[immutable_transfer_data] >>
  gvs[immutable_transfers_def] >>
  irule immutable_transfers_cong >> simp[]
QED

Theorem immutable_transfers_snoc:
  !n off s.
  immutable_transfers store ctor a b (SUC n) off s =
    immutable_word_transfer store ctor a b (off+32*n)
      (immutable_transfers store ctor a b n off s)
Proof
  Induct >- simp[immutable_transfers_def] >> rpt gen_tac >>
  pure_once_rewrite_tac[immutable_transfers_def] >>
  first_x_assum (qspec_then `off+32` (fn th => once_rewrite_tac[th])) >>
  `off+32+32*n = off+32*SUC n` by decide_tac >>
  asm_rewrite_tac[]
QED

Theorem immutable_mcopy_memory_cong:
  s1.vs_memory = s.vs_memory ==>
  (mcopy dst src nbytes s1).vs_memory = (mcopy dst src nbytes s).vs_memory
Proof
  simp[mcopy_def, immutable_write_memory_bytes]
QED

Theorem immutable_transfer_memory_copy:
  (store \/ ctor) /\ src+off < dimword (:256) /\ dst+off < dimword (:256) ==>
  (immutable_word_transfer store ctor (n2w src) (n2w dst) off s).vs_memory =
    (mcopy (dst+off) (src+off) 32 s).vs_memory
Proof
  strip_tac >>
  simp[immutable_word_transfer_fields, immutable_copy_read_def,
       wordsTheory.word_add_n2w, wordsTheory.w2n_n2w,
       mload_mstore_is_mcopy]
QED

Theorem immutable_memory_transfers_snapshot:
  !n src dst off s.
  0 < n /\ (store \/ ctor) /\
  src+off+32*n < dimword (:256) /\ dst+off+32*n < dimword (:256) /\
  (dst+off+32*n <= src+off \/ src+off+32*n <= dst+off) ==>
  (immutable_transfers store ctor (n2w src) (n2w dst) n off s).vs_memory =
    (mcopy (dst+off) (src+off) (32*n) s).vs_memory
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >> (
  `src+off+32*n < dimword (:256) /\ dst+off+32*n < dimword (:256)` by decide_tac >>
  simp[immutable_transfers_snoc] >>
  `src+(off+32*n) < dimword (:256) /\ dst+(off+32*n) < dimword (:256)` by decide_tac >>
  simp[immutable_transfer_memory_copy] >>
  Cases_on `n = 0`
  >- simp[immutable_transfers_def] >>
  `0 < n` by decide_tac >>
  qpat_x_assum `!src dst off s. _`
    (qspecl_then [`src`,`dst`,`off`,`s`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  irule EQ_TRANS >> irule_at (Pos hd) immutable_mcopy_memory_cong >>
  qexists_tac `mcopy (dst+off) (src+off) (32*n) s` >>
  conj_tac >- gvs[] >>
  `dst+(off+32*n) = (dst+off)+32*n /\
    src+(off+32*n) = (src+off)+32*n` by decide_tac >>
  simp[] >>
  `~interval_overlaps (mk_interval (dst+off) (32*n+32))
     (mk_interval (src+off) (32*n+32))` by
    gvs[interval_overlaps_def, mk_interval_def, interval_end_def] >>
  drule mcopy_merge_step >> disch_then (qspec_then `s` mp_tac) >>
  simp[arithmeticTheory.MULT_CLAUSES])
QED

Theorem immutable_padded_read_append:
  TAKE m (DROP src bs ++ REPLICATE m (0w:word8)) ++
  TAKE n (DROP (src+m) bs ++ REPLICATE n 0w) =
  TAKE (m+n) (DROP src bs ++ REPLICATE (m+n) 0w)
Proof
  rw[listTheory.LIST_EQ_REWRITE, listTheory.LENGTH_TAKE_EQ,
     listTheory.LENGTH_DROP, listTheory.EL_APPEND_EQN, listTheory.EL_TAKE,
     listTheory.EL_DROP, rich_listTheory.EL_REPLICATE] >> fs[] >>
  rpt IF_CASES_TAC >> gvs[]
QED

Theorem immutable_runtime_word_as_write:
  src+off < dimword (:256) /\ dst+off < dimword (:256) ==>
  immutable_word_transfer F F (n2w src) (n2w dst) off s =
  write_memory_with_expansion (dst+off)
    (TAKE 32 (DROP (src+off) s.vs_data_section ++ REPLICATE 32 0w)) s
Proof
  simp[immutable_word_transfer_def, immutable_copy_read_def,
       wordsTheory.word_add_n2w, wordsTheory.w2n_n2w] >>
  strip_tac >> simp[mstore_def, write_memory_with_expansion_def,
                   word_bytes_roundtrip_256, listTheory.LENGTH_TAKE_EQ]
QED

Theorem immutable_padded_writes_append:
  write_memory_with_expansion (dst+n)
    (TAKE m (DROP (src+n) bs ++ REPLICATE m 0w))
    (write_memory_with_expansion dst (TAKE n (DROP src bs ++ REPLICATE n 0w)) s) =
  write_memory_with_expansion dst
    (TAKE (n+m) (DROP src bs ++ REPLICATE (n+m) 0w)) s
Proof
  qabbrev_tac `head = TAKE n (DROP src bs ++ REPLICATE n 0w)` >>
  `LENGTH head = n` by simp[Abbr `head`, listTheory.LENGTH_TAKE_EQ] >>
  qpat_x_assum `LENGTH head = n` (SUBST1_TAC o SYM) >>
  rewrite_tac[write_memory_append] >>
  simp[Abbr `head`] >>
  `n+src = src+n` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  `m+n = n+m` by decide_tac >> pop_assum (fn th => pure_rewrite_tac[th]) >>
  AP_THM_TAC >> AP_TERM_TAC >> irule immutable_padded_read_append
QED

Theorem immutable_runtime_transfers_snapshot:
  !n src dst off s.
  0 < n /\ src+off+32*n < dimword (:256) /\ dst+off+32*n < dimword (:256) ==>
  immutable_transfers F F (n2w src) (n2w dst) n off s =
  write_memory_with_expansion (dst+off)
    (TAKE (32*n) (DROP (src+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) s
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `src+(off+32*n) < dimword (:256) /\ dst+(off+32*n) < dimword (:256)` by decide_tac >>
  simp[immutable_transfers_snoc, immutable_runtime_word_as_write] >>
  Cases_on `n = 0`
  >- simp[immutable_transfers_def] >>
  qpat_x_assum `!src dst off s. _`
    (qspecl_then [`src`,`dst`,`off`,`s`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `src+(off+32*n) = (src+off)+32*n /\
    dst+(off+32*n) = (dst+off)+32*n` by decide_tac >>
  `LENGTH (TAKE (32*n) (DROP (src+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) = 32*n`
    by simp[listTheory.LENGTH_TAKE_EQ] >>
  asm_rewrite_tac[] >>
  `(!at bs s0. (write_memory_with_expansion at bs s0).vs_data_section = s0.vs_data_section)`
    by simp[write_memory_with_expansion_def] >>
  asm_rewrite_tac[] >>
  `dst+(32*n+off) = (dst+off)+32*n` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `32*n+(off+src) = (src+off)+32*n` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `off+src = src+off` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  `32*SUC n = 32*n+32` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  irule immutable_padded_writes_append
QED

Theorem immutable_transfers_copy_map:
  !n off s. (immutable_transfers F ctor a b n off s).vs_immutables = s.vs_immutables
Proof
  Induct >> simp[immutable_transfers_def, immutable_word_transfer_def, mstore_def]
QED

Theorem immutable_transfers_store_map_snoc:
  (immutable_transfers T ctor a b (SUC n) off s).vs_immutables =
  (immutable_transfers T ctor a b n off s).vs_immutables |+
    (w2n (b+n2w (off+32*n)),
     mload (w2n (a+n2w (off+32*n))) (immutable_transfers T ctor a b n off s))
Proof
  simp[immutable_transfers_snoc, immutable_word_transfer_fields, immutable_copy_read_def]
QED

Theorem compile_imm_copy_to_memory_execution:
  compile_imm_copy_to_memory ctor (SOME region) src dst n off st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (ctor ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  mp_tac (SRULE [] (Q.INST [`store` |-> `F`]
    (SPEC_ALL immutable_compile_transfers_execution))) >>
  simp[] >> strip_tac >> qexists_tac `s'` >> simp[immutable_transfers_copy_map]
QED

Theorem compile_imm_store_words_execution:
  compile_imm_store_words (SOME region) src dst n off st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers T T a b n off s).vs_memory /\
    s'.vs_immutables = (immutable_transfers T T a b n off s).vs_immutables
Proof
  strip_tac >>
  mp_tac (SRULE [] (Q.INST [`store` |-> `T`, `ctor` |-> `T`]
    (SPEC_ALL immutable_compile_transfers_execution))) >> simp[]
QED

(* Runtime immutable loads do not consult the constructor region operand. *)
Theorem immutable_runtime_copy_region_irrelevant:
  !n off. compile_imm_copy_to_memory F imm_base src dst n off =
    compile_imm_copy_to_memory F (SOME (Lit 0w)) src dst n off
Proof
  Induct >> simp[compile_imm_copy_to_memory_def, compile_imm_load_word_def]
QED

Theorem immutable_runtime_copy_execution:
  compile_imm_copy_to_memory F imm_base src dst n off st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_transfers F F a b n off s).vs_memory /\
    s'.vs_immutables = s.vs_immutables
Proof
  once_rewrite_tac[immutable_runtime_copy_region_irrelevant] >> strip_tac >>
  mp_tac (SRULE [] (Q.INST [`ctor` |-> `F`, `region` |-> `Lit 0w`]
    (SPEC_ALL compile_imm_copy_to_memory_execution))) >> simp[]
QED

Theorem immutable_compile_memory_snapshot:
  (if store then compile_imm_store_words (SOME region) src dst n off
   else compile_imm_copy_to_memory ctor (SOME region) src dst n off) st = ((),st') /\
  eval_operand src s = SOME (n2w src_addr) /\ eval_operand dst s = SOME (n2w dst_addr) /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt st s /\
  0 < n /\ (store \/ ctor) /\
  src_addr+off+32*n < dimword (:256) /\ dst_addr+off+32*n < dimword (:256) /\
  (dst_addr+off+32*n <= src_addr+off \/ src_addr+off+32*n <= dst_addr+off) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (mcopy (dst_addr+off) (src_addr+off) (32*n) s).vs_memory /\
    s'.vs_immutables = (immutable_transfers store ctor
      (n2w src_addr) (n2w dst_addr) n off s).vs_immutables
Proof
  strip_tac >> (
  drule_all immutable_compile_transfers_execution >> strip_tac >>
  ` (immutable_transfers store ctor (n2w src_addr) (n2w dst_addr) n off s).vs_memory =
    (mcopy (dst_addr+off) (src_addr+off) (32*n) s).vs_memory` by
    (irule immutable_memory_transfers_snapshot >> simp[]) >>
  qexists_tac `s'` >> asm_rewrite_tac[])
QED

Theorem immutable_compile_runtime_snapshot:
  compile_imm_copy_to_memory F imm_base src dst n off st = ((),st') /\
  eval_operand src s = SOME (n2w src_addr) /\ eval_operand dst s = SOME (n2w dst_addr) /\
  fresh_vars_wrt st s /\ 0 < n /\
  src_addr+off+32*n < dimword (:256) /\ dst_addr+off+32*n < dimword (:256) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (write_memory_with_expansion (dst_addr+off)
      (TAKE (32*n) (DROP (src_addr+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) s).vs_memory /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >>
  mp_tac (Q.INST [`a` |-> `n2w src_addr`, `b` |-> `n2w dst_addr`]
    (SPEC_ALL immutable_runtime_copy_execution)) >>
  simp[] >> strip_tac >>
  `immutable_transfers F F (n2w src_addr) (n2w dst_addr) n off s =
   write_memory_with_expansion (dst_addr+off)
     (TAKE (32*n) (DROP (src_addr+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) s` by
    (irule immutable_runtime_transfers_snapshot >> simp[]) >>
  qexists_tac `s'` >> gvs[]
QED

(* A bulk-write boundary gives both the installed bytes and any protected,
   initially allocated slice. It is applied below only after execution. *)
Theorem immutable_snapshot_slices:
  s'.vs_memory = (write_memory_with_expansion at bs s).vs_memory /\
  protected + len <= LENGTH s.vs_memory /\
  (protected + len <= at \/ at + LENGTH bs <= protected) ==>
  TAKE (LENGTH bs) (DROP at s'.vs_memory) = bs /\
  TAKE len (DROP protected s'.vs_memory) = TAKE len (DROP protected s.vs_memory)
Proof
  strip_tac >> (asm_rewrite_tac[] >>
  conj_tac >- irule immutable_write_memory_slice >>
  irule immutable_write_memory_disjoint >> simp[])
QED

Theorem immutable_compile_memory_slices:
  (if store then compile_imm_store_words (SOME region) src dst n off
   else compile_imm_copy_to_memory ctor (SOME region) src dst n off) st = ((),st') /\
  eval_operand src s = SOME (n2w src_addr) /\ eval_operand dst s = SOME (n2w dst_addr) /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt st s /\
  0 < n /\ (store \/ ctor) /\
  src_addr+off+32*n < dimword (:256) /\ dst_addr+off+32*n < dimword (:256) /\
  (dst_addr+off+32*n <= src_addr+off \/ src_addr+off+32*n <= dst_addr+off) /\
  src_addr+off+32*n <= LENGTH s.vs_memory /\
  protected+len <= LENGTH s.vs_memory /\
  (protected+len <= dst_addr+off \/ dst_addr+off+32*n <= protected) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    TAKE (32*n) (DROP (dst_addr+off) s'.vs_memory) =
      TAKE (32*n) (DROP (src_addr+off) s.vs_memory) /\
    TAKE len (DROP protected s'.vs_memory) = TAKE len (DROP protected s.vs_memory) /\
    s'.vs_immutables = (immutable_transfers store ctor
      (n2w src_addr) (n2w dst_addr) n off s).vs_immutables
Proof
  strip_tac >> (
  mp_tac (SPEC_ALL immutable_compile_memory_snapshot) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `LENGTH (TAKE (32*n) (DROP (src_addr+off) s.vs_memory)) = 32*n` by
    simp[listTheory.LENGTH_TAKE_EQ, listTheory.LENGTH_DROP] >>
  `s'.vs_memory = (write_memory_with_expansion (dst_addr+off)
    (TAKE (32*n) (DROP (src_addr+off) s.vs_memory)) s).vs_memory` by
    gvs[mcopy_def, listTheory.TAKE_APPEND1, listTheory.LENGTH_DROP] >>
  drule immutable_snapshot_slices >>
  disch_then (qspecl_then [`protected`,`len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `s'` >> gvs[])
QED

Theorem immutable_compile_runtime_slices:
  compile_imm_copy_to_memory F imm_base src dst n off st = ((),st') /\
  eval_operand src s = SOME (n2w src_addr) /\ eval_operand dst s = SOME (n2w dst_addr) /\
  fresh_vars_wrt st s /\ 0 < n /\
  src_addr+off+32*n < dimword (:256) /\ dst_addr+off+32*n < dimword (:256) /\
  protected+len <= LENGTH s.vs_memory /\
  (protected+len <= dst_addr+off \/ dst_addr+off+32*n <= protected) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    TAKE (32*n) (DROP (dst_addr+off) s'.vs_memory) =
      TAKE (32*n) (DROP (src_addr+off) s.vs_data_section ++ REPLICATE (32*n) 0w) /\
    TAKE len (DROP protected s'.vs_memory) = TAKE len (DROP protected s.vs_memory) /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> (
  drule_all immutable_compile_runtime_snapshot >> strip_tac >>
  `LENGTH (TAKE (32*n) (DROP (src_addr+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) = 32*n`
    by simp[listTheory.LENGTH_TAKE_EQ] >>
  drule immutable_snapshot_slices >>
  disch_then (qspecl_then [`protected`,`len`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `s'` >> gvs[])
QED

(* Zero words execute no instructions, including with arbitrary roots/bases. *)
Theorem immutable_copy_zero_execution:
  compile_imm_copy_to_memory ctor imm_base src dst 0 off st = ((),st) /\
  run_inst_seq (emitted_insts st st) s = OK s
Proof
  simp[compile_imm_copy_to_memory_def, comp_return_def,
       emitted_insts_def, run_inst_seq_def]
QED

Theorem immutable_store_zero_execution:
  compile_imm_store_words imm_base src dst 0 off st = ((),st) /\
  run_inst_seq (emitted_insts st st) s = OK s
Proof
  simp[compile_imm_store_words_def, comp_return_def,
       emitted_insts_def, run_inst_seq_def]
QED

(* Two-word regression covers both real compiler functions, constructor and
   runtime reads, and the sequential (possibly overlapping) ISTORE map. *)
Theorem immutable_compile_two_words_execution:
  (if store then compile_imm_store_words (SOME region) src dst 2 off
   else compile_imm_copy_to_memory ctor (SOME region) src dst 2 off) st = ((),st') /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  ((store \/ ctor) ==> eval_operand region s = SOME 0w) /\ fresh_vars_wrt st s ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (immutable_word_transfer store ctor a b (off+32)
      (immutable_word_transfer store ctor a b off s)).vs_memory /\
    s'.vs_immutables = (immutable_word_transfer store ctor a b (off+32)
      (immutable_word_transfer store ctor a b off s)).vs_immutables
Proof
  strip_tac >>
  mp_tac (Q.INST [`n` |-> `2`] (SPEC_ALL immutable_compile_transfers_execution)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  `2 = SUC (SUC 0)` by decide_tac >>
  pop_assum (fn th => pure_rewrite_tac[th, immutable_transfers_def]) >> simp[]
QED

(* Reject oracle-bearing dependencies at the strict execution boundary. *)
val _ = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn tag => tag = "DISK_THM") oracles then ()
     else raise Fail ("Oracle in immutableCopyExecution." ^ name)
  end) (DB.thms "immutableCopyExecution");

(* Sequential transfers include the effect of overlapping source and destination. *)
val _ = Parse.hide "count";

Theorem immutable_loop_code[local]:
  compile_word_copy_loop_base src dst count LocMemory LocCode T
    (SOME region) sa = (u,sb) /\
  fn_has_code sa sb func ==>
  ?hdr body_lbl cv tv mv sv vv dm dv av nv id0 idh idb bb0 bbh bbb.
    lookup_block sa.cs_current_bb func.fn_blocks = SOME bb0 /\
    isPREFIX
      [mk_inst id0 ASSIGN [Lit 0w] [cv];
       mk_inst (id0+1) JMP [Label hdr] []]
      (DROP (LENGTH sa.cs_current_insts) bb0.bb_instructions) /\
    lookup_block hdr func.fn_blocks = SOME bbh /\
    isPREFIX
      [mk_inst idh EQ [Var cv; count] [tv];
       mk_inst (idh+1) JNZ [Var tv; Label sb.cs_current_bb; Label body_lbl] []]
      bbh.bb_instructions /\
    lookup_block body_lbl func.fn_blocks = SOME bbb /\
    isPREFIX
      [mk_inst idb MUL [Var cv; Lit 32w] [mv];
       mk_inst (idb+1) ADD [src; Var mv] [sv];
       mk_inst (idb+2) MLOAD [Var sv] [vv];
       mk_inst (idb+3) MUL [Var cv; Lit 32w] [dm];
       mk_inst (idb+4) ADD [dst; Var dm] [dv];
       mk_inst (idb+5) ADD [region; Var dv] [av];
       mk_inst (idb+6) ISTORE [Var av; Var vv] [];
       mk_inst (idb+7) ADD [Var cv; Lit 1w] [nv];
       mk_inst (idb+8) ASSIGN [Var nv] [cv];
       mk_inst (idb+9) JMP [Label hdr] []]
      bbb.bb_instructions /\
    LENGTH sb.cs_current_insts = 0 /\
    sb.cs_next_var = sa.cs_next_var + 9 /\
    ALL_DISTINCT [cv;tv;mv;sv;vv;dm;dv;av;nv] /\
    (!x. MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv] ==> not_fresh_at sb x) /\
    (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv])
Proof
  strip_tac >>
  gvs[compile_word_copy_loop_base_def, word_scale_def,
      compile_ptr_load_def, compile_ptr_store_def, compile_imm_store_word_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_label_def, fresh_var_def, emit_inst_def, emit_op_def,
      emit_void_def, fresh_id_def, emit_def, new_block_def,
      not_fresh_at_def, fragExecTheory.fn_has_code_def, fragExecTheory.emitted_blocks_def,
      Excl "isPREFIX"] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM, arithmeticTheory.ADD1, Excl "isPREFIX"] >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MUL [Var cv; Lit 32w] [mv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ EQ _ [tv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [src; Var mv] [sv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ MLOAD _ [vv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [dst; Var dm] [dv]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [region; Var dv] [av]` >>
  qmatch_asmsub_abbrev_tac `mk_inst _ ADD [Var cv; Lit 1w] [nv]` >>
  qexistsl_tac [`fresh_label_output "wcopy_cond" sa.cs_next_label`,
    `fresh_label_output "wcopy_body" (sa.cs_next_label + 1)`,
    `cv`, `tv`, `mv`, `sv`, `vv`, `dm`, `dv`, `av`, `nv`,
    `sa.cs_next_id`, `sa.cs_next_id + 2`, `sa.cs_next_id + 4`] >>
  rpt (goal_assum (drule_at Any)) >>
  once_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, Excl "isPREFIX"] >>
  simp[Abbr `cv`, Abbr `tv`, Abbr `mv`, Abbr `sv`, Abbr `vv`,
       Abbr `dm`, Abbr `dv`, Abbr `av`, Abbr `nv`, fresh_var_distinct] >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem immutable_loop_normalize_store[local]:
  store_copy_normalize s (istore at v t) =
    istore at v (store_copy_normalize s t)
Proof
  simp[store_copy_normalize_def, istore_def, mstore_def]
QED

Theorem immutable_loop_prefix_step[local]:
  store_copy_normalize s t = immutable_transfers T T a b i 0 s ==>
  store_copy_normalize s
    (istore (w2n (b + n2w (32*i)))
       (mload (w2n (a + n2w (32*i))) t) t) =
    immutable_transfers T T a b (SUC i) 0 s
Proof
  strip_tac >>
  simp[immutable_transfers_snoc, immutable_word_transfer_def,
       immutable_copy_read_def, immutable_loop_normalize_store] >>
  qpat_x_assum `_ = _` (SUBST1_TAC o SYM) >>
  simp[store_copy_normalize_def, mload_def]
QED

Theorem immutable_loop_fresh_write[local]:
  fresh_vars_wrt sb t /\ not_fresh_at sb x ==>
  fresh_vars_wrt sb (update_var x v t)
Proof
  simp[fresh_vars_wrt_def, not_fresh_at_def, update_var_def] >>
  metis_tac[]
QED

Theorem immutable_loop_entry_operand[local]:
  fresh_vars_wrt sa s /\ lookup_var x s = SOME w ==>
  not_fresh_at sa x
Proof
  simp[lookup_var_def, fresh_vars_wrt_def, not_fresh_at_def] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  gvs[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem immutable_loop_operand_frame[local]:
  fresh_vars_wrt sa s /\ fresh_vars_wrt sb t /\
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  immutable_operand_frame sa s sb t
Proof
  strip_tac >> simp[immutable_operand_frame_def] >>
  rpt strip_tac >>
  Cases_on `p` >> gvs[eval_operand_def] >>
  drule_all immutable_loop_entry_operand >> metis_tac[]
QED

Definition immutable_loop_frame_def:
  immutable_loop_frame sa sb s a b i t <=>
    store_copy_normalize s t = immutable_transfers T T a b i 0 s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (fresh_vars_wrt sa s ==> fresh_vars_wrt sb t)
End

Theorem immutable_loop_frame_write[local]:
  immutable_loop_frame sa sb s a b i t /\
  (!x. not_fresh_at sa x ==> x <> name) /\ not_fresh_at sb name ==>
  immutable_loop_frame sa sb s a b i (update_var name v t)
Proof
  simp[immutable_loop_frame_def, store_copy_normalize_update,
       store_copy_normalize_jump, store_copy_normalize_idx] >>
  rpt strip_tac
  >- (simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      metis_tac[lookup_var_def]) >>
  irule immutable_loop_fresh_write >> simp[]
QED

Theorem immutable_loop_frame_control[local]:
  (immutable_loop_frame sa sb s a b i (jump_to lbl t) <=>
   immutable_loop_frame sa sb s a b i t) /\
  (immutable_loop_frame sa sb s a b i (t with vs_inst_idx := k) <=>
   immutable_loop_frame sa sb s a b i t)
Proof
  simp[immutable_loop_frame_def, store_copy_normalize_update,
       store_copy_normalize_jump, store_copy_normalize_idx,
       lookup_var_def, fresh_vars_wrt_def, jump_to_def]
QED

Theorem immutable_loop_prefix_shared[local]:
  !i. (immutable_transfers T T a b i 0 s).vs_labels = s.vs_labels /\
      (immutable_transfers T T a b i 0 s).vs_halted = s.vs_halted
Proof
  Induct >> simp[immutable_transfers_snoc, immutable_word_transfer_def,
                immutable_transfers_def, istore_def, mstore_def]
QED

Theorem immutable_loop_frame_shared[local]:
  immutable_loop_frame sa sb s a b i t ==>
  t.vs_labels = s.vs_labels /\ t.vs_halted = s.vs_halted
Proof
  simp[immutable_loop_frame_def] >> strip_tac >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\t. (t.vs_labels,t.vs_halted)`) >>
  simp[store_copy_normalize_def, immutable_loop_prefix_shared]
QED

Theorem immutable_loop_frame_operand[local]:
  immutable_loop_frame sa sb s a b i t /\
  (!x. p = Var x ==> not_fresh_at sa x) ==>
  eval_operand p t = eval_operand p s
Proof
  strip_tac >> drule immutable_loop_frame_shared >> strip_tac >>
  Cases_on `p` >> gvs[eval_operand_def, immutable_loop_frame_def]
QED

Theorem immutable_loop_test_path[local]:
  ~q.vs_halted /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; count] [tv]]
    (DROP q.vs_inst_idx bb.bb_instructions) /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  eval_operand count q = SOME (n2w n) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  not_fresh_at sb tv /\ i <= n /\ n < dimword (:256) ==>
  ?t. gas_marked_path F ctx func q 0 (OK t) /\
      immutable_loop_frame sa sb s a b i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      eval_operand (Var tv) t = SOME (if i = n then 1w else 0w) /\
      ~t.vs_halted /\ t.vs_current_bb = q.vs_current_bb /\
      t.vs_inst_idx = q.vs_inst_idx + 1
Proof
  strip_tac >>
  `i < dimword (:256)` by decide_tac >>
  `bool_to_word (n2w i = n2w n : bytes32) =
   (if i = n then 1w else 0w)` by
    (Cases_on `i = n` >> simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD,
                              bool_to_word_def]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code _` >>
  `run_inst_seq code q =
   OK (update_var tv (if i = n then 1w else 0w) q)` by
    simp[Abbr `code`, run_inst_seq_def, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``EQ``, exec_pure2_def] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `(update_var tv (if i = n then 1w else 0w) q)
                with vs_inst_idx := q.vs_inst_idx + 1` >>
  conj_tac >- simp[gas_marked_path_def] >>
  conj_tac >- (simp[immutable_loop_frame_control] >>
               irule immutable_loop_frame_write >> metis_tac[]) >>
  gvs[eval_operand_def, update_var_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem immutable_loop_load_prefix[local]:
  eval_operand src q = SOME a /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  cv <> mv /\ mv <> sv /\ src <> Var mv ==>
  run_inst_seq
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv]] q =
  OK (update_var vv (mload (w2n (a+n2w (32*i))) q)
        (update_var sv (a+n2w (32*i)) (update_var mv (n2w (32*i)) q)))
Proof
  strip_tac >>
  `n2w i * 32w = (n2w (32*i):bytes32)` by
    simp[GSYM wordsTheory.word_mul_n2w, wordsTheory.WORD_MULT_COMM] >>
  qabbrev_tac `q1 = update_var mv (n2w (32*i)) q` >>
  qabbrev_tac `q2 = update_var sv (a+n2w (32*i)) q1` >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [mv]) q = OK q1` by
    simp[Abbr `q1`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``MUL``,
         exec_pure2_def, eval_operand_lit] >>
  `eval_operand src q1 = SOME a /\
   eval_operand (Var mv) q1 = SOME (n2w (32*i))` by
    simp[Abbr `q1`, slot_copy_operand_update] >>
  `step_inst_base (mk_inst (id+1) ADD [src; Var mv] [sv]) q1 = OK q2` by
    simp[Abbr `q2`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ADD``,
         exec_pure2_def] >>
  `eval_operand (Var sv) q2 = SOME (a+n2w (32*i))` by
    simp[Abbr `q2`, slot_copy_operand_update] >>
  `mload (w2n (a+n2w (32*i))) q2 = mload (w2n (a+n2w (32*i))) q` by
    simp[Abbr `q2`, Abbr `q1`, immutable_word_istore_operand_frame, mload_def, update_var_def] >>
  `step_inst_base (mk_inst (id+2) MLOAD [Var sv] [vv]) q2 =
     OK (update_var vv (mload (w2n (a+n2w (32*i))) q) q2)` by
    simp[mk_inst_def, stepInstBaseLib.simp_opcode_clause ``MLOAD``, exec_read1_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def] >>
  simp[Once run_inst_seq_def, Abbr `q2`, Abbr `q1`]
QED

Theorem immutable_loop_store_suffix[local]:
  eval_operand dst q = SOME b /\ eval_operand region q = SOME 0w /\
  eval_operand (Var vv) q = SOME value /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  ALL_DISTINCT [cv;vv;dm;dv;av;nv] /\
  (!x. MEM x [dm;dv;av] ==> dst <> Var x /\ region <> Var x) ==>
  run_inst_seq
    [mk_inst id MUL [Var cv; Lit 32w] [dm];
     mk_inst (id+1) ADD [dst; Var dm] [dv];
     mk_inst (id+2) ADD [region; Var dv] [av];
     mk_inst (id+3) ISTORE [Var av; Var vv] [];
     mk_inst (id+4) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+5) ASSIGN [Var nv] [cv]] q =
  OK (update_var cv (n2w (SUC i)) (update_var nv (n2w (SUC i))
      (istore (w2n (b+n2w (32*i))) value
        (update_var av (b+n2w (32*i))
          (update_var dv (b+n2w (32*i)) (update_var dm (n2w (32*i)) q))))))
Proof
  strip_tac >> fs[listTheory.ALL_DISTINCT, listTheory.MEM,
                  DISJ_IMP_THM, FORALL_AND_THM] >>
  `n2w i * 32w = (n2w (32*i):bytes32)` by
    simp[GSYM wordsTheory.word_mul_n2w, wordsTheory.WORD_MULT_COMM] >>
  qabbrev_tac `q1 = update_var dm (n2w (32*i)) q` >>
  qabbrev_tac `q2 = update_var dv (b+n2w (32*i)) q1` >>
  qabbrev_tac `q3 = update_var av (b+n2w (32*i)) q2` >>
  qabbrev_tac `q4 = istore (w2n (b+n2w (32*i))) value q3` >>
  qabbrev_tac `q5 = update_var nv (n2w (SUC i)) q4` >>
  `step_inst_base (mk_inst id MUL [Var cv; Lit 32w] [dm]) q = OK q1` by
    simp[Abbr `q1`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``MUL``,
         exec_pure2_def, eval_operand_lit] >>
  `eval_operand dst q1 = SOME b /\
   eval_operand (Var dm) q1 = SOME (n2w (32*i))` by
    simp[Abbr `q1`, slot_copy_operand_update] >>
  `step_inst_base (mk_inst (id+1) ADD [dst; Var dm] [dv]) q1 = OK q2` by
    simp[Abbr `q2`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ADD``, exec_pure2_def] >>
  `eval_operand region q2 = SOME 0w /\
   eval_operand (Var dv) q2 = SOME (b+n2w (32*i))` by
    simp[Abbr `q2`, Abbr `q1`, slot_copy_operand_update] >>
  `step_inst_base (mk_inst (id+2) ADD [region; Var dv] [av]) q2 = OK q3` by
    simp[Abbr `q3`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ADD``,
         exec_pure2_def, wordsTheory.WORD_ADD_0] >>
  `eval_operand (Var av) q3 = SOME (b+n2w (32*i)) /\
   eval_operand (Var vv) q3 = SOME value` by
    simp[Abbr `q3`, Abbr `q2`, Abbr `q1`, slot_copy_operand_update] >>
  `step_inst_base (mk_inst (id+3) ISTORE [Var av; Var vv] []) q3 = OK q4` by
    simp[Abbr `q4`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ISTORE``] >>
  `eval_operand (Var cv) q4 = SOME (n2w i)` by
    simp[Abbr `q4`, Abbr `q3`, Abbr `q2`, Abbr `q1`,
         immutable_word_istore_operand_frame, mload_def, update_var_def, slot_copy_operand_update] >>
  `n2w i + 1w = (n2w (SUC i):bytes32)` by simp[wordsTheory.n2w_SUC] >>
  `step_inst_base (mk_inst (id+4) ADD [Var cv; Lit 1w] [nv]) q4 = OK q5` by
    simp[Abbr `q5`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ADD``,
         exec_pure2_def, eval_operand_lit] >>
  `step_inst_base (mk_inst (id+5) ASSIGN [Var nv] [cv]) q5 =
    OK (update_var cv (n2w (SUC i)) q5)` by
    simp[Abbr `q5`, mk_inst_def, stepInstBaseLib.simp_opcode_clause ``ASSIGN``,
         slot_copy_operand_update] >>
  ntac 6 (simp[Once run_inst_seq_def]) >>
  simp[run_inst_seq_def, Abbr `q5`, Abbr `q4`, Abbr `q3`, Abbr `q2`, Abbr `q1`]
QED

Theorem immutable_loop_body_run[local]:
  eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
  eval_operand region q = SOME 0w /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x) ==>
  run_inst_seq
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (id+4) ADD [dst; Var dm] [dv];
     mk_inst (id+5) ADD [region; Var dv] [av];
     mk_inst (id+6) ISTORE [Var av; Var vv] [];
     mk_inst (id+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+8) ASSIGN [Var nv] [cv]] q =
  OK (update_var cv (n2w (SUC i)) (update_var nv (n2w (SUC i))
        (istore (w2n (b+n2w (32*i))) (mload (w2n (a+n2w (32*i))) q)
          (update_var av (b+n2w (32*i))
            (update_var dv (b+n2w (32*i)) (update_var dm (n2w (32*i))
              (update_var vv (mload (w2n (a+n2w (32*i))) q)
                (update_var sv (a+n2w (32*i)) (update_var mv (n2w (32*i)) q)))))))))
Proof
  strip_tac >>
  `cv <> mv /\ mv <> sv /\ src <> Var mv` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[listTheory.MEM]) >>
  drule_all immutable_loop_load_prefix >>
  disch_then (qspecl_then [`vv`, `id`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code1 q = OK mid` >>
  `eval_operand dst mid = SOME b /\ eval_operand region mid = SOME 0w /\
   eval_operand (Var vv) mid = SOME (mload (w2n (a+n2w (32*i))) q) /\
   eval_operand (Var cv) mid = SOME (n2w i)` by
    (fs[listTheory.ALL_DISTINCT, listTheory.MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
     simp[Abbr `mid`, slot_copy_operand_update]) >>
  `ALL_DISTINCT [cv;vv;dm;dv;av;nv] /\
   (!x. MEM x [dm;dv;av] ==> dst <> Var x /\ region <> Var x)` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[listTheory.MEM]) >>
  drule_all immutable_loop_store_suffix >>
  disch_then (qspec_then `id+3` mp_tac) >>
  simp[arithmeticTheory.ADD_ASSOC] >> strip_tac >>
  qpat_assum `run_inst_seq code1 q = OK mid` (mp_tac o MATCH_MP run_inst_seq_append) >>
  disch_then (qspec_then
    `[mk_inst (id+3) MUL [Var cv; Lit 32w] [dm];
      mk_inst (id+4) ADD [dst; Var dm] [dv];
      mk_inst (id+5) ADD [region; Var dv] [av];
      mk_inst (id+6) ISTORE [Var av; Var vv] [];
      mk_inst (id+7) ADD [Var cv; Lit 1w] [nv];
      mk_inst (id+8) ASSIGN [Var nv] [cv]]` mp_tac) >>
  simp[Abbr `code1`, Abbr `mid`]
QED

Theorem immutable_loop_frame_store[local]:
  immutable_loop_frame sa sb s a b i q ==>
  immutable_loop_frame sa sb s a b (SUC i)
    (istore (w2n (b+n2w (32*i))) (mload (w2n (a+n2w (32*i))) q) q)
Proof
  strip_tac >> simp[immutable_loop_frame_def] >>
  conj_tac >- (irule immutable_loop_prefix_step >>
               gvs[immutable_loop_frame_def]) >>
  gvs[immutable_loop_frame_def, istore_def, mstore_def,
      lookup_var_def, fresh_vars_wrt_def]
QED

Theorem immutable_loop_body_frame[local]:
  immutable_loop_frame sa sb s a b i q /\
  (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;av;nv]) ==>
  immutable_loop_frame sa sb s a b (SUC i)
    (update_var cv (n2w (SUC i)) (update_var nv (n2w (SUC i))
      (istore (w2n (b+n2w (32*i))) (mload (w2n (a+n2w (32*i))) q)
        (update_var av (b+n2w (32*i))
          (update_var dv (b+n2w (32*i)) (update_var dm (n2w (32*i))
            (update_var vv (mload (w2n (a+n2w (32*i))) q)
              (update_var sv (a+n2w (32*i)) (update_var mv (n2w (32*i)) q)))))))))
Proof
  strip_tac >>
  ntac 2 (irule immutable_loop_frame_write >>
    conj_tac >- metis_tac[listTheory.MEM] >>
    conj_tac >- metis_tac[listTheory.MEM]) >>
  qmatch_goalsub_abbrev_tac `istore _ _ p` >>
  `immutable_loop_frame sa sb s a b i p` by
    (simp_tac bool_ss [Abbr `p`] >>
     ntac 6 (irule immutable_loop_frame_write >>
       conj_tac >- metis_tac[listTheory.MEM] >>
       conj_tac >- metis_tac[listTheory.MEM]) >> simp[]) >>
  drule immutable_loop_frame_store >>
  simp[Abbr `p`, mload_def, update_var_def]
QED

Theorem immutable_loop_body_path[local]:
  ~q.vs_halted /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX
    [mk_inst id MUL [Var cv; Lit 32w] [mv];
     mk_inst (id+1) ADD [src; Var mv] [sv];
     mk_inst (id+2) MLOAD [Var sv] [vv];
     mk_inst (id+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (id+4) ADD [dst; Var dm] [dv];
     mk_inst (id+5) ADD [region; Var dv] [av];
     mk_inst (id+6) ISTORE [Var av; Var vv] [];
     mk_inst (id+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (id+8) ASSIGN [Var nv] [cv]]
    (DROP q.vs_inst_idx bb.bb_instructions) /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
  eval_operand region q = SOME 0w /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x /\ not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;av;nv]) ==>
  ?t. gas_marked_path F ctx func q 0 (OK t) /\
      immutable_loop_frame sa sb s a b (SUC i) t /\
      eval_operand (Var cv) t = SOME (n2w (SUC i)) /\
      ~t.vs_halted /\ t.vs_current_bb = q.vs_current_bb /\
      t.vs_inst_idx = q.vs_inst_idx + 9
Proof
  strip_tac >>
  `!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
       src <> Var x /\ dst <> Var x /\ region <> Var x` by metis_tac[] >>
  drule_all immutable_loop_body_run >>
  disch_then (qspec_then `id` mp_tac) >>
  strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq code q = OK result` >>
  `immutable_loop_frame sa sb s a b (SUC i) result` by
    (simp_tac bool_ss [Abbr `result`] >>
     irule immutable_loop_body_frame >>
     metis_tac[]) >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[Abbr `code`, mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qexists_tac `result with vs_inst_idx := q.vs_inst_idx + 9` >>
  conj_tac >- simp[gas_marked_path_def] >>
  conj_tac >- simp[immutable_loop_frame_control] >>
  conj_tac >- simp[Abbr `result`, eval_operand_def, lookup_var_def,
                    update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[Abbr `result`, update_var_def, istore_def, mstore_def]
QED

Theorem immutable_loop_header_path[local]:
  ~q.vs_halted /\ q.vs_inst_idx = 0 /\
  lookup_block q.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv; count] [tv];
    mk_inst (id+1) JNZ [Var tv; Label exit; Label body_lbl] []]
    bb.bb_instructions /\
  immutable_loop_frame sa sb s a b i q /\
  eval_operand (Var cv) q = SOME (n2w i) /\
  eval_operand count q = SOME (n2w n) /\
  cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
  not_fresh_at sb tv /\ i <= n /\ n < dimword (:256) ==>
  ?r. gas_marked_path F ctx func q 0 (OK r) /\
      immutable_loop_frame sa sb s a b i r /\
      eval_operand (Var cv) r = SOME (n2w i) /\
      ~r.vs_halted /\ r.vs_inst_idx = 0 /\
      r.vs_current_bb = (if i = n then exit else body_lbl)
Proof
  strip_tac >>
  qpat_assum `isPREFIX _ _`
    (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  `isPREFIX [mk_inst id EQ [Var cv; count] [tv]]
    (DROP q.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all immutable_loop_test_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `get_instruction bb t.vs_inst_idx =
   SOME (mk_inst (id+1) JNZ [Var tv; Label exit; Label body_lbl] [])` by
    simp[get_instruction_def, listTheory.EL_APPEND_EQN] >>
  `lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by metis_tac[] >>
  drule_all place_copy_branch_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `gas_marked_path F ctx func t 0
    (OK (jump_to (if i = n then exit else body_lbl) t))` by
    (Cases_on `i = n` >> fs[]) >>
  qexists_tac `jump_to (if i = n then exit else body_lbl) t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- simp[immutable_loop_frame_control] >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[jump_to_def, eval_operand_def, lookup_var_def]
QED

Theorem immutable_loop_iterate[local]:
  lookup_block hdr func.fn_blocks = SOME bbh /\
  isPREFIX [mk_inst idh EQ [Var cv; count] [tv];
    mk_inst (idh+1) JNZ [Var tv; Label exit; Label body_lbl] []]
    bbh.bb_instructions /\
  lookup_block body_lbl func.fn_blocks = SOME bbb /\
  isPREFIX
    [mk_inst idb MUL [Var cv; Lit 32w] [mv];
     mk_inst (idb+1) ADD [src; Var mv] [sv];
     mk_inst (idb+2) MLOAD [Var sv] [vv];
     mk_inst (idb+3) MUL [Var cv; Lit 32w] [dm];
     mk_inst (idb+4) ADD [dst; Var dm] [dv];
     mk_inst (idb+5) ADD [region; Var dv] [av];
     mk_inst (idb+6) ISTORE [Var av; Var vv] [];
     mk_inst (idb+7) ADD [Var cv; Lit 1w] [nv];
     mk_inst (idb+8) ASSIGN [Var nv] [cv];
     mk_inst (idb+9) JMP [Label hdr] []] bbb.bb_instructions /\
  ALL_DISTINCT [cv;tv;mv;sv;vv;dm;dv;av;nv] /\
  (!x. MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv] ==> not_fresh_at sb x) /\
  (!x. not_fresh_at sa x ==> ~MEM x [cv;tv;mv;sv;vv;dm;dv;av;nv]) /\
  (!x. src = Var x \/ dst = Var x \/ count = Var x \/ region = Var x ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand count s = SOME (n2w n) /\ eval_operand region s = SOME 0w /\
  n < dimword (:256) /\ k <= n /\
  immutable_loop_frame sa sb s a b k r /\
  eval_operand (Var cv) r = SOME (n2w k) /\
  ~r.vs_halted /\ r.vs_current_bb = hdr /\ r.vs_inst_idx = 0 ==>
  ?t. gas_marked_path F ctx func r 0 (OK t) /\
      immutable_loop_frame sa sb s a b n t /\
      eval_operand (Var cv) t = SOME (n2w n) /\
      ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0
Proof
  strip_tac >>
  qabbrev_tac `Inv = \j q. immutable_loop_frame sa sb s a b j q /\
    eval_operand (Var cv) q = SOME (n2w j)` >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\ Inv n t /\
       ~t.vs_halted /\ t.vs_current_bb = exit /\ t.vs_inst_idx = 0`
    suffices_by (simp[Abbr `Inv`] >> metis_tac[]) >>
  irule place_copy_iterate_path >> simp[] >>
  reverse conj_tac
  >- (qexistsl_tac [`k`, `n-k`] >> simp[Abbr `Inv`]) >>
  qexists_tac `body_lbl` >> simp[] >>
  conj_tac >- suspend "body" >> suspend "header"
QED

Resume immutable_loop_iterate[body]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand src q = SOME a /\ eval_operand dst q = SOME b /\
   eval_operand region q = SOME 0w` by
    (conj_tac >- (drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
       disch_then (qspec_then `src` mp_tac) >> simp[] >> metis_tac[]) >>
     conj_tac >- (drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
       disch_then (qspec_then `dst` mp_tac) >> simp[] >> metis_tac[]) >>
     drule_at (Pat `immutable_loop_frame _ _ _ _ _ j q`)
        immutable_loop_frame_operand >>
     disch_then (qspec_then `region` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_assum `isPREFIX (_::_::_::_::_::_::_::_::_::_::[]) _`
    (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
  qmatch_asmsub_abbrev_tac `isPREFIX code bbb.bb_instructions` >>
  `isPREFIX (TAKE 9 code) (DROP q.vs_inst_idx bbb.bb_instructions)` by
    simp[Abbr `code`] >>
  `ALL_DISTINCT [cv;mv;sv;vv;dm;dv;av;nv] /\
   (!x. MEM x [cv;mv;sv;vv;dm;dv;av;nv] ==>
     src <> Var x /\ dst <> Var x /\ region <> Var x /\ not_fresh_at sb x) /\
   (!x. not_fresh_at sa x ==> ~MEM x [cv;mv;sv;vv;dm;dv;av;nv])` by
    (fs[listTheory.ALL_DISTINCT, listTheory.MEM] >> metis_tac[]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbb` by simp[] >>
  qunabbrev_tac `code` >>
  qpat_x_assum `isPREFIX (TAKE 9 _) _`
    (assume_tac o SIMP_RULE (srw_ss()) [listTheory.TAKE_def, Excl "isPREFIX"]) >>
  drule_all immutable_loop_body_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >>
     qexists_tac `idb+9` >>
     simp[get_instruction_def, listTheory.EL_APPEND_EQN]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  qpat_x_assum `eval_operand (Var cv) t = _`
    (assume_tac o REWRITE_RULE [eval_operand_def, lookup_var_def]) >>
  simp[immutable_loop_frame_control, jump_to_def, eval_operand_def,
       lookup_var_def, GSYM arithmeticTheory.ADD1]
QED

Resume immutable_loop_iterate[header]:
  qunabbrev_tac `Inv` >> BETA_TAC >> rpt gen_tac >> strip_tac >>
  `eval_operand count q = SOME (n2w n)` by
    (drule immutable_loop_frame_operand >>
     disch_then (qspec_then `count` mp_tac) >> simp[] >> metis_tac[]) >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
   not_fresh_at sb tv` by
    (fs[listTheory.ALL_DISTINCT] >> metis_tac[listTheory.MEM]) >>
  `lookup_block q.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  drule_all immutable_loop_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `r'` >> simp[]
QED

Finalise immutable_loop_iterate

Theorem compile_imm_store_loop_path:
  compile_word_copy_loop_base src dst count LocMemory LocCode T
    (SOME region) sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ count = Var x \/ region = Var x ==>
       not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand count s = SOME (n2w n) /\
  eval_operand region s = SOME 0w /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b n 0 s /\
      (fresh_vars_wrt sa s ==> immutable_operand_frame sa s sb t) /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all immutable_loop_code >> strip_tac >>
  `?r. gas_marked_path F ctx func s 0 (OK r) /\
       immutable_loop_frame sa sb s a b 0 r /\
       eval_operand (Var cv) r = SOME 0w /\ ~r.vs_halted /\
       r.vs_current_bb = hdr /\ r.vs_inst_idx = 0` by suspend "init" >>
  `?t. gas_marked_path F ctx func r 0 (OK t) /\
       immutable_loop_frame sa sb s a b n t /\
       eval_operand (Var cv) t = SOME (n2w n) /\
       ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = 0` by
    (`eval_operand (Var cv) r = SOME (n2w 0) /\ 0 <= n` by simp[] >>
     drule_all immutable_loop_iterate >>
     disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  qexists_tac `t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[immutable_loop_frame_shared] >>
  fs[immutable_loop_frame_def, store_copy_normalize_def] >>
  metis_tac[immutable_loop_operand_frame]
QED

Resume compile_imm_store_loop_path[init]:
  `immutable_loop_frame sa sb s a b 0 s` by
    (simp[immutable_loop_frame_def, immutable_transfers_def, fresh_vars_wrt_def,
          store_copy_normalize_def, venom_state_component_equality]) >>
  `!x. not_fresh_at sa x ==> x <> cv` by metis_tac[listTheory.MEM] >>
  `not_fresh_at sb cv` by metis_tac[listTheory.MEM] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bb0` by simp[] >>
  `isPREFIX [mk_inst id0 ASSIGN [Lit 0w] [cv]]
    (DROP s.vs_inst_idx bb0.bb_instructions)` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
     simp[]) >>
  `run_inst_seq [mk_inst id0 ASSIGN [Lit 0w] [cv]] s =
    OK (update_var cv 0w s)` by
    simp[run_inst_seq_def, mk_inst_def,
         stepInstBaseLib.simp_opcode_clause ``ASSIGN``, eval_operand_lit] >>
  drule tuple_run_inst_seq_gas_path >>
  disch_then drule >> disch_then drule >>
  simp[mk_inst_def, is_terminator_def] >>
  disch_then (qspec_then `ctx` mp_tac) >> strip_tac >>
  qabbrev_tac `t = update_var cv 0w s with
    vs_inst_idx := LENGTH sa.cs_current_insts + 1` >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    simp[gas_marked_path_def, Abbr `t`] >>
  `~t.vs_halted /\ t.vs_current_bb = sa.cs_current_bb /\
   t.vs_inst_idx = LENGTH sa.cs_current_insts + 1` by
    simp[Abbr `t`, update_var_def] >>
  `get_instruction bb0 t.vs_inst_idx =
    SOME (mk_inst (id0+1) JMP [Label hdr] [])` by
    (qpat_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
       (mp_then Any strip_assume_tac fragGasSeqAbortTheory.instruction_prefix_cursor) >>
     drule fragGasSeqAbortTheory.instruction_prefix_cursor >> simp[arithmeticTheory.ADD1]) >>
  `gas_marked_path F ctx func t 0 (OK (jump_to hdr t))` by
    (irule place_copy_jump_path >> simp[] >> metis_tac[]) >>
  qexists_tac `jump_to hdr t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- (simp[immutable_loop_frame_control, Abbr `t`] >>
               irule immutable_loop_frame_write >> simp[] >> metis_tac[]) >>
  simp[Abbr `t`, jump_to_def, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Finalise compile_imm_store_loop_path

Theorem immutable_transfers_normalize[local]:
  !n off t.
  store_copy_normalize s (immutable_transfers T T a b n off t) =
    immutable_transfers T T a b n off (store_copy_normalize s t)
Proof
  Induct >> simp[immutable_transfers_def] >>
  simp[immutable_word_transfer_def, immutable_copy_read_def,
       immutable_loop_normalize_store, store_copy_normalize_def,
       mload_def, istore_def, mstore_def]
QED

Theorem compile_store_immutable_bytestring_path:
  compile_store_immutable_bytestring (SOME region) src dst sa = ((),sb) /\
  fn_has_code sa sb func /\ len + 63 < dimword (:256) /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  eval_operand region s = SOME 0w /\ mload (w2n a) s = n2w len /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (t with <|vs_vars := s.vs_vars;
                vs_current_bb := s.vs_current_bb;
                vs_prev_bb := s.vs_prev_bb;
                vs_inst_idx := s.vs_inst_idx|>) =
        immutable_transfers T T a b (1 + word_size len) 0 s /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `compile_bytestring_word_count src sa` >>
  rename1 `compile_bytestring_word_count src sa = (wc,sm)` >>
  Cases_on `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    (SOME region) sm` >>
  rename1 `compile_word_copy_loop_base src dst wc LocMemory LocCode T
    (SOME region) sm = (u,sn)` >>
  `sn = sb` by
    fs[compile_store_immutable_bytestring_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, pairTheory.UNCURRY] >> gvs[] >>
  drule bytestring_word_count_shape >> strip_tac >>
  `cs_extends sa sm` by
    (irule cs_extends_same_block >> fs[same_blocks_def] >> simp[]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`src`, `dst`, `wc`, `LocMemory`, `LocCode`, `T`,
                      `SOME region`, `sm`] ci_mono_word_copy) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  `!x. wc = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[compile_bytestring_word_count_def, emit_op_def,
          comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     strip_tac >> gvs[not_fresh_at_def]) >>
  `1 + word_size len < dimword (:256)` by
    (`(len + 31) DIV 32 <= len + 31` by simp[arithmeticTheory.DIV_LESS_EQ] >>
     fs[vfmConstantsTheory.word_size_def] >> decide_tac) >>
  drule_all bytestring_word_count_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path F ctx func s 0 (OK r)` >>
  `r.vs_labels = s.vs_labels /\ store_copy_normalize s r = s` by
    (fs[venom_state_component_equality, store_copy_normalize_def]) >>
  `!p. (!x. p = Var x ==> not_fresh_at sa x) ==>
       eval_operand p r = eval_operand p s` by
    (Cases >> simp[eval_operand_def]) >>
  `eval_operand src r = SOME a /\ eval_operand dst r = SOME b /\
   eval_operand region r = SOME 0w` by metis_tac[] >>
  `!x. src = Var x \/ dst = Var x \/ wc = Var x \/ region = Var x ==>
       not_fresh_at sm x` by metis_tac[] >>
  drule_all compile_imm_store_loop_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >>
  conj_tac >- (drule_all gas_marked_path_then >> simp[]) >>
  conj_tac >- metis_tac[] >>
  simp[] >>
  qpat_x_assum `(t with <|vs_vars := r.vs_vars; vs_current_bb := r.vs_current_bb;
      vs_prev_bb := r.vs_prev_bb; vs_inst_idx := r.vs_inst_idx|>) = _`
    (mp_tac o AP_TERM ``store_copy_normalize s``) >>
  simp[immutable_transfers_normalize, store_copy_normalize_def]
QED

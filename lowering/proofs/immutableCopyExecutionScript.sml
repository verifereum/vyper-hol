Theory immutableCopyExecution
Ancestors
  immutableWordExecution immutableMemoryFrame emitHelperProps
  context compileEnv emitHelper exprLoweringProps venomState venomExecSemantics venomInst
  mmCopyEquiv venomMemProps mmInterval

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
  simp[emitted_insts_def, run_inst_seq_def, listTheory.DROP_APPEND,
       mk_inst_def, step_inst_base_def, exec_pure2_def,
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
   >- (gvs[] >> simp[run_inst_seq_def, mk_inst_def, step_inst_base_def,
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
  simp[emitted_insts_def, listTheory.DROP_APPEND, same_blocks_def,
       run_inst_seq_def, mk_inst_def, step_inst_base_def, exec_write2_def,
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
  qexists_tac `s'` >> simp[] >>
  irule immutable_memory_transfers_snapshot >> simp[])
QED

Theorem immutable_compile_runtime_snapshot:
  compile_imm_copy_to_memory F (SOME region) src dst n off st = ((),st') /\
  eval_operand src s = SOME (n2w src_addr) /\ eval_operand dst s = SOME (n2w dst_addr) /\
  fresh_vars_wrt st s /\ 0 < n /\
  src_addr+off+32*n < dimword (:256) /\ dst_addr+off+32*n < dimword (:256) ==>
  ?s'. immutable_execution_frame st s st' s' /\
    s'.vs_memory = (write_memory_with_expansion (dst_addr+off)
      (TAKE (32*n) (DROP (src_addr+off) s.vs_data_section ++ REPLICATE (32*n) 0w)) s).vs_memory /\
    s'.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all compile_imm_copy_to_memory_execution >> strip_tac >>
  qexists_tac `s'` >> simp[] >>
  drule_all immutable_runtime_transfers_snapshot >> simp[]
QED

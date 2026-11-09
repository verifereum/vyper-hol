(* Allocation ownership adapters for the continuing event encoder. *)
Theory stmtSimLogStoreEncode
Ancestors
  stmtSimLogStoreFresh stmtSimLogAllocate stmtSimLogEncodeFrame
  abiDecoderFrame abiBuiltinAllocation abiEncoderInput abiEncoderProps abiEncoderCounters
  localPtrsProps exprLoweringProps context compileEnv loweringStateRelDefs emitHelper emitHelperProps abiDecoderReentry
  venomExecSemantics venomState venomInst finite_map words list arithmetic

Theorem log_buffer_local_footprint[local]:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    abi_footprint_disjoint lo sz [(p,cap)]
Proof
  rpt strip_tac >> simp[abi_footprint_disjoint_def] >>
  drule_all log_buffer_clear_of_locals >> decide_tac
QED

Theorem log_buffer_immutable_footprint[local]:
  compile_alloc_buffer cap sa = (buf,sb) /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func ce cx es s /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (p,cap) ==>
  ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) [(p,cap)]
Proof
  rpt strip_tac >> simp[abi_footprint_disjoint_def] >>
  drule_all log_buffer_clear_of_immutable >> simp[]
QED

Theorem log_tuple_cursor_footprints[local]:
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_operands = [Lit (n2w 32)] /\
  inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)] /\
  local_ptrs_reserved ce st /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srccap) /\
  FLOOKUP s.vs_allocas dstid = SOME (db,outcap) /\
  srcid <> inst.inst_id /\ dstid <> inst.inst_id /\ cap <= srccap ==>
  ?p. ((FLOOKUP s.vs_allocas inst.inst_id = NONE /\ p = s.vs_alloca_next) \/
       FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    (!name lo sz. local_region ce es.scopes s name lo sz ==>
      abi_footprint_disjoint lo sz [(p,32)]) /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      abi_footprint_disjoint off (type_memory_size tv) [(p,32)])
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_cursor_ownership >>
  disch_then (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `p+32 <= sb \/ sb+srccap <= p` by
    (qpat_assum `!id b sz. _` (qspec_then `srcid` mp_tac) >> simp[]) >>
  `p+32 <= db \/ db+outcap <= p` by
    (qpat_assum `!id b sz. _` (qspec_then `dstid` mp_tac) >> simp[]) >>
  qexists_tac `p` >> simp[abi_footprint_disjoint_def] >>
  rpt conj_tac >> rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem log_output_buffer_shape:
  compile_alloc_buffer cap st = (buf,prepared) ==>
  prepared.cs_next_id = st.cs_next_id + 1 /\
  prepared.cs_next_var = st.cs_next_var + 1 /\
  abi_decoder_operand_live prepared.cs_next_var buf.buf_operand
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `Var _ = _` (SUBST1_TAC o SYM) >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       ASCIInumbersTheory.toString_inj]
QED

Theorem log_reserved_operand_live[local]:
  local_ptrs_reserved ce st /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
  abi_decoder_operand_live st.cs_next_var (Var v)
Proof
  simp[local_ptrs_reserved_def, abi_decoder_operand_live_def,
       abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]
QED

Theorem log_two_footprints[local]:
  abi_footprint_disjoint lo sz [a] /\ abi_footprint_disjoint lo sz [b] ==>
  abi_footprint_disjoint lo sz [a;b]
Proof
  simp[abi_footprint_disjoint_def] >> metis_tac[]
QED

Theorem log_tuple_encoder_owned[local]:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  FLOOKUP initial.vs_allocas st.cs_next_id = SOME (db,outcap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  db+outcap < dimword (:256) /\ (sb+cap <= db \/ db+outcap <= sb) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst.buf_operand initial = SOME (n2w db) /\
  abi_decoder_operand_live prepared.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual. run_inst_seq (emitted_insts prepared end_st) initial = OK actual /\
    inst_extends prepared end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live prepared.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_output_buffer_shape >> strip_tac >>
  `local_ptrs_reserved ce prepared` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `!name entry v sz. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) ==>
    abi_decoder_operand_live prepared.cs_next_var (Var v)` by
    (rpt strip_tac >> drule_all log_reserved_operand_live >> simp[]) >>
  `!x. ce.ce_imm_alloca = SOME (Var x) ==>
     abi_decoder_operand_live prepared.cs_next_var (Var x)` by
    (qpat_x_assum `local_ptrs_reserved ce prepared` mp_tac >>
     simp[local_ptrs_reserved_def, abi_decoder_operand_live_def,
          abi_decoder_older_vars_def, not_fresh_at_def] >> metis_tac[]) >>
  `!name lo sz. local_region ce es.scopes initial name lo sz ==>
    abi_footprint_disjoint lo sz [(db,outcap)]` by
    (rpt strip_tac >> drule_all log_buffer_local_footprint >> simp[]) >>
  `ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    abi_footprint_disjoint off (type_memory_size tv) [(db,outcap)]` by
    (rpt strip_tac >> drule_all log_buffer_immutable_footprint >> simp[]) >>
  `sb+cap < dimword (:256)` by decide_tac >>
  qpat_x_assum `(?n. _) \/ (?infos. _)` strip_assume_tac
  >- (drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`)
        log_scalar_tuple_continue >>
      disch_then irule >> gnvs[] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`cap`,`outcap`,`sb`] >> simp[] >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "dynamic"
QED

Resume log_tuple_encoder_owned[dynamic]:
  qpat_x_assum `ei = AbiComplex infos` SUBST_ALL_TAC >>
  drule_all log_encoder_cursor_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w 32)] /\
   inst.inst_outputs = [STRING #"%" (toString prepared.cs_next_var)] /\
   inst.inst_id = prepared.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
  `srcid <> inst.inst_id /\ st.cs_next_id <> inst.inst_id` by decide_tac >>
  Q.SUBGOAL_THEN `?p. ((FLOOKUP initial.vs_allocas inst.inst_id = NONE /\ p = initial.vs_alloca_next) \/
         FLOOKUP initial.vs_allocas inst.inst_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    (!name lo sz. local_region ce es.scopes initial name lo sz ==>
      abi_footprint_disjoint lo sz [(p,32)]) /\
    (ce.ce_is_ctor ==> !name tv v off.
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
      abi_footprint_disjoint off (type_memory_size tv) [(p,32)])`
    (qx_choose_then `p` (MAP_EVERY assume_tac o CONJUNCTS))
    >- (irule log_tuple_cursor_footprints >>
     simp[] >> conj_tac
     >- (qexists_tac `st.cs_next_id` >> simp[]) >>
     conj_tac >- (qexistsl_tac [`srccap`,`srcid`] >> simp[]) >>
     conj_tac >- (qexists_tac `prepared` >> simp[]) >>
     qexistsl_tac [`ctx`,`func`] >> simp[]) >>
  drule_at (Pat `compile_abi_encode_to_buf _ _ _ _ = _`) log_scalar_tuple_continue >>
  disch_then irule >>
  asm_simp_tac bool_ss [abi_enc_info_distinct, abi_enc_info_11] >>
  conj_tac >- (qpat_x_assum `!name entry v sz. _` mp_tac >> asm_simp_tac bool_ss []) >>
  conj_tac >- (qexists_tac `inst` >> simp[]) >>
  qexistsl_tac [`cap`,`outcap`,`p`,`sb`] >>
  asm_simp_tac bool_ss [optionTheory.SOME_11] >>
  conj_tac
  >- (rpt strip_tac >>
      irule log_two_footprints >>
      conj_tac >> first_assum irule >> goal_assum (drule_at Any)) >>
  conj_tac
  >- (qpat_x_assum `(FLOOKUP _ inst.inst_id = NONE /\ _) \/ _` mp_tac >>
      asm_simp_tac bool_ss []) >>
  rpt strip_tac >> irule log_two_footprints >>
  conj_tac >> first_assum irule >> simp[] >>
  qexistsl_tac [`name`,`v`] >> simp[]
QED

Finalise log_tuple_encoder_owned

Theorem log_allocated_tuple_encode_continue_bounded:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  outcap < dimword (:256) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_output_buffer_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_buffer_allocate >>
  disch_then (qx_choose_then `allocated` (qx_choose_then `db`
    (MAP_EVERY assume_tac o CONJUNCTS))) >>
  `FLOOKUP allocated.vs_allocas srcid = SOME (sb,srccap)` by
    (drule_at (Pat `abi_builtin_allocation_frame _ _ _ _ _`)
      abi_builtin_allocation_frame_outside >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src allocated = SOME (n2w sb)` by metis_tac[] >>
  Q.SUBGOAL_THEN `sb+cap <= db \/ db+outcap <= sb` assume_tac
    >- (qpat_x_assum `!id b sz. _` (qspec_then `srcid` mp_tac) >> simp[] >> decide_tac) >>
  Q.SUBGOAL_THEN `?actual.
    run_inst_seq (emitted_insts prepared end_st) allocated = OK actual /\
    inst_extends prepared end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live prepared.cs_next_var op /\
      eval_operand op allocated = SOME w ==> eval_operand op actual = SOME w)`
    (qx_choose_then `actual` (MAP_EVERY assume_tac o CONJUNCTS))
  >- (drule_at (Pat `compile_alloc_buffer _ _ = _`) log_tuple_encoder_owned >>
      disch_then irule >> asm_simp_tac bool_ss [] >>
      qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
      qexistsl_tac [`srcid`,`srccap`,`sb`,`cap`] >>
      gvs[]) >>
  `run_inst_seq (emitted_insts st end_st) initial = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `inst_extends st end_st` by
    (irule inst_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand dst.buf_operand actual = SOME (n2w db)` by
    (first_x_assum irule >> simp[]) >>
  `db < dimword (:256)` by decide_tac >>
  qexistsl_tac [`actual`,`db`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_operand_live prepared.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op allocated = SOME w` by metis_tac[] >>
  first_x_assum drule_all >> simp[]
QED

Theorem log_allocated_tuple_encode_continue:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand src ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\
  srcid < st.cs_next_id /\ cap <= srccap /\ sb+srccap < dimword (:256) /\
  outcap < dimword (:256) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  abi_decoder_operand_live st.cs_next_var src /\
  stmt_state_rel ctx func ce cx es initial /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all log_allocated_tuple_encode_continue_bounded >>
  strip_tac >> qexistsl_tac [`actual`,`db`] >> simp[] >> first_assum ACCEPT_TAC
QED

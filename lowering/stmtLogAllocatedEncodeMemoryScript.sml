(* Allocation and checked scalar tuple encoding for the Log suffix. *)
Theory stmtLogAllocatedEncodeMemory
Ancestors
  stmtLogSuffixStageMemory stmtLogEncodeReadyMemory stmtSimLogStoreEncode
  stmtSimLogAllocate abiBuiltinAllocation abiEncoderCounters abiEncoderInput
  exprLoweringProps localPtrsProps context abiDecoderReentry emitHelperProps
  fragExecMem fragExec venomMemDefs venomInst words list arithmetic
  stmtSimLogEncodeFields

Theorem log_allocated_tuple_encode_continue_mem:
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
  run_inst_seq_mem_ok (emitted_insts st end_st) initial /\
  (!t. run_inst_seq (emitted_insts st end_st) initial = OK t ==>
    initial.vs_alloca_next <= t.vs_alloca_next) /\
  ?actual db. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    stmt_state_rel ctx func ce cx es actual /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
    db < dimword (:256) /\
    db + LENGTH (enc (Tuple ats) (ListV avs)) <= actual.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all log_allocated_tuple_encode_continue_bounded >>
  disch_then (mk_asm "functional") >>
  drule log_output_buffer_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_buffer_allocate >>
  disch_then (qx_choose_then `allocated` (qx_choose_then `db`
    (map_every assume_tac o CONJUNCTS))) >>
  `FLOOKUP allocated.vs_allocas srcid = SOME (sb,srccap)` by
    (drule_at (Pat `abi_builtin_allocation_frame _ _ _ _ _`)
      abi_builtin_allocation_frame_outside >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand src allocated = SOME (n2w sb)` by metis_tac[] >>
  Q.SUBGOAL_THEN `sb+cap <= db \/ db+outcap <= sb` assume_tac
  >- (qpat_x_assum `!id b sz. _` (qspec_then `srcid` mp_tac) >> simp[] >> decide_tac) >>
  `local_ptrs_reserved ce prepared` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  Q.SUBGOAL_THEN `?p. (?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP allocated.vs_allocas prepared.cs_next_id = NONE /\ p = allocated.vs_alloca_next) \/
      FLOOKUP allocated.vs_allocas prepared.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w 32)] /\ inst.inst_id = prepared.cs_next_id`
    (qx_choose_then `p` assume_tac)
  >- suspend "cursor" >>
  suspend "ready"
QED

Resume log_allocated_tuple_encode_continue_mem[cursor]:
  Cases_on `?infos. ei = AbiComplex infos`
  >- (qpat_x_assum `?infos. ei = AbiComplex infos` strip_assume_tac >>
      `EXISTS (\(_,_,_,dyn). dyn) infos` by
        (qpat_x_assum `(?n. _) \/ (?infos. _)` mp_tac >> simp[]) >>
      qpat_x_assum `ei = AbiComplex infos` SUBST_ALL_TAC >>
      drule_all log_encoder_cursor_code >> strip_tac >>
      qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
      `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w 32)] /\
       inst.inst_outputs = [STRING #"%" (toString prepared.cs_next_var)] /\
       inst.inst_id = prepared.cs_next_id` by simp[Abbr `inst`, mk_inst_def] >>
      drule_all log_cursor_ownership >>
      disch_then (qx_choose_then `p` (map_every assume_tac o CONJUNCTS)) >>
      `srcid <> inst.inst_id /\ st.cs_next_id <> inst.inst_id` by decide_tac >>
      Q.SUBGOAL_THEN `p+32 <= sb \/ sb+srccap <= p` assume_tac
      >- (qpat_assum `!id b sz. _` (qspec_then `srcid` mp_tac) >> simp[]) >>
      Q.SUBGOAL_THEN `p+32 <= db \/ db+outcap <= p` assume_tac
      >- (qpat_assum `!id b sz. _` (qspec_then `st.cs_next_id` mp_tac) >> simp[]) >>
      qexists_tac `p` >> strip_tac >> asm_simp_tac bool_ss [] >>
      conj_tac >- metis_tac[] >>
      conj_tac >- decide_tac >>
      conj_tac >- metis_tac[] >>
      qexists_tac `inst` >> simp[]) >>
  qexists_tac `0` >> simp[]
QED

Resume log_allocated_tuple_encode_continue_mem[ready]:
  `abi_encoder_input ei (Tuple ats) (ListV avs) sb cap allocated.vs_memory` by metis_tac[] >>
  Q.SUBGOAL_THEN `run_inst_seq_mem_ok (emitted_insts prepared end_st) allocated /\
    (!t. run_inst_seq (emitted_insts prepared end_st) allocated = OK t ==>
      allocated.vs_alloca_next <= t.vs_alloca_next) /\
    ?actual. run_inst_seq (emitted_insts prepared end_st) allocated = OK actual /\
      mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory = enc (Tuple ats) (ListV avs) /\
      eval_operand dst.buf_operand actual = SOME (n2w db) /\
      eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs))))`
    strip_assume_tac
  >- (irule log_scalar_tuple_encode_mem_ok >>
      goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
      conj_tac >- metis_tac[] >>
      qpat_assum `compile_abi_encode_to_buf _ _ _ _ = _` (irule_at Any) >>
      qpat_assum `abi_encoder_input _ _ _ _ _ initial.vs_memory` (irule_at Any) >>
      qpat_assum `stmt_state_rel _ _ _ _ _ allocated` (irule_at Any) >>
      qpat_assum `FLOOKUP allocated.vs_allocas srcid = _` (irule_at Any) >>
      qpat_assum `FLOOKUP allocated.vs_allocas st.cs_next_id = _` (irule_at Any) >>
      qexists_tac `p` >> asm_simp_tac bool_ss [] >>
      conj_tac >- decide_tac >> metis_tac[]) >>
  `inst_extends prepared end_st` by
    (qpat_x_assum `(?n. _) \/ (?infos. _)` strip_assume_tac >>
     gvs[] >> metis_tac[log_encode_copy_safe, log_encode_dynamic_safe]) >>
  `emitted_insts st end_st = emitted_insts st prepared ++ emitted_insts prepared end_st` by
    (irule emitted_insts_append >> gvs[inst_extends_def]) >>
  `run_inst_seq (emitted_insts st end_st) initial = OK actual` by
    (drule_all run_inst_seq_compose_ok >> simp[]) >>
  `alloca_next_valid allocated` by fs[stmt_state_rel_def, alloca_inv_def] >>
  drule_all log_mem_alloc_frame_bounds >> strip_tac >>
  `db + LENGTH (enc (Tuple ats) (ListV avs)) <= actual.vs_alloca_next` by
    (first_x_assum drule >> decide_tac) >>
  `run_inst_seq_mem_ok (emitted_insts st prepared) initial` by
    (irule log_mem_alloc_check >> goal_assum (drule_at Any)) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >>
      simp[] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_TRANS]) >>
  asm_x "functional" (qx_choose_then `finished` (qx_choose_then `dbase` (map_every assume_tac o CONJUNCTS))) >>
  `finished = actual` by gvs[] >>
  `dbase = db` by
    gvs[] >>
  qexistsl_tac [`actual`,`db`] >> gvs[]
QED

Finalise log_allocated_tuple_encode_continue_mem

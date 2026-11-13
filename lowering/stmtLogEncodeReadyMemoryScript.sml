(* Statement-state resource adapter for the scalar Log tuple encoder. *)
Theory stmtLogEncodeReadyMemory
Ancestors
  stmtLogEncodeMemory stmtSimLogScalarEncode context allocaFootprint exprLoweringProps exprSimDefs
  abiBuiltinAllocation abiEncoderInput abiDecoderReentry stmtSimLogScalarMembers
  fragExecMem instMemFrontier venomMemDefs words arithmetic list

Theorem log_scalar_tuple_encode_mem_ok:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  FLOOKUP initial.vs_allocas srcid = SOME (sb,srccap) /\ cap <= srccap /\
  FLOOKUP initial.vs_allocas dstid = SOME (db,outcap) /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  stmt_state_rel ctx func ce cx es initial /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db) /\
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit (n2w 32)] /\ inst.inst_id = st.cs_next_id) ==>
  run_inst_seq_mem_ok (emitted_insts st end_st) initial /\
  (!actual. run_inst_seq (emitted_insts st end_st) initial = OK actual ==>
     initial.vs_alloca_next <= actual.vs_alloca_next) /\
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand dst actual = SOME (n2w db) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `alloca_next_valid initial /\ alloca_room ctx func initial` by
    fs[stmt_state_rel_def, alloca_inv_def] >>
  `initial.vs_alloca_next < dimword (:256)` by
    (drule alloca_room_next_lt >> simp[]) >>
  `sb+cap <= initial.vs_alloca_next /\ db+outcap <= initial.vs_alloca_next` by
    (fs[alloca_next_valid_def] >> res_tac >> decide_tac) >>
  `(?infos. ei = AbiComplex infos) ==>
     (FLOOKUP initial.vs_allocas st.cs_next_id <> NONE ==>
       p+32 <= initial.vs_alloca_next) /\
     (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next < dimword (:256)` by
    (strip_tac >>
     qpat_x_assum `(?infos. ei = AbiComplex infos) ==> _` mp_tac >>
     simp[] >> strip_tac >>
     drule_all log_scalar_cursor_stmt_resources >> strip_tac >>
     gvs[] >> metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ]) >>
  `run_inst_seq_mem_ok (emitted_insts st end_st) initial /\
   !actual. run_inst_seq (emitted_insts st end_st) initial = OK actual ==>
     initial.vs_alloca_next <= actual.vs_alloca_next` by
    (drule log_scalar_tuple_mem_ok >> disch_then drule >>
     disch_then (qspecl_then [`p`,`outcap`,`limit_st`,`db`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> simp[]) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  drule log_scalar_tuple_run >> disch_then drule >>
  disch_then (qspecl_then [`p`,`outcap`,`limit_st`,`db`] mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >>
  first_x_assum irule >> simp[]
QED

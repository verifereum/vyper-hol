(* Ownership adapters at the actual allocated tuple-encoder caller. *)
Theory logTupleCallerPtr
Ancestors
  logTupleDispatchPtr logTupleGhostPtr logAllocFramePtr stmtSimLogStoreEncode
  stmtSimLogEncodeFields stmtSimLogExecFields exprSimPtrLiteralBuffer
  localPtrsProps abiBuiltinAllocation abiDecoderFrame bodyPtrDefs compileEnv
  allocationPtr emitHelperProps fragGasSeqPtr context ASCIInumbers string
  logDataAllocPtr abiEncoderCounters stmtFragPtr abiDecoderReentry
  ghostPcTransportPtr instIdxIndep logInstSeqPtr logTupleOwnershipPtr
  exprLoweringProps logMembersInvariantPtr loweringHalt venomExecSemantics venomMemProps
  venomState venomInst venomMemDefs finite_map words list arithmetic

Theorem log_alloca_robust_encoder_input:
  stmt_state_rel ctx func ce cx es s /\
  MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
  n < dimword (:256) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK t /\
  a+cap <= s.vs_alloca_next /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei at av a cap q) ==>
  !q. mem_agree_outside
    (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem
    t.vs_memory q ==> abi_encoder_input ei at av a cap q
Proof
  strip_tac >>
  `t.vs_memory = s.vs_memory` by
    (qspecl_then [`id`,`n2w n`,`out`,`s`] mp_tac step_alloca_frame >>
     simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule robust_abi_encoder_input_copy_transport >>
  qexistsl_tac [`tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s t tn).t_mem`,
    `s.vs_memory`,`t.vs_memory`,`a`] >>
  asm_simp_tac bool_ss [] >> rpt strip_tac >>
  irule alloca_step_taint_below_frontier >>
  asm_simp_tac bool_ss [] >> conj_tac >- decide_tac >>
  qexistsl_tac [`ce`,`ctx`,`cx`,`es`,`func`] >> asm_simp_tac bool_ss []
QED

(* The caller's staged input survives allocating the output buffer, including
   a reused allocation site.  No cleanliness is demanded of source padding. *)
Theorem log_buffer_encoder_source_seq_ptr:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\
  inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tm /\
  stmt_state_rel ctx func ce cx es s /\ n < dimword (:256) /\
  not_fresh_at sa src /\ ptr_covers G tn src s srcCap /\
  a+cap <= s.vs_alloca_next /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei at av a cap q) ==>
  ptr_covers H tm src t srcCap /\
  (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
    abi_encoder_input ei at av a cap q)
Proof
  strip_tac >> drule_all log_buffer_alloca_step >> strip_tac >>
  `src <> STRING #"%" (toString sa.cs_next_var)` by
    (strip_tac >> gvs[not_fresh_at_def]) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[inst_seq_ptr_def, run_inst_seq_def, AllCaseEqs()] >>
  conj_tac
  >- (irule alloca_step_old_ptr_covers >> metis_tac[]) >>
  rpt strip_tac >> irule log_alloca_robust_encoder_input >> metis_tac[]
QED

(* Semantic correctness is reused only after identifying the endpoint of the
   certified pointer sequence with the endpoint of the S1 run. *)
Theorem log_allocated_tuple_semantic_align:
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
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  run_inst_seq (emitted_insts st end_st) initial = OK actual ==>
  stmt_state_rel ctx func ce cx es actual /\ fresh_vars_wrt limit_st actual /\
  (!op w. abi_decoder_operand_live st.cs_next_var op /\
    eval_operand op initial = SOME w ==> eval_operand op actual = SOME w) /\
  ?db. eval_operand dst.buf_operand actual = SOME (n2w db) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    db < dimword (:256)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_allocated_tuple_encode_continue_bounded >>
  disch_then (qx_choose_then `actual'` (qx_choose_then `db`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `actual' = actual` by gvs[] >>
  gns[] >> qexists_tac `db` >> asm_simp_tac bool_ss [] >> simp[]
QED

Theorem log_buffer_encoder_entry_ptr:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ outcap < dimword (:256) /\
  prepared.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~ctx_has_dalloca ctx /\ srcid < st.cs_next_id /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\
  not_fresh_at st src /\ lookup_var src s = SOME (n2w sb) /\
  ptr_covers G tn src s srcCap /\ sb+srcCap < dimword (:256) /\ inputCap <= srcCap /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei at av sb inputCap q) ==>
  ?t db H tm dv.
    run_inst_seq (emitted_insts st prepared) s = OK t /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st prepared) s H tm /\
    dst.buf_operand = Var dv /\ dst.buf_size = outcap /\
    stmt_state_rel ctx func ce cx es t /\ fresh_vars_wrt limit_st t /\
    local_ptrs_reserved ce prepared /\
    not_fresh_at prepared src /\ not_fresh_at prepared dv /\
    lookup_var src t = SOME (n2w sb) /\ lookup_var dv t = SOME (n2w db) /\
    ptr_covers H tm src t srcCap /\ ptr_covers H tm dv t outcap /\
    FLOOKUP t.vs_allocas srcid = SOME (sb,srcCap) /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (db,outcap) /\
    srcid <> prepared.cs_next_id /\ st.cs_next_id <> prepared.cs_next_id /\
    db+outcap < dimword (:256) /\ (sb+srcCap <= db \/ db+outcap <= sb) /\
    (!q. mem_agree_outside tm.t_mem t.vs_memory q ==>
      abi_encoder_input ei at av sb inputCap q) /\
    abi_builtin_allocation_frame st.cs_next_var st.cs_next_id outcap s t /\
    inst_extends st prepared
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all log_buffer_seq_ptr >>
  disch_then (qspecl_then [`tn`,`PG`,`G`,`D`]
    (qx_choose_then `t` (qx_choose_then `db` (qx_choose_then `H`
      (qx_choose_then `tm` (qx_choose_then `dv`
        (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))) >>
  `sb+inputCap <= s.vs_alloca_next` by
    (fs[stmt_state_rel_def, state_rel_def, alloca_inv_def, alloca_next_valid_def] >>
     `sb+srcCap <= s.vs_alloca_next` by metis_tac[] >> decide_tac) >>
  drule_all log_buffer_encoder_source_seq_ptr >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  suspend "entry_post"
QED
Resume log_buffer_encoder_entry_ptr[entry_post]:
  markerLib.RESUME_TAC >>
  `srcid <> st.cs_next_id` by decide_tac >>
  `FLOOKUP t.vs_allocas srcid = SOME (sb,srcCap)` by
    metis_tac[abi_builtin_allocation_frame_outside] >>
  `sb+srcCap <= db \/ db+outcap <= sb` by metis_tac[] >>
  `local_ptrs_reserved ce prepared` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `not_fresh_at prepared src` by
    (irule not_fresh_at_mono >> qexists_tac `st` >> simp[]) >>
  `not_fresh_at prepared dv` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  `lookup_var src t = SOME (n2w sb)` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _`
      (qspec_then `Var src` mp_tac) >>
     simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       not_fresh_at_def, eval_operand_def] >>
     metis_tac[not_fresh_at_def]) >>
  `lookup_var dv t = SOME (n2w db)` by gns[eval_operand_def] >>
  qexistsl_tac [`t`,`db`,`H`,`tm`,`dv`] >> asm_simp_tac bool_ss [] >>
  gvs[] >> decide_tac
QED
Finalise log_buffer_encoder_entry_ptr

Theorem log_allocated_tuple_sequence_ptr:
  compile_alloc_buffer outcap st = (dst,prepared) /\ fn_has_code st prepared func /\
  compile_abi_encode_to_buf dst.buf_operand (Var src) ei prepared = (out,end_st) /\
  fn_has_code prepared end_st func /\
  FLOOKUP s.vs_allocas srcid = SOME (sb,srcCap) /\ srcid < st.cs_next_id /\
  inputCap <= srcCap /\ sb+srcCap < dimword (:256) /\ outcap < dimword (:256) /\
  not_fresh_at st src /\ lookup_var src s = SOME (n2w sb) /\
  ptr_covers G tn src s srcCap /\ ~ctx_has_dalloca ctx /\
  ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!q. mem_agree_outside tn.t_mem s.vs_memory q ==>
    abi_encoder_input ei (Tuple ats) (ListV avs) sb inputCap q) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ fresh_vars_wrt limit_st s /\
  end_st.cs_next_var <= limit_st.cs_next_var /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
      EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) ==>
  ?actual db H tm.
    run_inst_seq (emitted_insts st end_st) s = OK actual /\
    inst_seq_ptr D 0 ctx func PG G tn (emitted_insts st end_st) s H tm /\
    inst_extends st end_st /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st end_st) /\ fresh_vars_wrt limit_st actual /\
    stmt_state_rel ctx func ce cx es actual /\
    eval_operand dst.buf_operand actual = SOME (n2w db) /\ db < dimword (:256) /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    (!i. db <= i /\ i < db+LENGTH (enc (Tuple ats) (ListV avs)) ==> i NOTIN tm.t_mem) /\
    ghost_inv d ce cx es H tm actual /\ ghost_kept ce es st G tn s H tm /\
    (?dv. dst.buf_operand = Var dv /\ ptr_covers H tm dv actual outcap) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op actual = SOME w) /\
    (!p. not_fresh_at st p ==> op_taint tm (Var p) = op_taint tn (Var p))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule abi_encoder_counters >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_buffer_encoder_entry_ptr >>
  disch_then (qspecl_then [`PG`,`D`]
    (qx_choose_then `t` (qx_choose_then `db` (qx_choose_then `H`
      (qx_choose_then `tm` (qx_choose_then `dv`
        (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))) >>
  `!p. not_fresh_at st p ==> FLOOKUP H p = FLOOKUP G p /\
     op_taint tm (Var p) = op_taint tn (Var p)` by
    (match_mp_tac (Q.INST [`sb` |-> `prepared`, `cap` |-> `outcap`,
       `buf` |-> `dst`] log_buffer_old_ghost_seq_ptr) >>
     goal_assum (drule_at Any) >> asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule_all log_buffer_ghost_seq_ptr >>
  disch_then (qspec_then `s.vs_inst_idx + LENGTH (emitted_insts st prepared)`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  suspend "dispatch"
QED
Resume log_allocated_tuple_sequence_ptr[dispatch]:
  markerLib.RESUME_TAC >>
  mp_tac (Q.INST [`st` |-> `prepared`, `dst` |-> `dv`,
    `dstid` |-> `st.cs_next_id`, `d` |-> `db`, `cap` |-> `outcap`,
    `tys` |-> `ats`, `G` |-> `H`, `tn` |-> `tm`,
    `s` |-> `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st prepared)`]
    (SPEC_ALL compile_log_tuple_seq_ptr)) >>
  impl_tac >- (asm_simp_tac bool_ss [] >>
    fs[stmt_state_rel_inst_idx, fresh_vars_wrt_def, lookup_var_def,
      ptr_covers_inst_idx] >> metis_tac[]) >>
  disch_then (qx_choose_then `Gf` (qx_choose_then `tk` (qx_choose_then `u`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  suspend "ownership"
QED
Resume log_allocated_tuple_sequence_ptr[ownership]:
  markerLib.RESUME_TAC >>
  `?fp.
    abi_decode_footprint_frame fp
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st prepared)) u /\
    (!i. abi_footprint_disjoint i 1 fp ==> (i IN tk.t_mem <=> i IN tm.t_mem)) /\
    (!name b sz. local_region ce es.scopes t name b sz ==> abi_footprint_disjoint b sz fp) /\
    (!aid off sz i. FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
      aid < st.cs_next_id /\ off <= i /\ i < off+sz ==> abi_footprint_disjoint i 1 fp) /\
    (!name b sz i. local_region ce es.scopes s name b sz /\ b <= i /\ i < b+sz ==>
      abi_footprint_disjoint i 1 fp)` by
    (qpat_x_assum `(_ /\ abi_decode_footprint_frame _ _ _ /\ _) \/ _`
       (DISJ_CASES_THEN assume_tac)
     >- (pop_assum (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
         drule_all log_output_protected_footprint >>
         disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
         qexists_tac `[(db,outcap)]` >>
         asm_simp_tac bool_ss [] >>
         conj_tac >- (simp_tac bool_ss [abi_footprint_disjoint_def, MEM, pairTheory.PAIR_EQ] >>
           rpt strip_tac >>
           qpat_x_assum `!i. ~(_ /\ _) ==> _` irule >> decide_tac) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum (qx_choose_then `p` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
     qpat_x_assum `?infos. _` (qx_choose_then `infos`
       (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
     `u.vs_allocas = (abi_builtin_allocate_state prepared.cs_next_id 32 t).vs_allocas` by
       (qpat_x_assum `u.vs_allocas = _` mp_tac >>
        Cases_on `FLOOKUP t.vs_allocas prepared.cs_next_id = NONE` >>
        asm_simp_tac bool_ss [abi_builtin_allocate_state_def, venom_state_accfupds]) >>
     `compile_abi_encode_to_buf dst.buf_operand (Var src) (AbiComplex infos) prepared = (out,end_st)` by
       metis_tac[] >>
     drule_all log_tuple_protected_footprint >>
     disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
     qexists_tac `[(db,outcap);(p,32)]` >> asm_simp_tac bool_ss [] >>
     conj_tac >- (simp_tac bool_ss [abi_footprint_disjoint_def, MEM, pairTheory.PAIR_EQ] >>
       rpt strip_tac >>
       qpat_x_assum `!i. ~(_ /\ _) /\ ~(_ /\ _) ==> _` irule >>
       qpat_assum `!d sz. _` (qspecl_then [`db`,`outcap`] mp_tac) >>
       qpat_x_assum `!d sz. _` (qspecl_then [`p`,`32`] mp_tac) >>
       simp_tac bool_ss [] >> decide_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "ghosts"
QED
Resume log_allocated_tuple_sequence_ptr[ghosts]:
  markerLib.RESUME_TAC >>
  `log_encode_external u = log_encode_external
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st prepared))` by
    (irule log_scalar_encode_external >> goal_assum (drule_at Any) >>
     asm_simp_tac bool_ss [] >> metis_tac[]) >>
  drule log_encode_external_fields >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `ghost_kept ce es st G tn s Gf tk` by
    (irule ghost_kept_footprint_transport >>
     qexistsl_tac [`H`,`fp`,`prepared`,`tm`] >> asm_simp_tac bool_ss [] >>
     rpt conj_tac >- metis_tac[] >- metis_tac[] >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  `ghost_inv d ce cx es Gf tk u` by
    (irule ghost_inv_footprint_transport >>
     qexistsl_tac [`H`,`fp`,`func`,
       `t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st prepared)`,
       `prepared`,`tm`] >>
     asm_simp_tac bool_ss [venom_state_accfupds] >>
     conj_tac >- (simp_tac bool_ss [log_local_region_inst_idx] >> first_assum ACCEPT_TAC) >>
     `st.cs_next_var <= prepared.cs_next_var` by
       (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
        drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     conj_tac >- metis_tac[not_fresh_at_mono] >>
     qpat_x_assum `stmt_state_rel ctx func ce cx es t` mp_tac >>
     simp_tac bool_ss [local_ptrs_rel_inst_idx, stmt_state_rel_def, state_rel_def] >>
     metis_tac[]) >>
  suspend "compose"
QED
Resume log_allocated_tuple_sequence_ptr[compose]:
  markerLib.RESUME_TAC >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st prepared)` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts prepared end_st)` by
    fs[EVERY_MEM] >>
  drule_all successful_seq_ptr_append >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `emitted_insts st end_st = emitted_insts st prepared ++ emitted_insts prepared end_st` by
    (irule emitted_insts_append >> fs[inst_extends_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st end_st)` by
    (asm_simp_tac bool_ss [EVERY_APPEND]) >>
  `run_inst_seq (emitted_insts st end_st) s = OK (u with vs_inst_idx := t.vs_inst_idx)` by
    metis_tac[] >>
  `abi_encoder_input ei (Tuple ats) (ListV avs) sb inputCap s.vs_memory` by
    (qpat_x_assum `!q. mem_agree_outside tn.t_mem s.vs_memory q ==> _` irule >>
     simp[mem_agree_outside_def]) >>
  `abi_decoder_operand_live st.cs_next_var (Var src)` by
    fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def] >>
  `eval_operand (Var src) s = SOME (n2w sb)` by simp[eval_operand_def] >>
  drule_all log_allocated_tuple_semantic_align >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  suspend "result"
QED
Resume log_allocated_tuple_sequence_ptr[result]:
  markerLib.RESUME_TAC >>
  `lookup_var dv u = SOME (n2w db)` by
    (qpat_x_assum `!v. not_fresh_at prepared v ==> _`
      (qspec_then `dv` mp_tac) >> simp[lookup_var_def] >> fs[lookup_var_def]) >>
  `ptr_covers Gf tk dv u outcap` by
    (qpat_x_assum `!v. not_fresh_at prepared v ==> _`
      (qspec_then `dv` mp_tac) >>
     asm_simp_tac bool_ss [] >> strip_tac >>
     qpat_x_assum `ptr_covers H tm dv t outcap` mp_tac >>
     asm_simp_tac bool_ss [ptr_covers_def, lookup_var_def, venom_state_accfupds]) >>
  `db < dimword (:256)` by decide_tac >>
  `inst_extends st end_st` by metis_tac[inst_extends_trans] >>
  qexistsl_tac [`u with vs_inst_idx := t.vs_inst_idx`,`db`,`Gf`,`tk`] >>
  asm_simp_tac bool_ss [venom_state_accfupds, eval_operand_inst_idx, eval_operand_def,
    ptr_covers_inst_idx,
    PURE_REWRITE_RULE [ghost_inv_gas_obs] literal_ptr_ghost_inv_normalize] >>
  conj_tac >- (qexists_tac `dv` >> asm_simp_tac bool_ss []) >>
  rpt strip_tac >>
  `not_fresh_at prepared p` by
    (irule not_fresh_at_mono >> qexists_tac `st` >>
     asm_simp_tac bool_ss [] >>
     drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> simp[]) >>
  metis_tac[]
QED
Finalise log_allocated_tuple_sequence_ptr

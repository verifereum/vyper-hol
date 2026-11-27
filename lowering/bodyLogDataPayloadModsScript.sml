(* The data ALLOCA has no header. The captured data rows are encoded by the
   shared linked tuple loop; the final LOG instruction is not executed here. *)
Theory bodyLogDataPayloadMods
Ancestors
  bodyAbiTupleLinkedLoopMods bodyFullAbiEncodeAllocOrigin
  bodyMethodIdScratchFrameMods bodyFullAllocaFresh bodyFullAbiEncodeOriginFloor
  abiBuiltinAllocation exprSimAlloc bodyMemoryDefs abiLogReady
  bodyFullPostsMods bodyInvSplit exprLoweringProps stateRelProj exprSimWordArgs
  fragGasOriginPtrLoop bodyFullShadowBodyInv loweringStateRelDefs exprSafeOperand
  ptrDiscipline bodyPtrDefs emitHelperProps venomInst loweringPosts exprSimProps
  wordArgsPtr bodyAbiTupleBufferStateMods venomState allocaSiteResource
  contractABI venomMemDefs memoryReadProps words finite_map list pair pred_set
  valueEncodingDefs fragGasOriginPtr arithmetic
Libs horizonTypeLib

Theorem log_alloca_fields[local]:
  FLOOKUP (abi_builtin_allocate_state aid cap s).vs_allocas j = SOME (b,n) ==>
  FLOOKUP s.vs_allocas j = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  Cases_on `FLOOKUP s.vs_allocas aid` >>
  simp[abi_builtin_allocate_state_def] >> strip_tac >>
  Cases_on `j = aid` >> gvs[FLOOKUP_UPDATE]
QED

Theorem log_alloc_immutable[local]:
  immutable_frame_mods func ce cx ee s /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  u.vs_immutables = s.vs_immutables /\ s.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_allocas = (abi_builtin_allocate_state aid cap s).vs_allocas /\
  local_ptrs_reserved ce st /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s) ==>
  immutable_frame_mods func ce cx ee u
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_frame >> qexistsl [`s`,`ee`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> disj1_tac >>
      rename1 `local_region _ _ u name b n` >> qexists `name` >>
      fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC log_alloca_fields
QED

Theorem log_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx ee Gu tu u
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx ee G tn s` by drule_then ACCEPT_TAC method_id_ghost_at_zero >>
  `ghost_inv_at D 0 d ce cx ee Gu tu u` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl [`G`,`H`,`ctx`,`stop`,`func`,`s`,`st`,`tn`] >> simp[]) >>
  `u.vs_memory = s.vs_memory` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> metis_tac[]) >>
  decide_tac
QED

Theorem log_data_alloc[local]:
  compile_alloc_buffer cap se = (buf,st) /\ cap < dimword (:256) /\
  fn_has_code se st func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\ immutable_frame_mods func ce cx ee s) /\
  return_buf_frame d ce se s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?p b u Gu tu inst.
    buf.buf_operand = Var p /\ MEM inst (fn_insts func) /\
    inst.inst_id = se.cs_next_id /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [p] /\ not_local_ptr ce ee.scopes p /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id b cap p p 0 [] st u Gu tu /\
    b + cap < dimword (:256) /\
    (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
      op_taint tu (Var x) = op_taint tn (Var x)) /\
    se.cs_next_id < st.cs_next_id /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all (INST_TYPE [Type.beta |-> ``:256``] abi_encode_alloc_origin_exact) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`p`,`w`,`u`,`Gu`,`tu`] strip_assume_tac)) >>
  `p = STRING #"%" (toString se.cs_next_var) /\
   se.cs_next_var <= st.cs_next_var /\ se.cs_next_id < st.cs_next_id` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> gvs[]) >>
  `not_local_ptr ce ee.scopes p` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists `se` >> simp[]) >>
  `MEM (mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [p]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  qexistsl [`p`,`w2n (w:bytes32)`,`u`,`Gu`,`tu`,
            `mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [p]`] >>
  asm_rewrite_tac[] >> simp_tac (srw_ss()) [mk_inst_def] >>
  suspend "state"
QED

Resume log_data_alloc[state]:
  qpat_assum `u with <| vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _ |> = s`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE (srw_ss()) [venom_state_component_equality]) >>
  `return_buf_frame d ce st u` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s`,`se`] >> simp[]) >>
  `!b n. ((b = 0 /\ n = lo) \/ (?name. local_region ce ee.scopes s name b n) \/
        (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
       b+n <= s.vs_alloca_next` by suspend "protected" >>
  `wb_frame ce ee ee se s u` by simp[wb_frame_def, locals_kept_mem] >>
  `ghost_kept_at lo ce ee se G tn s Gu tu` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl [`G`,`w2n (w:bytes32)+cap`,`s`,`tn`] >>
     simp[ghost_kept_at_refl] >> rpt strip_tac >> first_x_assum irule >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee u /\ storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u /\ immutable_frame_mods func ce cx ee u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     conj_tac >- (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> conj_tac >- drule_all_then ACCEPT_TAC log_alloc_ghost >>
     irule log_alloc_immutable >> qexistsl [`se.cs_next_id`,`cap`,`s`,`se`] >>
     asm_rewrite_tac[] >> gen_tac >> disch_tac >> simp[]) >>
  `se.cs_current_bb = st.cs_current_bb` by metis_tac[] >>
  `!b n. ((b = 0 /\ n = lo) \/ (?name. local_region ce ee.scopes s name b n) \/
        (?aid. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n))) ==>
       mem_bytes_at b n u.vs_memory = mem_bytes_at b n s.vs_memory /\
       (!i. b <= i /\ i < b+n /\ i IN tu.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     `b+n <= s.vs_alloca_next` by
       (qpat_assum `!b n. _ ==> b+n <= s.vs_alloca_next`
          (qspecl_then [`b`,`n`] irule) >> first_assum ACCEPT_TAC) >>
     asm_rewrite_tac[] >> rpt strip_tac >> decide_tac) >>
  qpat_x_assum `p = STRING _ _` SUBST_ALL_TAC >>
  conj_tac
  >- (rewrite_tac[abi_tuple_buffer_state_mods_def] >>
      asm_rewrite_tac[] >> simp[read_memory_def, eval_operand_def]) >>
  gen_tac >> disch_tac >> simp[]
QED

Resume log_data_alloc[protected]:
  rpt gen_tac >> strip_tac
  >- gvs[]
  >- (irule (horizonTypeLib.at_horizon_named "H" body_local_region_frontier) >>
      qexistsl [`hz`,`ce`,`ctx`,`cx`,`ee`,`func`,`name`] >> simp[]) >>
  irule alloca_site_registered_below >> conj_tac
  >- (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  qexists `aid` >> first_assum ACCEPT_TAC
QED

Finalise log_data_alloc[local]

Theorem log_keep_topics[local]:
  !ops topics se s z tn tz.
    EVERY (safe_operand se) ops /\
    EVERY (\op. op_taint tn op = {}) ops /\ eval_operands ops s = SOME topics /\
    (!x. not_fresh_at se x ==> op_taint tz (Var x) = op_taint tn (Var x)) /\
    (!x w. not_fresh_at se x /\ lookup_var x s = SOME w ==> lookup_var x z = SOME w) ==>
    EVERY (\op. op_taint tz op = {}) ops /\ eval_operands ops z = SOME topics
Proof
  Induct >> simp[eval_operands_def] >> rpt gen_tac >>
  simp[AllCaseEqs(), safe_operand_def] >> strip_tac >>
  `eval_operand h z = SOME v /\ op_taint tz h = {}` by
    (Cases_on `h` >> fs[eval_operand_def, op_taint_def]) >>
  first_x_assum (drule_all_then strip_assume_tac) >> simp[]
QED

(* The allocation-to-loop interface isolates the physical payload landing from
   the choice of the checked tuple-loop driver. *)
Theorem log_data_payload_core_mods[local]:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\ immutable_frame_mods func ce cx ee s) /\
  return_buf_frame d ce se s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  EVERY (safe_operand se) ops /\ EVERY (\op. op_taint tn op = {}) ops /\
  eval_operands ops s = SOME topics /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                     abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  ((rows = [] /\ en = se /\ len_op = Lit 0w /\ ptr_op = Lit 0w) \/
   (rows <> [] /\ cap = abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) /\
    LENGTH bytes <= cap /\ cap < dimword (:256) /\
    compile_alloc_buffer cap se = (buf,st) /\ ptr_op = buf.buf_operand /\
    compile_abi_encode_values_to_buf ce ptr_op rows st = (len_op,en) /\
    fn_has_code se st func /\ fn_has_code st en func /\
    (!p b u Gu tu inst.
      ptr_op = Var p /\ se.cs_next_id < st.cs_next_id /\
      MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = se.cs_next_id /\ inst.inst_outputs = [p] /\
      not_local_ptr ce ee.scopes p /\
      abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
        se.cs_next_id b cap p p 0 [] st u Gu tu ==>
      ?z Gz tz.
        abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
          se.cs_next_id b cap p p 0 [] en z Gz tz /\
        abi_tuple_row_effects_mods ce ee func se.cs_next_id b cap 0 st.cs_next_id
          st u Gu tu en z Gz tz /\
        eval_operand len_op z = SOME (n2w (LENGTH bytes)) /\
        op_taint tz len_op = {} /\
        (!x. len_op = Var x ==> not_fresh_at en x) /\
        mem_bytes_at b (LENGTH bytes) z.vs_memory = bytes /\
        (!j. b <= j /\ j < b + LENGTH bytes ==> j NOTIN tz.t_mem) /\
        !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
          (u,Gu,tu) [] (OK z,Gz,tz)))) ==>
  ?z Gz tz off.
    eval_operands ops z = SOME topics /\
    eval_operand ptr_op z = SOME off /\ eval_operand len_op z = SOME (n2w (LENGTH bytes)) /\
    EVERY (\op. op_taint tz op = {}) (ptr_op::len_op::ops) /\
    (LENGTH bytes <> 0 ==> ?p. ptr_op = Var p /\ ptr_covers Gz tz p z (LENGTH bytes)) /\
    mem_bytes_at (w2n off) (LENGTH bytes) z.vs_memory = bytes /\
    (!i. w2n off <= i /\ i < w2n off + LENGTH bytes ==> i NOTIN tz.t_mem) /\
    LENGTH bytes < dimword (:256) /\
    (LENGTH bytes = 0 \/ w2n off + LENGTH bytes <= z.vs_alloca_next) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z) /\
    return_buf_frame d ce en z /\ ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts /\ alloca_history func z /\
    se.cs_next_var <= en.cs_next_var /\ s.vs_alloca_next <= z.vs_alloca_next /\
    wb_frame ce ee ee se s z /\ ghost_kept_at lo ce ee se G tn s Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `(rows = [] /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "empty_core" >>
  drule_all_then
    (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`p`,`b`,`u`,`Gu`,`tu`,`inst`] strip_assume_tac))
    log_data_alloc >>
  `ptr_op = Var p` by simp[] >>
  qpat_x_assum `ptr_op = Var p` SUBST_ALL_TAC >>
  qpat_assum `!p b u Gu tu inst. _`
    (qspecl_then [`p`,`b`,`u`,`Gu`,`tu`,`inst`] mp_tac) >>
  impl_tac >- (conj_tac >- simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`z`,`Gz`,`tz`] strip_assume_tac) >>
  suspend "landing_core"
QED

Resume log_data_payload_core_mods[empty_core]:
  `ats = [] /\ avs = []` by metis_tac[LIST_REL_LENGTH, LENGTH_NIL] >>
  `bytes = []` by simp[enc_def, REV_DEF] >>
  qexistsl [`s`,`G`,`tn`,`0w`] >>
  simp[eval_operand_def, op_taint_def, mem_bytes_at_def, wb_frame_refl,
       ghost_kept_at_refl, gas_origin_ptr_path_rules]
QED

Resume log_data_payload_core_mods[landing_core]:
  qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ en z Gz tz`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
  qpat_x_assum `abi_tuple_row_effects_mods _ _ _ _ _ _ _ _ st u Gu tu en z Gz tz`
    (strip_assume_tac o REWRITE_RULE [abi_tuple_row_effects_mods_def]) >>
  `se.cs_next_var <= st.cs_next_var` by
    (qpat_assum `abi_tuple_buffer_state_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ st u Gu tu`
       (strip_assume_tac o REWRITE_RULE [abi_tuple_buffer_state_mods_def]) >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at se x ==> not_fresh_at st x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists `se` >> simp[]) >>
  `eval_operands ops z = SOME topics /\ EVERY (\op. op_taint tz op = {}) ops` by
    (mp_tac (Q.SPECL [`ops`,`topics`,`se`,`s`,`z`,`tn`,`tz`] log_keep_topics) >>
     impl_tac >- (asm_rewrite_tac[] >> conj_tac >- suspend "topic_taint_core" >> suspend "topic_value_core") >>
     disch_then strip_assume_tac >> asm_rewrite_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)` by
    (gen_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gu`,`u`,`tu`] >> simp[]) >>
  `alloca_inv z` by
    (qpat_assum `?H. valid_horizon _ _ H _` (qx_choose_then `hz` assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ z /\ _`
       (drule_then strip_assume_tac) >> drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `b + cap <= z.vs_alloca_next` by
    (irule alloca_site_registered_below >> simp[] >> qexists `se.cs_next_id` >> simp[]) >>
  `LENGTH bytes < dimword (:256) /\ b < dimword (:256)` by decide_tac >>
  `w2n (n2w b : bytes32) = b` by simp[w2n_n2w] >>
  `ptr_covers Gz tz p z (LENGTH bytes)` by drule_all_then ACCEPT_TAC reasonCopySourcePtrTheory.ptr_covers_mono >>
  `op_taint tz (Var p) = {}` by fs[ptr_covers_def] >>
  `EVERY (\op. op_taint tz op = {}) (Var p::len_op::ops)` by simp[] >>
  `(LENGTH bytes <> 0 ==> ?p'. Var p = Var p' /\ ptr_covers Gz tz p' z (LENGTH bytes))` by
    (disch_tac >> qexists `p` >> conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
  `b + LENGTH bytes <= z.vs_alloca_next` by decide_tac >>
  qexistsl [`z`,`Gz`,`tz`,`n2w b`] >>
  qpat_assum `w2n (n2w b : bytes32) = b` (fn th => pure_rewrite_tac[th]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE (disj2_tac >> first_assum ACCEPT_TAC))
QED

Resume log_data_payload_core_mods[topic_taint_core]:
  gen_tac >> disch_tac >>
  `not_fresh_at st x` by (qpat_assum `!x. not_fresh_at se x ==> not_fresh_at st x` irule >> simp[]) >>
  qpat_assum `!x. not_fresh_at st x ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[]
QED

Resume log_data_payload_core_mods[topic_value_core]:
  qx_gen_tac `x` >> gen_tac >> strip_tac >>
  `not_fresh_at st x` by (qpat_assum `!x. not_fresh_at se x ==> not_fresh_at st x` irule >> simp[]) >>
  qpat_assum `!x. not_fresh_at st x ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!w. lookup_var x u = SOME w ==> _` irule >> asm_rewrite_tac[]
QED

Finalise log_data_payload_core_mods[local]


Theorem log_data_payload_mods:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\ immutable_frame_mods func ce cx ee s) /\
  return_buf_frame d ce se s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  EVERY (safe_operand se) ops /\ EVERY (\op. op_taint tn op = {}) ops /\
  eval_operands ops s = SOME topics /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                     abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  ((rows = [] /\ en = se /\ len_op = Lit 0w /\ ptr_op = Lit 0w) \/
   (rows <> [] /\ cap = abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) /\
    LENGTH bytes <= cap /\ cap < dimword (:256) /\
    compile_alloc_buffer cap se = (buf,st) /\ ptr_op = buf.buf_operand /\
    compile_abi_encode_values_to_buf ce ptr_op rows st = (len_op,en) /\
    fn_has_code se st func /\ fn_has_code st en func /\
    (!p b. ptr_op = Var p ==>
      !ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
        ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
      !i a c v Gv tv cursor slot. i < LENGTH rows /\
        abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
          se.cs_next_id b cap p p 0 [] a v Gv tv /\
        abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot i a v Gv tv /\
        compile_abi_encode_value_rows ce (Var p) cursor
          (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
          [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
        ?q Gq tq.
          abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
            se.cs_next_id b cap p p 0 [] c q Gq tq /\
          abi_tuple_row_effects_mods ce ee func se.cs_next_id b cap 0 st.cs_next_id
            a v Gv tv c q Gq tq /\
          abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot (SUC i) c q Gq tq /\
          !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK q,Gq,tq)))) ==>
  ?z Gz tz off.
    eval_operands ops z = SOME topics /\
    eval_operand ptr_op z = SOME off /\ eval_operand len_op z = SOME (n2w (LENGTH bytes)) /\
    EVERY (\op. op_taint tz op = {}) (ptr_op::len_op::ops) /\
    (LENGTH bytes <> 0 ==> ?p. ptr_op = Var p /\ ptr_covers Gz tz p z (LENGTH bytes)) /\
    mem_bytes_at (w2n off) (LENGTH bytes) z.vs_memory = bytes /\
    (!i. w2n off <= i /\ i < w2n off + LENGTH bytes ==> i NOTIN tz.t_mem) /\
    LENGTH bytes < dimword (:256) /\
    (LENGTH bytes = 0 \/ w2n off + LENGTH bytes <= z.vs_alloca_next) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z) /\
    return_buf_frame d ce en z /\ ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts /\ alloca_history func z /\
    se.cs_next_var <= en.cs_next_var /\ s.vs_alloca_next <= z.vs_alloca_next /\
    wb_frame ce ee ee se s z /\ ghost_kept_at lo ce ee se G tn s Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule log_data_payload_core_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (
    qexistsl [`ats`,`avs`,`buf`,`cap`,`hl`,`rows`,`st`] >>
    reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `(rows = [] /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
    >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    suspend "legacy_driver") >>
  first_assum ACCEPT_TAC
QED

Resume log_data_payload_mods[legacy_driver]:
  map_every qx_gen_tac [`p`,`b`,`u`,`Gu`,`tu`,`inst`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_op = Var p` SUBST_ALL_TAC >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (mp_then (Pos hd)
      (qspecl_then [`rows`,`inst`,`hl`,`explicit`,`en`,`bytes`,`avs`,`ats`,`len_op`,`PG`]
        (mp_tac o PURE_REWRITE_RULE [ADD_0])) abi_tuple_linked_loop_mods) >>
  impl_tac >- (
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `!p b. Var _ = Var p ==> _` (qspecl_then [`p`,`b`] mp_tac) >>
    simp_tac (srw_ss()) []) >>
  disch_then ACCEPT_TAC
QED

Finalise log_data_payload_mods

Theorem log_data_payload_with_cursor_mods:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\ immutable_frame_mods func ce cx ee s) /\
  return_buf_frame d ce se s /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  EVERY (safe_operand se) ops /\ EVERY (\op. op_taint tn op = {}) ops /\
  eval_operands ops s = SOME topics /\
  LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                     abi_member_head_size at) rows ats /\
  LIST_REL abi_encoder_layout_valid ats avs /\
  hl = head_lengths ats 0 /\ bytes = enc (Tuple ats) (ListV avs) /\
  ((rows = [] /\ en = se /\ len_op = Lit 0w /\ ptr_op = Lit 0w) \/
   (rows <> [] /\ cap = abi_size_bound ce.ce_struct_fields (TupleT (MAP SND rows)) /\
    LENGTH bytes <= cap /\ cap < dimword (:256) /\
    compile_alloc_buffer cap se = (buf,st) /\ ptr_op = buf.buf_operand /\
    compile_abi_encode_values_to_buf ce ptr_op rows st = (len_op,en) /\
    fn_has_code se st func /\ fn_has_code st en func /\
    (!p b owner. ptr_op = Var p /\ MEM owner (fn_insts func) /\
      owner.inst_opcode = ALLOCA /\ owner.inst_id = se.cs_next_id /\
      owner.inst_outputs = [p] /\ not_local_ptr ce ee.scopes p /\
      se.cs_next_id < st.cs_next_id ==>
      !ci r. MEM ci (fn_insts func) /\ ci.inst_id = st.cs_next_id /\
        ci.inst_opcode = ALLOCA /\ ci.inst_outputs = [r] /\ not_local_ptr ce ee.scopes r ==>
      !i a c v Gv tv cursor slot. i < LENGTH rows /\ cursor = Var r /\
        abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
          se.cs_next_id b cap p p 0 [] a v Gv tv /\
        abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot i a v Gv tv /\
        compile_abi_encode_value_rows ce (Var p) cursor
          (SUM (MAP (abi_embedded_static_size ce.ce_struct_fields o SND) (TAKE i rows)))
          [EL i rows] a = ((),c) /\ fn_has_code a c func ==>
        ?q Gq tq.
          abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
            se.cs_next_id b cap p p 0 [] c q Gq tq /\
          abi_tuple_row_effects_mods ce ee func se.cs_next_id b cap 0 st.cs_next_id
            a v Gv tv c q Gq tq /\
          abi_encode_values_prefix_at ats avs hl b cursor st.cs_next_id slot (SUC i) c q Gq tq /\
          !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,Gv,tv) [] (OK q,Gq,tq)))) ==>
  ?z Gz tz off.
    eval_operands ops z = SOME topics /\
    eval_operand ptr_op z = SOME off /\ eval_operand len_op z = SOME (n2w (LENGTH bytes)) /\
    EVERY (\op. op_taint tz op = {}) (ptr_op::len_op::ops) /\
    (LENGTH bytes <> 0 ==> ?p. ptr_op = Var p /\ ptr_covers Gz tz p z (LENGTH bytes)) /\
    mem_bytes_at (w2n off) (LENGTH bytes) z.vs_memory = bytes /\
    (!i. w2n off <= i /\ i < w2n off + LENGTH bytes ==> i NOTIN tz.t_mem) /\
    LENGTH bytes < dimword (:256) /\
    (LENGTH bytes = 0 \/ w2n off + LENGTH bytes <= z.vs_alloca_next) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee z /\ storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gz tz z /\ immutable_frame_mods func ce cx ee z) /\
    return_buf_frame d ce en z /\ ~z.vs_halted /\ z.vs_current_bb = en.cs_current_bb /\
    z.vs_inst_idx = LENGTH en.cs_current_insts /\ alloca_history func z /\
    se.cs_next_var <= en.cs_next_var /\ s.vs_alloca_next <= z.vs_alloca_next /\
    wb_frame ce ee ee se s z /\ ghost_kept_at lo ce ee se G tn s Gz tz /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  irule log_data_payload_core_mods >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- (
    qexistsl [`ats`,`avs`,`buf`,`cap`,`hl`,`rows`,`st`] >>
    reverse conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
    qpat_x_assum `(rows = [] /\ _) \/ _` (DISJ_CASES_THEN strip_assume_tac)
    >- (disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disj2_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    suspend "cursor_driver") >>
  first_assum ACCEPT_TAC
QED

Resume log_data_payload_with_cursor_mods[cursor_driver]:
  map_every qx_gen_tac [`p`,`b`,`u`,`Gu`,`tu`,`owner`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `ptr_op = Var p` SUBST_ALL_TAC >>
  qhdtm_assum `abi_tuple_buffer_state_mods`
    (mp_then (Pos hd)
      (qspecl_then [`rows`,`owner`,`hl`,`explicit`,`en`,`bytes`,`avs`,`ats`,`len_op`,`PG`]
        (mp_tac o PURE_REWRITE_RULE [ADD_0])) abi_tuple_linked_loop_with_cursor_mods) >>
  impl_tac >- (
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >- (
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `!p b owner. Var _ = Var p /\ _ ==> _`
      (qspecl_then [`p`,`b`,`owner`] mp_tac) >>
    impl_tac >- (rewrite_tac[REFL_CLAUSE] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
    disch_then ACCEPT_TAC) >>
  disch_then ACCEPT_TAC
QED

Finalise log_data_payload_with_cursor_mods

(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  abiDecoderArrayHeader compileEnv exprLoweringProps emitHelperProps fragExec
  decoderNavigationPtr instIdxIndep venomInst venomExecSemantics
  fragExecPtr decoderArraySetupPtr decoderSetupStepPtr wordLoadStorePtr fragGasOriginPtr fragGasSeqPtr fragGasSeqMem
  memSafeRun ghostPcTransportPtr fragGasOrigin instMemFrontier ptrSafetyTransport decoderGhostFramePtr words finite_map pred_set
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel
  sourcePrimitiveGasMem sourceBulkGasMem
  sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr abiDecoderSequenceReach
  decoderPrimitiveObservations decoderWorldFramePtr
  sourceBulkArrayLayout calldataBulkReentry calldataBulkUniformPtr
  abiDecoderBulkExecute abiStaticDynarrayLayout calldataTypedRobustPtr dynarrayLiveRobustPtr
  abiDecoderClampedWord abiDecoderBytesTyped abiValueEncoding
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr abiDecoderReentry
  venomState abiDecoderBytes calldataDynOwned abiDecoderFrameCompose
  allocaFrontierBound allocaBudgetProps venomMemDefs ptrDiscipline bodyPtrDefs arithmetic

Theorem source_bulk_header_origin[local]:
  abi_decode_array_header (Var root) src CALLDATALOAD sa = (cnt,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  lookup_var root s = SOME (n2w d) /\ d < dimword (:256) /\
  ptr_covers G tn root s capacity /\ 32 <= capacity /\ not_fresh_at sa root /\
  eval_operand src s = SOME a /\ op_taint tn src = {} ==>
  ?H u.
    ptr_covers H u root t capacity /\ op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    eval_operand cnt t = SOME (abi_decode_load CALLDATALOAD a s) /\
    (!op. abi_decoder_operand_live sa.cs_next_var op ==> eval_operand op t = eval_operand op s) /\
    u.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32} /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_halted = s.vs_halted /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn
        (s with vs_inst_idx := LENGTH sa.cs_current_insts)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\ d + 32 <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
        (s with vs_inst_idx := LENGTH sa.cs_current_insts,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >>
  `eval_operand (Var root) s = SOME (n2w d) /\
   abi_decoder_operand_live sa.cs_next_var (Var root)` by
    simp[eval_operand_def, calldata_operand_live_not_fresh] >>
  drule_all calldata_array_header_repeat_sequence >> strip_tac >>
  qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
  simp[abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def] >> pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,sm)` >>
  rename1 `emit_void MSTORE [Var root; cnt] sm = ((),sb)` >>
  `inst_extends sa sm /\ inst_extends sm sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa sm ++ emitted_insts sm sb` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK s1` >>
  `run_inst_seq (emitted_insts sa sm)
    (s with vs_inst_idx := LENGTH sa.cs_current_insts) =
    OK (s1 with vs_inst_idx := LENGTH sa.cs_current_insts)` by
    (drule emit_op_run_pc >> simp[is_terminator_def] >>
     disch_then (qspecl_then [`s`,`LENGTH sa.cs_current_insts`] mp_tac) >>
     simp[exec_result_map_def]) >>
  `eval_operand src (s with vs_inst_idx := LENGTH sa.cs_current_insts) = SOME a` by simp[] >>
  drule_all (Q.INST [`s` |-> `s with vs_inst_idx := LENGTH sa.cs_current_insts`,
    `t` |-> `s1 with vs_inst_idx := LENGTH sa.cs_current_insts`]
    (SPEC_ALL emit_calldata_load_endpoint_ptr_origin_core)) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`,`G`] strip_assume_tac) >>
  gvs[lookup_var_def] >>
  suspend "finish"
QED

Resume source_bulk_header_origin[finish]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H u root s1 capacity` by
    (conj_tac >- metis_tac[lookup_var_def] >>
     irule ptr_covers_frame >> metis_tac[lookup_var_def]) >>
  `ptr_covers H u root s1 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `?w. eval_operand cnt s1 = SOME w` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, AllCaseEqs()] >> metis_tac[]) >>
  `t = mstore d w s1` by
    (qpat_x_assum `run_inst_seq (emitted_insts sm sb) _ = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def, eval_operand_def, w2n_n2w] >>
     Cases_on `cnt` >> fs[eval_operand_def]) >>
  `w2n (n2w d : bytes32) = d` by simp[] >>
  drule_all mstore_ghost_frame >> disch_then (qspecl_then [`PG`,`H`] strip_assume_tac) >>
  qabbrev_tac `u2 = step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) s1 t u` >>
  `u2.t_var = u.t_var /\ u2.t_stor = tn.t_stor /\ u2.t_trans = tn.t_trans /\
    u2.t_mem = tn.t_mem DIFF {x | d <= x /\ x < d+32}` by
    (simp[Abbr `u2`] >> metis_tac[]) >>
  `step_prov PG H (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) t = H` by metis_tac[] >>
  qpat_x_assum `!id. _` kall_tac >>
  `u2.t_imm = tn.t_imm` by
    simp[Abbr `u2`, step_taint_def, mk_inst_def, set_var_taint_def, imm_taint_def] >>
  `!op. op_taint u2 op = op_taint u op` by (Cases >> simp[op_taint_def]) >>
  `!x. lookup_var x t = lookup_var x s1` by
    simp[mstore_def, write_memory_with_expansion_def, lookup_var_def] >>
  `ptr_covers H u2 root t capacity` by (irule ptr_covers_frame >> metis_tac[]) >>
  qexistsl_tac [`H`,`u2`] >> simp[] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (drule emitted_insts_emit_op >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK s1` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, AllCaseEqs()] >> strip_tac >>
     gvs[update_var_def, mstore_def, write_memory_with_expansion_def]) >>
  simp[] >>
  conj_tac >- metis_tac[lookup_var_def] >>
  conj_tac >- suspend "backward" >>
  suspend "joint"
QED

Resume source_bulk_header_origin[backward]:
  rpt gen_tac >> strip_tac >>
  `same_blocks sa sm /\ same_blocks sm sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
    s1.vs_alloca_next = s.vs_alloca_next` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  `!fuel. ptr_safe_run D lower fuel ctx func PG H u
     (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` suffices_by
    (strip_tac >> first_x_assum (qspecl_then [`D`,`lower`,`ctx`,`func`] mp_tac) >> simp[]) >>
  `!fuel. ptr_inst_ok D lower fuel ctx func H u
    (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[] >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  irule setup_instruction_continuation >>
  qexistsl_tac [`H`, `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`,
    `sm`, `sb`, `t with vs_inst_idx := LENGTH sm.cs_current_insts`, `u2`] >>
  simp[mk_inst_def, is_terminator_def, same_blocks_def] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
    eval_operand_def, mstore_def, write_memory_with_expansion_def] >>
  Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def, mstore_def,
    write_memory_with_expansion_def, w2n_n2w, Abbr `u2`]
QED

Resume source_bulk_header_origin[joint]:
  rpt gen_tac >> strip_tac >>
  `same_blocks sa sm /\ same_blocks sm sb` by
    metis_tac[emit_op_same_blocks, emit_void_same_blocks] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def, same_blocks_def] >> metis_tac[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\ sb.cs_current_bb = sm.cs_current_bb` by fs[same_blocks_def] >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
    s1.vs_alloca_next = s.vs_alloca_next` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  `ptr_inst_ok D lower 0 ctx func H u
    (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[] >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  `?bb. lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sm.cs_current_insts) =
      SOME (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])` by
    (`?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
      !k. k < LENGTH [mk_inst sm.cs_next_id MSTORE [Var root;cnt] []] ==>
      get_instruction bb (LENGTH sm.cs_current_insts + k) =
        SOME (EL k [mk_inst sm.cs_next_id MSTORE [Var root;cnt] []])` by
       (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
     qexists_tac `bb` >> gvs[] >> first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
      eval_operand_def, lookup_var_def, w2n_n2w] >>
     Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def,
      mstore_def, write_memory_with_expansion_def]) >>
  `inst_mem_below_frontier (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts)` by
    (simp[below_frontier_MSTORE, eval_operand_def, lookup_var_def] >>
     gvs[lookup_var_def]) >>
  suspend "edges"
QED

Resume source_bulk_header_origin[edges]:
  `gas_path_mem_edge ctx func
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.INST [`s` |-> `s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
      `u` |-> `t with vs_inst_idx := LENGTH sm.cs_current_insts`,
      `i` |-> `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`]
      straight_line_mem_edge) >>
     simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >> gvs[ADD1]) >>
  `gas_path_ptr_edge D lower ctx func PG H u
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts) 0 H u2
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (mp_tac (Q.INST [`lo` |-> `lower`, `fn` |-> `func`, `G` |-> `H`, `tn` |-> `u`]
      (Q.INST [`s` |-> `s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
        `u` |-> `t with vs_inst_idx := LENGTH sm.cs_current_insts`,
        `i` |-> `mk_inst sm.cs_next_id MSTORE [Var root;cnt] []`]
        straight_line_ptr_edge)) >>
     simp[mk_inst_def, is_terminator_def, Abbr `u2`] >> gvs[ADD1]) >>
  `gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts,H,u) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u2)` by
    (simp[gas_origin_ptr_edge_def] >> gvs[gas_path_mem_edge_zero_origin]) >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH sm.cs_current_insts,H,u) []
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u2)` by
    (irule (SRULE [] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
       (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
     qexistsl_tac [`H`,`t with vs_inst_idx := LENGTH sb.cs_current_insts`,`u2`] >>
     simp[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  qpat_x_assum `!D lower explicit ctx' func. _` (qspecl_then
    [`D`,`lower`,`explicit`,`ctx`,`func`] mp_tac) >> simp[] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`s1 with vs_inst_idx := LENGTH sm.cs_current_insts`,
    `H`,`u`,`[]`,`OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`,`H`,`u2`] mp_tac) >>
  simp[]
QED

Finalise source_bulk_header_origin

Theorem source_owned_primitive_decoder_ptr:
  abi_decoder_coherent ce env sf ty tv /\
  ((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\ is_word_type ty) \/
   (?m. type_to_abi_dec_info sf ce ty = DecBytestring m)) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env ty v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env ty) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env ty) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env ty) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings
Proof
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  `evaluate_type env ty = SOME tv /\
   type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `((?clamp. type_to_abi_dec_info sf ce ty = DecPrimWord clamp /\
       is_word_type ty /\ type_memory_size tv = 32) \/
    (?m. type_to_abi_dec_info sf ce ty = DecBytestring m /\
       type_memory_size tv = abi_decode_bytes_copy_size m /\ m < dimword (:256)))` by
    (qpat_x_assum `(?clamp. _ /\ is_word_type ty) \/ _` strip_assume_tac
     >- metis_tac[abi_word_type_size] >>
     drule_all coherent_source_bytes_representation >> strip_tac >>
     disj2_tac >> qexists `m` >>
     `m < dimword (:256)` by
       (mp_tac (Q.INST [`n` |-> `m`] abi_decoder_bytes_copy_size) >> decide_tac) >>
     metis_tac[]) >> (
  `type_memory_size tv < dimword (:256) /\ e < dimword (:256) /\
    srcpos < dimword (:256)` by decide_tac >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  `?t H u.
    run_inst_seq (emitted_insts middle end_st) r = OK (t with vs_inst_idx := r.vs_inst_idx) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\
    ptr_covers H u child t (type_memory_size tv) /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem) /\
    abi_decode_frame e (type_memory_size tv) r t /\ fresh_vars_wrt limit t /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!op w. (!x. op = Var x ==> not_fresh_at middle x) /\ eval_operand op r = SOME w ==>
      eval_operand op t = SOME w) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r)` by
    (irule source_primitive_decoder_reentry_ptr >>
     metis_tac[]) >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + type_memory_size tv <= r.vs_alloca_next` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK ((t with vs_inst_idx := r.vs_inst_idx) with
       vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (irule source_primitive_run_gas_path_mem >>
     conj_tac >- simp[] >>
     qexistsl [`child`, `type_to_abi_dec_info sf ce ty`, `e`, `middle`,
       `childsrc`, `type_memory_size tv`] >> metis_tac[]) >>
  `gas_path_mem ctx fn r 0 (OK t)` by
    (qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  drule decoder_primitive_code_shape >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `abi_decode_sim ctx fn r t` by
    (drule_all abi_decoder_run_sequence_reach >>
     qpat_x_assum `t.vs_inst_idx = _` (fn th => simp[GSYM th])) >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >>
     drule decoder_primitive_old_operand >>
     disch_then (qspecl_then [`t with vs_inst_idx := r.vs_inst_idx`,`r`,`op`] mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     simp[eval_operand_def, lookup_var_def]) >>
  drule_all decoder_run_world_frame >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  qexistsl [`t`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac bool_ss [] >>
  conj_tac >- metis_tac[abi_decode_frame_footprint] >>
  conj_tac >-
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  conj_tac >-
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     pure_asm_rewrite_tac [allocas_from_def] >> simp_tac bool_ss []) >>
  simp_tac bool_ss [LESS_EQ_REFL] >>
  `lookup_var root t = lookup_var root r` by
    (qpat_x_assum `!op. abi_decoder_operand_live _ op ==> _` (qspec_then `Var root` mp_tac) >>
     simp[eval_operand_def]) >>
  qpat_x_assum `ptr_covers G tn root r outsz` mp_tac >>
  pure_rewrite_tac[ptr_covers_def] >>
  `FLOOKUP H root = FLOOKUP G root /\ op_taint u (Var root) = op_taint tn (Var root)` by
    metis_tac[] >>
  pure_asm_rewrite_tac[] >> simp_tac bool_ss [])
QED

Theorem source_owned_bulk_array_ptr:
  abi_decoder_coherent ce env sf (ArrayT ety (Dynamic maxn)) tv /\
  ~is_abi_dynamic ce.ce_struct_fields ety /\
  ~dec_info_needs_clamp (type_to_abi_dec_info sf ce ety) /\
  compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn))) middle = ((),end_st) /\
  value_has_type tv v /\
  vyper_to_abi env (ArrayT ety (Dynamic maxn)) v = SOME av /\
  mem_bytes_at srcpos (LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av))
    r.vs_call_ctx.cc_calldata = enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av /\
  srcpos + LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) < dimword (:256) /\
  eval_operand childsrc r = SOME (n2w srcpos) /\
  lookup_var child r = SOME (n2w e) /\ lookup_var root r = SOME (n2w d) /\
  abi_decoder_operand_live middle.cs_next_var childsrc /\
  abi_decoder_operand_live middle.cs_next_var (Var child) /\
  abi_decoder_operand_live middle.cs_next_var (Var root) /\
  ptr_covers G tn child r (type_memory_size tv) /\
  ptr_covers G tn root r outsz /\ op_taint tn childsrc = {} /\ op_prov G childsrc = NONE /\
  alloca_inv r /\ alloca_frontier_inv ctx fn site r /\
  unit_alloca_budget ctx < dimword (:256) /\
  FLOOKUP r.vs_allocas oid = SOME (base_addr,owner_cap) /\
  (oid < middle.cs_next_id \/ end_st.cs_next_id <= oid) /\
  base_addr <= e /\ e + type_memory_size tv <= base_addr + owner_cap /\
  e + type_memory_size tv < dimword (:256) /\
  (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
    FLOOKUP r.vs_allocas id = SOME (p,k) ==>
    k = 32 /\ p < dimword (:256) /\ p+32 <= r.vs_alloca_next /\
    ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
      ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
  fn_has_code middle end_st fn /\ fn_inst_ids_distinct fn /\
  (middle.cs_blocks = end_st.cs_blocks \/
    !bb. lookup_block end_st.cs_current_bb fn.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  end_st.cs_next_var <= limit.cs_next_var /\ fresh_vars_wrt limit r /\
  allocas_from lower r /\ lower <= r.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~r.vs_halted /\ r.vs_current_bb = middle.cs_current_bb /\
  r.vs_inst_idx = LENGTH middle.cs_current_insts ==>
  ?t H u.
    abi_decode_sim ctx fn r t /\
    gas_path_mem ctx fn r 0 (OK t) /\
    (!D explicit. gas_origin_ptr_path (D, lower, explicit, ctx, fn, PG) (r, G, tn) [] (OK t, H, u)) /\
    ~t.vs_halted /\ t.vs_current_bb = end_st.cs_current_bb /\
    t.vs_inst_idx = LENGTH end_st.cs_current_insts /\ fresh_vars_wrt limit t /\
    val_in_memory tv v e t.vs_memory /\
    (!mem. mem_agree_outside u.t_mem t.vs_memory mem ==>
      val_in_memory tv v e mem) /\
    abi_decode_footprint_frame [(e,type_memory_size tv)] r t /\
    alloca_inv t /\ alloca_frontier_inv ctx fn site t /\ allocas_from lower t /\
    r.vs_alloca_next <= t.vs_alloca_next /\
    FLOOKUP t.vs_allocas oid = SOME (base_addr,owner_cap) /\
    (!id p k. FLOOKUP r.vs_allocas id = SOME (p,k) ==>
      FLOOKUP t.vs_allocas id = SOME (p,k)) /\
    (!id. id < middle.cs_next_id \/ end_st.cs_next_id <= id ==>
      FLOOKUP t.vs_allocas id = FLOOKUP r.vs_allocas id) /\
    (!id p k. middle.cs_next_id <= id /\ id < end_st.cs_next_id /\
      FLOOKUP t.vs_allocas id = SOME (p,k) ==>
      k = 32 /\ p < dimword (:256) /\ p+32 <= t.vs_alloca_next /\
      ?ins. MEM ins (fn_insts fn) /\ ins.inst_id = id /\
        ins.inst_opcode = ALLOCA /\ ins.inst_operands = [Lit 32w]) /\
    ptr_covers H u child t (type_memory_size tv) /\ ptr_covers H u root t outsz /\
    (!op. abi_decoder_operand_live middle.cs_next_var op ==>
      eval_operand op t = eval_operand op r) /\
    (!x. not_fresh_at middle x ==> FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    u.t_mem SUBSET tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx fn PG H u t) ==>
      !fuel. ptr_safe_run D lower fuel ctx fn PG G tn r) /\
    t.vs_accounts = r.vs_accounts /\ t.vs_transient = r.vs_transient /\
    t.vs_logs = r.vs_logs /\ t.vs_outcomes = r.vs_outcomes /\
    t.vs_requests = r.vs_requests /\
    t.vs_pending_deletions = r.vs_pending_deletions /\ t.vs_tx_ctx = r.vs_tx_ctx /\
    t.vs_block_ctx = r.vs_block_ctx /\ t.vs_fmp = r.vs_fmp /\
    t.vs_gas_readings = r.vs_gas_readings /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all source_bulk_array_layout >> strip_tac >>
  `evaluate_type env (ArrayT ety (Dynamic maxn)) = SOME tv` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `type_to_abi_dec_info sf ce (ArrayT ety (Dynamic maxn)) =
    DecDynArray (type_to_abi_dec_info sf ce ety) (abi_embedded_static_size ce.ce_struct_fields ety)
      (type_memory_size etv) F maxn` by
    simp[exprLoweringTheory.type_to_abi_dec_info_def] >>
  `0 < type_slot_size etv /\
   1 + maxn * type_slot_size etv < dimword (:256)` by
    (qpat_x_assum `evaluate_type env (ArrayT _ _) = _` mp_tac >>
     pure_asm_rewrite_tac [Once vyperValueTheory.evaluate_type_def] >>
     simp_tac (srw_ss()) [LET_THM, AllCaseEqs(), vyperValueTheory.type_slot_size_def]) >>
  `maxn <= maxn * type_slot_size etv` by
    (Cases_on `type_slot_size etv` >- decide_tac >> simp[MULT_SUC]) >>
  `maxn < dimword (:256)` by decide_tac >>
  `type_memory_size tv = 32 + maxn * type_memory_size etv` by
    metis_tac[valueEncodingTheory.type_memory_size_def] >>
  `LENGTH vs * type_memory_size etv <= maxn * type_memory_size etv` by
    simp[LE_MULT_RCANCEL] >>
  `32 + LENGTH vs * type_memory_size etv <= type_memory_size tv /\
   e+32 < dimword (:256) /\ LENGTH vs * type_memory_size etv < dimword (:256)` by
    decide_tac >>
  `LENGTH (enc (vyper_to_abi_type env (ArrayT ety (Dynamic maxn))) av) =
    32 + LENGTH vs * type_memory_size etv` by
    (pure_asm_rewrite_tac [listTheory.LENGTH_APPEND] >> simp_tac (srw_ss()) []) >>
  `srcpos+32 < dimword (:256) /\ srcpos < dimword (:256)` by decide_tac >>
  `mem_word_at srcpos r.vs_call_ctx.cc_calldata = n2w (LENGTH vs) /\
   mem_bytes_at (srcpos+32) (LENGTH vs * type_memory_size etv)
     r.vs_call_ctx.cc_calldata = FLAT (MAP (enc (vyper_to_abi_type env ety)) avs)` by
    (irule abiDecoderBulkTheory.static_dynarray_source_windows >>
     pure_asm_rewrite_tac [] >>
     conj_tac >-
       (qpat_x_assum `mem_bytes_at srcpos _ _ = _` mp_tac >>
        pure_rewrite_tac [vyperABITheory.vyper_to_abi_type_def] >>
        pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
     metis_tac[]) >>
  `abi_decode_load CALLDATALOAD (n2w srcpos : bytes32) r = n2w (LENGTH vs)` by
    (qpat_x_assum `mem_word_at srcpos _ = _` mp_tac >>
     simp_tac (srw_ss()) [abiDecoderContractTheory.abi_decode_load_def,
       abiDecoderContractTheory.abi_decode_source_def, valueEncodingDefsTheory.mem_word_at_def,
       valueEncodingDefsTheory.mem_bytes_at_def, wordsTheory.w2n_n2w] >>
     `srcpos MOD dimword (:256) = srcpos` by simp[] >>
     pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `eval_operand (Var child) r = SOME (n2w e)` by simp[eval_operand_def] >>
  qpat_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _`
    (assume_tac o PURE_ONCE_REWRITE_RULE
      [exprLoweringTheory.type_to_abi_dec_info_def]) >>
  `compile_abi_decode_to_buf (Var child) childsrc CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray (type_to_abi_dec_info sf ce ety)
      (abi_embedded_static_size ce.ce_struct_fields ety) (type_memory_size etv) F maxn)
      middle = ((),end_st)` by metis_tac[] >>
  drule_all calldata_bulk_reentry_sequence >> strip_tac >>
  `base_addr + owner_cap <= r.vs_alloca_next` by
    metis_tac[alloca_inv_def, alloca_next_valid_def] >>
  `e + (32 + LENGTH vs * type_memory_size etv) <= r.vs_alloca_next /\
   e + (32 + LENGTH vs * type_memory_size etv) < dimword (:256)` by decide_tac >>
  `gas_path_mem ctx fn r 0
     (OK (t with vs_inst_idx := LENGTH end_st.cs_current_insts))` by
    (drule_all source_bulk_run_gas_path_mem >> simp_tac (srw_ss()) []) >>
  `not_fresh_at middle child /\ not_fresh_at middle root /\
   (!x. childsrc = Var x ==> not_fresh_at middle x)` by
    (conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     conj_tac >- metis_tac[calldata_operand_live_not_fresh] >>
     rpt strip_tac >> metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all calldata_bulk_decoder_endpoint_ptr_uniform >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `val_in_memory tv v e t.vs_memory` by
    (pure_asm_rewrite_tac [] >>
     irule static_dynarray_canonical_layout >> metis_tac[]) >>
  `!mem. mem_agree_outside u.t_mem t.vs_memory mem ==> val_in_memory tv v e mem` by
    (rpt strip_tac >> pure_asm_rewrite_tac [] >> irule clean_live_prefix_dynarray_robust >>
     metis_tac[vyperTypingTheory.all_have_type_EVERY]) >>
  `abi_decode_source_opcode CALLDATALOAD` by
    simp[abiDecoderContractTheory.abi_decode_source_opcode_def] >>
  drule_all abiDecoderBulkTheory.abi_decoder_bulk_shape >> strip_tac >>
  drule_all abi_decoder_bulk_allocation_shape >> strip_tac >>
  `inst_extends middle end_st` by
    (pure_asm_rewrite_tac [emitHelperPropsTheory.inst_extends_def,
       exprLoweringPropsTheory.emitted_insts_def] >>
     metis_tac[rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_LENGTH_APPEND]) >>
  drule_all abi_decoder_run_sequence_reach >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qpat_x_assum `t' = _` SUBST_ALL_TAC >>
  `t.vs_labels = r.vs_labels` by
    metis_tac[ctorAbiActualObservationsTheory.ctor_actual_sequence_labels] >>
  `!op. abi_decoder_operand_live middle.cs_next_var op ==>
    eval_operand op t = eval_operand op r` by
    (rpt strip_tac >> Cases_on `op` >>
     simp_tac (srw_ss()) [eval_operand_def] >>
     metis_tac[calldata_operand_live_not_fresh]) >>
  drule_all decoder_run_world_frame >> strip_tac >>
  `alloca_inv t` by
    (qpat_x_assum `alloca_inv r` mp_tac >>
     pure_asm_rewrite_tac [alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def] >>
     simp_tac bool_ss []) >>
  `alloca_frontier_inv ctx fn site t` by
    (qpat_x_assum `alloca_frontier_inv ctx fn site r` mp_tac >>
     pure_asm_rewrite_tac [alloca_frontier_inv_def, remaining_alloca_budget_def] >>
     simp_tac bool_ss []) >>
  `allocas_from lower (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (qpat_x_assum `allocas_from lower r` mp_tac >>
     simp_tac (srw_ss()) [allocas_from_def] >> pure_asm_rewrite_tac [] >> simp_tac bool_ss []) >>
  `ptr_covers H u root t outsz` by
    (irule decoderGhostFramePtrTheory.ptr_covers_frame >> metis_tac[]) >>
  `abi_decode_frame e (type_memory_size tv) r t` by
    (irule abiDecoderFrameComposeTheory.abi_decode_frame_widen >>
     qexistsl [`e`,`32 + LENGTH vs * type_memory_size etv`] >>
     pure_asm_rewrite_tac [] >> decide_tac) >>
  `abi_decode_footprint_frame [(e,type_memory_size tv)] r
     (t with vs_inst_idx := LENGTH end_st.cs_current_insts)` by
    (simp_tac (srw_ss()) [GSYM abi_decode_frame_footprint,
       abiDecoderContractTheory.abi_decode_frame_def] >>
     metis_tac[abiDecoderContractTheory.abi_decode_frame_def]) >>
  qpat_x_assum `tv = _` SUBST_ALL_TAC >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  qexistsl [`t with vs_inst_idx := LENGTH end_st.cs_current_insts`,`H`,`u`] >>
  pure_asm_rewrite_tac [] >>
  simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def,
    lookup_var_def, eval_operand_def] >>
  pure_asm_rewrite_tac [] >> simp_tac bool_ss [] >>
  conj_tac >- (qpat_assum `fresh_vars_wrt _ t` mp_tac >>
    simp_tac (srw_ss()) [loweringStateRelDefsTheory.fresh_vars_wrt_def]) >>
  simp_tac arith_ss [] >>
  conj_tac >- (qpat_x_assum `ptr_covers H u child t _` mp_tac >>
    pure_asm_rewrite_tac [] >> simp_tac arith_ss []) >>
  metis_tac[]
QED

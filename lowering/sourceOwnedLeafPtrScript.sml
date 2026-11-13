(* The allocation-free leaves of the owned source decoder contract: primitive
   words and bytestrings, and dynamic arrays of static elements without clamp
   (copied in bulk).  Neither allocates scratch. *)
Theory sourceOwnedLeafPtr
Ancestors
  fragGasOriginPtr fragGasSeqPtr fragGasSeqMem venomExecSemantics emitHelper
  emitHelperProps compileEnv finite_map pred_set valueEncodingProps
  ptrSafetyTransport fragExecPtr entryDispatchPtr calldataClampPtr
  decoderNavigationPtr venomInstProps abiEncoder abiDecoderContract
  calldataWordPtr instSeqComposePtr calldataOverwritePtr venomInst list
  unitTransformDefs ptrSafeRun contextCodegenRel memSafeRun codegenRel fragExec
  loweringStateRelDefs decoderGhostFramePtr exprLoweringProps
  ghostPcTransportPtr instIdxIndep abiDecoderArrayHeader decoderArraySetupPtr
  decoderSetupStepPtr wordLoadStorePtr fragGasOrigin instMemFrontier words
  ptrDiscipline sourcePrimitiveGasMem sourceBulkGasMem abiDecoderGuards
  abiDecoderDynarrayPrefix abiDecoderDynarrayBound abiDecoderBulk
  venomExecProofs decoderArrayInitPtr decoderGuardClampCorePtr venomInstProofs
  rich_list memLocDefs decoderRawEndpointPtr abiDecoderComposition
  moduleLoweringProps sourceOwnedArrayLoopPtr sourcePrimitiveReentryPtr
  abiDecoderSequenceReach decoderPrimitiveObservations decoderWorldFramePtr
  sourceBulkArrayLayout calldataBulkReentry calldataBulkUniformPtr
  abiDecoderBulkExecute abiStaticDynarrayLayout calldataTypedRobustPtr
  dynarrayLiveRobustPtr abiDecoderClampedWord abiDecoderBytesTyped
  abiValueEncoding abiCanonicalBytes valueTypingMemoryProps exprSimProps
  abiDecoderCoherence sourceBytesRepresentation calldataDecodePtr
  abiDecoderReentry venomState abiDecoderBytes calldataDynOwned
  abiDecoderFrameCompose allocaFrontierBound allocaBudgetProps venomMemDefs
  bodyPtrDefs arithmetic calldataBulkPayloadPtr

Theorem source_bulk_copy_origin[local]:
  emit_void CALLDATACOPY [Var p;src;n] sa = ((),sb) /\
  eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
  eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) /\
  op_taint tn src = {} /\ op_taint tn n = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!root cap. ptr_covers G tn root s cap ==> ptr_covers H u root t cap) /\
    u.t_mem SUBSET tn.t_mem /\
    (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
      op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      (!fuel. ptr_safe_run D lower fuel ctx func PG H u
        (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
      !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      w2n dw + w2n nw <= s.vs_alloca_next ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  `t = write_memory_with_expansion (w2n dw)
    (TAKE (w2n nw)
      (DROP (w2n sw) s.vs_call_ctx.cc_calldata ++ REPLICATE (w2n nw) 0w)) s` by
    gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def] >>
  drule_all calldatacopy_ghost_frame >>
  disch_then (qspecl_then [`tn`,`sa.cs_next_id`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [
    `step_prov PG G (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) t`,
    `step_taint (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s t tn`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
        !k. k < LENGTH [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []] ==>
          get_instruction bb (LENGTH sa.cs_current_insts + k) =
            SOME (EL k [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []])` by
        (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
      irule calldatacopy_safe_continuation >> simp[] >>
      qexistsl_tac [`dw`,`sa.cs_next_id`,`n`,`nw`,`p`,`src`,`sw`] >>
      simp[ADD1] >> conj_tac
      >- fs[ptr_covers_def] >>
      first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  rpt strip_tac >>
  `?bb. lookup_block sa.cs_current_bb func.fn_blocks = SOME bb /\
    !k. k < LENGTH [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []] ==>
      get_instruction bb (LENGTH sa.cs_current_insts + k) =
        SOME (EL k [mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []])` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >> simp[]) >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `step_inst_base (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s = OK t` by
    simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  `ptr_inst_ok D lower 0 ctx func G tn
     (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s` by
    (`access_ok lower G func (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s` by
       (irule calldatacopy_access_ok >> metis_tac[]) >>
     `taint_ok func tn (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s` by
       (irule calldatacopy_taint_ok >> fs[ptr_covers_def]) >>
     simp[ptr_inst_ok_def, mk_inst_def, step_inst_non_invoke,
       step_inst_base_opcode_eqs, write_memory_with_expansion_def,
       write_memory_def, expand_memory_def]) >>
  `gas_path_ptr_edge D lower ctx func PG G tn s 0
     (step_prov PG G (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) t)
     (step_taint (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s t tn)
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (pure_rewrite_tac [mk_inst_def] >> irule (SRULE [mk_inst_def] (Q.INST
       [`i` |-> `mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []`]
       straight_line_ptr_edge)) >>
     fs[mk_inst_def, is_terminator_def] >> metis_tac[]) >>
  `inst_mem_below_frontier (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s` by
    simp[below_frontier_CALLDATACOPY] >>
  `gas_path_mem_edge ctx func s 0 (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    (pure_rewrite_tac [mk_inst_def] >> irule (SRULE [mk_inst_def] (Q.INST
       [`i` |-> `mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []`]
       straight_line_mem_edge)) >>
     fs[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >> metis_tac[]) >>
  `gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG) (s,G,tn) []
     (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
      step_prov PG G (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) t,
      step_taint (mk_inst sa.cs_next_id CALLDATACOPY [Var p;src;n] []) s t tn)` by
    (simp[gas_origin_ptr_edge_def] >>
     metis_tac[gas_path_mem_edge_zero_origin]) >>
  `~t.vs_halted` by
    simp[write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  rewrite_tac[listTheory.APPEND] >> disch_then irule >>
  asm_rewrite_tac[ADD1] >>
  irule (cj 1 gas_origin_ptr_path_rules) >>
  simp[write_memory_with_expansion_def, write_memory_def, expand_memory_def]
QED

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
(* A single emitted scalar instruction, with its canonical ghost update. *)
Theorem source_bulk_instruction_origin[local]:
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [i] /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_inst_ok D lower 0 ctx func G tn i s /\
  step_inst_base i s = OK t ==>
  gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i` by
    (drule_all fn_has_code_same_block >> strip_tac >>
     qexists_tac `bb` >> simp[] >>
     first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx func s 0
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqMemTheory.straight_line_mem_edge] >>
  `gas_path_ptr_edge D lower ctx func PG G tn s 0
    (step_prov PG G i t) (step_taint i s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[fragGasSeqPtrTheory.straight_line_ptr_edge] >>
  `step_inst 0 ctx i s = OK t` by simp[step_inst_non_invoke] >>
  `~t.vs_halted` by metis_tac[step_preserves_halted] >>
  `gas_origin_ptr_edge (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i t, step_taint i s t tn)` by
    (simp[gas_origin_ptr_edge_def] >>
     metis_tac[fragGasOriginTheory.gas_path_mem_edge_zero_origin]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >>
  simp[cj 1 gas_origin_ptr_path_rules]
QED

Theorem source_bulk_compare_origin[local]:
  emit_op GT [src; Lit bound] sa = (out,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
          (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
       !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `out = "%" ++ toString sa.cs_next_var` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id GT [src; Lit bound] [out]` >>
  `step_inst_base inst s =
    OK (update_var out (bool_to_word (w2n a > w2n bound)) s)` by
    (simp[Abbr `inst`] >> irule step_GT >> simp[eval_operand_def]) >>
  `t = update_var out (bool_to_word (w2n a > w2n bound)) s` by
    (qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
     qpat_x_assum `step_inst_base inst s = _` mp_tac >>
     simp[Abbr `inst`, Abbr `out`, run_inst_seq_def] >> metis_tac[]) >>
  `step_inst_base inst s = OK t` by metis_tac[] >>
  `!x. not_fresh_at sa x ==> x <> out` by
    (simp[not_fresh_at_def, Abbr `out`] >> metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `H = step_prov PG G inst t` >>
  qabbrev_tac `u = step_taint inst s t tn` >>
  `!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)` by
    (rpt gen_tac >> strip_tac >>
     `ptr_inst_ok D lower 0 ctx func G tn inst s` by
       (`op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
        qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
        simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `inst`, mk_inst_def, step_inst_non_invoke,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          update_var_def] >> metis_tac[]) >>
     `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     simp[NoAsms, Abbr `H`, Abbr `u`] >>
     qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
     irule source_bulk_instruction_origin >>
     goal_assum (drule_at Any) >>
     simp[Abbr `inst`, Abbr `out`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]) >>
  qpat_x_assum `!D lower explicit ctx func. _` (assume_tac o SRULE []) >>
  qexistsl_tac [`H`,`u`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> strip_tac >>
     irule decoderSetupStepPtrTheory.setup_instruction_continuation >>
     goal_assum (drule_at Any) >>
     qexistsl_tac [`H`,`inst`,`sb`,`t`,`u`] >>
     `!fuel. ptr_inst_ok D lower fuel ctx func G tn inst s` by
       (gen_tac >>
        `op_taint tn (Lit bound) = {}` by simp[op_taint_def] >>
        qpat_x_assum `step_inst_base inst s = OK t` mp_tac >>
        simp[ptr_inst_ok_def, access_ok_def, taint_ok_def,
          Abbr `inst`, mk_inst_def, step_inst_non_invoke,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          update_var_def] >> metis_tac[]) >>
     gvs[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`, mk_inst_def,
       is_terminator_def, update_var_def]) >>
  simp[] >>
  simp[Abbr `H`, Abbr `u`, Abbr `inst`, Abbr `out`,
    lookup_var_def, op_prov_def, step_prov_def, out_prov_def, set_prov_def,
    op_taint_def, step_taint_def, out_taint_def, set_var_taint_def,
    FLOOKUP_UPDATE, FLOOKUP_DRESTRICT, mk_inst_def,
    mem_taint_def, new_site_bytes_def, step_writes_def,
    written_taint_def, store_taint_def, imm_taint_def, adopt_reset_def,
    update_var_def, source_memory_write_ranges_def, range_bytes_def,
    pred_setTheory.EXTENSION, FDOM_DRESTRICT, SF CONJ_ss] >>
  simp[FLOOKUP_DEF, SF CONJ_ss] >>
  conj_tac >- (qexists_tac `t.vs_vars` >> simp[update_var_def]) >>
  reverse conj_tac >-
    (qpat_x_assum `!D lower explicit ctx func. _` mp_tac >>
     simp[update_var_def, step_prov_def, out_prov_def, set_prov_def,
       step_taint_def, out_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, new_site_bytes_def, step_writes_def, written_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def,
       source_memory_write_ranges_def, range_bytes_def,
       pred_setTheory.EXTENSION, FDOM_DRESTRICT, FLOOKUP_DEF, SF CONJ_ss]) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  gen_tac >> disch_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by metis_tac[] >>
  simp[FLOOKUP_DEF, SF CONJ_ss]
QED

Theorem source_bulk_iszero_origin[local]:
  emit_op ISZERO [op] sa = (out,sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u.
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
          (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
       !fuel. ptr_safe_run D lower fuel ctx func PG G tn s)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    op_taint u out = {} /\ op_prov H out = NONE /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_op_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ISZERO [op]
    ["%" ++ toString sa.cs_next_var]` >>
  `step_inst_base inst s = OK t` by
    gvs[Abbr `inst`, run_inst_seq_def, AllCaseEqs()] >>
  `MEM ISZERO [SIGNEXTEND; SHR; SHL; EQ; ISZERO; ASSERT] /\
   EVERY (\op. op_taint tn op = {} /\ op_prov G op = NONE) [op]` by simp[] >>
  `?vars. t = s with vs_vars := vars` by
    (qpat_assum `step_inst_base inst s = OK t` mp_tac >>
     simp[Abbr `inst`] >> metis_tac[clamp_scalar_state_frame, MEM]) >>
  qexistsl_tac [`step_prov PG G inst t`, `step_taint inst s t tn`] >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >> strip_tac >>
     `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
       (drule_all fn_has_code_same_block >> strip_tac >>
        qexists_tac `bb` >> simp[Abbr `inst`] >>
        first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
     `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     irule clamp_scalar_continuation >>
     simp[] >>
     qexistsl_tac [`sa.cs_next_id`,`ISZERO`,`[op]`,
       `["%" ++ toString sa.cs_next_var]`,`t`] >>
     gvs[Abbr `inst`]) >>
  conj_tac >-
    (rpt gen_tac >> strip_tac >>
     `ptr_inst_ok D lower 0 ctx func G tn inst s` by
       (simp[Abbr `inst`] >>
        irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
        simp[step_inst_non_invoke, mk_inst_def] >>
        qexists_tac `t` >> gvs[step_inst_non_invoke, mk_inst_def] >>
        simp[]) >>
     `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
     qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
     irule source_bulk_instruction_origin >> goal_assum (drule_at Any) >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def,
       inst_mem_below_frontier_def, inst_dload_in_section_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     qexistsl_tac [`sa`,`sb`] >> simp[mk_inst_def]) >>
  `EVERY (\op. op_taint tn op = {}) [op]` by simp[] >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  conj_tac >- (simp[Abbr `inst`] >> metis_tac[clamp_scalar_output_ghost]) >>
  `!x. not_fresh_at sa x ==> x <> "%" ++ toString sa.cs_next_var` by
    (simp[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  simp[Abbr `inst`] >>
  qpat_x_assum `step_inst_base _ _ = _` (assume_tac o SRULE []) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (assume_tac o SRULE []) >>
  drule_all clamp_scalar_taint_frame >>
  disch_then (qspec_then `tn` strip_assume_tac) >>
  gvs[] >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  gen_tac >> disch_tac >>
  `x <> "%" ++ toString sa.cs_next_var` by (simp[] >> metis_tac[]) >>
  qpat_x_assum `x <> _` (assume_tac o SRULE []) >>
  conj_tac >-
    (irule clamp_scalar_lookup_frame >> goal_assum (drule_at Any) >> simp[]) >>
  simp[mk_inst_def, step_prov_other_output, step_taint_other_output]
QED
Theorem source_bulk_assert_origin[local]:
  emit_void ASSERT [op] sa = ((),sb) /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  (!D lower ctx func.
    fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!fuel. ptr_safe_run D lower fuel ctx func PG G tn
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
    !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
  t = s /\
  (!D lower explicit ctx func.
    fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G,tn))
Proof
  strip_tac >> conj_tac
  >- (drule_all emit_assert_endpoint_ptr_core >>
      disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] mp_tac) >>
      metis_tac[]) >>
  `t = s` by (drule_all emit_assert_endpoint_ptr_core >> metis_tac[]) >>
  drule emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    (drule emit_void_same_blocks >> simp[same_blocks_def]) >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ASSERT [op] []` >>
  `step_inst_base inst s = OK s` by
    gvs[Abbr `inst`, run_inst_seq_def, AllCaseEqs()] >>
  simp[NoAsms] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  `ptr_inst_ok D lower 0 ctx func G tn inst s` by
    (simp[Abbr `inst`] >>
     irule (cj 1 (SRULE [ptr_safe_step_def] clamp_scalar_step_safe)) >>
     simp[step_inst_non_invoke, mk_inst_def] >> qexists_tac `s` >>
     gvs[step_inst_non_invoke, mk_inst_def]) >>
  `step_prov PG G inst s = G /\ step_taint inst s s tn = tn` by
    simp[Abbr `inst`, mk_inst_def, step_prov_def, set_prov_def,
      step_taint_def, set_var_taint_def, mem_taint_def, new_site_bytes_def,
      step_writes_def, written_taint_def, store_taint_def, imm_taint_def,
      adopt_reset_def, source_memory_write_ranges_def, range_bytes_def,
      DRESTRICT_UNIV, FLOOKUP_DEF, taint_component_equality,
      pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `LENGTH sb.cs_current_insts = SUC s.vs_inst_idx` by simp[] >>
  qpat_assum `LENGTH sb.cs_current_insts = _` (fn th => rewrite_tac [th]) >>
  qpat_x_assum `t = s` SUBST_ALL_TAC >>
  `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
   ~is_terminator inst.inst_opcode /\ inst_mem_below_frontier inst s /\
   inst_dload_in_section inst s` by
    simp[Abbr `inst`, mk_inst_def, is_terminator_def,
      inst_mem_below_frontier_def, inst_dload_in_section_def,
      source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  drule_all source_bulk_instruction_origin >>
  disch_then (qspecl_then [`explicit`,`PG`] mp_tac) >> simp[]
QED


Theorem source_bulk_count_guard_origin[local]:
  abi_decode_count_guard CALLDATALOAD src maxn sa = (cnt,sb) /\
  eval_operand src s = SOME a /\ op_taint tn src = {} /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u. op_taint u cnt = {} /\ op_prov H cnt = NONE /\
    (?vars. t = s with vs_vars := vars) /\
    u.t_mem = tn.t_mem /\ u.t_stor = tn.t_stor /\
    u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    (!D lower explicit ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u)) /\
    (!D lower ctx func.
      fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
      ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ((!fuel. ptr_safe_run D lower fuel ctx func PG H u
          (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
       !fuel. ptr_safe_run D lower fuel ctx func PG G tn s))
Proof
  strip_tac >>
  qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
  simp[abi_decode_count_guard_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op CALLDATALOAD [src] sa = (cnt,c1)` >>
  rename1 `emit_op GT [cnt; Lit (n2w maxn)] c1 = (cmp,c2)` >>
  rename1 `emit_op ISZERO [cmp] c2 = (ok,c3)` >>
  rename1 `emit_void ASSERT [ok] c3 = ((),sb)` >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\
    inst_extends c2 c3 /\ inst_extends c3 sb` by
    metis_tac[inst_extends_emit_op, inst_extends_emit_void] >>
  `emitted_insts sa sb = emitted_insts sa c1 ++
    (emitted_insts c1 c2 ++ (emitted_insts c2 c3 ++ emitted_insts c3 sb))` by
    (fs[inst_extends_def] >> metis_tac[emitted_insts_append, APPEND_ASSOC]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> pure_asm_rewrite_tac [] >>
  disch_then (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  qpat_x_assum `run_inst_seq (_ ++ _) _ = OK t`
    (mp_then Any strip_assume_tac run_inst_seq_append_ok) >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `s2.vs_inst_idx = s.vs_inst_idx /\ s3.vs_inst_idx = s.vs_inst_idx /\
    t.vs_inst_idx = s.vs_inst_idx` by
    (imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     gvs[run_inst_seq_def, AllCaseEqs()] >>
     imp_res_tac step_inst_base_preserves_inst_idx >>
     gvs[mk_inst_def, is_terminator_def]) >>
  drule_all emit_calldata_load_endpoint_ptr_origin_core >>
  disch_then (qspecl_then [`G`,`ARB`,`ARB`,`PG`,`ARB`] mp_tac) >>
  strip_tac >>
  suspend "segments"
QED

Resume source_bulk_count_guard_origin[segments]:
  rename1 `op_taint u1 cnt = {}` >> rename1 `op_prov H1 cnt = NONE` >>
  `?vars1. s1 = s with vs_vars := vars1` by
    (qpat_assum `emit_op CALLDATALOAD _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts sa c1) s = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read1_def, AllCaseEqs(), update_var_def] >> metis_tac[]) >>
  `?b. eval_operand cnt s1 = SOME b` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, AllCaseEqs()] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c1 c2)
    (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
    OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `emit_op GT _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `eval_operand cnt (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) = SOME b` by
    (Cases_on `cnt` >> gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c1 c2) s1 = _` kall_tac >>
  drule_all source_bulk_compare_origin >>
  disch_then (qspecl_then [`PG`,`H1`] mp_tac) >> strip_tac >>
  rename1 `op_taint u2 cmp = {}` >> rename1 `op_prov H2 cmp = NONE` >>
  `run_inst_seq (emitted_insts c2 c3)
    (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
    OK (s3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op ISZERO _ _ = _` (mp_then Any mp_tac emit_op_run_pc) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c2 c3) s2 = _` kall_tac >>
  drule_all source_bulk_iszero_origin >>
  disch_then (qspec_then `PG` mp_tac) >> strip_tac >>
  rename1 `op_taint u3 ok = {}` >> rename1 `op_prov H3 ok = NONE` >>
  `run_inst_seq (emitted_insts c3 sb)
    (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) =
    OK (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (qpat_assum `emit_void ASSERT _ _ = _`
      (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def, exec_result_map_def]) >>
  qpat_x_assum `run_inst_seq (emitted_insts c3 sb) s3 = _` kall_tac >>
  drule_all source_bulk_assert_origin >> disch_then (qspec_then `PG` mp_tac) >>
  strip_tac >> suspend "frames"
QED

Resume source_bulk_count_guard_origin[frames]:
  `s2 = s1 with vs_vars := vars /\ s3 = s2 with vs_vars := vars' /\ t = s3` by
    (qpat_x_assum `s2 with vs_inst_idx := _ = _` mp_tac >>
     qpat_x_assum `s3 with vs_inst_idx := _ = _` mp_tac >>
     qpat_x_assum `t with vs_inst_idx := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `!x. cnt = Var x ==> not_fresh_at c1 x` by
    (qpat_assum `emit_op CALLDATALOAD _ sa = _`
      (mp_then Any mp_tac abi_decoder_operand_live_emit) >>
     Cases_on `cnt` >> simp[calldata_operand_live_not_fresh]) >>
  `!x. cnt = Var x ==> not_fresh_at c2 x` by
    (rpt strip_tac >> `not_fresh_at c1 x` by metis_tac[] >>
     gvs[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  qexistsl_tac [`H3`,`u3`] >>
  conj_tac >- (Cases_on `cnt` >> gvs[op_taint_def] >> metis_tac[]) >>
  conj_tac >- (Cases_on `cnt` >> gvs[op_prov_def] >> metis_tac[]) >>
  conj_tac >- (qexists_tac `vars'` >> simp[]) >>
  simp[] >>
  conj_tac >- (fs[lookup_var_def] >> rpt strip_tac >> metis_tac[]) >>
  conj_tac >- suspend "joint" >> suspend "backward"
QED

Resume source_bulk_count_guard_origin[joint]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def] >>
     metis_tac[emit_op_same_blocks, emit_void_same_blocks, same_blocks_def]) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   c2.cs_current_bb = sa.cs_current_bb /\ c3.cs_current_bb = sa.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> gvs[same_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (`cs_extends c2 sb` by metis_tac[cs_extends_trans] >>
     `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
     drule_all (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
  gvs[] >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  `allocas_from lower (s with vs_vars := vars1) /\
   allocas_from lower (s with vs_vars := vars) /\
   allocas_from lower (s with vs_vars := vars')` by (fs[allocas_from_def] >> metis_tac[]) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code sa c1 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c1 c2 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c2 c3 func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_x_assum `!D lower explicit ctx func. fn_has_code c3 sb func /\ _ ==> _`
    (drule_all_then (qspecl_then [`D`,`explicit`] assume_tac)) >>
  qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] _`
    (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[NoAsms] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[NoAsms] >>
  disch_then (mp_then Any mp_tac gas_origin_ptr_path_append) >> simp[NoAsms] >>
  disch_then drule >> simp[]
QED

Resume source_bulk_count_guard_origin[backward]:
  rpt (qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac) >>
  rpt (qpat_x_assum `!x. not_fresh_at _ x ==> _` kall_tac) >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (rpt conj_tac >> irule cs_extends_same_block >> fs[inst_extends_def] >>
     metis_tac[emit_op_same_blocks, emit_void_same_blocks, same_blocks_def]) >>
  `c1.cs_current_bb = sa.cs_current_bb /\
   c2.cs_current_bb = sa.cs_current_bb /\ c3.cs_current_bb = sa.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> gvs[same_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (`cs_extends c2 sb` by metis_tac[cs_extends_trans] >>
     `cs_extends c1 sb` by metis_tac[cs_extends_trans] >>
     drule_all (Q.SPECL [`sa`,`c1`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c1`,`c2`,`sb`,`func`] fn_has_code_split) >> strip_tac >>
     drule_all (Q.SPECL [`c2`,`c3`,`sb`,`func`] fn_has_code_split) >> simp[]) >>
  gvs[] >>
  rpt (qpat_x_assum `run_inst_seq _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `emit_op _ _ _ = _` kall_tac) >>
  qpat_x_assum `emit_void _ _ _ = _` kall_tac >>
  `allocas_from lower (s with vs_vars := vars1) /\
   allocas_from lower (s with vs_vars := vars) /\
   allocas_from lower (s with vs_vars := vars')` by (fs[allocas_from_def] >> metis_tac[]) >>
  simp[]
QED

Finalise source_bulk_count_guard_origin

(* Split the successful concrete bulk run before choosing any ghosts. *)
Theorem source_bulk_phase_runs[local]:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?count_op c1 cnt c2 s1 s2.
    abi_decode_count_guard CALLDATALOAD src maxn sa = (count_op,c1) /\
    abi_decode_array_header (Var root) src CALLDATALOAD c1 = (cnt,c2) /\
    abi_decode_bulk_payload (Var root) src cnt mem_sz CALLDATALOAD (Lit 0w) c2 = ((),sb) /\
    inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb /\
    cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 sb /\
    sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
    same_blocks sa c1 /\ same_blocks c1 c2 /\
    (!x. cnt = Var x ==> not_fresh_at c2 x) /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2) /\
    run_inst_seq (emitted_insts sa c1) s = OK s1 /\
    run_inst_seq (emitted_insts c1 c2) s1 = OK s2 /\
    run_inst_seq (emitted_insts c2 sb) s2 = OK t
Proof
  strip_tac >>
  `abi_decode_source_opcode CALLDATALOAD` by simp[abi_decode_source_opcode_def] >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases,
    abi_decode_dynarray_position_prefix_def,
    compile_abi_dec_addr_def,
    abiDecoderBytesBoundTheory.abi_decode_bytes_head_def,
    abi_decode_dynarray_payload_guard_def, abi_decode_dynarray_end_guard_def,
    abi_decode_bulk_body_def, comp_bind_def, comp_ignore_bind_def,
    comp_return_def, LET_THM, eval_operand_def, ADD_CLAUSES,
    abi_decoder_operand_live_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  rename1 `abi_decode_count_guard CALLDATALOAD src maxn sa = (count_op,c1)` >>
  rename1 `abi_decode_array_header (Var root) src CALLDATALOAD c1 = (cnt,c2)` >>
  `inst_extends sa c1 /\ inst_extends c1 c2 /\ inst_extends c2 sb` by
    (imp_res_tac abi_decode_count_guard_shape >>
     qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def,
       abi_decode_array_header_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   same_blocks sa c1 /\ same_blocks c1 c2 /\
   (!x. cnt = Var x ==> not_fresh_at c2 x) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts c1 c2)` by
    (qpat_x_assum `abi_decode_count_guard _ _ _ _ = _` mp_tac >>
     qpat_x_assum `abi_decode_array_header _ _ _ _ = _` mp_tac >>
     simp[abi_decode_count_guard_def, abi_decode_array_header_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[same_blocks_def, not_fresh_at_def, is_terminator_def, mk_inst_def] >>
     rename1 `emit_op CALLDATALOAD [src] c1 = (_,mid)` >>
     `emitted_insts c1 c2 = emitted_insts c1 mid ++ emitted_insts mid c2` by
       (irule emitted_insts_append >> simp[]) >> simp[is_terminator_def]) >>
  `cs_extends sa c1 /\ cs_extends c1 c2` by
    fs[cs_extends_def, same_blocks_def, inst_extends_def] >>
  `cs_extends c2 sb` by
    (qpat_x_assum `abi_decode_bulk_payload _ _ _ _ _ _ _ = _` mp_tac >>
     simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
     imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     imp_res_tac inst_extends_trans >> fs[cs_extends_def, same_blocks_def, inst_extends_def] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 sb` by
    (imp_res_tac inst_extends_trans >> metis_tac[emitted_insts_append,inst_extends_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >> asm_rewrite_tac[] >> strip_tac >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 sb) s2 = OK t` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa c1) s = OK s1` >>
  qexistsl_tac [`s1`,`s2`] >> simp[]
QED

Theorem source_bulk_payload_origin_from_copy[local]:
  (!sa p src n sb s dw sw nw G tn t PG.
    emit_void CALLDATACOPY [Var p;src;n] sa = ((),sb) /\
    eval_operand (Var p) s = SOME dw /\ eval_operand src s = SOME sw /\
    eval_operand n s = SOME nw /\ ptr_covers G tn p s (w2n nw) /\
    op_taint tn src = {} /\ op_taint tn n = {} /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    ?H u.
      (!root cap. ptr_covers G tn root s cap ==> ptr_covers H u root t cap) /\
      u.t_mem SUBSET tn.t_mem /\
      (!i. w2n dw <= i /\ i < w2n dw + w2n nw ==> i NOTIN u.t_mem) /\
      u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
      (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint u (Var x) = op_taint tn (Var x)) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      (!D lower ctx func.
        fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
        s.vs_current_bb = sa.cs_current_bb /\
        s.vs_inst_idx = LENGTH sa.cs_current_insts /\
        (!fuel. ptr_safe_run D lower fuel ctx func PG H u
          (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
        !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
      (!D lower explicit ctx func.
        fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
        ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
        s.vs_inst_idx = LENGTH sa.cs_current_insts /\
        w2n dw + w2n nw <= s.vs_alloca_next ==>
        gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
          (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))) ==>
  abi_decode_bulk_payload (Var root) src cnt mem_sz CALLDATALOAD (Lit 0w) sa = ((),sb) /\
  lookup_var root s = SOME (n2w d) /\ eval_operand src s = SOME a /\
  eval_operand cnt s = SOME (n2w n) /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. cnt = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s capacity /\
  op_taint tn src = {} /\ op_prov G src = NONE /\
  op_taint tn cnt = {} /\ op_prov G cnt = NONE /\
  32 + n * mem_sz <= capacity /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  d + 32 + n * mem_sz <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    ptr_covers H u root t capacity /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d+32 <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  disch_tac >>
  simp[abi_decode_bulk_payload_def, compile_abi_dec_addr_def, comp_return_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] sa = (sz,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (sd,c2)` >>
  rename1 `emit_op ADD [Var root; Lit 32w] c2 = (dd,c3)` >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `emitted_insts sa sb = emitted_insts sa c1 ++ emitted_insts c1 c2 ++
    emitted_insts c2 c3 ++ emitted_insts c3 sb` by
    (imp_res_tac inst_extends_trans >>
     metis_tac[emitted_insts_append, inst_extends_def]) >>
  qpat_x_assum `run_inst_seq _ s = OK t` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 sb) s3 = OK t` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  dxrule run_inst_seq_append_ok >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `cs_extends sa c1 /\ cs_extends c1 c2 /\ cs_extends c2 c3 /\ cs_extends c3 sb` by
    (imp_res_tac emit_op_same_blocks >> imp_res_tac emit_void_same_blocks >>
     fs[cs_extends_def, same_blocks_def, inst_extends_def]) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
   fn_has_code c2 c3 func /\ fn_has_code c3 sb func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  `eval_operand sz s1 = SOME (n2w n * n2w mem_sz) /\
   s1.vs_labels = s.vs_labels /\ s2.vs_labels = s1.vs_labels /\
   s3.vs_labels = s2.vs_labels /\
   s1.vs_current_bb = s.vs_current_bb /\ s2.vs_current_bb = s1.vs_current_bb /\
   s3.vs_current_bb = s2.vs_current_bb /\
   s1.vs_alloca_next = s.vs_alloca_next /\
   s2.vs_alloca_next = s1.vs_alloca_next /\ s3.vs_alloca_next = s2.vs_alloca_next /\
   s1.vs_allocas = s.vs_allocas /\ s2.vs_allocas = s1.vs_allocas /\
   s3.vs_allocas = s2.vs_allocas /\
   ~s1.vs_halted /\ ~s2.vs_halted /\ ~s3.vs_halted` by
    (imp_res_tac emitted_insts_emit_op >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE, AllCaseEqs()]) >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz) /\
   op_taint tn (Lit (n2w mem_sz)) = {} /\
   op_prov G (Lit (n2w mem_sz)) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `MUL`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `op_taint u1 sz = {}` >> rename1 `op_prov H1 sz = NONE` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  qpat_assum `!x. not_fresh_at sa x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
  `eval_operand src s1 = SOME a /\
   eval_operand (Lit 32w) s1 = SOME 32w /\
   op_taint u1 (Lit 32w) = {} /\ op_prov H1 (Lit 32w) = NONE` by
    simp[eval_operand_def, op_taint_def, op_prov_def] >>
  `run_inst_seq (emitted_insts c1 c2)
      (s1 with vs_inst_idx := LENGTH c1.cs_current_insts) =
      OK (s2 with vs_inst_idx := LENGTH c1.cs_current_insts)` by
    (qpat_assum `emit_op ADD [src; Lit 32w] c1 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s1`,`LENGTH c1.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  drule_all (SRULE [eval_op_inst_idx] (Q.INST [`opc` |-> `ADD`,
    `s` |-> `s1 with vs_inst_idx := LENGTH c1.cs_current_insts`,
    `t` |-> `s2 with vs_inst_idx := LENGTH c1.cs_current_insts`]
    (SPEC_ALL emit_scalar_binop_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `op_taint u2 sd = {}` >> rename1 `op_prov H2 sd = NONE` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  fs[lookup_var_def] >>
  `sa.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var /\
   c2.cs_next_var <= c3.cs_next_var` by
    (imp_res_tac emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x /\ not_fresh_at c3 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `lookup_var root s2 = SOME (n2w d) /\ ptr_covers H2 u2 root s2 capacity` by
    (gvs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  `eval_operand (Lit 32w) s2 = SOME (n2w 32) /\
   op_taint u2 (Lit 32w) = {} /\ op_prov H2 (Lit 32w) = NONE /\
   32 + n*mem_sz <= capacity /\ w2n (n2w d : bytes32)+32 < dimword (:256)` by
    (`d < dimword (:256)` by decide_tac >>
     simp[eval_operand_def, op_taint_def, op_prov_def, w2n_n2w]) >>
  `run_inst_seq (emitted_insts c2 c3)
      (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
      OK (s3 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (qpat_assum `emit_op ADD [Var root; Lit 32w] c2 = _` (mp_then Any mp_tac emit_op_run_pc) >>
     disch_then (qspecl_then [`s2`,`LENGTH c2.cs_current_insts`] mp_tac) >>
     simp[is_terminator_def, exec_result_map_def]) >>
  `ptr_covers H2 u2 root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) capacity` by
    simp[ptr_covers_def, lookup_var_def] >>
  drule_all (SRULE [eval_op_inst_idx, cj 4 control_moves_keep_vars]
    (Q.INST [`off` |-> `32`, `n` |-> `n*mem_sz`,
      `s` |-> `s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,
      `t` |-> `s3 with vs_inst_idx := LENGTH c2.cs_current_insts`]
      (SPEC_ALL emit_ptr_offset_endpoint_ptr_origin_core))) >>
  disch_then (qspecl_then [`ARB`,`ARB`,`ARB`,`PG`] strip_assume_tac) >>
  rename1 `dd = Var q` >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` kall_tac >>
  rename1 `u3.t_mem = u2.t_mem` >>
  rename1 `gas_origin_ptr_path _ (_,H2,u2) [] (_,H3,u3)` >>
  `(!x. sz = Var x ==> not_fresh_at c1 x) /\
   (!x. sd = Var x ==> not_fresh_at c2 x)` by
    (imp_res_tac abiDecoderReentryTheory.abi_decoder_operand_live_emit >>
     conj_tac >> rpt strip_tac >> gvs[] >>
     fs[calldata_operand_live_not_fresh]) >>
  `!x. sz = Var x ==> not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >>
     qpat_x_assum `!x. sz = Var x ==> _` drule >>
     simp[not_fresh_at_def] >> disch_then irule >> decide_tac) >>
  qpat_assum `!x. not_fresh_at c1 x ==> _`
    (mp_then Any mp_tac (SRULE[lookup_var_def] old_operand_ghost_frame)) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sz` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  qpat_assum `!x. not_fresh_at c2 x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `sd` mp_tac) >> simp[lookup_var_def] >> strip_tac >>
  `eval_operand sd s2 = SOME (a + 32w)` by
    (qpat_assum `emit_op ADD [src; Lit 32w] c1 = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  `d < dimword (:256)` by decide_tac >>
  `eval_operand (Var q) s3 = SOME (n2w (d+32)) /\
   eval_operand sz s3 = SOME (n2w (n*mem_sz)) /\
   ptr_covers H3 u3 q s3 (w2n (n2w (n*mem_sz):bytes32))` by
    (fs[w2n_n2w, word_mul_n2w] >> simp[eval_operand_def, lookup_var_def]) >>
  `emit_void CALLDATACOPY [Var q;sd;sz] c3 = ((),sb)` by
    fs[abi_decode_copy_opcode_def] >>
  `run_inst_seq (emitted_insts c3 sb)
      (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) =
      OK (t with vs_inst_idx := LENGTH c3.cs_current_insts)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     simp[run_inst_seq_inst_idx, is_terminator_def, mk_inst_def, exec_result_map_def]) >>
  `eval_operand (Var q) (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w (d+32)) /\
   eval_operand sd (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (a+32w) /\
   eval_operand sz (s3 with vs_inst_idx := LENGTH c3.cs_current_insts) = SOME (n2w (n*mem_sz)) /\
   ptr_covers H3 u3 q (s3 with vs_inst_idx := LENGTH c3.cs_current_insts)
     (w2n (n2w (n*mem_sz):bytes32))` by
    simp[eval_op_inst_idx, ptr_covers_def, lookup_var_def] >>
  qpat_assum `!sa p src n sb s dw sw nw G tn t PG. _`
    (fn th => drule_all (Q.INST
      [`s` |-> `s3 with vs_inst_idx := LENGTH c3.cs_current_insts`,
       `t` |-> `t with vs_inst_idx := LENGTH c3.cs_current_insts`,
       `PG` |-> `PG`] (SPEC_ALL th))) >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `u4.t_mem SUBSET u3.t_mem` >>
  rename1 `gas_origin_ptr_path _ (_,H3,u3) [] (_,H4,u4)` >>
  fs[] >>
  qpat_x_assum `!sa p src n sb s dw sw nw G tn t PG. _` kall_tac >>
  `allocas_from lower s1 /\ allocas_from lower s2 /\ allocas_from lower s3 /\
   s1.vs_current_bb = c1.cs_current_bb /\
   s2.vs_current_bb = c2.cs_current_bb /\
   s3.vs_current_bb = c3.cs_current_bb` by
    (imp_res_tac emit_op_same_blocks >> fs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  qexistsl [`H4`,`u4`] >>
  simp[w2n_n2w] >>
  conj_tac >-
    (qpat_assum `!root cap. ptr_covers H3 u3 root _ cap ==> _` irule >>
     simp[ptr_covers_def, lookup_var_def] >>
     gvs[ptr_covers_def, lookup_var_def, w2n_n2w] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (fs[lookup_var_def] >> metis_tac[]) >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
     (OK (s1 with vs_inst_idx := LENGTH c1.cs_current_insts),H1,u1)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s1 with vs_inst_idx := LENGTH c1.cs_current_insts,H1,u1) []
     (OK (s2 with vs_inst_idx := LENGTH c2.cs_current_insts),H2,u2)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s2 with vs_inst_idx := LENGTH c2.cs_current_insts,H2,u2) []
     (OK (s3 with vs_inst_idx := LENGTH c3.cs_current_insts),H3,u3)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
     (s3 with vs_inst_idx := LENGTH c3.cs_current_insts,H3,u3) []
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H4,u4)` by simp[] >>
  metis_tac[gas_origin_ptr_path_append, APPEND]

QED

Theorem source_bulk_decoder_origin[local]:
  compile_abi_decode_to_buf (Var root) src CALLDATALOAD (Lit 0w) (Lit 0w)
    (DecDynArray ei abi_sz mem_sz F maxn) sa = ((),sb) /\
  ~dec_info_needs_clamp ei /\ lookup_var root s = SOME (n2w d) /\
  eval_operand src s = SOME a /\ abi_decode_load CALLDATALOAD a s = n2w n /\
  not_fresh_at sa root /\ (!x. src = Var x ==> not_fresh_at sa x) /\
  ptr_covers G tn root s capacity /\ op_taint tn src = {} /\ op_prov G src = NONE /\
  32+n*mem_sz <= capacity /\ d+32 < dimword (:256) /\ n*mem_sz < dimword (:256) /\
  d+32+n*mem_sz <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t /\ ~s.vs_halted /\
  fn_has_code sa sb func /\ allocas_from lower s /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?H u.
    ptr_covers H u root t capacity /\ u.t_mem SUBSET tn.t_mem /\
    (!i. d <= i /\ i < d+32+n*mem_sz ==> i NOTIN u.t_mem) /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\ u.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x)) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!D. (!fuel. ptr_safe_run D lower fuel ctx func PG H u
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)) ==>
     !fuel. ptr_safe_run D lower fuel ctx func PG G tn s) /\
    (!D explicit. gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),H,u))
Proof
  strip_tac >> drule_all source_bulk_phase_runs >> strip_tac >>
  drule_all source_bulk_count_guard_origin >>
  disch_then (qspecl_then [`PG`,`G`] strip_assume_tac) >>
  rename1 `op_taint u1 count_op = {}` >> rename1 `op_prov H1 count_op = NONE` >>
  `!x. not_fresh_at sa x ==> not_fresh_at c1 x /\ not_fresh_at c2 x` by
    (simp[not_fresh_at_def] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  `s1.vs_labels = s.vs_labels /\ s1.vs_current_bb = s.vs_current_bb /\
   s1.vs_allocas = s.vs_allocas /\ s1.vs_alloca_next = s.vs_alloca_next /\
   ~s1.vs_halted` by simp[] >>
  qpat_assum `!x. not_fresh_at sa x ==> _`
    (mp_then Any mp_tac old_operand_ghost_frame) >>
  disch_then (qspec_then `src` mp_tac) >> simp[] >> strip_tac >>
  `lookup_var root s1 = SOME (n2w d) /\ ptr_covers H1 u1 root s1 capacity` by
    (conj_tac >- metis_tac[] >> irule ptr_covers_frame >> metis_tac[]) >>
  `not_fresh_at c1 root /\ 32 <= capacity /\ d < dimword (:256)` by
    (simp[] >> decide_tac) >>
  `eval_operand src s1 = SOME a` by fs[] >>
  drule_all source_bulk_header_origin >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `op_taint u2 cnt = {}` >> rename1 `op_prov H2 cnt = NONE` >>
  `abi_decoder_operand_live c1.cs_next_var src` by
    (Cases_on `src` >> fs[abi_decoder_operand_live_def, calldata_operand_live_not_fresh] >> metis_tac[]) >>
  `eval_operand src s2 = SOME a /\ op_taint u2 src = {} /\ op_prov H2 src = NONE` by
    (conj_tac >- metis_tac[] >> Cases_on `src` >>
     fs[op_taint_def, op_prov_def] >> metis_tac[]) >>
  `lookup_var root s2 = SOME (n2w d) /\ not_fresh_at c2 root /\
   (!x. src = Var x ==> not_fresh_at c2 x)` by metis_tac[] >>
  `eval_operand cnt s2 = SOME (n2w n)` by
    (qpat_x_assum `s1 = s with vs_vars := _` SUBST_ALL_TAC >>
     fs[abi_decode_load_def, abi_decode_source_def]) >>
  `fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\ fn_has_code c2 sb func` by
    (imp_res_tac cs_extends_trans >> metis_tac[fn_has_code_split]) >>
  `allocas_from lower s1 /\ allocas_from lower s2 /\ ~s2.vs_halted /\
   s1.vs_current_bb = c1.cs_current_bb /\ s2.vs_current_bb = c2.cs_current_bb /\
   d+32+n*mem_sz <= s2.vs_alloca_next` by
    (fs[allocas_from_def, same_blocks_def] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts c2 sb)
     (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) =
     OK (t with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    metis_tac[decoderHeaderRawPtrTheory.calldata_bulk_payload_run_pc] >>
  `lookup_var root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w d) /\
   eval_operand src (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME a /\
   eval_operand cnt (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) = SOME (n2w n) /\
   ptr_covers H2 u2 root (s2 with vs_inst_idx := LENGTH c2.cs_current_insts) capacity /\
   allocas_from lower (s2 with vs_inst_idx := LENGTH c2.cs_current_insts)` by
    (gvs[lookup_var_def, eval_op_inst_idx, ptr_covers_def, allocas_from_def] >> metis_tac[]) >>
  mp_tac (SRULE [] (Q.INST
    [`sa` |-> `c2`, `G` |-> `H2`, `tn` |-> `u2`,
     `s''` |-> `s2 with vs_inst_idx := LENGTH c2.cs_current_insts`,
     `t` |-> `t with vs_inst_idx := LENGTH c2.cs_current_insts`]
    (MATCH_MP source_bulk_payload_origin_from_copy
      (Q.GENL [`sa`,`p`,`src`,`n`,`sb`,`s`,`dw`,`sw`,`nw`,`G`,`tn`,`t`,`PG`]
        (SPEC_ALL source_bulk_copy_origin))))) >>
  (impl_tac >- simp[]) >>
  strip_tac >> rename1 `u3.t_mem SUBSET u2.t_mem` >>
  rename1 `ptr_covers H3 u3 root _ capacity` >>
  qexistsl [`H3`,`u3`] >>
  conj_tac >- (fs[ptr_covers_def, lookup_var_def] >> metis_tac[]) >>
  conj_tac >- (fs[SUBSET_DEF] >> gvs[]) >>
  conj_tac >-
    (rpt strip_tac >> Cases_on `i < d+32`
     >- (qpat_x_assum `u3.t_mem SUBSET u2.t_mem` mp_tac >>
         simp[SUBSET_DEF] >> metis_tac[]) >>
     gvs[]) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >> fs[lookup_var_def] >> metis_tac[]) >>
  rpt gen_tac >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG) (s,G,tn) []
    (OK (s1 with vs_inst_idx := LENGTH c1.cs_current_insts),H1,u1)` by metis_tac[] >>
  `gas_origin_ptr_path (D,lower,explicit,ctx,func,PG)
    (s1 with vs_inst_idx := LENGTH c1.cs_current_insts,H1,u1) []
    (OK (s2 with vs_inst_idx := LENGTH c2.cs_current_insts),H2,u2)` by
      (first_assum irule >> simp[] >> decide_tac) >>
  gvs[] >> metis_tac[gas_origin_ptr_path_append, APPEND]
QED

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
  `e+32+LENGTH vs * type_memory_size etv <= r.vs_alloca_next` by decide_tac >>
  drule_all source_bulk_decoder_origin >>
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

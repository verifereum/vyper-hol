(* Transport the read-only dynamic Slice capture to the first bound's PC. *)
Theory exprSimSliceDynamicStartEntry
Ancestors
  exprSimSliceCaptureControl exprSimConvertBytes exprSimWordArgs
  bodyPtrBytestringBuiltinsCalldataReserved bodyFullGhostFrame
  bodyFullUnwrapRun bodyFullIfExpReach bodyFullHashKeccakFixed[qualified,ignore_grammar]
  ghostPcTransportPtr exprLoweringProps loweringPosts loweringStateRelDefs
  bodyMemoryDefs vyperStorageFootprint venomState exprSimDefs stateRelProj
  exprSimSliceMemory bodyPtrSignedConvertSourceFixed builtinBytesMemory
  instSeqPtrLo fragGasSeqPtr bodyPtrDefs venomExecSemantics
  bodyPtrBopOperandRetention bodyPtrPrecompileBuiltinsGhost stmtSimLogArgs
  logTopicFramePtr stmtSimLogTopics abiEncodeOwnership exprSimHashBoundary
  valueEncodingProofs valueEncodingDefs compileEnv vyperValue supportedTypes
  vyperTypeSystem vyperTyping ptrDiscipline bodyPtrBytestringBuiltinsAllocation
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr list

Theorem slice_dynamic_capture_start_entry:
  compile_bytestring_src src_op st1 = ((src_len,src_data),sc) /\
  fn_has_code st1 sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st1 /\ sa.cs_next_var <= st1.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!x. src_op = Var x ==> not_fresh_at st1 x) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx src es sa st1 s0 mid v src_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  return_buf_frame d cenv sa s0 /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = st1.cs_current_bb /\ t.vs_inst_idx = LENGTH st1.cs_current_insts /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
  eval_operand src_op t = SOME p /\
  run_inst_seq (emitted_insts st1 sc) t = OK captured /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) []
    (OK (captured with vs_inst_idx := LENGTH sc.cs_current_insts),Gu,tu)) /\
  captured = t with vs_vars := captured.vs_vars /\
  tn1.t_mem = tu.t_mem /\ tn1.t_stor = tu.t_stor /\
  tn1.t_trans = tu.t_trans /\ tn1.t_imm = tu.t_imm /\
  (!x. not_fresh_at st1 x ==>
    lookup_var x captured = lookup_var x t /\ FLOOKUP Gu x = FLOOKUP G1 x /\
    op_taint tu (Var x) = op_taint tn1 (Var x)) ==>
  ?u. u = captured with vs_inst_idx := LENGTH sc.cs_current_insts /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu) /\
      stmt_state_rel H ctx func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid Gu tu u) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx src es sa sc s0 mid v src_op captured) /\
    eval_operand src_op u = SOME p /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    return_buf_frame d cenv sc u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z)
Proof
  strip_tac >>
  drule slice_bytestring_src_control >> strip_tac >>
  `st1.cs_next_var <= sc.cs_next_var /\ st1.cs_next_id <= sc.cs_next_id` by
    (qspec_then `st1` mp_tac (Q.SPEC `src_op` ci_mono_compile_bytestring_src) >>
     simp[ci_mono_def]) >>
  qabbrev_tac `u = captured with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `eval_operand src_op captured = SOME p` by
    (Cases_on `src_op` >> fs[eval_operand_def] >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid captured` by
    (rpt strip_tac >> irule stmt_state_rel_reserved_vars_update >>
     qexists_tac `t` >> qexists_tac `st1` >> simp[] >>
     metis_tac[expr_post_state]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx src es sa sc s0 mid v src_op captured` by
    (rpt strip_tac >> irule convert_readonly_expr_post >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`p`,`t`,`st1`,`src_op`] >> simp[] >>
     qpat_assum `captured = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
      stmt_state_rel H ctx func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid Gu tu u` by
    (gen_tac >> disch_tac >> simp[Abbr `u`,stmt_state_rel_inst_idx] >>
     conj_tac >- metis_tac[expr_post_def] >>
     simp[ghost_inv_at_inst_idx] >> irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G1`,`mid`,`t`,`st1`,`tn1`] >> simp[] >>
     qpat_assum `captured = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >>
     simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
      mid.storage_trace` by fs[storage_trace_domain_def] >>
  `return_buf_frame d cenv sc u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >>
     conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ captured`
           (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
         (impl_tac >- simp[]) >>
         simp[NoAsms,expr_post_def,lookup_var_def,Abbr `u`]) >>
     `captured.vs_alloca_next = t.vs_alloca_next` by
       (qpat_assum `captured = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
     simp[Abbr `u`] >> decide_tac) >>
  `alloca_history func u` by
    (simp[NoAsms,Abbr `u`] >> irule emitted_alloca_history >>
     qpat_assum `run_inst_seq (emitted_insts st1 sc) t = OK captured` (irule_at Any) >>
     qexists_tac `st1` >> simp[] >>
     reverse conj_tac
     >- (drule slice_bytestring_src_zero_code >> simp[listTheory.EVERY_MEM]) >>
     metis_tac[expr_post_state,stmt_state_rel_local_ptrs_alloca]) >>
  qexists_tac `u` >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom] >>
  `~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb` by
    (simp[NoAsms,Abbr `u`] >>
     qpat_assum `captured = t with vs_vars := _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `u.vs_inst_idx = LENGTH sc.cs_current_insts /\ eval_operand src_op u = SOME p` by
    simp[Abbr `u`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem slice_dynamic_capture_source_post_from_run:
  (!sa src len data sb func s p G tn capacity bs lo ctx explicit PG.
    compile_bytestring_src (Var src) sa = ((len,data),sb) /\
    fn_has_code sa sb func /\ not_fresh_at sa src /\
    lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
    32 <= capacity /\ w2n p + 32 < dimword (:256) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    w2n p + 32 <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
      eval_operand len u = SOME (n2w (LENGTH bs)) /\
      eval_operand data u = SOME (p+32w) /\
      op_taint tn' len = {} /\ op_prov G' len = NONE /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
      (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      u = s with vs_vars := u.vs_vars /\
      (!x. not_fresh_at sa x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!n. 32+n <= capacity ==>
         ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
      (?lp dp. len = Var lp /\ data = Var dp /\
         not_fresh_at sb lp /\ not_fresh_at sb dp)) ==>
  !H ctx func cenv cx e es0 sa sm s0 es v srcop s bt vt env G tn
    ghost_D floor d len data sc lo explicit PG.
  expr_post (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx e es0 sa sm s0 es v srcop s /\
  post_value_type cenv e = BaseT bt /\
  (?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\ value_has_type vt v /\
  expr_sim_inv cenv cx env es /\
  ptr_val_ok cx (BaseT bt) v srcop G tn s /\
  ghost_inv_at ghost_D floor d cenv cx es G tn s /\
  compile_bytestring_src srcop sm = ((len,data),sc) /\ fn_has_code sm sc func /\
  (!z. srcop = Var z ==> not_fresh_at sm z) /\ (!l. srcop <> Label l) /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u G' tn' src p bs.
    srcop = Var src /\ eval_operand srcop s = SOME p /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    val_footprint vt v = 32 + LENGTH bs /\
    run_inst_seq (emitted_insts sm sc) s = OK u /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK (u with vs_inst_idx := LENGTH sc.cs_current_insts),G',tn')) /\
    eval_operand len u = SOME (n2w (LENGTH bs)) /\
    eval_operand data u = SOME (p+32w) /\
    op_taint tn' len = {} /\ op_prov G' len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    u = s with vs_vars := u.vs_vars /\
    (!x. not_fresh_at sm x ==>
       lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!n. n <= LENGTH bs ==>
       ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
    expr_post H ctx func cenv cx e es0 sa sc s0 es v srcop u /\
    ghost_inv_at ghost_D floor d cenv cx es G' tn' u /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ptr_covers G' tn' src u (32+LENGTH bs) /\
    (?dp. data = Var dp /\ ptr_covers G' tn' dp u (LENGTH bs)) /\
    (?lp dp. len = Var lp /\ data = Var dp /\
       not_fresh_at sc lp /\ not_fresh_at sc dp)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es s /\
   expr_val_rel cx (BaseT bt) v srcop s /\
   expr_val_at cenv cx (BaseT bt) sa sm es v srcop s` by
    gvs[expr_post_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `~is_word_type (BaseT bt) /\ supported_scalar_type (BaseT bt) /\
   is_bytestring_type (BaseT bt)` by
    gvs[supported_scalar_type_def, supported_word_type_def,
        supported_string_type_def, is_word_type_def, is_bytestring_type_def] >>
  `log_arg_rel cenv cx sa sm es s (srcop,BaseT bt) v` by
    (simp[log_arg_rel_def] >> irule log_arg_clear_base >>
     goal_assum (drule_at Any)) >>
  `?p. eval_operand srcop s = SOME p` by gvs[expr_val_rel_def] >>
  drule_all expr_val_rel_memory >> strip_tac >>
  `?bs. (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
        val_footprint vt v = 32 + LENGTH bs /\
        mem_word_at (w2n p) s.vs_memory = n2w (LENGTH bs) /\
        mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs` by
    (gvs[] >> Cases_on `v` >>
     gvs[evaluate_type_def, value_has_type_def, val_footprint_def,
         val_in_memory_def] >> metis_tac[]) >>
  drule_all log_arg_footprint_bound >> strip_tac >>
  `LENGTH bs < dimword (:256) /\ w2n p + 32 < dimword (:256)` by decide_tac >>
  drule_all ptr_val_ok_log_bytestring_window >> strip_tac >>
  `w2n p + 32 <= s.vs_alloca_next` by
    (drule_all abi_encode_owned_footprint_frontier >> decide_tac) >>
  `mload (w2n p) s = n2w (LENGTH bs)` by
    metis_tac[mem_word_at_eq_mload_proof] >>
  `lookup_var src s = SOME p` by gvs[eval_operand_def] >>
  `32 <= 32 + LENGTH bs` by simp[] >>
  `not_fresh_at sm src` by metis_tac[] >>
  qpat_x_assum `srcop = Var src` SUBST_ALL_TAC >>
  qpat_x_assum `!sa src len data sb func s p G tn capacity bs lo ctx explicit PG. _`
    (drule_all_then (qspecl_then [`explicit`,`PG`] strip_assume_tac)) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (irule stmt_state_rel_reserved_vars_update >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s`
       (ACCEPT_TAC o MATCH_MP (cj 1 stmt_state_rel_local_ptrs_alloca))) >>
  `stor_taint_ok_at ghost_D tn' u /\
   allocas_from floor u /\ floor <= u.vs_alloca_next` by
    (qpat_assum `ghost_inv_at ghost_D floor _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `u = s with vs_vars := _` mp_tac >>
     qpat_assum `tn'.t_stor = tn.t_stor` mp_tac >>
     qpat_assum `tn'.t_trans = tn.t_trans` mp_tac >>
     qpat_assum `tn'.t_imm = tn.t_imm` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ghost_inv_at_def,stor_taint_ok_at_def,allocas_from_def,
       venom_state_component_equality] >> metis_tac[]) >>
  `ghost_inv_at ghost_D floor d cenv cx es G' tn' u` by
    (irule ghost_inv_at_local_window_transport >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`G`,`es`,`func`,`s`,`sm`,`tn`] >>
     simp[] >> gvs[venom_state_component_equality] >> metis_tac[]) >>
  `sm.cs_next_id <= sc.cs_next_id` by
    (qspec_then `sm` mp_tac (Q.SPEC `Var src` ci_mono_compile_bytestring_src) >>
     simp[ci_mono_def]) >>
  `eval_operand (Var src) u = SOME p` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `expr_post H ctx func cenv cx e es0 sa sc s0 es v (Var src) u` by
    (irule convert_readonly_expr_post >> simp[] >>
     qexistsl_tac [`s`,`sm`,`Var src`] >> simp[] >>
     gvs[venom_state_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`u`,`G'`,`tn'`,`src`,`p`,`bs`] >> simp[] >>
  gvs[allocas_from_def, venom_state_component_equality,
      ptr_covers_def, eval_operand_def] >> metis_tac[]
QED

(* Select the capture once; the start entry then works at every valid horizon. *)
Theorem slice_dynamic_capture_typed_start_entry:
  (!sa src len data sb func s p G tn capacity bs lo ctx explicit PG.
    compile_bytestring_src (Var src) sa = ((len,data),sb) /\
    fn_has_code sa sb func /\ not_fresh_at sa src /\
    lookup_var src s = SOME p /\ ptr_covers G tn src s capacity /\
    32 <= capacity /\ w2n p + 32 < dimword (:256) /\
    mload (w2n p) s = n2w (LENGTH bs) /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) s.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn.t_mem) /\
    allocas_from lo s /\ lo <= s.vs_alloca_next /\
    w2n p + 32 <= s.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u G' tn'.
      run_inst_seq (emitted_insts sa sb) s = OK u /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
         (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
      eval_operand len u = SOME (n2w (LENGTH bs)) /\
      eval_operand data u = SOME (p+32w) /\
      op_taint tn' len = {} /\ op_prov G' len = NONE /\
      mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
      (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tn'.t_mem) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      u = s with vs_vars := u.vs_vars /\
      (!x. not_fresh_at sa x ==>
         lookup_var x u = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
      (!n. 32+n <= capacity ==>
         ?dp. data = Var dp /\ ptr_covers G' tn' dp u n) /\
      (?lp dp. len = Var lp /\ data = Var dp /\
         not_fresh_at sb lp /\ not_fresh_at sb dp)) ==>
  !DF lo explicit ctx func PG d cenv cx src es sa st1 s0 mid v src_op t G1 tn1
    bt vt env src_len src_data sc st0.
  post_value_type cenv src = BaseT bt /\
  (?cap. bt = BytesT (Dynamic cap) \/ bt = StringT cap) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME vt /\ value_has_type vt v /\
  expr_sim_inv cenv cx env mid /\ ptr_val_ok cx (BaseT bt) v src_op G1 tn1 t /\
  compile_bytestring_src src_op st1 = ((src_len,src_data),sc) /\
  fn_has_code st1 sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv st1 /\ sa.cs_next_var <= st1.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x) /\
  (!x. src_op = Var x ==> not_fresh_at st1 x) /\ (!l. src_op <> Label l) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx src es sa st1 s0 mid v src_op t /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t) /\
  return_buf_frame d cenv sa s0 /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = st1.cs_current_bb /\ t.vs_inst_idx = LENGTH st1.cs_current_insts /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) ==>
  ?captured Gu tu srcvar p bs u.
    src_op = Var srcvar /\ eval_operand src_op t = SOME p /\
    (v = BytesV bs \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    val_footprint vt v = 32 + LENGTH bs /\
    run_inst_seq (emitted_insts st1 sc) t = OK captured /\
    u = captured with vs_inst_idx := LENGTH sc.cs_current_insts /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu)) /\
    eval_operand src_len u = SOME (n2w (LENGTH bs)) /\
    eval_operand src_data u = SOME (p+32w) /\
    eval_operand src_op u = SOME p /\
    op_taint tu src_len = {} /\ op_prov Gu src_len = NONE /\
    mem_bytes_at (w2n p + 32) (LENGTH bs) u.vs_memory = bs /\
    (!i. w2n p <= i /\ i < w2n p + 32 + LENGTH bs ==> i NOTIN tu.t_mem) /\
    tu.t_mem = tn1.t_mem /\ tu.t_stor = tn1.t_stor /\
    tu.t_trans = tn1.t_trans /\ tu.t_imm = tn1.t_imm /\
    captured = t with vs_vars := captured.vs_vars /\
    (!x. not_fresh_at st1 x ==>
       lookup_var x u = lookup_var x t /\ FLOOKUP Gu x = FLOOKUP G1 x /\
       op_taint tu (Var x) = op_taint tn1 (Var x)) /\
    allocas_from lo u /\ lo <= u.vs_alloca_next /\
    ptr_covers Gu tu srcvar u (32+LENGTH bs) /\
    (!n. n <= LENGTH bs ==> ?dp. src_data = Var dp /\ ptr_covers Gu tu dp u n) /\
    (?lp dp. src_len = Var lp /\ src_data = Var dp /\
       not_fresh_at sc lp /\ not_fresh_at sc dp) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu) /\
      stmt_state_rel H ctx func cenv cx mid u /\
      storage_well_formed_on cx mid (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx mid Gu tu u) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx src es sa sc s0 mid v src_op captured) /\
    ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
    u.vs_inst_idx = LENGTH sc.cs_current_insts /\
    return_buf_frame d cenv sc u /\ alloca_history func u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
    (!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z)
Proof
  disch_then (mp_then Any (mk_asm "capture") slice_dynamic_capture_source_post_from_run) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  asm "capture" drule >> simp[] >>
  disch_then (qspecl_then [`env`,`G1`,`tn1`,
    `DF (storage_trace_horizon mid.storage_trace)`,`lo`,`d`,`lo`,`explicit`,`PG`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`captured`,`Gu`,`tu`,`srcvar`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) >>
  asm_x "capture" kall_tac >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] (OK _,Gu,tu)`
    (mp_then Any (fn with_path =>
      qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (mp_then Any (fn with_post =>
          qpat_assum `compile_bytestring_src src_op st1 = _`
            (mp_then Any (fn with_compile =>
              qpat_assum `eval_operand src_op t = SOME p`
                (mp_then Any mp_tac with_compile)) with_post)) with_path))
      slice_dynamic_capture_start_entry) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  qpat_x_assum `src_op = Var srcvar` SUBST_ALL_TAC >>
  qexistsl_tac [`captured`,`Gu`,`tu`,`srcvar`,`p`,`bs`] >>
  RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [lookup_var_def,allocas_from_def,allocas_below_fmp_def]) >>
  simp[lookup_var_def,allocas_from_def,allocas_below_fmp_def] >> metis_tac[]
QED

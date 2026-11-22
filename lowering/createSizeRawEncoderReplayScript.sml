Theory createSizeRawEncoderReplay
Ancestors
  abiEncoderProps exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  venomExecSemantics venomInst venomState vyperCreate vyperState relation list words
  createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering vfmConstants compileEnv
  exprLoweringProps freshWrites rich_list exprSimHypsDefs vyperTypeSystem bodyPtrDefs
  loweringPosts context vyperAST vyperStorageFootprint vyperTyping vyperValue integer_word
  valueEncoding createCtorSegmentArrival bodyFullHashKeccakFixed loweringStateRelDefs
  exprSimMemDefs ptrDiscipline createCtorObservedSilence createCtorPayloadLength
  bodyFullExtCallDirectState bodyPtrMakeArrayPrimitiveInstall bodyPtrMakeArrayEmission
  venomInstProofs1 gasEvents bodySim loweringShapeDefs createExprSizeExitDefs
  createSizePrefixReplay

(* A straight prologue instruction accounts for both the observed marks and
   the successor PC, without replacing the observed machine state. *)
Theorem raw_encoder_straight_edge[local]:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  gas_origin_edge F explicit ctx func s ms (OK t) ==>
  ms = [] /\ t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[gas_origin_edge_def] >>
  Cases_on `step_inst_base i s` >>
  gvs[step_inst_non_invoke,exit_result_def,Once gas_events_step_def] >>
  drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem raw_encoder_prefix_rtc:
  create_expr_prefix a b explicit ctx func u marks v <=>
  RTC (create_marked_edge (\p ms q. ?bb i.
    (p.vs_current_bb,p.vs_inst_idx) <> (b.cs_current_bb,LENGTH b.cs_current_insts) /\
    lookup_block p.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb p.vs_inst_idx = SOME i /\ i.inst_id IN frag_ids a b /\
    gas_origin_edge F explicit ctx func p ms (OK q))) (u,[]) (v,marks)
Proof
  rewrite_tac[create_expr_prefix_marked] >>
  AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >> AP_TERM_TAC >>
  simp[FUN_EQ_THM, create_prefix_step_def, PAIR_EQ] >> metis_tac[]
QED

(* This application takes row-success evidence; it does not replay the
   source constructor list. s/u/t are the observed row/prologue/ABI exits. *)
Theorem create_raw_encoder_at_cuts:
  args <> [] /\ LENGTH args = LENGTH vs /\ LENGTH svs = LENGTH args /\
  compile_create_ctor_args compile_expr ce args (C 0) = (svs,C (LENGTH args)) /\
  body_inv tops ctx ce cx /\ (!K. dead_lo_ok K (DF K) lo ce cx) /\
  EVERY (\c. FST c = NONE /\ IS_SOME (supported_function_decl tops c Internal))
    (int_calls_exprs args) /\
  (?H. valid_horizon cx st0 H (E (LENGTH args)).storage_trace) /\
  fn_inst_ids_distinct func /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    vyperState$bind (eval_expr cx (EL i args)) (read_result cx) (E i) =
      (INL (EL i vs),E (SUC i)) /\
    (expr_sim_inv ce cx env (E i) ==> expr_body_pre ce cx env (EL i args) (E i)) /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
      arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
      value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (St (SUC i)).vs_labels = (St i).vs_labels /\
    ~(St (SUC i)).vs_halted /\ (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      (if exprs_can_mutate ce (DROP (SUC i) args) then
        fn_has_code (M i) (C (SUC i)) func /\ ~(Mid i).vs_halted /\
        (Mid i).vs_current_bb = (M i).cs_current_bb /\
        (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
        RTC (\p q. (p.vs_current_bb,p.vs_inst_idx) <>
             ((C (SUC i)).cs_current_bb,LENGTH (C (SUC i)).cs_current_insts) /\
          ?j ms. ctor_segment_fetch func p = SOME j /\
            (M i).cs_next_id <= j.inst_id /\ j.inst_id < (C (SUC i)).cs_next_id /\
            gas_origin_edge F explicit ctx func p ms (OK q)) (Mid i) (St (SUC i)) /\
        (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
             (C (SUC i)).cs_next_id <= j.inst_id)
       else Mid i = St (SUC i)))) /\
  expr_sim_inv ce cx env (E 0) /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ ~(St 0).vs_halted /\
  (St 0).vs_current_bb = (C 0).cs_current_bb /\ (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K (E 0).storage_trace ==>
    stmt_state_rel K ctx func ce cx (E 0) (St 0) /\
    storage_well_formed_on cx (E 0) (FST K) /\
    ghost_inv_at (DF K) lo d ce cx (E 0) G0 tn0 (St 0)) /\
  (!i g h. i < LENGTH args /\ expr_sim_inv ce cx env (E i) /\
    return_buf_frame d ce (C i) (St i) /\ alloca_history func (St i) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K (E i).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E i) (St i) /\
      storage_well_formed_on cx (E i) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
        lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
          (op,C (SUC i)) ==>
        expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
          (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
            ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      ?g' h' raw_value. eval_expr cx (EL i args) (E i) = (INL raw_value,E (SUC i)) /\
       !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
        vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
          ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
        vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
          ((E (SUC i)) with gas_obs := []) raw_value (V i) (Mid i) /\
        ptr_vv_ok cx (post_value_type ce (EL i args)) raw_value (V i)
          ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
        alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
        ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
        ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
        (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
          ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
        (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
        (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
          ?val. read_result cx raw_value ((E (SUC i)) with gas_obs := []) =
              (INL val,(E (SUC i)) with gas_obs := []) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
              eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                     val_in_memory rt val (w2n w) mem)))) /\
  se = C (LENGTH args) /\ s = St (LENGTH args) /\ ee = E (LENGTH args) /\
  local_ptrs_reserved ce se /\ ci_mono (C 0) se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  capacity = prefix_bound +
    abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
  capacity < dimword (:256) /\
  compile_alloc_buffer capacity se = (buf,a) /\ fn_has_code se a func /\
  gas_origin_edge F explicit ctx func s am (OK su) /\
  compile_copy_memory_dynamic buf.buf_operand (Var src) (Var len) a = ((),b) /\
  fn_has_code a b func /\ emit_op ADD [buf.buf_operand;Var len] b = (dst_op,st) /\
  fn_has_code b st func /\ w2n nword <= prefix_bound /\
  not_fresh_at (C 0) src /\ not_fresh_at (C 0) len /\
  lookup_var src (St 0) = SOME p /\ lookup_var len (St 0) = SOME nword /\
  ptr_covers G0 tn0 src (St 0) (w2n nword) /\ op_taint tn0 (Var len) = {} /\
  w2n p + w2n nword <= (St 0).vs_alloca_next /\
  gas_origin_edge F explicit ctx func su bm (OK sv) /\
  gas_origin_edge F explicit ctx func sv cm (OK u) /\
  compile_abi_encode_values_to_buf ce dst_op (ZIP (svs,MAP (lowered_value_type ce) args))
    st = (alen,en) /\ fn_has_code st en func /\
  create_expr_prefix st en explicit ctx func u encmarks t /\
  (t.vs_current_bb,t.vs_inst_idx) = (en.cs_current_bb,LENGTH en.cs_current_insts) /\
  c 0 = en /\ r 0 = t /\ r n = bad /\
  (!k. k < n ==>
    (c k).cs_next_id <= (c (SUC k)).cs_next_id /\
    create_expr_prefix (c k) (c (SUC k)) explicit ctx func (r k) (chunk k) (r (SUC k))) /\
  lookup_block bad.vs_current_bb func.fn_blocks = SOME bbad /\
  get_instruction bbad bad.vs_inst_idx = SOME dispatch /\
  ((dispatch.inst_opcode = CREATE /\ dispatch.inst_operands = [value;off;sz]) \/
   (dispatch.inst_opcode = CREATE2 /\ dispatch.inst_operands = [value;off;sz;salt])) /\
  eval_operand sz bad = SOME w /\ 2 * max_code_size < w2n w /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) ==>
  am = [] /\ bm = [] /\ cm = [] /\ encmarks = [] /\
  ?bytes Gt tt.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    eval_operand alen t = SOME (n2w (LENGTH bytes)) /\
    (!x. alen = Var x ==> not_fresh_at en x) /\ op_taint tt alen = {} /\
    wb_frame ce (E 0) ee (C 0) (St 0) t /\
    lookup_var len t = SOME nword /\
    expr_sim_inv ce cx env ee /\ return_buf_frame d ce en t /\ alloca_history func t /\
    ~(t.vs_halted) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = en.cs_current_bb /\ t.vs_inst_idx = LENGTH en.cs_current_insts /\
    local_ptrs_reserved ce en /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at en x) /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
    (!K. valid_horizon cx st0 K ee.storage_trace ==>
      stmt_state_rel K ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST K) /\
      ghost_inv_at (DF K) lo d ce cx ee Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "payload"
QED
Resume create_raw_encoder_at_cuts[payload]:
  mp_tac (PURE_REWRITE_RULE[COND_CLAUSES,AND_CLAUSES,IMP_CLAUSES,NOT_CLAUSES]
            (Q.INST [`raw` |-> `T`] create_ctor_payload_length)) >>
  (impl_tac >- suspend "premises") >>
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  disch_then strip_assume_tac >>
  rename1 `encode_create_ctor_args _ _ _ = SOME bytes` >>
  qpat_assum `!D. gas_origin_ptr_path _ _ [] _ /\ _`
    (qspec_then `ARB` (map_every assume_tac o CONJUNCTS)) >>
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (u,_,_) [] (OK t,Gexit,texit)` >>
  suspend "silence"
QED
Resume create_raw_encoder_at_cuts[premises]:
  qpat_assum `args <> []` (simp_tac bool_ss o single) >>
  pure_rewrite_tac[GSYM raw_encoder_prefix_rtc] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
Resume create_raw_encoder_at_cuts[silence]:
  `s.vs_current_bb = se.cs_current_bb /\ s.vs_inst_idx = LENGTH se.cs_current_insts` by
    (`PRE (LENGTH args) < LENGTH args` by (Cases_on `args` >> fs[]) >>
     `SUC (PRE (LENGTH args)) = LENGTH args` by decide_tac >>
     qpat_assum `!i. i < LENGTH args ==> compile_expr _ _ _ _ = _ /\ _`
       (qspec_then `PRE (LENGTH args)` (drule_then (map_every assume_tac o CONJUNCTS))) >>
     qpat_assum `s = St _` (fn hs => qpat_assum `se = C _` (fn hc =>
       pure_rewrite_tac [hs,hc])) >>
     qpat_assum `SUC (PRE _) = _` (SUBST_ALL_TAC) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `am = [] /\ su.vs_current_bb = a.cs_current_bb /\ su.vs_inst_idx = LENGTH a.cs_current_insts` by
    (`?tmp. emit_op ALLOCA [Lit (n2w capacity)] se = (tmp,a)` by
       (Cases_on `emit_op ALLOCA [Lit (n2w capacity)] se` >>
        qpat_assum `compile_alloc_buffer _ _ = _` (mp_tac o PURE_REWRITE_RULE
          [compile_alloc_buffer_def,comp_bind_def,comp_return_def]) >>
        qpat_assum `emit_op ALLOCA _ _ = _` (fn th => simp_tac (srw_ss()) [th,comp_return_def,LET_THM])) >>
     pop_assum strip_assume_tac >>
     drule_all (Q.INST [`opc` |-> `ALLOCA`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ALLOCA ops outs`] raw_encoder_straight_edge)) >>
     strip_tac >> fs[]) >>
  `bm = [] /\ sv.vs_current_bb = b.cs_current_bb /\ sv.vs_inst_idx = LENGTH b.cs_current_insts` by
    (`emit_void MCOPY [buf.buf_operand;Var src;Var len] a = ((),b)` by fs[compile_copy_memory_dynamic_def] >>
     drule_all emit_void_fetch_boundary >> strip_tac >>
     qmatch_asmsub_rename_tac `get_instruction copybb _ = SOME (mk_inst _ MCOPY _ _)` >>
     `?bb. lookup_block su.vs_current_bb func.fn_blocks = SOME bb /\
           get_instruction bb su.vs_inst_idx =
             SOME (mk_inst a.cs_next_id MCOPY [buf.buf_operand;Var src;Var len] [])` by
       (qexists_tac `copybb` >> fs[]) >>
     pop_assum strip_assume_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id MCOPY ops outs`] raw_encoder_straight_edge)) >> strip_tac >> fs[]) >>
  `cm = []` by
    (drule_all (Q.INST [`opc` |-> `ADD`] emit_op_fetch_boundary) >> strip_tac >>
     drule_all (SIMP_RULE (srw_ss()) [is_terminator_def]
       (Q.INST [`i` |-> `mk_inst id ADD ops outs`] raw_encoder_straight_edge)) >> simp[]) >>
  `encmarks = []` by
    (irule ctor_observed_cut_silent >>
     qexistsl_tac [`ctx`,`(en.cs_current_bb,LENGTH en.cs_current_insts)`,`explicit`,`func`,`t`,`u`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
     >- (irule RTC_MONOTONE >>
         qpat_assum `create_expr_prefix st en _ _ _ _ _ _`
           (irule_at Any o REWRITE_RULE[create_expr_prefix_marked]) >>
         simp[create_marked_edge_def,FORALL_PROD,create_prefix_step_def,PAIR_EQ] >> metis_tac[]) >>
     drule gas_origin_ptr_path_projections >> simp[]) >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`bytes`,`Gexit`,`texit`] >> suspend "entry"
QED
Resume create_raw_encoder_at_cuts[entry]:
  qhdtm_assum `abi_encode_saved_state`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE[abi_encode_saved_state_def]) >>
  `lookup_var len t = SOME nword` by
    (qpat_assum `wb_frame ce (E 0) ee (C 0) (St 0) t`
       (irule o cj 1 o REWRITE_RULE[wb_frame_def]) >> simp[]) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ _ [] (OK u,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z` by
    (qpat_assum `gas_origin_ptr_path _ _ [] (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `ee = E _` (fn he =>
       qpat_assum `?H. valid_horizon cx st0 H (E _).storage_trace`
         (qx_choose_then `hz` (assume_tac o PURE_REWRITE_RULE [GSYM he]))) >>
     qpat_assum `!K. valid_horizon cx st0 K ee.storage_trace ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `hz` (drule_then
          (ACCEPT_TAC o MATCH_MP stmt_state_rel_allocas_below_fmp o CONJUNCT1)))) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC)
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `se` >> simp[])
  >> rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `se` >> simp[]
QED
Finalise create_raw_encoder_at_cuts

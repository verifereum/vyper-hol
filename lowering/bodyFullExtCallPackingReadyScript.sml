Theory bodyFullExtCallPackingReady
Ancestors targetPurePostTransport[qualified,ignore_grammar]
  bodyFullExtCallPacking bodyFullExtCallBufferSetup bodyFullExtCallEncodeTail
  bodyFullExtCallCallStage bodyFullExtCallPosList bodyFullExtCallSelectorReady
  bodyFullExtCallTupleStores bodyFullOriginAllocationGrowth
  bodyFullExtCallEncoderWindows bodyFullExtCallEncoderStmtFrame
  bodyFullExtCallEncoderCallerFrames
  ctorDeployMemoryRunMemEntryLiteralPath[qualified,ignore_grammar]
  fragGasMode[qualified,ignore_grammar]

Theorem extcall_packing_evaluated_size_bound[local]:
  (!env ty tv. evaluate_type env ty = SOME tv ==>
      type_memory_size tv <= vyper_abi_size_bound env ty) /\
  (!env tys acc tvs. evaluate_types env tys acc = SOME tvs ==>
      type_memory_size_list tvs <=
      type_memory_size_list acc + vyper_abi_size_bound_list env tys)
Proof
  ho_match_mp_tac vyperValueTheory.evaluate_type_ind >>
  rpt conj_tac >> rpt gen_tac >>
  simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(), boolTheory.LET_THM,
       vyperABITheory.vyper_abi_size_bound_def, PULL_EXISTS] >>
  rpt strip_tac >>
  gvs[vyperABITheory.vyper_abi_size_bound_def, valueEncodingTheory.type_memory_size_def,
      contractABITheory.ceil32_def, vfmConstantsTheory.word_size_def]
  >- (Cases_on `bd` >>
      simp[valueEncodingTheory.type_memory_size_def, vyperABITheory.vyper_abi_size_bound_def,
           arithmeticTheory.LE_MULT_LCANCEL] >> decide_tac)
  >- (`LENGTH args = LENGTH tvs` by
        (drule vyperTypeDefaultsTheory.evaluate_types_length >> simp[]) >>
      simp[valueEncodingTypingTheory.type_memory_size_fields_zip])
  >- simp[typeLayoutPropsTheory.type_memory_size_list_sum, listTheory.MAP_REVERSE,
          rich_listTheory.SUM_REVERSE] >>
  decide_tac
QED

Theorem extcall_packing_observed_domain[local]:
  valid_horizon cx st H obs ==> storage_trace_domain cx st obs
Proof
  simp[vyperStorageFootprintTheory.storage_trace_domain_def,
       vyperStorageFootprintTheory.valid_horizon_def,
       vyperStorageFootprintTheory.storage_trace_horizon_def,
       vyperStorageFootprintTheory.storage_observations_ok_def,
       vyperStorageFootprintTheory.regions_consistent_def,
       vyperStorageFootprintTheory.storage_locks_separated_def,
       vyperStorageFootprintTheory.storage_well_formed_on_def,
       vyperStorageFootprintTheory.storage_trace_backends_well_formed_def,
       listTheory.EVERY_MEM] >>
  strip_tac >> rpt conj_tac >> rpt strip_tac >>
  TRY (qpat_assum `!o'. MEM o' obs ==> _` drule >>
       Cases_on `observation` >> gvs[]) >>
  metis_tac[]
QED

Theorem extcall_request_packing_ready:
  LENGTH xs = LENGTH vals /\ LENGTH vals = LENGTH argvs /\
  LENGTH argvs = LENGTH arg_types /\ tys = MAP (lowered_value_type cenv) xs /\
  EVERY (assignable_type (get_tenv cx)) arg_types /\
  EVERY (abi_decode_bytes_widths (get_tenv cx)) arg_types /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ee /\
  return_buf_frame d cenv se s /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!i. i < LENGTH xs ==>
    ?e sv v raw si sm ss vv tv param_tv.
      e = EL i xs /\ sv = EL i vals /\ v = EL i argvs /\
      arg_type_fits (lowered_value_type cenv e) (EL i arg_types) /\
      evaluate_type (get_tenv cx) (EL i arg_types) = SOME param_tv /\
      value_has_type param_tv v /\
      (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv F
        (ext_call_arg_value (lowered_value_type cenv e) vv) sm = (sv,ss) /\
      ((?tag op0. sv = StackValue tag op0) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location = LocMemory) \/
       (?p. sv = LocatedValue (lowered_value_type cenv e) p /\
            ~is_word_type (lowered_value_type cenv e) /\ p.ptr_location <> LocMemory /\
            lowered_value_type cenv e = expr_type e /\ sv = vv)) /\
      local_ptrs_reserved cenv si /\
      sm.cs_next_var <= se.cs_next_var /\ sm.cs_next_id <= se.cs_next_id /\
      ss.cs_next_var <= se.cs_next_var /\
      ss.cs_next_id <= se.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at si x) /\
      (!l. vv_operand sv <> Label l) /\
      read_result cx raw ee = (INL v,ee) /\
      vv_holds cenv cx (lowered_value_type cenv e) raw sv ee s /\
      vv_at cenv cx (lowered_value_type cenv e) si ss ee raw sv s /\
      ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn s /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw sv s /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx sv ee s) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G s)) /\
  mem = SUM (MAP (type_memory_bytes cenv) tys) /\
  abi = vyper_abi_size_bound (get_tenv cx) (TupleT tys) /\
  abi_enc_plan (get_tenv cx) (TupleT tys) aenc /\
  mid = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types))) /\
  compile_alloc_buffer ((if abi > cap then abi else cap) + 32) se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (n2w mid)] sb = ((),sm) /\
  (if vals = [] then comp_return (Lit 4w) else
     comp_bind (compile_alloc_buffer mem) (\aa.
     comp_ignore_bind (compile_extcall_store_values cenv (ZIP (vals,tys))
                        aa.buf_operand 0)
     (comp_bind (emit_op ADD [ba.buf_operand;Lit 32w]) (\dst.
      comp_bind (compile_abi_encode_to_buf dst aa.buf_operand aenc) (\alen.
      emit_op ADD [alen;Lit 4w]))))) sm = (len,sf) /\
  emit_op ADD [ba.buf_operand;Lit 28w] sf = (off,sp) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\
  fn_has_code sm sf func /\ fn_has_code sf sp func /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  (if abi > cap then abi else cap) + 32 < dimword (:256) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  stmt_state_rel H0 ctx func cenv cx es s0 /\
  wb_frame cenv es ee sa s0 s /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= se.cs_next_var /\
  sa.cs_next_id <= se.cs_next_id /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts /\ ee.gas_obs = [] /\
  outcomes_accounts_typed ee.outcomes /\ accounts_runtime_well_typed ee.accounts /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  EVERY (safe_operand se) [addr;value;gas;def] /\
  EVERY (\p. op_taint tn p = {}) [addr;value;gas;def] /\
  (?aw. eval_operand addr s = SOME aw /\ w2w aw = target) /\
  (stat <=> value_opt = NONE) /\
  (?vw. eval_operand value s = SOME vw /\
        w2n vw = (case value_opt of NONE => 0 | SOME k => k)) /\
  eval_operand gas s = SOME gw /\
  (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
  extcall_default_ready cx rt hasdef def dt dopt s /\
  (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
    ptr_mem_ok cx dt dv def G tn s /\
    (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers G tn p s (type_memory_bytes cenv dt)) /\
      (!w. eval_operand def s = SOME w ==>
           w2n w + type_memory_bytes cenv dt <= s.vs_alloca_next)) /\
    (?w aid tv. eval_operand def s = SOME w /\
      evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
      FLOOKUP s.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < se.cs_next_id)) ==>
  ?calldata t Gf tf.
    build_ext_calldata (get_tenv cx) fname arg_types argvs = SOME calldata /\
    extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas ba.buf_operand off len cap target value_opt calldata
      hasdef def dt dopt ee t /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,Gf,tf)) /\
    alloca_history func t /\ allocas_from lo t /\
    lo <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx ee Gf tf t) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf /\
    eval_operand gas t = SOME gw /\
    (!g. OPTION_BIND source_gas dest_NumV = SOME g ==> g = w2n gw) /\
    EVERY (\p. op_taint tf p = {}) [addr;value;gas;ba.buf_operand;off;len;def] /\
    (!ao az. eval_operand off t = SOME ao /\ eval_operand len t = SOME az ==>
      (az <> 0w ==> (?p. off = Var p /\ ptr_covers Gf tf p t (w2n az)) /\
                    w2n ao + w2n az <= t.vs_alloca_next) /\
      (!j. w2n ao <= j /\ j < w2n ao + w2n az ==> j NOTIN tf.t_mem)) /\
    (cap <> 0 ==> ?p. ba.buf_operand = Var p /\ ptr_covers Gf tf p t cap) /\
    (!dv. dopt = SOME dv /\ ~is_word_type dt ==>
      ptr_mem_ok cx dt dv def Gf tf t /\
      (type_memory_bytes cenv dt <> 0 ==>
        (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
        (!w. eval_operand def t = SOME w ==>
             w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `vals = []`
  >- (qpat_assum `vals = []` (fn th =>
        qpat_x_assum `(if vals = [] then _ else _) sm = _`
          (mp_tac o REWRITE_RULE [th, compileEnvTheory.comp_return_def, pairTheory.PAIR_EQ])) >>
      disch_then (CONJUNCTS_THEN (SUBST_ALL_TAC o SYM)) >>
      irule (INST_TYPE [``:'b`` |-> ``:'a``] extcall_selector_packing_ready) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qexists `[]` >> gvs[])
      >- (qexistsl [`abi`,`mid`,`sb`,`se`,`sm`] >>
          rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (qexists `H0` >> first_assum ACCEPT_TAC)) >>
  suspend "nonempty"
QED

Resume extcall_request_packing_ready[nonempty]:
  qpat_assum `vals <> []` (fn th =>
    qpat_x_assum `(if vals = [] then _ else _) sm = _`
      (mp_tac o REWRITE_RULE [th])) >>
  simp[NoAsms, compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (pairarg_tac >> first_assum (fn th => simp[NoAsms, th])) >>
  strip_tac >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = (_,_)`
    (mp_tac o SIMP_RULE (srw_ss()) [oneTheory.one]) >>
  strip_tac >>
  rename [`compile_alloc_buffer _ sm = (aa,sd)`,
          `compile_extcall_store_values _ _ _ _ sd = ((),st)`,
          `emit_op ADD [ba.buf_operand; Lit 32w] st = (dst,sadd)`,
          `compile_abi_encode_to_buf dst aa.buf_operand aenc sadd = (alen,senc)`] >>
  `cs_extends sm sd` by (irule loweringHaltTheory.compile_alloc_buffer_extends >>
    goal_assum drule) >>
  `cs_extends sd st` by
    (qpat_assum `compile_extcall_store_values _ _ _ _ sd = _`
      (fn th => mp_tac (Q.SPECL [`cenv`,`ZIP (vals,tys)`,`aa.buf_operand`,`0`,`sd`]
         externalEntryShapeTheory.compile_extcall_store_values_labels) >>
         simp[NoAsms, th])) >>
  `cs_extends st sadd /\ cs_extends sadd senc /\ cs_extends senc sf` by
    metis_tac[abiEncoderAddressReachTheory.abi_encoder_emit_address_shape,
              abiEncoderAppendTheory.cs_extends_abi_encode] >>
  `cs_extends st sf /\ cs_extends sd sf /\ cs_extends sadd sf` by
    metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code sm sd func /\ fn_has_code sd sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `!i. i < LENGTH tys ==> ?tv.
      evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
      type_memory_bytes cenv (EL i tys) = type_memory_size tv` by
    (rpt strip_tac >>
     `i < LENGTH xs` by
       (qpat_assum `tys = MAP _ xs` (fn th =>
         qpat_assum `i < LENGTH tys` (mp_tac o REWRITE_RULE [th,listTheory.LENGTH_MAP])) >>
        simp[NoAsms]) >>
     `EL i tys = lowered_value_type cenv (EL i xs)` by
       (qpat_assum `tys = MAP _ xs` SUBST1_TAC >>
        irule listTheory.EL_MAP >> qpat_assum `i < LENGTH xs` ACCEPT_TAC) >>
     qpat_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> qexists `tv` >>
     qpat_assum `EL i tys = _` SUBST1_TAC >>
     qpat_assum `e = EL i xs` (SUBST1_TAC o SYM) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `tvs = MAP (THE o evaluate_type (get_tenv cx)) tys` >>
  `evaluate_types (get_tenv cx) tys [] = SOME tvs` by
    (simp[vyperValueTheory.evaluate_types_OPT_MMAP, optionTheory.OPTION_MAP_EQ_SOME,
          vyperMiscTheory.OPT_MMAP_SOME_IFF, Abbr `tvs`,
          listTheory.EVERY_EL, listTheory.EL_MAP] >> metis_tac[optionTheory.IS_SOME_DEF]) >>
  `mem = type_memory_size_list tvs` by
    (simp[typeLayoutPropsTheory.type_memory_size_list_sum] >>
     AP_TERM_TAC >> simp[Abbr `tvs`, listTheory.LIST_EQ_REWRITE, listTheory.EL_MAP] >>
     metis_tac[optionTheory.THE_DEF]) >>
  `mem <= abi` by
    (drule (cj 2 extcall_packing_evaluated_size_bound) >>
     qpat_assum `mem = type_memory_size_list tvs` (fn hm =>
       qpat_assum `abi = vyper_abi_size_bound _ (TupleT tys)` (fn ha =>
         simp[NoAsms, hm, ha, vyperABITheory.vyper_abi_size_bound_def,
              valueEncodingTheory.type_memory_size_def]))) >>
  `mem < dimword (:256)` by decide_tac >>
  `evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs)` by
    (qpat_assum `evaluate_types _ tys [] = _` (fn th =>
       simp[NoAsms, Once vyperValueTheory.evaluate_type_def, th]) >>
     `type_memory_size_list tvs = 32 * type_slot_size_list tvs` by
       simp[valueEncodingPropsTheory.type_memory_size_slots] >>
     simp[NoAsms, vyperValueTheory.type_slot_size_def] >> decide_tac) >>
  qabbrev_tac `bs = function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types)` >>
  qabbrev_tac `n = (if abi > cap then abi else cap) + 32` >>
  `emit_void MSTORE [ba.buf_operand; Lit (calldata_method_id bs)] sb = ((),sm)` by
    (qpat_assum `mid = _` (fn hm =>
       qpat_assum `emit_void MSTORE _ sb = _` (mp_tac o REWRITE_RULE [hm])) >>
     simp[NoAsms, Abbr `bs`]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `HH` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _` (qspec_then `HH` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `local_ptrs_reserved cenv se` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `LENGTH bs = 4` by simp[Abbr `bs`, selectorCompilerPropsTheory.function_selector_length] >>
  `32 <= n` by simp[Abbr `n`] >>
  mp_tac (Q.INST [`sa` |-> `se`, `sc` |-> `sm`, `shared` |-> `ba`,
     `tuple` |-> `aa`, `has_args` |-> `T`, `es` |-> `ee`, `H0` |-> `HH`]
     extcall_request_buffer_setup) >>
  simp[NoAsms] >> impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `r` (qx_choose_then `rw` (qx_choose_then `u`
    (qx_choose_then `Gu` (qx_choose_then `tu` strip_assume_tac))))) >>
  `fn_has_code sd st func /\ fn_has_code st sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `sm.cs_next_id < sd.cs_next_id /\
   MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w mem)] [p]) (fn_insts func)` by
    (qpat_assum `compile_alloc_buffer mem sm = _`
       (strip_assume_tac o MATCH_MP abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
     conj_tac >- decide_tac >>
     irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl [`sm`,`sd`] >>
     `p = STRING #"%" (toString sm.cs_next_var)` by
       (qpat_assum `aa.buf_operand = Var p` (fn hp =>
          qpat_assum `aa.buf_operand = Var (STRING _ _)` (fn hn =>
            simp[NoAsms, GSYM hp] >> mp_tac (TRANS (SYM hp) hn) >> simp[NoAsms]))) >> simp[]) >>
  `storage_trace_domain cx st0 ee.storage_trace` by
    (irule extcall_packing_observed_domain >> qexists `HH` >> simp[]) >>
  `local_ptrs_reserved cenv sd` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists `se` >> simp[]) >>
  `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sd x` by
        (rpt strip_tac >> irule exprLoweringPropsTheory.local_ptrs_reserved_imm_base >>
     qexists `cenv` >> simp[]) >>
  `return_buf_frame d cenv sd u` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >> qexistsl [`cenv`,`s`,`se`] >>
     simp[] >> metis_tac[]) >>
  `se.cs_next_id <= sm.cs_next_id /\ se.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `compile_alloc_buffer n se = _`
       (strip_assume_tac o MATCH_MP abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
     qpat_assum `emit_void MSTORE _ sb = _`
       (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
     decide_tac) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sd x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `se` >> simp[] >> metis_tac[]) >>
  `local_ptrs_rel func cenv ee.scopes s` by
    (drule_then (ACCEPT_TAC o CONJUNCT1) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
  `!nm b nb. local_region cenv ee.scopes s nm b nb ==>
     mem_bytes_at b nb u.vs_memory = mem_bytes_at b nb s.vs_memory /\
     (!i. b <= i /\ i < b + nb /\ i IN tu.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!a k. _ \/ _ \/ _ ==> mem_bytes_at _ _ u.vs_memory = _ /\ _`
       (qspecl_then [`b`,`nb`] irule) >>
     disj2_tac >> disj1_tac >> qexistsl [`nm`,`b`,`nb`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee u /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx ee Gu tu u` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
     irule bodyPtrBytestringBuiltinsWindowGhostTheory.ghost_inv_at_local_window_transport >>
     `lo <= u.vs_alloca_next` by decide_tac >>
     `stor_taint_ok_at (DF H) tu u` by
       (qpat_assum `ghost_inv_at (DF H) _ _ _ _ _ G tn s`
          (mp_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
        simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     simp[] >> qexistsl [`G`,`ee`,`func`,`s`,`se`,`tn`] >>
     simp[] >> rpt strip_tac >>
     FIRST [
       qpat_assum `!nm b nb. local_region _ _ s nm b nb ==> _`
         (drule_then strip_assume_tac) >> simp[],
       qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >> decide_tac]) >>
  `!a k. a < se.cs_next_id ==> FLOOKUP s.vs_allocas a = SOME k ==>
     mem_bytes_at (FST k) (SND k) u.vs_memory =
       mem_bytes_at (FST k) (SND k) s.vs_memory /\
     (!i. FST k <= i /\ i < FST k + SND k /\ i IN tu.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> PairCases_on `k` >> simp[NoAsms] >> rpt disch_tac >>
     qpat_assum `!a k. _ \/ _ \/ _ ==> mem_bytes_at _ _ u.vs_memory = _ /\ _`
       (qspecl_then [`k0`,`k1`] irule) >>
     disj2_tac >> disj2_tac >> qexistsl [`a`,`k0`,`k1`] >> simp[]) >>
  `wb_frame cenv ee ee se s u` by
    (simp[NoAsms, loweringPostsTheory.wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
           (drule_then strip_assume_tac) >> simp[])
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_assum `!a k. a < se.cs_next_id ==> _` (drule_all_then mp_tac) >> simp[NoAsms]) >>
     irule exprSimPropsTheory.locals_kept_regions >>
     rpt strip_tac >> qpat_assum `!nm b nb. local_region _ _ s nm b nb ==> _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `ghost_kept_at lo cenv ee se G tn s Gu tu` by
    (simp[NoAsms, bodyPtrDefsTheory.ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
           (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
     >- (rpt strip_tac >>
         qpat_assum `!a k. a < se.cs_next_id ==> _` (drule_all_then mp_tac) >>
         simp[NoAsms] >> disch_then (irule o CONJUNCT2) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt strip_tac >> qpat_assum `!nm b nb. local_region _ _ s nm b nb ==> _`
       (drule_then (irule o CONJUNCT2)) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `fn` |-> `func`, `ca` |-> `sd`,
     `cb` |-> `st`, `svs` |-> `vals`, `vs` |-> `argvs`, `off` |-> `0`,
     `root` |-> `p`, `bw` |-> `z`, `cap` |-> `mem`, `aid` |-> `sm.cs_next_id`,
     `s` |-> `u`, `G` |-> `Gu`, `tn` |-> `tu`, `entry` |-> `ee`]
     extcall_store_values_joint_all_dead) >>
  impl_tac
  >- (simp[NoAsms, boolTheory.LET_THM] >>
      rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC,
        simp[NoAsms, Abbr `tvs`],
        qpat_assum `aa.buf_operand = Var p` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC,
        qpat_assum `tys = MAP _ xs` SUBST1_TAC >> simp[NoAsms] >> decide_tac,
        rpt strip_tac >> first_assum ACCEPT_TAC,
        rpt strip_tac >> qpat_assum `!x. cenv.ce_imm_alloca = SOME (Var x) ==> _` irule >>
          first_assum ACCEPT_TAC,
        qpat_assum `mem + w2n z < dimword (:256)` mp_tac >> decide_tac,
        qpat_assum `mem = SUM _` (SUBST1_TAC o SYM) >> simp[NoAsms],
        rpt gen_tac >> disch_tac >>
          qpat_assum `!name b k. local_region _ _ u name b k ==> regions_disjoint _ _ _ _`
            (drule_then mp_tac) >>
          simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def,
               arithmeticTheory.ADD_COMM]]) >>
      gen_tac >> disch_tac >>
      `i < LENGTH xs` by
        (qpat_assum `tys = MAP _ xs` (fn th =>
           qpat_assum `i < LENGTH tys` (mp_tac o REWRITE_RULE [th,listTheory.LENGTH_MAP])) >>
         simp[NoAsms]) >>
      `EL i tys = lowered_value_type cenv (EL i xs)` by
        (qpat_assum `tys = MAP _ xs` SUBST1_TAC >>
         irule listTheory.EL_MAP >> first_assum ACCEPT_TAC) >>
      qpat_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (qx_choose_then `e` (qx_choose_then `sv` (qx_choose_then `v`
        (qx_choose_then `raw` (qx_choose_then `si` (qx_choose_then `smi`
        (qx_choose_then `ss` (qx_choose_then `vv` (qx_choose_then `tv`
        (qx_choose_then `ptv` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))))))) >>
      `EL i tys = lowered_value_type cenv e` by
        (qpat_assum `EL i tys = _` SUBST1_TAC >>
         qpat_assum `e = EL i xs` (SUBST1_TAC o SYM) >> REFL_TAC) >>
      `EL i tvs = tv` by
        (qpat_assum `EL i tys = lowered_value_type cenv e` (fn ht =>
           qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME tv` (fn hv =>
             qpat_assum `i < LENGTH tys` (fn hi =>
               simp[NoAsms, Abbr `tvs`, listTheory.EL_MAP, ht, hv, hi])))) >>
      map_every (fn q => qpat_assum q (SUBST1_TAC o SYM))
        [`sv = EL i vals`,`v = EL i argvs`] >>
      qpat_assum `EL i tys = lowered_value_type cenv e` SUBST1_TAC >>
      qpat_assum `EL i tvs = tv` SUBST1_TAC >>
      `type_memory_size tv < 18446744073709551616` by
        (qpat_assum `type_memory_size tv < 2 ** 64` mp_tac >> simp[NoAsms]) >>
      `!x. vv_operand sv = Var x ==> not_fresh_at se x` by
        (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists `ss` >> conj_tac >- first_assum ACCEPT_TAC >>
         drule_all bodyFullExtCallSavedOperandTheory.extcall_saved_operand_not_fresh >>
         disch_then irule >> first_assum ACCEPT_TAC) >>
      `eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) s` by
        (Cases_on `vv_operand sv` >> simp[NoAsms, venomStateTheory.eval_operand_def] >>
         FIRST_PROVE [qpat_assum `u.vs_labels = s.vs_labels` SUBST1_TAC >> REFL_TAC,
           rename1 `lookup_var name u = _` >>
           `not_fresh_at se name` by
             (qpat_assum `!x. Var name = Var x ==> not_fresh_at se x`
                (qspec_then `name` mp_tac) >> simp[NoAsms]) >>
           qpat_assum `!x. not_fresh_at se x ==> lookup_var x u = _ /\ _`
             (drule_then (ACCEPT_TAC o CONJUNCT1))]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (rpt strip_tac >> irule targetPurePostTransportTheory.target_saved_storage_live_frame >>
          qexists `s` >>
          qpat_assum `eval_operand (vv_operand sv) u = eval_operand (vv_operand sv) s`
            (fn th => simp[NoAsms,th]) >>
          conj_tac >- (drule_then ACCEPT_TAC targetPurePostTransportTheory.target_saved_operand_exists) >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> vv_storage_live H _ sv _ s`
            (drule_then ACCEPT_TAC)) >>
      qexistsl [`e`,`si`,`vv`,`smi`,`ss`,`raw`] >>
      rpt (conj_tac >- FIRST_PROVE [first_assum ACCEPT_TAC, REFL_TAC, decide_tac]) >>
      `(vv_location sv = SOME LocMemory ==> ~is_word_type (lowered_value_type cenv e)) /\
       (!tag p. sv = LocatedValue tag p ==> tag = lowered_value_type cenv e)` by
        (qpat_assum `(?tag op0. sv = StackValue tag op0) \/ _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[contextTheory.vv_location_def]) >>
      `stmt_state_rel HH ctx func cenv cx ee u /\
       ghost_inv_at (DF HH) lo d cenv cx ee Gu tu u` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ u /\ _`
           (qspec_then `HH` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
         strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
      `vv_storage_live HH cx sv ee s /\ dead_lo_ok HH (DF HH) lo cenv cx` by
        (conj_tac
         >- (qpat_assum `!H. valid_horizon _ _ H _ ==> vv_storage_live H _ sv _ s`
               (drule_then ACCEPT_TAC)) >> simp[]) >>
      irule (INST_TYPE [alpha |-> ``:256``] extcall_tuple_saved_entry) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- (qexists `tv` >> first_assum ACCEPT_TAC) >>
      conj_tac >- (qexists `v` >> first_assum ACCEPT_TAC) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`DF HH`,`G`,`HH`,`ctx`,`se`,`d`,`func`,`lo`,`s`,`tn`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[NoAsms] >>
  disch_then (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tq`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  `se.cs_next_id < sm.cs_next_id` by
    (qpat_assum `compile_alloc_buffer n se = _`
       (strip_assume_tac o MATCH_MP abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
     qpat_assum `emit_void MSTORE _ sb = _`
       (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_void) >>
     decide_tac) >>
  `!nm b k. local_region cenv ee.scopes u nm b k ==>
       w2n rw + n <= b \/ b + k <= w2n rw` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee.scopes s nm b k` by
       metis_tac[exprSimSubscriptArrayFrameTheory.local_region_wb_frame] >>
     qpat_assum `!name b k. local_region _ _ s name b k ==> regions_disjoint _ _ _ _`
       (drule_then mp_tac) >>
     simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `FLOOKUP q.vs_allocas se.cs_next_id = SOME (w2n rw,n) /\
   lookup_var r q = SOME rw /\
   mem_bytes_at (w2n rw) n q.vs_memory = mem_bytes_at (w2n rw) n u.vs_memory` by
    (qpat_assum `wb_frame _ _ _ (sd with cs_next_id := _) u q`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     rpt conj_tac >- (first_assum irule >> first_assum ACCEPT_TAC)
     >- (first_assum irule >> simp[NoAsms, loweringStateRelDefsTheory.not_fresh_at_def] >>
         qpat_assum `not_fresh_at sd r` (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.not_fresh_at_def]) >>
         simp[]) >>
     first_assum irule >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `se.cs_next_id` >> simp[]) >>
  `read_memory (w2n rw + 28) 4 q = bs` by
    (qpat_assum `read_memory _ 4 u = bs` (SUBST1_TAC o SYM) >>
     simp[NoAsms, memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
     qpat_assum `mem_bytes_at (w2n rw) n q.vs_memory = _`
       (mp_then Any (qspecl_then [`28`,`4`] mp_tac)
         valueEncodingPropsTheory.mem_bytes_at_translated_window) >> simp[]) >>
  `(!i. w2n rw + 28 <= i /\ i < w2n rw + 32 ==> i NOTIN tq.t_mem) /\
   ptr_covers Gq tq r q n` by
    (qpat_assum `ghost_kept_at _ _ _ (sd with cs_next_id := _) Gu tu u Gq tq`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     conj_tac
     >- (rpt strip_tac >>
         `i IN tu.t_mem` by
           (qpat_assum `!aid off sz j. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> j IN tu.t_mem`
              (qspecl_then [`se.cs_next_id`,`w2n rw`,`n`,`i`] mp_tac) >>
            simp[NoAsms] >> impl_tac >-
              (rpt conj_tac >>
               FIRST_PROVE [first_assum ACCEPT_TAC, decide_tac,
                 rpt strip_tac >>
                 qpat_assum `!nm b k. local_region cenv ee.scopes u nm b k ==>
                                      w2n rw + n <= b \/ b + k <= w2n rw`
                   (drule_then mp_tac) >> simp[NoAsms, arithmeticTheory.ADD_COMM]]) >> simp[]) >>
         qpat_assum `!i. w2n rw + 28 <= i /\ i < w2n rw + 32 ==> i NOTIN tu.t_mem`
           (qspec_then `i` mp_tac) >> simp[]) >>
     irule assignTuplePtrCopyLenTheory.ptr_covers_lookup_frame >>
     qexistsl [`Gu`,`u`,`tu`] >> simp[] >>
     qpat_assum `!x. not_fresh_at (sd with cs_next_id := _) x ==> _`
       (qspec_then `r` mp_tac) >>
     impl_tac >-
       (qpat_assum `not_fresh_at sd r` mp_tac >>
        simp[NoAsms, loweringStateRelDefsTheory.not_fresh_at_def]) >>
     strip_tac >> simp[]) >>
  qabbrev_tac `ptvs = MAP (THE o evaluate_type (get_tenv cx)) arg_types` >>
  `LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs` by
    (irule vyperTypeABITheory.evaluate_types_LIST_REL >> first_assum ACCEPT_TAC) >>
  `LENGTH tys = LENGTH xs /\ LENGTH tvs = LENGTH xs /\
   LENGTH ptvs = LENGTH xs /\ LENGTH arg_types = LENGTH xs` by
    simp[Abbr `tvs`, Abbr `ptvs`] >>
  `!i. i < LENGTH xs ==>
     arg_type_fits (EL i tys) (EL i arg_types) /\
     evaluate_type (get_tenv cx) (EL i arg_types) = SOME (EL i ptvs) /\
     value_has_type (EL i tvs) (EL i argvs) /\
     value_has_type (EL i ptvs) (EL i argvs)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!i. i < LENGTH xs ==> _` (qspec_then `i` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (qx_choose_then `e` (qx_choose_then `sv` (qx_choose_then `v`
       (qx_choose_then `raw` (qx_choose_then `si` (qx_choose_then `arg_sm`
         (qx_choose_then `ss` (qx_choose_then `vv` (qx_choose_then `phys_tv`
           (qx_choose_then `param_tv` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))))))) >>
     `EL i tys = lowered_value_type cenv e` by
       (qpat_assum `tys = MAP _ xs` SUBST1_TAC >>
        qpat_assum `i < LENGTH xs` (fn hi =>
          qpat_assum `e = EL i xs` (fn he =>
            simp[NoAsms,listTheory.EL_MAP,hi,GSYM he]))) >>
     `EL i ptvs = param_tv` by
       (`i < LENGTH arg_types` by decide_tac >>
        qpat_assum `i < LENGTH arg_types` (fn hi =>
          qpat_assum `evaluate_type _ (EL i arg_types) = SOME param_tv` (fn ht =>
            simp[NoAsms, Abbr `ptvs`, listTheory.EL_MAP, hi, ht]))) >>
     `EL i tvs = phys_tv` by
       (`i < LENGTH tys` by decide_tac >>
        qpat_assum `i < LENGTH tys` (fn hi =>
          qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME phys_tv` (fn ht =>
            qpat_assum `EL i tys = _` (fn he =>
              simp[NoAsms, Abbr `tvs`, listTheory.EL_MAP, hi, he, ht])))) >>
     qpat_assum `v = EL i argvs` (SUBST1_TAC o SYM) >>
     qpat_assum `EL i tys = _` SUBST1_TAC >>
     qpat_assum `EL i ptvs = _` SUBST1_TAC >>
     qpat_assum `EL i tvs = _` SUBST1_TAC >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `arg_types_fit tys arg_types /\
   LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) arg_types ptvs /\
   values_have_types tvs argvs /\ values_have_types ptvs argvs` by
    (rewrite_tac[vyperTypeArgFitsTheory.arg_types_fit_LIST_REL,
                 vyperTypeDefaultsTheory.values_have_types_LIST_REL, listTheory.LIST_REL_EL_EQN] >> BETA_TAC >>
     rpt strip_tac >>
     FIRST_PROVE [decide_tac,
       qmatch_goalsub_rename_tac `EL i _` >>
       `i < LENGTH xs` by decide_tac >>
       qpat_assum `!i. i < LENGTH xs ==> arg_type_fits _ _ /\ _` (qspec_then `i` mp_tac) >>
       impl_tac >- first_assum ACCEPT_TAC >>
       disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> first_assum ACCEPT_TAC]) >>
  `?avs. vyper_to_abi_list (get_tenv cx) arg_types argvs = SOME avs` by
    (irule (cj 2 vyperTypeABITheory.vyper_to_abi_total) >>
     qexists `ptvs` >> simp[]) >>
  `vyper_to_abi_types (get_tenv cx) tys = vyper_to_abi_types (get_tenv cx) arg_types /\
   vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV argvs)) = SOME (ListV avs)` by
    (drule (cj 2 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_abi_type) >>
     strip_tac >> simp[vyperABITheory.vyper_to_abi_def] >>
     drule_all (cj 2 exprSimAbiEncodeArgsPhysicalCapacityTheory.abi_args_fits_conversion) >>
     disch_then (qspec_then `argvs` mp_tac) >> simp[]) >>
  `stmt_state_rel HH ctx func cenv cx ee q` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
          gas_origin_ptr_path _ (u,Gu,tu) [] (OK q,Gq,tq) /\ _`
       (qspec_then `HH` mp_tac) >> simp[NoAsms] >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!i w b sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
    i.inst_id IN frag_ids sadd senc /\ i.inst_operands = [Lit w] /\
    FLOOKUP q.vs_allocas i.inst_id = SOME (b,sz) ==> sz = w2n w` by
    (drule stateRelProjTheory.stmt_state_rel_alloca_size >> metis_tac[]) >>
  `fn_has_code st sadd func /\ fn_has_code sadd sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code sadd senc func /\ fn_has_code senc sf func` by
    (irule fragExecTheory.fn_has_code_split >> simp[]) >>
  `ci_mono sd st` by
    (`!rows off cs. ci_mono cs
        (SND (compile_extcall_store_values cenv rows aa.buf_operand off cs))` by
       (POP_ASSUM_LIST (K ALL_TAC) >> Induct_on `rows` >> rpt gen_tac
        >- simp[exprLoweringTheory.compile_extcall_store_values_def,
                exprLoweringPropsTheory.ci_mono_comp_return] >>
        PairCases_on `h` >>
        simp[Once exprLoweringTheory.compile_extcall_store_values_def] >>
        ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >>
        conj_tac >- simp[exprLoweringPropsTheory.ci_mono_emit_op] >>
        rpt strip_tac >> ho_match_mp_tac exprLoweringPropsTheory.ci_mono_bind >>
        conj_tac >- simp[exprLoweringPropsTheory.ci_mono_unwrap_value] >>
        rpt strip_tac >> ho_match_mp_tac exprLoweringPropsTheory.ci_mono_ignore_bind >>
        conj_tac >- (IF_CASES_TAC >>
          simp[exprLoweringPropsTheory.ci_mono_emit_void,
               exprLoweringPropsTheory.ci_mono_compile_store_bytestring] >>
          IF_CASES_TAC >>
          simp[exprLoweringPropsTheory.ci_mono_emit_void,
               exprLoweringPropsTheory.ci_mono_compile_store_bytestring]) >>
        rpt strip_tac >> first_x_assum irule) >>
     pop_assum (qspecl_then [`ZIP (vals,tys)`,`0`,`sd`] mp_tac) >> simp[]) >>
  `sd.cs_next_var <= st.cs_next_var /\ sd.cs_next_id <= st.cs_next_id` by
    (qpat_assum `ci_mono sd st` mp_tac >> simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
  `alloca_inv q /\ alloca_room ctx func q` by
    (qpat_assum `stmt_state_rel HH ctx func _ _ _ q` (fn th =>
       mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca th) >>
       mp_tac (MATCH_MP stateRelProjTheory.stmt_state_rel_alloca_room th)) >> simp[]) >>
  `allocas_from lo q` by
    (`lo <= u.vs_alloca_next` by decide_tac >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK q,Gq,tq)`
       (qspec_then `DF HH` assume_tac) >>
     drule_all bodyFullAbiEncodeOriginFloorTheory.abi_encode_origin_path_allocas_from >> simp[]) >>
  `val_footprint (TupleTV tvs) (ArrayV (TupleV argvs)) = mem` by
    simp[loweringPostsTheory.val_footprint_def, valueEncodingTheory.type_memory_size_def] >>
  `value_has_type (TupleTV tvs) (ArrayV (TupleV argvs))` by
    simp[vyperTypingTheory.value_has_type_def] >>
  `32 + abi <= n` by (simp[NoAsms,Abbr `n`] >> IF_CASES_TAC >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q /\
    q.vs_alloca_next + pending_alloca_size func q <= w2n q.vs_initial_fmp` by simp[] >>
  qabbrev_tac `bytes = contractABI$enc
    (Tuple (vyper_to_abi_types (get_tenv cx) arg_types)) (ListV avs)` >>
  mp_tac (Q.INST [`a` |-> `st`, `b` |-> `sadd`, `c` |-> `senc`, `d` |-> `sf`, `e` |-> `sp`,
      `root` |-> `r`, `src` |-> `p`, `ei` |-> `aenc`, `fn` |-> `func`,
      `s` |-> `q`, `G` |-> `Gq`, `tn` |-> `tq`, `shared` |-> `se.cs_next_id`,
      `source` |-> `sm.cs_next_id`, `p0` |-> `w2n (rw:bytes32)`, `q0` |-> `w2n (z:bytes32)`,
      `capacity` |-> `n`, `source_capacity` |-> `mem`, `env` |-> `get_tenv cx`,
      `ty` |-> `TupleT tys`, `tv` |-> `TupleTV tvs`, `v` |-> `ArrayV (TupleV argvs)`,
      `av` |-> `ListV avs`, `selector` |-> `bs`]
    (Q.INST [`p` |-> `p0`, `q` |-> `q0`] extcall_packed_tuple_tail_local_sizes)) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     TRY (FIRST_PROVE
       [qpat_assum `ba.buf_operand = Var r` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC,
        qpat_assum `aa.buf_operand = Var p` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC]) >>
     TRY (FIRST_PROVE [
       qpat_assum `val_footprint (TupleTV tvs) (ArrayV (TupleV argvs)) = mem` SUBST1_TAC >>
         first_assum ACCEPT_TAC,
       simp[NoAsms,wordsTheory.n2w_w2n] >> first_assum ACCEPT_TAC,
       qpat_assum `vyper_to_abi_types _ tys = vyper_to_abi_types _ arg_types`
         (fn th => simp[NoAsms,Abbr `bytes`,vyperABITheory.vyper_to_abi_type_def,th])]) >>
     FIRST_PROVE [decide_tac,
       irule freshWritesTheory.not_fresh_at_mono >> qexists `sd` >> simp[],
       map_every (fn pat => qpat_assum pat (SUBST1_TAC o SYM))
         [`tys = MAP (lowered_value_type cenv) xs`,
          `abi = vyper_abi_size_bound (get_tenv cx) (TupleT tys)`] >> decide_tac]) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choose_then `x` (qx_choose_then `y`
    (qx_choose_then `t` (qx_choose_then `Gf` (qx_choose_then `tf` strip_assume_tac)))))) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    (gen_tac >>
     `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK q,Gq,tq)` by
       (qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK u,Gu,tu)`
          (qspec_then `D` (qspecl_then [`u`,`Gu`,`tu`,`[]`,`OK q`,`Gq`,`tq`] mp_tac o
             MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append)) >> simp[]) >>
     qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK q,Gq,tq)`
       (qspecl_then [`q`,`Gq`,`tq`,`[]`,`OK t`,`Gf`,`tf`] mp_tac o
        MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_append) >> simp[]) >>
  `ci_mono st sadd /\ ci_mono sadd senc /\ ci_mono senc sf /\ ci_mono sf sp` by
    (mp_tac (Q.SPECL [`ADD`,`[ba.buf_operand; Lit 32w]`,`st`] exprLoweringPropsTheory.ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`dst`,`aa.buf_operand`,`aenc`,`sadd`] (cj 2 exprLoweringPropsTheory.ci_mono_compile_abi_encode)) >>
     mp_tac (Q.SPECL [`ADD`,`[alen; Lit 4w]`,`senc`] exprLoweringPropsTheory.ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`ADD`,`[ba.buf_operand; Lit 28w]`,`sf`] exprLoweringPropsTheory.ci_mono_emit_op) >> simp[]) >>
  `st.cs_next_id <= sp.cs_next_id /\ st.cs_next_var <= sp.cs_next_var` by
    (qpat_assum `ci_mono st sadd` mp_tac >> qpat_assum `ci_mono sadd senc` mp_tac >>
     qpat_assum `ci_mono senc sf` mp_tac >> qpat_assum `ci_mono sf sp` mp_tac >>
     simp[NoAsms,exprLoweringPropsTheory.ci_mono_def]) >>
  `build_ext_calldata (get_tenv cx) fname arg_types argvs = SOME (bs ++ bytes)` by
    (`TAKE (LENGTH argvs) arg_types = arg_types` by
       (irule listTheory.TAKE_LENGTH_ID_rwt >> first_assum ACCEPT_TAC) >>
     qpat_assum `TAKE (LENGTH argvs) arg_types = arg_types` (fn take =>
       qpat_assum `vyper_to_abi_list _ arg_types argvs = SOME avs` (fn conv =>
         simp[NoAsms,vyperABITheory.build_ext_calldata_def,take,conv,Abbr `bs`,Abbr `bytes`]))) >>
  `gas_origin_ptr_path (DF HH,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK t,Gf,tf)` by
    (first_assum (qspec_then `DF HH` ACCEPT_TAC)) >>
  `alloca_history func t` by
    (drule bodyFullPathHistoryTheory.body_full_path_alloca_history >>
     disch_then irule >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `se.cs_next_var <= st.cs_next_var` by decide_tac >>
  `se.cs_next_var <= (sd with cs_next_id := sm.cs_next_id).cs_next_var /\
   se.cs_next_id <= (sd with cs_next_id := sm.cs_next_id).cs_next_id` by simp[] >>
  `wb_frame cenv ee ee se s q` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee s`
       (mp_then Any irule
          (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans)) >>
     qpat_assum `wb_frame cenv ee ee (sd with cs_next_id := sm.cs_next_id) u q`
       (irule_at Any) >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv ee se G tn s Gq tq` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee s`
       (mp_then Any irule wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv ee (sd with cs_next_id := sm.cs_next_id) Gu tu u Gq tq`
       (irule_at Any) >>
     qexists `ee` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid row. FLOOKUP q.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row` by
    (rpt strip_tac >>
     drule_all abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_allocated >>
     disch_then ACCEPT_TAC) >>
  `allocation_growth q t` by
    (qpat_assum `gas_origin_ptr_path (DF HH,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK t,Gf,tf)`
       (mp_then Any irule body_full_origin_path_allocation_growth) >> simp[]) >>
  `se.cs_next_id <= sadd.cs_next_id` by
    (qpat_assum `ci_mono st sadd` mp_tac >>
     simp[NoAsms,exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!i. i IN window_alloca_sites func (frag_ids sadd senc) ==> se.cs_next_id <= i` by
    (rpt strip_tac >> drule (REWRITE_RULE [pred_setTheory.SUBSET_DEF]
       abiEncoderWindowContractTheory.window_alloca_sites_subset) >>
     simp[abiEncoderPropsTheory.frag_ids_def] >> decide_tac) >>
  `32 + LENGTH bytes <= n` by
    (drule_all abiEncoderSourceRobustTheory.abi_encoder_source_window_robust >>
     disch_then (qx_choose_then `ct` (qx_choose_then `rv` strip_assume_tac)) >>
     `contractABI$enc ct rv = bytes` by
       (qpat_assum `contractABI$enc ct rv = _` SUBST1_TAC >>
        simp[Abbr `bytes`,vyperABITheory.vyper_to_abi_type_def]) >>
     `LENGTH bytes <= abi` by
       (qpat_assum `contractABI$enc ct rv = bytes` (SUBST1_TAC o SYM) >>
        qpat_assum `abi = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >> decide_tac) >>
  qabbrev_tac `ids = window_alloca_sites func (frag_ids sadd senc)` >>
  `!b k.
      ((?old. old < se.cs_next_id /\ FLOOKUP q.vs_allocas old = SOME (b,k)) \/
       (?ptr. local_backed func ptr q b k /\ b+k <= q.vs_alloca_next /\
          (!inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
             inst.inst_outputs = [ptr] ==> inst.inst_id NOTIN (se.cs_next_id INSERT ids))) \/
       (b+k <= q.vs_alloca_next /\
        (!i r sz. i IN (se.cs_next_id INSERT ids) /\ FLOOKUP q.vs_allocas i = SOME (r,sz) ==>
           b+k <= r \/ r+sz <= b))) ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k q.vs_memory /\
      (!j. b <= j /\ j < b+k /\ j IN tf.t_mem ==> j IN tq.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     mp_tac (Q.INST [`q` |-> `q`, `t` |-> `t`, `func` |-> `func`,
        `shared` |-> `se.cs_next_id`, `cut` |-> `se.cs_next_id`, `ids` |-> `ids`,
        `p` |-> `w2n (rw:bytes32)`, `n` |-> `n`, `dst` |-> `w2n (rw:bytes32)+32`,
        `m` |-> `LENGTH (bytes:word8 list)`, `tf` |-> `tf`, `tq` |-> `tq`,
        `b` |-> `b`, `k` |-> `k`] extcall_encoder_caller_window) >>
     impl_tac >-
       (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac,
         simp[NoAsms, Abbr `ids`] >> first_assum ACCEPT_TAC]) >>
     disch_then ACCEPT_TAC) >>
  `!aid b k. FLOOKUP q.vs_allocas aid = SOME (b,k) /\ aid < se.cs_next_id ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k q.vs_memory /\
      (!j. b <= j /\ j < b+k /\ j IN tf.t_mem ==> j IN tq.t_mem)` by
    (rpt gen_tac >> strip_tac >> first_assum irule >>
     disj1_tac >> qexists `aid` >> simp[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo q.vs_memory /\
   (!j. j < lo /\ j IN tf.t_mem ==> j IN tq.t_mem)` by
    (qpat_assum `!b k. _ ==> mem_bytes_at b k t.vs_memory = _ /\ _`
       (qspecl_then [`0`,`lo`] mp_tac) >>
     simp[NoAsms] >> impl_tac >-
       (disj2_tac >> disj2_tac >> conj_tac >- decide_tac >>
        rpt gen_tac >> strip_tac >> disj1_tac >>
        qpat_assum `allocas_from lo q` (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
        disch_then (drule_then ACCEPT_TAC)) >> simp[NoAsms]) >>
  `MEM (mk_inst se.cs_next_id ALLOCA [Lit (n2w n)]
          [STRING #"%" (toString se.cs_next_var)]) (fn_insts func)` by
    (irule compileAllocaProvenanceTheory.fn_has_code_current_member >>
     qexistsl [`se`,`sb`] >>
     qpat_assum `compile_alloc_buffer n se = _`
       (strip_assume_tac o MATCH_MP abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
     simp[]) >>
  `!i. i IN se.cs_next_id INSERT ids ==>
     ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_id = i` by
    (simp[NoAsms, Abbr `ids`, abiEncoderWindowContractTheory.window_alloca_sites_def] >>
     gen_tac >> strip_tac
     >- (qexists `mk_inst se.cs_next_id ALLOCA [Lit (n2w n)]
                   [STRING #"%" (toString se.cs_next_var)]` >> simp[venomInstTheory.mk_inst_def]) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_rel func cenv ee.scopes q` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee q`
       (mp_then Any (ACCEPT_TAC o CONJUNCT1) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca)) >>
  `!name b k. local_region cenv ee.scopes q name b k ==>
      mem_bytes_at b k t.vs_memory = mem_bytes_at b k q.vs_memory /\
      (!j. b <= j /\ j < b+k /\ j IN tf.t_mem ==> j IN tq.t_mem)` by
    (rpt gen_tac >> simp[NoAsms,loweringStateRelDefsTheory.local_region_def] >>
     disch_then (qx_choose_then `entry` (qx_choose_then `lp` (qx_choose_then `lw` strip_assume_tac))) >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes q`
       (drule_all_then strip_assume_tac o cj 1 o
        PURE_REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
     `local_backed func lp q b k /\ b+k <= q.vs_alloca_next` by
       (qpat_assum `b = w2n lw` SUBST1_TAC >>
        qpat_x_assum `lookup_var lp q = SOME lw` mp_tac >>
        qpat_assum `lookup_var lp q = SOME w` (fn th => simp[NoAsms,th]) >>
        disch_then (SUBST1_TAC o SYM) >> simp[]) >>
     qpat_assum `!b k. (?old. _) \/ _ ==> mem_bytes_at b k t.vs_memory = _ /\ _` irule >>
     disj2_tac >> disj1_tac >> qexists `lp` >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (strip_tac >>
         `inst = mk_inst se.cs_next_id ALLOCA [Lit (n2w n)]
                     [STRING #"%" (toString se.cs_next_var)]` by
           (irule localPtrsPropsTheory.fn_inst_ids_distinct_inj >> conj_tac
            >- simp[venomInstTheory.mk_inst_def] >> qexists `func` >> simp[]) >>
         `not_local_ptr cenv ee.scopes (STRING #"%" (toString se.cs_next_var))` by
           (irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >> qexists `se` >> simp[]) >>
         qpat_x_assum `inst.inst_outputs = [lp]` mp_tac >> simp[venomInstTheory.mk_inst_def] >>
         disch_then SUBST_ALL_TAC >>
         qpat_assum `not_local_ptr cenv ee.scopes _`
           (mp_tac o REWRITE_RULE [loweringStateRelDefsTheory.not_local_ptr_def]) >>
         simp[NoAsms] >> metis_tac[]) >>
     simp[NoAsms, Abbr `ids`] >>
     irule exprSimAbiEncodeCallerFrameTheory.abi_encode_scratch_local_id_exclusion >>
     qpat_assum `compile_abi_encode_to_buf dst aa.buf_operand aenc sadd = (alen,senc)` (irule_at Any) >>
     qpat_assum `FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var lp) k)` (irule_at Any) >>
     qpat_assum `lookup_scopes name ee.scopes = SOME entry` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv se` (irule_at Any) >>
     qexists `func` >> simp[NoAsms] >> rpt conj_tac >>
     FIRST [first_assum ACCEPT_TAC,
       qpat_assum `ci_mono st sadd` mp_tac >>
       simp[NoAsms,exprLoweringPropsTheory.ci_mono_def] >> decide_tac]) >>
  `cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
       mem_bytes_at off (type_memory_size tv) t.vs_memory =
       mem_bytes_at off (type_memory_size tv) q.vs_memory` by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `stmt_state_rel HH ctx func cenv cx ee q`
       (mp_tac o MATCH_MP bodyFullIntCallReturnFrameTheory.return_stmt_immutable_sep) >>
     simp[NoAsms,exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     disch_then (mp_tac o CONJUNCT2) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (drule_all_then strip_assume_tac) >>
     rename1 `mem_bytes_at imm_off (type_memory_size imm_tv) t.vs_memory = _` >>
     qpat_assum `!b k. (?old. _) \/ _ ==> mem_bytes_at b k t.vs_memory = _ /\ _`
       (qspecl_then [`imm_off`,`type_memory_size imm_tv`] mp_tac) >>
     impl_tac >-
       (disj2_tac >> disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
        rpt gen_tac >> strip_tac >>
        qpat_assum `!i. _ ==> ?inst. MEM inst _ /\ _`
          (first_assum o mp_then Any strip_assume_tac) >>
        qpat_x_assum `inst.inst_id = i` (SUBST_ALL_TAC o SYM) >>
        qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
          (drule_all_then mp_tac) >> simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def]) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `gas_path_mem ctx func q 0 (OK t)` by
    (qpat_assum `gas_origin_ptr_path (DF HH,lo,explicit,ctx,func,PG) (q,Gq,tq) [] (OK t,Gf,tf)`
       (mp_tac o MATCH_MP fragGasOriginPtrTheory.gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP fragGasOriginTheory.gas_origin_path_erase o CONJUNCT1) >>
     simp[NoAsms,fragGasModeTheory.gas_marked_path_def]) >>
  `!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
      sz = w2n n` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee q`
       (mp_then Any assume_tac stateRelProjTheory.stmt_state_rel_alloca_size) >>
     qpat_assum `gas_path_mem ctx func q 0 (OK t)`
       (qspec_then `t` mp_tac o
        MATCH_MP ctorDeployMemoryRunMemEntryLiteralPathTheory.ctor_path_literal_sizes) >>
     (impl_tac >- REFL_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then ACCEPT_TAC) >>
  `!x. not_fresh_at se x ==> FLOOKUP Gf x = FLOOKUP Gq x /\
       op_taint tf (Var x) = op_taint tq (Var x) /\
       (!w. lookup_var x q = SOME w ==> lookup_var x t = SOME w)` by
    (qx_gen_tac `oldvar` >> strip_tac >>
     `not_fresh_at st oldvar` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `se` >> simp[]) >>
     qpat_assum `!z. not_fresh_at st z ==> FLOOKUP Gf z = _ /\ _`
       (drule_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee t` by
    (rpt strip_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,Gu,tu) [] (OK q,Gq,tq) /\ _`
       (drule_then strip_assume_tac) >>
     irule extcall_encoder_stmt_frame >>
     qpat_assum `abi_encoder_registered_effect _ _ q t` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv se` (irule_at Any) >>
     simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     FIRST [first_assum (drule_all_then ACCEPT_TAC),
            first_assum (drule_all_then (ACCEPT_TAC o CONJUNCT1)),
            qpat_assum `!z. not_fresh_at se z ==> FLOOKUP Gf z = _ /\ _`
              (drule_then (drule_then ACCEPT_TAC o cj 3))]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       wb_frame cenv ee ee se q t /\
       ghost_kept_at lo cenv ee se Gq tq q Gf tf /\
       ghost_inv_at (DF H) lo d cenv cx ee Gf tf t` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (u,Gu,tu) [] (OK q,Gq,tq) /\ _`
       (drule_then strip_assume_tac) >>
     `stor_taint_ok_at (DF H) tf t` by
       (qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gq tq q`
          (assume_tac o cj 4 o REWRITE_RULE [bodyPtrDefsTheory.ghost_inv_at_def]) >>
        qpat_assum `abi_encode_exec_frame func q t`
          (strip_assume_tac o REWRITE_RULE [exprSimAbiEncodeExecFrameTheory.abi_encode_exec_frame_def,
                                          exprSimAbiEncodeSemanticTheory.abi_encode_semantic_obs_fields]) >>
        qpat_assum `abi_encoder_registered_effect _ _ q t`
          (strip_assume_tac o REWRITE_RULE [abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]) >>
        qpat_x_assum `stor_taint_ok_at (DF H) tq q` mp_tac >>
        simp[bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
     match_mp_tac extcall_encoder_caller_frames >>
     qpat_assum `ghost_inv_at (DF H) lo d cenv cx ee Gq tq q` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes q` (irule_at Any) >>
     simp[NoAsms] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >>
     qpat_assum `!z. not_fresh_at se z ==> FLOOKUP Gf z = _ /\ _`
       (drule_then (fn th => FIRST [ACCEPT_TAC (cj 1 th), ACCEPT_TAC (cj 2 th),
                                   drule_then ACCEPT_TAC (cj 3 th)]))) >>
  qpat_assum `!H. _ ==> wb_frame cenv ee ee se q t /\ _`
    (drule_then strip_assume_tac) >>
  `wb_frame cenv ee ee se s t` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee s`
       (mp_then Any irule
          (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans)) >>
     qpat_assum `wb_frame cenv ee ee se q t` (irule_at Any) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv ee se G tn s Gf tf` by
    (qpat_assum `stmt_state_rel HH ctx func cenv cx ee s`
       (mp_then Any irule wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv ee se Gq tq q Gf tf` (irule_at Any) >>
     qexists `ee` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee sa s0 t` by
    (irule exprSimWordArgsTheory.wb_frame_trans >>
     qpat_assum `wb_frame cenv ee ee se s t` (irule_at Any) >>
     qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0` (irule_at Any) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region cenv ee.scopes s name b k <=>
              local_region cenv es.scopes s0 name b k` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s0`
       (mp_then Any (assume_tac o CONJUNCT1) stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `wb_frame cenv es ee sa s0 s`
       (assume_tac o cj 1 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     rpt gen_tac >> eq_tac >> strip_tac
     >- (irule exprSimPropsTheory.local_region_frame >>
         qpat_assum `local_ptrs_rel func cenv es.scopes s0` (irule_at Any) >>
         qpat_assum `local_region cenv ee.scopes s name b k` (irule_at Any) >>
         qexists `sa` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     irule exprSimPropsTheory.local_region_frame_fwd >>
     qpat_assum `local_region cenv es.scopes s0 name b k` (irule_at Any) >>
     qexists `sa` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tf` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qpat_assum `ghost_kept_at lo cenv ee se G tn s Gf tf` (irule_at Any) >>
     qpat_assum `wb_frame cenv es ee sa s0 s`
       (assume_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `q.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `allocation_growth q t`
       (ACCEPT_TAC o cj 3 o REWRITE_RULE [allocationGrowthTheory.allocation_growth_def])) >>
  `s.vs_alloca_next <= t.vs_alloca_next /\ s0.vs_alloca_next <= t.vs_alloca_next /\
   sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id /\ cap <= n` by
    (simp[Abbr `n`] >> IF_CASES_TAC >> decide_tac) >>
  `local_ptrs_reserved cenv sp` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `se` >> simp[] >> decide_tac) >>
  qpat_assum `wb_frame cenv ee ee se s t`
    (assume_tac o cj 1 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
  qpat_assum `ghost_kept_at lo cenv ee se G tn s Gf tf`
    (assume_tac o cj 1 o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `!op. safe_operand se op ==> safe_operand sp op /\
       op_taint tf op = op_taint tn op /\
       (!w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)` by
    (Cases >> simp[NoAsms, venomStateTheory.eval_operand_def,
                   exprSafeOperandTheory.safe_operand_def] >>
     TRY (simp[NoAsms, ptrDisciplineTheory.op_taint_def] >> NO_TAC) >>
     rpt strip_tac >> FIRST
       [qpat_assum `!x. not_fresh_at se x ==> FLOOKUP Gf x = _ /\ _`
          (drule_then (ACCEPT_TAC o CONJUNCT2)),
        first_assum (drule_all_then ACCEPT_TAC),
        irule freshWritesTheory.not_fresh_at_mono >> qexists `se` >>
        simp[NoAsms] >> rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac]]) >>
  (* A registered row at the tuple-store cut is either itself a local
     region or disjoint from every local: local backing cannot partially
     overlap a registered row. Use the appropriate clause of each frame. *)
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,k) ==>
       mem_bytes_at b k q.vs_memory = mem_bytes_at b k u.vs_memory /\
       (!j. b <= j /\ j < b+k /\ j IN tq.t_mem ==> j IN tu.t_mem)` by
    (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee u /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `stmt_state_rel HH ctx func cenv cx ee u`
       (strip_assume_tac o MATCH_MP stateRelProjTheory.stmt_state_rel_local_ptrs_alloca) >>
     qpat_assum `wb_frame _ _ _ (sd with cs_next_id := _) u q`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `ghost_kept_at _ _ _ (sd with cs_next_id := _) Gu tu u Gq tq`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     rpt gen_tac >> strip_tac >>
     Cases_on `?nm. local_region cenv ee.scopes u nm b k`
     >- (qpat_x_assum `?nm. local_region cenv ee.scopes u nm b k`
           (qx_choose_then `row_local` assume_tac) >>
         conj_tac
         >- (qpat_assum `locals_kept cenv ee ee u q` mp_tac >>
             simp[NoAsms, loweringPostsTheory.locals_kept_def] >>
             disch_then strip_assume_tac >>
             qpat_assum `!name b sz. local_region cenv ee.scopes u name b sz ==> mem_bytes_at b sz q.vs_memory = _`
               (qspecl_then [`row_local`,`b`,`k`] mp_tac) >> simp[]) >>
         rpt strip_tac >>
         qpat_assum `!name b sz i. local_region cenv ee.scopes u name b sz /\ _ ==> i IN tu.t_mem`
           (qspecl_then [`row_local`,`b`,`k`,`j`] mp_tac) >> simp[]) >>
     `!nm a sz. local_region cenv ee.scopes u nm a sz ==> b+k <= a \/ a+sz <= b` by
       (rpt gen_tac >>
        simp[NoAsms, loweringStateRelDefsTheory.local_region_def] >>
        disch_then (qx_choose_then `entry` (qx_choose_then `lp` (qx_choose_then `lw` strip_assume_tac))) >>
        `local_backed func lp u a sz` by
          (qpat_assum `local_ptrs_rel func cenv ee.scopes u`
             (drule_all_then strip_assume_tac o cj 1 o
              PURE_REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
           qpat_assum `a = w2n lw` SUBST1_TAC >>
           qpat_x_assum `lookup_var lp u = SOME lw` mp_tac >>
           qpat_assum `lookup_var lp u = SOME w` (fn th => simp[NoAsms,th]) >>
           disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
        qpat_assum `local_backed func lp u a sz` mp_tac >>
        simp[NoAsms,loweringStateRelDefsTheory.local_backed_def] >> strip_tac
        >- (`inst.inst_id <> aid` by
              (strip_tac >>
               `a = b /\ sz = k` by
                 (qpat_assum `FLOOKUP u.vs_allocas inst.inst_id = SOME (a,sz)` mp_tac >>
                  qpat_assum `inst.inst_id = aid` (fn th => simp[NoAsms,th]) >>
                  qpat_assum `FLOOKUP u.vs_allocas aid = SOME (b,k)` (fn th => simp[NoAsms,th]) >>
                  metis_tac[]) >>
               qpat_assum `~(?nm. local_region cenv ee.scopes u nm b k)` mp_tac >>
               simp[NoAsms,loweringStateRelDefsTheory.local_region_def] >>
               qexistsl [`nm`,`entry`,`lp`,`lw`] >> simp[]) >>
            qpat_assum `alloca_inv u`
              (mp_tac o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
            simp[NoAsms, venomMemDefsTheory.allocas_non_overlapping_def] >>
            disch_then (qspecl_then [`aid`,`inst.inst_id`,`b`,`k`,`a`,`sz`] mp_tac) >> simp[]) >>
        first_x_assum (qspecl_then [`aid`,`b`,`k`] mp_tac) >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     `aid < (sd with cs_next_id := sm.cs_next_id).cs_next_id` by simp[] >>
     conj_tac
     >- (qpat_assum `!aid off sz. FLOOKUP u.vs_allocas aid = SOME _ /\ _ ==> mem_bytes_at off sz q.vs_memory = _`
           (qspecl_then [`aid`,`b`,`k`] mp_tac) >> simp[] >>
         (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME _ /\ _ ==> i IN tu.t_mem`
       (qspecl_then [`aid`,`b`,`k`,`j`] mp_tac) >> simp[] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[]) >>
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
       mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
       (!j. b <= j /\ j < b+k /\ j IN tf.t_mem ==> j IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (b,k)` by
       (qpat_assum `wb_frame cenv ee ee se s u`
          (mp_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
        disch_then (drule_then ACCEPT_TAC)) >>
     `FLOOKUP q.vs_allocas aid = SOME (b,k)` by
       (qpat_assum `wb_frame _ _ _ (sd with cs_next_id := _) u q`
          (mp_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
        disch_then (drule_then ACCEPT_TAC)) >>
     qpat_assum `!a k. a < se.cs_next_id ==> FLOOKUP s.vs_allocas a = SOME k ==> _`
       (qspecl_then [`aid`,`(b,k)`] mp_tac) >> simp[NoAsms] >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!a b k. a < se.cs_next_id /\ FLOOKUP u.vs_allocas a = SOME (b,k) ==> _`
       (qspecl_then [`aid`,`b`,`k`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `!a b k. FLOOKUP q.vs_allocas a = SOME (b,k) /\ a < se.cs_next_id ==> _`
       (qspecl_then [`aid`,`b`,`k`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >> conj_tac
     >- asm_rewrite_tac[] >>
     rpt strip_tac >>
     `j IN tq.t_mem` by first_assum (drule_all_then ACCEPT_TAC) >>
     `j IN tu.t_mem` by first_assum (drule_all_then ACCEPT_TAC) >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  qpat_assum `EVERY (safe_operand se) [addr;value;gas;def]`
    (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  qpat_assum `EVERY (\op. op_taint tn op = {}) [addr;value;gas;def]`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  map_every (fn operand => qpat_assum `!op. safe_operand se op ==> _`
     (qspec_then operand (drule_then strip_assume_tac))) [`addr`,`value`,`gas`,`def`] >>
  `!dv. dopt = SOME dv /\ ~is_word_type dt ==>
       ?w tv. eval_operand def s = SOME w /\ eval_operand def t = SOME w /\
           evaluate_type (get_tenv cx) dt = SOME tv /\ val_wf tv dv /\
           mem_bytes_at (w2n w) (type_memory_size tv) t.vs_memory =
             mem_bytes_at (w2n w) (type_memory_size tv) s.vs_memory /\
           (!i. w2n w <= i /\ i < w2n w + type_memory_size tv /\ i IN tf.t_mem ==>
                i IN tn.t_mem)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ptr_mem_ok cx dt dv def G tn s /\ _ /\ ?w aid tv. _`
       (drule_all_then strip_assume_tac) >>
     qpat_assum `!aid b k. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
        mem_bytes_at b k t.vs_memory = _ /\ _`
       (qspecl_then [`aid`,`w2n w`,`type_memory_size tv`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qexistsl [`w`,`tv`] >> simp[]) >>
  `extcall_default_ready cx rt hasdef def dt dopt t` by
    (qpat_assum `extcall_default_ready cx rt hasdef def dt dopt s`
       (strip_assume_tac o PURE_REWRITE_RULE [exprSimExtCallCaseTheory.extcall_default_ready_def]) >>
     pure_rewrite_tac[exprSimExtCallCaseTheory.extcall_default_ready_def] >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     qx_gen_tac `default_v` >> disch_tac >>
     qpat_assum `!d. dopt = SOME d ==> _`
       (drule_then (CONJUNCTS_THEN2 assume_tac
          (qx_choose_then `dtv` (qx_choose_then `rtv` (qx_choose_then `dw` strip_assume_tac))))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `eval_operand def t = SOME dw` by first_assum (drule_then ACCEPT_TAC) >>
     qexistsl [`dtv`,`rtv`,`dw`] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (Cases_on `is_word_type dt`
         >- (qpat_assum `expr_val_rel cx dt default_v def s`
               (qx_choose_then `old_dw` strip_assume_tac o
                REWRITE_RULE [loweringPostsTheory.expr_val_rel_def]) >>
             `old_dw = dw` by metis_tac[optionTheory.SOME_11] >>
             `dw = typed_val_to_w256 dtv default_v` by
               (qpat_assum `!tv. evaluate_type (get_tenv cx) dt = SOME tv ==> _`
                  (qspec_then `dtv` (drule_then mp_tac)) >>
                asm_rewrite_tac[]) >>
             pure_rewrite_tac[loweringPostsTheory.expr_val_rel_def] >>
             qexists `dw` >> conj_tac >- first_assum ACCEPT_TAC >>
             gen_tac >>
             qpat_assum `evaluate_type (get_tenv cx) dt = SOME dtv`
               (fn th => rewrite_tac[th,optionTheory.SOME_11]) >>
             disch_then (SUBST1_TAC o SYM) >> asm_rewrite_tac[]) >>
         qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ?w tv. _`
           (drule_all_then (qx_choose_then `mw` (qx_choose_then `mtv` strip_assume_tac))) >>
         irule exprSimPropsTheory.expr_val_rel_mem_agree >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexistsl [`s`,`mtv`,`mw`] >>
         rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE sym_tac >> first_assum ACCEPT_TAC)) >>
     strip_tac >>
     `w2n dw + val_footprint dtv default_v <= s.vs_alloca_next`
       by first_assum (drule_then ACCEPT_TAC) >> decide_tac) >>
  `!dv. dopt = SOME dv /\ ~is_word_type dt ==>
     ptr_mem_ok cx dt dv def Gf tf t /\
     (type_memory_bytes cenv dt <> 0 ==>
      (?p. def = Var p /\ ptr_covers Gf tf p t (type_memory_bytes cenv dt)) /\
      !w. eval_operand def t = SOME w ==>
          w2n w + type_memory_bytes cenv dt <= t.vs_alloca_next)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ptr_mem_ok cx dt dv def G tn s /\ _`
       (drule_all_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac))) >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ?w tv. _`
       (drule_all_then (qx_choose_then `mw` (qx_choose_then `mtv` strip_assume_tac))) >>
     conj_tac
     >- (simp[NoAsms,bodyPtrDefsTheory.ptr_mem_ok_def] >> rpt gen_tac >>
         qpat_assum `evaluate_type (get_tenv cx) dt = SOME mtv` (fn th => simp[NoAsms,th]) >>
         qpat_assum `eval_operand def t = SOME mw` (fn th => simp[NoAsms,th]) >>
         disch_then (CONJUNCTS_THEN (SUBST1_TAC o SYM)) >>
         qpat_assum `ptr_mem_ok cx dt dv def G tn s`
           (qspecl_then [`mtv`,`mw`] mp_tac o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_mem_ok_def]) >>
         (impl_tac >- simp[]) >> strip_tac >> conj_tac
         >- (gen_tac >> disch_tac >>
             irule bodyPtrBytestringBuiltinsWindowGhostTheory.robust_val_in_memory_window_transport >>
             conj_tac >- first_assum ACCEPT_TAC >>
             qexistsl [`tn.t_mem`,`tf.t_mem`,`type_memory_size mtv`,`s.vs_memory`,`t.vs_memory`] >>
             rpt conj_tac >>
             (first_assum ACCEPT_TAC ORELSE irule exprSimPropsTheory.val_footprint_le >>
                                            first_assum ACCEPT_TAC)) >>
         disch_tac >> qpat_assum `val_footprint mtv dv <> 0 ==> _`
           (drule_then strip_assume_tac) >>
         rename1 `def = Var dp` >>
         `not_fresh_at se dp` by
           (qpat_assum `safe_operand se def`
              (mp_tac o cj 1 o PURE_REWRITE_RULE [exprSafeOperandTheory.safe_operand_def]) >>
            disch_then (drule_then ACCEPT_TAC)) >>
         qexistsl [`dp`,`b`,`sz`] >> simp[NoAsms] >> rpt conj_tac >>
         (first_assum ACCEPT_TAC ORELSE
          qpat_assum `!x. not_fresh_at se x ==> FLOOKUP Gf x = _ /\ _`
            (drule_then (fn th => simp[th])))) >>
     disch_tac >>
     qpat_assum `type_memory_bytes cenv dt <> 0 ==> _`
       (drule_then strip_assume_tac) >> conj_tac
     >- (rename1 `def = Var dp` >>
         `not_fresh_at se dp` by
           (qpat_assum `safe_operand se def`
              (mp_tac o cj 1 o PURE_REWRITE_RULE [exprSafeOperandTheory.safe_operand_def]) >>
            disch_then (drule_then ACCEPT_TAC)) >>
         qexists `dp` >> conj_tac >- first_assum ACCEPT_TAC >>
         qpat_assum `ptr_covers G tn dp s (type_memory_bytes cenv dt)`
           (CONJUNCTS_THEN2 assume_tac
             (qx_choose_then `pw` (qx_choose_then `pb` (qx_choose_then `psz` strip_assume_tac))) o
            PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >>
         `lookup_var dp t = SOME pw` by simp[] >>
         qpat_assum `!x. not_fresh_at se x ==> FLOOKUP Gf x = _ /\ _`
           (drule_then strip_assume_tac) >>
         pure_rewrite_tac[bodyPtrDefsTheory.ptr_covers_def] >>
         conj_tac >- asm_rewrite_tac[] >>
         qexistsl [`pw`,`pb`,`psz`] >> asm_rewrite_tac[]) >>
     qpat_assum `eval_operand def t = SOME mw` (fn th => simp[NoAsms,th]) >>
     `w2n mw + type_memory_bytes cenv dt <= s.vs_alloca_next`
       by first_assum (drule_then ACCEPT_TAC) >> decide_tac) >>
  `FLOOKUP t.vs_allocas se.cs_next_id = SOME (w2n rw,n)` by
    first_assum (drule_then ACCEPT_TAC) >>
  `lookup_var r t = SOME rw` by
    (`not_fresh_at st r` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `sd` >> simp[]) >>
     qpat_assum `!z. not_fresh_at st z ==> FLOOKUP Gf z = _ /\ _`
       (drule_then (drule_then ACCEPT_TAC o cj 3))) >>
  `se.cs_next_id < sp.cs_next_id` by decide_tac >>
  `!name b k. local_region cenv ee.scopes t name b k ==>
       local_region cenv ee.scopes s name b k` by
    (rpt gen_tac >> strip_tac >> irule exprSimPropsTheory.local_region_frame >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes s` (irule_at Any) >>
     qpat_assum `local_region cenv ee.scopes t name b k` (irule_at Any) >>
     qexists `se` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region cenv ee.scopes s name b k ==>
       regions_disjoint (w2n rw) cap b k` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b k. local_region cenv ee.scopes s name b k ==> regions_disjoint (w2n rw) n b k`
       (drule_then mp_tac) >>
     simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       regions_disjoint (w2n rw) cap b k` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_inv t`
       (mp_tac o cj 1 o PURE_REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     simp[NoAsms,venomMemDefsTheory.allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`se.cs_next_id`,`aid`,`w2n rw`,`n`,`b`,`k`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv v imm_off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc imm_off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     regions_disjoint (w2n rw) cap imm_off (type_memory_size tv)` by
    (disch_tac >> rpt gen_tac >> strip_tac >>
     `stmt_state_rel HH ctx func cenv cx ee t` by first_assum (drule_then ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel HH ctx func cenv cx ee t`
       (mp_tac o MATCH_MP bodyFullIntCallReturnFrameTheory.return_stmt_immutable_sep) >>
     simp[NoAsms,exprLoweringPropsTheory.immutable_alloca_sep_def] >>
     disch_then (mp_tac o CONJUNCT2) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (drule_all_then strip_assume_tac) >>
     `se.cs_next_id IN se.cs_next_id INSERT ids` by simp[] >>
     qpat_assum `!i. _ ==> ?inst. MEM inst _ /\ _`
       (drule_then (qx_choose_then `out_inst` strip_assume_tac)) >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz`
       (qspecl_then [`out_inst`,`w2n rw`,`n`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!dv w tv. dopt = SOME dv /\ ~is_word_type dt /\
       eval_operand def t = SOME w /\ evaluate_type (get_tenv cx) dt = SOME tv ==>
       regions_disjoint (w2n rw) cap (w2n w) (val_footprint tv dv)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ptr_mem_ok cx dt dv def G tn s /\ _ /\ ?w aid tv. _`
       (drule_all_then (qx_choose_then `dw` (qx_choose_then `aid` (qx_choose_then `dtv` strip_assume_tac))) o cj 3) >>
     `eval_operand def t = SOME dw` by first_assum (drule_then ACCEPT_TAC) >>
     `dw = w /\ dtv = tv` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `dw = w` SUBST_ALL_TAC >> qpat_x_assum `dtv = tv` SUBST_ALL_TAC >>
     `FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv)` by
       (qpat_assum `wb_frame cenv ee ee se s t`
          (mp_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
        disch_then (drule_then ACCEPT_TAC)) >>
     `val_footprint tv dv <= type_memory_size tv` by
       (irule exprSimPropsTheory.val_footprint_le >> first_assum ACCEPT_TAC) >>
     qpat_assum `!aid b k. aid < se.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==> _`
       (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  (* Package the calldata facts at the same encoder endpoint. *)
  `eval_operand off t = SOME (n2w (w2n rw + 28)) /\
   eval_operand len t = SOME (n2w (4 + LENGTH bytes)) /\
   eval_operand ba.buf_operand t = SOME rw` by
    simp[venomStateTheory.eval_operand_def] >>
  `w2n rw + n <= t.vs_alloca_next` by
    (irule allocaSiteResourceTheory.alloca_site_registered_below >>
     conj_tac >- first_assum ACCEPT_TAC >> qexists `se.cs_next_id` >> simp[]) >>
  `w2n (n2w (w2n rw + 28) : bytes32) = w2n rw + 28 /\
   w2n (n2w (4 + LENGTH bytes) : bytes32) = 4 + LENGTH bytes` by simp[] >>
  `eval_operand gas t = SOME gw` by simp[] >>
  `extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas ba.buf_operand off len cap target value_opt (bs ++ bytes)
      hasdef def dt dopt ee t` by
    (pure_rewrite_tac[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qexists `HH` >> first_assum ACCEPT_TAC)
     >- (qx_gen_tac `H` >> disch_tac >> conj_tac
         >- (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t`
               (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
         qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
           (qspec_then `H` (irule o cj 2)) >> first_assum ACCEPT_TAC)
     >- (`not_fresh_at sp r` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists `sd` >> simp[] >> decide_tac) >>
         simp[] >> simp[exprSafeOperandTheory.safe_operand_def])
     >- (qpat_assum `?aw. eval_operand addr s = SOME aw /\ _`
           (qx_choose_then `aw` strip_assume_tac) >>
         qexists `aw` >> simp[] >> first_assum (drule_then ACCEPT_TAC))
     >- (qpat_assum `?vw. eval_operand value s = SOME vw /\ _`
           (qx_choose_then `vw` strip_assume_tac) >>
         qexists `vw` >> simp[] >> first_assum (drule_then ACCEPT_TAC))
     >- simp[]
     >- (qexistsl [`n2w (w2n rw + 28)`,`n2w (4 + LENGTH bytes)`] >>
         simp[] >>
         CONV_TAC (LAND_CONV (RATOR_CONV (RAND_CONV (REWR_CONV arithmeticTheory.ADD_COMM)))) >>
         first_assum ACCEPT_TAC) >>
     qexists `rw` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- decide_tac
     >- (qexistsl [`se.cs_next_id`,`n`] >> simp[])
     >- (rpt strip_tac >> `local_region cenv ee.scopes s name b sz`
           by first_assum (drule_then ACCEPT_TAC) >> first_assum (drule_then ACCEPT_TAC))
     >- (rpt strip_tac >> `local_region cenv ee.scopes s name b sz` by simp[] >>
         first_assum (drule_then ACCEPT_TAC)) >>
     rpt strip_tac >> `aid < se.cs_next_id` by decide_tac >>
     first_assum (drule_all_then ACCEPT_TAC)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
       ghost_inv_at (DF H) lo d cenv cx ee Gf tf t` by
    (qx_gen_tac `H` >> disch_tac >>
     qpat_assum `!H. _ ==> wb_frame cenv ee ee se q t /\ _`
       (qspec_then `H` (irule o cj 3)) >> first_assum ACCEPT_TAC) >>
  `EVERY (\p. op_taint tf p = {}) [addr;value;gas;ba.buf_operand;off;len;def]` by
    (qpat_assum `!op. safe_operand se op ==> safe_operand sp op /\ _`
       (fn th => map_every (fn p => qspec_then p (mp_tac o cj 2) th)
                           [`addr`,`value`,`gas`]) >>
     simp[] >> rpt conj_tac >>
     first_assum (ACCEPT_TAC o cj 1 o PURE_REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def])) >>
  `ptr_covers Gf tf r t cap` by
    (qpat_assum `ptr_covers Gf tf r t n`
       (mp_then Any irule reasonCopySourcePtrTheory.ptr_covers_mono) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `EVERY (\p. op_taint tf p = {}) _`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  qexistsl [`bs ++ bytes`,`t`,`Gf`,`tf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (first_assum (ACCEPT_TAC o REWRITE_RULE [optionTheory.OPTION_BIND_EQUALS_OPTION]))
  >- (qx_gen_tac `ao` >> qx_gen_tac `az` >> strip_tac >>
      `w2n (ao:bytes32) = w2n rw + 28` by
        (qpat_x_assum `eval_operand off t = SOME ao` mp_tac >>
         simp[IgnAsm `eval_operand off t = SOME ao`] >>
         disch_then (SUBST1_TAC o SYM) >> simp[]) >>
      `w2n (az:bytes32) = 4 + LENGTH bytes` by
        (qpat_x_assum `eval_operand len t = SOME az` mp_tac >>
         simp[IgnAsm `eval_operand len t = SOME az`] >>
         disch_then (SUBST1_TAC o SYM) >> simp[]) >>
      conj_tac
      >- (strip_tac >> conj_tac
          >- (qexists `x` >> conj_tac >- first_assum ACCEPT_TAC >>
              qpat_assum `w2n az = 4 + LENGTH bytes` SUBST1_TAC >>
              first_assum ACCEPT_TAC) >>
          decide_tac) >>
      qx_gen_tac `j` >> disch_tac >>
      qpat_assum `!i. w2n rw + 28 <= i /\ _ ==> i NOTIN tf.t_mem`
        (qspec_then `j` irule) >> decide_tac)
  >- (disch_tac >> qexists `r` >> simp[])
QED

Finalise extcall_request_packing_ready

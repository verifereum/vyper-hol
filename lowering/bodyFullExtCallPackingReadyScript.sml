Theory bodyFullExtCallPackingReady
Ancestors
  bodyFullExtCallPacking bodyFullExtCallEncodeTail bodyFullExtCallSelectorReady
  bodyFullExtCallDirectStart bodyFullExtCallDirectLayout
  bodyFullExtCallDirectEncode bodyFullExtCallDirectRow bodyFullExtCallDirectState
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  localPtrsProps abiEncodeValuesMetadata abiDecodeRanges abiDecoderMembers
  bodyFullIntCallReturnFrame bodyPtrBytestringBuiltinsWindowGhost
  exprLoweringProps exprSimAggregates exprSimWordArgs wordArgsPtr exprSimProps exprSimExtCallCase
  emitHelperProps compileEnv fragGasOriginPtrLoop fragGasOriginPtr list pair words
Libs horizonTypeLib

Theorem extcall_packing_observed_domain:
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
    ?e sv v raw si sm ss vv tv param_tv copy.
      e = EL i xs /\ sv = EL i vals /\ v = EL i argvs /\
      arg_type_fits (lowered_value_type cenv e) (EL i arg_types) /\
      evaluate_type (get_tenv cx) (EL i arg_types) = SOME param_tv /\
      value_has_type param_tv v /\
      (~is_word_type (lowered_value_type cenv e) ==> ~is_word_type (expr_type e)) /\
      evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
      type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
      type_memory_size tv < 2**64 /\ value_has_type tv v /\
      compile_expr cenv (expr_type e) e si = (vv,sm) /\
      compile_snapshot_vv cenv copy
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
      vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv s /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==> vv_storage_live H cx sv ee s) /\
      ((case sv of StackValue tag op0 => ~is_word_type (lowered_value_type cenv e)
        | LocatedValue tag p => p.ptr_location = LocMemory) ==>
        ptr_buf_ok cenv e (vv_operand sv) G s)) /\
  abi = abi_size_bound cenv.ce_struct_fields (TupleT tys) /\
  abi = vyper_abi_size_bound (get_tenv cx) (TupleT tys) /\
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!ty. MEM ty tys ==> abi_enc_plan (get_tenv cx) ty
    (type_to_abi_enc_info cenv.ce_struct_fields cenv ty)) /\
  mid = w2n (calldata_method_id
    (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types))) /\
  compile_alloc_buffer ((if abi > cap then abi else cap) + 32) se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (n2w mid)] sb = ((),sm) /\
  (if vals = [] then comp_return (Lit 4w) else
     comp_bind (emit_op ADD [ba.buf_operand;Lit 32w]) (\dst.
      comp_bind (compile_abi_encode_values_to_buf cenv dst (ZIP (vals,tys))) (\alen.
      emit_op ADD [alen;Lit 4w]))) sm = (len,sf) /\
  emit_op ADD [ba.buf_operand;Lit 28w] sf = (off,sp) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\
  fn_has_code sm sf func /\ fn_has_code sf sp func /\
  fn_inst_ids_distinct func /\
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
    (IS_SOME dopt /\ ~is_word_type dt ==>
      ?w aid tv. eval_operand def t = SOME w /\
        evaluate_type (get_tenv cx) dt = SOME tv /\
        FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
        aid < sp.cs_next_id) /\
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
    qpat_x_assum `(if vals = [] then _ else _) sm = _` (assume_tac o REWRITE_RULE [th])) >>
  qabbrev_tac `bs = function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types)` >>
  qabbrev_tac `n = (if abi > cap then abi else cap) + 32` >>
  qabbrev_tac `rows = ZIP (vals,tys)` >>
  `LENGTH tys = LENGTH xs /\ LENGTH rows = LENGTH xs` by
    simp[Abbr `rows`, LENGTH_ZIP] >>
  `32 <= n /\ abi <= n-32 /\ cap <= n` by
    (simp[Abbr `n`] >> IF_CASES_TAC >> decide_tac) >>
  `LENGTH bs = 4` by simp[Abbr `bs`, selectorCompilerPropsTheory.function_selector_length] >>
  `emit_void MSTORE [ba.buf_operand; Lit (calldata_method_id bs)] sb = ((),sm)` by
    (qpat_assum `mid = _` (fn hm =>
       qpat_assum `emit_void MSTORE _ sb = _` (mp_tac o REWRITE_RULE [hm])) >>
     simp[NoAsms, Abbr `bs`]) >>
  qpat_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `HH` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `HH` (drule_then strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee s` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  `local_ptrs_reserved cenv se` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists `sa` >> simp[] >> metis_tac[]) >>
  `storage_trace_domain cx st0 ee.storage_trace` by
    metis_tac[extcall_packing_observed_domain] >>
  Q.SUBGOAL_THEN `?avs ats bytes.
    vyper_to_abi_list (get_tenv cx) tys argvs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) tys /\
    bytes = enc (Tuple ats) (ListV avs) /\
    build_ext_calldata (get_tenv cx) fname arg_types argvs =
      SOME (function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types) ++ bytes) /\
    LENGTH bytes <= abi_size_bound cenv.ce_struct_fields (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size cenv.ce_struct_fields (SND row) =
      abi_member_head_size at) (ZIP (vals,tys)) ats`
    (qx_choosel_then [`avs`,`ats`,`bytes`] strip_assume_tac)
  >- (irule extcall_direct_args_layout >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
      gen_tac >> disch_tac >>
      `i < LENGTH xs` by decide_tac >>
      qpat_assum `!i. i < LENGTH xs ==> ?e sv v raw si sm ss vv tv param_tv copy. _`
        (qspec_then `i` (drule_then
          (qx_choosel_then [`e`,`sv`,`v`,`raw`,`si`,`row_mid`,`ss`,`vv`,`tv`,`param_tv`,`copy`]
            (MAP_EVERY assume_tac o CONJUNCTS)))) >>
      qexistsl [`tv`,`param_tv`] >> asm_simp_tac bool_ss [EL_MAP] >>
      qpat_assum `e = EL i xs` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      qpat_assum `v = EL i argvs` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `hl = head_lengths ats 0` >>
  `hl = head_lengths ats 0` by simp[NoAsms, Abbr `hl`] >>
  `LENGTH bytes <= abi` by
    (qpat_assum `abi = abi_size_bound _ _` (fn th => PURE_REWRITE_TAC [th]) >>
     first_assum ACCEPT_TAC) >>
  `LENGTH ats = LENGTH xs /\ LENGTH avs = LENGTH xs` by
    (qpat_assum `ats = vyper_to_abi_types _ tys`
      (assume_tac o SIMP_RULE bool_ss [abiDecoderMembersTheory.vyper_to_abi_types_MAP,LENGTH_MAP]
        o AP_TERM ``LENGTH:abi_type list -> num``) >>
     qpat_assum `LIST_REL abi_encoder_layout_valid ats avs`
       (assume_tac o MATCH_MP LIST_REL_LENGTH) >>
     conj_tac >> decide_tac) >>
  `LIST_REL (\row at. abi_embedded_static_size cenv.ce_struct_fields (SND row) =
      abi_member_head_size at) rows ats` by
    (simp_tac bool_ss [Abbr `rows`] >> first_assum ACCEPT_TAC) >>
  `?dst enc_start alen enc_end.
    emit_op ADD [ba.buf_operand;Lit 32w] sm = (dst,enc_start) /\
    compile_abi_encode_values_to_buf cenv dst rows enc_start = (alen,enc_end) /\
    emit_op ADD [alen;Lit 4w] enc_end = (len,sf) /\
    ci_mono sm enc_start /\ ci_mono enc_start enc_end /\ ci_mono enc_end sf /\
    fn_has_code sm enc_start func /\ fn_has_code enc_start enc_end func /\ fn_has_code enc_end sf func` by
    (irule extcall_direct_request_trace >> simp[Abbr `rows`]) >>
  `ci_mono se sb /\ ci_mono sb sm /\ ci_mono sf sp` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono se enc_start /\ ci_mono enc_end sp /\ ci_mono se sp` by metis_tac[ci_mono_trans] >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `capacity` |-> `n`, `selector` |-> `bs`,
    `payload` |-> `dst`, `st` |-> `enc_start`] extcall_direct_request_start) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then (qx_choosel_then [`r`,`p`,`rw`,`u`,`Gu`,`tu`,`inst`] strip_assume_tac) >>
  qpat_x_assum `dst = Var p` SUBST_ALL_TAC >>
  `extcall_direct_state ctx func cenv cx st0 ee DF lo d se s G tn
    se.cs_next_id (w2n rw) n r p bs enc_start u Gu tu` by
    (qpat_assum `ci_mono se enc_start` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
     simp_tac bool_ss [extcall_direct_state_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     simp[venomStateTheory.eval_operand_def]) >>
  mp_tac (Q.INST [`ce` |-> `cenv`,`disp` |-> `d`, `shared` |-> `se.cs_next_id`,
    `pbase` |-> `w2n (rw:bytes32)`, `capacity` |-> `n`, `root` |-> `r`, `payload_var` |-> `p`,
    `selector` |-> `bs`, `st` |-> `enc_start`, `en` |-> `enc_end`]
    extcall_direct_values_execute) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qx_gen_tac `ci` >> qx_gen_tac `cursor_var` >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      map_every qx_gen_tac [`i`,`a`,`c`,`vvstate`,`Gv`,`tvstate`,`cursor`,`slot`] >>
      disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
      `i < LENGTH xs /\ i < LENGTH vals /\ i < LENGTH tys /\ i < LENGTH argvs /\
       i < LENGTH ats` by decide_tac >>
      qpat_assum `!i. i < LENGTH xs ==> ?e sv v raw si sm ss vv tv param_tv copy. _`
        (qspec_then `i` (drule_then
          (qx_choosel_then [`e`,`sv`,`v`,`raw`,`si`,`smi`,`ss`,`vv`,`tv`,`ptv`,`copy`]
            (MAP_EVERY assume_tac o CONJUNCTS)))) >>
      qabbrev_tac `at = EL i ats` >> qabbrev_tac `av = EL i avs` >>
      qabbrev_tac `h = SUM (MAP (abi_embedded_static_size cenv.ce_struct_fields o SND) (TAKE i rows))` >>
      qabbrev_tac `ofst = hl + LENGTH (FLAT (abi_tuple_tails (TAKE i ats) (TAKE i avs)))` >>
      `EL i rows = (sv,lowered_value_type cenv e) /\
       at = vyper_to_abi_type (get_tenv cx) (lowered_value_type cenv e)` by
        simp[Abbr `rows`, Abbr `at`, abiDecoderMembersTheory.vyper_to_abi_types_MAP, EL_ZIP, EL_MAP] >>
      `EL i tys = lowered_value_type cenv e` by
        (qpat_assum `tys = MAP _ xs` (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `e = EL i xs` (fn th => PURE_REWRITE_TAC [th]) >>
         asm_simp_tac bool_ss [EL_MAP]) >>
      `vyper_to_abi (get_tenv cx) (lowered_value_type cenv e) v = SOME av` by
        (qpat_assum `vyper_to_abi_list _ tys argvs = SOME avs`
          (assume_tac o cj 3 o MATCH_MP vyperABIRoundtripTheory.vyper_to_abi_list_EL) >>
         simp_tac bool_ss [Abbr `av`] >>
         qpat_assum `EL i tys = lowered_value_type cenv e` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
         qpat_assum `v = EL i argvs` (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `!j. j < LENGTH argvs ==> vyper_to_abi _ _ _ = _`
           (qspec_then `i` (drule_then ACCEPT_TAC))) >>
      `abi_enc_plan (get_tenv cx) (lowered_value_type cenv e)
         (type_to_abi_enc_info cenv.ce_struct_fields cenv (lowered_value_type cenv e))` by
        (qpat_assum `!ty. MEM ty tys ==> _` irule >>
         simp_tac bool_ss [MEM_EL] >> qexists_tac `i` >>
         conj_tac >- first_assum ACCEPT_TAC >>
         sym_tac >> first_assum ACCEPT_TAC) >>
      `h = LENGTH (FLAT (abi_tuple_heads hl 0 (TAKE i ats) (TAKE i avs))) /\
       hl <= ofst /\ ofst <= LENGTH bytes /\ h + abi_member_head_size at <= hl /\
       (is_dynamic at ==> ofst + LENGTH (enc at av) <= LENGTH bytes) /\
       (~is_dynamic at ==> LENGTH (enc at av) = abi_member_head_size at) /\
       abi_encoder_layout_valid at av /\ LIST_REL abi_encoder_layout_valid (TAKE i ats) (TAKE i avs)` by
        (irule (INST_TYPE [alpha |-> ``:vyper_value``, beta |-> ``:string``, gamma |-> ``:num``]
           abi_encode_values_index_bounds) >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         TRY (simp_tac bool_ss [Abbr `at`,Abbr `av`,Abbr `ofst`] >> NO_TAC) >>
         TRY (qpat_assum `bytes = enc _ _` (fn th => simp[NoAsms,th]) >> NO_TAC) >>
         qexistsl [`rows`,`cenv.ce_struct_fields`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[NoAsms, Abbr `h`]) >>
      `LENGTH ats = LENGTH avs /\ ofst <= n-32 /\
       (is_dynamic at ==> ofst + LENGTH (enc at av) <= n-32)` by
        (rpt conj_tac >> TRY decide_tac >> disch_tac >>
         qpat_assum `is_dynamic at ==> ofst + LENGTH (enc at av) <= LENGTH bytes`
           (drule_then assume_tac) >> decide_tac) >>
      `!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\ vv_storage_live H cx sv ee s` by metis_tac[] >>
      `compile_abi_encode_value_rows cenv (Var p) cursor h [(sv,lowered_value_type cenv e)] a = ((),c)` by
        (qpat_assum `EL i rows = _` (fn th => rewrite_tac [GSYM th]) >>
         simp_tac bool_ss [Abbr `h`] >> first_assum ACCEPT_TAC) >>
      mp_tac (Q.INST [`ce` |-> `cenv`,`ty` |-> `lowered_value_type cenv e`,
        `pbase` |-> `w2n (rw:bytes32)`, `capacity` |-> `n`,`root` |-> `r`,`dst` |-> `p`,
        `selector` |-> `bs`, `saved` |-> `sv`,`sm` |-> `smi`,`loc` |-> `enc_start.cs_next_id`,
        `su` |-> `a`,`en` |-> `c`, `u` |-> `vvstate`, `Gu` |-> `Gv`, `tu` |-> `tvstate`,
        `off` |-> `ofst`, `cursor_inst` |-> `ci`] extcall_direct_row) >>
      impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY REFL_TAC >> simp[Abbr `at`,Abbr `av`]) >>
      disch_then ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac) >>
  `extcall_direct_state ctx func cenv cx st0 ee DF lo d se s G tn
    se.cs_next_id (w2n rw) n r p bs enc_end q Gq tq` by first_assum ACCEPT_TAC >>
  drule_all extcall_direct_state_resources >> strip_tac >>
  qpat_assum `extcall_direct_state ctx func cenv cx st0 ee DF lo d se s G tn
    se.cs_next_id (w2n rw) n r p bs enc_end q Gq tq`
    (strip_assume_tac o REWRITE_RULE [extcall_direct_state_def]) >>
  `w2n rw + n <= q.vs_alloca_next` by
    metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
  `!j. w2n rw+28 <= j /\ j < w2n rw+32+LENGTH bytes ==> j NOTIN tq.t_mem` by
    (gen_tac >> disch_tac >> Cases_on `j < w2n rw+32`
     >- (qpat_assum `!i. w2n rw+28 <= i /\ i < w2n rw+32 ==> i NOTIN tq.t_mem` irule >>
         decide_tac) >>
     qpat_assum `!i. w2n rw+32 <= i /\ i < w2n rw+32+LENGTH bytes ==> i NOTIN tq.t_mem` irule >>
     decide_tac) >>
  `emit_op ADD [Var r;Lit 28w] sf = (off,sp)` by
    (qpat_assum `ba.buf_operand = Var r` (fn th =>
       qpat_assum `emit_op ADD [ba.buf_operand;Lit 28w] sf = (off,sp)`
         (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  `lookup_var r q = SOME (n2w (w2n rw))` by
    (qpat_assum `eval_operand (Var r) q = _`
       (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.eval_operand_def])) >>
  `read_memory (w2n rw+32) (LENGTH bytes) q = bytes` by
    (simp_tac bool_ss [memoryReadPropsTheory.read_memory_eq_mem_bytes_at] >>
     first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee q /\ _`
       (qspec_then `HH` (drule_then (mp_tac o CONJUNCT1))) >>
     MATCH_ACCEPT_TAC
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
  mp_tac (Q.INST [`a` |-> `enc_end`,`b` |-> `sf`,`c` |-> `sp`,
    `p` |-> `w2n (rw:bytes32)`,`root` |-> `r`,`bs` |-> `bytes`,`selector` |-> `bs`,
    `fn` |-> `func`,`capacity` |-> `n`,`s` |-> `q`,`G` |-> `Gq`,`tn` |-> `tq`]
    extcall_encoded_request_suffix) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> TRY decide_tac >>
      simp[venomStateTheory.eval_operand_def, memoryReadPropsTheory.read_memory_eq_mem_bytes_at]) >>
  disch_then (qspecl_then [`explicit`,`PG`] (qx_choosel_then [`x`,`y`,`t`,`Gf`,`tf`] strip_assume_tac)) >>
  mp_tac (Q.INST [`ce` |-> `cenv`,`shared` |-> `se.cs_next_id`,
    `pbase` |-> `w2n (rw:bytes32)`,`capacity` |-> `n`,`root` |-> `r`,`dst` |-> `p`,
    `selector` |-> `bs`,`a` |-> `enc_end`,`c` |-> `sp`,`u` |-> `q`,`v` |-> `t`,
    `Gu` |-> `Gq`,`tu` |-> `tq`,`Gv` |-> `Gf`,`tv` |-> `tf`]
    extcall_direct_state_arith) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
  disch_then (strip_assume_tac o REWRITE_RULE [extcall_direct_state_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,Gf,tf)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee t` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> ghost_inv_at (DF H) lo d cenv cx ee Gf tf t` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o cj 3))) >>
  `stmt_state_rel HH ctx func cenv cx ee t` by metis_tac[] >>
  `local_ptrs_rel func cenv ee.scopes s /\ alloca_inv s` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `local_ptrs_rel func cenv ee.scopes t /\ alloca_inv t` by
    metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
  `w2n rw + n <= t.vs_alloca_next` by
    metis_tac[allocaSiteResourceTheory.alloca_site_registered_below] >>
  `t.vs_alloca_next < dimword (:256)` by
    metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  qpat_assum `ci_mono se sp` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
  `s0.vs_alloca_next <= t.vs_alloca_next /\
    sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id` by decide_tac >>
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
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
       mem_bytes_at b k t.vs_memory = mem_bytes_at b k s.vs_memory /\
       (!j. b <= j /\ j < b+k /\ j IN tf.t_mem ==> j IN tn.t_mem)` by
    (qpat_assum `wb_frame cenv ee ee se s t`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_assum `ghost_kept_at lo cenv ee se G tn s Gf tf`
       (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]) >>
     rpt gen_tac >> strip_tac >>
     Cases_on `?nm. local_region cenv ee.scopes s nm b k`
     >- (qpat_x_assum `?nm. local_region cenv ee.scopes s nm b k`
           (qx_choose_then `row_local` assume_tac) >>
         conj_tac
         >- (qpat_assum `locals_kept cenv ee ee s t` mp_tac >>
             simp[NoAsms, loweringPostsTheory.locals_kept_def] >>
             disch_then strip_assume_tac >>
             qpat_assum `!name b sz. local_region cenv ee.scopes s name b sz ==> mem_bytes_at b sz t.vs_memory = _`
               (qspecl_then [`row_local`,`b`,`k`] mp_tac) >> simp[]) >>
         rpt strip_tac >>
         qpat_assum `!name b sz i. local_region cenv ee.scopes s name b sz /\ _ ==> i IN tn.t_mem`
           (qspecl_then [`row_local`,`b`,`k`,`j`] mp_tac) >> simp[]) >>
     `!nm a sz. local_region cenv ee.scopes s nm a sz ==> b+k <= a \/ a+sz <= b` by
       (rpt gen_tac >>
        simp[NoAsms, loweringStateRelDefsTheory.local_region_def] >>
        disch_then (qx_choose_then `entry` (qx_choose_then `lp` (qx_choose_then `lw` strip_assume_tac))) >>
        `local_backed func lp s a sz` by
          (qpat_assum `local_ptrs_rel func cenv ee.scopes s`
             (drule_all_then strip_assume_tac o cj 1 o
              PURE_REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_rel_def]) >>
           qpat_assum `a = w2n lw` SUBST1_TAC >>
           qpat_x_assum `lookup_var lp s = SOME lw` mp_tac >>
           qpat_assum `lookup_var lp s = SOME w` (fn th => simp[NoAsms,th]) >>
           disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
        qpat_assum `local_backed func lp s a sz` mp_tac >>
        simp[NoAsms,loweringStateRelDefsTheory.local_backed_def] >>
        disch_then (DISJ_CASES_THEN2 (qx_choose_then `local_inst` strip_assume_tac) assume_tac)
        >- (`local_inst.inst_id <> aid` by
              (strip_tac >>
               `a = b /\ sz = k` by
                 (qpat_assum `FLOOKUP s.vs_allocas local_inst.inst_id = SOME (a,sz)` mp_tac >>
                  qpat_assum `local_inst.inst_id = aid` (fn th => simp[NoAsms,th]) >>
                  qpat_assum `FLOOKUP s.vs_allocas aid = SOME (b,k)` (fn th => simp[NoAsms,th]) >>
                  metis_tac[]) >>
               qpat_assum `~(?nm. local_region cenv ee.scopes s nm b k)` mp_tac >>
               simp[NoAsms,loweringStateRelDefsTheory.local_region_def] >>
               qexistsl [`nm`,`entry`,`lp`,`lw`] >> simp[]) >>
            qpat_assum `alloca_inv s`
              (mp_tac o cj 1 o REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
            simp[NoAsms, venomMemDefsTheory.allocas_non_overlapping_def] >>
            disch_then (qspecl_then [`aid`,`local_inst.inst_id`,`b`,`k`,`a`,`sz`] mp_tac) >> simp[]) >>
        first_x_assum (qspecl_then [`aid`,`b`,`k`] mp_tac) >>
        simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     conj_tac
     >- (qpat_assum `!aid off sz. FLOOKUP s.vs_allocas aid = SOME _ /\ _ ==> mem_bytes_at off sz t.vs_memory = _`
           (qspecl_then [`aid`,`b`,`k`] MATCH_MP_TAC) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
     rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_assum `!aid off sz i. FLOOKUP s.vs_allocas aid = SOME _ /\ _ ==> i IN tn.t_mem`
       (qspecl_then [`aid`,`b`,`k`,`j`] MATCH_MP_TAC) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `EVERY (safe_operand se) [addr;value;gas;def]`
    (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  qpat_assum `EVERY (\op. op_taint tn op = {}) [addr;value;gas;def]`
    (strip_assume_tac o BETA_RULE o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  map_every (fn operand => qpat_assum `!op. safe_operand se op ==> _`
     (qspec_then operand (fn th => first_assum (strip_assume_tac o MP th))))
    [`addr`,`value`,`gas`,`def`] >>
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
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     `eval_operand def t = SOME w` by
       (qpat_assum `!w. eval_operand def s = SOME w ==> eval_operand def t = SOME w`
          (drule_then ACCEPT_TAC)) >>
     qexistsl [`w`,`tv`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
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
  `lookup_var r t = SOME rw /\ eval_operand ba.buf_operand t = SOME rw` by
    simp[venomStateTheory.eval_operand_def] >>
  `!name b k. local_region cenv ee.scopes t name b k ==>
       local_region cenv ee.scopes s name b k` by
    (rpt gen_tac >> strip_tac >> irule exprSimPropsTheory.local_region_frame >>
     qpat_assum `local_ptrs_rel func cenv ee.scopes s` (irule_at Any) >>
     qpat_assum `local_region cenv ee.scopes t name b k` (irule_at Any) >>
     qexists `se` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name b k. local_region cenv ee.scopes s name b k ==>
       regions_disjoint (w2n rw) cap b k` by
    (rpt gen_tac >> disch_tac >>
     `local_region cenv ee.scopes t name b k` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qpat_assum `local_region cenv ee.scopes s name b k` (irule_at Any) >>
        qexists `se` >> simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     mp_tac (Q.SPECL
       [`func`,`cenv`,`ee.scopes`,`t`,`inst`,`r`,`w2n (rw:bytes32)`,`n`,`name`,`b`,`k`]
       local_ptrs_rel_alloca_disjoint) >>
     impl_tac >- asm_rewrite_tac[] >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid b k. aid < se.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,k) ==>
       regions_disjoint (w2n rw) cap b k` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `alloca_inv t`
       (mp_tac o cj 1 o PURE_REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
     simp[NoAsms,venomMemDefsTheory.allocas_non_overlapping_def] >>
     disch_then (qspecl_then [`se.cs_next_id`,`aid`,`w2n rw`,`n`,`b`,`k`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !src name tv v imm_off.
     (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
     FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc imm_off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
     regions_disjoint (w2n rw) cap imm_off (type_memory_size tv)` by
    (disch_tac >> rpt gen_tac >>
     disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
     `stmt_state_rel HH ctx func cenv cx ee t` by first_assum (drule_then ACCEPT_TAC) >>
     mp_tac (Q.INST [`inst` |-> `inst`, `b` |-> `w2n (rw:bytes32)`, `sz` |-> `n`,
         `es` |-> `ee`, `H` |-> `HH`]
        (horizonTypeLib.at_horizon_named "H" aggregate_alloca_immutable_sep_source)) >>
     impl_tac >- simp[] >>
     disch_then (drule_then (qspecl_then [`src`,`name`,`tv`,`v`,`imm_off`] mp_tac)) >>
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
  `w2n rw + 28 < dimword (:256) /\ 4 + LENGTH bytes < dimword (:256)` by decide_tac >>
  `w2n (n2w (w2n rw + 28) : bytes32) = w2n rw + 28 /\
   w2n (n2w (4 + LENGTH bytes) : bytes32) = 4 + LENGTH bytes` by
    (simp_tac bool_ss [wordsTheory.w2n_n2w] >>
     conj_tac >> irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
  `eval_operand gas t = SOME gw` by
    (qpat_assum `!w. eval_operand gas s = SOME w ==> eval_operand gas t = SOME w`
       (drule_then ACCEPT_TAC)) >>
  `extcall_request_ready st0 ctx func cenv cx rt es sa s0 sp stat
      addr value gas ba.buf_operand off len cap target value_opt (bs ++ bytes)
      hasdef def dt dopt ee t` by
    (pure_rewrite_tac[exprSimExtCallCaseTheory.extcall_request_ready_def] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (qx_gen_tac `H` >> disch_tac >> conj_tac
         >- (qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t`
               (qspec_then `H` irule) >> first_assum ACCEPT_TAC) >>
         qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee s /\ _`
           (qspec_then `H` (irule o cj 2)) >> first_assum ACCEPT_TAC)
     >- (simp_tac bool_ss [EVERY_DEF] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         map_every (fn pat => qpat_assum pat (fn th => PURE_REWRITE_TAC [th]))
           [`ba.buf_operand = Var r`,`off = Var x`,`len = Var y`] >>
         simp[NoAsms, exprSafeOperandTheory.safe_operand_def] >> first_assum ACCEPT_TAC)
     >- (qpat_assum `?aw. eval_operand addr s = SOME aw /\ _`
           (qx_choose_then `aw` strip_assume_tac) >>
         qexists `aw` >> conj_tac >- first_assum (drule_then ACCEPT_TAC) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `?vw. eval_operand value s = SOME vw /\ _`
           (qx_choose_then `vw` strip_assume_tac) >>
         qexists `vw` >> conj_tac >- first_assum (drule_then ACCEPT_TAC) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `eval_operand gas t = SOME gw` (fn th => simp[NoAsms,th]))
     >- (qexistsl [`n2w (w2n rw + 28)`,`n2w (4 + LENGTH bytes)`] >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_assum `w2n (n2w (w2n rw + 28) : bytes32) = _` (fn th => PURE_REWRITE_TAC [th]) >>
         qpat_assum `w2n (n2w (4 + LENGTH bytes) : bytes32) = _` (fn th => PURE_REWRITE_TAC [th]) >>
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
  `IS_SOME dopt /\ ~is_word_type dt ==>
    ?w aid tv. eval_operand def t = SOME w /\
      evaluate_type (get_tenv cx) dt = SOME tv /\
      FLOOKUP t.vs_allocas aid = SOME (w2n w,type_memory_size tv) /\
      aid < sp.cs_next_id` by
    (strip_tac >>
     `?dv. dopt = SOME dv` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
     qpat_assum `!dv. dopt = SOME dv /\ ~is_word_type dt ==> ptr_mem_ok cx dt dv def G tn s /\ _ /\ ?w aid tv. _`
       (drule_all_then (qx_choosel_then [`w`,`aid`,`tv`] strip_assume_tac) o cj 3) >>
     qexistsl_tac [`w`,`aid`,`tv`] >> simp[] >>
     `aid < sp.cs_next_id` by decide_tac >>
     qpat_assum `wb_frame cenv ee ee se s t`
       (mp_tac o cj 2 o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >> simp[]) >>
  qexistsl [`bs ++ bytes`,`t`,`Gf`,`tf`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (simp_tac bool_ss [Abbr `bs`] >> first_assum ACCEPT_TAC)
  >- (qx_gen_tac `ao` >> qx_gen_tac `az` >> strip_tac >>
      `w2n (ao:bytes32) = w2n rw + 28` by
        (qpat_x_assum `eval_operand off t = SOME ao` mp_tac >>
         qpat_assum `eval_operand off t = SOME (n2w (w2n rw + 28))`
           (fn th => PURE_REWRITE_TAC [th,optionTheory.SOME_11]) >>
         disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      `w2n (az:bytes32) = 4 + LENGTH bytes` by
        (qpat_x_assum `eval_operand len t = SOME az` mp_tac >>
         qpat_assum `eval_operand len t = SOME (n2w (4 + LENGTH bytes))`
           (fn th => PURE_REWRITE_TAC [th,optionTheory.SOME_11]) >>
         disch_then (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
      conj_tac
      >- (strip_tac >> conj_tac
          >- (qexists `x` >> conj_tac >- first_assum ACCEPT_TAC >>
              qpat_assum `w2n az = 4 + LENGTH bytes` SUBST1_TAC >>
              first_assum ACCEPT_TAC) >>
          decide_tac) >>
      qx_gen_tac `j` >> disch_tac >>
      qpat_assum `!i. w2n rw + 28 <= i /\ i < w2n rw + 32 + LENGTH bytes ==> i NOTIN tf.t_mem`
        (qspec_then `j` irule) >> decide_tac)
  >- (disch_tac >> qexists `r` >> conj_tac >> first_assum ACCEPT_TAC)
QED

Finalise extcall_request_packing_ready

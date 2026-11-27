(* Execute the nonempty custom-error payload against the direct encoder. *)
Theory bodyFullCustomErrorEncode
Ancestors
  bodyFullExtCallPacking bodyFullExtCallEncodeTail bodyFullExtCallSelectorReady
  bodyFullExtCallDirectStart bodyFullExtCallDirectLayout
  bodyFullExtCallDirectEncode bodyFullExtCallDirectRow bodyFullExtCallDirectState
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  localPtrsProps abiEncodeValuesMetadata abiDecodeRanges abiDecoderMembers
  bodyFullIntCallReturnFrame bodyPtrBytestringBuiltinsWindowGhost
  exprLoweringProps exprSimWordArgs wordArgsPtr exprSimProps exprSimExtCallCase
  emitHelperProps compileEnv fragGasOriginPtrLoop fragGasOriginPtr list pair words
  vyperABI vyperStorageFootprint stateRelProj venomMemDefs memoryReadProps
  bodyInvSplit[qualified] exprSimHypsDefs[qualified]

Theorem custom_error_data_eq_calldata[local]:
  LENGTH tys = LENGTH vals ==>
  build_custom_error_data tenv name tys vals = build_ext_calldata tenv name tys vals
Proof
  strip_tac >>
  `TAKE (LENGTH vals) tys = tys` by simp[TAKE_LENGTH_ID_rwt] >>
  simp[build_custom_error_data_def, build_ext_calldata_def]
QED

Theorem custom_error_encode_payload:
  !mods exps.
  LENGTH xs = LENGTH vals /\ LENGTH vals = LENGTH argvs /\
  LENGTH argvs = LENGTH arg_types /\ tys = MAP (lowered_value_type cenv) xs /\
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\ expr_sim_inv_mods mods cenv cx env ee /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
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
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  bs = function_selector fname (vyper_to_abi_types (get_tenv cx) arg_types) /\
  n = abi + 32 /\ n < dimword (:256) /\
  compile_alloc_buffer n se = (ba,sb) /\
  emit_void MSTORE [ba.buf_operand;Lit (calldata_method_id bs)] sb = ((),sm) /\
  emit_op ADD [ba.buf_operand;Lit 32w] sm = (dst,enc_start) /\
  compile_abi_encode_values_to_buf cenv dst (ZIP (vals,tys)) enc_start = (alen,enc_end) /\
  fn_has_code se sb func /\ fn_has_code sb sm func /\
  fn_has_code sm enc_start func /\ fn_has_code enc_start enc_end func /\
  fn_inst_ids_distinct func /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s) /\
  local_ptrs_reserved cenv se /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?r rw bytes q Gq tq.
    ba.buf_operand = Var r /\
    build_custom_error_data (get_tenv cx) fname arg_types argvs = SOME (bs ++ bytes) /\
    eval_operand alen q = SOME (n2w (LENGTH bytes)) /\
    (!x. alen = Var x ==> not_fresh_at enc_end x) /\
    op_taint tq alen = {} /\
    lookup_var r q = SOME rw /\ ptr_covers Gq tq r q n /\
    w2n rw + n <= q.vs_alloca_next /\ q.vs_alloca_next < dimword (:256) /\
    32 + LENGTH bytes <= n /\
    read_memory (w2n rw+28) (4 + LENGTH bytes) q = bs ++ bytes /\
    allocas_from lo q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    ~q.vs_halted /\ q.vs_current_bb = enc_end.cs_current_bb /\
    q.vs_inst_idx = LENGTH enc_end.cs_current_insts /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK q,Gq,tq)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `rows = ZIP (vals,tys)` >>
  `LENGTH tys = LENGTH xs /\ LENGTH rows = LENGTH xs` by
    simp[Abbr `rows`, LENGTH_ZIP] >>
  `32 <= n` by simp[] >>
  `LENGTH bs = 4` by simp[selectorCompilerPropsTheory.function_selector_length] >>
  qabbrev_tac `HH = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 HH ee.storage_trace` by
    fs[Abbr `HH`, storage_trace_domain_def] >>
  Q.SUBGOAL_THEN `?H. valid_horizon cx st0 H ee.storage_trace` assume_tac
  >- (qexists_tac `HH` >> first_assum ACCEPT_TAC) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
    (qspec_then `HH` (drule_then strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee s` by
    (gen_tac >> disch_tac >> first_assum (drule_then (ACCEPT_TAC o cj 1))) >>
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
  `ci_mono se sb /\ ci_mono sb sm /\ ci_mono sm enc_start` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_emit_void, ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono se enc_start` by metis_tac[ci_mono_trans] >>
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
        `off` |-> `ofst`, `cursor_inst` |-> `ci`] abi_encode_direct_row) >>
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
  `stmt_state_rel HH ctx func cenv cx ee q` by metis_tac[] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  `q.vs_alloca_next < dimword (:256)` by
    metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  `build_custom_error_data (get_tenv cx) fname arg_types argvs = SOME (bs ++ bytes)` by
    (qpat_assum `LENGTH argvs = LENGTH arg_types`
       (fn th => PURE_ONCE_REWRITE_TAC [MATCH_MP custom_error_data_eq_calldata (SYM th)]) >>
     qpat_assum `bs = function_selector _ _` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `read_memory (w2n rw+32) (LENGTH bytes) q = bytes` by
    (PURE_REWRITE_TAC[read_memory_eq_mem_bytes_at] >> first_assum ACCEPT_TAC) >>
  `read_memory (w2n rw+28) (4 + LENGTH bytes) q = bs ++ bytes` by
    (ONCE_REWRITE_TAC[read_memory_split] >>
     `w2n rw+28+4 = w2n rw+32` by decide_tac >>
     qpat_assum `w2n rw+28+4 = w2n rw+32` (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `read_memory (w2n rw+28) 4 q = bs`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     qpat_assum `read_memory (w2n rw+32) (LENGTH bytes) q = bytes`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> REFL_TAC) >>
  qexistsl_tac [`r`,`rw`,`bytes`,`q`,`Gq`,`tq`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`lookup_var r q = SOME rw`]
  >- (qpat_assum `eval_operand (Var r) q = SOME (n2w (w2n rw))`
       (ACCEPT_TAC o REWRITE_RULE [venomStateTheory.eval_operand_def, n2w_w2n]))
  >~ [`32 + LENGTH bytes <= n`]
  >- (qpat_assum `LENGTH bytes <= abi` mp_tac >>
      qpat_assum `n = abi + 32` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  gen_tac >>
  match_mp_tac (Q.INST [`s1` |-> `u`, `G1` |-> `Gu`, `tn1` |-> `tu`] gas_origin_ptr_path_trans) >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

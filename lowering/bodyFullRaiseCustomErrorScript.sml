(* Join the saved argument values and the custom-error exit at one horizon. *)
Theory bodyFullRaiseCustomError
Ancestors
  bodyFullCustomErrorSource bodyFullCustomErrorLayout bodyFullCustomErrorExit
  bodyFullCustomErrorEncode bodyFullExtCallPosList bodyFullExtCallBufferSetup
  bodyFullExtCallRequestPostGasPacking bodyFullHashKeccakFixed[qualified,ignore_grammar]
  contractABI abiDecoderMembers vyperTypeSystem gasContext
  bodyFullShadowBodyInv bodyFullPreds bodySimFull bodySim bodyInvMetadataProps
  bodyCustomErrorWindowBounds exprSimHyps exprBodyPreProps augAssignFullRhsSaved
  exprSimHypsDefs exprSimSource exprSimDefs stmtSimDefs stmtSimProps reasonCopySourcePtr
  gasOutcomeFullCompose gasOutcomeFull gasExemptCert gasSummary gasShadow gasShadowState
  gasShadowCompilePure bodyMemoryDefs bodyPtrDefs bodyFullShared
  stmtLowering exprLowering exprLoweringProps compileEnv context
  allocLimits loweringPosts stateRelProj
  vyperInterpreter vyperState vyperStorageTrace vyperStorageFootprint
  vyperABIRoundtrip vyperABI vyperTypeArgFits vyperTypeExprSoundness vyperTypeInvariants
  vyperContext selectorDispatch selectorCompilerProps valueEncoding
  ptrDiscipline venomMemDefs fragGasOriginPtrLoop fragExec
  list pair words arithmetic
  bodyFullPostsMods[qualified] bodyFullPredsMods[qualified] bodyInvSplit[qualified]

Theorem custom_error_tail_outcome[local]:
  build_custom_error_data tenv name formals vs = SOME data /\
  ~u.vs_halted /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (u,Gu,tu) [] (Abort Revert_abort t,Gexit,tt)) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
    (bind (lift_option (build_custom_error_data tenv name formals vs)
       "custom error encoding") (\data. raise (Error (RevertData data))))
    (mid,u,Gu,tu) Q
    (\H res ee gt r.
       (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
       halt_exit H cx ee res r /\
       (ctx_has_dalloca ctx ==>
         !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
Proof
  strip_tac >> irule gas_outcome_full_exit >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`Gexit`,`mid`,`Abort Revert_abort t`,`INR (Error (RevertData data))`,`tt`] >>
  simp[bind_def, lift_option_def, raise_def, return_def, exit_result_def,
       stmt_exit_ptr_def, expr_exit_def, halt_exit_def]
QED

Theorem compile_raise_custom_frag_full:
  !mods exps cx err DF lo d PG tops bindings ctx shadow_ctx func shadow_func cenv env
    env' ret_ty lctx RetQ es.
    (!id pos kw error_tops params args.
       err = CustomError id pos kw /\
       get_module_code cx (FST id) = SOME error_tops /\
       lookup_custom_error_args_in (SND id) error_tops = SOME params /\
       order_custom_error_args params err = SOME args ==>
       body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    supported_stmt tops bindings (Raise (RaiseCustomError err)) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Raise (RaiseCustomError err)) ==> occurs_abi_decode_target target tops) /\
    body_const_cells_agree mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx RetQ cenv ret_ty ==>
    stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (stmt_env (gas_shadow_env T cenv) lctx ret_ty
        (gas_shadow_stmt (Raise (RaiseCustomError err))))
      (eval_stmt cx (Raise (RaiseCustomError err))) es
Proof
  rpt gen_tac >> strip_tac >> Cases_on `err` >> rename1 `CustomError id pos kw` >>
  drule_all custom_error_raise_source >>
  disch_then (qx_choosel_then [`params`,`args`] strip_assume_tac) >>
  `body_exprs_full_ok cx args` by metis_tac[] >>
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  fs[gas_shadow_stmt_def, gas_shadow_raise_reason_def] >>
  qabbrev_tac `tys = MAP (lowered_value_type cenv) args` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `ta` |-> `shadow_sa`,
    `tb` |-> `shadow_sb`, `sfunc` |-> `shadow_func`, `ty` |-> `ret_ty`,
    `ca` |-> `cenv'`, `ct` |-> `gas_shadow_env T cenv'`]
    compile_raise_custom_layout_full) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> simp[Abbr `tys`]) >>
  disch_then (qx_choosel_then [`saved`,`se`,`te`,`buf`,`sm`,`ss`]
    strip_assume_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    metis_tac[ret_pc_ok_def] >>
  mp_tac (Q.INST [`kw_es` |-> `[]:expr list`, `xs` |-> `args`,
     `svs` |-> `saved`, `sb` |-> `se`, `shadow_sb` |-> `te`]
     (Q.SPEC `F` extcall_request_positional_packing_outcome_named)) >>
  simp[NoAsms, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss] >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     fs[Abbr `tys`, MAP_MAP_o, combinTheory.o_DEF, SF ETA_ss]) >>
  strip_tac >>
  qpat_assum `eval_stmt cx (Raise (RaiseCustomError _)) = _`
    (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
  irule gas_outcome_full_bind_all >>
  rpt conj_tac
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[cj 6 evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_lifts, storage_trace_frame_raise])
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  qexists_tac `extcall_positional_post F DF lo d ctx func cenv cx env
    [] args saved sa se es s0 G0 tn0` >>
  reverse conj_tac
  >- (qpat_assum `args = custom_error_exprs _`
        (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
      irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[expr_exit_def] >>
      pop_assum (strip_assume_tac o BETA_RULE) >>
      simp[] >> drule_all augassign_expr_exit_to_stmt_exit >>
      disch_then (qspecl_then [`gt`,`RetQ`] strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "arguments"
QED

Resume compile_raise_custom_frag_full[arguments]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`u`] >>
  BETA_TAC >> strip_tac >>
  qpat_assum `args = custom_error_exprs _` (fn eq =>
    qpat_x_assum `!tail. eval_exprs _ _ _ = _`
      (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post F DF lo d ctx func cenv cx env [] args saved sa se es s0 G0 tn0 H _ _ _ _ _`
    (qspec_then `H0` (drule_then
        (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def]))) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  disj1_tac >> qexists_tac `vs` >> simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 u` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post F DF lo d ctx func cenv cx env [] args saved sa se es s0 G0 tn0 H _ _ _ _ _`
       (qspec_then `H` (drule_then
         (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def]))) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `sa.cs_next_var <= se.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv se /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x)` by
    metis_tac[local_ptrs_reserved_next_var, freshWritesTheory.not_fresh_at_mono] >>
  `get_tenv cx = type_env tops` by
    (drule_then assume_tac body_inv_contract >>
     drule_then assume_tac contract_inv_type_env >>
     fs[type_env_all_modules_def, type_env_def, finite_mapTheory.FUNION_FEMPTY_2]) >>
  qabbrev_tac `selector = function_selector (SND id)
    (vyper_to_abi_types (get_tenv cx) (MAP SND params))` >>
  `LENGTH selector = 4` by simp[Abbr `selector`, function_selector_length] >>
  `n2w (cenv.ce_method_id (SND id) (MAP SND params)) = calldata_method_id selector` by
    fs[body_inv_def, cenv_module_pins_def, Abbr `selector`] >>
  qabbrev_tac `abi = abi_size_bound cenv.ce_struct_fields (TupleT tys)` >>
  qabbrev_tac `n = abi + 32` >>
  `32 <= n /\ n < dimword (:256)` by
    (Cases_on `id` >> gvs[Abbr `n`, Abbr `abi`, Abbr `tys`,
        custom_error_alloc_ok_def, dimword_def] >> decide_tac) >>
  Cases_on `NULL args`
  >- (qpat_assum `NULL args` (fn is_null =>
        qpat_x_assum `if NULL args then _ else _`
          (qx_choosel_then [`offset`,`sn`] strip_assume_tac o REWRITE_RULE [is_null])) >>
      suspend "nullary") >>
  qpat_assum `~NULL args` (fn nonempty =>
    qpat_x_assum `if NULL args then _ else _`
      (qx_choosel_then [`dst`,`st`,`payload_len`,`en`,`offset`,`sr`,`len`,`sn`]
        strip_assume_tac o REWRITE_RULE [nonempty])) >>
  suspend "payload"
QED

Resume compile_raise_custom_frag_full[nullary]:
  `args = []` by fs[NULL_EQ] >>
  `vs = []` by
    (qpat_assum `args = []` (fn eq =>
       qpat_assum `!tail. eval_exprs cx args _ = _`
         (mp_tac o PURE_ONCE_REWRITE_RULE [eq] o Q.SPEC `[]`)) >>
     simp_tac bool_ss [Once evaluate_def, return_def, pairTheory.PAIR_EQ, sumTheory.INL_11] >>
     strip_tac >> sym_tac >> first_assum ACCEPT_TAC) >>
  `params = []` by fs[Abbr `tys`] >>
  `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) [] =
      SOME selector` by
    simp[Abbr `selector`, build_custom_error_data_def, vyper_to_abi_def,
         vyper_to_abi_type_def, enc_def, REV_DEF] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid u`
       (fn rel => assume_tac (MATCH_MP stmt_state_rel_fmp_room rel) >>
                  assume_tac (MATCH_MP
                    bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp rel)) >>
     simp[] >> strip_tac >> fs[fmp_room_def] >> decide_tac) >>
  mp_tac (Q.INST [`H0` |-> `H0`, `bs` |-> `selector`, `cenv` |-> `cenv`,
      `sa` |-> `se`, `sb` |-> `sm`, `sc` |-> `ss`, `es` |-> `mid`,
      `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`, `shared` |-> `buf`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `n` |-> `n`]
    extcall_direct_request_buffer) >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> fs[Abbr `n`, Abbr `abi`]) >>
  disch_then (qx_choosel_then [`root`,`w`,`v`,`Gv`,`tv`] strip_assume_tac) >>
  qpat_assum `buf.buf_operand = Var root` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    metis_tac[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  mp_tac (Q.INST [`encoded` |-> `NONE:operand option`,`k` |-> `0`,
     `a` |-> `ss`,`b` |-> `sn`,`c` |-> `sn`,`en` |-> `sb`,
     `len` |-> `Lit 4w`,`s` |-> `v`,`G` |-> `Gv`,`tn` |-> `tv`,
     `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] custom_error_terminal_path) >>
  simp[] >>
  impl_tac >-
    (`v.vs_alloca_next < dimword (:256)` by
       metis_tac[stateRelProjTheory.stmt_state_rel_alloca_room, alloca_room_next_lt] >>
     `ptr_covers Gv tv root v 32` by metis_tac[ptr_covers_mono] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`t`,`Gexit`,`tt`] strip_assume_tac) >>
  irule custom_error_tail_outcome >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`?data. build_custom_error_data _ _ _ _ = SOME data`]
  >- (qexists_tac `selector` >>
      qpat_assum `get_tenv cx = type_env tops` (fn htenv =>
        qpat_assum `params = []` (fn hparams =>
          qpat_assum `build_custom_error_data (get_tenv cx) _ _ _ = SOME selector`
            (ACCEPT_TAC o REWRITE_RULE [htenv, hparams, MAP])))) >>
  qexistsl_tac [`Gexit`,`t`,`tt`] >>
  gen_tac >>
  match_mp_tac (Q.INST [`s1` |-> `v`, `G1` |-> `Gv`, `tn1` |-> `tv`] gas_origin_ptr_path_trans) >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

fun push_saved_row () =
  qpat_assum `LENGTH args = LENGTH saved` (fn same =>
    qpat_assum `i < LENGTH args` (fn bound =>
      let
        val zip_len = CONJUNCT1
          (MATCH_MP (Q.SPECL [`args`,`saved`] LENGTH_ZIP) same)
        val zip_el = MATCH_MP (Q.SPECL [`args`,`saved`,`i`] EL_ZIP)
          (CONJ same bound)
      in
        qpat_assum `LIST_REL _ (ZIP (args,saved)) vs` (fn rows =>
          let
            val indexed = Q.SPEC `i` (cj 2 (REWRITE_RULE [LIST_REL_EL_EQN,zip_len] rows))
          in
            mp_tac (SIMP_RULE (srw_ss()) [zip_el] (MATCH_MP indexed bound))
          end)
      end));

Resume compile_raise_custom_frag_full[payload]:
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) args vs` by
    (qspecl_then [`args`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
         `vs`,`mid with gas_obs := []`] mp_tac
       (Q.INST [`ce` |-> `cenv`] eval_exprs_physical_runtime_typed) >>
     impl_tac
     >- (rpt conj_tac
         >- (simp[EVERY_MEM] >> rpt strip_tac >>
             qpat_assum `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==> _`
               (qspecl_then [`e`,`es with gas_obs := gas_explicit marks s0.vs_gas_readings`] irule) >>
             simp[])
         >- (qpat_assum `args = custom_error_exprs _`
               (fn eq => PURE_ONCE_REWRITE_TAC [GSYM eq]) >>
             qpat_assum `!tail. eval_exprs cx args _ = _`
               (ACCEPT_TAC o PURE_REWRITE_RULE [APPEND_NIL] o Q.SPEC `[]`))
         >- (rpt strip_tac >> irule expr_sim_inv_read_lowered_typed >>
             fs[expr_body_pre_def] >> metis_tac[])) >>
     disch_then ACCEPT_TAC) >>
  `LENGTH args = LENGTH vs /\ LENGTH args = LENGTH (MAP SND params)` by
    (drule LIST_REL_LENGTH >> simp[] >>
     qpat_assum `MAP expr_type args = _`
       (mp_tac o Q.AP_TERM `LENGTH:type list -> num`) >> simp[]) >>
  `arg_types_fit (MAP expr_type args) (MAP SND params)` by
    (qpat_assum `MAP expr_type args = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     simp[arg_types_fit_LIST_REL, LIST_REL_refl, arg_type_fits_refl]) >>
  `EVERY (well_formed_type (get_tenv cx)) (MAP SND params)` by
    (qpat_assum `MAP expr_type args = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     simp[NoAsms, EVERY_MAP, EVERY_MEM, well_formed_type_def] >>
     rpt strip_tac >> irule expr_body_pre_type_evaluates >>
     qexistsl_tac [`cenv`,`env`,`es`] >> metis_tac[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by
    metis_tac[custom_error_invariant_layout] >>
  mp_tac (Q.INST [`xs` |-> `args`, `vs` |-> `vs`, `av` |-> `saved`,
     `ats` |-> `MAP SND (params : (string # type) list)`, `pos` |-> `es`, `ee` |-> `mid`, `t` |-> `u`,
     `G` |-> `G1`, `tn` |-> `tn1`] post_gas_indexed_rows) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qx_gen_tac `i` >> strip_tac >>
      `LENGTH args = LENGTH saved` by (sym_tac >> first_assum ACCEPT_TAC) >>
      push_saved_row () >>
      disch_then (CONJUNCTS_THEN2
        (qx_choosel_then [`si`,`row_mid`,`row_end`,`vv`,`raw`,`copy`]
          (MAP_EVERY assume_tac o CONJUNCTS))
        (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qexistsl_tac [`EL i args`,`EL i saved`,`EL i vs`,`raw`,`si`,`row_mid`,
        `row_end`,`vv`,`copy`] >>
      rpt conj_tac >> TRY REFL_TAC >> TRY (first_assum ACCEPT_TAC)
      >- (qx_gen_tac `H` >> strip_tac >>
          qpat_x_assum `LIST_REL _ (ZIP (args,saved)) vs` (K ALL_TAC) >>
          qpat_assum `!H. valid_horizon _ _ H _ ==> extcall_positional_post F DF lo d ctx func cenv cx env [] args saved sa se es s0 G0 tn0 H _ _ _ _ _`
            (qspec_then `H` (drule_then
              (strip_assume_tac o SIMP_RULE bool_ss [extcall_positional_post_def]))) >>
          qpat_x_assum `INL vs = INL _`
            (SUBST_ALL_TAC o SYM o SIMP_RULE bool_ss [sumTheory.INL_11]) >>
          push_saved_row () >> disch_then (ACCEPT_TAC o cj 2))
      >- (qpat_assum `!tag op. EL i saved = StackValue tag op /\ _ ==> _` mp_tac >>
          qpat_assum `!tag p. EL i saved = LocatedValue tag p /\ _ ==> _` mp_tac >>
          POP_ASSUM_LIST (K ALL_TAC) >>
          Cases_on `EL i saved` >> simp[vv_operand_def])) >>
  strip_tac >>
  mp_tac (Q.INST [`xs` |-> `args`, `vals` |-> `saved`, `argvs` |-> `vs`,
      `arg_types` |-> `MAP SND (params : (string # type) list)`,
      `fname` |-> `SND (id : num option # string)`, `bs` |-> `selector`,
      `ba` |-> `buf`, `sb` |-> `sm`, `sm` |-> `ss`, `s` |-> `u`,
      `G` |-> `G1`, `tn` |-> `tn1`, `ee` |-> `mid`, `alen` |-> `payload_len`,
      `enc_start` |-> `st`, `enc_end` |-> `en`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    custom_error_encode_payload) >>
  impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     fs[Abbr `selector`, Abbr `n`, Abbr `abi`, Abbr `tys`]) >>
  disch_then (qx_choosel_then [`root`,`w`,`bytes`,`q`,`Gq`,`tq`] strip_assume_tac) >>
  qpat_assum `buf.buf_operand = Var root` (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
  `ptr_covers Gq tq root q (LENGTH bytes + 32)` by
    (ONCE_REWRITE_TAC [arithmeticTheory.ADD_COMM] >> metis_tac[ptr_covers_mono]) >>
  mp_tac (Q.INST [`encoded` |-> `SOME payload_len`, `k` |-> `LENGTH (bytes : word8 list)`,
      `a` |-> `en`, `b` |-> `sr`, `c` |-> `sn`, `en` |-> `sb`,
      `s` |-> `q`, `G` |-> `Gq`, `tn` |-> `tq`,
      `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] custom_error_terminal_path) >>
  simp[NoAsms] >>
  impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  disch_then (qx_choosel_then [`t`,`Gexit`,`tt`] strip_assume_tac) >>
  irule custom_error_tail_outcome >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >~ [`?data. build_custom_error_data _ _ _ _ = SOME data`]
  >- (qexists_tac `selector ++ bytes` >>
      qpat_assum `build_custom_error_data _ _ _ _ = SOME (selector ++ bytes)` ACCEPT_TAC) >>
  qexistsl_tac [`Gexit`,`t`,`tt`] >>
  gen_tac >>
  match_mp_tac (Q.INST [`s1` |-> `q`, `G1` |-> `Gq`, `tn1` |-> `tq`] gas_origin_ptr_path_trans) >>
  conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Finalise compile_raise_custom_frag_full

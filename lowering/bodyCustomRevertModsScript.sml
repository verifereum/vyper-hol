(* The custom-error descriptor selects its owner in the linked unit. *)
Theory bodyCustomRevertMods
Ancestors
  bodyInvCodeProps bodyQualifiedStmtSupport vyperTypeContract vyperInterpreter
  vyperAST vyperABI vyperEvent vyperState list pair
  bodyCustomErrorCompilerPinsMods bodyCustomErrorArgPreMods bodyCustomErrorPositionalMods
  bodyCustomErrorBindMods bodyCustomErrorTerminalMods bodyExtPosListRunMods gasOutcomeFullPostMods
  bodyExtPhysicalPrefixMods bodyExtTuplePayloadMods bodyFullExtCallDirectLayout
  bodyCopyArgReadTypesMods bodyCopyReadPhysicalTypeMods bodyAssignNameLinkedSetup
  bodyFullHashKeccakFixed stateRelProj memoryReadProps typedMemoryCopy
  exprBodyPreProps exprBodyPreTypingProps exprSimHypsDefs exprSimFullBundleProps
  bodyFullPostsMods bodyFullShadowBodyInv bodySim exprLoweringProps freshWrites loweringPosts
  bodyPtrDefs selectorCompilerProps contractABI reasonCopySourcePtr allocLimits vyperTypeArgFits
  vyperStorageFootprint gasShadow fragGasOriginPtr words bodyWriteSubscriptSourceMods
  vyperTypeEvalCaseProofs vyperTypeInvariants exprSafeOperand logArgumentTypeEval
  vyperTypeSystem vyperTypeDefaults vyperTypeExprSoundness entryDecodeStaticProps
  vyperABIRoundtrip bodyExtPackingEndpointMods allocaSiteResource
Libs
  horizonTypeLib

Theorem custom_error_order_keeps_exprs_mods[local]:
  order_custom_error_args params err = SOME args ==>
  args = custom_error_exprs err
Proof
  Cases_on `err` >>
  simp[order_custom_error_args_def, custom_error_exprs_def, AllCaseEqs()] >>
  strip_tac >> gvs[NULL_EQ] >>
  drule order_custom_error_kwargs_SOME >> simp[]
QED

Theorem custom_error_raise_source_mods:
  contract_inv mods exps ctx cenv cx /\
  qualified_stmt_decls_ok mods (Raise (RaiseCustomError err)) ==>
  ?id pos kw error_tops params args.
    err = CustomError id pos kw /\
    get_module_code cx (FST id) = SOME error_tops /\
    lookup_custom_error_args_in (SND id) error_tops = SOME params /\
    order_custom_error_args params err = SOME args /\
    args = custom_error_exprs err /\
    MAP expr_type args = MAP SND params /\
    eval_stmt cx (Raise (RaiseCustomError err)) =
      bind (eval_exprs cx args) (\vs. bind
        (lift_option (build_custom_error_data (get_tenv cx) (SND id)
          (MAP SND params) vs) "custom error encoding")
        (\data. raise (Error (RevertData data))))
Proof
  Cases_on `err` >> PairCases_on `p` >> strip_tac >>
  drule_then assume_tac contract_inv_module_codes >>
  fs[qualified_stmt_decls_ok_def, qualified_custom_error_ok_def,
     custom_error_resolved_def] >>
  Cases_on `ALOOKUP mods p0` >> gvs[] >>
  rename1 `ALOOKUP mods _ = SOME ts` >>
  Cases_on `lookup_custom_error_args_in p1 ts` >> gvs[] >>
  rename1 `lookup_custom_error_args_in _ _ = SOME ps` >>
  Cases_on `order_custom_error_args ps (CustomError (p0,p1) l l0)` >> gvs[] >>
  drule custom_error_order_keeps_exprs_mods >> strip_tac >>
  gvs[Once evaluate_def]
QED

val raise_err = ``Raise (RaiseCustomError err)``;
val resolve = ``!ctx cenv src tops env es bindings s ret_ty env'.
   contract_inv mods exps ctx cenv cx /\
   module_body_inv mods src tops cenv cx /\
   expr_sim_inv_mods mods cenv cx env es /\
   body_const_cells_agree_mods mods cx env es /\
   supported_stmt tops bindings s /\ type_stmt env ret_ty s = SOME env' ==>
   EVERY (source_body_call_supported cx) (int_calls_stmt s)``;

Theorem compile_raise_custom_frag_full_mods:
  (!id pos kw error_tops params args.
     err = CustomError id pos kw /\
     get_module_code cx (FST id) = SOME error_tops /\
     lookup_custom_error_args_in (SND id) error_tops = SOME params /\
     order_custom_error_args params err = SOME args ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  ^resolve /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  qualified_stmt_decls_ok mods ^raise_err /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings ^raise_err /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target) ^raise_err ==>
     EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  type_stmt env ret_ty ^raise_err = SOME env' /\ stmt_exprs_ok cenv ^raise_err /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) ^raise_err /\
  call_evaluation_safe cx (int_calls_stmt ^raise_err) /\
  frame_ret_ok_full_mods mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty ^raise_err)
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty (gas_shadow_stmt ^raise_err))
    (eval_stmt cx ^raise_err) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all custom_error_raise_source_mods >>
  disch_then (qx_choosel_then [`id`,`pos`,`kw`,`error_tops`,`params`,`args`]
    (map_every assume_tac o CONJUNCTS)) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  `ALOOKUP mods (FST id) = SOME error_tops` by
    (drule contract_inv_module_codes >> disch_then (qspec_then `FST id` (SUBST1_TAC o SYM)) >>
     first_assum ACCEPT_TAC) >>
  `!e. MEM e args ==> expr_body_pre_mods mods cenv cx env e es` by
    (gen_tac >> disch_tac >>
     mp_tac custom_error_arg_pre_mods >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then irule >> simp[] >> qexistsl_tac [`bindings`,`ctx`,`env'`,`exps`,`src`,`tops`,`ret_ty`,`err`] >> simp[]) >>
  qpat_x_assum `err = CustomError id pos kw` SUBST_ALL_TAC >>
  drule_all custom_error_compiler_pins_mods >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  mp_tac (Q.INST [`Pos` |-> `\st0 sa se saved s0 G0 tn0 H vs mid G1 tn1 t.
       extcall_positional_post_mods F mods DF lo d ctx func cenv cx env
         [] args saved sa se es s0 G0 tn0 H (INL vs) mid G1 tn1 t`,
     `err` |-> `CustomError id pos kw`] custom_error_frag_from_stages_mods) >>
  asm_rewrite_tac[] >> BETA_TAC >>
  (impl_tac >- suspend "stages") >> simp[]
QED

Resume compile_raise_custom_frag_full_mods[stages]:
  qpat_assum `args = custom_error_exprs _` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >>
      simp[expr_body_pre_mods_def]) >>
  conj_tac >- suspend "positional" >>
  suspend "tail"
QED

Resume compile_raise_custom_frag_full_mods[positional]:
  rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac custom_error_positional_outcome_mods >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `!PG. gas_outcome_full_mods _ _ _ _ _ _ _ _` (qspec_then `PG` (irule_at Any)) >>
  simp[extcall_positional_post_mods_def]
QED

Resume compile_raise_custom_frag_full_mods[tail]:
  qx_genl_tac [`st0`,`sa`,`sb`,`se`,`sha`,`te`,`saved`,`buf`,`sm`,`ss`,`s0`,
               `G0`,`tn0`,`marks`,`vs`,`mid`,`u`,`G1`,`tn1`,`Q`] >> strip_tac >>
  drule_then strip_assume_tac expr_sim_full_code_fields >>
  qabbrev_tac `tys = MAP (lowered_value_type cenv) args` >>
  qabbrev_tac `n = abi_size_bound cenv.ce_struct_fields (TupleT tys) + 32` >>
  qabbrev_tac `selector = function_selector (SND id)
     (vyper_to_abi_types (get_tenv cx) (MAP SND params))` >>
  `LENGTH selector = 4` by simp[Abbr `selector`, function_selector_length] >>
  qabbrev_tac `hz = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 hz mid.storage_trace` by fs[Abbr `hz`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ mid.storage_trace ==> _`
    (drule_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [extcall_positional_post_mods_def])) >>
  qpat_x_assum `INL vs = INL _` (SUBST_ALL_TAC o SYM o REWRITE_RULE [sumTheory.INL_11]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `sa.cs_next_var <= se.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv se` by metis_tac[local_ptrs_reserved_next_var] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x` by
    metis_tac[not_fresh_at_mono] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x` by
    metis_tac[ret_pc_ok_def, not_fresh_at_mono] >>
  Cases_on `NULL args`
  >- (qpat_assum `NULL args` (fn eq =>
        qpat_x_assum `if NULL args then _ else _`
          (qx_choosel_then [`offset`,`sn`] strip_assume_tac o REWRITE_RULE [eq])) >>
      suspend "nullary") >>
  qpat_assum `~NULL args` (fn eq =>
    qpat_x_assum `if NULL args then _ else _`
      (qx_choosel_then [`dst`,`st`,`encoded`,`en`,`offset`,`sr`,`len`,`sn`]
         strip_assume_tac o REWRITE_RULE [eq])) >>
  suspend "payload"
QED

Resume compile_raise_custom_frag_full_mods[nullary]:
  `args = []` by fs[NULL_EQ] >>
  `vs = []` by
    (qpat_assum `args = []` (fn eq =>
       qpat_assum `!tail. eval_exprs cx args _ = _`
         (mp_tac o PURE_ONCE_REWRITE_RULE [eq] o Q.SPEC `[]`)) >>
     simp[Once evaluate_def, return_def]) >>
  `params = []` by fs[Abbr `tys`] >>
  `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs = SOME selector` by
    simp[Abbr `selector`, build_custom_error_data_def, vyper_to_abi_def,
         vyper_to_abi_type_def, enc_def, REV_DEF] >>
  mp_tac (Q.INST [`cenv` |-> `cenv`, `es` |-> `mid`, `d` |-> `d`,
       `bs` |-> `selector`, `H0` |-> `hz`, `sa` |-> `se`, `s` |-> `u`,
       `sb` |-> `sm`, `sc` |-> `ss`, `shared` |-> `buf`, `G` |-> `G1`, `tn` |-> `tn1`,
       `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] ext_physical_prefix_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`root`,`w`,`v`,`Gv`,`tv`] (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel hz ctx func cenv cx mid v` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp v` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `v.vs_alloca_next < dimword (:256)` by
    metis_tac[stmt_state_rel_alloca_room, alloca_room_next_lt] >>
  `w2n w + 32 <= v.vs_alloca_next` by decide_tac >>
  `ptr_covers Gv tv root v 32` by (irule ptr_covers_mono >> qexists_tac `n` >> simp[]) >>
  qpat_assum `buf.buf_operand = Var root` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  irule (Q.INST [`encoded` |-> `NONE:operand option`, `k` |-> `0`] custom_error_terminal_outcome_mods) >>
  simp[] >> qexistsl_tac [`Gv`,`ss`,`sn`,`sb`,`offset`,`root`,`v`,`tv`,`w`] >> simp[]
QED

Resume compile_raise_custom_frag_full_mods[payload]:
  qabbrev_tac `entry = es with gas_obs := gas_explicit marks s0.vs_gas_readings` >>
  `eval_exprs cx args entry = (INL vs, mid with gas_obs := [])` by
    (simp_tac bool_ss [Abbr `entry`] >>
     qpat_assum `!tail. eval_exprs cx args _ = _`
        (qspec_then `[]` (ACCEPT_TAC o REWRITE_RULE [APPEND_NIL]))) >>
  `expr_sim_inv_mods mods cenv cx env entry` by simp[Abbr `entry`] >>
  `LIST_REL (\e v. value_runtime_typed env (lowered_value_type cenv e) v) args vs` by
    (qpat_x_assum `args = custom_error_exprs _` kall_tac >>
     irule copy_arg_read_types_from_members_mods >>
     qexistsl_tac [`cx`,`mid with gas_obs := []`,`mods`,`entry`] >>
     asm_rewrite_tac[] >> reverse conj_tac
     >- (simp_tac (srw_ss()) [EVERY_MEM] >> rpt strip_tac >>
         qpat_assum `!e. MEM e args ==> _` (drule_then (mp_tac o REWRITE_RULE [expr_body_pre_mods_def])) >> simp[]) >>
     qx_genl_tac [`e`,`s`,`v`,`ee`] >> strip_tac >>
     `expr_body_pre_mods mods cenv cx env e s` by
       (qpat_assum `!e. MEM e args ==> _`
          (drule_then (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def])) >>
        asm_rewrite_tac[expr_body_pre_mods_def]) >>
     qpat_x_assum `expr_body_pre_mods _ _ _ _ e s`
       (strip_assume_tac o REWRITE_RULE [expr_body_pre_mods_def]) >>
     drule_all_then ACCEPT_TAC copy_read_lowered_type_mods) >>
  `env.type_defs = get_tenv cx` by
    (drule_then assume_tac expr_sim_inv_mods_env >> drule env_consistent_type_defs_get_tenv >> simp[]) >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx)` by fs[expr_sim_inv_mods_def] >>
  `!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
      type_memory_bytes cenv ty = type_memory_size tv` by
    (rpt strip_tac >> irule assign_name_memory_bytes_mods >>
     first_assum (irule_at Any) >> first_assum (irule_at Any)) >>
  `EVERY (type_alloc_ok cenv) tys` by
    fs[stmt_exprs_ok_def, alloc_limits_stmt_def, alloc_limits_raise_def,
       custom_error_alloc_ok_def, Abbr `tys`] >>
  suspend "payload_rows"
QED

Resume compile_raise_custom_frag_full_mods[payload_rows]:
  `LENGTH args = LENGTH vs` by (drule LIST_REL_LENGTH >> simp[]) >>
  `LENGTH (MAP SND params) = LENGTH args` by
    (qpat_assum `MAP expr_type args = MAP SND params` (mp_tac o Q.AP_TERM `LENGTH:type list -> num`) >> simp[]) >>
  `LENGTH tys = LENGTH args /\ LENGTH tys = LENGTH (MAP SND params) /\
   LENGTH tys = LENGTH vs /\ LENGTH tys = LENGTH saved` by simp[Abbr `tys`] >>
  `!i. i < LENGTH tys ==> ?tv ftv.
      evaluate_type (get_tenv cx) (EL i tys) = SOME tv /\
      evaluate_type (get_tenv cx) (EL i (MAP SND params)) = SOME ftv /\
      arg_type_fits (EL i tys) (EL i (MAP SND params)) /\
      value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs)` by suspend "row_types" >>
  `?avs ats bytes.
     vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
     ats = vyper_to_abi_types (get_tenv cx) tys /\
     bytes = enc (Tuple ats) (ListV avs) /\
     build_ext_calldata (get_tenv cx) (SND id) (MAP SND params) vs =
        SOME (function_selector (SND id) (vyper_to_abi_types (get_tenv cx) (MAP SND params)) ++ bytes) /\
     LENGTH bytes <= abi_size_bound cenv.ce_struct_fields (TupleT tys) /\
     LIST_REL abi_encoder_layout_valid ats avs /\
     LIST_REL (\row at. abi_embedded_static_size cenv.ce_struct_fields (SND row) =
                       abi_member_head_size at) (ZIP (saved,tys)) ats` by
    (irule extcall_direct_args_layout >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `build_custom_error_data (get_tenv cx) (SND id) (MAP SND params) vs = SOME (selector ++ bytes)` by
    (`LENGTH (MAP SND params) = LENGTH vs` by decide_tac >>
     `TAKE (LENGTH vs) (MAP SND params) = MAP SND params` by simp[TAKE_LENGTH_ID_rwt] >>
     qpat_assum `TAKE _ _ = _` (fn take =>
       qpat_assum `build_ext_calldata _ _ _ _ = _`
         (mp_tac o REWRITE_RULE [build_ext_calldata_def, LET_THM, take])) >>
     simp_tac bool_ss [build_custom_error_data_def, LET_THM, Abbr `selector`] >>
     asm_rewrite_tac[]) >>
  `LENGTH bytes <= n - 32` by
    (simp_tac bool_ss [Abbr `n`, arithmeticTheory.ADD_SUB] >> first_assum ACCEPT_TAC) >>
  suspend "tuple_run"
QED

Resume compile_raise_custom_frag_full_mods[row_types]:
  qx_gen_tac `i` >> strip_tac >>
  `i < LENGTH args` by decide_tac >>
  `EL i (MAP SND params) = expr_type (EL i args)` by
    (qpat_assum `MAP expr_type args = MAP SND params` (SUBST1_TAC o SYM) >> simp[EL_MAP]) >>
  `EL i tys = lowered_value_type cenv (EL i args)` by simp[Abbr `tys`, EL_MAP] >>
  `expr_body_pre_mods mods cenv cx env (EL i args) es` by
    (qpat_assum `!e. MEM e args ==> _` irule >> simp[EL_MEM]) >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  `arg_type_fits (lowered_value_type cenv (EL i args)) (expr_type (EL i args))` by
    (irule copy_lowered_fits_mods >> goal_assum (drule_at Any) >>
     qexistsl_tac [`cx`,`es`,`mods`] >> simp[]) >>
  `well_formed_type (get_tenv cx) (expr_type (EL i args))` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >>
     irule well_typed_expr_type_well_formed >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env es`
       (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
     metis_tac[consistent_variable_type_well_formed]) >>
  qpat_assum `well_formed_type _ _` (strip_assume_tac o REWRITE_RULE [well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  qpat_assum `LIST_REL (\e v. value_runtime_typed _ _ _) args vs`
    (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def] o BETA_RULE) >>
  rename1 `evaluate_type env.type_defs (lowered_value_type cenv (EL i args)) = SOME tv` >>
  rename1 `evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ftv` >>
  `evaluate_type (get_tenv cx) (lowered_value_type cenv (EL i args)) = SOME tv` by
    (qpat_assum `env.type_defs = get_tenv cx` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `value_has_type ftv (EL i vs)` by
    (irule (cj 1 arg_type_fits_value_has_type) >>
     rpt (goal_assum (drule_at Any))) >>
  qexistsl_tac [`tv`,`ftv`] >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   (qpat_assum `EL i tys = _` SUBST1_TAC >>
    qpat_assum `EL i (MAP SND params) = _` SUBST1_TAC >> first_assum ACCEPT_TAC))
QED

Resume compile_raise_custom_frag_full_mods[tuple_run]:
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid u /\ storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 u /\ immutable_frame_mods func cenv cx mid u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then (strip_assume_tac o BETA_RULE o REWRITE_RULE [extcall_positional_post_mods_def])) >>
     asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`sa` |-> `se`, `sb` |-> `sm`, `sc` |-> `ss`, `sd` |-> `st`,
           `out` |-> `encoded`, `ret` |-> `d`, `ce` |-> `cenv`,
           `shared` |-> `buf`, `bs` |-> `selector`, `rows` |-> `ZIP (saved,tys)`,
           `ee` |-> `mid`, `s` |-> `u`, `G` |-> `G1`, `tn` |-> `tn1`,
           `pos` |-> `sa`, `kw_es` |-> `[]:expr list`,
           `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] ext_tuple_payload_mods) >>
  (impl_tac >- (rpt conj_tac >>
    ((first_assum ACCEPT_TAC) ORELSE
     (qexists_tac `hz` >> first_assum ACCEPT_TAC) ORELSE suspend "tuple_inputs"))) >>
  disch_then (qx_choosel_then [`root`,`dp`,`p`,`z`,`Gz`,`tz`] (map_every assume_tac o CONJUNCTS)) >>
  suspend "payload_finish"
QED

Resume compile_raise_custom_frag_full_mods[tuple_inputs]:
  rpt disch_tac >>
  qx_gen_tac `i` >> strip_tac >>
  `LENGTH saved = LENGTH tys` by decide_tac >>
  `LENGTH (ZIP (saved,tys)) = LENGTH tys` by
    (irule (cj 2 (SPEC_ALL LENGTH_ZIP)) >> first_assum ACCEPT_TAC) >>
  `i < LENGTH tys` by decide_tac >>
  `i < LENGTH args` by decide_tac >>
  `i < LENGTH vs` by decide_tac >>
  qpat_assum `!j. j < LENGTH tys ==> ?tv ftv. _`
    (qspec_then `i` (drule_then strip_assume_tac)) >>
  rename1 `evaluate_type (get_tenv cx) (EL i tys) = SOME tv` >>
  qexistsl_tac [`EL i args`,`EL i saved`,`EL i tys`,`EL i vs`,`tv`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule EL_ZIP >> decide_tac)
  >- (simp_tac bool_ss [Abbr `tys`] >> irule EL_MAP >> first_assum ACCEPT_TAC)
  >- (qpat_assum `!ty tv. evaluate_type _ ty = SOME tv ==> _`
        (drule_then ACCEPT_TAC))
  >- (`type_memory_bytes cenv (EL i tys) = type_memory_size tv` by
        (qpat_assum `!ty tv. evaluate_type _ ty = SOME tv ==> _` (drule_then ACCEPT_TAC)) >>
      `type_alloc_ok cenv (EL i tys)` by
        (qpat_assum `EVERY (type_alloc_ok cenv) tys`
          (mp_tac o Q.SPEC `i` o REWRITE_RULE [EVERY_EL]) >>
         disch_then (drule_then ACCEPT_TAC)) >>
      `type_memory_bytes cenv (EL i tys) < 2**64` by
        (Cases_on `is_word_type (EL i tys)`
         >- (drule (cj 3 (SPEC_ALL word_type_dec_sizes)) >>
             disch_then (qspec_then `cenv` SUBST1_TAC) >> simp[]) >>
         qpat_assum `type_alloc_ok cenv (EL i tys)` mp_tac >>
         simp_tac bool_ss [type_alloc_ok_def] >> disch_then drule >> simp[]) >>
      decide_tac)
  >- (qpat_assum `ats = _` SUBST1_TAC >>
      simp_tac bool_ss [abiDecoderMembersTheory.vyper_to_abi_types_MAP] >>
      irule EL_MAP >> first_assum ACCEPT_TAC)
  >- (drule vyper_to_abi_list_EL >>
      disch_then (qspec_then `i` (drule_then ACCEPT_TAC) o cj 3)) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> extcall_positional_post_mods F mods DF lo d ctx func cenv cx env [] args saved sa se es s0 G0 tn0 H (INL vs) mid G1 tn1 u`
    (qspec_then `H` (drule_then
      (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11, UNWIND_THM2] o BETA_RULE o
       REWRITE_RULE [extcall_positional_post_mods_def]))) >>
  `LENGTH args = LENGTH saved` by decide_tac >>
  `LENGTH (ZIP (args,saved)) = LENGTH args` by
    (irule (cj 1 (SPEC_ALL LENGTH_ZIP)) >> first_assum ACCEPT_TAC) >>
  `i < LENGTH (ZIP (args,saved))` by decide_tac >>
  `EL i (ZIP (args,saved)) = (EL i args,EL i saved)` by
    (irule EL_ZIP >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `LIST_REL (\(e,sv) v. ext_pos_saved_row_mods _ _ _ _ _ _ H e sv v _ _ _ _) (ZIP (args,saved)) vs`
    (mp_tac o Q.SPEC `i` o CONJUNCT2 o REWRITE_RULE [LIST_REL_EL_EQN]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL i (ZIP (args,saved)) = _` (fn th => simp_tac bool_ss [th,pairTheory.UNCURRY,pairTheory.FST,pairTheory.SND])
QED

Resume compile_raise_custom_frag_full_mods[payload_finish]:
  qhdtm_assum `ext_packing_endpoint_mods`
    (strip_assume_tac o REWRITE_RULE [ext_packing_endpoint_mods_def]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel H _ _ _ _ _ z /\ _`
    (qspec_then `hz` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then strip_assume_tac >>
  `alloca_inv z` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `p + n <= z.vs_alloca_next` by
    (drule_all alloca_site_registered_below >> disch_then ACCEPT_TAC) >>
  `z.vs_alloca_next < dimword (:256)` by
    (irule alloca_room_next_lt >> qexistsl_tac [`ctx`,`func`] >>
     qpat_assum `stmt_state_rel hz ctx func cenv cx mid z`
       (ACCEPT_TAC o MATCH_MP stmt_state_rel_alloca_room)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  `allocas_from lo z` by
    (qpat_assum `ghost_inv_at_mods (DF hz) lo d cenv cx mid Gz tz z`
      (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >> first_assum ACCEPT_TAC) >>
  `w2n (n2w p:256 word) = p` by
    (`p < dimword (:256)` by decide_tac >> simp[w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  `p + 32 + LENGTH bytes <= z.vs_alloca_next` by decide_tac >>
  `ptr_covers Gz tz root z (32 + LENGTH bytes)` by
    (irule ptr_covers_mono >> qexists_tac `n` >>
     reverse conj_tac >- first_assum ACCEPT_TAC >> decide_tac) >>
  `read_memory (p + 32) (LENGTH bytes) z = bytes` by
    (simp_tac bool_ss [read_memory_eq_mem_bytes_at] >> first_assum ACCEPT_TAC) >>
  `read_memory (p + 28) (4 + LENGTH bytes) z = selector ++ bytes` by
    (`p + 28 + 4 = p + 32` by decide_tac >>
     once_rewrite_tac[read_memory_split] >>
     qpat_assum `p + 28 + 4 = p + 32` SUBST1_TAC >> asm_rewrite_tac[]) >>
  qpat_assum `buf.buf_operand = Var root` (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
  irule custom_error_terminal_outcome_mods >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gz`,`en`,`sr`,`sn`,`selector ++ bytes`,`sb`,`SOME encoded`,
                 `LENGTH bytes`,`len`,`offset`,`root`,`z`,`tz`,`n2w p`] >>
  simp_tac bool_ss [optionTheory.option_case_def] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (qpat_assum `w2n (n2w p:256 word) = p` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!D. gas_origin_ptr_path (D,lo,_,ctx,func,PG) _ [] (OK z,Gz,tz)` irule
QED

Finalise compile_raise_custom_frag_full_mods

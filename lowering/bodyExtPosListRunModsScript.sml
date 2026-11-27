(* Linked positional arguments, with all saved rows at one exit. *)
Theory bodyExtPosListRunMods
Ancestors
  bodyExtPosListFoldMods bodyExtPosSavedRowMods bodyExtPosWordHeadMods
  bodyExtPosAggregateHeadMods bodyExtPosRowTransportMods bodyExtNoncopySourceMods
  bodyExtSavedCtorReadMods bodyFullExtCallSavedOperand
  bodyWriteSubscriptSourceMods bodyBranchCellFrameMods bodyInvCodeProps
  bodyFullHashKeccakFixed gasShadowCompileStmtHelpers gasShadowCompileConvert
  gasOutcomeFullPostMods gasOutcomeFullPostPathMods fragGasPathFrameMem
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  loweringPosts loweringStateRelDefs vyperStorageFootprint
  exprLoweringProps exprLowering gasShadowCompileHelpers exprSimHypsDefs
  stmtLoweringMono exprOperandVar bodyExtNoncopySigReachedFrameMods compileExprAllocaFresh
  vyperReadOnlyEval whitelistCheckerDecls constSubstCorrect vyperTypeContract vyperStorageTrace
  vyperInterpreter vyperState finite_map list compileEnv gasShadowState
  fragGasOriginPtr wordArgsPtr exprSimWordArgs exprReasonOperand
  gasOriginPtrLabels bodyFullIfExpReach gasExplicitSites fragExec stmtSimProps
  bodyCopyReadPhysicalTypeMods abiEncodeArgsCase aggregateEvaluatedLayout
  exprBodyPreProps exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeExprResult
  vyperTypeEvalSoundness vyperExprNoControl
  gasContext allocLimits vyperAST exprSimDefs words exprSimHyps vyperArith context
Libs horizonTypeLib monadsyntax

Definition extcall_positional_post_mods_def:
  extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
    kw_es xs svs sa sb es s0 G0 tn0 =
    \H res ee G tn t. ?vs.
      res = INL vs /\ LENGTH svs = LENGTH xs /\
      LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx kw_es sa sb H
         e sv v ee G tn t) (ZIP (xs,svs)) vs /\
      EVERY (\sv. !x. vv_operand sv = Var x ==> not_fresh_at sb x) svs /\
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv sb t /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      wb_frame cenv es ee sa s0 t /\
      (keep_pure /\ ~EXISTS expr_has_effect xs ==> pure_frame cenv func es sa s0 t) /\
      MAP FDOM ee.scopes = MAP FDOM es.scopes /\
      expr_sim_inv_mods mods cenv cx env ee /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
End

Theorem positional_frame_gas_obs[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- simp[immutable_frame_mods_def, immutables_rel_mods_def,
          immutables_rel_def, immutable_alloca_sep_mods_def, immutable_alloca_sep_def]
  >- simp[ghost_inv_at_mods_def]
  >> irule storage_well_formed_on_backends >> simp[]
QED

Theorem positional_nil_outcome[local]:
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  expr_sim_inv_mods mods cenv cx env es /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG)
    mods cx st0 (eval_exprs cx []) (es,s0,G0,tn0)
    (\H res ee G tn t. extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
       kw_es [] [] sa sa es s0 G0 tn0 H res ee G tn t /\ t.vs_labels = s0.vs_labels) R
Proof
  strip_tac >>
  irule (Q.INST [`res` |-> `INL ([] : value list)`, `ee` |-> `es`,
                 `t` |-> `s0`, `G'` |-> `G0`, `tn'` |-> `tn0`]
    (INST_TYPE [alpha |-> ``:value list``] gas_outcome_full_mods_pure)) >>
  simp[evaluate_def, return_def] >>
  qexistsl_tac [`G0`,`s0`,`tn0`] >>
  simp[gas_origin_ptr_path_rules, extcall_positional_post_mods_def,
       ghost_kept_at_refl, wb_frame_refl, positional_frame_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[]
QED

(* Positional compilation keeps the same operand and snapshot at both cuts. *)
Theorem positional_compile_cons[local]:
  gas_shadow_state sa shadow_sa /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) (e::xs)) (e::xs) sa = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr (e::xs)))
    (MAP gas_shadow_expr (e::xs)) shadow_sa = (svs,shadow_sb) ==>
  ?vv si shadow_si sv sm shadow_sm rest.
    compile_expr cenv (expr_type e) e sa = (vv,si) /\
    compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
      (vv,shadow_si) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv (xs ++ kw_es))
      (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sm) /\
    compile_snapshot_vv cenv (exprs_can_mutate cenv (xs ++ kw_es))
      (ext_call_arg_value (lowered_value_type cenv e) vv) shadow_si = (sv,shadow_sm) /\
    gas_shadow_state si shadow_si /\ gas_shadow_state sm shadow_sm /\ svs = sv::rest /\
    compile_ext_call_args compile_expr cenv kw_es
      (MAP (lowered_value_type cenv) xs) xs sm = (rest,sb) /\
    compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
      (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
      (MAP gas_shadow_expr xs) shadow_sm = (rest,shadow_sb)
Proof
  strip_tac >>
  qabbrev_tac `copy = exprs_can_mutate cenv (xs ++ kw_es)` >>
  `exprs_can_mutate cenv (MAP gas_shadow_expr xs ++ MAP gas_shadow_expr kw_es) = copy` by
    (pure_rewrite_tac[GSYM MAP_APPEND, gas_shadow_expr_can_mutate] >> simp[Abbr `copy`]) >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr cenv (expr_type e) e sa = (vv,si)` >>
  Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa` >>
  rename1 `compile_expr _ _ (gas_shadow_expr e) shadow_sa = (shvv,shadow_si)` >>
  `shvv = vv /\ gas_shadow_state si shadow_si` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     qpat_assum `gas_shadow_compiles (compile_expr _ _ _) _`
       (mp_tac o Q.SPECL [`sa`, `shadow_sa`] o REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >>
  qpat_x_assum `shvv = vv` SUBST_ALL_TAC >>
  qabbrev_tac `snap = compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv)` >>
  `gas_shadow_compiles snap snap` by simp[Abbr `snap`, gas_shadow_compiles_snapshot_vv] >>
  Cases_on `snap si` >> rename1 `snap si = (sv,sm)` >>
  Cases_on `snap shadow_si` >> rename1 `snap shadow_si = (shsv,shadow_sm)` >>
  `shsv = sv /\ gas_shadow_state sm shadow_sm` by
    (qpat_assum `gas_shadow_compiles snap snap`
       (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     disch_then (qspecl_then [`si`,`shadow_si`] mp_tac) >> simp[]) >>
  qpat_x_assum `shsv = sv` SUBST_ALL_TAC >>
  Cases_on `compile_ext_call_args compile_expr cenv kw_es
      (MAP (lowered_value_type cenv) xs) xs sm` >>
  rename1 `compile_ext_call_args _ _ kw_es _ xs sm = (rest,sr)` >>
  Cases_on `compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
      (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs)) (MAP gas_shadow_expr xs) shadow_sm` >>
  rename1 `compile_ext_call_args _ _ (MAP _ kw_es) _ (MAP _ xs) shadow_sm = (shrest,shadow_sr)` >>
  qpat_x_assum `compile_ext_call_args _ _ kw_es _ (e::xs) sa = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [listTheory.MAP]) >>
  qpat_x_assum `compile_ext_call_args _ _ (MAP _ kw_es) _ _ shadow_sa = _`
    (mp_tac o ONCE_REWRITE_RULE [compile_ext_call_args_def] o REWRITE_RULE [listTheory.MAP]) >>
  fs[comp_bind_def, comp_return_def, Abbr `snap`, Abbr `copy`] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem positional_forced_admissible[local]:
  expr_body_pre_mods mods cenv cx env e es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `expr_body_pre_mods mods cenv cx env e (es with gas_obs := gs)` by simp[] >>
  qpat_assum `expr_body_pre_mods _ _ _ _ _ (_ with gas_obs := _)`
    (strip_assume_tac o MATCH_MP expr_body_pre_mods_runtime_typing) >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  `no_type_error_result (INR y : value + vyperState$exception)` by
    (qpat_assum `bind _ _ _ = (INR _,_)`
       (mp_then Any mp_tac (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound)) >>
     disch_then (qspec_then `env` mp_tac) >>
     fs[runtime_consistent_def,gas_obs_type_invariants] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `no_control_exc y` by
    (qpat_assum `bind _ _ _ = (INR _,_)` mp_tac >>
     simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 eval_expr_no_control,read_result_no_control]) >>
  Cases_on `y` >> gvs[expr_res_ok_def,no_control_exc_def,no_type_error_result_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[]
QED

Theorem positional_nonword_layout[local]:
  expr_body_pre_mods mods cenv cx env e es /\ ~is_word_type (expr_type e) /\
  compile_expr cenv (expr_type e) e sa = (vv,si) ==>
  ~is_word_type (lowered_value_type cenv e) /\
  type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
  ~is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then assume_tac copy_lowered_fits_mods >>
  `~is_word_type (lowered_value_type cenv e)` by metis_tac[arg_type_fits_word_type] >>
  `type_alloc_ok cenv (expr_type e)` by
    (irule alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_mods_def]) >>
  `type_memory_bytes cenv (lowered_value_type cenv e) < 2 ** 64` by
    (drule_then (qspec_then `cenv` assume_tac) (GEN_ALL (cj 1 abi_args_fits_memory_bytes)) >>
     gvs[type_alloc_ok_def] >> decide_tac) >>
  simp[] >> conj_tac >- (irule lt_dimword_256 >> qexists `64` >> simp[]) >>
  `reason_uniform_shape compile_expr cenv (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >> fs[expr_sim_inv_mods_def]) >>
  `vv_type vv = expr_type e \/ vv_type vv = lowered_value_type cenv e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[reason_result_shape_def,vv_type_def]) >>
  Cases_on `vv` >> gvs[ext_call_arg_value_def,vv_type_def] >>
  CASE_TAC >> simp[vv_type_def]
QED

Theorem positional_word_row[local]:
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  compile_snapshot_vv cenv copy (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sm) /\
  is_word_type (lowered_value_type cenv e) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  sv = StackValue (lowered_value_type cenv e) op /\
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv ee t /\
    vv_at cenv cx (lowered_value_type cenv e) sa sm ee raw sv t /\
    ptr_vv_ok cx (lowered_value_type cenv e) raw sv ee G tn t /\
    vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) ee raw sv t) /\
  vv_storage_live H cx sv ee t ==>
  ext_pos_saved_row_mods lo cenv cx kw_es sa sm H e sv v ee G tn t
Proof
  strip_tac >>
  `ci_mono si sm` by
    (qspecl_then [`cenv`,`copy`,`ext_call_arg_value (lowered_value_type cenv e) vv`,`si`]
       mp_tac ci_mono_compile_snapshot_vv >> simp[]) >>
  `is_word_type (vv_type (ext_call_arg_value (lowered_value_type cenv e) vv))` by
    (CCONTR_TAC >>
     qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     Cases_on `copy` >> simp[compile_snapshot_vv_def,comp_bind_def,comp_return_def]
     >- (pairarg_tac >> simp[]) >>
     strip_tac >> fs[vv_type_def]) >>
  `compile_snapshot_vv cenv T (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sm)` by
    (qpat_x_assum `compile_snapshot_vv _ copy _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def]) >>
  qpat_x_assum `sv = StackValue _ _` SUBST_ALL_TAC >>
  simp[ext_pos_saved_row_mods_def, vv_location_def] >>
  qexistsl_tac [`sa`,`si`,`sm`,`vv`,`raw`,`T`] >> fs[ci_mono_def]
QED

fun pos_exit ty = inst [alpha |-> ty] ``\(H : (bool # bytes32 # type_value) list # num list)
    (res : 'a + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;
val pos_head_exit = pos_exit ``:value``;

val head_source = ``bind (eval_expr cx e) (read_result cx)``;

val head_physical = ``
  ext_pos_saved_row_mods lo cenv cx (xs ++ kw_es) sa sm
    (H : (bool # bytes32 # type_value) list # num list) e sv v mid G1 tn1 t /\
  stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
  storage_well_formed_on cx mid (FST H) /\ return_buf_frame d cenv sm t /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  wb_frame cenv es mid sa s0 t /\ (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)``;

val head_compile = ``
  compile_expr cenv (expr_type e) e sa = (vv,si) /\
  compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e) shadow_sa =
    (vv,shadow_si) /\
  compile_snapshot_vv cenv (exprs_can_mutate cenv (xs ++ kw_es))
    (ext_call_arg_value (lowered_value_type cenv e) vv) si = (sv,sm) /\
  compile_snapshot_vv cenv (exprs_can_mutate cenv (xs ++ kw_es))
    (ext_call_arg_value (lowered_value_type cenv e) vv) shadow_si = (sv,shadow_sm)``;

val pos_common = ``
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_inst_ids_distinct func /\
  (!H : (bool # bytes32 # type_value) list # num list.
     dead_lo_ok_mods H (DF H) lo cenv cx)``;

val pos_start = ``
  gas_shadow_state sa shadow_sa /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H : (bool # bytes32 # type_value) list # num list.
     valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
     storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

Theorem positional_head_outcome:
  ^pos_common /\ ^pos_start /\ ^head_compile /\
  body_const_cells_agree_mods mods cx env es /\ expr_body_pre_mods mods cenv cx env e es /\
  body_expr_full_ok_mods mods exps cx e /\
  gas_shadow_state si shadow_si /\ gas_shadow_state sm shadow_sm /\
  fn_has_code sa si func /\ fn_has_code si sm func /\ fn_has_code sa sm func /\
  fn_has_code shadow_sa shadow_si shadow_func /\ fn_has_code shadow_sa shadow_sm shadow_func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 ^head_source (es,s0,G0,tn0)
    (\H res mid G1 tn1 t. ?v. res = INL v /\ ^head_physical) (^pos_head_exit)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac positional_forced_admissible >>
  `arg_type_fits (lowered_value_type cenv e) (expr_type e)` by
    (drule_then assume_tac expr_body_pre_mods_inv >>
     drule_then assume_tac expr_body_pre_mods_well_typed >>
     drule_all_then ACCEPT_TAC copy_lowered_fits_mods) >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >>
  suspend "aggregate"
QED

Resume positional_head_outcome[word]:
  `is_word_type (lowered_value_type cenv e)` by metis_tac[arg_type_fits_word_type] >>
  `gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cenv.ce_modules cx st0 ^head_source (es,s0,G0,tn0)
     (\H res mid G1 tn1 t. ?v op. res = INL v /\ sv = StackValue (lowered_value_type cenv e) op /\
       (?raw. read_result cx raw mid = (INL v,mid) /\
        vv_holds_mods cenv cx (lowered_value_type cenv e) raw sv mid t /\
        vv_at cenv cx (lowered_value_type cenv e) sa sm mid raw sv t /\
        ptr_vv_ok cx (lowered_value_type cenv e) raw sv mid G1 tn1 t /\
        vv_store_bound cx (lowered_value_type cenv e) (lowered_value_type cenv e) mid raw sv t) /\
       vv_storage_live H cx sv mid t /\ stmt_state_rel H ctx func cenv cx mid t /\
       immutable_frame_mods func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
       return_buf_frame d cenv sm t /\ ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ alloca_history func t /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
       (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
       ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
       wb_frame cenv es mid sa s0 t /\ (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
       (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
       (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b))
     (^pos_head_exit)` by
    (irule (GEN_ALL (cj 4 (UNDISCH ext_pos_word_head_mods) |> DISCH_ALL)) >> simp[] >>
     conj_tac >- (rpt strip_tac >>
       qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _` (drule_then ACCEPT_TAC)) >>
     conj_tac >- (gen_tac >> disch_tac >> first_x_assum drule >> simp[]) >>
     conj_tac >- (qexistsl_tac [`exprs_can_mutate cenv (xs ++ kw_es)`,
        `shadow_func`,`shadow_sa`,`shadow_si`,`shadow_sm`] >> simp[]) >>
     qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[]) >>
  qpat_assum `cenv.ce_modules = mods` (SUBST_ALL_TAC o SYM) >>
  irule gas_outcome_full_mods_post_source >>
  qpat_assum `gas_outcome_full_mods _ _ _ _ ^head_source _ _ _` (irule_at Any) >>
  BETA_TAC >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `?v op. _` (qx_choosel_then [`v`,`op`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `sv = StackValue _ _` SUBST_ALL_TAC >>
  qexists_tac `v` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!fn inst z. frag_reachable ctx func t fn inst z ==> _` (drule_then ACCEPT_TAC)) >>
  irule positional_word_row >>
  qpat_assum `compile_expr cenv _ e sa = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ si = _` (irule_at Any) >>
  simp[]
QED

Resume positional_head_outcome[aggregate]:
  drule_all_then strip_assume_tac positional_nonword_layout >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi_mods] >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es` by
    (qpat_x_assum `body_expr_full_ok_mods _ _ _ _` mp_tac >>
     rewrite_tac[Once body_expr_full_ok_mods_def] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ _`
       (qspecl_then [`DF`,`lo`,`d`,`PG`,`src`,`tops`,`ctx`,`shadow_ctx`,
                     `func`,`shadow_func`,`cenv`,`env`,`expr_type e`,`es`] mp_tac) >> simp[]) >>
  qpat_assum `cenv.ce_modules = mods` (SUBST_ALL_TAC o SYM) >>
  irule ext_pos_aggregate_head_mods >> simp[] >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`tops`,`src`,`shadow_si`,`shadow_sa`,`cenv.ce_modules`,`exps`,`env`] >> simp[] >>
  conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  gen_tac >> disch_tac >> first_x_assum drule >> simp[]
QED

Finalise positional_head_outcome[local]

Theorem positional_row_suffix[local]:
  ext_pos_saved_row_mods lo cenv cx (xs ++ kw_es) sa sm
    (H : (bool # bytes32 # type_value) list # num list) e sv v mid G1 tn1 t /\
  ci_mono sm sb /\ wb_frame cenv mid ee sm t u /\
  ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2 /\
  (!x w. not_fresh_at sm x /\ lookup_var x t = SOME w ==> lookup_var x u = SOME w) /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  t.vs_alloca_next <= u.vs_alloca_next /\ u.vs_labels = t.vs_labels /\
  MAP FDOM ee.scopes = MAP FDOM mid.scopes /\
  (~exprs_can_mutate cenv xs ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
      (!tr. get_storage cx ee tr = get_storage cx mid tr)) /\
  stmt_state_rel H ctx func cenv cx mid t /\ stmt_state_rel H ctx func cenv cx ee u /\
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env mid /\
  immutable_frame_mods func cenv cx ee u /\
  ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u /\ dead_lo_ok_mods H (DF H) lo cenv cx ==>
  ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G2 tn2 u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ext_pos_saved_row_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (CONJUNCTS_THEN2 (qx_choosel_then [`si`,`sm'`,`ss`,`vv`,`raw`,`copy`]
       (map_every assume_tac o CONJUNCTS)) (map_every assume_tac o CONJUNCTS) o
     PURE_REWRITE_RULE [ext_pos_saved_row_mods_def]) >>
  irule ext_pos_row_transport_mods >>
  qpat_assum `compile_expr cenv _ e _ = _` (irule_at Any) >>
  qpat_assum `compile_snapshot_vv _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `wb_frame cenv mid ee sm t u` (irule_at Any) >>
  qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env mid` (irule_at Any) >>
  qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`tn1`,`raw`,`func`,`G1`] >> simp[ci_mono_def] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> disch_tac >>
    pure_once_rewrite_tac [arithmeticTheory.ADD_COMM] >>
    irule (INST_TYPE [``:'a`` |-> ``:256``] ext_saved_ctor_read_linked) >>
    qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
    qpat_assum `expr_sim_inv_mods mods cenv cx env mid` (irule_at Any) >>
    qpat_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` (irule_at Any) >>
    qpat_assum `immutable_frame_mods func cenv cx ee u` (irule_at Any) >>
    simp[] >> qexistsl_tac [`ty`,`raw'`,`p`,`H`] >> simp[]) >>
  fs[exprs_can_mutate_append,ci_mono_def]
QED

Theorem positional_rows_weaken[local]:
  ci_mono sa sm /\
  LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx kw_es sm sb H e sv v ee G tn u) rows vs ==>
  LIST_REL (\(e,sv) v. ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G tn u) rows vs
Proof
  strip_tac >> irule LIST_REL_mono >> first_assum (irule_at Any) >>
  PairCases >> simp[ext_pos_saved_row_mods_def] >> gen_tac >>
  disch_then (CONJUNCTS_THEN2
    (qx_choosel_then [`si`,`sm'`,`ss`,`vv`,`raw`,`copy`] (map_every assume_tac o CONJUNCTS))
    kall_tac) >>
  `sa.cs_next_var <= si.cs_next_var /\ sa.cs_next_id <= si.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  qexistsl_tac [`si`,`sm'`,`ss`,`vv`,`raw`,`copy`] >> simp[]
QED

fun pos_exit ty = inst [alpha |-> ty] ``\(H : (bool # bytes32 # type_value) list # num list)
    (res : 'a + vyperState$exception) ee (gt : (string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)``;
val pos_head_exit = pos_exit ``:value``;

val head_source = ``bind (eval_expr cx e) (read_result cx)``;

val head_physical = ``
  ext_pos_saved_row_mods lo cenv cx (xs ++ kw_es) sa sm
    (H : (bool # bytes32 # type_value) list # num list) e sv v mid G1 tn1 t /\
  stmt_state_rel H ctx func cenv cx mid t /\ immutable_frame_mods func cenv cx mid t /\
  storage_well_formed_on cx mid (FST H) /\ return_buf_frame d cenv sm t /\
  ghost_inv_at_mods (DF H) lo d cenv cx mid G1 tn1 t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\ alloca_history func t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  wb_frame cenv es mid sa s0 t /\ (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)``;

val pos_tail_exit = pos_exit ``:value list``;
val pos_tail_Q = ``\mid t G1 tn1
    (H : (bool # bytes32 # type_value) list # num list) vs ee G2 tn2 u.
  extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
    kw_es xs rest sm sb mid t G1 tn1 H (INL vs) ee G2 tn2 u /\ u.vs_labels = t.vs_labels``;

Theorem ext_pos_list_run_mods:
  body_exprs_full_ok_mods mods exps cx xs /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_sim_inv_mods mods cenv cx env es /\
  exports_ok cx.layouts cx.txn.target mods exps /\
  IS_SOME (check_contract F cx.layouts cx.txn.target mods) /\
  (!e st. MEM e xs /\
    expr_sim_inv_mods mods cenv cx env st ==>
      expr_body_pre_mods mods cenv cx env e st) /\
  compile_ext_call_args compile_expr cenv kw_es
    (MAP (lowered_value_type cenv) xs) xs sa = (svs,sb) /\
  compile_ext_call_args compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr kw_es)
    (MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs))
    (MAP (gas_shadow_expr) xs) shadow_sa = (svs,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
  fn_has_code shadow_sa shadow_sb shadow_func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
    dalloca_fmp_headroom inst s) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full_mods
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    mods cx st0 (eval_exprs cx xs) (es,s0,G0,tn0)
    (extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
      kw_es xs svs sa sb es s0 G0 tn0)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  map_every qid_spec_tac [`tn0`,`G0`,`s0`,`es`,`shadow_sa`,`sa`,`svs`] >>
  Induct_on `xs` >> rpt gen_tac >> strip_tac
  >- (gvs[compile_ext_call_args_def, comp_return_def] >>
      irule gas_outcome_full_mods_post_source >>
      qexistsl_tac [`\H res ee G tn t.
        extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
          kw_es [] [] sa sa es s0 G0 tn0 H res ee G tn t /\ t.vs_labels = s0.vs_labels`,
        `\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)`] >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >> gvs[])
      >- (conj_tac
          >- (rpt gen_tac >> strip_tac >> simp[])
          >- (irule positional_nil_outcome >> simp[] >>
              rpt gen_tac >> disch_tac >>
              qpat_assum `!H. valid_horizon _ _ H _ ==> _`
                (qspec_then `H` (drule_then strip_assume_tac)) >> simp[])))
  >- (rename1 `body_exprs_full_ok_mods mods exps cx (e::xs)` >>
      drule_all_then strip_assume_tac positional_compile_cons >>
      `ci_mono sa si /\ ci_mono shadow_sa shadow_si` by
        (conj_tac >> drule_then (ACCEPT_TAC o cj 1) compile_expr_alloca_fresh) >>
      `ci_mono si sm /\ ci_mono shadow_si shadow_sm` by
        (conj_tac
         >- (qspecl_then [`cenv`,`exprs_can_mutate cenv (xs ++ kw_es)`,
                 `ext_call_arg_value (lowered_value_type cenv e) vv`,`si`]
               mp_tac ci_mono_compile_snapshot_vv >> simp[])
         >- (qspecl_then [`cenv`,`exprs_can_mutate cenv (xs ++ kw_es)`,
                 `ext_call_arg_value (lowered_value_type cenv e) vv`,`shadow_si`]
               mp_tac ci_mono_compile_snapshot_vv >> simp[])) >>
      `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by metis_tac[ci_mono_trans] >>
      `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
        (qspecl_then [`xs`,`MAP (lowered_value_type cenv) xs`,`compile_expr`,`cenv`,`kw_es`,`sm`]
           mp_tac ci_mono_compile_ext_call_args >>
         qspecl_then [`MAP gas_shadow_expr xs`,`MAP (lowered_value_type cenv) (MAP gas_shadow_expr xs)`,
           `compile_expr`,`gas_shadow_env T cenv`,`MAP gas_shadow_expr kw_es`,`shadow_sm`]
           mp_tac ci_mono_compile_ext_call_args >> simp[cj 1 ci_mono_compile_expr_sa]) >>
      `fn_has_code sa sm func /\ fn_has_code sm sb func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      `fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      `fn_has_code sa si func /\ fn_has_code si sm func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      `fn_has_code shadow_sa shadow_si shadow_func /\ fn_has_code shadow_si shadow_sm shadow_func` by
        (irule fn_has_code_split >> fs[ci_mono_def]) >>
      `local_ptrs_reserved cenv sm` by
        (irule local_ptrs_reserved_next_var >> fs[ci_mono_def] >> qexists_tac `sa` >> simp[]) >>
      qpat_x_assum `body_exprs_full_ok_mods mods exps cx (e::xs)`
        (strip_assume_tac o REWRITE_RULE [body_exprs_full_ok_mods_def]) >>
      `expr_body_pre_mods mods cenv cx env e es` by simp[] >>
      irule ext_pos_list_fold_mods >>
      qexistsl_tac [`\H v mid G1 tn1 t. ^head_physical`,`^pos_head_exit`,
        `^pos_tail_Q`,`^pos_tail_exit`] >>
      rpt conj_tac
      >- (rpt gen_tac >> strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
          conj_tac
          >- (pop_assum kall_tac >> pop_assum kall_tac >>
              irule (INST_TYPE [``:'a`` |-> ``:value``, ``:'b`` |-> ``:value list``]
                bodyFullTargetSubscriptTheory.expr_exit_INR_retype) >>
              pop_assum ACCEPT_TAC)
          >- (pop_assum kall_tac >>
              irule (iffLR (INST_TYPE [``:'a`` |-> ``:value``, ``:'b`` |-> ``:value list``]
                haltExitProjTheory.halt_exit_INR_type)) >>
              pop_assum ACCEPT_TAC))
      >- (rpt gen_tac >> strip_tac >>
          irule gas_outcome_full_mods_post_path >>
          qexists_tac `\H res ee G2 tn2 u. ?vs. res = INL vs /\
            extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
              kw_es xs rest sm sb mid t G1 tn1 H (INL vs) ee G2 tn2 u` >>
          BETA_TAC >>
          (conj_tac >- (rpt gen_tac >> strip_tac >>
            drule_then assume_tac gas_origin_ptr_path_preserves_labels >> simp[])) >>
          irule gas_outcome_full_mods_post_source >>
          qexistsl_tac [`extcall_positional_post_mods keep_pure mods DF lo d ctx func cenv cx env
              kw_es xs rest sm sb mid t G1 tn1`, `^pos_tail_exit`] >>
          reverse (rpt conj_tac)
          >- (`valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
                fs[storage_trace_domain_def] >>
              qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
                (assume_tac o BETA_RULE) >>
              qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
                (qspec_then `storage_trace_horizon mid.storage_trace`
                  (drule_then (map_every assume_tac o CONJUNCTS))) >>
              `expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid` by
                (`expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs)` by simp[] >>
                 `body_const_cells_agree_mods mods cx env (es with gas_obs := obs)` by simp[] >>
                 drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] write_index_read_source_mods) >> simp[]) >>
              `body_exprs_full_ok_mods mods exps cx xs` by
                (qpat_assum `(?s tv t s1 v t1. _) ==> body_exprs_full_ok_mods _ _ _ _` match_mp_tac >>
                 qpat_assum `^head_source _ = _` mp_tac >>
                 simp[NoAsms,bind_def,AllCaseEqs()] >> strip_tac >>
                 qpat_x_assum `_ = INL _` SUBST_ALL_TAC >>
                 goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
                 goal_assum (drule_at (Pat `read_result _ _ _ = _`)) >> simp[]) >>
              qpat_assum `!svs sa shadow_sa es s0 G0 tn0. _ ==> gas_outcome_full_mods _ _ _ _ _ _ _ _`
                (qspecl_then [`rest`,`sm`,`shadow_sm`,`mid`,`t`,`G1`,`tn1`] match_mp_tac) >>
              simp[] >> rpt conj_tac
              >~ [`not_fresh_at sm _`]
              >- (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[])
              >~ [`not_fresh_at sm _`]
              >- (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[])
              >~ [`dalloca_fmp_headroom _ _`]
              >- (rpt strip_tac >>
                  qpat_assum `!fn inst z. frag_reachable ctx func t fn inst z ==> _`
                    (drule_then ACCEPT_TAC)) >>
              rpt gen_tac >> disch_tac >>
              qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
                (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[])
          >- simp[]
          >- (rpt gen_tac >>
              simp[extcall_positional_post_mods_def] >> metis_tac[]))
      >- suspend "join"
      >- (rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def])
      >- (BETA_TAC >> irule positional_head_outcome >>
          qpat_assum `compile_expr cenv _ e sa = _` (irule_at Any) >>
          qpat_assum `compile_expr _ _ (gas_shadow_expr e) shadow_sa = _` (irule_at Any) >>
          qpat_assum `body_expr_full_ok_mods mods exps cx e` (irule_at Any) >>
          qpat_assum `module_body_inv mods src tops cenv cx` (irule_at Any) >>
          qexistsl_tac [`shadow_sm`,`shadow_func`,`env`] >> simp[] >> conj_tac
          >- (rpt strip_tac >>
              qpat_assum `!fn inst z. frag_reachable ctx func s0 fn inst z ==> _`
                (drule_then ACCEPT_TAC)) >>
          rpt strip_tac >>
          qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
            (drule_then strip_assume_tac) >> simp[]))
QED

Resume ext_pos_list_run_mods[join]:
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv_mods mods cenv cx env mid /\ body_const_cells_agree_mods mods cx env mid` by
    (`expr_body_pre_mods mods cenv cx env e (es with gas_obs := obs0)` by simp[] >>
     `body_const_cells_agree_mods mods cx env (es with gas_obs := obs0)` by simp[] >>
     drule_all_then strip_assume_tac (REWRITE_RULE [ETA_AX] write_index_read_source_mods) >> simp[]) >>
  `~exprs_can_mutate cenv xs ==> ee.scopes = mid.scopes /\ ee.immutables = mid.immutables /\
      (!tr. get_storage cx ee tr = get_storage cx mid tr)` by
    (strip_tac >>
     qpat_assum `body_const_cells_agree_mods mods cx env mid`
       (strip_assume_tac o REWRITE_RULE [body_const_cells_agree_mods_def]) >>
     `!x. MEM x xs ==> expr_body_pre_mods mods cenv cx env x mid` by simp[] >>
     `EVERY (source_body_call_supported cx) (int_calls_exprs xs)` by
       (simp[int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
        CONV_TAC (REWR_CONV EVERY_MEM) >> BETA_TAC >> rpt strip_tac >>
        qpat_assum `!x. MEM x xs ==> expr_body_pre_mods _ _ _ _ _ mid`
          (drule_then (ACCEPT_TAC o MATCH_MP expr_body_pre_mods_int_calls))) >>
     `env.fn_sigs = art.cta_fn_sigs` by fs[frame_maps_def] >>
     `EVERY (\k. IS_SOME (FLOOKUP art.cta_fn_sigs k)) (int_calls_exprs xs)` by
       (simp[int_calls_exprs_FLAT_MAP, EVERY_FLAT, EVERY_MAP] >>
        CONV_TAC (REWR_CONV EVERY_MEM) >> BETA_TAC >> rpt strip_tac >>
        qpat_assum `!x. MEM x xs ==> expr_body_pre_mods _ _ _ _ _ mid`
          (drule_then (mp_tac o MATCH_MP expr_body_pre_mods_well_typed)) >>
        disch_then (mp_tac o MATCH_MP (cj 1 well_typed_int_calls_fn_sigs)) >>
        simp[FLOOKUP_DEF]) >>
     qpat_x_assum `IS_SOME (check_contract F _ _ _)`
       (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
     drule_all_then strip_assume_tac ext_noncopy_reached_sig_suffix_frame_mods >> simp[]) >>
  qhdtm_x_assum `extcall_positional_post_mods`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [extcall_positional_post_mods_def]) >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes` by
    (qpat_assum `^head_source _ = _`
       (mp_tac o MATCH_MP stmtSimDefsTheory.eval_read_preserves_scopes_dom) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (`valid_horizon cx st0 H (mid with gas_obs := obs).storage_trace` by
       (qpat_assum `eval_exprs cx xs _ = _`
          (mp_then Any mp_tac valid_horizon_frame) >>
        simp[cj 6 evaluate_storage_trace_frame]) >>
     `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
     `storage_trace_frame ^head_source` by
       (irule storage_trace_frame_bind_all >>
        simp[cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
     `valid_horizon cx st0 H (es with gas_obs := obs0).storage_trace` by
       (qpat_assum `^head_source _ = _`
          (mp_then Any mp_tac valid_horizon_frame) >> simp[]) >>
     fs[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by fs[ci_mono_def] >>
  `ext_pos_saved_row_mods lo cenv cx kw_es sa sb H e sv v ee G2 tn2 u` by
    (irule positional_row_suffix >>
     qpat_assum `ext_pos_saved_row_mods _ _ _ (xs ++ kw_es) _ _ _ _ _ _ _ _ _ _`
       (irule_at Any) >>
     qpat_assum `ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 u` (irule_at Any) >>
     qpat_assum `contract_inv mods exps ctx cenv cx` (irule_at Any) >>
     qpat_assum `expr_sim_inv_mods mods cenv cx env mid` (irule_at Any) >>
     qexists_tac `func` >> simp[]) >>
  `LIST_REL (\(a,b) w. ext_pos_saved_row_mods lo cenv cx kw_es sa sb H a b w ee G2 tn2 u)
      (ZIP (xs,rest)) vs` by (irule positional_rows_weaken >> qexists_tac `sm` >> simp[]) >>
  `!x. vv_operand sv = Var x ==> not_fresh_at sb x` by
    (rpt strip_tac >> irule compiler_ci_mono_not_fresh >> qexists_tac `sm` >> simp[] >>
     drule_all_then irule extcall_saved_operand_not_fresh >> simp[]) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by
    (irule arithmeticTheory.LESS_EQ_TRANS >> qexists_tac `t.vs_alloca_next` >> simp[]) >>
  `wb_frame cenv es ee sa s0 u` by
    (irule (horizonTypeLib.at_horizon_named "H" wb_frame_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >>
     qpat_assum `wb_frame cenv mid ee sm t u` (irule_at Any) >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (irule (horizonTypeLib.at_horizon_named "H" ghost_kept_at_wb_trans) >>
     qpat_assum `stmt_state_rel H ctx func cenv cx es s0` (irule_at Any) >>
     qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t G2 tn2` (irule_at Any) >>
     qpat_assum `wb_frame cenv es mid sa s0 t` (irule_at Any) >> simp[]) >>
  simp[extcall_positional_post_mods_def, ZIP] >> conj_tac
  >- (strip_tac >> irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
      qexistsl_tac [`mid`,`sm`,`t`] >> simp[GSYM EVERY_NOT_EXISTS]) >>
  rpt strip_tac >> rename1 `lookup_var x u = SOME w` >>
  `not_fresh_at sm x` by (irule compiler_ci_mono_not_fresh >> qexists_tac `sa` >> simp[]) >>
  `lookup_var x t = SOME w` by simp[] >> simp[]
QED

Finalise ext_pos_list_run_mods

(* Readiness-parametric composition of argument evaluation and Log emission. *)
Theory stmtSimLogCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource   exprSimWordArgs
  stmtSimLogSuffixActual stmtSimLogSuffixFrame stmtSimLogSuffixCode stmtSimLogArgs freshWrites
  compileEnv loweringStateRelDefs stmtLowering fragExec loweringSlice exprLoweringProps emitHelperProps
  vyperInterpreter vyperState vyperTyping list stmtSimLogTrace emitHelper context venomInst
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  fragGasMode fragGasPath fragGasSeq rich_list vyperEvalExprPreservesScopesDom
Libs
  monadsyntax

Theorem log_ready_values_typed:
  !args es vs es'.
  (!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\ eval_exprs cx args es = (INL vs,es') ==>
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) (MAP expr_type args) vs
Proof
  Induct
  >- simp[eval_exprs_nil] >>
  rpt gen_tac >> strip_tac >> drule eval_exprs_cons_cases >> strip_tac
  >- gvs[] >>
  rename1 `eval_exprs cx args es1 = (tail_res,es')` >>
  Cases_on `tail_res` >> gvs[] >> conj_tac
  >- metis_tac[] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem log_emit_open[local]:
  emit_inst LOG ops [] sa = ((),sb) ==> ~block_is_terminated sb
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> strip_tac >> gvs[] >>
  Cases_on `sa.cs_current_insts` >>
  simp[block_is_terminated_def, rich_listTheory.LAST_APPEND, LAST_CONS_cond,
       mk_inst_def, is_terminator_def]
QED

Theorem log_compile_structure[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,MAP expr_type args,flags) /\
  LENGTH flags = LENGTH args /\ EVERY supported_scalar_type (MAP expr_type args) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) /\
  fn_has_code sa sb func ==>
  ?xs sm ops st. compile_log_eval_all cenv args sa = (xs,sm) /\
    compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
    MAP SND xs = MAP expr_type args /\ LENGTH flags = LENGTH xs /\
    inst_extends sm sb /\ same_blocks sm sb /\ sm.cs_next_var <= sb.cs_next_var /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sm sb) /\ cs_extends sa sm /\ cs_extends sm sb /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >> Cases_on `compile_log_eval_all cenv args sa` >>
  rename1 `compile_log_eval_all cenv args sa = (xs,sm)` >>
  Cases_on `compile_log_topic_ops (FST (split_log_ops xs flags)) sm` >>
  rename1 `compile_log_topic_ops _ sm = (ops,st)` >>
  `MAP SND xs = MAP expr_type args` by
    (drule compile_log_eval_all_types >> simp[]) >>
  `LENGTH xs = LENGTH args` by metis_tac[listTheory.LENGTH_MAP] >>
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF]) >>
  `LENGTH flags = LENGTH xs` by decide_tac >>
  drule_all log_success_suffix_code >> strip_tac >>
  `cs_extends sa sm` by (drule compile_log_eval_all_grows >> simp[]) >>
  `cs_extends sm sb` by
    (irule cs_extends_same_block >>
     gvs[same_blocks_def, inst_extends_def, rich_listTheory.IS_PREFIX_APPEND] >>
     metis_tac[]) >>
  map_every qexists_tac [`xs`, `sm`, `ops`, `st`] >> simp[] >>
  metis_tac[fn_has_code_mid, cs_extends_refl]
QED


Theorem log_stmt_open[local]:
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all cenv args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt cenv lctx ty (Log id args) sa = ((),sb) ==>
  ~block_is_terminated sb
Proof
  strip_tac >>
  Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
      metis_tac[log_emit_open]) >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> drule log_emit_open >> simp[]
QED

(* Outside a static frame the static-write check passes. *)
Theorem eval_log_bind[local]:
  ~cx.txn.is_static ==>
  eval_stmt cx (Log id args) =
    bind (eval_exprs cx args)
      (\vs. bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                                 cx.txn.target id vs) "Log encode event")
                 push_log)
Proof
  strip_tac >> simp[Once evaluate_def] >>
  simp[FUN_EQ_THM, bind_def, ignore_bind_def] >> rpt gen_tac >>
  rpt (CASE_TAC >> gvs[])
QED

Theorem log_args_admissible[local]:
  ~cx.txn.is_static /\
  gas_admissible (eval_stmt cx (Log id args)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_exprs cx args) log_args_res_ok es
Proof
  rw[gas_admissible_def, log_args_res_ok_def] >>
  `eval_stmt cx (Log id args) (es with gas_obs := gs) = (INR exc, ee)` by
    simp[log_eval_outcome] >>
  first_x_assum drule >> strip_tac >> metis_tac[log_argument_error_ok]
QED

Theorem log_args_scopes_dom:
  gas_marked_exec memory (ctx,func) (eval_exprs cx args)
    (es,s0) marks res ee r ==>
  MAP FDOM ee.scopes = MAP FDOM es.scopes
Proof
  simp[gas_marked_exec_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
  drule eval_exprs_preserves_scopes_dom >> simp[]
QED

Theorem log_wb_alloca_frame:
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  wb_frame cenv es es1 sa s0 t ==>
  alloca_frame cenv es sa s0 cenv ee t
Proof
  strip_tac >> irule alloca_frame_of_mem_frame >>
  goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]
QED

Theorem log_suffix_alloca_frame:
  stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sm /\
  MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  (!op w. (!z. op = Var z ==> not_fresh_at sm z) /\
    (!l. op <> Label l) /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\
  (!aid a k. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (a,k) ==>
    mem_bytes_at a k t.vs_memory = mem_bytes_at a k s.vs_memory) ==>
  alloca_frame cenv es sm s cenv ee t
Proof
  strip_tac >> irule alloca_frame_of_mem_frame >>
  goal_assum (drule_at Any) >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  metis_tac[]
QED

Theorem compile_log_ready_stmt_frag:
  (!e tail s. R (e::tail) s ==>
    expr_sim ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  (!tail s gs. R tail s ==> R tail (s with gas_obs := gs)) /\
  R args es /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword (:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword (:256) ==>
  stmt_frag ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  qpat_x_assum `!e tail s. _` (assume_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  (* A static frame has no related target state. *)
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >>
  drule_all log_compile_structure >> strip_tac >>
  `gas_admissible (eval_exprs cx args) log_args_res_ok es` by
    metis_tac[log_args_admissible] >>
  qspecl_then [`args`, `ctx`, `func`, `cenv`, `cx`, `R`, `es`, `sa`, `xs`, `sm`,
               `s0`, `env`, `env`, `es`] mp_tac compile_log_eval_all_gas >>
  impl_tac
  >- (RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> simp[] >>
      first_assum ACCEPT_TAC) >>
  qpat_assum `~cx.txn.is_static` (rewrite_tac o single o MATCH_MP eval_log_bind) >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "args_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`, `ee`, `leaf`, `fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag[args_summary]:
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >> strip_tac
  >- suspend "args_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks` >> disj1_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_ready_stmt_frag[args_value]:
  gvs[Excl "enc_def"] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, Excl "enc_def"] >>
     metis_tac[gas_marked_path_exec, gas_path_normal]) >>
  drule_all (SRULE [] (Q.INST [`tys` |-> `MAP expr_type args`]
    log_source_event_encoded)) >> strip_tac >>
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm (es_end with gas_obs := []) t arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs` by
    (fs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
        combinTheory.o_DEF, Excl "enc_def"] >>
     rpt strip_tac >>
     `SND (EL n xs) = expr_type (EL n args)` by
       (qpat_x_assum `MAP SND xs = _` (mp_tac o Q.AP_TERM `EL n`) >>
        simp[EL_MAP, Excl "enc_def"]) >>
     qpat_x_assum `!n. n < LENGTH args ==> _` (qspec_then `n` mp_tac) >>
     simp[Excl "enc_def"]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[log_args_post_state] >>
  `local_ptrs_reserved cenv sm` by
    (drule compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `LENGTH flags = LENGTH xs` by simp[] >>
  qpat_assum `MAP SND xs = MAP expr_type args`
    (fn th => drule_all (REWRITE_RULE [th] log_success_suffix_actual_run)) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  suspend "suffix"
QED

Resume compile_log_ready_stmt_frag[suffix]:
  rename1 `compile_stmt _ _ _ (Log _ _) sa = ((),sb)` >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts sm sb) (DROP t.vs_inst_idx bb.bb_instructions) /\
        t.vs_inst_idx + LENGTH (emitted_insts sm sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def,
         IS_PREFIX_APPEND, Excl "enc_def"] >>
     qexists_tac `l` >>
     REWRITE_TAC[GSYM listTheory.APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND]) >>
  qspecl_then [`emitted_insts sm sb`, `t`, `u`, `ctx`, `func`, `bb`]
    mp_tac tuple_run_inst_seq_gas_path >>
  impl_tac >- simp[Excl "enc_def"] >> strip_tac >>
  `u.vs_current_bb = t.vs_current_bb` by
    (qspecl_then [`emitted_insts sm sb`, `t`, `0`, `ctx`, `bb`]
       mp_tac exec_block_run_inst_seq >>
     impl_tac >- simp[Excl "enc_def"] >> simp[Excl "enc_def"]) >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sb))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `gas_marked_exec F (ctx,func)
     (bind (lift_option (encode_source_event (get_tenv cx) cx.sources
                          cx.txn.target id vs) "Log encode event") push_log)
     (es_end with gas_obs := [], t) (REPLICATE n F) (INL ())
     (es_end with logs := es_end.logs ++ [ev])
     (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule gas_marked_exec_no_source_read >>
     simp[gas_marked_path_def, Excl "enc_def"] >>
     conj_tac
     >- (simp[bind_def, lift_option_def, return_def, push_log_def, Abbr `ev`,
              wordsTheory.w2w_id, Excl "enc_def"] >>
         simp[Once contractABITheory.enc_def]) >>
     metis_tac[]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def, Excl "enc_def"] >>
  qexistsl_tac [`INL ()`, `es_end with logs := es_end.logs ++ [ev]`,
                `OK (u with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac
  >- (irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`es_end`, `t`, `vs`] >> simp[Excl "enc_def"] >>
      qpat_x_assum `gas_marked_exec _ _ (bind (lift_option _ _) push_log) _ _ _ _ _`
        mp_tac >>
      qpat_assum `encode_source_event _ _ _ _ _ = _` (fn th => rewrite_tac[th]) >>
      simp[Excl "enc_def"]) >>
  suspend "post"
QED

Resume compile_log_ready_stmt_frag[post]:
  `MAP FDOM es_end.scopes = MAP FDOM es.scopes` by
    (drule log_args_scopes_dom >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv (es_end with gas_obs := []) t` by
    (irule log_wb_alloca_frame >> simp[] >> metis_tac[log_args_post_frame]) >>
  `alloca_frame cenv (es_end with gas_obs := []) sm t cenv
     (es_end with <|logs := es_end.logs ++ [ev]; gas_obs := []|>) u` by
    (irule log_suffix_alloca_frame >> simp[Excl "enc_def"] >>
     metis_tac[stmt_state_rel_gas_obs]) >>
  `sa.cs_next_id <= sm.cs_next_id` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  drule log_args_post_frame >> simp[wb_frame_def, Excl "enc_def"] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `~u.vs_halted` by
    (drule gas_path_normal >> simp[Excl "enc_def"]) >>
  disj1_tac >>
  simp[stmt_post_def, stmt_lands_def, stmt_state_rel_inst_idx, Excl "enc_def"] >>
  simp[cenv_top_ext_refl, Excl "enc_def"] >>
  rpt conj_tac
  >- fs[same_blocks_def]
  >- metis_tac[log_stmt_open]
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) u` mp_tac >>
      simp[Abbr `ev`, wordsTheory.w2w_id, Excl "enc_def"])
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def])
  >> irule alloca_frame_same_state >> qexists_tac `u` >> simp[] >>
  irule alloca_frame_trans >>
  qexistsl_tac [`cenv`, `es_end with gas_obs := []`, `t`, `sm`] >>
  fs[Excl "enc_def"]
QED

Finalise compile_log_ready_stmt_frag

(* Readiness-parametric composition over counted pointer outcomes. *)
Theory logStmtComposePtr
Ancestors
  logReadyRunPtr logArgsRunPtr logSuccessSuffixPtr logComposeFacts bodyPtrDefs stmtFragPtr
  stmtSimLogArgs stmtSimLogSource stmtSimLogArgsGrowth stmtSimProps
  exprSimDefs exprSimProps exprSimHypsDefs loweringPosts compileEnv loweringStateRelDefs
  stmtLowering gasSummaryComposePtr gasExemptCert gasOutcome gasContext
  fragGasPathPtr fragGasPath gasSummary gasSummaryCompose
  valueTypingMemoryProps vyperInterpreter vyperState venomState
  exprLoweringProps emitHelperProps list rich_list words
  fragExec fragGasMode stmtSimLogSuffixActual exprSimWordArgs

Theorem log_args_post_scalars:
  log_args_post ctx func ce cx es sa sm s0 ee xs vs t /\
  EVERY supported_scalar_type (MAP SND xs) /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v) (MAP SND xs) vs ==>
  LIST_REL (\arg v. log_arg_rel ce cx sa sm ee t arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs
Proof
  simp[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP] >>
  rpt strip_tac >> simp[] >> metis_tac[value_has_type_memory_wf]
QED

Theorem compile_log_ready_stmt_frag_ptr:
  log_args_ready_ptr d ctx PG func cenv cx Inv args /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  expr_sim_inv cenv cx env es /\ well_typed_exprs env args /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)) /\
  cenv.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  LENGTH (FILTER I flags) <= 3 /\ EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags tys)) < dimword(:256) /\
  abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags tys)) < dimword(:256) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty (Log id args)) (eval_stmt cx (Log id args)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  gvs[stmt_env_def, declare_stmt_local_def, comp_bind_def, comp_return_def,
      comp_ignore_bind_def] >> pairarg_tac >> gvs[] >>
  drule_all log_compile_decompose >> strip_tac >>
  `gas_admissible (eval_exprs cx args)
    (\r. !exc. r = INR exc ==> expr_res_ok (INR exc : value + exception)) es` by
    metis_tac[log_arguments_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    fs[ret_pc_ok_def] >>
  drule_all compile_log_eval_all_gas_ptr >>
  qpat_assum `~cx.txn.is_static` (fn th => rewrite_tac[MATCH_MP eval_log_nonstatic_bind th]) >>
  simp[gas_outcome_ptr_def] >> strip_tac
  >- suspend "args_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  rename1 `gas_exempt_cert _ _ _ _ _ marks (err,ee) (leaf,fin)` >>
  qexistsl_tac [`err`,`ee`,`leaf`,`fin`] >>
  rewrite_tac[ignore_bind_bind_return] >>
  irule gas_exempt_cert_error_values >> first_assum ACCEPT_TAC
QED

Resume compile_log_ready_stmt_frag_ptr[args_summary]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "args_value" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INR ex`,`es_end`,`G`,`tn`,`r`] >> conj_tac
  >- (irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_log_ready_stmt_frag_ptr[args_value]:
  markerLib.RESUME_TAC >> gvs[Excl "enc_def"] >>
  suspend "success"
QED

Resume compile_log_ready_stmt_frag_ptr[success]:
  markerLib.RESUME_TAC >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     metis_tac[gas_path_normal]) >>
  drule_all (SRULE [] (Q.INST [`tys` |-> `MAP expr_type args`]
    log_source_event_encoded)) >> strip_tac >>
  `EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v) (MAP SND xs) vs` by metis_tac[] >>
  drule_all log_args_post_scalars >> disch_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    metis_tac[log_args_post_state] >>
  `local_ptrs_reserved cenv sm` by
    (drule compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  `(!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
   (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)` by
    metis_tac[not_fresh_at_mono] >>
  `?bb. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm cs') (DROP t.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
         Excl "enc_def"] >>
     qexists_tac `l` >> rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND]) >>
  qspecl_then [`t`,`cs'`] strip_assume_tac log_fresh_limit_exists >>
  suspend "path"
QED

Resume compile_log_ready_stmt_frag_ptr[path]:
  markerLib.RESUME_TAC >>
  `encode_indexed_event_topics flags (MAP SND xs) vs = SOME topics /\
   SUM (MAP (type_memory_bytes cenv) (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
   abi_size_bound cenv.ce_struct_fields (TupleT (log_non_indexed_types flags (MAP SND xs))) < dimword(:256) /\
   vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags (MAP SND xs))
      (log_non_indexed_values flags vs) = SOME avs` by asm_rewrite_tac[] >>
  `LENGTH flags = LENGTH xs` by simp[] >>
  drule_all log_success_suffix_path_ptr >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  suspend "bind"
QED

Resume compile_log_ready_stmt_frag_ptr[bind]:
  markerLib.RESUME_TAC >>
  qabbrev_tac `n = LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm cs'))` >>
  qabbrev_tac `ev = <|logger := cx.txn.target; topics := n2w h::topics;
    data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
      (log_non_indexed_types flags (MAP expr_type args)))) (ListV avs)|>` >>
  `encode_source_event (get_tenv cx) cx.sources cx.txn.target id vs = SOME ev` by
    (simp[Abbr `ev`, Once contractABITheory.enc_def]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
    (bind (lift_option (encode_source_event (get_tenv cx) cx.sources
      cx.txn.target id vs) "Log encode event") push_log)
    (es_end with gas_obs := [],t,G,tn) (REPLICATE n F) (INL ())
    (es_end with logs := es_end.logs ++ [ev]) H tm (OK t')` by
    (irule gas_marked_exec_ptr_no_source_read >> simp[] >>
     simp[bind_def, lift_option_def, return_def, push_log_def,
          evaluation_state_component_equality]) >>
  qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
  qexistsl_tac [`INL ()`,`es_end with logs := es_end.logs ++ [ev]`,`H`,`tm`,`OK t'`] >>
  conj_tac
  >- (irule gas_marked_exec_ptr_bind_normal >>
      goal_assum (drule_at Any) >>
      qpat_x_assum `gas_marked_exec_ptr _ _ _ (bind (lift_option _ _) _) _ _ _ _ _ _ _` mp_tac >>
      simp[]) >>
  disj1_tac >> simp[] >>
  suspend "post"
QED

Resume compile_log_ready_stmt_frag_ptr[post]:
  markerLib.RESUME_TAC >>
  `~block_is_terminated cs'` by metis_tac[log_compiled_not_terminated] >>
  `stmt_lands lctx cs' (INL ()) t'` by
    (fs[stmt_lands_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
        emitted_insts_def] >>
     qpat_assum `cs'.cs_current_insts = sm.cs_current_insts ++ _`
       (mp_tac o Q.AP_TERM `LENGTH`) >> simp[] >> decide_tac) >>
  drule log_args_post_frame >> strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x t' = SOME w` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G0 x /\
       op_taint tm (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
     fs[ghost_kept_def] >> metis_tac[]) >>
  simp[cenv_top_ext_refl] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (_ with <|logs := _; gas_obs := _|>) t'` mp_tac >>
  qpat_x_assum `ghost_inv _ _ _ (_ with <|logs := _; gas_obs := _|>) _ _ t'` mp_tac >>
  simp[Abbr `ev`, Excl "enc_def"] >> rpt strip_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx final t'` >>
  `stmt_state_rel ctx func cenv cx (final with gas_obs := []) t'` by
    simp[Abbr `final`, Excl "stmt_state_rel_gas_obs", Excl "enc_def"] >>
  fs[stmt_state_rel_gas_obs]
QED
Finalise compile_log_ready_stmt_frag_ptr

val _ = if null (hyp compile_log_ready_stmt_frag_ptr) then ()
  else raise Fail "compile_log_ready_stmt_frag_ptr is not closed";

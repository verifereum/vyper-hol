(* Readiness-parametric composition of argument evaluation and Log emission. *)
Theory stmtSimLogCompose
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts stmtSimDefs stmtSimProps
  stmtSimLogArgsRun stmtSimLogArgsGrowth stmtSimLogSuffix stmtSimLogSource   exprSimWordArgs
  stmtSimLogSuffixActual stmtSimLogSuffixFrame stmtSimLogSuffixCode stmtSimLogArgs freshWrites
  compileEnv stmtLowering fragExec loweringSlice exprLoweringProps emitHelperProps
  vyperInterpreter vyperState vyperTyping list stmtSimLogTrace emitHelper context venomInst
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

Theorem log_ready_eval_outcome[local]:
  (!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
  R args es /\ eval_stmt cx (Log id args) es = (res,es') /\ ~cx.txn.is_static /\
  lookup_event_metadata (get_tenv cx) cx.sources cx.txn.target id = SOME (h,tys,flags) /\
  MAP expr_type args = tys /\ LENGTH flags = LENGTH tys /\
  EVERY supported_scalar_type tys ==>
  (?err. eval_exprs cx args es = (INR err,es') /\ res = INR err) \/
  (?vs mid topics avs. eval_exprs cx args es = (INL vs,mid) /\
    encode_indexed_event_topics flags tys vs = SOME topics /\
    vyper_to_abi_list (get_tenv cx) (log_non_indexed_types flags tys)
      (log_non_indexed_values flags vs) = SOME avs /\ res = INL () /\
    es' = mid with logs := mid.logs ++
      [<|logger := cx.txn.target; topics := n2w h::topics;
         data := enc (Tuple (vyper_to_abi_types (get_tenv cx)
           (log_non_indexed_types flags tys))) (ListV avs)|>])
Proof
  strip_tac >> gvs[log_eval_outcome]
  >> `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
           value_has_type tv v) (MAP expr_type args) vals` by
       (irule log_ready_values_typed >> goal_assum (drule_at Any) >>
        qexists_tac `R` >> conj_tac >- first_assum ACCEPT_TAC >>
        first_assum ACCEPT_TAC)
  >> drule_all (SRULE [] (Q.INST [`tys` |-> `MAP expr_type args`]
       log_source_event_encoded)) >> strip_tac >> gvs[]
  >> metis_tac[]
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


Theorem compile_log_ready_stmt_frag:
  (!e tail s. R (e::tail) s ==>
    expr_sim ctx func cenv cx (expr_type e) e s /\
    !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
      R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                        value_has_type tv v) /\
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
    (stmt_env cenv lctx ty (Log id args))
      (eval_stmt cx (Log id args)) es
Proof
  strip_tac >>
  (* A static frame has no related target state. *)
  Cases_on `cx.txn.is_static`
  >- (simp[stmt_frag_def] >> rpt strip_tac >>
      fs[stmt_state_rel_def, state_rel_def]) >>
  `(!e tail s. R (e::tail) s ==>
     !v s1. (do r <- eval_expr cx e; read_result cx r od) s = (INL v,s1) ==>
       R tail s1 /\ ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                          value_has_type tv v)` by metis_tac[] >>
  drule_all log_ready_eval_outcome >> strip_tac
  >- suspend "error" >>
  suspend "success"
QED

Resume compile_log_ready_stmt_frag[error]:
  gvs[stmt_frag_def, stmt_env_def, declare_stmt_local_def,
      comp_bind_def, comp_return_def] >> rpt strip_tac >>
  `expr_res_ok (INR err : value + exception)` by
    (drule_all log_argument_error_ok >> simp[]) >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule_all log_compile_structure >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`rr` |-> `INR err`] (SPEC_ALL compile_log_eval_all_sim))) >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def, wb_args_exit_def] >>
  disch_then (qspec_then `func` mp_tac) >>
  simp[stmt_exit_def] >> strip_tac >> disj2_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  disj1_tac >>
  Cases_on `err` >> Cases_on `run_from fuel ctx func s0` >>
  gvs[expr_exit_def] >> rename1 `Error ex` >> Cases_on `ex` >>
  gvs[expr_exit_def]
QED

Resume compile_log_ready_stmt_frag[success]:
  gvs[stmt_frag_def, stmt_env_def, declare_stmt_local_def,
      comp_bind_def, comp_return_def, Excl "enc_def"] >> rpt strip_tac >>
  gvs[comp_ignore_bind_def, comp_bind_def, comp_return_def, Excl "enc_def"] >>
  pairarg_tac >> gvs[Excl "enc_def"] >>
  drule_all log_compile_structure >> strip_tac >>
  drule_all (SRULE [] (Q.INST [`rr` |-> `INL vs`] (SPEC_ALL compile_log_eval_all_safe_sim))) >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[frag_exec_def, wb_args_exit_def, Excl "enc_def"] >>
  disch_then (qspec_then `func` mp_tac) >> simp[Excl "enc_def"] >> strip_tac >>
  rename1 `log_args_post _ _ _ _ _ _ _ _ _ _ _ u` >>
  `LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v) (MAP SND xs) vs` by
    (asm_rewrite_tac [] >> irule log_ready_values_typed >>
     goal_assum (drule_at Any) >> qexists_tac `R` >>
     conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `eval_stmt _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_event_metadata _ _ _ _ = _` kall_tac >>
  ntac 2 (qpat_x_assum `!e tail s. _` kall_tac) >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx final_es` >>
  suspend "suffix"
QED

Resume compile_log_ready_stmt_frag[suffix]:
  `EVERY (supported_scalar_type o SND) xs` by
    (`EVERY supported_scalar_type (MAP SND xs)` by metis_tac[] >>
     gvs[EVERY_MAP, combinTheory.o_DEF, Excl "enc_def"]) >>
  `LIST_REL (\arg v. log_arg_rel cenv cx sa sm mid u arg v /\
      supported_scalar_type (SND arg) /\
      ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\ value_has_type tv v) xs vs` by
    (fs[log_args_post_def, LIST_REL_EL_EQN, EVERY_EL, EL_MAP,
        combinTheory.o_DEF, Excl "enc_def"] >>
     metis_tac[LIST_REL_LENGTH, LENGTH_MAP]) >>
  `stmt_state_rel ctx func cenv cx mid u` by metis_tac[log_args_post_state] >>
  `local_ptrs_reserved cenv sm` by
    (drule compile_log_eval_all_grows >> strip_tac >>
     metis_tac[local_ptrs_reserved_next_var]) >>
  qpat_assum `MAP SND xs = MAP expr_type args`
    (fn th => drule_all (REWRITE_RULE [th] log_success_suffix_actual_run)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx final_es t` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) t` mp_tac >>
     simp[Abbr `final_es`, wordsTheory.w2w_id, Excl "enc_def"]) >>
  suspend "landing"
QED

Resume compile_log_ready_stmt_frag[landing]:
  `frag_exec ctx sm cs' (\s. s = u)
     (\s. s = t with vs_inst_idx := LENGTH cs'.cs_current_insts) (\r. F)` by
    (irule frag_exec_run_inst_seq >>
     gvs[same_blocks_def, inst_extends_def, Excl "enc_def"] >>
     rpt strip_tac >> disj1_tac >> qexists_tac `t` >> simp[]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  simp[frag_exec_def, Excl "enc_def"] >>
  disch_then (qspec_then `func` mp_tac) >> simp[Excl "enc_def"] >> strip_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ (_ with logs := _) t` kall_tac >>
  qpat_x_assum `LIST_REL (\arg v. _ /\ _ /\ _) xs vs` kall_tac >>
  qpat_x_assum `LIST_REL (\ty v. _) (MAP SND xs) vs` kall_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  drule log_args_post_frame >> simp[wb_frame_def] >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_log_eval_all_grows >> simp[]) >>
  disj1_tac >> qexists_tac `t with vs_inst_idx := LENGTH cs'.cs_current_insts` >>
  simp[stmt_lands_def, stmt_state_rel_inst_idx, cenv_top_ext_refl, Excl "enc_def"] >>
  conj_tac >- suspend "open" >>
  conj_tac
  >- (rpt strip_tac >>
      `lookup_var x u = SOME w` by metis_tac[] >>
      `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
      qpat_x_assum `!op w. _` (qspecl_then [`Var x`, `w`] mp_tac) >>
      simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]) >>
  rpt strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx func u = _` drule >>
  strip_tac >>
  qpat_x_assum `!fuel. _ ==> ?fuel'. run_from fuel' ctx func s0 = _`
    (qspec_then `fuel'` mp_tac) >>
  simp[] >> metis_tac[]
QED

Resume compile_log_ready_stmt_frag[open]:
  Cases_on `SND (split_log_ops xs flags) = []`
  >- (drule_all compile_log_empty_trace >> strip_tac >>
      qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
      metis_tac[log_emit_open]) >>
  drule_all (SRULE [] (Q.INST [`data_ops` |-> `SND (split_log_ops xs flags)`]
    compile_log_data_trace)) >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >> simp[] >>
  strip_tac >> drule log_emit_open >> simp[]
QED

Finalise compile_log_ready_stmt_frag

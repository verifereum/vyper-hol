(* Conditional control flow with destination-indexed selected-arm posts. *)
Theory bodyIfExpConditionalMemory
Ancestors
  bodyIfExpDestinationEndpoint bodyIfExpCountedOutcome bodyIfExpRootSelection
  bodyIfExpMemory bodyIfExpMemoryJoin exprSimMemUnwrap exprSimHyps
  exprSimIfExp exprSimOperators exprSimDefs exprSimMemDefs gasSummary gasOutcome
  fragGasPathMem fragGasMode loweringPosts exprLoweringProps compileEnv
  venomState vyperState exprLowering allocaHistoryFragment

Theorem ifexp_body_nonword_vv_sim_mem:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (IfExp t c a b) es /\
  ~is_word_type t /\
  expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
  (!gs tv es1.
    vyperState$bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) = (INL tv,es1) ==>
    expr_body_pre cenv cx env a es1 /\ expr_body_pre cenv cx env b es1 /\
    expr_sim_mem ctx func cenv cx ty a es1 /\ expr_sim_mem ctx func cenv cx ty b es1 /\
    expr_vv_sim_mem ctx func cenv cx ty a es1 /\ expr_vv_sim_mem ctx func cenv cx ty b es1) ==>
  expr_vv_sim_mem ctx func cenv cx ty (IfExp t c a b) es
Proof
  strip_tac >> drule expr_body_pre_ifexp >> strip_tac >>
  `!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  `!e sa sb op. (e = a \/ e = b) /\
    lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    metis_tac[cj 2 exprLoweringPropsTheory.compile_expr_grows] >>
  simp[exprSimMemDefsTheory.expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule ifexp_root_condition_admissible >> goal_assum (drule_at Any)) >>
  drule_all ifexp_root_code_layout >> disch_then (qspec_then `T` strip_assume_tac) >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr cenv ty (if T then a else b) _ = _` kall_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` kall_tac >> gvs[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ c _` mp_tac >>
  simp[exprSimMemDefsTheory.expr_sim_mem_def] >> disch_then drule_all >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ root_post root_exit` >>
  simp[Abbr `root_exit`] >> irule ifexp_root_condition_dispatch_mem >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> suspend "selected"
QED

Resume ifexp_body_nonword_vv_sim_mem[selected]:
  gvs[] >>
  qpat_x_assum `sj.cs_current_bb = _` kall_tac >>
  qpat_x_assum `sj.cs_current_insts = _` kall_tac >>
  qpat_x_assum `se.cs_current_insts = _` kall_tac >>
  qpat_x_assum `fn_has_code sj sn func` kall_tac >>
  qpat_x_assum `fn_has_code se sx func` kall_tac >>
  qpat_x_assum `fn_has_code sx sy func` kall_tac >>
  qpat_x_assum `fn_has_code sy sz func` kall_tac >>
  qpat_x_assum `local_ptrs_reserved cenv se` kall_tac >>
  qpat_x_assum `cs_extends se sx` kall_tac >>
  qpat_x_assum `sc.cs_next_var <= se.cs_next_var` kall_tac >>
  qpat_x_assum `sc.cs_next_id <= se.cs_next_id` kall_tac >>
  qpat_x_assum `sx.cs_next_id <= sb.cs_next_id` kall_tac >>
  drule_all ifexp_root_code_layout >> disch_then (qspec_then `sel` strip_assume_tac) >> gvs[] >>
  `~u.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
     drule fragGasPathMemTheory.gas_path_mem_exec >> metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `gas_path_mem ctx func u 0 (OK (jump_to se.cs_current_bb u))` by
    (asm_rewrite_tac[] >> irule ifexp_jnz_path_mem >> simp[] >> metis_tac[]) >>
  irule ifexp_selected_outcome_prefix_mem >>
  goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (qpat_x_assum `!sa sb op. _` drule >> simp[]) >>
  drule ifexp_selected_entry_facts_mem >>
  disch_then (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (qspecl_then [`ty`,`se`,`marks`,`se.cs_current_bb`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >> suspend "raw_arm"
QED

Resume ifexp_body_nonword_vv_sim_mem[raw_arm]:
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  `cs_extends sea sx` by
    (`ci_mono sea (SND (compile_ifexp_arm cenv (expr_type a)
       (lowered_value_type cenv (if sel then a else b)) av sea))` by
       irule exprLoweringPropsTheory.ci_mono_compile_ifexp_arm >> gvs[exprLoweringPropsTheory.ci_mono_def]) >>
  `fn_has_code se sea func /\ fn_has_code sea sx func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `!x. vv_operand av = Var x ==> not_fresh_at sea x` by
    (drule (cj 1 exprOperandVarTheory.compiler_compile_var) >> simp[]) >>
  `gas_admissible (eval_expr cx (if sel then a else b)) expr_vv_res_ok
      (mid with gas_obs := [])` by
    (qpat_x_assum `gas_admissible (bind _ (conditional_result _)) _ _` mp_tac >>
     simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
     first_x_assum (qspec_then `gs` mp_tac) >>
     simp[vyperStateTheory.bind_def] >> Cases_on `res`
     >- (rename1 `eval_expr _ _ _ = (INL raw,ee)` >>
         Cases_on `raw` >> simp[exprSimDefsTheory.expr_vv_res_ok_def] >>
         simp[vyperStateTheory.conditional_result_def, vyperStateTheory.raise_def,
              exprSimDefsTheory.expr_vv_res_ok_def]) >> simp[]) >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ (if _ then _ else _) _` mp_tac >>
  simp[exprSimMemDefsTheory.expr_vv_sim_mem_def] >> disch_then drule >>
  disch_then (qspec_then `jump_to se.cs_current_bb u` mp_tac) >>
  impl_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with gas_obs := []) _` mp_tac >>
      simp[venomStateTheory.jump_to_def, exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  strip_tac >> gvs[] >>
  drule ifexp_raw_counted_conditional_outcome_mem >> disch_then irule >> simp[] >>
  reverse conj_tac >- (rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> suspend "endpoint"
QED

Resume ifexp_body_nonword_vv_sim_mem[endpoint]:
  `~s.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule fragGasPathMemTheory.gas_path_mem_exec >> metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `expr_type (if sel then a else b) = expr_type a` by (Cases_on `sel` >> simp[]) >>
  `expr_body_pre cenv cx env (if sel then a else b) (mid with gas_obs := [])` by
    (`vyperState$bind (eval_expr cx c) (read_result cx)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
       (INL (BoolV sel),mid with gas_obs := [])` by
       (fs[gas_marked_exec_def] >> metis_tac[listTheory.APPEND_NIL]) >>
     qpat_x_assum `!gs tv es1. _ ==> expr_body_pre _ _ _ _ _ /\ _` drule >>
     Cases_on `sel` >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM ee.scopes` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` assume_tac) >>
     drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `?right tv v q.
    gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) right (INL tv) (ee with gas_obs := []) (OK q) /\
    read_result cx tv (ee with gas_obs := []) = (INL v,ee with gas_obs := []) /\
    expr_post ctx func cenv cx (IfExp (expr_type (if sel then a else b)) c a b)
      (mid with gas_obs := []) se sx (jump_to (if sel then tl else el) u)
      (ee with gas_obs := []) v aop q /\
    vv_store_bound cx (expr_type (if sel then a else b)) (expr_type (if sel then a else b))
      (ee with gas_obs := []) tv
      (LocatedValue (expr_type (if sel then a else b)) (mk_ptr aop LocMemory)) q /\
    ~q.vs_halted /\ q.vs_current_bb = sx.cs_current_bb /\
    q.vs_inst_idx = LENGTH sx.cs_current_insts /\ alloca_history func q /\
    (jump_to (if sel then tl else el) u).vs_alloca_next <= q.vs_alloca_next` by
    (irule ifexp_selected_destination_marked_endpoint_mem >>
     simp[SF SFY_ss] >> suspend "endpoint_premises") >> suspend "joined"
QED
Resume ifexp_body_nonword_vv_sim_mem[endpoint_premises]:
  conj_tac
  >- (qexists `env` >> qpat_x_assum `expr_body_pre _ _ _ (if _ then _ else _) _` mp_tac >> simp[]) >>
  qexistsl [`sea`, `se`, `ty`, `av`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
  qexists `se` >> simp[]
QED
Resume ifexp_body_nonword_vv_sim_mem[joined]:
  gvs[] >>
  `?w. eval_operand aop q = SOME w` by
    fs[loweringPostsTheory.expr_post_def, expr_val_rel_def] >>
  qmatch_asmsub_rename_tac `read_result cx tv _ = (INL v,_)` >>
  qexistsl [`right`, `tv`,
    `jump_to sb.cs_current_bb (update_var rv' w q with vs_inst_idx := LENGTH sy.cs_current_insts)`] >>
  conj_tac
  >- (irule ifexp_marked_zero_suffix_mem >> goal_assum (drule_at Any) >>
      irule ifexp_suffix_path_mem >> simp[] >> metis_tac[]) >>
  simp[Abbr `root_post`] >> suspend "join_post"
QED
Resume ifexp_body_nonword_vv_sim_mem[join_post]:
  conj_tac
  >- (qpat_assum `~is_word_type (expr_type a)` (fn th =>
        irule (SRULE [th, vyperASTTheory.expr_type_def, loweringPostsTheory.post_value_type_def]
          (Q.INST [`e` |-> `IfExp (expr_type a) c a b`, `t` |-> `expr_type a`]
            ifexp_finish_post))) >>
      simp[SF SFY_ss] >> suspend "finish_premises") >>
  conj_tac
  >- (simp[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def] >>
      irule ifexp_pointer_bound_assign >> metis_tac[]) >>
  `alloca_inv q` by fs[expr_post_def, stmt_state_rel_def] >>
  `alloca_history func (update_var rv' w q with vs_inst_idx := LENGTH sy.cs_current_insts)` by
    (irule assign_history >> metis_tac[]) >>
  drule ifexp_history_jump >> disch_then (qspec_then `sb.cs_current_bb` assume_tac) >>
  fs[jump_to_def, update_var_def] >> gvs[] >> decide_tac
QED
Resume ifexp_body_nonword_vv_sim_mem[finish_premises]:
  qexistsl [`cop`, `mid with gas_obs := []`, `if sel then tl else el`,
    `aop`, `sc`, `se`, `sx`, `u`, `BoolV sel`] >> simp[] >>
  metis_tac[]
QED
Finalise ifexp_body_nonword_vv_sim_mem

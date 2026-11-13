Theory stmtIfPtr
Ancestors
  ifComposePtr ifBranchPtr ifGhostPtr ifJumpPtr bodyPtrDefs
  stmtSimIfProps stmtSimProps stmtSimDefs exprSimDefs exprSimProps loweringPosts
  gasSummaryComposePtr fragGasPathPtr gasOutcome gasSummary gasSummaryCompose
  gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs valueEncoding vyperInterpreter vyperState vyperValue
  venomExecSemantics venomExecProofs venomInst venomState

Theorem if_ptr_condition_bool:
  gas_admissible (eval_stmt cx (If c ss1 ss2)) (stmt_res_ok lctx) es /\
  gas_marked_exec_ptr D (ctx,func) PG (bind (eval_expr cx c) (read_result cx))
    (es,s0,G0,tn0) marks (INL v) mid G tn (OK t) ==>
  ?b. v = BoolV b
Proof
  strip_tac >> spose_not_then assume_tac >>
  `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  rewrite_tac[gas_admissible_def] >>
  disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
    `INR (Error (TypeError "not BoolV"))`, `mid with gas_obs := []`] mp_tac) >>
  simp[stmt_res_ok_def] >>
  qpat_x_assum `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_marked_exec_ptr_def] >> strip_tac >>
  first_x_assum (qspec_then `[]` assume_tac) >>
  fs[] >> rewrite_tac[eval_stmt_if_forced] >>
  pure_once_rewrite_tac[bind_def] >> simp[raise_def]
QED

Theorem compile_if_stmt_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim_ptr d ctx PG func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       bind (eval_expr cx c) (read_result cx)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (If c ss1 ss2)) (eval_stmt cx (If c ss1 ss2)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_if_code_layout_frontiers >> strip_tac >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule if_condition_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_ptr_def] >>
  disch_then (qspecl_then [`sa`, `cond`, `op`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[ret_pc_ok_def] >> metis_tac[])) >>
  rewrite_tac[gas_outcome_ptr_def, gas_summary_ptr_at_marked] >> strip_tac
  >- suspend "selected_branch"
  >- (gvs[] >> Cases_on `res` >- fs[] >>
      rename1 `INR ex` >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR ex`, `es_end`, `G`, `tn`, `r`] >>
      conj_tac
      >- (rewrite_tac[eval_stmt_if_forced] >>
          irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
      disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  drule eval_stmt_if_condition_cert >> metis_tac[]
QED

Resume compile_if_stmt_frag_ptr[selected_branch]:
  gvs[] >> drule_all if_ptr_condition_bool >> strip_tac >> gvs[] >>
  qpat_x_assum `!b. ?entry last after. _` (qspec_then `b` strip_assume_tac) >>
  qpat_x_assum `!sa' op sb'. lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `cs_mono (stmts_env _ _ _ ss1)` kall_tac >>
  qpat_x_assum `cs_mono (stmts_env _ _ _ ss2)` kall_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  `!tail. bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL (BoolV b), es_end with gas_obs := tail)` by fs[gas_marked_exec_ptr_def] >>
  `gas_admissible (eval_stmts cx (if b then ss1 else ss2)) (stmt_res_ok lctx)
     (es_end with scopes := FEMPTY :: es_end.scopes)` by
    (drule_all if_branch_admissible >> simp[]) >>
  `eval_operand op t = SOME (val_to_w256 (BoolV b))` by
    (drule_all if_condition_operand >> simp[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_erase, gas_path_normal]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G tn
     (OK (jump_to (if b then tl else el) t))` by
    (irule if_jnz_zero_path_ptr >>
     drule emit_inst_extends >> strip_tac >> simp[] >>
     qexistsl_tac [`op`, `pre`, `post`] >>
     simp[valueEncodingTheory.val_to_w256_def] >> fs[ptr_val_ok_def]) >>
  qpat_x_assum `!gs b es1. _` mp_tac >>
  disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `b`,
    `es_end with gas_obs := []`] mp_tac) >>
  (impl_tac >- (qpat_x_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` mp_tac) >> simp[SF ETA_ss])) >>
  rewrite_tac[stmt_frag_ptr_def] >>
  disch_then (qspecl_then [`entry`, `last`, `jump_to (if b then tl else el) t`,
    `G`, `tn`, `FST (stmts_env cenv lctx ty (if b then ss1 else ss2) entry)`] mp_tac) >>
  (impl_tac >- suspend "entry") >>
  simp[] >> strip_tac >> suspend "compose"
QED
Resume compile_if_stmt_frag_ptr[entry]:
  `ghost_inv d cenv cx
     ((es_end with gas_obs := []) with scopes := FEMPTY :: es_end.scopes)
     G tn (jump_to (if b then tl else el) t)` by
    (qpat_assum `ghost_inv _ _ _ (es_end with gas_obs := []) _ _ _`
       (mp_tac o MATCH_MP if_ghost_inv_push) >>
     simp[] >> strip_tac >> irule if_ghost_inv_jump >> simp[]) >>
  simp[compile_stmts_env, ret_pc_ok_jump_to, stmt_state_rel_jump_to,
       stmt_state_rel_push_scope, block_is_terminated_def, jump_to_def] >>
  conj_tac
  >- (qpat_x_assum `compile_stmts _ _ _ _ _ = _` mp_tac >>
      simp[compile_stmts_env] >> metis_tac[pairTheory.PAIR]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
  conj_tac
  >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
      fs[expr_post_def]) >>
  conj_tac >- (fs[not_fresh_at_def] >> metis_tac[]) >>
  conj_tac
  >- (qpat_x_assum `gas_admissible (eval_stmts _ _) _ _` mp_tac >>
      simp[gas_admissible_def]) >>
  fs[expr_post_def] >> gvs[jump_to_def]
QED

Resume compile_if_stmt_frag_ptr[compose]:
  `gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_stmt cx (If c ss1 ss2)) (es,s0,G0,tn0)
    (stmt_post_ptr d ctx func cx lctx cenv cenv sa sb s0 G0 tn0)
    (\res ee gt r. !tail. stmt_exit_ptr RetQ (ee with gas_obs := tail) res gt r)`
    suffices_by simp[gas_outcome_ptr_def, gas_summary_ptr_at_marked, stmt_post_ptr_def] >>
  irule if_selected_outcome_prefix_ptr >>
  qexistsl_tac [`G`, `b`, `cond`, `entry`, `if b then tl else el`,
    `marks`, `es_end`, `op`, `t`, `tn`] >> simp[] >>
  irule if_branch_outcome_ptr >> simp[jump_to_def] >>
  qexistsl_tac [`after`, `FST (stmts_env cenv lctx ty (if b then ss1 else ss2) entry)`,
    `last`, `xl`] >>
  conj_tac
  >- (Cases_on `block_is_terminated last` >> gvs[]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` mp_tac >>
  simp[GSYM stmt_post_ptr_def, SF ETA_ss, jump_to_def]
QED
Finalise compile_if_stmt_frag_ptr

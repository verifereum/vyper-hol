(* Actual-source counted conditional statement simulation. *)
Theory stmtIfMemory
Ancestors
  exprSimMemDefs bodyMemoryDefs fragGasPathMem stmtSimIfCounted
  stmtSimDefs stmtSimProps stmtSimIfProps exprSimDefs exprSimProps loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasMode
  list rich_list finite_map pred_set fragExec localPtrsProps loweringSlice
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding vyperInterpreter vyperState vyperValue vyperEvalPreservesScopes
  vyperExprNoControl vyperValueOperation vyperStatePreservation
  venomExecSemantics venomExecProofs venomInst venomState integer_word
Libs
  monadsyntax intLib

Theorem compile_if_stmt_frag_mem:
  !d ctx func cx lctx RetQ cenv ty c ss1 ss2 es.
    expr_type c = BaseT BoolT /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!sa op sb. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
                cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var) /\
    cs_mono (stmts_env cenv lctx ty ss1) /\
    cs_mono (stmts_env cenv lctx ty ss2) /\
    (!gs b es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL (BoolV b), es1) ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmts_env cenv lctx ty (if b then ss1 else ss2))
         (eval_stmts cx (if b then ss1 else ss2))
         (es1 with scopes := FEMPTY :: es1.scopes)) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv (stmt_env cenv lctx ty (If c ss1 ss2))
      (eval_stmt cx (If c ss1 ss2)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_mem_def] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_if_code_layout_frontiers >> strip_tac >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule if_condition_admissible >> metis_tac[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_mem_def] >>
  disch_then (qspecl_then [`sa`, `cond`, `op`, `s0`] mp_tac) >>
  impl_tac >- simp[] >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- suspend "selected_branch"
  >- (gvs[] >> Cases_on `res` >- fs[] >>
      rename1 `INR ex` >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR ex`, `es_end`, `r`] >>
      conj_tac
      >- (rewrite_tac[eval_stmt_if_forced] >>
          irule gas_marked_exec_bind_exception >> simp[]) >>
      disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  drule eval_stmt_if_condition_cert >> metis_tac[]
QED

Resume compile_if_stmt_frag_mem[selected_branch]:
  gvs[] >>
  `?b. v = BoolV b` by
    (spose_not_then assume_tac >>
     `v <> BoolV T /\ v <> BoolV F` by metis_tac[] >>
     qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` mp_tac >>
     rewrite_tac[gas_admissible_def] >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,
       `INR (Error (TypeError "not BoolV"))`, `es_end with gas_obs := []`] mp_tac) >>
     simp[stmt_res_ok_def] >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` assume_tac) >>
     fs[] >> rewrite_tac[eval_stmt_if_forced] >>
     pure_once_rewrite_tac[bind_def] >> simp[raise_def]) >>
  gvs[] >>
  qpat_x_assum `!b. ?entry last after. _`
    (qspec_then `b` strip_assume_tac) >>
  `!tail. bind (eval_expr cx c) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL (BoolV b), es_end with gas_obs := tail)` by
    fs[gas_marked_exec_def] >>
  `gas_admissible (eval_stmts cx (if b then ss1 else ss2)) (stmt_res_ok lctx)
     (es_end with scopes := FEMPTY :: es_end.scopes)` by
    (drule_all if_branch_admissible >> simp[]) >>
  qpat_x_assum `!sa' op sb'. lower_value _ _ _ _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `cs_mono (stmts_env _ _ _ ss1)` kall_tac >>
  qpat_x_assum `cs_mono (stmts_env _ _ _ ss2)` kall_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  `eval_operand op t = SOME (val_to_w256 (BoolV b))` by
    (drule_all if_condition_operand >> simp[]) >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[gas_path_mem_exec, gas_path_normal]) >>
  `gas_path_mem ctx func t 0 (OK (jump_to (if b then tl else el) t))` by
    (irule assert_jnz_zero_path_mem >>
     drule emit_inst_extends >> strip_tac >> simp[] >>
     qexistsl_tac [`op`, `pre`, `post`] >>
     simp[valueEncodingTheory.val_to_w256_def]) >>
  qpat_x_assum `!gs b es1. _` mp_tac >>
  disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`, `b`,
    `es_end with gas_obs := []`] mp_tac) >>
  impl_tac >- (qpat_x_assum `!tail. bind _ _ _ = _`
    (qspec_then `[]` mp_tac) >> simp[SF ETA_ss]) >>
  rewrite_tac[stmt_frag_mem_def] >>
  disch_then (qspecl_then [`entry`, `last`, `jump_to (if b then tl else el) t`,
      `FST (stmts_env cenv lctx ty (if b then ss1 else ss2) entry)`] mp_tac) >>
  impl_tac
  >- (simp[compile_stmts_env, ret_pc_ok_jump_to, stmt_state_rel_jump_to,
           stmt_state_rel_push_scope, block_is_terminated_def, jump_to_def] >>
      conj_tac
      >- (qpat_x_assum `compile_stmts _ _ _ _ _ = _` mp_tac >>
          simp[compile_stmts_env] >> metis_tac[pairTheory.PAIR]) >>
      conj_tac >- metis_tac[local_ptrs_reserved_next_var] >>
      conj_tac
      >- (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `s0`, `sa`] >>
          fs[expr_post_def]) >>
      conj_tac
      >- (qpat_x_assum `gas_admissible (eval_stmts _ _) _ _` mp_tac >>
          simp[gas_admissible_def]) >>
      conj_tac
      >- (simp[return_buf_frame_jump_to] >> irule return_buf_frame_frame >>
          qexistsl_tac [`cenv`, `s0`, `sa`] >>
          fs[expr_post_def, lookup_var_def, jump_to_def]) >>
      fs[expr_post_def, allocaHistoryTheory.alloca_history_def, jump_to_def]) >>
  simp[] >> strip_tac >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (ignore_bind push_scope (finally (eval_stmts cx (if b then ss1 else ss2)) pop_scope))
     (es_end with gas_obs := [], jump_to (if b then tl else el) t)
     (\res ee u. ?cenv''.
       stmt_lands lctx sb res u /\ ~u.vs_halted /\
       (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
       cenv_top_ext cenv cenv'' ee.scopes /\
       stmt_state_rel ctx func cenv'' cx ee u /\
       (!x w. not_fresh_at entry x /\
              lookup_var x (jump_to (if b then tl else el) t) = SOME w ==>
              lookup_var x u = SOME w) /\
       (!aid bnd. FLOOKUP (jump_to (if b then tl else el) t).vs_allocas aid = SOME bnd ==>
                  FLOOKUP u.vs_allocas aid = SOME bnd) /\
       return_buf_frame d cenv'' sb u /\ alloca_history func u /\
       (jump_to (if b then tl else el) t).vs_alloca_next <= u.vs_alloca_next)
     (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)` by
    (irule if_branch_outcome_mem >> simp[jump_to_def] >>
     qexistsl_tac [`after`, `FST (stmts_env cenv lctx ty (if b then ss1 else ss2) entry)`,
       `last`, `xl`] >> simp[] >>
     conj_tac >- (Cases_on `block_is_terminated last` >> fs[]) >>
     qpat_x_assum `gas_outcome _ _ _ (eval_stmts _ _) _ _ _` mp_tac >>
     simp[jump_to_def]) >>
  drule_all if_selected_outcome_prefix_mem >>
  simp[gas_outcome_def, gas_summary_at_def]
QED

Finalise compile_if_stmt_frag_mem

(* Preserved fixed-result proof (verbatim):
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_mem_def] >> rpt gen_tac >>
  strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  Cases_on `compile_stmt cenv lctx ty (If c ss1 ss2) sa` >>
  rename1 `_ = (u, sm)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  drule_all compile_if_layout_mem >> strip_tac >>
  imp_res_tac new_block_props >>
  qpat_x_assum `eval_stmt _ _ _ = _`
    (strip_assume_tac o MATCH_MP eval_stmt_if_all_mem)
  >- (fs[] >>
      `expr_res_ok r1` by
        (gvs[] >>
         qpat_x_assum `(do result <- _; _ od) _ = _` mp_tac >>
         simp[bind_def] >> Cases_on `eval_expr cx c es` >>
         rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
         imp_res_tac read_result_no_control >>
         imp_res_tac (cj 1 eval_expr_no_control) >>
         gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
      gvs[] >>
      `!v. INR ex = INL v ==> ?b. v = BoolV b` by simp[] >>
      `INR ex <> (INR (Error (RuntimeError "convert empty bytes to signed")) : value + exception)` by simp[] >>
      drule_all cond_jump_frag_mem >> strip_tac >> fs[] >>
      disj2_tac >> qexists_tac `fuel` >> gvs[stmt_exit_def] >> disj1_tac >>
      metis_tac[expr_exit_INR_type])
  >- gvs[stmt_res_ok_def] >>
  gvs[] >>
  `expr_res_ok (INL (BoolV b)) /\
   (!v. (INL (BoolV b) : value + exception) = INL v ==> ?b. v = BoolV b)` by
    simp[expr_res_ok_def] >>
  `INL (BoolV b) <> (INR (Error (RuntimeError "convert empty bytes to signed")) : value + exception)` by simp[] >>
  drule_all cond_jump_frag_mem >> strip_tac >> fs[] >>
  gvs[] >> rename1 `stmt_state_rel ctx func cenv cx es1 sv` >>
  `!st l. sa.cs_next_var <= st.cs_next_var ==>
          ret_pc_ok cenv st (jump_to l sv) /\
          return_buf_frame d cenv st (jump_to l sv)` by
    (rpt gen_tac >> disch_tac >>
     simp[ret_pc_ok_jump_to, return_buf_frame_jump_to] >>
     conj_tac
     >- (irule ret_pc_ok_frame >> metis_tac[]) >>
     irule return_buf_frame_frame >> metis_tac[]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `!sa' op sb'. _` kall_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `lookup_block _ _ = _` kall_tac >>
  rpt (qpat_x_assum `_.cs_blocks = _` kall_tac) >>
  qabbrev_tac `si = if b then s6 else s9` >>
  qabbrev_tac `se = jump_to si.cs_current_bb sv` >>
  `(?s. stmt_lands lctx sb res s /\ ~s.vs_halted /\
         (res = INL () ==> ~block_is_terminated (if b then s7 else s10)) /\
         stmt_state_rel ctx func cenv cx (es2 with scopes := rest) s /\
         alloca_history func s /\
         (!x w. not_fresh_at si x /\ lookup_var x se = SOME w ==>
                lookup_var x s = SOME w) /\
         (!aid bnd. FLOOKUP se.vs_allocas aid = SOME bnd ==>
                    FLOOKUP s.vs_allocas aid = SOME bnd) /\
         return_buf_frame d cenv sb s /\ se.vs_alloca_next <= s.vs_alloca_next /\
         !fuel r. run_from fuel ctx func s = r /\ (!e. r <> Error e) ==>
                  ?fuel'. run_from fuel' ctx func se = r /\
                    (mem_safe_run fuel ctx func s ==> mem_safe_run fuel' ctx func se)) \/
    (?fuel r. run_from fuel ctx func se = r /\ exit_result r /\
              stmt_exit RetQ (es2 with scopes := rest) res r /\
              mem_safe_run fuel ctx func se)` by
    (Cases_on `b` >> (fs[Abbr `si`, Abbr `se`] >>
     irule (SRULE [] if_branch_frag_mem_join) >>
     simp[stmt_state_rel_jump_to, stmt_state_rel_push_scope] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac
     >- (strip_tac >>
         `?x11. new_block le s11 = (x11, sb)` by metis_tac[] >>
         imp_res_tac new_block_props >> fs[] >> metis_tac[]) >>
     conj_tac >- gvs[allocaHistoryTheory.alloca_history_def, jump_to_def] >>
     conj_tac
     >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[]) >>
     qexists_tac `es1 with scopes := FEMPTY :: es1.scopes` >>
     goal_assum (drule_at Any) >>
     simp[stmt_state_rel_push_scope]))
  >- (disj1_tac >> qexistsl_tac [`s`, `cenv`] >>
      simp[cenv_top_ext_refl] >>
      conj_tac
      >- (strip_tac >>
          `?x11. new_block le s11 = (x11, sb)` by
            (Cases_on `b` >> fs[] >> metis_tac[]) >>
          imp_res_tac new_block_props >> fs[block_is_terminated_def]) >>
      conj_tac
      >- (rpt strip_tac >>
          `lookup_var x sv = SOME w` by metis_tac[] >>
          qpat_x_assum `!x w. not_fresh_at si x /\ _ ==> _` irule >>
          fs[Abbr `se`, lookup_var_def, jump_to_def] >>
          irule freshWritesTheory.not_fresh_at_mono >>
          qexists_tac `sa` >> Cases_on `b` >> fs[Abbr `si`]) >>
      conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!aid bnd. FLOOKUP se.vs_allocas aid = SOME bnd ==> _` irule >>
          simp[Abbr `se`, jump_to_def] >> metis_tac[]) >>
      conj_tac >- (fs[Abbr `se`, jump_to_def] >> decide_tac) >>
      rpt strip_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx func s = r /\ _ ==> _`
        (qspecl_then [`fuel`, `run_from fuel ctx func s`] mp_tac) >>
      simp[] >> strip_tac >>
      qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
        (qspec_then `fuel'` mp_tac) >>
      fs[Abbr `se`, Abbr `si`] >>
      (impl_tac >- (Cases_on `b` >> gvs[])) >>
      strip_tac >> qexists_tac `fuel''` >> Cases_on `b` >> gvs[]) >>
  disj2_tac >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func (jump_to _ sv) <> Error e) ==> _`
    (qspec_then `fuel` mp_tac) >>
  fs[Abbr `se`, Abbr `si`] >>
  (impl_tac >- (Cases_on `b` >> gvs[] >> metis_tac[exit_result_not_error])) >>
  strip_tac >> qexists_tac `fuel'` >> Cases_on `b` >> gvs[]
QED
*)


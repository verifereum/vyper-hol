(* Tuple-return simulation, retained for counted migration. *)
Theory stmtSimReturnTuple
Ancestors
  stmtSimReturn stmtSimProps stmtSimDefs exprSimProps exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath gasExemptCert
  list rich_list finite_map fragExec freshWrites vyperTypeABI
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  vyperStatePreservation venomExecSemantics venomInst venomState
Libs
  monadsyntax

(* return e of a tuple of words that goes back on the stack
   (ce_returns_count = LENGTH tys > 1, no return buffer): e's fragment,
   whose errors exit, leaves a pointer to the tuple in memory; its words
   are loaded and returned with the return PC.  The pointer's variable, if
   any, was handed out before the loads (a local's is, by
   local_ptrs_reserved), so they do not overwrite it.  Typing is required
   of the value after read_result, including results read from places. *)
Theorem compile_return_tuple_int_frag:
  !ctx func cx lctx cenv e es rpc rsz tys ret_tv.
    cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
    cenv.ce_returns_count = LENGTH tys /\ 1 < LENGTH tys /\
    cenv.ce_return_buf = NONE /\
    expr_type e = TupleT tys /\ EVERY is_word_type tys /\
    evaluate_type (get_tenv cx) (TupleT tys) = SOME ret_tv /\
    (!gs v es1. (do raw <- eval_expr cx e; read_result cx raw od)
                 (es with gas_obs := gs) =
               (INL v, es1) ==> value_has_type ret_tv v) /\
    expr_sim ctx func cenv cx (TupleT tys) e es /\
    (!sa op sb. local_ptrs_reserved cenv sa /\
                lower_value compile_expr cenv (TupleT tys) e sa = (op, sb) ==>
                !x. op = Var x ==> not_fresh_at sb x) ==>
    stmt_frag ctx func cx lctx (intret_q func cenv cx ret_tv) cenv
      (stmt_env cenv lctx (TupleT tys) (Return (SOME e)))
      (eval_stmt cx (Return (SOME e))) es
Proof
  rpt gen_tac >> strip_tac >> simp[stmt_frag_def] >> rpt gen_tac >>
  strip_tac >> disj2_tac >>
  `LENGTH tys <> 1 /\ 0 < LENGTH tys` by decide_tac >>
  `tys <> []` by (strip_tac >> gvs[]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def,
       compile_internal_return_from_env_def, compile_internal_return_def] >>
  Cases_on `lower_value compile_expr cenv (TupleT tys) e sa` >>
  rename1 `_ = (op, s1)` >> simp[] >>
  Cases_on `compile_load_tuple_elements cenv op tys 0 s1` >>
  rename1 `_ = (elems, s2)` >> simp[] >>
  Cases_on `emit_inst RET (elems ++ [Var rpc]) [] s2` >>
  rename1 `_ = (u, s3)` >> Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  suspend "code"
QED

Resume compile_return_tuple_int_frag[code]:
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at s1 x` by metis_tac[] >>
  drule compile_load_tuple_elements_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s2 s3` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split] >>
  qpat_x_assum `eval_stmt _ _ _ = _` mp_tac >>
  pure_rewrite_tac[eval_return_forced] >>
  Cases_on `(do raw <- eval_expr cx e; read_result cx raw od) es` >>
  rename1 `_ = (r1, es1)` >> simp[Once bind_def, raise_def] >> strip_tac >>
  `expr_res_ok r1` by (
    Cases_on `r1`
    >- gvs[expr_res_ok_def] >>
    qpat_x_assum `(do raw <- _; _ od) _ = _` mp_tac >>
    simp[bind_def] >> Cases_on `eval_expr cx e es` >>
    rename1 `_ = (raw,est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
    imp_res_tac read_result_no_control >>
    imp_res_tac (cj 1 eval_expr_no_control) >>
    gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]) >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `op`, `r1`, `es1`, `s0`] mp_tac) >>
  impl_tac >- fs[] >>
  simp[frag_exec_def] >>
  disch_then (qspec_then `func` mp_tac) >> impl_tac >- fs[] >> strip_tac
  >- suspend "value" >>
  qexists_tac `fuel` >> Cases_on `r1` >> gvs[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_return_tuple_int_frag[value]:
  rename1 `expr_post ctx func cenv cx e es sa s1 s0 es1 v op sv` >>
  `value_has_type ret_tv v` by
    (qpat_x_assum `!v es1. _ ==> _` (qspecl_then [`v`, `es1`] mp_tac) >>
     simp[]) >>
  drule_all tuple_type_value >> strip_tac >>
  gvs[expr_post_def, return_def] >>
  `~is_word_type (TupleT tys)` by simp[is_word_type_def] >>
  qpat_x_assum `expr_val_rel _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_val_rel_def]) >>
  `tuple_in_memory vs tvs (w2n w + 0) sv.vs_memory` by
    (first_x_assum (qspec_then `TupleTV tvs` mp_tac) >>
     simp[val_in_memory_def]) >>
  `w2n w + 0 + 32 * LENGTH tys <= dimword (:256)` by
    (drule_all expr_val_at_bound >>
     simp[val_footprint_def, type_memory_size_def] >>
     drule_all word_tuple_size >> simp[]) >>
  `tuple_words cenv w tys 0 sv.vs_memory =
     MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` by
    (irule tuple_words_typed >> metis_tac[]) >>
  drule compile_load_tuple_elements_run >>
  disch_then (qspecl_then [`sv`, `w`] mp_tac) >> simp[] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  rename1 `run_inst_seq _ sv = OK (sv with vs_vars := lvars)` >>
  suspend "loads"
QED

Resume compile_return_tuple_int_frag[loads]:
  qabbrev_tac `words = MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` >>
  qabbrev_tac `sl = sv with <| vs_vars := lvars; vs_inst_idx := LENGTH s2.cs_current_insts |>` >>
  `frag_exec ctx s1 s2 (\x. x = sv) (\x. x = sl) (\r. F)` by
    (irule frag_exec_run_inst_seq >> fs[same_blocks_def, IS_PREFIX_APPEND3] >>
     simp[Abbr `sl`]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _` (mp_tac o REWRITE_RULE [frag_exec_def]) >>
  disch_then (qspecl_then [`func`, `sv`] mp_tac) >> simp[] >> strip_tac >>
  `?pc. lookup_var rpc sl = SOME pc` by
    (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >>
     strip_tac >>
     `not_fresh_at s1 rpc` by
       (irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
     simp[Abbr `sl`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  `eval_operands elems sl = SOME words` by
    simp[Abbr `sl`, eval_operands_vars_inst_idx] >>
  qspecl_then [`s2`, `s3`, `func`,
               `[mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb (LENGTH s2.cs_current_insts) =
     SOME (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) [])` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []) sl =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |> sl` by
    (irule step_ret_values >> metis_tac[]) >>
  `run_from 0 ctx func sl =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |> sl` by
    (qpat_x_assum `step_inst_base _ sl = _` mp_tac >>
     qpat_x_assum `get_instruction bb _ = _` mp_tac >>
     simp[Abbr `sl`, run_from_def, Once exec_block_def, step_inst_non_invoke,
          venomInstTheory.mk_inst_def] >>
     rpt strip_tac >> gvs[]) >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func sl <> Error e) ==> _`
    (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from fv ctx func sv = _` >>
  qpat_x_assum `!fuel. (!e. run_from fuel ctx func sv <> Error e) ==> _`
    (qspec_then `fv` mp_tac) >> simp[] >> strip_tac >>
  rename1 `run_from f0 ctx func s0 = _` >>
  `state_rel func cenv cx (es' with scopes := []) sl` by
    (`state_rel func cenv cx (es' with scopes := []) sv` by
       (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
     irule state_rel_frame >>
     simp[local_ptrs_rel_def, lookup_scopes_def, local_region_def] >>
     qexistsl [`es' with scopes := []`, `sv`] >> simp[Abbr `sl`] >>
     qpat_x_assum `state_rel _ _ _ _ sv` mp_tac >>
     simp[state_rel_def, immutables_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH vs = LENGTH tvs /\ LENGTH tvs = LENGTH tys` by
    (drule values_have_types_length >> drule LIST_REL_LENGTH >> simp[]) >>
  qexists_tac `f0` >>
  simp[exit_result_def, stmt_exit_def, intret_q_def, result_rel_def,
       Abbr `words`] >>
  disj2_tac >> irule intret_vals_match_tuple >> simp[]
QED

Finalise compile_return_tuple_int_frag

(* Check that the tuple consumer, including every resumed path, is closed. *)
val () =
  let val th = compile_return_tuple_int_frag
      val (ors, axs) = Tag.dest_tag (Thm.tag th)
  in if null axs andalso null (Thm.hyp th) andalso
        List.all (fn s => s = "DISK_THM") ors
     then print "RETURN_FORCE_AUDIT tuple OK\n"
     else raise Fail "forced tuple return inherited admission"
  end;

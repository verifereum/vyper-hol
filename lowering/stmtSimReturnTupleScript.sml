(* Tuple-return simulation, retained for counted migration. *)
Theory stmtSimReturnTuple
Ancestors
  stmtSimReturn stmtSimProps stmtSimDefs exprSimProps exprSimDefs loweringPosts exprSimTypedAlloc
  gasOutcome gasSummary gasSummaryCompose gasContext gasCount fragGasPath fragGasSeq gasExemptCert
  list rich_list arithmetic finite_map fragExec freshWrites vyperTypeABI
  exprLowering stmtLowering emitHelper emitHelperProps exprLoweringProps
  compileEnv valueEncoding venomMemDefs
  vyperInterpreter vyperState vyperValue vyperTyping vyperExprNoControl
  vyperStatePreservation venomExecSemantics venomInst venomState
Libs
  monadsyntax

Theorem return_forced_source_normal[local]:
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INL v, fin with gas_obs := tail)) ==>
  !tail. eval_stmt cx (Return (SOME e)) (es with gas_obs := xs ++ tail) =
    (INR (ReturnException v), fin with gas_obs := tail)
Proof
  simp[eval_return_forced, bind_def, raise_def]
QED

Theorem return_forced_source_exception[local]:
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := xs ++ tail) = (INR ex, fin with gas_obs := tail)) ==>
  !tail. eval_stmt cx (Return (SOME e)) (es with gas_obs := xs ++ tail) =
    (INR ex, fin with gas_obs := tail)
Proof
  simp[eval_return_forced, bind_def]
QED


Theorem tuple_load_no_gas[local]:
  !tys cenv bop off sa elems sb.
    compile_load_tuple_elements cenv bop tys off sa = (elems,sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []
Proof
  Induct
  >- (rw[compile_load_tuple_elements_def, comp_return_def] >>
      simp[emitted_insts_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_load_tuple_elements _ _ _ _ _ = _` mp_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv, sm)` >>
  rename1 `emit_op MLOAD _ sm = (v, sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest, sf)` >>
  first_x_assum drule >> strip_tac >>
  imp_res_tac emitted_insts_emit_op >>
  `emitted_insts sa sf = emitted_insts sa sm ++ emitted_insts sm sh ++
     emitted_insts sh sf` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_x_assum `sf.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `sh.cs_current_insts = _` SUBST1_TAC >>
     qpat_x_assum `sm.cs_current_insts = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  simp[FILTER_APPEND, venomInstTheory.mk_inst_def, APPEND_ASSOC]
QED

Theorem tuple_ret_gas_path[local]:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode = RET /\
  step_inst_base i s = IntRet ir s ==>
  gas_path ctx func s 0 (IntRet ir s)
Proof
  strip_tac >> irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def, exit_result_def]
QED

Theorem tuple_load_gas_path[local]:
  compile_load_tuple_elements cenv bop tys off sa = (elems,sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME w /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?vs. gas_path ctx func s 0
         (OK (s with <|vs_vars := vs; vs_inst_idx := LENGTH sb.cs_current_insts|>)) /\
       (!x. not_fresh_at sa x ==>
          lookup_var x (s with vs_vars := vs) = lookup_var x s) /\
       eval_operands elems (s with vs_vars := vs) =
         SOME (tuple_words cenv w tys off s.vs_memory)
Proof
  strip_tac >> drule_all compile_load_tuple_elements_run >> strip_tac >> gvs[] >>
  drule tuple_load_no_gas >> strip_tac >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all tuple_run_inst_seq_gas_path >>
  simp[] >> strip_tac >> qexists_tac `vs` >> simp[]
QED

Theorem tuple_suffix_post:
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  cenv.ce_returns_count = LENGTH tys /\ 1 < LENGTH tys /\
  cenv.ce_return_buf = NONE /\ expr_type e = TupleT tys /\
  post_value_type cenv e = TupleT tys /\
  EVERY is_word_type tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME ret_tv /\
  value_has_type ret_tv v /\
  expr_post ctx func cenv cx e es sa s1 s0 ee v op sv /\
  ret_pc_ok cenv sa s0 /\ sa.cs_next_var <= s1.cs_next_var /\
  (!x. op = Var x ==> not_fresh_at s1 x) /\
  compile_load_tuple_elements cenv op tys 0 s1 = (elems,s2) /\
  emit_inst RET (elems ++ [Var rpc]) [] s2 = ((),s3) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  ~sv.vs_halted /\ sv.vs_current_bb = s1.cs_current_bb /\
  sv.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  ?r. gas_path ctx func sv 0 r /\ exit_result r /\
      !tail. intret_q func cenv cx ret_tv v
               ((ee with gas_obs := tail) with scopes := []) r
Proof
  strip_tac >> drule_all tuple_type_value >> strip_tac >>
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
  drule_all compile_load_tuple_elements_run >> strip_tac >> gvs[] >>
  suspend "path"
QED

Resume tuple_suffix_post[path]:
  qpat_x_assum `!aid off sz. _` kall_tac >>
  qpat_x_assum `!aid b. FLOOKUP _ _ = _ ==> _` kall_tac >>
  qpat_x_assum `locals_kept _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_assum `fn_has_code s1 s2 func` (mp_tac o REWRITE_RULE [fn_has_code_def]) >>
  strip_tac >>
  `isPREFIX (emitted_insts s1 s2) (DROP sv.vs_inst_idx bb.bb_instructions)` by
    (fs[IS_PREFIX_APPEND] >> gvs[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  `lookup_block sv.vs_current_bb func.fn_blocks = SOME bb` by gvs[same_blocks_def] >>
  drule_all tuple_load_gas_path >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_path _ _ sv 0 (OK (sv with <|vs_vars := lvars; vs_inst_idx := _|>))` >>
  qabbrev_tac `sl = sv with <|vs_vars := lvars; vs_inst_idx := LENGTH s2.cs_current_insts|>` >>
  qabbrev_tac `words = MAP (\(tv, v). typed_val_to_w256 tv v) (ZIP (tvs, vs))` >>
  `?pc. lookup_var rpc sl = SOME pc` by
    (qpat_x_assum `ret_pc_ok _ _ _` mp_tac >> simp[ret_pc_ok_def] >> strip_tac >>
     `not_fresh_at s1 rpc` by
       (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     simp[Abbr `sl`, lookup_var_def] >> fs[lookup_var_def] >> metis_tac[]) >>
  `eval_operands elems sl = SOME words` by
    simp[Abbr `sl`, Abbr `words`, eval_operands_vars_inst_idx] >>
  drule emit_inst_extends >> strip_tac >>
  qspecl_then [`s2`, `s3`, `func`,
               `[mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []]`]
    mp_tac fn_has_code_same_block >>
  impl_tac >- simp[] >> strip_tac >>
  `get_instruction bb' (LENGTH s2.cs_current_insts) =
     SOME (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `step_inst_base (mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []) sl =
     IntRet <| iret_values := words; iret_adopt_fmp := NONE |> sl` by
    (irule step_ret_values >> metis_tac[]) >>
  suspend "post"
QED

Resume tuple_suffix_post[post]:
  `gas_path ctx func sl 0 (IntRet <|iret_values := words; iret_adopt_fmp := NONE|> sl)` by
    (irule tuple_ret_gas_path >>
     conj_tac >- simp[Abbr `sl`] >>
     qexistsl [`bb'`, `mk_inst s2.cs_next_id RET (elems ++ [Var rpc]) []`] >>
     gvs[Abbr `sl`, same_blocks_def, venomInstTheory.mk_inst_def]) >>
  `state_rel func cenv cx (ee with scopes := []) sl` by
    (`state_rel func cenv cx (ee with scopes := []) sv` by
       (irule state_rel_scopes_nil >> fs[stmt_state_rel_def]) >>
     irule state_rel_frame >>
     simp[local_ptrs_rel_def, lookup_scopes_def, local_region_def] >>
     qexistsl [`ee with scopes := []`, `sv`] >> simp[Abbr `sl`] >>
     qpat_x_assum `state_rel _ _ _ _ sv` mp_tac >>
     simp[state_rel_def, immutables_rel_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `LENGTH vs = LENGTH tvs /\ LENGTH tvs = LENGTH tys` by
    (drule values_have_types_length >> drule LIST_REL_LENGTH >> simp[]) >>
  qexists_tac `IntRet <|iret_values := words; iret_adopt_fmp := NONE|> sl` >>
  conj_tac
  >- (drule gas_path_then >> disch_then drule >> simp[Abbr `sl`]) >>
  simp[exit_result_def] >> gen_tac >>
  `((ee with gas_obs := tail) with scopes := []) =
   ((ee with scopes := []) with gas_obs := tail)` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> rewrite_tac[intret_q_gas_obs] >>
  simp[intret_q_def, result_rel_def, Abbr `words`] >>
  irule intret_vals_match_tuple >> simp[]
QED

Finalise tuple_suffix_post[local]

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
    expr_type e = TupleT tys /\ post_value_type cenv e = expr_type e /\
    EVERY is_word_type tys /\
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
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
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
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `!x. op = Var x ==> not_fresh_at s1 x` by metis_tac[] >>
  drule compile_load_tuple_elements_extends >> strip_tac >>
  drule emit_inst_extends >> strip_tac >>
  `cs_extends s2 s3` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s3 func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[return_forced_admissible] >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` (mp_tac o REWRITE_RULE [expr_sim_def]) >>
  disch_then drule >> simp[] >> disch_then (qspec_then `s0` mp_tac) >> simp[] >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  disch_then (qx_choose_then `marks` (DISJ_CASES_THEN assume_tac))
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `?res es_end r. _` strip_assume_tac >> gvs[]
      >- suspend "normal" >>
      suspend "exception") >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[return_forced_exempt]
QED

Resume compile_return_tuple_int_frag[normal]:
  qpat_x_assum `!sa' op' sb'. _` kall_tac >>
  qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def]) >>
  `value_has_type ret_tv v` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     strip_tac >> first_x_assum irule >>
     simp[SF ETA_ss] >> metis_tac[]) >>
  `1 < LENGTH tys` by decide_tac >>
  `~t.vs_halted` by metis_tac[gas_path_normal] >>
  drule_all tuple_suffix_post >> strip_tac >>
  qexistsl_tac [`INR (ReturnException v)`, `es_end`, `r`] >>
  conj_tac
  >- (simp[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def] >>
      conj_tac
      >- (irule return_forced_source_normal >> first_assum ACCEPT_TAC) >>
      drule gas_path_then >> disch_then drule >> simp[]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  gen_tac >> pure_rewrite_tac[stmt_exit_def] >> disj2_tac >>
  qexists_tac `v` >> simp[NoAsms] >>
  `((es_end with gas_obs := tail) with scopes := []) =
   ((es_end with scopes := []) with gas_obs := tail)` by
    simp[evaluation_state_component_equality] >>
  pop_assum SUBST1_TAC >> rewrite_tac[intret_q_gas_obs] >>
  qpat_x_assum `!tail. intret_q _ _ _ _ _ _ _` (qspec_then `[]` mp_tac) >>
  simp[] >> strip_tac >>
  irule (iffLR intret_q_gas_obs) >> qexists_tac `[]` >> simp[]
QED

Resume compile_return_tuple_int_frag[exception]:
  Cases_on `res` >- fs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_marked_exec_def] >> strip_tac >>
      irule return_forced_source_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type]
QED

Finalise compile_return_tuple_int_frag

(* Check that the tuple consumer, including every resumed path, is closed. *)

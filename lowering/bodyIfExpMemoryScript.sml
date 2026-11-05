Theory bodyIfExpMemory
Ancestors
  loweringPosts exprSimMemUnwrap
  exprBopSimProps
  exprSimIfExp fragExec fragExecMem instMemFrontier allocaHistoryFragment
  emitHelper emitHelperProps compileEnv venomState venomInst
  list rich_list loweringSlice venomExecSemantics venomExecProofs exprLoweringProps
  fragGasSeqMem fragGasPathMem stmtSimProps
  gasOutcome gasExemptCert gasSummary gasContext exprSimProps vyperState
  fragGasMode fragGasPath gasCount gasSummaryCompose exprLowering
  bodyMemoryDefs exprSimDefs exprSimMemDefs vyperAST vyperInterpreter memSafeRun allocaHistory

Theorem frag_exec_assign_mem:
  !ctx st st' src out P Q R.
    emit_inst ASSIGN [src] [out] st = ((), st') /\
    (!s. P s ==> ?w. eval_operand src s = SOME w /\
                     Q ((update_var out w s) with
                          vs_inst_idx := LENGTH st'.cs_current_insts)) ==>
    frag_exec_mem ctx st st' P Q R
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  irule frag_exec_mem_run_inst_seq >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[venomInstTheory.mk_inst_def, is_terminator_def] >> gen_tac >> disch_tac >>
  first_x_assum drule >> strip_tac >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >>
  simp[run_inst_seq_def, step_inst_base_def, exec_pure1_def, comp_bind_def,
       comp_return_def] >> gvs[]
QED

Theorem assign_history[local]:
  emit_inst ASSIGN [src] [out] st = ((),st') /\ fn_has_code st st' func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  eval_operand src s = SOME w ==>
  alloca_history func ((update_var out w s) with
                       vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  rpt strip_tac >> imp_res_tac emit_inst_extends >>
  `emitted_insts st st' = [mk_inst st.cs_next_id ASSIGN [src] [out]]` by
    simp[emitted_insts_def, DROP_LENGTH_APPEND] >>
  `run_inst_seq (emitted_insts st st') s = OK (update_var out w s)` by
    simp[run_inst_seq_def, mk_inst_def, step_inst_base_def, exec_pure1_def,
         comp_bind_def, comp_return_def] >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts st st' ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts st st')` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem frag_exec_assign_mem_at:
  emit_inst ASSIGN [src] [out] st = ((),st') /\
  fn_has_code st st' func /\ fn_inst_ids_distinct func /\
  alloca_history func entry /\ alloca_inv entry /\
  eval_operand src entry = SOME w ==>
  frag_exec_mem ctx st st' (\s. s = entry)
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R
Proof
  rpt strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ ~s.vs_halted /\
     s.vs_current_bb = st.cs_current_bb /\
     s.vs_inst_idx = LENGTH st.cs_current_insts` >>
  `frag_exec_mem ctx st st' P
    (\s. s = ((update_var out w entry) with
                vs_inst_idx := LENGTH st'.cs_current_insts) /\
         alloca_history func s /\
         s.vs_alloca_next = entry.vs_alloca_next) R` suffices_by
    (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_assign_mem >> qexistsl_tac [`out`, `src`] >> simp[] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  drule_all assign_history >> simp[update_var_def]
QED

Theorem ifexp_history_jump[local]:
  alloca_history func s ==> alloca_history func (jump_to lbl s)
Proof
  strip_tac >> irule alloca_history_jump >> simp[jump_to_def] >>
  qexists_tac `s` >> simp[]
QED

Theorem ifexp_assign_zero_path_mem:
  emit_inst ASSIGN [op] [rv] sa = ((),sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ eval_operand op s = SOME w ==>
  gas_path_mem ctx func s 0
    (OK ((update_var rv w s) with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSIGN [op] [rv]]` by
    metis_tac[emit_inst_extends] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx =
    SOME (mk_inst sa.cs_next_id ASSIGN [op] [rv])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `gas_path_mem_edge ctx func s 0
    (OK ((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule (SRULE [mk_inst_def] (Q.INST
       [`i` |-> `mk_inst sa.cs_next_id ASSIGN [op] [rv]`,
        `u` |-> `update_var rv w s`] straight_line_mem_edge)) >>
     simp[step_inst_base_def, exec_pure1_def, mk_inst_def,
          is_terminator_def, inst_dload_in_section_def] >>
     qexistsl_tac [`op`, `sa`] >> simp[GSYM mk_inst_def] >>
     conj_tac >- metis_tac[] >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `~((update_var rv w s) with vs_inst_idx := SUC s.vs_inst_idx).vs_halted` by
    simp[update_var_def] >>
  drule (cj 1 gas_path_mem_rules) >> strip_tac >>
  gvs[GSYM arithmeticTheory.ADD1] >>
  metis_tac[cj 2 gas_path_mem_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_jnz_path_mem:
  expr_post ctx func cenv cx c es sa sc s0 mid (BoolV sel) cop u /\
  expr_type c = BaseT BoolT /\
  emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
  fn_has_code sj sn func /\ sj.cs_current_bb = sc.cs_current_bb /\
  sj.cs_current_insts = sc.cs_current_insts /\
  ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_path_mem ctx func u 0 (OK (jump_to (if sel then tl else el) u))
Proof
  strip_tac >> irule assert_jnz_zero_path_mem >>
  simp[] >> qexistsl_tac [`cop`,`sj`,`sn`] >> simp[] >>
  drule emit_inst_extends >> strip_tac >> simp[] >>
  fs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def, is_word_type_def,
     valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def]
QED

Theorem ifexp_root_eval_forced[local]:
  eval_expr cx (IfExp t c a b) =
  vyperState$bind (vyperState$bind (eval_expr cx c) (read_result cx))
    (\v. if v = BoolV T then vyperState$bind (eval_expr cx a) (conditional_result cx)
         else if v = BoolV F then vyperState$bind (eval_expr cx b) (conditional_result cx)
         else raise (Error (TypeError "not BoolV")))
Proof
  simp[Once evaluate_def, switch_BoolV_def, vyperStateTheory.bind_assoc] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def] >> gen_tac >>
  Cases_on `eval_expr cx c x` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[] >>
  rename1 `read_result cx captured st` >>
  Cases_on `read_result cx captured st` >> rename1 `_ = (forced,sf)` >>
  Cases_on `forced` >> simp[] >> rpt IF_CASES_TAC >>
  simp[raise_def, vyperStateTheory.bind_def]
QED

Theorem ifexp_root_condition_admissible[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es ==>
  gas_admissible (vyperState$bind (eval_expr cx c) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  fs[expr_vv_res_ok_def, expr_res_ok_def] >> metis_tac[]
QED

Theorem ifexp_root_branch_admissible[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  (!tail. vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >>
  rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[ifexp_root_eval_forced, vyperStateTheory.bind_def] >>
  Cases_on `sel` >> gvs[]
QED

Theorem ifexp_root_condition_bool[local]:
  gas_admissible (eval_expr cx (IfExp t c a b)) expr_vv_res_ok es /\
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  ?sel. v = BoolV sel
Proof
  strip_tac >>
  Cases_on `v = BoolV T` >- metis_tac[] >>
  Cases_on `v = BoolV F` >- metis_tac[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def, ifexp_root_eval_forced] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[vyperStateTheory.bind_def, raise_def, expr_vv_res_ok_def]
QED

Theorem ifexp_root_condition_cert[local]:
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind
      (vyperState$bind (eval_expr cx c) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst) ==>
  gas_exempt_cert memory tops (ctx,func)
    (vyperState$ignore_bind (eval_expr cx (IfExp t c a b)) (return ()))
    (es,s0) marks (err,ee) (leaf,finalst)
Proof
  strip_tac >> rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem ifexp_root_code_layout[local]:
  compile_expr cenv ty (IfExp t c a b) st = (vv,st') /\
  fn_has_code st st' func /\ local_ptrs_reserved cenv st /\
  (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) /\
  (!e sa sb op. (e = a \/ e = b) /\ lower_value compile_expr cenv ty e sa = (op,sb) ==>
    cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id) ==>
  ?cop sc sj sn tl el xl rv se av sea aop sx sy sz.
    lower_value compile_expr cenv (BaseT BoolT) c st = (cop,sc) /\
    emit_inst JNZ [cop; Label tl; Label el] [] sj = ((),sn) /\
    sj.cs_current_bb = sc.cs_current_bb /\ sj.cs_current_insts = sc.cs_current_insts /\
    compile_expr cenv ty (if sel then a else b) se = (av,sea) /\
    compile_ifexp_arm cenv t (lowered_value_type cenv (if sel then a else b)) av sea = (aop,sx) /\
    emit_inst ASSIGN [aop] [rv] sx = ((),sy) /\
    emit_inst JMP [Label xl] [] sy = ((),sz) /\
    se.cs_current_bb = (if sel then tl else el) /\ se.cs_current_insts = [] /\
    st'.cs_current_bb = xl /\ st'.cs_current_insts = [] /\
    vv = (if is_word_type t then StackValue t (Var rv)
          else LocatedValue t (mk_ptr (Var rv) LocMemory)) /\
    fn_has_code st sc func /\ fn_has_code sj sn func /\
    fn_has_code se sx func /\ fn_has_code sx sy func /\ fn_has_code sy sz func /\
    local_ptrs_reserved cenv se /\ cs_extends sc st' /\ cs_extends se sx /\
    st.cs_next_var <= sc.cs_next_var /\ st.cs_next_id <= sc.cs_next_id /\
    sc.cs_next_var <= se.cs_next_var /\ sc.cs_next_id <= se.cs_next_id /\
    sx.cs_next_id <= st'.cs_next_id /\ (!x. not_fresh_at st x ==> x <> rv)
Proof
  strip_tac >> drule_all compile_expr_ifexp_states >> strip_tac >>
  `cs_extends s5 s6 /\ cs_extends s8 s9 /\ cs_extends s9 s10 /\
   cs_extends s12 s13 /\ cs_extends s13 s14` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s6 s7 /\ cs_extends s10 s11 /\ cs_extends s14 st'` by
    metis_tac[cs_extends_new_block] >>
  `fn_has_code st s1 func /\ fn_has_code s5 s6 func /\
   fn_has_code s7 s8 func /\ fn_has_code s8 s9 func /\ fn_has_code s9 s10 func /\
   fn_has_code s11 s12 func /\ fn_has_code s12 s13 func /\ fn_has_code s13 s14 func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `local_ptrs_reserved cenv s7 /\ local_ptrs_reserved cenv s11` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `~not_fresh_at st rv` by metis_tac[] >>
  Cases_on `sel`
  >- (qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
                   `s7`,`av`,`s7a`,`aop`,`s8`,`s9`,`s10`] >> simp[]) >>
  qexistsl_tac [`cond_op`,`s1`,`s5`,`s6`,`tl`,`el`,`xl`,`rv`,
               `s11`,`bv`,`s11a`,`bop`,`s12`,`s13`,`s14`] >> simp[]
QED

Theorem ifexp_outcome_suffix_mem[local]:
  gas_outcome T tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u /\ ~u.vs_halted ==>
     ?v. gas_path_mem ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome T tops (ctx,func) source (es,s0) Q' R
Proof
  simp[gas_outcome_def] >> strip_tac >> qexists_tac `marks` >>
  Cases_on `gas_summary_at T (ctx,func) marks source (es,s0) Q R`
  >- (disj1_tac >>
      fs[gas_summary_at_def] >>
      Cases_on `?u. r = OK u /\ Q res (es_end with gas_obs := []) u`
      >- (gvs[] >>
          `~t.vs_halted` by
            (fs[gas_marked_exec_def, gas_marked_path_def] >>
             drule gas_path_mem_exec >> metis_tac[gas_path_normal]) >>
          first_x_assum drule_all >> strip_tac >>
          qexistsl_tac [`res`,`es_end`,`OK v`] >> simp[] >>
          gvs[gas_marked_exec_def, gas_marked_path_def] >>
          metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
      metis_tac[]) >> metis_tac[]
QED

Theorem ifexp_suffix_path_mem[local]:
  emit_inst ASSIGN [op] [rv] sx = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sx sy func /\ fn_has_code sy sz func /\
  ~u.vs_halted /\ u.vs_current_bb = sx.cs_current_bb /\
  u.vs_inst_idx = LENGTH sx.cs_current_insts /\ eval_operand op u = SOME w ==>
  gas_path_mem ctx func u 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))
Proof
  strip_tac >> drule_all ifexp_assign_zero_path_mem >> strip_tac >>
  `sy.cs_current_bb = sx.cs_current_bb /\ sz.cs_blocks = sy.cs_blocks /\
   sz.cs_current_bb = sy.cs_current_bb /\
   sz.cs_current_insts = sy.cs_current_insts ++
     [mk_inst sy.cs_next_id JMP [Label xl] []]` by
    metis_tac[emit_inst_extends] >>
  `gas_path_mem ctx func
    ((update_var rv w u) with vs_inst_idx := LENGTH sy.cs_current_insts) 0
    (OK (jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)))` by
    (irule emit_jump_zero_path_mem >> simp[update_var_def] >>
     qexistsl_tac [`sy`,`sz`] >> simp[]) >>
  qpat_x_assum `!ctx. gas_path_mem _ _ _ _ _` (qspec_then `ctx` mp_tac) >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_marked_zero_suffix_mem[local]:
  gas_marked_exec T (ctx,func) source (es,s0) marks res mid (OK u) /\
  gas_path_mem ctx func u 0 (OK v) ==>
  gas_marked_exec T (ctx,func) source (es,s0) marks res mid (OK v)
Proof
  simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >> simp[] >>
  metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_selected_outcome_prefix_mem[local]:
  gas_marked_exec T (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  gas_path_mem ctx func u 0 (OK v) /\
  gas_outcome T tops (ctx,func)
    (vyperState$bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
    (mid with gas_obs := [],v) Q R ==>
  gas_outcome T tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q R
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK v)` by
    (irule ifexp_marked_zero_suffix_mem >> metis_tac[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`OK t'`] >> simp[] >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >> Cases_on `sel` >> fs[])
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_normal >>
      qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >> Cases_on `sel` >> fs[]) >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[vyperStateTheory.ignore_bind_def] >>
  pure_once_rewrite_tac[vyperStateTheory.bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >>
  Cases_on `sel` >> fs[GSYM vyperStateTheory.ignore_bind_def]
QED

Theorem ifexp_condition_exit_mem[local]:
  gas_marked_exec T (ctx,func)
    (vyperState$bind (eval_expr cx c) (read_result cx))
    (es,s0) marks res mid r /\ expr_exit res r ==>
  gas_outcome T tops (ctx,func) (eval_expr cx (IfExp t c a b)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  Cases_on `res` >> simp[] >> strip_tac >>
  simp[gas_outcome_def, gas_summary_at_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR y`,`mid`,`r`] >> simp[] >>
  conj_tac
  >- (rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  disj2_tac >> simp[] >>
  Cases_on `r` >> fs[expr_exit_def, exit_result_def] >>
  Cases_on `y` >> fs[expr_exit_def] >>
  rename1 `Error er` >> Cases_on `er` >> fs[expr_exit_def]
QED

Theorem ifexp_vv_post_of_expr_post_read[local]:
  expr_post ctx func cenv cx e es sa sb s0 es' v (Var rv) s /\
  read_result cx tv es' = (INL v, es') ==>
  vv_post ctx func cenv cx e es sa sb s0 es' tv
    (if is_word_type (expr_type e) then StackValue (expr_type e) (Var rv)
     else LocatedValue (expr_type e) (mk_ptr (Var rv) LocMemory)) s
Proof
  rw[expr_post_def, vv_post_def] >>
  gvs[vv_holds_def, vv_at_def, contextTheory.mk_ptr_def] >>
  fs[expr_val_rel_def, expr_val_at_def] >>
  rpt strip_tac >> res_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_finish_post[local]:
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
  read_result cx tv ee = (INL v,ee) /\ expr_type e = t /\
  eval_operand op u = SOME w /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id ==>
  vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
    (if is_word_type t then StackValue t (Var rv)
     else LocatedValue t (mk_ptr (Var rv) LocMemory))
    (jump_to xl (update_var rv w u with vs_inst_idx := k))
Proof
  strip_tac >>
  irule (SRULE [vyperASTTheory.expr_type_def]
    (Q.INST [`e` |-> `IfExp t c a b`] ifexp_vv_post_of_expr_post_read)) >>
  goal_assum (drule_at Any) >>
  irule expr_post_ifexp >>
  `~not_fresh_at sa rv` by metis_tac[] >>
  simp[] >> metis_tac[]
QED

Theorem ifexp_word_arm_finish_mem[local]:
  expr_post ctx func cenv cx c es sa s1 s0 es1 v1 cop tt /\
  is_word_type t /\ expr_type e = t /\ (!x. not_fresh_at sa x ==> x <> rv) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= sc.cs_next_var /\
  sa.cs_next_id <= s1.cs_next_id /\ s1.cs_next_id <= sc.cs_next_id /\
  sd.cs_next_id <= sb.cs_next_id /\ sb.cs_current_bb = xl /\ sb.cs_current_insts = [] /\
  emit_inst ASSIGN [op] [rv] sd = ((),sy) /\
  emit_inst JMP [Label xl] [] sy = ((),sz) /\
  fn_has_code sd sy func /\ fn_has_code sy sz func /\ fn_inst_ids_distinct func /\
  s0.vs_alloca_next <= tt.vs_alloca_next /\
  gas_outcome T tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv v. res = INL tv /\ read_result cx tv ee = (INL v,ee) /\
      expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next) R ==>
  gas_outcome T tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee tv
        (StackValue t (Var rv)) u /\
      vv_store_bound cx t ee tv (StackValue t (Var rv)) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next) R
Proof
  strip_tac >> irule ifexp_outcome_suffix_mem >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  qexists_tac `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)` >>
  conj_tac >- (irule ifexp_suffix_path_mem >> simp[] >> metis_tac[]) >>
  qexists_tac `tv` >> simp[vv_store_bound_stack_word] >> conj_tac
  >- (qpat_assum `is_word_type t` (fn th => irule (SRULE [th] ifexp_finish_post)) >>
      simp[] >> metis_tac[]) >>
  `alloca_inv u` by fs[expr_post_def, stmt_state_rel_def] >>
  `alloca_history func ((update_var rv w u) with
      vs_inst_idx := LENGTH sy.cs_current_insts)` by
    (irule assign_history >> metis_tac[]) >>
  drule ifexp_history_jump >> disch_then (qspec_then `xl` assume_tac) >>
  simp[jump_to_def, update_var_def]
QED

Theorem ifexp_arm_lower_value[local]:
  compile_expr cenv ty e sa = (vv,sm) /\
  compile_ifexp_arm cenv t at vv sm = (op,sb) /\
  (is_word_type t \/ same_memory_layout cenv at t) ==>
  lower_value compile_expr cenv ty e sa = (op,sb)
Proof
  simp[compile_ifexp_arm_def, lower_value_def,
       comp_bind_def] >> metis_tac[]
QED

Theorem ifexp_conditional_read_cases[local]:
  !cx raw st res st'.
    (do r <- conditional_result cx raw; read_result cx r od) st = (res,st') ==>
    read_result cx raw st = (res,st') \/
    ?m. conditional_result cx raw st = (INR (Error (TypeError m)),st') /\
        res = INR (Error (TypeError m))
Proof
  rpt gen_tac >> Cases_on `raw` >>
  simp[conditional_result_def, read_result_def, bind_def, return_def, raise_def] >>
  rename1 `place_type_value cx p st` >>
  Cases_on `place_type_value cx p st` >> rename1 `place_type_value cx p st = (pr,pst)` >>
  drule place_type_value_state >> strip_tac >> gvs[] >>
  Cases_on `pr` >> simp[]
  >- (IF_CASES_TAC >> simp[read_result_def, bind_def, return_def] >>
      Cases_on `read_place cx p pst` >> rename1 `read_place cx p pst = (rr,ss)` >>
      Cases_on `rr` >> simp[read_result_def, return_def]) >>
  Cases_on `p` >>
  gvs[place_type_value_def, get_scopes_def, get_immutables_def,
      get_address_immutables_def, bind_def, return_def, lift_option_type_def,
      raise_def, AllCaseEqs()] >>
  rpt (BasicProvers.FULL_CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem ifexp_arm_conditional_read[local]:
  read_result cx raw ee = (INL v,ee) /\
  conditional_result cx raw ee = (res,ss) /\ expr_vv_res_ok res ==>
  ?tv. res = INL tv /\ ss = ee /\
       read_result cx tv ee = (INL v,ee)
Proof
  rpt strip_tac >>
  Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ee` >>
  drule ifexp_conditional_read_cases >> strip_tac >>
  imp_res_tac vyperStatePreservationTheory.conditional_result_state >>
  gvs[expr_vv_res_ok_def, bind_def, AllCaseEqs()]
QED

Theorem ifexp_retained_read_typeerror_probe[local]:
  !cx es.
    ?st raw.
      conditional_result cx raw st = (INL raw,st) /\
      expr_vv_res_ok (INL raw) /\
      read_result cx raw st =
        (INR (Error (TypeError "evaluate_subscripts type")),st)
Proof
  rpt gen_tac >>
  qexists_tac `es with scopes :=
    [FEMPTY |+ ("x", <| assignable := T;
       type := ArrayTV (ArrayTV (BaseTV BoolT) (Fixed 1)) (Fixed 1);
       value := BoolV F; popped := [] |>)]` >>
  qexists_tac `PlaceR (MemoryPlace "x" [ValueSubscript (IntV 0)])` >>
  simp[conditional_result_def, expr_vv_res_ok_def, read_result_def,
       place_type_value_def, read_place_def, get_scopes_def,
       lookup_scopes_def, subscripts_type_def, subscript_type_def,
       read_memory_path_def, evaluate_subscripts_def, read_popped_def,
       bind_def, lift_option_type_def, lift_sum_def, return_def, raise_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >> EVAL_TAC
QED

Theorem ifexp_root_forced_branch_admissible[local]:
  gas_admissible (bind (eval_expr cx (IfExp t c a b)) (read_result cx))
    expr_res_ok es /\
  (!tail. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  gas_admissible (bind (eval_expr cx (if sel then a else b)) (read_result cx))
    expr_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `!gs res ee. _` (qspec_then `xs ++ gs` mp_tac) >>
  simp[ifexp_root_eval_forced, bind_def] >>
  Cases_on `sel` >> gvs[] >> strip_tac >>
  rename1 `bind (eval_expr cx arm) (read_result cx) _ = _` >>
  Cases_on `eval_expr cx arm (mid with gas_obs := gs)` >>
  rename1 `_ = (ar,ast)` >> Cases_on `ar` >> gvs[bind_def] >>
  (rename1 `conditional_result cx raw ast` >>
      Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ast` >>
      `read_result cx raw ast = (q,r) \/
       ?m. conditional_result cx raw ast = (INR (Error (TypeError m)),r) /\
           q = INR (Error (TypeError m))` by
        (irule ifexp_conditional_read_cases >> simp[bind_def]) >>
      gvs[bind_def, expr_res_ok_def])
QED

Theorem ifexp_read_conditional_cert[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (conditional_result cx)) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)
Proof
  strip_tac >>
  `gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_expr cx e) (return ()))
    (es,s0) marks (err,ee) (leaf,finstate)` by
    (irule gas_exempt_cert_unforce_result >> simp[]) >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem ifexp_missing_flag_type_probe[local]:
  get_tenv cx = FEMPTY ==>
  is_word_type (FlagT nsid) /\
  evaluate_type (get_tenv cx) (FlagT nsid) = NONE /\
  vv_holds cenv cx (FlagT nsid) (Value NoneV)
    (LocatedValue (FlagT nsid) (mk_ptr (Lit 0w) LocMemory)) es s /\
  vv_store_bound cx (FlagT nsid) es (Value NoneV)
    (LocatedValue (FlagT nsid) (mk_ptr (Lit 0w) LocMemory)) s
Proof
  simp[is_word_type_def, vyperValueTheory.evaluate_type_def,
       finite_mapTheory.FLOOKUP_EMPTY, vv_holds_def, vv_store_bound_def,
       contextTheory.mk_ptr_def, eval_operand_def, read_result_def, return_def]
QED

(* Full-post specialization: state relation remains an explicit premise.
   This is not a compile_expr or source-execution witness. *)
Theorem ifexp_missing_flag_full_post_probe[local]:
  get_tenv cx = FEMPTY /\ expr_type e = FlagT nsid ==>
  (vv_post ctx func cenv cx e es sa sb s es (Value NoneV)
     (LocatedValue (FlagT nsid) (mk_ptr (Lit 0w) LocMemory)) s /\
   vv_store_bound cx (expr_type e) es (Value NoneV)
     (LocatedValue (FlagT nsid) (mk_ptr (Lit 0w) LocMemory)) s
   <=> stmt_state_rel ctx func cenv cx es s)
Proof
  simp[vv_post_def, vv_at_def, vv_holds_def, vv_store_bound_def,
       vyperValueTheory.evaluate_type_def, finite_mapTheory.FLOOKUP_EMPTY,
       contextTheory.mk_ptr_def, eval_operand_def, read_result_def, return_def]
QED

(* Successful raw StackValue endpoint: the actual arm emits no unwrap code. *)
Theorem ifexp_stack_arm_endpoint_mem[local]:
  compile_expr cenv ty e sa = (StackValue st op,sm) /\
  compile_ifexp_arm cenv t at (StackValue st op) sm = (out,sb) /\
  is_word_type t /\ expr_type e = t /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (StackValue st op) u /\
  read_result cx raw ee = (INL v,ee) /\
  alloca_history func u /\ ~u.vs_halted /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z. gas_path_mem ctx func u 0 (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v out z /\
    expr_store_bound cx t v out z /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  gvs[compile_ifexp_arm_def, unwrap_value_def, comp_return_def] >>
  qexists_tac `u` >> simp[cj 1 gas_path_mem_rules, expr_store_bound_word] >>
  irule exprSimUnwrapTheory.expr_post_of_vv_post_stack >>
  drule exprSimUnwrapPropsTheory.vv_post_read_result >>
  disch_then (fn th => fs[th]) >> qexists_tac `st` >> simp[]
QED

(* Construction with the precise residual MLOAD bound exposed, not discharged. *)
Theorem ifexp_memory_arm_endpoint_mem[local]:
  compile_expr cenv ty e sa = (LocatedValue st p,sm) /\
  compile_ifexp_arm cenv t at (LocatedValue st p) sm = (op,sb) /\
  is_word_type t /\ expr_type e = t /\ p.ptr_location = LocMemory /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw (LocatedValue st p) u /\
  read_result cx raw ee = (INL v,ee) /\
  (?w. eval_operand p.ptr_operand u = SOME w /\
       w2n w + 32 <= u.vs_alloca_next) /\
  alloca_history func u /\ ~u.vs_halted /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z. gas_path_mem ctx func u 0 (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    expr_store_bound cx t v op z /\
    alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
    z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `st = t` by fs[vv_post_def, vv_holds_def] >> gvs[] >>
  `unwrap_value cenv (LocatedValue (expr_type e) p) sm = (op,sb)` by
    fs[compile_ifexp_arm_def] >>
  `is_word_type (expr_type e) ==>
    ?w. eval_operand p.ptr_operand u = SOME w /\
        w2n w + 32 <= u.vs_alloca_next` by simp[] >>
  drule_all bodyFieldMemoryPropsTheory.body_unwrap_memory_counted_read >>
  strip_tac >> goal_assum (drule_at Any) >> simp[expr_store_bound_word]
QED

Theorem compile_ifexp_vv_sim_mem:
  !ctx func cenv cx ty t c a b es.
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (~is_word_type t ==>
     !e. (e = a \/ e = b) ==>
         lowered_value_type cenv e = expr_type e \/
         is_bytestring_type (expr_type e) /\
         is_bytestring_type (lowered_value_type cenv e) /\
         arg_type_fits (lowered_value_type cenv e) (expr_type e) \/
         same_memory_layout cenv (lowered_value_type cenv e) (expr_type e)) /\
    (!tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ ~is_word_type t ==>
       type_memory_bytes cenv t = type_memory_size tvt /\
       type_memory_size tvt < 2 ** 64) /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1 /\
       expr_vv_sim_mem ctx func cenv cx ty a es1 /\
       expr_vv_sim_mem ctx func cenv cx ty b es1 /\
       !e gs' v es2. ~is_word_type t /\ (e = a \/ e = b) /\
         (do r <- eval_expr cx e; read_result cx r od)
           (es1 with gas_obs := gs') = (INL v, es2) ==>
         ?tvt. evaluate_type (get_tenv cx) t = SOME tvt /\ value_has_type tvt v) ==>
    expr_vv_sim_mem ctx func cenv cx ty (IfExp t c a b) es
Proof
  cheat
QED

Theorem compile_ifexp_word_sim_mem:
  !ctx func cenv cx ty t c a b es.
    is_word_type t /\
    expr_type c = BaseT BoolT /\ expr_type a = t /\ expr_type b = t /\
    (!sa sb op. lower_value compile_expr cenv (BaseT BoolT) c sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    (!e sa sb op. (e = a \/ e = b) /\
       lower_value compile_expr cenv ty e sa = (op, sb) ==>
       cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
       sa.cs_next_id <= sb.cs_next_id) /\
    expr_sim_mem ctx func cenv cx (BaseT BoolT) c es /\
    (!gs tv es1.
       (do result <- eval_expr cx c; read_result cx result od)
         (es with gas_obs := gs) = (INL tv, es1) ==>
       expr_sim_mem ctx func cenv cx ty a es1 /\
       expr_sim_mem ctx func cenv cx ty b es1 /\
       expr_vv_sim_mem ctx func cenv cx ty a es1 /\
       expr_vv_sim_mem ctx func cenv cx ty b es1) ==>
    expr_sim_mem ctx func cenv cx ty (IfExp t c a b) es
Proof
  cheat

QED

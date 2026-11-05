Theory bodyIfExpMemory
Ancestors
  loweringPosts exprSimMemUnwrap vyperStoragePlaceProvenance
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

Theorem ifexp_forced_arm_finish_mem[local]:
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
    (\res ee u. ?v. res = INL v /\
      expr_post ctx func cenv cx e es1 sc sd (jump_to lbl tt) ee v op u /\
      u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func u /\ tt.vs_alloca_next <= u.vs_alloca_next) R ==>
  gas_outcome T tops (ctx,func) source (es1,jump_to lbl tt)
    (\res ee u. ?v. res = INL v /\
      expr_post ctx func cenv cx (IfExp t c a b) es sa sb s0 ee v (Var rv) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next) R
Proof
  strip_tac >> irule ifexp_outcome_suffix_mem >>
  goal_assum (drule_at Any) >> simp[] >> rpt strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_post_def, expr_val_rel_def] >>
  qexists_tac `jump_to xl (update_var rv w u with vs_inst_idx := LENGTH sy.cs_current_insts)` >>
  conj_tac >- (irule ifexp_suffix_path_mem >> simp[] >> metis_tac[]) >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (irule expr_post_ifexp >> metis_tac[]) >>
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

Theorem ifexp_forced_success_conditional_marked[local]:
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx e) (read_result cx))
    (es,s0) marks (INL v) ee (OK u) /\
  (!tail. eval_expr cx e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL raw,ee with gas_obs := tail)) /\
  (!tail. conditional_result cx raw (ee with gas_obs := tail) =
    (INL tv,ee with gas_obs := tail)) ==>
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx e) (conditional_result cx))
    (es,s0) marks (INL tv) ee (OK u) /\
  read_result cx tv (ee with gas_obs := []) =
    (INL v,ee with gas_obs := [])
Proof
  simp[gas_marked_exec_def] >> strip_tac >> conj_tac
  >- simp[bind_def] >>
  `read_result cx raw (ee with gas_obs := []) =
    (INL v,ee with gas_obs := [])` by
    (qpat_x_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[bind_def]) >>
  drule ifexp_arm_conditional_read >>
  simp[expr_vv_res_ok_def] >>
  disch_then irule >>
  qpat_x_assum `!tail. conditional_result _ _ _ = _`
    (qspec_then `[]` assume_tac) >> simp[] >>
  Cases_on `raw` >>
  gvs[conditional_result_def, bind_def, return_def, raise_def,
      AllCaseEqs()] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  IF_CASES_TAC >>
  simp[bind_def, return_def, AllCaseEqs()] >> metis_tac[]
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

Theorem ifexp_root_condition_scopes[local]:
  vyperState$bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := gs) = (INL v,mid) ==>
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  simp[vyperStateTheory.bind_def] >>
  Cases_on `eval_expr cx c (es with gas_obs := gs)` >>
  rename1 `_ = (raw,st)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]
QED

Theorem ifexp_forced_arm_source[local]:
  gas_admissible
    (bind (bind (eval_expr cx e) (conditional_result cx)) (read_result cx))
    expr_res_ok es ==>
  !gs. bind (bind (eval_expr cx e) (conditional_result cx)) (read_result cx)
         (es with gas_obs := gs) =
       bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs)
Proof
  rewrite_tac[gas_admissible_def] >> strip_tac >> gen_tac >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (ar,ast)` >> Cases_on `ar` >> simp[bind_def] >>
  rename1 `conditional_result cx raw ast` >>
  Cases_on `(do r <- conditional_result cx raw; read_result cx r od) ast` >>
  drule ifexp_conditional_read_cases >> strip_tac >> simp[bind_def] >>
  qpat_x_assum `!gs res ee. _` (qspec_then `gs` mp_tac) >>
  gvs[bind_def, expr_res_ok_def]
QED

Theorem ifexp_forced_selected_source[local]:
  gas_admissible (bind (eval_expr cx (IfExp t c a b)) (read_result cx))
    expr_res_ok es /\
  (!tail. bind (eval_expr cx c) (read_result cx)
    (es with gas_obs := xs ++ tail) = (INL (BoolV sel),mid with gas_obs := tail)) ==>
  !tail. bind (eval_expr cx (IfExp t c a b)) (read_result cx)
    (es with gas_obs := xs ++ tail) =
    bind (eval_expr cx (if sel then a else b)) (read_result cx)
      (mid with gas_obs := tail)
Proof
  strip_tac >>
  `gas_admissible
    (bind (bind (eval_expr cx (if sel then a else b)) (conditional_result cx))
      (read_result cx)) expr_res_ok (mid with gas_obs := [])` by
    (rw[gas_admissible_def] >>
     qpat_x_assum `gas_admissible _ _ _` mp_tac >>
     simp[gas_admissible_def] >> disch_then (qspec_then `xs ++ gs` mp_tac) >>
     rewrite_tac[ifexp_root_eval_forced] >>
     pure_once_rewrite_tac[bind_assoc] >>
     pure_once_rewrite_tac[bind_def] >> simp[] >>
     Cases_on `sel` >> gvs[bind_def]) >>
  drule ifexp_forced_arm_source >> simp[] >> strip_tac >> gen_tac >>
  simp[ifexp_root_eval_forced, bind_def] >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `sel` >> gvs[bind_def]
QED

Theorem ifexp_forced_marked_prefix_mem[local]:
  gas_admissible (bind (eval_expr cx (IfExp t c a b)) (read_result cx))
    expr_res_ok es /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) left (INL (BoolV sel)) mid (OK u) /\
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx (if sel then a else b)) (read_result cx))
    (mid with gas_obs := [],u) right res fin r ==>
  gas_marked_exec T (ctx,func)
    (bind (eval_expr cx (IfExp t c a b)) (read_result cx))
    (es,s0) (left ++ right) res fin r
Proof
  strip_tac >>
  `!tail. bind (eval_expr cx (IfExp t c a b)) (read_result cx)
      (es with gas_obs := gas_explicit left s0.vs_gas_readings ++ tail) =
    bind (eval_expr cx (if sel then a else b)) (read_result cx)
      (mid with gas_obs := tail)` by
    (irule ifexp_forced_selected_source >> simp[] >>
     fs[gas_marked_exec_def]) >>
  `gas_explicit (left ++ right) s0.vs_gas_readings =
    gas_explicit left s0.vs_gas_readings ++
    gas_explicit right u.vs_gas_readings` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_explicit_append_path] >>
  fs[gas_marked_exec_def] >> conj_tac
  >- (pure_once_rewrite_tac[GSYM APPEND_ASSOC] >> pure_asm_rewrite_tac[] >> simp[]) >>
  simp[LENGTH_APPEND] >> metis_tac[gas_marked_path_then]
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

Theorem ifexp_forced_selected_outcome_prefix_mem[local]:
  gas_admissible (bind (eval_expr cx (IfExp t c a b)) (read_result cx))
    expr_res_ok es /\
  gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK u) /\
  gas_path_mem ctx func u 0 (OK v) /\
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx (if sel then a else b)) (read_result cx))
    (mid with gas_obs := [],v) Q R ==>
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx (IfExp t c a b)) (read_result cx)) (es,s0) Q R
Proof
  strip_tac >>
  `gas_marked_exec T (ctx,func) (bind (eval_expr cx c) (read_result cx))
    (es,s0) marks (INL (BoolV sel)) mid (OK v)` by
    (irule ifexp_marked_zero_suffix_mem >> metis_tac[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`OK t'`] >> simp[] >>
      irule ifexp_forced_marked_prefix_mem >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[])
  >- (qexists_tac `marks ++ marks'` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
      irule ifexp_forced_marked_prefix_mem >> goal_assum (drule_at Any) >> simp[] >>
      metis_tac[]) >>
  qexists_tac `marks ++ marks'` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >>
  rewrite_tac[GSYM ignore_bind_def] >>
  rewrite_tac[ifexp_root_eval_forced] >>
  pure_once_rewrite_tac[ignore_bind_def] >>
  pure_once_rewrite_tac[bind_assoc] >>
  irule gas_exempt_cert_bind_value >>
  qexistsl_tac [`mid`,`v`,`BoolV sel`] >> simp[] >>
  Cases_on `sel` >> gvs[GSYM ignore_bind_def] >>
  irule ifexp_read_conditional_cert >> simp[]
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

(* Concrete producer diagnostic: a Name annotation need not match its entry. *)
Theorem ifexp_name_literal_ptr_compile_probe[local]:
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Lit w) sz) ==>
  compile_expr cenv ty (Name (FlagT nsid) id) sa =
    (LocatedValue (FlagT nsid) (mk_ptr (Lit w) LocMemory),sa) /\
  lower_value compile_expr cenv ty (Name (FlagT nsid) id) sa =
    emit_op MLOAD [Lit w] sa
Proof
  simp[compile_expr_def, compile_name_vv_def, expr_type_def, lower_value_def,
       unwrap_value_def, is_word_type_def, contextTheory.mk_ptr_def,
       contextTheory.compile_ptr_load_def, comp_return_def, comp_bind_def]
QED

Theorem ifexp_name_source_probe[local]:
  lookup_scopes id es.scopes = SOME entry ==>
  eval_expr cx (Name (FlagT nsid) id) es =
    (INL (PlaceR (MemoryPlace id [])),es) /\
  bind (eval_expr cx (Name (FlagT nsid) id)) (read_result cx) es =
    (INL entry.value,es)
Proof
  simp[evaluate_def, get_scopes_def, type_check_def,
       vyperStateTheory.assert_def, ignore_bind_def, bind_def, return_def, read_result_def, read_place_def,
       lift_option_type_def, lift_sum_def, read_memory_path_def,
       evaluate_subscripts_def]
QED

Theorem ifexp_name_forced_admissible_probe[local]:
  lookup_scopes id es.scopes = SOME entry ==>
  gas_admissible
    (bind (eval_expr cx (Name (FlagT nsid) id)) (read_result cx))
    expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  `lookup_scopes id (es with gas_obs := gs).scopes = SOME entry` by simp[] >>
  drule ifexp_name_source_probe >> strip_tac >> gvs[expr_res_ok_def]
QED

Theorem gas_outcome_total_success_summary[local]:
  (!prefix. ?tail v st.
     source (es with gas_obs := prefix ++ tail) = (INL v,st)) /\
  gas_outcome memory tops (ctx,func) source (es,s0) Q R ==>
  ?marks. gas_summary_at memory (ctx,func) marks source (es,s0) Q R
Proof
  rw[gas_outcome_def] >- metis_tac[] >>
  drule gas_exempt_cert_execution >> strip_tac >>
  qpat_x_assum `!prefix. ?tail v st. _`
    (qspec_then `gas_explicit marks s0.vs_gas_readings` strip_assume_tac) >>
  qpat_x_assum `!tail. _` (qspec_then `tail` mp_tac) >>
  simp[ignore_bind_def, bind_def, return_def]
QED

Theorem ifexp_name_forced_summary_probe[local]:
  lookup_scopes id es.scopes = SOME entry /\
  gas_outcome memory tops (ctx,func)
    (bind (eval_expr cx (Name (FlagT nsid) id)) (read_result cx))
    (es,s0) Q R ==>
  ?marks. gas_summary_at memory (ctx,func) marks
    (bind (eval_expr cx (Name (FlagT nsid) id)) (read_result cx))
    (es,s0) Q R
Proof
  strip_tac >> irule gas_outcome_total_success_summary >>
  conj_tac
  >- (gen_tac >> qexists_tac `[]` >> simp[] >>
      `lookup_scopes id (es with gas_obs := prefix).scopes = SOME entry` by simp[] >>
      drule ifexp_name_source_probe >> metis_tac[]) >>
  qexists_tac `tops` >> first_assum ACCEPT_TAC
QED

Theorem gas_path_mem_ok_first_edge[local]:
  gas_path_mem ctx fn s n (OK z) /\ z <> s ==>
  ?k u. gas_path_mem_edge ctx fn s k (OK u)
Proof
  strip_tac >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
  simp[Once gas_path_mem_cases, exit_result_def] >> metis_tac[]
QED

Theorem gas_path_mem_first_mload_bound[local]:
  gas_path_mem ctx fn s n (OK z) /\ z <> s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id MLOAD [op] outs) /\
  ~revert_forward_at bb s.vs_inst_idx ==>
  !w. eval_operand op s = SOME w ==> w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >> drule_all gas_path_mem_ok_first_edge >> strip_tac >>
  gvs[gas_path_mem_edge_def] >>
  fs[mem_safe_step_non_invoke, mk_inst_def] >>
  qpat_x_assum `inst_mem_below_frontier _ _` mp_tac >>
  rewrite_tac[GSYM mk_inst_def, below_frontier_MLOAD] >> simp[]
QED

(* A successful forced Name outcome checks the load even when its FlagT
   annotation has no evaluated type.  The endpoint must be beyond entry. *)
Theorem ifexp_name_forced_frontier_probe[local]:
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Lit w) sz) /\
  emit_op MLOAD [Lit w] sa = (op,sb) /\
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx (Name (FlagT nsid) name)) (read_result cx))
    (es,s0)
    (\res ee z. z.vs_current_bb = sb.cs_current_bb /\
                z.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r) /\
  ~(s0.vs_current_bb = sb.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sb.cs_current_insts) /\
  lookup_block s0.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s0.vs_inst_idx = SOME (mk_inst iid MLOAD [Lit w] outs) /\
  ~revert_forward_at bb s0.vs_inst_idx ==>
  w2n w + 32 <= s0.vs_alloca_next
Proof
  strip_tac >> drule_all ifexp_name_forced_summary_probe >> strip_tac >>
  gvs[gas_summary_at_def, gas_marked_exec_def, gas_marked_path_def]
  >- (`z <> s0` by metis_tac[] >>
      drule gas_path_mem_first_mload_bound >>
      disch_then (qspecl_then [`outs`, `Lit w`, `iid`, `bb`, `w`] mp_tac) >>
      simp[eval_operand_def]) >>
  qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
  `lookup_scopes name
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings).scopes =
    SOME entry` by simp[] >>
  drule ifexp_name_source_probe >>
  disch_then (qspecl_then [`nsid`, `cx`] strip_assume_tac) >>
  simp[] >> strip_tac >>
  gvs[expr_exit_def]
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

Theorem ifexp_gas_explicit_empty[local]:
  !marks. gas_explicit marks [] = REPLICATE (LENGTH (FILTER I marks)) 0w
Proof
  Induct >> simp[gas_explicit_cons] >> Cases_on `h` >> simp[gas_explicit_cons]
QED

(* The all-zero target observation stream cannot hide a bad zero-gas arm
   behind a different choice of explicit marks.  This is an obstruction
   to the proposed single-GAS, total-raw-success witness family. *)
Theorem ifexp_zero_stream_raw_sim_obstruction[local]:
  (!prefix. ?tail raw ee.
     eval_expr cx e (es with gas_obs := prefix ++ tail) = (INL raw,ee)) /\
  (!n raw ee. eval_expr cx e (es with gas_obs := REPLICATE n 0w) =
       (INL raw,ee) ==>
     ~(?v. read_result cx raw (ee with gas_obs := []) =
            (INL v,ee with gas_obs := []))) /\
  compile_expr cenv ty e sa = (vv,sb) /\
  s0.vs_gas_readings = [] /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ~expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> strip_tac >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_vv_sim_mem_def] >>
  disch_then (qspecl_then [`sa`,`sb`,`vv`,`s0`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all gas_outcome_total_success_summary >> strip_tac >>
  gvs[gas_summary_at_def, gas_marked_exec_def]
  >- (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >>
      simp[ifexp_gas_explicit_empty] >> strip_tac >>
      qpat_x_assum `!n raw ee. _` drule >>
      simp[] >>
      qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac >>
      Cases_on `vv`
      >- (simp[vv_post_def, vv_holds_def] >> metis_tac[]) >>
      Cases_on `p.ptr_location` >>
      simp[vv_post_def, vv_holds_def, storage_holds_def, immutable_holds_def] >>
      metis_tac[]) >>
  qpat_x_assum `!prefix. ?tail raw ee. _`
    (qspec_then `gas_explicit marks []` strip_assume_tac) >>
  qpat_x_assum `!tail. _` (qspec_then `tail` mp_tac) >>
  simp[] >> strip_tac >> gvs[expr_exit_def]
QED

(* gas_source_bind_normal and gas_source_bind_exception already provide
   the all-tail success composition and short-circuit boundaries. *)
Theorem ifexp_next_gas_tail[local]:
  !tail. next_gas_reading (es with gas_obs := w::tail) =
    (INL (IntV (&w2n (w:bytes32))),es with gas_obs := tail)
Proof
  simp[next_gas_reading_def, return_def]
QED

Theorem ifexp_next_gas_exhausted[local]:
  next_gas_reading (es with gas_obs := []) =
    (INR (Error (RuntimeError "msg.gas: no gas reading")),es with gas_obs := [])
Proof
  simp[next_gas_reading_def, raise_def]
QED

Theorem ifexp_gas_zero_test_source[local]:
  es.gas_obs = w::ws ==>
  eval_expr cx
    (Builtin (BaseT BoolT) (Bop Eq)
      [Builtin (BaseT (UintT 256)) (Env MsgGas) [];
       Literal (BaseT (UintT 256)) (IntL 0)]) es =
  (INL (Value (BoolV (HD (es.gas_obs ++ [0w]) = 0w))),
   es with gas_obs := TL es.gas_obs)
Proof
  strip_tac >>
  simp[evaluate_def, next_gas_reading_def, bind_def, return_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       vyperContextTheory.builtin_args_length_ok_def,
       read_result_def] >>
  simp[get_accounts_def, vyperContextTheory.evaluate_builtin_def,
       expr_type_def, vyperValueOperationTheory.evaluate_literal_def,
       vyperValueOperationTheory.evaluate_binop_def, lift_sum_def,
       return_def, bind_def]
QED

Theorem ifexp_malformed_subscript_source[local]:
  es.scopes =
    [FEMPTY |+ ("x", <| assignable := T;
       type := ArrayTV (ArrayTV (BaseTV BoolT) (Fixed 1)) (Fixed 1);
       value := BoolV F; popped := [] |>)] ==>
  eval_expr cx
    (Subscript (FlagT nsid)
      (Name (ArrayT (ArrayT (BaseT BoolT) (Fixed 1)) (Fixed 1)) "x")
      (Literal (BaseT (UintT 256)) (IntL 0))) es =
  (INR (Error (TypeError "evaluate_subscripts type")),es)
Proof
  strip_tac >>
  simp[evaluate_def, select_result_def, extend_place_def,
       get_scopes_def, type_check_def, vyperStateTheory.assert_def,
       ignore_bind_def, bind_def, return_def, lookup_scopes_def,
       read_result_def, vyperValueOperationTheory.evaluate_literal_def,
       place_type_value_def, read_place_def, read_memory_path_def,
       evaluate_subscripts_def, lift_option_type_def, lift_sum_def,
       finite_mapTheory.FLOOKUP_UPDATE, finite_mapTheory.FLOOKUP_EMPTY] >>
  gvs[lookup_scopes_def, read_popped_def, lift_option_type_def, lift_sum_def,
      bind_def, return_def, raise_def] >> EVAL_TAC >>
  simp[lookup_scopes_def, lift_option_type_def, lift_sum_def,
       bind_def, return_def, raise_def] >> EVAL_TAC
QED

(* Exact history-domain boundary; no typing or reachability premise. *)
Theorem ifexp_memory_path_type_error[local]:
  read_memory_path entry path = INR (TypeError msg) <=>
  evaluate_subscripts entry.type entry.value path = INR (TypeError msg) /\
  read_popped entry.type path entry.popped = NONE
Proof
  simp[read_memory_path_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ifexp_pop_conditional_readback[local]:
  pop_place cx (MemoryPlace id path) es =
    (INL (PlaceR (MemoryPlace outid outpath)),ee) /\
  conditional_result cx (PlaceR (MemoryPlace outid outpath)) ee = (INL tv,ee) ==>
  ?v. read_result cx (PlaceR (MemoryPlace outid outpath)) ee = (INL v,ee)
Proof
  strip_tac >> Cases_on `find_containing_scope id es.scopes`
  >- gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def, return_def, raise_def] >>
  PairCases_on `x` >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       lift_sum_def, return_def, raise_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> gvs[return_def, raise_def, AllCaseEqs()] >>
  Cases_on `arr` >> gvs[return_def, raise_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[return_def, raise_def, vyperStateTheory.check_def,
      ignore_bind_def, bind_def, vyperStateTheory.assert_def] >>
  gvs[vyperValueOperationTheory.popped_value_def,
      vyperValueOperationTheory.pop_element_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >>
  gvs[bind_def, set_scopes_def, return_def, AllCaseEqs(), raise_def] >>
  drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
  gvs[conditional_result_def, place_type_value_def, bind_def, get_scopes_def,
      vyperLookupTheory.lookup_scopes_update, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `subscripts_type x2.type (path ++ [ValueSubscript (IntV &(LENGTH l - 1))])` >>
  gvs[return_def, raise_def] >>
  simp[read_result_def, read_place_def, get_scopes_def, bind_def,
       vyperLookupTheory.lookup_scopes_update, lift_option_type_def,
       return_def, read_memory_path_def, record_pop_def] >>
  simp[read_popped_def, evaluate_subscripts_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts x2.type x0' (path ++ [ValueSubscript (IntV &(LENGTH l - 1))])` >>
  simp[return_def]
QED

Theorem ifexp_malformed_pop_source[local]:
  es.scopes =
    [FEMPTY |+ ("x", <| assignable := T; type := BaseTV BoolT;
       value := ArrayV (DynArrayV [BoolV F]); popped := [] |>)] ==>
  ?ee. eval_expr cx (Pop (BaseT BoolT) (NameTarget "x")) es =
    (INL (PlaceR (MemoryPlace "x" [ValueSubscript (IntV 0)])),ee) /\
    read_result cx (PlaceR (MemoryPlace "x" [ValueSubscript (IntV 0)])) ee =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee) /\
    conditional_result cx (PlaceR (MemoryPlace "x" [ValueSubscript (IntV 0)])) ee =
    (INR (Error (TypeError "place_type_value path")),ee)
Proof
  Cases_on `es` >> simp[] >> strip_tac >> gvs[] >>
  simp[evaluate_def, conditional_result_def, place_type_value_def, get_scopes_def, type_check_def,
       vyperStateTheory.assert_def, ignore_bind_def, bind_def, return_def,
       lookup_scopes_def, get_place_def, pop_place_def,
       find_containing_scope_def, read_memory_path_def, evaluate_subscripts_def,
       lift_option_type_def, lift_sum_def, read_result_def, read_place_def,
       set_scopes_def, record_pop_def, read_popped_def, subscripts_type_def] >>
  gvs[] >> EVAL_TAC >> simp[] >> EVAL_TAC
QED

Theorem ifexp_pop_index_source[local]:
  es.scopes =
    [FEMPTY |+ ("x", <| assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
       value := ArrayV (DynArrayV [IntV 0]); popped := [] |>)] ==>
  ?ee. eval_expr cx
    (Subscript (BaseT (UintT 256))
      (Name (ArrayT (BaseT (UintT 256)) (Dynamic 1)) "x")
      (Pop (BaseT (UintT 256)) (NameTarget "x"))) es =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)
Proof
  Cases_on `es` >> simp[] >> strip_tac >> gvs[] >>
  simp[evaluate_def, get_scopes_def, type_check_def,
       vyperStateTheory.assert_def, ignore_bind_def, bind_def, return_def,
       lookup_scopes_def, get_place_def, pop_place_def,
       find_containing_scope_def, read_memory_path_def, evaluate_subscripts_def,
       lift_option_type_def, lift_sum_def, read_result_def, read_place_def,
       set_scopes_def, record_pop_def, read_popped_def, subscripts_type_def,
       select_result_def, extend_place_def, place_type_value_def,
       extend_memory_place_def] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_AX))) >> simp[]
QED

(* Primitive snapshot-rescued Pop: the child snapshot has no type metadata. *)
Theorem ifexp_snapshot_pop_child_probe[local]:
  es.scopes =
    [FEMPTY |+ ("x", <| assignable := T;
       type := ArrayTV (BaseTV BoolT) (Dynamic 1); value := BoolV F;
       popped := [([],ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])]))] |>)] ==>
  ?ee. pop_place cx (MemoryPlace "x" [ValueSubscript (IntV 0)]) es =
    (INL (PlaceR (MemoryPlace "x"
      [ValueSubscript (IntV 0); ValueSubscript (IntV 0)])),ee) /\
    read_result cx (PlaceR (MemoryPlace "x"
      [ValueSubscript (IntV 0); ValueSubscript (IntV 0)])) ee =
    (INR (Error (TypeError "evaluate_subscripts type")),ee)
Proof
  Cases_on `es` >> simp[] >> strip_tac >> gvs[] >>
  simp[get_scopes_def, type_check_def,
       vyperStateTheory.assert_def, ignore_bind_def, bind_def, return_def,
       lookup_scopes_def, pop_place_def,
       find_containing_scope_def, read_memory_path_def, evaluate_subscripts_def,
       lift_option_type_def, lift_sum_def, read_result_def, read_place_def,
       set_scopes_def, record_pop_def, read_popped_def, subscripts_type_def] >>
  EVAL_TAC >> simp[return_def, bind_def, lift_sum_def, raise_def] >> EVAL_TAC >>
  simp[lookup_scopes_def, return_def, bind_def, lift_sum_def, raise_def] >> EVAL_TAC >>
  simp[return_def, raise_def] >> EVAL_TAC
QED

(* The corresponding target rejects the malformed current root before Pop. *)
Theorem ifexp_snapshot_pop_target_rejected[local]:
  es.scopes =
    [FEMPTY |+ ("x", <| assignable := T;
       type := ArrayTV (BaseTV BoolT) (Dynamic 1); value := BoolV F;
       popped := [([],ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])]))] |>)] ==>
  eval_target_place cx
    (SubscriptTarget (NameTarget "x") (Literal (BaseT (UintT 256)) (IntL 0))) es =
    (INR (Error (TypeError "evaluate_subscripts type")),es)
Proof
  Cases_on `es` >> simp[] >> strip_tac >> gvs[] >>
  simp[evaluate_def, get_scopes_def, type_check_def,
       vyperStateTheory.assert_def, ignore_bind_def, bind_def, return_def,
       lookup_scopes_def, get_place_def, extend_place_def, place_type_value_def,
       read_place_def, read_memory_path_def, evaluate_subscripts_def,
       lift_option_type_def, lift_sum_def, read_result_def, raise_def] >> EVAL_TAC
QED

Theorem ifexp_current_error_append[local]:
  !tv value path. !msg suffix.
    evaluate_subscripts tv value path = INR (RuntimeError msg) ==>
    evaluate_subscripts tv value (path ++ suffix) = INR (RuntimeError msg)
Proof
  recInduct evaluate_subscripts_ind >> rpt strip_tac >>
  gvs[evaluate_subscripts_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem ifexp_current_extension_domain[local]:
  subscripts_type entry.type path = SOME ptv /\
  (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg)) /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts ptv v [sb] = INL w ==>
  !msg. evaluate_subscripts entry.type entry.value (path ++ [sb]) <> INR (TypeError msg)
Proof
  rpt strip_tac >> Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >>
      drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
      disch_then (qspec_then `[sb]` mp_tac) >> simp[]) >>
  drule evaluate_subscripts_error_shape >> strip_tac
  >- (gvs[] >> drule ifexp_current_error_append >>
      disch_then (qspec_then `[sb]` assume_tac) >> gvs[]) >>
  metis_tac[]
QED

Theorem ifexp_replace_path_runtime[local]:
  !path tv value replacement updated suffix msg.
    assign_subscripts tv value path (Replace replacement) = INL updated /\
    (!ptv. evaluate_subscripts ptv replacement suffix = INR (RuntimeError msg)) ==>
    evaluate_subscripts tv updated (path ++ suffix) = INR (RuntimeError msg)
Proof
  Induct >> rpt gen_tac
  >- (simp[assign_subscripts_def, evaluate_subscripts_def] >> metis_tac[]) >>
  Cases_on `h`
  >- (Cases_on `v` >> Cases_on `value` >>
      simp[assign_subscripts_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >>
      `?av. updated = ArrayV av` by
        (Cases_on `a` >> gvs[vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >> metis_tac[]) >>
      gvs[] >> drule vyperArrayTheory.array_index_after_set_same >> strip_tac >>
      first_x_assum drule_all >> simp[evaluate_subscripts_def]) >>
  Cases_on `value` >> simp[assign_subscripts_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >> first_x_assum drule_all >>
  simp[evaluate_subscripts_def, alistTheory.AFUPDKEY_ALOOKUP]
QED

Theorem ifexp_shortened_child_runtime[local]:
  vs <> [] ==>
  !tv. evaluate_subscripts tv (ArrayV (DynArrayV (FRONT vs)))
    [ValueSubscript (IntV &(LENGTH vs - 1))] =
    INR (RuntimeError "evaluate_subscripts array_index")
Proof
  Cases_on `vs` >> simp[] >>
  simp[evaluate_subscripts_def, vyperValueOperationTheory.array_index_def,
       listTheory.oEL_THM]
QED

Theorem ifexp_pop_read_domain[local]:
  lookup_scopes id es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg)) /\
  pop_place cx (MemoryPlace id path) es = (INL (PlaceR p),ee) /\
  read_result cx (PlaceR p) ee = (res,ef) ==>
  expr_res_ok res
Proof
  strip_tac >>
  Cases_on `find_containing_scope id es.scopes`
  >- gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def, return_def, raise_def] >>
  PairCases_on `x` >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       lift_sum_def, return_def, raise_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  Cases_on `arr` >> gvs[return_def, raise_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[return_def, raise_def, vyperStateTheory.check_def,
      ignore_bind_def, bind_def, vyperStateTheory.assert_def] >>
  gvs[vyperValueOperationTheory.popped_value_def,
      vyperValueOperationTheory.pop_element_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >>
  gvs[bind_def, set_scopes_def, return_def, AllCaseEqs(), raise_def] >>
  drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
  gvs[read_result_def, read_place_def, get_scopes_def, bind_def,
      lift_option_type_def, return_def, vyperLookupTheory.lookup_scopes_update] >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (Cases_on `assign_subscripts entry.type entry.value path
        (Replace (ArrayV (DynArrayV (FRONT l))))` >>
      gvs[return_def, raise_def] >>
      drule ifexp_replace_path_runtime >>
      disch_then (qspecl_then
        [`[ValueSubscript (IntV &(LENGTH l - 1))]`,
         `"evaluate_subscripts array_index"`] mp_tac) >>
      simp[ifexp_shortened_child_runtime] >> strip_tac >>
      gvs[read_memory_path_def, lift_sum_def, return_def, raise_def,
          AllCaseEqs(), expr_res_ok_def] >>
      Cases_on `read_popped entry.type
        (path ++ [ValueSubscript (IntV &(LENGTH l - 1))])
        (record_pop path (ArrayV (DynArrayV l)) (LAST l) entry.popped)` >>
      gvs[return_def, raise_def]) >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  Cases_on `replace_popped entry.type path
    (ArrayV (DynArrayV (FRONT l))) entry.popped` >> gvs[return_def, raise_def] >>
  drule evaluate_subscripts_error_shape >> strip_tac >> gvs[] >>
  drule ifexp_current_error_append >>
  disch_then (qspec_then `[ValueSubscript (IntV &(LENGTH l - 1))]` assume_tac) >>
  gvs[read_memory_path_def, lift_sum_def, return_def, raise_def, expr_res_ok_def] >>
  Cases_on `read_popped entry.type
    (path ++ [ValueSubscript (IntV &(LENGTH l - 1))])
    (record_pop path (ArrayV (DynArrayV l)) (LAST l) x)` >>
  gvs[return_def, raise_def]
QED

Theorem ifexp_front_domain[local]:
  !tv vs retained.
    (!msg. evaluate_subscripts tv (ArrayV (DynArrayV vs)) retained <> INR (TypeError msg)) ==>
    !msg. evaluate_subscripts tv (ArrayV (DynArrayV (FRONT vs))) retained <> INR (TypeError msg)
Proof
  rpt gen_tac >> Cases_on `retained` >> simp[evaluate_subscripts_def] >>
  Cases_on `h` >> simp[evaluate_subscripts_def] >>
  Cases_on `v` >> simp[evaluate_subscripts_def] >>
  Cases_on `vs = []` >- gvs[vyperValueOperationTheory.array_index_def] >>
  simp[vyperValueOperationTheory.array_index_def, listTheory.oEL_THM,
       rich_listTheory.LENGTH_FRONT] >>
  Cases_on `0 <= i` >> simp[] >>
  Cases_on `Num i < LENGTH vs - 1` >> simp[] >>
  `EL (Num i) (FRONT vs) = EL (Num i) vs` by
    (irule rich_listTheory.EL_FRONT >> simp[rich_listTheory.LENGTH_FRONT, listTheory.NULL_EQ]) >> simp[]
QED

Theorem ifexp_pop_replace_domain[local]:
  !mutation tv value vs updated retained.
    evaluate_subscripts tv value mutation = INL (ArrayV (DynArrayV vs)) /\
    assign_subscripts tv value mutation (Replace (ArrayV (DynArrayV (FRONT vs)))) = INL updated /\
    (!msg. evaluate_subscripts tv value retained <> INR (TypeError msg)) ==>
    !msg. evaluate_subscripts tv updated retained <> INR (TypeError msg)
Proof
  Induct >> rpt gen_tac
  >- (simp[evaluate_subscripts_def, assign_subscripts_def] >>
      metis_tac[ifexp_front_domain]) >>
  Cases_on `h`
  >- (Cases_on `v` >> Cases_on `value` >>
      simp[evaluate_subscripts_def, assign_subscripts_def] >> rpt strip_tac >>
      gvs[AllCaseEqs()] >>
      `?av. updated = ArrayV av` by
        (Cases_on `a` >> gvs[vyperValueOperationTheory.array_set_index_def, AllCaseEqs()] >> metis_tac[]) >>
      gvs[] >> Cases_on `retained` >- gvs[evaluate_subscripts_def] >>
      Cases_on `h` >> gvs[evaluate_subscripts_def] >>
      Cases_on `v'` >> gvs[evaluate_subscripts_def] >>
      Cases_on `i = i'`
      >- (gvs[] >> drule vyperArrayTheory.array_index_after_set_same >> strip_tac >>
          gvs[AllCaseEqs()] >> first_x_assum drule_all >> simp[]) >>
      `array_index tv av i' = array_index tv a i'` by
        (irule vyperArrayTheory.array_index_after_set_other >> metis_tac[]) >>
      gvs[]) >>
  Cases_on `value` >> simp[evaluate_subscripts_def, assign_subscripts_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  Cases_on `retained` >- gvs[evaluate_subscripts_def] >>
  Cases_on `h`
  >- (Cases_on `v'` >> gvs[evaluate_subscripts_def]) >>
  gvs[evaluate_subscripts_def] >> Cases_on `s = s'` >>
  gvs[alistTheory.AFUPDKEY_ALOOKUP, AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem ifexp_pop_retained_domain[local]:
  lookup_scopes keep es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) /\
  pop_place cx (MemoryPlace changed mutation) es = (INL result,ee) ==>
  ?entry'. lookup_scopes keep ee.scopes = SOME entry' /\
    entry'.type = entry.type /\
    (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  strip_tac >> Cases_on `find_containing_scope changed es.scopes`
  >- gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def, return_def, raise_def] >>
  PairCases_on `x` >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       lift_sum_def, return_def, raise_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  Cases_on `arr` >> gvs[return_def, raise_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[return_def, raise_def, vyperStateTheory.check_def,
      ignore_bind_def, bind_def, vyperStateTheory.assert_def] >>
  gvs[vyperValueOperationTheory.popped_value_def,
      vyperValueOperationTheory.pop_element_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >>
  gvs[bind_def, set_scopes_def, return_def, AllCaseEqs(), raise_def] >>
  drule vyperLookupTheory.find_containing_scope_structure >> strip_tac >>
  Cases_on `changed = keep`
  >- (gvs[] >>
      drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >> gvs[] >>
      drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
      simp[vyperLookupTheory.lookup_scopes_update] >>
      gvs[return_def, raise_def, AllCaseEqs()] >>
      gvs[read_memory_path_def, return_def, raise_def, AllCaseEqs()] >>
      Cases_on `evaluate_subscripts entry.type entry.value mutation` >>
      gvs[return_def, raise_def] >>
      Cases_on `assign_subscripts entry.type entry.value mutation
        (Replace (ArrayV (DynArrayV (FRONT l))))` >>
      gvs[return_def, raise_def] >>
      Cases_on `replace_popped entry.type mutation
        (ArrayV (DynArrayV (FRONT l))) entry.popped` >>
      gvs[return_def, raise_def] >>
      drule_all ifexp_pop_replace_domain >> simp[]) >>
  simp[vyperLookupTheory.lookup_scopes_update_other] >> metis_tac[]
QED

Theorem ifexp_call_cleanup_retained_domain[local]:
  lookup_scopes keep saved = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) /\
  finally f (do pop_function saved; unlock_if_nr cx nr is_view od) s = (res,ee) ==>
  lookup_scopes keep ee.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg))
Proof
  strip_tac >> gvs[unlock_if_nr_def] >>
  drule vyperPlaceResultTypingTheory.finally_conditional_lock_scopes >> simp[]
QED

Theorem ifexp_defaults_retained_domain[local]:
  lookup_scopes keep saved = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) /\
  finally (do set_scopes [FEMPTY]; defaults od) (set_scopes saved) s = (res,ee) ==>
  lookup_scopes keep ee.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg))
Proof
  strip_tac >> drule vyperScopePreservationTheory.finally_set_scopes >> simp[]
QED

Theorem ifexp_entry_pop_read_obstruction[local]:
  entry = <| assignable := T; type := BaseTV BoolT;
    value := ArrayV (DynArrayV [BoolV F]); popped := [] |> /\
  entry' = entry with <|value := ArrayV (DynArrayV []);
    popped := [([ValueSubscript (IntV 0)], BoolV F)]|> ==>
  entry_pop_step entry [] entry' /\
  read_memory_path entry [ValueSubscript (IntV 0)] = INL (BoolV F) /\
  read_memory_path entry' [ValueSubscript (IntV 0)] =
    INR (RuntimeError "evaluate_subscripts array_index")
Proof
  rpt strip_tac >> gvs[] >>
  simp[vyperPlaceResultTypingTheory.entry_pop_step_def,
       read_memory_path_def, evaluate_subscripts_def, read_popped_def,
       record_pop_def, subscripts_type_def, subscript_type_def,
       vyperValueOperationTheory.popped_value_def,
       vyperValueOperationTheory.pop_element_def,
       assign_subscripts_def] >> EVAL_TAC >> simp[]
QED

Theorem ifexp_entry_pop_metadata_probe[local]:
  !historical.
  entry = <|assignable := T;
    type := ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1);
    value := ArrayV (DynArrayV (if historical then [] else
      [ArrayV (DynArrayV [IntV 7]) ]));
    popped := if historical then
      [([ValueSubscript (IntV 0)], ArrayV (DynArrayV [IntV 7]))] else []|> /\
  entry' = entry with <|
    value := ArrayV (DynArrayV (if historical then [] else [ArrayV (DynArrayV [])]));
    popped := ([ValueSubscript (IntV 0);ValueSubscript (IntV 0)], IntV 7)::
      (if historical then
        [([ValueSubscript (IntV 0)],ArrayV (DynArrayV []))] else [])|> ==>
  entry_pop_step entry [ValueSubscript (IntV 0)] entry' /\
  subscripts_type entry.type [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] =
    SOME (BaseTV BoolT) /\
  read_memory_path entry [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] = INL (IntV 7) /\
  read_memory_path entry' [ValueSubscript (IntV 0);ValueSubscript (IntV 0)] = INL (IntV 7) /\
  read_memory_path entry' [ValueSubscript (IntV 0)] = INL (ArrayV (DynArrayV []))
Proof
  Cases_on `historical` >> rpt strip_tac >> gvs[] >>
  simp[vyperPlaceResultTypingTheory.entry_pop_step_def,
       read_memory_path_def, evaluate_subscripts_def, read_popped_def,
       replace_popped_def, record_pop_def, subscripts_type_def, subscript_type_def,
       vyperValueOperationTheory.popped_value_def,
       vyperValueOperationTheory.pop_element_def, assign_subscripts_def] >>
  EVAL_TAC >> simp[vyperValueOperationTheory.popped_value_def,
    vyperValueOperationTheory.pop_element_def, oEL_THM]
QED
Theorem ifexp_read_popped_extend[local]:
  !history ty path pty v suffix w.
    subscripts_type ty path = SOME pty /\
    read_popped ty path history = SOME v /\
    evaluate_subscripts pty v suffix = INL w ==>
    ?z. read_popped ty (path ++ suffix) history = SOME z
Proof
  Induct >- simp[read_popped_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[read_popped_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()]
  >- (first_x_assum drule_all >> strip_tac >> qexists_tac `z` >> metis_tac[])
  >- (drule_all vyperPlaceResultTypingTheory.read_popped_snapshot_extend >>
      strip_tac >> qexists_tac `w` >> simp[])
  >- (first_x_assum drule_all >> strip_tac >>
      Cases_on `IS_PREFIX (path ++ suffix) h0` >> simp[] >>
      Cases_on `evaluate_subscripts ptv h1 (DROP (LENGTH h0) (path ++ suffix))` >>
      gvs[] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `IS_PREFIX (path ++ suffix) h0` >> simp[] >>
  Cases_on `subscripts_type ty h0` >> simp[] >>
  Cases_on `evaluate_subscripts x h1 (DROP (LENGTH h0) (path ++ suffix))` >>
  gvs[] >> metis_tac[]
QED

Theorem ifexp_read_memory_extend[local]:
  subscripts_type entry.type path = SOME pty /\
  read_memory_path entry path = INL v /\
  evaluate_subscripts pty v suffix = INL w ==>
  ?z. read_memory_path entry (path ++ suffix) = INL z
Proof
  strip_tac >> Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (gvs[read_memory_path_def] >>
      drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
      simp[read_memory_path_def]) >>
  gvs[read_memory_path_def, AllCaseEqs()] >>
  drule_all ifexp_read_popped_extend >> strip_tac >>
  Cases_on `evaluate_subscripts entry.type entry.value (path ++ suffix)` >>
  simp[]
QED

Theorem ifexp_extend_memory_readback[local]:
  extend_place cx (PlaceR (MemoryPlace id path)) sb es =
    (INL (PlaceR (MemoryPlace outid outpath)),ee) /\
  conditional_result cx (PlaceR (MemoryPlace outid outpath)) ee = (INL tv,ee) ==>
  ?v. read_result cx (PlaceR (MemoryPlace outid outpath)) ee = (INL v,ee)
Proof
  simp[extend_place_def, place_type_value_def, read_place_def,
       bind_def, get_scopes_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, extend_memory_place_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[return_def, raise_def, ignore_bind_def, bind_def, AllCaseEqs()] >>
  Cases_on `lookup_scopes id es.scopes` >> gvs[return_def, raise_def] >>
  rename1 `lookup_scopes id es.scopes = SOME retained_entry` >>
  Cases_on `subscripts_type retained_entry.type path` >> gvs[return_def, raise_def] >>
  rename1 `subscripts_type retained_entry.type path = SOME retained_ty` >>
  Cases_on `read_memory_path retained_entry path` >> gvs[return_def, raise_def] >>
  rename1 `read_memory_path retained_entry path = INL retained_val` >>
  Cases_on `evaluate_subscripts retained_ty retained_val [sb]` >> gvs[return_def, raise_def] >>
  drule_all ifexp_read_memory_extend >> strip_tac >>
  simp[read_result_def, read_place_def, bind_def, get_scopes_def,
       lift_option_type_def, lift_sum_def, return_def, raise_def]
QED


Theorem ifexp_entry_pop_domain[local]:
  entry_pop_step entry mutation entry' /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) ==>
  entry'.type = entry.type /\
  (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  simp[vyperPlaceResultTypingTheory.entry_pop_step_def] >> rpt strip_tac >> gvs[] >>
  gvs[read_memory_path_def, AllCaseEqs()] >>
  Cases_on `arr` >> gvs[vyperValueOperationTheory.popped_value_def,
    vyperValueOperationTheory.pop_element_def, AllCaseEqs()] >>
  Cases_on `a` >> gvs[vyperValueOperationTheory.pop_element_def, AllCaseEqs()] >>
  drule_all ifexp_pop_replace_domain >> simp[]
QED

Theorem ifexp_scope_pop_trace_domain[local]:
  !events sc final keep entry retained.
    scope_pop_trace sc events final /\ lookup_scopes keep sc = SOME entry /\
    (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) ==>
    ?entry'. lookup_scopes keep final = SOME entry' /\ entry'.type = entry.type /\
      (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  Induct >- simp[vyperPlaceResultTypingTheory.scope_pop_trace_def] >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp[vyperPlaceResultTypingTheory.scope_pop_trace_def] >> strip_tac >>
  Cases_on `h0 = keep`
  >- (gvs[] >> drule vyperPlaceResultTypingTheory.scope_pop_step_lookup >>
      strip_tac >> gvs[] >> drule_all ifexp_entry_pop_domain >> strip_tac >>
      first_x_assum drule_all >> metis_tac[]) >>
  drule_all vyperPlaceResultTypingTheory.scope_pop_step_lookup_other >> strip_tac >>
  gvs[] >> first_x_assum drule_all >> simp[]
QED

Theorem ifexp_scope_pop_effect_domain[local]:
  scope_pop_effect f /\ f es = (res,ee) /\
  lookup_scopes keep es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) ==>
  ?entry'. lookup_scopes keep ee.scopes = SOME entry' /\ entry'.type = entry.type /\
    (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  simp[vyperPlaceResultTypingTheory.scope_pop_effect_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> drule_all ifexp_scope_pop_trace_domain >> simp[]
QED

Theorem ifexp_eval_expr_retained_domain[local]:
  eval_expr cx e es = (res,ee) /\ lookup_scopes keep es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) ==>
  ?entry'. lookup_scopes keep ee.scopes = SOME entry' /\ entry'.type = entry.type /\
    (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  strip_tac >>
  `scope_pop_effect (eval_expr cx e)` by
    metis_tac[vyperPlaceResultTypingTheory.eval_mutual_scope_pop_effect] >>
  drule_all ifexp_scope_pop_effect_domain >> simp[]
QED

Theorem ifexp_expr_results_pop_effect[local]:
  !args cx. scope_pop_effect (eval_expr_results cx args)
Proof
  Induct >> simp[Once evaluate_def] >> rpt gen_tac >>
  irule vyperPlaceResultTypingTheory.scope_pop_effect_bind >> conj_tac
  >- (gen_tac >> simp[] >> irule vyperPlaceResultTypingTheory.scope_pop_effect_bind >> simp[]) >>
  metis_tac[vyperPlaceResultTypingTheory.eval_mutual_scope_pop_effect]
QED

Theorem ifexp_eval_expr_results_retained_domain[local]:
  eval_expr_results cx args es = (res,ee) /\ lookup_scopes keep es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value retained <> INR (TypeError msg)) ==>
  ?entry'. lookup_scopes keep ee.scopes = SOME entry' /\ entry'.type = entry.type /\
    (!msg. evaluate_subscripts entry'.type entry'.value retained <> INR (TypeError msg))
Proof
  strip_tac >>
  qspecl_then [`args`, `cx`] assume_tac ifexp_expr_results_pop_effect >>
  drule_all ifexp_scope_pop_effect_domain >> simp[]
QED

Theorem ifexp_extend_memory_domain[local]:
  lookup_scopes id es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg)) /\
  extend_place cx (PlaceR (MemoryPlace id path)) sb es = (INL out,ee) ==>
  out = PlaceR (MemoryPlace id (path ++ [sb])) /\ ee = es /\
  (!msg. evaluate_subscripts entry.type entry.value (path ++ [sb]) <> INR (TypeError msg))
Proof
  simp[extend_place_def, place_type_value_def, read_place_def, get_scopes_def,
       bind_def, ignore_bind_def, lift_option_type_def, return_def, raise_def,
       lift_sum_def, extend_memory_place_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  gvs[return_def, raise_def, AllCaseEqs()] >>
  Cases_on `subscripts_type entry.type path` >> gvs[return_def, raise_def] >>
  Cases_on `read_memory_path entry path` >> gvs[return_def, raise_def] >>
  rename1 `evaluate_subscripts tv rv [sb]` >>
  Cases_on `evaluate_subscripts tv rv [sb]` >> gvs[return_def, raise_def] >>
  drule_all ifexp_current_extension_domain >> simp[]
QED

Theorem ifexp_extend_memory_origin[local]:
  extend_place cx pv sb es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  ?base. pv = PlaceR (MemoryPlace id base) /\ path = base ++ [sb]
Proof
  Cases_on `pv`
  >- simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p` >>
      simp[extend_place_def, bind_def, ignore_bind_def, return_def,
           raise_def, extend_memory_place_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[AllCaseEqs()] >>
      qmatch_asmsub_rename_tac `extend_storage_place cx tr slot tv sub es` >>
      qpat_x_assum `extend_storage_place _ _ _ _ _ _ = _` mp_tac >>
      Cases_on `sub`
      >- (rename1 `ValueSubscript v` >> Cases_on `v` >> Cases_on `tv` >>
          simp[extend_storage_place_def, bind_def, ignore_bind_def,
               lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
          rpt strip_tac >> gvs[return_def, raise_def, AllCaseEqs()] >>
          pairarg_tac >> gvs[return_def, raise_def, AllCaseEqs()]) >>
      Cases_on `tv` >>
      simp[extend_storage_place_def, bind_def, ignore_bind_def,
           lift_option_type_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[return_def, raise_def, AllCaseEqs()] >>
          pairarg_tac >> gvs[return_def, raise_def, AllCaseEqs()]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, lift_option_type_def, return_def,
       raise_def, value_type_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED

Theorem ifexp_base_place_memory_domain[local]:
  !bt cx es id path ee.
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  ?entry. lookup_scopes id ee.scopes = SOME entry /\
    (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg))
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
  rpt gen_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, type_check_def,
       assert_def, check_def, ignore_bind_def, return_def, raise_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
  >- (Cases_on `lookup_scopes id ee.scopes` >> gvs[evaluate_subscripts_def])
  >- (PairCases_on `p` >>
      gvs[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def, get_immutables_def, AllCaseEqs()] >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.prod_CASE_rator,
          var_decl_info_CASE_rator, bind_def, return_def, raise_def, AllCaseEqs()] >>
      gvs[bind_def, return_def, raise_def, AllCaseEqs()]) >>
  drule ifexp_extend_memory_origin >> strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  first_x_assum drule >> strip_tac
  >- (drule read_result_state >> strip_tac >> gvs[] >>
      drule_all ifexp_eval_expr_retained_domain >> strip_tac >>
      drule_all ifexp_extend_memory_domain >> strip_tac >> gvs[] >>
      metis_tac[]) >>
  drule_all ifexp_extend_memory_domain >> strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ifexp_target_place_memory_domain[local]:
  eval_target_place cx bt es = (INL (MemoryPlace id path),ee) ==>
  ?entry. lookup_scopes id ee.scopes = SOME entry /\
    (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg))
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule ifexp_base_place_memory_domain >> simp[]
QED

Theorem ifexp_conditional_memory_origin[local]:
  conditional_result cx res es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  res = PlaceR (MemoryPlace id path) /\ ee = es
Proof
  Cases_on `res` >>
  simp[conditional_result_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[COND_RATOR, return_def, bind_def, AllCaseEqs()] >>
  drule place_type_value_state >> simp[]
QED

Theorem ifexp_select_memory_origin[local]:
  select_result cx ty res sb es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  extend_place cx res sb es = (INL (PlaceR (MemoryPlace id path)),ee)
Proof
  Cases_on `res` >>
  simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[return_def, raise_def, AllCaseEqs()]
QED

Theorem ifexp_pop_memory_origin[local]:
  pop_place cx p es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  ?baseid base. p = MemoryPlace baseid base
Proof
  Cases_on `p`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      simp[pop_place_def, raise_def] >>
      rename1 `ArrayTV tv bd` >> Cases_on `bd` >>
      simp[pop_place_def, bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()])
  >- simp[] >>
  simp[pop_place_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Theorem ifexp_pop_memory_domain[local]:
  lookup_scopes id es.scopes = SOME entry /\
  (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg)) /\
  pop_place cx (MemoryPlace id path) es = (INL (PlaceR (MemoryPlace outid outpath)),ee) ==>
  ?entry'. lookup_scopes outid ee.scopes = SOME entry' /\
    (!msg. evaluate_subscripts entry'.type entry'.value outpath <> INR (TypeError msg))
Proof
  strip_tac >> Cases_on `find_containing_scope id es.scopes`
  >- gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def, return_def, raise_def] >>
  PairCases_on `x` >>
  drule vyperLookupTheory.find_containing_scope_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `pop_place _ _ _ = _` mp_tac >>
  simp[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
       type_check_def, vyperStateTheory.assert_def, ignore_bind_def,
       lift_sum_def, return_def, raise_def] >>
  strip_tac >> gvs[AllCaseEqs()] >> gvs[return_def, raise_def, AllCaseEqs()] >>
  Cases_on `arr` >> gvs[return_def, raise_def] >>
  rename1 `ArrayV av` >> Cases_on `av` >>
  gvs[return_def, raise_def, vyperStateTheory.check_def,
      ignore_bind_def, bind_def, vyperStateTheory.assert_def] >>
  gvs[vyperValueOperationTheory.popped_value_def,
      vyperValueOperationTheory.pop_element_def, AllCaseEqs(), return_def, raise_def] >>
  PairCases_on `x` >>
  gvs[bind_def, set_scopes_def, return_def, AllCaseEqs(), raise_def] >>
  drule vyperLookupTheory.find_containing_scope_pre_none >> strip_tac >>
  gvs[vyperLookupTheory.lookup_scopes_update] >>
  Cases_on `evaluate_subscripts entry.type entry.value path`
  >- (Cases_on `assign_subscripts entry.type entry.value path
        (Replace (ArrayV (DynArrayV (FRONT l))))` >>
      gvs[return_def, raise_def] >>
      drule ifexp_replace_path_runtime >>
      disch_then (qspecl_then
        [`[ValueSubscript (IntV &(LENGTH l - 1))]`,
         `"evaluate_subscripts array_index"`] mp_tac) >>
      simp[ifexp_shortened_child_runtime]) >>
  gvs[AllCaseEqs(), return_def, raise_def] >>
  Cases_on `replace_popped entry.type path
    (ArrayV (DynArrayV (FRONT l))) entry.popped` >> gvs[return_def, raise_def] >>
  drule evaluate_subscripts_error_shape >> strip_tac >> gvs[] >>
  drule ifexp_current_error_append >> simp[]
QED

Theorem ifexp_create_no_place[local]:
  eval_create cx kind salt rof tys vs bsize st <>
    (INL (PlaceR p),ee)
Proof
  strip_tac >>
  gvs[vyperCreateTheory.eval_create_def] >>
  gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
  gvs[COND_RATOR, bind_def, ignore_bind_def, return_def, raise_def,
      vyperCreateTheory.create_soft_failure_def, AllCaseEqs()]
  >- gvs[vyperCreateTheory.create_oracle_result_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, bind_def, ignore_bind_def,
      return_def, raise_def, COND_RATOR, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `run_create_evm _ _ _ _ _ _ _ _ = SOME tail` >>
  PairCases_on `tail` >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, COND_RATOR, AllCaseEqs()]
QED

Theorem ifexp_expr_memory_domain_mutual[local]:
  (!(cx:evaluation_context) (s:stmt). T) /\
  (!(cx:evaluation_context) (ss:stmt list). T) /\
  (!(cx:evaluation_context) (it:iterator). T) /\
  (!(cx:evaluation_context) (tyv:type_value) (nm:string) (body:stmt list) (vs:value list). T) /\
  (!cx e es id path ee.
    eval_expr cx e es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
    ?entry. lookup_scopes id ee.scopes = SOME entry /\
      (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg))) /\
  (!(cx:evaluation_context) (es:expr list). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (bt:base_assignment_target). T) /\
  (!(cx:evaluation_context) (g:assignment_target) (v:value). T) /\
  (!(cx:evaluation_context) (gs:assignment_target list) (vs:value list). T) /\
  (!(cx:evaluation_context) (es:expr list). T)
Proof
  ho_match_mp_tac evaluate_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[] >> rpt strip_tac
  >- (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, get_scopes_def, type_check_def, assert_def,
           check_def, bind_def, ignore_bind_def, return_def, raise_def,
           AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
      Cases_on `lookup_scopes id ee.scopes` >> gvs[evaluate_subscripts_def])
  >- (qspec_then `TopLevelNameTarget (src_id_opt,id)` mp_tac
        ifexp_base_place_memory_domain >>
      simp[Once evaluate_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def] >> metis_tac[])
  >- (PairCases_on `nsid` >>
      gvs[Once evaluate_def, lookup_flag_mem_def,
          vyperMiscTheory.option_CASE_rator, return_def, raise_def, AllCaseEqs()])
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
      drule ifexp_conditional_memory_origin >> strip_tac >> gvs[] >>
      gvs[switch_BoolV_def, bind_def, COND_RATOR, return_def,
          raise_def, AllCaseEqs()] >>
      metis_tac[])
  >- gvs[Once evaluate_def, return_def]
  >- (gvs[Once evaluate_def, bind_def, return_def, AllCaseEqs()])
  >- suspend "subscript"
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
      drule ifexp_select_memory_origin >> strip_tac >>
      drule ifexp_extend_memory_origin >> strip_tac >> gvs[] >>
      first_x_assum drule >> strip_tac >>
      drule_all ifexp_extend_memory_domain >> strip_tac >> gvs[] >> metis_tac[])
  >- (gvs[Once evaluate_def] >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()])
  >- (gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
      drule ifexp_pop_memory_origin >> strip_tac >> gvs[] >>
      drule ifexp_target_place_memory_domain >> strip_tac >>
      drule_all ifexp_pop_memory_domain >> simp[])
  >- (gvs[Once evaluate_def] >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()])
  >- suspend "send"
  >- suspend "extcall"
  >- (gvs[Once evaluate_def] >> gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()]) >>
  (gvs[Once evaluate_def] >>
   gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
   gvs[eval_raw_call_def, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()] >>
   gvs[pairTheory.UNCURRY, bind_def, ignore_bind_def, return_def,
       raise_def, COND_RATOR, AllCaseEqs()]) >>
  Cases_on `kind` >>
  gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  metis_tac[ifexp_create_no_place]
QED

Resume ifexp_expr_memory_domain_mutual[subscript]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  drule ifexp_select_memory_origin >> strip_tac >>
  drule ifexp_extend_memory_origin >> strip_tac >> gvs[] >>
  qpat_x_assum `!es id path ee. _` drule >> strip_tac >>
  drule read_result_state >> strip_tac >> gvs[] >>
  drule_all ifexp_eval_expr_retained_domain >> strip_tac >>
  drule_all ifexp_extend_memory_domain >> strip_tac >> gvs[] >> metis_tac[]
QED

Resume ifexp_expr_memory_domain_mutual[send]:
  gvs[Once evaluate_def] >>
  gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  Cases_on `vs` >> gvs[eval_send_def, raise_def] >>
  Cases_on `t` >> gvs[eval_send_def, raise_def] >>
  gvs[bind_def, ignore_bind_def, return_def, COND_RATOR,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
  pairarg_tac >> gvs[return_def, bind_def, ignore_bind_def, AllCaseEqs()]
QED

Resume ifexp_expr_memory_domain_mutual[extcall]:
  gvs[Once evaluate_def, bind_def, AllCaseEqs()] >>
  qmatch_asmsub_rename_tac `eval_ext_call cx isstatic skip sig opts args st` >>
  PairCases_on `sig` >> Cases_on `args` >>
  gvs[eval_ext_call_def, raise_def, bind_def, ignore_bind_def, return_def,
      vyperMiscTheory.option_CASE_rator, COND_RATOR, AllCaseEqs()] >>
  gvs[bind_def, ignore_bind_def, return_def,
      vyperMiscTheory.option_CASE_rator, AllCaseEqs()]
QED

Finalise ifexp_expr_memory_domain_mutual

Theorem ifexp_eval_expr_memory_domain[local]:
  !cx e es id path ee.
    eval_expr cx e es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
    ?entry. lookup_scopes id ee.scopes = SOME entry /\
      (!msg. evaluate_subscripts entry.type entry.value path <> INR (TypeError msg))
Proof
  metis_tac[ifexp_expr_memory_domain_mutual]
QED

Theorem ifexp_lookup_immutable_domain[local]:
  lookup_global cx src nm es = (INL (PlaceR (ImmutablePlace src' id path)),ee) ==>
  ?imms tv v. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src' imms) id = SOME (tv,v) /\
    (!msg. evaluate_subscripts tv v path <> INR (TypeError msg))
Proof
  strip_tac >>
  gvs[lookup_global_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  Cases_on `find_var_decl_by_name nm ts`
  >- (gvs[bind_def, get_immutables_def, get_address_immutables_def,
          lift_option_type_def, vyperMiscTheory.option_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      gvs[evaluate_subscripts_def] >> Cases_on `tvv` >> metis_tac[]) >>
  PairCases_on `x` >> Cases_on `x0` >>
  gvs[bind_def, return_def, raise_def, AllCaseEqs()]
QED

Theorem ifexp_extend_immutable_domain[local]:
  extend_place cx raw sb es = (INL (PlaceR (ImmutablePlace src id path)),ee) ==>
  ?imms tv v. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    (!msg. evaluate_subscripts tv v path <> INR (TypeError msg))
Proof
  Cases_on `raw`
  >- simp[extend_place_def, raise_def]
  >- (rename1 `PlaceR p` >> Cases_on `p`
      >- (simp[extend_place_def, bind_def, return_def, AllCaseEqs()] >>
          rpt strip_tac >> drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
          simp[]) 
      >- simp[extend_place_def, bind_def, ignore_bind_def, return_def,
              extend_memory_place_def, AllCaseEqs()] >>
      strip_tac >>
      gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
          extend_memory_place_def, AllCaseEqs()] >>
      gvs[place_type_value_def, read_place_def, get_immutables_def,
          get_address_immutables_def, lift_option_type_def, lift_sum_def,
          bind_def, return_def, raise_def, AllCaseEqs()] >>
      gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
          return_def, raise_def, AllCaseEqs()] >>
      drule_all vyperPlaceResultTypingTheory.evaluate_subscripts_append >>
      disch_then (qspec_then `[sb]` assume_tac) >>
      Cases_on `tva` >> gvs[]) >>
  Cases_on `sb` >>
  simp[extend_place_def, bind_def, return_def, raise_def,
       lift_option_type_def, value_type_CASE_rator, AllCaseEqs()] >>
  rpt strip_tac >> gvs[return_def, raise_def, AllCaseEqs()]
QED

Theorem ifexp_conditional_no_immutable[local]:
  conditional_result cx raw es <> (INL (PlaceR (ImmutablePlace src id path)),ee)
Proof
  Cases_on `raw` >> simp[conditional_result_def, return_def, raise_def] >>
  rename1 `PlaceR p` >> Cases_on `p` >>
  simp[conditional_result_def, bind_def, COND_RATOR, return_def,
       AllCaseEqs()] >> rpt strip_tac >> gvs[return_def, AllCaseEqs()]
QED

Theorem ifexp_pop_no_immutable[local]:
  pop_place cx p es <> (INL (PlaceR (ImmutablePlace src id path)),ee)
Proof
  Cases_on `p`
  >- (rename1 `StoragePlace tr slot tv` >> Cases_on `tv` >>
      simp[pop_place_def, raise_def] >> rename1 `ArrayTV elem bd` >>
      Cases_on `bd` >> simp[pop_place_def, raise_def, bind_def,
        ignore_bind_def, return_def, AllCaseEqs()])
  >- (simp[pop_place_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[return_def, AllCaseEqs()] >>
      gvs[pairTheory.UNCURRY, bind_def, ignore_bind_def, return_def, AllCaseEqs()]) >>
  simp[pop_place_def, bind_def, ignore_bind_def, return_def, AllCaseEqs()]
QED

Theorem ifexp_select_immutable_domain[local]:
  select_result cx ty raw sb es = (INL (PlaceR (ImmutablePlace src id path)),ee) ==>
  ?imms tv v. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    (!msg. evaluate_subscripts tv v path <> INR (TypeError msg))
Proof
  Cases_on `raw` >> simp[select_result_def, bind_def, return_def, AllCaseEqs()] >>
  metis_tac[ifexp_extend_immutable_domain]
QED

Theorem ifexp_eval_expr_immutable_domain[local]:
  eval_expr cx e es = (INL (PlaceR (ImmutablePlace src id path)),ee) ==>
  ?imms tv v. ALOOKUP ee.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
    (!msg. evaluate_subscripts tv v path <> INR (TypeError msg))
Proof
  Cases_on `e` >> strip_tac >>
  gvs[Once evaluate_def] >>
  gvs[bind_def, ignore_bind_def, return_def, raise_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      drule ifexp_lookup_immutable_domain >> simp[])
  >- (PairCases_on `p` >>
      gvs[lookup_flag_mem_def, vyperMiscTheory.option_CASE_rator,
          return_def, raise_def, AllCaseEqs()])
  >- metis_tac[ifexp_conditional_no_immutable]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()])
  >- (drule ifexp_select_immutable_domain >> simp[])
  >- (drule ifexp_select_immutable_domain >> simp[])
  >- metis_tac[ifexp_pop_no_immutable] >>
  Cases_on `c` >> gvs[Once evaluate_def] >>
  gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()]
  >- (PairCases_on `p` >> gvs[Once evaluate_def] >>
      gvs[bind_def, ignore_bind_def, return_def, AllCaseEqs()])
  >- (PairCases_on `p` >> Cases_on `target ++ vs ++ kwargs` >>
      gvs[eval_ext_call_def, raise_def, bind_def, ignore_bind_def, return_def,
          vyperMiscTheory.option_CASE_rator, COND_RATOR, AllCaseEqs()] >>
      gvs[bind_def, ignore_bind_def, return_def,
          vyperMiscTheory.option_CASE_rator, AllCaseEqs()])
  >- (Cases_on `vs` >> gvs[eval_send_def, raise_def] >>
      Cases_on `t` >> gvs[eval_send_def, raise_def] >>
      gvs[bind_def, ignore_bind_def, return_def, COND_RATOR,
          vyperMiscTheory.option_CASE_rator, AllCaseEqs()] >>
      gvs[bind_def, ignore_bind_def, return_def, raise_def,
          vyperMiscTheory.option_CASE_rator, pairTheory.UNCURRY, AllCaseEqs()])
  >> gvs[eval_raw_call_def, bind_def, ignore_bind_def, return_def,
         raise_def, COND_RATOR, AllCaseEqs()] >>
  gvs[pairTheory.UNCURRY, bind_def, ignore_bind_def, return_def,
      raise_def, COND_RATOR, AllCaseEqs()] >>
  Cases_on `c'` >> gvs[bind_def, ignore_bind_def, AllCaseEqs()] >>
  metis_tac[ifexp_create_no_place]
QED

Theorem ifexp_produced_memory_read_ok[local]:
  eval_expr cx e es0 = (INL (PlaceR (MemoryPlace id path)),ee) /\
  read_result cx (PlaceR (MemoryPlace id path)) ee = (res,ef) ==>
  expr_res_ok res
Proof
  strip_tac >> drule ifexp_eval_expr_memory_domain >> strip_tac >>
  gvs[read_result_def, read_place_def, get_scopes_def, lift_option_type_def,
      bind_def, return_def, lift_sum_def, AllCaseEqs()] >>
  Cases_on `read_memory_path entry path` >>
  gvs[return_def, raise_def]
  >- simp[expr_res_ok_def] >>
  drule read_memory_path_error_shape >> strip_tac >> gvs[expr_res_ok_def] >>
  gvs[ifexp_memory_path_type_error]
QED

Theorem ifexp_storage_read_ok[local]:
  read_result cx (PlaceR (StoragePlace tr slot tv)) ee = (res,ef) ==>
  expr_res_ok res
Proof
  strip_tac >> Cases_on `tr` >>
  gvs[read_result_def, read_place_def, read_storage_slot_def,
      get_storage_backend_def, get_transient_storage_def, get_accounts_def,
      lift_option_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, return_def, raise_def,
      expr_res_ok_def, AllCaseEqs()]
QED

Theorem ifexp_produced_immutable_read_ok[local]:
  eval_expr cx e es0 = (INL (PlaceR (ImmutablePlace src id path)),ee) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (res,ef) ==>
  expr_res_ok res
Proof
  strip_tac >> drule ifexp_eval_expr_immutable_domain >> strip_tac >>
  gvs[read_result_def, read_place_def, get_immutables_def,
      get_address_immutables_def, lift_option_type_def, bind_def,
      return_def, lift_sum_def, AllCaseEqs()] >>
  Cases_on `evaluate_subscripts tv v path` >>
  gvs[return_def, raise_def, expr_res_ok_def] >>
  drule evaluate_subscripts_error_shape >> strip_tac >> gvs[]
QED

Theorem ifexp_produced_place_read_ok[local]:
  eval_expr cx e es0 = (INL (PlaceR p),ee) /\
  read_result cx (PlaceR p) ee = (res,ef) ==>
  expr_res_ok res
Proof
  Cases_on `p` >> rpt strip_tac
  >- metis_tac[ifexp_storage_read_ok]
  >- metis_tac[ifexp_produced_memory_read_ok] >>
  metis_tac[ifexp_produced_immutable_read_ok]
QED

Theorem ifexp_raw_admissible_force_boundary[local]:
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  (!gs p ee res ef.
    eval_expr cx e (es with gas_obs := gs) = (INL (PlaceR p),ee) /\
    read_result cx (PlaceR p) ee = (res,ef) ==> expr_res_ok res) ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  rw[gas_admissible_def, bind_def, AllCaseEqs()]
  >- (Cases_on `x`
      >- gvs[read_result_def, return_def, expr_res_ok_def]
      >- (qpat_x_assum `!gs p ee res ef. _` drule_all >> simp[]) >>
      qpat_x_assum `!gs res ee. _` drule >>
      simp[expr_vv_res_ok_def]) >>
  qpat_x_assum `!gs res ee. _` drule >>
  simp[expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem ifexp_raw_admissible_force[local]:
  gas_admissible (eval_expr cx e) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> irule ifexp_raw_admissible_force_boundary >> simp[] >>
  metis_tac[ifexp_produced_place_read_ok]
QED

(* Actual source producer: syntax annotations alone do not exclude mappings.
   This is a read-totality diagnostic, not a simulation counterexample. *)
Theorem ifexp_mapping_producer_unreadable[local]:
  cx.sources = [(cx.txn.target,
    [(NONE,[HashMapDecl Private F "m" (BaseT BoolT) (Type (BaseT BoolT)) NONE])])] /\
  cx.layouts = [(cx.txn.target, ([( (NONE,"m"),0)],[]))] ==>
  eval_expr cx (TopLevelName (BaseT BoolT) (NONE,"m")) es =
    (INL (HashMapRef F 0w (BaseT BoolT) (Type (BaseT BoolT))),es) /\
  read_result cx (HashMapRef F 0w (BaseT BoolT) (Type (BaseT BoolT))) es =
    (INR (Error (TypeError "read_result mapping")),es)
Proof
  strip_tac >>
  simp[evaluate_def, lookup_global_def, vyperContextTheory.get_module_code_def,
       find_var_decl_by_name_def, lookup_var_slot_from_layout_def,
       bind_def, return_def, lift_option_type_def, read_result_def, raise_def]
QED

Theorem ifexp_raw_conditional_outcome_mem[local]:
  gas_outcome T tops (ctx,func) (eval_expr cx e) (es,s0) P
    (\res ee r. expr_exit res r) /\
  (!res ee s. P res ee s ==> ?raw. res = INL raw) /\
  (!marks raw ee s.
    gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
      marks (INL raw) ee (OK s) /\ P (INL raw) (ee with gas_obs := []) s ==>
    ?tv q. gas_marked_exec T (ctx,func) (conditional_result cx raw)
      (ee with gas_obs := [],s) [] (INL tv) (ee with gas_obs := []) (OK q) /\
      Q (INL tv) (ee with gas_obs := []) q) ==>
  gas_outcome T tops (ctx,func)
    (bind (eval_expr cx e) (conditional_result cx)) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >>
      `?raw. res = INL raw` by metis_tac[] >> gvs[] >>
      qpat_x_assum `!marks raw ee s. _` drule_all >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INL tv`,`es_end with gas_obs := []`,`OK q`] >> simp[] >>
      irule (SRULE [] (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal)) >>
      goal_assum (drule_at Any) >>
      goal_assum (drule_at Any) >> simp[])
  >- (gvs[] >> Cases_on `res` >> gvs[expr_exit_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR y`,`es_end`,`r`] >> simp[] >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >> simp[ignore_bind_def]
QED

Theorem compile_ifexp_word_vv_sim_mem[local]:
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
    expr_vv_sim_mem ctx func cenv cx ty (IfExp t c a b) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule ifexp_root_condition_admissible >> goal_assum (drule_at Any)) >>
  drule_all ifexp_root_code_layout >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr cenv ty (if T then a else b) _ = _` kall_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` kall_tac >>
  gvs[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ c _` mp_tac >>
  simp[expr_sim_mem_def] >> disch_then drule_all >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ root_post root_exit` >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> suspend "selected")
  >- (pure_rewrite_tac[GSYM gas_summary_at_def, GSYM gas_outcome_def] >>
      simp[Abbr `root_exit`] >> irule ifexp_condition_exit_mem >>
      goal_assum (drule_at Any) >> gvs[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  irule ifexp_root_condition_cert >> simp[]
QED

Resume compile_ifexp_word_vv_sim_mem[selected]:
  cheat
QED

Finalise compile_ifexp_word_vv_sim_mem

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

Theorem ifexp_word_lowering_result[local]:
  is_word_type t /\
  lower_value compile_expr cenv ty (IfExp t c a b) sa = (op,sb) ==>
  ?rv. op = Var rv /\
    compile_expr cenv ty (IfExp t c a b) sa = (StackValue t (Var rv),sb)
Proof
  simp[lower_value_def, comp_bind_def] >> strip_tac >>
  Cases_on `compile_expr cenv ty (IfExp t c a b) sa` >>
  rename1 `compile_expr cenv ty (IfExp t c a b) sa = (vv,sm)` >>
  gvs[] >> drule compile_expr_ifexp >> strip_tac >>
  gvs[unwrap_value_def, comp_return_def]
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
  rpt gen_tac >> strip_tac >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all ifexp_word_lowering_result >> strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx (IfExp (expr_type a) c a b)) expr_vv_res_ok es` by
    (irule exprSimMemorySourceTheory.forced_expr_admissible_raw >> simp[]) >>
  `gas_admissible (bind (eval_expr cx c) (read_result cx)) expr_res_ok es` by
    (irule ifexp_root_condition_admissible >> goal_assum (drule_at Any)) >>
  drule_all ifexp_root_code_layout >>
  disch_then (qspec_then `T` strip_assume_tac) >>
  qpat_x_assum `emit_inst JNZ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst ASSIGN _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_inst JMP _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_expr cenv ty (if T then a else b) _ = _` kall_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` kall_tac >>
  gvs[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ c _` mp_tac >>
  simp[expr_sim_mem_def] >>
  disch_then drule_all >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ root_post root_exit` >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (gvs[] >> suspend "selected_arm")
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
      Cases_on `res` >> fs[expr_exit_def, Abbr `root_exit`] >>
      rewrite_tac[ifexp_root_eval_forced] >>
      irule gas_marked_exec_bind_exception >>
      irule gas_marked_exec_bind_exception >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_result >>
  rewrite_tac[GSYM ignore_bind_def] >>
  irule ifexp_root_condition_cert >> simp[]

QED

Resume compile_ifexp_word_sim_mem[selected_arm]:
  `?sel. v = BoolV sel` by
    (irule ifexp_root_condition_bool >> goal_assum (drule_at Any) >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> metis_tac[]) >>
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
  drule_all ifexp_root_code_layout >>
  disch_then (qspec_then `sel` strip_assume_tac) >> gvs[] >>
  pure_rewrite_tac[GSYM gas_summary_at_def, GSYM gas_outcome_def] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
     drule gas_path_mem_exec >> metis_tac[gas_path_normal]) >>
  `gas_path_mem ctx func t 0 (OK (jump_to se.cs_current_bb t))` by
    (asm_rewrite_tac[] >> irule ifexp_jnz_path_mem >> simp[] >> metis_tac[]) >>
  irule ifexp_forced_selected_outcome_prefix_mem >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`marks`,`es_end`,`sel`] >> simp[] >>
  `lower_value compile_expr cenv ty (if sel then a else b) se = (aop,sx)` by
    (irule ifexp_arm_lower_value >> simp[] >> metis_tac[]) >>
  `gas_admissible
    (bind (eval_expr cx (if sel then a else b)) (read_result cx))
    expr_res_ok (es_end with gas_obs := [])` by
    (irule ifexp_root_forced_branch_admissible >> goal_assum (drule_at Any) >>
     fs[gas_marked_exec_def] >> metis_tac[]) >>
  `expr_sim_mem ctx func cenv cx ty (if sel then a else b)
      (es_end with gas_obs := [])` by
    (`?gs. bind (eval_expr cx c) (read_result cx) (es with gas_obs := gs) =
         (INL (BoolV sel),es_end with gas_obs := [])` by
       (fs[gas_marked_exec_def] >> metis_tac[]) >>
     first_x_assum (qspecl_then [`gs`,`BoolV sel`,
       `es_end with gas_obs := []`] mp_tac) >>
     simp[SF ETA_ss] >> Cases_on `sel` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := [])
      (jump_to se.cs_current_bb t)` by
    fs[expr_post_def, stmt_state_rel_jump_to] >>
  `alloca_history func (jump_to se.cs_current_bb t)` by
    metis_tac[ifexp_history_jump] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ (if _ then _ else _) _` mp_tac >>
  simp[expr_sim_mem_def] >> disch_then drule >>
  disch_then (qspec_then `jump_to se.cs_current_bb t` mp_tac) >>
  impl_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ (_ with gas_obs := []) _` mp_tac >>
      simp[jump_to_def, exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  strip_tac >>
  `expr_type (if sel then a else b) = expr_type a` by (Cases_on `sel` >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by
    (qpat_x_assum `!sa sb op. _` drule >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM (es_end with gas_obs := []).scopes` by
    (irule ifexp_root_condition_scopes >> fs[gas_marked_exec_def] >> metis_tac[]) >>
  `(jump_to (if sel then tl else el) t).vs_alloca_next = t.vs_alloca_next` by
    simp[jump_to_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[expr_store_bound_word] >> strip_tac >>
  simp[Abbr `root_post`, expr_store_bound_word, vyperASTTheory.expr_type_def] >>
  qpat_assum `sb.cs_current_insts = []`
    (fn th => irule (SRULE [th] ifexp_forced_arm_finish_mem)) >>
  goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >>
  simp[] >> goal_assum (drule_at Any) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]

QED

Finalise compile_ifexp_word_sim_mem

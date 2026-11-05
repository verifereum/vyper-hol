Theory bodyIfExpMemory
Ancestors
  loweringPosts
  exprBopSimProps
  exprSimIfExp fragExec fragExecMem instMemFrontier allocaHistoryFragment
  emitHelper emitHelperProps compileEnv venomState venomInst
  list rich_list loweringSlice venomExecSemantics venomExecProofs exprLoweringProps
  fragGasSeqMem fragGasPathMem stmtSimProps
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

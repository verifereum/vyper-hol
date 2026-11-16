(* Source-linked invalid-EC stopping cut. Operand-prefix execution and the
   nonempty source witness are supplied by the recursive consumer. *)
Theory loweringBudgetECStopping
Ancestors
  loweringBudgetPrecompilePrefix loweringBudgetRecorderOutcomes
  loweringBudgetCursorCuts fragExec context emitHelper compileEnv
  exprSimECArith exprSimPrecompiles
  vyperContext extCallOracle vfmBuffer vfmTypes byte words list rich_list
Libs
  monadsyntax

Theorem ecadd_invalid_source_request:
  extract_ec_point v1 = SOME (x1,y1) /\
  extract_ec_point v2 = SOME (x2,y2) /\
  Num x1 < 2 ** 256 /\ Num y1 < 2 ** 256 /\
  Num x2 < 2 ** 256 /\ Num y2 < 2 ** 256 /\
  evaluate_ecadd [v1;v2] = INR (RuntimeError "ECAdd invalid point") /\
  rq.cr_target = 6w /\
  rq.cr_data = word_to_bytes (n2w (Num x1):bytes32) T ++
    word_to_bytes (n2w (Num y1):bytes32) T ++
    word_to_bytes (n2w (Num x2):bytes32) T ++
    word_to_bytes (n2w (Num y2):bytes32) T ==>
  ec_source_tail cx ann ECAdd tys [v1;v2] es =
    (INR (Error (RuntimeError "ECAdd invalid point")),es) /\
  precompile_result rq.cr_target rq.cr_data = SOME NONE
Proof
  strip_tac >> conj_tac
  >- simp[ec_source_tail_def, exprSimWordArgsTheory.builtin_result_def,
          evaluate_builtin_def] >>
  `vfmExecution$ecadd (Num x1,Num y1) (Num x2,Num y2) = NONE` by
    (gvs[evaluate_ecadd_def, AllCaseEqs()]) >>
  asm_rewrite_tac[] >>
  rewrite_tac[precompile_result_ecadd,
       SRULE [] (Q.INST [`n` |-> `0`] drop_word_prefix),
       SRULE [] (Q.INST [`n` |-> `32`] drop_word_prefix),
       SRULE [] (Q.INST [`n` |-> `64`] drop_word_prefix),
       take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_APPEND1,
       DROP_APPEND, TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def, w2n_n2w, dimword_def] >>
  gvs[]
QED

Theorem ecmul_invalid_source_request:
  extract_ec_point v = SOME (x,y) /\
  Num x < 2 ** 256 /\ Num y < 2 ** 256 /\ Num scalar < 2 ** 256 /\
  evaluate_ecmul [v;IntV scalar] = INR (RuntimeError "ECMul invalid point") /\
  rq.cr_target = 7w /\
  rq.cr_data = word_to_bytes (n2w (Num x):bytes32) T ++
    word_to_bytes (n2w (Num y):bytes32) T ++
    word_to_bytes (n2w (Num scalar):bytes32) T ==>
  ec_source_tail cx ann ECMul tys [v;IntV scalar] es =
    (INR (Error (RuntimeError "ECMul invalid point")),es) /\
  precompile_result rq.cr_target rq.cr_data = SOME NONE
Proof
  strip_tac >> conj_tac
  >- simp[ec_source_tail_def, exprSimWordArgsTheory.builtin_result_def,
          evaluate_builtin_def] >>
  `vfmExecution$ecmul (Num x,Num y) (Num scalar) = NONE` by
    (gvs[evaluate_ecmul_def, AllCaseEqs()]) >>
  asm_rewrite_tac[] >>
  rewrite_tac[precompile_result_ecmul,
       SRULE [] (Q.INST [`n` |-> `0`] drop_word_prefix),
       SRULE [] (Q.INST [`n` |-> `32`] drop_word_prefix),
       take_pad_word_prefix] >>
  simp[take_pad_0_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_APPEND1,
       DROP_APPEND, TAKE_LENGTH_TOO_LONG, DROP_LENGTH_TOO_LONG, PAD_RIGHT,
       num_of_be_bytes_word32, word_to_bytes_word_of_bytes_32,
       word_of_bytes_be_def, w2n_n2w, dimword_def] >>
  gvs[]
QED

(* The source sentinel is independent of the target residual:
   no target nonemptiness is assumed. *)
Theorem embedded_computed_failure_budget:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  fn_has_code sf sb fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE /\
  ~s.vs_halted /\ p.bp_state = s /\ p.bp_fn = fn /\
  lower_budget_path F (D,lo,explicit,ctx) p h marks q ==>
  lower_history_count h <= 1 /\
  (!sentinel. sentinel <> ([]:call_outcome list) ==>
     lower_history_count h <= LENGTH sentinel) /\
  q.bp_state.vs_outcomes = DROP (lower_history_count h) s.vs_outcomes /\
  (q.bp_state.vs_inst_idx = s.vs_inst_idx + 2 ==>
    !h' marks' q'. lower_budget_path F (D,lo,explicit,ctx) q h' marks' q' ==>
      h' = [] /\ marks' = [] /\ q' = q)
Proof
  strip_tac >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_x_assum `_ sm = (res,sb)` mp_tac >>
     simp[comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  drule computed_suffix_shape >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND1]) >>
  `!st i. st.vs_current_bb = s.vs_current_bb /\
    st.vs_inst_idx < s.vs_inst_idx + 3 /\
    s.vs_inst_idx <= st.vs_inst_idx /\ active_inst fn i st ==>
    i = EL (st.vs_inst_idx - s.vs_inst_idx) (emitted_insts sm sb)` by
    (rpt strip_tac >>
     `st.vs_inst_idx < LENGTH sb.cs_current_insts` by gvs[] >>
     `st.vs_current_bb = sb.cs_current_bb` by metis_tac[] >>
     drule_all embedded_current_active_inst >> strip_tac >>
     gvs[EL_APPEND]) >>
  drule_all computed_failure_budget_prefix >> strip_tac >>
  conj_tac >- simp[] >>
  conj_tac >- (Cases >> simp[] >> decide_tac) >>
  conj_tac >- metis_tac[lower_budget_path_outcomes] >>
  metis_tac[computed_failure_budget_terminal]
QED

Theorem invalid_ec_source_stopping_cut:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL [gas; Lit target; ip; Lit insz; op; Lit outsz];
      emit_void ASSERT [success]; return op od) sm = (res,sb) /\
  fn_has_code sf sb fn /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand ip s = SOME wi /\ eval_operand op s = SOME wo /\
  (!x. ip = Var x ==> not_fresh_at sm x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  rq = venom_call_request s target 0w wi insz T /\
  ((bt = ECAdd /\ args = [v1;v2] /\ msg = "ECAdd invalid point" /\
    extract_ec_point v1 = SOME (x1,y1) /\
    extract_ec_point v2 = SOME (x2,y2) /\
    Num x1 < 2 ** 256 /\ Num y1 < 2 ** 256 /\
    Num x2 < 2 ** 256 /\ Num y2 < 2 ** 256 /\
    evaluate_ecadd [v1;v2] = INR (RuntimeError "ECAdd invalid point") /\
    rq.cr_target = 6w /\
    rq.cr_data = word_to_bytes (n2w (Num x1):bytes32) T ++
      word_to_bytes (n2w (Num y1):bytes32) T ++
      word_to_bytes (n2w (Num x2):bytes32) T ++
      word_to_bytes (n2w (Num y2):bytes32) T) \/
   (bt = ECMul /\ args = [v;IntV scalar] /\ msg = "ECMul invalid point" /\
    extract_ec_point v = SOME (x,y) /\
    Num x < 2 ** 256 /\ Num y < 2 ** 256 /\ Num scalar < 2 ** 256 /\
    evaluate_ecmul [v;IntV scalar] = INR (RuntimeError "ECMul invalid point") /\
    rq.cr_target = 7w /\
    rq.cr_data = word_to_bytes (n2w (Num x):bytes32) T ++
      word_to_bytes (n2w (Num y):bytes32) T ++
      word_to_bytes (n2w (Num scalar):bytes32) T)) /\
  es.outcomes = SOME sentinel /\ sentinel <> [] /\
  ~s.vs_halted /\ p.bp_state = s /\ p.bp_fn = fn /\
  lower_budget_path F (D,lo,explicit,ctx) p h marks q ==>
  ec_source_tail cx ann bt tys args es =
    (INR (Error (RuntimeError msg)),es) /\
  lower_history_count h <= LENGTH sentinel /\
  q.bp_state.vs_outcomes = DROP (lower_history_count h) s.vs_outcomes /\
  (q.bp_state.vs_inst_idx = s.vs_inst_idx + 2 ==>
    !h' marks' q'. lower_budget_path F (D,lo,explicit,ctx) q h' marks' q' ==>
      h' = [] /\ marks' = [] /\ q' = q)
Proof
  strip_tac >>
  `ec_source_tail cx ann bt tys args es =
     (INR (Error (RuntimeError msg)),es) /\
   precompile_result rq.cr_target rq.cr_data = SOME NONE` by
    (FIRST [drule_all ecadd_invalid_source_request,
            drule_all ecmul_invalid_source_request] >>
     disch_then (fn th => simp[th])) >>
  `precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME NONE` by
    metis_tac[] >>
  drule_all embedded_computed_failure_budget >> strip_tac >>
  `lower_history_count h <= LENGTH sentinel` by
    (qpat_x_assum `!sentinel. _` irule >> asm_rewrite_tac[]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

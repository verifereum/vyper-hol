(* Structured control opcode boundaries, parameterized by body preservation. *)
Theory ctorCallFreeStmtControl
Ancestors
  list pair stmtLowering emitHelper context compileEnv exprLowering venomInst loweringShapeDefs
  ctorCallFreeRules ctorCallFreeValues ctorCallFreeCallbacks ctorCallFreeStmtStorage
  supportedExprTraverse supportedStmtTraverse e2eDeployDefs loweringShapeProps

(* Discharge precise opcode premises from the complement-of-seven premise;
   c7 also discharges generator callbacks with the given precise lemmas. *)
val base7_tm = ``!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
  opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
  opc <> RETURNDATACOPY ==> (P:opcode -> bool) opc``;
fun b7 th = SIMP_RULE (srw_ss()) [ASSUME base7_tm, DISJ_IMP_THM, FORALL_AND_THM] th;
fun c7 ths th = SIMP_RULE (srw_ss()) (map b7 ths) (b7 th);

Theorem outcomes_free_emit_jmp_if_not_terminated:
  P JMP ==>
  !lbl s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (emit_jmp_if_not_terminated lbl s)))
Proof
  rpt strip_tac >>
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def] >>
  IF_CASES_TAC >> simp[every_state_insts_return, opcode_every_emit_op, opcode_every_emit_void,
      opcode_every_emit_inst]
QED

Theorem every_state_insts_declare_local_bind[local]:
  (!ce' st. ce'.ce_func_defaults = ce.ce_func_defaults ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (f ce' st)))) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (comp_bind (declare_local ce id ty) f st)))
Proof
  strip_tac >> Cases_on `ce.ce_alloca_locals` >>
  simp[declare_local_def, comp_bind_def, comp_return_def, fresh_var_def] >>
  rpt strip_tac >> first_x_assum irule >> fs[state_insts_def, all_blocks_def]
QED

Theorem outcomes_free_stmt_if:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !cond b1 b2.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b1 st)))) /\
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b2 st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (If cond b1 b2) /\
  ~supported_stmt_expr_exists extra_root (If cond b1 b2) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (If cond b1 b2) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_declare_local_bind >>
      gen_tac >> gen_tac >> strip_tac >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_get,
      every_state_insts_fresh_label, every_state_insts_new_block,
      opcode_every_emit_inst, (b7 outcomes_free_emit_jmp_if_not_terminated)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)]]) >> metis_tac[]
QED

Theorem opcode_every_stmt_if:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !cond b1 b2.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b1 st)))) /\
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty b2 st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (If cond b1 b2) /\
  ~supported_stmt_expr_exists extra_root (If cond b1 b2) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (If cond b1 b2) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_if >> simp[]
QED

Theorem outcomes_free_stmt_for_range:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty start_e end_e bound body.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (For id fty (Range start_e end_e) bound body) /\
  ~supported_stmt_expr_exists extra_root (For id fty (Range start_e end_e) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound body) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  `!ty e st. ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))`
    by metis_tac[] >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_declare_local_bind >>
      gen_tac >> gen_tac >> strip_tac >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      (b7 outcomes_free_declare_local), (b7 outcomes_free_emit_local_alloca),
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (b7 outcomes_free_range_bound_checks), (b7 outcomes_free_emit_jmp_if_not_terminated)]),
    qid_spec_tac `st` >> ho_match_mp_tac every_state_insts_lower_value >>
      simp[(b7 outcomes_free_unwrap_value)]])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      Cases_on `end_e` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, opcode_every_emit_op] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, opcode_every_emit_op])
  >- (Cases_on `start_e` >> simp[every_state_insts_return, (b7 outcomes_free_range_bound_checks)] >>
      Cases_on `end_e` >> simp[every_state_insts_return, (b7 outcomes_free_range_bound_checks)] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_end` >>
      Cases_on `lit_end` >> simp[every_state_insts_return, (b7 outcomes_free_range_bound_checks)] >>
      qmatch_goalsub_rename_tac `literal_CASE lit_start` >>
      Cases_on `lit_start` >> simp[every_state_insts_return, (b7 outcomes_free_range_bound_checks)])
  >>~- ([`compile_stmts _ _ _ _ _ (* sg *)`],
         rpt strip_tac >> first_assum irule >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars loop_id` >>
  Cases_on `FLOOKUP vars loop_id` >> simp[opcode_every_emit_void] >>
  rename1 `SOME loc` >> Cases_on `loc` >> simp[opcode_every_emit_void]
QED

Theorem opcode_every_stmt_for_range:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty start_e end_e bound body.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (For id fty (Range start_e end_e) bound body) /\
  ~supported_stmt_expr_exists extra_root (For id fty (Range start_e end_e) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Range start_e end_e) bound body) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_for_range >> simp[]
QED

Theorem outcomes_free_stmt_for_array:
  (!opc. opc <> CALL /\ opc <> STATICCALL /\ opc <> DELEGATECALL /\
         opc <> CREATE /\ opc <> CREATE2 /\ opc <> INVOKE /\
         opc <> RETURNDATACOPY ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty arr bound body.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (For id fty (Array arr) bound body) /\
  ~supported_stmt_expr_exists extra_root (For id fty (Array arr) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Array arr) bound body) st)))
  )
Proof
  strip_tac >>
  strip_tac >> rpt gen_tac >> strip_tac >> rpt gen_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  `!ty e st. ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e st)))`
    by metis_tac[] >>
  simp[Once compile_stmt_def] >>
  rpt (FIRST [ho_match_mp_tac every_state_insts_declare_local_bind >>
      gen_tac >> gen_tac >> strip_tac >> qid_spec_tac `st`,
    ho_match_mp_tac every_state_insts_bind >> conj_tac,
    ho_match_mp_tac every_state_insts_ignore_bind >> conj_tac,
    gen_tac, IF_CASES_TAC >> qid_spec_tac `st`,
    CHANGED_TAC (simp[every_state_insts_return, every_state_insts_fresh_var,
      every_state_insts_fresh_label, every_state_insts_new_block,
      (b7 outcomes_free_declare_local), (b7 outcomes_free_emit_local_alloca),
      opcode_every_emit_inst, opcode_every_emit_void, opcode_every_emit_op,
      (b7 outcomes_free_ptr_load), (c7 [outcomes_free_slot_to_memory, outcomes_free_ptr_load, outcomes_free_imm_copy, outcomes_free_copy_memory, outcomes_free_store_memory] outcomes_free_iter_elem_copy), (b7 outcomes_free_emit_jmp_if_not_terminated)])])
  >>~- ([`compile_stmts _ _ _ _ _ (* sg *)`],
         rpt strip_tac >> first_assum irule >> metis_tac[]) >>
  qmatch_goalsub_abbrev_tac `FLOOKUP vars loop_id` >>
  Cases_on `FLOOKUP vars loop_id` >> simp[opcode_every_emit_void] >>
  rename1 `SOME targetloc` >> Cases_on `targetloc` >>
  simp[(c7 [outcomes_free_slot_to_memory, outcomes_free_ptr_load, outcomes_free_imm_copy, outcomes_free_copy_memory, outcomes_free_store_memory] outcomes_free_iter_elem_copy), opcode_every_emit_void]
QED

Theorem opcode_every_stmt_for_array:
  (!opc. opc <> RETURNDATACOPY /\ opc <> INVOKE /\
         opc <> CREATE /\ opc <> CREATE2 ==> P opc) ==>
  (
  (!ce ty e st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    ~supported_expr_exists R e /\
    ~supported_expr_exists extra_root e ==>
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_expr ce ty e st)))) ==>
  !id fty arr bound body.
  (!ce lc ty st.
    (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
      EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                   ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
    EVERY (\i. P i.inst_opcode) (state_insts st) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmts ce lc ty body st)))) ==>
  !ce lc ty.
  (!ann id args d. ~R (Call ann (IntCall id) args d) ==>
    EVERY (\nd. ~supported_exprs_exists R (SND nd) /\
                 ~supported_exprs_exists extra_root (SND nd)) ce.ce_func_defaults) /\
  ~supported_stmt_expr_exists R (For id fty (Array arr) bound body) /\
  ~supported_stmt_expr_exists extra_root (For id fty (Array arr) bound body) ==>
  !st. EVERY (\i. P i.inst_opcode) (state_insts st) ==>
  EVERY (\i. P i.inst_opcode)
    (state_insts (SND (compile_stmt ce lc ty (For id fty (Array arr) bound body) st)))
  )
Proof
  strip_tac >> match_mp_tac outcomes_free_stmt_for_array >> simp[]
QED

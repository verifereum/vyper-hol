Theory deployOutcomesFreeStmtAssignCases
Ancestors
  deployOutcomesFreeLowering deployOutcomesFreeStmtControl stmtLowering compileEnv list

Theorem outcomes_free_stmt_annassign:
  P ALLOCA /\ P MSTORE /\ P INVALID /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce (expr_type e) e s)))) /\
  (!vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce vv s)))) /\
  (!dst loc value prim src dt st info bytes s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_assign_value ce dst loc value prim src dt st info bytes s)))) ==>
  !lc ty id vt s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (AnnAssign id vt e) s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def] >>
  irule outcomes_free_ignore_bind >> simp[] >> conj_tac
  >- simp[outcomes_free_emit_local_alloca] >>
  rpt gen_tac >> strip_tac >>
  irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[] >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[outcomes_free_return]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  simp[comp_bind_def, comp_return_def] >>
  Cases_on `FLOOKUP ce.ce_vars id` >> simp[outcomes_free_emit_ops] >>
  rename1 `FLOOKUP ce.ce_vars id = SOME binding` >>
  Cases_on `binding` >> simp[outcomes_free_emit_ops] >>
  IF_CASES_TAC >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_stmt_assign_base:
  P INVALID /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce (expr_type e) e s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_get_target_ptr compile_expr ce bt s)))) /\
  (!vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce vv s)))) /\
  (!vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce T vv s)))) /\
  (!dst value loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_at_loc ce.ce_imm_alloca dst value loc s)))) /\
  (!dst loc value prim src dt st info bytes s.
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_assign_value ce dst loc value prim src dt st info bytes s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Assign (BaseTarget bt) e) s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def] >> IF_CASES_TAC
  >- (irule outcomes_free_bind >> simp[]) >>
  irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[] >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[outcomes_free_return]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return]),
              irule outcomes_free_bind >> simp[] ,
              gen_tac, disch_tac, CHANGED_TAC BETA_TAC]) >>
  BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_emit_ops]
QED

Theorem outcomes_free_stmt_assign_tuple:
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce (expr_type e) e s)))) /\
  (!vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce vv s)))) /\
  (!stage src s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_tuple_unpack ce (lowered_value_type ce e) stage targets src s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Assign (TupleTarget targets) e) s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def] >> irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >> irule outcomes_free_bind >> simp[]
QED

Theorem outcomes_free_stmt_augassign:
  EVERY P [INVALID; MLOAD; SLOAD; TLOAD; MSTORE; SSTORE; TSTORE] /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_get_target_ptr compile_expr ce bt s)))) /\
  (!s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (lower_value compile_expr ce target_ty e s)))) /\
  (!a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_binop bop a b target_ty NONE (if bop = Exp then expr_int_literal e else NONE) s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (AugAssign target_ty bt bop e) s)))
Proof
  simp[EVERY_DEF] >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def] >> irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  ntac 2 (simp[Once comp_bind_def, comp_return_def]) >>
  BasicProvers.TOP_CASE_TAC >> simp[outcomes_free_emit_ops] >>
  rename1 `FST (SND _) = SOME loc` >>
  Cases_on `loc` >>
  ntac 2 (simp[Once comp_bind_def, comp_return_def]) >>
  rpt (FIRST [CHANGED_TAC (simp[outcomes_free_return, outcomes_free_emit_ops]),
              irule outcomes_free_bind >> simp[],
              gen_tac, disch_tac, CHANGED_TAC BETA_TAC])
QED

Theorem outcomes_free_stmt_append:
  (!et s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (lower_value compile_expr ce et e s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!value ptr et sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce value ptr et sty s)))) /\
  (!value et sty prim s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND
      (compile_dynarray_append ce (compile_target_base ce target) value
        (word_scale (infer_array_location ce (target_to_expr target)))
        (elem_size_in_location ce (infer_array_location ce (target_to_expr target)) et)
        et sty (target_root_capacity ce target) prim
        (load_opc_for (infer_array_location ce (target_to_expr target)))
        (store_opc_for (infer_array_location ce (target_to_expr target))) s)))) ==>
  !lc ty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode)
      (state_insts (SND (compile_stmt ce lc ty (Append target e) s)))
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once compile_stmt_def] >> irule outcomes_free_bind >> simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[] >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[outcomes_free_return] >>
      rpt gen_tac >> strip_tac >> irule outcomes_free_bind >> simp[] >>
      rpt gen_tac >> strip_tac >> BETA_TAC >>
      irule outcomes_free_ignore_bind >> simp[outcomes_free_return]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[outcomes_free_return]
QED

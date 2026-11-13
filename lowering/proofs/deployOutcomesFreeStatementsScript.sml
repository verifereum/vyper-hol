Theory deployOutcomesFreeStatements
Ancestors
  deployOutcomesFreeStmtLog deployOutcomesFreeStmtValues
  deployOutcomesFreeStmtControl deployOutcomesFreeTyping
  deployOutcomesFreeStmtAssign deployOutcomesFreeStmtTuple
  deployOutcomesFreeStmtAssignCases deployOutcomesFreeStmtExitCases
  deployOutcomesFreeStmtFlowCases
  deployOutcomesFreeExprBody deployOutcomesFreeLowering stmtLowering
  e2eDeployDefs supportedStmtTraverse supportedExprTraverse exprLowering

Theorem outcomes_free_compile_reason_message:
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
     (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!bs n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_bytelike_literal bs n s)))) ==>
  !env ce e s. ~supported_expr_exists constructor_call_root e /\
    well_typed_expr env e /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_reason_message ce e s)))
Proof
  strip_tac >> gen_tac >> recInduct compile_reason_message_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  simp[compile_reason_message_def]
  >- (irule outcomes_free_bind >> simp[outcomes_free_return]) >>
  metis_tac[]
QED

Theorem outcomes_free_compile_log_eval_all:
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
     (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!ce vv s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce vv s)))) /\
  (!ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode)
       (state_insts (SND (compile_log_save_arg ce ty op es s)))) ==>
  !es env ce s. ~supported_exprs_exists constructor_call_root es /\
    EVERY (well_typed_expr env) es /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_eval_all ce es s)))
Proof
  strip_tac >> Induct >> simp[compile_log_eval_all_def, outcomes_free_return,
    supported_expr_exists_def] >> rpt strip_tac >>
  irule outcomes_free_bind >> reverse conj_tac
  >- (rpt strip_tac >> simp[lower_value_def] >>
      irule outcomes_free_bind >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_bind >> simp[outcomes_free_return] >> metis_tac[]
QED

(* The expression and target certificates are deliberately typed and quantify
   over source environments independently of the lowering environment. *)
Theorem outcomes_free_compile_statements_mutual:
  (!opc. ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==> P opc) /\
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!env ce t vt s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_get_target_ptr compile_expr ce t s)))) /\
  (!ce v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v s)))) /\
  (!ce b v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce b v s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce a b ty sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty s)))) /\
  (!ce a ty b sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory_typed ce a ty b sty s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_copy_memory a b n s)))) /\
  (!a b ew ems tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_to_storage a b ew ems tr s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_storage a b n s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_transient a b n s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_word imm a b s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_immutable_bytestring imm a b s)))) /\
  (!imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_words imm a b n k s)))) /\
  (!src prim s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_load_memory src prim s)))) /\
  (!b a c ty n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_binop b a c ty n k s)))) /\
  (!bs n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytelike_literal bs n s)))) /\
  (!ce v ty n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_revert_with_reason ce v ty n s)))) /\
  (!key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_nonreentrant_unlock key tr view s)))) /\
  (!ret prim raw info n lock key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_return ret prim raw info n lock key tr view s)))) /\
  (!ctor imm loc ptr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ptr_load ctor imm loc ptr s)))) /\
  (!a b n loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slot_to_memory a b n loc s)))) /\
  (!ctor imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_copy_to_memory ctor imm a b n k s)))) /\
  (!ce a b ws sz ty sty cap prim load store s.
    MEM load [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD; CALLDATALOAD] /\
    MEM store [MSTORE; SSTORE; TSTORE; ISTORE; INVALID] /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim load store s)))) /\
  (!ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_save_arg ce ty op es s)))) /\
  (!topics s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_topic_ops topics s)))) /\
  (!ce ops tys buf n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_store_data ce ops tys buf n s)))) /\
  (!buf src info s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_to_buf buf src info s)))) ==>
  (!ce lc ty st env ret out s.
    type_stmt env ret st = SOME out /\ ~supported_stmt_expr_exists constructor_call_root st /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmt ce lc ty st s)))) /\
  (!ce lc ty sts env ret out s.
    type_stmts env ret sts = SOME out /\ ~supported_stmts_expr_exists constructor_call_root sts /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce lc ty sts s))))
Proof
  strip_tac >>
  `!ce dst loc value prim sl dt st info n s.
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND
       (compile_assign_value ce dst loc value prim sl dt st info n s)))`
    by (simp[outcomes_free_compile_assign_value]) >>
  `!imm dst value loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND
       (compile_store_at_loc imm dst value loc s)))`
    by (simp[outcomes_free_compile_store_at_loc]) >>
  `!tys ce base offset s. EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND
       (compile_tuple_load_all ce base tys offset s)))`
    by (simp[outcomes_free_compile_tuple_load_all]) >>
  `!tys tgts vals env ce s.
     EVERY (\tgt. ?t. well_typed_atarget env tgt t) tgts /\
     ~supported_assignments_exists constructor_call_root tgts /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND
       (compile_tuple_store_all ce tys tgts vals s)))`
    by (match_mp_tac outcomes_free_compile_tuple_store_all >> simp[] >> metis_tac[]) >>
  `!env ce ty stage tgts src s.
     EVERY (\tgt. ?t. well_typed_atarget env tgt t) tgts /\
     ~supported_assignments_exists constructor_call_root tgts /\
     EVERY (\i. P i.inst_opcode) (state_insts s) ==>
     EVERY (\i. P i.inst_opcode) (state_insts (SND
       (compile_tuple_unpack ce ty stage tgts src s)))`
    by (match_mp_tac outcomes_free_compile_tuple_unpack >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac compile_stmt_ind >> rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`compile_stmt _ _ _ (For _ _ (Range _ _) _ _)`] >- suspend "range"
  >~ [`compile_stmt _ _ _ (For _ _ (Array _) _ _)`] >- suspend "array"
  >~ [`compile_stmt _ _ _ (If _ _ _)`] >- suspend "if"
  >~ [`compile_stmt _ _ _ (AnnAssign _ _ _)`] >- suspend "annassign"
  >~ [`compile_stmt _ _ _ (Assign (BaseTarget _) _)`] >- suspend "assign"
  >~ [`compile_stmt _ _ _ (Assign (TupleTarget _) _)`] >- suspend "tuple"
  >~ [`compile_stmt _ _ _ (AugAssign _ _ _ _)`] >- suspend "augassign"
  >~ [`compile_stmt _ _ _ (Append _ _)`] >- suspend "append"
  >~ [`compile_stmt _ _ _ (Log _ _)`] >- suspend "log"
  >~ [`compile_stmt _ _ _ (Return (SOME _))`] >- suspend "return_some"
  >~ [`compile_stmt _ _ _ (Return NONE)`] >- suspend "return_none"
  >~ [`compile_stmts _ _ _ (_::_)`] >- suspend "cons"
  >~ [`compile_stmt _ _ _ (Assert _ (AssertReason _))`] >- suspend "assert_reason"
  >~ [`compile_stmt _ _ _ (Assert _ AssertBare)`] >- suspend "assert_simple"
  >~ [`compile_stmt _ _ _ (Assert _ AssertUnreachable)`] >- suspend "assert_simple"
  >~ [`compile_stmt _ _ _ (Raise (RaiseReason _))`] >- suspend "raise_reason"
  >~ [`compile_stmt _ _ _ (Expr _)`] >- suspend "expr" >>
  simp[Once compile_stmt_def, outcomes_free_return, outcomes_free_emit_ops,
       supported_stmt_expr_exists_def] >>
  rpt (irule outcomes_free_ignore_bind >> simp[outcomes_free_return]) >>
  simp[outcomes_free_emit_ops]
QED

Resume outcomes_free_compile_statements_mutual[range]:
  markerLib.RESUME_TAC >>
  drule outcomes_free_typed_for >> strip_tac >>
  drule outcomes_free_typed_range_iterator >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_range >> simp[] >>
  conj_tac
  >- (qpat_x_assum `!is_signed ce exit incr. _`
        (qspec_then `is_signed_type fty` mp_tac) >> simp[] >> metis_tac[]) >>
  reverse conj_tac >- simp[outcomes_free_range_bound_checks] >>
  qpat_x_assum `~supported_iterator_exists _ _` mp_tac >>
  simp[supported_iterator_exists_def] >> strip_tac >>
  rpt strip_tac >> gvs[] >> simp[lower_value_def] >>
  irule outcomes_free_bind >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[array]:
  markerLib.RESUME_TAC >>
  drule outcomes_free_typed_for >> strip_tac >>
  drule outcomes_free_typed_array_iterator >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_iterator_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_array >> simp[] >> conj_tac
  >- (qpat_x_assum `!a b c. _` mp_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule outcomes_free_iter_elem_copy >> simp[]) >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[if]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_if >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_if >> simp[] >> rpt conj_tac
  >- metis_tac[]
  >- metis_tac[] >>
  rpt strip_tac >> simp[lower_value_def] >>
  irule outcomes_free_bind >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[annassign]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_annassign >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_annassign >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[assign]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_assign >> strip_tac >>
  drule outcomes_free_typed_base_assignment >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_assign_base >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[tuple]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_assign >> strip_tac >>
  drule outcomes_free_typed_tuple_assignment >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_assign_tuple >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[augassign]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_augassign >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_assignment_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_augassign >> simp[listTheory.EVERY_DEF] >>
  conj_tac
  >- (rpt strip_tac >> simp[lower_value_def] >>
      irule outcomes_free_bind >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[append]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_append >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_append >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      Cases_on `infer_array_location ce (target_to_expr target)` >>
      simp[compileEnvTheory.load_opc_for_def, compileEnvTheory.store_opc_for_def]) >>
  rpt strip_tac >> simp[lower_value_def] >>
  irule outcomes_free_bind >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[log]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_log >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_log >> simp[] >>
  rpt strip_tac >> irule outcomes_free_compile_log_eval_all >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[return_none]:
  markerLib.RESUME_TAC >> irule outcomes_free_stmt_return_none >> simp[] >>
  rpt strip_tac >> irule outcomes_free_return_unlock >> simp[]
QED

Resume outcomes_free_compile_statements_mutual[return_some]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_return >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def, supported_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_return_some >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[lower_value_def] >>
      irule outcomes_free_bind >> simp[] >> metis_tac[]) >>
  rpt strip_tac >> irule outcomes_free_internal_return_from_env >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> irule outcomes_free_return_unlock >> simp[]) >>
  simp[outcomes_free_compile_internal_return]
QED

Resume outcomes_free_compile_statements_mutual[expr]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_expr_stmt >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >> irule outcomes_free_ignore_bind >>
  simp[outcomes_free_return] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[assert_simple]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_assert >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_assert_simple >> simp[] >>
  rpt strip_tac >> simp[lower_value_def] >>
  irule outcomes_free_bind >> simp[] >> metis_tac[]
QED

Resume outcomes_free_compile_statements_mutual[assert_reason]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_assert >> strip_tac >>
  drule outcomes_free_typed_assert_reason >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_assert_reason >> simp[] >> conj_tac
  >- (rpt strip_tac >> simp[lower_value_def] >>
      irule outcomes_free_bind >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule outcomes_free_compile_reason_message >>
      simp[] >> conj_tac >- metis_tac[] >>
      fs[supported_assert_exists_def] >> metis_tac[]) >>
  rpt gen_tac >> rpt disch_tac >>
  irule outcomes_free_compile_revert_with_reason >> simp[]
QED

Resume outcomes_free_compile_statements_mutual[raise_reason]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_raise_reason >> strip_tac >>
  qpat_x_assum `~supported_stmt_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  irule outcomes_free_stmt_raise >> simp[] >> conj_tac
  >- (rpt strip_tac >> irule outcomes_free_compile_reason_message >> simp[] >>
      conj_tac >- metis_tac[] >>
      fs[supported_raise_exists_def] >> metis_tac[]) >>
  rpt gen_tac >> rpt disch_tac >>
  irule outcomes_free_compile_revert_with_reason >> simp[]
QED

Resume outcomes_free_compile_statements_mutual[cons]:
  markerLib.RESUME_TAC >> drule outcomes_free_typed_stmts_cons >> strip_tac >>
  qpat_x_assum `~supported_stmts_expr_exists _ _` mp_tac >>
  simp[supported_stmt_expr_exists_def] >> strip_tac >>
  simp[Once compile_stmt_def] >> irule outcomes_free_bind >>
  simp[compileEnvTheory.comp_get_def] >> rpt gen_tac >> strip_tac >> BETA_TAC >>
  IF_CASES_TAC >- simp[outcomes_free_return] >>
  irule outcomes_free_bind >> reverse conj_tac
  >- simp[outcomes_free_declare_stmt_local] >>
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  irule outcomes_free_ignore_bind >> conj_tac >> rpt strip_tac >> metis_tac[]
QED

Finalise outcomes_free_compile_statements_mutual

(* Projection interfaces retain the generator obligations for the Body join. *)
Theorem outcomes_free_compile_stmt_conditional:
  (!opc. ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==> P opc) /\
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!env ce t vt s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_get_target_ptr compile_expr ce t s)))) /\
  (!ce v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v s)))) /\
  (!ce b v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce b v s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce a b ty sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty s)))) /\
  (!ce a ty b sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory_typed ce a ty b sty s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_copy_memory a b n s)))) /\
  (!a b ew ems tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_to_storage a b ew ems tr s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_storage a b n s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_transient a b n s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_word imm a b s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_immutable_bytestring imm a b s)))) /\
  (!imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_words imm a b n k s)))) /\
  (!src prim s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_load_memory src prim s)))) /\
  (!b a c ty n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_binop b a c ty n k s)))) /\
  (!bs n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytelike_literal bs n s)))) /\
  (!ce v ty n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_revert_with_reason ce v ty n s)))) /\
  (!key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_nonreentrant_unlock key tr view s)))) /\
  (!ret prim raw info n lock key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_return ret prim raw info n lock key tr view s)))) /\
  (!ctor imm loc ptr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ptr_load ctor imm loc ptr s)))) /\
  (!a b n loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slot_to_memory a b n loc s)))) /\
  (!ctor imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_copy_to_memory ctor imm a b n k s)))) /\
  (!ce a b ws sz ty sty cap prim load store s. MEM load [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD; CALLDATALOAD] /\ MEM store [MSTORE; SSTORE; TSTORE; ISTORE; INVALID] /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim load store s)))) /\
  (!ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_save_arg ce ty op es s)))) /\
  (!topics s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_topic_ops topics s)))) /\
  (!ce ops tys buf n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_store_data ce ops tys buf n s)))) /\
  (!buf src info s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_to_buf buf src info s)))) ==>
  !ce lc ty st env ret out s.
    type_stmt env ret st = SOME out /\ ~supported_stmt_expr_exists constructor_call_root st /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmt ce lc ty st s)))
Proof
  MATCH_ACCEPT_TAC (cj 1 outcomes_free_compile_statements_mutual)
QED

Theorem outcomes_free_compile_stmts_conditional:
  (!opc. ~MEM opc [CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; INVOKE] ==> P opc) /\
  (!env ce ty e s. ~supported_expr_exists constructor_call_root e /\
    (well_typed_expr env e \/ (?vt. type_place_expr env e = SOME vt)) /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_expr ce ty e s)))) /\
  (!env ce t vt s. type_place_target env t = SOME vt /\
    ~supported_target_exists constructor_call_root t /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_get_target_ptr compile_expr ce t s)))) /\
  (!ce v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (unwrap_value ce v s)))) /\
  (!ce b v s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_snapshot_vv ce b v s)))) /\
  (!n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_alloc_buffer n s)))) /\
  (!ce a b ty sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory ce a b ty sty s)))) /\
  (!ce a ty b sty s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_memory_typed ce a ty b sty s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_copy_memory a b n s)))) /\
  (!a b ew ems tr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_to_storage a b ew ems tr s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_storage a b n s)))) /\
  (!a b n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_memory_to_transient a b n s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_word imm a b s)))) /\
  (!imm a b s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_store_immutable_bytestring imm a b s)))) /\
  (!imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_store_words imm a b n k s)))) /\
  (!src prim s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_load_memory src prim s)))) /\
  (!b a c ty n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_binop b a c ty n k s)))) /\
  (!bs n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_bytelike_literal bs n s)))) /\
  (!ce v ty n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_revert_with_reason ce v ty n s)))) /\
  (!key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_nonreentrant_unlock key tr view s)))) /\
  (!ret prim raw info n lock key tr view s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_external_return ret prim raw info n lock key tr view s)))) /\
  (!ctor imm loc ptr s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_ptr_load ctor imm loc ptr s)))) /\
  (!a b n loc s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_slot_to_memory a b n loc s)))) /\
  (!ctor imm a b n k s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_imm_copy_to_memory ctor imm a b n k s)))) /\
  (!ce a b ws sz ty sty cap prim load store s. MEM load [MLOAD; SLOAD; TLOAD; ILOAD; DLOAD; CALLDATALOAD] /\ MEM store [MSTORE; SSTORE; TSTORE; ISTORE; INVALID] /\ EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_dynarray_append ce a b ws sz ty sty cap prim load store s)))) /\
  (!ce ty op es s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_save_arg ce ty op es s)))) /\
  (!topics s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_topic_ops topics s)))) /\
  (!ce ops tys buf n s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_log_store_data ce ops tys buf n s)))) /\
  (!buf src info s. EVERY (\i. P i.inst_opcode) (state_insts s) ==> EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_abi_encode_to_buf buf src info s)))) ==>
  !ce lc ty sts env ret out s.
    type_stmts env ret sts = SOME out /\ ~supported_stmts_expr_exists constructor_call_root sts /\
    EVERY (\i. P i.inst_opcode) (state_insts s) ==>
    EVERY (\i. P i.inst_opcode) (state_insts (SND (compile_stmts ce lc ty sts s)))
Proof
  MATCH_ACCEPT_TAC (cj 2 outcomes_free_compile_statements_mutual)
QED

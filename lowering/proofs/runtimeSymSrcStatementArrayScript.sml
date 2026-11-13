Theory runtimeSymSrcStatementArray
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcModuleDispatch
  runtimeSymSrcArrayLoopBlocks runtimeSymSrcArrayIterator stmtLowering compileEnv
  supportedStmts supportedStmtTraverse supportedExprs context venomInst stackPlanTypes
  emitHelper loweringShapeDefs list finite_map vyperAST

(* Iter-copy is supplied by C1.1.5.4.1; declaration/allocation boundaries
   are supplied by the declaration family. The loop_body callback is only for
   the proper loop_body subterm, at arbitrary safe environments and loop labels. *)
Theorem runtime_sym_stmt_for_array_conditional:
  (!src dst sz loc slots dt st s u s'.
    runtime_sym_env ce /\ ~is_label_operand src /\ ~is_label_operand dst /\
    EVERY runtime_sym_inst (state_insts s) /\
    compile_iter_elem_copy ce src dst sz loc slots dt st s = (u,s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  runtime_sym_expr_contract tops compile_expr ce (expr_type arr_e) arr_e /\
  (!s ce' s'. runtime_sym_env ce /\ EVERY runtime_sym_inst (state_insts s) /\
    declare_local ce id fty s = (ce',s') ==>
    runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s')) /\
  (!ce' s s'. runtime_sym_env ce' /\ EVERY runtime_sym_inst (state_insts s) /\
    emit_local_alloca ce' id s = ((),s') ==>
    EVERY runtime_sym_inst (state_insts s')) /\
  (!bs ce' lc'. runtime_sym_stmts_contract tops bs compile_stmts ce' lc' ty loop_body) ==>
  runtime_sym_stmt_contract tops bindings compile_stmt ce lc ty
    (For id fty (Array arr_e) bound loop_body)
Proof
  strip_tac >> simp[runtime_sym_stmt_contract_def] >> rpt gen_tac >> strip_tac >>
  fs[Once supported_stmt_def, Once supported_stmt_expr_exists_def,
     supported_iterator_exists_def] >>
  drule runtime_sym_array_iterator_type >> strip_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  drule_at (Pat `supported_iterator _ _ _ _`) runtime_sym_array_iterator_eval >> simp[] >>
  disch_then (drule_at (Pat `compile_expr _ _ _ _ = _`)) >> simp[] >> strip_tac >>
  drule runtime_sym_value_operand >> strip_tac >>
  drule_all (PURE_REWRITE_RULE [comp_return_def] runtime_sym_array_length) >> strip_tac >>
  qpat_x_assum `!s ce' s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!ce' s s'. _` drule_all >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  qpat_assum `emit_inst JMP [Label entry_lbl] [] _ = _`
    (mp_then (Pat `emit_inst JMP [Label _] [] _ = _`) mp_tac runtime_sym_array_entry) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  fs[arithmeticTheory.GREATER_DEF] >>
  qpat_assum `emit_op ADD [vv_operand arr_vv; _] _ = _`
    (mp_then (Pat `emit_op ADD _ _ = _`) mp_tac runtime_sym_array_address) >>
  disch_then (drule_at (Pat `(if _ then _ else _) _ = _`)) >>
  disch_then (drule_at (Pat `emit_op MUL _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op EQ _ _ = _`)) >>
  disch_then drule_all >> strip_tac >>
  drule_at (Pat `_ _ = (_,_)`) runtime_sym_array_copy >> simp[] >>
  (impl_tac >- first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!bs ce' lc'. _`
    (qspecl_then [`bindings`, `body_cenv`, `InLoop exit_lbl incr_lbl`] mp_tac) >>
  simp[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >>
  disch_then drule_all >> strip_tac >>
  drule_all runtime_sym_array_tail >> simp[]
QED

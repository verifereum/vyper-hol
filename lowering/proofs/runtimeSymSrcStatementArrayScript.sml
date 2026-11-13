Theory runtimeSymSrcStatementArray
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission runtimeSymSrcModuleDispatch stmtLowering compileEnv
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
  strip_tac >> simp[runtime_sym_stmt_contract_def] >> rpt strip_tac >>
  fs[Once supported_stmt_def, Once supported_stmt_expr_exists_def,
     supported_iterator_def, AllCaseEqs()] >>
  Cases_on `arr_e` >> fs[] >>
  rename1 `Name aty nm` >> Cases_on `aty` >> fs[] >>
  rename1 `ArrayT et bd` >> Cases_on `bd` >> gvs[] >>
  gvs[Once compile_stmt_def, expr_type_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  ntac 5 (pairarg_tac >> gvs[]) >>
  rpt (pairarg_tac >> gvs[]) >>
  fs[runtime_sym_expr_contract_def, supported_iterator_exists_def] >>
  qpat_x_assum `!s v s'. _` (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
  (impl_tac >- simp[supported_expr_def, supported_pure_expr_def]) >>
  strip_tac >> drule runtime_sym_value_operand >> strip_tac >>
  qpat_x_assum `!s ce' s'. _` drule_all >> strip_tac >>
  qpat_x_assum `!ce' s s'. _` drule_all >> strip_tac >>
  imp_res_tac runtime_sym_fresh_label >> gvs[] >>
  imp_res_tac runtime_sym_fresh_var >> gvs[] >>
  qpat_assum `emit_inst JMP [Label entry_lbl] _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> (impl_tac >- simp[]) >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> fs[] >>
  qpat_assum `emit_inst ASSIGN [Lit 0w] _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  simp[runtime_sym_ordinary_inst, is_label_operand_def] >> strip_tac >>
  rename1 `emit_inst ASSIGN [Lit 0w] [idx_var] _ = ((),init_s)` >>
  qpat_assum `emit_inst JMP [Label cond_lbl] _ init_s = _`
    (mp_then Any mp_tac runtime_sym_jump) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `emit_op EQ _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_assum `emit_inst JNZ _ _ _ = _` (mp_then Any mp_tac runtime_sym_jnz) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `emit_op MUL _ _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_assum `emit_op ADD [vv_operand _; _] _ = _` (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[]) >> strip_tac >>
  suspend "tail"
QED

Resume runtime_sym_stmt_for_array_conditional[tail]:
  rename1 `compile_stmts body_cenv (InLoop exit_lbl incr_lbl) ty loop_body copy_s = _` >>
  `EVERY runtime_sym_inst (state_insts copy_s)` by
    (Cases_on `FLOOKUP body_cenv.ce_vars id` >> gvs[]
     >- (drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
     drule_all runtime_sym_env_local >> strip_tac >>
     Cases_on `x` >> gvs[runtime_sym_loc_def]
     >>~- ([`emit_void INVALID [] _ = _`],
           drule_at (Pat `emit_void _ _ _ = _`) runtime_sym_emit_void >> simp[]) >>
     qpat_x_assum `!src dst sz loc slots dt st s s'. _`
       (fn th => qpat_assum `compile_iter_elem_copy _ _ _ _ _ _ _ _ _ = _`
          (mp_then Any mp_tac th)) >> simp[is_label_operand_def]) >>
  qpat_x_assum `!bs ce' lc'. _`
    (qspecl_then [`bindings`, `body_cenv`, `InLoop exit_lbl incr_lbl`] mp_tac) >>
  simp[runtime_sym_stmts_contract_def, runtime_sym_loop_def] >>
  disch_then drule_all >> strip_tac >>
  drule_all runtime_sym_jmp_if_not_terminated >> strip_tac >>
  qpat_assum `emit_op ADD [Var idx_var; Lit 1w] _ = _`
    (mp_then Any mp_tac runtime_sym_emit_op) >>
  (impl_tac >- simp[is_label_operand_def]) >> strip_tac >>
  qpat_assum `emit_inst ASSIGN [new_idx] _ _ = _`
    (mp_then Any mp_tac runtime_sym_emit_inst) >>
  simp[runtime_sym_ordinary_inst] >> strip_tac >>
  qpat_assum `emit_inst JMP [Label cond_lbl] _ _ = _`
    (mp_then Any mp_tac runtime_sym_jump) >> simp[]
QED
Finalise runtime_sym_stmt_for_array_conditional

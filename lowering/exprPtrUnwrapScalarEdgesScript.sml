(* Scalar ghost boundaries for the bounded generated copy body. *)
Theory exprPtrUnwrapScalarEdges
Ancestors
  exprPtrUnwrapCopyEdges typedCopyPtr ptrDiscipline venomState venomInst
  venomExecSemantics venomInstProofs ptrSafeRun finite_map codegenRel contextCodegenRel

Theorem copy_mul_ghost_frame:
  !PG G tn s id left right tmp w.
    op_taint (step_taint (mk_inst id MUL [left;right] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = out_taint tn (mk_inst id MUL [left;right] [tmp]) s /\
    (step_taint (mk_inst id MUL [left;right] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id MUL [left;right] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id MUL [left;right] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id MUL [left;right] [tmp]) s
      (update_var tmp w s) tn).t_imm = tn.t_imm /\
    (!p. p <> tmp ==>
      FLOOKUP (step_prov PG G (mk_inst id MUL [left;right] [tmp])
        (update_var tmp w s)) p = FLOOKUP G p /\
      op_taint (step_taint (mk_inst id MUL [left;right] [tmp]) s
        (update_var tmp w s) tn) (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >>
  `new_site_bytes s (update_var tmp w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  Cases_on `eval_operand left s` >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem copy_assign_ghost_frame:
  !PG G tn s id arg tmp w.
    op_taint tn arg = {} ==>
    op_taint (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp w s) tn) (Var tmp) = {} /\
    (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp w s) tn).t_mem = tn.t_mem /\
    (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp w s) tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp w s) tn).t_trans = tn.t_trans /\
    (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
      (update_var tmp w s) tn).t_imm = tn.t_imm /\
    (!p. p <> tmp ==>
      FLOOKUP (step_prov PG G (mk_inst id ASSIGN [arg] [tmp])
        (update_var tmp w s)) p = FLOOKUP G p /\
      op_taint (step_taint (mk_inst id ASSIGN [arg] [tmp]) s
        (update_var tmp w s) tn) (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `eval_operand arg s` >> Cases_on `first_prov G [arg]` >>
  gvs[op_taint_def] >>
  `new_site_bytes s (update_var tmp w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem ptr_inst_ok_copy_arith:
  (opc = ADD \/ opc = MUL) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn
    (mk_inst id opc [left;right] [tmp]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ptr_inst_ok_copy_assign:
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id ASSIGN [arg] [tmp]) s
Proof
  strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, mk_inst_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[]
QED

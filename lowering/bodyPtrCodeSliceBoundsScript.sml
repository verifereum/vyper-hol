(* Source-independent checked bounds for clean provenance-free words. *)
Theory bodyPtrCodeSliceBounds
Ancestors
  exprSimSliceBounds typedCopyPtr exprSendPtr bodyPtrHashBuiltinsGhostFrame
  fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel compileEnv
  loweringStateRelDefs words finite_map pred_set list

Theorem slice_bounds_compare_checked:
  !D ctx fn G tn s id opc a b dst fuel.
    (opc = LT \/ opc = GT \/ opc = OR) /\
    op_taint tn a = {} /\ op_taint tn b = {} /\
    op_prov G a = NONE /\ op_prov G b = NONE /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a;b] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  `!u. a = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  `!u. b = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_iszero_checked:
  !D ctx fn G tn s id a dst fuel.
    op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [a] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_scalar_ghost:
  !PG G tn s id opc ops out w.
    (opc = ADD \/ opc = LT \/ opc = GT \/ opc = OR \/ opc = ISZERO) /\
    EVERY (\op. op_prov G op = NONE) ops ==>
    step_prov PG G (mk_inst id opc ops [out]) (update_var out w s) =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id opc ops [out]) s (update_var out w s) tn =
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> disch_tac >>
  `out_prov PG G (mk_inst id opc ops [out]) (update_var out w s) = NONE` by
    (Cases_on `opc = ADD`
     >- (irule out_prov_arith_none >> simp[mk_inst_def]) >>
     irule out_prov_other_none >> gvs[mk_inst_def]) >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         EXTENSION, SF CONJ_ss] >>
  conj_tac >- simp[step_prov_def, set_prov_def, mk_inst_def] >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality] >>
  (Cases_on `ops` >- simp[out_taint_def] >>
   Cases_on `t` >- (simp[out_taint_def] >> CASE_TAC >> simp[]) >>
   Cases_on `t'` >- (simp[out_taint_def] >> CASE_TAC >> simp[]) >>
   Cases_on `t` >> simp[out_taint_def])
QED

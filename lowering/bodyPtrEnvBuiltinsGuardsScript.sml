(* Scalar guard boundaries for the guarded BLOCKHASH suffix.
   ASSERT paths (including failure) are supplied by exprSendPtr. *)
Theory bodyPtrEnvBuiltinsGuards
Ancestors
  bodyPtrEnvBuiltinsEdges bodyPtrDefs exprSendPtr fragGasSeqPtr
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  finite_map pred_set list codegenRel contextCodegenRel

Theorem guard_compare_inst_ok:
  MEM opc [LT; SLT] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops [out]) s
Proof
  strip_tac >> gvs[MEM] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs, instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[]
  >- (qpat_x_assum `!op. _` (qspec_then `Var u` mp_tac) >>
      simp[op_prov_def, finite_mapTheory.FLOOKUP_DEF])
  >- (qpat_x_assum `!op. _` (qspec_then `Var w` mp_tac) >>
      simp[op_prov_def, finite_mapTheory.FLOOKUP_DEF]) >>
  metis_tac[]
QED

Theorem guard_compare_output_clean:
  MEM opc [LT; SLT] ==>
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) (Var out) = NONE /\
  op_taint (step_taint (mk_inst id opc ops [out]) s t tn) (Var out) = {}
Proof
  simp[MEM] >> strip_tac >>
  gvs[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
      mk_inst_def, FLOOKUP_DRESTRICT, op_taint_def, step_taint_def,
      set_var_taint_def, FLOOKUP_UPDATE, out_taint_def] >>
  (namedCases_on `ops` ["", "a rest"] >> simp[] >>
   namedCases_on `rest` ["", "b tail"]
   >- (Cases_on `eval_operand a s` >> simp[]) >>
   Cases_on `tail` >> simp[] >>
   Cases_on `eval_operand a s` >> simp[])
QED

Theorem scalar_arith_output_no_prov:
  MEM opc [ADD; SUB; ASSIGN] /\
  (!op. MEM op ops ==> op_prov G op = NONE) ==>
  op_prov (step_prov PG G (mk_inst id opc ops [out]) t) (Var out) = NONE
Proof
  strip_tac >>
  `first_prov G ops = NONE` by
    simp[first_prov_eq_none, EVERY_MEM] >>
  gvs[MEM, op_prov_def, step_prov_def, set_prov_def, out_prov_def,
      mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem guard_compare_counted_edge:
  MEM opc [LT; SLT] /\
  (!op. MEM op ops ==> op_taint tn op = {} /\ op_prov G op = NONE) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc ops [out]) /\
  step_inst_base (mk_inst id opc ops [out]) s = OK u ==>
  gas_path_ptr_edge D 0 ctx fn PG G tn s 0
    (step_prov PG G (mk_inst id opc ops [out]) u)
    (step_taint (mk_inst id opc ops [out]) s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc ops [out]) s` by
    (irule guard_compare_inst_ok >> simp[]) >>
  `opc <> INVOKE /\ ~is_terminator opc` by
    (gvs[MEM] >> simp[is_terminator_def]) >>
  `opc <> GAS` by gvs[MEM] >>
  drule_at (Pat `step_inst_base _ _ = _`) straight_line_ptr_edge >>
  simp[mk_inst_def] >> disch_then irule >> gvs[mk_inst_def]
QED

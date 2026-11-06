(* External-source slice instructions: offsets are scalar source positions,
   not pointers into the runtime memory provenance map. *)
Theory bodyPtrBytestringBuiltinsExternalSlice
Ancestors
  bodyPtrBytestringBuiltinsSlice ptrDiscipline fragExecPtr venomInst
  venomExecSemantics venomState bodyPtrDefs list words finite_map
  ptrSafeRun memLocDefs codegenRel contextCodegenRel

Theorem ptr_inst_ok_external_copy:
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst; start; cnt_op]) \/
   (opc = EXTCODECOPY /\ ops = [addr; Var dst; start; cnt_op] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand start s = SOME a /\ eval_operand cnt_op s = SOME n /\
  op_taint tn start = {} /\ op_taint tn cnt_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc ops []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    source_memory_write_ranges_def, source_memory_read_ranges_def,
    fixed_source_write_range_def, eval_operand_def, mem_write_ops_def,
    mem_read_ops_def, sized_source_write_range_def, mk_inst_def,
    step_inst_non_invoke, Once step_inst_base_def,
    write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[] >>
  TRY (qpat_x_assum `step_inst_base _ _ = Halt _` mp_tac >>
       PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
       simp[eval_operand_def] >> NO_TAC) >>
  metis_tac[]
QED

Theorem external_copy_ghost_frame:
  (opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY) ==>
  step_prov PG G (mk_inst id opc ops []) t = G /\
  (step_taint (mk_inst id opc ops []) s t tn).t_var = tn.t_var /\
  (step_taint (mk_inst id opc ops []) s t tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc ops []) s t tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id opc ops []) s t tn).t_imm = tn.t_imm
Proof
  strip_tac >> gvs[step_prov_def, set_prov_def, out_prov_def,
    step_taint_def, set_var_taint_def, out_taint_def, store_taint_def,
    imm_taint_def, adopt_reset_def, mem_taint_def, mk_inst_def,
    DRESTRICT_UNIV]
QED

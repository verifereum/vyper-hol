Theory exprSimAbiDecodePrefixProbe
Ancestors
  fragExec venomExecSemantics venomExecProofs venomExecProps venomInstProofs venomState venomInst finite_map

(* A successful observation cannot skip an ALLOCA at the current cursor.
   Keep the actual remaining run, not merely the instruction's code membership. *)
Theorem abi_decode_alloca_run_inversion:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode = ALLOCA /\ run_from fuel ctx fn s = Halt h ==>
  ?u. step_inst_base inst s = OK u /\
    run_from fuel ctx fn (u with vs_inst_idx := SUC s.vs_inst_idx) = Halt h
Proof
  strip_tac >>
  qpat_x_assum `run_from fuel ctx fn s = Halt h` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke,
    is_terminator_def] >>
  Cases_on `step_inst_base inst s` >> simp[]
  >- (strip_tac >> rename1 `step_inst_base inst s = OK u` >>
      `u.vs_current_bb = s.vs_current_bb` by
        (qpat_x_assum `step_inst_base inst s = OK u` mp_tac >>
         simp[Once step_inst_base_def, exec_alloca_def, AllCaseEqs(),
           update_var_def] >> rpt strip_tac >> gvs[]) >>
      simp[Once run_from_def]) >>
  qpat_x_assum `step_inst_base inst s = _` mp_tac >>
  simp[Once step_inst_base_def, exec_alloca_def, AllCaseEqs()]
QED

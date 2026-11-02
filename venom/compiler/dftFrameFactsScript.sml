(* Semantic boundaries for DFT frame-prefix simulation. *)
Theory dftFrameFacts
Ancestors
  dftDefs unitShapeDefs venomExecSemantics venomWf venomState venomInst
  venomEffects finite_map list option

Theorem dft_operand_defined:
  (!v. MEM (Var v) ops ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) ops ==> l IN FDOM s.vs_labels) /\
  MEM op ops ==> ?w. eval_operand op s = SOME w
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >>
  metis_tac[FLOOKUP_DEF, option_CASES]
QED

Theorem dft_operands_defined[local]:
  (!op. MEM op ops ==> ?w. eval_operand op s = SOME w) ==>
  ?ws. eval_operands ops s = SOME ws
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt strip_tac >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >> simp[] >> metis_tac[]
QED

Theorem dft_movable_step_total:
  inst_wf i /\ inst_shape_ok i /\ ~is_pseudo i.inst_opcode /\
  ~is_terminator i.inst_opcode /\ ~is_fallible i /\
  i.inst_opcode <> ALLOCA /\
  (!v. MEM (Var v) i.inst_operands ==> v IN FDOM s.vs_vars) /\
  (!l. MEM (Label l) i.inst_operands ==> l IN FDOM s.vs_labels) ==>
  ?t. step_inst fuel C i s = OK t
Proof
  strip_tac >>
  `!op. MEM op i.inst_operands ==> ?w. eval_operand op s = SOME w`
    by metis_tac[dft_operand_defined] >>
  Cases_on `i.inst_opcode` >>
  gvs[is_fallible_def, opcode_fail_class_def, is_pseudo_def,
      is_terminator_def, inst_shape_ok_def] >>
  qpat_x_assum `inst_wf i` mp_tac >>
  asm_simp_tac (pure_ss ++ boolSimps.BOOL_ss)
    [inst_wf_def, TypeBase.case_def_of ``:opcode``] >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> gvs[] >>
  simp[step_inst_non_invoke] >>
  simp[step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def] >>
  gvs[DISJ_IMP_THM, FORALL_AND_THM] >>
  simp[exec_ext_call_def, LET_THM] >>
  rpt pairarg_tac >> gvs[] >>
  simp[REVERSE_APPEND, AllCaseEqs()] >>
  metis_tac[dft_operands_defined, MEM_REVERSE]
QED

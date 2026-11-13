Theory concretizePtrDallocaAffine
Ancestors
  concretizePtrBPReverse concretizePtrDallocaGhostInterface
  ptrDiscipline venomState venomInst finite_map pred_set list

Theorem ptr_dalloca_affine_out_prov:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ FDOM G SUBSET fn_pv P fn /\
  (!v site. FLOOKUP Gt v = SOME site ==> FLOOKUP G v = SOME site) /\
  out_prov PGt Gt inst t = SOME site ==>
  out_prov PG G inst s = SOME site
Proof
  strip_tac >>
  `~(?v w. a = Var v /\ b = Var w /\
           v IN fn_pv P fn /\ w IN fn_pv P fn)` by
    metis_tac[ptr_reverse_affine] >>
  gvs[out_prov_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[first_prov_def, op_prov_def, AllCaseEqs()] >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

Theorem ptr_dalloca_affine_operand_values:
  fn_ptr_ok P fn /\ MEM inst (fn_insts fn) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
  inst.inst_operands = [a;b] /\ FDOM G SUBSET fn_pv P fn /\
  ptr_dalloca_ghost_vars G V s Gt Vt t /\
  (!v. v NOTIN fn_pv P fn ==> lookup_var v s = lookup_var v t) /\
  s.vs_labels = t.vs_labels /\
  out_prov PGt Gt inst t = SOME site ==>
  !op. MEM op [a;b] ==> eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `~(?v w. a = Var v /\ b = Var w /\
           v IN fn_pv P fn /\ w IN fn_pv P fn)` by
    metis_tac[ptr_reverse_affine] >>
  gvs[out_prov_def, ptr_dalloca_ghost_vars_def] >>
  Cases_on `a` >> Cases_on `b` >>
  gvs[first_prov_def, op_prov_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[eval_operand_def] >>
  fs[SUBSET_DEF, FLOOKUP_DEF] >> metis_tac[]
QED

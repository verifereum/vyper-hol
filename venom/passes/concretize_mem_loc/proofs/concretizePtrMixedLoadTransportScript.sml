Theory concretizePtrMixedLoadTransport
Ancestors concretizePtrLoadTransport concretizePtrOpaqueRetpc
  concretizePtrValueTransport ptrDiscipline venomExecSemantics
  venomState codegenRel list words finite_map pred_set

Theorem ptr_mixed_mload_transport_back:
  inst.inst_opcode = MLOAD /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [out] /\
  ((?v. op = Var v) \/ (?w. op = Lit w)) /\
  ~retpc_var f out /\
  ptr_mixed_vars births positions TG tn f g s t /\
  eval_operand op s = SOME x /\ eval_operand op t = SOME y /\
  (!k. k < 32 /\ w2n x + k NOTIN tn.t_mem ==>
    read_byte (w2n x+k) s.vs_memory = read_byte (w2n y+k) t.vs_memory) /\
  step_inst fuel C' inst t = OK t' ==>
  ?s'. step_inst fuel C inst s = OK s' /\
    ptr_mixed_vars births positions (step_prov PT TG inst s')
      (step_taint inst s s' tn) f g s' t'
Proof
  strip_tac >>
  `word_agree_except (mem_word_taint tn.t_mem (w2n x))
    (mload (w2n x) s) (mload (w2n y) t)` by
    (irule ptr_mload_masked_value >> simp[]) >>
  gvs[Once run_defs, step_inst_base_def, exec_read1_def,
      eval_operands_def, AllCaseEqs()] >>
  qexists_tac `update_var out (mload (w2n x) s) s` >>
  simp[Once run_defs, step_inst_base_def, exec_read1_def, eval_operands_def] >>
  irule ptr_mixed_vars_update >>
  simp[step_prov_def, out_prov_def, step_taint_def, out_taint_def,
       set_prov_def, set_var_taint_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[ptr_value_transport_def] >>
  fs[ptr_mixed_vars_def, ptrDisciplineTheory.op_taint_def] >>
  metis_tac[]
QED

Theory bodyPureModTaintMods
Ancestors
  ptrDiscipline venomInst venomState codegenRel finite_map

Theorem pure_mod_step_taint:
  !id opc x y z out s u v tn.
    (opc = ADDMOD \/ opc = MULMOD) /\
    u = update_var out v s /\
    op_taint tn x = {} /\
    op_taint tn y = {} /\
    op_taint tn z = {} /\
    out_taint tn (mk_inst id opc [x;y;z] [out]) s = {} /\
    written_taint tn (mk_inst id opc [x;y;z] [out]) s = {} /\
    new_site_bytes s u = {} ==>
    step_taint (mk_inst id opc [x;y;z] [out]) s u tn =
      tn with t_var := tn.t_var |+ (out,{})
Proof
  rpt gen_tac >> strip_tac >>
  gvs[mk_inst_def] >>
  simp[step_taint_def, taint_component_equality, set_var_taint_def,
       store_taint_def, imm_taint_def, adopt_reset_def] >>
  simp[mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       range_bytes_def]
QED

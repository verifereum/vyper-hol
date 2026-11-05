Theory lowerDloadPairedEntry
Ancestors
  lowerDloadOpaqueExecution lowerDloadControlPosition lowerDloadPairedBoundary
  o1PassContract venomInst venomExecProps venomState contextCodegenRel list pred_set

Theorem lower_dload_paired_enters_block:
  lower_dload_function_supply a fn = (gn,b) /\
  ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E AG AH tn un s t /\
  (!v. v IN V ==> (lookup_var v s = NONE <=> lookup_var v t = NONE)) /\
  (!i v. MEM i (fn_insts fn) /\ MEM (Var v) i.inst_operands ==> v IN V) /\
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  enters_block gn t t1 ==>
  ?bb s1.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    enters_block fn s s1 /\
    ld_owned_vars {v | v IN V /\ ~retpc_var fn v} E
      (ld_phis_prov s.vs_prev_bb AG bb.bb_instructions)
      (ld_phis_prov t.vs_prev_bb AH bb.bb_instructions)
      (tn with t_var := phis_taint s.vs_prev_bb tn bb.bb_instructions)
      (un with t_var := phis_taint t.vs_prev_bb un bb.bb_instructions) s1 t1 /\
    (!v. v IN V ==> (lookup_var v s1 = NONE <=> lookup_var v t1 = NONE)) /\
    s1.vs_inst_idx = phi_prefix_length bb.bb_instructions /\
    t1.vs_inst_idx = phi_prefix_length bb.bb_instructions
Proof
  strip_tac >>
  `enters_block fn t t1` by
    metis_tac[lower_dload_function_supply_enters_block] >>
  qpat_x_assum `enters_block fn t t1` mp_tac >>
  simp[enters_block_def] >> strip_tac >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by
    (rpt strip_tac >> simp[fn_insts_def, fn_insts_blocks_MEM] >>
     qexists_tac `bb` >> simp[] >> metis_tac[lookup_block_MEM]) >>
  `!i v. MEM i bb.bb_instructions /\ MEM (Var v) i.inst_operands ==> v IN V` by
    metis_tac[] >>
  drule_all ld_nonopaque_phis_backward >> strip_tac >>
  qexistsl_tac [`bb`, `s' with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  qpat_x_assum `enters_block gn t t1` kall_tac >>
  gvs[ld_owned_vars_def, lookup_var_def, enters_block_def] >> metis_tac[]
QED

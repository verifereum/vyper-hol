Theory dftPacketCalleeAlignment
Ancestors
  dftRunRel o1PassLift gasOracleReplay venomExecSemantics venomInst venomState list

Theorem dft_packet_callee_setup_dft:
  tf = dft_fn sf /\ dft_fn_rel sf tf ==>
  setup_callee sf args s = setup_callee tf args s
Proof
  strip_tac >> irule setup_callee_entry_label >>
  metis_tac[dft_fn_rel_entry_label]
QED

Theorem dft_packet_paired_lookup[local]:
  !fs gs name.
    LIST_REL (\f g. g = dft_fn f) fs gs /\ LIST_REL dft_fn_rel fs gs ==>
    OPTREL (\f g. g = dft_fn f /\ dft_fn_rel f g)
      (lookup_function name fs) (lookup_function name gs)
Proof
  Induct >> Cases_on `gs` >> simp[lookup_function_def, FIND_thm] >>
  rpt strip_tac >>
  `h'.fn_name = h.fn_name` by fs[dft_fn_rel_def] >>
  simp[] >> IF_CASES_TAC >> gvs[lookup_function_def]
QED

Theorem dft_packet_callee_alignment:
  LIST_REL (\f g. g = dft_fn f) C7.ctx_functions C8.ctx_functions /\
  LIST_REL dft_fn_rel C7.ctx_functions C8.ctx_functions /\
  decode_invoke c = SOME (nm,ops) /\
  lookup_function nm C8.ctx_functions = SOME ctf /\
  eval_operands ops b0 = SOME args /\
  setup_callee ctf args b0 = SOME child_entry /\
  (!op. MEM op c.inst_operands ==> eval_operand op u = eval_operand op b0) /\
  (!callee argv.
    setup_callee callee argv (u with vs_gas_readings := b0.vs_gas_readings) =
      setup_callee callee argv b0) ==>
  ?csf. lookup_function nm C7.ctx_functions = SOME csf /\
    ctf = dft_fn csf /\ dft_fn_rel csf ctf /\
    eval_operands ops u = SOME args /\
    setup_callee csf args u =
      SOME (child_entry with vs_gas_readings := u.vs_gas_readings)
Proof
  rpt strip_tac >>
  drule_all dft_packet_paired_lookup >>
  disch_then (qspec_then `nm` mp_tac) >>
  Cases_on `lookup_function nm C7.ctx_functions` >> simp[] >>
  strip_tac >>
  `!op. MEM op ops ==> eval_operand op u = eval_operand op b0` by
    (gvs[decode_invoke_def, AllCaseEqs()] >> metis_tac[MEM]) >>
  `eval_operands ops u = eval_operands ops b0` by
    (qpat_x_assum `!op. MEM op ops ==> _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Induct_on `ops` >> simp[eval_operands_def] >>
     rpt strip_tac >> gvs[]) >>
  `setup_callee ctf args u =
      SOME (child_entry with vs_gas_readings := u.vs_gas_readings)` by
    (qpat_x_assum `!callee argv. _`
       (qspecl_then [`ctf`, `args`] mp_tac) >>
     simp[gas_setup_callee] >>
     Cases_on `setup_callee ctf args u` >> simp[] >> strip_tac >>
     drule gas_setup_callee_readings >>
     simp[venom_state_component_equality]) >>
  metis_tac[dft_packet_callee_setup_dft]
QED

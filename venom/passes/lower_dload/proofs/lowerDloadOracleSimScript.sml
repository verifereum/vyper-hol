(* TASK036: oracle projections of existing legacy LowerDload simulations.
 * These do NOT certify the configured supply transform, missing observables,
 * or O1 composition. Every original hypothesis and simulation is retained. *)
Theory lowerDloadOracleSim
Ancestors
  lowerDloadOracleFields lowerDloadProofs lowerDloadSim lowerDloadCorrectness
  lowerDloadDefs lowerDloadClassify venomExecSemantics venomState venomInst
  venomWf stateEquiv words list

Theorem lower_dload_single_inst_oracle:
  !h fuel ctx s1 s2 vars s1_mid.
    ld_ok vars s1 s2 /\
    code_layout_valid s1 /\ code_layout_valid s2 /\
    ~is_terminator h.inst_opcode /\
    h.inst_opcode <> INVOKE /\
    ~reads_memory h.inst_opcode /\
    inst_wf h /\
    (!x. MEM (Var x) h.inst_operands ==> x NOTIN vars) /\
    (!out. h.inst_opcode = ALLOCA /\ MEM out h.inst_outputs ==> out IN vars) /\
    (h.inst_opcode = DLOAD ==>
      ?v. h.inst_operands = [Lit v] /\
          w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
          ld_alloca_var h.inst_id IN vars /\
          ld_add_var h.inst_id IN vars) /\
    (h.inst_opcode = DLOADBYTES ==>
      ?dst_op v size_op. h.inst_operands = [dst_op; Lit v; size_op] /\
          w2n v + (LENGTH s1.vs_code - LENGTH s1.vs_data_section) < dimword(:256) /\
          ld_add_var h.inst_id IN vars) /\
    step_inst fuel ctx h s1 = OK s1_mid ==>
    ?s2_mid. run_insts fuel ctx (lower_dload_inst h) s2 = OK s2_mid /\
             ld_ok vars s1_mid s2_mid /\
             s1_mid.vs_outcomes = s2_mid.vs_outcomes /\
             s1_mid.vs_requests = s2_mid.vs_requests
Proof
  rpt gen_tac >> strip_tac >> drule_all ld_single_inst_step >>
  strip_tac >> qexists_tac `s2_mid` >> simp[] >>
  irule ld_ok_oracle >> qexists_tac `vars` >> simp[]
QED

Theorem lower_dload_function_oracle:
  !fuel ctx fn s.
    wf_function fn /\ fn_inst_wf fn /\ code_layout_valid s /\
    ld_no_mem_read fn /\ ld_dload_safe fn /\
    ld_no_original_alloca fn /\
    (!bb inst x.
       MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
       MEM (Var x) inst.inst_operands ==>
       x NOTIN ld_fresh_vars_fn fn) /\
    s.vs_inst_idx = 0 ==>
    lift_result
      (ld_ok (ld_exempt_vars_fn fn))
      (ld_equiv (ld_exempt_vars_fn fn)) (ld_equiv (ld_exempt_vars_fn fn))
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lower_dload_function fn) s) /\
    lift_result
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (lower_dload_function fn) s)
Proof
  rpt gen_tac >> strip_tac >> drule_all lower_dload_function_correct >>
  strip_tac >> ASM_REWRITE_TAC[] >> irule ld_lift_result_oracle >>
  qexists_tac `ld_exempt_vars_fn fn` >> simp[]
QED

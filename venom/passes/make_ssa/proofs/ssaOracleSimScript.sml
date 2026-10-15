(* TASK036: oracle projections of the existing SSA simulations.
 * All old premises, directional sigma scope, exit facts and fuel witnesses
 * are retained. Concrete CALL and GAS semantics are unchanged. *)
Theory ssaOracleSim
Ancestors
  ssaOracleFields ssaSimDefs ssaRenamedSim makeSsaHelper makeSsaCorrectness
  makeSsaDefs venomExecSemantics venomState venomInst venomWf stateEquiv
  list rich_list finite_map

Theorem ssa_renamed_inst_oracle:
  !sigma inst1 inst2 s1 s2 s1'.
    ssa_sim sigma s1 s2 /\
    inst_renamed sigma inst1 inst2 /\
    output_fresh sigma inst1 inst2 s1 /\
    ~is_terminator inst1.inst_opcode /\
    inst1.inst_opcode <> INVOKE /\
    inst1.inst_opcode <> PHI /\
    inst1.inst_opcode <> ASSIGN /\
    step_inst_base inst1 s1 = OK s1' ==>
    ?s2'. step_inst_base inst2 s2 = OK s2' /\
          ssa_sim (output_sigma inst1.inst_opcode
                     inst1.inst_outputs inst2.inst_outputs sigma) s1' s2' /\
          s1'.vs_outcomes = s2'.vs_outcomes /\
          s1'.vs_requests = s2'.vs_requests
Proof
  rpt gen_tac >> strip_tac >> drule_all step_inst_base_renamed_sim >>
  strip_tac >> qexists_tac `s2'` >> simp[] >> irule ssa_sim_oracle >>
  qexists_tac `output_sigma inst1.inst_opcode
    inst1.inst_outputs inst2.inst_outputs sigma` >> simp[]
QED

Theorem ssa_run_block_oracle:
  !fuel ctx bb bb' sigma sigma_out s1 s2 rs_mid.
    s1.vs_inst_idx = 0 /\ s2.vs_inst_idx = 0 /\
    EVERY (\inst. EVERY colon_free inst.inst_outputs) bb.bb_instructions /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ~opcode_has_output (EL j bb.bb_instructions).inst_opcode ==>
      (EL j bb.bb_instructions).inst_outputs = []) /\
    (!j. j < LENGTH bb.bb_instructions ==>
      ALL_DISTINCT (EL j bb.bb_instructions).inst_outputs) /\
    bb_well_formed bb /\
    EVERY inst_wf bb.bb_instructions /\
    (!e. run_block fuel ctx bb s1 <> Error e) /\
    phi_args_ok bb bb' sigma sigma_out s1 s2 rs_mid /\
    (!j x. j < LENGTH bb.bb_instructions /\
           MEM (Var x) (EL j bb.bb_instructions).inst_operands /\
           (!m. m < j ==> ~MEM x (EL m bb.bb_instructions).inst_outputs) ==>
           sigma_out x = latest_version rs_mid x) ==>
    ssa_result_equiv
      (run_block fuel ctx bb s1) (run_block fuel ctx bb' s2) /\
    (!v v'. run_block fuel ctx bb s1 = OK v /\
            run_block fuel ctx bb' s2 = OK v' ==>
      ?sigma_exit.
        ssa_sim sigma_exit v v' /\
        (!x. colon_free x ==> ?n. sigma_exit x = version_var x n) /\
        (!x. (!j. j < LENGTH bb.bb_instructions ==>
                  ~MEM x (EL j bb.bb_instructions).inst_outputs) ==>
             sigma_exit x = sigma_out x) /\
        (!x j. j < LENGTH bb.bb_instructions /\
               MEM x (EL j bb.bb_instructions).inst_outputs ==>
               sigma_exit x = latest_version
                 (FST (rename_block_insts rs_mid bb.bb_instructions)) x) /\
        vars_colon_free v) /\
    lift_result
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
      (run_block fuel ctx bb s1) (run_block fuel ctx bb' s2)
Proof
  rpt gen_tac >> strip_tac >> drule_all run_block_ssa_sim >> strip_tac >>
  ASM_REWRITE_TAC[] >> irule ssa_result_equiv_oracle >> first_assum ACCEPT_TAC
QED

Theorem make_ssa_pass_oracle:
  !dom_frontiers dtree dom_post_order pred_map succ_map live_in
   func s fuel ctx.
    wf_function func /\
    valid_dom_tree dom_frontiers dtree dom_post_order func /\
    valid_cfg_maps pred_map succ_map func /\
    valid_liveness live_in func /\
    fn_entry_no_preds func /\
    fn_inst_wf func /\
    valid_liveness_flow live_in func /\
    valid_liveness_uses live_in func /\
    s.vs_vars = FEMPTY /\
    s.vs_inst_idx = 0 /\
    s.vs_prev_bb = NONE /\
    fn_entry_label func = SOME s.vs_current_bb /\
    live_in_scope live_in s /\
    (!bb inst. MEM bb func.fn_blocks /\
              MEM inst bb.bb_instructions ==>
              inst.inst_opcode <> PHI /\
              EVERY colon_free inst.inst_outputs /\
              ALL_DISTINCT inst.inst_outputs /\
              (~opcode_has_output inst.inst_opcode ==>
               inst.inst_outputs = [])) ==>
    let func' = make_ssa_fn dom_frontiers dtree dom_post_order
                  pred_map succ_map live_in func in
    ?fresh fuel'.
      result_equiv fresh
        (run_blocks fuel ctx func s) (run_blocks fuel' ctx func' s) /\
      lift_result
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (\s1 s2. s1.vs_outcomes = s2.vs_outcomes /\ s1.vs_requests = s2.vs_requests)
        (run_blocks fuel ctx func s) (run_blocks fuel' ctx func' s)
Proof
  rpt gen_tac >> strip_tac >> simp_tac std_ss [LET_THM] >>
  drule_all make_ssa_pass_correct >>
  disch_then (qspecl_then [`fuel`, `ctx`] mp_tac) >>
  simp_tac std_ss [LET_THM] >> strip_tac >>
  qexistsl_tac [`fresh`, `fuel'`] >> ASM_REWRITE_TAC[] >>
  irule result_equiv_oracle >> qexists_tac `fresh` >> simp[]
QED

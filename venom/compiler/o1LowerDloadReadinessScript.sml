Theory o1LowerDloadReadiness
Ancestors
  unitMemInv contextRawReachable contextCodegenRel lowerDloadDefs
  venomWf venomInst venomExecSemantics list words

(* This is a raw-reachability boundary, not a projection from the occurrence
   relation. The latter's return rule needs a separate semantic bridge. *)
Theorem ld_reachable_headroom:
  mem_inv dload_headroom_ok C vs /\ raw_reachable vs C fn inst s ==>
  s.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  simp[mem_inv_raw_reachable, dload_headroom_ok_def] >> metis_tac[]
QED

Theorem ld_next_headroom:
  mem_inv dload_headroom_ok C vs /\ raw_reachable vs C fn inst s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s1 /\
  active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx) ==>
  s1.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >>
  `raw_reachable vs C fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    metis_tac[raw_reachable_next] >>
  drule_all ld_reachable_headroom >> simp[]
QED

(* Well-formed blocks cannot finish with ALLOCA (or any nonterminator).
   Keeping current-block preservation explicit makes this purely structural. *)
Theorem ld_nonterminator_successor:
  wf_function fn /\ active_inst fn inst s /\
  ~is_terminator inst.inst_opcode /\ s1.vs_current_bb = s.vs_current_bb ==>
  ?inst2. active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[active_inst_def] >> rpt strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `SUC s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[bb_well_formed_def] >>
     `s.vs_inst_idx <> PRE (LENGTH bb.bb_instructions)` by
       (strip_tac >> gvs[LAST_EL]) >> decide_tac) >>
  qexists_tac `bb` >> simp[]
QED

Theorem ld_alloca_successor_active:
  wf_function fn /\ active_inst fn inst s /\ inst.inst_opcode = ALLOCA /\
  step_inst fuel C inst s = OK s1 ==>
  ?inst2. active_inst fn inst2 (s1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  `s1.vs_current_bb = s.vs_current_bb` by
    gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, exec_alloca_def,
        AllCaseEqs(), venomStateTheory.update_var_def] >>
  irule ld_nonterminator_successor >> simp[] >>
  qexists_tac `inst` >> simp[is_terminator_def]
QED

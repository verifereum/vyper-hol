Theory makeSsaCurrentActualDefined
Ancestors venomExecSemantics venomState venomInst finite_map pred_set list

Theorem current_eval_phis_domain:
  !insts post. eval_phis st insts = OK post ==>
    FDOM st.vs_vars SUBSET FDOM post.vs_vars
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def, SUBSET_DEF] >> metis_tac[SUBSET_DEF]
QED

Theorem current_eval_phis_control:
  !insts post. eval_phis st insts = OK post ==>
    post.vs_current_bb = st.vs_current_bb /\
    post.vs_prev_bb = st.vs_prev_bb
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  simp[update_var_def]
QED

Theorem current_eval_phis_outputs:
  !insts post inst v.
    eval_phis st insts = OK post /\
    MEM inst (TAKE (phi_prefix_length insts) insts) /\
    MEM v inst.inst_outputs ==> v IN FDOM post.vs_vars
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  strip_tac >> gvs[AllCaseEqs()]
  >- (gvs[eval_one_phi_def, AllCaseEqs()] >> simp[update_var_def]) >>
  simp[update_var_def] >> metis_tac[]
QED

Theorem current_eval_phis_dispatch_domain:
  eval_phis st insts = OK post ==>
  FDOM st.vs_vars SUBSET
    FDOM (post with vs_inst_idx := phi_prefix_length insts).vs_vars /\
  (!inst v. MEM inst (TAKE (phi_prefix_length insts) insts) /\
    MEM v inst.inst_outputs ==>
    v IN FDOM (post with vs_inst_idx := phi_prefix_length insts).vs_vars) /\
  (post with vs_inst_idx := phi_prefix_length insts).vs_current_bb = st.vs_current_bb /\
  (post with vs_inst_idx := phi_prefix_length insts).vs_prev_bb = st.vs_prev_bb /\
  (post with vs_inst_idx := phi_prefix_length insts).vs_inst_idx = phi_prefix_length insts
Proof
  simp[] >> metis_tac[current_eval_phis_domain, current_eval_phis_outputs,
    current_eval_phis_control]
QED

Theorem current_eval_phis_empty_probe[local]:
  eval_phis st [] = OK st
Proof
  EVAL_TAC
QED

Theorem current_eval_phis_duplicate_probe[local]:
  a.inst_opcode = PHI /\ b.inst_opcode = PHI /\
  eval_one_phi st a = SOME (v,x) /\ eval_one_phi st b = SOME (v,y) ==>
  eval_phis st [a;b] = OK (update_var v x (update_var v y st)) /\
  v IN FDOM (update_var v x (update_var v y st)).vs_vars
Proof
  simp[eval_phis_def, update_var_def]
QED

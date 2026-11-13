Theory concretizePtrRevertHistory
Ancestors concretizePtrLifetime concretizePtrChronologicalHistory
  contextCodegenRel venomExecSemantics venomState venomInst venomWf
  venomInstProps venomExecProofs ptrDiscipline o1PassContract list arithmetic

Theorem ptr_revert_active_lookup[local]:
  ALL_DISTINCT (fn_labels fn) /\ active_inst fn inst s ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       get_instruction bb s.vs_inst_idx = SOME inst
Proof
  rw[active_inst_def, fn_labels_def] >> qexists `bb` >>
  simp[get_instruction_def] >> irule MEM_lookup_block >> simp[]
QED

Theorem ptr_revert_no_successor[local]:
  ptr_chrono_step ctx a b ==> a.po_inst.inst_opcode <> REVERT
Proof
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def, is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_def, AllCaseEqs()]
QED

Theorem ptr_revert_step_fields[local]:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY) /\
  step_inst fuel ctx inst s = OK s' ==>
  s'.vs_current_bb = s.vs_current_bb /\ s'.vs_inst_idx = s.vs_inst_idx
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  drule step_inst_non_invoke >>
  disch_then (qspecl_then [`fuel`,`ctx`,`s`] assume_tac) >> fs[] >>
  qpat_x_assum `step_inst fuel ctx inst s = _` kall_tac >>
  gvs[step_inst_base_def, AllCaseEqs()] >>
  simp[update_var_def, write_memory_with_expansion_def, write_memory_def]
QED

Theorem ptr_revert_step_no_intret[local]:
  (inst.inst_opcode = ASSIGN \/ inst.inst_opcode = RETURNDATACOPY) ==>
  step_inst_base inst s <> IntRet ret t
Proof
  strip_tac >> simp[step_inst_base_def] >>
  simp[AllCaseEqs()]
QED

Theorem ptr_revert_chrono_fields[local]:
  ptr_chrono_step ctx a b /\
  (a.po_inst.inst_opcode = ASSIGN \/ a.po_inst.inst_opcode = RETURNDATACOPY) ==>
  b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
  b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
  b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx
Proof
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def, is_terminator_def] >>
  imp_res_tac ptr_revert_step_fields >> gvs[] >>
  `rinst.inst_opcode <> INVOKE` by gvs[] >>
  drule step_inst_non_invoke >>
  disch_then (qspecl_then [`fuel`,`ctx`,`s`] assume_tac) >>
  metis_tac[ptr_revert_step_no_intret]
QED

Theorem ptr_revert_chrono_active[local]:
  ptr_chrono_step ctx a b ==>
  active_inst a.po_fn a.po_inst a.po_state /\
  active_inst b.po_fn b.po_inst b.po_state
Proof
  simp[Once ptr_chrono_step_cases] >> rpt strip_tac >>
  gvs[ptr_observe_def]
QED

Theorem ptr_revert_interval_step[local]:
  ptr_chrono_step ctx a b /\ ALL_DISTINCT (fn_labels a.po_fn) /\
  lookup_block a.po_state.vs_current_bb a.po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb p q /\
  p <= a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx <= q ==>
  b.po_fn = a.po_fn /\
  b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
  p < b.po_state.vs_inst_idx /\ b.po_state.vs_inst_idx <= q
Proof
  strip_tac >>
  drule ptr_revert_chrono_active >> strip_tac >>
  drule_all ptr_revert_active_lookup >> strip_tac >> gvs[] >>
  `a.po_state.vs_inst_idx <> q` by
    (strip_tac >> gvs[revert_forward_pair_def] >>
     metis_tac[ptr_revert_no_successor]) >>
  `a.po_inst.inst_opcode = ASSIGN \/
   a.po_inst.inst_opcode = RETURNDATACOPY` by
    (Cases_on `a.po_state.vs_inst_idx = p` >>
     gvs[revert_forward_pair_def] >>
     `p < a.po_state.vs_inst_idx /\ a.po_state.vs_inst_idx < q` by decide_tac >>
     metis_tac[]) >>
  `b.po_fn = a.po_fn /\ b.po_stack = a.po_stack /\
   b.po_state.vs_current_bb = a.po_state.vs_current_bb /\
   b.po_state.vs_inst_idx = SUC a.po_state.vs_inst_idx` by
    metis_tac[ptr_revert_chrono_fields] >> simp[]
QED

Theorem ptr_revert_history_interval[local]:
  !d. ptr_chrono_history vs0 ctx h endpoint /\
  ALL_DISTINCT (fn_labels (EL i h).po_fn) /\
  lookup_block (EL i h).po_state.vs_current_bb (EL i h).po_fn.fn_blocks = SOME bb /\
  revert_forward_pair bb p q /\
  p <= (EL i h).po_state.vs_inst_idx /\ (EL i h).po_state.vs_inst_idx <= q /\
  i + d < LENGTH h ==>
  (EL (i+d) h).po_fn = (EL i h).po_fn /\
  (EL (i+d) h).po_state.vs_current_bb = (EL i h).po_state.vs_current_bb /\
  p <= (EL (i+d) h).po_state.vs_inst_idx /\
  (EL (i+d) h).po_state.vs_inst_idx <= q /\
  (0 < d ==> p < (EL (i+d) h).po_state.vs_inst_idx)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `i + d < LENGTH h` by decide_tac >>
  first_x_assum drule_all >> strip_tac >>
  `ptr_chrono_step ctx (EL (i+d) h) (EL (SUC (i+d)) h)` by
    metis_tac[ptr_chrono_history_adjacent, ADD_CLAUSES] >>
  drule ptr_revert_interval_step >> simp[] >>
  disch_then (qspecl_then [`q`,`p`] mp_tac) >> gvs[ADD_CLAUSES]
QED

Theorem ptr_revert_history_active[local]:
  ptr_chrono_history vs0 ctx h endpoint /\ k < LENGTH h ==>
  active_inst (EL k h).po_fn (EL k h).po_inst (EL k h).po_state
Proof
  strip_tac >> drule ptr_chrono_history_reachable >>
  simp[EVERY_EL, ptr_observation_reachable_def] >> strip_tac >>
  first_x_assum drule >>
  qid_spec_tac `k` >>
  `!vs0 ctx stk PG G tn fn inst s.
    frame_reachable vs0 ctx stk PG G tn fn inst s ==> active_inst fn inst s` by
    (ho_match_mp_tac frame_reachable_ind >> simp[]) >>
  metis_tac[]
QED

Theorem ptr_chrono_revert_suffix:
  ptr_chrono_history vs0 ctx h endpoint /\ i < j /\ j < LENGTH h /\
  ALL_DISTINCT (fn_labels (EL i h).po_fn) /\
  in_revert_forward (EL i h).po_fn (EL i h).po_state ==>
  (EL j h).po_inst.inst_opcode = ASSIGN \/
  ((EL j h).po_inst.inst_opcode = REVERT /\
   in_revert_forward (EL j h).po_fn (EL j h).po_state)
Proof
  strip_tac >>
  `?bb p q. lookup_block (EL i h).po_state.vs_current_bb
                    (EL i h).po_fn.fn_blocks = SOME bb /\
    revert_forward_pair bb p q /\
    p <= (EL i h).po_state.vs_inst_idx /\
    (EL i h).po_state.vs_inst_idx <= q` by
    (gvs[in_revert_forward_def, revert_forward_at_def] >>
     metis_tac[revert_forward_pair_def, LESS_OR_EQ]) >>
  `i + (j-i) = j /\ 0 < j-i` by decide_tac >>
  drule ptr_revert_history_interval >> ntac 5 (disch_then drule) >>
  disch_then (qspec_then `j-i` mp_tac) >> simp[] >> strip_tac >>
  `active_inst (EL j h).po_fn (EL j h).po_inst (EL j h).po_state` by
    metis_tac[ptr_revert_history_active] >>
  `ALL_DISTINCT (fn_labels (EL j h).po_fn)` by metis_tac[] >>
  drule_all ptr_revert_active_lookup >> strip_tac >> gvs[] >>
  Cases_on `(EL j h).po_state.vs_inst_idx = q`
  >- (`in_revert_forward (EL j h).po_fn (EL j h).po_state` by
        metis_tac[in_revert_forward_def, revert_forward_at_def] >>
      gvs[revert_forward_pair_def]) >>
  disj1_tac >> gvs[revert_forward_pair_def] >>
  `(EL j h).po_state.vs_inst_idx < q` by decide_tac >> metis_tac[]
QED

Theorem ptr_revert_lookup_labels[local]:
  o1_ctx_shape ctx /\ lookup_function nm ctx.ctx_functions = SOME fn ==>
  ALL_DISTINCT (fn_labels fn)
Proof
  rw[o1_ctx_shape_def, EVERY_MEM, o1_fn_shape_def, wf_function_def] >>
  metis_tac[lookup_function_MEM]
QED

Theorem ptr_revert_frame_labels[local]:
  !vs0 ctx stk PG G tn fn inst s.
  frame_reachable vs0 ctx stk PG G tn fn inst s ==>
  o1_ctx_shape ctx ==>
  ALL_DISTINCT (fn_labels fn) /\
  EVERY (\f. ALL_DISTINCT (fn_labels f.cf_fn)) stk
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt strip_tac >>
  gvs[] >> metis_tac[ptr_revert_lookup_labels]
QED

Theorem ptr_chrono_history_labels:
  o1_ctx_shape ctx /\ ptr_chrono_history vs0 ctx h endpoint ==>
  EVERY (\obs. ALL_DISTINCT (fn_labels obs.po_fn)) h
Proof
  strip_tac >> drule ptr_chrono_history_reachable >>
  simp[EVERY_MEM, ptr_observation_reachable_def] >>
  metis_tac[ptr_revert_frame_labels]
QED

Theorem ptr_chrono_ordinary_non_revert:
  o1_ctx_shape ctx /\ ptr_chrono_history vs0 ctx h endpoint /\
  ~in_revert_forward endpoint.po_fn endpoint.po_state /\
  endpoint.po_inst.inst_opcode <> ASSIGN ==>
  EVERY (\obs. ~in_revert_forward obs.po_fn obs.po_state) h
Proof
  strip_tac >>
  drule_all ptr_chrono_history_labels >> simp[EVERY_EL] >> strip_tac >>
  drule ptr_chrono_history_end >> strip_tac >>
  `LENGTH h <> 0` by metis_tac[LENGTH_NIL] >>
  `EL (LENGTH h - 1) h = endpoint` by
    (`PRE (LENGTH h) = LENGTH h - 1` by decide_tac >> gvs[LAST_EL]) >>
  simp[EVERY_EL] >> rpt strip_tac >>
  Cases_on `n = LENGTH h - 1`
  >- gvs[] >>
  `n < LENGTH h - 1 /\ LENGTH h - 1 < LENGTH h` by decide_tac >>
  metis_tac[ptr_chrono_revert_suffix]
QED

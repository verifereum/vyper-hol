Theory gasFocusConcretizeGhostCutControl
Ancestors
  concretizePtrDallocaRuntimeControl concretizePtrDallocaRuntimeBlockHistory
  concretizePtrPairedPrefix concretizePtrPairedFields concretizePtrStructuralTranscript
  concretizePtrStructuralTrace concretizePtrChronologicalHistory
  concretizePtrHistoricalWriteExclusion concretizePtrSourceOwnership
  concretizePtrOperationalOpcodes
  concretizeStepShape concretizeStepStructure concretizePtrDallocaGhostInterface
  callLayoutDefs o1PassLift o1PassContract venomWf venomExecProofs
  venomExecSemantics venomInst finite_map list rich_list option

Theorem cut_call_entry_shapes[local]:
  o1_ctx_shape C /\
  LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
  (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name) ==>
  (!name fn. lookup_function name C.ctx_functions = SOME fn ==>
     first_block_no_phi fn) /\
  (!name fn. lookup_function name Ct.ctx_functions = SOME fn ==>
     first_block_no_phi fn)
Proof
  strip_tac >>
  `!fn. MEM fn C.ctx_functions ==>
     wf_function fn /\ first_block_no_preds fn /\ first_block_no_phi fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac >- metis_tac[lookup_function_MEM] >>
  drule_all list_rel_lookup_function >> disch_tac >> rpt strip_tac >>
  first_x_assum (qspec_then `name` mp_tac) >>
  Cases_on `lookup_function name C.ctx_functions` >> simp[] >> strip_tac >>
  rename1 `lookup_function name C.ctx_functions = SOME source` >>
  `MEM source C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `first_block_no_phi (concretize_function_with_positions (lp source) source)` by
    (irule (cj 2 concretize_positions_first_block) >> metis_tac[]) >>
  fs[ptr_paired_code_def, first_block_no_phi_def]
QED

Theorem cut_departed_invoke_inst[local]:
  ptr_paired_prefix R lp positions lo vs C Ct
    h endpoint ht endpoint_t done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n = EL q done /\
  a = EL n h /\ at = EL q ht /\ a.po_inst.inst_opcode = INVOKE ==>
  at.po_inst = a.po_inst
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule ptr_paired_prefix_samples >> strip_tac >>
  `q < LENGTH ht /\ n < LENGTH h` by
    fs[ptr_paired_samples_def, ptr_sample_list_def, EVERY_EL] >>
  drule ptr_paired_prefix_transcript >> strip_tac >>
  drule ptr_structural_transcript_erasure >> strip_tac >>
  `ptr_observation_reachable vs C a` by
    (drule ptr_structural_trace_source >>
     disch_then (mp_tac o MATCH_MP ptr_chrono_history_reachable) >>
     simp[EVERY_EL]) >>
  `MEM a.po_fn C.ctx_functions` by
    (fs[ptr_observation_reachable_def] >>
     drule ptr_frame_context_membership >> simp[]) >>
  `fn_inst_ids_distinct a.po_fn` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def, EVERY_MEM] >> metis_tac[]) >>
  `ptr_paired_cursor lp a at` by
    (drule_all (Q.INST [`j` |-> `q`] ptr_paired_prefix_alignment) >>
     fs[EL_APPEND_EQN]) >>
  `a.po_inst.inst_id = at.po_inst.inst_id` by
    (drule ptr_trace_departed_inst_ids >>
     disch_then (qspec_then `q` mp_tac) >> simp[]) >>
  drule_all ptr_departed_cursor_instruction >>
  simp[concretize_positions_unchanged]
QED

Theorem cut_tagged_return_has_caller[local]:
  ptr_tagged_chrono_step C token a b PT TG saved PT' TG' saved' /\
  is_raw_return_opcode a.po_inst.inst_opcode ==>
  a.po_stack <> []
Proof
  simp[Once ptr_tagged_chrono_step_cases, ptr_observe_def,
       ptr_observation_component_equality, is_raw_return_opcode_def] >>
  strip_tac >> gvs[ptr_observation_component_equality] >>
  fs[is_terminator_def] >>
  `is_terminator a.po_inst.inst_opcode` by simp[is_terminator_def] >>
  drule_all step_inst_ok_terminator_jump >> simp[]
QED

(* Only the matched control edge is transported. The persistent masks and
   effects are handled by the history fold, not by the saved-frame relation. *)
Theorem focus_cut_ghost_runtime_control:
  ptr_paired_prefix R lp positions lo vs C Ct
    h endpoint ht endpoint_t done tokens registry births PT TG saved entries H calls ws /\
  o1_ctx_shape C /\ q < LENGTH done /\ n = EL q done /\
  a = EL n h /\ at = EL q ht /\ b = EL (SUC n) h /\ bt = EL (SUC q) ht /\
  EL n H = (tsj,rj,bj,PTj,TGj,sj,ej) /\
  ptr_tagged_chrono_step C (HD tsj) a b PTj TGj sj PTj' TGj' sj' /\
  ptr_chrono_step Ct at bt /\
  (a.po_inst.inst_opcode = JMP \/ a.po_inst.inst_opcode = JNZ \/
   a.po_inst.inst_opcode = DJMP \/ a.po_inst.inst_opcode = INVOKE \/
   is_raw_return_opcode a.po_inst.inst_opcode) /\
  (a.po_inst.inst_opcode = INVOKE ==>
    LIST_REL (ptr_paired_code R lp positions) C.ctx_functions Ct.ctx_functions /\
    (!f g. ptr_paired_code R lp positions f g ==> g.fn_name = f.fn_name)) /\
  ptr_dalloca_ghost_vars a.po_prov a.po_taint.t_var a.po_state
    at.po_prov at.po_taint.t_var at.po_state /\
  (!v site. FLOOKUP at.po_prov v = SOME site ==> FLOOKUP TGj v = NONE) /\
  (!v site. FLOOKUP TGj v = NONE /\ FLOOKUP a.po_prov v = SOME site ==>
    FLOOKUP at.po_prov v = SOME site) /\
  LENGTH PTj = LENGTH a.po_params /\ LENGTH a.po_params = LENGTH at.po_params /\
  (!k site. k < LENGTH a.po_params ==>
    (EL k at.po_params = SOME site ==>
      EL k a.po_params = SOME site /\ EL k PTj = NONE /\
      EL k a.po_state.vs_params = EL k at.po_state.vs_params) /\
    (EL k PTj = NONE /\ EL k a.po_params = SOME site ==>
      EL k at.po_params = SOME site)) /\
  LENGTH sj = LENGTH a.po_stack /\
  LIST_REL (\((pt,tg),f) ft.
    ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
      ft.cf_prov ft.cf_tvar ft.cf_state /\
    (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
    (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
      FLOOKUP ft.cf_prov v = SOME site) /\
    f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
    LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
    (!k site. k < LENGTH f.cf_params ==>
      (EL k ft.cf_params = SOME site ==>
        EL k f.cf_params = SOME site /\ EL k pt = NONE /\
        EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
      (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
        EL k ft.cf_params = SOME site)))
    (ZIP (sj,a.po_stack)) at.po_stack ==>
  ptr_dalloca_ghost_vars b.po_prov b.po_taint.t_var b.po_state
    bt.po_prov bt.po_taint.t_var bt.po_state /\
  (!v site. FLOOKUP bt.po_prov v = SOME site ==> FLOOKUP TGj' v = NONE) /\
  (!v site. FLOOKUP TGj' v = NONE /\ FLOOKUP b.po_prov v = SOME site ==>
    FLOOKUP bt.po_prov v = SOME site) /\
  LENGTH PTj' = LENGTH b.po_params /\ LENGTH b.po_params = LENGTH bt.po_params /\
  (!k site. k < LENGTH b.po_params ==>
    (EL k bt.po_params = SOME site ==>
      EL k b.po_params = SOME site /\ EL k PTj' = NONE /\
      EL k b.po_state.vs_params = EL k bt.po_state.vs_params) /\
    (EL k PTj' = NONE /\ EL k b.po_params = SOME site ==>
      EL k bt.po_params = SOME site)) /\
  LENGTH sj' = LENGTH b.po_stack /\
  LIST_REL (\((pt,tg),f) ft.
    ptr_dalloca_ghost_vars f.cf_prov f.cf_tvar f.cf_state
      ft.cf_prov ft.cf_tvar ft.cf_state /\
    (!v site. FLOOKUP ft.cf_prov v = SOME site ==> FLOOKUP tg v = NONE) /\
    (!v site. FLOOKUP tg v = NONE /\ FLOOKUP f.cf_prov v = SOME site ==>
      FLOOKUP ft.cf_prov v = SOME site) /\
    f.cf_inst.inst_outputs = ft.cf_inst.inst_outputs /\
    LENGTH pt = LENGTH f.cf_params /\ LENGTH f.cf_params = LENGTH ft.cf_params /\
    (!k site. k < LENGTH f.cf_params ==>
      (EL k ft.cf_params = SOME site ==>
        EL k f.cf_params = SOME site /\ EL k pt = NONE /\
        EL k f.cf_state.vs_params = EL k ft.cf_state.vs_params) /\
      (EL k pt = NONE /\ EL k f.cf_params = SOME site ==>
        EL k ft.cf_params = SOME site)))
    (ZIP (sj',b.po_stack)) bt.po_stack
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `a.po_inst.inst_opcode = INVOKE` >- suspend "call" >>
  Cases_on `is_raw_return_opcode a.po_inst.inst_opcode` >- suspend "return" >>
  suspend "jump"
QED

Resume focus_cut_ghost_runtime_control[call]:
  `at.po_inst = a.po_inst` by (irule cut_departed_invoke_inst >> metis_tac[]) >>
  qpat_x_assum `a.po_inst.inst_opcode = INVOKE ==> _` (drule_then strip_assume_tac) >>
  drule_all cut_call_entry_shapes >> strip_tac >>
  drule_all ptr_dalloca_runtime_chrono_call >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  map_every (fn p => qpat_x_assum p kall_tac)
    [`a = EL n h`, `at = EL q ht`, `b = EL (SUC n) h`, `bt = EL (SUC q) ht`] >>
  simp[]
QED

Resume focus_cut_ghost_runtime_control[return]:
  drule_all cut_tagged_return_has_caller >> strip_tac >>
  namedCases_on `a.po_stack` ["", "f stk"] >- fs[] >>
  namedCases_on `sj` ["", "ptg tail"] >- fs[] >>
  namedCases_on `ptg` ["rptg rtg"] >>
  namedCases_on `at.po_stack` ["", "ft stkt"] >- fs[] >>
  qpat_x_assum `LIST_REL _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [ZIP]) >>
  drule_all (REWRITE_RULE[] (Q.INST [`sj` |-> `(RPT,RTG)::tail`]
    ptr_dalloca_historical_runtime_ret)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  map_every (fn p => qpat_x_assum p kall_tac)
    [`a = EL n h`, `at = EL q ht`, `b = EL (SUC n) h`, `bt = EL (SUC q) ht`] >>
  fs[]
QED

Resume focus_cut_ghost_runtime_control[jump]:
  Q.SUBGOAL_THEN `a.po_inst.inst_opcode = JMP \/ a.po_inst.inst_opcode = JNZ \/
    a.po_inst.inst_opcode = DJMP` assume_tac >- metis_tac[] >>
  map_every (fn p => qpat_x_assum p SUBST_ALL_TAC)
    [`a = EL n h`, `at = EL q ht`, `b = EL (SUC n) h`, `bt = EL (SUC q) ht`] >>
  drule_all ptr_dalloca_historical_runtime_block >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `n = EL q done` SUBST_ALL_TAC >> simp[]
QED

Finalise focus_cut_ghost_runtime_control

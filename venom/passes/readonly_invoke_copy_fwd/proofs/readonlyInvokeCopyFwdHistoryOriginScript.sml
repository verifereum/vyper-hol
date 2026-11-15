(* Located validation is paired with original-source execution, never with
   an assertion that the original block itself accepted the event. *)
Theory readonlyInvokeCopyFwdHistoryOrigin
Ancestors
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdProtectionOrigin
  readonlyInvokeCopyFwdTraceOrigin readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdOccurrenceAlias venomWf venomWfProps list
  ptrDiscipline venomExecSemantics

Definition ricf_history_origin_def:
  ricf_history_origin vs C ctx0 log p stk PG G tn <=>
    ?round b es prefix current dr sr szop.
      ricf_located_event ctx0 p.rpe_fn log round b es prefix p.rpe_event current /\
      p.rpe_block = EL b p.rpe_fn.fn_blocks /\
      ricf_event_copy p.rpe_event current =
        ricf_event_copy p.rpe_event p.rpe_block /\
      ricf_event_roots p.rpe_event current = SOME (dr,sr,szop) /\
      ricf_source_copy_payload vs C p stk PG G tn
        (ricf_event_copy p.rpe_event p.rpe_block) dr sr szop
End

Definition ricf_history_cursor_def:
  ricf_history_cursor vs C ctx0 log p pre PG G tn fn s <=>
    ?stk RPG RG RT.
      ricf_history_origin vs C ctx0 log p stk RPG RG RT /\
      ricf_visit_prefix C p.rpe_fn RPG
        (step_prov RPG RG (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
        (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
          p.rpe_before p.rpe_after RT)
        (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
        pre PG G tn fn s
End

Theorem ricf_located_event_actual_origin:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK t ==>
  ?p. p.rpe_event = e /\ p.rpe_block = EL b fn.fn_blocks /\ p.rpe_fn = fn /\
    p.rpe_before = s /\ p.rpe_after = t /\ p.rpe_owner = a /\
    ricf_history_origin vs C ctx0 log p stk PG G tn
Proof
  strip_tac >>
  drule occurrence_alias_reachable >> simp[] >> strip_tac >>
  `ssa_form fn` by fs[wf_ssa_def] >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  `MEM (EL b fn.fn_blocks) fn.fn_blocks` by simp[EL_MEM] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  drule_all ricf_later_round_alloca_witnesses >> strip_tac >>
  drule_all ricf_actual_source_copy_payload >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  simp[ricf_history_origin_def] >> metis_tac[]
QED

Theorem ricf_history_cursor_activate:
  ricf_history_origin vs C ctx0 log p stk PG G tn ==>
  ricf_history_cursor vs C ctx0 log p [] PG
    (step_prov PG G (ricf_event_copy p.rpe_event p.rpe_block) p.rpe_after)
    (step_taint (ricf_event_copy p.rpe_event p.rpe_block)
      p.rpe_before p.rpe_after tn) p.rpe_fn
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx)
Proof
  simp[ricf_history_cursor_def] >> metis_tac[ricf_visit_prefix_start]
QED

Theorem ricf_history_cursor_next:
  ricf_history_cursor vs C ctx0 log p pre PG G tn fn s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' ==>
  ricf_history_cursor vs C ctx0 log p pre PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[ricf_history_cursor_def] >> metis_tac[ricf_visit_prefix_next]
QED

Theorem ricf_history_cursor_call:
  ricf_history_cursor vs C ctx0 log p pre PG G tn caller s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 ==>
  ricf_history_cursor vs C ctx0 log p
    (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
Proof
  simp[ricf_history_cursor_def] >> metis_tac[ricf_visit_prefix_call]
QED

Theorem ricf_history_cursor_return:
  ricf_history_cursor vs C ctx0 log p (f::pre) PG G tn fn s /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' ==>
  ricf_history_cursor vs C ctx0 log p pre f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  simp[ricf_history_cursor_def] >> metis_tac[ricf_visit_prefix_ret]
QED

Theorem ricf_history_cursor_no_reentry:
  ricf_history_cursor vs C ctx0 log p [] PG G tn fn s ==>
  s.vs_current_bb =
    (p.rpe_after with vs_inst_idx := SUC p.rpe_before.vs_inst_idx).vs_current_bb /\
  SUC p.rpe_before.vs_inst_idx <= s.vs_inst_idx
Proof
  simp[ricf_history_cursor_def] >> rpt strip_tac >>
  drule ricf_visit_prefix_owner_location >> simp[ricf_visit_owner_state_def]
QED

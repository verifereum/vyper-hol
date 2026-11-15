(* Alignment is retained as witness data, never inferred from two independent
   existential histories.  The indexed interface exposes the scope being popped. *)
Theory readonlyInvokeCopyFwdAlignedOrigins
Ancestors
  readonlyInvokeCopyFwdOperationalMapOrigins
  readonlyInvokeCopyFwdHistoryInheritedLifecycle
  readonlyInvokeCopyFwdOperationalSupport readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryOrigin readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdReadonlyReach readonlyInvokeCopyFwdHistoryClosure
  readonlyInvokeCopyFwdHistoryStackAlignment
  ptrDiscipline venomExecSemantics finite_map list pred_set

Definition ricf_aligned_origin_at_def:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn inst s U B key triple
    p pre anchor tail atn <=>
    triple = (p.rpe_db,p.rpe_sb,p.rpe_size) /\
    key = (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
    stk = pre ++ anchor::tail /\ LENGTH pre < LENGTH U /\
    (EL (LENGTH pre) U).of_owner = p.rpe_owner /\
    FST p.rpe_dst = p.rpe_owner /\ FST p.rpe_src = p.rpe_owner /\
    anchor.cf_state.vs_current_bb = p.rpe_block.bb_label /\
    ricf_selected_position p.rpe_event p.rpe_block anchor.cf_state.vs_inst_idx /\
    anchor.cf_inst.inst_opcode = INVOKE /\
    anchor.cf_inst = EL anchor.cf_state.vs_inst_idx p.rpe_block.bb_instructions /\
    atn.t_var = anchor.cf_tvar /\
    ricf_history_cursor vs C ctx0 log p [] anchor.cf_params anchor.cf_prov
      atn anchor.cf_fn anchor.cf_state /\
    readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
      anchor tail (SND p.rpe_dst) p.rpe_db p.rpe_size pre PG G tn fn inst s /\
    readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
      anchor tail (SND p.rpe_src) p.rpe_sb p.rpe_size pre PG G tn fn inst s /\
    ricf_history_cursor vs C ctx0 log p (pre ++ [anchor]) PG G tn fn s
End

Definition ricf_aligned_translation_origin_def:
  ricf_aligned_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr <=>
    ?p pre anchor tail atn.
      ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn inst s U B key tr
        p pre anchor tail atn
End

Theorem ricf_aligned_origin_projection:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn inst s U B key tr
    p pre anchor tail atn ==>
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr
Proof
  rw[ricf_aligned_origin_at_def, ricf_translation_origin_def] >>
  qexistsl_tac [`p`, `pre`, `anchor`, `tail`, `atn`] >>
  simp[ricf_history_inherited_def] >> metis_tac[]
QED

Theorem ricf_aligned_translation_origin_projection:
  ricf_aligned_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr ==>
  ricf_translation_origin vs C ctx0 log stk PG G tn fn inst s U B key tr
Proof
  rw[ricf_aligned_translation_origin_def] >>
  metis_tac[ricf_aligned_origin_projection]
QED

Theorem ricf_aligned_origin_selected:
  ricf_history_cursor vs C ctx0 log p [] PG G tn caller s /\
  frame_reachable vs C stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  FLOOKUP s.vs_allocas (SND p.rpe_dst) = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP s.vs_allocas (SND p.rpe_src) = SOME (p.rpe_sb,p.rpe_size) /\
  0 < p.rpe_size /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
       ==> rma_is_readonly ctx0.icf_rma nm k) /\
  FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
  FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size) /\
  a = p.rpe_owner /\ s.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx /\
  callinst = EL s.vs_inst_idx p.rpe_block.bb_instructions ==>
  ricf_aligned_origin_at vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
    p [] (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>) stk tn
Proof
  strip_tac >> drule ricf_history_cursor_endpoint_owners >> strip_tac >>
  rw[ricf_aligned_origin_at_def] >>
  metis_tac[readonly_call_reachable_start, ricf_history_cursor_call]
QED

Theorem ricf_aligned_origin_next:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn inst s U B key tr
    p pre anchor tail atn /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_aligned_origin_at vs C ctx0 log stk PG
    (step_prov PG G inst s') (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx) U B key tr p pre anchor tail atn
Proof
  rw[ricf_aligned_origin_at_def] >>
  metis_tac[readonly_call_reachable_next, ricf_history_cursor_next]
QED

Theorem ricf_aligned_origin_block:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn inst s U B key tr
    p pre anchor tail atn /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
  ricf_aligned_origin_at vs C ctx0 log stk PG
    (entry_prov fn s' G) (entry_taint_vars fn s' tn) fn inst' s1
    U B key tr p pre anchor tail atn
Proof
  rw[ricf_aligned_origin_at_def]
  >- metis_tac[readonly_call_reachable_block]
  >- metis_tac[readonly_call_reachable_block] >>
  fs[ricf_history_cursor_def] >>
  Cases_on `pre` >> gvs[] >> metis_tac[ricf_visit_prefix_block]
QED

Theorem ricf_aligned_origin_call:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn caller callinst s U B key tr
    p pre anchor tail atn /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_aligned_origin_at vs C ctx0 log
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (u::U) B key tr p
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre) anchor tail atn
Proof
  rw[ricf_aligned_origin_at_def] >>
  metis_tac[readonly_call_reachable_call, ricf_history_cursor_call]
QED

Theorem ricf_aligned_origin_nested_return:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn rinst s (u::U) B key tr
    p (f::pre) anchor tail atn /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_aligned_origin_at vs C ctx0 log (pre ++ anchor::tail) f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    U B key tr p pre anchor tail atn
Proof
  rw[ricf_aligned_origin_at_def] >>
  metis_tac[readonly_call_reachable_ret, ricf_history_cursor_return]
QED

(* Scope exhaustion: only the advanced source cursor is returned.  There is
   deliberately no conclusion that the popped translation remains installed. *)
Theorem ricf_aligned_origin_matching_return:
  ricf_aligned_origin_at vs C ctx0 log stk PG G tn fn rinst s U B key tr
    p [] anchor tail atn /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs anchor.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state anchor.cf_state se)) = SOME s' ==>
  ricf_history_cursor vs C ctx0 log p [] anchor.cf_params
    (DRESTRICT anchor.cf_prov (COMPL (set anchor.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT anchor.cf_tvar (COMPL (set anchor.cf_inst.inst_outputs)))
    anchor.cf_fn (s' with vs_inst_idx := SUC anchor.cf_state.vs_inst_idx)
Proof
  pure_rewrite_tac[ricf_aligned_origin_at_def] >> strip_tac >>
  irule ricf_history_cursor_return >> metis_tac[APPEND]
QED

(* A concrete two-level execution test of the interface.  The initial witness
   is produced by ricf_aligned_origin_selected (and may have advanced through
   ordinary next/block transitions).  Neither exit cursor is a premise. *)
Theorem ricf_aligned_origin_nested_roundtrip:
  ricf_aligned_origin_at vs C ctx0 log (anchor::tail) PG G tn caller callinst s
    U B key tr p [] anchor tail atn /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs se /\ active_inst callee rinst se /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> /\
  step_inst fuel C rinst se = IntRet ret sr /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state sr)) = SOME sb /\
  active_inst caller exit (sb with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst fuel' C exit (sb with vs_inst_idx := SUC s.vs_inst_idx) = IntRet ret' sr' /\
  bind_outputs anchor.cf_inst.inst_outputs ret'.iret_values
    (adopt_return_fmp ret' (merge_callee_state anchor.cf_state sr')) = SOME done ==>
  ricf_history_cursor vs C ctx0 log p [] anchor.cf_params
    (DRESTRICT anchor.cf_prov (COMPL (set anchor.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT anchor.cf_tvar (COMPL (set anchor.cf_inst.inst_outputs)))
    anchor.cf_fn (done with vs_inst_idx := SUC anchor.cf_state.vs_inst_idx)
Proof
  strip_tac >>
  `ricf_aligned_origin_at vs C ctx0 log (f::anchor::tail)
     (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee rinst se
     (u::U) B key tr p [f] anchor tail atn` by
    (gvs[] >> irule ricf_aligned_origin_call >> metis_tac[]) >>
  gvs[] >>
  drule ricf_aligned_origin_nested_return >> simp[] >>
  disch_then drule >> simp[] >>
  disch_then drule >> simp[] >>
  strip_tac >>
  drule ricf_aligned_origin_matching_return >> simp[] >>
  metis_tac[]
QED

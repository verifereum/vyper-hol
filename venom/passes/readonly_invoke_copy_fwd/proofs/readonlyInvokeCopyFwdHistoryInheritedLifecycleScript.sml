(* Source-only transport within a paired readonly activation.  The saved
   history cursor remains at the common anchor; no relational bytes or
   translation-map lifetime conclusions are asserted here. *)
Theory readonlyInvokeCopyFwdHistoryInheritedLifecycle
Ancestors
  readonlyInvokeCopyFwdHistorySelected readonlyInvokeCopyFwdReadonlyReach
  list finite_map pred_set

(* This rule also covers ALLOCA: its provenance and taint updates are exactly
   those of readonly_call_reachable_next. *)
Theorem ricf_history_inherited_next:
  ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_history_inherited vs C ctx0 log p stk PG
    (step_prov PG G inst s') (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  simp[ricf_history_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_next >> metis_tac[]
QED

Theorem ricf_history_inherited_block:
  ricf_history_inherited vs C ctx0 log p stk PG G tn fn inst s /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK s' /\ ~s'.vs_halted /\
  enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
  ricf_history_inherited vs C ctx0 log p stk PG
    (entry_prov fn s' G) (entry_taint_vars fn s' tn) fn inst' s1
Proof
  simp[ricf_history_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_block >> metis_tac[]
QED

Theorem ricf_history_inherited_call:
  ricf_history_inherited vs C ctx0 log p stk PG G tn caller callinst s /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_history_inherited vs C ctx0 log p
    (<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
Proof
  simp[ricf_history_inherited_def] >> rpt strip_tac >>
  qexistsl_tac [`anchor`, `tail`,
    `<| cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var |> :: pre`, `atn`] >>
  simp[] >> conj_tac >> irule readonly_call_reachable_call >> metis_tac[]
QED

(* f is strictly inside the protected activation.  Keeping the witnesses
   explicit prevents this rule from inadvertently popping the anchor. *)
Theorem ricf_history_inherited_nested_ret:
  atn.t_var = anchor.cf_tvar /\
  ricf_history_cursor vs C ctx0 log p [] anchor.cf_params anchor.cf_prov
    atn anchor.cf_fn anchor.cf_state /\
  readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
    anchor tail (SND p.rpe_dst) p.rpe_db p.rpe_size
    (f::pre) PG G tn fn rinst s /\
  readonly_call_reachable vs C (rma_is_readonly ctx0.icf_rma)
    anchor tail (SND p.rpe_src) p.rpe_sb p.rpe_size
    (f::pre) PG G tn fn rinst s /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_history_inherited vs C ctx0 log p (pre ++ anchor::tail) f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn inst' (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
Proof
  strip_tac >> simp[ricf_history_inherited_def] >>
  qexistsl_tac [`anchor`, `tail`, `pre`, `atn`] >> simp[] >>
  conj_tac >> irule readonly_call_reachable_ret >> metis_tac[]
QED

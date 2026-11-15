(* Call restoration for provenance-relocated readonly arguments. *)
Theory readonlyInvokeCopyFwdCalls
Ancestors
  readonlyInvokeCopyFwdRel reachableFnSim taintAgree
  o1LowerDloadJointRestore o1LowerDloadShared internalReturnCopyFwdSim
  o1LowerDloadRelocationKernel venomExecSemantics venomState ptrDiscipline
  finite_map list pred_set passSimulationDefs calleeTransport

Theorem ricf_frame_adopt_return:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_frame_agree D X sites PG G tn
    (adopt_return_fmp ret s) (adopt_return_fmp ret t)
Proof
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, ricf_frame_agree_def, taint_agree_def,
       ld_shared_agree_def, ircf_cross_def] >>
  rpt strip_tac >> gvs[venom_state_component_equality] >> metis_tac[]
QED

Theorem ricf_frame_update_scalar:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_frame_agree D X sites PG (DRESTRICT G (COMPL {out}))
    (tn with t_var := DRESTRICT tn.t_var (COMPL {out}))
    (update_var out w s) (update_var out w t)
Proof
  simp[ricf_frame_agree_def, taint_agree_def, update_var_def,
       ld_shared_agree_def, ircf_cross_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[venom_state_component_equality] >>
  Cases_on `v = out` >>
  gvs[ricf_value_agree_def, ld_value_agree_def, word_agree_except_def,
      FAPPLY_FUPDATE_THM] >> metis_tac[]
QED

Theorem ricf_frame_fold_outputs:
  !bindings G tn s t.
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_frame_agree D X sites PG
    (DRESTRICT G (COMPL (set (MAP FST bindings))))
    (tn with t_var := DRESTRICT tn.t_var (COMPL (set (MAP FST bindings))))
    (FOLDL (\st (out,w). update_var out w st) s bindings)
    (FOLDL (\st (out,w). update_var out w st) t bindings)
Proof
  Induct >- simp[DRESTRICT_UNIV] >>
  simp[] >> qx_gen_tac `h` >> PairCases_on `h` >> rpt strip_tac >>
  drule ricf_frame_update_scalar >>
  disch_then (qspecl_then [`h1`, `h0`] mp_tac) >> strip_tac >>
  first_x_assum drule >>
  `COMPL {h0} INTER COMPL (set (MAP FST bindings)) =
   COMPL (h0 INSERT set (MAP FST bindings))` by simp[EXTENSION] >>
  simp[DRESTRICT_DRESTRICT]
QED

Theorem ricf_frame_bind_outputs:
  ricf_frame_agree D X sites PG G tn s t /\
  bind_outputs outs vals s = SOME s' ==>
  ?t'. bind_outputs outs vals t = SOME t' /\
    ricf_frame_agree D X sites PG (DRESTRICT G (COMPL (set outs)))
      (tn with t_var := DRESTRICT tn.t_var (COMPL (set outs))) s' t'
Proof
  simp[bind_outputs_def] >> rpt strip_tac >> gvs[] >>
  drule ricf_frame_fold_outputs >>
  disch_then (qspec_then `ZIP (outs,vals)` mp_tac) >> simp[MAP_ZIP]
QED

Theorem ricf_live_resume_caller:
  ricf_live_return_core D ids (cf::stk) (sites::maps)
    (caller::targets) tn se te /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cf.cf_state se)) = SOME s' ==>
  ?t'. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
      (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
      (DRESTRICT cf.cf_prov (COMPL (set outs)))
      (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs))) s' t' /\
    ricf_live_stack_agree D ids tn maps stk targets se te
Proof
  strip_tac >> drule ricf_live_return_actual_caller >> strip_tac >>
  drule ricf_frame_adopt_return >>
  disch_then (qspec_then `ret` assume_tac) >>
  drule_all ricf_frame_bind_outputs >> strip_tac >>
  qexists_tac `t'` >> simp[] >>
  fs[ricf_live_return_core_def, ricf_live_stack_cons]
QED

(* Smaller-fuel recursion is independent of the representation of the
   readonly/certificate invariant used to establish the entry boundary. *)
Theorem ricf_invoke_recursive_result:
  fn_sim_below D vs C C' (ricf_live_boundary_agree D ids) Rret (SUC k) /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  ricf_live_boundary_agree D ids stk PG FEMPTY tn fn cs ct /\
  block_reach vs C stk PG FEMPTY tn fn cs /\
  terminates (run_blocks k C fn cs) ==>
  ?m. fn_run_rel D Rret stk PG fn (run_blocks k C fn cs)
    (run_blocks m C' fn' ct)
Proof
  simp[fn_sim_below_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem ricf_frame_inst_idx:
  ricf_frame_agree D X sites PG G tn s t ==>
  ricf_frame_agree D X sites PG G tn
    (s with vs_inst_idx := n) (t with vs_inst_idx := n)
Proof
  simp[ricf_frame_agree_def, taint_agree_def, ld_shared_agree_def,
       ircf_cross_def] >> rpt strip_tac >>
  gvs[venom_state_component_equality] >> metis_tac[]
QED

(* An actual target caller is explicit here; no existential return witness
   may silently replace its local variables or relocation map. *)
Theorem ricf_live_resume_next:
  ricf_live_return_core D ids (cf::stk) (sites::maps)
    (caller::targets) tn se te /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cf.cf_state se)) = SOME s' ==>
  ?t'. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
      (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
      (DRESTRICT cf.cf_prov (COMPL (set outs)))
      (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs)))
      (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
    ricf_live_stack_agree D ids tn maps stk targets se te
Proof
  strip_tac >> drule_all ricf_live_resume_caller >> strip_tac >>
  qexists_tac `t'` >> simp[] >> irule ricf_frame_inst_idx >> simp[]
QED

(* The callee run keeps the suspended-map index fixed.  Entry saves the
   actual caller locals; the recursive return may choose fresh targets,
   which are reanchored before the existing restoration kernel is used. *)
Theorem ricf_indexed_resume_next:
  ricf_live_boundary_core D ids (cf::stk) PG G etn fn current
    (sites::maps) (caller::targets) G0 tn0 cs ct /\
  ricf_indexed_return D ids (sites::maps) (cf::stk)
    PG' G' tn fn' ret se te /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cf.cf_state se)) = SOME s' ==>
  ?t'. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
      (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
      (DRESTRICT cf.cf_prov (COMPL (set outs)))
      (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs)))
      (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
    ricf_live_stack_agree D ids tn maps stk targets se te
Proof
  strip_tac >> drule_all ricf_indexed_call_return >> strip_tac >>
  drule_all ricf_live_resume_next >> simp[]
QED

Theorem ricf_invoke_outcome_view:
  i.inst_opcode = INVOKE /\ j.inst_opcode = INVOKE /\
  j.inst_outputs = i.inst_outputs /\
  decode_invoke i = SOME (nm,ops) /\ decode_invoke j = SOME (nm',ops') /\
  lookup_function nm C.ctx_functions = SOME fn /\
  lookup_function nm' C'.ctx_functions = SOME fn' /\
  eval_operands ops s = SOME args /\ eval_operands ops' t = SOME args' /\
  setup_callee fn args s = SOME cs /\ setup_callee fn' args' t = SOME ct /\
  terminates (step_inst k C i s) /\
  fn_run_rel D Rret stk PG fn (run_blocks k C fn cs)
    (run_blocks m C' fn' ct) ==>
  case step_inst k C i s of
    OK s' => ?ret se te G tn.
      run_blocks k C fn cs = IntRet ret se /\
      run_blocks m C' fn' ct = IntRet ret te /\
      Rret stk PG G tn fn ret se te /\
      bind_outputs i.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' /\
      (!t'. bind_outputs i.inst_outputs ret.iret_values
        (adopt_return_fmp ret (merge_callee_state t te)) = SOME t' ==>
        step_inst m C' j t = OK t')
  | _ => dead_result_rel D (step_inst k C i s) (step_inst m C' j t)
Proof
  strip_tac >>
  Cases_on `run_blocks k C fn cs` >>
  Cases_on `run_blocks m C' fn' ct` >>
  gvs[fn_run_rel_def] >> fs[step_inst_def] >>
  gvs[terminates_def, AllCaseEqs()] >>
  rename1 `Rret _ _ _ _ _ ret se te` >>
  Cases_on `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s se))` >>
  gvs[terminates_def] >> metis_tac[]
QED

(* Factor the operational INVOKE cases once.  Certificate families supply
   only the successful-return continuation. *)
Theorem ricf_invoke_outcome_lift:
  i.inst_opcode = INVOKE /\ j.inst_opcode = INVOKE /\
  j.inst_outputs = i.inst_outputs /\
  decode_invoke i = SOME (nm,ops) /\
  decode_invoke j = SOME (nm',ops') /\
  lookup_function nm C.ctx_functions = SOME fn /\
  lookup_function nm' C'.ctx_functions = SOME fn' /\
  eval_operands ops s = SOME args /\ eval_operands ops' t = SOME args' /\
  setup_callee fn args s = SOME cs /\ setup_callee fn' args' t = SOME ct /\
  terminates (step_inst k C i s) /\
  fn_run_rel D Rret stk PG fn (run_blocks k C fn cs)
    (run_blocks m C' fn' ct) /\
  (!ret se te G tn s'.
    run_blocks k C fn cs = IntRet ret se /\
    run_blocks m C' fn' ct = IntRet ret te /\
    Rret stk PG G tn fn ret se te /\
    bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s se)) = SOME s' ==>
    ?t' un. bind_outputs i.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state t te)) = SOME t' /\ Q un s' t') ==>
  case step_inst k C i s of
    OK s' => ?t' un. step_inst m C' j t = OK t' /\ Q un s' t'
  | _ => dead_result_rel D (step_inst k C i s) (step_inst m C' j t)
Proof
  strip_tac >> drule_all_then assume_tac ricf_invoke_outcome_view >>
  Cases_on `step_inst k C i s` >> gvs[] >> metis_tac[]
QED

(* Semantic outcome kernel.  Operand evaluation and the entry core are
   supplied by the readonly/certificate call preparation: the two argument
   lists need not be equal.  The suspended maps remain indexed throughout
   recursion, including when the callee itself makes nested calls. *)
Theorem ricf_indexed_invoke_outcomes:
  i.inst_opcode = INVOKE /\ j.inst_opcode = INVOKE /\
  j.inst_outputs = i.inst_outputs /\
  decode_invoke i = SOME (nm,ops) /\
  decode_invoke j = SOME (nm',ops') /\
  lookup_function nm C.ctx_functions = SOME fn /\
  lookup_function nm' C'.ctx_functions = SOME fn' /\
  eval_operands ops cf.cf_state = SOME args /\
  eval_operands ops' caller = SOME args' /\
  setup_callee fn args cf.cf_state = SOME cs /\
  setup_callee fn' args' caller = SOME ct /\
  ricf_live_boundary_core D ids (cf::stk) PG FEMPTY etn fn current
    (sites::maps) (caller::targets) G0 tn0 cs ct /\
  ricf_indexed_sim_below D ids vs C C' n /\ k < n /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  block_reach vs C (cf::stk) PG FEMPTY etn fn cs /\
  terminates (step_inst k C i cf.cf_state) ==>
  ?m. case step_inst k C i cf.cf_state of
    OK s' => ?t' tn.
      step_inst m C' j caller = OK t' /\
      ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
        (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
        (DRESTRICT cf.cf_prov (COMPL (set i.inst_outputs)))
        (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set i.inst_outputs)))
        (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
        (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
      ricf_live_stack_agree D ids tn maps stk targets
        (case run_blocks k C fn cs of IntRet ret se => se | _ => cs)
        (case run_blocks m C' fn' ct of IntRet ret te => te | _ => ct)
  | _ => dead_result_rel D (step_inst k C i cf.cf_state)
           (step_inst m C' j caller)
Proof
  strip_tac >>
  `terminates (run_blocks k C fn cs)` by
    (qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
     simp[step_inst_def] >> Cases_on `run_blocks k C fn cs` >>
     simp[terminates_def, AllCaseEqs()]) >>
  `ricf_indexed_boundary D ids (sites::maps) (cf::stk) PG FEMPTY
     etn fn cs ct` by
    (simp[ricf_indexed_boundary_def] >> metis_tac[]) >>
  drule_all ricf_indexed_sim_below_elim >> strip_tac >>
  drule_all_then assume_tac ricf_invoke_outcome_view >>
  qexists_tac `m` >> Cases_on `step_inst k C i cf.cf_state` >>
  gvs[] >>
  drule_all ricf_indexed_resume_next >> strip_tac >>
  qexistsl [`t'`, `tn`] >> simp[]
QED

(* Cross-only certificates observe shared memory, not relocated locals. *)
Theorem ricf_cert_nested_entry:
  ricf_frame_agree D (ircf_dead ids s stk) oldsites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  cf.cf_state = s /\ cf.cf_params = PG /\ cf.cf_prov = G /\
  cf.cf_tvar = tn.t_var /\
  ricf_params_agree sites newPG args args' /\ ricf_sites_ok sites /\
  ircf_cross tn (ricf_site_triples sites) s t /\
  ircf_cross tn cur s t /\ ricf_cert_crosses tn curs stk s t /\
  (if NULL args then 0w else LAST args) =
    (if NULL args' then 0w else LAST args') /\
  setup_callee fn args s = SOME cs /\
  setup_callee fn args' t = SOME ct ==>
  ricf_cert_core D ids (cf::stk) newPG FEMPTY
    (tn with t_var := FEMPTY) fn sites (oldsites::maps) (t::targets)
    FEMPTY (tn with t_var := FEMPTY) {} (cur::curs) cs ct
Proof
  strip_tac >> drule_all ricf_live_nested_entry >> strip_tac >>
  simp[ricf_cert_core_def, ricf_cert_crosses_cons] >>
  fs[setup_callee_def] >> gvs[AllCaseEqs()] >>
  fs[ricf_cert_crosses_def, ircf_cross_def] >> gvs[]
QED

Theorem ricf_cert_resume_next:
  ricf_cert_core D ids (cf::stk) PG G etn fn current
    (sites::maps) (caller::targets) G0 tn0 calcur (cur::curs) cs ct /\
  ricf_cert_return D ids (sites::maps) (cur::curs) (cf::stk)
    PG' G' tn fn' ret se te /\
  bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cf.cf_state se)) = SOME s' ==>
  ?t'. bind_outputs outs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state caller te)) = SOME t' /\
    ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
      (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
      (DRESTRICT cf.cf_prov (COMPL (set outs)))
      (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs)))
      (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
    ricf_live_stack_agree D ids tn maps stk targets se te /\
    ircf_cross (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs)))
      cur (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
    ricf_cert_crosses
      (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set outs))) curs stk
      (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
      (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
Proof
  strip_tac >> drule_all ricf_cert_call_return >> strip_tac >>
  fs[ricf_cert_return_core_def, ricf_cert_crosses_cons] >>
  drule_all ricf_live_resume_next >> strip_tac >> qexists_tac `t'` >>
  simp[] >>
  imp_res_tac bind_outputs_shared_fields >>
  fs[ricf_cert_crosses_def, ircf_cross_def,
     adopt_return_fmp_def, merge_callee_state_def] >>
  Cases_on `ret.iret_adopt_fmp` >> gvs[]
QED

Theorem ricf_cert_invoke_outcomes:
  i.inst_opcode = INVOKE /\ j.inst_opcode = INVOKE /\
  j.inst_outputs = i.inst_outputs /\
  decode_invoke i = SOME (nm,ops) /\ decode_invoke j = SOME (nm',ops') /\
  lookup_function nm C.ctx_functions = SOME fn /\
  lookup_function nm' C'.ctx_functions = SOME fn' /\
  eval_operands ops cf.cf_state = SOME args /\
  eval_operands ops' caller = SOME args' /\
  setup_callee fn args cf.cf_state = SOME cs /\
  setup_callee fn' args' caller = SOME ct /\
  ricf_cert_core D ids (cf::stk) PG FEMPTY etn fn current
    (sites::maps) (caller::targets) G0 tn0 calcur (cur::curs) cs ct /\
  ricf_cert_sim_below D ids vs C C' n /\ k < n /\
  MEM fn C.ctx_functions /\
  lookup_function fn.fn_name C'.ctx_functions = SOME fn' /\
  block_reach vs C (cf::stk) PG FEMPTY etn fn cs /\
  terminates (step_inst k C i cf.cf_state) ==>
  ?m. case step_inst k C i cf.cf_state of
    OK s' => ?t' tn.
      step_inst m C' j caller = OK t' /\
      ricf_frame_agree D (ircf_dead ids cf.cf_state stk) sites
        (ricf_complete_params cf.cf_params cf.cf_state.vs_params)
        (DRESTRICT cf.cf_prov (COMPL (set i.inst_outputs)))
        (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set i.inst_outputs)))
        (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
        (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
      ricf_live_stack_agree D ids tn maps stk targets
        (case run_blocks k C fn cs of IntRet ret se => se | _ => cs)
        (case run_blocks m C' fn' ct of IntRet ret te => te | _ => ct) /\
      ircf_cross (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set i.inst_outputs)))
        cur (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
        (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx) /\
      ricf_cert_crosses
        (tn with t_var := DRESTRICT cf.cf_tvar (COMPL (set i.inst_outputs)))
        curs stk (s' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
        (t' with vs_inst_idx := SUC cf.cf_state.vs_inst_idx)
  | _ => dead_result_rel D (step_inst k C i cf.cf_state)
           (step_inst m C' j caller)
Proof
  strip_tac >>
  `terminates (run_blocks k C fn cs)` by
    (qpat_x_assum `terminates (step_inst _ _ _ _)` mp_tac >>
     simp[step_inst_def] >> Cases_on `run_blocks k C fn cs` >>
     simp[terminates_def, AllCaseEqs()]) >>
  `ricf_cert_boundary D ids (sites::maps) (cur::curs) (cf::stk)
     PG FEMPTY etn fn cs ct` by
    (simp[ricf_cert_boundary_def] >> metis_tac[]) >>
  drule_all ricf_cert_sim_below_elim >> strip_tac >>
  drule_all_then assume_tac ricf_invoke_outcome_view >>
  qexists_tac `m` >> Cases_on `step_inst k C i cf.cf_state` >> gvs[] >>
  drule_all ricf_cert_resume_next >> strip_tac >>
  qexistsl [`t'`, `tn`] >> simp[]
QED

(* Two nested calls: the inner saved current-copy set is empty, whereas
   the outer set is not.  Both saved relocation maps have genuine shifts.
   Return certificates are conditional run results, not resumed callers. *)
Theorem ricf_cert_two_level_probe:
  oldsites <> sites1 /\ cur <> {} /\
  FLOOKUP oldsites (db0,sz0) = SOME (db0,sb0,sz0) /\ db0 <> sb0 /\
  FLOOKUP sites1 (db1,sz1) = SOME (db1,sb1,sz1) /\ db1 <> sb1 /\
  ricf_frame_agree D (ircf_dead ids s stk) oldsites
    (ricf_complete_params PG s.vs_params) G tn s t /\
  ricf_live_stack_agree D ids tn maps stk targets s t /\
  cf0.cf_state = s /\ cf0.cf_params = PG /\ cf0.cf_prov = G /\
  cf0.cf_tvar = tn.t_var /\
  ricf_params_agree sites1 PG1 args1 args1' /\ ricf_sites_ok sites1 /\
  ircf_cross tn (ricf_site_triples sites1) s t /\
  ircf_cross tn cur s t /\ ricf_cert_crosses tn curs stk s t /\
  (if NULL args1 then 0w else LAST args1) =
    (if NULL args1' then 0w else LAST args1') /\
  setup_callee fn1 args1 s = SOME cs1 /\
  setup_callee fn1 args1' t = SOME ct1 /\
  cf1.cf_state = cs1 /\ cf1.cf_params = PG1 /\
  cf1.cf_prov = FEMPTY /\ cf1.cf_tvar = FEMPTY /\
  ricf_params_agree sites2 PG2 args2 args2' /\ ricf_sites_ok sites2 /\
  ircf_cross (tn with t_var := FEMPTY) (ricf_site_triples sites2) cs1 ct1 /\
  (if NULL args2 then 0w else LAST args2) =
    (if NULL args2' then 0w else LAST args2') /\
  setup_callee fn2 args2 cs1 = SOME cs2 /\
  setup_callee fn2 args2' ct1 = SOME ct2 /\
  ricf_cert_return D ids (sites1::oldsites::maps) ({}::cur::curs)
    (cf1::cf0::stk) RPG2 RG2 rtn2 fn2 ret2 se2 te2 /\
  ricf_cert_return D ids (oldsites::maps) (cur::curs)
    (cf0::stk) RPG1 RG1 rtn1 fn1 ret1 se1 te1 /\
  bind_outputs outs2 ret2.iret_values
    (adopt_return_fmp ret2 (merge_callee_state cs1 se2)) = SOME u2 /\
  bind_outputs outs1 ret1.iret_values
    (adopt_return_fmp ret1 (merge_callee_state s se1)) = SOME u1 ==>
  ?v2 v1.
    bind_outputs outs2 ret2.iret_values
      (adopt_return_fmp ret2 (merge_callee_state ct1 te2)) = SOME v2 /\
    bind_outputs outs1 ret1.iret_values
      (adopt_return_fmp ret1 (merge_callee_state t te1)) = SOME v1 /\
    ricf_frame_agree D (ircf_dead ids cs1 (cf0::stk)) sites1
      (ricf_complete_params PG1 cs1.vs_params)
      (DRESTRICT FEMPTY (COMPL (set outs2)))
      (rtn2 with t_var := DRESTRICT FEMPTY (COMPL (set outs2)))
      (u2 with vs_inst_idx := SUC cs1.vs_inst_idx)
      (v2 with vs_inst_idx := SUC cs1.vs_inst_idx) /\
    ricf_frame_agree D (ircf_dead ids s stk) oldsites
      (ricf_complete_params PG s.vs_params)
      (DRESTRICT G (COMPL (set outs1)))
      (rtn1 with t_var := DRESTRICT tn.t_var (COMPL (set outs1)))
      (u1 with vs_inst_idx := SUC s.vs_inst_idx)
      (v1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    ricf_cert_crosses
      (rtn2 with t_var := DRESTRICT FEMPTY (COMPL (set outs2)))
      (cur::curs) (cf0::stk)
      (u2 with vs_inst_idx := SUC cs1.vs_inst_idx)
      (v2 with vs_inst_idx := SUC cs1.vs_inst_idx) /\
    ircf_cross (rtn1 with t_var := DRESTRICT tn.t_var (COMPL (set outs1)))
      cur (u1 with vs_inst_idx := SUC s.vs_inst_idx)
      (v1 with vs_inst_idx := SUC s.vs_inst_idx) /\
    ricf_cert_crosses
      (rtn1 with t_var := DRESTRICT tn.t_var (COMPL (set outs1))) curs stk
      (u1 with vs_inst_idx := SUC s.vs_inst_idx)
      (v1 with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >>
  drule_all_then assume_tac ricf_cert_nested_entry >>
  `ricf_cert_core D ids (cf1::cf0::stk) PG2 FEMPTY
     (tn with t_var := FEMPTY) fn2 sites2 (sites1::oldsites::maps)
     (ct1::t::targets) FEMPTY (tn with t_var := FEMPTY)
     {} ({}::cur::curs) cs2 ct2` by
    (irule (SRULE [] (Q.INST [`tn` |-> `tn with t_var := FEMPTY`] ricf_cert_nested_entry)) >>
     fs[ricf_cert_core_def, ricf_live_boundary_core_def] >> metis_tac[]) >>
  metis_tac[ricf_cert_resume_next]
QED

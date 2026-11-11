(* Call restoration for provenance-relocated readonly arguments. *)
Theory readonlyInvokeCopyFwdCalls
Ancestors
  readonlyInvokeCopyFwdRel reachableFnSim taintAgree
  o1LowerDloadJointRestore o1LowerDloadShared internalReturnCopyFwdSim
  o1LowerDloadRelocationKernel venomExecSemantics venomState ptrDiscipline
  finite_map list pred_set passSimulationDefs

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
  qexists_tac `m` >>
  Cases_on `run_blocks k C fn cs` >>
  Cases_on `run_blocks m C' fn' ct` >>
  gvs[fn_run_rel_def] >>
  fs[step_inst_def] >>
  gvs[terminates_def, AllCaseEqs()] >>
  rename1 `ricf_indexed_return _ _ _ _ _ _ _ _ ret se te` >>
  Cases_on `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state cf.cf_state se))` >>
  gvs[] >>
  drule_all ricf_indexed_resume_next >> strip_tac >> metis_tac[]
QED

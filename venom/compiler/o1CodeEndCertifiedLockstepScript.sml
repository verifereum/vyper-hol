Theory o1CodeEndCertifiedLockstep
Ancestors
  o1FrameLockstep o1PassLift ptrDiscipline unitMemInv stateFrame
  contextCodegenRel codegenRel venomExecSemantics venomExecProps venomInst
  venomState list finite_map option pred_set

(* Retain evidence about the very relation used by the simulation. *)
Definition code_end_certified_ctx_def:
  code_end_certified_ctx cert L C C' <=>
    C'.ctx_entry = C.ctx_entry /\
    LIST_REL (\fn fn'. fn'.fn_name = fn.fn_name /\
      fn_entry_label fn' = fn_entry_label fn /\
      ?pos R. (!l k. pos l (SUC k) = SUC (pos l k)) /\
        lockstep_sim L C C' fn fn' pos R /\ cert fn fn' pos R)
      C.ctx_functions C'.ctx_functions
End

Definition code_end_certified_frame_def:
  code_end_certified_frame cert L C C' f f' <=>
    f'.cf_params = f.cf_params /\ f'.cf_inst.inst_opcode = INVOKE /\
    ?pos R sg.
      (!l k. pos l (SUC k) = SUC (pos l k)) /\
      lockstep_sim L C C' f.cf_fn f'.cf_fn pos R /\
      cert f.cf_fn f'.cf_fn pos R /\
      R T (f.cf_inst,f.cf_state) sg (f'.cf_inst,f'.cf_state) /\
      vars_ghost_rel sg f.cf_prov f.cf_tvar f'.cf_prov f'.cf_tvar
End

Theorem code_end_certified_lookup[local]:
  code_end_certified_ctx cert L C C' /\
  lookup_function nm C'.ctx_functions = SOME fn' ==>
  ?fn pos R. lookup_function nm C.ctx_functions = SOME fn /\
    fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn /\
    (!l k. pos l (SUC k) = SUC (pos l k)) /\
    lockstep_sim L C C' fn fn' pos R /\ cert fn fn' pos R
Proof
  rw[code_end_certified_ctx_def] >> drule list_rel_lookup_function >>
  (impl_tac >- simp[]) >>
  disch_then (qspec_then `nm` mp_tac) >>
  Cases_on `lookup_function nm C.ctx_functions` >>
  simp[optionTheory.OPTREL_def] >> metis_tac[]
QED

Theorem code_end_certified_resume[local]:
  code_end_certified_frame cert L C C' f f' /\ execution_frame e' = execution_frame e /\
  bind_outputs f'.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f'.cf_state e')) = SOME t' /\
  active_inst f'.cf_fn j' (t' with vs_inst_idx := SUC f'.cf_state.vs_inst_idx) ==>
  ?posF RF sgF pF jF tF sgF'.
    (!l k. posF l (SUC k) = SUC (posF l k)) /\
    lockstep_sim L C C' f.cf_fn f'.cf_fn posF RF /\ cert f.cf_fn f'.cf_fn posF RF /\
    bind_outputs f.cf_inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state f.cf_state e)) = SOME tF /\
    RF pF (jF, tF with vs_inst_idx := SUC f.cf_state.vs_inst_idx) sgF'
       (j', t' with vs_inst_idx := SUC f'.cf_state.vs_inst_idx) /\
    out_rename_ok sgF f.cf_inst.inst_outputs f'.cf_inst.inst_outputs sgF' /\
    vars_ghost_rel sgF f.cf_prov f.cf_tvar f'.cf_prov f'.cf_tvar /\
    active_inst f.cf_fn jF (tF with vs_inst_idx := SUC f.cf_state.vs_inst_idx) /\
    f'.cf_params = f.cf_params
Proof
  rewrite_tac[code_end_certified_frame_def] >> strip_tac >>
  drule_all lockstep_resume >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  qexistsl [`pos`, `R`, `sg`] >> simp[] >> metis_tac[]
QED

Theorem code_end_frame_reachable_certified:
  !vs C' stk' PG G' tn' fn' inst' s'.
    frame_reachable vs C' stk' PG G' tn' fn' inst' s' ==>
    !cert C. code_end_certified_ctx cert vs.vs_labels C C' /\
      vs.vs_vars = FEMPTY /\ ~vs.vs_halted ==>
    ?stk G tn fn inst s p sg pos R.
      frame_reachable vs C stk PG G tn fn inst s /\
      (!l k. pos l (SUC k) = SUC (pos l k)) /\
      lockstep_sim vs.vs_labels C C' fn fn' pos R /\ cert fn fn' pos R /\
      R p (inst,s) sg (inst',s') /\ ghost_rel sg G tn G' tn' /\
      LIST_REL (code_end_certified_frame cert vs.vs_labels C C') stk stk'
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume code_end_frame_reachable_certified[entry]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all code_end_certified_lookup >> strip_tac >>
  `C.ctx_entry = SOME name` by fs[code_end_certified_ctx_def] >>
  qmatch_asmsub_abbrev_tac `enters_block _ s0 _` >>
  `fn_entry_state fn s0` by
    (simp[Abbr `s0`] >> irule context_fn_entry_state >> gvs[]) >>
  `s0.vs_labels = vs.vs_labels` by simp[Abbr `s0`] >>
  drule_all lockstep_entry >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  rename1 `R p (instS,s1S) sg _` >>
  qexistsl [`[]`, `FEMPTY`, `entry_taint`, `fn`, `instS`, `s1S`, `p`, `sg`,
            `pos`, `R`] >>
  simp[ghost_rel_def, vars_ghost_rel_def] >>
  reverse conj_tac >- simp[entry_taint_def, var_taint_def] >>
  irule frame_reachable_entry >> gvs[Abbr `s0`]
QED

Resume code_end_frame_reachable_certified[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  Cases_on `p`
  >- (gvs[] >>
      drule_all lockstep_step >> strip_tac >>
      `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
        fs[inst_pair_def] >>
      gvs[] >>
      qpat_x_assum `!j'. active_inst fn' j' _ ==> _` drule >> strip_tac >>
      imp_res_tac lockstep_rel >>
      rename1 `R p2 (j,_) sg2 (inst'',_)` >>
      qexistsl [`stk`, `step_prov PG G inst t`, `step_taint inst s t tn`,
                `fn`, `j`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `p2`,
                `sg2`, `pos`, `R`] >>
      simp[] >> conj_tac
      >- (irule frame_reachable_next >> simp[] >> metis_tac[]) >>
      irule step_ghost_pair >> gvs[state_rel_def] >> qexists `sg` >> gvs[]) >>
  fs[] >>
  drule_all lockstep_copy >> strip_tac >>
  rename1 `R pc (inst,s) sgc (inst'',_)` >>
  qexistsl [`stk`, `G`, `tn`, `fn`, `inst`, `s`, `pc`, `sgc`, `pos`, `R`] >>
  simp[] >> irule (cj 2 step_ghost_copy) >> simp[] >> metis_tac[]
QED

Resume code_end_frame_reachable_certified[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all lockstep_rel >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP /\
   inst'.inst_opcode <> INVOKE` by (rpt strip_tac >> gvs[is_terminator_def]) >>
  `p` by (Cases_on `p` >> gvs[]) >>
  gvs[] >>
  `inst.inst_opcode = inst'.inst_opcode` by fs[inst_pair_def] >>
  drule_all lockstep_step >> strip_tac >> gvs[] >>
  qpat_x_assum `!t1' j'. _` drule_all >> strip_tac >>
  imp_res_tac lockstep_rel >>
  rename1 `enters_block fn t t1N` >>
  rename1 `R pN (jN,t1N) sgN _` >>
  `~t.vs_halted` by metis_tac[execution_frame_fields] >>
  qexistsl [`stk`, `entry_prov fn t G`, `entry_taint_vars fn t tn`, `fn`,
            `jN`, `t1N`, `pN`, `sgN`, `pos`, `R`] >>
  simp[] >> conj_tac
  >- (irule frame_reachable_block >> simp[] >> metis_tac[]) >>
  irule entry_ghost_rel >> simp[] >> qexists `sg` >> simp[]
QED

Resume code_end_frame_reachable_certified[call]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by simp[] >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  `?ops0. inst.inst_operands = Label nm :: ops0 /\
          LIST_REL (op_rename sg) ops0 ops` by
    (gvs[inst_pair_def, decode_invoke_def, AllCaseEqs(), LIST_REL_CONS2,
         op_rename_label] >> metis_tac[]) >>
  `decode_invoke inst = SOME (nm, ops0) /\ inst.inst_opcode = INVOKE` by
    fs[decode_invoke_def, inst_pair_def] >>
  `vars_ghost_rel sg G tn.t_var G' tn'.t_var` by fs[ghost_rel_def] >>
  `MAP (op_prov G') ops = MAP (op_prov G) ops0` by
    metis_tac[map_op_prov_rename] >>
  `execution_frame s' = execution_frame s /\ vars_rel sg s s'` by
    fs[state_rel_def] >>
  `s'.vs_labels = s.vs_labels` by metis_tac[execution_frame_fields] >>
  `LIST_REL (\op op'. op_rename sg op op' /\
                      eval_operand op' s' = eval_operand op s) ops0 ops` by
    (irule LIST_REL_op_rename_eval >> fs[]) >>
  drule eval_operands_rel >> strip_tac >>
  `eval_operands ops0 s = SOME args` by gvs[] >>
  drule_all code_end_certified_lookup >>
  disch_then (qx_choose_then `calleeS` (qx_choose_then `callee_pos`
    (qx_choose_then `callee_R` strip_assume_tac))) >>
  `setup_callee calleeS args s = SOME cs` by
    metis_tac[setup_callee_execution_frame] >>
  `fn_entry_state calleeS cs` by metis_tac[setup_callee_fn_entry_state] >>
  `cs.vs_labels = vs.vs_labels` by
    (imp_res_tac frame_reachable_labels >>
     qpat_x_assum `setup_callee calleeS _ _ = _` mp_tac >>
     rw[setup_callee_def] >> simp[]) >>
  drule_at (Pos (el 2)) lockstep_entry >> disch_then drule_all >> strip_tac >>
  rename1 `enters_block calleeS cs s1c` >>
  rename1 `callee_R pc (instc,s1c) sgc _` >>
  imp_res_tac lockstep_rel >>
  `frame_reachable vs C
     (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
        cf_prov := G; cf_tvar := tn.t_var|> :: stk)
     (MAP (op_prov G) ops0) FEMPTY (tn with t_var := FEMPTY) calleeS instc s1c` by
    (irule frame_reachable_call >> simp[] >> metis_tac[]) >>
  `code_end_certified_frame cert vs.vs_labels C C'
     <|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
       cf_prov := G; cf_tvar := tn.t_var|>
     <|cf_fn := fn'; cf_inst := inst'; cf_state := s'; cf_params := PG;
       cf_prov := G'; cf_tvar := tn'.t_var|>` by
    (simp[code_end_certified_frame_def] >> qexistsl [`pos`, `R`, `sg`] >> simp[]) >>
  qexistsl [`<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
               cf_prov := G; cf_tvar := tn.t_var|> :: stk`,
            `FEMPTY`, `tn with t_var := FEMPTY`, `calleeS`, `instc`, `s1c`,
            `pc`, `sgc`, `callee_pos`, `callee_R`] >>
  fs[ghost_rel_def, vars_ghost_rel_def, var_taint_def]
QED

Resume code_end_frame_reachable_certified[ret]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `step_inst fuel C' ri' sc' = IntRet ret e'` >>
  rename1 `bind_outputs fr'.cf_inst.inst_outputs ret.iret_values _ = SOME tq'` >>
  rename1 `active_inst fr'.cf_fn jq' _` >>
  rename1 `R p (ri,sc) sg (ri',sc')` >>
  fs[LIST_REL_CONS2] >>
  rename1 `code_end_certified_frame cert _ C C' fr fr'` >>
  rename1 `LIST_REL (code_end_certified_frame cert _ C C') stkS stk'` >>
  `ri'.inst_opcode <> ASSIGN /\ ri'.inst_opcode <> NOP /\
   ri'.inst_opcode <> INVOKE` by
    (rpt strip_tac >>
     metis_tac[step_inst_copy_not_intret, step_inst_invoke_not_intret]) >>
  drule_all lockstep_paired >> strip_tac >> fs[] >>
  drule_all lockstep_intret >> strip_tac >>
  drule_all code_end_certified_resume >> strip_tac >>
  `frame_reachable vs C stkS fr.cf_params
     (DRESTRICT fr.cf_prov (COMPL (set fr.cf_inst.inst_outputs)))
     (tn with t_var := DRESTRICT fr.cf_tvar (COMPL (set fr.cf_inst.inst_outputs)))
     fr.cf_fn jF (tF with vs_inst_idx := SUC fr.cf_state.vs_inst_idx)` by
    (irule frame_reachable_ret >> simp[] >> metis_tac[]) >>
  qexistsl [`stkS`,
            `DRESTRICT fr.cf_prov (COMPL (set fr.cf_inst.inst_outputs))`,
            `tn with t_var :=
               DRESTRICT fr.cf_tvar (COMPL (set fr.cf_inst.inst_outputs))`,
            `fr.cf_fn`, `jF`,
            `tF with vs_inst_idx := SUC fr.cf_state.vs_inst_idx`, `pF`,
            `sgF'`, `posF`, `RF`] >>
  fs[ghost_rel_def] >> irule ret_ghost_rel >> qexists `sgF` >> simp[]
QED

Finalise code_end_frame_reachable_certified

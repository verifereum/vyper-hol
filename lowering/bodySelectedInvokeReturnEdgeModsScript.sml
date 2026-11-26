(* Lift a single selected callee exit to the caller's INVOKE continuation. *)
Theory bodySelectedInvokeReturnEdgeMods
Ancestors
  fragGasOriginPtrInvoke fragGasFocus contextCodegenRel fragExec
  intCallFrame intCallStep lowerDloadPtrReturn allocaHistory ptrSafeRun
  ptrDiscipline vyperStorageFootprint venomExecSemantics venomState
  venomInst finite_map

Theorem selected_invoke_terminal[local]:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\
  decode_invoke inst = SOME (lbl,ops) /\ eval_operands ops t = SOME argv /\
  gas_origin_ptr_path (D,lo,explicit,ctx,callee,MAP (op_prov G) ops)
    (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc) /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u ==>
  ?setup fuel.
    setup_callee callee argv t = SOME setup /\ enters_block callee setup entered /\
    run_blocks fuel ctx callee setup = IntRet ir cs /\
    step_inst fuel ctx inst t = OK u
Proof
  strip_tac >>
  qpat_x_assum `gas_invoke_entry _ _ _ _` mp_tac >>
  simp[gas_invoke_entry_def] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (e,FEMPTY,_) _ _` >>
  `enters_block callee setup e` by
    (simp[enters_block_def, Abbr `e`] >> metis_tac[]) >>
  `exit_result (IntRet ir cs)` by simp[exit_result_def] >>
  drule_all setup_terminal_certificate >> strip_tac >>
  qexists_tac `fuel` >> simp[Once step_inst_def]
QED

Theorem selected_invoke_advance[local]:
  alloca_history func t /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  step_inst fuel ctx inst t = OK u /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  ir.iret_adopt_fmp = NONE /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  ~u.vs_halted /\ alloca_history func (u with vs_inst_idx := SUC t.vs_inst_idx) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >>
  drule_all step_inst_invoke_OK_control >> strip_tac >>
  drule_then strip_assume_tac invoke_return_frame >>
  `alloca_history func (t with vs_inst_idx := SUC t.vs_inst_idx)` by
    (irule history_nonalloca_advance >> simp[] >> qexistsl [`bb`,`inst`] >> simp[]) >>
  simp[] >> conj_tac
  >- (irule alloca_history_frame >>
      qexists_tac `t with vs_inst_idx := SUC t.vs_inst_idx` >> simp[]) >>
  `u.vs_fmp = t.vs_fmp /\ u.vs_initial_fmp = t.vs_initial_fmp` by
    (drule dload_bind_outputs_frame >> disch_then (once_rewrite_tac o single) >>
     simp[adopt_return_fmp_def, merge_callee_state_def]) >>
  qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
  simp[allocas_below_fmp_def] >> metis_tac[]
QED

Theorem selected_invoke_return_edge_mods:
  gas_invoke_entry (ctx,func) t callee entered /\
  lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME inst /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (lbl,ops) /\ eval_operands ops t = SOME argv /\
  outs = inst.inst_outputs /\ LENGTH outs = LENGTH ir.iret_values /\
  ir.iret_adopt_fmp = NONE /\ alloca_history func t /\
  valid_horizon cx st0 H observations /\
  (!H'. valid_horizon cx st0 H' observations ==>
    ptr_inst_ok (DF H') lo 0 ctx func G tn inst t /\
    gas_origin_ptr_path (DF H',lo,explicit,ctx,callee,MAP (op_prov G) ops)
      (entered,FEMPTY,tn with t_var := FEMPTY) marks (IntRet ir cs,Gc,tc)) ==>
  ?u setup fuel.
    bind_outputs outs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
    setup_callee callee argv t = SOME setup /\ enters_block callee setup entered /\
    run_blocks fuel ctx callee setup = IntRet ir cs /\ step_inst fuel ctx inst t = OK u /\
    let a = u with vs_inst_idx := SUC t.vs_inst_idx in
    let J = DRESTRICT G (COMPL (set outs)) in
    let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
      ~a.vs_halted /\ alloca_history func a /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
      !H'. valid_horizon cx st0 H' observations ==>
        gas_origin_ptr_edge (DF H',lo,explicit,ctx,func,PG) (t,G,tn) marks (OK a,J,N)
Proof
  strip_tac >> gvs[] >>
  qpat_assum `!H'. valid_horizon _ _ H' _ ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all gas_origin_ptr_invoke_intret >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  rename1 `bind_outputs _ _ _ = SOME u` >>
  drule_all selected_invoke_terminal >> strip_tac >>
  `~t.vs_halted` by fs[gas_invoke_entry_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by fs[ptr_inst_ok_def] >>
  drule_all selected_invoke_advance >> strip_tac >>
  qexistsl [`u`,`setup`,`fuel`] >> simp[] >>
  qpat_x_assum `ptr_inst_ok _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `gas_origin_ptr_path _ _ _ _` kall_tac >>
  qx_gen_tac `H1` >> strip_tac >>
  qpat_assum `!H'. valid_horizon _ _ H' _ ==> _` (qspec_then `H1` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all gas_origin_ptr_invoke_intret >>
  disch_then (qspec_then `PG` strip_assume_tac) >> gvs[]
QED

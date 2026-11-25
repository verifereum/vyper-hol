(* Close the selected SELFDESTRUCT suffix without extending the child path
   through a source overflow. The one target result is shared by all masks. *)
Theory entryCreateSelfdestructExit
Ancestors
  bodyFullCases selfdestructHalt entryCreateTerminalFetch entryCreateFocusSpec
  allocasBelowFmpUpdatesProps vyperStorageFootprint vyperInterpreter vyperState
  fragGasOriginPtr fragExec exprSimDefs venomInst venomExecSemantics venomState
Libs
  monadsyntax

Theorem selfdestruct_halt_preserves_allocas[local]:
  eval_operand op t = SOME w /\
  step_inst_base (mk_inst id SELFDESTRUCT [op] []) t = Halt u ==>
  (allocas_below_fmp u <=> allocas_below_fmp t)
Proof
  simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def] >>
  rpt (COND_CASES_TAC >> simp[LET_THM]) >>
  strip_tac >> gvs[] >> irule allocas_below_fmp_fields >>
  simp[halt_state_def, set_returndata_def]
QED

Theorem selfdestruct_selected_terminal_exit:
  compile_selfdestruct op m = ((),b) /\ fn_has_code m b func /\
  create_operand_at m t /\ ~t.vs_halted /\ eval_operand op t = SOME w /\
  op_taint tn op = {} /\ op_prov G op = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  t.vs_call_ctx.cc_address = cx.txn.target /\
  t.vs_call_ctx.cc_created_in_tx = cx.txn.created_in_tx /\
  t.vs_call_ctx.cc_static = cx.txn.is_static /\
  dest_AddressV v = SOME (w2w w) /\
  (cx.txn.is_static \/ ~selfdestruct_overflows cx (w2w w) mid.accounts) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
       halt_rel H cx (mid with gas_obs := []) t /\
       ghost_inv_at (DF H) lo d ce cx (mid with gas_obs := []) G tn t) ==>
  ?exc ee r.
    (!tail. selfdestruct_tail cx v (mid with gas_obs := tail) =
       (INR exc : eval_result + exception,ee with gas_obs := tail)) /\
    ee.storage_trace = mid.storage_trace /\
    storage_trace_domain cx st0 ee.storage_trace /\
    create_operand_full_scope m b explicit ctx func t [] r /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G,tn) /\
       create_operand_exit_post ctx cx H (INR exc : eval_result + exception)
         (ee with gas_obs := []) (G,tn) r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?r. step_inst_base (mk_inst m.cs_next_id SELFDESTRUCT [op] []) t = r /\
       exit_result r /\
       (!D. ghost_inv_at D lo d ce cx (mid with gas_obs := []) G tn t ==>
         gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G,tn))` by
    (irule selfdestruct_full_compiled_tail_joint >>
     fs[create_operand_at_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (r,G,tn)` by
    (rpt strip_tac >> first_assum irule >> metis_tac[]) >>
  `create_operand_full_scope m b explicit ctx func t [] r` by
    (irule selfdestruct_joint_scope >> simp[] >> metis_tac[]) >>
  Cases_on `cx.txn.is_static`
  >- (`r = Abort ExHalt_abort (halt_state (set_returndata [] t))` by
        (`t.vs_call_ctx.cc_static` by fs[] >>
         qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
         simp[step_inst_base_opcode_eqs, mk_inst_def, eval_operands_def]) >>
      qexistsl_tac [`Error (RuntimeError "write in static context")`,`mid`,`r`] >>
      conj_tac
      >- simp[selfdestruct_tail_def, bind_def, ignore_bind_def, lift_option_type_def,
              check_not_static_def, check_def, assert_def, raise_def, return_def] >>
      simp[] >> rpt strip_tac >> simp[create_operand_exit_post_def, expr_exit_def, halt_exit_def]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       ?u. step_inst_base (mk_inst m.cs_next_id SELFDESTRUCT [op] []) t = Halt u /\
           u.vs_returndata = [] /\
           halt_rel H cx (selfdestruct_final cx (w2w w) (mid with gas_obs := [])) u` by
    (rpt strip_tac >> irule step_selfdestruct_halt_rel >> simp[] >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `r = Halt u` by metis_tac[] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (drule_all selfdestruct_halt_preserves_allocas >> simp[]) >>
  qexistsl_tac [`HaltException`,`selfdestruct_final cx (w2w w) mid`,`r`] >>
  conj_tac
  >- (gen_tac >> rewrite_tac[GSYM (cj 1 selfdestruct_final_fields)] >>
      irule selfdestruct_tail_halt >> fs[]) >>
  `!a. (selfdestruct_final cx a mid).storage_trace = mid.storage_trace` by
    simp[selfdestruct_final_def] >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> ?u. _` drule >> strip_tac >>
  gvs[create_operand_exit_post_def, expr_exit_def, halt_exit_def]
QED

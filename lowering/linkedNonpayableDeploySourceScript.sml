(* Source rejection before the linked constructor body runs. *)
Theory linkedNonpayableDeploySource
Ancestors
  e2eDeployModsDefs ctorDeployLoweringArms vyperTypeDeploymentSoundness
  vyperInterpreter vyperContext vyperState alist finite_map list
val _ = Parse.hide "body";

Theorem linked_nonpayable_deploy_source:
  check_contract T am.layouts tx.target mods = SOME art /\
  ALOOKUP mods NONE = SOME tops /\
  lookup_function NONE tx.function_name Deploy tops =
    SOME (mut,nr,args,[],ret,body) /\
  LENGTH tx.args = LENGTH args /\ mut <> Payable /\ tx.value <> 0 ==>
  !orc gs. load_contract_trace orc gs am tx mods exps =
    (INR (Error (RuntimeError "not Payable")),[])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then (qx_choose_then `imms` assume_tac)
    check_contract_initial_immutables >>
  qabbrev_tac `cx = deploy_evaluation_context_mods mods am tx` >>
  qabbrev_tac `start = am with <|exports updated_by CONS (tx.target,exps);
      immutables updated_by CONS (tx.target,imms)|>` >>
  `ALOOKUP cx.sources cx.txn.target = SOME mods /\
   ALOOKUP start.immutables cx.txn.target = SOME imms /\
   cx.txn.target = tx.target` by
    simp[Abbr `cx`, Abbr `start`, deploy_evaluation_context_mods_def,
         initial_evaluation_context_def] >>
  drule_all check_contract_evaluate_all_constants_trace >>
  disch_then (qx_choose_then `am_c` assume_tac) >>
  `cx.in_deploy /\ cx.txn.value = tx.value` by
    simp[Abbr `cx`, deploy_evaluation_context_mods_def,
         initial_evaluation_context_def] >>
  rpt gen_tac >>
  `call_external_function_trace orc gs start cx nr mut tops mods
      args [] tx.args body ret = (INR (Error (RuntimeError "not Payable")),start,[],[])` by
    simp[call_external_function_trace_def, send_call_value_def, check_def,
         assert_def, ignore_bind_def, bind_def, raise_def, initial_state_def] >>
  qunabbrev_tac `cx` >> qunabbrev_tac `start` >>
  qpat_x_assum `call_external_function_trace _ _ _ _ _ _ _ _ _ _ _ _ _ = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [deploy_evaluation_context_mods_def, initial_evaluation_context_def]) >>
  simp[load_contract_trace_def, initial_evaluation_context_def]
QED

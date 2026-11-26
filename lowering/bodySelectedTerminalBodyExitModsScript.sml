(* Classify the already-reached terminal endpoint of the qualified body. *)
Theory bodySelectedTerminalBodyExitMods
Ancestors
  bodyPtrDefs stmtSimReturn exprSimDefs createSizeExit fragExec fragGasOriginPtr
  externalCallSelected[qualified] loweringStateRelDefs
  vyperStorageFootprint vyperInterpreter vyperState

Theorem terminal_handler_exit[local]:
  expr_exit (res : unit + exception) r ==>
  ?ex. res = INR ex /\ FST (handle_function ex ee) = INR ex /\
       expr_exit (INR ex : value + exception) r
Proof
  Cases_on `res` >> simp[expr_exit_def] >>
  rename1 `expr_exit (INR ex) r` >> Cases_on `ex` >> Cases_on `r` >>
  simp[expr_exit_def, handle_function_def, return_def, raise_def] >>
  rename1 `expr_exit (INR (Error err)) _ ==> _` >> Cases_on `err` >>
  simp[expr_exit_def, handle_function_def, return_def, raise_def]
QED

Theorem terminal_unlock_rule[local]:
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) ==>
  unlock_if_nr cx nr (is_view_mut mut) =
    if nr /\ ~view then release_nonreentrant_lock cx.txn.target key
    else return ()
Proof
  Cases_on `nr` >> Cases_on `view` >> simp[unlock_if_nr_def]
QED

Theorem terminal_return_after_unlock[local]:
  frame.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  intret_q H callee frame (cx with stk updated_by CONS (src,name)) rtv v
    (ee with scopes := []) r ==>
  ?ir cs out. r = IntRet ir cs /\
    unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),out) /\
    state_rel H callee frame (cx with stk updated_by CONS (src,name))
      (out with scopes := []) cs /\
    intret_vals_match rtv v ir.iret_values /\
    LENGTH ir.iret_values = frame.ce_returns_count /\ ir.iret_adopt_fmp = NONE
Proof
  strip_tac >> drule_then assume_tac terminal_unlock_rule >>
  drule_all_then strip_assume_tac intret_q_source_epilogue >>
  rename1 `result_rel H callee rtv frame _ (INR (ReturnException v),e0) r` >>
  `unlock_if_nr cx nr (is_view_mut mut) (ee with scopes := []) = (INL (),e0)` by
    (qpat_assum `unlock_if_nr _ _ _ = _` (pure_once_rewrite_tac o single) >>
     qpat_assum `(if _ then _ else _) _ = (INL (),e0)`
       (ACCEPT_TAC o REWRITE_RULE [vyperContextTheory.evaluation_context_accfupds])) >>
  Cases_on `unlock_if_nr cx nr (is_view_mut mut) ee` >>
  drule externalCallSelectedTheory.unlock_if_nr_with_scopes >>
  disch_then (qspec_then `[]` assume_tac) >>
  gvs[Excl "unlock_if_nr_def"] >>
  qpat_x_assum `intret_q _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [intret_q_def]) >>
  gvs[result_rel_def]
QED

val p = ``cx with stk updated_by CONS (src,name)``;
val e0 = ``ee with gas_obs := []``;
val ans = ``case (res : unit + exception) of
                INL _ => INL NoneV
              | INR ex => FST (handle_function ex ee)``;
val native_terminal = ``
  gas_origin_ptr_path (DF (H : (bool # bytes32 # type_value) list # num list),
    lo,explicit,ctx,callee,PG) start marks (r,Gc,tc) /\
  exit_result r /\ create_size_exit_ok ctx res r /\
  (!tail. stmt_exit_ptr (RetQ H) (^e0 with gas_obs := tail) res (Gc,tc) r) /\
  halt_exit H ^p ^e0 res r /\
  (ctx_has_dalloca ctx ==>
   !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s)``;

Theorem selected_terminal_body_exit_mods:
  storage_trace_domain ^p st0 ee.storage_trace /\
  (!H. valid_horizon ^p st0 H ee.storage_trace ==> ^native_terminal) /\
  answer = ^ans /\
  frame.ce_nonreentrant = (nr,key,T,view) /\
  (nr ==> cx.nonreentrant_slot = SOME key /\ view = is_view_mut mut) /\
  (!H v. RetQ H v (^e0 with scopes := []) (Gc,tc) r ==>
    intret_q H callee frame ^p rtv v (^e0 with scopes := []) r) ==>
  ((?v ir cs out.
      res = INR (ReturnException v) /\ answer = INL v /\ r = IntRet ir cs /\
      unlock_if_nr cx nr (is_view_mut mut) ^e0 = (INL (),out) /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = frame.ce_returns_count /\ ir.iret_adopt_fmp = NONE /\
      !H. valid_horizon ^p st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,PG) start marks (r,Gc,tc) /\
        exit_result r /\ create_size_exit_ok ctx answer r /\
        RetQ H v (^e0 with scopes := []) (Gc,tc) r /\
        state_rel H callee frame ^p (out with scopes := []) cs /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp cs)) \/
   (?ex. res = INR ex /\ answer = INR ex /\ expr_exit answer r /\
      !H. valid_horizon ^p st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,callee,PG) start marks (r,Gc,tc) /\
        exit_result r /\ create_size_exit_ok ctx answer r /\
        halt_exit H cx ^e0 answer r /\
        (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s)))
Proof
  strip_tac >>
  `stmt_exit_ptr (RetQ (storage_trace_horizon ee.storage_trace))
     ^e0 res (Gc,tc) r` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
     impl_tac >- fs[storage_trace_domain_def] >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `stmt_exit_ptr _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [stmt_exit_ptr_def])
  >- (drule terminal_handler_exit >> disch_then (qspec_then `ee` strip_assume_tac) >>
      disj2_tac >> qexists_tac `ex` >> gvs[] >>
      gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      simp[] >> qpat_x_assum `halt_exit _ _ _ _ _` mp_tac >>
      simp[NoAsms,halt_exit_def,halt_rel_def,accounts_rel_def]) >>
  qpat_assum `!H v. RetQ H v _ _ _ ==> _` drule >> strip_tac >>
  drule_all terminal_return_after_unlock >>
  disch_then (qx_choosel_then [`ir`,`cs`,`out`] strip_assume_tac) >>
  disj1_tac >> qexistsl_tac [`v`,`ir`,`cs`,`out`] >>
  simp[handle_function_def,return_def, Excl "unlock_if_nr_def"] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> strip_tac >>
  `RetQ H v (^e0 with scopes := []) (Gc,tc) (IntRet ir cs)` by
    (qpat_assum `!tail. stmt_exit_ptr _ _ _ _ _` (qspec_then `[]` mp_tac) >>
     gvs[stmt_exit_ptr_def, expr_exit_def, evaluation_state_fupdcanon]) >>
  qpat_x_assum `intret_q (storage_trace_horizon _) _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `RetQ (storage_trace_horizon _) _ _ _ _` kall_tac >>
  qpat_x_assum `r = IntRet ir cs` SUBST_ALL_TAC >>
  qpat_assum `!H v. RetQ H v _ _ _ ==> _` drule >> strip_tac >>
  drule_all terminal_return_after_unlock >> strip_tac >>
  gvs[exit_result_def, Excl "unlock_if_nr_def"]
QED

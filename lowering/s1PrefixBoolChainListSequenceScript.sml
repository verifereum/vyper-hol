(* Sequence value reads at the paired entries supplied by the caller. *)
Theory s1PrefixBoolChainListSequence
Ancestors
  s1PrefixCompose s1PrefixDefs s1PrefixProps gasOutcomeFull
  exprSimWordArgs vyperStorageTrace vyperStorageFootprint vyperState venomState
  list sum

Triviality list_read_nil_bind:
  bind (eval_exprs cx []) k = k []
Proof
  simp[FUN_EQ_THM, eval_exprs_nil, bind_def]
QED

Triviality list_read_cons_acc:
  bind (eval_exprs cx (e::todo)) (\vs. next (acc ++ vs)) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v. bind (eval_exprs cx todo) (\vs. next ((acc ++ [v]) ++ vs)))
Proof
  pure_once_rewrite_tac[eval_exprs_cons_action] >>
  simp_tac bool_ss [bind_assoc, bind_return, GSYM APPEND_ASSOC, APPEND]
QED

(* Ready packages the paired ordinary/shadow entry for the residual list.
   The head callback supplies the full and prefix runs at that entry and
   re-establishes Ready only at a successful replay cut. The final callback
   handles the action after the complete list; acc holds values already read. *)
Theorem bool_chain_list_sequence_prefix:
  (!vs. storage_trace_frame (next vs)) /\
  (!acc es s G tn. Ready [] acc es s G tn ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0 (next acc) (es,s,G,tn)) /\
  (!e todo acc es s G tn. Ready (e::todo) acc es s G tn ==>
    ?Q R.
      gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) Q R /\
      (!H res ee gt r. R H res ee gt r ==> ISR res) /\
      gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
        (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn) /\
      (!marks v mid G1 tn1 t.
        (!tail. bind (eval_expr cx e) (read_result cx)
          (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ tail) =
          (INL v,mid with gas_obs := tail)) /\
        storage_trace_domain cx st0 mid.storage_trace /\
        (!H. valid_horizon cx st0 H mid.storage_trace ==>
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) marks (OK t,G1,tn1) /\ Q H (INL v) mid G1 tn1 t) ==>
        Ready todo (acc ++ [v]) mid t G1 tn1)) ==>
  !todo acc es s G tn. Ready todo acc es s G tn ==>
    gas_prefix_full (DF,lo,explicit,ctx,func,PG) cx st0
      (bind (eval_exprs cx todo) (\vs. next (acc ++ vs))) (es,s,G,tn)
Proof
  strip_tac >> Induct >> simp[list_read_nil_bind] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!e todo acc es s G tn. Ready (e::todo) acc es s G tn ==> _`
    (drule_then strip_assume_tac) >>
  rewrite_tac[list_read_cons_acc] >>
  qhdtm_assum `gas_outcome_full` (mp_then Any irule gas_prefix_full_bind_replay) >>
  simp[storage_trace_frame_bind_all, evaluate_storage_trace_frame,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  conj_tac
  >- (qx_genl_tac [`marks`,`v`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
      qpat_assum `!acc es s G tn. Ready todo acc es s G tn ==> _`
        (qspec_then `acc ++ [v]` irule) >>
      first_x_assum irule >> simp[] >> metis_tac[]) >>
  first_assum ACCEPT_TAC
QED

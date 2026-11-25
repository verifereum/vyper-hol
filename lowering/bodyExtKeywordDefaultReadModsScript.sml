(* The successful read boundary for the linked nonword default keyword.  The
   continuation is deliberately generic: allocation and the physical copy are
   supplied by the later keyword cuts. *)
Theory bodyExtKeywordDefaultReadMods
Ancestors
  bodyFullPostsMods bodyFullPredsMods gasOutcomeFullBindMods
  gasExemptCertMods vyperStorageTrace vyperState exprSimHyps

Theorem ext_kw_default_read_cut_mods:
  gas_outcome_full_mods
    (DF,lo,explicit,ctx,func,PG) mods cx st0 (eval_expr cx e)
    (es,s0,G0,tn0) childQ
      (\H res ee gt r. ?exc. res = INR exc /\ R H (INR exc) ee gt r) /\
  (!marks res mid G1 tn1 t.
    (!tail. eval_expr cx e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\
    storage_trace_domain cx st0 mid.storage_trace /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
       childQ H res mid G1 tn1 t) ==>
    (?v. res = INL v /\
       gas_outcome_full_mods
         (DF,lo,explicit,ctx,func,PG) mods cx st0 (read_result cx v)
         (mid,t,G1,tn1) Q R) \/
    (?exc. res = INR exc /\
       !H. valid_horizon cx st0 H mid.storage_trace ==>
         Q H (INR exc) mid G1 tn1 t)) /\
  storage_trace_frame (eval_expr cx e) /\
  (!v. storage_trace_frame (read_result cx v)) /\
  (!marks err ee leaf stop_state.
    gas_exempt_cert_mods T mods (ctx,func)
      (ignore_bind (eval_expr cx e) (return ()))
      (es,s0) marks (err,ee) (leaf,stop_state) ==>
    gas_exempt_cert_mods T mods (ctx,func)
      (bind (eval_expr cx e)
        (\v. ignore_bind (read_result cx v) (return ())))
      (es,s0) marks (err,ee) (leaf,stop_state)) /\
  (!left v mid t right err ee leaf stop_state.
    gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
      left (INL v) mid (OK t) /\
    gas_exempt_cert_mods T mods (ctx,func)
      (ignore_bind (read_result cx v) (return ()))
      (mid with gas_obs := [],t) right (err,ee) (leaf,stop_state) ==>
    gas_exempt_cert_mods T mods (ctx,func)
      (bind (eval_expr cx e)
        (\v. ignore_bind (read_result cx v) (return ())))
      (es,s0) (left ++ right) (err,ee) (leaf,stop_state)) ==>
  gas_outcome_full_mods
    (DF,lo,explicit,ctx,func,PG) mods cx st0
    (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0) Q R
Proof
  strip_tac >>
  irule (Q.INST [`Q1` |-> `childQ`] gas_outcome_full_mods_bind_all) >>
  (conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
  (conj_tac >-
    (rpt strip_tac >> drule gas_exempt_cert_mods_bind_result >>
     simp[] >> disch_then irule >> simp[])) >>
  (conj_tac >-
    (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >>
     first_assum ACCEPT_TAC)) >>
  (conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  qexists `childQ` >> conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
QED

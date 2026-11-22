(* Source sequencing at a selected visit. A completed segment refers to the
   actual preceding visits; a remaining cut has the very same final hit. *)
Theory entryCreateStmtCases
Ancestors
  entryCreateBodyCut gasSummary gasSummaryCompose fragGasMode
  vyperInterpreter vyperState vyperStorageTrace vyperEvalPreservesScopes
  vyperTypeEvalProofs
  venomRunBounded venomState venomInst list pair

val _ = Parse.hide "body";
Theorem create_cut_noncreate_visit:
  inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2 ==>
  create_body_cut explicit tops cx st0 source (es,s) (before,(key,fnc,inst,t))
Proof
  simp[create_body_cut_def, inst_create_size_ok_def]
QED

Theorem create_cut_stmts_cons:
  (create_body_cut explicit tops cx st0 (eval_stmt cx stmt) (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split explicit tops cx st0 (ctx,func) (eval_stmt cx stmt)
       (\u. eval_stmts cx ss) (es,s) Q (left,right,hit)) ==>
  create_body_cut explicit tops cx st0 (eval_stmts cx (stmt::ss)) (es,s) (before,hit)
Proof
  simp[Once evaluate_def, ignore_bind_def] >> strip_tac
  >- (irule create_cut_bind_left >> simp[evaluate_storage_trace_frame]) >>
  gvs[] >> drule_at Any create_cut_bind_right >>
  simp[evaluate_storage_trace_frame]
QED

Theorem create_cut_stmts_nil:
  inst.inst_opcode <> CREATE /\ inst.inst_opcode <> CREATE2 ==>
  create_body_cut explicit tops cx st0 (eval_stmts cx []) (es,s)
    (before,(key,fnc,inst,t))
Proof
  strip_tac >> irule create_cut_noncreate_visit >> simp[]
QED

(* The continuation can be taken only on source agreement for every tail,
   not merely on equality of the compiler cursor. *)
Theorem create_cut_admin_prefix:
  gas_marked_exec F (ctx,func) admin (es,s)
    (create_cut_marks explicit left) (INL v) mid (OK t) /\
  (!w. storage_trace_frame (next w)) /\
  create_body_cut explicit tops cx st0 (next v) (mid,t) (right,hit) ==>
  create_body_cut explicit tops cx st0 (bind admin next) (es,s) (left ++ right,hit)
Proof
  strip_tac >> irule create_cut_bind_right >> simp[] >>
  qexistsl_tac [`\H v ee G tn st. T`,`ctx`,`func`] >>
  simp[create_cut_bind_split_def] >>
  qexistsl_tac [`t`,`INL v`,`mid`] >> simp[]
QED

(* An admin suffix with no GAS reads does not change the source readings
   available at an already selected cut. *)
Theorem create_cut_unmarked_suffix:
  create_cut_marks explicit glue = [] /\
  create_body_cut explicit tops cx st0 source (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 source (es,s) (before ++ glue,hit)
Proof
  strip_tac >> gvs[create_body_cut_def] >> first_assum ACCEPT_TAC
QED

Theorem create_cut_source_cong:
  (!tail. source (es with gas_obs :=
      gas_explicit (create_cut_marks explicit before) s.vs_gas_readings ++ tail) =
    source' (es' with gas_obs :=
      gas_explicit (create_cut_marks explicit before) s.vs_gas_readings ++ tail)) /\
  create_body_cut explicit tops cx st0 source' (es',s) (before,hit) ==>
  create_body_cut explicit tops cx st0 source (es,s) (before,hit)
Proof
  simp[create_body_cut_def] >> metis_tac[]
QED

Theorem create_cut_scoped_pop[local]:
  es.scopes <> [] /\ eval_stmts cx ss es = (res,ee) ==>
  ee.scopes <> [] /\ pop_scope ee = (INL (),ee with scopes := TL ee.scopes)
Proof
  strip_tac >> drule eval_stmts_preserves_scopes_len >>
  Cases_on `ee.scopes` >> simp[pop_scope_def, return_def, LENGTH_NIL] >>
  metis_tac[]
QED

Theorem create_cut_scoped_stmts:
  es.scopes <> [] /\
  create_body_cut explicit tops cx st0 (eval_stmts cx ss) (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 (finally (eval_stmts cx ss) pop_scope)
    (es,s) (before,hit)
Proof
  rw[create_body_cut_def] >> fs[finally_def] >>
  qmatch_asmsub_abbrev_tac `eval_stmts cx ss input` >>
    Cases_on `eval_stmts cx ss input` >>
  qmatch_asmsub_rename_tac `eval_stmts _ _ _ = (body_result,mid)` >>
  `input.scopes <> []` by simp[Abbr `input`] >>
  drule_all create_cut_scoped_pop >> strip_tac >>
  Cases_on `body_result` >> gvs[ignore_bind_def, bind_def, return_def, raise_def] >>
  fs[Abbr `input`] >> metis_tac[]
QED

Definition create_if_after_condition_def:
  create_if_after_condition cx yes no tv =
    ignore_bind push_scope
      (finally (switch_BoolV cx tv (eval_stmts cx yes) (eval_stmts cx no)) pop_scope)
End

Theorem create_if_after_condition_frame[local]:
  storage_trace_frame (create_if_after_condition cx yes no tv)
Proof
  simp[create_if_after_condition_def] >> irule storage_trace_frame_ignore_bind >>
  simp[storage_trace_frame_state_updates] >> irule storage_trace_frame_finally >>
  simp[storage_trace_frame_pop_scope, storage_trace_frame_switch,
       evaluate_storage_trace_frame]
QED

Theorem create_cut_if:
  (create_body_cut explicit tops cx st0 (eval_expr cx cond) (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split explicit tops cx st0 (ctx,func) (eval_expr cx cond)
       (create_if_after_condition cx yes no) (es,s) Q (left,right,hit)) ==>
  create_body_cut explicit tops cx st0 (eval_stmt cx (If cond yes no))
    (es,s) (before,hit)
Proof
  `eval_stmt cx (If cond yes no) =
   bind (eval_expr cx cond) (create_if_after_condition cx yes no)` by
    simp[Once evaluate_def, create_if_after_condition_def, FUN_EQ_THM, bind_def] >>
  simp[] >> strip_tac
  >- (irule create_cut_bind_left >> simp[create_if_after_condition_frame]) >>
  gvs[] >> drule_at Any create_cut_bind_right >> simp[create_if_after_condition_frame]
QED

(* The all-tails read equation selects exactly the branch reached by JNZ.
   The push-scope witness includes the target's administrative edge. *)
Theorem create_cut_if_taken:
  gas_marked_exec F (ctx,func) push_scope (es,s)
    (create_cut_marks explicit left) (INL ()) mid (OK t) /\
  (!tail. read_result cx tv (mid with gas_obs := tail) =
     (INL (BoolV b),mid with gas_obs := tail)) /\
  create_body_cut explicit tops cx st0 (eval_stmts cx (if b then yes else no))
    (mid,t) (right,hit) ==>
  create_body_cut explicit tops cx st0 (create_if_after_condition cx yes no tv)
    (es,s) (left ++ right,hit)
Proof
  strip_tac >> simp[create_if_after_condition_def, ignore_bind_def] >>
  irule create_cut_admin_prefix >>
  simp[storage_trace_frame_finally, storage_trace_frame_pop_scope,
       storage_trace_frame_switch, evaluate_storage_trace_frame] >>
  qexistsl_tac [`ctx`,`func`,`mid`,`t`] >> simp[] >>
  irule create_cut_source_cong >>
  qexistsl_tac [`mid`,`finally (eval_stmts cx (if b then yes else no)) pop_scope`] >>
  conj_tac
  >- (Cases_on `b` >> simp[finally_def, switch_BoolV_def, bind_def]) >>
  irule create_cut_scoped_stmts >> simp[] >>
  fs[gas_marked_exec_def] >>
  qpat_x_assum `!tail. push_scope _ = _` (qspec_then `[]` mp_tac) >>
  simp[push_scope_def, return_def] >>
  disch_then (mp_tac o AP_TERM ``evaluation_state_scopes``) >>
  Cases_on `mid.scopes` >> simp[]
QED

(* Loop cleanup handles Continue and Break, but neither a CREATE size
   error nor a source exemption is a loop-control exception. *)
Theorem create_cut_loop_body:
  es.scopes <> [] /\
  create_body_cut explicit tops cx st0 (eval_stmts cx body) (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0
    (finally (try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception)
      pop_scope) (es,s) (before,hit)
Proof
  rw[create_body_cut_def] >>
  drule_at Any for_body_decompose_any >> simp[] >> strip_tac >>
  qmatch_asmsub_rename_tac `eval_stmts _ _ _ = (body_result,mid)` >>
  `valid_horizon cx st0 H mid.storage_trace` by fs[] >>
  `create_cut_failure tops body_result` by metis_tac[] >>
  fs[create_cut_failure_def] >> metis_tac[exception_distinct]
QED

Definition create_for_round_body_def:
  create_for_round_body cx body =
    finally (try (ignore_bind (eval_stmts cx body) (return F)) handle_loop_exception)
      pop_scope
End

Definition create_for_round_def:
  create_for_round cx tyv nm body r =
    bind (bind (read_result cx r) (push_scope_with_var nm tyv))
      (\u. create_for_round_body cx body)
End

Theorem create_for_round_body_frame[local]:
  storage_trace_frame (create_for_round_body cx body)
Proof
  simp[create_for_round_body_def] >> irule storage_trace_frame_finally >>
  simp[storage_trace_frame_pop_scope] >> irule storage_trace_frame_try >>
  simp[storage_trace_frame_loop_handler] >> irule storage_trace_frame_ignore_bind >>
  simp[evaluate_storage_trace_frame, storage_trace_frame_return]
QED

Theorem create_cut_for_round:
  gas_marked_exec F (ctx,func)
    (bind (read_result cx r) (push_scope_with_var nm tyv)) (es,s)
    (create_cut_marks explicit left) (INL ()) mid (OK t) /\
  create_body_cut explicit tops cx st0 (eval_stmts cx body) (mid,t) (right,hit) ==>
  create_body_cut explicit tops cx st0 (create_for_round cx tyv nm body r)
    (es,s) (left ++ right,hit)
Proof
  strip_tac >> simp[create_for_round_def] >> irule create_cut_admin_prefix >>
  simp[create_for_round_body_frame] >> qexistsl_tac [`ctx`,`func`,`mid`,`t`] >> simp[] >>
  simp[create_for_round_body_def] >> irule create_cut_loop_body >> simp[] >>
  fs[gas_marked_exec_def] >>
  qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
  simp[bind_def] >> BasicProvers.TOP_CASE_TAC >> simp[] >> BasicProvers.TOP_CASE_TAC >>
  simp[push_scope_with_var_def, return_def] >>
  disch_then (mp_tac o AP_TERM ``evaluation_state_scopes``) >>
  Cases_on `mid.scopes` >> simp[]
QED

Definition create_for_next_def:
  create_for_next cx tyv nm body rs broke =
    if broke then return () else eval_for cx tyv nm body rs
End

Theorem create_for_next_frame[local]:
  storage_trace_frame (create_for_next cx tyv nm body rs b)
Proof
  Cases_on `b` >> simp[create_for_next_def, evaluate_storage_trace_frame,
                       storage_trace_frame_return]
QED

Theorem create_eval_for_cons[local]:
  eval_for cx tyv nm body (r::rs) =
    bind (create_for_round cx tyv nm body r) (create_for_next cx tyv nm body rs)
Proof
  simp[Once evaluate_def, create_for_round_def, create_for_round_body_def,
       create_for_next_def, FUN_EQ_THM, bind_def, ignore_bind_def] >>
  gen_tac >> BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >>
  simp[push_scope_with_var_def, return_def]
QED

(* A selected loop visit is either in this round or follows the actual
   completed round. The post retains one pair for all horizons at the
   split. Only fallthrough and Continue (INL F) can reach another round. *)
Inductive create_selected_for:
[~here:]
  (create_body_cut explicit tops cx st0 (create_for_round cx tyv nm body r)
     (es,s) (before,hit) ==>
   create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
     (r::rs) (es,s) (before,hit))
[~stop:]
  (gas_marked_exec F (ctx,func) (create_for_round cx tyv nm body r) (es,s)
     (create_cut_marks explicit left) failure mid (OK t) /\
   create_cut_failure tops failure ==>
   create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
     (r::rs) (es,s) (left ++ right,hit))
[~next:]
  (gas_marked_exec F (ctx,func) (create_for_round cx tyv nm body r) (es,s)
     (create_cut_marks explicit left) (INL F) mid (OK t) /\
   (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H rs mid G tn t) /\
   (!H. valid_horizon cx st0 H mid.storage_trace /\ Q H rs mid G tn t ==>
      create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
        rs (mid,t) (right,hit)) ==>
   create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
     (r::rs) (es,s) (left ++ right,hit))
End

Theorem create_cut_eval_for:
  create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
    vs (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 (eval_for cx tyv nm body vs) (es,s) (before,hit)
Proof
  qid_spec_tac `before` >> qid_spec_tac `hit` >>
  qid_spec_tac `es` >> qid_spec_tac `s` >> Induct_on `vs`
  >- simp[Once create_selected_for_cases] >>
  simp[Once create_selected_for_cases, create_eval_for_cons] >>
  rpt gen_tac >> strip_tac
  >- (irule create_cut_bind_left >> simp[create_for_next_frame])
  >- (gvs[] >> irule create_cut_bind_right >> simp[create_for_next_frame] >>
      qexistsl_tac [`\H b ee G tn st. T`,`ctx`,`func`] >>
      simp[create_cut_bind_split_def] >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  gvs[] >> irule create_cut_bind_right >> simp[create_for_next_frame] >>
  qexistsl_tac [`\H b ee G tn st. T`,`ctx`,`func`] >>
  simp[create_cut_bind_split_def] >>
  qexistsl_tac [`t`,`INL F`,`mid`] >> simp[create_for_next_def] >> metis_tac[]
QED

Definition create_for_after_iterator_def:
  create_for_after_iterator cx tyv nm body n vs =
    ignore_bind (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
      (eval_for cx tyv nm body vs)
End

Theorem create_for_after_iterator_frame[local]:
  storage_trace_frame (create_for_after_iterator cx tyv nm body n vs)
Proof
  simp[create_for_after_iterator_def, storage_trace_frame_ignore_bind,
       storage_trace_frame_checks, evaluate_storage_trace_frame]
QED

Theorem create_cut_for_after_iterator:
  gas_marked_exec F (ctx,func)
    (check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long")
    (es,s) (create_cut_marks explicit left) (INL ()) mid (OK t) /\
  create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
    vs (mid,t) (right,hit) ==>
  create_body_cut explicit tops cx st0 (create_for_after_iterator cx tyv nm body n vs)
    (es,s) (left ++ right,hit)
Proof
  strip_tac >> simp[create_for_after_iterator_def, ignore_bind_def] >>
  irule create_cut_admin_prefix >> simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`ctx`,`func`,`mid`,`t`] >> simp[] >>
  irule create_cut_eval_for >> metis_tac[]
QED

Definition create_for_after_type_def:
  create_for_after_type cx nm body n it tyv =
    bind (eval_iterator cx it) (create_for_after_iterator cx tyv nm body n)
End

Theorem create_for_after_type_frame[local]:
  storage_trace_frame (create_for_after_type cx nm body n it tyv)
Proof
  simp[create_for_after_type_def] >> irule storage_trace_frame_bind >>
  simp[evaluate_storage_trace_frame, create_for_after_iterator_frame]
QED

Theorem create_cut_for_iterator:
  (create_body_cut explicit tops cx st0 (eval_iterator cx it) (es,s) (before,hit) \/
   ?left right. before = left ++ right /\
     create_cut_bind_split explicit tops cx st0 (ctx,func) (eval_iterator cx it)
       (create_for_after_iterator cx tyv nm body n) (es,s) Q (left,right,hit)) ==>
  create_body_cut explicit tops cx st0 (create_for_after_type cx nm body n it tyv)
    (es,s) (before,hit)
Proof
  simp[create_for_after_type_def] >> strip_tac
  >- (irule create_cut_bind_left >> simp[create_for_after_iterator_frame]) >>
  gvs[] >> drule_at Any create_cut_bind_right >> simp[create_for_after_iterator_frame]
QED

Theorem create_cut_for_stmt:
  gas_marked_exec F (ctx,func)
    (lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type")
    (es,s) (create_cut_marks explicit left) (INL tyv) mid (OK t) /\
  create_body_cut explicit tops cx st0 (create_for_after_type cx nm body n it tyv)
    (mid,t) (right,hit) ==>
  create_body_cut explicit tops cx st0 (eval_stmt cx (For nm typ it n body))
    (es,s) (left ++ right,hit)
Proof
  `eval_stmt cx (For nm typ it n body) =
   bind (lift_option_type (evaluate_type (get_tenv cx) typ) "For evaluate_type")
     (create_for_after_type cx nm body n it)` by
    simp[Once evaluate_def, FUN_EQ_THM, create_for_after_type_def,
         create_for_after_iterator_def, bind_def] >>
  simp[] >> strip_tac >> irule create_cut_admin_prefix >>
  simp[create_for_after_type_frame] >>
  qexistsl_tac [`ctx`,`func`,`mid`,`t`,`tyv`] >> simp[]
QED

Theorem create_cut_stmt_expr:
  create_body_cut explicit tops cx st0 (eval_expr cx e) (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 (eval_stmt cx (Expr e)) (es,s) (before,hit)
Proof
  simp[Once evaluate_def] >> strip_tac >>
  irule create_cut_bind_left >> simp[storage_trace_frame_checks]
QED

Theorem create_cut_stmt_return:
  create_body_cut explicit tops cx st0
    (bind (eval_expr cx e) (read_result cx)) (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 (eval_stmt cx (Return (SOME e)))
    (es,s) (before,hit)
Proof
  `eval_stmt cx (Return (SOME e)) =
     bind (bind (eval_expr cx e) (read_result cx)) (\v. raise (ReturnException v))` by
    (simp[Once evaluate_def, FUN_EQ_THM, bind_def] >>
     gen_tac >> BasicProvers.TOP_CASE_TAC >> BasicProvers.TOP_CASE_TAC >> simp[]) >>
  simp[] >> strip_tac >> irule create_cut_bind_left >> simp[storage_trace_frame_raise]
QED

(* A compiler-specific one-round decomposition is sufficient. Active carries
   the selected native prefix in the current loop activation; after a normal
   round the same hit persists, with only the completed visits removed. *)
Theorem create_cut_for_from_rounds:
  (!es s before key fnc inst t.
    Active [] (es,s) (before,(key,fnc,inst,t)) ==> inst_create_size_ok inst t) /\
  (!r rs es s before key fnc inst t.
    Active (r::rs) (es,s) (before,(key,fnc,inst,t)) /\
    ~inst_create_size_ok inst t ==>
    create_body_cut explicit tops cx st0 (create_for_round cx tyv nm body r)
      (es,s) (before,(key,fnc,inst,t)) \/
    ?left right result mid u.
      before = left ++ right /\
      gas_marked_exec F (ctx,func) (create_for_round cx tyv nm body r) (es,s)
        (create_cut_marks explicit left) result mid (OK u) /\
      (create_cut_failure tops result \/
       ?G tn. result = INL F /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==> Q H rs mid G tn u) /\
         (!H. valid_horizon cx st0 H mid.storage_trace /\ Q H rs mid G tn u ==>
            Active rs (mid,u) (right,(key,fnc,inst,t))))) ==>
  !vs es s before key fnc inst t.
    Active vs (es,s) (before,(key,fnc,inst,t)) ==>
    create_body_cut explicit tops cx st0 (eval_for cx tyv nm body vs)
      (es,s) (before,(key,fnc,inst,t))
Proof
  strip_tac >>
  `!vs es s before key fnc inst t.
    Active vs (es,s) (before,(key,fnc,inst,t)) /\ ~inst_create_size_ok inst t ==>
    create_selected_for explicit tops cx st0 (ctx,func) tyv nm body Q
      vs (es,s) (before,(key,fnc,inst,t))` by
    (Induct
     >- metis_tac[] >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!a rest e0 s0 pre k f i t0. Active _ _ _ /\ _ ==> _`
       (drule_all_then strip_assume_tac)
     >- (irule create_selected_for_here >> simp[]) >>
     gvs[]
     >- (irule create_selected_for_stop >> metis_tac[]) >>
     irule create_selected_for_next >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `inst_create_size_ok inst t`
  >- simp[create_body_cut_def] >>
  irule create_cut_eval_for >> metis_tac[]
QED

Theorem create_cut_stmt_log:
  create_body_cut explicit tops cx st0 (eval_exprs cx args) (es,s) (before,hit) ==>
  create_body_cut explicit tops cx st0 (eval_stmt cx (Log id args)) (es,s) (before,hit)
Proof
  simp[Once evaluate_def] >> strip_tac >> irule create_cut_bind_left >>
  simp[storage_trace_frame_bind, storage_trace_frame_ignore_bind,
       storage_trace_frame_lifts, storage_trace_frame_check_not_static,
       storage_trace_frame_state_updates]
QED

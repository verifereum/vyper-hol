(* Source-ordered capture and evaluation for external-call operands. *)
Theory extcallOperandMemory
Ancestors
  extcallPositionalMemory extcallCaptureMemory extcallLoweredTyping
  extcallLoweredRepresentation extcallRequestStages extcallStoreUnwrapMemory
  noEffectSourceFrame sourceReadTransport exprSimExtCallCase vyperState
  vyperInterpreter

Theorem extcall_delayed_read_source[local]:
  EVERY (\e. ~expr_has_effect e) pos /\
  EVERY (\e. ~expr_has_effect e) kws /\
  eval_expr_results cx pos capture = (rp,mid) /\
  eval_exprs cx kws mid = (rk,last) /\
  read_result cx r last = (INL v,last) ==>
  read_result cx r capture = (INL v,capture)
Proof
  strip_tac >>
  `mid.scopes = capture.scopes /\
   mid.immutables = capture.immutables /\
   (!tr. get_storage cx mid tr = get_storage cx capture tr)` by
    metis_tac[no_effect_eval_results_frame] >>
  `last.scopes = mid.scopes /\ last.immutables = mid.immutables /\
   (!tr. get_storage cx last tr = get_storage cx mid tr)` by
    metis_tac[no_effect_eval_exprs_frame] >>
  irule read_result_source_fields_success >>
  qexists_tac `last` >> simp[]
QED

Theorem extcall_delayed_capture_bound[local]:
  EVERY (\e. ~expr_has_effect e) pos /\
  EVERY (\e. ~expr_has_effect e) kws /\
  eval_expr_results cx pos capture = (rp,mid) /\
  eval_exprs cx kws mid = (rk,last) /\
  vv_store_bound cx ty lt capture r vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  s.vs_alloca_next <= t.vs_alloca_next ==>
  vv_store_bound cx ty lt last r vv t
Proof
  strip_tac >> irule extcall_vv_bound_read_transport >>
  qexistsl_tac [`capture`, `s`] >> simp[] >>
  metis_tac[extcall_delayed_read_source]
QED

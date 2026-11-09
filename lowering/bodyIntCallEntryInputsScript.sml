(* Projections of the frozen call boundary, synchronized with caller decode. *)
Theory bodyIntCallEntryInputs
Ancestors
  bodyIntCallSeamDefs bodyIntCallInvokeEntry

Theorem intcall_entry_semantic_inputs:
  intcall_entry tops ctx func cenv cx tenv name es sa sb vv s0 es0
    (mut,args,ret,ss,rr) prev penv rtv es1 t ==>
  call_evaluation_safe (cx with stk updated_by CONS (NONE,name))
    (int_calls_stmts ss) /\
  es1.scopes = [penv] /\
  gas_admissible (intcall_rest cx name mut ss prev rtv) expr_vv_res_ok es1 /\
  stmt_state_rel ctx func cenv cx (es1 with scopes := prev) t /\
  expr_sim_inv cenv cx tenv (es1 with scopes := prev)
Proof
  simp[intcall_entry_def] >> rpt strip_tac >> simp[]
QED


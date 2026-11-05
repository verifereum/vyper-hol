Theory bodyPtrTypeBuiltinsFunctionFrame
Ancestors
  exprLoweringProps

(* The frame is not extensional in the instruction multiset: it identifies
   the entire function record with the function stored in the context. *)
Theorem stmt_state_rel_function_lookup:
  stmt_state_rel ctx func cenv cx es s ==>
  lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[stmt_state_rel_def, alloca_room_def]
QED

Theorem stmt_state_rel_same_name_unique:
  stmt_state_rel ctx f ce cx es s /\
  stmt_state_rel ctx g ce' cx' es' s' /\ f.fn_name = g.fn_name ==>
  f = g
Proof
  strip_tac >> imp_res_tac stmt_state_rel_function_lookup >> gvs[]
QED
